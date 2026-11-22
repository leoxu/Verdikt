#!/usr/bin/env python3
"""Taint-entry discovery: who in this project touches ATTACKER DATA FIRST.

The pre-scan harness used to answer this with two files that were both useless. On libgit2 (726
units) `entries.txt` listed 25,715 lines -- a listing, not a plan -- while the candidate-assist
report came out nearly empty: no ops tables, no opcode switch, and a "public API" section that
listed HEADER FILE NAMES instead of functions. The person picking entries got no help and no
warning, picked the loose-object parser by reading one file, and never scanned the pack/delta path
where a confirmed real defect had been found a month earlier (DESIGN.md Sec.22.131 / Sec.22.489).

So this looks for evidence instead of names, strongest first:

  fuzz     The project's OWN fuzz harnesses. A `LLVMFuzzerTestOneInput` is a maintainer writing
           down "these bytes are the attacker's, and this is the function I hand them to" -- the
           single most direct statement of attack surface a repository can contain, and the old
           tooling ignored it completely. libgit2 ships seven, one of them the packfile path.
  public   Declared in an installed header: the library's stated contract with its callers.
  buflen   Takes a (pointer, length) pair -- the shape every parser entry has.
  io       Calls read/recv/fread/inflate/mmap itself: where untrusted bytes first appear.
  name     parse/decode/unpack/load/... Ranking only, never evidence on its own.

A function with `fuzz` evidence is not a candidate, it is the answer unless there is a reason to
disagree. Everything below that is a ranked suggestion and still has to be read against the real
dispatch code (memory: testing-series-entry-selection).

Usage:  scan_entries.py <project-dir> [--out FILE] [--top N]
"""
import argparse
import os
import re
import sys
from collections import defaultdict

FUZZ_ENTRY = re.compile(r"LLVMFuzzerTestOneInput")
# a C function definition's name, at the start of a line, with its parameter list
# The return-type prefix is OPTIONAL and, when present, must end in space/tab/star. Requiring it
# (the old `^[A-Za-z_]...`) ate the first character of any name written at the start of its line --
# nginx's `ssize_t\nngx_read_file(...)` came out as `gx_read_file`. A name at line start now keeps
# all of itself.
FUNC_DEF = re.compile(r"^(?:[A-Za-z_][A-Za-z0-9_ \t\*]*?[ \t\*])?([A-Za-z_][A-Za-z0-9_]*)\s*\(([^;{]*)\)\s*\{", re.M)
FUNC_DECL = re.compile(r"^(?:[A-Za-z_][A-Za-z0-9_ \t\*]*?[ \t\*])?([A-Za-z_][A-Za-z0-9_]*)\s*\(([^;{]*)\)\s*;", re.M)
CALL = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]{2,})\s*\(")
# ---------------------------------------------------------------- the trust boundary
#
# THE criterion, of which "calls read()" was only a weak proxy: a parameter carries data that
# CROSSED A SECURITY TRUST BOUNDARY into this process. The boundary is what makes the bytes
# untrusted -- not the function's name, not where it sits in the library.
#
# Each kind below is a different way in, and they are listed separately because the attacker model
# differs: bytes off a socket come from whoever can reach the port, bytes from a file come from
# whoever can write the file, and shared memory can be rewritten by the peer AFTER a check has
# passed (so a value read twice can differ -- time-of-check/time-of-use is intrinsic to that kind,
# not an extra worry).
BOUNDARY = {
    "net": {"recv", "recvfrom", "recvmsg", "read", "readv", "accept", "SSL_read", "BIO_read",
            "SSL_peek", "gnutls_record_recv", "mbedtls_ssl_read", "curl_easy_perform"},
    "file": {"fread", "pread", "preadv", "fgets", "getline", "getdelim", "fscanf", "readlink",
             "getxattr", "fgetc", "fgetws", "readdir", "gzread", "archive_read_data"},
    "shm": {"shmat", "shm_open", "mmap", "mmap64", "MapViewOfFile"},
    "ipc": {"msgrcv", "mq_receive", "MsgReceive", "MsgReceivev", "MsgRead", "resmgr_msgread",
            "dbus_connection_pop_message", "binder_transaction"},
    "user": {"copy_from_user", "get_user", "memdup_user", "strncpy_from_user", "__copy_from_user",
             "simple_write_to_buffer", "copy_struct_from_user", "vmemdup_user"},
    "env": {"getenv", "secure_getenv", "setlocale", "nl_langinfo"},
}
IO_FNS = set().union(*BOUNDARY.values()) | {"inflate", "uncompress", "inflateInit", "inflateInit2",
                                            "lzma_code", "BZ2_bzDecompress", "zlib_inflate"}
ARGS_OF = re.compile(r"\b%s\s*\(([^;]*?)\)")
IDENT = re.compile(r"&?\s*([A-Za-z_][A-Za-z0-9_]*)")


# WHICH argument of a boundary call holds the bytes. Taking "the first three" instead marked the
# FILE DESCRIPTOR as a carrier -- `read(fd, buf, n)` -- so every function that takes an fd came out
# as attacker-facing, and close/write/send outranked the parsers. A carrier is the buffer, or the
# value assigned from the call when the bytes arrive as a return value (getenv, mmap, shmat).
BUF_ARG = {0: {"fread", "fgets", "fscanf", "getline", "getdelim", "copy_from_user", "__copy_from_user",
               "strncpy_from_user", "simple_write_to_buffer", "copy_struct_from_user", "get_user",
               "archive_read_data", "readdir"},
           1: {"read", "recv", "readv", "pread", "preadv", "SSL_read", "SSL_peek", "BIO_read",
               "gnutls_record_recv", "mbedtls_ssl_read", "msgrcv", "mq_receive", "MsgReceive",
               "MsgReceivev", "MsgRead", "resmgr_msgread", "gzread", "recvfrom", "recvmsg"}}
RET_CARRIER = {"getenv", "secure_getenv", "mmap", "mmap64", "shmat", "memdup_user", "vmemdup_user",
               "MapViewOfFile", "nl_langinfo", "readdir"}
ASSIGN = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(?:\([^)]*\)\s*)?$")


def boundary_kinds(body):
    """Which trust boundaries does this body cross, and which identifiers hold what came in?"""
    kinds, carriers = set(), set()
    for kind, fns in BOUNDARY.items():
        for fn in fns:
            for m in re.finditer(r"\b%s\s*\(([^;)]*)\)" % re.escape(fn), body):
                kinds.add(kind)
                args = [x.strip() for x in m.group(1).split(",")]
                idx = 0 if fn in BUF_ARG[0] else (1 if fn in BUF_ARG[1] else None)
                if idx is not None and len(args) > idx:
                    i = IDENT.match(args[idx])
                    if i:
                        carriers.add(i.group(1))
                if fn in RET_CARRIER:
                    a = ASSIGN.search(body[max(0, m.start() - 80):m.start()])
                    if a:
                        carriers.add(a.group(1))
    return kinds, carriers
NAME_HINT = re.compile(r"(^|_)(parse|decode|read|load|unpack|inflate|decompress|import|scan|from_raw|"
                       r"from_buffer|from_string|from_bytes|deserial|unmarshal|header|entry|apply)(_|$)", re.I)
PTR_PARAM = re.compile(r"(const\s+)?(unsigned\s+|signed\s+)?(char|void|uint8_t|int8_t|u_char|byte)\s*\*")
LEN_PARAM = re.compile(r"\b(size_t|ssize_t|unsigned|uint\d+_t|int|long|u_?int)\b[^,]*\b"
                       r"(len|size|n|count|nbytes|sz|length|cap)\w*\s*$", re.I)
SKIP_DIRS = {".git", "build", "scan_prep_build", "_build", "node_modules", "docs", "doc"}
TEST_DIRS = {"tests", "test", "examples", "example", "benchmarks", "ci"}


def c_files(root):
    for d, dirs, files in os.walk(root):
        dirs[:] = [x for x in dirs if x not in SKIP_DIRS and not x.startswith(".")]
        for fn in files:
            if fn.endswith((".c", ".cc", ".cpp", ".h")):
                yield os.path.join(d, fn)


def is_fuzz_file(path):
    low = path.lower()
    return "fuzz" in low or "ossfuzz" in low or "oss-fuzz" in low


def body_of(text, start):
    """Crude brace matcher from the '{' at or after `start`."""
    i = text.find("{", start)
    if i < 0:
        return ""
    depth, j = 0, i
    while j < len(text):
        if text[j] == "{":
            depth += 1
        elif text[j] == "}":
            depth -= 1
            if depth == 0:
                return text[i:j]
        j += 1
    return text[i:]


def param_pairs(params):
    """Does this parameter list contain a (pointer, length) pair?"""
    parts = [p.strip() for p in params.split(",") if p.strip()]
    for i, p in enumerate(parts):
        if PTR_PARAM.search(p):
            for q in parts[i:i + 3]:
                if q is not p and LEN_PARAM.search(q):
                    return True
    return False


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("project")
    ap.add_argument("--out", help="write the report here (default: stdout)")
    ap.add_argument("--top", type=int, default=40)
    a = ap.parse_args()
    root = os.path.abspath(a.project)
    if not os.path.isdir(root):
        sys.exit("not a directory: %s" % root)

    ev = defaultdict(set)        # function -> {evidence tags}
    where = {}                   # function -> "file:line" of its definition
    fuzz_targets = []            # (harness file, [functions it calls])
    public_headers = set()

    # ---- 1. the project's own fuzz harnesses
    for path in c_files(root):
        if not is_fuzz_file(path):
            continue
        try:
            txt = open(path, errors="replace").read()
        except OSError:
            continue
        if not FUZZ_ENTRY.search(path) and not FUZZ_ENTRY.search(txt):
            continue
        m = FUZZ_ENTRY.search(txt)
        body = body_of(txt, m.end()) if m else txt
        # A harness calls its target AND the lifecycle around it. Counting `git_str_init` or
        # `..._free` as attack surface buries the two or three calls that actually receive the
        # bytes, which is the whole reason this report exists. Lifecycle names are dropped from
        # the EVIDENCE but kept in the listing above, so nothing is hidden -- a reader can still
        # see the whole harness.
        # Matched as a SUFFIX, which is where C libraries put the verb. Matching the token anywhere
        # killed `git_commit_graph_file_parse` (because of `git_indexer_commit`) -- a filter that
        # removes a real parser to silence a free() is worse than the noise it removes.
        LIFECYCLE = re.compile(r"_(init|new|free|dispose|close|reset|clear|cstr|last|commit|"
                               r"attach_notowned)$", re.I)
        called = []
        for c in CALL.findall(body):
            if c in ("if", "for", "while", "switch", "return", "sizeof", "free", "memcpy", "abort",
                     "fprintf", "printf", "assert", "exit", "calloc", "malloc", "strlen"):
                continue
            called.append(c)
        seen = []
        for c in called:
            if c not in seen:
                seen.append(c)
        fuzz_targets.append((os.path.relpath(path, root), seen))
        # ...and a file that drives OTHER harnesses is not itself a statement about attack surface.
        if re.search(r"(driver|util|common|support)\.(c|cc|cpp)$", os.path.basename(path), re.I):
            continue
        for c in seen:
            if LIFECYCLE.search(c):
                continue
            ev[c].add("fuzz")

    # ---- 2. installed headers = the stated public contract
    for path in c_files(root):
        rel = os.path.relpath(path, root)
        if not path.endswith(".h"):
            continue
        if not (rel.startswith("include/") or "/include/" in rel):
            continue
        public_headers.add(rel)
        try:
            txt = open(path, errors="replace").read()
        except OSError:
            continue
        for name, params in FUNC_DECL.findall(txt):
            ev[name].add("public")
            if param_pairs(params):
                ev[name].add("buflen")

    # ---- 3/4/5. definitions: (ptr,len) shape, direct I/O, name hints
    for path in c_files(root):
        if path.endswith(".h") or is_fuzz_file(path):
            continue
        rel = os.path.relpath(path, root)
        top = rel.split(os.sep)[0]
        try:
            txt = open(path, errors="replace").read()
        except OSError:
            continue
        for m in FUNC_DEF.finditer(txt):
            name, params = m.group(1), m.group(2)
            if name in ("if", "for", "while", "switch", "return", "sizeof"):
                continue
            line = txt.count("\n", 0, m.start()) + 1
            where.setdefault(name, "%s:%d" % (rel, line))
            if top in TEST_DIRS:
                ev[name].add("test-only")
            if param_pairs(params):
                ev[name].add("buflen")
            if NAME_HINT.search(name):
                ev[name].add("name")
            body = body_of(txt, m.end() - 1)
            kinds, carriers = boundary_kinds(body)
            for k in kinds:
                ev[name].add("boundary:" + k)          # the data enters the process HERE
            # ...and one hop forward: whatever this function hands those bytes to is the first
            # thing that PARSES untrusted data, which is usually the entry worth scanning. The
            # reader of a socket is rarely interesting; the function it passes the buffer to is.
            if carriers:
                for cm in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]{2,})\s*\(([^;)]*)\)", body):
                    callee, args = cm.group(1), cm.group(2)
                    if callee in IO_FNS or callee in ("if", "for", "while", "switch", "return", "sizeof"):
                        continue
                    if any(re.search(r"\b%s\b" % re.escape(c), args) for c in carriers):
                        for k in kinds:
                            ev[callee].add("fed-by:" + k)
            if any(re.search(r"\b%s\s*\(" % re.escape(io), body) for io in IO_FNS):
                ev[name].add("io")

    # ---- rank
    # A boundary crossing is the definition, so it outranks every inferred signal and is beaten
    # only by the project stating the answer itself (a fuzz harness). `fed-by` -- the function the
    # boundary-crossing bytes are handed to -- scores just under it: that is usually the parser,
    # while the function that merely called recv() is usually plumbing.
    def wof(tag):
        if tag.startswith("boundary:"):
            return 30
        if tag.startswith("fed-by:"):
            return 25
        return {"fuzz": 100, "public": 8, "buflen": 6, "io": 3, "name": 2, "dispatch": 20,
                "test-only": -50}.get(tag, 0)
    rows = []
    for fn, tags in ev.items():
        if fn not in where and "fuzz" not in tags and "public" not in tags:
            continue                      # no definition in this tree and nothing vouching for it
        # `fed-by` means "this project's code hands it the bytes". A libc function that merely
        # receives the same buffer (write, snprintf, fclose) is not an entry of this project, and
        # only a definition in this tree proves the difference.
        if fn not in where:
            tags = [t for t in tags if not t.startswith(("fed-by:", "boundary:"))]
        score = sum(wof(t) for t in tags)
        if score <= 0:
            continue
        rows.append((score, fn, sorted(tags), where.get(fn, "(declared only)")))
    rows.sort(key=lambda r: (-r[0], r[1]))

    out = []
    out.append("# Taint-entry candidates -- %s" % os.path.basename(root))
    out.append("")
    out.append("Generated by `scan_entries.py`. **Evidence, not names.** Read it against the real")
    out.append("dispatch code before choosing; `fuzz` rows are the project's own statement of what")
    out.append("attacker data reaches, and skipping one needs a reason written in NOTES.md.")
    out.append("")
    if fuzz_targets:
        out.append("## What the project itself says is attacker-facing (%d harness(es))" % len(fuzz_targets))
        out.append("")
        for f, fns in fuzz_targets:
            out.append("* `%s`" % f)
            if fns:
                out.append("    calls: %s" % ", ".join(fns[:12]))
        out.append("")
        corp = [os.path.relpath(os.path.join(d, x), root)
                for d, dirs, files in os.walk(root) for x in dirs if "corp" in x.lower()]
        if corp:
            out.append("Seed corpora ship with the repo (%s) -- real inputs for --seed-bytes."
                       % ", ".join(sorted(corp)[:4]))
            out.append("")
    else:
        out.append("## No fuzz harness found in the tree")
        out.append("")
        out.append("That is itself a fact worth knowing: nobody has written down what this project's")
        out.append("attacker surface is, so every row below is inference.")
        out.append("")
    out.append("## Ranked candidates")
    out.append("")
    out.append("| score | function | evidence | defined at |")
    out.append("|---|---|---|---|")
    for score, fn, tags, w in rows[:a.top]:
        out.append("| %d | `%s` | %s | %s |" % (score, fn, " ".join(tags), w))
    out.append("")
    out.append("%d candidate(s) scored; %d shown. Public headers read: %d."
               % (len(rows), min(len(rows), a.top), len(public_headers)))
    text = "\n".join(out) + "\n"
    if a.out:
        open(a.out, "w").write(text)
        print("scan_entries: wrote %s (%d candidates, %d fuzz harness(es))"
              % (a.out, len(rows), len(fuzz_targets)), file=sys.stderr)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""scan_init.py -- the PRE-SCAN harness.

Gets from a project checkout to a profile that scan_profile.py can run:

  build system  ->  compile_commands.json  ->  flags  ->  scan-profiles/<name>/profile.yaml
                                                          + NOTES.md + harness skeleton

scan_preprocess.sh already owns the first arrow (cmake / meson / makefile / kernel) and the entry
listing. This script owns the second and third: it reads compile_commands.json, extracts the
include and define flags the project actually compiles with, and writes a profile carrying the four
acceptance gates of docs/SCAN_SETUP_CHECKLIST.md.

WHAT IT REFUSES TO DO: choose entries, and write a harness body. Entry selection needs the real
dispatch code read by a human (memory: testing-series-entry-selection.md), and a harness is the one
artefact in the chain that encodes what the program MEANS. Both are emitted as skeletons, and the
profile is written `status: draft`, which scan_profile.py refuses to run.

  scan_init.py <project-dir> [--name N] [--mode harness|bare] [--build cmake|meson|makefile|auto]
               [--entry FN]... [--force]
"""
import argparse
import collections
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
PROFILES = os.path.join(ROOT, "scan-profiles")


def die(msg):
    print("scan_init: %s" % msg, file=sys.stderr)
    sys.exit(1)


def detect_build(src):
    if os.path.exists(os.path.join(src, "CMakeLists.txt")):
        return "cmake"
    if os.path.exists(os.path.join(src, "meson.build")):
        return "meson"
    for n in ("configure", "configure.ac", "Makefile.am", "Makefile", "makefile", "GNUmakefile"):
        if os.path.exists(os.path.join(src, n)):
            return "makefile"
    return None


def prior_work(name, hlir_root):
    """Has this project been scanned before, and what was found?

    THIS EXISTS BECAUSE OF libgit2. It was scanned on 2026-10-23 (DESIGN.md Sec.22.131) and a REAL
    shift-range UB was confirmed in the delta header decoder, reachable from any untrusted pack file.
    On 2026-11-15 the project was set up again from scratch, the entries were chosen by reading
    object.c, and the pack/delta path -- the one with the known defect -- was not scanned at all.
    Nothing in this pipeline asked the question, and the knowledge lived in exactly one section of a
    thirty-thousand-line document. The October run had also left no memory note, unlike every other
    project of that period, so the one recall mechanism that does run every session had nothing.

    This prints what it finds and does not block: the point is that the person choosing entries SEES
    the earlier attack surface before choosing, not that the tool decides for them."""
    out = []
    pats = [name]
    if name.startswith("lib"):
        pats.append(name[3:])
    design = os.path.join(hlir_root, "docs", "DESIGN.md")
    if os.path.exists(design):
        with open(design, errors="replace") as f:
            for ln in f:
                if ln.startswith("#") and any(re.search(r"\b%s\b" % re.escape(p), ln, re.I) for p in pats):
                    out.append(("DESIGN.md", ln.strip()[:160]))
    mem = os.environ.get("HLIR_NOTES_DIR", "")
    for d, label in ((mem, "memory"),
                     (os.path.join(hlir_root, "..", "security_reports"), "report"),
                     (os.path.join(hlir_root, "..", "cve-corpus"), "cve-corpus")):
        if not os.path.isdir(d):
            continue
        for root, _, files in os.walk(d):
            for fn in files:
                if not fn.endswith((".md", ".yaml")):
                    continue
                fp = os.path.join(root, fn)
                try:
                    txt = open(fp, errors="replace").read()
                except OSError:
                    continue
                if any(re.search(r"\b%s\b" % re.escape(p), txt, re.I) for p in pats):
                    out.append((label, os.path.relpath(fp, os.path.dirname(d))))
    return out


def find_compile_commands(src):
    """Where a compile database can be, INCLUDING the directory this tool's own build step writes to.

    `scan_prep_build` was missing from this list, and the omission was silent in the worst way: on
    libgit2 the cmake step ran, produced scan_prep_build/compile_commands.json, and this function --
    called again right afterwards for exactly that reason -- still said there was none. The profile
    came out with no -I and no -D at all, and the message blamed the project ("every -I/-D has to be
    written by hand"). It only worked on libssh because that build happened to leave a copy in the
    project root.

    Newest wins when several exist: a stale database from someone's old build directory describes
    flags the current source may not even compile with."""
    cands = []
    for d in (src, os.path.join(src, "scan_prep_build"), os.path.join(src, "build"),
              os.path.join(src, "_build")):
        p = os.path.join(d, "compile_commands.json")
        if os.path.exists(p):
            cands.append(p)
    if not cands:
        return None
    return max(cands, key=os.path.getmtime)


def run_preprocess(mode, src, out):
    sh = os.path.join(HERE, "scan_preprocess.sh")
    if not os.path.exists(sh):
        die("scan_preprocess.sh not found at %s" % sh)
    print("scan_init: scan_preprocess.sh %s %s" % (mode, src))
    r = subprocess.run(["bash", sh, mode, src], capture_output=True, text=True)
    (out or sys.stdout).write(r.stdout[-4000:])
    if r.returncode != 0:
        print(r.stderr[-3000:], file=sys.stderr)
        print("scan_init: scan_preprocess.sh failed -- this is normal for a project that needs "
              "configure flags. Produce compile_commands.json yourself and re-run with --build skip.",
              file=sys.stderr)
    return r.returncode == 0


# ---------------------------------------------------------------- flags out of compile_commands
def extract_flags(ccpath, src):
    """The mechanical half of a profile: which -I and -D the project really compiles with.

    Counted across every translation unit, not taken from the first one: a project compiles its
    generated headers into some units and not others, and a flag present in one unit out of two
    hundred is a per-file quirk, not a project flag. Everything is reported with its share so the
    threshold is visible rather than hidden."""
    with open(ccpath) as f:
        db = json.load(f)
    incs, defs, others = collections.Counter(), collections.Counter(), collections.Counter()
    std = collections.Counter()
    n = 0
    for tu in db:
        args = tu.get("arguments")
        if not args:
            args = tu.get("command", "").split()
        if not args:
            continue
        n += 1
        i = 0
        while i < len(args):
            a = args[i]
            if a == "-I" and i + 1 < len(args):
                incs[args[i + 1]] += 1; i += 2; continue
            if a.startswith("-I"):
                incs[a[2:]] += 1
            elif a == "-D" and i + 1 < len(args):
                defs[args[i + 1]] += 1; i += 2; continue
            elif a.startswith("-D"):
                defs[a[2:]] += 1
            elif a.startswith("-std="):
                std[a[5:]] += 1
            elif a.startswith("-f") and "sanitize" not in a:
                others[a] += 1
            i += 1
    return dict(units=n, includes=incs, defines=defs, std=std, others=others)


def rel_to(path, src):
    try:
        r = os.path.relpath(path, src)
    except ValueError:
        return path
    return "$SRC/" + r if not r.startswith("..") else path


HARNESS_SKELETON = '''/* %(name)s harness -- SKELETON, NOT RUNNABLE.
 *
 * scan_init.py wrote the shape; the body is the one thing in the chain that cannot be generated,
 * because it encodes what the program MEANS: which call sequence puts the library in the state the
 * entry is reached from, and which bytes of `src` stand for what the attacker controls.
 *
 * The signature is the project convention (cve-corpus/*/harness.c): one byte buffer and its length,
 * so --seed-bytes and the CVE corpus runner both work without a special case.
 *
 * RULES THAT HAVE COST US TIME BEFORE:
 *   - pin SIZES, not CONTENTS (memory: harness-pin-size-not-contents). A symbolic length makes
 *     every run vacuous; a fixed-size struct with symbolic bytes does not.
 *   - copy the product's own formula for every config value (memory: harness-config-values).
 *     A value you invented is a program the project does not have.
 *   - build it natively with ASan FIRST and make it crash on a known input, before any scan.
 *     See scan-profiles/redis/native/build.sh for the pattern (it derives its stub list from the
 *     link error rather than hand-writing it).
 *
 * TODO: everything below.
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int %(entry)s(unsigned char *src, unsigned int len)
{
    if (len < 1)
        return -1;

    /* TODO: construct the state the real caller would have built, then call into the library
     * with `src` standing in for the attacker-controlled bytes. Returning 0 here means the
     * scan reports 0 blocks visited -- which the profile's `blocks_visited: ">0"` gate catches. */
    (void) src;
    return 0;
}
'''

NOTES_SKELETON = '''# %(name)s -- scan notes

Generated by `scan_init.py` on %(date)s. **Every heading below is a question this file has to answer
before the profile leaves `status: draft`.** `scan-profiles/README.md`: "Configuration without its
reasons gets simplified by the next person, which is how a trap gets re-entered."

## What this project is, and where the attacker data enters

TODO.

## Earlier work on this project

%(prior)s

## Entry selection -- why THESE entries

TODO. Read the real dispatch code (ops-struct initialisers, ioctl/opcode switches, route tables,
public headers). `%(out)s/entries.txt` is a listing, not an answer.

If the section above is not empty, say here why the entries chosen now DO or DO NOT cover the
surface the earlier work used. libgit2 is the cautionary case: a confirmed shift-range UB in the
pack/delta decoder (Sec.22.131) sat in a path the next setup did not scan at all, and the gap was
only noticed a month later because someone remembered.

## Build flags that are load-bearing

%(flagnotes)s

## Externals: what the scan will NOT have

TODO. After the first run, `scan_report.py <out>` lists `opaque_calls`. Each one needs a decision:
link the file that defines it, model it, or justify it in an `--externs` document.

## Deliberate approximations

TODO. Anything the harness fakes, and why it is faithful rather than convenient.

## Known dead ends

TODO.
'''


SPEC_HEADER = """# TAINT ENTRY for %(fn)s -- harvested from the SYNTHESISED spec, then corrected by hand.
#
# `--spec-dir` makes hlir-scan use this file instead of what it would synthesise. What the
# synthesiser produced is below; it is a GUESS from the signature and the struct layouts, and the
# three things it cannot know are the three that decide whether the scan measures the real program:
#
#   1. WHICH PARAMETERS CARRY ATTACKER DATA.  `taint: pointee` (the bytes behind the pointer),
#      `taint: value` (the scalar itself), `taint: none` (a context object the caller owns).
#      PREFER DECLARING `taint: none` HERE OVER `--ctx-names`.  That flag is a regex over parameter
#      NAMES: on yara it matched macho's `object` and missed ELF's `elf_obj`, so one validation ran
#      as two incomparable halves -- macho's object tree pinned to zero, ELF's walked as attacker
#      data -- and the coverage numbers could not be compared at all. A spec names the parameter.
#
#   2. THE RELATIONS BETWEEN PARAMETERS.  A (pointer, length) pair that is not declared lets the
#      solver pick a length longer than the buffer, and every finding behind it is an artefact.
#      Equally, a relation that CONTRADICTS the real call makes the entry unsatisfiable: yara's
#      parse_elf_header_32_le pinned `elf` to 52 bytes while the real caller guarantees
#      `size(elf) == elf_size > 52`, so the engine explored an impossible program at 100%% coverage.
#      Read the REAL call site before trusting this section.
#
#   3. SIZES vs CONTENTS.  Pin sizes, leave contents symbolic. A symbolic length produces vacuous
#      runs (memory: harness-pin-size-not-contents).
#
# After editing, re-run and check `scan_advise.py` for CHECK_SPEC.
"""


def profile_command(pname, entry_set=None, entries=None, drop_spec_dir=False, overrides=None):
    """Build the scan command FROM THE PROFILE, the same way scan_profile.py would.

    The first version of --harvest-specs made the caller pass every source and flag as --scan-arg.
    That is the profile's own content: harvesting yara's seven taint entries meant a shell loop
    emitting 36 --scan-arg, and `--scan-arg --link` silently became an argparse option (it needs
    `--scan-arg=--link`). Worse, hand-assembled flags DRIFT from the profile the specs belong to.
    Both modes below now read link.files and flags from the profile itself.
    """
    import yaml
    sys.path.insert(0, HERE)
    import scan_profile as SP
    prof_dir = SP.find_profile(pname)
    with open(os.path.join(prof_dir, "profile.yaml")) as f:
        prof = yaml.safe_load(f) or {}
    sets = prof.get("entry_sets") or {}
    if entry_set:
        if entry_set not in sets:
            die("profile '%s' has no entry set '%s' (have: %s)" % (pname, entry_set, ", ".join(sets)))
        chosen = {entry_set: sets[entry_set]}
    else:
        chosen = sets or {"<none>": {}}
    src = SP.resolve_source(prof, prof_dir, None)
    # The same three the runner seeds before resolve_vars. Omitting them left `-I$SRC/libyara`
    # literal on the command line, so clang got NO include path: `size_t` came back as an
    # incomplete type, 19 names got stub typedefs, every entry was "not lowered" and the run
    # reported `0 entries` -- a scan of nothing that still exits 0.
    vars_ = {"SRC": src, "PROFILE": prof_dir, "HLIR": SP.HLIR}
    vars_.update(SP.resolve_vars(prof, prof_dir, {}))
    out = []
    for sname, eset in chosen.items():
        eset = dict(eset or {})
        if entries:
            eset["entry"] = list(entries)
        ents = [e for e in (eset.get("entry") or []) if not str(e).startswith("TODO")]
        if not ents:
            continue
        eset["entry"] = ents
        cmd = SP.build_command(prof, eset, vars_, src, prof_dir, {}, list(overrides or []))
        if drop_spec_dir and "--spec-dir" in cmd:
            k = cmd.index("--spec-dir")
            del cmd[k:k + 2]
        out.append((sname, ents, cmd, prof_dir))
    if not out:
        die("no runnable entries in profile '%s' (entry_sets are empty or still TODO)" % pname)
    return out


def _short_run(cmd, entries, tmp, runs="1", timeout="5"):
    """Replace the budget with a trivial one and point --out at a scratch dir."""
    cmd = list(cmd)
    for flag, val in (("--runs", runs), ("--timeout", timeout), ("--jobs", "2")):
        if flag in cmd:
            cmd[cmd.index(flag) + 1] = val
        else:
            cmd += [flag, val]
    if "--out" in cmd:
        cmd[cmd.index("--out") + 1] = tmp
    else:
        cmd += ["--out", tmp]
    return subprocess.run(cmd, capture_output=True, text=True)


def harvest_specs(pname, entry_set, entries):
    """Run a trivial scan with NO --spec-dir, so the engine emits what it would SYNTHESISE, then
    install those under <profile>/specs/<function>.yaml for hand correction."""
    import glob
    import tempfile
    total = 0
    for sname, ents, cmd, pdir in profile_command(pname, entry_set, entries, drop_spec_dir=True):
        tmp = tempfile.mkdtemp(prefix="hlir-spec-")
        print("scan_init: harvesting %d entry(s) of set '%s'" % (len(ents), sname))
        r = _short_run(cmd, ents, tmp)
        sdir = os.path.join(pdir, "specs")
        os.makedirs(sdir, exist_ok=True)
        n = 0
        for f in sorted(glob.glob(os.path.join(tmp, "specs", "*.yaml"))):
            base = os.path.basename(f)
            fn = base.rsplit("__", 1)[-1][:-5] if "__" in base else base[:-5]
            if fn not in ents:
                continue
            dst = os.path.join(sdir, fn + ".yaml")
            if os.path.exists(dst):
                print("  specs/%s.yaml  EXISTS, not overwritten (delete it to re-harvest)" % fn)
                continue
            open(dst, "w").write(SPEC_HEADER % dict(fn=fn) + open(f).read())
            n += 1
            print("  specs/%s.yaml" % fn)
        shutil.rmtree(tmp, ignore_errors=True)
        if not n and not os.listdir(sdir):
            print("scan_init: set '%s' produced no spec -- the build probably failed:\n%s"
                  % (sname, (r.stderr or r.stdout)[-1500:]), file=sys.stderr)
        total += n
    return total


def validate_specs(pname, entry_set, entries):
    """Run every entry for 1 run WITH --spec-dir and prove the corrected specs were USED.

    A corrected spec is a small program nobody compiles. `size.from_param` was the first thing
    written into yara's ELF specs and the engine refused it -- "does not name an EARLIER scalar
    parameter" -- which only surfaced because a 20-run scan was launched by hand.

    The check is the report's own `spec` field, not a log line: the "using the user-written spec"
    note only prints for a failing entry or under -v, so counting it passed a run in which NO spec
    was loaded at all. A validator that can report success while the thing it validates was never
    read is the same defect as a gate reachable from one entry point."""
    import json as _json
    import tempfile
    bad = 0
    for sname, ents, cmd, pdir in profile_command(pname, entry_set, entries):
        sdir = os.path.join(pdir, "specs")
        if "--spec-dir" not in cmd:
            print("  set '%s': profile declares no specs: -- nothing to validate" % sname)
            continue
        have = {f[:-5] for f in os.listdir(sdir) if f.endswith(".yaml")} if os.path.isdir(sdir) else set()
        tmp = tempfile.mkdtemp(prefix="hlir-specval-")
        rep = os.path.join(tmp, "val.json")
        r = _short_run(cmd + ["--format", "json", "--output", rep], ents, tmp)
        text = (r.stdout or "") + (r.stderr or "")
        # The error has to come from the REPORT, not from stdout: with --format json the engine
        # stops printing the human-readable per-entry detail, so grepping stdout for `input_error:`
        # found nothing and this validator passed a spec the engine had refused. The structured
        # `incomplete` list carries the same thing and does not depend on the output format.
        errs = []
        used = set()
        if os.path.exists(rep):
            try:
                for e in (_json.load(open(rep)).get("entries") or []):
                    sp = e.get("spec") or ""
                    if os.path.dirname(os.path.abspath(sp)) == os.path.abspath(sdir):
                        used.add(e.get("function"))
                    for inc in (e.get("incomplete") or []):
                        if inc.get("code") == "input_error":
                            errs.append("@%s %s" % (e.get("function"), inc.get("detail", "")))
            except Exception as ex:  # noqa: BLE001
                print("    FAIL could not read the validation report: %s" % ex)
                bad += 1
        else:
            print("    FAIL the validation run produced no report (the scan itself failed)")
            bad += 1
        expected = {e for e in ents if e in have}
        missing = sorted(expected - used)
        print("  set '%s': %d entry(s), %d spec(s) on disk, %d LOADED" % (sname, len(ents), len(expected), len(used)))
        for e in errs:
            print("    FAIL %s" % e)
            bad += 1
        for m in missing:
            print("    FAIL specs/%s.yaml exists but the run did not load it -- the engine fell back to "
                  "the SYNTHESISED entry and the verdict would print as usual" % m)
            bad += 1
        shutil.rmtree(tmp, ignore_errors=True)
    return bad


def main():
    ap = argparse.ArgumentParser(description="pre-scan harness: project -> compile_commands -> profile")
    ap.add_argument("project", help="the project checkout")
    ap.add_argument("--name", help="profile name (default: the directory name)")
    ap.add_argument("--mode", choices=["harness", "bare"], default="harness",
                    help="harness: emit a harness skeleton. bare: no harness, --entry names library "
                         "functions directly and the engine synthesises the entry contract.")
    ap.add_argument("--build", choices=["auto", "cmake", "meson", "makefile", "skip"], default="auto")
    ap.add_argument("--entry", action="append", default=[], help="seed the entry set (repeatable)")
    ap.add_argument("--min-share", type=float, default=0.5,
                    help="a flag is a PROJECT flag when this fraction of units carry it (default 0.5)")
    ap.add_argument("--force", action="store_true", help="overwrite an existing profile")
    ap.add_argument("--label", default="network", help="taint label (default network)")
    ap.add_argument("--ctx-names", help="regex of parameter names that are untainted context objects. "
                                        "Prefer `taint: none` in specs/ -- see the generated spec header.")
    ap.add_argument("--harvest-specs", action="store_true",
                    help="PROJECT is an existing profile name: run a 1-run scan (sources and flags taken "
                         "FROM THE PROFILE) to emit the synthesised taint entries under <profile>/specs/")
    ap.add_argument("--validate-specs", action="store_true",
                    help="PROJECT is an existing profile name: run every entry for 1 run with --spec-dir "
                         "and report any input_error. Seconds, not a scan.")
    ap.add_argument("--set-name", metavar="SET", help="limit --harvest-specs/--validate-specs to one entry set")
    a = ap.parse_args()

    # ---- mode 2: harvest taint entries into an EXISTING profile. Separate from profile creation
    # because a synthesised spec needs a build that works, which needs link.files, which a human
    # fills in after the profile is generated.
    if a.harvest_specs or a.validate_specs:
        if not os.path.isdir(os.path.join(PROFILES, a.project)):
            die("no profile '%s' under %s" % (a.project, PROFILES))
        if a.validate_specs:
            print("scan_init: validating specs of profile '%s'" % a.project)
            bad = validate_specs(a.project, a.set_name, a.entry or None)
            if bad:
                print("\n%d spec error(s). A spec the engine refuses is silently ignored in a real scan: "
                      "it falls back to the SYNTHESISED entry and the verdict prints as usual." % bad)
                return 2
            print("\nall specs parse and load")
            return 0
        n = harvest_specs(a.project, a.set_name, a.entry or None)
        print("\nscan_init: %d taint entry(s) installed. Each one is the engine's GUESS -- read its"
              " header, then correct:" % n)
        print("    1. which parameters carry attacker data (taint: pointee / value / none)")
        print("    2. the relations between them -- against the REAL call site")
        print("    3. sizes pinned, contents symbolic")
        print("  then: scan_init.py %s --validate-specs" % a.project)
        return 0

    src = os.path.abspath(a.project)
    if not os.path.isdir(src):
        die("%s is not a directory" % src)
    name = a.name or os.path.basename(src.rstrip("/"))
    if not re.match(r"^[A-Za-z0-9_.-]+$", name):
        die("profile name %r is not a safe directory name" % name)
    pdir = os.path.join(PROFILES, name)
    if os.path.exists(pdir) and not a.force:
        die("%s already exists (use --force to overwrite)" % pdir)

    # ---- 0. what does this project already have a history of?
    hlir_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    hist = prior_work(name, hlir_root)
    if hist:
        print("\n" + "=" * 78, file=sys.stderr)
        print("scan_init: THIS PROJECT HAS BEEN LOOKED AT BEFORE -- read this before choosing entries.",
              file=sys.stderr)
        for where, what in hist[:20]:
            print("  %-18s %s" % (where, what), file=sys.stderr)
        if len(hist) > 20:
            print("  ... and %d more" % (len(hist) - 20), file=sys.stderr)
        print("An earlier run's ATTACK SURFACE is the first candidate entry set, not a footnote: on\n"
              "libgit2 a confirmed real defect sat in a path the next setup did not scan at all.",
              file=sys.stderr)
        print("=" * 78 + "\n", file=sys.stderr)
    else:
        print("scan_init: no earlier mention of '%s' in DESIGN.md, memory, reports or the CVE corpus."
              % name, file=sys.stderr)

    # ---- 1. compile_commands.json
    cc = find_compile_commands(src)
    if not cc and a.build != "skip":
        mode = a.build if a.build != "auto" else detect_build(src)
        if not mode:
            die("no build system recognised in %s and no compile_commands.json found; "
                "produce one yourself and re-run with --build skip" % src)
        run_preprocess(mode, src, None)
        cc = find_compile_commands(src)
    if not cc:
        print("scan_init: no compile_commands.json -- the profile will carry no extracted flags "
              "and every -I/-D has to be written by hand.", file=sys.stderr)
        flags = dict(units=0, includes=collections.Counter(), defines=collections.Counter(),
                     std=collections.Counter(), others=collections.Counter())
    else:
        print("scan_init: reading %s" % cc)
        flags = extract_flags(cc, src)
        print("scan_init: %d translation unit(s)" % flags["units"])

    n = max(1, flags["units"])
    keep_inc = [(p, c) for p, c in flags["includes"].most_common() if c / n >= a.min_share]
    keep_def = [(d, c) for d, c in flags["defines"].most_common() if c / n >= a.min_share]
    drop_inc = [(p, c) for p, c in flags["includes"].most_common() if c / n < a.min_share]
    drop_def = [(d, c) for d, c in flags["defines"].most_common() if c / n < a.min_share]

    # ---- 2. write the profile
    os.makedirs(os.path.join(pdir, "harness"), exist_ok=True)
    os.makedirs(os.path.join(pdir, "stub"), exist_ok=True)
    entry_fn = "%s_entry" % re.sub(r"[^A-Za-z0-9_]", "_", name)
    entries = a.entry or ([entry_fn] if a.mode == "harness" else ["TODO_pick_a_real_function"])

    def q(s):
        """A YAML double-quoted scalar. The backslash has to be escaped BEFORE the quote, or a value
        that already contains one produces a file this script's own reader cannot parse.

        Measured on libgit2, whose build passes -DCLAR_FIXTURE_PATH="/path/to/tests/resources/":
        the old version emitted `"\\"/path/\\""`, i.e. a backslash followed by an unescaped quote,
        and the generated profile died in yaml.safe_load. A generator that emits a file it cannot
        read back is worse than one that refuses: the error surfaces later, somewhere else, as the
        project's problem."""
        return '"%s"' % s.replace("\\", "\\\\").replace('"', '\\"')

    lines = []
    lines.append("# %s -- generated by scan_init.py. status: draft until a human finishes it." % name)
    lines.append("name: %s" % name)
    lines.append("upstream: TODO")
    lines.append("internal: false")
    lines.append("")
    lines.append("# A profile in `draft` is REFUSED by scan_profile.py. Flip it to `runnable` only once")
    lines.append("# the harness body exists, the entries are chosen from the real dispatch code, and")
    lines.append("# NOTES.md answers its headings.")
    lines.append("status: draft")
    lines.append("")
    lines.append("source:")
    lines.append("  env: %s_SRC" % re.sub(r"[^A-Za-z0-9]", "_", name).upper())
    lines.append("  default: %s" % os.path.relpath(src, pdir))
    lines.append("  kind: git")
    lines.append("")
    lines.append("flags:")
    if flags["std"]:
        lines.append("  std: %s" % flags["std"].most_common(1)[0][0])
    lines.append("  include:")
    for p, c in keep_inc:
        lines.append("    - %s   # %d/%d units" % (q(rel_to(p, src)), c, n))
    lines.append("    - %s" % q("$PROFILE/stub"))
    if keep_def:
        lines.append("  define:")
        for d, c in keep_def:
            k, _, v = d.partition("=")
            lines.append("    %s: %s   # %d/%d units" % (k, q(v) if v else 1, c, n))
    lines.append("  extra: [-Wno-everything]")
    if drop_inc or drop_def:
        lines.append("  # BELOW THE %.0f%% SHARE THRESHOLD -- per-file quirks, not project flags." % (100 * a.min_share))
        lines.append("  # Promote one only when a scan actually needs it, and say why in NOTES.md.")
        for p, c in drop_inc[:12]:
            lines.append("  #   -I %s   (%d/%d)" % (rel_to(p, src), c, n))
        for d, c in drop_def[:12]:
            lines.append("  #   -D %s   (%d/%d)" % (d, c, n))
    lines.append("")
    lines.append("engine:")
    lines.append("  link: true          # without it every file is a SEPARATE scan target (CHECKLIST #2)")
    lines.append("  runs: 20000")
    lines.append("  timeout: 600")
    lines.append("  label: %s          # the taint label; --seed-bytes keys on THIS, not on a parameter name" % a.label)
    if a.ctx_names:
        lines.append("  ctx_names: %s" % q(a.ctx_names))
        lines.append("  # ^ a regex over parameter NAMES. It is the blunt instrument: on yara it matched")
        lines.append("  #   macho's `object` and missed ELF's `elf_obj`, so the two halves of one validation")
        lines.append("  #   were not comparable. Prefer `taint: none` on the named parameter in specs/.")
    lines.append("")
    lines.append("# Hand-corrected TAINT ENTRIES (--spec-dir). Each specs/<function>.yaml replaces what the")
    lines.append("# engine would synthesise: which parameters carry attacker data, the relations between")
    lines.append("# them, and which are context objects the caller owns.")
    lines.append("specs: specs")
    lines.append("")
    lines.append("harness:")
    if a.mode == "harness":
        lines.append("  files: [harness/%s_harness.c]" % name)
    else:
        lines.append("  files: []   # bare-entry scan: --entry names a library function directly and the")
        lines.append("              # engine synthesises the entry contract from its signature.")
    lines.append("")
    lines.append("link:")
    lines.append("  files: []           # TODO: the translation units the entry needs. MISSING IS AN ERROR.")
    lines.append("  files_optional: []")
    lines.append("")
    lines.append("entry_sets:")
    lines.append("  default:")
    lines.append("    description: TODO")
    lines.append("    entry: [%s]" % ", ".join(entries))
    lines.append("")
    lines.append("# docs/SCAN_SETUP_CHECKLIST.md -- these four do NOT make a scan fail on their own.")
    lines.append("# Written here, they are checked on every run instead of when someone remembers.")
    lines.append("expect:")
    lines.append('  entries: ">0"           # the harness could not call the function at all')
    lines.append('  blocks_visited: ">0"    # the entry never executed')
    lines.append('  checks_queried: ">0"    # CHECKLIST #3 -- no UB check was ever asked about')
    lines.append("  opaque_calls: empty     # CHECKLIST #1 -- an unmodelled external CUTS THE TAINT")
    open(os.path.join(pdir, "profile.yaml"), "w").write("\n".join(lines) + "\n")

    # ---- 3. harness skeleton + notes
    if a.mode == "harness":
        hp = os.path.join(pdir, "harness", "%s_harness.c" % name)
        open(hp, "w").write(HARNESS_SKELETON % dict(name=name, entry=entries[0]))
    fn_notes = []
    for d, c in keep_def[:10]:
        fn_notes.append("- `-D%s` (%d/%d units) -- TODO: load-bearing, or just noise?" % (d, c, n))
    if not fn_notes:
        fn_notes.append("TODO -- no compile_commands.json was available, so every flag is hand-written.")
    import datetime
    prior_txt = ("\n".join("* `%s` -- %s" % (w, x) for w, x in hist)
                 if hist else "None found in DESIGN.md, memory, the reports or the CVE corpus.")
    open(os.path.join(pdir, "NOTES.md"), "w").write(NOTES_SKELETON % dict(
        name=name, date=datetime.date.today().isoformat(), prior=prior_txt,
        out=os.path.relpath(src, pdir), flagnotes="\n".join(fn_notes)))

    # ---- taint-entry discovery, into the profile where it will be read
    cand = os.path.join(pdir, "ENTRY_CANDIDATES.md")
    try:
        subprocess.run([sys.executable, os.path.join(hlir_root, "scripts", "scan_entries.py"),
                        src, "--out", cand, "--top", "60"], check=True)
    except Exception as exc:                      # discovery is an aid; its failure must not lose the profile
        print("scan_init: entry discovery failed (%s) -- %s not written" % (exc, cand), file=sys.stderr)
        cand = None

    print("\nscan_init: wrote %s" % pdir)
    print("  profile.yaml   status: draft  (scan_profile.py will refuse to run it)")
    if a.mode == "harness":
        print("  harness/%s_harness.c   SKELETON -- returns 0, so blocks_visited will be 0" % name)
    print("  NOTES.md       skeleton, every heading is a question")
    if cand:
        print("  ENTRY_CANDIDATES.md   evidence-ranked taint entries -- the `fuzz` rows are the")
        print("                        project's OWN statement of its attack surface; skipping one")
        print("                        needs a reason in NOTES.md")
    print("\nnext:")
    print("  1. fill the harness body; build it natively with ASan and make it crash on a known input")
    print("  2. choose entries from the real dispatch code, not from a name grep")
    print("  3. fill link.files")
    print("  4. answer NOTES.md, then set status: runnable")
    print("  5. python3 scripts/scan_profile.py %s default" % name)
    print("  6. python3 scripts/scan_report.py <out>   then   scan_advise.py <out>")
    return 0


if __name__ == "__main__":
    sys.exit(main())

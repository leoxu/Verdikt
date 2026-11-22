#!/usr/bin/env python3
"""Run a saved scan profile (scan-profiles/<name>/profile.yaml).

Why this exists. Everything a scan of a real project needs beyond the source tree -- the harness, the stub
headers, the include/define flags, which files go in the --link set, the entry names, the per-project externs
document, the budget -- used to live in an ad-hoc shell script next to a worktree, and the REASONS lived only
in a memory note. Re-scanning the same project six weeks later meant reconstructing all of it. A profile is
that configuration, written down once, in the scanner's own tree, so it is versioned alongside the engine it
was tuned against.

The source tree is NOT part of a profile. `source:` only says where to look for it, and --src overrides that:
the code can live anywhere.

The part that is easy to miss: `expect:`. docs/SCAN_SETUP_CHECKLIST.md lists three setup failures that do not
make a scan fail -- they make it quietly degrade into a weaker analysis while the verdict prints as usual.
Written as gates here, the runner checks them every time instead of waiting for someone to remember.
"""
import argparse
import json
import os
import re
import shlex
import subprocess
import sys

try:
    import yaml
except ImportError:
    sys.exit("scan_profile: PyYAML is required (pip install pyyaml)")

HLIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hlir_scanlib as L  # noqa: E402

# The gates used to live here, which meant they ran only for a scan that went through a profile.
# yara v4.6.0 (2026-11-13) was a bare hlir-scan run: `opaque_calls: [__builtin_bswap32 x301]` went
# unevaluated because the only code that could evaluate it was in this file. They now live in
# hlir_scanlib so scan_report.py can apply them to ANY report.
cmp_expr = L.cmp_expr
check_gates = L.check_gates


def die(msg):
    sys.exit("scan_profile: " + msg)


def find_profile(name):
    for base in ("scan-profiles", "scan-profiles/_internal"):
        p = os.path.join(HLIR, base, name)
        if os.path.isfile(os.path.join(p, "profile.yaml")):
            return p
    die("no profile '%s' (looked in scan-profiles/ and scan-profiles/_internal/)" % name)


def subst(value, vars_):
    """$SRC / $PROFILE / $HLIR and -D parameters, in strings and nested containers."""
    if isinstance(value, str):
        out = value
        for k, v in vars_.items():
            out = out.replace("$" + k, str(v))
        return out
    if isinstance(value, list):
        return [subst(v, vars_) for v in value]
    if isinstance(value, dict):
        return {k: subst(v, vars_) for k, v in value.items()}
    return value


def resolve_vars(prof, prof_dir, overrides):
    """`vars:` are extra directories the profile needs that are NOT part of it: a cmake build directory
    holding a generated config header, a second checkout, a seed corpus. Same resolution order as the source
    tree -- an explicit --set, then an environment variable, then the profile's suggested default -- so the
    profile never hard-codes a path on one machine."""
    out = {}
    for name, spec in (prof.get("vars") or {}).items():
        if name in overrides:
            continue
        spec = spec or {}
        if spec.get("env") and os.environ.get(spec["env"]):
            path = os.environ[spec["env"]]
        elif spec.get("default"):
            path = os.path.join(prof_dir, spec["default"])
        else:
            die("var $%s has no default; pass --set %s=..." % (name, name))
        path = os.path.abspath(path)
        if spec.get("must_exist", True) and not os.path.exists(path):
            hint = " (set $%s or pass --set %s=...)" % (spec["env"], name) if spec.get("env") else \
                   " (pass --set %s=...)" % name
            die("$%s -> '%s' does not exist%s" % (name, path, hint))
        out[name] = path
    return out


def resolve_source(prof, prof_dir, override):
    src = prof.get("source") or {}
    if override:
        path = override
    elif src.get("env") and os.environ.get(src["env"]):
        path = os.environ[src["env"]]
    elif src.get("default"):
        path = os.path.join(prof_dir, src["default"])
    else:
        die("profile has no source: and no --src was given")
    path = os.path.abspath(path)
    if not os.path.isdir(path):
        hint = " (set $%s or pass --src)" % src["env"] if src.get("env") else " (pass --src)"
        die("source tree '%s' does not exist%s" % (path, hint))
    return path


def build_command(prof, entry_set, vars_, src, prof_dir, defines_in, extra):
    binary = os.environ.get("HLIR_SCAN", os.path.join(HLIR, "build", "hlir-scan"))
    if not os.path.isfile(binary):
        die("hlir-scan not built at %s (set $HLIR_SCAN)" % binary)
    cmd = [binary]

    # --- engine options: a plain map, so a new hlir-scan flag needs no change here. `runs: 8000` becomes
    #     `--runs 8000`; `link: true` becomes `--link`; underscores in a key become dashes.
    engine = dict(prof.get("engine") or {})
    engine.update(entry_set.get("engine") or {})
    for k, v in engine.items():
        flag = "--" + str(k).replace("_", "-")
        if v is True:
            cmd.append(flag)
        elif v is False or v is None:
            continue
        elif isinstance(v, list):
            for item in v:
                cmd += [flag, str(subst(item, vars_))]
        else:
            cmd += [flag, str(subst(v, vars_))]

    # --- entries
    for e in entry_set.get("entry") or []:
        cmd += ["--entry", str(e)]

    # --- extra engine flags that belong to THIS SET, not to the project.
    #
    # `--init-fn` is the case that forced this: which initialiser an entry needs is part of what the
    # set IS, and leaving it on the command line means the next person runs the same set name and
    # gets a different scan. libgit2 has no ELF constructor, so without git_libgit2_init its global
    # allocator table is never installed -- the `noinit` set exists to measure exactly that, and the
    # two sets can only be compared if each carries its own flags rather than the caller remembering
    # them.
    for x in subst(entry_set.get("args") or [], vars_):
        cmd.append(str(x))

    # --- the project's own statement about its externals (hlir-scan --externs)
    if prof.get("externs"):
        ext = subst(prof["externs"], vars_)
        if not os.path.isabs(ext):
            cand = os.path.join(prof_dir, ext)
            ext = cand if os.path.exists(cand) else os.path.join(HLIR, ext)
        cmd += ["--externs", ext]
    # Hand-written entry specs. `specs:` is profile-wide; an entry set may override it with `spec_dir:`, because
    # one set often needs a pinned object size that would be wrong for the others (scan-profiles/libxml2).
    spec_dir = entry_set.get("spec_dir") or prof.get("specs")
    if spec_dir:
        # ABSOLUTE, against the profile directory. hlir-scan runs from wherever the user is, so a relative
        # `--spec-dir specs` resolves to nothing, the generated specs are used instead, and the scan degrades
        # silently -- on scan-profiles/libxml2 that turned a replay-confirmed CVE into a one-run "safe".
        sd = subst(spec_dir, vars_)
        cmd += ["--spec-dir", sd if os.path.isabs(sd) else os.path.join(prof_dir, sd)]

    # --- clang flags
    flags = prof.get("flags") or {}
    if flags.get("std"):
        cmd.append("-std=" + str(flags["std"]))
    for inc in subst(flags.get("include") or [], vars_):
        cmd.append("-I" + inc)
    defines = dict(flags.get("define") or {})
    defines.update(entry_set.get("define") or {})
    defines.update(defines_in)
    for k, v in defines.items():
        cmd.append("-D%s=%s" % (k, subst(str(v), vars_)) if v is not None and v != "" else "-D" + k)
    for h in subst(flags.get("pre_include") or [], vars_):
        cmd += ["-include", h]
    cmd += [str(x) for x in subst(flags.get("extra") or [], vars_)]

    # --- inputs: harness first, then the link set. A REQUIRED file that is missing is an error; an OPTIONAL
    #     one is a file that only exists in some versions of the tree (tcpdump's checksum.c, expat's xcs.c).
    #     An entry set may replace BOTH lists: one target can need a different harness and a different slice of
    #     the project (scan-profiles/libxml2's CVE-2024-56171 set needs the whole library through
    #     compile_commands.json, where the other set needs three files). Overriding `engine` and `define` but
    #     not these would have forced a second profile for the same project.
    inputs = []
    harness_src = entry_set.get("harness") or prof.get("harness") or {}
    link = entry_set.get("link") if entry_set.get("link") is not None else (prof.get("link") or {})
    for h in subst(harness_src.get("files") or [], vars_):
        p = h if os.path.isabs(h) else os.path.join(prof_dir, h)
        if not os.path.isfile(p):
            die("harness file '%s' is missing" % p)
        inputs.append(p)
    for f in subst(link.get("files") or [], vars_):
        p = f if os.path.isabs(f) else os.path.join(src, f)
        if not os.path.isfile(p):
            die("link file '%s' is missing from the source tree" % p)
        inputs.append(p)
    for f in subst(link.get("files_optional") or [], vars_):
        p = f if os.path.isabs(f) else os.path.join(src, f)
        if os.path.isfile(p):
            inputs.append(p)
    if not inputs and not (engine.get("compile-commands") or engine.get("compile_commands")
                           or engine.get("makefile")):
        die("the profile names no input files and no build system to take them from "
            "(harness.files / link.files, or engine.compile-commands / engine.makefile)")
    return cmd + extra + inputs


# ------------------------------------------------------------------ preflight: the thing must BUILD first
def preflight(cmd, inputs, prof, keep=False):
    """Compile every unit with a real compiler and partially link them, BEFORE scanning.

    A scan setup is a small C program that nobody ever compiles, and that is where its defects hide. Three
    real ones, all of which a compiler would have caught in a second:

      * a printer whose declaration does not match the harness's call -- hlir-scan reports this as
        `0 entries`, with no hint that a signature is wrong (tcpdump CVE-2017-5202/5486);
      * a variadic declared with different arity in two translation units -- the whole module failed to
        lower and nine targets sat at `blocks=0` for weeks (DESIGN.md §22.422);
      * a file added to the link set whose definitions are silently IGNORED because the harness already
        defines those names. A real linker calls that `multiple definition`; hlir-scan prints a `note:`.

    So: compile errors and duplicate definitions are HARNESS BUGS and stop the scan. Undefined symbols are
    NOT -- they are the externals the scan will model or assume opaque, and they are printed so the list can
    be compared against what the report ends up claiming.
    """
    import tempfile
    cc = os.environ.get("HLIR_PREFLIGHT_CC") or (prof.get("build") or {}).get("cc") or "cc"
    # every clang-style flag from the command line, which is everything that is not an hlir-scan option
    cflags = [c for c in cmd[1:] if c not in inputs and
              (c.startswith("-I") or c.startswith("-D") or c.startswith("-std=") or c.startswith("--target=")
               or c.startswith("-W") or c.startswith("-f"))]
    for i, c in enumerate(cmd):
        if c == "-include" and i + 1 < len(cmd):
            cflags += ["-include", cmd[i + 1]]
    cflags += [str(x) for x in ((prof.get("build") or {}).get("extra") or [])]

    # Flags that live in compile_commands.json, not on the command line. Without this the preflight compiles
    # every cmake/`make -n` profile with almost no -I and fails on the project's first header -- which is what
    # the nginx and Fluent Bit profiles did, aborting before the scan ran at all. hlir-scan reads this database
    # per file; the check that is supposed to catch harness defects has to compile the same way or it only ever
    # tests profiles that spell their flags out (DESIGN.md Sec.22.455).
    ccdb, ccdb_first = {}, None
    for i, c in enumerate(cmd):
        if c == "--compile-commands" and i + 1 < len(cmd) and os.path.exists(cmd[i + 1]):
            try:
                for e in json.load(open(cmd[i + 1])):
                    d = e.get("directory") or "."
                    argv = e.get("arguments") or shlex.split(e.get("command") or "")
                    fl, j = [], 0
                    while j < len(argv):
                        a = argv[j]
                        if a in ("-I", "-isystem", "-include") and j + 1 < len(argv):
                            fl += [a, os.path.join(d, argv[j + 1]) if not os.path.isabs(argv[j + 1]) else argv[j + 1]]
                            j += 2
                            continue
                        if a.startswith("-I") and len(a) > 2:
                            v = a[2:]
                            fl.append("-I" + (v if os.path.isabs(v) else os.path.join(d, v)))
                        elif a.startswith("-D") or a.startswith("-std=") or a.startswith("-fwrapv") or a.startswith("-fno-strict"):
                            fl.append(a)
                        j += 1
                    ccdb[os.path.realpath(os.path.join(d, e.get("file", "")))] = fl
            except Exception as ex:
                print("preflight: could not read %s (%s); using command-line flags only" % (cmd[i + 1], ex))
    if ccdb:
        for f in inputs:
            if os.path.realpath(f) in ccdb:
                ccdb_first = ccdb[os.path.realpath(f)]
                break

    tmp = tempfile.mkdtemp(prefix="hlir_preflight_")
    objs, bad = [], []
    for i, f in enumerate(inputs):
        o = os.path.join(tmp, "u%d.o" % i)
        # Same rule the engine uses: this file's own flags, else a neighbour's. The harness is never in the
        # database -- it is our file, not the project's.
        extra = ccdb.get(os.path.realpath(f)) or ccdb_first or []
        r = subprocess.run([cc, "-c", "-o", o, f] + extra + cflags, capture_output=True, text=True)
        if r.returncode:
            bad.append((f, (r.stderr or r.stdout).strip()))
        else:
            objs.append(o)
    if bad:
        print("\npreflight: %d of %d unit(s) DO NOT COMPILE against this tree." % (len(bad), len(inputs)))
        for f, err in bad:
            print("\n  %s" % f)
            for line in err.splitlines()[:12]:
                print("    " + line)
        print("\nThis is a defect in the scan setup, not in the engine. hlir-scan recovers from errors a real\n"
              "compiler refuses, and then reports `0 entries` or `blocks=0` with no hint of the cause. Fix the\n"
              "harness (or the flags) and run again.")
        return False

    link = os.path.join(tmp, "all.o")
    r = subprocess.run(["ld", "-r", "-o", link] + objs, capture_output=True, text=True)
    if r.returncode:
        print("\npreflight: the units COMPILE but do not LINK.")
        for line in (r.stderr or r.stdout).strip().splitlines()[:20]:
            print("  " + line)
        print("\n`multiple definition` here means the harness defines a name the project also defines. At link\n"
              "time the FIRST definition wins and the project's real one is silently ignored, so the scan\n"
              "measures the harness instead of the program. Remove the harness's copy (or compile it out).")
        return False

    und = subprocess.run(["nm", "--undefined-only", "--format=posix", link], capture_output=True, text=True)
    names = sorted({l.split()[0] for l in und.stdout.splitlines() if l.split()})
    print("preflight: %d unit(s) compile and link; %d undefined symbol(s) the scan must model or assume "
          "opaque" % (len(inputs), len(names)))
    if names:
        print("  " + ", ".join(names[:24]) + (" ..." if len(names) > 24 else ""))

    # Conditional compilation: code behind an `#if defined(FEATURE)` the build did not turn on is not
    # in the binary at all, so the scan cannot enter it -- and a function whose only interesting path is
    # #ifdef'd out reads as clean, or vacuous, for a reason that is nothing to do with its safety. This
    # is NOT a harness defect (the build is valid), so it is a WARNING, never a stop. brotli's
    # serialized-dictionary parser was 53 lines behind BROTLI_EXPERIMENTAL and the dict scan sat at
    # checks_queried=0 until the flag was added (DESIGN §22.5xx).
    try:
        excluded = L.inactive_conditionals(inputs, cflags, cc)
    except Exception as ex:
        excluded = []
        print("preflight: conditional-compilation check skipped (%s)" % ex)
    if excluded:
        infn = [r for r in excluded if r["kind"] == "in-function"]
        print("\npreflight: WARNING -- %d code region(s) are EXCLUDED by conditional compilation; the scan\n"
              "cannot enter them. If an entry's attack surface lives behind one, a clean/vacuous verdict\n"
              "means the code was #ifdef'd out, not that it is safe. Add the -D to reach it, or record why\n"
              "the default build is the one that matters." % len(excluded))
        for r in excluded[:12]:
            loc = "%s:%d" % (os.path.basename(r["file"]), r["line"])
            where = ("in %s()" % r["function"]) if (r["kind"] == "in-function" and r.get("function")) else "file scope"
            tag = " [path inside a function body]" if r["kind"] == "in-function" else ""
            print("    %-28s  #if needs %-24s  %s, %d line(s)%s"
                  % (loc, r["macro"], where, r["span"], tag))
        if len(excluded) > 12:
            print("    ... and %d more" % (len(excluded) - 12))
        if infn:
            print("  %d of these sit INSIDE a function body: a path within an entry/called function that no\n"
                  "  seed can take in this build." % len(infn))

    if not keep:
        for f in objs + [link]:
            try:
                os.remove(f)
            except OSError:
                pass
        try:
            os.rmdir(tmp)
        except OSError:
            pass
    return True


def main():
    ap = argparse.ArgumentParser(description="run a saved scan profile")
    ap.add_argument("profile")
    ap.add_argument("entry_set", nargs="?", help="which entry set (omit to list them)")
    ap.add_argument("--src", help="the source tree (overrides source: in the profile)")
    ap.add_argument("-D", dest="params", action="append", default=[], metavar="K=V",
                    help="a preprocessor define the entry set declares (repeatable)")
    ap.add_argument("--set", dest="sets", action="append", default=[], metavar="K=V",
                    help="fill a $K placeholder used elsewhere in the profile, e.g. which file to link "
                         "(repeatable); unlike -D this does not become a -D on the command line")
    ap.add_argument("--out", help="write the JSON report here (default: a temp file)")
    ap.add_argument("--dry-run", action="store_true", help="print the command and stop")
    ap.add_argument("--no-gates", action="store_true", help="run but do not check expect:")
    ap.add_argument("--no-build", action="store_true",
                    help="skip the preflight build (it is the check that catches harness defects; only "
                         "skip it for a tree that genuinely cannot be compiled here)")
    # Unrecognised arguments are passed straight through to hlir-scan, so a one-off
    # `--runs 40000 --timeout 600` needs no profile edit.
    a, passthrough = ap.parse_known_args()

    # The scan writes straight to the fd while this wrapper's print() is block-buffered when stdout is
    # a file, so a redirected run showed hlir-scan's output first and everything this script says --
    # the command, the preflight result -- only at exit. On a 900s scan that reads as "the preflight
    # did not run". Line-buffer so the order on screen is the order of events.
    try:
        sys.stdout.reconfigure(line_buffering=True)
    except Exception:  # noqa: BLE001  (not a tty, or an old Python)
        pass

    prof_dir = find_profile(a.profile)
    with open(os.path.join(prof_dir, "profile.yaml")) as f:
        prof = yaml.safe_load(f) or {}

    # A profile scan_init.py generated is a SKELETON: the harness returns 0, the link set is empty and
    # the entries are placeholders. Running one produces a clean-looking report of nothing at all, which
    # is the exact failure mode docs/SCAN_SETUP_CHECKLIST.md exists to stop. The flip to `runnable` is a
    # human saying the harness body, the entry choice and NOTES.md are done.
    if str(prof.get("status", "runnable")).strip() == "draft":
        die("profile '%s' is status: draft -- scan_init.py generated it and a human has not finished it.\n"
            "  Fill the harness body, choose entries from the real dispatch code, fill link.files,\n"
            "  answer NOTES.md, then set status: runnable in %s/profile.yaml"
            % (a.profile, prof_dir))

    sets = prof.get("entry_sets") or {}
    if not a.entry_set:
        print("profile %s (%s)" % (prof.get("name", a.profile), prof_dir))
        for k, v in sets.items():
            need = (v.get("params") or [])
            print("  %-16s %s%s" % (k, v.get("description", ""),
                                    ("   [needs %s]" % ", ".join(need)) if need else ""))
        return 0
    if a.entry_set not in sets:
        die("profile has no entry set '%s' (have: %s)" % (a.entry_set, ", ".join(sets) or "none"))
    eset = sets[a.entry_set]

    def kvs(items, flag):
        out = {}
        for p in items:
            if "=" not in p:
                die("%s expects K=V, got '%s'" % (flag, p))
            k, v = p.split("=", 1)
            out[k] = v
        return out

    params = kvs(a.params, "-D")       # become -DK=V AND $K
    placeholders = kvs(a.sets, "--set")  # become $K only
    missing = [p for p in (eset.get("params") or []) if p not in params and p not in placeholders]
    if missing:
        die("entry set '%s' needs -D or --set for: %s" % (a.entry_set, ", ".join(missing)))

    src = resolve_source(prof, prof_dir, a.src)
    vars_ = {"SRC": src, "PROFILE": prof_dir, "HLIR": HLIR}
    vars_.update(resolve_vars(prof, prof_dir, placeholders))
    vars_.update(placeholders)
    vars_.update(params)
    extra = [x for x in passthrough if x != "--"]

    out = a.out or os.path.join("/tmp", "hlir_profile_%s_%d.json" % (a.profile.replace("/", "_"), os.getpid()))
    cmd = build_command(prof, eset, vars_, src, prof_dir, params, extra + ["--format", "json", "--output", out])

    print("# profile %s / %s" % (a.profile, a.entry_set))
    print("# source  %s" % src)
    print(" ".join(shlex.quote(c) for c in cmd))
    if a.dry_run:
        return 0

    # The scan setup must BUILD before it is allowed to produce a verdict.
    if not a.no_build and (prof.get("build") or {}).get("enabled", True):
        files = [c for c in cmd if c.endswith(".c") or c.endswith(".cc") or c.endswith(".cpp")]
        if files and not preflight(cmd, files, prof):
            return 3

    rc = subprocess.call(cmd)
    if not os.path.isfile(out):
        print("scan_profile: the scan produced no report (exit %d)" % rc, file=sys.stderr)
        return rc or 1
    with open(out) as f:
        report = json.load(f)

    # An entry set may replace the gates too. `branch_coverage > 10` is right for an entry whose denominator is
    # three files and wrong for one whose denominator is a whole library, and a gate that is wrong for a set is
    # worse than no gate: it fails every run and stops being read (DESIGN.md §22.430).
    expect = (eset.get("expect") if eset.get("expect") is not None else prof.get("expect")) or {}
    if a.no_gates or not expect:
        print("scan_profile: %d entries, no gates checked" % len(report.get("entries") or []))
        return rc
    failures, lines = check_gates(report, expect)
    print("\n--- acceptance gates (docs/SCAN_SETUP_CHECKLIST.md) ---")
    for l in lines:
        print(l)
    if failures:
        print("\nFAILED %d gate(s):" % len(failures))
        for f in failures:
            print("  * " + f)
        print("\nA failed gate does not mean the scan crashed. It means the scan quietly degraded into a\n"
              "weaker analysis than the profile claims, and its verdicts are worth less than they look.")
        return 2
    print("\nall gates passed")
    return rc


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""Shared report handling for the scan pre/post tooling.

Three callers:
  scan_profile.py   runs a profile, then checks the gates below
  scan_report.py    the POST-SCAN harness: gates + degradation signals + aggregation, on ANY report
  scan_advise.py    the DIAGNOSIS harness: what to do next, and whether another round is even useful

Why this module exists: the gates used to live inside scan_profile.py, so they ran only when a
scan went through a profile. The yara v4.6.0 scan (2026-11-13) was a bare `hlir-scan` invocation
with no profile, and `opaque_calls: [__builtin_bswap32 x301]` -- a gate that has existed since
2026-11-06 and would have failed the run on the spot -- was never evaluated. A gate reachable only
from one entry point is a gate that is not there.
"""
import json
import os
import re
import subprocess

# The four gates docs/SCAN_SETUP_CHECKLIST.md argues for, applied when a report carries no profile
# of its own. `opaque_calls: empty` is checklist #1, `checks_queried: ">0"` is #3; the other two are
# the two ways a setup produces a clean-looking report having executed nothing.
DEFAULT_GATES = {
    "entries": ">0",
    "blocks_visited": ">0",
    "checks_queried": ">0",
    "opaque_calls": "empty",
}


# ---------------------------------------------------------------- loading
def load_report(path):
    """Accept an hlir-scan --out directory, a combined scan.json, or one per-entry report.

    Returns (report_dict, source_path). A directory prefers scan.json (all entries of the run);
    reports/*.json are merged only when scan.json is absent, so an --out dir written by an older
    run still works."""
    if os.path.isdir(path):
        comb = os.path.join(path, "scan.json")
        if os.path.exists(comb):
            with open(comb) as f:
                return json.load(f), comb
        rdir = os.path.join(path, "reports")
        if os.path.isdir(rdir):
            entries = []
            for name in sorted(os.listdir(rdir)):
                if name.endswith(".json"):
                    with open(os.path.join(rdir, name)) as f:
                        entries.extend(json.load(f).get("entries") or [])
            if entries:
                return {"tool": "hlir", "entries": entries}, rdir
        raise SystemExit("hlir_scanlib: no scan.json and no reports/*.json under %s" % path)
    with open(path) as f:
        return json.load(f), path


def entry_name(e):
    return e.get("function", "?")


def opaque_split(e):
    """opaque_calls holds two different blind spots and conflating them hides the smaller one.
    Returns (externals, indirects): a body-less function vs a function POINTER with no known target."""
    names = sorted({c.get("function", "?") for c in (e.get("opaque_calls") or [])})
    ind = [n for n in names if n.startswith("__hlir_unknown_indirect")]
    return [n for n in names if n not in ind], ind


def declared_skips(e):
    """The externals this project has EXAMINED and left opaque on purpose (hlir-scan --externs).

    The engine records them as a `skipped_external` assumption, not inside `opaque_calls` -- which
    holds the externals that were actually CALLED, justified or not. The gate used to read only the
    latter, so a profile that did exactly what the gate's own message asks ("justify them in the
    profile's externs document") still failed it. Measured on libssh: nine externals justified in
    externs.yaml, three of them called, gate red with no action left to take.

    The reason text carries the file, and the file is the record; what matters here is which names
    were decided, so they can be reported as decisions and not counted as omissions. A skip is still
    a claim about the program -- it is just a claim someone made deliberately and wrote down."""
    out = set()
    for a in e.get("assumptions") or []:
        if a.get("category") != "skipped_external":
            continue
        # the engine renders them as `name (reason); name (reason); ...`
        for n in re.findall(r"([A-Za-z_][A-Za-z0-9_]*) \(", a.get("text") or ""):
            out.add(n)
    return out


def opaque_counts(e):
    return {c.get("function", "?"): c.get("calls", 0) for c in (e.get("opaque_calls") or [])}


def lower_failures(e):
    """Functions that are opaque ONLY because the FRONTEND could not lower them (name -> reason).

    A failed lowering (an unsupported construct -- e.g. an SSE `__m128` vector initializer) is emitted
    as a body-less declaration, so it goes opaque exactly like a genuine missing external and lands in
    `opaque_calls`. But the two are different problems and the gate must not conflate them: the source
    IS present here, so the fix is a compile flag (-U__SSE2__ for SIMD) or frontend support, NOT a model
    or a link line. Measured on openjpeg: opj_t1_clbl_decode_processor and 15 others in dwt/mct/t1 were
    opaque for this reason, and the bare name sent the reader looking for a missing external that did not
    exist. The engine now emits a `lower_failures` list so this is self-diagnosing."""
    return {c.get("function", "?"): c.get("reason", "unsupported construct")
            for c in (e.get("lower_failures") or [])}


def checks_queried(e):
    return sum(c.get("queried", 0) for c in (e.get("checks") or []))


def checks_reached(e):
    return sum(c.get("reached", 0) for c in (e.get("checks") or []))


def is_positive(e):
    return str(e.get("verdict", "")).startswith("safe")


def incomplete_codes(e):
    return [i.get("code", "?") for i in (e.get("incomplete") or [])]


# ---------------------------------------------------------------- gates
def cmp_expr(expr, value):
    m = re.match(r"^\s*(>=|<=|>|<|==|=)\s*(-?\d+(?:\.\d+)?)\s*$", str(expr))
    if not m:
        return None, "cannot parse '%s'" % expr
    op, n = m.group(1), float(m.group(2))
    ok = {">": value > n, ">=": value >= n, "<": value < n, "<=": value <= n,
          "==": value == n, "=": value == n}[op]
    return ok, "%s (want %s)" % (value, expr)


def check_gates(report, expect):
    """Returns (failures, lines). Evaluated PER ENTRY: a gate that holds on average and fails on the
    one entry that matters is not a gate."""
    failures, lines = [], []
    entries = report.get("entries") or []
    if "entries" in expect:
        ok, how = cmp_expr(expect["entries"], len(entries))
        lines.append("  entries: %s" % how)
        if ok is False:
            failures.append("entries %s" % how)
    for e in entries:
        fn = entry_name(e)
        # ALWAYS, gated or not: a scan reported without its branch coverage is a statement about what
        # was never executed, dressed as a result. The five counts say which part of the gap is even
        # addressable -- only `open` is a budget question (DESIGN.md Sec.22.429); `global_init` is an
        # `init:`/G2 question and answering it with budget is pure waste (DESIGN.md Sec.22.465).
        cv = e.get("coverage") or {}
        if cv.get("measured"):
            br, bv = cv.get("branches_reachable", 0), cv.get("branches_visited", 0)
            lines.append("  %-28s branch coverage: %d/%d (%.0f%%)  not covered: open=%d unsat=%d const=%d unreached=%d global_init=%d"
                         % (fn, bv, br, 100.0 * bv / max(1, br), cv.get("branch_miss_open", 0),
                            cv.get("branch_miss_unsat", 0), cv.get("branch_miss_const", 0),
                            cv.get("branch_miss_unreached", 0), cv.get("branch_miss_global_init", 0)))
            bie = cv.get("branches_in_entered", 0)
            if bie:
                lines.append("  %-28s   of branches in entered functions: %d/%d (%.0f%%)   functions entered: %d/%d"
                             % (fn, bv, bie, 100.0 * bv / max(1, bie),
                                cv.get("functions_entered", 0), cv.get("functions_reachable", 0)))
        keys = list(expect.items())
        if "unknown_indirect" not in expect:
            keys.append(("unknown_indirect", "report-only"))
        for key, want in keys:
            if key == "entries":
                continue
            ext, ind = opaque_split(e)
            if want == "report-only":
                lines.append("  %-28s unknown_indirect: %s   (reported, not gated)" % (fn, ind or "[]"))
                continue
            if key in ("opaque_calls", "unknown_indirect"):
                names = ind if key == "unknown_indirect" else ext
                allowed = [] if want in ("empty", [], None) else list(want)
                decided = declared_skips(e) if key == "opaque_calls" else set()
                bad = [n for n in names if n not in allowed and n not in decided]
                lines.append("  %-28s %s: %s" % (fn, key, names or "[]"))
                # Reported on their own line, never merged into the one above: "examined and judged
                # irrelevant" and "nobody has looked" are different claims (DESIGN.md Sec.22.379), and
                # the whole point of writing the reasons down is that they stay visible.
                seen_decided = sorted(n for n in names if n in decided)
                if seen_decided:
                    lines.append("  %-28s %s" % (fn, "opaque BY DECISION (externs): " + ", ".join(seen_decided)))
                if bad and key == "opaque_calls":
                    lf = lower_failures(e)
                    lowered_bad = [(n, lf[n]) for n in bad if n in lf]
                    ext_bad = [n for n in bad if n not in lf]
                    if lowered_bad:
                        # The source IS present; the frontend could not lower it. Different problem, different fix.
                        desc = ", ".join("%s (%s)" % (n, why) for n, why in lowered_bad)
                        failures.append("%s: opaque because the FRONTEND could not lower them -- %s. The source is "
                                        "present; this is NOT a missing external, so a model/link line will not help. "
                                        "Fix with a compile flag (e.g. -U__SSE__ -U__SSE2__ ... for SIMD/__m128 code) "
                                        "so the scalar path is analysed, or add frontend support for the construct." % (fn, desc))
                    if ext_bad:
                        failures.append("%s: unexplained external(s) %s -- model them, link the file that "
                                        "defines them, or justify them in the profile's externs document "
                                        "(SCAN_SETUP_CHECKLIST #1)" % (fn, ext_bad))
                elif bad:
                    failures.append("%s: indirect call(s) with no known target %s -- the module that defines "
                                    "them is not in the scan, or nothing took their address where the "
                                    "frontend could see it" % (fn, bad))
                continue
            val = None
            cov, met = e.get("coverage") or {}, e.get("metrics") or {}
            if key == "branch_coverage":  # percentage, so a profile does not have to know the denominator
                val = 100.0 * cov.get("branches_visited", 0) / max(1, cov.get("branches_reachable", 0))
            elif key in cov:
                val = cov[key]
            elif key in met:
                val = met[key]
            elif key == "checks_queried":
                val = checks_queried(e)
            elif key == "findings":
                val = len([f for f in (e.get("findings") or []) if not f.get("warning")])
            else:
                failures.append("%s: unknown gate '%s'" % (fn, key))
                continue
            ok, how = cmp_expr(want, val)
            lines.append("  %-28s %s: %s" % (fn, key, how))
            if ok is False:
                failures.append("%s: %s %s" % (fn, key, how))
            elif ok is None:
                failures.append("%s: gate %s: %s" % (fn, key, how))
    return failures, lines


# ---------------------------------------------------------------- degradation signals
# Everything here is a way a scan stays green while measuring less than it claims. None of these
# makes hlir-scan exit non-zero; that is the whole point of collecting them in one place.
def degradations(e):
    """Returns a list of dicts {code, severity, text, evidence}. `severity` is one of
    'blocking' (the verdict means nothing), 'degraded' (the verdict is weaker than it reads),
    'note' (disclosed narrowing, in the report's own assumptions)."""
    out = []
    cv, met = e.get("coverage") or {}, e.get("metrics") or {}
    ext, ind = opaque_split(e)
    counts = opaque_counts(e)
    cq, cr = checks_queried(e), checks_reached(e)
    codes = incomplete_codes(e)

    if cv.get("blocks_visited", 0) == 0:
        out.append(dict(code="blocks_zero", severity="blocking",
                        text="the entry never executed a single block",
                        evidence="blocks_visited=0"))
    if ext:
        out.append(dict(code="opaque_calls", severity="blocking",
                        text="body-less, model-less external(s): each returns an ARBITRARY UNTAINTED "
                             "result and writes nothing, so the call cuts the taint chain and every "
                             "check downstream is decided concretely (SCAN_SETUP_CHECKLIST #1)",
                        evidence=", ".join("%s x%d" % (n, counts.get(n, 0)) for n in ext)))
    if ind:
        out.append(dict(code="unknown_indirect", severity="degraded",
                        text="function pointer(s) with no known target: the module defining them is not "
                             "in the scan, or nothing took their address where the frontend could see it",
                        evidence=", ".join(ind)))
    if is_positive(e) and cq == 0 and cr > 0:
        out.append(dict(code="vacuous_positive", severity="blocking",
                        text="a POSITIVE verdict that asked the solver nothing: every check was decided "
                             "concretely on the path that reached it, so this says 'these concrete values "
                             "did not fail', not 'no input makes them fail' (SCAN_SETUP_CHECKLIST #3)",
                        evidence="verdict=%s checks_reached=%d checks_queried=0" % (e.get("verdict"), cr)))
    elif cq == 0 and cr > 0:
        out.append(dict(code="checks_never_queried", severity="degraded",
                        text="no check was ever handed to the solver; the verdict is not positive so this "
                             "is not a false proof, but nothing was symbolically tested either",
                        evidence="checks_reached=%d checks_queried=0" % cr))
    if "frontier_dropped" in codes:
        out.append(dict(code="frontier_dropped", severity="blocking",
                        text="search branches were discarded when the frontier overflowed: the exploration "
                             "is not exhaustive, so `safe` is not a conclusion this run supports",
                        evidence=[i.get("detail") for i in (e.get("incomplete") or [])
                                  if i.get("code") == "frontier_dropped"]))
    if e.get("reads_incomplete"):
        out.append(dict(code="reads_incomplete", severity="degraded",
                        text="the global-read set is incomplete", evidence="reads_incomplete=true"))
    for c in codes:
        if c in ("time_budget", "symbolic_time_budget", "run_limit"):
            out.append(dict(code=c, severity="note",
                            text="the run hit a budget wall; whether more budget would help is decided by "
                                 "branch_miss_open, NOT by this line",
                            evidence="incomplete: %s; branch_miss_open=%d" % (c, cv.get("branch_miss_open", 0))))
    for a in (e.get("assumptions") or []):
        if a.get("category") in ("checks_never_symbolic", "synthesis_frontier"):
            out.append(dict(code=a.get("category"), severity="note",
                            text=(a.get("text") or "")[:200], evidence=""))
    return out


def finding_rows(e):
    """(kind, function, warning, confirmed, id) per finding, with no judgement attached."""
    rows = []
    for f in (e.get("findings") or []):
        fid = f.get("id", "")
        fn = fid.split("@")[-1].split(":")[0] if "@" in fid else entry_name(e)
        rows.append(dict(kind=f.get("kind", "?"), function=fn, warning=bool(f.get("warning")),
                         in_prologue=bool(f.get("in_prologue")), id=fid,
                         message=f.get("message", "")))
    return rows


# ---------------------------------------------------------------- conditional compilation
# A path inside an entry/tainted function that sits behind `#if defined(FEATURE)` is UNREACHABLE
# when FEATURE is not in the build's -D set: the scan enters the function, the guarded branch is
# simply gone, and the run looks clean -- or vacuous -- for a reason that has nothing to do with the
# program's safety. brotli's serialized-dictionary parser was exactly this (DESIGN Sec.22.5xx): 53
# lines behind BROTLI_EXPERIMENTAL, absent from the default build, so BrotliSharedDictionaryAttach's
# SERIALIZED branch `return`ed immediately and the dict scan sat at checks_queried=0 until the flag
# was added. The engine cannot tell "the parser is safe" from "the parser was #ifdef'd out". So warn.

# Guards that are legitimately off on this host or toolchain: platform/compiler selection, not a
# feature gate whose absence hides attack surface. Flagging them is pure noise.
COND_PLATFORM_OFF = {
    "__cplusplus", "_WIN32", "_WIN64", "WIN32", "WIN64", "_MSC_VER", "_MSC_FULL_VER", "_MSVC_LANG",
    "__MINGW32__", "__MINGW64__", "__APPLE__", "__MACH__", "_WIN32_WCE", "__BORLANDC__", "__CYGWIN__",
    "_AIX", "__sun", "__hpux", "__ANDROID__", "_M_IX86", "_M_X64", "_M_ARM", "_M_ARM64",
    "__EMSCRIPTEN__", "__wasm__", "__native_client__", "_MSC_EXTENSIONS",
}

_COND_DIRECTIVE = re.compile(r'^\s*#\s*(if|ifdef|ifndef|elif|else|endif)\b(.*)$')
_COND_DEFINED = re.compile(r'defined\s*\(?\s*([A-Za-z_]\w*)\s*\)?')
_COND_FUNC_HEAD = re.compile(r'^[A-Za-z_][\w \t\*]*\b[A-Za-z_]\w*\s*\([^;]*\)\s*$')


def _tu_macros(path, cflags, cc):
    """Every macro defined at the END of preprocessing `path`: command line + builtins + headers.

    Using the real preprocessor (not a guess) is what makes this precise -- a FEATURE macro set by an
    included config header shows up here, so we never warn about a guard that is actually on."""
    try:
        r = subprocess.run([cc, "-dM", "-E", path] + list(cflags),
                           capture_output=True, text=True, timeout=180)
    except Exception:
        return None
    if r.returncode:
        return None
    out = set()
    for line in r.stdout.splitlines():
        m = re.match(r'#define\s+([A-Za-z_]\w*)', line)
        if m:
            out.add(m.group(1))
    return out


def _eval_guard(kind, expr, macros):
    """Return (value, absent_feature_macros). value True/False, or None when we cannot tell.

    Only the common feature-gate forms are decided; anything with arithmetic, comparisons or nested
    macros we do not understand returns None and is left alone. Low false positives beat completeness
    for a warning."""
    expr = expr.split("//")[0].split("/*")[0].strip()
    if kind == "ifdef":
        m = expr.strip()
        if re.fullmatch(r'[A-Za-z_]\w*', m):
            return (m in macros, [] if m in macros else [m])
        return (None, [])
    if kind == "ifndef":
        m = expr.strip()
        if re.fullmatch(r'[A-Za-z_]\w*', m):
            return (m not in macros, [])   # absence makes it TRUE -> normal/include-guard, never flagged
        return (None, [])
    # #if / #elif: handle defined()-only boolean expressions
    names = _COND_DEFINED.findall(expr)
    stripped = _COND_DEFINED.sub("D", expr)
    # bare `#if MACRO` (single identifier, no operators) -> treat as defined?
    if not names and re.fullmatch(r'[A-Za-z_]\w*', stripped.strip()):
        m = stripped.strip()
        if m.isupper() or "_" in m:
            return (m in macros, [] if m in macros else [m])
        return (None, [])
    # the expression must be only D / ! / && / || / () / whitespace to be safely evaluable
    if not names or not re.fullmatch(r'[D!&|()\s]*', stripped):
        return (None, [])
    pyexpr = stripped
    absent = [n for n in names if n not in macros]
    # substitute each defined() left-to-right with its truth
    def repl(_m, it=iter(n in macros for n in names)):
        return "1" if next(it) else "0"
    pyexpr = re.sub(r'D', repl, pyexpr).replace("&&", " and ").replace("||", " or ").replace("!", " not ")
    try:
        val = bool(eval(pyexpr, {"__builtins__": {}}, {}))
    except Exception:
        return (None, [])
    return (val, absent if not val else [])


def _enclosing_function(lines, idx):
    """Nearest preceding function-definition-ish header above line index idx (0-based). Best effort."""
    depth_seen = False
    for j in range(idx, -1, -1):
        t = lines[j].rstrip()
        if t.endswith("{") and _COND_FUNC_HEAD.match(t[:-1].strip() + ""):
            m = re.search(r'([A-Za-z_]\w*)\s*\([^;]*\)\s*\{?\s*$', t)
            if m:
                return m.group(1)
        m = re.match(r'^[A-Za-z_][\w \t\*]*\b([A-Za-z_]\w*)\s*\(', t)
        if m and j + 1 < len(lines):
            return m.group(1)
    return None


def inactive_conditionals(files, cflags, cc="cc"):
    """List code regions excluded by conditional compilation because a feature macro is not defined.

    Each record: file, line (of the #if), macro(s), function (enclosing, best effort), kind
    ('in-function' when the guard sits inside a function body, else 'top-level'), lines (region size).
    Only regions that (a) are controlled by an absent, non-platform feature macro and (b) actually
    contain code are reported -- a declarations/typedef-only block is not attack surface."""
    records = []
    # cflags are already compiler flags; `cc -dM -E` tolerates -W/-f/-std and needs the -I/-D/-include
    # ones, so pass them through intact rather than filter and risk splitting an `-include <path>` pair.
    cflags = list(cflags)
    for f in files:
        if not (f.endswith(".c") or f.endswith(".cc") or f.endswith(".cpp") or f.endswith(".h")):
            continue
        macros = _tu_macros(f, cflags, cc)
        if macros is None:
            continue
        try:
            lines = open(f, errors="replace").read().splitlines()
        except Exception:
            continue
        # stack of frames: dict(active=bool parent-active, taken=any branch active yet,
        #   this_val, start=line idx, guard_absent=[], from_feature=bool)
        stack = []
        brace = 0   # brace depth over lines that are actually compiled in (active)
        def parent_active():
            return all(fr["this_val"] for fr in stack) if stack else True
        for i, ln in enumerate(lines):
            m = _COND_DIRECTIVE.match(ln)
            if not m:
                if parent_active():
                    brace += ln.count("{") - ln.count("}")
                continue
            d, rest = m.group(1), m.group(2)
            if d in ("if", "ifdef", "ifndef"):
                pa = parent_active()
                val, absent = _eval_guard(d, rest, macros)
                this_val = bool(val) and pa if val is not None else (None if pa else False)
                feature = (val is False and pa and absent and
                           not any(a in COND_PLATFORM_OFF for a in absent))
                stack.append(dict(start=i, this_val=(this_val if this_val is not None else False),
                                  unknown=(val is None), absent=absent, feature=bool(feature),
                                  brace_at=brace))
            elif d == "elif":
                if stack:
                    fr = stack[-1]
                    pa = all(x["this_val"] for x in stack[:-1]) if len(stack) > 1 else True
                    val, absent = _eval_guard("if", rest, macros)
                    fr["this_val"] = bool(val) and pa if val is not None else False
            elif d == "else":
                if stack:
                    fr = stack[-1]
                    pa = all(x["this_val"] for x in stack[:-1]) if len(stack) > 1 else True
                    fr["this_val"] = (not fr["this_val"]) and pa
                    fr["feature"] = False  # the #else half is not the feature-off region we flag
            elif d == "endif":
                if stack:
                    fr = stack.pop()
                    if fr["feature"]:
                        body = lines[fr["start"] + 1:i]
                        has_code = any(_is_code_line(b) for b in body)
                        if has_code:
                            fn = _enclosing_function(lines, fr["start"])
                            records.append(dict(
                                file=f, line=fr["start"] + 1,
                                macro=", ".join(fr["absent"]),
                                function=fn,
                                kind="in-function" if fr["brace_at"] > 0 else "top-level",
                                span=i - fr["start"] + 1))
    return records


def _is_code_line(s):
    t = s.strip()
    if not t or t.startswith(("//", "/*", "*", "#")):
        return False
    # a line that opens a block, returns, assigns, or calls -- i.e. executable, not a bare prototype
    if "{" in t or t.startswith(("return", "if", "for", "while", "switch", "do", "goto", "case")):
        return True
    if "(" in t and ")" in t and not t.endswith(";"):
        return True   # function-definition header
    if "=" in t and t.endswith(";"):
        return True
    if t.endswith(";") and "(" in t:
        return True   # a call statement
    return False

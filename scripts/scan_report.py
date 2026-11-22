#!/usr/bin/env python3
"""scan_report.py -- the POST-SCAN harness.

Reads an hlir-scan report and answers one question: IS THIS RUN WORTH BELIEVING?
It does three things and deliberately stops there:

  1. the acceptance gates of docs/SCAN_SETUP_CHECKLIST.md, on ANY report (a profile is optional)
  2. the degradation signals -- every way a scan stays green while measuring less than it claims
  3. a plain COUNT of the findings, by kind and by function

It does NOT judge whether a finding is real. That needs the setup diagnosis as an input (a finding
in a function whose caller was never entered, in a run whose taint was cut by an opaque call, is not
the same evidence as the same finding in a clean run), so it lives in scan_advise.py.

  scan_report.py <out-dir | scan.json | report.json> [--expect k=v ...] [--format text|json]
  scan_report.py --diff <before> <after>

Exit: 0 all gates passed, 2 a gate failed, 1 the report could not be read.
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hlir_scanlib as L  # noqa: E402

SEV_ORDER = {"blocking": 0, "degraded": 1, "note": 2}
SEV_MARK = {"blocking": "!!", "degraded": " !", "note": "  "}


def bucket_line(cv):
    o, u, c, n, g = (cv.get("branch_miss_open", 0), cv.get("branch_miss_unsat", 0),
                     cv.get("branch_miss_const", 0), cv.get("branch_miss_unreached", 0),
                     cv.get("branch_miss_global_init", 0))
    s = "open=%d unsat=%d const=%d unreached=%d global_init=%d" % (o, u, c, n, g)
    # The one inference this file is willing to make, because it is arithmetic rather than judgement:
    # only `open` responds to budget (DESIGN.md Sec.22.429). Everything else is a setup question.
    if o == 0 and (n + c) > 0:
        s += "\n      -> open=0: MORE BUDGET CANNOT HELP. The gap is setup, not search."
    return s


def report_text(rep, src, expect, out):
    entries = rep.get("entries") or []
    out.append("scan_report: %s -- %d entry(s)" % (src, len(entries)))

    out.append("\n=== gates (docs/SCAN_SETUP_CHECKLIST.md) ===")
    failures, lines = L.check_gates(rep, expect)
    out.extend(lines)
    if failures:
        out.append("\nFAILED %d gate(s):" % len(failures))
        for f in failures:
            out.append("  - %s" % f)
        out.append("\nA failed gate does not mean the scan crashed. It means the scan quietly degraded")
        out.append("into a weaker analysis while the verdict printed exactly as usual.")
    else:
        out.append("  all gates passed")

    out.append("\n=== degradation signals ===")
    any_sig = False
    for e in entries:
        sigs = sorted(L.degradations(e), key=lambda d: SEV_ORDER.get(d["severity"], 9))
        if not sigs:
            continue
        any_sig = True
        out.append("  @%s  [%s]" % (L.entry_name(e), e.get("verdict", "?")))
        for d in sigs:
            out.append("   %s %-22s %s" % (SEV_MARK.get(d["severity"], "  "), d["code"], d["text"]))
            if d.get("evidence"):
                out.append("        evidence: %s" % d["evidence"])
    if not any_sig:
        out.append("  none")

    out.append("\n=== coverage ===")
    for e in entries:
        cv = e.get("coverage") or {}
        if not cv.get("measured"):
            continue
        met = e.get("metrics") or {}
        bv, br, bie = (cv.get("branches_visited", 0), cv.get("branches_reachable", 0),
                       cv.get("branches_in_entered", 0))
        out.append("  @%s" % L.entry_name(e))
        out.append("      branches %d/%d reachable (%.0f%%)   %d/%d in entered functions (%.0f%%)"
                   % (bv, br, 100.0 * bv / max(1, br), bv, bie, 100.0 * bv / max(1, bie)))
        out.append("      functions entered %d/%d   runs=%s paths=%s"
                   % (cv.get("functions_entered", 0), cv.get("functions_reachable", 0),
                      met.get("runs", "?"), met.get("paths", "?")))
        out.append("      %s" % bucket_line(cv))
        ne = cv.get("not_entered") or []
        if ne:
            out.append("      not entered (%d): %s" % (len(ne), ", ".join(ne)))

    out.append("\n=== findings (counts only -- see scan_advise.py for confirmation) ===")
    tot = 0
    for e in entries:
        rows = L.finding_rows(e)
        tot += len(rows)
        if not rows:
            continue
        by = {}
        for r in rows:
            by.setdefault((r["kind"], r["function"], r["warning"]), 0)
            by[(r["kind"], r["function"], r["warning"])] += 1
        out.append("  @%s  %d finding(s)" % (L.entry_name(e), len(rows)))
        for (kind, fn, warn), n in sorted(by.items(), key=lambda kv: -kv[1]):
            out.append("      %-22s x%-4d @%s%s" % (kind, n, fn, "   [warning]" if warn else ""))
    if tot == 0:
        out.append("  none")
    return failures


def do_diff(a_path, b_path, out):
    ra, sa = L.load_report(a_path)
    rb, sb = L.load_report(b_path)
    ia = {L.entry_name(e): e for e in (ra.get("entries") or [])}
    ib = {L.entry_name(e): e for e in (rb.get("entries") or [])}
    out.append("scan_report --diff\n  BEFORE %s\n  AFTER  %s" % (sa, sb))
    for fn in sorted(set(ia) & set(ib)):
        ea, eb = ia[fn], ib[fn]
        ca, cb = ea.get("coverage") or {}, eb.get("coverage") or {}
        ma, mb = ea.get("metrics") or {}, eb.get("metrics") or {}
        out.append("\n  @%s   %s -> %s" % (fn, ea.get("verdict"), eb.get("verdict")))
        out.append("      %-22s %8s %8s %8s" % ("", "BEFORE", "AFTER", "delta"))
        for label, va, vb in [
                ("branches_visited", ca.get("branches_visited", 0), cb.get("branches_visited", 0)),
                ("miss_const", ca.get("branch_miss_const", 0), cb.get("branch_miss_const", 0)),
                ("miss_unreached", ca.get("branch_miss_unreached", 0), cb.get("branch_miss_unreached", 0)),
                ("miss_open", ca.get("branch_miss_open", 0), cb.get("branch_miss_open", 0)),
                ("functions_entered", ca.get("functions_entered", 0), cb.get("functions_entered", 0)),
                ("runs", ma.get("runs", 0), mb.get("runs", 0)),
                ("paths", ma.get("paths", 0), mb.get("paths", 0)),
                ("findings", len(ea.get("findings") or []), len(eb.get("findings") or [])),
        ]:
            d = vb - va
            out.append("      %-22s %8d %8d %+8d" % (label, va, vb, d))
        # Counts alone cannot answer the question a precondition fix asks: WHICH finding went away.
        # After yara's `data: min 1 -> 4` the count moved 16 -> 15 and identifying the one that
        # disappeared took a hand-written script. Sites are (kind, function, line).
        def sites(e):
            out = {}
            for f in (e.get("findings") or []):
                k = (f.get("kind", "?"), f.get("function", "?"),
                     (f.get("location") or {}).get("line", "?"), bool(f.get("warning")))
                out[k] = out.get(k, 0) + 1
            return out
        fa, fb = sites(ea), sites(eb)
        gone = sorted(k for k in fa if k not in fb)
        new = sorted(k for k in fb if k not in fa)
        chg = sorted(k for k in fa if k in fb and fa[k] != fb[k])
        if gone or new or chg:
            out.append("      findings by site:")
            for k in gone:
                out.append("        - GONE  %-20s @%s:%s%s x%d"
                           % (k[0], k[1], k[2], "  [warning]" if k[3] else "", fa[k]))
            for k in new:
                out.append("        + NEW   %-20s @%s:%s%s x%d"
                           % (k[0], k[1], k[2], "  [warning]" if k[3] else "", fb[k]))
            for k in chg:
                out.append("        ~ COUNT %-20s @%s:%s  %d -> %d" % (k[0], k[1], k[2], fa[k], fb[k]))
        elif (ea.get("findings") or eb.get("findings")):
            out.append("      findings by site: unchanged")
        na, nb = set(ca.get("not_entered") or []), set(cb.get("not_entered") or [])
        if na - nb:
            out.append("      newly ENTERED:     %s" % ", ".join(sorted(na - nb)))
        if nb - na:
            out.append("      newly NOT entered: %s" % ", ".join(sorted(nb - na)))
        oa = set(L.opaque_split(ea)[0])
        ob = set(L.opaque_split(eb)[0])
        if oa != ob:
            out.append("      opaque_calls: %s -> %s" % (sorted(oa) or "[]", sorted(ob) or "[]"))
    only = (set(ia) ^ set(ib))
    if only:
        out.append("\n  entries on one side only: %s" % ", ".join(sorted(only)))


def main():
    ap = argparse.ArgumentParser(description="post-scan harness: gates, degradation signals, counts")
    ap.add_argument("target", help="hlir-scan --out dir, scan.json, or a per-entry report.json")
    ap.add_argument("--diff", metavar="AFTER", help="compare TARGET (before) with AFTER")
    ap.add_argument("--expect", action="append", default=[],
                    help="override a gate, e.g. --expect checks_queried='>0' (repeatable). "
                         "Without any, the four defaults of SCAN_SETUP_CHECKLIST are used.")
    ap.add_argument("--no-gates", action="store_true")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    a = ap.parse_args()

    out = []
    if a.diff:
        do_diff(a.target, a.diff, out)
        print("\n".join(out))
        return 0

    try:
        rep, src = L.load_report(a.target)
    except Exception as exc:  # noqa: BLE001
        print("scan_report: cannot read %s: %s" % (a.target, exc), file=sys.stderr)
        return 1

    expect = {} if a.no_gates else dict(L.DEFAULT_GATES)
    for kv in a.expect:
        if "=" not in kv:
            print("scan_report: --expect wants K=V, got '%s'" % kv, file=sys.stderr)
            return 1
        k, v = kv.split("=", 1)
        expect[k.strip()] = v.strip()

    if a.format == "json":
        entries = rep.get("entries") or []
        failures, _ = L.check_gates(rep, expect)
        print(json.dumps({
            "source": src,
            "gate_failures": failures,
            "entries": [{
                "function": L.entry_name(e),
                "verdict": e.get("verdict"),
                "degradations": L.degradations(e),
                "coverage": e.get("coverage") or {},
                "findings": L.finding_rows(e),
            } for e in entries],
        }, indent=2))
        return 2 if failures else 0

    failures = report_text(rep, src, expect, out)
    print("\n".join(out))
    return 2 if failures else 0


if __name__ == "__main__":
    sys.exit(main())

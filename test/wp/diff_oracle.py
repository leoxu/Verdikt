#!/usr/bin/env python3
# seam③ differential oracle (docs/BACKWARD_WP_DESIGN.md §3.3, BACKWARD_WP_P0_PLAN.md).
#
# Forward (hlir-scan) and backward (hlir-wp-probe --solve) are two independent decisions about the SAME check sites.
# They must not disagree where both have an opinion:
#   - forward reported a finding at a site that backward proves SAFE(unsat)  -> CONTRADICTION: one engine is wrong.
# Everywhere else is consistent:
#   - both flag it (forward finding + backward sat): agreement on danger.
#   - backward SAFE + no forward finding: agreement on safety.
#   - backward sat + no forward finding: backward's sound over-approximation (it dropped path guards); not a conflict.
#
# This is a cross-validator: contradictions are rare and each is a real bug in one engine. It also surfaces backward
# SAFE proofs the forward run has no finding for -- candidates for bucket-1 safety (strongest when the site is one
# forward never covered, which needs per-site coverage; this driver works at finding granularity).
#
#   diff_oracle.py <hlir-scan> <hlir-wp-probe> <file.c> [--entry NAME ...] [-- <clang flags>]
import json
import os
import re
import subprocess
import sys
import tempfile

# backward check kind (from --list) -> the forward finding kinds it decides
FAMILY = {
    "check.oob": {"oob_read", "oob_write"},
    "call:memcpy": {"oob_read", "oob_write"}, "call:memmove": {"oob_read", "oob_write"},
    "call:memset": {"oob_read", "oob_write"}, "call:strncpy": {"oob_read", "oob_write"},
    "call:strncat": {"oob_read", "oob_write"}, "call:strlcpy": {"oob_read", "oob_write"},
    "call:strlcat": {"oob_read", "oob_write"}, "call:memccpy": {"oob_read", "oob_write"}, "call:bcopy": {"oob_read", "oob_write"},
    "check.ptr_arith": {"ptr_arith_oob"},
    "check.div": {"div_by_zero", "div_overflow"},
    "check.shift": {"shift_range", "shift_negative", "shift_overflow"},
    "check.sadd_ovf": {"signed_overflow"}, "check.ssub_ovf": {"signed_overflow"},
    "check.smul_ovf": {"signed_overflow"}, "check.sneg_ovf": {"signed_overflow"},
    "check.field_oob": {"field_oob"},
}


def forward_findings(scan, src, entries, clang):
    core = tempfile.NamedTemporaryFile(suffix=".core", delete=False).name
    cmd = [scan, "--format", "json", "--link", "--dump-linked", core]  # --dump-linked needs --link
    for e in entries:
        cmd += ["--entry", e]
    cmd += [src, *clang]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
    try:
        j = json.loads(p.stdout)
    except json.JSONDecodeError:
        print(f"forward scan produced no JSON (rc={p.returncode}):\n{p.stderr[-2000:]}", file=sys.stderr)
        sys.exit(2)
    # set of (basename, line, kind) forward reported as a finding
    found = set()
    entered = set()   # names of functions some forward run actually entered (coverage.entered_functions)
    covered = set()   # (basename, line) source lines some forward run actually executed (coverage.covered_lines)
    for e in j.get("entries", []):
        cov = e.get("coverage", {})
        for n in cov.get("entered_functions", []):
            entered.add(normfn(n))
        for fl in cov.get("covered_lines", []):
            f, _, ln = fl.rpartition(":")
            if ln.isdigit():
                covered.add((os.path.basename(f), int(ln)))
        for f in e.get("findings", []):
            loc = f.get("loc") or f.get("site") or {}
            # findings carry their loc inline under a loc-ish object; fall back to scanning the finding dict
            file = loc.get("file") or f.get("file")
            line = loc.get("line") or f.get("line")
            if file is None or line is None:
                # the loc is nested; find the first {file,line} pair in the finding
                for v in f.values():
                    if isinstance(v, dict) and "file" in v and "line" in v:
                        file, line = v["file"], v["line"]
                        break
            if file is not None and line is not None:
                found.add((os.path.basename(file), int(line), f.get("kind", "")))
    return core, found, entered, covered


def normfn(n):
    # backward prints @name; forward prints the core name. per-callsite clones carry a .uN suffix; the base
    # function is the same code, so a check in cbor_decref.u0 is covered iff forward entered any cbor_decref clone.
    n = n.lstrip("@")
    return re.sub(r"\.u\d+$", "", n)


def backward_verdicts(probe, core):
    p = subprocess.run([probe, "--list", "--solve", core], capture_output=True, text=True, timeout=300)
    # (basename, line) -> {kind: (verdict, funcname)}
    out = {}
    for line in p.stdout.splitlines():
        m = re.match(r"^(\S+)\t(@\S+)\t([^\t]*):(\d+)\t.*?(SAFE\(unsat\)|sat\(candidate\)|unknown|unsupported)?\s*$", line)
        if not m:
            continue
        kind, fn, file, ln, verdict = m.group(1), m.group(2), m.group(3), int(m.group(4)), m.group(5) or ""
        out.setdefault((os.path.basename(file), ln), {})[kind] = (verdict, normfn(fn))
    return out


def main():
    if len(sys.argv) < 4:
        print("usage: diff_oracle.py <hlir-scan> <hlir-wp-probe> <file.c> [--entry NAME ...] [-- clang flags]", file=sys.stderr)
        sys.exit(2)
    scan, probe, src = sys.argv[1:4]
    rest = sys.argv[4:]
    entries, clang = [], []
    expect_uncovered_min = None   # if set, fail unless the uncovered-bucket has >= this many sites
    i = 0
    while i < len(rest):
        if rest[i] == "--entry":
            entries.append(rest[i + 1]); i += 2
        elif rest[i] == "--expect-uncovered-min":
            expect_uncovered_min = int(rest[i + 1]); i += 2
        elif rest[i] == "--":
            clang = rest[i + 1:]; break
        else:
            clang.append(rest[i]); i += 1

    core, found, entered, covered = forward_findings(scan, src, entries, clang)
    verdicts = backward_verdicts(probe, core)

    contradictions, agree_danger, agree_safe, backward_over = [], 0, 0, 0
    # Two grains of the seam③ uncovered-bucket, both sound (forward's POSITIVE coverage sets; "not in" never over-claims):
    #   fn-grain   : backward SAFE in a function no run ENTERED.
    #   block-grain: backward SAFE on a LINE no run EXECUTED -- subsumes fn-grain and also catches a guarded branch
    #                inside an entered function that the search never took. This is the finer, primary number.
    uncov_fn, uncov_blk, uncov_sites = 0, 0, []
    seen_finding_sites = set()
    for (fbase, fline, fkind) in found:
        seen_finding_sites.add((fbase, fline))
        v = verdicts.get((fbase, fline), {})
        # does backward prove SAFE a check whose family covers this forward finding kind?
        safe_fam = [k for k, (ver, fn) in v.items() if ver == "SAFE(unsat)" and fkind in FAMILY.get(k, set())]
        sat_fam = [k for k, (ver, fn) in v.items() if ver == "sat(candidate)" and fkind in FAMILY.get(k, set())]
        if safe_fam and not sat_fam:
            contradictions.append((fbase, fline, fkind, safe_fam))
        elif sat_fam:
            agree_danger += 1
    for site, kinds in verdicts.items():
        for k, (ver, fn) in kinds.items():
            if site in seen_finding_sites:
                continue
            if ver == "SAFE(unsat)":
                agree_safe += 1
                in_entered = (not entered) or (fn in entered)
                on_covered_line = (not covered) or (site in covered)
                if not in_entered:
                    uncov_fn += 1
                if not on_covered_line:          # block-grain: line no run executed (superset of fn-grain)
                    uncov_blk += 1
                    uncov_sites.append((site[0], site[1], k, fn, "fn" if not in_entered else "guard"))
            elif ver == "sat(candidate)":
                backward_over += 1

    print("=== seam③ differential oracle ===")
    print(f"forward findings: {len(found)}   backward-verdict sites: {len(verdicts)}   "
          f"forward-entered fns: {len(entered)}   covered lines: {len(covered)}")
    print(f"agree on danger (forward finding + backward sat): {agree_danger}")
    print(f"agree on safety (backward SAFE, no forward finding): {agree_safe}")
    print(f"  UNCOVERED-BUCKET, block-grain (backward SAFE on a line no run executed): {uncov_blk}")
    print(f"    of which in a function no run entered: {uncov_fn}; inside an entered fn (guarded branch): {uncov_blk - uncov_fn}")
    print(f"backward over-approx (backward sat, no forward finding -- dropped guards): {backward_over}")
    print(f"CONTRADICTIONS (backward SAFE where forward found a bug): {len(contradictions)}")
    for c in contradictions:
        print(f"  !!! {c[0]}:{c[1]} forward={c[2]} but backward proved SAFE via {c[3]}")
    if uncov_sites:
        from collections import Counter
        byfn = Counter(s[3] for s in uncov_sites)
        print("  uncovered-bucket by function (top):")
        for fn, n in byfn.most_common(12):
            print(f"    {n:4d}  @{fn}")
    os.unlink(core)
    if expect_uncovered_min is not None and uncov_blk < expect_uncovered_min:
        print(f"FAIL: uncovered-bucket (block-grain) = {uncov_blk}, expected >= {expect_uncovered_min}", file=sys.stderr)
        sys.exit(3)
    sys.exit(1 if contradictions else 0)


if __name__ == "__main__":
    main()

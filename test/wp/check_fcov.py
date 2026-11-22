#!/usr/bin/env python3
# seam③ uncovered-bucket, wired into the backward probe's own output (not just the python oracle).
# hlir-wp-probe --forward-coverage <scan.json> reads hlir-scan's coverage.covered_lines and tags each SAFE verdict
# [uncovered] / [covered], reporting "UNCOVERED-BUCKET" (SAFE on a line no forward run executed) in its summary.
# This drives both tools on bug.c and asserts: unreached_safe is never entered by the forward search, so backward's
# SAFE proof there is uncovered -- the native count must be >= 1 and must equal the number of [uncovered] tags.
#
#   check_fcov.py <hlir-scan> <hlir-wp-probe> <bug.c> [--entry NAME ...]
import os
import re
import subprocess
import sys
import tempfile

ENTRIES = ["oob_guarded", "div_zero", "add_ovf", "shift_amt", "safe_stack"]


def main():
    scan, probe, src = sys.argv[1:4]
    core = tempfile.NamedTemporaryFile(suffix=".core", delete=False).name
    js = tempfile.NamedTemporaryFile(suffix=".json", delete=False).name
    cmd = [scan, "--format", "json", "--link", "--dump-linked", core]
    for e in ENTRIES:
        cmd += ["--entry", e]
    cmd += [src]
    with open(js, "w") as f:
        p = subprocess.run(cmd, stdout=f, stderr=subprocess.PIPE, text=True, timeout=300)
    if not os.path.getsize(js):
        print(f"FAIL: forward scan produced no JSON (rc={p.returncode})\n{p.stderr[-1500:]}", file=sys.stderr)
        sys.exit(2)

    out = subprocess.run([probe, "--list", "--solve", "--forward-coverage", js, core],
                         capture_output=True, text=True, timeout=300).stdout
    m = re.search(r"UNCOVERED-BUCKET \(SAFE on a line no forward run executed\):\s*(\d+)", out)
    assert m, f"FAIL: probe did not report an uncovered-bucket summary line\n{out[-1500:]}"
    reported = int(m.group(1))
    tagged = len([l for l in out.splitlines() if l.endswith("[uncovered]")])
    assert reported >= 1, f"FAIL: uncovered-bucket = 0, expected >= 1 (unreached_safe should be uncovered)\n{out}"
    assert reported == tagged, f"FAIL: summary count {reported} != number of [uncovered] tags {tagged}"
    # the SAFE proof in unreached_safe (a function the forward search never enters) must be among the tagged ones
    assert any("unreached_safe" in l and l.endswith("[uncovered]") for l in out.splitlines()), \
        f"FAIL: unreached_safe's SAFE proof was not tagged [uncovered]\n{out}"
    os.unlink(core)
    os.unlink(js)
    print(f"  ok fcov: probe --forward-coverage reports {reported} uncovered-bucket SAFE proofs, tags match")
    print("check_fcov: uncovered-bucket wired into the probe output -- assertions passed")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""hlir-invariant gives the right verdict on the committed fixtures (test/invariant/README.md)."""
import os
import subprocess
import sys

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
tool = sys.argv[1] if len(sys.argv) > 1 else os.path.join(root, "build", "hlir-invariant")
core = os.path.join(root, "test", "invariant", "sum_to.core")
cases = [("i <= n", "inductive"), ("i < n", "not_inductive"), ("acc >= i", "not_inductive")]

fails = 0
for inv, want in cases:
    r = subprocess.run([tool, core, "--function", "sum_to", "--loop", "while1", "--inv", inv],
                       capture_output=True, text=True, timeout=300)
    got = ""
    for line in r.stdout.splitlines():
        if line.startswith("verdict: "):
            got = line[len("verdict: "):].strip()
    if got != want:
        fails += 1
        print("FAIL  %-12s expected %s, got %s" % (inv, want, got or "<no verdict>"))
        print(r.stdout.strip()[-400:] or r.stderr.strip()[-400:])
print("check_invariant: %d case(s), %d failed" % (len(cases), fails))
sys.exit(1 if fails else 0)

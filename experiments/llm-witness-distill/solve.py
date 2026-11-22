#!/usr/bin/env python3
# LLM-assisted witness distillation -- the distill + solve step.
#
# Given the backward-WP obligation "reach the gate (a^b) == MAGIC", the LLM reads target.c and DISTILLS the
# mixing loop into a self-contained SMT problem f(unknown bytes) == MAGIC. Two guards keep it honest:
#   (1) a faithful python mimic of the exact C semantics (hpy) -- used to pick a REACHABLE target and to
#   (2) cross-check that the Z3 translation (hz) computes the same value as the real C loop.
# Without the cross-check a mistranslated model silently returns a false unsat / a false witness.
#
# Requires z3 (pip install z3-solver). Run: python3 solve.py
from z3 import *

MASK = 0xFFFFFFFF

def hpy(inb):                                  # faithful mimic of target.c's loop (ground truth)
    a, b = 0x1234, 0
    for x in inb:
        a = ((a << 5) + a + x) & MASK          # a = a*33 + byte
        b = (b ^ ((a + (b >> 3)) & MASK)) & MASK
    return (a ^ b) & MASK

def hz(ins):                                   # the distilled model: C loop -> Z3 bitvector (uint32 wrap)
    a = BitVecVal(0x1234, 32)
    b = BitVecVal(0, 32)
    for x in ins:
        a = (a << 5) + a + x
        b = b ^ (a + LShR(b, 3))               # LShR = logical >>, matching unsigned C
    return a ^ b

def invert(target):
    ins = [BitVec(f"in{i}", 8) for i in range(6)]
    s = Solver()
    s.add(hz([ZeroExt(24, c) for c in ins]) == target)
    if s.check() != sat:
        return None
    m = s.model()
    return [m[ins[i]].as_long() for i in range(6)]

if __name__ == "__main__":
    # MAGIC in target.c is the loop's output for this secret input, so a preimage is guaranteed to exist.
    secret = [0x11, 0x22, 0x33, 0x44, 0x55, 0x66]
    MAGIC = hpy(secret)
    assert MAGIC == 0x370dd88f, hex(MAGIC)

    # cross-check: the Z3 model must compute the same value as the real C loop for a concrete input.
    chk = simplify(hz([BitVecVal(x, 32) for x in secret])).as_long()
    print(f"model-vs-C cross-check: {chk == MAGIC}  (z3={chk:#010x}, c={MAGIC:#010x})")
    assert chk == MAGIC, "DISTILLATION IS UNFAITHFUL -- do not trust the solve"

    w = invert(MAGIC)
    assert w is not None and hpy(w) == MAGIC
    print("WITNESS bytes:", " ".join(f"{x:02x}" for x in w))
    print("  (note: this is a DIFFERENT input than the secret -- a genuine inversion)")

    # bonus: an arbitrary target is proven UNREACHABLE (the gate is dead for 6 bytes) -- fuzzing can never
    # conclude this, and backward WP alone only says sat.
    dead = invert(0x0BADF00D)
    print(f"arbitrary target 0x0BADF00D reachable? {dead is not None}  (unsat => the gate is proven dead)")

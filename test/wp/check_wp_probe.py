#!/usr/bin/env python3
# ctest driver for the backward-WP P0 probe (docs/BACKWARD_WP_P0_PLAN.md step 5 DoD).
# Runs hlir-wp-probe on frozen linked-core fixtures and asserts the gate numbers, locking the probe's counting
# semantics (|S|, root classes, numeric vs non-numeric, loop-carried) against regression. The .core fixtures are
# frozen snapshots committed next to their .c source, so this tests the probe, not the frontend.
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def run(probe, core, extra=()):
    out = subprocess.run([probe, *extra, str(core)], capture_output=True, text=True)
    if out.returncode != 0:
        print(f"FAIL {core.name}: probe exited {out.returncode}\n{out.stderr}", file=sys.stderr)
        sys.exit(1)
    return out.stdout


def num(text, pat):
    m = re.search(pat, text)
    if not m:
        print(f"FAIL: pattern not found: {pat!r}\n--- output ---\n{text}", file=sys.stderr)
        sys.exit(1)
    return int(m.group(1))


def expect(core, got, want, what):
    if got != want:
        print(f"FAIL {core}: {what} = {got}, expected {want}", file=sys.stderr)
        sys.exit(1)
    print(f"  ok {core}: {what} = {got}")


# Each fixture asserts the properties it was built to demonstrate (see docs/BACKWARD_WP_P0_PLAN.md).
def check_parse_demo(probe):
    core = HERE / "parse_demo.core"
    t = run(probe, core)
    listing = run(probe, core, ["--list"])
    expect(core.name, num(t, r"numeric \(sliced\): (\d+)"), 11, "numeric candidates")
    # the §2.1 canonical memcpy depends on cnt (loop-carried) AND recs[i].len (a load) -> |S|=2, two root classes.
    memcpy = [l for l in listing.splitlines() if l.startswith("call:memcpy")]
    assert memcpy and "|S|=2" in memcpy[0] and "loop_carried:1" in memcpy[0] and "load:1" in memcpy[0], \
        f"FAIL parse_demo: memcpy line not as expected: {memcpy}"
    print("  ok parse_demo: memcpy |S|=2 = loop_carried + load (DESIGN §2.1, measured richer than {cnt})")
    # a[i*8+j]: offset depends on two params
    oob2 = [l for l in listing.splitlines() if l.startswith("check.oob") and "two_inputs" in l]
    assert oob2 and "|S|=2" in oob2[0] and "param:2" in oob2[0], f"FAIL parse_demo: two_inputs oob: {oob2}"
    print("  ok parse_demo: two_inputs a[i*8+j] oob |S|=2 param")


def check_sym_in_loop(probe):
    core = HERE / "sym_in_loop.core"
    t = run(probe, core)
    listing = run(probe, core, ["--list"])
    # every numeric check's S is a single loop-carried obligation (DESIGN §4.4): the WP stops at the loop boundary.
    expect(core.name, num(t, r"numeric \(sliced\): (\d+)"), 6, "numeric candidates")
    expect(core.name, num(t, r"checks whose S hits a loop-carried root:\s+(\d+)"), 6, "loop-carried checks")
    expect(core.name, num(t, r"empty S \(free safety candidate for P1\): (\d+)"), 0, "empty-S")
    for l in listing.splitlines():
        if l.startswith("check.oob") or l.startswith("check.ptr_arith"):
            assert "|S|=1" in l and "loop_carried:1" in l, f"FAIL sym_in_loop: {l}"
    print("  ok sym_in_loop: all 6 numeric checks = |S|=1 loop_carried (the §4.4 obligation, stops at loop)")


def check_stress(probe):
    core = HERE / "stress.core"
    t = run(probe, core)
    listing = run(probe, core, ["--list"])
    # the filter's failure side: |S| can reach 10, but splits cleanly by root class (seam ②).
    # many_params a[p0+..+p9]: |S|=10 all param (big but P1-trivial scalars).
    mp = [l for l in listing.splitlines() if l.startswith("check.oob") and "many_params" in l]
    assert mp and "|S|=10" in mp[0] and "param:10" in mp[0], f"FAIL stress: many_params oob: {mp}"
    # many_loads a[arr[0]+..+arr[7]]: |S|=8 all load (the genuine memory wall).
    ml = [l for l in listing.splitlines() if l.startswith("check.oob") and "many_loads" in l and "|S|=8" in l]
    assert ml and "load:8" in ml[0], f"FAIL stress: many_loads oob |S|=8 load: {ml}"
    # branchy_len memcpy: branch-merge unions both arms -> |S|=4 = param:1 + load:3.
    bl = [l for l in listing.splitlines() if l.startswith("call:memcpy") and "branchy_len" in l]
    assert bl and "|S|=4" in bl[0] and "param:1" in bl[0] and "load:3" in bl[0], f"FAIL stress: branchy memcpy: {bl}"
    print("  ok stress: many_params |S|=10 param (benign) | many_loads |S|=8 load (wall) | branchy union |S|=4")


def check_solve(probe):
    # P1 (--solve): UNSAT pruning must prove an in-bounds constant index SAFE and must NOT prove the overflow safe.
    corpus = HERE.parent / "corpus"
    good = run(probe, corpus / "CWE121_const_idx4_good.core", ["--list", "--solve"])
    bad = run(probe, corpus / "CWE121_const_idx4_bad.core", ["--list", "--solve"])
    goodline = [l for l in good.splitlines() if l.startswith("check.oob")]
    badline = [l for l in bad.splitlines() if l.startswith("check.oob")]
    assert goodline and "SAFE(unsat)" in goodline[0], f"FAIL solve: const_idx4_good not proved SAFE: {goodline}"
    assert badline and "SAFE(unsat)" not in badline[0], f"FAIL solve (UNSOUND): const_idx4_bad proved SAFE: {badline}"
    print("  ok solve: const_idx4 good -> SAFE(unsat), bad -> not safe (sound UNSAT pruning)")
    # an access into a pointer param of unknown size must NOT be provable safe (fresh size -> SAT). parse_demo is all
    # pointer-param buffers, so it must yield zero false SAFE proofs.
    pd = run(probe, HERE / "parse_demo.core", ["--solve"])
    safe = num(pd, r"SAFE \(bucket 1, violation UNSAT\):\s+(\d+)")
    assert safe == 0, f"FAIL solve (UNSOUND): parse_demo (unknown-size pointer params) proved {safe} checks SAFE"
    print("  ok solve: parse_demo pointer-param accesses -> 0 false SAFE (unknown size stays SAT)")
    # overflow family goes through the engine's shared ubViolations (no second definition). The real overflow must
    # not be proved safe, and the whole corpus must have no 'unsupported' integer check left.
    ov = run(probe, corpus / "CWE190_add_bad.core", ["--list", "--solve"])
    ovline = [l for l in ov.splitlines() if l.startswith("check.sadd_ovf")]
    assert ovline and "SAFE(unsat)" not in ovline[0], f"FAIL solve (UNSOUND): CWE190_add_bad overflow proved SAFE: {ovline}"
    uns = num(ov, r"unsupported[^:]*:\s*(\d+)")
    assert uns == 0, f"FAIL solve: CWE190_add_bad left {uns} integer checks unsupported (overflow should be solved)"
    print("  ok solve: overflow via shared ubViolations -- CWE190 bad not SAFE, 0 unsupported")
    # ptr_arith (memory-side V) + term sharing: CWE122_sym_len_bad does q = p + n into an n-byte buffer. The pointer
    # p+n is a LEGAL one-past-end address (ptr_arith n>n is UNSAT -> SAFE, and only because off and n share one symbol
    # via the memo), while the 1-byte WRITE at offset n is OOB (oob sat). This is the exact pointer-arith-vs-deref
    # distinction, and it would break if the term memo did not alias off and n.
    pa = run(probe, corpus / "CWE122_sym_len_bad.core", ["--list", "--solve"])
    paline = [l for l in pa.splitlines() if l.startswith("check.ptr_arith")]
    obline = [l for l in pa.splitlines() if l.startswith("check.oob")]
    assert paline and "SAFE(unsat)" in paline[0], f"FAIL solve: ptr_arith one-past-end not SAFE (term sharing?): {paline}"
    assert obline and "SAFE(unsat)" not in obline[0], f"FAIL solve (UNSOUND): the oob_write at offset n proved SAFE: {obline}"
    print("  ok solve: ptr_arith one-past-end SAFE, oob_write sat (pointer-arith vs deref; memo term-sharing works)")
    # step 3b path conditions: a dominating guard `if (i < 10)` on an int[10] proves the access SAFE; a loose guard
    # `if (i < 20)` must stay sat. The guard constrains the same `i` the oob offset uses (shared via the term memo).
    b1 = run(probe, HERE / "bounded1.core", ["--list", "--solve"])
    good = [l for l in b1.splitlines() if l.startswith("check.oob") and "bounded1" in l]
    bad = [l for l in b1.splitlines() if l.startswith("check.oob") and "bad1" in l]
    assert good and "SAFE(unsat)" in good[0], f"FAIL 3b: bounds-checked access not proved SAFE: {good}"
    assert bad and "SAFE(unsat)" not in bad[0], f"FAIL 3b (UNSOUND): loose guard proved SAFE: {bad}"
    print("  ok solve: step-3b path conditions -- if(i<10) a[10] SAFE, if(i<20) stays sat (tight vs loose guard)")
    # φ-aware VC-gen: a COMPOUND guard `if (i >= 0 && i < 10)` short-circuits into a block-arg phi. The phi is encoded
    # per incoming edge (reach(P) & guard => r == value_from_P), recovering r = t4 ? t8 : false = (i>=0 && i<10), so
    # the guarded access into int[10] proves SAFE; the unguarded sibling stays sat.
    cg = run(probe, HERE / "compound_guard.core", ["--list", "--solve"])
    gd = [l for l in cg.splitlines() if l.startswith("check.oob") and "@bounded" in l]
    ug = [l for l in cg.splitlines() if l.startswith("check.oob") and "@unbounded" in l]
    assert gd and all("SAFE(unsat)" in l for l in gd), f"FAIL φ: compound-guarded access not all SAFE: {gd}"
    assert ug and all("SAFE(unsat)" not in l for l in ug), f"FAIL φ (UNSOUND): unguarded access proved SAFE: {ug}"
    print("  ok solve: φ-aware VC-gen -- compound guard (i>=0 && i<10) proves SAFE, unguarded stays sat")
    # P2 loop summary: a loop-carried induction slot shares ONE symbol across its in-loop loads, so the loop guard
    # `i<10` constrains the access. for(i=0;i<10;i++) a[i] on int[10] -> SAFE; for(i<n) -> sat (n unknown).
    ls = run(probe, HERE / "loop_summary.core", ["--list", "--solve"])
    fk = [l for l in ls.splitlines() if l.startswith("check.oob") and "fill_known" in l and "in-loop" in l]
    fb = [l for l in ls.splitlines() if l.startswith("check.oob") and "fill_bad" in l and "in-loop" in l]
    assert fk and all("SAFE(unsat)" in l for l in fk), f"FAIL P2: bounded loop for(i<10) a[i] not SAFE: {fk}"
    assert fb and all("SAFE(unsat)" not in l for l in fb), f"FAIL P2 (UNSOUND): for(i<n) a[i] proved SAFE: {fb}"
    print("  ok solve: P2 loop summary -- for(i<10) a[10] SAFE, for(i<n) stays sat")
    # P2 SOUNDNESS GUARD: when the induction slot is modified mid-iteration BEFORE the access -- while(i<10){i=i+1;a[i]}
    # reaches a[10] -- the slot symbol must NOT be shared, so the access stays sat. (A naive share proves this real bug
    # safe; the oracle cannot catch it because forward misses it too, so this fixture is the only guard.)
    mm = run(probe, HERE / "loop_midmod.core", ["--list", "--solve"])
    m2 = [l for l in mm.splitlines() if l.startswith("check.oob") and "midmod2" in l and "in-loop" in l]
    assert m2 and all("SAFE(unsat)" not in l for l in m2), f"FAIL P2 (UNSOUND): while(i<10){{i++;a[i]}} proved SAFE: {m2}"
    print("  ok solve: P2 soundness -- mid-iteration-modified slot stays sat (while(i<10){i=i+1;a[i]} not proved safe)")
    # P2 accumulator summary: for(i<10) cnt+=5 gives cnt == 5*i; with i<10 the in-loop buf[cnt] into buf[100] is SAFE.
    at = run(probe, HERE / "acc_trip.core", ["--list", "--solve"])
    ti = [l for l in at.splitlines() if l.startswith("check.oob") and "trip_in" in l and "in-loop" in l]
    assert ti and all("SAFE(unsat)" in l for l in ti), f"FAIL P2-acc: trip_in (cnt=5*i, i<10) not SAFE: {ti}"
    print("  ok solve: P2 accumulator -- for(i<10) cnt+=5 => cnt<=5*i, in-loop buf[cnt] SAFE")
    # P2 accumulator SOUNDNESS: the bound must not prove a real overflow safe, a symbolic step gives no bound, and a
    # conditionally-incremented induction var is not a valid trip counter. All three in-loop accesses must stay sat.
    aa = run(probe, HERE / "acc_adversarial.core", ["--list", "--solve"])
    for fn in ("acc_ovf", "acc_sym", "acc_condiv"):
        ln = [l for l in aa.splitlines() if l.startswith("check.oob") and fn in l and "in-loop" in l]
        assert ln and all("SAFE(unsat)" not in l for l in ln), f"FAIL P2-acc (UNSOUND): {fn} in-loop access proved SAFE: {ln}"
    print("  ok solve: P2 accumulator soundness -- overflow / symbolic-step / conditional-iv all stay sat")
    # P2 post-loop exit value: a loop counter / accumulator used AFTER the loop reads the EXIT value, bounded by the trip
    # count. The post-loop access is NOT in-loop, so filter on that. SAFE: counter i<=50 into buf[64], accumulator
    # cnt<=80 into buf[100]. MUST stay sat: buffer too small (buf[40]); non-strict `<=` guard (exits at 51); and a
    # post-loop re-store of the counter (the exit-value bound must not apply).
    pl = run(probe, HERE / "loop_postloop.core", ["--list", "--solve"])
    post = lambda fn: [l for l in pl.splitlines() if l.startswith("check.oob") and fn in l and "in-loop" not in l]
    for fn in ("pl_iv_safe", "pl_acc_safe"):
        ln = post(fn)
        assert ln and all("SAFE(unsat)" in l for l in ln), f"FAIL P2-postloop: {fn} exit value not proved SAFE: {ln}"
    for fn in ("pl_iv_oob", "pl_nonstrict", "pl_restore"):
        ln = post(fn)
        assert ln and all("SAFE(unsat)" not in l for l in ln), f"FAIL P2-postloop (UNSOUND): {fn} proved SAFE: {ln}"
    print("  ok solve: P2 post-loop exit value -- counter/accumulator after loop SAFE; too-small/non-strict/re-store stay sat")
    # P2 in-loop lower bound: a SIGNED induction counter sign-extends into the offset, so the oob V's slt(offset,0)
    # disjunct kept a bounded access sat; `init0 <=s i` kills it. for(int i=0;i<50;i++) a[i] on int[50] -> SAFE. A DOWN
    # counter is not a +1 induction var, so no lower bound fires and the real a[10] OOB MUST stay sat.
    si = run(probe, HERE / "signed_idx.core", ["--list", "--solve"])
    up = [l for l in si.splitlines() if l.startswith("check.oob") and "sidx_safe" in l and "in-loop" in l]
    dn = [l for l in si.splitlines() if l.startswith("check.oob") and "sidx_down" in l and "in-loop" in l]
    assert up and all("SAFE(unsat)" in l for l in up), f"FAIL P2-lower: signed in-loop a[i] not SAFE: {up}"
    assert dn and all("SAFE(unsat)" not in l for l in dn), f"FAIL P2-lower (UNSOUND): down-counter a[i] proved SAFE: {dn}"
    print("  ok solve: P2 in-loop lower bound -- signed for(i<50) a[i] SAFE; down-counter stays sat")
    # P2 symbolic-step accumulator: cnt += s with s loop-invariant (single unconditional store) gives the exact relation
    # cnt == init0 + s*(iv-iv0). A bounded step (x<=9) then proves the in-loop buf[cnt] SAFE; an unbounded step and a
    # per-iteration-varying step (cnt += a[i]) provably cannot be bounded and MUST stay sat.
    ss = run(probe, HERE / "sym_step.core", ["--list", "--solve"])
    sf = [l for l in ss.splitlines() if l.startswith("check.oob") and "ss_safe" in l and "in-loop" in l]
    assert sf and all("SAFE(unsat)" in l for l in sf), f"FAIL P2-symstep: bounded symbolic step not SAFE: {sf}"
    for fn in ("ss_unbounded", "ss_vary"):
        ln = [l for l in ss.splitlines() if l.startswith("check.oob") and fn in l and "in-loop" in l]
        assert ln and all("SAFE(unsat)" not in l for l in ln), f"FAIL P2-symstep (UNSOUND): {fn} proved SAFE: {ln}"
    print("  ok solve: P2 symbolic-step accumulator -- bounded invariant step SAFE; unbounded / per-iteration-varying stay sat")
    # P2 interval-delta accumulator: a per-iteration-VARYING step with a structural constant bound M (a byte read M=255,
    # a mask `x & 0xF` M=15) gives cnt <= init0 + M*(iv-iv0). byte/mask into a big-enough buffer -> all in-loop oob SAFE;
    # the same byte step into a too-small buffer, and a full-width unbounded step, keep the out[cnt] access sat.
    idl = run(probe, HERE / "interval_delta.core", ["--list", "--solve"])
    ild = lambda fn: [l for l in idl.splitlines() if l.startswith("check.oob") and fn in l and "in-loop" in l]
    for fn in ("ib_byte", "ib_mask"):
        ln = ild(fn)
        assert ln and all("SAFE(unsat)" in l for l in ln), f"FAIL P2-interval: {fn} not all SAFE: {ln}"
    for fn in ("ib_small", "ib_unbounded"):
        ln = ild(fn)
        assert ln and any("SAFE(unsat)" not in l for l in ln), f"FAIL P2-interval (UNSOUND): {fn} out[cnt] proved SAFE: {ln}"
    print("  ok solve: P2 interval-delta accumulator -- bounded-varying step (byte/mask) SAFE; too-small/unbounded stay sat")
    # Interprocedural WP: a call result is bounded by the callee's sound return upper bound (all return sites const or
    # structurally bounded). buf[clamp3(k)] with clamp3 returning x&7 -> idx<=7<8 SAFE. An unbounded return (ident), a
    # too-wide bound (clamp15 returns 0..15 into buf[8]), and a callee unbounded on one path (maybe) all stay sat.
    ipc = run(probe, HERE / "interproc.core", ["--list", "--solve"])
    ip = lambda fn: [l for l in ipc.splitlines() if l.startswith("check.oob") and ("@" + fn) in l]
    assert ip("ip_safe") and all("SAFE(unsat)" in l for l in ip("ip_safe")), f"FAIL interproc: buf[clamp3(k)] not SAFE: {ip('ip_safe')}"
    for fn in ("ip_unbounded", "ip_toobig", "ip_mixed"):
        ln = ip(fn)
        assert ln and all("SAFE(unsat)" not in l for l in ln), f"FAIL interproc (UNSOUND): {fn} proved SAFE: {ln}"
    print("  ok solve: interprocedural return summary -- buf[clamp3(k)] SAFE; unbounded / too-wide / mixed-return stay sat")
    # P2 coupled-counter invariant: `while (dn) { buf[up]=..; up++; dn--; }` runs at most dn0 times, so up <= up0 + C*dn0
    # even though the guard is on dn. With dn0 bounded (interprocedural ret7()<=7) the write into buf[8] is SAFE; an
    # unbounded dn0 (the brotli shape), a too-wide bound (ret15 into buf[8]), and a down-counter re-stored mid-loop
    # (not a clean down-counter) all stay sat.
    dcc = run(probe, HERE / "down_counter.core", ["--list", "--solve"])
    wr = lambda fn: [l for l in dcc.splitlines() if l.startswith("check.oob") and ("@" + fn) in l and "loop_carried" in l]
    assert wr("dc_safe") and all("SAFE(unsat)" in l for l in wr("dc_safe")), f"FAIL coupled-counter: dc_safe write not SAFE: {wr('dc_safe')}"
    for fn in ("dc_unbounded", "dc_toobig", "dc_reset"):
        ln = wr(fn)
        assert ln and all("SAFE(unsat)" not in l for l in ln), f"FAIL coupled-counter (UNSOUND): {fn} proved SAFE: {ln}"
    print("  ok solve: P2 coupled-counter -- while(dn){buf[up++];dn--} with bounded dn0 SAFE; unbounded/too-wide/reset stay sat")
    # Interprocedural parameter-bound summary: an INTERNAL (static), non-address-taken function whose every call site
    # passes a structurally-bounded arg has that parameter bounded (sound: all callers are in-module). pick's param <= 7
    # -> t[16][i] SAFE; pick_u (one unbounded caller), pick_w (a caller passes 31 >= 16), and the EXTERNAL ext_pick all
    # stay sat. This exercises the frontend `internal` linkage marker too.
    pbd = run(probe, HERE / "param_bound.core", ["--list", "--solve"])
    pf = lambda fn: [l for l in pbd.splitlines() if l.startswith("check.oob") and ("@" + fn + "\t") in l and "param:1" in l]
    assert pf("pick") and all("SAFE(unsat)" in l for l in pf("pick")), f"FAIL param-bound: pick t[i] not SAFE: {pf('pick')}"
    for fn in ("pick_u", "pick_w", "ext_pick"):
        ln = pf(fn)
        assert ln and all("SAFE(unsat)" not in l for l in ln), f"FAIL param-bound (UNSOUND): {fn} proved SAFE: {ln}"
    print("  ok solve: interprocedural parameter bound -- internal+bounded callers SAFE; unbounded/too-wide/external stay sat")
    # Interprocedural validate-then-use: the return summary is a disjunction over return sites (exact `r==c` for a
    # constant/sentinel, `r<=M` for a bounded return). The caller's `if (c >= 0)` guard excludes the -1 sentinel, leaving
    # 0..7 -> buf[8][c] SAFE. No sentinel check stays sat; a too-wide valid range (0..31 into buf[8]) stays sat.
    vu = run(probe, HERE / "validate_use.core", ["--list", "--solve"])
    vf = lambda fn: [l for l in vu.splitlines() if l.startswith("check.oob") and ("@" + fn + "\t") in l and "call_ret" in l]
    assert vf("vu_safe") and all("SAFE(unsat)" in l for l in vf("vu_safe")), f"FAIL validate-use: guarded buf[c] not SAFE: {vf('vu_safe')}"
    for fn in ("vu_noguard", "vu_toowide"):
        ln = vf(fn)
        assert ln and all("SAFE(unsat)" not in l for l in ln), f"FAIL validate-use (UNSOUND): {fn} proved SAFE: {ln}"
    print("  ok solve: interprocedural validate-then-use -- if(classify(x)>=0) buf[c] SAFE; no-guard / too-wide stay sat")
    # Interprocedural guard-derived return bound: the return value's bound comes from a guard INSIDE the callee that
    # dominates the return (`if (n <= 16) return n;` -> r <= 16), not the return expression's structure. get_len (<=16)
    # into buf[17] and get_strict (<16 -> <=15) into buf[16] prove SAFE; the same <=16 bound into buf[16] stays sat.
    gr = run(probe, HERE / "guard_return.core", ["--list", "--solve"])
    gf = lambda fn: [l for l in gr.splitlines() if l.startswith("check.oob") and ("@" + fn + "\t") in l and "call_ret" in l]
    for fn in ("gr_safe", "gr_strict"):
        ln = gf(fn)
        assert ln and all("SAFE(unsat)" in l for l in ln), f"FAIL guard-return: {fn} not SAFE: {ln}"
    assert gf("gr_toosmall") and all("SAFE(unsat)" not in l for l in gf("gr_toosmall")), \
        f"FAIL guard-return (UNSOUND): gr_toosmall proved SAFE: {gf('gr_toosmall')}"
    print("  ok solve: interprocedural guard-derived return -- if(n<=16)return n bounds the result; buf[16] stays sat")


def main():
    if len(sys.argv) < 2:
        print("usage: check_wp_probe.py <path-to-hlir-wp-probe>", file=sys.stderr)
        sys.exit(2)
    probe = sys.argv[1]
    check_parse_demo(probe)
    check_sym_in_loop(probe)
    check_stress(probe)
    check_solve(probe)
    print("wp-probe P0+P1 fixtures: all assertions passed")


if __name__ == "__main__":
    main()

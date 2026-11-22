#!/usr/bin/env python3
"""Run a batch of candidate loop invariants through hlir-invariant and report the four numbers that decide
whether the LLM pipeline is worth building (docs/LLM_GUIDED_SE.md §5, item: "first answer one question").

The four numbers:
  1. the inductive rate -- how loaded the sieve is;
  2. how many inductive candidates are TAUTOLOGIES -- "inductive but too weak" is the real failure mode, and
     a top-1 accuracy number hides it completely. Measured, not judged: a candidate is a tautology when
     assuming its NEGATION at the loop header leaves no path at all;
  3. the distribution of failure kinds;
  4. the proposer's own bill (§6.4) -- which is why `--prompt-bytes` and `--candidates` are recorded even
     when a human wrote the candidates: the cost has to be comparable with "just double --runs".
"""
import argparse
import collections
import json
import os
import subprocess
import sys
import time


def run(tool, module, fn, loop, inv, timeout, extra):
    t0 = time.time()
    try:
        r = subprocess.run([tool, module, "--function", fn, "--loop", loop, "--inv", inv] + extra,
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", "", time.time() - t0
    verdict, detail = "", ""
    for line in r.stdout.splitlines():
        if line.startswith("verdict: "):
            verdict = line[len("verdict: "):].strip()
        if "reading:" in line and not detail:
            detail = line.split("reading:")[1].strip()
    if not verdict:
        verdict = "tool_error"
        detail = (r.stderr or r.stdout).strip().splitlines()[-1][:120] if (r.stderr or r.stdout).strip() else ""
    return verdict, detail, time.time() - t0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("candidates")
    ap.add_argument("--tool", default="build/hlir-invariant")
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--obj-size", default="32")
    ap.add_argument("--models", default="", help="a .core model file (libc.core): without it a loop that "
                                                 "calls one modelled function comes back `incomplete`")
    ap.add_argument("--out", help="write the results as JSON here")
    ap.add_argument("--llm-model", default="", help="exact model id that produced the candidates")
    ap.add_argument("--llm-tokens-in", type=int, default=0)
    ap.add_argument("--llm-tokens-out", type=int, default=0)
    ap.add_argument("--llm-cost-usd", type=float, default=0.0)
    a = ap.parse_args()

    spec = json.load(open(a.candidates))
    module = spec["module"]
    extra = ["--obj-size", a.obj_size] + (["--models", a.models] if a.models else [])
    rows, prompt_bytes = [], 0
    for lp in spec["loops"]:
        prompt_bytes += len(lp.get("note", "")) + len(lp.get("site", ""))
        for c in lp["candidates"]:
            if c.get("expect") == "unexpressible":
                rows.append(dict(loop=lp["function"] + ":" + lp["loop"], site=lp.get("site", ""),
                                 inv=c["inv"], expect=c["expect"], verdict="unexpressible",
                                 detail=c.get("why", ""), seconds=0.0, tautology=False))
                print("%-34s %-28s -> %-16s %s" % (lp["function"] + ":" + lp["loop"], c["inv"],
                                                   "unexpressible", c.get("why", "")))
                continue
            v, d, secs = run(a.tool, module, lp["function"], lp["loop"], c["inv"], a.timeout, extra)
            taut = False
            if v == "inductive":
                # A tautology is inductive and buys nothing. Assume the NEGATION at the header: if no path
                # survives, the candidate was true of every state, loop or no loop.
                nv, _, _ = run(a.tool, module, lp["function"], lp["loop"], "!(" + c["inv"] + ")", a.timeout, extra)
                taut = nv == "vacuous"
            rows.append(dict(loop=lp["function"] + ":" + lp["loop"], site=lp.get("site", ""), inv=c["inv"],
                             expect=c.get("expect", ""), verdict=v, detail=d, seconds=round(secs, 1),
                             tautology=taut))
            print("%-34s %-28s -> %-16s%s %s" % (lp["function"] + ":" + lp["loop"], c["inv"], v,
                                                 "  TAUTOLOGY" if taut else "", d))

    n = len(rows)
    by = collections.Counter(r["verdict"] for r in rows)
    ind = [r for r in rows if r["verdict"] == "inductive"]
    taut = [r for r in ind if r["tautology"]]
    agree = sum(1 for r in rows if r["expect"] and r["expect"] == r["verdict"])
    print("\n--- the four numbers ---")
    print("1. inductive            : %d/%d (%.0f%%)" % (len(ind), n, 100.0 * len(ind) / n))
    print("2. of those, TAUTOLOGIES: %d  (inductive and buys nothing -- the failure mode a pass rate hides)"
          % len(taut))
    print("   useful (inductive, not a tautology): %d/%d (%.0f%%)" % (len(ind) - len(taut), n,
                                                                      100.0 * (len(ind) - len(taut)) / n))
    print("3. verdict distribution : %s" % dict(by))
    print("   predicted correctly  : %d/%d" % (agree, n))
    print("4. checker time         : %.1fs total, %.1fs median"
          % (sum(r["seconds"] for r in rows), sorted(r["seconds"] for r in rows)[n // 2]))
    if a.llm_model:
        acc = len(ind) - len(taut)
        print("   proposer             : %s, %d in / %d out tokens, $%.4f%s"
              % (a.llm_model, a.llm_tokens_in, a.llm_tokens_out, a.llm_cost_usd,
                 ", $%.4f per ACCEPTED invariant" % (a.llm_cost_usd / acc) if acc else ""))
    else:
        print("   proposer             : NOT MEASURED -- the candidates were written by hand in this run, so "
              "there is no token count to report.\n"
              "                          `prompt context: %d bytes of loop source/notes` is the only honest "
              "proxy, and it is not a cost." % prompt_bytes)
    if a.out:
        json.dump({"rows": rows, "summary": {"n": n, "inductive": len(ind), "tautologies": len(taut),
                                             "by_verdict": dict(by), "predicted_correctly": agree},
                   "llm": {"model": a.llm_model, "tokens_in": a.llm_tokens_in,
                           "tokens_out": a.llm_tokens_out, "cost_usd": a.llm_cost_usd,
                           "measured": bool(a.llm_model)}},
                  open(a.out, "w"), indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main())

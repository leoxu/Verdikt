#!/usr/bin/env python3
"""scan_advise.py -- the DIAGNOSIS harness.

Takes a finished scan and answers the two questions a human asks next:

  1. WHAT DO I DO NOW?  rescan with more budget / write a model / fix the harness / update the
     profile / accept the result. Each action carries the evidence that produced it and the exact
     command or edit, and nothing is applied automatically.
  2. WHICH FINDINGS CAN I BELIEVE?  Finding confirmation lives here, not in scan_report.py,
     because a finding's credibility is CONDITIONAL on the setup: the same `oob_read` means one
     thing in a clean run and nothing at all in a run whose taint was cut by an opaque call.

PRECEDENCE IS THE POINT. A blocking setup defect suppresses every downstream recommendation,
because acting on coverage or on findings before fixing it is wasted work. That ordering is not a
style choice -- it is the yara v4.6.0 session (2026-11-13) written down: `__builtin_bswap32`
returned an unconstrained value, 12 branches folded to constants, and the coverage gap looked like
a search problem for three rounds of reading.

  scan_advise.py <out-dir | scan.json | report.json> [--prev <earlier run>] [--format text|json]

Exit: 0 nothing blocking, 2 at least one blocking action, 1 the report could not be read.
"""
import argparse
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hlir_scanlib as L  # noqa: E402

RANK = {"blocking": 0, "major": 1, "minor": 2, "ok": 3}
MARK = {"blocking": "!!", "major": " !", "minor": "  ", "ok": " +"}
BULK = 5  # same (kind, function) at or above this is one root cause, not N defects


def act(sev, kind, what, why, how):
    return dict(severity=sev, kind=kind, what=what, why=why, how=how)


# ---------------------------------------------------------------- the rule set
def advise_entry(e, prev=None):
    """Returns (actions, blocked). `blocked` is True when a setup defect makes everything
    downstream -- coverage reasoning and finding triage alike -- premature."""
    acts = []
    cv, met = e.get("coverage") or {}, e.get("metrics") or {}
    ext, ind = opaque = L.opaque_split(e)
    ext, ind = opaque
    counts = L.opaque_counts(e)
    cq, cr = L.checks_queried(e), L.checks_reached(e)
    codes = L.incomplete_codes(e)
    fn = L.entry_name(e)

    # ---- blocking: the entry did not really run
    if cv.get("blocks_visited", 0) == 0:
        acts.append(act("blocking", "FIX_HARNESS",
                        "the entry executed nothing",
                        "blocks_visited=0 -- a signature mismatch prints as 0 entries, a failed "
                        "lowering as blocks=0, and both still print a verdict",
                        "run the preflight build (scan_profile.py does it automatically): compile "
                        "every unit with a real compiler and partially link them"))

    # ---- taint was cut. Blocking when nobody has looked; a named limitation when someone has.
    #
    # The two are not the same claim (DESIGN.md Sec.22.379) and this harness used to merge them: a
    # profile that did exactly what this action asks for -- justify each external in an --externs
    # document -- still came back BLOCKED, and every finding was held. Measured on libssh, where all
    # nine called externals were OpenSSL teardown and logging with a written reason each.
    #
    # The downgrade is to `major`, not to silence: a decided external still returns an untainted
    # value and still writes nothing, so the branches behind it still fold. What changes is who has
    # to act -- a decision is someone's position to defend, not a hole nobody noticed.
    decided = L.declared_skips(e)
    unexplained = [n for n in ext if n not in decided]
    examined = [n for n in ext if n in decided]
    if unexplained:
        acts.append(act("blocking", "MODEL",
                        "%d unmodelled external(s) were CALLED" % len(unexplained),
                        "each returns an arbitrary UNTAINTED result and writes nothing, so the call "
                        "cuts the taint chain; downstream checks decide concretely and the branches "
                        "behind them fold to constants (SCAN_SETUP_CHECKLIST #1)",
                        "pick one per external: (a) add the file that defines it to --link, "
                        "(b) write a model under models/, or (c) justify it in an --externs document "
                        "with a reason. Re-run with `--model-todo todo.yaml` to get the worklist.\n"
                        "        externals: " + ", ".join("%s x%d" % (n, counts.get(n, 0)) for n in unexplained)))
    if examined:
        acts.append(act("major", "EXTERN_DECIDED",
                        "%d external(s) left opaque BY DECISION were CALLED" % len(examined),
                        "the reasons are recorded, but the effect is not cancelled by the reason: each "
                        "still returns an untainted value and writes nothing, so anything whose verdict "
                        "depends on what they produce is OUT OF SCOPE for this scan rather than clean",
                        "read the reasons against what this entry actually does; if one of them writes a "
                        "buffer this entry later reads, its skip is wrong.\n"
                        "        externals: " + ", ".join("%s x%d" % (n, counts.get(n, 0)) for n in examined)))

    # ---- blocking: a positive verdict nobody tested
    if L.is_positive(e) and cq == 0 and cr > 0:
        acts.append(act("blocking", "DISTRUST_VERDICT",
                        "the `%s` verdict asked the solver nothing" % e.get("verdict"),
                        "checks_reached=%d, checks_queried=0 -- every check was decided concretely on "
                        "the path that reached it (SCAN_SETUP_CHECKLIST #3)" % cr,
                        "do not record this entry as safe. Fix the setup defects above first; if "
                        "there are none, the entry's inputs are not reaching its checks at all"))

    # ---- a POSITIVE verdict out of a run that barely executed.
    #
    # The vacuity gate asks `checks_queried > 0`, and libgit2's no-init control passed it with TWELVE:
    # 209 checks reached in the whole run, 22 of 5980 functions entered, 78 blocks -- and a verdict of
    # `safe_under_assumptions`, with every gate green. The same entry with its initialiser reached
    # 7,569,491 checks. The RATIO does not separate them (5.7% queried against 0.7%), because a run
    # that executes almost nothing also asks about almost nothing: what separates them is the absolute
    # scale of the execution.
    #
    # 1000 is a floor, not a measurement, and it is written here rather than hidden so that the next
    # person can argue with the number instead of discovering it. It is `major`, not blocking: a small
    # leaf function genuinely has few checks, and this must not stop that scan from being accepted.
    if L.is_positive(e) and cr and cr < 1000:
        acts.append(act("major", "THIN_RUN",
                        "a `%s` verdict from a run that reached only %d check(s)" % (e.get("verdict"), cr),
                        "a positive verdict covers what the run executed, and this run executed almost "
                        "nothing -- the usual cause is a missing prologue (an initialiser that was not "
                        "run, DESIGN.md Sec.22.488) or an entry whose preconditions are unsatisfiable, "
                        "not a program with nothing in it",
                        "compare against another run of the SAME entry: libgit2's git_object__from_raw "
                        "reached 209 checks without git_libgit2_init and 7,569,491 with it. If this "
                        "entry really is a small leaf, say so in the profile and ignore this line"))

    if "frontier_dropped" in codes:
        acts.append(act("blocking", "DISTRUST_VERDICT",
                        "the search frontier overflowed and branches were discarded",
                        "incomplete: frontier_dropped -- the exploration is not exhaustive",
                        "`safe` is not a conclusion this run supports; narrow the entry or raise the "
                        "frontier cap, then re-run"))

    # ---- indirect calls: a different blind spot, smaller, and hidden if conflated with the above
    if ind:
        acts.append(act("major", "IFACE_MODEL",
                        "%d indirect call(s) matched no target" % len(ind),
                        "a function POINTER whose target module is not in the scan, or whose address "
                        "never flowed anywhere the frontend could see",
                        "write an interface model under models/interfaces/ and re-run with "
                        "`--entries iface`.\n        pointers: " + ", ".join(ind)))

    # ---- coverage: the ONE arithmetic question, kept separate from judgement
    o = cv.get("branch_miss_open", 0)
    un, const = cv.get("branch_miss_unreached", 0), cv.get("branch_miss_const", 0)
    gi, uns = cv.get("branch_miss_global_init", 0), cv.get("branch_miss_unsat", 0)
    if o > 0:
        acts.append(act("major", "RESCAN_BUDGET",
                        "%d branch(es) were still queued when the budget ran out" % o,
                        "branch_miss_open>0 is the ONLY bucket that responds to budget "
                        "(DESIGN.md Sec.22.429)",
                        "re-run with a larger --runs / --timeout"))
    elif (un + const) > 0:
        detail = []
        if ext:
            detail.append("opaque_calls is non-empty -- fix that FIRST, const branches are its "
                          "signature (a folded comparison downstream of a severed taint chain)")
        if const > 0 and not ext:
            detail.append("const=%d with no opaque call: look for a narrowing that pinned the value "
                          "(--ctx-names, a taint:none parameter, a global's initial value)" % const)
        ne = cv.get("not_entered") or []
        if ne:
            detail.append("not entered (%d): %s" % (len(ne), ", ".join(ne[:8]) + (" ..." if len(ne) > 8 else "")))
        acts.append(act("major", "NOT_A_BUDGET_PROBLEM",
                        "%d unreached + %d const branch(es), open=0" % (un, const),
                        "more budget cannot move either bucket; the gap is setup",
                        "\n        ".join(detail) or "inspect the entry's spec and the not_entered list"))
    if gi > 0:
        acts.append(act("minor", "FIX_INIT",
                        "%d branch(es) decided by a global's initial value" % gi,
                        "an `init:`/G2 question; budget spent here is pure waste (DESIGN.md Sec.22.465)",
                        "declare the global's real range in the spec's `init:` section"))
    # The SPEC says whether the precondition is a lie; the infeasible COUNT does not (see
    # untied_length). Kept as an "ok"-level fact so the number is still visible, with the direction
    # spelled out, because reading a rising unsat count as a regression cost a round on yara.
    if uns > 0:
        extra = ""
        if prev is not None:
            pcv = prev.get("coverage") or {}
            d_un = uns - pcv.get("branch_miss_unsat", 0)
            d_nr = cv.get("branch_miss_unreached", 0) - pcv.get("branch_miss_unreached", 0)
            d_v = cv.get("branches_visited", 0) - pcv.get("branches_visited", 0)
            if d_un > 0 and d_nr < 0:
                extra = (" vs --prev: unsat %+d while unreached %+d and visited %+d -- the HEALTHY "
                         "direction: branches the search could not reach before are now reached and "
                         "proved impossible" % (d_un, d_nr, d_v))
            elif d_un or d_nr or d_v:
                extra = " vs --prev: unsat %+d, unreached %+d, visited %+d" % (d_un, d_nr, d_v)
        acts.append(act("ok", "INFEASIBLE",
                        "%d branch(es) proved infeasible (%.1f%% of reachable)%s"
                        % (uns, 100.0 * uns / max(1, cv.get("branches_reachable", 0)), extra),
                        "infeasible is a normal result, and the count is NOT evidence about the "
                        "precondition: a rising count usually means the search got deeper",
                        "nothing, unless SPEC_UNTIED_LENGTH below also fired"))
    for fnm, bname, n, lname in (untied_length(e.get("spec") or "") or []):
        acts.append(act("major", "SPEC_UNTIED_LENGTH",
                        "parameter '%s' is pinned to %s bytes beside the free length '%s'" % (bname, n, lname),
                        "nothing in the spec ties them, so the solver may pick a length the buffer "
                        "cannot have. If the real caller guarantees size(%s) == %s, the synthesised "
                        "precondition is UNSATISFIABLE and every verdict from this entry is about a "
                        "program that cannot exist" % (bname, lname),
                        "read the real call site, then add to %s:\n"
                        "          trusted_len: { buf: %s, len: %s }\n"
                        "        and a relation for the caller's own guard, e.g. \"%s > %s\".\n"
                        "        Verify with: scan_init.py <profile> --validate-specs"
                        % (e.get("spec") or "the spec", bname, lname, lname, n)))

    # ---- the search itself
    runs, paths = met.get("runs", 0), met.get("paths", 0)
    if runs >= 50 and paths and runs / max(1, paths) > 100:
        acts.append(act("major", "SEARCH_STARVED",
                        "%d runs produced only %d symbolic path(s)" % (runs, paths),
                        "the search is re-walking one path instead of branching",
                        "look at search_budget: the top consumer is eating the flip queue"))
    # `branches_reachable` is a CALL-GRAPH over-approximation, and in a big project with function
    # pointers it is not a number this rule can defend: libgit2's allocator is a funcptr, so
    # git_delta_read_header -- a function whose whole body calls hdr_sz twice and git_error_set --
    # was credited with 5981 reachable functions and 31862 reachable branches. 99.7% of them went
    # unreached, the rule fired BLOCKING, and the actual local evidence said the opposite: of the
    # callees the executed code really has, 10 were not entered and they are the alternative
    # allocators behind that same pointer (debugalloc__malloc, git_failalloc_*).
    #
    # So the global fraction stays as the trigger and the LOCAL count decides: more callees never
    # entered than functions entered. That is a number taken from what the run actually executed
    # rather than from what the call graph imagines. yara's macho_parse_fat_file -- the case this
    # rule was written for, 2 runs and 0 paths -- still satisfies both.
    ne, fe = cv.get("not_entered_total", 0), cv.get("functions_entered", 0)
    if not codes and un > 0 and cv.get("branches_reachable", 0):
        frac = 100.0 * un / cv["branches_reachable"]
        if frac >= 50 and ne > fe:
            acts.append(act("blocking", "SEARCH_COLLAPSE",
                            "the run claims completeness with %.0f%% of branches never reached" % frac,
                            "no `incomplete` code was recorded, so the frontier emptied by itself after "
                            "%d run(s) / %d path(s) -- that is a search defect, not a budget one"
                            % (runs, paths),
                            "this is the shape of yara's macho_parse_fat_file (2 runs, 0 paths, "
                            "338/364 unreached, verdict safe). Do not accept the verdict; report it"))
    tot, solve = met.get("seconds_total", 0) or 0, met.get("sec_solve", 0) or 0
    if tot > 30 and solve / max(1e-9, tot) > 0.5:
        top = (e.get("search_budget") or [{}])[0]
        acts.append(act("minor", "SOLVER_BOUND",
                        "%.0f%% of wall clock went to the solver" % (100.0 * solve / tot),
                        "sec_solve=%.0fs of %.0fs" % (solve, tot),
                        "top flip consumer: %s (share %.0f%%). Consider folding it, narrowing the "
                        "entry, or --no-escalate"
                        % (top.get("function", "?"), 100.0 * (top.get("share", 0) or 0))))

    blocked = any(a["severity"] == "blocking" for a in acts)
    if not acts:
        acts.append(act("ok", "ACCEPT", "no setup defect detected",
                        "gates clean, open=0, no opaque call, verdict testable",
                        "the verdict and the findings are usable as evidence"))
    return acts, blocked


# ---------------------------------------------------------------- finding confirmation
LEN_NAME = re.compile(r"(^|_)(size|len|length|count|num|sz|n)(_|$)", re.I)


def untied_length(spec_path):
    """A FIXED-size buffer parameter beside a free length scalar, with nothing tying them.

    This is the shape of yara's parse_elf_header_32_le as the synthesiser wrote it:
    `elf: size {min:52,max:52}` next to `elf_size: uint64` and no relation, i.e. the real contract
    `size(elf) == elf_size > 52` became `52 == elf_size > 52` -- unsatisfiable, and the entry then
    explored a program that cannot exist at up to 100% branch coverage.

    It replaces the old CHECK_SPEC heuristic, which fired on the COUNT of infeasible branches.
    That count cannot detect this: measured on this very entry, the contradictory spec gave
    unsat = 4 of 374 (1.1%) and the CORRECTED one gives 11 of 374 (2.9%). The broken version
    scored better. Counting infeasible branches says how deep the search got, not whether the
    precondition is a lie."""
    try:
        import yaml
    except ImportError:
        return None
    try:
        with open(spec_path) as f:
            doc = yaml.safe_load(f) or {}
    except Exception:  # noqa: BLE001
        return None
    out = []
    for en in (doc.get("taint_entries") or []):
        params = en.get("params") or {}
        tied = " ".join(str(r) for r in (en.get("relations") or []))
        tl = en.get("trusted_len") or {}
        tied += " %s %s" % (tl.get("buf", ""), tl.get("len", ""))
        fixed, lens = [], []
        for name, p in params.items():
            if not isinstance(p, dict):
                continue
            if p.get("kind") == "buffer" and p.get("taint") != "none":
                sz = p.get("size") or {}
                if isinstance(sz, dict) and sz.get("min") is not None and sz.get("min") == sz.get("max"):
                    fixed.append((name, sz.get("min")))
            elif p.get("taint") == "value" and LEN_NAME.search(name):
                lens.append(name)
        for bname, n in fixed:
            for lname in lens:
                if bname in tied and lname in tied:
                    continue
                out.append((en.get("function", "?"), bname, n, lname))
    return out


def reached_by_siblings(report, fname, exclude=None):
    """Which OTHER entries of the same run reach `fname` as a callee, and how often.

    A bare entry is called with a precondition the synthesiser guessed from its signature. A sibling
    entry that reaches the same function through its REAL caller is the same engine, same build, same
    run -- so when the sibling reaches it and reports nothing there, the bare entry's findings are
    the precondition's, not the program's."""
    out = []
    for e in (report.get("entries") or []):
        # Skip the function's own bare entry (that IS the precondition under suspicion) and the
        # entry currently being confirmed (comparing a run against itself proves nothing).
        if L.entry_name(e) in (fname, exclude):
            continue
        calls = sum(c.get("calls", 0) for c in (e.get("call_edges") or [])
                    if c.get("callee") == fname and c.get("caller") != "<entry>")
        if calls:
            sites = {(f.get("kind"), (f.get("location") or {}).get("line"))
                     for f in (e.get("findings") or []) if f.get("function") == fname}
            out.append((L.entry_name(e), calls, sites))
    return out


def confirm_findings(e, blocked, report=None):
    """Credibility per finding, conditional on the setup. Every rule below reads a field the engine
    actually writes -- none is a guess about the program."""
    rows = []
    fs = e.get("findings") or []
    bulk = {}
    for f in fs:
        bulk[(f.get("kind"), f.get("function"))] = bulk.get((f.get("kind"), f.get("function")), 0) + 1
    for f in fs:
        kind, fn = f.get("kind", "?"), f.get("function", "?")
        acc = f.get("access") or {}
        objs = f.get("objects") or []
        verdict, why = "CANDIDATE", []
        if blocked:
            verdict = "HOLD"
            why.append("the entry has a BLOCKING setup defect; triaging findings before fixing it "
                       "is how a setup artefact becomes a reported bug")
        elif f.get("warning"):
            verdict = "WARNING"
            why.append("warning=true -- a property worth reading, not a claim of undefined behaviour")
        elif f.get("in_prologue"):
            verdict = "ARTEFACT"
            why.append("in_prologue=true -- inside the initialiser region, not the entry")
        elif f.get("replay") != "confirmed":
            verdict = "UNCONFIRMED"
            why.append("replay=%s -- the engine did not reproduce it concretely" % f.get("replay"))
        elif any(o.get("frontier") for o in objs):
            verdict = "SYNTH_ARTEFACT"
            why.append("the offending object was materialised past the synthesis frontier: it was "
                       "invented by the spec synthesiser, not built by the program")
        elif acc and acc.get("offset_symbolic") is False:
            verdict = "WEAK"
            why.append("access.offset_symbolic=false -- the offset was a concrete value on that path; "
                       "the solver was never shown an input that drives it out of bounds")
        if verdict in ("CANDIDATE", "WEAK") and bulk.get((kind, fn), 0) >= BULK:
            why.append("%d findings of this kind in this one function: triage the single root cause, "
                       "not %d instances" % (bulk[(kind, fn)], bulk[(kind, fn)]))
        # CROSS-ENTRY CORROBORATION. Measured on yara 2026-11-14: the bare entry
        # macho_load_fat_arch_header reports 11 oob_read at macho.c:687, while in the same run
        # macho_parse_fat_file calls that function 2220 times through the real call site -- whose
        # `count > (size - sizeof(yr_fat_header_t)) / fat_arch_sz` bounds the argument -- and reports
        # nothing there at all.
        if verdict in ("CANDIDATE", "WEAK") and report is not None:
            line = (f.get("location") or {}).get("line")
            for sib, calls, sites in reached_by_siblings(report, fn, exclude=L.entry_name(e)):
                if (kind, line) not in sites:
                    verdict = "CALLER_REFUTED"
                    why.append("@%s reaches %s %d time(s) through its REAL caller in this same run and "
                               "reports no %s at line %s: this entry's synthesised precondition is "
                               "weaker than the real call" % (sib, fn, calls, kind, line))
                    break
        rows.append(dict(id=f.get("id"), kind=kind, function=fn, verdict=verdict, why=why,
                         location=f.get("location") or {},
                         offset_symbolic=acc.get("offset_symbolic"),
                         replay=f.get("replay"), labels=f.get("labels") or []))
    return rows


# ---------------------------------------------------------------- next round
def decide_next(all_acts):
    kinds = {a["kind"] for acts in all_acts for a in acts}
    if "FIX_HARNESS" in kinds:
        return "FIX THE HARNESS, then rescan. Nothing in this report is evidence yet."
    if "MODEL" in kinds:
        return ("WRITE MODELS (or extend --link), then rescan. The taint chain is cut; coverage and "
                "findings both measure a program the scan does not have.")
    # AHEAD of SEARCH_COLLAPSE on purpose. A run that executed almost nothing also "claims
    # completeness with 100% of branches never reached", so the collapse line fires too -- but its
    # advice ("report it as an engine issue") is wrong here: on libgit2's no-init control the cause
    # was a library initialiser the entry set did not run, which is the profile's business. The
    # symptom must not outrank the cause.
    if "THIN_RUN" in kinds:
        return ("THE RUN BARELY EXECUTED. Look for a missing prologue first (`init:` / --init-fn, "
                "Sec.22.488), then for an entry precondition that cannot be satisfied. Neither more "
                "budget nor a rescan changes this.")
    if "SEARCH_COLLAPSE" in kinds or "DISTRUST_VERDICT" in kinds:
        return ("DO NOT ACCEPT THE VERDICT. Report the collapse as an engine issue; a rescan with the "
                "same setup will reproduce it.")
    if "IFACE_MODEL" in kinds:
        return "WRITE AN INTERFACE MODEL, then rescan with --entries iface."
    if "RESCAN_BUDGET" in kinds:
        return "RESCAN WITH MORE BUDGET -- open>0 means the search had more to do."
    if "NOT_A_BUDGET_PROBLEM" in kinds:
        return ("UPDATE THE PROFILE, do not rescan as-is. More budget changes nothing; the entry's "
                "preconditions or the link set are what limit coverage.")
    return "ACCEPT: the setup is clean. Triage the findings below."


def main():
    ap = argparse.ArgumentParser(description="diagnosis harness: next action + finding confirmation")
    ap.add_argument("target")
    ap.add_argument("--prev", help="an earlier run of the same entries, for trend")
    ap.add_argument("--format", choices=["text", "json"], default="text")
    a = ap.parse_args()
    try:
        rep, src = L.load_report(a.target)
    except Exception as exc:  # noqa: BLE001
        print("scan_advise: cannot read %s: %s" % (a.target, exc), file=sys.stderr)
        return 1

    entries = rep.get("entries") or []
    per, all_acts = [], []
    prev_by_fn = {}
    if a.prev:
        try:
            prep, _ = L.load_report(a.prev)
            prev_by_fn = {L.entry_name(x): x for x in (prep.get("entries") or [])}
        except Exception as exc:  # noqa: BLE001
            print("scan_advise: --prev unreadable (%s); continuing without it" % exc, file=sys.stderr)
    for e in entries:
        acts, blocked = advise_entry(e, prev_by_fn.get(L.entry_name(e)))
        all_acts.append(acts)
        per.append((e, acts, blocked, confirm_findings(e, blocked, rep)))

    if a.format == "json":
        print(json.dumps({"source": src, "next": decide_next(all_acts),
                          "entries": [{"function": L.entry_name(e), "verdict": e.get("verdict"),
                                       "blocked": b, "actions": acts, "findings": fs}
                                      for e, acts, b, fs in per]}, indent=2))
        return 2 if any(b for _, _, b, _ in per) else 0

    print("scan_advise: %s -- %d entry(s)" % (src, len(entries)))
    print("\n################ NEXT ################")
    print("  " + decide_next(all_acts))

    print("\n################ ACTIONS ################")
    for e, acts, blocked, _ in per:
        print("\n  @%s  [%s]%s" % (L.entry_name(e), e.get("verdict", "?"),
                                   "   << BLOCKED" if blocked else ""))
        for act_ in sorted(acts, key=lambda d: RANK.get(d["severity"], 9)):
            print("   %s %-22s %s" % (MARK.get(act_["severity"], "  "), act_["kind"], act_["what"]))
            print("        why: %s" % act_["why"])
            print("        do : %s" % act_["how"])

    print("\n################ FINDING CONFIRMATION ################")
    any_f = False
    for e, _, blocked, fs in per:
        if not fs:
            continue
        any_f = True
        agg = {}
        for r in fs:
            agg.setdefault(r["verdict"], []).append(r)
        print("\n  @%s  %d finding(s)%s" % (L.entry_name(e), len(fs),
                                            "   << setup BLOCKED: all held" if blocked else ""))
        for v in ("CANDIDATE", "WEAK", "CALLER_REFUTED", "UNCONFIRMED", "SYNTH_ARTEFACT", "ARTEFACT", "WARNING", "HOLD"):
            rs = agg.get(v) or []
            if not rs:
                continue
            print("    --- %s x%d" % (v, len(rs)))
            seen = set()
            for r in rs:
                key = (r["kind"], r["function"])
                if key in seen and len(rs) > BULK:
                    continue
                seen.add(key)
                loc = r["location"]
                print("      %-18s @%s %s:%s" % (r["kind"], r["function"],
                                                 loc.get("file", "?"), loc.get("line", "?")))
                for w in r["why"]:
                    print("          %s" % w)
            if len(rs) > BULK:
                print("      (%d more of the same kinds collapsed)" % (len(rs) - len(seen)))
    if not any_f:
        print("  no findings")
    return 2 if any(b for _, _, b, _ in per) else 0


if __name__ == "__main__":
    sys.exit(main())

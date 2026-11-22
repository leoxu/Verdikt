# CVE regression fixtures

Each file distils ONE CVE that HLIR has detected on the real tree, with native ASan ground truth, into a pair
of self-contained functions:

    <name>_vuln     the shape as it was, which must be found
    <name>_fixed    the same shape with the upstream fix applied, which must come back clean

The pair is the point. A detection fixture without its fixed twin tests recall and says nothing about false
positives, and the differential ("the finding disappears on the fixed tree") is one of the four criteria the
real corpus is judged by -- so it has to survive the distillation.

**These are shape regressions, not the CVEs.** A minimised function is not the program the CVE was filed
against: the real differential corpus lives in `workspace/`, runs against actual upstream worktrees, and is
confirmed by native ASan. This directory exists so that a change to the engine cannot silently lose a class of
defect between those (slow, manual) runs. Claiming "HLIR detects CVE-X" on the strength of a fixture here
would be claiming something these files do not show.

Header keys read by `test/c/cve_tests.cpp`:

    // CVE:    the identifier
    // SOURCE: upstream file:line and the fix commit
    // KIND:   the UB kind that must be reported on the vuln entry
    // VULN:   entry function that must report it
    // FIXED:  entry function that must not
    // ARGS:   extra hlir-scan flags for this fixture (optional)

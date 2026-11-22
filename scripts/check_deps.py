#!/usr/bin/env python3
"""Enforce the module dependency matrix from docs/ARCHITECTURE.md §3.

Rules checked:
  1. Every #include "hlir/<m>/..." in module X's code must have <m> in ALLOWED[X] (or <m> == X).
  2. No code may include another module's private headers (lib/<m>/...).
  3. Public headers (include/hlir/<m>/) must not include third-party headers listed in PRIVATE_THIRD_PARTY.
Exit code 1 and a report on violation.
"""
import os
import re
import sys

ALLOWED = {
    "support":   set(),
    "ir":        {"support"},
    "smt":       {"support"},
    "memory":    {"support", "smt"},
    "model":     {"support"},
    "frontend":  {"support", "ir"},
    "entry":     {"support", "ir", "smt", "model"},
    "semantics": {"support", "ir", "smt", "memory", "model"},
    "taint":     {"support", "ir", "smt", "semantics", "model"},
    "analysis":  {"support", "ir"},
    "report":    {"support"},
    "scan":      {"support", "frontend", "iface"},
    # call-contract models of the well-known dispatch interfaces (file_operations, resmgr_io_funcs_t, wayland
    # request vtables). Pure data + a reader: it describes what a handler is HANDED, and is consumed by `scan`,
    # which lowers it into an ordinary entry spec. Depends on nothing but `support` on purpose -- it must stay
    # readable and overridable without pulling the engine in (DESIGN.md §22.357).
    "iface":     {"support"},
    "buildinfo": {"support"},
    "link":      {"support"},
    "driver":    None,  # may use everything
}
# third-party headers that must stay out of public headers (they may appear under lib/<m>/)
PRIVATE_THIRD_PARTY = [r"clang/", r"z3", r"cvc5/", r"yaml-cpp/", r"mlir/"]

INC = re.compile(r'^\s*#\s*include\s*[<"]([^>"]+)[>"]')
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
errors = []


def scan(path, module, public):
    with open(path, encoding="utf-8", errors="replace") as f:
        for n, line in enumerate(f, 1):
            m = INC.match(line)
            if not m:
                continue
            inc = m.group(1)
            if inc.startswith("hlir/"):
                dep = inc.split("/")[1]
                if dep not in ALLOWED:
                    errors.append(f"{path}:{n}: unknown module '{dep}' in include {inc}")
                elif module != "driver" and dep != module and dep not in ALLOWED[module]:
                    errors.append(f"{path}:{n}: module '{module}' may not depend on '{dep}' ({inc})")
            if public:
                for pat in PRIVATE_THIRD_PARTY:
                    if re.search(pat, inc):
                        errors.append(f"{path}:{n}: public header leaks third-party header {inc}")
            if re.search(r'(^|/)lib/', inc):
                errors.append(f"{path}:{n}: includes a private header path {inc}")


for base, public in (("include/hlir", True), ("lib", False)):
    d = os.path.join(root, base)
    if not os.path.isdir(d):
        continue
    for mod in sorted(os.listdir(d)):
        md = os.path.join(d, mod)
        if not os.path.isdir(md):
            continue
        if mod not in ALLOWED:
            errors.append(f"{md}: directory is not a declared module (add it to ALLOWED + docs/ARCHITECTURE.md)")
            continue
        for dp, _, files in os.walk(md):
            for fn in files:
                if fn.endswith((".h", ".hpp", ".cpp", ".cc")):
                    scan(os.path.join(dp, fn), mod, public)

# lib/<m> private includes: a file may include "<its own dir>-relative" headers freely; cross-module private
# access is caught by rule 2 above (paths containing lib/) and by the module matrix.

if errors:
    print("dependency check FAILED:")
    for e in errors:
        print("  " + e)
    sys.exit(1)
print("dependency check OK")

#!/usr/bin/env python3
"""Check the numeric `// RUN: @f(args) => N` expectations of test/c/*.c against the native C compiler.

The interpreter result for a UB-free C function must equal what the real compiler produces; this validates the
frontend's lowering independently of hand-computed expectations. Lines expecting ub:/assert/etc. are skipped.
Usage: c_native_check.py <cc> <dir-with-.c-files> [<c++ compiler> <dir-with-.cpp-files>]
"""
import glob, os, re, subprocess, sys, tempfile

cc, d = sys.argv[1], sys.argv[2]
cxx, cppdir = (sys.argv[3], sys.argv[4]) if len(sys.argv) > 4 else (None, None)
RUN = re.compile(r'^//\s*RUN:\s*@(\w+)\(([^)]*)\)\s*=>\s*(-?\d+)\s*$')
bad = checked = 0
jobs = [(p, cc, False) for p in sorted(glob.glob(os.path.join(d, '*.c')))]
if cxx: jobs += [(p, cxx, True) for p in sorted(glob.glob(os.path.join(cppdir, '*.cpp')))]
for path, comp, isCxx in jobs:
    src = open(path).read()
    calls = [m.groups() for m in map(RUN.match, src.splitlines()) if m]
    if not calls:
        continue
    main = (['#include <cstdio>', 'int main() {'] if isCxx else ['int printf(const char *, ...);', 'int main(void) {'])
    for i, (f, args, _) in enumerate(calls):
        main.append(f'  {"std::" if isCxx else ""}printf("%lld\\n", (long long){f}({args}));')
    main.append('  return 0;\n}')
    with tempfile.TemporaryDirectory() as t:
        c, exe = os.path.join(t, 'a.cpp' if isCxx else 'a.c'), os.path.join(t, 'a.out')
        open(c, 'w').write(src + '\n' + '\n'.join(main) + '\n')
        r = subprocess.run([comp, '-w', '-O0', '-std=gnu++17' if isCxx else '-std=gnu11', c, '-o', exe], capture_output=True, text=True)
        if r.returncode:
            print(f'{path}: native compile failed:\n{r.stderr}'); bad += 1; continue
        out = subprocess.run([exe], capture_output=True, text=True).stdout.split()
    for (f, args, want), got in zip(calls, out):
        checked += 1
        if int(want) != int(got):
            bad += 1
            print(f'{os.path.basename(path)}: @{f}({args}) expected {want} but the native compiler gives {got}')
print(f'c_native_check: {checked} expectations checked, {bad} mismatches')
sys.exit(1 if bad else 0)

#!/usr/bin/env python3
"""Rewrite the `=> N` expectations of test/cpp/<file>.cpp from what the native C++ compiler computes (the authority).
Usage: cpp_regen.py <file.cpp> [c++ compiler]"""
import re, subprocess, sys, os, tempfile
path = sys.argv[1]
cxx = sys.argv[2] if len(sys.argv) > 2 else 'g++'
RUN = re.compile(r'^(//\s*RUN:\s*@(\w+)\(([^)]*)\)\s*=>\s*)(-?\d+)\s*$')
lines = open(path).read().splitlines()
calls = [(i, m) for i, m in ((i, RUN.match(l)) for i, l in enumerate(lines)) if m]
main = ['#include <cstdio>', 'int main() {'] + [f'  std::printf("%lld\\n", (long long){m.group(2)}({m.group(3)}));' for _, m in calls] + ['  return 0;', '}']
with tempfile.TemporaryDirectory() as t:
    c, exe = os.path.join(t, 'a.cpp'), os.path.join(t, 'a.out')
    open(c, 'w').write('\n'.join(lines) + '\n' + '\n'.join(main) + '\n')
    r = subprocess.run([cxx, '-w', '-O0', '-std=gnu++17', c, '-o', exe], capture_output=True, text=True)
    if r.returncode: print(r.stderr); sys.exit(1)
    out = subprocess.run([exe], capture_output=True, text=True).stdout.split()
for (i, m), v in zip(calls, out):
    lines[i] = m.group(1) + v
open(path, 'w').write('\n'.join(lines) + '\n')
print(f'{len(calls)} expectations set from the native compiler')

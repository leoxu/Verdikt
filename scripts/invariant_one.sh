#!/bin/bash
# One candidate loop invariant through the full scan (docs/LLM_GUIDED_SE.md §10).
#   invariant_one.sh FUNCTION:HEADER "EXPR" [ASSERT_EXPR]
#
# Three things this script does that the first version of it did not, each of which produced a wrong
# conclusion when it was missing (ENGINE_LIMITATIONS.md §7.7):
#   * delete the output file first,
#   * check the exit code,
#   * do not swallow stderr -- a refusal to run must not read as a property of the program.
#
# It also prints the entry's verdict and `incomplete` reasons, because "no violation" is only a PROOF when
# the exploration was complete. On a real target it almost never is.
set -u
HLIR=$(cd "$(dirname "$0")/.." && pwd)
W=${TCPDUMP_SRC:?set TCPDUMP_SRC to a tcpdump checkout}
OUT=${IV_OUT:-/tmp/invariant_one.json}
rm -f "$OUT"
EXTRA=()
[ $# -ge 3 ] && EXTRA=(--invariant-assert "$3")
err=$(timeout "${IV_TIMEOUT:-600}" python3 "$HLIR/scripts/scan_profile.py" tcpdump printer \
  --src "$W" -D HX_PRINTER="${IV_PRINTER:-isoclns_print}" --set PRINTER_FILE="${IV_FILE:-print-isoclns.c}" \
  --runs "${IV_RUNS:-3000}" --timeout "${IV_ENTRY_TIMEOUT:-120}" --buf-max 56 --no-build --no-gates \
  --out "$OUT" --check-invariant "$1:$2" "${EXTRA[@]}" 2>&1 >/dev/null)
rc=$?
if [ ! -s "$OUT" ]; then
  echo "NO REPORT (rc=$rc): $(echo "$err" | grep -iE 'verify|error|fail' | head -2 | tr '\n' ' ')"
  exit 1
fi
python3 - "$OUT" <<'PY'
import json, sys
e = json.load(open(sys.argv[1]))["entries"][0]
a = [f for f in e["findings"] if f["kind"] == "assert"]
inc = [i["code"] for i in e.get("incomplete", [])]
if a:
    print("REFUTED (%s)   blocks=%s" % (a[0].get("replay", ""), e["coverage"]["blocks_visited"]))
elif inc:
    print("no counterexample in budget   blocks=%s  incomplete=%s  <- NOT a proof"
          % (e["coverage"]["blocks_visited"], ",".join(inc)))
else:
    print("PROVED (complete exploration)   blocks=%s" % e["coverage"]["blocks_visited"])
PY

#!/bin/bash
# Build a per-module copy of the dispatch-interface models with the receive buffer sized the way THAT module
# sizes it (DESIGN.md §22.366). The shipped models/interfaces/qnx_resmgr.yaml carries 2048 as a placeholder, and
# the placeholder is wrong for every module measured so far: <driver> 512, <driver> 1024, <driver> 8192,
# <driver> 65536. Too small invents out-of-bounds reads; too large HIDES them -- which is the dangerous direction,
# because the scan then reports `safe` about a handler that really does read past the client's message.
#
# Usage: scripts/qnx/module_interfaces.sh <bytes> <outdir>
set -eu
bytes="${1:?usage: module_interfaces.sh <bytes> <outdir>}"
out="${2:?usage: module_interfaces.sh <bytes> <outdir>}"
here="$(cd "$(dirname "$0")" && pwd)"
src="$here/../../models/interfaces"
mkdir -p "$out"
cp "$src"/*.yaml "$out"/
sed -i "s/size: { min: 2048, max: 2048 }/size: { min: $bytes, max: $bytes }/g" "$out/qnx_resmgr.yaml"
n=$(grep -c "min: $bytes, max: $bytes" "$out/qnx_resmgr.yaml")
echo "$out: $n slot contract(s) sized to $bytes bytes"

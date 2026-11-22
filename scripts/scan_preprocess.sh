#!/usr/bin/env bash
# scan_preprocess.sh -- standardizes the mechanical "get from a real project checkout to a
# compile_commands.json / --makefile hlir-scan can use, then list candidate entries" pipeline
# that every round of the open-source/kernel testing series (docs/DESIGN.md §22.x) has been
# re-deriving by hand.
#
# WHAT THIS SCRIPT DOES NOT DO: it does not choose which entries to scan. Entry selection
# requires actually reading the project's real dispatch/registration code (ops-struct field
# initializers, ioctl/opcode switch-case dispatch, .proto rpc definitions, HTTP route tables,
# a library's public header declarations) -- see memory: testing-series-entry-selection.md.
# This script's "candidate assist" step (stage 3) surfaces a few greps that often help locate
# that dispatch code faster, but reading it remains a required manual/fork step, not optional.
#
# Usage:
#   scan_preprocess.sh cmake       <project-dir> [extra cmake args...]
#   scan_preprocess.sh meson       <project-dir> [extra meson setup args...]
#   scan_preprocess.sh makefile    <project-dir> [--configure "<configure args>"]
#   scan_preprocess.sh kernel-subsys   <subsystem-path-relative-to-kernel-root> [--config-module NAME]... [--config-enable NAME]... [--config-disable NAME]...
#   scan_preprocess.sh kernel-outoftree <module-dir> [--config-module NAME]...
#
# Each mode ends by writing compile_commands.json (or confirming --makefile works directly)
# into the project dir / a scratch build dir, then running `hlir-scan --entries all --list`
# and saving the raw listing to <out>/entries.txt, plus a short candidate-assist grep report
# to <out>/candidates.txt. Prints the output directory at the end.
#
# Known quirks this script does NOT handle (every project so far has had its own; see the
# relevant docs/DESIGN.md §22.x section when one of these bites): FetchContent-style CMake
# projects that pull CUDA/gRPC/other heavyweight deps (hand-pick
# an independent, low-dependency source file slice instead of trying to build the whole
# thing); meson projects needing bison/flex/m4 from a local toolchain prefix (Mesa §22.* --
# see corpus/drm-build-cache/toolchain-debs/); autotools projects whose `./configure` needs
# specific --disable-* flags to shed heavy external deps (mbedtls/libpng precedent). This
# script gets you to a clean starting point for the COMMON case; the quirky remainder is
# still a per-project judgment call, same as always.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HLIR_ROOT="$(cd "$HERE/.." && pwd)"
HLIR_SCAN="$HLIR_ROOT/build/hlir-scan"
CORPUS_DIR="$HLIR_ROOT/../corpus"

die() { echo "scan_preprocess.sh: error: $*" >&2; exit 1; }

[ -x "$HLIR_SCAN" ] || die "hlir-scan not found/built at $HLIR_SCAN -- build HLIR first (cmake --build build)"

MODE="${1:-}"
[ -n "$MODE" ] || die "usage: scan_preprocess.sh <cmake|meson|makefile|kernel-subsys|kernel-outoftree> ..."
shift || true

# ---------------------------------------------------------------- shared: entry discovery + candidate-assist grep
# $1 = compile_commands.json path, $2 = output dir, remaining = extra hlir-scan args
# `--compile-commands FILE` is a flag, not a positional source file -- with no positional
# inputs, hlir-scan scans every file the compile_commands.json compiles (same as --makefile).
run_entry_discovery() {
  local target="$1" out="$2"; shift 2
  mkdir -p "$out"
  echo "scan_preprocess.sh: running entry discovery (--compile-commands $target) -> $out/entries.txt"
  "$HLIR_SCAN" --entries all --list --compile-commands "$target" "$@" > "$out/entries.txt" 2>&1 || true
  local n
  n=$(grep -c '^\S.*@' "$out/entries.txt" 2>/dev/null || echo 0)
  echo "scan_preprocess.sh: $n candidate entries listed (see $out/entries.txt)"

  {
    echo "# candidate-assist grep report -- NOT a substitute for reading the real dispatch code."
    echo "# (memory: testing-series-entry-selection.md -- read route tables / ioctl switches /"
    echo "#  ops-struct field initializers / .proto rpc defs before picking a final entry set)"
    echo
    echo "## struct ...ops = { .field = fn, ... } style registrations (ops-table/vtable candidates):"
    grep -rnE '^\s*\.[A-Za-z_][A-Za-z0-9_]*\s*=\s*[A-Za-z_][A-Za-z0-9_]*\s*,?\s*$' "$(dirname "$target")" 2>/dev/null | head -100 || true
    echo
    echo "## switch-case dispatch on what looks like a command/opcode/ioctl constant:"
    grep -rnE 'case\s+[A-Z_][A-Z0-9_]{3,}\s*:' "$(dirname "$target")" 2>/dev/null | head -100 || true
    echo
    echo "## .proto service method definitions (gRPC/protobuf RPC surface, if any):"
    find "$(dirname "$target")" -iname '*.proto' 2>/dev/null -exec grep -Hn 'rpc ' {} \; | head -100 || true
    echo
    echo "## public header declarations (library's own stated public API, if headers exist):"
    find "$(dirname "$target")" -iname '*.h' -path '*include*' 2>/dev/null | head -20 || true
  } > "$out/candidates.txt"
  echo "scan_preprocess.sh: candidate-assist report -> $out/candidates.txt"
}

# ---------------------------------------------------------------- kernel: objtool/CONFIG_OBJTOOL workaround
# DESIGN.md §22.117/123/128/132/...: x86_64 defconfig's HAVE_STATIC_CALL_INLINE/HAVE_UACCESS_VALIDATION
# `select OBJTOOL`, so `scripts/config --disable CONFIG_OBJTOOL` doesn't stick through olddefconfig; this
# makes tools/objtool actually build instead, and ITS link step fails against the static libelf.a/libzstd.a
# this project's toolchain-debs cache provides (no zlib/zstd runtime symbols). Fix: demote objtool's link to
# dynamic by removing the static archives and symlinking to the system .so.1 runtime libs instead. Apply this
# PRE-EMPTIVELY (before `make olddefconfig`), not only after hitting the link error -- confirmed safe/no-op
# on kernel configs that don't end up building objtool at all (§22.128/132 applied it pre-emptively with no
# issues both times).
apply_kernel_objtool_fix() {
  local prefix="$1"  # local toolchain prefix dir (dpkg -x target for libelf-dev/libzstd-dev .deb's)
  local lib="$prefix/usr/lib/x86_64-linux-gnu"
  [ -d "$lib" ] || { echo "scan_preprocess.sh: no $lib, skipping objtool fix (toolchain prefix not set up yet?)"; return 0; }
  for name in libelf libzstd libz; do
    if [ -f "$lib/$name.a" ]; then
      mv -f "$lib/$name.a" "$lib/$name.a.bak"
    fi
    if [ ! -e "$lib/$name.so" ]; then
      local real
      real=$(ls "/usr/lib/x86_64-linux-gnu/$name.so."* 2>/dev/null | head -1)
      [ -n "$real" ] || real=$(ls "$lib/$name.so."* 2>/dev/null | head -1)
      if [ -n "$real" ]; then
        ln -sf "$real" "$lib/$name.so"
        echo "scan_preprocess.sh: objtool fix: $lib/$name.so -> $real"
      fi
    fi
  done
}

# ---------------------------------------------------------------- kernel: standard recipe (memory: drm-kernel-build-recipe.md)
# $1 = scratch dir, $2 = subsystem path relative to kernel root (for compile_commands scoping message only)
# remaining args: repeated --config-module/--config-enable/--config-disable NAME pairs
setup_kernel_tree() {
  local scratch="$1" subsys_hint="$2"; shift 2
  local tarball="$CORPUS_DIR/linux-6.12.112.tar.xz"
  [ -f "$tarball" ] || die "expected kernel source at $tarball (corpus/linux-6.12.112.tar.xz) -- not found"
  mkdir -p "$scratch"
  echo "scan_preprocess.sh: extracting kernel source to $scratch (this + subdirs are scratch, not persisted)"
  tar -xf "$tarball" -C "$scratch"
  local ktree="$scratch/linux-6.12.112"

  local prefix="$scratch/toolchain"
  mkdir -p "$prefix"
  if [ -d "$CORPUS_DIR/drm-build-cache/toolchain-debs" ]; then
    for deb in "$CORPUS_DIR/drm-build-cache/toolchain-debs"/*.deb; do
      [ -f "$deb" ] && dpkg -x "$deb" "$prefix" 2>/dev/null || true
    done
  else
    echo "scan_preprocess.sh: WARNING: no corpus/drm-build-cache/toolchain-debs/ -- flex/bison/m4/libelf-dev/libzstd-dev must already be on PATH, or the kernel build will fail on missing host tools"
  fi
  export PATH="$prefix/usr/bin:$PATH"
  export C_INCLUDE_PATH="$prefix/usr/include:${C_INCLUDE_PATH:-}"
  export LIBRARY_PATH="$prefix/usr/lib/x86_64-linux-gnu:${LIBRARY_PATH:-}"
  export BISON_PKGDATADIR="$prefix/usr/share/bison"
  export M4="$prefix/usr/bin/m4"

  apply_kernel_objtool_fix "$prefix"

  ( cd "$ktree" && make defconfig )
  local configs=("$@")
  if [ "${#configs[@]}" -gt 0 ]; then
    ( cd "$ktree" && scripts/config "${configs[@]}" )
  fi
  apply_kernel_objtool_fix "$prefix"  # re-apply: scripts/config above may have touched the .config but not the toolchain dir, harmless to repeat
  ( cd "$ktree" && make olddefconfig )
  echo "scan_preprocess.sh: building $subsys_hint to confirm config+env actually work (this is a real compile, not just --list)"
  ( cd "$ktree" && make -k -j"$(nproc)" "$subsys_hint" )
  echo "scan_preprocess.sh: generating compile_commands.json (rebuilds vmlinux, budget ~10-15 min)"
  ( cd "$ktree" && make compile_commands.json )
  echo "$ktree/compile_commands.json"
}

OUT_DEFAULT="$HLIR_ROOT/scan_prep_out"

case "$MODE" in
  cmake)
    proj="${1:?project dir required}"; shift || true
    bdir="$proj/scan_prep_build"
    mkdir -p "$bdir"
    ( cd "$bdir" && cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DCMAKE_BUILD_TYPE=RelWithDebInfo "$@" .. && cmake --build . -j"$(nproc)" )
    run_entry_discovery "$bdir/compile_commands.json" "$OUT_DEFAULT"
    ;;
  meson)
    proj="${1:?project dir required}"; shift || true
    bdir="$proj/scan_prep_build"
    ( cd "$proj" && meson setup "$bdir" "$@" && ninja -C "$bdir" )
    run_entry_discovery "$bdir/compile_commands.json" "$OUT_DEFAULT"
    ;;
  makefile)
    proj="${1:?project dir required}"; shift || true
    cfg_args=""
    if [ "${1:-}" = "--configure" ]; then cfg_args="$2"; shift 2; fi
    if [ -n "$cfg_args" ] && [ -x "$proj/configure" ]; then
      ( cd "$proj" && ./configure $cfg_args )
    elif [ -x "$proj/autogen.sh" ] && [ ! -x "$proj/configure" ]; then
      ( cd "$proj" && ./autogen.sh && ./configure $cfg_args )
    fi
    # hlir-scan/hlirgen have built-in `--makefile` support (make -n dry-run extraction of real
    # compiler flags) -- no bear/compiledb dependency needed for the plain-Makefile/autotools case.
    mkdir -p "$OUT_DEFAULT"
    "$HLIR_SCAN" --entries all --list --makefile "$proj" > "$OUT_DEFAULT/entries.txt" 2>&1 || true
    n=$(grep -c '^\S.*@' "$OUT_DEFAULT/entries.txt" 2>/dev/null || echo 0)
    echo "scan_preprocess.sh: $n candidate entries listed via --makefile (see $OUT_DEFAULT/entries.txt)"
    {
      echo "## switch-case dispatch on what looks like a command/opcode constant:"
      grep -rnE 'case\s+[A-Z_][A-Z0-9_]{3,}\s*:' "$proj" 2>/dev/null | head -100 || true
      echo
      echo "## public header declarations:"
      find "$proj" -iname '*.h' -path '*include*' 2>/dev/null | head -20 || true
    } > "$OUT_DEFAULT/candidates.txt"
    ;;
  kernel-subsys)
    subsys="${1:?subsystem path relative to kernel root required, e.g. drivers/gpu/drm/}"; shift || true
    cc=$(setup_kernel_tree "/tmp/scan_prep_kernel_$$" "$subsys" "$@")
    run_entry_discovery "$cc" "$OUT_DEFAULT"
    ;;
  kernel-outoftree)
    moddir="${1:?out-of-tree module dir required}"; shift || true
    scratch="/tmp/scan_prep_kernel_$$"
    cc=$(setup_kernel_tree "$scratch" "modules" "$@")
    ktree="$(dirname "$cc")"
    echo "scan_preprocess.sh: building out-of-tree module against $ktree"
    ( cd "$moddir" && make -C "$ktree" M="$moddir" modules )
    if [ -f "$ktree/scripts/clang-tools/gen_compile_commands.py" ]; then
      python3 "$ktree/scripts/clang-tools/gen_compile_commands.py" -d "$moddir" -o "$moddir/compile_commands.json" || true
    fi
    if [ -f "$moddir/compile_commands.json" ]; then
      run_entry_discovery "$moddir/compile_commands.json" "$OUT_DEFAULT"
    else
      echo "scan_preprocess.sh: no compile_commands.json produced for $moddir -- inspect $ktree/scripts/clang-tools/gen_compile_commands.py availability, or build with 'bear -- make' manually"
      exit 1
    fi
    ;;
  *)
    die "unknown mode '$MODE' (want cmake|meson|makefile|kernel-subsys|kernel-outoftree)"
    ;;
esac

echo
echo "scan_preprocess.sh: done. Output in $OUT_DEFAULT/ (entries.txt, candidates.txt)."
echo "Next step is manual: read $OUT_DEFAULT/candidates.txt + the real dispatch/registration code"
echo "to build the actual entry list -- see memory: testing-series-entry-selection.md."

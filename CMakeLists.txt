cmake_minimum_required(VERSION 3.20)
project(HLIR LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
# Default: optimised with debug info and assertions kept (-O2 -g, no -DNDEBUG). The analysis is wall-clock budgeted,
# so an unoptimised build simply explores less: on the cJSON exported-entry scan -O0 ran ~3x fewer concolic runs in
# the same budget and missed 4 replay-confirmed bugs (docs/DESIGN.md Sec.22.336). Assertions stay on because they
# guard engine invariants (e.g. TermManager's per-name width) that must fail loudly, not silently. -DCMAKE_BUILD_TYPE=Debug
# still gives an -O0 build for debugging.
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE RelWithDebInfo)
endif()
string(REPLACE "-DNDEBUG" "" CMAKE_CXX_FLAGS_RELWITHDEBINFO "${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")

option(HLIR_SANITIZE "Build with ASAN+UBSAN" OFF)
if(HLIR_SANITIZE)
  add_compile_options(-fsanitize=address,undefined -fno-omit-frame-pointer)
  add_link_options(-fsanitize=address,undefined)
endif()
add_compile_options(-Wall -Wextra -Wno-unused-parameter)

# LLVM is used only for ADT/Support (APInt, raw_ostream). No MLIR, no Clang yet (P0-P2).
# We query llvm-config instead of find_package(LLVM): the distro LLVMExports.cmake requires zstd::libzstd_shared
# (libzstd-dev), which is not needed for LLVMSupport usage here.
find_program(LLVM_CONFIG NAMES llvm-config-18 llvm-config REQUIRED)
execute_process(COMMAND ${LLVM_CONFIG} --version OUTPUT_VARIABLE LLVM_VER OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${LLVM_CONFIG} --includedir OUTPUT_VARIABLE LLVM_INC OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${LLVM_CONFIG} --libdir OUTPUT_VARIABLE LLVM_LIBDIR OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND ${LLVM_CONFIG} --link-shared --libs support OUTPUT_VARIABLE LLVM_LIBS OUTPUT_STRIP_TRAILING_WHITESPACE)
message(STATUS "LLVM ${LLVM_VER} (include: ${LLVM_INC}, libs: ${LLVM_LIBS})")
string(REGEX MATCH "^[0-9]+" LLVM_MAJOR "${LLVM_VER}")
if(LLVM_MAJOR LESS 16)
  message(FATAL_ERROR "LLVM >= 16 required, found ${LLVM_VER}")
endif()
add_library(LLVMSupport INTERFACE)
target_include_directories(LLVMSupport SYSTEM INTERFACE ${LLVM_INC})
target_link_directories(LLVMSupport INTERFACE ${LLVM_LIBDIR})
separate_arguments(LLVM_LIBS_LIST UNIX_COMMAND "${LLVM_LIBS}")
target_link_libraries(LLVMSupport INTERFACE ${LLVM_LIBS_LIST})
target_compile_definitions(LLVMSupport INTERFACE __STDC_CONSTANT_MACROS __STDC_FORMAT_MACROS __STDC_LIMIT_MACROS)
include_directories(${CMAKE_SOURCE_DIR}/include)

# ---- modules (one target each; link only what docs/ARCHITECTURE.md §3 allows) ----
add_library(hlir_support lib/support/Diagnostics.cpp lib/support/Yaml.cpp)
target_link_libraries(hlir_support PUBLIC LLVMSupport)

add_library(hlir_ir
  lib/ir/Loops.cpp
  lib/ir/InvariantCheck.cpp
  lib/ir/Ops.cpp
  lib/ir/IR.cpp
  lib/ir/Printer.cpp
  lib/ir/Parser.cpp
  lib/ir/Verifier.cpp)
target_link_libraries(hlir_ir PUBLIC hlir_support LLVMSupport)

add_library(hlir_model lib/model/ModelDB.cpp)
target_link_libraries(hlir_model PUBLIC hlir_support)

add_library(hlir_smt
  lib/smt/Term.cpp
  lib/smt/Eval.cpp
  lib/smt/SmtLib.cpp
  lib/smt/EnumSolver.cpp
  lib/smt/Z3Process.cpp
  lib/smt/Z3Native.cpp)
target_link_libraries(hlir_smt PUBLIC hlir_support LLVMSupport)

# Optional: makeZ3NativeSolver() (lib/smt/Z3Native.cpp), a libz3-linked SMT backend that exists ALONGSIDE
# makeZ3ProcessSolver() (the z3 subprocess, still the only backend any existing caller uses -- see docs/DESIGN.md).
# Z3Native.cpp itself is always compiled; HLIR_HAVE_Z3_NATIVE just switches it between a real implementation and a
# stub that returns nullptr, so a dev tree without libz3-dev builds exactly as before this option existed.
find_path(Z3_INCLUDE_DIR NAMES z3.h)
find_library(Z3_LIBRARY NAMES z3)
if(Z3_INCLUDE_DIR AND Z3_LIBRARY)
  message(STATUS "libz3 found (include: ${Z3_INCLUDE_DIR}, lib: ${Z3_LIBRARY}): makeZ3NativeSolver() will be functional")
  target_compile_definitions(hlir_smt PRIVATE HLIR_HAVE_Z3_NATIVE=1)
  target_include_directories(hlir_smt PRIVATE ${Z3_INCLUDE_DIR})
  target_link_libraries(hlir_smt PRIVATE ${Z3_LIBRARY})
else()
  message(STATUS "libz3 not found (no z3.h / libz3.so): makeZ3NativeSolver() will return nullptr; makeZ3ProcessSolver() is unaffected")
endif()

add_library(hlir_entry
  lib/entry/Spec.cpp
  lib/entry/Relations.cpp
  lib/entry/InitGen.cpp
  lib/entry/SeedSolver.cpp
  lib/entry/HarnessGen.cpp)
target_include_directories(hlir_entry PRIVATE lib/entry)
target_link_libraries(hlir_entry PUBLIC hlir_ir hlir_smt hlir_support)

add_library(hlir_report
  lib/report/Report.cpp
  lib/report/JsonRead.cpp
  lib/report/Sarif.cpp)
target_include_directories(hlir_report PRIVATE lib/report)
target_link_libraries(hlir_report PUBLIC hlir_support)

add_library(hlir_semantics
  lib/semantics/UB.cpp
  lib/semantics/Env.cpp
  lib/semantics/Interpreter.cpp
  lib/semantics/Symbolic.cpp
  lib/semantics/Taint.cpp)
target_include_directories(hlir_semantics PRIVATE lib/semantics)
target_link_libraries(hlir_semantics PUBLIC hlir_ir hlir_smt hlir_model hlir_support)

add_library(hlir_link lib/link/Link.cpp)
target_link_libraries(hlir_link PUBLIC hlir_support)
add_library(hlir_buildinfo lib/buildinfo/BuildInfo.cpp)
target_link_libraries(hlir_buildinfo PUBLIC hlir_support)

add_library(hlir_iface lib/iface/Interface.cpp)
target_link_libraries(hlir_iface PUBLIC hlir_support)
add_library(hlir_scan lib/scan/Scan.cpp lib/scan/StructRanges.cpp)
target_link_libraries(hlir_scan PUBLIC hlir_support hlir_iface)

# C frontend: the only module that needs Clang's C++ API (libclang-cpp + shared LLVM). Link it only into the tools
# that read .c files; everything else keeps working on `core` text.
find_library(CLANG_CPP NAMES clang-cpp clang-cpp-${LLVM_MAJOR} HINTS ${LLVM_LIBDIR})
if(CLANG_CPP AND EXISTS ${LLVM_INC}/clang/Tooling/Tooling.h)
  add_library(hlir_frontend lib/frontend/Frontend.cpp)
  target_include_directories(hlir_frontend PRIVATE lib/frontend)
  target_include_directories(hlir_frontend SYSTEM PRIVATE ${LLVM_INC})
  target_compile_definitions(hlir_frontend PRIVATE HLIR_CLANG_RESOURCE_DIR="${LLVM_LIBDIR}/clang/${LLVM_MAJOR}")
  target_compile_options(hlir_frontend PRIVATE -fno-rtti)
  target_link_libraries(hlir_frontend PUBLIC hlir_support ${CLANG_CPP} LLVM-${LLVM_MAJOR})
  set(HLIR_HAVE_FRONTEND ON)
  message(STATUS "C frontend: enabled (${CLANG_CPP})")
else()
  message(STATUS "C frontend: disabled (needs libclang-cpp${LLVM_MAJOR}-dev)")
endif()

add_library(hlir_driver lib/driver/Pipeline.cpp)
target_link_libraries(hlir_driver PUBLIC hlir_entry hlir_semantics hlir_report hlir_smt hlir_ir hlir_support)

# ---- tools (the only place that may depend on several modules) ----
add_executable(hlir-opt tools/hlir-opt.cpp)
target_link_libraries(hlir-opt PRIVATE hlir_ir)

# backward-WP probe: P0 (default) is ir-only; P1 (--solve) adds hlir_smt for UNSAT pruning (BACKWARD_WP_P0_PLAN.md).
# Includes lib/ so it can reuse lib/semantics/{TermOps,UBConditions}.h -- the engine's ONE integer-UB definition
# (DESIGN §4.1), header-only, no hlir_semantics link.
add_executable(hlir-wp-probe tools/hlir-wp-probe.cpp)
target_link_libraries(hlir-wp-probe PRIVATE hlir_ir hlir_smt)
target_include_directories(hlir-wp-probe PRIVATE ${CMAKE_SOURCE_DIR}/lib)

add_executable(hlir-run tools/hlir-run.cpp)
target_link_libraries(hlir-run PRIVATE hlir_ir hlir_semantics)

# ---- tests ----
enable_testing()
add_executable(ir_tests test/ir/ir_tests.cpp)
target_link_libraries(ir_tests PRIVATE hlir_ir)
target_compile_definitions(ir_tests PRIVATE HLIR_TEST_DIR="${CMAKE_SOURCE_DIR}/test/ir")
add_test(NAME ir_tests COMMAND ir_tests)

add_executable(semantics_tests test/semantics/semantics_tests.cpp)
target_link_libraries(semantics_tests PRIVATE hlir_ir hlir_semantics)
target_compile_definitions(semantics_tests PRIVATE HLIR_TEST_DIR="${CMAKE_SOURCE_DIR}/test/semantics")
add_test(NAME semantics_tests COMMAND semantics_tests)

find_package(Python3 COMPONENTS Interpreter)
if(Python3_FOUND)
  add_test(NAME check_deps COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/scripts/check_deps.py)
endif()

add_executable(smt_tests test/smt/smt_tests.cpp)
target_link_libraries(smt_tests PRIVATE hlir_smt)
add_test(NAME smt_tests COMMAND smt_tests)

add_executable(hlir-sym tools/hlir-sym.cpp)
target_link_libraries(hlir-sym PRIVATE hlir_ir hlir_semantics hlir_smt)

add_executable(hlir-invariant tools/hlir-invariant.cpp)
target_link_libraries(hlir-invariant PRIVATE hlir_ir hlir_semantics hlir_smt hlir_entry hlir_model)
if(Python3_FOUND)
  add_test(NAME check_invariant COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/scripts/check_invariant.py $<TARGET_FILE:hlir-invariant>)
  set_tests_properties(check_invariant PROPERTIES TIMEOUT 600)
  # backward-WP P0 probe: assert the |S| / root-class gate numbers on frozen core fixtures (BACKWARD_WP_P0_PLAN.md §5).
  add_test(NAME check_wp_probe COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/test/wp/check_wp_probe.py $<TARGET_FILE:hlir-wp-probe>)
endif()


add_executable(symbolic_tests test/symbolic/symbolic_tests.cpp)
target_link_libraries(symbolic_tests PRIVATE hlir_ir hlir_semantics hlir_smt)
target_compile_definitions(symbolic_tests PRIVATE HLIR_TEST_DIR="${CMAKE_SOURCE_DIR}/test/symbolic" HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
add_test(NAME symbolic_tests COMMAND symbolic_tests)

target_compile_definitions(hlir-run PRIVATE HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
target_compile_definitions(hlir-sym PRIVATE HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")

add_executable(corpus_tests test/corpus/corpus_tests.cpp)
target_link_libraries(corpus_tests PRIVATE hlir_ir hlir_semantics hlir_smt)
target_compile_definitions(corpus_tests PRIVATE HLIR_CORPUS_DIR="${CMAKE_SOURCE_DIR}/test/corpus" HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
add_test(NAME corpus_tests COMMAND corpus_tests)

add_executable(hlir-entry tools/hlir-entry.cpp)
target_link_libraries(hlir-entry PRIVATE hlir_ir hlir_semantics hlir_smt hlir_entry)
target_compile_definitions(hlir-entry PRIVATE HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")

add_executable(entry_tests test/entry/entry_tests.cpp)
target_link_libraries(entry_tests PRIVATE hlir_ir hlir_semantics hlir_smt hlir_entry)
target_compile_definitions(entry_tests PRIVATE HLIR_TEST_DIR="${CMAKE_SOURCE_DIR}/test/entry" HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
add_test(NAME entry_tests COMMAND entry_tests)

add_executable(hlir-taint tools/hlir-taint.cpp)
target_link_libraries(hlir-taint PRIVATE hlir_driver)
target_compile_definitions(hlir-taint PRIVATE HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")

add_executable(taint_tests test/taint/taint_tests.cpp)
target_link_libraries(taint_tests PRIVATE hlir_ir hlir_semantics hlir_smt hlir_entry)
target_compile_definitions(taint_tests PRIVATE HLIR_ENTRY_DIR="${CMAKE_SOURCE_DIR}/test/entry" HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
add_test(NAME taint_tests COMMAND taint_tests)
set_tests_properties(taint_tests PROPERTIES TIMEOUT 900)

add_executable(iface_tests test/iface/iface_tests.cpp)
target_link_libraries(iface_tests PRIVATE hlir_iface)
target_compile_definitions(iface_tests PRIVATE HLIR_INTERFACES_DIR="${CMAKE_SOURCE_DIR}/models/interfaces")
add_test(NAME iface_tests COMMAND iface_tests)
add_executable(report_tests test/report/report_tests.cpp)
target_link_libraries(report_tests PRIVATE hlir_driver)
target_compile_definitions(report_tests PRIVATE HLIR_ENTRY_DIR="${CMAKE_SOURCE_DIR}/test/entry" HLIR_CORPUS_DIR="${CMAKE_SOURCE_DIR}/test/corpus" HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
add_test(NAME report_tests COMMAND report_tests)

if(Python3_FOUND)
  add_test(NAME sarif_smoke COMMAND sh -c "$<TARGET_FILE:hlir-taint> --spec ${CMAKE_SOURCE_DIR}/test/entry/copy_if_small.yaml ${CMAKE_SOURCE_DIR}/test/entry/copy_if_small.core --entry copy_if_small --libc --format sarif --output ${CMAKE_BINARY_DIR}/smoke.sarif; ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/scripts/check_sarif.py ${CMAKE_BINARY_DIR}/smoke.sarif")
endif()

add_executable(models_tests test/model/models_tests.cpp)
target_link_libraries(models_tests PRIVATE hlir_driver)
target_compile_definitions(models_tests PRIVATE HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
add_test(NAME models_tests COMMAND models_tests)

if(HLIR_HAVE_FRONTEND)
  add_executable(hlirgen tools/hlirgen.cpp)
  target_link_libraries(hlirgen PRIVATE hlir_frontend hlir_buildinfo)
  target_compile_options(hlirgen PRIVATE -fno-rtti)
  foreach(t hlir-run hlir-taint)
    target_link_libraries(${t} PRIVATE hlir_frontend)
    target_compile_definitions(${t} PRIVATE HLIR_WITH_FRONTEND=1)
  endforeach()
  add_executable(hlir-scan tools/hlir-scan.cpp)
  target_link_libraries(hlir-scan PRIVATE hlir_frontend hlir_scan hlir_driver hlir_buildinfo hlir_link)
  target_compile_options(hlir-scan PRIVATE -fno-rtti)
  target_compile_definitions(hlir-scan PRIVATE HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
  add_executable(scan_tests test/c/scan_tests.cpp)
  target_link_libraries(scan_tests PRIVATE hlir_frontend hlir_scan hlir_report hlir_ir hlir_semantics hlir_buildinfo hlir_link hlir_entry)
  target_compile_definitions(scan_tests PRIVATE HLIR_SCAN_FIXTURE_DIR="${CMAKE_SOURCE_DIR}/test/c/scan" HLIR_SCAN_BIN="$<TARGET_FILE:hlir-scan>")
  add_dependencies(scan_tests hlir-scan)
  add_test(NAME scan_tests COMMAND scan_tests)
  set_tests_properties(scan_tests PROPERTIES TIMEOUT 600)
  # seam③ differential oracle (BACKWARD_WP_P0_PLAN.md): forward findings vs backward --solve on the same sites must
  # not contradict. A standing cross-validator -- if any backward V becomes unsound it proves a real bug safe and
  # forward's finding there turns into a contradiction (nonzero exit). Needs both binaries.
  if(Python3_FOUND)
    add_test(NAME check_wp_oracle COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/test/wp/diff_oracle.py
             $<TARGET_FILE:hlir-scan> $<TARGET_FILE:hlir-wp-probe> ${CMAKE_SOURCE_DIR}/test/wp/bug.c
             --entry oob_guarded --entry div_zero --entry add_ovf --entry shift_amt --entry safe_stack
             --expect-uncovered-min 1)  # unreached_safe is never entered -> backward's SAFE there is the uncovered-bucket
    set_tests_properties(check_wp_oracle PROPERTIES TIMEOUT 600)
    add_dependencies(scan_tests hlir-wp-probe)  # ensure the probe is built for the oracle test
    # seam③ uncovered-bucket wired into the probe's own output: hlir-wp-probe --forward-coverage reads hlir-scan's
    # covered_lines and reports/tags SAFE proofs on code the forward search never executed (backward's unique payoff).
    add_test(NAME check_wp_fcov COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/test/wp/check_fcov.py
             $<TARGET_FILE:hlir-scan> $<TARGET_FILE:hlir-wp-probe> ${CMAKE_SOURCE_DIR}/test/wp/bug.c)
    set_tests_properties(check_wp_fcov PROPERTIES TIMEOUT 600)
  endif()
  # CVE regression suite: one vuln/fixed pair per CVE HLIR has detected on a real tree. See
  # test/c/cve/README.md for what it does and does not claim.
  add_executable(cve_tests test/c/cve_tests.cpp)
  target_link_libraries(cve_tests PRIVATE hlir_report)
  target_compile_definitions(cve_tests PRIVATE HLIR_CVE_FIXTURE_DIR="${CMAKE_SOURCE_DIR}/test/c/cve" HLIR_SCAN_BIN="$<TARGET_FILE:hlir-scan>")
  add_dependencies(cve_tests hlir-scan)
  add_test(NAME cve_tests COMMAND cve_tests)
  set_tests_properties(cve_tests PROPERTIES TIMEOUT 900)
  add_executable(c_tests test/c/c_tests.cpp)
  target_link_libraries(c_tests PRIVATE hlir_frontend hlir_driver)
  target_compile_definitions(c_tests PRIVATE HLIR_C_TEST_DIR="${CMAKE_SOURCE_DIR}/test/c" HLIR_CPP_TEST_DIR="${CMAKE_SOURCE_DIR}/test/cpp" HLIR_MODELS_DIR="${CMAKE_SOURCE_DIR}/models")
  add_test(NAME c_tests COMMAND c_tests)
  set_tests_properties(c_tests PROPERTIES TIMEOUT 600)
  find_program(NATIVE_CC NAMES clang clang-18 cc)
  find_program(NATIVE_CXX NAMES clang++ clang++-18 g++ c++)
  if(Python3_FOUND AND NATIVE_CC)
    # the interpreter's answers for UB-free C must equal the real compiler's
    add_test(NAME c_native_check COMMAND ${Python3_EXECUTABLE} ${CMAKE_SOURCE_DIR}/scripts/c_native_check.py ${NATIVE_CC} ${CMAKE_SOURCE_DIR}/test/c ${NATIVE_CXX} ${CMAKE_SOURCE_DIR}/test/cpp)
  endif()
endif()

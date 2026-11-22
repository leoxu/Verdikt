// Tests for the `entry` module (P5): spec parsing and diagnostics, type-driven initialisation, legality of generated
// models, seed solving (DESIGN.md §21.8 reproduced), harness generation and end-to-end analysis with replay.
#include <algorithm>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>

#include "hlir/entry/HarnessGen.h"
#include "hlir/entry/SeedSolver.h"
#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/semantics/Symbolic.h"

using namespace hlir;
using llvm::APInt;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; if (g_fail < 40) std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static std::string slurp(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }
static std::unique_ptr<smt::Solver> g_z3;

static bool contains(const std::vector<std::string> &v, const std::string &needle) {
  for (auto &s : v)
    if (s.find(needle) != std::string::npos) return true;
  return false;
}

struct Loaded {
  std::unique_ptr<Module> mod;
  entry::EntryFile ef;
  Diagnostics d;
  smt::TermManager tm;
  entry::InitPlan plan;
  bool ok = false;
};

static std::unique_ptr<Loaded> load(const std::string &core, const std::string &yaml, const std::string &fn) {
  auto L = std::make_unique<Loaded>();
  L->mod = parseModule(core, "m.core", L->d);
  if (!L->mod || L->d.hasErrors() || !verifyModule(*L->mod, {}, L->d)) { std::cerr << "bad core:\n" << L->d.str(); return L; }
  if (!entry::parseEntrySpec(yaml, "spec.yaml", L->ef, L->d)) return L;
  const entry::EntrySpec *es = L->ef.find(fn);
  if (!es) { L->d.error("no entry " + fn); return L; }
  L->ok = entry::buildInitPlan(*L->mod, L->ef, *es, L->tm, L->plan, L->d);
  return L;
}

// ---------------------------------------------------------------- spec / diagnostics
static void testSpecErrors() {
  const char *core = "core.func @f(ptr, i32) -> i32 {\n^entry(%p: ptr, %n: i32):\n  core.return %n\n}\n";
  auto bad = [&](const std::string &yaml, const std::string &needle, unsigned line) {
    auto L = load(core, yaml, yaml.find("function: g") != std::string::npos ? "g" : "f");
    bool found = false;
    for (auto &dg : L->d.all())
      if (dg.severity == Diag::Error && dg.message.find(needle) != std::string::npos && (!line || dg.loc.line == line)) found = true;
    CHECK(!L->ok && found, "expected error '" << needle << "' at line " << line << ", got: " << L->d.str());
  };
  bad("taint_entries:\n  - function: f\n    params:\n      n: { range: [5, 1] }\n", "empty range", 4);
  bad("taint_entries:\n  - function: f\n    params:\n      zz: { taint: value }\n", "no parameter named 'zz'", 4);
  bad("taint_entries:\n  - function: f\n    params:\n      n: { taint: pointee }\n", "non-pointer", 4);
  bad("taint_entries:\n  - function: f\n    params:\n      p: { taint: value }\n", "tainted pointer value", 4);
  bad("taint_entries:\n  - function: f\n    params:\n      n: { taint: value, type: int64_t }\n", "64 bits", 4);
  bad("taint_entries:\n  - function: f\n    params:\n      n: { taint: value, wat: 1 }\n", "unknown key 'wat'", 4);
  bad("taint_entries:\n  - function: f\n    params:\n      n: { taint: value, range: [0, 99999999999] }\n", "does not fit", 4);
  bad("taint_entries:\n  - function: g\n", "does not exist", 2);
  bad("taint_entries:\n  - function: f\n    params:\n      n: { taint: value }\n    relations:\n      - \"n >= m\"\n", "unknown parameter 'm'", 6);
  bad("taint_entries:\n  - function: f\n    params:\n      p: { taint: pointee, size: {min: 9, max: 3} }\n", "size.min > size.max", 4);
  bad("taint_entries:\n\tfoo\n", "tabs", 2);
  bad("defaults:\n  max_obj: abc\n", "integer", 2);
  {
    // size.from_param: the cross-top-level-parameter "pointer + length" idiom (nft_set_elem_init's key/klen shape).
    const char *core2 = "core.func @g(i32, ptr) -> i32 {\n^entry(%n: i32, %p: ptr):\n  core.return %n\n}\n";
    auto bad2 = [&](const std::string &yaml, const std::string &needle) {
      auto L = load(core2, yaml, "g");
      bool found = false;
      for (auto &dg : L->d.all())
        if (dg.severity == Diag::Error && dg.message.find(needle) != std::string::npos) found = true;
      CHECK(!L->ok && found, "expected error '" << needle << "', got: " << L->d.str());
    };
    bad2("taint_entries:\n  - function: g\n    params:\n      n: { taint: value }\n      p: { taint: pointee, size: { from_param: { name: nosuch } } }\n",
         "does not name an earlier scalar");
    bad2("taint_entries:\n  - function: g\n    params:\n      n: { taint: value }\n      p: { taint: pointee, size: { from_param: { name: n }, min: 4 } }\n",
         "cannot be combined with min/max");
    bad2("taint_entries:\n  - function: g\n    params:\n      n: { taint: value }\n      p: { taint: pointee, kind: cstring, size: { from_param: { name: n } } }\n",
         "does not apply to kind: cstring");
    // ordering is enforced the same way `elements.count` already enforces it against `out.params`: a buffer
    // parameter declared BEFORE the scalar it names cannot see that scalar yet (it isn't planned until later).
    const char *core3 = "core.func @h(ptr, i32) -> i32 {\n^entry(%p: ptr, %n: i32):\n  core.return %n\n}\n";
    auto L3 = load(core3, "taint_entries:\n  - function: h\n    params:\n      p: { taint: pointee, size: { from_param: { name: n } } }\n      n: { taint: value }\n", "h");
    bool found3 = false;
    for (auto &dg : L3->d.all())
      if (dg.severity == Diag::Error && dg.message.find("does not name an earlier scalar") != std::string::npos) found3 = true;
    CHECK(!L3->ok && found3, "size.from_param referencing a parameter declared LATER in the signature is rejected: " << L3->d.str());
  }
  // externally_mutable (double-fetch/TOCTOU, see FieldSpec::externallyMutable): the 'owned'-shaped restrictions --
  // only a plain pointer buffer parameter, not a scalar.
  bad("taint_entries:\n  - function: f\n    params:\n      n: { taint: value, externally_mutable: true }\n", "fields/at only apply to pointer parameters", 4);
}

// pointer fields of the pointee: spec errors, planning and the generated harness
static void testPointerFields() {
  const char *core = "core.func @t1(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n"
                     "core.func @t2(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n"
                     "core.func @f(ptr, i32) -> i32 {\n^entry(%p: ptr, %n: i32):\n  core.return %n\n}\n";
  auto bad = [&](const std::string &fields, const std::string &needle) {
    std::string yaml = "taint_entries:\n  - function: f\n    params:\n      p:\n        taint: pointee\n        size: { min: 16, max: 16 }\n        fields: " + fields + "\n";
    auto L = load(core, yaml, "f");
    bool found = false;
    for (auto &dg : L->d.all())
      if (dg.severity == Diag::Error && dg.message.find(needle) != std::string::npos) found = true;
    CHECK(!L->ok && found, "expected error '" << needle << "' for fields " << fields << ", got: " << L->d.str());
  };
  bad("[ { kind: buffer } ]", "no 'offset'");
  bad("[ { offset: 12, size: { min: 8, max: 8 } } ]", "does not fit");
  bad("[ { offset: 0 }, { offset: 4 } ]", "overlaps");
  bad("[ { offset: 0, kind: funcptr } ]", "needs 'targets'");
  bad("[ { offset: 0, kind: funcptr, targets: [nosuch] } ]", "does not exist");
  bad("[ { offset: 0, kind: buffer, targets: [t1] } ]", "only applies to funcptr");
  bad("[ { offset: 0, wat: 1 } ]", "unknown key 'wat'");
  bad("[ { offset: 0, kind: funcptr, targets: [t1], at: 4 } ]", "only applies to buffer");
  bad("[ { offset: 0, size: { min: 8, max: 8 }, at: 8 } ]", "outside the object");
  bad("[ { offset: 0, kind: funcptr, targets: [t1], same_alloc: { offset: 0 } } ]", "only applies to buffer");
  bad("[ { offset: 0, kind: buffer, same_alloc: { offset: 99 } } ]", "does not name an earlier");
  bad("[ { offset: 0, kind: buffer, size: { min: 8, max: 8 } }, { offset: 8, kind: buffer, same_alloc: { offset: 0 }, size: { min: 8, max: 8 } } ]", "cannot be combined with 'size'");
  bad("[ { offset: 0, kind: self } ]", "needs 'target'");
  bad("[ { offset: 0, kind: self, target: 99 } ]", "outside");
  bad("[ { offset: 0, kind: self, target: 8, size: { min: 8, max: 8 } } ]", "only has 'offset' and 'target'");
  bad("[ { offset: 0, kind: buffer, target: 8 } ]", "only applies to self");
  // externally_mutable (double-fetch/TOCTOU, see FieldSpec::externallyMutable): only a plain buffer field, and not
  // combined with same_alloc (a same_alloc field is a pure view, not its own allocated object to mark).
  bad("[ { offset: 0, kind: funcptr, targets: [t1], externally_mutable: true } ]", "only applies to buffer fields");
  bad("[ { offset: 0, kind: buffer, size: { min: 8, max: 8 } }, { offset: 8, kind: buffer, same_alloc: { offset: 0 }, externally_mutable: true } ]",
      "cannot be combined with 'externally_mutable'");
  {
    std::string yaml = "taint_entries:\n  - function: f\n    params:\n      n: { taint: value, fields: [ { offset: 0 } ] }\n";
    auto L = load(core, yaml, "f");
    CHECK(!L->ok, "fields on a scalar parameter are rejected");
  }
  // a good plan: nested fields, a function-pointer field with two targets, NULL allowed on one
  std::string yaml =
      "taint_entries:\n  - function: f\n    label: net\n    params:\n      p:\n        taint: pointee\n        size: { min: 32, max: 32 }\n"
      "        fields:\n"
      "          - { offset: 0, kind: buffer, taint: pointee, size: { min: 8, max: 16 }, fields: [ { offset: 0, kind: funcptr, targets: [t1, t2] } ] }\n"
      "          - { offset: 8, kind: buffer, taint: none, size: { min: 8, max: 8 }, nullable: true }\n";
  auto L = load(core, yaml, "f");
  CHECK(L->ok, "fields plan builds: " << L->d.str());
  if (!L->ok) return;
  {
    // a self link: the pointer value is the holder's own address (+ target); an empty list head
    const char *lcore = "core.func @g(ptr) -> i32 {\n^entry(%p: ptr):\n"
                        "  %c = core.const 8 : i64\n  %q = core.ptr_add %p, %c : ptr\n  %a = core.load %q : ptr\n"
                        "  %e = core.ptr_cmp eq %a, %q : bool\n  %r = core.b2i %e : i32\n  core.return %r\n}\n";
    std::string y2 = "taint_entries:\n  - function: g\n    params:\n      p:\n        taint: none\n        size: { min: 24, max: 24 }\n"
                     "        fields: [ { offset: 8, kind: self, target: 8 }, { offset: 16, kind: self, target: 8 } ]\n";
    auto L2 = load(lcore, y2, "g");
    CHECK(L2->ok, "self fields plan: " << L2->d.str());
    if (L2->ok) {
      std::string h2 = entry::generateHarness(L2->plan);
      Diagnostics d3;
      auto m3 = parseModule(std::string(lcore) + h2, "m.core", d3);
      CHECK(m3 && !d3.hasErrors(), "self harness parses: " << d3.str());
      if (m3) {
        TableEnv env2;
        RunConfig cfg2;
        auto r2 = Interpreter(*m3).run(entry::harnessName(L2->plan), {}, env2, cfg2);
        CHECK(r2.status == RunStatus::Returned && r2.returnValue && r2.returnValue->getZExtValue() == 1, "the link at +8 holds the address of +8 (list_empty): " << runStatusName(r2.status) << " " << r2.message);
      }
    }
  }
  {
    // `at`: the argument points into the middle of its object (container_of); p - 8 is the object start
    const char *acore = "core.func @a(ptr) -> i32 {\n^entry(%p: ptr):\n  %m8 = core.const -8 : i64\n  %q = core.ptr_add %p, %m8 : ptr\n"
                        "  %d = core.ptr_diff %p, %q : i64\n  %eight = core.const 8 : i64\n  %e = core.icmp eq %d, %eight : bool\n  %r = core.b2i %e : i32\n  core.return %r\n}\n";
    std::string y3 = "taint_entries:\n  - function: a\n    params:\n      p: { taint: none, size: { min: 24, max: 24 }, at: 8 }\n";
    auto L3 = load(acore, y3, "a");
    CHECK(L3->ok && L3->plan.params[0].at == 8, "param at is planned: " << L3->d.str());
    if (L3->ok) {
      Diagnostics d4;
      auto m4 = parseModule(std::string(acore) + entry::generateHarness(L3->plan), "m.core", d4);
      CHECK(m4 && !d4.hasErrors(), "at harness parses: " << d4.str());
      if (m4) {
        TableEnv env3;
        RunConfig cfg3;
        auto r3 = Interpreter(*m4).run(entry::harnessName(L3->plan), {}, env3, cfg3);
        CHECK(r3.status == RunStatus::Returned && r3.returnValue && r3.returnValue->getZExtValue() == 1, "the argument is object+8: " << runStatusName(r3.status));
      }
    }
    std::string y4 = "taint_entries:\n  - function: a\n    params:\n      p: { taint: none, size: { min: 8, max: 8 }, at: 8 }\n";
    auto L4 = load(acore, y4, "a");
    CHECK(!L4->ok, "param at outside the object is rejected");
  }
  {
    // same_alloc: the base/end, start/end, bottom/top pointer-pair idiom (NFS xdr_stream's p/end, QuickJS
    // BCReaderState, Duktape valstack_top/bottom) -- a sibling field is a one-past-the-end view into an earlier
    // field's own allocation, not an independently-sized object of its own, so the two pointers are provably into
    // the same allocation: ptr_diff(end, base) must equal the base field's real (here fixed) size.
    const char *sacore = "core.func @sa(ptr) -> i32 {\n^entry(%p: ptr):\n"
                         "  %o1 = core.const 0 : i64\n  %f1 = core.ptr_add %p, %o1 : ptr\n  %base = core.load %f1 : ptr\n"
                         "  %o2 = core.const 8 : i64\n  %f2 = core.ptr_add %p, %o2 : ptr\n  %end = core.load %f2 : ptr\n"
                         "  %d = core.ptr_diff %end, %base : i64\n  %sixteen = core.const 16 : i64\n"
                         "  %e = core.icmp eq %d, %sixteen : bool\n  %r = core.b2i %e : i32\n  core.return %r\n}\n";
    std::string y5 = "taint_entries:\n  - function: sa\n    params:\n      p:\n        taint: none\n        size: { min: 16, max: 16 }\n"
                     "        fields:\n"
                     "          - { offset: 0, kind: buffer, taint: none, size: { min: 16, max: 16 } }\n"
                     "          - { offset: 8, kind: buffer, same_alloc: { offset: 0 } }\n";
    auto L5 = load(sacore, y5, "sa");
    CHECK(L5->ok, "same_alloc plan builds: " << L5->d.str());
    if (L5->ok) {
      CHECK(L5->plan.params[0].fields.size() == 2 && L5->plan.params[0].fields[1].sameAllocIndex && *L5->plan.params[0].fields[1].sameAllocIndex == 0,
            "the end field is planned as a same_alloc view of the base field");
      std::string h5 = entry::generateHarness(L5->plan);
      CHECK(h5.find("core.heap_alloc") != std::string::npos, "the base field still gets a real allocation");
      // the end field must NOT get its own heap_alloc: exactly two allocations in the whole harness (the top-level
      // `p` parameter object itself, plus its base field `p.0`) -- the end field is a ptr_add off the base field's
      // allocation instead of a third independent one.
      size_t allocs = 0, pos = 0;
      while ((pos = h5.find("core.heap_alloc", pos)) != std::string::npos) { ++allocs; pos += 1; }
      CHECK(allocs == 2, "same_alloc field does not get an independent allocation: " << allocs << " heap_alloc(s)");
      CHECK(h5.find("name=\"p.8\"") == std::string::npos, "the end field is not given its own named allocation");
      Diagnostics d5;
      auto m5 = parseModule(std::string(sacore) + h5, "m.core", d5);
      CHECK(m5 && !d5.hasErrors(), "same_alloc harness parses: " << d5.str());
      if (m5) {
        TableEnv env5;
        RunConfig cfg5;
        auto r5 = Interpreter(*m5).run(entry::harnessName(L5->plan), {}, env5, cfg5);
        CHECK(r5.status == RunStatus::Returned && r5.returnValue && r5.returnValue->getZExtValue() == 1,
              "end is exactly base+16 (one past the shared allocation's real size): " << runStatusName(r5.status) << " " << r5.message);
      }
    }
  }
  {
    // externally_mutable: true (double-fetch/TOCTOU, see FieldSpec/ParamSpec::externallyMutable): the plan carries
    // the flag through to the field (PlannedField::externallyMutable), and the generated harness's core.heap_alloc
    // carries the `externally_mutable` attribute Machine.h's Opc::HeapAlloc reads to call markExternallyMutable() --
    // while a field that does NOT declare it gets no such attribute (default-off).
    std::string y6 = "taint_entries:\n  - function: f\n    params:\n      p:\n        taint: pointee\n        size: { min: 16, max: 16 }\n"
                     "        fields:\n"
                     "          - { offset: 0, kind: buffer, taint: pointee, size: { min: 8, max: 8 }, externally_mutable: true }\n"
                     "          - { offset: 8, kind: buffer, taint: pointee, size: { min: 8, max: 8 } }\n";
    auto L6 = load(core, y6, "f");
    CHECK(L6->ok, "externally_mutable field plan builds: " << L6->d.str());
    if (L6->ok) {
      CHECK(L6->plan.params[0].fields.size() == 2 && L6->plan.params[0].fields[0].externallyMutable && !L6->plan.params[0].fields[1].externallyMutable,
            "externally_mutable is planned per-field, true only where declared");
      std::string h6 = entry::generateHarness(L6->plan);
      CHECK(h6.find("name=\"p.0\"") != std::string::npos, "field p.0 is allocated");
      size_t allocLine0 = h6.find("name=\"p.0\"");
      size_t stmtStart0 = h6.rfind("\n  %", allocLine0);
      CHECK(stmtStart0 != std::string::npos && h6.substr(stmtStart0, allocLine0 - stmtStart0).find("externally_mutable") != std::string::npos,
            "p.0's core.heap_alloc carries the externally_mutable attribute:\n" << h6);
      size_t allocLine1 = h6.find("name=\"p.8\"");
      size_t stmtStart1 = h6.rfind("\n  %", allocLine1);
      CHECK(stmtStart1 != std::string::npos && h6.substr(stmtStart1, allocLine1 - stmtStart1).find("externally_mutable") == std::string::npos,
            "p.8 (not declared externally_mutable) does NOT carry the attribute -- default-off:\n" << h6);
      Diagnostics d6;
      auto m6 = parseModule(std::string(core) + h6, "m.core", d6);
      CHECK(m6 && !d6.hasErrors(), "externally_mutable harness parses: " << d6.str());
    }
    // a non-pointer parameter rejects externally_mutable the same way it rejects owned/fields/at.
    std::string y7 = "taint_entries:\n  - function: t1\n    params:\n      x: { taint: value, externally_mutable: true }\n";
    const char *core7 = "core.func @t1(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n";
    auto L7 = load(core7, y7, "t1");
    CHECK(!L7->ok, "externally_mutable on a scalar parameter is rejected");
  }
  auto &pl = L->plan.params[0];
  CHECK(pl.fields.size() == 2 && pl.fields[0].name == "p.0" && pl.fields[0].fields.size() == 1 && pl.fields[0].fields[0].name == "p.0.0", "planned field names");
  CHECK(pl.fields[0].fields[0].kind == entry::PlannedField::FuncPtr && pl.fields[0].fields[0].targets.size() == 2 && pl.fields[0].fields[0].selector, "funcptr field with a selector input");
  CHECK(pl.fields[1].isNull && !pl.fields[1].tainted, "nullable untainted field");
  std::string h = entry::generateHarness(L->plan);
  CHECK(h.find("core.func_addr @t1") != std::string::npos && h.find("core.func_addr @t2") != std::string::npos, "harness selects between the targets");
  CHECK(h.find("name=\"p.0\"") != std::string::npos && h.find("name=\"p.8\"") != std::string::npos, "harness allocates one object per field");
  Diagnostics d;
  auto mod = parseModule(std::string(core) + h, "m.core", d);
  CHECK(mod && !d.hasErrors() && verifyModule(*mod, {}, d), "module with the generated harness verifies: " << d.str());
  // run it: the pointer fields are stored, so the harness returns and the child objects exist
  if (mod) {
    auto m0 = entry::SeedSolver(L->tm, *g_z3, L->plan).benign();
    CHECK(m0.result == smt::SatResult::Sat, "seed exists for a spec with pointer fields");
    TableEnv env;
    for (auto &kv : m0.model) env.set(kv.first, kv.second.getSExtValue());
    RunConfig cfg;
    auto r = Interpreter(*mod).run(entry::harnessName(L->plan), {}, env, cfg);
    CHECK(r.status == RunStatus::Returned, "harness runs: " << runStatusName(r.status) << " " << r.message);
  }
}

// preconditions: elements / where in the spec, the preconditions file, the harness, and the engine's repair of a seed
static void testPreconditions() {
  const char *core = "core.func @f(ptr, i32) -> i32 {\n^entry(%p: ptr, %n: i32):\n  %z = core.const 0 : i32\n  core.return %z\n}\n";
  auto bad = [&](const std::string &p, const std::string &needle) {
    std::string yaml = "taint_entries:\n  - function: f\n    params:\n      p: { taint: pointee, size: { min: 16, max: 16 }, " + p + " }\n      n: { taint: value, type: int }\n";
    auto L = load(core, yaml, "f");
    bool found = false;
    for (auto &dg : L->d.all()) if (dg.severity == Diag::Error && dg.message.find(needle) != std::string::npos) found = true;
    CHECK(!L->ok && found, "expected error '" << needle << "' for " << p << ", got: " << L->d.str());
  };
  bad("elements: { range: [0, 9] }", "needs a 'type'");
  bad("elements: { type: int32_t }", "needs a range");
  bad("elements: { type: wat_t, range: [0, 9] }", "unknown type name");
  bad("elements: { type: uint8_t, range: [0, 300] }", "does not fit");
  bad("elements: { type: int32_t, range: [0, 9], count: nosuch }", "not an integer parameter");
  bad("where: [ { type: int32_t, range: [0, 9] } ]", "needs an 'offset'");
  bad("where: [ { offset: 14, type: int32_t, range: [0, 9] } ]", "outside the object");
  bad("where: [ { offset: 0, type: int32_t, range: [0, 9], wat: 1 } ]", "unknown key 'wat'");
  {
    std::string yaml = "taint_entries:\n  - function: f\n    params:\n      n: { taint: value, type: int, elements: { type: int32_t, range: [0, 9] } }\n";
    auto L = load(core, yaml, "f");
    CHECK(!L->ok, "elements on a scalar parameter are rejected");
  }
  // a good plan, and the preconditions file merged onto an existing spec
  std::string yaml = "taint_entries:\n  - function: f\n    params:\n      p: { taint: pointee, size: { min: 16, max: 16 } }\n      n: { taint: value, type: int }\n";
  entry::EntryFile ef;
  Diagnostics d;
  auto mod = parseModule(core, "m.core", d);
  CHECK(mod && entry::parseEntrySpec(yaml, "spec.yaml", ef, d), "spec parses");
  const char *pre = "preconditions:\n  - function: f\n    params:\n      n: { range: [0, 4] }\n"
                    "      p: { elements: { type: int32_t, range: [0, 99], count: n }, where: [ { offset: 12, type: int32_t, range: [-3, 0] } ] }\n"
                    "    relations: [ \"(size_t)n <= size(p)\" ]\n  - function: other\n    params: { zz: { range: [0, 1] } }\n";
  CHECK(entry::applyPreconditions(pre, "pre.yaml", ef, d), "preconditions apply: " << d.str());
  smt::TermManager tm;
  entry::InitPlan plan;
  CHECK(entry::buildInitPlan(*mod, ef, *ef.find("f"), tm, plan, d), "plan with preconditions builds: " << d.str());
  bool relNamed = false, rangeNamed = false;
  for (auto &c : plan.constraints) {
    relNamed |= c.name.find("pre.rel.") == 0 && c.name.find("@pre.yaml:6") != std::string::npos;
    rangeNamed |= c.name.find("pre.n.range[0,4]@pre.yaml:4") == 0;
  }
  CHECK(relNamed && rangeNamed, "constraints from the preconditions file are named pre.* and point at it");
  CHECK(plan.params[0].elements.size() == 1 && plan.params[0].elements[0].elemBytes == 4 && plan.params[0].wheres.size() == 1, "elements and where are planned");
  std::string h = entry::generateHarness(plan);
  CHECK(h.find("name=\"pre.p.elements@pre.yaml:5\"") != std::string::npos && h.find("name=\"pre.p.where[12]@pre.yaml:5\"") != std::string::npos, "the harness states each as a named assumption");
  Diagnostics d2;
  auto m2 = parseModule(std::string(core) + h, "m.core", d2);
  CHECK(m2 && !d2.hasErrors() && verifyModule(*m2, {}, d2), "harness with preconditions verifies: " << d2.str());
  // an unknown parameter name is an error
  entry::EntryFile ef2;
  Diagnostics d3;
  entry::parseEntrySpec(yaml, "spec.yaml", ef2, d3);
  entry::applyPreconditions("preconditions:\n  - function: f\n    params:\n      p: { range: [0, 1] }\n      n: { nullable: true }\n", "pre.yaml", ef2, d3);
  // (p exists, so this is fine; the next one names a parameter the plan does not have)
  entry::applyPreconditions("preconditions:\n  - function: f\n    params:\n      zz: { range: [0, 1] }\n", "pre2.yaml", ef2, d3);
  entry::InitPlan plan2;
  smt::TermManager tm2;
  CHECK(!entry::buildInitPlan(*mod, ef2, *ef2.find("f"), tm2, plan2, d3), "a precondition on a parameter the function does not have is an error");
}

static void testYamlStyles() {
  // block style with comments, quotes, nested maps and sequences, and a list item that starts an inline map
  const char *y =
      "# attacker model\n"
      "defaults:\n"
      "  max_obj: 0x100   # bytes\n"
      "taint_entries:\n"
      "  - function: f\n"
      "    label: \"file input\"\n"
      "    params:\n"
      "      p:\n"
      "        taint: pointee\n"
      "        size:\n"
      "          min: 2\n"
      "          max: 300\n"
      "      n:\n"
      "        taint: value\n"
      "        range: [-5, 5]\n"
      "        enum:\n"
      "          - 1\n"
      "          - 2\n"
      "    relations:\n"
      "      - n <= 3\n"
      "  - function: g\n";
  Diagnostics d;
  entry::EntryFile ef;
  bool ok = entry::parseEntrySpec(y, "s.yaml", ef, d);
  CHECK(ok && ef.entries.size() == 2, "block-style spec parses: " << d.str());
  if (!ok) return;
  CHECK(ef.defaults.maxObj == 256, "hex integer and trailing comment");
  auto &e = ef.entries[0];
  CHECK(e.label == "file input" && e.params.size() == 2 && e.params[0].sizeMax == 300u && e.params[1].lo == -5 && e.params[1].enumValues.size() == 2, "values read");
  CHECK(e.relations.size() == 1 && e.relations[0].text == "n <= 3" && e.relations[0].line == 20, "relation keeps its spec line");
  CHECK(e.params[1].line == 14, "parameter line numbers");
}

// ---------------------------------------------------------------- the §21.8 example
static void testCopyIfSmall() {
  auto L = load(slurp(HLIR_TEST_DIR "/copy_if_small.core"), slurp(HLIR_TEST_DIR "/copy_if_small.yaml"), "copy_if_small");
  CHECK(L->ok, "plan builds: " << L->d.str());
  if (!L->ok) return;
  CHECK(L->plan.constraints.size() == 2, "two named constraints");
  CHECK(L->plan.constraints[0].name.find("init.src.size[1,4096]@") == 0, "size constraint is named after the parameter and spec line: " << L->plan.constraints[0].name);
  CHECK(L->plan.constraints[0].name.find(":10") != std::string::npos, "size constraint points at spec line 10");
  CHECK(L->plan.params.size() == 3 && L->plan.params[0].kind == entry::PlannedParam::Buffer && !L->plan.params[0].tainted, "dst: untainted buffer");
  CHECK(L->plan.params[2].kind == entry::PlannedParam::Scalar && L->plan.params[2].tainted && L->plan.params[2].isSigned, "len: tainted signed scalar");

  entry::SeedSolver ss(L->tm, *g_z3, L->plan);
  entry::Seed legal = ss.legality();
  CHECK(legal.result == smt::SatResult::Sat, "C_init is satisfiable");
  entry::Seed m0 = ss.benign();
  CHECK(m0.result == smt::SatResult::Sat && m0.model.at("p.len") == 64 && m0.model.at("size.src") == 64, "M0 is the benign seed len=64, size(src)=64");
  std::map<std::string, entry::Seed> byLabel;
  for (auto &s : ss.boundary()) byLabel.emplace(s.label, s);
  auto &imax = byLabel.at("len=max");
  CHECK(imax.result == smt::SatResult::Unsat, "len=INT_MAX is outside the contract");
  CHECK(contains(imax.core, "init.rel.") && contains(imax.core, "init.src.size[1,4096]") && contains(imax.core, "seed.len=max"),
        "the core names exactly the relation, the size bound and the seed");
  auto &imin = byLabel.at("len=min");
  CHECK(imin.result == smt::SatResult::Sat && imin.model.at("p.len").isMinSignedValue(), "len=INT_MIN is legal (the dangerous input)");
  CHECK(byLabel.at("len=size(src)").result == smt::SatResult::Sat && byLabel.at("len=size(src)+1").result == smt::SatResult::Unsat, "size(src) is reachable, size(src)+1 is not");
  CHECK(byLabel.at("len=-1").result == smt::SatResult::Sat, "negative lengths are unconstrained by the contract");

  // every model of C_init is legal: check every constraint on the model by evaluation
  auto seeds = ss.diverse(25);
  CHECK(seeds.size() == 25, "25 diverse models");
  std::set<std::string> distinct;
  for (auto &s : seeds) {
    smt::Assignment asg(s.model.begin(), s.model.end());
    for (auto &c : L->plan.constraints) CHECK(smt::evalTerm(c.term, asg).getBoolValue(), "model violates " << c.name);
    uint64_t sz = s.model.at("size.src").getZExtValue();
    CHECK(sz >= 1 && sz <= 4096, "size in range");
    distinct.insert(std::to_string(s.model.at("p.len").getSExtValue()) + "/" + std::to_string(sz));
  }
  CHECK(distinct.size() == 25, "blocking clauses make the models pairwise distinct");
}

// ---------------------------------------------------------------- spec contradictions point back at the spec
static void testContradiction() {
  const char *core = "core.func @f(ptr, i32) -> i32 {\n^entry(%p: ptr, %n: i32):\n  core.return %n\n}\n";
  const char *yaml =
      "taint_entries:\n"
      "  - function: f\n"
      "    params:\n"
      "      p: { taint: pointee, size: { min: 1, max: 10 } }\n"
      "      n: { taint: value, type: int, range: [0, 100] }\n"
      "    relations:\n"
      "      - \"(size_t)n >= size(p) + 200\"\n";
  auto L = load(core, yaml, "f");
  CHECK(L->ok, "contradictory specs still build a plan: " << L->d.str());
  if (!L->ok) return;
  entry::SeedSolver ss(L->tm, *g_z3, L->plan);
  entry::Seed s = ss.legality();
  CHECK(s.result == smt::SatResult::Unsat, "contradiction detected");
  CHECK(contains(s.core, "init.rel.") && contains(s.core, "init.p.size[1,10]@spec.yaml:4") && contains(s.core, "init.n.range[0,100]@spec.yaml:5"),
        "core lists relation, size and range with their spec lines");
}

// ---------------------------------------------------------------- types: bool, enum, unsigned range, nullable
static void testTypes() {
  const char *core =
      "core.func @f(bool, i32, i16, ptr) -> i32 {\n^entry(%flag: bool, %mode: i32, %port: i16, %p: ptr):\n  %z = core.const 0 : i32\n  core.return %z\n}\n";
  const char *yaml =
      "taint_entries:\n"
      "  - function: f\n"
      "    label: network\n"
      "    params:\n"
      "      flag: { taint: value }\n"
      "      mode: { taint: value, enum: [3, 5, 9], type: int }\n"
      "      port: { taint: value, type: uint16_t, range: [1024, 65535] }\n"
      "      p: { taint: pointee, nullable: true, size: { min: 4, max: 32 } }\n";
  auto L = load(core, yaml, "f");
  CHECK(L->ok, "plan: " << L->d.str());
  if (!L->ok) return;
  entry::SeedSolver ss(L->tm, *g_z3, L->plan);
  entry::Seed m0 = ss.benign();
  CHECK(m0.result == smt::SatResult::Sat && m0.model.at("p.mode") == 3, "benign enum value is the first one");
  CHECK(m0.model.at("p.port").getZExtValue() == 1024, "benign port is clamped into its range: " << m0.model.at("p.port").getZExtValue());
  CHECK(m0.model.at("null.p").isZero() && m0.model.at("p.flag").isZero(), "benign: non-null pointer, false flag");
  bool sawNull = false, sawNonNull = false;
  for (auto &s : ss.diverse(40)) {
    smt::Assignment asg(s.model.begin(), s.model.end());
    int64_t mode = s.model.at("p.mode").getSExtValue();
    CHECK(mode == 3 || mode == 5 || mode == 9, "enum value legal: " << mode);
    uint64_t port = s.model.at("p.port").getZExtValue();
    CHECK(port >= 1024 && port <= 65535, "port legal: " << port);
    uint64_t sz = s.model.at("size.p").getZExtValue();
    CHECK(sz >= 4 && sz <= 32, "size legal: " << sz);
    (s.model.at("null.p").isZero() ? sawNonNull : sawNull) = true;
  }
  CHECK(sawNull && sawNonNull, "a nullable pointer takes both values across diverse seeds");
  // boundary: unsigned range limits are the only legal extremes
  std::map<std::string, entry::Seed> byLabel;
  for (auto &s : ss.boundary()) byLabel.emplace(s.label, s);
  CHECK(byLabel.at("port=max").result == smt::SatResult::Sat, "port=65535 is legal (u16 max equals range hi)");
  CHECK(byLabel.at("port=0").result == smt::SatResult::Unsat, "port=0 is below the range");
  CHECK(byLabel.at("mode=0").result == smt::SatResult::Unsat || byLabel.count("mode=0") == 0, "mode=0 is not an enum value");

  // the generated harness parses, verifies and runs concretely on the interpreter
  std::string h = entry::generateHarness(L->plan);
  Diagnostics d;
  auto full = parseModule(std::string(core) + h, "h.core", d);
  CHECK(full && !d.hasErrors() && verifyModule(*full, {}, d), "harness verifies: " << d.str());
}

// ---------------------------------------------------------------- end-to-end analysis (harness + symbolic execution + replay)
struct Analysis {
  std::set<std::string> kinds;
  bool complete = false, allReplayed = true;
  unsigned findings = 0;
};

static Analysis analyze(const std::string &core, const std::string &yaml, const std::string &fn, bool libc) {
  Analysis a;
  std::string text = core + (libc ? "\n" + slurp(HLIR_MODELS_DIR "/libc.core") : "");
  auto L = load(text, yaml, fn);
  CHECK(L->ok, "analysis setup: " << L->d.str());
  if (!L->ok) return a;
  std::string h = entry::generateHarness(L->plan);
  Diagnostics d;
  auto full = parseModule(text + "\n" + h, "full.core", d);
  CHECK(full && !d.hasErrors() && verifyModule(*full, {}, d), "harness verifies: " << d.str());
  if (!full) return a;
  smt::TermManager tm;
  SymbolicExecutor ex(*full, tm, *g_z3);
  SymConfig cfg;
  cfg.maxPaths = 2000;
  SymResult r = ex.run(entry::harnessName(L->plan), {}, cfg);
  a.complete = r.complete;
  Interpreter in(*full);
  for (auto &f : r.findings) {
    ++a.findings;
    a.kinds.insert(f.ub ? ubKindName(f.ub->kind) : "assert");
    SeqEnv env(f.nondets, f.inputs);
    RunResult rr = in.run(entry::harnessName(L->plan), {}, env);
    bool ok = f.ub ? (rr.status == RunStatus::UB && rr.ub && rr.ub->kind == f.ub->kind) : rr.status == RunStatus::AssertFailed;
    if (!ok) a.allReplayed = false;
  }
  return a;
}

// ---------------------------------------------------------------- C++: `this` runs the class's real constructor
// Mangled Itanium symbols (no clang involved): `Foo::Foo()`/`Foo::bar()`, `Baz::Baz(int)`, `Qux::Qux(int*)`/`Qux::zap()`,
// `Amb::Amb(int)` + `Amb::Amb(bool)` (two same-arity candidates: ambiguous) + `Amb::use()`, `NoCtor1::use()` (no ctor at all).
static void testCtorConstruction() {
  // a this-only constructor sets a sentinel the method asserts on: if the harness skipped it, `this` stays zeroed and
  // the sentinel would be 0, not 42.
  const char *core1 =
      "core.func @_ZN3FooC1Ev(ptr) -> void {\n^entry(%this: ptr):\n  %c = core.const 42 : i32\n  core.store %c, %this\n  core.return\n}\n"
      "core.func @_ZN3Foo3barEv(ptr) -> void {\n^entry(%this: ptr):\n  %v = core.load %this : i32\n  %c = core.const 42 : i32\n"
      "  %eq = core.icmp eq %v, %c : bool\n  core.assert %eq\n  core.return\n}\n";
  auto L1 = load(core1, "taint_entries:\n  - function: _ZN3Foo3barEv\n    params: {}\n", "_ZN3Foo3barEv");
  CHECK(L1->ok, "plan: " << L1->d.str());
  if (L1->ok) {
    CHECK(L1->plan.ctorFunction == "_ZN3FooC1Ev", "the this-only constructor of Foo is found: '" << L1->plan.ctorFunction << "'");
    CHECK(L1->plan.ctorExtraParamTys.empty(), "no extra parameters beyond this");
    std::string h = entry::generateHarness(L1->plan);
    CHECK(h.find("core.call @_ZN3FooC1Ev(") != std::string::npos, "the harness calls the constructor: " << h);
  }
  Analysis a1 = analyze(core1, "taint_entries:\n  - function: _ZN3Foo3barEv\n    params: {}\n", "_ZN3Foo3barEv", false);
  CHECK(a1.complete && a1.findings == 0, "the constructor ran: the sentinel is 42, the assert in bar() holds (" << a1.findings << " finding(s))");

  // control: a method of a class with no constructor function in the module leaves `this` zeroed, so the same shape
  // of assert (now checking for 42) fires — this confirms the positive result above is from the constructor running,
  // not from some other effect.
  const char *core1b =
      "core.func @_ZN7NoCtor13useEv(ptr) -> void {\n^entry(%this: ptr):\n  %v = core.load %this : i32\n  %c = core.const 42 : i32\n"
      "  %eq = core.icmp eq %v, %c : bool\n  core.assert %eq\n  core.return\n}\n";
  auto Lb = load(core1b, "taint_entries:\n  - function: _ZN7NoCtor13useEv\n    params: {}\n", "_ZN7NoCtor13useEv");
  CHECK(Lb->ok && Lb->plan.ctorFunction.empty(), "no constructor exists for a class with none: '" << Lb->plan.ctorFunction << "'");
  Analysis ab = analyze(core1b, "taint_entries:\n  - function: _ZN7NoCtor13useEv\n    params: {}\n", "_ZN7NoCtor13useEv", false);
  CHECK(ab.complete && ab.kinds == std::set<std::string>{"assert"}, "without a constructor, `this` is zeroed: the ==42 assert fails as expected");

  // a constructor with extra scalar (non-pointer) parameters, covering a default-argument constructor such as
  // XMLDocument(bool = true, Whitespace = ...): `core` carries no default-argument value, so the harness passes 0.
  const char *core2 =
      "core.func @_ZN3BazC1Ei(ptr, i32) -> void {\n^entry(%this: ptr, %x: i32):\n  %c = core.const 100 : i32\n  %s = core.add %x, %c : i32\n  core.store %s, %this\n  core.return\n}\n"
      "core.func @_ZN3Baz3useEv(ptr) -> void {\n^entry(%this: ptr):\n  %v = core.load %this : i32\n  %c = core.const 100 : i32\n"
      "  %eq = core.icmp eq %v, %c : bool\n  core.assert %eq\n  core.return\n}\n";
  auto L2 = load(core2, "taint_entries:\n  - function: _ZN3Baz3useEv\n    params: {}\n", "_ZN3Baz3useEv");
  CHECK(L2->ok, "plan: " << L2->d.str());
  if (L2->ok) {
    CHECK(L2->plan.ctorFunction == "_ZN3BazC1Ei", "the constructor with one extra i32 parameter is found");
    CHECK(L2->plan.ctorExtraParamTys.size() == 1 && !L2->plan.ctorExtraParamTys[0]->isBool() && L2->plan.ctorExtraParamTys[0]->width() == 32,
          "the extra parameter's type (i32) is recorded");
  }
  Analysis a2 = analyze(core2, "taint_entries:\n  - function: _ZN3Baz3useEv\n    params: {}\n", "_ZN3Baz3useEv", false);
  CHECK(a2.complete && a2.findings == 0, "the constructor ran with its extra i32 passed as 0: 0+100 == 100, the assert holds");

  // a constructor whose only extra parameter is a pointer is not called: it would need an object the way an entry's
  // own pointer parameters do, which this (intentionally scoped-down) mechanism does not attempt.
  const char *core3 =
      "core.func @_ZN3QuxC1EPi(ptr, ptr) -> void {\n^entry(%this: ptr, %p: ptr):\n  core.return\n}\n"
      "core.func @_ZN3Qux3zapEv(ptr) -> void {\n^entry(%this: ptr):\n  core.return\n}\n";
  auto L3 = load(core3, "taint_entries:\n  - function: _ZN3Qux3zapEv\n    params: {}\n", "_ZN3Qux3zapEv");
  CHECK(L3->ok && L3->plan.ctorFunction.empty(), "a constructor with a pointer extra parameter is not used: '" << L3->plan.ctorFunction << "'");

  // two constructors tying for fewest extra parameters (one int, one bool: both compile from a defaulted argument of
  // a different type) are ambiguous: neither is used, `this` stays zeroed rather than guessing.
  const char *core4 =
      "core.func @_ZN3AmbC1Ei(ptr, i32) -> void {\n^entry(%this: ptr, %x: i32):\n  core.return\n}\n"
      "core.func @_ZN3AmbC1Eb(ptr, bool) -> void {\n^entry(%this: ptr, %b: bool):\n  core.return\n}\n"
      "core.func @_ZN3Amb3useEv(ptr) -> void {\n^entry(%this: ptr):\n  core.return\n}\n";
  auto L4 = load(core4, "taint_entries:\n  - function: _ZN3Amb3useEv\n    params: {}\n", "_ZN3Amb3useEv");
  CHECK(L4->ok && L4->plan.ctorFunction.empty(), "two equally-minimal constructor candidates are ambiguous: '" << L4->plan.ctorFunction << "'");
}

static void testEndToEnd() {
  std::string core = slurp(HLIR_TEST_DIR "/copy_if_small.core");
  std::string yaml = slurp(HLIR_TEST_DIR "/copy_if_small.yaml");
  Analysis contract = analyze(core, yaml, "copy_if_small", true);
  CHECK(contract.complete && contract.kinds == std::set<std::string>{"oob_write"} && contract.allReplayed, "contract mode: only the sign-extension overflow of dst");

  // hostile: drop the relation => the caller no longer guarantees size(src) >= len
  std::string hostile = yaml.substr(0, yaml.find("    relations:"));
  Analysis h = analyze(core, hostile, "copy_if_small", true);
  CHECK(h.complete && h.kinds == (std::set<std::string>{"oob_write", "oob_read"}) && h.allReplayed, "hostile mode additionally reports the src over-read");

  // trusted_len shorthand: size(src) == len, so len cannot be negative or exceed the buffer
  std::string trusted = hostile + "    trusted_len: { buf: src, len: len }\n";
  Analysis t = analyze(core, trusted, "copy_if_small", true);
  CHECK(t.complete && t.findings == 0, "trusted_len: no findings");

  // cstring: the generated object always ends in NUL, a plain buffer does not
  const char *fcore =
      "core.func @third_is_nul(ptr) -> i32 {\n^entry(%s: ptr):\n  %sz = core.obj_size %s : i64\n  %three = core.const 3 : i64\n"
      "  %is3 = core.icmp eq %sz, %three : bool\n  core.cond_br %is3, ^chk, ^out\n^chk:\n  %two = core.const 2 : i64\n"
      "  %q = core.ptr_add %s, %two : ptr\n  %b = core.load %q : i8\n  %z = core.const 0 : i8\n  %isz = core.icmp eq %b, %z : bool\n"
      "  core.assert %isz {msg=\"not NUL terminated\"}\n  core.br ^out\n^out:\n  %r = core.const 0 : i32\n  core.return %r\n}\n";
  auto spec = [](const char *kind) {
    return std::string("taint_entries:\n  - function: third_is_nul\n    params:\n      s: { taint: pointee, kind: ") + kind + ", size: { min: 1, max: 8 } }\n";
  };
  Analysis cs = analyze(fcore, spec("cstring"), "third_is_nul", false);
  CHECK(cs.complete && cs.findings == 0, "cstring: byte size-1 is NUL on every path (findings " << cs.findings << ")");
  Analysis buf = analyze(fcore, spec("buffer"), "third_is_nul", false);
  CHECK(buf.kinds == std::set<std::string>{"assert"} && buf.allReplayed, "plain buffer: the assertion can fail, and the input bytes replay");

  // a callee that frees its (non-heap) parameter object, and one that reads uninitialised untainted content
  const char *fr = "core.declare @free(ptr) -> void\ncore.func @drop(ptr) -> void {\n^entry(%p: ptr):\n  core.call @free(%p)\n  core.return\n}\n";
  Analysis f = analyze(fr, "taint_entries:\n  - function: drop\n    params:\n      p: { taint: pointee, size: { min: 4, max: 4 } }\n", "drop", true);
  CHECK(f.kinds == std::set<std::string>{"invalid_free"} && f.allReplayed, "freeing a parameter object is an invalid free");
  {
    // `owned: true`: the callee owns a heap object, so freeing it is fine (and freeing it twice is not)
    const char *fcore = "core.func @once(ptr) -> void {\n^entry(%p: ptr):\n  core.check.free %p {expect=heap}\n  core.free %p\n  core.return\n}\n"
                        "core.func @twice(ptr) -> void {\n^entry(%p: ptr):\n  core.check.free %p {expect=heap}\n  core.free %p\n  core.check.free %p {expect=heap}\n  core.free %p\n  core.return\n}\n";
    auto run1 = [&](const char *fn, bool owned) {
      std::string y = std::string("taint_entries:\n  - function: ") + fn + "\n    params:\n      p: { taint: pointee, size: { min: 4, max: 4 }" + (owned ? ", owned: true" : "") + " }\n";
      auto L = load(fcore, y, fn);
      if (!L->ok) return std::string("plan: ") + L->d.str();
      Diagnostics d5;
      auto m5 = parseModule(std::string(fcore) + entry::generateHarness(L->plan), "m.core", d5);
      if (!m5) return std::string("parse: ") + d5.str();
      TableEnv env5;
      RunConfig cfg5;
      auto r5 = Interpreter(*m5).run(entry::harnessName(L->plan), {}, env5, cfg5);
      return r5.ub ? std::string(ubKindName(r5.ub->kind)) : std::string(runStatusName(r5.status));
    };
    CHECK(run1("once", false) == "invalid_free", "a borrowed parameter object cannot be freed: " << run1("once", false));
    CHECK(run1("once", true) == "returned", "an owned parameter object can: " << run1("once", true));
    CHECK(run1("twice", true) == "double_free", "an owned object freed twice is a double free: " << run1("twice", true));
  }
  const char *rd =
      "core.func @first_byte(ptr) -> i8 {\n^entry(%p: ptr):\n  core.check.null %p\n  core.check.uninit %p {w=1}\n  %v = core.load %p : i8\n  core.return %v\n}\n";
  Analysis u = analyze(rd, "taint_entries:\n  - function: first_byte\n    params:\n      p: { taint: pointee, size: { min: 1, max: 8 } }\n", "first_byte", false);
  CHECK(u.complete && u.findings == 0, "tainted parameter content counts as initialised");

  // symbolic offset into a parameter object: its content is an SMT array, and the model names the byte it relies on
  const char *gcore =
      "core.func @g(ptr, i32) -> i32 {\n^entry(%src: ptr, %len: i32):\n  %m = core.const 15 : i32\n  %k = core.and %len, %m : i32\n  %idx = core.zext %k : i64\n"
      "  %p = core.ptr_add %src, %idx : ptr\n  core.check.oob %p {w=1, access=\"r\"}\n  %b = core.load %p : i8\n  %bi = core.zext %b : i64\n  %buf = core.alloca {size=8} : ptr\n"
      "  %q = core.ptr_add %buf, %bi : ptr\n  core.check.oob %q {w=1, access=\"w\"} loc(\"g.c\":7:3)\n  core.store %b, %q\n  %z = core.const 0 : i32\n  core.return %z\n}\n";
  Analysis ga = analyze(gcore, "taint_entries:\n  - function: g\n    params:\n      src: { taint: pointee, size: { min: 16, max: 16 } }\n      len: { taint: value, type: int }\n", "g", false);
  CHECK(ga.complete && ga.kinds == std::set<std::string>{"oob_write"} && ga.allReplayed, "array content with a symbolic index: found, and the chosen input byte replays (complete " << ga.complete << ")");
  Analysis nn = analyze(rd, "taint_entries:\n  - function: first_byte\n    params:\n      p: { taint: pointee, nullable: true, size: { min: 1, max: 8 } }\n", "first_byte", false);
  CHECK(nn.kinds == std::set<std::string>{"null_deref"} && nn.allReplayed, "a nullable pointer parameter exposes the missing NULL check");
}

// size.from_param: the cross-top-level-parameter "pointer + length" idiom (e.g. nft_set_elem_init's key buffer,
// whose real length is a sibling parameter's value, not a field of its own pointee object -- see DESIGN.md's
// relations-DSL "cross-top-level-parameter size relation" gap). klen declared [1,64] so both the bug and safe
// variants have an unambiguous, non-empty object regardless of which byte is written.
// An EMPTY pointer parameter: `size: { min: 0, max: 0 }`. This is what an interface model's `user_addr` role
// lowers to (hlir::scan, DESIGN.md §22.361) -- a real but zero-byte object, so passing the pointer on and doing
// arithmetic with it is fine while dereferencing it is reported out of bounds, which is exactly what following a
// __user pointer in kernel code is. The spec PARSER always accepted it; the planner rejected it on `at >= lo` with
// `at` at its default 0, which made every `read`/`write` handler of every modelled interface unanalysable
// (19 of 87 entries in the sound/core run that found this). A pointer to the start of an empty object is a legal C
// pointer, so only a real container_of offset has to land inside.
static void testEmptyPointerParam() {
  const char *core = "core.func @f(ptr, i64) -> i64 {\n^entry(%p: ptr, %n: i64):\n  core.return %n\n}\n";
  auto L = load(core, "taint_entries:\n  - function: f\n    params:\n      p: { taint: none, kind: buffer, size: { min: 0, max: 0 } }\n      n: { taint: value, type: uint64_t }\n", "f");
  CHECK(L->ok, "a zero-byte pointer parameter is plannable: " << L->d.str());
  const entry::PlannedParam *pp = nullptr;
  for (auto &q : L->plan.params)
    if (q.name == "p") pp = &q;
  CHECK(pp && pp->sizeLo == 0 && pp->sizeHi == 0, "it really is empty, not silently widened to 1 byte");
  CHECK(pp && !pp->tainted, "and untainted: its bytes reach the code only through the copy_*_user models");
  // a non-zero container_of offset into it is still an error -- the check was narrowed, not removed
  auto B = load(core, "taint_entries:\n  - function: f\n    params:\n      p: { taint: none, kind: buffer, size: { min: 0, max: 0 }, at: 8 }\n", "f");
  bool found = false;
  for (auto &dg : B->d.all())
    if (dg.severity == Diag::Error && dg.message.find("is outside the object") != std::string::npos) found = true;
  CHECK(!B->ok && found, "a real container_of offset must still land inside the object: " << B->d.str());
}

static void testSizeFromParam() {
  const char *fpcore =
      "core.func @nft_bug(i32, ptr) -> i32 {\n^entry(%klen: i32, %key: ptr):\n"
      "  %klen64 = core.sext %klen : i64\n  %p = core.ptr_add %key, %klen64 : ptr\n"
      "  core.check.oob %p {w=1, access=\"w\"}\n  %zero = core.const 0 : i8\n  core.store %zero, %p\n"
      "  %r = core.const 0 : i32\n  core.return %r\n}\n"
      "core.func @nft_safe(i32, ptr) -> i32 {\n^entry(%klen: i32, %key: ptr):\n"
      "  %klen64 = core.sext %klen : i64\n  %one = core.const 1 : i64\n  %off = core.sub %klen64, %one : i64\n"
      "  %p = core.ptr_add %key, %off : ptr\n"
      "  core.check.oob %p {w=1, access=\"w\"}\n  %zero = core.const 0 : i8\n  core.store %zero, %p\n"
      "  %r = core.const 0 : i32\n  core.return %r\n}\n";
  std::string bugYaml = "taint_entries:\n  - function: nft_bug\n    params:\n      klen: { taint: value, type: int32_t, range: [1, 64] }\n"
                        "      key: { taint: pointee, size: { from_param: { name: klen } } }\n";
  Analysis bugA = analyze(fpcore, bugYaml, "nft_bug", false);
  CHECK(bugA.complete && bugA.kinds == std::set<std::string>{"oob_write"} && bugA.allReplayed,
        "size.from_param: writing key[klen] (one past the real klen-sized object) is flagged oob_write (complete " << bugA.complete << ")");

  std::string safeYaml = "taint_entries:\n  - function: nft_safe\n    params:\n      klen: { taint: value, type: int32_t, range: [1, 64] }\n"
                         "      key: { taint: pointee, size: { from_param: { name: klen } } }\n";
  Analysis safeA = analyze(fpcore, safeYaml, "nft_safe", false);
  CHECK(safeA.complete && safeA.findings == 0, "size.from_param: writing key[klen-1] (the real last byte) is safe (findings " << safeA.findings << ")");
}

// ---------------------------------------------------------------- C++: std::string (kind: string/wstring) synthesis
// is self-consistent (SSO-vs-heap, see InitGen.cpp / HarnessGen.cpp "StdString"): not a replay of the historical
// json11 inputs, but the general invariants any attacker-controlled std::basic_string<CharT> must satisfy regardless
// of content. libstdc++ ABI (64-bit, _S_local_capacity = 15/sizeof(CharT)): offset 0 = _M_p, offset 8 =
// _M_string_length, offset 16 = local buffer / capacity union.
static void testStdString() {
  // 1. NUL terminator: _M_p[_M_string_length] == 0 on every explored path (both SSO and heap representations).
  const char *nul =
      "core.func @str_nul(ptr) -> i32 {\n^entry(%s: ptr):\n  %p = core.load %s : ptr\n  %o8 = core.const 8 : i64\n"
      "  %la = core.ptr_add %s, %o8 : ptr\n  %len = core.load %la : i64\n  %ea = core.ptr_add %p, %len : ptr\n"
      "  %b = core.load %ea : i8\n  %z = core.const 0 : i8\n  %eq = core.icmp eq %b, %z : bool\n"
      "  core.assert %eq {msg=\"nul terminator\"}\n  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a1 = analyze(nul, "taint_entries:\n  - function: str_nul\n    params:\n      s: { taint: pointee, kind: string, size: { min: 0, max: 20 } }\n", "str_nul", false);
  CHECK(a1.complete && a1.findings == 0, "kind:string: the NUL terminator invariant holds on every path (findings " << a1.findings << ")");

  // 2. SSO linkage: whenever _M_p points at the local buffer (offset 16, the only way a parameter-object address and
  // an independently heap-allocated address can ever compare equal), the length must be <= 15 -- the forward
  // direction is NOT forced the other way (a short string can legitimately still be heap-represented after e.g. a
  // prior reserve(); libstdc++ never shrinks back to SSO on its own), so this is the actual invariant, not
  // "length <= 15 implies the local buffer", which this synthesis deliberately does not force.
  const char *link =
      "core.func @str_sso(ptr) -> i32 {\n^entry(%s: ptr):\n  %p = core.load %s : ptr\n  %o8 = core.const 8 : i64\n"
      "  %la = core.ptr_add %s, %o8 : ptr\n  %len = core.load %la : i64\n  %o16 = core.const 16 : i64\n"
      "  %local = core.ptr_add %s, %o16 : ptr\n  %d = core.ptr_diff %p, %local : i64\n  %zero64 = core.const 0 : i64\n"
      "  %isLocal = core.icmp eq %d, %zero64 : bool\n  core.cond_br %isLocal, ^chk, ^out\n^chk:\n"
      "  %fifteen = core.const 15 : i64\n  %short = core.icmp ule %len, %fifteen : bool\n"
      "  core.assert %short {msg=\"local buffer pointer implies length <= 15\"}\n  core.br ^out\n^out:\n  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a2 = analyze(link, "taint_entries:\n  - function: str_sso\n    params:\n      s: { taint: pointee, kind: string, size: { min: 0, max: 20 } }\n", "str_sso", false);
  CHECK(a2.complete && a2.findings == 0, "kind:string: a local-buffer pointer always carries length <= 15 (findings " << a2.findings << ")");

  // 3. control: the same NUL-terminator assertion over the generic "kind: buffer" synthesis (independently symbolic
  // fields, the pre-fix behaviour) is NOT an invariant -- it fails, confirming test 1 is not vacuously true.
  Analysis a3 = analyze(nul,
                        "taint_entries:\n  - function: str_nul\n    params:\n"
                        "      s: { taint: pointee, kind: buffer, size: { min: 32, max: 32 }, fields: [ { offset: 0, kind: buffer, taint: pointee, size: { min: 1, max: 20 } } ] }\n",
                        "str_nul", false);
  CHECK(a3.kinds.count("assert") == 1, "control: a generic field-by-field buffer has no such invariant (kinds: " << a3.kinds.size() << ")");

  // 4. content is real, readable, attacker-controlled data: the first byte (when the length is nonzero) is neither
  // an out-of-bounds nor an uninitialised read.
  const char *first =
      "core.func @str_first(ptr) -> i32 {\n^entry(%s: ptr):\n  %p = core.load %s : ptr\n  %o8 = core.const 8 : i64\n"
      "  %la = core.ptr_add %s, %o8 : ptr\n  %len = core.load %la : i64\n  %zero = core.const 0 : i64\n"
      "  %nonempty = core.icmp ugt %len, %zero : bool\n  core.cond_br %nonempty, ^rd, ^out\n^rd:\n"
      "  core.check.oob %p {w=1, access=\"r\"}\n  core.check.uninit %p {w=1}\n  %b = core.load %p : i8\n  core.br ^out\n^out:\n"
      "  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a4 = analyze(first, "taint_entries:\n  - function: str_first\n    params:\n      s: { taint: pointee, kind: string, size: { min: 0, max: 20 } }\n", "str_first", false);
  CHECK(a4.complete && a4.findings == 0, "kind:string: the first content byte is a real, initialised, in-bounds read (findings " << a4.findings << ")");

  // 5. wstring: same ABI shape with sizeof(wchar_t) == 4 (Linux/gcc), local capacity 15/4 == 3 elements; the NUL
  // terminator is at element offset `len`, i.e. byte offset `len*4`.
  const char *nulw =
      "core.func @wstr_nul(ptr) -> i32 {\n^entry(%s: ptr):\n  %p = core.load %s : ptr\n  %o8 = core.const 8 : i64\n"
      "  %la = core.ptr_add %s, %o8 : ptr\n  %len = core.load %la : i64\n  %four = core.const 4 : i64\n"
      "  %lenb = core.mul %len, %four : i64\n  %ea = core.ptr_add %p, %lenb : ptr\n  %b = core.load %ea : i32\n"
      "  %z = core.const 0 : i32\n  %eq = core.icmp eq %b, %z : bool\n  core.assert %eq {msg=\"wide nul terminator\"}\n"
      "  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a5 = analyze(nulw, "taint_entries:\n  - function: wstr_nul\n    params:\n      s: { taint: pointee, kind: wstring, size: { min: 0, max: 8 } }\n", "wstr_nul", false);
  CHECK(a5.complete && a5.findings == 0, "kind:wstring: the wide NUL terminator invariant holds on every path (findings " << a5.findings << ")");

  // 6. plan-level sanity: a non-pointer parameter cannot be given kind: string, and fields/at/owned/elements/where
  // are rejected alongside it (the layout is fixed, not user-describable).
  const char *scalarCore = "core.func @h(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n";
  auto Lbad1 = load(scalarCore, "taint_entries:\n  - function: h\n    params:\n      x: { taint: value, kind: string }\n", "h");
  CHECK(!Lbad1->ok, "kind: string on a non-pointer parameter is rejected");
  auto Lbad2 = load(nul, "taint_entries:\n  - function: str_nul\n    params:\n      s: { taint: pointee, kind: string, at: 4 }\n", "str_nul");
  CHECK(!Lbad2->ok, "'at' is rejected alongside kind: string");
}

// ---------------------------------------------------------------- C++: std::vector<T> (kind: vector) synthesis is
// self-consistent (one free variable, the element count -- see InitGen.cpp / HarnessGen.cpp "StdVector"): general
// invariants, not a replay of the sum_vec.cpp diagnosis. libstdc++ ABI (64-bit): offset 0 = _M_start, offset 8 =
// _M_finish, offset 16 = _M_end_of_storage (see IMPLEMENTATION_PLAN "std::vector/std::map 入口参数合成自洽化").
static void testStdVector() {
  // 1. ordering + alignment: _M_start <= _M_finish <= _M_end_of_storage, and (_M_finish - _M_start) is a multiple of
  // sizeof(T) (T = int32, the default elem_bits), on every explored path.
  const char *order =
      "core.func @vec_order(ptr) -> i32 {\n^entry(%s: ptr):\n  %start = core.load %s : ptr\n  %o8 = core.const 8 : i64\n"
      "  %fp = core.ptr_add %s, %o8 : ptr\n  %finish = core.load %fp : ptr\n  %o16 = core.const 16 : i64\n"
      "  %ep = core.ptr_add %s, %o16 : ptr\n  %eos = core.load %ep : ptr\n  %d1 = core.ptr_diff %finish, %start : i64\n"
      "  %zero = core.const 0 : i64\n  %ok1 = core.icmp sle %zero, %d1 : bool\n  core.assert %ok1 {msg=\"start <= finish\"}\n"
      "  %d2 = core.ptr_diff %eos, %finish : i64\n  %ok2 = core.icmp sle %zero, %d2 : bool\n"
      "  core.assert %ok2 {msg=\"finish <= end_of_storage\"}\n  %four = core.const 4 : i64\n  %rem = core.urem %d1, %four : i64\n"
      "  %ok3 = core.icmp eq %rem, %zero : bool\n  core.assert %ok3 {msg=\"finish-start is a multiple of sizeof(T)\"}\n"
      "  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a1 = analyze(order, "taint_entries:\n  - function: vec_order\n    params:\n      s: { taint: pointee, kind: vector, size: { min: 0, max: 20 } }\n", "vec_order", false);
  CHECK(a1.complete && a1.findings == 0, "kind:vector: start<=finish<=end_of_storage and elem-size alignment hold on every path (findings " << a1.findings << ")");

  // 2. content is real, readable, attacker-controlled data: when the vector is non-empty, its first element is
  // neither an out-of-bounds nor an uninitialised read.
  const char *first =
      "core.func @vec_first(ptr) -> i32 {\n^entry(%s: ptr):\n  %start = core.load %s : ptr\n  %o8 = core.const 8 : i64\n"
      "  %fp = core.ptr_add %s, %o8 : ptr\n  %finish = core.load %fp : ptr\n  %d = core.ptr_diff %finish, %start : i64\n"
      "  %zero = core.const 0 : i64\n  %nonempty = core.icmp ugt %d, %zero : bool\n  core.cond_br %nonempty, ^rd, ^out\n^rd:\n"
      "  core.check.oob %start {w=4, access=\"r\"}\n  core.check.uninit %start {w=4}\n  %v = core.load %start : i32\n  core.br ^out\n^out:\n"
      "  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a2 = analyze(first, "taint_entries:\n  - function: vec_first\n    params:\n      s: { taint: pointee, kind: vector, size: { min: 0, max: 20 } }\n", "vec_first", false);
  CHECK(a2.complete && a2.findings == 0, "kind:vector: the first element (when non-empty) is a real, initialised, in-bounds read (findings " << a2.findings << ")");

  // 3. control: the same ordering assertion over the generic "kind: buffer" synthesis (three independently symbolic
  // 8-byte words, the pre-fix behaviour) is NOT an invariant -- confirms test 1 is not vacuously true.
  Analysis a3 = analyze(order, "taint_entries:\n  - function: vec_order\n    params:\n      s: { taint: pointee, kind: buffer, size: { min: 24, max: 24 } }\n", "vec_order", false);
  CHECK(a3.kinds.count("assert") == 1, "control: a generic 3-pointer buffer has no such ordering invariant (kinds: " << a3.kinds.size() << ")");

  // 4. elem_bits is honoured: the object is always 3 pointers (24 bytes) regardless of the element width, only the
  // *interpretation* of the content (and so the modulus in test 1) changes with it.
  auto L16 = load(order, "taint_entries:\n  - function: vec_order\n    params:\n      s: { taint: pointee, kind: vector, elem_bits: 16, size: { min: 0, max: 20 } }\n", "vec_order");
  CHECK(L16->ok && L16->plan.params[0].sizeLo == 24 && L16->plan.params[0].sizeHi == 24 && L16->plan.params[0].elemWidth == 16,
        "kind:vector elem_bits: 16: object is still 24 bytes, elemWidth recorded as 16");

  // 5. plan-level sanity: a non-pointer parameter cannot be given kind: vector; fields/at/owned/elements/where and
  // elem_bits on a non-vector kind are rejected (the layout is fixed, not user-describable).
  const char *scalarCore = "core.func @h(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n";
  auto Lbad1 = load(scalarCore, "taint_entries:\n  - function: h\n    params:\n      x: { taint: value, kind: vector }\n", "h");
  CHECK(!Lbad1->ok, "kind: vector on a non-pointer parameter is rejected");
  auto Lbad2 = load(order, "taint_entries:\n  - function: vec_order\n    params:\n      s: { taint: pointee, kind: vector, at: 4 }\n", "vec_order");
  CHECK(!Lbad2->ok, "'at' is rejected alongside kind: vector");
  auto Lbad3 = load(order, "taint_entries:\n  - function: vec_order\n    params:\n      s: { taint: pointee, kind: buffer, size: { min: 24, max: 24 }, elem_bits: 32 }\n", "vec_order");
  CHECK(!Lbad3->ok, "elem_bits is rejected on kind: buffer");
  auto Lbad4 = load(order, "taint_entries:\n  - function: vec_order\n    params:\n      s: { taint: pointee, kind: vector, elem_bits: 12 }\n", "vec_order");
  CHECK(!Lbad4->ok, "elem_bits must be 8, 16, 32 or 64");
}

// ---------------------------------------------------------------- C++: std::map<K,V> (kind: map) synthesis models
// only "empty" or "exactly one (black, root) node" -- see InitPlan.h "StdMap" and IMPLEMENTATION_PLAN "std::vector/
// std::map 入口参数合成自洽化" for why a general symbolic red-black tree was judged out of scope. libstdc++ ABI
// (64-bit, default key_bits/val_bits 32): offset 8 = _M_header.{color,parent,left,right}, offset 40 = _M_node_count;
// the lone node (when present) is a separate heap object with color@0, parent@8, left@16, right@24, key@32, val@36.
static void testStdMap() {
  // 1. at most one node: the header's leftmost and rightmost links always agree (trivially true with 0 or 1 node;
  // would not hold in general for a >=2-node tree, which is exactly the shape this kind deliberately does not model).
  const char *leaf =
      "core.func @map_leaf(ptr) -> i32 {\n^entry(%s: ptr):\n  %o24 = core.const 24 : i64\n  %lp = core.ptr_add %s, %o24 : ptr\n"
      "  %left = core.load %lp : ptr\n  %o32 = core.const 32 : i64\n  %rp = core.ptr_add %s, %o32 : ptr\n  %right = core.load %rp : ptr\n"
      "  %eq = core.ptr_cmp eq %left, %right : bool\n  core.assert %eq {msg=\"leftmost == rightmost (<=1 node)\"}\n"
      "  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a1 = analyze(leaf, "taint_entries:\n  - function: map_leaf\n    params:\n      s: { taint: pointee, kind: map }\n", "map_leaf", false);
  CHECK(a1.complete && a1.findings == 0, "kind:map: leftmost == rightmost on every explored path (findings " << a1.findings << ")");

  // 2. node_count is 0 or 1, and _M_header._M_parent == NULL iff node_count == 0 (the real libstdc++ `_M_reset()`
  // invariant for an empty tree, and the real "just inserted the first/root node" state otherwise).
  const char *cnt =
      "core.func @map_count(ptr) -> i32 {\n^entry(%s: ptr):\n  %o40 = core.const 40 : i64\n  %cp = core.ptr_add %s, %o40 : ptr\n"
      "  %cnt = core.load %cp : i64\n  %one = core.const 1 : i64\n  %le1 = core.icmp ule %cnt, %one : bool\n"
      "  core.assert %le1 {msg=\"node_count <= 1\"}\n  %o16 = core.const 16 : i64\n  %pp = core.ptr_add %s, %o16 : ptr\n"
      "  %parent = core.load %pp : ptr\n  %zero64 = core.const 0 : i64\n  %null = core.int_to_ptr %zero64 : ptr\n"
      "  %parentNull = core.ptr_cmp eq %parent, %null : bool\n  %zero = core.const 0 : i64\n  %countZero = core.icmp eq %cnt, %zero : bool\n"
      "  %x = core.b2i %parentNull : i32\n  %y = core.b2i %countZero : i32\n  %iff = core.icmp eq %x, %y : bool\n"
      "  core.assert %iff {msg=\"parent == NULL iff node_count == 0\"}\n  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a2 = analyze(cnt, "taint_entries:\n  - function: map_count\n    params:\n      s: { taint: pointee, kind: map }\n", "map_count", false);
  CHECK(a2.complete && a2.findings == 0, "kind:map: node_count <= 1, and parent == NULL iff node_count == 0 (findings " << a2.findings << ")");

  // 3. content is real, readable, attacker-controlled data: when node_count == 1, the sole node's key (reached via
  // _M_header._M_parent, which is that node's address exactly when it exists) is a real, initialised, in-bounds read.
  const char *first =
      "core.func @map_first(ptr) -> i32 {\n^entry(%s: ptr):\n  %o40 = core.const 40 : i64\n  %cp = core.ptr_add %s, %o40 : ptr\n"
      "  %cnt = core.load %cp : i64\n  %one = core.const 1 : i64\n  %has = core.icmp eq %cnt, %one : bool\n"
      "  core.cond_br %has, ^rd, ^out\n^rd:\n  %o16 = core.const 16 : i64\n  %pp = core.ptr_add %s, %o16 : ptr\n"
      "  %node = core.load %pp : ptr\n  %o32 = core.const 32 : i64\n  %kp = core.ptr_add %node, %o32 : ptr\n"
      "  core.check.oob %kp {w=4, access=\"r\"}\n  core.check.uninit %kp {w=4}\n  %k = core.load %kp : i32\n  core.br ^out\n^out:\n"
      "  %r = core.const 0 : i32\n  core.return %r\n}\n";
  Analysis a3 = analyze(first, "taint_entries:\n  - function: map_first\n    params:\n      s: { taint: pointee, kind: map }\n", "map_first", false);
  CHECK(a3.complete && a3.findings == 0, "kind:map: the sole node's key (when node_count == 1) is a real, initialised, in-bounds read (findings " << a3.findings << ")");

  // 4. control: the same leftmost == rightmost assertion over the generic "kind: buffer" synthesis (independently
  // symbolic bytes, the pre-fix behaviour) is NOT an invariant -- confirms test 1 is not vacuously true.
  Analysis a4 = analyze(leaf, "taint_entries:\n  - function: map_leaf\n    params:\n      s: { taint: pointee, kind: buffer, size: { min: 48, max: 48 } }\n", "map_leaf", false);
  CHECK(a4.kinds.count("assert") == 1, "control: a generic byte buffer has no such invariant (kinds: " << a4.kinds.size() << ")");

  // 5. key_bits/val_bits are honoured: the object is always ptrBytes + 40 (48 on this ABI) regardless of K/V width.
  auto L16 = load(leaf, "taint_entries:\n  - function: map_leaf\n    params:\n      s: { taint: pointee, kind: map, key_bits: 16, val_bits: 64 }\n", "map_leaf");
  CHECK(L16->ok && L16->plan.params[0].sizeLo == 48 && L16->plan.params[0].sizeHi == 48 &&
            L16->plan.params[0].keyWidth == 16 && L16->plan.params[0].valWidth == 64,
        "kind:map key_bits/val_bits: object is still 48 bytes, keyWidth/valWidth recorded");

  // 6. plan-level sanity: a non-pointer parameter cannot be given kind: map; fields/at/owned/elements/where/size (the
  // layout and shape are fixed, not user-describable) and key_bits/val_bits on a non-map kind are rejected.
  const char *scalarCore = "core.func @h(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n";
  auto Lbad1 = load(scalarCore, "taint_entries:\n  - function: h\n    params:\n      x: { taint: value, kind: map }\n", "h");
  CHECK(!Lbad1->ok, "kind: map on a non-pointer parameter is rejected");
  auto Lbad2 = load(leaf, "taint_entries:\n  - function: map_leaf\n    params:\n      s: { taint: pointee, kind: map, at: 4 }\n", "map_leaf");
  CHECK(!Lbad2->ok, "'at' is rejected alongside kind: map");
  auto Lbad3 = load(leaf, "taint_entries:\n  - function: map_leaf\n    params:\n      s: { taint: pointee, kind: map, size: { min: 1, max: 1 } }\n", "map_leaf");
  CHECK(!Lbad3->ok, "size is rejected alongside kind: map (it always models 0 or 1 entries)");
  auto Lbad4 = load(leaf, "taint_entries:\n  - function: map_leaf\n    params:\n      s: { taint: pointee, kind: buffer, size: { min: 48, max: 48 }, key_bits: 32 }\n", "map_leaf");
  CHECK(!Lbad4->ok, "key_bits is rejected on kind: buffer");
}

int main() {
  g_z3 = smt::makeZ3ProcessSolver("z3", 20000);
  if (!g_z3) { std::cout << "z3 not available: entry tests skipped\n"; return 0; }
  testYamlStyles();
  testSpecErrors();
  testPointerFields();
  testPreconditions();
  testCopyIfSmall();
  testContradiction();
  testTypes();
  testCtorConstruction();
  testEndToEnd();
  testSizeFromParam();
  testEmptyPointerParam();
  testStdString();
  testStdVector();
  testStdMap();
  std::cout << "entry_tests: " << g_pass << " passed, " << g_fail << " failed\n";
  return g_fail ? 1 : 0;
}

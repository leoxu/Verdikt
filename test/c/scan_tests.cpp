// Tests for entry discovery / spec generation (hlir/scan) and the hlir-scan driver (worker processes, timeouts, outputs).
#include <set>
#include <unistd.h>
#include <sys/wait.h>
#include <vector>

#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>

#include "hlir/buildinfo/BuildInfo.h"
#include "hlir/entry/Spec.h"
#include "hlir/frontend/Frontend.h"
#include "hlir/ir/Parser.h"
#include "hlir/link/Link.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/report/Report.h"
#include "hlir/iface/Interface.h"
#include "hlir/scan/Scan.h"

using namespace hlir;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; if (g_fail < 40) std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

// ---- sharding -----------------------------------------------------------------------------------------------
// scan_tests is 145 `hlir-scan` invocations and used to be 409s of ctest's 424s -- 96% of the suite in one
// sequential test, while a 16-core machine ran four workers at a time and left twelve cores idle. The fixed
// cost is not the problem: a scan of a trivial fixture starts and exits in 42ms, so 145 of them are ~6s. The
// 409s is analysis.
//
// Each top-level block in main() is independent (they share nothing but `bin` and the lowered fixture), so the
// blocks are dealt round-robin across N processes and CMake registers N tests that ctest -j runs together.
// With no argument the binary runs every block, so `./scan_tests` by hand is unchanged.
static int g_block = 0, g_shard = -1, g_nshard = 1;
static bool mine() { return g_nshard <= 1 || (g_block++ % g_nshard) == g_shard; }

static std::string slurp(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }
static bool has(const std::string &h, const std::string &n) { return h.find(n) != std::string::npos; }
// "no finding of this kind" must ask the parsed findings, never the report text. The `checks` summary lists every
// UB kind a check was REACHED for, finding or not (DESIGN.md §22.369), so a substring search over the JSON now
// matches a kind that was checked and came back clean -- which is the opposite of what these assertions mean.
static bool noFinding(const hlir::report::Report &r, const std::string &kind) {
  for (auto &e : r.entries)
    for (auto &f : e.findings)
      if (f.kind == kind) return false;
  return true;
}
static std::string join(const std::vector<std::string> &v) { std::string o; for (auto &x : v) o += (o.empty() ? "" : " ") + x; return o; }
static std::string run(const std::string &cmd, int *rc = nullptr) {
  std::string out = "/tmp/hlir_scan_test_out." + std::to_string(getpid());
  int r = std::system((cmd + " > " + out + " 2>&1").c_str());
  if (rc) *rc = WIFEXITED(r) ? WEXITSTATUS(r) : -1;
  std::string t = slurp(out);
  std::remove(out.c_str());
  return t;
}

static const scan::Entry *find(const std::vector<scan::Entry> &es, const std::string &n) {
  for (auto &e : es) if (e.function == n) return &e;
  return nullptr;
}

static bool noteLike(const scan::Entry &e, const std::string &n) {
  for (auto &x : e.notes) if (has(x, n)) return true;
  return false;
}
static std::string notesOf(const scan::Entry &e) {
  std::string s;
  for (auto &x : e.notes) s += "\n    " + x;
  return s;
}

static std::string joinSet(const std::set<std::string> &s) {
  std::string r;
  for (auto &x : s) { if (!r.empty()) r += ", "; r += x; }
  return r;
}

static bool confirmedKind(const report::Report &r, const char *kind) {
  for (auto &e : r.entries)
    for (auto &f : e.findings)
      if (f.kind == kind && !f.warning) return true;
  return false;
}

int main(int argc, char **argv) {
  // "--shard I/N": run blocks I, I+N, I+2N, ... "--jobs N" (the default) forks N of those and waits.
  int jobs = 8;
  for (int i = 1; i + 1 < argc; ++i) {
    if (std::string(argv[i]) == "--shard") {
      std::string v = argv[i + 1];
      size_t slash = v.find('/');
      if (slash != std::string::npos) { g_shard = std::stoi(v.substr(0, slash)); g_nshard = std::stoi(v.substr(slash + 1)); jobs = 1; }
    } else if (std::string(argv[i]) == "--jobs") {
      jobs = std::stoi(argv[i + 1]);
    }
  }
  if (const char *j = getenv("HLIR_TEST_JOBS")) jobs = atoi(j);
  // Measured on 16 cores: serial 428s, 4 shards 192s (2.2x), 8 shards 108s (4.0x). Four is short of linear
  // because the blocks are not equal weight and the un-blocked prologue runs in every shard; eight evens it
  // out. Forking here rather than registering eight ctest tests keeps a plain `ctest` fast without the caller
  // having to know to pass -j, and `--jobs 1` (or --shard) still gives a single deterministic process.
  if (jobs > 1 && g_nshard <= 1) {
    std::vector<pid_t> kids;
    for (int i = 0; i < jobs; ++i) {
      pid_t pid = fork();
      if (pid == 0) { g_shard = i; g_nshard = jobs; kids.clear(); break; }
      if (pid > 0) kids.push_back(pid);
    }
    if (!kids.empty()) {
      int bad = 0;
      for (pid_t pid : kids) {
        int st = 0;
        waitpid(pid, &st, 0);
        if (!WIFEXITED(st) || WEXITSTATUS(st)) ++bad;
      }
      std::cout << "scan_tests: " << jobs << " shard(s), " << bad << " failed\n";
      return bad ? 1 : 0;
    }
  }
  const std::string fixture = HLIR_SCAN_FIXTURE_DIR "/mini_driver.c";
  frontend::LowerOptions lo;
  lo.partial = true;
  auto low = frontend::lowerC(slurp(fixture), fixture, lo);
  CHECK(low.ok, "fixture does not lower: " << low.diagnostics);

  // ---------------------------------------------------------------- facts + discovery
  const frontend::FunctionInfo *hc = nullptr, *ioctl = nullptr;
  for (auto &f : low.functions) {
    if (f.name == "helper_checksum") hc = &f;
    if (f.name == "mini_ioctl") ioctl = &f;
  }
  CHECK(hc && hc->isStatic && hc->callers == 2, "helper_checksum is static and called from do_read and mini_api (callers=" << (hc ? hc->callers : 99) << ")");
  CHECK(ioctl && !ioctl->isStatic && ioctl->callers == 0 && ioctl->params.size() == 3, "mini_ioctl facts");
  CHECK(ioctl && ioctl->params[2].pointee == "struct" && ioctl->params[2].pointeeSize == 24, "struct req is 24 bytes");

  scan::Options o;
  auto roots = scan::discover(low.functions, o);
  CHECK(find(roots, "mini_ioctl") && find(roots, "mini_ioctl")->why == "root", "mini_ioctl is a root");
  CHECK(find(roots, "mini_api") && find(roots, "mini_api")->why == "root", "mini_api is a root");
  CHECK(find(roots, "do_read") && find(roots, "do_read")->why == "callback", "do_read is reached through the handler table");
  CHECK(find(roots, "do_write") && find(roots, "do_write")->why == "callback", "do_write is a callback");
  CHECK(!find(roots, "helper_checksum"), "a static helper called internally is not an entry");
  CHECK(find(roots, "mini_noarg") && !find(roots, "mini_noarg")->skipReason.empty(), "no attacker-controlled parameter => skipped");
  if (mine()) {
    // a zero-parameter entry's generated spec must still parse: `params:` followed by nothing is YAML null,
    // not a mapping, so makeEntry must omit the key entirely rather than emit an empty header line.
    const frontend::FunctionInfo *na = nullptr;
    for (auto &f : low.functions) if (f.name == "mini_noarg") na = &f;
    CHECK(na, "mini_noarg found");
    if (na) {
      scan::Options no = scan::Options();
      no.includeNoArg = true;
      auto e = scan::makeEntry(*na, no, low.functions);
      CHECK(e.skipReason.empty(), "mini_noarg not skipped with --include-noarg");
      CHECK(e.specText.find("params:") == std::string::npos, "no empty `params:` key for a zero-arg entry:\n" << e.specText);
      entry::EntryFile ef;
      Diagnostics d;
      CHECK(entry::parseEntrySpec(e.specText, "s.yaml", ef, d), "generated spec for a zero-arg entry parses: " << d.str());
    }
  }
  o.mode = scan::EntryMode::All;
  CHECK(find(scan::discover(low.functions, o), "helper_checksum"), "--entries all includes helpers");
  o = scan::Options();
  o.only = "^mini_";
  auto onlyMini = scan::discover(low.functions, o);
  CHECK(!find(onlyMini, "do_read") && find(onlyMini, "mini_api"), "--only filters by name");
  o = scan::Options();
  o.skip = "api";
  CHECK(!find(scan::discover(low.functions, o), "mini_api"), "--skip filters by name");

  // ---------------------------------------------------------------- generated specs
  o = scan::Options();
  auto api = *find(scan::discover(low.functions, o), "mini_api");
  CHECK(has(api.specText, "buf: { taint: pointee, kind: buffer, size: { min: 1, max: 256 } }"), "byte buffer spec:\n" << api.specText);
  CHECK(has(api.specText, "len: { taint: value, type: int32_t }"), "length spec:\n" << api.specText);
  CHECK(has(api.specText, "\"len >= 0 => (size_t)len <= size(buf)\""), "length relation:\n" << api.specText);
  auto rd = *find(scan::discover(low.functions, o), "do_read");
  CHECK(has(rd.specText, "g: { taint: none, kind: buffer, size: { min: 4, max: 4 } }"), "context object is untainted:\n" << rd.specText);
  CHECK(has(rd.specText, "r: { taint: pointee, kind: buffer, size: { min: 24, max: 24 } }"), "struct pointer is sized by sizeof:\n" << rd.specText);
  o.hostile = true;
  CHECK(!has(scan::makeEntry(*[&] { for (auto &f : low.functions) if (f.name == "mini_api") return &f; return &low.functions[0]; }(), o).specText, "relations"), "--hostile drops relations");

  // ---------------------------------------------------------------- the tool
  const std::string bin = HLIR_SCAN_BIN;
  int rc = 0;
  std::string list = run(bin + " --list " + fixture, &rc);
  CHECK(rc == 0 && has(list, "@mini_ioctl  [root]") && has(list, "@do_read  [callback]") && has(list, "@mini_noarg  skipped"), "--list output:\n" << list);

  std::string dir = "/tmp/hlir_scan_test_dir." + std::to_string(getpid());
  run("rm -rf " + dir);
  std::string txt = run(bin + " --jobs 2 --out " + dir + " " + fixture, &rc);
  CHECK(rc == 1, "exit status 1 (bugs found), got " << rc << "\n" << txt);
  CHECK(has(txt, "BUG      ") && has(txt, "@do_read") && has(txt, "safe     ") && has(txt, "skipped  "), "summary table:\n" << txt);
  report::Report rep;
  std::string err;
  CHECK(report::fromJson(slurp(dir + "/scan.json"), rep, err), "scan.json is readable: " << err);
  auto verdict = [&](const std::string &fn) {
    for (auto &e : rep.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
    return std::string("missing");
  };
  CHECK(verdict("do_read") == "bug", "do_read: " << verdict("do_read"));
  CHECK(verdict("do_write") == "safe_under_assumptions", "do_write: " << verdict("do_write"));
  CHECK(verdict("mini_ioctl") == "bug", "mini_ioctl (bug reached through the table): " << verdict("mini_ioctl"));
  CHECK(verdict("mini_api") == "safe_under_assumptions", "mini_api: " << verdict("mini_api"));
  bool oob = false, confirmed = true;
  for (auto &e : rep.entries)
    if (e.function == "mini_ioctl")
      for (auto &f : e.findings) { oob |= f.kind == "oob_write"; confirmed &= f.replay == report::ReplayStatus::Confirmed; }
  CHECK(oob && confirmed, "mini_ioctl has a replay-confirmed oob_write");
  CHECK(!slurp(dir + "/scan.sarif").empty(), "scan.sarif is written");
  std::string spec = run("ls " + dir + "/specs");
  CHECK(has(spec, "__mini_ioctl.yaml") && has(spec, "__mini_api.yaml"), "generated specs are written:\n" << spec);

  // a user-written spec replaces the generated one
  std::string sd = dir + "/user";
  run("mkdir -p " + sd);
  std::ofstream(sd + "/mini_api.yaml") << "taint_entries:\n  - function: mini_api\n    label: network\n    params:\n      buf: { taint: pointee, kind: buffer, size: { min: 1, max: 4 } }\n      len: { taint: value, type: int32_t }\n";
  std::string over = run(bin + " --entry mini_api --spec-dir " + sd + " --format json " + fixture, &rc);
  CHECK(rc == 1 && has(over, "\"verdict\": \"bug\""), "user spec (no relation, 4-byte buffer) finds the buffer overrun: rc=" << rc);

  // per-entry wall-clock limit: every worker is stopped and the entry is inconclusive, never silently safe
  std::string to = run(bin + " --timeout 0 --entry mini_api --format json " + fixture, &rc);
  CHECK(rc == 3 && has(to, "\"code\": \"timeout\"") && has(to, "\"verdict\": \"unknown\""), "timeout => unknown: rc=" << rc << "\n" << to);

  // an unreadable input is an error, not an empty scan
  run(bin + " /nonexistent/x.c", &rc);
  CHECK(rc == 2, "missing file => exit 2, got " << rc);
  run("rm -rf " + dir);

  // ---------------------------------------------------------------- pointer fields of input structs
  if (mine()) {
    const std::string pf = HLIR_SCAN_FIXTURE_DIR "/ptr_fields_driver.c";
    frontend::LowerOptions po;
    po.partial = true;
    auto r = frontend::lowerC(slurp(pf), pf, po);
    CHECK(r.ok, "ptr_fields_driver lowers: " << r.diagnostics);
    const frontend::FunctionInfo *cu = nullptr;
    for (auto &f : r.functions) if (f.name == "ctx_use") cu = &f;
    CHECK(cu && cu->params.size() == 2 && cu->params[0].pointee == "struct" && cu->params[0].ptrFields->size() == 4, "dev_ctx has 4 pointer fields: " << (cu ? cu->params[0].ptrFields->size() : 0));
    if (cu && cu->params[0].ptrFields->size() == 4) {
      auto &fl = *cu->params[0].ptrFields;
      CHECK(fl[0].kind == "struct" && fl[0].structName == "inner" && fl[0].pointeeSize == 12, "in -> struct inner (12 bytes)");
      CHECK(fl[1].kind == "struct" && fl[1].children.size() == 1 && fl[1].children[0].kind == "func" && fl[1].children[0].funcSig == "(i32) -> i32", "ops -> struct ops { int (*)(int) }");
      CHECK(fl[2].kind == "struct" && fl[2].structName == "priv", "void *priv is typed by the cast in ctx_use: " << fl[2].kind << " " << fl[2].structName);
      CHECK(fl[3].kind == "struct" && fl[3].children.size() == 1 && fl[3].children[0].cyclic, "node->next is a cyclic link");
    }
    scan::Options so;
    auto es = scan::discover(r.functions, so);
    const scan::Entry *use = find(es, "ctx_use");
    CHECK(use != nullptr, "ctx_use is an entry");
    if (use) {
      CHECK(has(use->specText, "kind: funcptr, targets: [run_a, run_b]"), "function-pointer field targets:\n" << use->specText);
      CHECK(has(use->specText, "fields: ["), "pointer fields are emitted:\n" << use->specText);
      bool cyc = false;
      for (auto &n : use->notes) cyc |= has(n, "self-referential");
      CHECK(cyc, "the self-referential link is explained in the notes");
    }
    scan::Options off;
    off.noPtrFields = true;
    auto es2 = scan::discover(r.functions, off);
    CHECK(find(es2, "ctx_use") && !has(find(es2, "ctx_use")->specText, "fields:"), "--no-ptr-fields emits no fields");

    std::string out = run(bin + " --format json " + pf, &rc);
    report::Report rep3;
    std::string err3;
    CHECK(report::fromJson(out.substr(out.find('{')), rep3, err3), "ptr fields scan json: " << err3);
    auto v3 = [&](const report::Report &rp, const std::string &fn) {
      for (auto &e : rp.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(v3(rep3, "ctx_use") == "safe_under_assumptions", "ctx_use is safe once the pointer fields are legal objects: " << v3(rep3, "ctx_use"));
    CHECK(v3(rep3, "ctx_bug") == "bug", "ctx_bug: " << v3(rep3, "ctx_bug"));
    bool oob = false;
    for (auto &e : rep3.entries)
      if (e.function == "ctx_bug") for (auto &f : e.findings) oob |= (f.kind == "ptr_arith_oob" || f.kind == "oob_read") && f.replay == report::ReplayStatus::Confirmed;
    CHECK(oob, "ctx_bug: the out-of-bounds read through the pointee is replay-confirmed");
    // the old behaviour: NULL pointer fields => false null dereferences
    std::string out2 = run(bin + " --no-ptr-fields --format json " + pf, &rc);
    report::Report rep4;
    CHECK(report::fromJson(out2.substr(out2.find('{')), rep4, err3), "no-ptr-fields json");
    CHECK(v3(rep4, "ctx_use") == "bug", "without pointer fields ctx_use dereferences NULL: " << v3(rep4, "ctx_use"));
  }

  // ---------------------------------------------------------------- same_alloc (base/end pointer-pair idiom)
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/same_alloc_driver.c";
    std::string sd = HLIR_SCAN_FIXTURE_DIR "/../tmp_same_alloc_specs";
    run("mkdir -p " + sd);
    auto writeSpec = [&](const std::string &fn) {
      std::ofstream(sd + "/" + fn + ".yaml") << "taint_entries:\n  - function: " << fn << "\n    label: network\n    params:\n"
          "      s:\n        taint: pointee\n        kind: buffer\n        size: { min: 16, max: 16 }\n        fields:\n"
          "          - { offset: 0, kind: buffer, taint: pointee, size: { min: 16, max: 16 } }\n"
          "          - { offset: 8, kind: buffer, same_alloc: { offset: 0 } }\n";
    };
    writeSpec("stream_consume_safe");
    writeSpec("stream_consume_bug");
    std::string outSafe = run(bin + " --entry stream_consume_safe --spec-dir " + sd + " --format json " + sf, &rc);
    std::string outBug = run(bin + " --entry stream_consume_bug --spec-dir " + sd + " --format json " + sf, &rc);
    report::Report repSafe, repBug;
    std::string errS, errB;
    CHECK(report::fromJson(outSafe.substr(outSafe.find('{')), repSafe, errS), "same_alloc safe scan json: " << errS << "\n" << outSafe);
    CHECK(report::fromJson(outBug.substr(outBug.find('{')), repBug, errB), "same_alloc bug scan json: " << errB << "\n" << outBug);
    auto vsa = [&](const report::Report &rp, const std::string &fn) {
      for (auto &e : rp.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(vsa(repSafe, "stream_consume_safe") == "safe_under_assumptions",
          "p<end correctly bounded by the shared allocation's real size: " << vsa(repSafe, "stream_consume_safe"));
    CHECK(vsa(repBug, "stream_consume_bug") == "bug", "p<=end writes one byte past the shared allocation: " << vsa(repBug, "stream_consume_bug"));
    bool oobConfirmed = false;
    for (auto &e : repBug.entries)
      if (e.function == "stream_consume_bug")
        for (auto &f : e.findings) oobConfirmed |= f.kind == "oob_write" && f.replay == report::ReplayStatus::Confirmed;
    CHECK(oobConfirmed, "stream_consume_bug: the off-by-one write past the shared allocation is replay-confirmed oob_write");
    run("rm -rf " + sd);
  }

  // ---------------------------------------------------------------- container_of
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/container_driver.c";
    frontend::LowerOptions co;
    co.partial = true;
    auto r = frontend::lowerC(slurp(cf), cf, co);
    CHECK(r.ok, "container_driver lowers: " << r.diagnostics);
    const frontend::FunctionInfo *rd = nullptr, *mo = nullptr;
    for (auto &f : r.functions) { if (f.name == "drv_read") rd = &f; if (f.name == "misc_open") mo = &f; }
    CHECK(rd && rd->params[0].ptrFields->size() == 1, "struct file has one pointer field (private_data)");
    if (rd && rd->params[0].ptrFields->size() == 1) {
      auto &pf = (*rd->params[0].ptrFields)[0];
      CHECK(pf.kind == "struct" && pf.structName == "drv" && pf.pointeeSize == 24 && pf.at == 12, "private_data -> struct drv (24 bytes), at +12 (miscdev): " << pf.kind << " " << pf.structName << " size " << pf.pointeeSize << " at " << pf.at);
    }
    CHECK(mo && mo->params[0].pointee == "struct" && mo->params[0].structName == "drv" && mo->params[0].at == 12 && mo->params[0].pointeeSize == 24, "misc_open's parameter is the miscdev member at +12 of a struct drv");
    scan::Options so;
    auto es = scan::discover(r.functions, so);
    CHECK(find(es, "drv_read") && has(find(es, "drv_read")->specText, "at: 12"), "generated spec carries at: 12:\n" << (find(es, "drv_read") ? find(es, "drv_read")->specText : ""));
    CHECK(find(es, "misc_open") && has(find(es, "misc_open")->specText, "size: { min: 24, max: 24 }, at: 12"), "parameter spec carries at: 12:\n" << (find(es, "misc_open") ? find(es, "misc_open")->specText : ""));
    std::string out = run(bin + " --format json " + cf, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "container scan json: " << er);
    auto vv = [&](const report::Report &x, const std::string &fn) {
      for (auto &e : x.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(vv(rp, "drv_read") == "safe_under_assumptions", "drv_read through container_of: " << vv(rp, "drv_read"));
    CHECK(vv(rp, "misc_open") == "safe_under_assumptions", "misc_open (container_of on the parameter): " << vv(rp, "misc_open"));
    CHECK(vv(rp, "drv_bug") == "bug", "drv_bug: " << vv(rp, "drv_bug"));
    bool oob = false;
    for (auto &e : rp.entries)
      if (e.function == "drv_bug") for (auto &f : e.findings) oob |= f.kind == "oob_read" && f.replay == report::ReplayStatus::Confirmed;
    CHECK(oob, "drv_bug: the real out-of-bounds read (not the container_of artefact) is replay-confirmed");
  }

  // ---------------------------------------------------------------- container_of behind a header-defined accessor
  // (the drm_to_adev() pattern: the container_of lives inside a helper function that the entry function's own file
  // does not define, so the hint has to be discovered while visiting the header and then carried across the call).
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/container_header_driver.c";
    frontend::LowerOptions co;
    co.partial = true;
    auto r = frontend::lowerC(slurp(cf), cf, co);
    CHECK(r.ok, "container_header_driver lowers: " << r.diagnostics);
    const frontend::FunctionInfo *orf = nullptr;
    for (auto &f : r.functions) if (f.name == "outer_read") orf = &f;
    CHECK(orf && orf->params[0].pointee == "struct" && orf->params[0].structName == "outer" && orf->params[0].at == 12 && orf->params[0].pointeeSize == 20,
          "outer_read's parameter is the `in` member at +12 of a struct outer (20 bytes), discovered through to_outer() in the header: "
              << (orf ? orf->params[0].structName : "?") << " at " << (orf ? orf->params[0].at : 999) << " size " << (orf ? orf->params[0].pointeeSize : 0));
    scan::Options so;
    auto es = scan::discover(r.functions, so);
    CHECK(find(es, "outer_read") && has(find(es, "outer_read")->specText, "at: 12"), "generated spec carries at: 12:\n" << (find(es, "outer_read") ? find(es, "outer_read")->specText : ""));
    std::string out = run(bin + " --format json " + cf, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "container_header scan json: " << er);
    auto vv = [&](const report::Report &x, const std::string &fn) {
      for (auto &e : x.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(vv(rp, "outer_read") == "safe_under_assumptions", "outer_read through a header-defined container_of accessor: " << vv(rp, "outer_read"));
    CHECK(vv(rp, "outer_bug") == "bug", "outer_bug: " << vv(rp, "outer_bug"));
    bool oob = false;
    for (auto &e : rp.entries)
      if (e.function == "outer_bug") for (auto &f : e.findings) oob |= f.kind == "oob_read" && f.replay == report::ReplayStatus::Confirmed;
    CHECK(oob, "outer_bug: the real out-of-bounds read (not a container_of artefact) is replay-confirmed");
  }

  // ---------------------------------------------------------------- build systems: compile options from Makefiles / compile_commands.json
  if (mine()) {
    using namespace buildinfo;
    auto hasArg = [](const std::vector<std::string> &v, const std::string &x) { for (auto &y : v) if (y == x) return true; return false; };
    // shell words
    auto w = shellSplit("gcc -DNAME='\"x y\"' -I\"a b\" c\\ d;echo");
    CHECK(w.size() == 6 && w[1] == "-DNAME=\"x y\"" && w[2] == "-Ia b" && w[3] == "c d" && w[4] == ";" && w[5] == "echo", "shellSplit: quotes, escapes and an attached ';': " << w.size());
    // `make -n` output: directories, cd, wrappers, several commands per line, continuation lines
    const std::string dry =
        "make[1]: Entering directory '/work/proj'\n"
        "gcc -Wp,-MD,.a.o.d -Iinc -I/abs/inc -DFOO=1 -D BAR -O2 -c -o a.o a.c\n"
        "cd sub && ccache gcc -Iinc2 -DSUB \\\n   -include conf.h -c -o b.o b.c; ./tools/objtool b.o\n"
        "arm-linux-gnueabi-gcc -fno-strict-overflow -c x.S\n"
        "make[1]: Leaving directory '/work/proj'\n"
        "gcc -c other.c\n";
    auto cmds = parseMakeDryRun(dry, "/start");
    CHECK(cmds.size() == 3, "three C compilations in the make log: " << cmds.size());
    if (cmds.size() == 3) {
      CHECK(cmds[0].file == "/work/proj/a.c" && cmds[0].directory == "/work/proj", "Entering directory sets the directory: " << cmds[0].file);
      CHECK(cmds[1].file == "/work/proj/sub/b.c" && cmds[1].directory == "/work/proj/sub", "`cd sub &&` and the ccache prefix: " << cmds[1].file);
      CHECK(cmds[2].file == "/start/other.c", "after Leaving directory the start directory is back: " << cmds[2].file);
      auto f0 = frontendFlags(cmds[0]);
      CHECK(hasArg(f0.clangArgs, "-I/work/proj/inc") && hasArg(f0.clangArgs, "-I/abs/inc") && hasArg(f0.clangArgs, "-DFOO=1") && hasArg(f0.clangArgs, "-DBAR"), "I/D flags, relative dirs made absolute, '-D BAR' joined");
      CHECK(f0.includeDirs == 2 && f0.defines == 2 && !f0.wrapSignedOverflow, "counts; -Wp,-MD,... and -O2 are dropped");
      auto f1 = frontendFlags(cmds[1]);
      CHECK(hasArg(f1.clangArgs, "-include") && hasArg(f1.clangArgs, "/work/proj/sub/conf.h") && hasArg(f1.clangArgs, "-I/work/proj/sub/inc2"), "-include file made absolute: " << join(f1.clangArgs));
    }
    // flag filtering
    CompileCommand cc;
    cc.directory = "/d";
    cc.args = {"-std=gnu11", "-nostdinc", "-isystem", "/usr/lib/gcc/x86_64-linux-gnu/13/include", "-isystem", "sysinc", "-fno-strict-overflow", "-m32", "-Wall", "-fplugin=x.so", "-DKBUILD_MODNAME=\"x\"", "-fms-extensions", "-o", "x.o", "-MF", "x.d"};
    auto ff = frontendFlags(cc);
    CHECK(hasArg(ff.clangArgs, "-std=gnu11") && hasArg(ff.clangArgs, "-nostdinc") && hasArg(ff.clangArgs, "-fms-extensions") && hasArg(ff.clangArgs, "-DKBUILD_MODNAME=\"x\""), "language flags are kept");
    CHECK(!hasArg(ff.clangArgs, "/usr/lib/gcc/x86_64-linux-gnu/13/include") && hasArg(ff.clangArgs, "/d/sysinc"), "gcc's own header directory is dropped, other -isystem dirs kept");
    CHECK(ff.wrapSignedOverflow, "-fno-strict-overflow => signed overflow wraps");
    CHECK(ff.warnings.size() == 1 && has(ff.warnings[0], "-m32"), "-m32 is reported as unsupported");
    CHECK(!hasArg(ff.clangArgs, "-Wall") && !hasArg(ff.clangArgs, "x.o") && !hasArg(ff.clangArgs, "-fplugin=x.so"), "warnings, outputs, plugins are dropped");
    // compile_commands.json: `command` and `arguments`
    std::string err;
    auto jc = parseCompileCommands("[{\"directory\":\"/p\",\"command\":\"cc -Iinc -DA=1 -c m.c\",\"file\":\"m.c\"},"
                                   " {\"directory\":\"/p\",\"arguments\":[\"cc\",\"-I/q\",\"-c\",\"n.c\"],\"file\":\"/p/n.c\"},"
                                   " {\"directory\":\"/p\",\"command\":\"cc -c asm.S\",\"file\":\"asm.S\"}]", err);
    CHECK(err.empty() && jc.size() == 2 && jc[0].file == "/p/m.c" && jc[1].file == "/p/n.c", "compile_commands.json: C files only, files made absolute: " << jc.size() << " " << err);
    jc = parseCompileCommands("{ not json", err);
    CHECK(jc.empty() && !err.empty(), "a broken compile_commands.json is reported");

    // static Makefile parse: variables, += under ifeq, $(SRCS:.c=.o), no execution
    const std::string bdir = HLIR_SCAN_FIXTURE_DIR "/../build";
    std::vector<std::string> warn;
    auto st = parseMakefileStatic(bdir, warn);
    CHECK(st.size() == 2, "static parse finds the two sources: " << st.size());
    if (st.size() == 2) {
      auto sf = frontendFlags(st[0]);
      CHECK(hasArg(sf.clangArgs, "-DLIMIT=8") && hasArg(sf.clangArgs, "-DEXTRA_FEATURE") && sf.wrapSignedOverflow, "CFLAGS = ... $(EXTRA) ... -fno-strict-overflow expanded: " << join(sf.clangArgs));
      CHECK(!hasArg(sf.clangArgs, "-DDEBUG_CHECKS=1"), "ifeq ($(MODE),debug) is false with the default MODE ?= release");
      bool incAbs = false;
      for (auto &a : sf.clangArgs) incAbs |= a.rfind("-I/", 0) == 0 && a.size() > 5 && a.compare(a.size() - 4, 4, "/inc") == 0;
      CHECK(incAbs, "-Iinc is made absolute against the Makefile's directory");
    }
    CompileCommand dbg;
    {
      std::string tmp = "/tmp/hlir_mk_test." + std::to_string(getpid());
      run("mkdir -p " + tmp);
      std::ofstream(tmp + "/Makefile") << "A := -DONE\nB = $(A) -DTWO\nCFLAGS = $(B) $(addprefix -I,x y) $(shell echo hi)\nifdef NOPE\nCFLAGS += -DNOPE\nelse\nCFLAGS += -DELSE\nendif\nSRCS = a.c\n";
      std::ofstream(tmp + "/a.c") << "int x;\n";
      std::vector<std::string> w2;
      auto cs = parseMakefileStatic(tmp, w2);
      CHECK(cs.size() == 1, "tmp Makefile parsed");
      if (cs.size() == 1) {
        auto fx = frontendFlags(cs[0]);
        CHECK(hasArg(fx.clangArgs, "-DONE") && hasArg(fx.clangArgs, "-DTWO") && hasArg(fx.clangArgs, "-DELSE") && !hasArg(fx.clangArgs, "-DNOPE"), "recursive/simple variables and ifdef/else: " << join(fx.clangArgs));
        CHECK(fx.includeDirs == 2, "$(addprefix -I,x y)");
      }
      bool shellWarn = false;
      for (auto &x : w2) shellWarn |= has(x, "$(shell");
      CHECK(shellWarn, "$(shell ...) is not executed and the user is told");
      run("rm -rf " + tmp);
    }

    // `make -n` (when make exists) gives the same options as the static parse
    if (run("which make").find("make") != std::string::npos) {
      BuildSource bs;
      bs.makefile = bdir;
      BuildDatabase db;
      std::vector<std::string> notes;
      std::string e2;
      CHECK(loadBuildDatabase(bs, db, notes, e2) && db.size() == 2, "make -n: two compile commands: " << e2);
      const CompileCommand *m = db.lookup(bdir + "/src/main.c");
      CHECK(m && m->origin == "make -n" && hasArg(frontendFlags(*m).clangArgs, "-DLIMIT=8"), "lookup by path gives the make -n command");
      BuildSource b2 = bs;
      b2.makeArgs = {"MODE=debug"};
      BuildDatabase db2;
      CHECK(loadBuildDatabase(b2, db2, notes, e2) && db2.lookup(bdir + "/src/main.c") && hasArg(frontendFlags(*db2.lookup(bdir + "/src/main.c")).clangArgs, "-DDEBUG_CHECKS=1"), "--make-arg MODE=debug reaches make");
    }

    // end to end: with the Makefile's options the buffer size (CAP = LIMIT + 8 = 16) and the wrapping add are known
    const std::string mf = bdir + "/src/main.c";
    std::string out = run(bin + " --makefile " + bdir + " --format json " + mf, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "makefile scan json: " << er);
    auto vv = [&](const report::Report &x, const std::string &fn) {
      for (auto &e : x.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(vv(rp, "copy_in") == "safe_under_assumptions", "copy_in with CAP == 16: " << vv(rp, "copy_in"));
    CHECK(vv(rp, "copy_off_by_one") == "bug", "copy_off_by_one with CAP == 16: " << vv(rp, "copy_off_by_one"));
    CHECK(vv(rp, "add") == "safe_under_assumptions", "add under -fno-strict-overflow: " << vv(rp, "add"));
    CHECK(vv(rp, "feature") != "missing", "-DEXTRA_FEATURE from the Makefile enables feature()");
    // no input files: everything the build compiles is scanned
    std::string all = run(bin + " --makefile " + bdir + " --make-mode static --format json", &rc);
    report::Report ra;
    CHECK(report::fromJson(all.substr(all.find('{')), ra, er) && vv(ra, "scale") != "missing" && vv(ra, "copy_in") != "missing", "without input files both sources of the Makefile are scanned");
    // without the build options the file does not even know CAP / the wrapping rule
    std::string plain = run(bin + " --format json " + mf, &rc);
    report::Report rpl;
    CHECK(report::fromJson(plain.substr(plain.find('{')), rpl, er), "plain scan json");
    CHECK(vv(rpl, "add") == "bug", "without -fno-strict-overflow a + b is a signed overflow: " << vv(rpl, "add"));
    // compile_commands.json
    std::string ccj = "/tmp/hlir_cc_test." + std::to_string(getpid()) + ".json";
    std::ofstream(ccj) << "[{\"directory\":\"" << bdir << "\",\"command\":\"gcc -Iinc -DLIMIT=8 -DEXTRA_FEATURE -fwrapv -c src/main.c\",\"file\":\"src/main.c\"}]";
    std::string viaCc = run(bin + " --compile-commands " + ccj + " --format json", &rc);
    report::Report rcc;
    CHECK(report::fromJson(viaCc.substr(viaCc.find('{')), rcc, er), "compile_commands scan json: " << er << viaCc.substr(0, 300));
    CHECK(vv(rcc, "copy_in") == "safe_under_assumptions" && vv(rcc, "add") == "safe_under_assumptions", "compile_commands.json gives the same result (-fwrapv)");
    std::remove(ccj.c_str());
    // a missing Makefile is an input error
    run(bin + " --makefile /nonexistent/dir --make-mode static", &rc);
    CHECK(rc == 2, "no Makefile => exit 2, got " << rc);
  }

  // ---------------------------------------------------------------- preconditions for internal functions
  if (mine()) {
    const std::string hf = HLIR_SCAN_FIXTURE_DIR "/../pre/hist.c", hp = HLIR_SCAN_FIXTURE_DIR "/../pre/hist.pre.yaml";
    auto verdicts = [&](const std::string &flags, std::string &raw) {
      raw = run(bin + " " + flags + " --format json " + hf, &rc);
      std::map<std::string, std::string> m;
      report::Report r;
      std::string e;
      if (raw.find('{') != std::string::npos && report::fromJson(raw.substr(raw.find('{')), r, e))
        for (auto &x : r.entries) m[x.function] = report::verdictName(x.verdict);
      return m;
    };
    std::string raw;
    auto base = verdicts("", raw);
    CHECK(base["make_lengths"] == "bug" && base["err_name"] == "bug", "without preconditions the internal functions 'fail' on inputs their callers never pass: " << base["make_lengths"] << " " << base["err_name"]);
    auto with = verdicts("--pre " + hp, raw);
    CHECK(with["make_lengths"] == "safe_under_assumptions", "make_lengths with 0<=alphaSize<=4 and freq[i] in [0,2^23): " << with["make_lengths"]);
    CHECK(with["err_name"] == "safe_under_assumptions", "err_name with the member `err` named in the preconditions: " << with["err_name"]);
    report::Report r;
    std::string e;
    CHECK(report::fromJson(raw.substr(raw.find('{')), r, e), "pre json");
    bool pre1 = false, pre2 = false, pre3 = false;
    for (auto &x : r.entries) for (auto &a : x.assumptions) {
      pre1 |= a.category == "precondition" && has(a.text, "alphaSize.range") && a.loc.file == hp && a.loc.line == 5;
      pre2 |= a.category == "precondition" && has(a.text, "freq.elements") && a.loc.line == 6;
      pre3 |= a.category == "precondition" && has(a.text, "c.where") && a.loc.line == 9;
    }
    CHECK(pre1 && pre2 && pre3, "the report lists each precondition with its file:line (" << pre1 << pre2 << pre3 << ")");
    // a precondition names a thing that does not exist: an error, never silently ignored
    std::string bad = "/tmp/hlir_pre_bad." + std::to_string(getpid()) + ".yaml";
    std::ofstream(bad) << "preconditions:\n  - function: make_lengths\n    params:\n      nosuch: { range: [0, 1] }\n";
    std::string o1 = run(bin + " --pre " + bad + " --entry make_lengths --format json " + hf, &rc);
    CHECK(has(o1, "no parameter named 'nosuch'"), "unknown parameter in preconditions is reported: " << o1.substr(0, 300));
    std::ofstream(bad) << "preconditions:\n  - function: err_name\n    params:\n      c: { where: [ { field: nope, range: [0, 1] } ] }\n";
    run(bin + " --pre " + bad + " " + hf, &rc);
    CHECK(rc == 2, "unknown struct member in preconditions => exit 2, got " << rc);
    std::ofstream(bad) << "preconditions:\n  - function: make_lengths\n    params:\n      freq: { elements: { type: int32_t, range: [5, 1] } }\n";
    std::string o3 = run(bin + " --pre " + bad + " --entry make_lengths --format json " + hf, &rc);
    CHECK(has(o3, "empty range"), "an empty range is reported: " << o3.substr(0, 300));
    std::remove(bad.c_str());
  }

  // ---------------------------------------------------------------- what a real project (bzip2) taught the spec generator
  if (mine()) {
    const std::string of = HLIR_SCAN_FIXTURE_DIR "/oss_patterns.c";
    frontend::LowerOptions oo;
    oo.partial = true;
    auto r = frontend::lowerC(slurp(of), of, oo);
    CHECK(r.ok, "oss_patterns lowers: " << r.diagnostics);
    scan::Options so;
    auto es = scan::discover(r.functions, so);
    auto spec = [&](const std::string &fn) { auto *e = find(es, fn); return e ? e->specText : std::string("<none>"); };
    CHECK(has(spec("count_w"), "mode: { taint: pointee, kind: cstring, size: { min: 1, max: 256 } }"), "const char * alone is a C string:\n" << spec("count_w"));
    CHECK(has(spec("sum_buf"), "buf: { taint: pointee, kind: buffer") && has(spec("sum_buf"), "size(buf)"), "const char * with a length stays a buffer:\n" << spec("sum_buf"));
    CHECK(has(spec("big_get"), "max_obj: 10004") || has(spec("big_get"), "max_obj:"), "a 10004-byte struct raises max_obj:\n" << spec("big_get"));
    CHECK(has(spec("my_free"), "owned: true") && has(spec("free_twice"), "owned: true"), "a parameter passed to free() is owned by the callee:\n" << spec("my_free"));
    CHECK(has(spec("outer"), "size: { min: 8, max: 8 }"), "the handle typed in inner() types outer's parameter (struct state, 8 bytes):\n" << spec("outer"));
    CHECK(has(spec("close_h"), "owned: true"), "a handle freed through a local and a callee is owned:\n" << spec("close_h"));
    CHECK(has(spec("outer"), "h: { taint: none"), "an opaque handle is library state, not attacker data:\n" << spec("outer"));
    CHECK(has(spec("sum_ints"), "(size_t)nVals * 4 <= size(vals)"), "camelCase count pairs with an int array (bytes = count * 4):\n" << spec("sum_ints"));
    std::string out = run(bin + " --format json " + of, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "oss scan json: " << er);
    {
      auto v2 = [&](const std::string &fn) { for (auto &e : rp.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict)); return std::string("missing"); };
      CHECK(v2("sum_ints") == "safe_under_assumptions", "sum_ints with the relation: " << v2("sum_ints"));
      CHECK(v2("close_h") == "safe_under_assumptions" || v2("close_h") == "missing", "close_h: " << v2("close_h"));
    }
    auto vv = [&](const std::string &fn) {
      for (auto &e : rp.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(vv("count_w") == "safe_under_assumptions", "count_w on a NUL-terminated string: " << vv("count_w"));
    CHECK(vv("big_get") == "safe_under_assumptions", "big_get with a 10 KB object (no input_error): " << vv("big_get"));
    CHECK(vv("my_free") == "safe_under_assumptions", "my_free of an owned heap object: " << vv("my_free"));
    CHECK(vv("free_twice") == "bug", "a double free of an owned object is still found: " << vv("free_twice"));
    CHECK(vv("outer") == "missing", "outer takes only an opaque handle: nothing attacker-controlled, so it is skipped: " << vv("outer"));
    // the wall-clock budget: the engine stops itself and reports what it has, instead of being killed with nothing
    std::string slow = run(bin + " --timeout 5 --format json " + HLIR_SCAN_FIXTURE_DIR "/slow_loop.c", &rc);
    report::Report rs;
    CHECK(report::fromJson(slow.substr(slow.find('{')), rs, er), "slow scan json: " << er);
    bool budget = false, killed = false;
    for (auto &e : rs.entries) for (auto &i : e.incomplete) { budget |= i.code == "time_budget" || i.code == "run_limit"; killed |= i.code == "timeout"; }
    CHECK(!killed, "the engine's own deadline fires before the worker is killed");
    CHECK(budget || !rs.entries.empty(), "a result comes back");
  }

  // ---------------------------------------------------------------- --max-steps: raises the per-run step budget
  // (default unchanged: 1,000,000, lib/semantics/Taint.h TaintConfig::maxSteps). deep_loop_concrete.c is a no-arg,
  // fully concrete entry whose loop alone costs ~3,000,000 interpreter steps before a real one-byte OOB write:
  // at the default budget the run is cut by step_limit before the write (unknown/incomplete); with --max-steps
  // raised past the loop's real cost, the run completes and the write is found (bug/oob_write).
  if (mine()) {
    const std::string dl = HLIR_SCAN_FIXTURE_DIR "/deep_loop_concrete.c";
    std::string er;
    std::string defOut = run(bin + " --entry deep_loop_concrete --include-noarg --timeout 15 --format json " + dl, &rc);
    report::Report rd;
    CHECK(report::fromJson(defOut.substr(defOut.find('{')), rd, er), "deep_loop_concrete default scan json: " << er);
    auto verdictOf = [&](const report::Report &r, const std::string &fn) {
      for (auto &e : r.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    auto hasStepLimit = [&](const report::Report &r, const std::string &fn) {
      for (auto &e : r.entries) if (e.function == fn) for (auto &i : e.incomplete) if (i.code == "step_limit") return true;
      return false;
    };
    CHECK(verdictOf(rd, "deep_loop_concrete") == "unknown", "default --max-steps (1,000,000) cuts the loop before the OOB write: " << verdictOf(rd, "deep_loop_concrete"));
    CHECK(hasStepLimit(rd, "deep_loop_concrete"), "default run is cut by step_limit, not some other bound");

    std::string raisedOut = run(bin + " --entry deep_loop_concrete --include-noarg --max-steps 5000000 --timeout 30 --format json " + dl, &rc);
    report::Report rr;
    CHECK(report::fromJson(raisedOut.substr(raisedOut.find('{')), rr, er), "deep_loop_concrete raised scan json: " << er);
    CHECK(verdictOf(rr, "deep_loop_concrete") == "bug", "--max-steps 5000000 lets the run reach the real OOB write: " << verdictOf(rr, "deep_loop_concrete"));
    CHECK(!hasStepLimit(rr, "deep_loop_concrete"), "raised budget: no longer cut by step_limit");
  }

  // ---------------------------------------------------------------- --mem-expand-max reaches the primary concolic/
  // taint engine (TaintExecutor), not just the symbolic escalation pass (docs/KNOWN_GAPS_PRIORITIZED.md, "kMaxExpand
  // 硬编码"). mem_expand_taint.c is a no-arg, fully concrete entry whose memcpy length is a compile-time constant one
  // byte over Memory::kMaxExpandDefault (1<<20): at the default cap the memcpy is rejected (incomplete:unsupported,
  // before a real one-byte OOB write after it); with --mem-expand-max raised past the length, the memcpy completes
  // and the write is found (bug).
  if (mine()) {
    const std::string me = HLIR_SCAN_FIXTURE_DIR "/mem_expand_taint.c";
    std::string er;
    auto verdictOf = [&](const report::Report &r, const std::string &fn) {
      for (auto &e : r.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    auto hasUnsupported = [&](const report::Report &r, const std::string &fn) {
      for (auto &e : r.entries) if (e.function == fn) for (auto &i : e.incomplete) if (i.code == "unsupported") return true;
      return false;
    };
    std::string defOut = run(bin + " --entry mem_expand_taint --include-noarg --timeout 15 --format json " + me, &rc);
    report::Report rd;
    CHECK(report::fromJson(defOut.substr(defOut.find('{')), rd, er), "mem_expand_taint default scan json: " << er);
    CHECK(verdictOf(rd, "mem_expand_taint") == "unknown", "default --mem-expand-max (1<<20) rejects the over-cap memcpy before the OOB write: " << verdictOf(rd, "mem_expand_taint"));
    CHECK(hasUnsupported(rd, "mem_expand_taint"), "default run is cut by the kMaxExpand cap (incomplete:unsupported), not some other reason");

    std::string raisedOut = run(bin + " --entry mem_expand_taint --include-noarg --mem-expand-max 2097152 --timeout 15 --format json " + me, &rc);
    report::Report rr2;
    CHECK(report::fromJson(raisedOut.substr(raisedOut.find('{')), rr2, er), "mem_expand_taint raised scan json: " << er);
    CHECK(verdictOf(rr2, "mem_expand_taint") == "bug", "--mem-expand-max 2097152 lets the primary taint engine's memcpy complete and reach the real OOB write: " << verdictOf(rr2, "mem_expand_taint"));
    CHECK(!hasUnsupported(rr2, "mem_expand_taint"), "raised cap: no longer cut by kMaxExpand");
  }

  // ---------------------------------------------------------------- --extern: a model replaces a function the sources define
  if (mine()) {
    const std::string ef = HLIR_SCAN_FIXTURE_DIR "/extern_driver.c", ey = HLIR_SCAN_FIXTURE_DIR "/extern_driver.yaml";
    auto verdictOf = [&](const std::string &flags) {
      std::string o = run(bin + " " + flags + " --format json " + ef, &rc);
      report::Report r;
      std::string e;
      if (!report::fromJson(o.substr(o.find('{')), r, e)) return std::string("unparsable");
      for (auto &x : r.entries) if (x.function == "pick") return std::string(report::verdictName(x.verdict));
      return std::string("missing");
    };
    CHECK(verdictOf("") == "bug", "with its own (non-clamping) body the index is out of range: " << verdictOf(""));
    CHECK(verdictOf("--extern clamp_idx --models " + ey) == "safe_under_assumptions", "the model clamps to 0..3: " << verdictOf("--extern clamp_idx --models " + ey));
  }

  // ---------------------------------------------------------------- --link + --linux: a `static` header-inline left external by
  // `// hlir-extern:` (e.g. <linux/uaccess.h>'s `copy_from_user()` wrapper) must bind to its ModelDB body in every unit, not get
  // renamed to a per-unit `.uN` by the --link clash logic (lib/link/Link.cpp) just because every unit redeclares it identically
  // with internal linkage. Regression for the bug found scanning net/ipv4 setsockopt/getsockopt (docs/DESIGN.md, "C support test
  // round 6"): the rename left the model's plain-named body unreferenced, so the call silently fell back to the generic opaque-
  // external default (no write through `to`), producing a spurious uninit_read on the value the real model always initialises.
  if (mine()) {
    const std::string a = HLIR_SCAN_FIXTURE_DIR "/static_inline_extern_a.c", b = HLIR_SCAN_FIXTURE_DIR "/static_inline_extern_b.c";
    std::string o = run(bin + " --linux --link --entry get_len_a --format json " + a + " " + b, &rc);
    report::Report r;
    std::string e;
    CHECK(report::fromJson(o.substr(o.find('{')), r, e), "static_inline_extern scan json: " << e);
    bool found = false;
    for (auto &x : r.entries) {
      if (x.function != "get_len_a") continue;
      found = true;
      CHECK(report::verdictName(x.verdict) == std::string("safe_under_assumptions"),
            "copy_from_user's model must bind across --link units, not fall back to opaque: " << report::verdictName(x.verdict));
    }
    CHECK(found, "get_len_a entry present in the report");
  }

  // ---------------------------------------------------------------- single-header library (`#define X_IMPLEMENTATION` +
  // `#include "x.h"`, the stb_image.h/dr_libs/qoi/miniz/nuklear idiom): FnCollector must not silently drop the function
  // body just because it lives in a `.h` file. Regression for docs/DESIGN.md §22.110's narrowed follow-up fix: the body is
  // gated behind `#ifdef SINGLEHEADER_IMPLEMENTATION`, a macro the *entry* file itself `#define`s before the `#include`,
  // which is exactly the case MainMacroIfdefs/inMainGatedIfdefRegion allow -- unlike a shared kernel header's `static
  // inline` helpers (covered by the kbuild test right below), never gated behind a macro the consuming file turns on.
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/singleheader_entry.c";
    std::string o = run(bin + " --entries all --list --format json " + sf, &rc);
    CHECK(o.find("0 entries") == std::string::npos, "singleheader_copy must be discovered, not silently dropped: " << o);
    std::string o2 = run(bin + " --entry singleheader_copy --hostile --format json " + sf, &rc);
    report::Report r;
    std::string e;
    CHECK(report::fromJson(o2.substr(o2.find('{')), r, e), "singleheader scan json: " << e);
    bool found = false, oob = false;
    for (auto &x : r.entries) {
      if (x.function != "singleheader_copy") continue;
      found = true;
      for (auto &f : x.findings) oob |= f.kind == "oob_write" && f.replay == report::ReplayStatus::Confirmed;
    }
    CHECK(found, "singleheader_copy entry present in the report");
    CHECK(oob, "the off-by-one write into local[4] must be found and replay-confirmed");
  }

  // ---------------------------------------------------------------- a kernel module built through kbuild (needs the kernel headers on this machine)
  if (mine()) {
    std::string hdr = run("ls -d /usr/src/linux-headers-*-generic 2>/dev/null | head -1");
    while (!hdr.empty() && isspace(static_cast<unsigned char>(hdr.back()))) hdr.pop_back();
    if (!hdr.empty() && run("which make").find("make") != std::string::npos) {
      std::string tmp = "/tmp/hlir_kmod_test." + std::to_string(getpid());
      run("mkdir -p " + tmp);
      auto write = [&](const std::string &limit) {
        std::ofstream(tmp + "/hello.c") <<
            "#include <linux/module.h>\n#include <linux/fs.h>\n#include <linux/uaccess.h>\n"
            "static ssize_t hello_write(struct file *f, const char __user *buf, size_t count, loff_t *ppos)\n{\n"
            "\tchar local[32];\n\tif (count > " + limit + ")\n\t\treturn -EINVAL;\n"
            "\tif (copy_from_user(local, buf, count))\n\t\treturn -EFAULT;\n\treturn count;\n}\n"
            "static const struct file_operations hello_fops = { .owner = THIS_MODULE, .write = hello_write };\n"
            "MODULE_LICENSE(\"GPL\");\n";
      };
      std::ofstream(tmp + "/Makefile") << "obj-m += hello.o\n";
      auto verdictK = [&](const std::string &limit) {
        write(limit);
        std::string o = run(bin + " --linux --makefile " + hdr + " --make-arg M=" + tmp + " --make-target modules --format json " + tmp + "/hello.c", &rc);
        report::Report r;
        std::string e;
        if (o.find('{') == std::string::npos || !report::fromJson(o.substr(o.find('{')), r, e)) return std::string("unparsable: ") + o.substr(0, 200);
        for (auto &x : r.entries) if (x.function == "hello_write") {
          bool oob = false;
          for (auto &f : x.findings) oob |= f.kind == "oob_write" && f.replay == report::ReplayStatus::Confirmed;
          return std::string(report::verdictName(x.verdict)) + (oob ? "+oob_write" : "");
        }
        return std::string("missing");
      };
      CHECK(verdictK("64") == "bug+oob_write", "kbuild flags via make -n; copy_from_user of up to 64 bytes into local[32]: " << verdictK("64"));
      CHECK(verdictK("32") == "safe_under_assumptions", "the same module with the bound fixed: " << verdictK("32"));
      run("rm -rf " + tmp);
    }
  }

  // ---------------------------------------------------------------- --linux: _copy_from_user must not run a synthesized-object-size
  // check against `from` (the __user source pointer) -- that side is fault-safe in the real kernel (an illegal user-space access is
  // caught by the page-fault handler; copy_from_user() just returns nonzero, it never over-reads kernel memory). Regression for
  // docs/DESIGN.md §22.128/§22.129 (diagnosed) and its follow-up fix round: a hardcoded copy length (no relation the auto spec
  // synthesizer can tie to `from`'s size) used to report a bogus ptr_arith_oob/oob on `from`; `to` (the real kernel destination
  // buffer) must still be checked exactly as before.
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/copy_from_user_src_check.c";
    auto verdictOf = [&](const std::string &fn) {
      std::string o = run(bin + " --linux --format json " + cf, &rc);
      report::Report r;
      std::string e;
      if (!report::fromJson(o.substr(o.find('{')), r, e)) return std::string("unparsable: ") + e;
      for (auto &x : r.entries) if (x.function == fn) return std::string(report::verdictName(x.verdict));
      return std::string("missing");
    };
    CHECK(verdictOf("cfu_src_hardcoded_len") == "safe_under_assumptions",
          "a hardcoded copy length no longer triggers a bogus check against the __user source pointer: " << verdictOf("cfu_src_hardcoded_len"));
    std::string o = run(bin + " --linux --format json " + cf, &rc);
    report::Report r;
    std::string e;
    CHECK(report::fromJson(o.substr(o.find('{')), r, e), "copy_from_user_src_check scan json: " << e);
    bool dstOob = false;
    for (auto &x : r.entries) {
      if (x.function != "cfu_dst_too_small") continue;
      CHECK(report::verdictName(x.verdict) == std::string("bug"), "a genuinely too-small `to` is still caught: " << report::verdictName(x.verdict));
      for (auto &f : x.findings) dstOob |= f.kind == "oob_write" && f.origin == "copy_from_user dst end" && f.replay == report::ReplayStatus::Confirmed;
    }
    CHECK(dstOob, "the `to`-side check (dst end, oob_write) is unaffected by removing the `from`-side check");
  }

  // ---------------------------------------------------------------- dispatch-table registrations (vtableBindings)
  if (mine()) {
    const std::string vf = HLIR_SCAN_FIXTURE_DIR "/vtable_bind.c";
    frontend::LowerOptions vo;
    vo.partial = true;
    auto r = frontend::lowerC(slurp(vf), vf, vo);
    CHECK(r.ok, "vtable_bind lowers: " << r.diagnostics);
    auto bound = [&](const std::string &fn, const std::string &slot) {
      auto it = r.vtableBindings.find(fn);
      return it != r.vtableBindings.end() && it->second.count(slot) > 0;
    };
    auto anySlotOf = [&](const std::string &fn) {
      auto it = r.vtableBindings.find(fn);
      return it == r.vtableBindings.end() ? std::string("<none>") : join({it->second.begin(), it->second.end()});
    };
    // a static initialiser with designated initialisers -- the shape the kernel registers almost everything with.
    // RecursiveASTVisitor hands the frontend the SYNTACTIC form here, whose inits are in source order; stepping
    // across to the semantic form is what makes position i mean field i (DESIGN.md §22.359).
    CHECK(bound("demo_read", "file_operations#read"), "designated initialiser binds .read: " << anySlotOf("demo_read"));
    CHECK(bound("demo_write", "file_operations#write"), "designated initialiser binds .write: " << anySlotOf("demo_write"));
    CHECK(bound("demo_ioctl", "file_operations#unlocked_ioctl"), "designated initialiser binds .unlocked_ioctl: " << anySlotOf("demo_ioctl"));
    // a run-time assignment registers just the same
    CHECK(bound("demo_release", "file_operations#release"), "`ops->release = f` binds .release: " << anySlotOf("demo_release"));
    // a slot that is not a function pointer is not a slot: `.owner = THIS_MODULE` must not produce a binding, and
    // nothing may be attributed to it by a position slip
    for (auto &kv : r.vtableBindings) CHECK(!kv.second.count("file_operations#owner"), "`.owner` is not a dispatch slot, but @" << kv.first << " was bound to it");
    // a nested record initialiser keys the slot by the INNER tag: `struct outer o = { .i = { .cb = f } }`
    CHECK(bound("demo_cb", "demo_inner#cb"), "nested initialiser keys by the inner record: " << anySlotOf("demo_cb"));
    CHECK(!bound("demo_cb", "demo_outer#cb") && !bound("demo_cb", "demo_outer#in"), "nested initialiser must not be keyed by the outer record: " << anySlotOf("demo_cb"));
    // an array of vtables binds every element to the ELEMENT type
    CHECK(bound("demo_s0", "demo_private_ops#step") && bound("demo_s1", "demo_private_ops#step"), "each array element binds to the element type: " << anySlotOf("demo_s0") << " / " << anySlotOf("demo_s1"));
    // an unmodelled struct still yields a binding -- which interfaces matter is the MODEL's decision, not the frontend's
    CHECK(bound("demo_step", "demo_private_ops#step"), "an unmodelled vtable is still recorded: " << anySlotOf("demo_step"));
    // taking an address without storing it in a record field is not a registration
    CHECK(!r.vtableBindings.count("demo_loose"), "a plain global function pointer is not a dispatch slot: " << anySlotOf("demo_loose"));
  }

  // ---------------------------------------------------------------- --entries iface: the attack surface is read
  // off the interface model, not guessed from linkage (DESIGN.md §22.360)
  if (mine()) {
    const std::string vf = HLIR_SCAN_FIXTURE_DIR "/vtable_bind.c";
    frontend::LowerOptions vo;
    vo.partial = true;
    auto r = frontend::lowerC(slurp(vf), vf, vo);
    CHECK(r.ok, "vtable_bind lowers for iface entry selection: " << r.diagnostics);

    // A self-contained model, so this test states what the SELECTOR does and cannot drift when the shipped
    // models/interfaces/linux.yaml gains or loses a slot (the end-to-end run below uses the real one).
    const std::string model =
        "version: 1\n"
        "interfaces:\n"
        "  - interface: file_operations\n"
        "    struct: file_operations\n"
        "    label: untrusted\n"
        "    slots:\n"
        "      read:\n"
        "        params:\n"
        "          file:  { role: session }\n"
        "          buf:   { role: user_addr, dir: out, size_from: count }\n"
        "          count: { role: value }\n"
        "      unlocked_ioctl:\n"
        "        params:\n"
        "          file: { role: session }\n"
        "          cmd:  { role: value }\n"
        "          arg:  { role: user_addr }\n";
    iface::InterfaceFile ifs;
    Diagnostics id;
    CHECK(iface::parseInterfaceFile(model, "<test>", ifs, id), "inline interface model parses: " << id.str());

    scan::Options io;
    io.mode = scan::EntryMode::Iface;
    io.interfaces = &ifs;
    io.vtableBindings = &r.vtableBindings;
    CHECK(scan::ifaceSlotOf("demo_read", io) == "file_operations.read", "a modelled slot resolves: " << scan::ifaceSlotOf("demo_read", io));
    CHECK(scan::ifaceSlotOf("demo_ioctl", io) == "file_operations.unlocked_ioctl", "a modelled slot resolves: " << scan::ifaceSlotOf("demo_ioctl", io));
    // registered, but in a slot THIS model does not list: a model is a closed statement, so an unlisted field is
    // deliberately not an entry point rather than an omission to guess around
    CHECK(scan::ifaceSlotOf("demo_write", io).empty(), "a slot the model omits is not an entry: " << scan::ifaceSlotOf("demo_write", io));
    CHECK(scan::ifaceSlotOf("demo_release", io).empty(), "a slot the model omits is not an entry: " << scan::ifaceSlotOf("demo_release", io));
    // registered in a struct no model describes
    CHECK(scan::ifaceSlotOf("demo_step", io).empty(), "an unmodelled vtable is not an entry: " << scan::ifaceSlotOf("demo_step", io));
    // never registered anywhere: this is the 67% of round 42 that `--entries roots` wrongly selected
    CHECK(scan::ifaceSlotOf("demo_entry", io).empty(), "a function registered nowhere is not an entry: " << scan::ifaceSlotOf("demo_entry", io));
    CHECK(scan::ifaceSlotOf("demo_loose", io).empty(), "a loose function pointer is not an entry: " << scan::ifaceSlotOf("demo_loose", io));

    auto es = scan::discover(r.functions, io);
    CHECK(es.size() == 2, "exactly the two modelled slots are discovered, got " << es.size());
    CHECK(find(es, "demo_read") && find(es, "demo_ioctl"), "the discovered entries are the modelled handlers");
    CHECK(!find(es, "demo_entry") && !find(es, "demo_step"), "non-handlers are not discovered");
    CHECK(find(es, "demo_read") && find(es, "demo_read")->why == "iface file_operations.read", "the reason names the slot the handler fills");

    // end-to-end against the SHIPPED models/interfaces: the selector must find the same handlers through the
    // binary's own default model path, and must say so when a scan matched nothing (the failure this guards
    // against is silent -- zero entries and exit 0 look exactly like a clean scan)
    std::string eo = run(bin + " --entries iface --list " + vf, &rc);
    CHECK(has(eo, "@demo_ioctl") && has(eo, "iface file_operations.unlocked_ioctl"), "shipped model selects the ioctl handler: " << eo);
    CHECK(!has(eo, "@demo_entry") && !has(eo, "@demo_step"), "shipped model selects nothing else: " << eo);
    CHECK(has(eo, "no model describes") && has(eo, "demo_private_ops"), "unmodelled registrations are reported as coverage, not dropped silently: " << eo);
    std::string ez = run(bin + " --entries iface --list " + std::string(HLIR_SCAN_FIXTURE_DIR "/mini_driver.c"), &rc);
    CHECK(has(ez, "WARNING") && has(ez, "no registration"), "a scan that matched no modelled interface says so loudly: " << ez);
  }

  // ---------------------------------------------------------------- --entries iface: the contract is LOWERED into
  // the spec, so the handler is handed what the interface really hands it (DESIGN.md §22.361)
  if (mine()) {
    const std::string rf = HLIR_SCAN_FIXTURE_DIR "/iface_roles.c";
    frontend::LowerOptions ro;
    ro.partial = true;
    auto r = frontend::lowerC(slurp(rf), rf, ro);
    CHECK(r.ok, "iface_roles lowers: " << r.diagnostics);

    // self-contained, with the REAL kernel parameter lists, so the test states what the lowering does and does not
    // drift when the shipped models/interfaces/linux.yaml changes
    const std::string model =
        "version: 1\n"
        "interfaces:\n"
        "  - interface: file_operations\n"
        "    struct: file_operations\n"
        "    label: untrusted\n"
        "    session:\n"
        "      param: file\n"
        "      created_by: open\n"
        "    slots:\n"
        "      open:\n"
        "        params:\n"
        "          inode: { role: kernel_owned }\n"
        "          file:  { role: session_out }\n"
        "      read:\n"
        "        params:\n"
        "          file:  { role: session }\n"
        "          buf:   { role: user_addr, dir: out, size_from: count }\n"
        "          count: { role: value }\n"
        "          ppos:  { role: kernel_owned, dir: inout }\n"
        "      write:\n"
        "        params:\n"
        "          file:  { role: session }\n"
        "          buf:   { role: user_addr, dir: in, size_from: count }\n"
        "          count: { role: value }\n"
        "          ppos:  { role: kernel_owned, dir: inout }\n"
        "      unlocked_ioctl:\n"
        "        params:\n"
        "          file: { role: session }\n"
        "          cmd:  { role: value }\n"
        "          arg:  { role: user_addr }\n"
        "      poll:\n"
        "        params:\n"
        "          file: { role: session }\n"
        "          wait: { role: kernel_owned }\n";
    iface::InterfaceFile ifs;
    Diagnostics id;
    CHECK(iface::parseInterfaceFile(model, "<test>", ifs, id), "role model parses: " << id.str());

    scan::Options io;
    io.mode = scan::EntryMode::Iface;
    io.interfaces = &ifs;
    io.vtableBindings = &r.vtableBindings;
    auto es = scan::discover(r.functions, io);
    const scan::Entry *rd = find(es, "demo_read");
    CHECK(rd, "the read handler is discovered");
    const std::string &sp = rd->specText;
    // session: today it degrades to kernel-owned untainted state. The generic path would taint this whole struct
    // field by field -- the measured dominant artefact source -- so the regression this pins is the taint, not the
    // object: `filp` must still BE an object (the handler dereferences it).
    CHECK(sp.find("filp: { taint: none") != std::string::npos, "the session object is not attacker data: " << sp);
    CHECK(sp.find("filp: { taint: none, kind: buffer, size: { min: 8") != std::string::npos ||
              sp.find("filp: { taint: none, kind: buffer, size: { min: 16") != std::string::npos,
          "the session object is still a real struct file, just untainted: " << sp);
    // user_addr: a real but EMPTY object, so following it is an out-of-bounds access and nothing else can read it
    CHECK(sp.find("ubuf: { taint: none, kind: buffer, size: { min: 0, max: 0 }") != std::string::npos,
          "a __user buffer backs no kernel object: " << sp);
    // value / kernel_owned
    CHECK(sp.find("count: { taint: value") != std::string::npos, "the length the attacker passes stays attacker data: " << sp);
    CHECK(sp.find("ppos: { taint: none") != std::string::npos, "the kernel-owned file position is not attacker data: " << sp);
    // size_from against an empty object would pin count to 0 and analyse nothing: the relation must be dropped,
    // loudly, not emitted
    CHECK(sp.find("size(ubuf)") == std::string::npos, "no length relation against an object that does not exist: " << sp);
    CHECK(noteLike(*rd, "stays unconstrained"), "dropping that relation is reported: " << notesOf(*rd));
    // every narrowing is NAMED in the spec, so the report can print it (same discipline as same_alloc/where)
    CHECK(sp.find("    assumptions:\n") != std::string::npos, "the contract's narrowings are named: " << sp);
    CHECK(sp.find("session object") != std::string::npos, "the session degradation is named: " << sp);
    CHECK(sp.find("userspace address") != std::string::npos, "the __user narrowing is named: " << sp);
    // ... and the spec with them still parses
    entry::EntryFile ef;
    Diagnostics ed;
    CHECK(entry::parseEntrySpec(sp, "<gen>", ef, ed), "a spec carrying assumptions parses: " << ed.str());
    const entry::EntrySpec *pe = ef.find("demo_read");
    CHECK(pe && pe->assumptions.size() >= 3, "the assumptions survive the round trip: " << (pe ? pe->assumptions.size() : 0));

    // a user_addr SCALAR (`unsigned long arg`) is an attacker value, not an empty object
    const scan::Entry *ic = find(es, "demo_ioctl");
    CHECK(ic, "the ioctl handler is discovered");
    CHECK(ic->specText.find("arg: { taint: value") != std::string::npos, "a __user scalar is an attacker-controlled value: " << ic->specText);
    CHECK(ic->specText.find("cmd: { taint: value") != std::string::npos, "the ioctl command is attacker-controlled: " << ic->specText);

    // a slot whose every parameter is kernel-owned or session state has no attacker input AT ALL under this
    // contract. Saying so is the point: silently analysing it with a synthesised session is what produced the
    // artefacts, and silently dropping it would hide how much the contract costs.
    const scan::Entry *pl = find(es, "demo_poll");
    CHECK(pl && pl->skipReason.find("file_operations.poll contract") != std::string::npos,
          "a slot with no attacker input says which contract decided that: " << (pl ? pl->skipReason : "<not discovered>"));
    const scan::Entry *op = find(es, "demo_open");
    CHECK(op && !op->skipReason.empty(), "the constructor slot is skipped too: " << (op ? op->skipReason : "<not discovered>"));

    // arity disagreement: the model and the code are describing different functions, so the contract is dropped
    // WHOLE (a shifted parameter list would mislabel every role) and the note says it was
    const scan::Entry *w3 = find(es, "demo_write3");
    CHECK(w3, "the mis-registered handler is still discovered");
    CHECK(noteLike(*w3, "contract was NOT applied"), "an arity mismatch is reported, not applied: " << notesOf(*w3));
    CHECK(w3->specText.find("filp: { taint: pointee") != std::string::npos,
          "with no contract the parameters are synthesised generically again: " << w3->specText);
    CHECK(w3->specText.find("assumptions:") == std::string::npos, "a dropped contract asserts nothing: " << w3->specText);

    // end-to-end through the shipped models/interfaces, via the binary's own default path
    int rc = 0;
    std::string eo = run(bin + " --entries iface --list " + rf, &rc);
    CHECK(has(eo, "@demo_read") && has(eo, "userspace address"), "the shipped contract lowers the same way: " << eo);
    CHECK(has(eo, "@demo_poll") && has(eo, "file_operations.poll contract"), "the shipped contract skips poll for a stated reason: " << eo);
  }

  // ---------------------------------------------------------------- a global's initial value is a NARROWING, and
  // the report has to name it (DESIGN.md §22.362). This is a measurement: it changes no verdict.
  if (mine()) {
    const std::string gf = HLIR_SCAN_FIXTURE_DIR "/global_gated.c";
    const std::string gj = "/tmp/hlir_gglobal." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string go = run(bin + " --entry demo_g_gated --entry demo_g_plain --format json --output " + gj + " " + gf, &rc);
    std::string js = slurp(gj);
    std::remove(gj.c_str());
    CHECK(!js.empty(), "the scan produced a report: " << go);
    // the gated entry: the assumption is there, names the global, and says the other edge was not explored
    size_t at = js.find("\"function\": \"demo_g_gated\"");
    size_t bt = js.find("\"function\": \"demo_g_plain\"");
    CHECK(at != std::string::npos && bt != std::string::npos, "both entries are in the report: " << js.substr(0, 400));
    std::string gated = at < bt ? js.substr(at, bt - at) : js.substr(at);
    std::string plain = at < bt ? js.substr(bt) : js.substr(bt, at - bt);
    CHECK(has(gated, "global_initial_value"), "a branch on an unwritten global is named as an assumption: " << gated);
    CHECK(has(gated, "gFoo"), "the assumption names which global: " << gated);
    CHECK(has(gated, "without a fork"), "the assumption says the opposite edge was not explored either: " << gated);
    // the negatives: a global the program wrote, and a const global, assert nothing
    CHECK(!has(plain, "global_initial_value"),
          "a global the program writes, and a const global, are not initial-value decisions: " << plain);

    // ... and `init:` is the fix, not just the measurement (DESIGN.md §22.368). Running the module's own
    // initialiser is not an approximation of anything -- it is the program's code, executed -- and it is the only
    // way the globals a handler reads hold the values it is really called with. `demo_g_init` sets gFoo to 100, so
    // the `gFoo < 100` edge, and the out-of-bounds read behind it, are dead in reality and must stop being
    // reported. G1's own count is the acceptance metric: it goes to zero.
    const std::string ij = "/tmp/hlir_ginit." + std::to_string(getpid()) + ".json";
    run(bin + " --init-fn demo_g_init --entry demo_g_gated --entry demo_g_plain --format json --output " + ij + " " + gf, &rc);
    std::string ijs = slurp(ij);
    std::remove(ij.c_str());
    report::Report ir;
    std::string ie;
    CHECK(!ijs.empty() && report::fromJson(ijs.substr(ijs.find('{')), ir, ie), "init-fn scan json: " << ie);
    const report::EntryReport *gi = nullptr;
    for (auto &x : ir.entries)
      if (x.function == "demo_g_gated") gi = &x;
    CHECK(gi && gi->verdict == report::Verdict::SafeUnderAssumptions,
          "running the initialiser kills the finding the uninitialised global produced: "
              << (gi ? report::verdictName(gi->verdict) : "missing"));
    CHECK(noFinding(ir, "oob_read") && noFinding(ir, "ptr_arith_oob"), "and no out-of-bounds survives it: " << ijs.substr(0, 600));
    CHECK(!has(ijs, "global_initial_value"), "G1 has nothing left to name -- the acceptance metric: " << ijs.substr(0, 600));
    // running it is still a CHOICE (an initialiser with configuration-dependent branches pins the scan to one
    // configuration), so it may not be invisible either -- §22.361 cuts both ways.
    bool saysInitRan = false;
    for (auto &x : ir.entries)
      for (auto &a : x.assumptions)
        saysInitRan |= a.category == "project_init" && has(a.text, "demo_g_init");
    CHECK(saysInitRan, "and the report names the initialiser it ran: " << ijs.substr(0, 900));

    // a `--init-fn` nobody defines is a project-wide input error: it must stop the scan, not turn every entry into
    // a silent `unknown` whose reason is buried in its own `incomplete` list.
    std::string bad = run(bin + " --init-fn no_such_init_fn --entry demo_g_gated --format json " + gf + " 2>&1", &rc);
    CHECK(has(bad, "names no function of these sources"), "a typo'd --init-fn fails loudly, once: " << bad.substr(0, 400));

    // G2 (DESIGN.md §22.374): when there is no initialiser to run, the honest alternative to believing the static
    // initial value is to stop believing it. `--promote-read-globals` first measures which globals the entry
    // actually reads (the target set), then re-runs with exactly those made unconstrained. The edge G1 could only
    // NAME is then explored, so block coverage rises -- and G1 must stop naming a global G2 has already freed,
    // or the report would assert a narrowing that is no longer in force.
    const std::string pj = "/tmp/hlir_gpromote." + std::to_string(getpid()) + ".json";
    run(bin + " --promote-read-globals --entry demo_g_gated --entry demo_g_plain --format json --output " + pj + " " + gf, &rc);
    std::string pjs = slurp(pj);
    std::remove(pj.c_str());
    report::Report pr;
    std::string pe;
    CHECK(!pjs.empty() && report::fromJson(pjs.substr(pjs.find('{')), pr, pe), "promote scan json: " << pe);
    const report::EntryReport *pg = nullptr, *base = nullptr;
    for (auto &x : pr.entries)
      if (x.function == "demo_g_gated") pg = &x;
    report::Report br;
    CHECK(report::fromJson(js.substr(js.find('{')), br, pe), "baseline json: " << pe);
    for (auto &x : br.entries)
      if (x.function == "demo_g_gated") base = &x;
    CHECK(pg && base, "both runs report the gated entry");
    CHECK(pg->coverage.blocksVisited > base->coverage.blocksVisited,
          "promotion explores the edge the static initial value had decided: " << pg->coverage.blocksVisited << " vs "
                                                                              << base->coverage.blocksVisited);
    bool named = false;
    for (auto &a : pg->assumptions) named |= a.category == "promoted_global";
    CHECK(named, "promotion is a WIDENING and the report names it: " << pjs.substr(0, 900));
    for (auto &a : pg->assumptions)
      CHECK(a.category != "global_initial_value",
            "a promoted global is no longer decided by its initial value, so G1 must not claim it too: " << a.text);

    // ... and the COVERAGE classifier has to say the same thing the assumption says (DESIGN.md Sec.22.465).
    // `gFoo < 100` is decided by the static initial value, so its other edge is unreachable by construction:
    // reporting it as `open` reads as "needs more budget" and sends the reader somewhere no budget can help.
    CHECK(base->coverage.missGlobalInit >= 1,
          "the edge G1 named is classified `global_init`, not `open`/`const`: global_init="
              << base->coverage.missGlobalInit << " open=" << base->coverage.missOpen
              << " const=" << base->coverage.missConst << " unsat=" << base->coverage.missUnsat);
    // and it is a RECLASSIFICATION, not a new gap: the total of the five classes is what it always was.
    CHECK(base->coverage.branchesReachable - base->coverage.branchesVisited ==
              base->coverage.missOpen + base->coverage.missUnsat + base->coverage.missConst +
                  base->coverage.missUnreached + base->coverage.missGlobalInit,
          "the five classes still partition the uncovered edges");
    // G2 frees the global, so the class must empty out with it -- same acceptance metric as the assumption.
    CHECK(pg->coverage.missGlobalInit < base->coverage.missGlobalInit,
          "promotion removes the narrowing, so the class it created shrinks: " << pg->coverage.missGlobalInit
                                                                              << " vs " << base->coverage.missGlobalInit);
  }

  // ---------------------------------------------------------------- `points_to` (DESIGN.md Sec.22.475): the
  // external hands back a HANDLE and the payload is behind a pointer field inside it. This is the shape of every
  // block-backed filesystem (`sb_bread` -> `bh->b_data`), and without the spec it fails twice over: the field
  // reads NULL, so the scan reports a null_deref the harness itself invented, AND the real defect behind that
  // pointer is never reached. Both halves are asserted, because fixing only the first would be a regression.
  if (mine()) {
    const std::string pf = HLIR_SCAN_FIXTURE_DIR "/pointsto.c";
    const std::string pm = HLIR_SCAN_FIXTURE_DIR "/externs/pointsto.yaml";
    auto pscan = [&](const std::string &flags, report::Report &r) {
      const std::string j = "/tmp/hlir_pointsto." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + flags + " --entry pt_parse --entry pt_safe --format json --output " + j +
                                " " + pf, &rc);
      std::string js = slurp(j);
      std::remove(j.c_str());
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "pointsto json: " << e << " / " << out);
      CHECK(r.entries.size() == 2, "two entries");
    };
    auto byName = [](const report::Report &r, const char *n) -> const report::EntryReport * {
      for (auto &x : r.entries)
        if (x.function == n) return &x;
      return nullptr;
    };
    auto kinds = [](const report::EntryReport *e) {
      std::string k;
      for (auto &f : e->findings) k += f.kind + ",";
      return k;
    };

    report::Report off, on;
    pscan("", off);
    pscan("--models " + pm, on);

    const report::EntryReport *op = byName(off, "pt_parse"), *os = byName(off, "pt_safe");
    const report::EntryReport *np = byName(on, "pt_parse"), *ns = byName(on, "pt_safe");
    CHECK(op && os && np && ns, "both entries in both runs");

    // BEFORE: the invented null_deref is all there is, on BOTH entries -- including the one with no defect.
    CHECK(kinds(op).find("null_deref") != std::string::npos && kinds(op).find("oob_write") == std::string::npos,
          "without the model the handle's field is NULL and the real overrun is invisible: " << kinds(op));
    CHECK(kinds(os).find("null_deref") != std::string::npos,
          "and the entry that has NO defect reports one too: " << kinds(os));

    // AFTER: the real overrun, and the negative control goes quiet. The second half is what separates this from
    // simply making the pointer non-null: a model that only widened would make pt_safe noisier, not cleaner.
    CHECK(kinds(np).find("oob_write") != std::string::npos,
          "points_to makes the block attacker data, so the overrun behind it is found: " << kinds(np));
    CHECK(kinds(np).find("null_deref") == std::string::npos, "and the invented null_deref is gone: " << kinds(np));
    CHECK(ns->findings.empty() && ns->verdict == report::Verdict::SafeUnderAssumptions,
          "the in-bounds reader of the same block stays clean: " << kinds(ns) << " / "
                                                                << report::verdictName(ns->verdict));

    // and the point of the whole mechanism: the parser actually RAN.
    CHECK(np->coverage.blocksVisited > op->coverage.blocksVisited,
          "the block behind the handle is what the parser needed to execute: " << np->coverage.blocksVisited
                                                                              << " vs " << op->coverage.blocksVisited);

    // the pointee's size is the model's STATED size (arg1), not an invented one -- that is what makes a bounds
    // verdict about it mean anything (contrast the synthesis frontier, whose sizeInvented suppresses them).
    // A model that says neither source/unknown/zeroed is refused rather than defaulted.
    const std::string badm = "/tmp/hlir_pointsto_bad." + std::to_string(getpid()) + ".yaml";
    { std::ofstream o(badm); o << "models:\n  - function: get_block\n    returns: { alloc: { size: 24 } }\n"
                                 "    points_to:\n      - { base: ret, offset: 16, size: arg1 }\n"; }
    int rc = 0;
    std::string bad = run(bin + " --models " + badm + " --entry pt_parse " + pf + " 2>&1", &rc);
    std::remove(badm.c_str());
    CHECK(bad.find("exactly one of") != std::string::npos,
          "a points_to that does not say what the pointee holds is refused, not defaulted: " << bad.substr(0, 400));
  }

  // ---------------------------------------------------------------- the kernel page allocator returns an
  // `unsigned long`, not a pointer (DESIGN.md Sec.22.476). Two independent things have to hold, and the two
  // negative controls below are what separate them from a model that merely returned something non-NULL.
  if (mine()) {
    const std::string gf = HLIR_SCAN_FIXTURE_DIR "/pagealloc.c";
    const std::string j = "/tmp/hlir_pagealloc." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --linux --entry pg_oob --entry pg_safe --entry pg_order2 --format json --output " +
                              j + " " + gf, &rc);
    std::string js = slurp(j);
    std::remove(j.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "pagealloc json: " << e << " / " << out);
    const report::EntryReport *oob = nullptr, *safe = nullptr, *ord2 = nullptr;
    for (auto &x : r.entries) {
      if (x.function == "pg_oob") oob = &x;
      if (x.function == "pg_safe") safe = &x;
      if (x.function == "pg_order2") ord2 = &x;
    }
    CHECK(oob && safe && ord2, "three entries");
    auto kinds = [](const report::EntryReport *x) {
      std::string k;
      for (auto &f : x->findings) k += f.kind + ",";
      return k;
    };
    // 1. the integer survives the caller's cast back to a pointer WITH its provenance. If it did not, `p` would
    //    be object 0, the NULL check would take the early return, and there would be nothing to find at all.
    CHECK(kinds(oob).find("oob_write") != std::string::npos,
          "the page the model allocated is a real bounded object on the far side of int_to_ptr: " << kinds(oob));
    // 2. the size is PAGE_SIZE << order, not a constant. A model that allocated 4096 would report an overrun on
    //    pg_order2, which asks for FOUR pages and stays inside them -- a model may not manufacture a finding.
    CHECK(ord2->findings.empty() && ord2->verdict == report::Verdict::SafeUnderAssumptions,
          "order 2 is four pages and correct code using all of them stays clean: " << kinds(ord2) << " / "
                                                                                   << report::verdictName(ord2->verdict));
    CHECK(safe->findings.empty() && safe->verdict == report::Verdict::SafeUnderAssumptions,
          "and an in-bounds write to one page is clean: " << kinds(safe));
  }

  // ---------------------------------------------------------------- a `size_from` whose length parameter is
  // UNTAINTED (DESIGN.md Sec.22.478). An untainted scalar is a fixed value in the generated spec, and the
  // relation `(size_t)len <= size(str)` against one produced a harness that did not compile. The damage was not
  // the broken relation but the SHAPE of the failure: `unknown`, 0/0 blocks, the reason buried in `incomplete`
  // as an input_error, with nothing saying a contract had deleted its own entries.
  if (mine()) {
    const std::string f = HLIR_SCAN_FIXTURE_DIR "/ifsizefrom.c";
    const std::string d = HLIR_SCAN_FIXTURE_DIR "/interfaces";
    const std::string j = "/tmp/hlir_ifsz." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --interfaces " + d + " --entries iface --format json --output " + j + " " + f, &rc);
    std::string js = slurp(j);
    std::remove(j.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "ifsizefrom json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "the slot is discovered through the interface");
    const report::EntryReport &x = r.entries[0];
    CHECK(x.verdict != report::Verdict::Unknown, "the generated harness compiles: " << report::verdictName(x.verdict));
    for (auto &i : x.incomplete) CHECK(i.code != "input_error", "no input_error: " << i.detail);
    CHECK(x.coverage.blocksVisited > 0, "and the entry actually ran: " << x.coverage.blocksVisited << " blocks");
    // the relation is DROPPED, not silently ignored -- the buffer is no longer tied to the length, and a read
    // past it would be an artefact, so the reader has to be told. The notes are not carried in the report JSON,
    // so this is asserted on what the run actually prints, which is where a reader would see it.
    std::string listing = run(bin + " --interfaces " + d + " --entries iface --list " + f + " 2>&1", &rc);
    CHECK(listing.find("DROPPED") != std::string::npos,
          "the dropped relation is named where the reader sees it, not swallowed: " << listing.substr(0, 600));
  }

  // ---------------------------------------------------------------- page_address()/folio_address() (DESIGN.md
  // Sec.22.479). Lowered faithfully the kernel inline is arithmetic on fabricated bases, so it yields an integer
  // with no provenance and EVERY call returns NULL. The model returns the page pointer itself; both properties
  // that makes it usable are asserted, because a model wrong in either direction is worse than no model.
  if (mine()) {
    const std::string f = HLIR_SCAN_FIXTURE_DIR "/pageaddr.c";
    const std::string j = "/tmp/hlir_pageaddr." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --linux --include-noarg --entry pa_stable --entry pa_oob --entry pa_inbounds"
                                " --format json --output " + j + " " + f, &rc);
    std::string js = slurp(j);
    std::remove(j.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "pageaddr json: " << e << " / " << out);
    const report::EntryReport *st = nullptr, *ob = nullptr, *in = nullptr;
    for (auto &x : r.entries) {
      if (x.function == "pa_stable") st = &x;
      if (x.function == "pa_oob") ob = &x;
      if (x.function == "pa_inbounds") in = &x;
    }
    CHECK(st && ob && in, "three entries");
    auto kinds = [](const report::EntryReport *x) {
      std::string k;
      for (auto &f2 : x->findings) k += f2.kind + ",";
      return k;
    };
    // STABLE: written through the first pointer, read through the second. A model that allocated a fresh object
    // per call makes those different objects and this reads uninitialised memory.
    CHECK(st->findings.empty(), "two page_address calls on one page give the same object: " << kinds(st));
    // BOUNDED, both ways: the page is 4096 real bytes.
    CHECK(kinds(ob).find("oob_write") != std::string::npos, "a write past the page is a finding: " << kinds(ob));
    CHECK(in->findings.empty() && in->verdict == report::Verdict::SafeUnderAssumptions,
          "and a write inside it is not: " << kinds(in));
  }

  // ---------------------------------------------------------------- declared per-struct field ranges (DESIGN.md
  // Sec.22.480): what a mount path validated about an object the handler is HANDED. Asserted in both directions,
  // because the failure modes are opposite: too wide only loses findings, too narrow HIDES real ones, and a
  // mechanism that simply silenced the entry would pass a one-sided test.
  if (mine()) {
    const std::string f = HLIR_SCAN_FIXTURE_DIR "/structranges.c";
    const std::string d = HLIR_SCAN_FIXTURE_DIR "/structs";
    auto sscan = [&](const std::string &dir, report::Report &r) {
      const std::string j = "/tmp/hlir_sr." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " --struct-ranges " + dir + " --entry sr_shift --entry sr_mask"
                                  " --format json --output " + j + " " + f, &rc);
      std::string js = slurp(j);
      std::remove(j.c_str());
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "structranges json: " << e << " / " << out);
    };
    report::Report off, on;
    sscan("/nonexistent", off);
    sscan(d, on);
    auto find = [](const report::Report &r, const char *n) -> const report::EntryReport * {
      for (auto &x : r.entries)
        if (x.function == n) return &x;
      return nullptr;
    };
    auto has = [](const report::EntryReport *x, const char *k) {
      for (auto &g : x->findings)
        if (g.kind == k) return true;
      return false;
    };
    const report::EntryReport *o = find(off, "sr_shift"), *n2 = find(on, "sr_shift");
    CHECK(o && n2, "the entry is in both runs");
    // the artefact goes
    CHECK(has(o, "shift_range"), "without the range, shifting by an unconstrained field is reported");
    CHECK(!has(n2, "shift_range"), "the declared enum removes it");
    // ... and the real defect beside it stays. A range that silenced the entry would be useless.
    CHECK(has(n2, "uninit_read"), "the genuine uninitialised read in the same function survives");
    // every applied range is named: it NARROWS, so it may not be invisible.
    bool named = false;
    for (auto &a : n2->assumptions) named |= a.text.find("declared range") != std::string::npos;
    CHECK(named, "the narrowing is named in the entry's assumptions");
    for (auto &a : o->assumptions)
      CHECK(a.text.find("declared range") == std::string::npos, "and is absent when no file declared one");

    // ... and the same, through a `void *` whose real pointee type only the code knows (Sec.22.482). Without the
    // retype the generic stand-in has no struct name, so no range for the real type can ever match -- which is
    // why fs/isofs's own superblock fields stayed unconstrained through `sb->s_fs_info`.
    report::Report voff, von;
    {
      auto one = [&](const std::string &dir, report::Report &r) {
        const std::string j = "/tmp/hlir_srv." + std::to_string(getpid()) + ".json";
        int rc2 = 0;
        std::string out2 = run(bin + " --struct-ranges " + dir + " --entry sr_void --format json --output " + j + " " + f, &rc2);
        std::string js2 = slurp(j);
        std::remove(j.c_str());
        std::string e2;
        CHECK(!js2.empty() && report::fromJson(js2.substr(js2.find('{')), r, e2), "sr_void json: " << e2 << " / " << out2);
        CHECK(r.entries.size() == 1, "one entry");
      };
      one("/nonexistent", voff);
      one(d, von);
    }
    CHECK(has(&voff.entries[0], "shift_range"), "without the retype the void*'s pointee is unconstrained");
    CHECK(!has(&von.entries[0], "shift_range"), "the retype carries the declared range through the void*");
    CHECK(has(&von.entries[0], "uninit_read"), "and the genuine defect beside it survives");
    // a retype is subsystem-specific -- it is right for one filesystem and wrong for the next -- so of all the
    // narrowings here it is the one that may least be invisible.
    bool rnamed = false;
    for (auto &a : von.entries[0].assumptions) rnamed |= a.text.find("declared retype") != std::string::npos;
    CHECK(rnamed, "the retype is named in the assumptions");
    // and the entry RAN. A declared range is a precondition, and against the zero fill an untainted object would
    // otherwise get, `zone in {9,10,11}` is unsatisfiable: no run completes and the entry comes back `unknown`
    // at 0% coverage, which looks like a clean scan and is the absence of one (DESIGN.md Sec.22.483).
    CHECK(von.entries[0].coverage.blocksVisited > 0 && von.entries[0].verdict != report::Verdict::Unknown,
          "the retyped object has unknown content, so its declared range is satisfiable: "
              << von.entries[0].coverage.blocksVisited << " blocks, "
              << report::verdictName(von.entries[0].verdict));
  }

  // ---------------------------------------------------------------- a struct whose outermost member is an
  // anonymous union (DESIGN.md Sec.22.484). The collector skipped unions whole, so such a parameter contributed
  // NO pointer fields and everything behind them was frontier guesswork -- `struct folio` is exactly this shape,
  // which cost every address_space_operations handler its whole object graph.
  if (mine()) {
    const std::string f = HLIR_SCAN_FIXTURE_DIR "/unionarm.c";
    const std::string j = "/tmp/hlir_ua." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry ua_entry --format json --output " + j + " " + f, &rc);
    std::string js = slurp(j);
    std::remove(j.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "unionarm json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "one entry");
    const report::EntryReport &x = r.entries[0];
    // the defect is BEHIND the union's pointer: it is reachable only if that pointer became a real object.
    bool oob = false;
    for (auto &g : x.findings) oob |= g.kind == "oob_read";
    CHECK(oob, "the field inside the union is synthesised, so the overrun behind it is found");
    // ... and taking one arm is a CHOICE -- the other arms overlay the same bytes -- so it may not be silent.
    bool named = false;
    for (auto &a : x.assumptions) named |= a.text.find("union") != std::string::npos;
    CHECK(named, "the chosen union arm is named in the assumptions");
  }

  // ---------------------------------------------------------------- the command line the initialiser is run with
  // (DESIGN.md §22.380). Inventing `argc = 1` is not a neutral default: it is the claim that the program is
  // started with no options, and for a program whose options are mandatory the initialiser then returns at its
  // first check and everything downstream is a vacuous safe.
  if (mine()) {
    const std::string af = HLIR_SCAN_FIXTURE_DIR "/initargv.c";
    auto ascan = [&](const std::string &flags, report::Report &r) {
      const std::string j = "/tmp/hlir_argv." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + flags + " --init-fn main --entries all --only '^demo_argv_entry$'"
                                                " --include-noarg --format json --output " + j + " " + af, &rc);
      std::string js = slurp(j);
      std::remove(j.c_str());
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "initargv json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry");
    };
    report::Report none, sep, att;
    ascan("", none);
    ascan("--externs " HLIR_SCAN_FIXTURE_DIR "/externs/argv.yaml", sep);
    ascan("--externs " HLIR_SCAN_FIXTURE_DIR "/externs/argv_attached.yaml", att);

    // with no stated command line the initialiser never parses anything, so the guarded defect does not exist
    CHECK(noFinding(none, "oob_read"), "without a stated argv the defect behind the option check is invisible");
    // ... and the report has to SAY that it chose a command line, because that choice is what hid it
    bool warned = false;
    for (auto &a : none.entries[0].assumptions)
      warned |= a.category == "project_init" && a.text.find("no command line was stated") != std::string::npos;
    CHECK(warned, "the invented command line is named as the claim it is");

    // with the real one, getopt parses it and the defect is found -- for BOTH POSIX spellings of an argument
    CHECK(sep.entries[0].verdict == report::Verdict::Bug && confirmedKind(sep, "oob_read"),
          "`-c 3`: the separate spelling is parsed and the defect found: " << report::verdictName(sep.entries[0].verdict));
    CHECK(att.entries[0].verdict == report::Verdict::Bug && confirmedKind(att, "oob_read"),
          "`-c3`: the attached spelling too: " << report::verdictName(att.entries[0].verdict));
    CHECK(sep.entries[0].coverage.blocksVisited > none.entries[0].coverage.blocksVisited,
          "and the initialiser gets further: " << sep.entries[0].coverage.blocksVisited << " vs "
                                               << none.entries[0].coverage.blocksVisited);
    // the stated command line is a CHOICE of configuration, so it is named too (§22.361 cuts both ways)
    bool named = false;
    for (auto &a : sep.entries[0].assumptions)
      named |= a.category == "project_init" && a.text.find("-c 3") != std::string::npos;
    CHECK(named, "the command line it did use is in the report verbatim");

    // an empty argv is not "no argv": argv[0] is the program name, so it is an input error, loud and once
    int rc = 0;
    std::string bad = run(bin + " --externs " HLIR_SCAN_FIXTURE_DIR "/externs/argv_empty.yaml --init-fn main"
                          " --entries all --only '^demo_argv_entry$' --include-noarg " + af + " 2>&1", &rc);
    CHECK(has(bad, "may not be empty"), "an empty argv fails loudly: " << bad.substr(0, 300));
  }

  // ---------------------------------------------------------------- `--externs` (DESIGN.md §22.379): a project
  // says which externals it has EXAMINED and judged not to contribute. Behaviour is unchanged -- they stay opaque
  // -- but "examined and judged irrelevant" and "nobody has looked" are different claims about the program, and
  // merging them is how the one entry that matters goes unnoticed in a list of seventy.
  if (mine()) {
    const std::string xf = HLIR_SCAN_FIXTURE_DIR "/externs.c";
    auto xscan = [&](const std::string &flags, report::Report &r) {
      const std::string j = "/tmp/hlir_externs." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + flags + " --entry demo_ext_entry --format json --output " + j + " " + xf, &rc);
      std::string js = slurp(j);
      std::remove(j.c_str());
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "externs json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry");
      return js;
    };
    auto assumptionWith = [](const report::EntryReport &e, const char *cat, const char *needle) -> const report::Assumption * {
      for (auto &a : e.assumptions)
        if (a.category == cat && a.text.find(needle) != std::string::npos) return &a;
      return nullptr;
    };
    report::Report bare, with;
    xscan("", bare);
    xscan("--externs " HLIR_SCAN_FIXTURE_DIR "/externs/project.yaml", with);

    // without the file both externals sit in the same list, indistinguishable
    const report::Assumption *b = assumptionWith(bare.entries[0], "model", "assumed opaque (arbitrary untainted result");
    CHECK(b && b->text.find("ext_log") != std::string::npos && b->text.find("ext_unexamined") != std::string::npos,
          "both are listed as unexamined to begin with: " << (b ? b->text : std::string("<none>")));
    // with it, the examined one MOVES -- it is not merely annotated in place
    const report::Assumption *w = assumptionWith(with.entries[0], "model", "assumed opaque (arbitrary untainted result");
    CHECK(w && w->text.find("ext_log") == std::string::npos,
          "the examined one leaves the unexamined list: " << (w ? w->text : std::string("<none>")));
    CHECK(w && w->text.find("ext_unexamined") != std::string::npos,
          "and the one nobody looked at stays in it: " << (w ? w->text : std::string("<none>")));
    const report::Assumption *sk = assumptionWith(with.entries[0], "skipped_external", "BY DECISION");
    CHECK(sk && sk->text.find("ext_log") != std::string::npos && sk->text.find("logging") != std::string::npos,
          "the decision is reported WITH its reason: " << (sk ? sk->text : std::string("<none>")));

    // a skip for a function this scan set never declares is a stale claim and must be said so: a list copied
    // from another project, or one left behind by a rename, otherwise looks like diligence it is not.
    report::Report stale;
    xscan("--externs " HLIR_SCAN_FIXTURE_DIR "/externs/stale.yaml", stale);
    const report::Assumption *st = assumptionWith(stale.entries[0], "skipped_external", "may be stale");
    CHECK(st && st->text.find("ext_never_declared_anywhere") != std::string::npos,
          "a stale skip is named: " << (st ? st->text : std::string("<none>")));

    // a skip with no reason is indistinguishable from an omission, which is the confusion this file exists to
    // remove -- so it is a project-wide input error, loud and once, not a quiet per-entry `unknown`.
    int rc = 0;
    std::string bad = run(bin + " --externs " HLIR_SCAN_FIXTURE_DIR "/externs/noreason.yaml --entry demo_ext_entry "
                          + xf + " 2>&1", &rc);
    CHECK(has(bad, "needs a reason"), "a reasonless skip fails loudly: " << bad.substr(0, 300));
  }

  // ---------------------------------------------------------------- the SDP's own resource-manager API
  // (models/qnx.yaml + the iofunc_ocb_attach model in models/qnx.core, DESIGN.md §22.378). Leaving these opaque
  // fails in BOTH directions at once, so both are asserted with their control.
  if (mine()) {
    const std::string qaf = HLIR_SCAN_FIXTURE_DIR "/qnx_api.c";
    auto qscan = [&](const std::string &flags) {
      const std::string j = "/tmp/hlir_qnxapi." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + flags + " --init-fn demo_qnx_init --entry demo_qnx_attr --entry demo_qnx_ocb"
                                               " --format json --output " + j + " " + qaf, &rc);
      std::string js = slurp(j);
      std::remove(j.c_str());
      report::Report r;
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "qnx_api json: " << e << " / " << out);
      return r;
    };
    report::Report off = qscan(""), on = qscan("--qnx");
    auto ent = [](const report::Report &r, const char *fn) -> const report::EntryReport * {
      for (auto &x : r.entries)
        if (x.function == fn) return &x;
      return nullptr;
    };
    const report::EntryReport *aOff = ent(off, "demo_qnx_attr"), *aOn = ent(on, "demo_qnx_attr");
    const report::EntryReport *oOff = ent(off, "demo_qnx_ocb"), *oOn = ent(on, "demo_qnx_ocb");
    CHECK(aOff && aOn && oOff && oOn, "both entries are in both reports");

    // direction 1 -- VACUOUS safe. Unmodelled, iofunc_attr_init leaves the structure zero, the guarded edge is
    // never taken and the out-of-bounds read behind it does not exist as far as the scan is concerned.
    CHECK(noFinding(off, "oob_read"), "without the model the out-of-bounds read is invisible");
    CHECK(aOn->coverage.blocksVisited > aOff->coverage.blocksVisited,
          "the model opens the edge the zeros had decided: " << aOn->coverage.blocksVisited << " vs " << aOff->coverage.blocksVisited);
    const report::Finding *af = nullptr;
    for (auto &f : aOn->findings)
      if (f.kind == "oob_read") af = &f;
    CHECK(af, "with the model it is found");
    CHECK(af && af->warning, "... as the analysis's own invention: nothing names what the library wrote there");
    bool uew = false;
    for (auto &a : aOn->assumptions) uew |= a.category == "unknown_external_write";
    CHECK(uew, "and the widening is named");

    // direction 2 -- PHANTOM defect. Unmodelled, ocb->attr stays NULL and the dereference is reported as a real
    // null dereference somebody can trigger. This one is not a missed bug, it is an invented one.
    bool phantom = false;
    for (auto &f : oOff->findings) phantom |= f.kind == "null_deref" && !f.warning;
    CHECK(phantom, "without the model ocb->attr is NULL and the dereference is reported as a defect");
    CHECK(noFinding(on, "null_deref"), "iofunc_ocb_attach's ocb->attr = attr removes the phantom");
    CHECK(oOn->coverage.blocksVisited > oOff->coverage.blocksVisited,
          "and the run no longer halts there: " << oOn->coverage.blocksVisited << " vs " << oOff->coverage.blocksVisited);

    // the rest of the API -- the four that decide how far the INITIALISER itself gets.
    auto rest = [&](const std::string &flags) {
      const std::string j = "/tmp/hlir_qnxrest." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + flags + " --entry demo_qnx_rest --format json --output " + j + " " + qaf, &rc);
      std::string js = slurp(j);
      std::remove(j.c_str());
      report::Report r;
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "qnx rest json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry");
      return r.entries[0];
    };
    report::EntryReport rOff = rest(""), rOn = rest("--qnx");
    CHECK(rOn.coverage.blocksVisited > rOff.coverage.blocksVisited,
          "modelling dispatch_create_channel/resmgr_attach/dispatch_context_alloc/procmgr_daemon lets the "
          "initialiser get further: " << rOn.coverage.blocksVisited << " vs " << rOff.coverage.blocksVisited);
    // the dispatch context holds UNKNOWN bytes, not zeros: zeroing it would assert `rcvid == 0`, a state the
    // resource manager's loop is never in, and would hide the read below it.
    bool ctxRead = false;
    for (auto &f : rOn.findings) ctxRead |= f.kind == "oob_read" && f.warning;
    CHECK(ctxRead, "a field of the dispatch context is unknown, so the index behind it is explored");
    // ... and every one of them keeps its failure edge: a module that does not check is making a real mistake,
    // and a model that cannot fail would delete that whole class of defect from the scan.
    CHECK(rOn.coverage.branchesVisited > rOff.coverage.branchesVisited,
          "the failure edges are real edges: " << rOn.coverage.branchesVisited << " vs " << rOff.coverage.branchesVisited);
  }

  // ---------------------------------------------------------------- `fills_unknown` (DESIGN.md §22.377): an
  // external wrote the caller's buffer and the model does not say what with. The three modelling answers must not
  // be interchangeable -- each one is a different claim about the program.
  if (mine()) {
    const std::string ff = HLIR_SCAN_FIXTURE_DIR "/fills_unknown.c";
    auto scan = [&](const std::string &models) {
      const std::string fj = "/tmp/hlir_fu." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + models + " --entry demo_fu_entry --format json --output " + fj + " " + ff, &rc);
      std::string fjs = slurp(fj);
      std::remove(fj.c_str());
      report::Report r;
      std::string e;
      CHECK(!fjs.empty() && report::fromJson(fjs.substr(fjs.find('{')), r, e), "fills_unknown json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry");
      return r;
    };
    report::Report none = scan("");
    report::Report unk = scan("--models " HLIR_SCAN_FIXTURE_DIR "/models_fu/unknown.yaml");
    report::Report src = scan("--models " HLIR_SCAN_FIXTURE_DIR "/models_fu/source.yaml");
    const report::EntryReport &n0 = none.entries[0], &u0 = unk.entries[0], &s0 = src.entries[0];

    // no model: the struct still holds the zeros the harness gave it, the guarded edge is never taken, and the
    // entry is pronounced safe for a reason that is an artefact of the analysis. This is the bug being fixed.
    CHECK(noFinding(none, "oob_read"), "with no model the out-of-bounds read is invisible -- vacuously safe");
    CHECK(n0.coverage.blocksVisited < u0.coverage.blocksVisited,
          "and a block is never entered at all: " << n0.coverage.blocksVisited << " vs " << u0.coverage.blocksVisited);

    // fills_unknown: the read is FOUND, and attributed to the analysis rather than to an attacker.
    const report::Finding *uf = nullptr;
    for (auto &f : u0.findings)
      if (f.kind == "oob_read") uf = &f;
    CHECK(uf, "fills_unknown finds the out-of-bounds read");
    CHECK(uf->warning && uf->reproducible == report::Reproducible::HarnessOnly,
          "... and does not claim anyone can trigger it: warning=" << uf->warning);
    CHECK(u0.verdict != report::Verdict::Bug, "so the entry is not pronounced buggy on invented bytes");
    bool named = false;
    for (auto &a : u0.assumptions) named |= a.category == "unknown_external_write" && a.text.find("@ext_attr_init") != std::string::npos;
    CHECK(named, "the widening is named, and names the model to make precise");

    // source: the same bytes, claimed to be the attacker's. A real defect -- which is the lie in the other
    // direction here, and the reason `fills_unknown` has to exist as its own primitive rather than be spelled
    // `source` with a made-up label.
    const report::Finding *sf = nullptr;
    for (auto &f : s0.findings)
      if (f.kind == "oob_read") sf = &f;
    CHECK(sf && !sf->warning && s0.verdict == report::Verdict::Bug,
          "`source` claims an attacker reaches it: " << (sf ? (sf->warning ? "warning" : "defect") : "missing"));
  }

  // ---------------------------------------------------------------- strncpy: a MISSING libc model is a false
  // positive generator, and the three halves of strncpy's contract each break a different lazy model (§22.385).
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/strncpy_model.c";
    const std::string sj = "/tmp/hlir_strncpy." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entries all --only '^demo_strncpy_(init|unterminated|nonul)$' --include-noarg"
                                " --buf-max 10 --runs 20000 --timeout 120 --format json --output " + sj + " " + sf, &rc);
    std::string js = slurp(sj);
    std::remove(sj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "strncpy json: " << e << " / " << out);
    auto entry = [&](const char *fn) -> const report::EntryReport & {
      for (auto &x : r.entries)
        if (x.function == fn) return x;
      CHECK(false, "entry @" << fn << " is in the report");
      return r.entries[0];
    };
    auto hard = [](const report::EntryReport &x) {
      std::string k;
      for (auto &f : x.findings)
        if (!f.warning) k += f.kind + "@" + std::to_string(f.loc.line) + " ";
      return k;
    };
    // (1) the destination is PADDED, so it is initialised. Without a model at all this was a uninit_read that
    // ended the very first run and left the entry essentially unanalysed.
    const report::EntryReport &i1 = entry("demo_strncpy_init");
    CHECK(hard(i1).empty(), "a padded destination reads as initialised: " << hard(i1));
    // (2) ...but a model that only zero-filled would also hide the real bug: strncpy writes NO terminator when the
    // source is not shorter than n, so reading the result as a C string runs off the end.
    const report::EntryReport &i2 = entry("demo_strncpy_unterminated");
    CHECK(i2.verdict == report::Verdict::Bug && confirmedKind(r, "oob_read"),
          "an unterminated destination is still a defect: " << report::verdictName(i2.verdict) << " " << hard(i2));
    // (3) ...and the SOURCE may legally have no NUL within n. Scanning it with plain strlen() (which is what the
    // first version of this model did) invents an out-of-bounds read of a perfectly valid object.
    const report::EntryReport &i3 = entry("demo_strncpy_nonul");
    CHECK(hard(i3).empty(), "the source is not scanned past n: " << hard(i3));
  }

  // ---------------------------------------------------------------- a char-class lookup over a CONSTANT needle is
  // answered in closed form, not by running the model's loop (DESIGN.md §22.385). Folding is only sound if it
  // answers exactly what the loop would, so the fixture turns every disagreement into an out-of-bounds write and
  // lets the scanner be its own oracle: `safe` means all eight hand-computed cases agreed for all 256 bytes.
  if (mine()) {
    const std::string ccf = HLIR_SCAN_FIXTURE_DIR "/charclass.c";
    const std::string cj = "/tmp/hlir_charclass." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry demo_charclass --runs 50000 --timeout 120 --format json --output " + cj + " " + ccf, &rc);
    std::string js = slurp(cj);
    std::remove(cj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "charclass json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    const report::EntryReport &cc = r.entries[0];
    std::string kinds;
    for (auto &f : cc.findings) kinds += f.kind + "@" + std::to_string(f.loc.line) + " ";
    CHECK(cc.findings.empty(), "the folded strchr/strrchr agree with the loop they replace: " << kinds);
    CHECK(cc.verdict == report::Verdict::SafeUnderAssumptions,
          "...and the exploration finished saying so: " << report::verdictName(cc.verdict));
    // The point of folding is the SEARCH, so the branch budget has to show it: with the loop in place the entry's
    // reachable conditional edges included strchr's own, two per needle character per call.
    CHECK(cc.coverage.branchesReachable > 0 && cc.coverage.branchesReachable < 80,
          "the needle's lookup contributes no branches of its own: " << cc.coverage.branchesVisited << "/"
                                                                     << cc.coverage.branchesReachable);
  }

  // ---------------------------------------------------------------- c-ares CVE-2023-31130, minimised. TIER A
  // (DESIGN.md §22.370): a regression guard, NOT a recall number -- the snippet is a different program from the
  // real `inet_net_pton_ipv6` and must never be quoted as one. What it pins is what the real one and this one
  // share: a bound recomputed from attacker data, a guard testing `==` where it needed `>`, and a write landing
  // BEFORE a real stack object (DESIGN.md §22.384).
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/cve_2023_31130.c";
    auto cve = [&](const std::string &extra, const char *entry) {
      const std::string cj = "/tmp/hlir_cve31130." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + extra + " --format json --output " + cj + " " + cf, &rc);
      std::string js = slurp(cj);
      std::remove(cj.c_str());
      report::Report r;
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "cve_2023_31130 json: " << e << " / " << out);
      for (auto &x : r.entries)
        if (x.function == entry) return x;
      CHECK(false, "the entry is in the report: " << js.substr(0, 300));
      return report::EntryReport{};
    };
    // The underflow itself: a write whose offset is NEGATIVE against a real 16-byte stack object. The sign is the
    // whole point -- it is caught by the UNSIGNED comparison in Memory::oobCond (off = 0xFF..FF > size), the same
    // expression that catches an overrun, so losing it would silently lose every container_of-style underflow.
    // The shift write is line 59 of the fixture (`*(endp - i) = ...`). Pinning the LINE matters: the same object
    // also carries a benign `tp + 2 > endp` pointer-arithmetic finding from the validator idiom a few lines up,
    // and a predicate loose enough to accept that one would pass without the defect ever being found.
    const unsigned kShiftLine = 59;
    auto underflow = [&](const report::EntryReport &e) -> const report::Finding * {
      for (auto &f : e.findings)
        if (!f.warning && (f.kind == "ptr_arith_oob" || f.kind == "oob_write") && f.loc.line == kShiftLine &&
            f.access.valid && f.access.objSizeKnown && f.access.objSize == 16)
          return &f;
      return nullptr;
    };
    // (a) DETECTION, from the published trigger. Deterministic and concrete: this half must never depend on the
    // search finding anything.
    report::EntryReport trig = cve("--entries all --only '^demo_cve_2023_31130_trigger$' --include-noarg --timeout 120", "demo_cve_2023_31130_trigger");
    const report::Finding *tf = underflow(trig);
    CHECK(tf, "the published trigger reaches a write before the object: " << trig.findings.size() << " finding(s), verdict "
                                                                          << report::verdictName(trig.verdict));
    CHECK(tf->access.offsetKnown && tf->access.offset < 0,
          "...at a NEGATIVE offset -- the sign is the whole point, and it is caught by the UNSIGNED comparison in "
          "Memory::oobCond (off = 0xFF..FF > size), the same expression that catches an overrun: "
              << (tf->access.offsetKnown ? std::to_string(tf->access.offset) : std::string("symbolic")));
    CHECK(tf->replay == report::ReplayStatus::Confirmed, "...and a concrete replay reproduces it");
    CHECK(tf->reproducible == report::Reproducible::RealInput,
          "...from a real input: nothing here is the harness's invention (the object is the program's own stack)");
    CHECK(trig.verdict == report::Verdict::Bug, "so the entry is a bug: " << report::verdictName(trig.verdict));
    // (b) SEARCH: the engine has to produce such an input itself, from a symbolic string, inside a bounded budget.
    // This is the half that regressed into a false `safe` when the frontier was culled without saying so (§22.383).
    report::EntryReport sym = cve("--entry demo_cve_2023_31130 --buf-max 10 --runs 20000 --timeout 120", "demo_cve_2023_31130");
    CHECK(underflow(sym), "the search produces a triggering string on its own: verdict " << report::verdictName(sym.verdict)
                                                                                          << ", " << sym.findings.size() << " finding(s)");
  }

  // ---------------------------------------------------------------- one attacker, one label. The bytes of a
  // parameter OBJECT used to carry TaintConfig's default "input" while a scalar parameter carried the label the
  // spec declares, so `--seed-bytes <label>=...` -- which looks the label up BY NAME -- silently did nothing for
  // every buffer (DESIGN.md §22.384).
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/seedlabel.c";
    auto sl = [&](const char *extra) {
      const std::string sj = "/tmp/hlir_seedlabel." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " --spec-dir " HLIR_SCAN_FIXTURE_DIR "/spec_seed --entry demo_seedlabel --runs 1 " +
                                extra + " --format json --output " + sj + " " + sf, &rc);
      std::string js = slurp(sj);
      std::remove(sj.c_str());
      report::Report r;
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "seedlabel json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
      return r.entries[0];
    };
    // `--runs 1`: the seed is the ONLY thing that decides the bytes, so this isolates the flag from the search.
    report::EntryReport bare = sl("");
    CHECK(bare.findings.empty(), "without a seed the first run cannot pass the fixture's gate: " << bare.findings.size());
    // The label the SPEC declares is the one a reader has, and it is the only name they can pass.
    report::EntryReport seeded = sl("--seed-bytes netmsg=4142434420");
    CHECK(seeded.verdict == report::Verdict::Bug,
          "seeding with the declared label reaches the defect on the first run: " << report::verdictName(seeded.verdict));
    bool labelled = false;
    for (auto &f : seeded.findings)
      for (auto &l : f.labels) labelled |= l == "netmsg";
    CHECK(labelled, "...and the bytes behind it carry that same label, not an internal default");
    // ...and the engine can write that seed ITSELF (DESIGN.md §22.386). `--runs 1` means the search does nothing
    // at all, so reaching the defect here is entirely the seed's doing. Nobody tells it the gate spells "ABCD":
    // each candidate is a model of a real path condition, derived by asking the solver to flip the deepest branch
    // of the run before it. There is no alphabet and no mutation -- the predecessor guessed bytes and could not
    // have passed this gate except by luck.
    report::EntryReport autos = sl("--auto-seed 400");
    CHECK(autos.verdict == report::Verdict::Bug,
          "an automatic seed passes a gate a zeroed one cannot, on the first run: " << report::verdictName(autos.verdict));
    const report::Assumption *aa = nullptr;
    for (auto &a : autos.assumptions)
      if (a.category == "auto_seed") aa = &a;
    CHECK(aa, "...and says so: picking where a search starts is a configuration, not a property of the program");
    CHECK(aa->text.find("ABCD") != std::string::npos, "the seed it chose is in the report: " << aa->text);
    CHECK(aa->text.find("model of a real path condition") != std::string::npos,
          "...and the report says where it came from, because a guessed byte and a solved one are not the same "
          "claim: " << aa->text);
    // The metric that picks the winner counts SOURCE LINES, not basic blocks, and this gate is why. `a || b || c
    // || d` lowers so that "failed at the last byte" and "passed" enter the SAME number of blocks (9) and take
    // the SAME number of edges (4); only the line sets differ ({6,8,11} against {6,8,11,12,13}). Scored by blocks
    // the two tie and "ABC" wins on insertion order, which is exactly what happened before this was measured.
    CHECK(aa->text.find("ABC\"") == std::string::npos, "...and it is not the input that stops one byte short: " << aa->text);
  }

  // ---------------------------------------------------------------- `if (p + n > end)` is undefined behaviour,
  // but it is not a memory-safety violation, and it must not decide the verdict (DESIGN.md §22.390).
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/cmponly_ptr.c";
    const std::string cj = "/tmp/hlir_cmponly." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry demo_cmponly --runs 3000 --timeout 120 --format json --output " + cj +
                              " " + cf, &rc);
    std::string js = slurp(cj);
    std::remove(cj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "cmponly json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    const report::EntryReport &er = r.entries[0];
    auto at = [&](unsigned line, const char *kind) -> const report::Finding * {
      for (auto &f : er.findings)
        if (f.loc.line == line && f.kind == kind) return &f;
      return nullptr;
    };
    // The out-of-range pointer is formed and compared, never dereferenced. ASan calls the same shape
    // invalid-pointer-pair, so it is REPORTED -- and it is a warning, so it does not reach the verdict.
    const report::Finding *one = at(20, "ptr_arith_oob");
    CHECK(one && one->warning, "a compared-but-never-dereferenced out-of-range pointer is a warning");
    CHECK(one->replay == report::ReplayStatus::Confirmed, "...and still a confirmed, real finding, not a guess");
    // Two chained ptr_adds: only the second is compared, and the first is compare-only only transitively.
    // c-ares ares_expand_name.c:175 is this shape, and on its own it kept a CVE-free tree at `bug`.
    const report::Finding *two = at(25, "ptr_arith_oob");
    CHECK(two && two->warning, "...and so is one that reaches the comparison through a further ptr_add");
    // The line the test exists to protect: the same kind, at a site where the pointer IS dereferenced, must
    // stay a finding. A downgrade rule that cannot tell these apart would hide real out-of-bounds accesses.
    const report::Finding *three = at(29, "ptr_arith_oob");
    CHECK(three && !three->warning, "an out-of-range pointer that is DEREFERENCED is not downgraded");
    CHECK(at(29, "oob_read") && !at(29, "oob_read")->warning, "...and the read itself is a finding too");
    CHECK(er.verdict == report::Verdict::Bug, "so the entry is still a bug, on the strength of the real access: "
                                                  << report::verdictName(er.verdict));
  }

  // ---------------------------------------------------------------- a fixed-length comparison is ONE question,
  // not one per byte (DESIGN.md §22.393). @strstr / @memmem used to spend a flippable branch per needle byte at
  // every candidate position; the inner comparison is now a branch-free conjunction (Machine::memEqFast) while
  // the outer scan keeps its branches, its termination semantics and its per-byte bounds checks.
  if (mine()) {
    // Half 1: a collapsed comparison must answer EXACTLY what the byte loop answered. The fixture hand-computes
    // thirteen strstr/memmem results and turns any disagreement into an out-of-bounds write, so the scanner is
    // its own oracle -- `safe` means all thirteen agreed. Verified to bite: flipping one expected value to a
    // wrong pointer turns this entry into `bug` with a confirmed oob_write.
    const std::string of = HLIR_SCAN_FIXTURE_DIR "/memeq_oracle.c";
    const std::string oj = "/tmp/hlir_memeqo." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry demo_memeq --runs 2000 --timeout 180 --format json --output " + oj + " " + of, &rc);
    std::string js = slurp(oj);
    std::remove(oj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "memeq oracle json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    unsigned real = 0;
    for (auto &f : r.entries[0].findings) real += f.warning ? 0u : 1u;
    CHECK(real == 0, "every folded strstr/memmem answer matches the loop's: " << real << " disagreement(s)");
    CHECK(r.entries[0].verdict != report::Verdict::Bug, "...so the oracle entry is not a bug: "
                                                            << report::verdictName(r.entries[0].verdict));
  }
  if (mine()) {
    // Half 2: what the collapse is FOR. The bug behind a 6-byte strstr match needs 100 runs when the inner loop
    // spends a branch per needle byte, and is found at 5 with the conjunction. Asserting it at 20 pins the win
    // with room to spare while still failing if the fold regresses -- the loop misses 3/3 at 20.
    const std::string gf = HLIR_SCAN_FIXTURE_DIR "/memeq_gate.c";
    const std::string gj = "/tmp/hlir_memeqg." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry strstr_gate --runs 20 --timeout 180 --format json --output " + gj + " " + gf, &rc);
    std::string js = slurp(gj);
    std::remove(gj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "memeq gate json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    // The reported kind is ptr_arith_oob, not oob_write: forming `small + 7` is already undefined and the run
    // stops there, before the store. It is NOT downgraded by §22.390 because the pointer is dereferenced.
    bool found = false;
    for (auto &f : r.entries[0].findings)
      found = found || (!f.warning && f.kind == "ptr_arith_oob" && f.loc.line == 16);
    CHECK(found, "the access behind a solved 6-byte substring is found in 20 runs (the byte loop needs 100): " << out);
    CHECK(r.entries[0].verdict == report::Verdict::Bug, "...and it decides the verdict: "
                                                            << report::verdictName(r.entries[0].verdict));
  }

  // ---------------------------------------------------------------- `queried == 0` with a large `reached`
  // is now a report-level warning (DESIGN.md §22.413). It is the §22.388 signature -- every memory-safety
  // check settled concretely, the solver never asked whether any of them CAN fail -- and it used to be
  // findable only by hand-running python over the JSON.
  if (mine()) {
    const std::string nf = HLIR_SCAN_FIXTURE_DIR "/neversym.c";
    auto scanOne = [&](const char *entry, report::Report &r) {
      const std::string nj = "/tmp/hlir_ns." + std::string(entry) + "." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " --entry " + entry + " --runs 200 --timeout 120 --format json --output " + nj + " " + nf, &rc);
      std::string js = slurp(nj);
      std::remove(nj.c_str());
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "neversym json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    };
    auto warned = [](const report::EntryReport &er) {
      for (auto &a : er.assumptions)
        if (a.category == "checks_never_symbolic") return true;
      return false;
    };
    // Loud on the sick shape: the index is a concrete loop counter, so the bounds checks are reached
    // thousands of times and never once handed to the solver.
    report::Report sick;
    scanOne("demo_neversym", sick);
    bool manyUnqueried = false;
    for (auto &c : sick.entries[0].checks)
      if (c.kind == "oob_read" && c.reached >= 1000 && c.queried == 0) manyUnqueried = true;
    CHECK(manyUnqueried, "the fixture really does reach oob_read many times with no query");
    CHECK(warned(sick.entries[0]), "...and that is reported, not left for a hand-written python one-liner");
    // Silent on the healthy shape -- this half is the point. A diagnostic that fires on working scans is
    // worse than none, because it trains the reader to skip it.
    report::Report ok;
    scanOne("demo_symindex", ok);
    CHECK(!warned(ok.entries[0]), "an index that comes FROM the attacker is queried, so no warning is due");
  }

  // ---------------------------------------------------------------- G2: symbolic index, constant table
  // DESIGN.md §22.465. A symbolic index used to be concretised to this run's slot, so the value read
  // back was untainted and the branch it fed was classified `const` -- executed, never symbolic, other
  // edge never explored. Both halves, because a fix that only makes the sick case pass proves nothing.
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/consttable.c";
    auto scanOne = [&](const char *entry, const char *extra, report::Report &r) {
      const std::string cj = "/tmp/hlir_ct." + std::string(entry) + "." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " --entry " + entry + " --runs 4000 --timeout 120 " + extra +
                            " --format json --output " + cj + " " + cf, &rc);
      std::string js = slurp(cj);
      std::remove(cj.c_str());
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "consttable json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    };
    report::Report sym;
    scanOne("tbl_symindex", "", sym);
    CHECK(sym.entries[0].coverage.missConst == 0,
          "a symbolic index into a const table must not leave a `const` branch: missConst="
              << sym.entries[0].coverage.missConst);
    CHECK(sym.entries[0].coverage.branchesVisited == sym.entries[0].coverage.branchesInEntered,
          "both edges: " << sym.entries[0].coverage.branchesVisited << "/"
                         << sym.entries[0].coverage.branchesInEntered);
    // The control: this shape never had the gap, so the change must not have cost it anything.
    report::Report cst;
    scanOne("tbl_constindex", "", cst);
    CHECK(cst.entries[0].coverage.branchesVisited == cst.entries[0].coverage.branchesInEntered,
          "constant index, symbolic shift was already complete and must stay so");
    // And the escape hatch really does turn it off, so a scan can be compared against the old behaviour.
    report::Report off;
    scanOne("tbl_symindex", "--no-table-select", off);
    // The old behaviour leaves the edge uncovered. WHICH bucket it lands in depends on the table: a
    // `const` one is `const` ("executed, condition never symbolic"), a merely-never-written one is
    // `global_init` -- G1's bucket (Sec.22.362), with the `global_initial_value` assumption naming the
    // global. This fixture uses nginx's shape, so it is the latter, and that is the whole arc: G1
    // gave the narrowing a name, G2's second half removes it.
    CHECK(off.entries[0].coverage.branchesVisited < off.entries[0].coverage.branchesInEntered,
          "--no-table-select restores the concretising behaviour: visited="
              << off.entries[0].coverage.branchesVisited << " of " << off.entries[0].coverage.branchesInEntered);
    CHECK(off.entries[0].coverage.missGlobalInit + off.entries[0].coverage.missConst > 0,
          "...and the missed edge is attributed to the global's initial value, not to budget");
  }

  // ---------------------------------------------------------------- the write side of selection
  // DESIGN.md §22.487, the dual of the block above. A STORE's symbolic offset used to be concretised
  // to this run's slot, so every other slot kept an untainted byte and a branch reading one of them
  // was classified `const`. Three claims: the gap is closed, the control is untouched, and the
  // escape hatch really restores the old behaviour (otherwise the first claim proves nothing).
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/storeselect.c";
    auto scanSt = [&](const char *entry, const char *extra, report::Report &r) {
      const std::string sj = "/tmp/hlir_ss." + std::string(entry) + "." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " --entry " + entry + " --runs 4000 --timeout 120 " + extra +
                            " --format json --output " + sj + " " + sf, &rc);
      std::string js = slurp(sj);
      std::remove(sj.c_str());
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "storeselect json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    };
    report::Report ssym;
    scanSt("st_symindex", "--store-select", ssym);
    CHECK(ssym.entries[0].coverage.missConst == 0,
          "a store at a symbolic offset must not leave a `const` branch behind it: missConst="
              << ssym.entries[0].coverage.missConst);
    CHECK(ssym.entries[0].coverage.branchesVisited == ssym.entries[0].coverage.branchesInEntered,
          "both edges: " << ssym.entries[0].coverage.branchesVisited << "/"
                         << ssym.entries[0].coverage.branchesInEntered);
    // The control: a constant store offset with a symbolic value never had the gap.
    report::Report scst;
    scanSt("st_constindex", "--store-select", scst);
    CHECK(scst.entries[0].coverage.branchesVisited == scst.entries[0].coverage.branchesInEntered,
          "constant store offset, symbolic value was already complete and must stay so");
    // The DEFAULT is the concretising behaviour: --store-select is opt-in until the
    // snprintf_chain_oob divergence of §22.487 is explained. This assertion is what makes the
    // first one mean something, and it will be the one to flip if the default ever changes.
    report::Report soff;
    scanSt("st_symindex", "", soff);
    CHECK(soff.entries[0].coverage.branchesVisited < soff.entries[0].coverage.branchesInEntered,
          "without --store-select the write is concretised and the edge stays uncovered: visited="
              << soff.entries[0].coverage.branchesVisited << " of "
              << soff.entries[0].coverage.branchesInEntered);
    CHECK(soff.entries[0].coverage.missConst > 0,
          "...and the missed edge is `const`: the slot it reads was written by a concretised offset");
  }

  // ---------------------------------------------------------------- the coverage frontier as a target set
  // (DESIGN.md §22.415). Three separate claims, and the fixture's comment says what is NOT claimed: this does
  // not assert that auto-targeting beats the baseline, only that the mechanism is wired correctly.
  if (mine()) {
    const std::string af = HLIR_SCAN_FIXTURE_DIR "/autotarget.c";
    auto scanAt = [&](unsigned rounds, report::Report &r) {
      const std::string aj = "/tmp/hlir_at." + std::to_string(getpid()) + "." + std::to_string(rounds) + ".json";
      int rc = 0;
      std::string out = run(bin + " --entry demo_autotarget --runs 600 --timeout 120 --buf-max 16 --auto-target " +
                                std::to_string(rounds) + " --format json --output " + aj + " " + af,
                            &rc);
      std::string js = slurp(aj);
      std::remove(aj.c_str());
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "autotarget json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    };
    report::Report base, targeted;
    scanAt(0, base);
    scanAt(2, targeted);
    const auto &bc = base.entries[0].coverage;

    // 1. The call frontier is the PROGRAM's functions. Before the filter it was mostly `__hlir_init.str*`, the
    //    engine's own string-literal initialisers, and with a cap of 20 they pushed the real names out of the
    //    report entirely -- on a libyaml scan all twenty shown entries were those.
    CHECK(!bc.notEntered.empty(), "the fixture leaves a call frontier");
    for (auto &n : bc.notEntered)
      CHECK(n.rfind("__hlir_", 0) != 0 && n.rfind("__str.", 0) != 0 && n.find(".__init") == std::string::npos,
            "no engine-generated symbol on the call frontier: " << n);

    // 2. Ordered so a never-entered function that CAN hold a defect comes before one that cannot. Alphabetically
    //    `cold_barren` sorts first, so seeing `cold_checked` first is the ordering doing work, not luck.
    auto pos = [&](const std::string &n) {
      for (size_t i = 0; i < bc.notEntered.size(); ++i)
        if (bc.notEntered[i] == n) return static_cast<long>(i);
      return -1L;
    };
    CHECK(pos("cold_checked") >= 0 && pos("cold_barren") >= 0, "both frontier functions are listed");
    CHECK(pos("cold_checked") < pos("cold_barren"),
          "the one with checks in it sorts first: " << pos("cold_checked") << " vs " << pos("cold_barren"));

    // 3. The targeted rounds are named in the report, and coverage is the UNION over all of them -- a multi-pass
    //    analysis must not report its last pass's numbers as the whole search's.
    bool named = false;
    for (auto &a : targeted.entries[0].assumptions) named |= a.category == "auto_target";
    CHECK(named, "a targeted round is declared in the report");
    const auto &tc = targeted.entries[0].coverage;
    CHECK(tc.branchesVisited >= bc.branchesVisited && tc.blocksVisited >= bc.blocksVisited &&
              tc.functionsEntered >= bc.functionsEntered,
          "union coverage never shrinks: " << tc.branchesVisited << "/" << bc.branchesVisited << " branches, "
                                           << tc.blocksVisited << "/" << bc.blocksVisited << " blocks");
  }

  // ---------------------------------------------------------------- an fp result's symbolic name must carry
  // its WIDTH (DESIGN.md §22.414). The TermManager outlives a single run, and the fp name was `fop.<fn>.<step>`:
  // two runs reaching the same (function, step) on different paths could ask for one name at two widths, which
  // tripped TermManager's assertion, killed the worker with SIGABRT, and left the entry as a silent `unknown`.
  // Found by it aborting a tcpdump print-stp.c sweep, where a whole entry came back empty and looked analysed.
  if (mine()) {
    const std::string ff = HLIR_SCAN_FIXTURE_DIR "/fopwidth.c";
    const std::string fj = "/tmp/hlir_fopw." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry demo_fopwidth --runs 3000 --timeout 120 --buf-max 64 --format json --output " + fj + " " + ff, &rc);
    std::string js = slurp(fj);
    std::remove(fj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "fopwidth json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    // The point of the test: the worker must survive. Before the fix this entry was `unknown` with
    // incomplete=[crashed] and runs=0 -- analysis that reports nothing and does not say it failed to run.
    for (auto &i : r.entries[0].incomplete)
      CHECK(i.code != "crashed", "the fp-width fixture must not abort a worker: " << i.code << " / " << i.detail);
    CHECK(r.entries[0].metrics.runs > 0, "and it must actually run: runs=" << r.entries[0].metrics.runs);
  }

  // ---------------------------------------------------------------- the rest of the character-class family
  // folds through the SAME closed form (DESIGN.md §22.412). memchr goes through Machine::charClassFast with
  // a count instead of a terminator; strpbrk/strspn/strcspn fold because their models ask @strchr about the
  // constant set, so they inherit §22.385's rule rather than adding a second one to keep correct.
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/charclass2.c";
    const std::string cj = "/tmp/hlir_cc2." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry demo_charclass2 --runs 3000 --timeout 180 --format json --output " + cj + " " + cf, &rc);
    std::string js = slurp(cj);
    std::remove(cj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "charclass2 json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    unsigned real = 0;
    for (auto &f : r.entries[0].findings) real += f.warning ? 0u : 1u;
    // The fixture hand-computes sixteen memchr/strpbrk/strspn/strcspn results and turns any disagreement
    // into an out-of-bounds write, so the scanner is its own oracle. Verified to bite: changing the
    // `memchr(zed, 'b', 3)` expectation -- the one that must look PAST an embedded NUL, which is exactly
    // what separates memchr's count from strchr's terminator -- turns this entry into `bug`.
    CHECK(real == 0, "every folded memchr/strpbrk/strspn/strcspn answer matches the loop's: " << real << " disagreement(s)");
    CHECK(r.entries[0].verdict != report::Verdict::Bug, "...so the oracle entry is not a bug: "
                                                            << report::verdictName(r.entries[0].verdict));
  }

  // ---------------------------------------------------------------- the search-budget profile picks the fold
  // candidate by itself (DESIGN.md §22.392). §22.385 collapsed @strchr because a human set HLIR_DEBUG_FRONTIER
  // and read the output; the profile was being computed on every run either way, so only the looking was manual.
  if (mine()) {
    const std::string ff = HLIR_SCAN_FIXTURE_DIR "/frontier_profile.c";
    const std::string fj = "/tmp/hlir_frontier." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry pick --runs 400 --timeout 120 --format json --output " + fj + " " + ff, &rc);
    std::string js = slurp(fj);
    std::remove(fj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "frontier json: " << e << " / " << out);
    CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
    const report::EntryReport &er = r.entries[0];
    CHECK(er.flippablePcsTotal > 0 && er.frontier.size() >= 2, "the profile is populated: total "
                                                                   << er.flippablePcsTotal << ", rows " << er.frontier.size());
    for (size_t i = 1; i < er.frontier.size(); ++i)
      CHECK(er.frontier[i - 1].flippablePcs >= er.frontier[i].flippablePcs, "ranked, descending: row " << i);
    auto row = [&](const char *fn) -> const report::EntryReport::FrontierSite * {
      for (auto &s : er.frontier)
        if (s.function == fn) return &s;
      return nullptr;
    };
    // Half 1: the library model whose loop costs many independent decisions per call is named, by itself.
    const report::EntryReport::FrontierSite *lib = row("strstr");
    CHECK(lib && lib->library, "@strstr is recognised as a model body (its branches carry no source location)");
    CHECK(lib->perCall >= 4.0, "...one call to it costs several independent flips: " << lib->perCall);
    CHECK(lib->foldCandidate, "...so it is named a fold candidate without anyone setting an env var");
    bool said = false;
    for (auto &a : er.assumptions)
      said = said || (a.category == "search_budget" && a.text.find("@strstr") != std::string::npos);
    CHECK(said, "...and the report says so in its assumptions, not only in a struct");
    // Half 2, the one that is easy to get wrong. @pick passes BOTH numeric gates -- it owns a quarter of the
    // frontier at six flips per call -- and must still not be flagged, because program control flow is the thing
    // under analysis and may not be summarised away. On c-ares this is the difference between reporting the cure
    // (inet_net_pton_ipv6 at 77% after the strchr fold) and reporting the disease.
    const report::EntryReport::FrontierSite *own = row("pick");
    CHECK(own && !own->library, "@pick is program code, not a model");
    CHECK(own->share >= 0.25 && own->perCall >= 4.0, "...and it clears both numeric thresholds: share "
                                                         << own->share << ", per call " << own->perCall);
    CHECK(!own->foldCandidate, "...yet it is NOT a fold candidate: only the `library` test holds it back, and it must");
  }

  // ---------------------------------------------------------------- a seed is not free: it SPENDS runs the
  // search would otherwise spend itself, and the search is the better spender (DESIGN.md §22.386).
  if (mine()) {
    const std::string vf = HLIR_SCAN_FIXTURE_DIR "/seedvalley.c";
    auto sv = [&](const char *extra) {
      const std::string vj = "/tmp/hlir_seedvalley." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " --entry demo_seedvalley " + extra + " --format json --output " + vj + " " + vf, &rc);
      std::string js = slurp(vj);
      std::remove(vj.c_str());
      report::Report r;
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "seedvalley json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
      return r.entries[0];
    };
    // The fixture is CVE-2023-31130's shape in miniature: '#' opens the guarded region but a LONE '#' is rejected
    // at once, while the digit branch is a broad, rewarding dead end. Every ordering that ranks candidates by how
    // much they cover prefers the dead end -- that is what starved "::" out of 500 mutational probes.
    CHECK(sv("--runs 4").verdict != report::Verdict::Bug, "four runs are not enough to cross the valley");
    CHECK(sv("--runs 8").verdict == report::Verdict::Bug,
          "...but the search's own frontier crosses it in eight, with no seed at all");
    // This is the honest half, and it is pinned deliberately rather than left as a hope. The automatic seed does
    // NOT make that earlier: at the budget where the unseeded search succeeds, the seeded one does not, because
    // the run it spends on its own candidate (and the frontier order that shifts behind it) costs more than the
    // candidate is worth. Measured, not assumed -- and the reason --auto-seed stays off by default.
    CHECK(sv("--runs 8 --auto-seed 400").verdict != report::Verdict::Bug,
          "a seed is not free: at the unseeded search's own threshold, seeding is still behind");
  }

  // ---------------------------------------------------------------- G2 promotes a global the entry reads, but a
  // POINTER field of it still read as NULL, and one probe pass under-promotes systematically (DESIGN.md §22.382).
  if (mine()) {
    const std::string pf = HLIR_SCAN_FIXTURE_DIR "/promoted_ptr.c";
    auto pp = [&](const char *extra) {
      const std::string pj = "/tmp/hlir_pp." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + extra + " --entry demo_pp --format json --output " + pj + " " + pf, &rc);
      std::string js = slurp(pj);
      std::remove(pj.c_str());
      report::Report r;
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "promoted_ptr json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
      return r.entries[0];
    };
    // Without promotion the magic gate is decided by the static initialiser (0) and nothing past it runs. This is
    // the baseline the `global_initial_value` assumption already names (§22.362); it is here to make the two
    // numbers below comparable rather than asserted.
    report::EntryReport base = pp("");
    CHECK(base.coverage.blocksVisited * 2 < base.coverage.blocksReachable,
          "an unpromoted global's magic gate stops the entry at its first branch: " << base.coverage.blocksVisited
                                                                                    << "/" << base.coverage.blocksReachable);
    // With promotion BOTH gates have to open. The integer one opened before §22.382 too; the pointer one did not,
    // for a mechanical reason that no amount of solving could get around -- promotion writes unconstrained bytes,
    // a pointer needs bytes carrying provenance, so the field read as obj 0 whatever the solver picked. And the
    // second gate is only VISIBLE once the first is open, so a single probe pass never puts `buf` in the read set
    // at all: this one assertion pins the pointer materialisation and the fixpoint iteration together, because
    // either one alone leaves the entry stuck at 4/7.
    report::EntryReport prom = pp("--promote-read-globals");
    CHECK(prom.coverage.blocksVisited >= base.coverage.blocksVisited + 4,
          "promoting the global opens the magic gate AND the pointer gate behind it: " << prom.coverage.blocksVisited
                                                                                        << "/" << prom.coverage.blocksReachable
                                                                                        << " vs " << base.coverage.blocksVisited);
    CHECK(prom.coverage.branchesVisited > base.coverage.branchesVisited,
          "...measured as branch edges too: " << prom.coverage.branchesVisited << " vs " << base.coverage.branchesVisited);
    // A widening has to be named (§22.361). The promoted_global assumption now has to say what happens to a
    // POINTER field, because "unconstrained value" alone does not describe materialising an object.
    bool named = false;
    for (auto &a : prom.assumptions)
      if (a.category == "promoted_global" && a.text.find("materialised on demand") != std::string::npos) named = true;
    std::string cats;
    for (auto &a : prom.assumptions) cats += a.category + " ";
    CHECK(named, "the pointer materialisation is named in the assumptions: " << cats);
  }

  // ---------------------------------------------------------------- a `session` object's bytes are the DRIVER's,
  // and a zero fill is not a neutral default but a specific state its constructor can never produce
  // (DESIGN.md §22.381). `content: unknown` gives them symbolic, HARNESS-LABELLED values: the module's own
  // validity gate becomes satisfiable, and a finding resting only on such a byte stays a warning.
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/session_unknown.c";
    auto su = [&](const char *dir, const char *fn) {
      const std::string sj = "/tmp/hlir_su." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " --spec-dir " HLIR_SCAN_FIXTURE_DIR "/" + dir + " --entry " + fn +
                                " --format json --output " + sj + " " + sf, &rc);
      std::string js = slurp(sj);
      std::remove(sj.c_str());
      report::Report r;
      std::string e;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "session_unknown json: " << e << " / " << out);
      CHECK(r.entries.size() == 1, "one entry: " << r.entries.size());
      return r;
    };
    // `content: zero` -- what every synthesised session was before §22.381. The gate `s->magic == SU_MAGIC` is
    // unsatisfiable against it, so the entry returns -1 on every run and reports itself SAFE while three of its
    // seven blocks were never reached. That verdict is the thing this change exists to stop.
    report::Report z = su("spec_su_zero", "demo_su_gated");
    CHECK(z.entries[0].verdict == report::Verdict::SafeUnderAssumptions && z.entries[0].findings.empty(),
          "a zero-filled session hides the defect behind the module's own gate: " << report::verdictName(z.entries[0].verdict));
    CHECK(z.entries[0].coverage.blocksVisited < z.entries[0].coverage.blocksReachable,
          "...and the coverage says so: " << z.entries[0].coverage.blocksVisited << "/" << z.entries[0].coverage.blocksReachable);
    // `content: unknown` -- the gate opens. The defect behind it is driven by the ATTACKER's buffer, so it is a
    // real defect, confirmed by replay, and reproducible from a real input: the session's invented bytes make the
    // path feasible but do not decide the out-of-bounds offset.
    report::Report u = su("spec_su", "demo_su_gated");
    CHECK(u.entries[0].coverage.blocksVisited == u.entries[0].coverage.blocksReachable,
          "an unknown session lets the entry be analysed at all: " << u.entries[0].coverage.blocksVisited << "/"
                                                                   << u.entries[0].coverage.blocksReachable);
    CHECK(u.entries[0].verdict == report::Verdict::Bug && confirmedKind(u, "oob_write"),
          "...and the defect behind the gate is found and replayed: " << report::verdictName(u.entries[0].verdict));
    const report::Finding *gf = nullptr;
    for (auto &f : u.entries[0].findings)
      if (f.kind == "oob_write") gf = &f;
    CHECK(gf && !gf->warning && gf->reproducible == report::Reproducible::RealInput,
          "the offset comes from the attacker's buffer, not from an invented byte: "
              << (gf ? report::reproducibleName(gf->reproducible) : "missing"));
    // The witness has to SHOW the invented bytes. Without them a reader is handed "object of 8 bytes" for the
    // very field that made the path feasible, and cannot tell why the gate opened.
    bool sessionBytesShown = false;
    for (auto &c : gf->witness)
      if (c.name == "s") sessionBytesShown = c.value.find("non-zero bytes:") != std::string::npos;
    CHECK(sessionBytesShown, "the session's invented content is in the witness");
    // ...and a defect decided ONLY by a session byte is the harness's own invention: a warning, harness_only, and
    // it does not make the entry a bug. Same discipline as the synthesis frontier (§22.365) -- which is exactly
    // what it is, since the bytes come from the same source and carry the same label.
    report::Report o = su("spec_su", "demo_su_sessiononly");
    CHECK(o.entries[0].verdict != report::Verdict::Bug,
          "a session-only defect does not make the entry a bug: " << report::verdictName(o.entries[0].verdict));
    bool sawWarn = false;
    for (auto &f : o.entries[0].findings)
      if (f.kind == "oob_write") {
        sawWarn = true;
        CHECK(f.warning && f.reproducible == report::Reproducible::HarnessOnly,
              "it is reported, as a harness_only warning: warning=" << f.warning << " " << report::reproducibleName(f.reproducible));
      }
    CHECK(sawWarn, "the session-only defect is still reported rather than dropped");
  }

  // ---------------------------------------------------------------- coverage is a fraction, and `init:` was
  // changing its DENOMINATOR (DESIGN.md §22.376). Running the initialiser must make the numerator BETTER; it may
  // not quietly enlarge the set of blocks the entry is measured against.
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/covdenom.c";
    auto cov = [&](const std::string &extra) {
      const std::string cj = "/tmp/hlir_covd." + std::to_string(getpid()) + ".json";
      int rc = 0;
      std::string out = run(bin + " " + extra + " --entry demo_cov_entry --format json --output " + cj + " " + cf, &rc);
      std::string cjs = slurp(cj);
      std::remove(cj.c_str());
      report::Report r;
      std::string e;
      CHECK(!cjs.empty() && report::fromJson(cjs.substr(cjs.find('{')), r, e), "covdenom json: " << e << " / " << out);
      for (auto &x : r.entries)
        if (x.function == "demo_cov_entry") return x.coverage;
      CHECK(false, "the entry is in the report: " << cjs.substr(0, 400));
      return report::Coverage{};
    };
    report::Coverage bare = cov(""), withInit = cov("--init-fn demo_cov_init");
    CHECK(bare.blocksReachable > 0, "the baseline measured something");
    CHECK(withInit.blocksReachable == bare.blocksReachable,
          "the initialiser's own call graph is not part of what this entry is measured against: "
              << withInit.blocksReachable << " vs " << bare.blocksReachable);
    CHECK(withInit.functionsReachable == bare.functionsReachable,
          "and neither are its functions: " << withInit.functionsReachable << " vs " << bare.functionsReachable);
    CHECK(withInit.blocksVisited >= bare.blocksVisited,
          "running the initialiser may only help the numerator: " << withInit.blocksVisited << " vs " << bare.blocksVisited);
    CHECK(withInit.blocksVisited <= withInit.blocksReachable, "and coverage cannot exceed 100%");
  }

  // ---------------------------------------------------------------- the target set has to be NAMEABLE and it has
  // to be about state an initialiser could establish (DESIGN.md §22.375). A runtime object id is an allocation-order
  // counter: it means nothing to a reader and nothing across two passes.
  if (mine()) {
    const std::string rf = HLIR_SCAN_FIXTURE_DIR "/readset.c";
    const std::string rj = "/tmp/hlir_readset." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string ro = run(bin + " --record-reads --entry demo_readset --format json --output " + rj + " " + rf, &rc);
    std::string rjs = slurp(rj);
    std::remove(rj.c_str());
    report::Report rr;
    std::string re;
    CHECK(!rjs.empty() && report::fromJson(rjs.substr(rjs.find('{')), rr, re), "readset json: " << re << " / " << ro);
    const report::EntryReport *rs = nullptr;
    for (auto &x : rr.entries)
      if (x.function == "demo_readset") rs = &x;
    CHECK(rs, "the entry is in the report");
    std::set<std::string> locs;
    for (auto &r : rs->reads) locs.insert(r.location);
    CHECK(!locs.empty(), "the target set was measured at all");
    for (auto &l : locs)
      CHECK(l.rfind("obj:#", 0) != 0, "every location is nameable -- a bare runtime id is not comparable: " << l);
    // `demo_rs_helper`'s `scratch` and `demo_readset`'s own `local` are stack slots: no initialiser can establish
    // them and they hold no static initial value, so they are not target-set members at all.
    for (auto &l : locs)
      CHECK(l.find("demo_rs_helper") == std::string::npos && l.find("demo_readset@") == std::string::npos,
            "a callee's own stack slot is not part of the target set: " << l);
    CHECK(locs.count("s"), "the entry parameter is named the way the spec names it: " << joinSet(locs));
    CHECK(locs.count("obj:s.0"), "and so is the object behind its pointer field: " << joinSet(locs));
    CHECK(locs.count("global:gReadsetLimit"), "a global the chain reads is in the set: " << joinSet(locs));
  }

  // ---------------------------------------------------------------- the session constructor (`setup:`): the
  // per-fd object a handler is handed is built by RUNNING the module's own `.open`, not synthesised field by
  // field, and UB inside that constructor decides nothing about the entry (DESIGN.md §22.368 §7).
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/setup_ctor.c";
    const std::string sd = HLIR_SCAN_FIXTURE_DIR "/specs_setup";
    const std::string sj = "/tmp/hlir_setupctor." + std::to_string(getpid()) + ".json";
    auto scanSetup = [&](const std::string &extra, report::Report &rr) {
      int src = 0;
      std::string so = run(bin + extra + " --entry demo_sc_ioctl --entry demo_sc_ioctl_oob --format json --output " + sj + " " + sf, &src);
      std::string js = slurp(sj);
      std::remove(sj.c_str());
      std::string se;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), rr, se), "setup_ctor scan json: " << se << " " << so);
      return js;
    };
    auto vOf = [](const report::Report &rr, const std::string &fn) {
      for (auto &x : rr.entries)
        if (x.function == fn) return std::string(report::verdictName(x.verdict));
      return std::string("missing");
    };

    // Without the constructor the session is synthesised field by field, so `s->scale` -- a field NOTHING but the
    // constructor ever writes -- can be zero, and the scan reports a division the real driver cannot perform.
    report::Report r0;
    scanSetup("", r0);
    CHECK(vOf(r0, "demo_sc_ioctl") == "bug", "without the constructor the invented session divides by zero: " << vOf(r0, "demo_sc_ioctl"));

    // With it, the field holds what the constructor put there and the finding is gone -- it was never a defect.
    report::Report r1;
    std::string js1 = scanSetup(" --spec-dir " + sd, r1);
    CHECK(vOf(r1, "demo_sc_ioctl") == "safe_under_assumptions",
          "running the real constructor removes it: " << vOf(r1, "demo_sc_ioctl"));
    // ... and the handler's own defect is NOT removed, or "run the constructor" would just be a way of making
    // findings disappear.
    CHECK(vOf(r1, "demo_sc_ioctl_oob") == "bug", "a defect of the handler's own survives: " << vOf(r1, "demo_sc_ioctl_oob"));

    const report::EntryReport *se1 = nullptr;
    for (auto &x : r1.entries)
      if (x.function == "demo_sc_ioctl") se1 = &x;
    CHECK(se1 && se1->setupFunction == "demo_sc_open_ub", "the report names the constructor it ran: " << (se1 ? se1->setupFunction : "none"));
    bool named = false;
    for (auto &a : se1 ? se1->assumptions : std::vector<report::Assumption>{})
      named |= a.category == "session_ctor" && has(a.text, "not synthesised field by field") && has(a.text, "assumed to succeed");
    CHECK(named, "replacing one narrowing with a smaller one is still a narrowing, and it is named: " << js1.substr(0, 1200));

    // The constructor in that spec performs real UB on the way. Round 49b measured what happens when such a UB is
    // allowed to speak for the entry: all 87 sound/core entries became `bug` and none was analysed.
    bool warnOnly = false, confirmedInSetup = false;
    for (auto &f : se1 ? se1->findings : std::vector<report::Finding>{}) {
      if (f.kind != "ptr_arith_oob") continue;
      if (f.warning) warnOnly = true; else confirmedInSetup = true;
    }
    CHECK(warnOnly, "UB inside the constructor is still reported, as a warning: " << js1.substr(0, 1200));
    CHECK(!confirmedInSetup, "and never as a confirmed defect of this entry");
    bool harnessOnly = false;
    for (auto &f : se1 ? se1->findings : std::vector<report::Finding>{})
      if (f.kind == "ptr_arith_oob" && f.warning) harnessOnly = f.reproducible == report::Reproducible::HarnessOnly;
    CHECK(harnessOnly, "and it is marked harness_only: chasing a real-world trigger for it is wasted work");
  }

  // ---------------------------------------------------------------- container_of on an empty list computes a
  // pointer before the object and never dereferences it. Only the ARITHMETIC check is waived; the dereference is
  // not (DESIGN.md §22.368).
  if (mine()) {
    const std::string cf = HLIR_SCAN_FIXTURE_DIR "/container_of.c";
    const std::string cj = "/tmp/hlir_containerof." + std::to_string(getpid()) + ".json";
    int crc = 0;
    std::string co = run(bin + " --entry demo_co_empty_walk --entry demo_co_arith_only --entry demo_co_kernel_walk"
                               " --entry demo_co_deref --format json --output " + cj + " " + cf, &crc);
    std::string js = slurp(cj);
    std::remove(cj.c_str());
    report::Report cr;
    std::string ce;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), cr, ce), "container_of scan json: " << ce << " " << co);
    auto vOf = [&](const std::string &fn) {
      for (auto &x : cr.entries)
        if (x.function == fn) return std::string(report::verdictName(x.verdict));
      return std::string("missing");
    };
    // the idiom itself: in sound/core round 49b every one of 87 "confirmed" findings was this shape
    CHECK(vOf("demo_co_empty_walk") == "safe_under_assumptions",
          "walking an empty list is not a defect: " << vOf("demo_co_empty_walk"));
    CHECK(vOf("demo_co_arith_only") == "safe_under_assumptions",
          "nor is the bare container_of arithmetic: " << vOf("demo_co_arith_only"));
    // the kernel's own spelling -- `void *__mptr` in a statement expression. The first version of the waiver only
    // matched the `(char *)` form, so this fixture passed while sound/core saw no change at all: Clang reports
    // `void` as width ZERO, and a "pointee is one byte" test rejects every real container_of.
    CHECK(vOf("demo_co_kernel_walk") == "safe_under_assumptions",
          "the kernel's void*-via-statement-expression spelling is the same idiom: " << vOf("demo_co_kernel_walk"));
    CHECK(noFinding(cr, "ptr_arith_oob"), "and no pointer-arithmetic finding survives on any of them: " << js.substr(0, 700));
    // ... and the control that keeps the waiver honest. A waiver that also swallowed the dereference would make a
    // whole class of real defects silent, which is a far worse trade than the false positive it removes.
    CHECK(vOf("demo_co_deref") == "bug",
          "a container_of result that IS dereferenced out of bounds is still a defect: " << vOf("demo_co_deref"));
    bool realOob = false;
    for (auto &x : cr.entries)
      if (x.function == "demo_co_deref")
        for (auto &f : x.findings) realOob |= f.kind == "oob_read" && !f.warning;
    CHECK(realOob, "and it is a confirmed out-of-bounds read: " << js.substr(0, 700));

    // ---- the evidence a reader needs to rebuild the state, rather than re-derive the defect (DESIGN.md §22.369)
    const report::Finding *df = nullptr;
    for (auto &x : cr.entries)
      if (x.function == "demo_co_deref")
        for (auto &f : x.findings)
          if (f.kind == "oob_read") df = &f;
    CHECK(df && df->access.valid, "the failing access is reported in numbers: " << js.substr(0, 900));
    // `the_list` is 16 bytes and the container_of result points 4 before it, so `->value` reads at offset 16
    CHECK(df && df->access.objName == "the_list" && df->access.objSizeKnown && df->access.objSize == 16,
          "it names the object it hit and how big it is: " << (df ? df->access.objName : "none"));
    CHECK(df && df->access.offsetKnown && df->access.offset == 16 && df->access.width == 4 && df->access.access == "r",
          "and the offset, width and direction: " << js.substr(0, 900));
    bool sawGlobal = false;
    for (auto &o : df ? df->objects : std::vector<report::EvidenceObject>{})
      if (o.name == "the_list" && o.kind == "global" && !o.progWritten) sawGlobal = true;
    CHECK(sawGlobal, "the globals the run touched are listed, with whether the PROGRAM wrote them: " << js.substr(0, 900));
    // nothing here was invented by the harness, so a real input really can produce it
    CHECK(df && df->reproducible == report::Reproducible::RealInput,
          "and it is marked as reproducible from a real input");

    // ---- `safe` carries its own evidence too, and that evidence is honest about being weak: every check on the
    // empty-list walk is settled WITHOUT the solver, which is the opposite of "the solver proved it safe" (§22.369 §4)
    const report::EntryReport *we = nullptr;
    for (auto &x : cr.entries)
      if (x.function == "demo_co_empty_walk") we = &x;
    CHECK(we && !we->checks.empty(), "a safe entry reports what was actually checked: " << js.substr(0, 900));
    bool allConcrete = we != nullptr;
    for (auto &c : we ? we->checks : std::vector<report::CheckSummary>{})
      allConcrete &= c.queried == 0 && c.decidedConcretely == c.reached;
    CHECK(allConcrete, "and here every check was decided without ever asking the solver -- weak evidence, stated as such");
    CHECK(we && !we->taintReach.any(), "no attacker value reached an index, a loop bound, an allocation size or a sink");
  }

  // ---------------------------------------------------------------- the project initialiser: it runs, it runs IN
  // ORDER, and -- the part the sound/core round measured the hard way -- UB inside it neither decides the entry's
  // verdict nor stops the entry from being analysed (DESIGN.md §22.368).
  if (mine()) {
    const std::string nf = HLIR_SCAN_FIXTURE_DIR "/init_entry.c";
    const std::string nj = "/tmp/hlir_initentry." + std::to_string(getpid()) + ".json";
    const std::string ents = " --entry demo_init_gated --entry demo_init_real_oob";
    auto scanInit = [&](const std::string &inits, report::Report &rr) {
      int irc = 0;
      std::string so = run(bin + inits + ents + " --format json --output " + nj + " " + nf, &irc);
      std::string js = slurp(nj);
      std::remove(nj.c_str());
      std::string ie;
      CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), rr, ie), "init_entry scan json: " << ie << " " << so);
      return js;
    };
    auto vOf = [](const report::Report &rr, const std::string &fn) {
      for (auto &x : rr.entries)
        if (x.function == fn) return std::string(report::verdictName(x.verdict));
      return std::string("missing");
    };
    auto hasFinding = [](const report::Report &rr, const std::string &fn, const std::string &kind, bool warning) {
      for (auto &x : rr.entries)
        if (x.function == fn)
          for (auto &f : x.findings)
            if (f.kind == kind && f.warning == warning) return true;
      return false;
    };

    // (1) nothing runs: `g_limit` is still its static initialiser, so the dead edge is live and the scan reports
    // an out-of-bounds read of code the real module never reaches.
    report::Report r1;
    scanInit("", r1);
    CHECK(vOf(r1, "demo_init_gated") == "bug", "without the initialiser the dead edge is live: " << vOf(r1, "demo_init_gated"));

    // (2) the SECOND initialiser alone does nothing, because it is guarded by what the first one sets. This is
    // what proves the order is real execution and not a list we merely read.
    report::Report r2;
    scanInit(" --init-fn demo_init_b", r2);
    CHECK(vOf(r2, "demo_init_gated") == "bug",
          "demo_init_b alone cannot set g_limit -- its guard needs demo_init_a first: " << vOf(r2, "demo_init_gated"));

    // (3) both, in order: the dead edge is gone, and the entry's OWN defect is untouched.
    report::Report r3;
    scanInit(" --init-fn demo_init_a --init-fn demo_init_b", r3);
    CHECK(vOf(r3, "demo_init_gated") == "safe_under_assumptions",
          "in order, the initialisers kill the false finding: " << vOf(r3, "demo_init_gated"));
    CHECK(vOf(r3, "demo_init_real_oob") == "bug", "a defect of the entry's own is not affected: " << vOf(r3, "demo_init_real_oob"));

    // (4) ... and an initialiser that performs real UB on the way (`&g_tbl[0] - 1`, the shape of the empty-list
    // `container_of` in `list_for_each_entry`) must not take the entry down with it. In sound/core round 49b one
    // such site, in `snd_info_register`, halted the first run of all 87 entries and made every verdict `bug`.
    report::Report r4;
    std::string js4 = scanInit(" --init-fn demo_init_a --init-fn demo_init_b --init-fn demo_init_ub", r4);
    CHECK(vOf(r4, "demo_init_gated") == "safe_under_assumptions",
          "UB inside the initialiser does not make the entry a bug: " << vOf(r4, "demo_init_gated"));
    CHECK(hasFinding(r4, "demo_init_gated", "ptr_arith_oob", /*warning=*/true),
          "it is still reported, as a warning: " << js4.substr(0, 900));
    CHECK(!hasFinding(r4, "demo_init_gated", "ptr_arith_oob", /*warning=*/false),
          "and never as a confirmed defect of this entry: " << js4.substr(0, 900));
    // the message names the setup code, whichever kind it is (the project initialiser here, a session constructor
    // elsewhere) -- asserted on the parsed finding, not on the report text, so a rewording of the sentence does
    // not silently turn this check into a no-op.
    bool saysWhere = false;
    for (auto &x : r4.entries)
      for (auto &f : x.findings)
        if (f.kind == "ptr_arith_oob" && f.warning)
          saysWhere |= has(f.message, "setup code") && has(f.message, "initialiser");
    CHECK(saysWhere, "and the message says where it really is: " << js4.substr(0, 900));
    // the entry is still ANALYSED -- the half that actually cost the sound/core round its coverage
    CHECK(vOf(r4, "demo_init_real_oob") == "bug" && hasFinding(r4, "demo_init_real_oob", "oob_read", false),
          "the entry's own defect is still found past the initialiser's UB: " << vOf(r4, "demo_init_real_oob"));
  }

  // ---------------------------------------------------------------- the harness's own structural choices are not
  // attacker data: only the three SECURITY verdicts that ask `isTainted` must change, the solver plumbing that
  // asks the same question to mean "is this symbolic" must not (DESIGN.md §22.363)
  if (mine()) {
    const std::string hf = HLIR_SCAN_FIXTURE_DIR "/harness_taint.c";
    const std::string hj = "/tmp/hlir_harness_taint." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string ho = run(bin + " --entries iface --format json --output " + hj + " " + hf, &rc);
    std::string js = slurp(hj);
    std::remove(hj.c_str());
    CHECK(!js.empty(), "the scan produced a report: " << ho);
    CHECK(has(js, "demo_ioctl"), "the handler was selected through its file_operations slot: " << js.substr(0, 300));
    // the entry really was explored -- otherwise "no warning" would be vacuous
    CHECK(has(js, "\"blocks_visited\"") && !has(js, "\"blocks_visited\": 0"), "the loop was actually executed: " << js);
    CHECK(!has(js, "tainted_loop_bound"),
          "a loop whose bound is the literal 31, reading only harness-chosen fields, is not attacker-governed: " << js);
    CHECK(!has(js, "tainted_index"), "nor is a harness-chosen value an attacker-controlled index: " << js);
  }

  // ---------------------------------------------------------------- pointer synthesis stops at a finite depth, and
  // past that frontier every pointer reads as NULL. That is a WIDENING -- it manufactures a defect rather than
  // hiding one -- so the report has to NAME it, exactly as it names the narrowings (DESIGN.md §22.364)
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/synth_frontier.c";
    const std::string sj = "/tmp/hlir_synth_frontier." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string so = run(bin + " --link --entries iface --format json --output " + sj + " " + sf, &rc);
    std::string js = slurp(sj);
    std::remove(sj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "synth_frontier scan json: " << e << " " << so);
    CHECK(r.entries.size() == 5, "all five file_operations slots were selected: " << r.entries.size());
    bool named = false, saysUnbounded = false;
    for (auto &x : r.entries)
      for (auto &a : x.assumptions) {
        named |= a.category == "synthesis_frontier" && has(a.text, "3 level(s) deep") && has(a.text, "as NULL");
        // the suppression below is a NARROWING and may not be invisible (DESIGN.md §22.361)
        saysUnbounded |= a.category == "synthesis_frontier" && has(a.text, "out-of-bounds");
      }
    CHECK(named, "the report names the frontier and how deep it is: " << js);
    // A declared `prologue:` is NOT executed (DESIGN.md §22.368 §1). The key used to carry a comment claiming it
    // ran with its own budget accounting, which made a reader of the yaml believe initialisation had happened.
    // The report has to say it, or the next person reads the yaml and believes the comment again.
    bool saysPrologueNotRun = false;
    for (auto &x : r.entries)
      for (auto &a : x.assumptions)
        saysPrologueNotRun |= has(a.text, "module_init") && has(a.text, "NOT executed");
    CHECK(saysPrologueNotRun, "the report says the declared prologue was not run: " << js.substr(0, 900));
    CHECK(saysUnbounded, "the report says bounds are not checked past the frontier: " << js);
    auto vOf = [&](const std::string &fn) {
      for (auto &x : r.entries) if (x.function == fn) return std::string(report::verdictName(x.verdict));
      return std::string("missing");
    };
    // the control: a chain that stops AT the frontier never depended on any of this
    CHECK(vOf("demo_inside_ioctl") == "safe_under_assumptions", "a chain that stops at the frontier is clean: " << vOf("demo_inside_ioctl"));
    // ... and one pointer PAST it is materialised on demand instead of read as NULL, so it is clean too
    CHECK(vOf("demo_chain_ioctl") == "safe_under_assumptions", "a pointer past the frontier is built, not nulled: " << vOf("demo_chain_ioctl"));
    // ... and an array walked inside such an object is measured against a size we invented, so it is not judged
    CHECK(vOf("demo_array_read") == "safe_under_assumptions", "an array past the frontier is not bounds-judged: " << vOf("demo_array_read"));
    CHECK(noFinding(r, "null_deref"), "the frontier no longer manufactures a null_deref: " << js.substr(0, 600));
    CHECK(noFinding(r, "ptr_arith_oob") && noFinding(r, "oob_read"),
          "nor an overrun of its own stand-in size: " << js.substr(0, 600));
    // ... and the content out there is invented too: a divisor only the harness could have zeroed is reported with
    // its witness, but as a warning, so it never becomes the entry's verdict (DESIGN.md §22.365)
    const report::Finding *dz = nullptr;
    for (auto &x : r.entries)
      for (auto &f : x.findings)
        if (f.kind == "div_by_zero") dz = &f;
    CHECK(dz, "the divisor read past the frontier is still reported, not silently dropped: " << js);
    CHECK(dz && dz->warning, "but only as a warning: " << (dz ? dz->message : std::string("<none>")));
    CHECK(dz && has(dz->message, "bytes the analysis invented rather than read from the program") && has(dz->message, "synthesis frontier"),
          "and it says why: " << (dz ? dz->message : std::string()));
    CHECK(vOf("demo_div_write") == "safe_under_assumptions", "a warning does not make the entry a bug: " << vOf("demo_div_write"));
    // ... and where the program states the field's invariant in its own assertion macro, there is no finding at all:
    // the fieldAsserts harvest (§22.358) now reaches objects materialised past the frontier too (§22.365)
    bool divOnW = false;
    for (auto &x : r.entries)
      if (x.function == "demo_div_llseek")
        for (auto &f : x.findings) divOnW |= f.kind == "div_by_zero";
    CHECK(!divOnW, "an asserted-nonzero divisor past the frontier is not a finding at all: " << js);
    CHECK(vOf("demo_div_llseek") == "safe_under_assumptions", "and its entry is clean: " << vOf("demo_div_llseek"));
  }

  // ------------------------------------------------- QNX resmgr: the request payload lives past the declared type
  //
  // `io_devctl_t` is a 16-byte union and the client's payload starts at byte 16 of the SAME receive buffer, so a
  // devctl handler sized by its declared pointee type is out of bounds on its first payload access -- a fact about
  // the C declaration and nothing else (models/interfaces/qnx_resmgr.yaml). Both halves of the fix are asserted
  // here, each with the control that shows it is load-bearing:
  //
  //   the interface contract   gives `msg` the real 2048-byte extent. Without it EVERY handler is a confirmed OOB,
  //                            including one with no defect (control A below).
  //   models/qnx.core          gives iofunc_devctl_default() its _RESMGR_DEFAULT return. Without it the handler
  //                            returns at its first line and the entry is a VACUOUS safe -- the real defect
  //                            disappears silently (control B below).
  if (mine()) {
    const std::string qf = HLIR_SCAN_FIXTURE_DIR "/qnx_devctl.c";
    const std::string qj = "/tmp/hlir_qnx_devctl." + std::to_string(getpid()) + ".json";
    auto scan = [&](const std::string &flags, report::Report &rr) {
      int qrc = 0;
      std::string qso = run(bin + " " + flags + " --format json --output " + qj + " " + qf, &qrc);
      std::string qjs = slurp(qj);
      std::remove(qj.c_str());
      std::string qe;
      CHECK(!qjs.empty() && report::fromJson(qjs.substr(qjs.find('{')), rr, qe), "qnx_devctl scan json: " << qe << " " << qso);
      return qjs;
    };
    auto verdictOf = [](const report::Report &rr, const std::string &fn) {
      for (auto &x : rr.entries) if (x.function == fn) return std::string(report::verdictName(x.verdict));
      return std::string("missing");
    };
    auto confirmed = [](const report::Report &rr, const std::string &fn, const std::string &kind) {
      for (auto &x : rr.entries)
        if (x.function == fn)
          for (auto &f : x.findings)
            if (f.kind == kind && !f.warning) return true;
      return false;
    };

    report::Report rq;
    std::string qjs = scan("--qnx --link --entries iface", rq);
    // the handlers are registered by ASSIGNMENT (`io_funcs.devctl = f;`), which is how this tree writes them --
    // not as a designated initialiser. Finding all three proves that form is picked up.
    CHECK(rq.entries.size() == 3, "all three resmgr_io_funcs slots were selected: " << rq.entries.size());
    // the extent is a WIDENING, so it has to be named the same way every narrowing is (DESIGN.md §22.361/§22.365)
    bool saysExtent = false;
    for (auto &x : rq.entries)
      for (auto &a : x.assumptions)
        saysExtent |= a.category == "interface_contract" && has(a.text, "2048") && has(a.text, "16 bytes its declared type");
    CHECK(saysExtent, "the report names the receive-buffer extent it gave 'msg': " << qjs.substr(0, 800));
    // a handler that only reads a fixed-size payload struct has no defect, and must not be given one
    CHECK(verdictOf(rq, "demo_devctl_ok") == "safe_under_assumptions",
          "a fixed-size payload read is clean: " << verdictOf(rq, "demo_devctl_ok"));
    // ... while an unbounded index into that payload is a real out-of-bounds read: widening must not HIDE defects
    CHECK(verdictOf(rq, "demo_devctl_oob") == "bug", "an unbounded payload index is still a bug: " << verdictOf(rq, "demo_devctl_oob"));
    CHECK(confirmed(rq, "demo_devctl_oob", "oob_read"), "and it is a confirmed oob_read: " << qjs.substr(0, 800));
    // ... and a handler that verifies its request first is clean, because devctl_verify_len() ties `nbytes`
    // to the length encoded in `dcmd` (models/qnx.core) instead of leaving it an unconstrained 32-bit value
    CHECK(verdictOf(rq, "demo_devctl_verify") == "safe_under_assumptions",
          "a verified request length is not an unbounded loop: " << verdictOf(rq, "demo_devctl_verify"));

    // control A -- the contract is what stops the structural artefact. Generic synthesis sizes `msg` by its
    // declared 16-byte type, so the handler with NO defect is reported as a confirmed out-of-bounds read.
    report::Report ra;
    scan("--qnx --link --entries all --only demo_devctl_.*", ra);
    CHECK(verdictOf(ra, "demo_devctl_ok") == "bug",
          "without the contract the clean handler is a false positive (that is the point): " << verdictOf(ra, "demo_devctl_ok"));

    // control B -- the core model is what stops a VACUOUS safe. With iofunc_devctl_default() opaque its return is
    // unconstrained, the handler takes its `!= _RESMGR_DEFAULT` early return, and the real defect is never reached.
    report::Report rb;
    scan("--link --entries iface", rb);
    CHECK(verdictOf(rb, "demo_devctl_oob") == "safe_under_assumptions",
          "without models/qnx.core the real defect is silently missed: " << verdictOf(rb, "demo_devctl_oob"));
  }

  // ---------------------------------------------------------------- getters, used fields, fair field budget
  if (mine()) {
    const std::string gf = HLIR_SCAN_FIXTURE_DIR "/getter_driver.c";
    frontend::LowerOptions go;
    go.partial = true;
    auto r = frontend::lowerC(slurp(gf), gf, go);
    CHECK(r.ok, "getter_driver lowers: " << r.diagnostics);
    const frontend::FunctionInfo *oe = nullptr, *ub = nullptr;
    for (auto &f : r.functions) { if (f.name == "on_event") oe = &f; if (f.name == "use_big") ub = &f; }
    // c -> dev (embedded, no pointer) -> driver_data : revealed as struct my_dev by `struct my_dev *d = client_get_data(c)`
    CHECK(oe && oe->params[0].ptrFields->size() == 1 && (*oe->params[0].ptrFields)[0].kind == "struct" && (*oe->params[0].ptrFields)[0].structName == "my_dev" && (*oe->params[0].ptrFields)[0].offset == 8,
          "driver_data is typed through two getters: " << (oe && !oe->params[0].ptrFields->empty() ? (*oe->params[0].ptrFields)[0].structName : "none"));
    CHECK(ub && ub->params[0].ptrFields->size() == 1 && (*ub->params[0].ptrFields)[0].offset == 8, "only the pointer field the code uses is initialised (unused is skipped)");
    std::string out = run(bin + " --format json " + gf, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "getter scan json: " << er);
    for (auto &e : rp.entries)
      if (e.function == "on_event" || e.function == "use_big") CHECK(e.verdict == report::Verdict::SafeUnderAssumptions, e.function << " is safe with the recovered private data: " << report::verdictName(e.verdict));
    // budget: a huge subtree under the first field must not starve the second field of the same object
    frontend::FunctionInfo fn;
    fn.name = "f";
    frontend::ParamInfo p;
    p.name = "x"; p.kind = "ptr"; p.pointee = "struct"; p.structName = "S"; p.pointeeSize = 32; p.structHasPointers = true;
    frontend::PtrFieldInfo first, second;
    first.offset = 0; first.kind = "struct"; first.structName = "Big"; first.pointeeSize = 64;
    for (unsigned i = 0; i < 300; ++i) { frontend::PtrFieldInfo c; c.offset = 8 * i; c.kind = "bytes"; c.pointeeSize = 1; first.children.push_back(c); }
    second.offset = 8; second.kind = "bytes"; second.pointeeSize = 1;
    p.ptrFields = std::make_shared<std::vector<frontend::PtrFieldInfo>>(std::vector<frontend::PtrFieldInfo>{first, second});
    fn.params.push_back(p);
    scan::Options bo;
    bo.maxFields = 20;
    auto be = scan::makeEntry(fn, bo, {});
    CHECK(has(be.specText, "{ offset: 8, kind: buffer, taint: pointee, size: { min: 1, max: 256 } }") , "the shallow second field is initialised although the first field's subtree is huge:\n" << be.specText.substr(0, 400));
    CHECK(has(be.specText, "offset: 0, kind: buffer"), "the first field is there too");
  }

  // ---------------------------------------------------------------- opaque handles and user data (wl_resource_get_user_data)
  if (mine()) {
    const std::string uf = HLIR_SCAN_FIXTURE_DIR "/userdata_driver.c";
    frontend::LowerOptions uo;
    uo.partial = true;
    uo.userDataGetters = {"wl_resource_get_user_data"};
    auto r = frontend::lowerC(slurp(uf), uf, uo);
    CHECK(r.ok, "userdata_driver lowers: " << r.diagnostics);
    const frontend::FunctionInfo *ap = nullptr;
    for (auto &f : r.functions) if (f.name == "add_plane") ap = &f;
    CHECK(ap && ap->params.size() == 5, "add_plane has 5 parameters");
    if (ap && ap->params.size() == 5) {
      CHECK(ap->params[0].opaqueHandle && ap->params[1].opaqueHandle, "incomplete struct pointers (wl_client, wl_resource) are opaque handles");
      CHECK(ap->params[1].udStruct == "planes" && ap->params[1].udSize == 48, "the user data of `res` is a struct planes of 48 bytes: " << ap->params[1].udStruct << " " << ap->params[1].udSize);
      CHECK(ap->params[0].udStruct.empty(), "`client` is never passed to the getter");
      scan::Options so;
      auto e = scan::makeEntry(*ap, so, r.functions);
      CHECK(has(e.specText, "client: { taint: none"), "an opaque handle is context, not tainted:\n" << e.specText);
      CHECK(has(e.specText, "res: { taint: none, kind: buffer, size: { min: 64, max: 64 }, fields: [ { offset: 0, kind: buffer, taint: pointee, size: { min: 48, max: 48 }"), "the handle holds a pointer to a struct planes:\n" << e.specText);
      so.userDataZero = true;
      auto z = scan::makeEntry(*ap, so, r.functions);
      CHECK(has(z.specText, "{ offset: 0, kind: buffer, taint: none, size: { min: 48"), "--user-data-zero: the state is not tainted");
    }
    const frontend::FunctionInfo *ao = nullptr;
    for (auto &f : r.functions) if (f.name == "add_outer") ao = &f;
    CHECK(ao && ao->params.size() == 3 && ao->params[1].udStruct == "planes", "the user data type propagates to a caller that only passes the handle down");
    const frontend::FunctionInfo *fp = nullptr;
    for (auto &f : r.functions) if (f.name == "free_plane") fp = &f;
    CHECK(fp && fp->params.size() == 3 && fp->params[1].udOwned, "a user data struct the code frees is an owned heap object");
    if (fp && fp->params.size() == 3) {
      scan::Options fo;
      auto fe = scan::makeEntry(*fp, fo, r.functions);
      CHECK(has(fe.specText, "size: { min: 48, max: 48 }, owned: true"), "the spec marks the user data owned:\n" << fe.specText);
    }
    std::string out = run(bin + " --wayland --user-data-zero --entries all --format json " + uf, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "userdata scan json: " << er);
    for (auto &e : rp.entries) {
      bool oobw = false;
      // field_oob (DESIGN.md P1 gap fix) now fires first for this case: `idx` only needs to exceed the `fd[4]`
      // field's own declared length, a condition the solver reaches before the coarser whole-object oob_write
      // bound -- still an unchecked-attacker-index bug, just classified more precisely than before.
      for (auto &f : e.findings) oobw |= f.kind == "oob_write" || f.kind == "field_oob";
      if (e.function == "bug_plane") CHECK(oobw, "bug_plane: unchecked attacker index into the user data array is an oob_write/field_oob");
      if (e.function == "free_plane") CHECK(e.findings.empty(), "free_plane: freeing the owned user data is not an invalid_free (" << e.findings.size() << " findings)");
      if (e.function == "add_plane") CHECK(e.verdict == report::Verdict::SafeUnderAssumptions, "add_plane (checked) is safe: " << report::verdictName(e.verdict));
    }
  }

  // ---------------------------------------------------------------- empty intrusive lists
  if (mine()) {
    const std::string lf = HLIR_SCAN_FIXTURE_DIR "/list_driver.c";
    frontend::LowerOptions lo2;
    lo2.partial = true;
    auto r = frontend::lowerC(slurp(lf), lf, lo2);
    CHECK(r.ok, "list_driver lowers: " << r.diagnostics);
    const frontend::FunctionInfo *df = nullptr, *nu = nullptr;
    for (auto &f : r.functions) { if (f.name == "dev_first") df = &f; if (f.name == "node_unlink") nu = &f; }
    CHECK(df && df->params[0].ptrFields->size() == 2, "struct dev has the two links of its embedded list head: " << (df ? df->params[0].ptrFields->size() : 0));
    if (df && df->params[0].ptrFields->size() == 2) {
      auto &fl = *df->params[0].ptrFields;
      CHECK(fl[0].kind == "self" && fl[0].offset == 8 && fl[0].selfTarget == 8, "next at +8 points at the head at +8");
      CHECK(fl[1].kind == "self" && fl[1].offset == 16 && fl[1].selfTarget == 8, "prev at +16 points at the head at +8");
    }
    CHECK(nu && nu->params[0].ptrFields->size() == 2 && (*nu->params[0].ptrFields)[0].selfTarget == 0, "a list-head parameter points at itself (target 0)");
    scan::Options so;
    auto es = scan::discover(r.functions, so);
    CHECK(find(es, "dev_first") && has(find(es, "dev_first")->specText, "kind: self, target: 8"), "self links in the generated spec:\n" << (find(es, "dev_first") ? find(es, "dev_first")->specText : ""));
    bool noted = false;
    for (auto &n : find(es, "dev_first")->notes) noted |= has(n, "point back at their own list head");
    CHECK(noted, "the empty-list assumption is explained in the notes");
    std::string out = run(bin + " --format json " + lf, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "list scan json: " << er);
    auto vv = [&](const report::Report &x, const std::string &fn) {
      for (auto &e : x.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(vv(rp, "dev_first") == "safe_under_assumptions", "dev_first on an empty list: " << vv(rp, "dev_first"));
    CHECK(vv(rp, "dev_count") == "safe_under_assumptions", "dev_count on an empty list: " << vv(rp, "dev_count"));
    CHECK(vv(rp, "node_unlink") == "safe_under_assumptions", "node_unlink of a self-linked node: " << vv(rp, "node_unlink"));
    std::string out2 = run(bin + " --no-ptr-fields --format json " + lf, &rc);
    report::Report rp2;
    CHECK(report::fromJson(out2.substr(out2.find('{')), rp2, er), "list scan json (no ptr fields)");
    CHECK(vv(rp2, "dev_first") == "bug" && vv(rp2, "node_unlink") == "bug", "with NULL links the same functions dereference NULL: " << vv(rp2, "dev_first") << " " << vv(rp2, "node_unlink"));
  }

  // ---------------------------------------------------------------- recover mode: an incomplete build environment
  if (mine()) {
    const std::string rf = HLIR_SCAN_FIXTURE_DIR "/../recover/recover.c";
    frontend::LowerOptions ro;
    ro.recover = true;
    ro.inferStructs = false;  // this fixture checks what happens to functions that cannot be recovered
    ro.clangArgs = {"-I" HLIR_SCAN_FIXTURE_DIR "/../recover/inc"};
    auto r = frontend::lowerC(slurp(rf), rf, ro);
    CHECK(r.ok, "recover mode lowers the incomplete file: " << r.diagnostics);
    auto hasStr = [](const std::vector<std::string> &v, const std::string &x) { for (auto &y : v) if (y == x) return true; return false; };
    CHECK(hasStr(r.missingHeaders, "vendor/platform.h") && hasStr(r.missingHeaders, "missing_local.h"), "missing headers are reported, got " << r.missingHeaders.size());
    CHECK(hasStr(r.assumedTypes, "u32") && hasStr(r.assumedTypes, "dev_handle_t"), "unknown types get stub typedefs, got " << r.assumedTypes.size());
    auto fi = [&](const std::string &n) -> const frontend::FunctionInfo * { for (auto &f : r.functions) if (f.name == n) return &f; return nullptr; };
    CHECK(fi("copy_clamped") && fi("copy_clamped")->lowered, "copy_clamped is lowered (implicit decl + header inline + stub type)");
    CHECK(fi("copy_unclamped") && fi("copy_unclamped")->lowered, "copy_unclamped is lowered");
    CHECK(fi("items_ok") && !fi("items_ok")->lowered && has(fi("items_ok")->skipReason, "MAX_ITEMS"), "undeclared macro => skipped with the reason: " << (fi("items_ok") ? fi("items_ok")->skipReason : "?"));
    CHECK(fi("ctx_flags") && !fi("ctx_flags")->lowered && has(fi("ctx_flags")->skipReason, "incomplete"), "incomplete struct => skipped: " << (fi("ctx_flags") ? fi("ctx_flags")->skipReason : "?"));
    CHECK(fi("sum32") && fi("sum32")->lowered, "sum32 (u32 params) is lowered");
    CHECK(fi("v_ret") && fi("v_ret")->lowered, "return f(); in a void function is lowered");
    CHECK(fi("sum32") && fi("sum32")->params.size() == 2 && fi("sum32")->params[0].bits == 32 && !fi("sum32")->params[0].isSigned, "u32 stub is a 32-bit unsigned integer");
    // the header inline really executes: sat_add_u32(0xffffffff, 1) saturates
    Diagnostics d;
    auto mod = parseModule(r.core, "recover.core", d);
    CHECK(mod != nullptr, "recovered core parses: " << d.str());
    if (mod) {
      Diagnostics d2;
      VerifyOptions vo;
      vo.checkCoverage = true;
      CHECK(verifyModule(*mod, vo, d2), "recovered core passes the UB-check coverage verifier: " << d2.str());
      RunConfig cfg;
      TableEnv env;
      auto run = [&](const char *f, std::vector<uint64_t> a) {
        std::vector<llvm::APInt> args;
        for (auto v : a) args.emplace_back(32, v);
        return Interpreter(*mod).run(f, args, env, cfg);
      };
      auto res = run("sum32", {0xffffffffu, 1});
      CHECK(res.status == RunStatus::Returned && res.returnValue && res.returnValue->getZExtValue() == 0xffffffffu, "sat_add_u32 from the header saturates");
      res = run("sum32", {5, 6});
      CHECK(res.status == RunStatus::Returned && res.returnValue && res.returnValue->getZExtValue() == 11, "sat_add_u32 adds");
    }
    // structs without a definition: layouts inferred from the member accesses
    {
      const std::string sf = HLIR_SCAN_FIXTURE_DIR "/../recover/structs.c";
      frontend::LowerOptions so2;
      so2.recover = true;
      auto sr = frontend::lowerC(slurp(sf), sf, so2);
      CHECK(sr.ok, "structs.c lowers in recover mode: " << sr.diagnostics);
      auto sfi = [&](const std::string &n) -> const frontend::FunctionInfo * { for (auto &f : sr.functions) if (f.name == n) return &f; return nullptr; };
      for (const char *n : {"get_pid", "copy_req", "nested", "classify"})
        CHECK(sfi(n) && sfi(n)->lowered, n << " is lowered: " << (sfi(n) ? sfi(n)->skipReason : "missing"));
      auto inferred = [&](const std::string &needle) { for (auto &t : sr.inferredStructs) if (has(t, needle)) return true; return false; };
      CHECK(inferred("struct ctx {") && inferred("struct dev * dev;"), "ctx.dev is a pointer to struct dev (from the typed variable)");
      CHECK(inferred("struct req {") && inferred("int pid;"), "req.pid is int (from the assigned call result)");
      CHECK(inferred("unsigned long size;"), "req.size is unsigned long (the widest of unsigned int and size_t)");
      CHECK(inferred("void * data;") || inferred("const void * data;"), "req.data is a void pointer (from memcpy's prototype)");
      CHECK(inferred("struct __hlir_stub_ctx__cfg cfg;") && inferred("struct __hlir_stub_ctx__opts * opts;"), "c->cfg.x is a struct, c->opts->y a pointer to one");
      CHECK(inferred("enum { CMD_START }") && inferred("enum { CMD_STOP }"), "unknown constants are listed");
      // the end-to-end result: the real bug (unbounded-by-8 copy into local[8]) is found on the inferred layout
      std::string so = run(bin + " --format json -I" HLIR_SCAN_FIXTURE_DIR "/../recover/inc " + sf, &rc);
      report::Report r5;
      std::string e5;
      CHECK(report::fromJson(so.substr(so.find('{')), r5, e5), "structs scan json: " << e5);
      auto v5 = [&](const std::string &fn) { for (auto &e : r5.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict)); return std::string("missing"); };
      CHECK(v5("copy_req") == "bug", "copy_req on the inferred layout: " << v5("copy_req"));
      CHECK(v5("classify") == "safe_under_assumptions" && v5("get_pid") == "safe_under_assumptions", "classify / get_pid: " << v5("classify") << " " << v5("get_pid"));
      std::string off = run(bin + " --no-infer-structs --format json " + sf, &rc);
      CHECK(has(off, "not lowered") || off.find("\"entries\": []") != std::string::npos || !has(off, "\"function\": \"copy_req\""), "--no-infer-structs: functions using the structs are skipped");
    }

    // without recovery the same file is rejected with Clang's own errors
    auto strict = frontend::lowerC(slurp(rf), rf, {});
    CHECK(!strict.ok, "strict mode refuses a file that does not compile");

    // end to end through hlir-scan: the bug is found, the clamped variant is safe, skipped functions are explained
    std::string out = run(bin + " --no-infer-structs --format json -I" HLIR_SCAN_FIXTURE_DIR "/../recover/inc " + rf, &rc);
    report::Report rep2;
    std::string err2;
    CHECK(report::fromJson(out.substr(out.find('{')), rep2, err2), "recover scan json: " << err2);
    auto verdict2 = [&](const std::string &fn) {
      for (auto &e : rep2.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(verdict2("copy_unclamped") == "bug", "copy_unclamped: " << verdict2("copy_unclamped"));
    CHECK(verdict2("copy_clamped") == "safe_under_assumptions", "copy_clamped: " << verdict2("copy_clamped"));
    CHECK(verdict2("items_ok") == "missing" && verdict2("ctx_flags") == "missing", "functions that could not be lowered are not analysed");
    bool opaqueListed = false;
    for (auto &e : rep2.entries)
      if (e.function == "copy_unclamped")
        for (auto &a : e.assumptions) opaqueListed |= a.category == "model" && has(a.text, "vendor_log");
    CHECK(opaqueListed, "the opaque-function assumption names vendor_log");
    std::string strictExt = run(bin + " --strict-externs --entry copy_unclamped --format json -I" HLIR_SCAN_FIXTURE_DIR "/../recover/inc " + rf, &rc);
    CHECK(has(strictExt, "no model for it"), "--strict-externs stops at an unmodelled call:\n" << strictExt.substr(0, 400));
    std::string strictScan = run(bin + " --strict " + rf, &rc);
    CHECK(rc == 2, "--strict: an incomplete file is an input error, exit " << rc);
  }


  // ---------------------------------------------------------------- linking units (hlir::link) and hlir-scan --link
  if (mine()) {
    link::Unit a, b;
    a.name = "a.c"; b.name = "b.c";
    a.internalTokens = {"bump", "counter", "counter.__init", "__hlir_init.counter"};
    b.internalTokens = {"bump", "counter", "counter.__init", "__hlir_init.counter"};
    a.core = "core.declare @helper(i32) -> i32\ncore.declare @__hlir_init.shared() -> void\n"
             "core.func @bump(i32) -> i32 {\n^entry(%x: i32):\n  %g = core.global_addr @counter {size=4} : ptr\n  core.return %x\n}\n"
             "core.func @api(i32) -> i32 {\n^entry(%x: i32):\n  %r = core.call @bump(%x) : i32\n  %h = core.call @helper(%r) : i32\n  core.call @__hlir_init.shared()\n"
             "  %t = core.global_addr @tab {size=1} : ptr\n  core.return %h\n}\n";
    b.core = "core.func @bump(i32) -> i32 {\n^entry(%x: i32):\n  %g = core.global_addr @counter {size=4} : ptr\n  core.return %x\n}\n"
             "core.func @helper(i32) -> i32 {\n^entry(%x: i32):\n  %r = core.call @bump(%x) : i32\n  %t = core.global_addr @tab {size=16, const} : ptr\n  core.return %r\n}\n"
             "core.func @api(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n";
    auto lr = link::linkUnits({a, b});
    CHECK(link::linkedName(lr, 0, "bump") == "bump.u0" && link::linkedName(lr, 1, "bump") == "bump.u1", "same-named statics are renamed apart: " << link::linkedName(lr, 0, "bump") << " " << link::linkedName(lr, 1, "bump"));
    CHECK(link::linkedName(lr, 0, "api") == "api", "external names are kept");
    CHECK(has(lr.core, "core.func @bump.u0(") && has(lr.core, "core.func @bump.u1(") && has(lr.core, "core.call @bump.u1(") , "calls follow the renaming");
    CHECK(!has(lr.core, "core.declare @helper"), "a declaration of a function another unit defines is dropped");
    CHECK(has(lr.core, "core.func @__hlir_init.shared() -> void {"), "an init function nobody defines gets an empty stub");
    CHECK(has(lr.core, "@tab {size=16, const}") && !has(lr.core, "@tab {size=1}"), "a global gets the largest size and constness any unit gives it");
    CHECK(has(lr.core, "@counter.u0 {size=4}") && has(lr.core, "@counter.u1 {size=4}"), "static globals are renamed too");
    bool dup = false;
    for (auto &n : lr.notes) dup |= has(n, "'api' is defined more than once");
    CHECK(dup, "a second definition of an external function is ignored with a note");
    {  // --expose: a harness in one file calling a `static` of another (CVE-2025-24928's xmlSnprintfElements shape).
       // Without it the harness's own declaration is what MAKES the name clash, so the static is renamed and the call
       // binds to nothing -- the target is never analysed and the report shows an ordinary opaque external.
      link::Unit h, t;
      h.name = "harness.c"; t.name = "target.c";
      h.core = "core.declare @only_static(i32) -> i32\ncore.func @hx(i32) -> i32 {\n^entry(%x: i32):\n  %r = core.call @only_static(%x) : i32\n  core.return %r\n}\n";
      t.core = "core.func @only_static(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n";
      t.internalTokens = {"only_static"};
      auto plain = link::linkUnits({h, t});
      CHECK(has(plain.core, "core.func @only_static.u1(") && has(plain.core, "core.call @only_static(") && plain.exposeApplied.empty(),
            "without --expose the static is renamed apart and the harness's call is left unresolved");
      auto exposed = link::linkUnits({h, t}, {}, {"only_static"});
      CHECK(has(exposed.core, "core.func @only_static(") && !has(exposed.core, "only_static.u1") &&
                exposed.exposeApplied.size() == 1 && exposed.exposeApplied[0] == "only_static",
            "--expose keeps the name so the harness binds to the real body:\n" << exposed.core);
      // Two files with a static of that name are two distinct entities: there is nothing to pick, and picking one
      // silently would make the scan analyse a function the user did not name.
      link::Unit t2;
      t2.name = "other.c";
      t2.core = "core.func @only_static(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n";
      t2.internalTokens = {"only_static"};
      auto amb = link::linkUnits({h, t, t2}, {}, {"only_static"});
      CHECK(amb.exposeApplied.empty() && !amb.exposeAmbiguous.empty() && has(amb.core, "only_static.u1"),
            "--expose on a name two files declare static is refused, not guessed");
    }
    {  // program-wide indirect calls: the dispatcher reaches the functions of every unit with the signature
      link::Unit x, y;
      x.name = "x.c"; y.name = "y.c";
      x.core = "core.declare @__hlir_indirect._i32_____i32(ptr, i32) -> i32\ncore.func @call(ptr, i32) -> i32 {\n^entry(%f: ptr, %a: i32):\n  %r = core.call @__hlir_indirect._i32_____i32(%f, %a) : i32\n  core.return %r\n}\n"
               "core.func @own(i32) -> i32 {\n^entry(%a: i32):\n  core.return %a\n}\n";
      x.addrTaken = {{"own", "(i32) -> i32"}, {"other_sig", "(i32, i32) -> i32"}};
      y.core = "core.func @theirs(i32) -> i32 {\n^entry(%a: i32):\n  core.return %a\n}\n";
      y.addrTaken = {{"theirs", "(i32) -> i32"}};
      auto lr3 = link::linkUnits({x, y});
      auto it = lr3.dispatchers.find("__hlir_indirect._i32_____i32");
      CHECK(it != lr3.dispatchers.end() && it->second.size() == 2 && it->second[0] == "own" && it->second[1] == "theirs", "the dispatcher reaches own() and theirs() but not the function of another signature");
      CHECK(has(lr3.core, "core.func @__hlir_indirect._i32_____i32(ptr, i32) -> i32 {") && has(lr3.core, "core.declare @__hlir_unknown_indirect._i32_____i32(i32) -> i32") && has(lr3.core, "core.call @theirs(%a1)"), "the dispatcher is generated, with an opaque fallback for unknown targets:\n" << lr3.core);
      CHECK(!has(lr3.core, "core.declare @__hlir_indirect"), "the dispatcher replaces the declaration");
    }
    {  // a call through a pointer of a known C type (`.t<hash>` suffix, key in indirectCallCTypes) reaches only candidates whose
       // key is compatible -- a different struct at some position rules one out, `void *`/integers (`_`) match anything --
       // plus those whose address escaped to an incompatible type (no addrTakenCTypes entry); an untagged call reaches all
      std::string typed = "__hlir_indirect._ptr_____i32" + link::indirectTypeTag("_(*s:net)");
      std::string generic = "__hlir_indirect._ptr_____i32" + link::indirectTypeTag("_(_)");
      link::Unit x, y;
      x.name = "x.c"; y.name = "y.c";
      x.core = "core.declare @" + typed + "(ptr, ptr) -> i32\ncore.declare @" + generic + "(ptr, ptr) -> i32\n"
               "core.declare @__hlir_indirect._ptr_____i32(ptr, ptr) -> i32\n"
               "core.func @own(ptr) -> i32 {\n^entry(%a: ptr):\n  %z = core.const 0 : i32\n  core.return %z\n}\n"
               "core.func @other(ptr) -> i32 {\n^entry(%a: ptr):\n  %z = core.const 0 : i32\n  core.return %z\n}\n"
               "core.func @gen(ptr) -> i32 {\n^entry(%a: ptr):\n  %z = core.const 0 : i32\n  core.return %z\n}\n";
      x.addrTaken = {{"own", "(ptr) -> i32"}, {"other", "(ptr) -> i32"}, {"gen", "(ptr) -> i32"}};
      x.addrTakenCTypes = {{"own", "_(*s:net)"}, {"other", "_(*s:socket)"}, {"gen", "_(_)"}};
      x.indirectCallCTypes = {{typed, "_(*s:net)"}, {generic, "_(_)"}};
      y.core = "core.func @cast(ptr) -> i32 {\n^entry(%a: ptr):\n  %z = core.const 0 : i32\n  core.return %z\n}\n";
      y.addrTaken = {{"cast", "(ptr) -> i32"}};
      auto lr4 = link::linkUnits({x, y});
      auto t = lr4.dispatchers.find(typed), g = lr4.dispatchers.find(generic), u = lr4.dispatchers.find("__hlir_indirect._ptr_____i32");
      CHECK(t != lr4.dispatchers.end() && t->second == std::vector<std::string>({"own", "gen", "cast"}),
            "a struct net * call reaches own() (struct net *), gen() (void *) and cast() (escaped), not other() (struct socket *): "
                << (t == lr4.dispatchers.end() ? std::string("missing") : std::to_string(t->second.size())));
      CHECK(g != lr4.dispatchers.end() && g->second.size() == 4, "a call through a void * pointer type reaches all four (libffi, vtables read as another type)");
      CHECK(u != lr4.dispatchers.end() && u->second.size() == 4, "the untagged dispatcher reaches all four");
      CHECK(!hlir::cTypesCompatible("_(*s:net,_)", "_(*s:socket,_)") && hlir::cTypesCompatible("_(_,_)", "_(*s:socket,_)") &&
                !hlir::cTypesCompatible("_(**s:a)", "_(*s:a)") && hlir::cTypesCompatible("", "_(*s:a)"),
            "cTypesCompatible: only differing named structs/depths are incompatible");
    }
    link::Unit c = a;  // an external `bump` in one unit and a static one in another: the static one is renamed
    c.internalTokens.clear();
    auto lr2 = link::linkUnits({c, b});
    CHECK(link::linkedName(lr2, 1, "bump") == "bump.u1", "a static function is renamed when another unit refers to an external one of the same name");

    {  // a unit's own internal symbol colliding with a ModelDB-defined name (e.g. a kernel header's real `static inline
       // isdigit` fallback body vs. libc.core's generic `@isdigit` model) is renamed apart, not left to clash at parse time
      link::Unit d;
      d.name = "d.c";
      d.internalTokens = {"isdigit"};
      d.core = "core.func @isdigit(i32) -> i32 {\n^entry(%c: i32):\n  %z = core.const 0 : i32\n  core.return %z\n}\n";
      CHECK(link::definedFunctionNames("core.declare @foo(i32) -> i32\ncore.func @isdigit(i32) -> i32 {\n^entry(%c: i32):\n  core.return %c\n}\n") == std::set<std::string>{"isdigit"}, "definedFunctionNames finds func bodies, not bare declares");
      auto lr4 = link::linkUnits({d}, {"isdigit"});
      CHECK(link::linkedName(lr4, 0, "isdigit") == "isdigit.u0", "an internal symbol colliding with a ModelDB-defined name is renamed apart");
      auto lr5 = link::linkUnits({d});  // no modelDefs: no collision to avoid, kept as-is
      CHECK(link::linkedName(lr5, 0, "isdigit") == "isdigit", "without modelDefs, a lone internal symbol is not renamed");
    }

    const std::string ldir = HLIR_SCAN_FIXTURE_DIR "/../link";
    std::string out = run(bin + " --link --format json " + ldir + "/main.c " + ldir + "/lib.c " + ldir + "/handlers.c", &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "link scan json: " << er);
    std::map<std::string, std::string> v;
    for (auto &e : rp.entries) v[e.function] = report::verdictName(e.verdict);
    CHECK(v.count("check_init") && v["check_init"] == "safe_under_assumptions", "cross-file initialisers and per-file statics are right (check_init): " << v["check_init"]);
    CHECK(v["checked_lookup"] == "safe_under_assumptions", "the bound comes from get_limit() in the other file: " << v["checked_lookup"]);
    CHECK(v["unchecked_lookup"] == "bug", "table[] has the size of its definition in lib.c (an out-of-bounds index is found): " << v["unchecked_lookup"]);
    CHECK(v["cmp_chain"] == "safe_under_assumptions", "by-value struct arguments in else-if conditions / && operands lower and verify: " << v["cmp_chain"]);
    CHECK(v["use_tbl"] == "safe_under_assumptions", "static functions reachable only through a global initialiser are lowered: " << v["use_tbl"]);
    bool dispOob = false;
    for (auto &e : rp.entries)
      if (e.function == "dispatch") for (auto &f : e.findings) dispOob |= f.kind == "oob_write";
    {
      size_t depth = 0;
      unsigned runDepth = 0;
      std::string last;
      for (auto &e : rp.entries)
        if (e.function == "dispatch") {
          runDepth = e.metrics.maxCallDepth;
          for (auto &f : e.findings) if (f.kind == "oob_write" && f.callStack.size() > depth) { depth = f.callStack.size(); last = f.callStack.back(); }
        }
      CHECK(depth == 3 && last == "handler_bug", "the finding records its call chain (entry -> dispatcher -> handler): depth " << depth << " ends in " << last);
      CHECK(runDepth >= 3, "metrics.max_call_depth is the deepest stack of the runs: " << runDepth);
      std::string txt = run(bin + " --link " + ldir + "/main.c " + ldir + "/lib.c " + ldir + "/handlers.c", &rc);
      CHECK(has(txt, "call chain (depth 3): dispatch -> __hlir_indirect") && has(txt, "call depth of findings"), "the text report prints the chain and the depth distribution");
    }
    CHECK(dispOob, "dispatch calls through a table of another file: the bug in handler_bug is reachable (program-wide indirect call resolution)");
    CHECK(v["on_big"] == "bug" && v.count("handler_bug"), "handlers only referenced from another file's table are callbacks (entries): on_big " << v["on_big"]);
    CHECK(!v.count("helper") && !v.count("get_limit"), "functions another file calls are not roots");
    std::string solo = run(bin + " --format json " + ldir + "/main.c", &rc);
    report::Report sp;
    CHECK(report::fromJson(solo.substr(solo.find('{')), sp, er), "solo scan json: " << er);
    bool soloLookup = false;
    for (auto &e : sp.entries) if (e.function == "checked_lookup") soloLookup = e.verdict == report::Verdict::SafeUnderAssumptions;
    CHECK(sp.entries.size() == 6 && soloLookup, "without --link the file is analysed on its own (get_limit is an opaque call): " << sp.entries.size());
    std::string dump = HLIR_SCAN_FIXTURE_DIR "/../link/.linked.core";
    std::string lst = run(bin + " --link --list --dump-linked " + dump + " " + ldir + "/main.c " + ldir + "/lib.c", &rc);
    std::ifstream df(dump);
    std::stringstream dss;
    dss << df.rdbuf();
    CHECK(has(dss.str(), "core.func @__hlir_init.table()") && has(dss.str(), "@table {size=16}"), "--dump-linked writes the linked module");
    std::remove(dump.c_str());
  }

  // ---------------------------------------------------------------- the indirect dispatcher's candidate order
  // (DESIGN.md §22.443). It used to be the order clang allocated the AST nodes, so it MOVED WITH ASLR: two runs of
  // the same command linked different programs and analysed them differently. Sorted is the order that can be
  // asserted; what matters is only that it is fixed and independent of the process.
  {
    const std::string dump = HLIR_SCAN_FIXTURE_DIR "/.indirect_order.core";
    run(bin + " --link --list --dump-linked " + dump + " " + HLIR_SCAN_FIXTURE_DIR "/indirect_order.c", &rc);
    std::string core = slurp(dump);
    std::remove(dump.c_str());
    // The candidates of the one dispatcher, in the order it tests them.
    std::vector<std::string> cands;
    size_t at = core.find("core.func @__hlir_indirect.");
    CHECK(at != std::string::npos, "the linked module has an indirect-call dispatcher");
    size_t end = core.find("\ncore.func @", at + 1);        // the dispatcher's body ends at the next function
    std::string body = core.substr(at, end == std::string::npos ? std::string::npos : end - at);
    const std::string mark = "= core.func_addr @";
    for (size_t p = body.find(mark); p != std::string::npos; p = body.find(mark, p + 1)) {
      size_t a = p + mark.size();
      cands.push_back(body.substr(a, body.find(' ', a) - a));
    }
    CHECK(cands.size() == 5, "all five address-taken functions are candidates: " << cands.size());
    std::vector<std::string> sorted = cands;
    std::sort(sorted.begin(), sorted.end());
    std::string got, want;
    for (auto &c : cands) got += " " + c;
    for (auto &c : sorted) want += " " + c;
    CHECK(cands == sorted,
          "the dispatcher's candidate order must not depend on the address space:" << got << "  (expected" << want << ")");
  }

  // ---------------------------------------------------------------- --link: dlsym("literal") resolves to the linked
  // function (DESIGN.md §22.424). The two entries differ only in how the symbol NAME is written, so the pair is a
  // controlled experiment: the literal one must reach the plugin's defect, the computed one must stay opaque.
  if (mine()) {
    const std::string dd = HLIR_SCAN_FIXTURE_DIR "/../link";
    std::string out = run(bin + " --link --format json --runs 2000 --buf-max 32 --entry dlsym_literal --entry dlsym_computed " +
                              dd + "/dlsym_host.c " + dd + "/dlsym_plugin.c", &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "dlsym link scan json: " << er);
    const report::EntryReport *lit = nullptr, *comp = nullptr;
    for (auto &e : rp.entries) {
      if (e.function == "dlsym_literal") lit = &e;
      if (e.function == "dlsym_computed") comp = &e;
    }
    CHECK(lit && comp, "both dlsym entries were analysed (" << rp.entries.size() << " found)");
    if (lit && comp) {
      bool oob = false, viaDispatcher = false;
      for (auto &f : lit->findings)
        if (!f.warning && f.kind == "oob_write" && f.replay == report::ReplayStatus::Confirmed) {
          oob = true;
          for (auto &c : f.callStack) viaDispatcher |= c.rfind("__hlir_indirect.", 0) == 0;
          CHECK(!f.callStack.empty() && f.callStack.back() == "plugin_parse",
                "...and the chain ends in the dlsym'd function: " << (f.callStack.empty() ? "" : f.callStack.back()));
        }
      CHECK(oob, "dlsym(h, \"plugin_parse\") resolves: the plugin's oob_write is reachable and replay-confirmed");
      // The address still travels as a VALUE through a function pointer -- resolution adds a candidate to the
      // dispatcher, it does not turn the call into a direct one. If this ever stops holding, the model of what
      // `dlsym` returns has quietly changed.
      CHECK(viaDispatcher, "...through the indirect-call dispatcher, as a function pointer and not a direct call");
      bool compOob = false;
      for (auto &f : comp->findings) compOob |= !f.warning && f.kind == "oob_write";
      CHECK(!compOob, "a COMPUTED dlsym name is not resolved: nothing is invented for `dlsym(h, nm)`");
    }
    // A name no unit defines must fall back to an opaque external under its own name, so it is reportable (and
    // reaches --model-todo) instead of silently resolving to something else.
    link::Unit hu, pu;
    hu.name = "h.c";
    hu.core = "core.declare @__hlir_dlsym.gone(ptr) -> ptr\n"
              "core.func @caller(ptr) -> ptr {\n^entry(%h: ptr):\n  %f = core.call @__hlir_dlsym.gone(%h) : ptr\n  core.return %f\n}\n";
    hu.dlsymNames = {"gone", "here"};
    pu.name = "p.c";
    pu.core = "core.declare @__hlir_dlsym.here(ptr) -> ptr\n"
              "core.func @here(i32) -> i32 {\n^entry(%x: i32):\n  core.return %x\n}\n"
              "core.func @user(ptr) -> ptr {\n^entry(%h: ptr):\n  %f = core.call @__hlir_dlsym.here(%h) : ptr\n  core.return %f\n}\n";
    pu.dlsymNames = {"here"};
    auto dl = link::linkUnits({hu, pu});
    CHECK(dl.dlsymResolved == std::vector<std::string>{"here"} && dl.dlsymUnresolved == std::vector<std::string>{"gone"},
          "the linker resolves the names some unit defines and reports the rest");
    CHECK(has(dl.core, "core.func @__hlir_dlsym.here(ptr) -> ptr {") && has(dl.core, "core.func_addr @here : ptr"),
          "the resolver returns the function's own address");
    CHECK(has(dl.core, "core.nondet {name=\"dlsym_fail.here\"}"),
          "...or NULL: a lookup that fails is real, reachable code and stays a branch the search can take");
    CHECK(has(dl.core, "core.declare @__hlir_dlsym.gone(ptr) -> ptr") && !has(dl.core, "core.func @__hlir_dlsym.gone"),
          "an unresolvable name stays an opaque external under its own name");
  }

  // ---------------------------------------------------------------- --link: whole-program used-fields (field read only
  // through a cross-unit call, the drm_to_adev()/driver_features DRM/amdgpu pattern)
  if (mine()) {
    const std::string ldir2 = HLIR_SCAN_FIXTURE_DIR "/../link";
    std::string outF = run(bin + " --link --format json " + ldir2 + "/field_use_entry.c " + ldir2 + "/field_use_body.c", &rc);
    report::Report rf;
    std::string erf;
    CHECK(report::fromJson(outF.substr(outF.find('{')), rf, erf), "field-use link scan json: " << erf);
    std::map<std::string, const report::EntryReport *> vf;
    for (auto &e : rf.entries) vf[e.function] = &e;
    CHECK(vf.count("entry_ok") && vf["entry_ok"]->verdict == report::Verdict::SafeUnderAssumptions,
          "entry_ok (bounded copy once `target` is a real object): " << (vf.count("entry_ok") ? report::verdictName(vf["entry_ok"]->verdict) : "missing"));
    bool falseNullDeref = false;
    for (auto &f : vf.count("entry_ok") ? vf["entry_ok"]->findings : std::vector<report::Finding>{}) falseNullDeref |= f.kind == "null_deref";
    CHECK(!falseNullDeref, "entry_ok: `target` is not left null (no false-positive null_deref from the field being wrongly pruned as unused)");
    CHECK(vf.count("entry_bug") && vf["entry_bug"]->verdict == report::Verdict::Bug,
          "entry_bug: the real OOB past `inner` is still found (no loss of detection power): " << (vf.count("entry_bug") ? report::verdictName(vf["entry_bug"]->verdict) : "missing"));
    bool realOob = false, maskedByNullDeref = false;
    for (auto &f : vf["entry_bug"]->findings) { realOob |= f.kind == "oob_read"; maskedByNullDeref |= f.kind == "null_deref"; }
    CHECK(realOob && !maskedByNullDeref, "entry_bug's finding is the real oob_read, not a null_deref on the previously-unmodelled `target`");
    for (auto &fn : {"entry_ok", "entry_bug"})
      CHECK(vf.count(fn) && vf[fn]->coverage.measured && vf[fn]->coverage.functionsEntered == 3 && vf[fn]->coverage.blocksVisited == vf[fn]->coverage.blocksReachable,
            fn << ": full coverage through the cross-file call into touch_ok/touch_bug (field_use_body.c)");
  }

  // ---------------------------------------------------------------- pointer arrays (`T **argv` + `argc`), goto past a declaration
  if (mine()) {
    const std::string pa = HLIR_SCAN_FIXTURE_DIR "/ptrarray_driver.c";
    frontend::LowerOptions po;
    po.partial = true;
    auto r = frontend::lowerC(slurp(pa), pa, po);
    CHECK(r.ok, "ptrarray_driver lowers: " << r.diagnostics);
    const frontend::FunctionInfo *gc = nullptr;
    for (auto &f : r.functions) if (f.name == "get_cmd") gc = &f;
    bool arr = false;
    if (gc && !gc->params.empty())
      for (auto &f : *gc->params[0].ptrFields) arr |= f.ptrArray && f.arraySlots == 3 && f.lenOffset == 4 && f.lenBits == 32 && f.children.size() == 3;
    CHECK(arr, "`obj **argv` is a pointer array of 3 slots and `argc` (offset 4) is its count");
    if (gc) {
      scan::Options so;
      auto e = scan::makeEntry(*gc, so, r.functions);
      CHECK(has(e.specText, "where: [ { offset: 4, type: int32_t, range: [1, 3] } ]"), "the count is bounded by the number of slots:\n" << e.specText);
    }
    // regression: the relations-DSL sibling-field-pair fix (`size: { from_field: ... } }`, DESIGN.md §22.105) only
    // ever fired on hand-written specs -- cmark/Duktape (§22.127/130) found `--entries all`'s automatic spec
    // synthesizer never emitted it. Frontend.cpp's findSiblingLenField() (shared with the ptrArray lenOffset
    // detection just above) now also runs on plain byte-buffer pointer fields (`data`/`datalen`-shaped), and
    // Scan.cpp's fieldsYaml() turns a hit into `size: { from_field: ... } }` instead of an independent range.
    {
      const std::string sf = HLIR_SCAN_FIXTURE_DIR "/sibling_size_field_auto.c";
      auto rs = frontend::lowerC(slurp(sf), sf, po);
      CHECK(rs.ok, "sibling_size_field_auto lowers: " << rs.diagnostics);
      const frontend::FunctionInfo *cn = nullptr;
      for (auto &f : rs.functions) if (f.name == "consume") cn = &f;
      bool linked = false;
      if (cn && !cn->params.empty())
        for (auto &f : *cn->params[0].ptrFields) linked |= f.kind == "bytes" && f.lenOffset == 8 && f.lenBits == 64;
      CHECK(linked, "`data`'s struct has a sibling `datalen` field (offset 8) found by findSiblingLenField");
      if (cn) {
        scan::Options so2;
        auto e2 = scan::makeEntry(*cn, so2, rs.functions);
        CHECK(has(e2.specText, "size: { from_field: { offset: 8, type: uint64_t } }"), "the auto-generated spec ties `data`'s size to `datalen`, not an independent range:\n" << e2.specText);
      }
      std::string sout = run(bin + " --entries all --format json " + sf, &rc);
      report::Report sr;
      std::string ser;
      CHECK(report::fromJson(sout.substr(sout.find('{')), sr, ser), "sibling_size_field_auto scan json: " << ser);
      CHECK(sr.entries.size() == 1 && sr.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
            "with the real sibling-field size, `el->data[el->datalen-1]` is in bounds (no spurious oob_read): "
            << (sr.entries.empty() ? "no entry" : report::verdictName(sr.entries[0].verdict)));
      std::string sbf = HLIR_SCAN_FIXTURE_DIR "/sibling_size_field_auto_bug.c";
      std::string sbout = run(bin + " --entries all --format json " + sbf, &rc);
      report::Report sbr;
      CHECK(report::fromJson(sbout.substr(sbout.find('{')), sbr, ser), "sibling_size_field_auto_bug scan json: " << ser);
      CHECK(sbr.entries.size() == 1 && sbr.entries[0].verdict == report::Verdict::Bug,
            "without the datalen==0 guard, the real underflow (datalen-1 wraps to SIZE_MAX) is still found: "
            << (sbr.entries.empty() ? "no entry" : report::verdictName(sbr.entries[0].verdict)));
    }
    // regression: findSiblingLenField()'s bare-generic-name fallback (Heartbleed/CVE-2014-0160 ground-truth
    // validation, DESIGN.md) -- a sibling length field whose name has NO textual relation to the buffer field
    // it describes (`struct record { unsigned int length; unsigned char *data; }`, the real-world shape is
    // OpenSSL's SSL3_RECORD) was never matched by the original name-composite candidate list (data -> datalen/
    // data_size/...). Only applies when the bare name is unique among the struct's own fields.
    {
      const std::string blf = HLIR_SCAN_FIXTURE_DIR "/bare_length_field.c";
      auto rb = frontend::lowerC(slurp(blf), blf, po);
      CHECK(rb.ok, "bare_length_field lowers: " << rb.diagnostics);
      const frontend::FunctionInfo *bcn = nullptr;
      for (auto &f : rb.functions) if (f.name == "consume") bcn = &f;
      if (bcn) {
        scan::Options so7;
        auto e7 = scan::makeEntry(*bcn, so7, rb.functions);
        CHECK(has(e7.specText, "from_field"), "the auto-generated spec ties `data`'s size to the bare `length` field:\n" << e7.specText);
      }
      std::string sbout2 = run(bin + " --entries all --format json " + blf, &rc);
      report::Report sbr2;
      std::string ser2;
      CHECK(report::fromJson(sbout2.substr(sbout2.find('{')), sbr2, ser2), "bare_length_field scan json: " << ser2);
      CHECK(sbr2.entries.size() == 1 && sbr2.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
            "with the real sibling-field size, `r->data[r->length-1]` is in bounds (no spurious oob_read): "
            << (sbr2.entries.empty() ? "no entry" : report::verdictName(sbr2.entries[0].verdict)));
      std::string bbf = HLIR_SCAN_FIXTURE_DIR "/bare_length_field_bug.c";
      std::string bbout = run(bin + " --entries all --format json " + bbf, &rc);
      report::Report bbr;
      CHECK(report::fromJson(bbout.substr(bbout.find('{')), bbr, ser2), "bare_length_field_bug scan json: " << ser2);
      CHECK(bbr.entries.size() == 1 && bbr.entries[0].verdict == report::Verdict::Bug,
            "the real off-by-one past length is still found: "
            << (bbr.entries.empty() ? "no entry" : report::verdictName(bbr.entries[0].verdict)));
    }
    // regression: findSiblingLenField()'s anonymous-union/struct recursion (collectFieldsForLenSearch,
    // Frontend.cpp) -- a length field packed inside an anonymous union/struct member (VFS's
    // `struct qstr { union { u64 hash_len; struct { u32 hash, len; }; }; }` shape) is invisible to
    // RecordDecl::fields() directly (only the anonymous union itself shows up, as one unnamed FieldDecl), so
    // without recursing into it `len` could never be found as a sibling-length candidate at all.
    {
      const std::string qf = HLIR_SCAN_FIXTURE_DIR "/qstr_anon_union_len.c";
      auto rq = frontend::lowerC(slurp(qf), qf, po);
      CHECK(rq.ok, "qstr_anon_union_len lowers: " << rq.diagnostics);
      const frontend::FunctionInfo *qcn = nullptr;
      for (auto &f : rq.functions) if (f.name == "consume") qcn = &f;
      bool qlinked = false;
      if (qcn && !qcn->params.empty())
        for (auto &f : *qcn->params[0].ptrFields) qlinked |= f.kind == "bytes" && f.lenOffset == 12 && f.lenBits == 32;
      CHECK(qlinked, "`len`, nested inside the anonymous union/struct, is found by findSiblingLenField at offset 12");
      if (qcn) {
        scan::Options so6;
        auto e6 = scan::makeEntry(*qcn, so6, rq.functions);
        CHECK(has(e6.specText, "from_field"), "the auto-generated spec ties `name`'s size to the nested `len` field:\n" << e6.specText);
      }
      std::string qout = run(bin + " --entries all --format json " + qf, &rc);
      report::Report qr;
      std::string qer;
      CHECK(report::fromJson(qout.substr(qout.find('{')), qr, qer), "qstr_anon_union_len scan json: " << qer);
      CHECK(qr.entries.size() == 1 && qr.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
            "with the real nested-len size, `q->name[q->len-1]` is in bounds (no spurious oob_read): "
            << (qr.entries.empty() ? "no entry" : report::verdictName(qr.entries[0].verdict)));
      std::string qbf = HLIR_SCAN_FIXTURE_DIR "/qstr_anon_union_len_bug.c";
      std::string qbout = run(bin + " --entries all --format json " + qbf, &rc);
      report::Report qbr;
      CHECK(report::fromJson(qbout.substr(qbout.find('{')), qbr, qer), "qstr_anon_union_len_bug scan json: " << qer);
      CHECK(qbr.entries.size() == 1 && qbr.entries[0].verdict == report::Verdict::Bug,
            "without the len==0 guard, the real underflow (len-1 wraps) is still found: "
            << (qbr.entries.empty() ? "no entry" : report::verdictName(qbr.entries[0].verdict)));
    }
    // regression: P0 item 2 of docs/KNOWN_GAPS_PRIORITIZED.md -- `struct sockaddr *addr, int addr_len`-shaped
    // top-level parameters (the highest-frequency signature in the Linux BSD-socket layer) were never linked by
    // `isByteBuffer()`, which only recognised `void*`/`int*` pointees. Scan.cpp's `isSockaddrLike()` (name-prefix
    // match on "sockaddr") now feeds into the existing length<->buffer relation mechanism, and `struct iovec *iov,
    // int iovcnt` (same signature shape, but `iovcnt` is an element count, not a byte length) must stay unaffected.
    {
      const std::string saf = HLIR_SCAN_FIXTURE_DIR "/sockaddr_len.c";
      auto rsa = frontend::lowerC(slurp(saf), saf, po);
      CHECK(rsa.ok, "sockaddr_len lowers: " << rsa.diagnostics);
      const frontend::FunctionInfo *scn = nullptr;
      for (auto &f : rsa.functions) if (f.name == "consume") scn = &f;
      if (scn) {
        scan::Options so3;
        auto e3 = scan::makeEntry(*scn, so3, rsa.functions);
        CHECK(has(e3.specText, "addr_len <= size(uaddr)"), "the auto-generated spec ties `addr_len` to `size(uaddr)`:\n" << e3.specText);
        CHECK(has(e3.specText, "size: { min: 16, max: "), "`uaddr` is a range, not a fixed 16-byte point:\n" << e3.specText);
      }
      std::string saout = run(bin + " --entries all --format json " + saf, &rc);
      report::Report sar;
      std::string saer;
      CHECK(report::fromJson(saout.substr(saout.find('{')), sar, saer), "sockaddr_len scan json: " << saer);
      CHECK(sar.entries.size() == 1 && sar.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
            "with the real addr_len-linked size, `uaddr[addr_len-1]` is in bounds (no spurious oob_read): "
            << (sar.entries.empty() ? "no entry" : report::verdictName(sar.entries[0].verdict)));
      std::string sabf = HLIR_SCAN_FIXTURE_DIR "/sockaddr_len_bug.c";
      std::string sabout = run(bin + " --entries all --format json " + sabf, &rc);
      report::Report sabr;
      CHECK(report::fromJson(sabout.substr(sabout.find('{')), sabr, saer), "sockaddr_len_bug scan json: " << saer);
      CHECK(sabr.entries.size() == 1 && sabr.entries[0].verdict == report::Verdict::Bug,
            "the real off-by-one past addr_len is still found: "
            << (sabr.entries.empty() ? "no entry" : report::verdictName(sabr.entries[0].verdict)));
      const std::string ivf = HLIR_SCAN_FIXTURE_DIR "/iovec_not_sockaddr.c";
      auto riv = frontend::lowerC(slurp(ivf), ivf, po);
      CHECK(riv.ok, "iovec_not_sockaddr lowers: " << riv.diagnostics);
      const frontend::FunctionInfo *ivn = nullptr;
      for (auto &f : riv.functions) if (f.name == "consume") ivn = &f;
      if (ivn) {
        scan::Options so4;
        auto e4 = scan::makeEntry(*ivn, so4, riv.functions);
        CHECK(!has(e4.specText, "iovcnt <= size(iov)"), "`iovcnt` (an element count) must not get a size(iov) relation:\n" << e4.specText);
        CHECK(has(e4.specText, "size: { min: 16, max: 16 }"), "`iov` keeps its fixed sizeof(struct iovec) size, unaffected by the sockaddr fix:\n" << e4.specText);
      }
    }
    // regression: §22.144 follow-up -- a sockaddr-family struct param's synthesized size floor is
    // sizeof(declared struct) normally, but sizeof(struct sockaddr_storage)=128 under `--linux` (real Linux
    // syscall args of this shape are always backed by at least that much allocation; net/unix's unix_mkname_bsd
    // writes up to that bound and a 110-byte floor for `struct sockaddr_un*` is a narrow false positive there).
    // Gated on `--linux` specifically because this guarantee does not hold for arbitrary userspace code.
    {
      const std::string slf = HLIR_SCAN_FIXTURE_DIR "/sockaddr_linux_floor.c";
      auto rl = frontend::lowerC(slurp(slf), slf, po);
      CHECK(rl.ok, "sockaddr_linux_floor lowers: " << rl.diagnostics);
      const frontend::FunctionInfo *lfn = nullptr;
      for (auto &f : rl.functions) if (f.name == "consume") lfn = &f;
      if (lfn) {
        scan::Options so5;
        auto e5 = scan::makeEntry(*lfn, so5, rl.functions);
        CHECK(has(e5.specText, "size: { min: 110, max:"), "without --linux, the floor stays at sizeof(struct sockaddr_un)=110:\n" << e5.specText);
        scan::Options so6;
        so6.linuxApi = true;
        auto e6 = scan::makeEntry(*lfn, so6, rl.functions);
        CHECK(has(e6.specText, "size: { min: 128, max:"), "with --linux, the floor is raised to sizeof(struct sockaddr_storage)=128:\n" << e6.specText);
      }
    }
    std::string out = run(bin + " --entries all --format json " + pa, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "ptrarray scan json: " << er);
    std::map<std::string, std::string> v;
    for (auto &e : rp.entries) v[e.function] = report::verdictName(e.verdict);
    CHECK(v["get_cmd"] == "safe_under_assumptions", "the argv slots are valid objects: get_cmd " << v["get_cmd"]);
    CHECK(v["bad_cmd"] == "bug", "argv[argc] is one past the slots: bad_cmd " << v["bad_cmd"]);
    std::string gt = run(bin + " --entries all --format json " + HLIR_SCAN_FIXTURE_DIR "/goto_decl.c", &rc);
    report::Report gr;
    CHECK(report::fromJson(gt.substr(gt.find('{')), gr, er), "goto scan json: " << er);
    CHECK(gr.entries.size() == 1 && gr.entries[0].verdict == report::Verdict::SafeUnderAssumptions, "a goto past a declaration lowers and verifies: " << (gr.entries.empty() ? "no entry" : report::verdictName(gr.entries[0].verdict)));
    // regression: a local declared under one `switch` case and used (via fallthrough and an explicit goto) under a
    // later case reached directly by the switch's own dispatch - the alloca must be hoisted to the entry block
    // (Memory/Frontend fix, DESIGN.md) or this fails IR verification ("does not dominate this use").
    std::string sgt = run(bin + " --entries all --format json " + HLIR_SCAN_FIXTURE_DIR "/switch_goto_decl.c", &rc);
    report::Report sgr;
    CHECK(report::fromJson(sgt.substr(sgt.find('{')), sgr, er), "switch_goto_decl scan json: " << er);
    CHECK(sgr.entries.size() == 1 && sgr.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
          "a local shared across switch cases via goto/fallthrough lowers and verifies: " << (sgr.entries.empty() ? "no entry" : report::verdictName(sgr.entries[0].verdict)));
    // regression: a function defined only via #include-ing a sibling `.c` "template" file (the X-macro idiom,
    // e.g. expat's xmltok.c pulling in xmltok_ns.c twice to generate Xml*/Xml*NS pairs), with the only caller in
    // a DIFFERENT file under `--link` (xmacro_entry.c calls what xmacro_defs.c defines via xmacro_tmpl.c) - must
    // still get a real body, not be dropped and treated as opaque (Frontend.cpp's FnCollector used to require
    // `isInMainFile`, which is false for `#include`d content even when it's a `.c` file meant to be pasted in
    // once; DESIGN.md has the full writeup).
    std::string xmt = run(bin + " --link --entries all --format json " + HLIR_SCAN_FIXTURE_DIR
                               + "/xmacro_entry.c " + HLIR_SCAN_FIXTURE_DIR + "/xmacro_defs.c",
                           &rc);
    report::Report xmr;
    CHECK(report::fromJson(xmt.substr(xmt.find('{')), xmr, er), "xmacro link scan json: " << er);
    CHECK(xmr.entries.size() == 1 && xmr.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
          "a function defined only via #include of a sibling .c template, called only from another --link unit, "
          "gets a real body: " << (xmr.entries.empty() ? "no entry" : report::verdictName(xmr.entries[0].verdict)));
    // regression: the same X-macro / #include'd-.c-file gap, but for a *global variable*'s initialiser instead
    // of a function body (freetype's `tt_driver_class`, #include'd into truetype.c via ttdriver.c, read only
    // from ftinit.c under --link - DESIGN.md has the full writeup). Frontend.cpp's separate "export this unit's
    // initialised globals for other --link units" pass used to require isInMainFile too, so the global's real
    // initialiser was dropped and it stayed all-zero at runtime.
    std::string xgt = run(bin + " --link --format json " + HLIR_SCAN_FIXTURE_DIR
                               + "/xglobal_entry.c " + HLIR_SCAN_FIXTURE_DIR + "/xglobal_defs.c",
                           &rc);
    report::Report xgr;
    CHECK(report::fromJson(xgt.substr(xgt.find('{')), xgr, er), "xglobal link scan json: " << er);
    CHECK(xgr.entries.size() == 1 && xgr.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
          "a global defined only via #include of a sibling .c template, read only from another --link unit, "
          "gets its real initialiser: " << (xgr.entries.empty() ? "no entry" : report::verdictName(xgr.entries[0].verdict)));
    // regression: the same #include'd-.c gap, for a function whose *address* is taken only inside the included
    // file (expat's xmltok_ns.c storing initScanProlog into the INIT_ENCODING it builds). The indirect-call
    // dispatcher's candidate collection (AddrTakenFinder) used to count only main-file references, so the call
    // through the stored pointer fell to the opaque fallback.
    std::string xat = run(bin + " --link --include-noarg --format json --entry entry " + HLIR_SCAN_FIXTURE_DIR
                               + "/xaddr_entry.c " + HLIR_SCAN_FIXTURE_DIR + "/xaddr_defs.c",
                           &rc);
    report::Report xar;
    CHECK(report::fromJson(xat.substr(xat.find('{')), xar, er), "xaddr link scan json: " << er);
    CHECK(xar.entries.size() == 1 && xar.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
          "a function whose address is taken only in a #include'd .c template is an indirect-call candidate: "
              << (xar.entries.empty() ? "no entry" : report::verdictName(xar.entries[0].verdict)));
    // regression (DESIGN §22.342): indirect-call candidates and the funcptr targets of a synthesized object are matched by
    // C type, not only by the core signature, which erases what pointers point to. net/rds: `trans->laddr_check(net,
    // addr, scope)` reached `rds_getname(sock, uaddr, peer)`, which wrote a sockaddr into a struct in6_addr. A function
    // whose address is cast to the call's type stays reachable. Checked on the generated spec and the linked dispatcher
    // (deterministic), plus the verdict of the typed case.
    {
      std::string xd = "/tmp/hlir_xctype." + std::to_string(getpid());
      run("rm -rf " + xd + " " + xd + "c " + xd + "s " + xd + "o");
      std::string fx = std::string(HLIR_SCAN_FIXTURE_DIR) + "/";
      std::string t1 = run(bin + " --link --entry entry --format json --out " + xd + " --dump-linked " + xd + ".core " + fx + "xctype_entry.c " + fx + "xctype_defs.c", &rc);
      report::Report x1;
      CHECK(report::fromJson(t1.substr(t1.find('{')), x1, er), "xctype link scan json: " << er);
      CHECK(x1.entries.size() == 1 && x1.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
            "a call through a check() pointer cannot reach a function of another C type with the same core signature: "
                << (x1.entries.empty() ? "no entry" : report::verdictName(x1.entries[0].verdict)));
      std::string sp1 = run("cat " + xd + "/specs/*xctype_entry.c__entry.yaml"), d1 = slurp(xd + ".core");
      CHECK(has(sp1, "targets: [check_real]"), "the synthesized check() field only gets check_real as target:\n" << sp1);
      CHECK(has(d1, "core.call @check_real(") && !has(d1, "core.call @getname_wide(") && !has(d1, "core.call @getname_exported("),
            "the dispatcher lists check_real, not getname_wide, and not getname_exported (an __ADDRESSABLE cast is no escape)");
      run(bin + " --link --entry entry --format json --out " + xd + "c --dump-linked " + xd + "c.core " + fx + "xctype_entry.c " + fx + "xctype_defs.c " + fx + "xctype_cast.c", &rc);
      std::string sp2 = run("cat " + xd + "c/specs/*xctype_entry.c__entry.yaml"), d2 = slurp(xd + "c.core");
      CHECK(has(sp2, "targets: [check_real, getname_cast]") && has(d2, "core.call @getname_cast("),
            "a function cast to the call's type stays a target and a dispatcher candidate:\n" << sp2);
      std::string t4 = run(bin + " --link --entry entry_other --format json --out " + xd + "o " + fx + "xctype_entry.c " + fx + "xctype_defs.c", &rc);
      std::string sp4 = run("cat " + xd + "o/specs/*xctype_entry.c__entry_other.yaml");
      CHECK(has(sp4, "kind: buffer, taint: none, size: { min: 1, max: 1 }") && !has(sp4, "funcptr"),
            "a funcptr field with no candidate of its C type (but some of its signature) is a non-NULL opaque function:\n" << sp4);
      report::Report x4;
      CHECK(report::fromJson(t4.substr(t4.find('{')), x4, er) && x4.entries.size() == 1 && x4.entries[0].verdict == report::Verdict::Bug,
            "the path goes on past the call through it (opaque external call): " << (x4.entries.empty() ? "no entry" : report::verdictName(x4.entries[0].verdict)));
      for (const char *mode : {"", "--link "}) {  // generic dispatch through `void *` signatures must still reach the typed handler
        std::string tg = run(bin + " " + mode + "--entry entry --format json " + fx + "xctype_generic.c", &rc);
        report::Report xg;
        bool reached = report::fromJson(tg.substr(tg.find('{')), xg, er) && xg.entries.size() == 1;
        if (reached) {
          reached = false;
          for (auto &f : xg.entries[0].findings) reached |= f.function == "on_req" && f.loc.line == 11;
        }
        CHECK(reached, "a vtable read back as void (*)(void) and called through a void * signature reaches on_req (" << mode << "):\n" << tg.substr(0, 400));
      }
      run(bin + " --entry entry --format json --out " + xd + "s " + fx + "xctype_single.c", &rc);
      std::string sp3 = run("cat " + xd + "s/specs/*xctype_single.c__entry.yaml");
      CHECK(has(sp3, "targets: [check_real]"), "without --link the same rule applies:\n" << sp3);
      run("rm -rf " + xd + " " + xd + "c " + xd + "s " + xd + "o " + xd + ".core " + xd + "c.core");
    }
    // regression: strtod's endptr must point back into nptr's object (models/libc.core's @strtod model, added
    // after scanning cJSON's parse_number hit a spurious ptr_cmp_diff_obj on `end - s` after `strtod(s, &end)` -
    // before the model existed, strtod fell back to the generic opaque-external default, whose output pointer has
    // no guaranteed relation to the input object. DESIGN.md has the full writeup.
    std::string stt = run(bin + " --entries all --format json " + HLIR_SCAN_FIXTURE_DIR "/strtod_endptr.c", &rc);
    report::Report str;
    CHECK(report::fromJson(stt.substr(stt.find('{')), str, er), "strtod_endptr scan json: " << er);
    bool diffObj = false;
    for (auto &e : str.entries)
      for (auto &f : e.findings)
        if (f.kind == "ptr_cmp_diff_obj") diffObj = true;
    CHECK(!diffObj, "strtod's endptr - nptr is a same-object pointer difference, never ptr_cmp_diff_obj");
    // regression (DESIGN.md §22.346, c-ares): length names with a type tag (`alen_int`) pair with their buffer; in a group
    // with another buffer a `const char *` is both NUL-terminated and as big as the length (inet_net_pton vs memcpy shape);
    // a group of only `const char *` is a plain buffer; a length never pairs across another length parameter
    {
      std::string ld = "/tmp/hlir_lenpair." + std::to_string(getpid());
      run("rm -rf " + ld);
      run(bin + " --entries all --list --out " + ld + " " + HLIR_SCAN_FIXTURE_DIR "/lenpair.c", &rc);
      std::string pr = run("cat " + ld + "/specs/*__parse_reply.yaml"), np = run("cat " + ld + "/specs/*__net_pton.yaml"),
                  ps = run("cat " + ld + "/specs/*__parse_str.yaml"), pp = run("cat " + ld + "/specs/*__ptr_reply.yaml");
      CHECK(has(pr, "(size_t)alen_int <= size(abuf)"), "alen_int pairs with abuf:\n" << pr);
      CHECK(has(np, "src: { taint: pointee, kind: cstring") && has(np, "(size_t)size <= size(dst)") && has(np, "(size_t)size <= size(src)"),
            "a const char * next to another buffer is NUL-terminated and still as big as the length:\n" << np);
      CHECK(has(ps, "kind: buffer") && has(ps, "(size_t)len <= size(s)"), "a lone const char * keeps its length:\n" << ps);
      CHECK(has(pp, "(size_t)alen_int <= size(abuf)") && has(pp, "(size_t)addrlen <= size(addr)") && !has(pp, "addrlen <= size(abuf)"),
            "addrlen does not reach back over alen_int to abuf:\n" << pp);
      // regression (DESIGN.md §22.349, libwebp): a role tag hides the length the same way a type tag did
      std::string ph = run("cat " + ld + "/specs/*__parse_headers.yaml"), tf = run("cat " + ld + "/specs/*__take_flags.yaml");
      CHECK(has(ph, "(size_t)data_size_param <= size(data_param)"), "data_size_param pairs with data_param:\n" << ph);
      CHECK(!has(tf, "size(buf)"), "the tag is stripped but not trusted: flags_param is not a length:\n" << tf);
      run("rm -rf " + ld);
    }
    // regression (DESIGN.md §22.352, FreeType ttload.c:75): an array of structs is sized by its sibling count field,
    // including when the count names only the tail of the pointer's name (dir_tables <- num_tables); a bare `count`
    // beside a non-array struct pointer stays unpaired, and with the pair tied the array walk is no longer an OOB
    {
      std::string ed = "/tmp/hlir_elemcount." + std::to_string(getpid());
      run("rm -rf " + ed);
      run(bin + " --entries all --list --out " + ed + " " + HLIR_SCAN_FIXTURE_DIR "/elemcount.c", &rc);
      std::string wt = run("cat " + ed + "/specs/*__walk_tables.yaml"), wi = run("cat " + ed + "/specs/*__walk_items.yaml"),
                  rx = run("cat " + ed + "/specs/*__read_ctx.yaml");
      CHECK(has(wt, "from_field: { offset: 0, type: uint16_t, elem: 16 }"), "dir_tables is sized by num_tables:\n" << wt);
      CHECK(has(wi, "from_field: { offset: 0, type: uint32_t, elem: 16 }"), "items is sized by num_items:\n" << wi);
      CHECK(!has(rx, "from_field"), "a bare count does not size a non-array struct pointer:\n" << rx);
      run("rm -rf " + ed);
      std::string et = run(bin + " --entries all --timeout 10 --format json " + HLIR_SCAN_FIXTURE_DIR "/elemcount.c", &rc);
      report::Report er2;
      CHECK(report::fromJson(et.substr(et.find('{')), er2, er), "elemcount scan json: " << er);
      bool walkOob = false;
      for (auto &e : er2.entries)
        if (e.function == "walk_tables" || e.function == "walk_items")
          for (auto &f : e.findings)
            if (!f.warning && f.replay == report::ReplayStatus::Confirmed &&
                (f.kind == "ptr_arith_oob" || f.kind == "oob_read")) walkOob = true;
      CHECK(!walkOob, "walking the whole array is in bounds once it is sized by its count:\n" << et);
    }
    // regression (DESIGN.md §22.351, fs/jfs dbJoin): a confirmed finding's witness must name the bytes that actually
    // drive it. `probe_objid`'s first parameter allocates a sub-object in between, so the object id can no longer be
    // guessed from the parameter's position; before the fix `h` printed "all bytes 0", which cannot reach the read.
    {
      std::string wt = run(bin + " --entries all --entry probe_objid --format json " + HLIR_SCAN_FIXTURE_DIR "/witobjid.c", &rc);
      report::Report wr;
      CHECK(report::fromJson(wt.substr(wt.find('{')), wr, er), "witobjid scan json: " << er);
      bool checked = false;
      for (auto &e : wr.entries)
        for (auto &f : e.findings) {
          if (f.kind != "oob_read" || f.replay != report::ReplayStatus::Confirmed) continue;
          for (auto &w : f.witness)
            if (w.name == "h") {
              CHECK(has(w.value, "non-zero bytes"), "the witness names h's bytes, not another object's:\n" << w.value);
              checked = true;
            }
        }
      CHECK(checked, "witobjid produced a confirmed oob_read with a witness for h:\n" << wt);
    }
    // regression (DESIGN.md §22.353, FreeType FT_StreamRec.read): an OPTIONAL callback field. Two halves:
    // the generator must mark exactly the fields the code tests for NULL, and the engine must actually explore
    // the NULL configuration -- the harness's own choice bits were emitted as untainted `core.nondet`, which
    // TaintDomain keeps fully CONCRETE, so the "callback absent" branch could never be taken.
    {
      std::string nd = "/tmp/hlir_nullfptr." + std::to_string(getpid());
      run("rm -rf " + nd);
      run(bin + " --entries all --list --out " + nd + " " + HLIR_SCAN_FIXTURE_DIR "/nullfptr.c", &rc);
      std::string sp = run("cat " + nd + "/specs/*__nullfptr_fetch.yaml");
      run("rm -rf " + nd);
      CHECK(has(sp, "offset: 0, kind: funcptr, targets: [zip_read], nullable: true"),
            "`read` is tested for NULL, so it may be synthesised as NULL:\n" << sp);
      CHECK(!has(sp, "targets: [zip_fill], nullable"), "`fill` is never tested for NULL, so it may not be:\n" << sp);
      std::string nt = run(bin + " --entries all --entry nullfptr_fetch --format json " + HLIR_SCAN_FIXTURE_DIR "/nullfptr.c", &rc);
      report::Report nr;
      CHECK(report::fromJson(nt.substr(nt.find('{')), nr, er), "nullfptr scan json: " << er);
      bool memPath = false;
      for (auto &e : nr.entries)
        for (auto &f : e.findings)
          if (!f.warning && f.replay == report::ReplayStatus::Confirmed && (f.kind == "oob_read" || f.kind == "ptr_arith_oob")) memPath = true;
      CHECK(memPath, "the branch taken when the callback is absent is reached and its oob confirmed:\n" << nt);
    }
    // regression (DESIGN.md §22.354, FreeType psobjs.c:286 x11): the (base, cursor, limit) idiom. The three
    // pointers walk ONE buffer; synthesised as independent objects, `while (cur < p->limit)` compares pointers
    // into unrelated allocations, which is UB by itself and makes the bound test meaningless. The owner must also
    // come FIRST in the emitted list -- `same_alloc` resolves against the fields already planned, and a parser
    // commonly declares its cursor before the base it walks.
    {
      std::string sd = "/tmp/hlir_samealloc." + std::to_string(getpid());
      run("rm -rf " + sd);
      run(bin + " --entries all --list --out " + sd + " " + HLIR_SCAN_FIXTURE_DIR "/samealloc.c", &rc);
      std::string sp = run("cat " + sd + "/specs/*__scan_spaces.yaml"), sv = run("cat " + sd + "/specs/*__span_len.yaml"),
                  sm = run("cat " + sd + "/specs/*__read_mixed.yaml"), ss = run("cat " + sd + "/specs/*__stream_span.yaml");
      run("rm -rf " + sd);
      CHECK(has(sp, "{ offset: 0, kind: buffer, taint: pointee, same_alloc: { offset: 8, pos: inside } }"),
            "the cursor is somewhere inside the base's allocation:\n" << sp);
      CHECK(has(sp, "{ offset: 16, kind: buffer, taint: pointee, same_alloc: { offset: 8 } }"),
            "the limit is one-past-the-end of it:\n" << sp);
      CHECK(sp.find("offset: 8, kind: buffer") < sp.find("offset: 0, kind: buffer"),
            "the owner is emitted before the views that name it:\n" << sp);
      CHECK(has(sv, "{ offset: 8, kind: buffer, taint: pointee, same_alloc: { offset: 0 } }"),
            "a validator's limit is one-past-the-end of its base:\n" << sv);
      CHECK(!has(sm, "same_alloc"), "pointers to different element types are two buffers, not one:\n" << sm);
      // FT_StreamRec: all three pointers also pair with the `size` field, which used to give three separate objects
      // of that size. Being a view wins for the two that are views; the owner keeps its derived size.
      CHECK(has(ss, "{ offset: 0, kind: buffer, taint: pointee, size: { from_field: { offset: 8, type: uint64_t } } }"),
            "the owner keeps the size it derives from its length field:\n" << ss);
      CHECK(has(ss, "{ offset: 16, kind: buffer, taint: pointee, same_alloc: { offset: 0, pos: inside } }") &&
                has(ss, "{ offset: 24, kind: buffer, taint: pointee, same_alloc: { offset: 0 } }"),
            "a view drops its own derived size in favour of sharing the owner's allocation:\n" << ss);
      std::string st = run(bin + " --entries all --timeout 10 --format json " + HLIR_SCAN_FIXTURE_DIR "/samealloc.c", &rc);
      report::Report sr;
      CHECK(report::fromJson(st.substr(st.find('{')), sr, er), "samealloc scan json: " << er);
      bool crossObj = false;
      for (auto &e : sr.entries)
        for (auto &f : e.findings)
          if (!f.warning && f.replay == report::ReplayStatus::Confirmed &&
              (f.kind == "ptr_cmp_diff_obj" || f.kind == "ptr_diff_diff_obj")) crossObj = true;
      CHECK(!crossObj, "cursor, base and limit are in one object, so comparing them is not cross-object:\n" << st);
    }
    // regression (DESIGN.md §22.355, FreeType FT_Outline.contours): an array of WIDER INTEGERS sized by a sibling
    // count. Only an unambiguous count spelling may size it -- reading a byte length as a count would make the
    // object sizeof(element) times too big and HIDE a real overrun, so `_len` and a bare `length` stay unpaired.
    {
      std::string id = "/tmp/hlir_intcount." + std::to_string(getpid());
      run("rm -rf " + id);
      run(bin + " --entries all --list --out " + id + " " + HLIR_SCAN_FIXTURE_DIR "/intcount.c", &rc);
      std::string lc = run("cat " + id + "/specs/*__last_contour.yaml"), lw = run("cat " + id + "/specs/*__last_word.yaml"),
                  ls = run("cat " + id + "/specs/*__last_slot.yaml"), fb = run("cat " + id + "/specs/*__first_byte.yaml");
      run("rm -rf " + id);
      CHECK(has(lc, "from_field: { offset: 0, type: uint16_t, elem: 2 }"), "contours is sized by n_contours shorts:\n" << lc);
      CHECK(!has(lw, "from_field"), "a `_len` byte length does not count elements of a wider array:\n" << lw);
      CHECK(!has(ls, "from_field"), "a bare `length` does not either:\n" << ls);
      CHECK(has(fb, "from_field: { offset: 0, type: uint32_t } }"), "a byte buffer keeps the plain byte-count form:\n" << fb);
      std::string it = run(bin + " --entries all --format json " + HLIR_SCAN_FIXTURE_DIR "/intcount.c", &rc);
      report::Report ir;
      CHECK(report::fromJson(it.substr(it.find('{')), ir, er), "intcount scan json: " << er);
      bool oob = false;
      for (auto &e : ir.entries)
        if (e.function == "last_contour")
          for (auto &f : e.findings)
            if (!f.warning && f.replay == report::ReplayStatus::Confirmed &&
                (f.kind == "oob_read" || f.kind == "ptr_arith_oob")) oob = true;
      CHECK(!oob, "indexing the last element is in bounds once the array is sized by its count:\n" << it);
    }
    // regression (DESIGN.md §22.356, FreeType CFF_PrivateRec.blue_values): the count of an INLINE fixed array.
    // The array is a member, not a pointer field, so no size mechanism reaches it; the harness needs the bound its
    // real producer enforces. It is a NARROWING assumption, so it is gated on names composed from the array's own
    // name and must show up in the report's assumptions.
    {
      std::string nd = "/tmp/hlir_inlinecount." + std::to_string(getpid());
      run("rm -rf " + nd);
      run(bin + " --entries all --list --out " + nd + " " + HLIR_SCAN_FIXTURE_DIR "/inlinecount.c", &rc);
      std::string sb = run("cat " + nd + "/specs/*__sum_blues.yaml"), sd = run("cat " + nd + "/specs/*__sum_dict.yaml"),
                  sl = run("cat " + nd + "/specs/*__sum_loose.yaml"), sw = run("cat " + nd + "/specs/*__sum_wide.yaml");
      run("rm -rf " + nd);
      CHECK(has(sb, "where: [ { offset: 112, type: uint8_t, range: [0, 14] } ]"),
            "num_blue_values cannot exceed blue_values[14]:\n" << sb);
      CHECK(has(sd, "where: [ { offset: 112, type: uint8_t, range: [0, 14] } ]"),
            "the same bound one level down, inside a synthesised field object:\n" << sd);
      CHECK(!has(sl, "where"), "a `limit` not composed from `slots` says nothing about that array:\n" << sl);
      CHECK(!has(sw, "where"), "a bound the type cannot exceed anyway is not worth stating:\n" << sw);
      std::string nt = run(bin + " --entries all --timeout 10 --format json " + HLIR_SCAN_FIXTURE_DIR "/inlinecount.c", &rc);
      report::Report nr;
      CHECK(report::fromJson(nt.substr(nt.find('{')), nr, er), "inlinecount scan json: " << er);
      bool boundedOob = false, looseOob = false, stated = false;
      for (auto &e : nr.entries) {
        bool oob = false;
        for (auto &f : e.findings)
          if (!f.warning && f.replay == report::ReplayStatus::Confirmed && f.kind == "field_oob") oob = true;
        if (e.function == "sum_blues" || e.function == "sum_dict") {
          boundedOob |= oob;
          for (auto &a : e.assumptions)
            if (a.category == "precondition") stated = true;
        }
        if (e.function == "sum_loose") looseOob |= oob;
      }
      CHECK(!boundedOob, "walking a bounded count stays inside the inline array:\n" << nt);
      CHECK(looseOob, "an unbounded count still walks off it -- the gate did not over-reach:\n" << nt);
      CHECK(stated, "the narrowing assumption is reported, not silent:\n" << nt);
    }
    // regression (DESIGN.md §22.358, sound/core round 42): a bound the program ASSERTS about its own member
    // (`snd_BUG_ON(dp->max_synthdev > MAX)`) becomes a `where:` precondition. The line that must not be crossed is
    // the negative here: an `if (x) return -EINVAL` VALIDATES attacker input and must never be harvested.
    {
      std::string ad = "/tmp/hlir_assertbound." + std::to_string(getpid());
      run("rm -rf " + ad);
      run(bin + " --link --entries all --list --out " + ad + " " + HLIR_SCAN_FIXTURE_DIR "/assertbound.c", &rc);
      std::string sd = run("cat " + ad + "/specs/*__sum_devs.yaml");
      run("rm -rf " + ad);
      CHECK(has(sd, "{ offset: 0, type: int32_t, range: [-2147483648, 12] } ]"),
            "the asserted bound on ndev is a precondition, and `checked` at offset 4 is not:\n" << sd);
      std::string at = run(bin + " --link --entries all --format json " + HLIR_SCAN_FIXTURE_DIR "/assertbound.c", &rc);
      std::string bt = run(bin + " --entries all --format json " + HLIR_SCAN_FIXTURE_DIR "/assertbound.c", &rc);
      report::Report ar, br;
      CHECK(report::fromJson(at.substr(at.find('{')), ar, er), "assertbound scan json: " << er);
      CHECK(report::fromJson(bt.substr(bt.find('{')), br, er), "assertbound no-link json: " << er);
      auto oob = [&](report::Report &r, const std::string &fn) {
        for (auto &e : r.entries)
          if (e.function == fn)
            for (auto &f : e.findings)
              if (!f.warning && f.replay == report::ReplayStatus::Confirmed && f.kind == "oob_read") return true;
        return false;
      };
      CHECK(oob(br, "sum_devs"), "without the asserted bound the walk runs off the array:\n" << bt);
      CHECK(!oob(ar, "sum_devs"), "with it, the walk is in bounds -- the assertion is a per-TYPE fact, and the\n"
                                  "function that states it is never called from this entry:\n" << at);
    }
    // regression: the same for memmem (found scanning c-ares, DESIGN.md): its result points into the haystack
    std::string mmt = run(bin + " --entries all --format json " + HLIR_SCAN_FIXTURE_DIR "/memmem_offset.c", &rc);
    report::Report mmr;
    CHECK(report::fromJson(mmt.substr(mmt.find('{')), mmr, er), "memmem_offset scan json: " << er);
    bool mmDiff = false, mmReal = false;  // the search loop is long: the verdict may stay unknown on the run limit
    for (auto &e : mmr.entries)
      for (auto &f : e.findings) {
        mmDiff |= f.kind == "ptr_cmp_diff_obj";
        mmReal |= !f.warning;
      }
    CHECK(!mmr.entries.empty() && !mmDiff && !mmReal, "memmem's result - haystack is a same-object difference, no finding:\n" << mmt.substr(0, 600));
    // regression: a size in an equality relation with a tainted length is symbolic, not fixed to its seed (found
    // scanning ntfs3, DESIGN.md §22.348): with `bytes == size(ib)` the sector-multiple branch used to be unflippable
    {
      std::string rd = dir + "/relsize";
      run("mkdir -p " + rd);
      std::ofstream(rd + "/check_indx.yaml") << "taint_entries:\n  - function: check_indx\n    label: network\n    params:\n"
          "      ib: { taint: pointee, kind: buffer, size: { min: 40, max: 4096 } }\n      bytes: { taint: value, type: uint32_t }\n"
          "    relations:\n      - \"(size_t)bytes == size(ib)\"\n";
      std::string rs = run(bin + " --entry check_indx --spec-dir " + rd + " --format json " HLIR_SCAN_FIXTURE_DIR "/relsize_pin.c", &rc);
      report::Report rr;
      CHECK(report::fromJson(rs.substr(rs.find('{')), rr, er), "relsize_pin scan json: " << er);
      bool oob = false;
      for (auto &e : rr.entries)
        for (auto &f : e.findings) oob |= f.kind == "oob_read" && f.replay == report::ReplayStatus::Confirmed;
      CHECK(oob, "check_indx: the read past `bytes` is found with bytes == size(ib):\n" << rs.substr(0, 800));
    }
    // regression: two real C idioms needing a struct (aggregate) expression used as an rvalue, both from libyaml's
    // scanner/parser (DESIGN.md) - `a = b = c;` with a plain-struct type (genL's "inner assignment used as an
    // lvalue" case used to only cover scalar LHS types), and `(void)*structPtr;` (Sema wraps this in an implicit
    // `CK_LValueToRValue ... part_of_explicit_cast` that genR/genCast can't turn into a scalar Value for a
    // non-scalar type - CK_ToVoid's isRecordTy branch now unwraps it via genL, like it already does for the ones
    // that are already glvalues, instead of calling genR on it).
    std::string agt = run(bin + " --entries all --format json " + HLIR_SCAN_FIXTURE_DIR "/aggregate_rvalue.c", &rc);
    report::Report agr;
    CHECK(report::fromJson(agt.substr(agt.find('{')), agr, er), "aggregate_rvalue scan json: " << er);
    CHECK(agr.entries.size() == 2, "aggregate_rvalue: both entries lower and scan, got " << agr.entries.size());
    for (auto &e : agr.entries)
      CHECK(e.verdict == report::Verdict::SafeUnderAssumptions,
            "aggregate_rvalue @" << e.function << " lowers and verifies: " << report::verdictName(e.verdict));
  }

  // ---------------------------------------------------------------- a long taint chain, length parameter names, strtol
  if (mine()) {
    const std::string dc = HLIR_SCAN_FIXTURE_DIR "/deep_chain.c";
    std::string out = run(bin + " --format json " + dc, &rc);
    report::Report rp;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), rp, er), "deep_chain json: " << er);
    std::map<std::string, const report::EntryReport *> m;
    for (auto &e : rp.entries) m[e.function] = &e;
    auto depthOf = [&](const char *fn, const char *kind) {
      size_t d = 0;
      if (m.count(fn)) for (auto &f : m[fn]->findings) if (f.kind == kind && f.replay == report::ReplayStatus::Confirmed) d = std::max(d, f.callStack.size());
      return d;
    };
    CHECK(m.count("handle_packet_bad") && m["handle_packet_bad"]->verdict == report::Verdict::Bug, "the bug 9 calls deep is found (the policy limit is too large)");
    CHECK(depthOf("handle_packet_bad", "oob_write") == 9, "its call chain is entry -> 7 layers -> memcpy: depth " << depthOf("handle_packet_bad", "oob_write"));
    CHECK(m.count("handle_packet_ok") && m["handle_packet_ok"]->verdict == report::Verdict::SafeUnderAssumptions, "the same chain with the right limit is safe (no false positive through 8 layers)");
    CHECK(m.count("handle_msg_trunc") && m["handle_msg_trunc"]->verdict == report::Verdict::Bug && depthOf("handle_msg_trunc", "oob_write") == 5, "the 8-bit check / 16-bit use mismatch is found across layers: depth " << depthOf("handle_msg_trunc", "oob_write"));
    CHECK(m.count("handle_msg_ok") && m["handle_msg_ok"]->verdict == report::Verdict::SafeUnderAssumptions, "the correct check is safe");
    if (m.count("handle_packet_bad"))
      for (auto &f : m["handle_packet_bad"]->findings)
        if (f.kind == "oob_write") {
          bool lenFromPacket = false;
          for (auto &w : f.witness) lenFromPacket |= w.name == "raw" && has(w.value, "[4]=");  // the field length byte of the packet
          CHECK(lenFromPacket, "the witness is a packet whose field length byte exceeds the buffer");
          break;
        }

    frontend::LowerOptions lo;
    lo.partial = true;
    const std::string lf = HLIR_SCAN_FIXTURE_DIR "/lenname.c";
    auto lr = frontend::lowerC(slurp(lf), lf, lo);
    CHECK(lr.ok && !lr.functions.empty(), "lenname lowers");
    if (lr.ok && !lr.functions.empty()) {
      auto e = scan::makeEntry(lr.functions[0], scan::Options{}, lr.functions);
      CHECK(has(e.specText, "size(dst)"), "`dstlen` is recognised as the length of dst:\n" << e.specText);
    }
    std::string st = run(bin + " --format json " + HLIR_SCAN_FIXTURE_DIR "/strto_driver.c", &rc);
    report::Report sr;
    CHECK(report::fromJson(st.substr(st.find('{')), sr, er), "strto json: " << er);
    for (auto &e : sr.entries) {
      if (e.function == "idx") CHECK(e.verdict == report::Verdict::Bug, "strtol: a number parsed from the string indexes past the table: " << report::verdictName(e.verdict));
      if (e.function == "idx_ok") CHECK(e.verdict != report::Verdict::Bug, "strtol with the bound has no bug: " << report::verdictName(e.verdict));
    }
  }

  // ---------------------------------------------------------------- pointer order, --lenient-ptr-arith, realloc
  if (mine()) {
    const std::string pf = HLIR_SCAN_FIXTURE_DIR "/ptr_order.c";
    auto verdictOf = [&](const std::string &cmd, const std::string &fn) {
      std::string o = run(cmd, &rc);
      report::Report r;
      std::string er;
      if (!report::fromJson(o.substr(o.find('{')), r, er)) return std::string("parse error: ") + er;
      for (auto &e : r.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(verdictOf(bin + " --format json " + pf, "back_ref") == "bug", "default: forming a pointer before the object is reported (formal UB)");
    CHECK(verdictOf(bin + " --lenient-ptr-arith --format json " + pf, "back_ref") == "safe_under_assumptions",
          "--lenient-ptr-arith: `ref < buf` is true for a negative offset (signed order), the access after the check is in bounds");
    CHECK(verdictOf(bin + " --format json " + HLIR_SCAN_FIXTURE_DIR "/abort_driver.c", "alloc_or_die") == "safe_under_assumptions", "abort() ends the path: the NULL branch of an allocator that aborts is not explored further");
    // DESIGN.md Sec.22.457. `malloc(len+1); memcpy(buf, in, len); buf[len] = '\0';` is the NUL-termination
    // contract every C-string harness in scan-profiles/ is built on. The concolic domain CONCRETISES the
    // tainted length, and writing the destination unguarded dropped the copied bytes' dependence on it while
    // the object's size kept one -- so strlen() reported an oob_read whose own witness (in_len = 2) stops two
    // bytes earlier. Both real defects below must survive the guard: a fix that silences the first case by
    // making the copy write less is a fix that hides them.
    // DESIGN.md Sec.22.461. `--seed-value` above the one soft preference on a tainted buffer
    // (`size(buf) <= 64`) must still produce a usable M0. Before the fix the preference was rejected,
    // SeedSolver skipped its re-check because none survived, and values() was read off an UNSAT
    // check -- so the seed came back all zeros and the entry ran with in_len = 0 while the result still
    // said Sat. 64 passed and 96 did not, which is why this asserts both: a fix that merely raised a
    // constant would keep the first and still fail the second.
    for (const char *sv : {"32", "64", "65", "96"}) {
      const std::string f = HLIR_SCAN_FIXTURE_DIR "/seed_value_large.c";
      int rc2 = 0;
      std::string o = run(bin + " --buf-max 96 --seed-value in_len=" + sv + " --entry seed_value_large --format json " + f, &rc2);
      report::Report rep;
      std::string er;
      CHECK(report::fromJson(o.substr(o.find('{')), rep, er), "seed_value_large.c parses: " << er);
      CHECK(rep.entries.size() == 1, "seed_value_large.c: one entry");
      if (rep.entries.size() == 1)
        CHECK(rep.entries[0].coverage.blocksVisited > 0,
              "--seed-value in_len=" << sv << " still runs the entry (blocks_visited > 0)");
    }
    {
      const std::string sc = HLIR_SCAN_FIXTURE_DIR "/symlen_copy.c";
      CHECK(verdictOf(bin + " --buf-max 48 --format json " + sc, "symlen_terminated") == "safe_under_assumptions",
            "a terminated buffer copied with a symbolic length does not over-read in strlen");
      CHECK(verdictOf(bin + " --buf-max 48 --format json " + sc, "symlen_memcpy_ovf") == "bug",
            "a symbolic-length memcpy into a 4-byte destination is still an oob_write");
      CHECK(verdictOf(bin + " --buf-max 48 --format json " + sc, "symlen_strlen_ovf") == "bug",
            "strlen over a buffer with no terminator is still an oob_read");
      // The one that proves the fix is a pin and not a muzzle: seeded with a length that FITS, so the engine
      // has to solve for one that does not. memcpy's bounds check runs before the length is pinned.
      CHECK(verdictOf(bin + " --buf-max 48 --seed-value in_len=2 --format json " + sc, "symlen_solve_ovf") == "bug",
            "an overflowing length is still SOLVED for, not just observed");
    }
    // ENGINE_LIMITATIONS.md §7.12: forming a pointer outside its object is reported, but it no longer ENDS the
    // run -- so a defect sitting behind the `p - n` compare idiom is reachable. Until this, `out[k] = 1` was
    // unreachable at any budget and the scan returned the weaker finding at the wrong line.
    {
      const std::string pa = HLIR_SCAN_FIXTURE_DIR "/ptr_arith_continue.c";
      std::string o = run(bin + " --entries all --format json " + pa, &rc);
      report::Report rep;
      std::string er;
      CHECK(report::fromJson(o.substr(o.find('{')), rep, er), "ptr_arith_continue.c parses: " << er);
      bool sawWrite = false, sawArith = false;
      for (auto &e : rep.entries)
        if (e.function == "behind_ptr_arith")
          for (auto &f : e.findings) {
            sawWrite |= f.kind == "oob_write";
            sawArith |= f.kind == "ptr_arith_oob";
          }
      CHECK(sawWrite, "the write BEHIND the out-of-range pointer computation is reported, at the write");
      CHECK(sawArith, "and the out-of-range pointer computation is still reported itself, not silently dropped");
      CHECK(verdictOf(bin + " --entries all --format json " + pa, "guarded") == "safe_under_assumptions",
            "the control (same shape, no out-of-range pointer, index checked) stays clean");
    }
    // --dump-branches (DESIGN.md §22.429): the reasons an edge is uncovered must come back DIFFERENT, because
    // they need opposite responses -- only `open` is a budget question. A test that merely counted missing edges
    // would pass with every one of them labelled the same, which is the state this replaced.
    {
      const std::string bf = "/tmp/hlir_branches_test." + std::to_string(getpid());
      (void)run(bin + " --entries all --runs 2000 --timeout 30 --dump-branches " + bf +
                    " --format json --output /dev/null " + HLIR_SCAN_FIXTURE_DIR "/dump_branches.c",
                &rc);
      std::ifstream bi(bf);
      std::stringstream bs;
      bs << bi.rdbuf();
      std::string body = bs.str();
      ::remove(bf.c_str());
      CHECK(has(body, "unsat\t"), "the edge the solver proved impossible is labelled `unsat`, not merely missing:\n" << body);
      CHECK(has(body, "const\t"), "the edge whose condition is a compile-time fact is labelled `const`:\n" << body);
      CHECK(has(body, "unsat=1") && has(body, "const=1"), "and the per-entry header counts them:\n" << body);
    }
    // A harness-declared deterministic setup region (DESIGN.md §22.438). Two things have to hold at once, and a
    // test that checked only the first would pass while the feature traded recall for speed: the PURE region is
    // reused, and the TAINTED one -- same shape, but it reads the entry's input -- is refused. Both must still
    // report the defect that sits after the region.
    {
      const std::string sf = HLIR_SCAN_FIXTURE_DIR "/setup_region.c";
      std::string o = run(bin + " --entries all --runs 400 --timeout 60 --format json " + sf, &rc);
      report::Report rep;
      std::string er;
      CHECK(report::fromJson(o.substr(o.find('{')), rep, er), "setup_region.c parses: " << er);
      bool sawPure = false, sawTainted = false;
      for (auto &e : rep.entries) {
        bool oob = false;
        for (auto &f : e.findings) oob |= f.kind == "oob_read";
        if (e.function == "pure_region") {
          sawPure = true;
          CHECK(e.setupRegion.declared && e.setupRegion.reused,
                "a region that touches no attacker data is executed once and restored: " << e.setupRegion.refusal);
          CHECK(e.setupRegion.skips > 0, "...and the later runs really did restore it");
          CHECK(oob, "the defect AFTER the region is still found: a checkpoint that loses it is a faster way to report nothing");
        }
        if (e.function == "tainted_region") {
          sawTainted = true;
          CHECK(e.setupRegion.declared && !e.setupRegion.reused,
                "a region that READS the entry's input must be refused, not frozen: freezing hands every later run the first run's input");
          CHECK(oob, "and the defect is still found, because the region simply runs every time");
        }
      }
      bool sawAlloc = false, sawPlain = false;
      for (auto &e : rep.entries) {
        bool nullDeref = false, oob = false;
        for (auto &f : e.findings) { nullDeref |= f.kind == "null_deref"; oob |= f.kind == "oob_read"; }
        // DESIGN.md §22.440: inside a declared region an allocation SUCCEEDS, so the unchecked store is not a
        // null_deref -- and `unguarded_alloc`, the same code with the markers removed, must still report one.
        // Without that control this would pass just as well if the engine had stopped exploring allocation
        // failure everywhere. Both must keep the defect that sits AFTER the region.
        if (e.function == "region_alloc") {
          sawAlloc = true;
          CHECK(e.setupRegion.allocsForced > 0, "the allocation inside the declared region was taken as succeeding");
          CHECK(!nullDeref, "...so the unchecked store in the region is not a null_deref");
          CHECK(oob, "...and the defect after the region is still found");
        }
        if (e.function == "unguarded_alloc") {
          sawPlain = true;
          CHECK(nullDeref, "the CONTROL: the same code without the markers still reports the allocation-failure null_deref");
          CHECK(oob, "...and its defect too");
        }
      }
      CHECK(sawAlloc && sawPlain, "the allocation entries were analysed");
      CHECK(sawPure && sawTainted, "both setup_region.c entries were analysed");

      // DESIGN.md §22.441. The two defects §22.440 fixed were both "the restored state is not what a re-run
      // produces", and both were found by noticing a finding had gone missing -- which only works when there
      // IS a finding to miss. `HLIR_SETUP_VERIFY=1` asks the question directly: run the region again instead
      // of restoring it, and report every cell, object and register that differs. Zero differences is the
      // invariant; the detail lines are printed only when it is broken, so their ABSENCE is the assertion.
      {
        std::string v = run("HLIR_SETUP_VERIFY=1 " + bin + " --entry pure_region --entry region_alloc --runs 60 "
                            "--timeout 60 --format json " + sf, &rc);
        CHECK(has(v, "[setup-verify] 0 difference"), "the verifier ran over the restored region" );
        CHECK(!has(v, "[setup-verify]   "),
              "a restored setup region differs from one that ran again:\n" + v);
      }

      // DESIGN.md §22.441: a --entry that names no function must FAIL, not quietly shrink the scan. The
      // control is the second half: the name that does exist is still refused along with it, so this cannot
      // pass by refusing every multi-entry scan.
      {
        int erc = 0;
        std::string e = run(bin + " --entry pure_region --entry no_such_entry --format json " + sf, &erc);
        CHECK(erc != 0, "a --entry naming no function is an error:\n" + e);
        CHECK(has(e, "no_such_entry"), "...and the message names it:\n" + e);
        CHECK(!has(e, "pure_region\""), "...and nothing was reported for the entries that did resolve");
        int ok = 0;
        std::string g = run(bin + " --entry pure_region --format json " + sf, &ok);
        // Not the exit code: hlir-scan exits non-zero when it FINDS something, and pure_region has a defect
        // after the region. What must differ is that the scan actually produced a report for the entry.
        CHECK(!has(g, "requested entry name(s)") && has(g, "pure_region"),
              "the same scan with only real names still runs and reports:\n" + g);
      }
    }
    // `noreturn` on a function-pointer TYPE (tcpdump's `void NORETURN_FUNCPTR (*ndo_error)(...)`). The control
    // matters more than the subject: `die_plain` is the same code with the attribute removed, and it must still be
    // reported -- otherwise the fix would be silencing guarded accesses in general rather than reading a declaration.
    {
      const std::string nf = HLIR_SCAN_FIXTURE_DIR "/noreturn_funcptr.c";
      CHECK(verdictOf(bin + " --entries all --format json " + nf, "die_noreturn") == "safe_under_assumptions",
            "an indirect call whose TYPE is noreturn ends the path: the guarded access after it is not reached");
      CHECK(verdictOf(bin + " --entries all --format json " + nf, "die_plain") == "bug",
            "the same shape without the attribute: the call returns and the out-of-range access IS reported");
    }
    const std::string rf = HLIR_SCAN_FIXTURE_DIR "/realloc_driver.c";
    CHECK(verdictOf(bin + " --entries all --format json " + rf, "grow") == "safe_under_assumptions", "realloc keeps the contents and frees the old block");
    CHECK(verdictOf(bin + " --entries all --format json " + rf, "grow_bug") == "bug", "freeing the old block after a successful realloc is a double free");
  }

  // ---------------------------------------------------------------- bounded loop unrolling (--loop-bound)
  if (mine()) {
    const std::string lf = HLIR_SCAN_FIXTURE_DIR "/loops_driver.c";
    auto verdicts = [&](const std::string &args) {
      std::map<std::string, std::string> m;
      std::string o = run(bin + " --buf-max 32 --timeout 60 --format json " + args + " " + lf, &rc);
      report::Report r;
      std::string er;
      if (!report::fromJson(o.substr(o.find('{')), r, er)) { m["__error"] = er; return m; }
      for (auto &e : r.entries) {
        m[e.function] = report::verdictName(e.verdict);
        for (auto &i : e.incomplete) if (i.code == "loop_bound") m[e.function + ":cut"] = "yes";
      }
      return m;
    };
    auto b4 = verdicts("--loop-bound 4");
    CHECK(b4["count_a"] == "safe_up_to_loop_bound" && b4["records"] == "safe_up_to_loop_bound" && b4["parse_dec"] == "safe_up_to_loop_bound",
          "a bound of 4 explores everything completely and says so: " << b4["count_a"] << " " << b4["records"] << " " << b4["parse_dec"]);
    CHECK(b4["count_a:cut"] == "yes", "the report lists the loop-bound incompleteness");
    auto deep = verdicts("--loop-bound 4,8,16");
    CHECK(deep["count_a"] == "bug", "iterative deepening finds the bug that needs five iterations (exactly five 'a'): " << deep["count_a"]);
    CHECK(deep["parse_dec"] == "bug", "... and the overflow after ten digits: " << deep["parse_dec"]);
    CHECK(deep["records"] != "bug", "records has no bug at any bound tried: " << deep["records"]);
    auto none = verdicts("");
    CHECK(none["count_a"] != "safe_up_to_loop_bound", "without --loop-bound there is no bounded verdict");
    std::string txt = run(bin + " --buf-max 32 --timeout 60 --loop-bound 4 " + lf, &rc);
    CHECK(has(txt, "safe up to the loop bound") && rc == 0, "the summary counts bounded entries, exit code 0: rc=" << rc);
  }

  // ---------------------------------------------------------------- noreturn declarations and the coverage report
  if (mine()) {
    const std::string nf = HLIR_SCAN_FIXTURE_DIR "/noreturn_driver.c";
    const std::string common = " --entry checked --entry allstop --entry attr --entry plain --format json " + nf;
    const std::string jf = "/tmp/hlir_cov_json." + std::to_string(getpid());
    auto scanJson = [&](const std::string &args) {  // runs hlir-scan with --output and returns the entries by function
      run(bin + " " + args + " --output " + jf);
      report::Report r;
      std::string e;
      std::map<std::string, report::EntryReport> m;
      if (report::fromJson(slurp(jf), r, e)) for (auto &x : r.entries) m[x.function] = x;
      return m;
    };
    // without a declaration `stop` is an opaque call that returns: the code after it is analysed (and the guard looks buggy)
    auto plainRun = scanJson(common);
    CHECK(plainRun["checked"].verdict == report::Verdict::Bug, "without --noreturn the opaque `stop` returns and tab[n] is reached with a bad n");
    // --noreturn: the path ends at the call
    auto nr = scanJson(" --noreturn stop" + common);
    CHECK(nr["checked"].verdict == report::Verdict::SafeUnderAssumptions, "checked is safe once `stop` never returns: " << report::verdictName(nr["checked"].verdict));
    CHECK(nr["checked"].coverage.measured && nr["checked"].coverage.runsTerminated >= 1 && nr["checked"].coverage.runsReturned >= 1, "coverage counts returned and terminated runs");
    CHECK(!nr["checked"].coverage.terminations.empty() && nr["checked"].coverage.terminations[0].by == "stop" && nr["checked"].coverage.terminations[0].function == "checked", "the termination site is reported");
    // every path ends at a noreturn call: nothing after it was analysed, so the verdict is never safe
    CHECK(nr["allstop"].verdict == report::Verdict::Unknown, "allstop: " << report::verdictName(nr["allstop"].verdict));
    bool noRun = false;
    for (auto &i : nr["allstop"].incomplete) noRun |= i.code == "no_run_completed";
    CHECK(noRun, "allstop is incomplete:no_run_completed");
    // a path that ended at a noreturn call is still a real execution: its branches are flipped, so the bug behind `n == 1` is found
    CHECK(nr["attr"].verdict == report::Verdict::Bug, "attr (noreturn attribute in the source; bug only for n == 1): " << report::verdictName(nr["attr"].verdict));
    CHECK(nr["plain"].coverage.blocksVisited == nr["plain"].coverage.blocksReachable && nr["plain"].coverage.runsTerminated == 0, "plain: all blocks entered, no terminations");
    // the text report prints it, and --min-coverage turns a thin exploration into unknown
    std::string t = run(bin + " --noreturn stop --entry checked --jobs 1 --out /tmp/hlir_cov_t." + std::to_string(getpid()) + " " + nf, &rc);
    CHECK(has(t, "cov "), "the summary table shows the coverage:\n" << t);
    auto thin = scanJson(" --noreturn stop --min-coverage 100" + common);
    bool low = false;
    for (auto &i : thin["checked"].incomplete) low |= i.code == "low_coverage";
    CHECK(low && thin["checked"].verdict == report::Verdict::Unknown, "--min-coverage 100 makes the 7/8-block exploration of checked unknown");
    // a ModelDB entry does the same as the flag
    const std::string ny = "/tmp/hlir_cov_nr." + std::to_string(getpid()) + ".yaml";
    std::ofstream(ny) << "models:\n  - function: stop\n    noreturn: true\n";
    auto viaYaml = scanJson(" --models " + ny + common);
    CHECK(viaYaml["checked"].verdict == report::Verdict::SafeUnderAssumptions, "noreturn: true in a ModelDB document");
  }
  // regression: new ModelDB models for strcat/strncat/getline (previously completely unmodelled -- see
  // docs/DESIGN.md's CVE-2016-3186/gif2tiff and CVE-2014-0160/Heartbleed ground-truth write-ups for why this
  // gap mattered). strcat_overflow/safe.c isolate the real overflow math (dstlen+srclen+1 vs the real object
  // size) from the unrelated "synthesized dst isn't guaranteed NUL-terminated" artifact by using a local,
  // explicitly-initialized-empty fixed-size buffer instead of a pointer parameter.
  if (mine()) {
    std::string er;
    const std::string sob = HLIR_SCAN_FIXTURE_DIR "/strcat_overflow.c";
    auto sor = run(bin + " --entries all --format json " + sob, &rc);
    report::Report so;
    CHECK(report::fromJson(sor.substr(sor.find('{')), so, er), "strcat_overflow scan json: " << er);
    CHECK(so.entries.size() == 1 && so.entries[0].verdict == report::Verdict::Bug,
          "strcat into an 8-byte buffer with a 1..256-byte src overflows: " << (so.entries.empty() ? "no entry" : report::verdictName(so.entries[0].verdict)));
    const std::string ssf = HLIR_SCAN_FIXTURE_DIR "/strcat_safe.c";
    auto ssr = run(bin + " --entries all --format json " + ssf, &rc);
    report::Report ss;
    CHECK(report::fromJson(ssr.substr(ssr.find('{')), ss, er), "strcat_safe scan json: " << er);
    CHECK(ss.entries.size() == 1 && ss.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
          "strcat into a 512-byte buffer (room for any synthesized src) is safe: " << (ss.entries.empty() ? "no entry" : report::verdictName(ss.entries[0].verdict)));
    const std::string glf = HLIR_SCAN_FIXTURE_DIR "/getline_bounds.c";
    auto glr = run(bin + " --entries all --format json " + glf, &rc);
    report::Report gl;
    CHECK(report::fromJson(glr.substr(glr.find('{')), gl, er), "getline_bounds scan json: " << er);
    std::map<std::string, report::Verdict> glv;
    for (auto &e : gl.entries) glv[e.function] = e.verdict;
    CHECK(glv.count("consume_safe") && glv["consume_safe"] == report::Verdict::SafeUnderAssumptions,
          "getline: line[r-1] within the model's real allocation is safe: " << (glv.count("consume_safe") ? report::verdictName(glv["consume_safe"]) : "missing"));
    CHECK(glv.count("consume_bug") && glv["consume_bug"] == report::Verdict::Bug,
          "getline: line[5000] past the model's 4096-byte allocation is a bug: " << (glv.count("consume_bug") ? report::verdictName(glv["consume_bug"]) : "missing"));
    // regression: plain `strlen()` used to be a purely declarative ModelDB entry (an opaque, concrete-bytes-only
    // native primitive, invisible to concolic branch-flipping and unsupported by the symbolic engine on symbolic
    // bytes) -- a core.func body (reusing __hlir_strlen's real branch-structured, bounds-checked loop) now takes
    // precedence. Ground-truth find: OpenSSL CVE-2021-3712 (ASN1_STRING not guaranteed NUL-terminated).
    const std::string slf = HLIR_SCAN_FIXTURE_DIR "/strlen_non_nul_buffer.c";
    auto slr = run(bin + " --entries all --format json " + slf, &rc);
    report::Report sl;
    CHECK(report::fromJson(slr.substr(slr.find('{')), sl, er), "strlen_non_nul_buffer scan json: " << er);
    CHECK(sl.entries.size() == 1 && sl.entries[0].verdict == report::Verdict::Bug,
          "strlen() on a from_field-sized buffer with no guaranteed NUL within its length is a bug: " << (sl.entries.empty() ? "no entry" : report::verdictName(sl.entries[0].verdict)));
    // regression: isLenName() didn't recognize the "_max"/"Max" suffix (a buffer's declared capacity, as
    // distinct from its current fill level) -- the top-level length<->buffer relation loop in makeEntry()
    // never tied a synthesized buffer's size to a sibling "*_max" parameter. Ground-truth find: zlib
    // CVE-2022-37434 (gz_header::extra_max never got linked to the synthesized extra buffer's size, so a
    // repro without this fix couldn't cleanly distinguish the vulnerable code from the fixed code).
    const std::string mxf = HLIR_SCAN_FIXTURE_DIR "/maxsuffix_len_relation.c";
    auto mxr = run(bin + " --entries all --format json " + mxf, &rc);
    report::Report mx;
    CHECK(report::fromJson(mxr.substr(mxr.find('{')), mx, er), "maxsuffix_len_relation scan json: " << er);
    CHECK(mx.entries.size() == 1 && mx.entries[0].verdict == report::Verdict::Bug,
          "extra_len far exceeding extra_max (a real buffer of only extra_max bytes) is a bug: " << (mx.entries.empty() ? "no entry" : report::verdictName(mx.entries[0].verdict)));
    const std::string mxff = HLIR_SCAN_FIXTURE_DIR "/maxsuffix_len_relation_fixed.c";
    auto mxfr = run(bin + " --entries all --format json " + mxff, &rc);
    report::Report mxfx;
    CHECK(report::fromJson(mxfr.substr(mxfr.find('{')), mxfx, er), "maxsuffix_len_relation_fixed scan json: " << er);
    CHECK(mxfx.entries.size() == 1 && mxfx.entries[0].verdict == report::Verdict::SafeUnderAssumptions,
          "with the real `len < extra_max` guard, the real zlib fix is safe: " << (mxfx.entries.empty() ? "no entry" : report::verdictName(mxfx.entries[0].verdict)));
  }

  // regression: core.check.field_oob (DESIGN.md P1 gap fix, docs/KNOWN_GAPS_PRIORITIZED.md) -- a new, independent
  // check emitted at `expr.field[idx]` / `expr->field[idx]` subscripts on a fixed-size struct-field array, using
  // that field's own declared length instead of core.check.oob's whole-backing-object size. Ground-truth find:
  // Redis modules/vector-sets/hnsw.c's random_level() (pre-fix, `level` can reach HNSW_MAX_LEVEL itself and
  // `level_queues[level]` overwrites the adjacent `node` field while staying inside the whole InsertContext
  // allocation -- core.check.oob alone cannot see this; neither can native ASan, whose heap redzone sits outside
  // the allocation, not between fields within it).
  if (mine()) {
    const std::string fof = HLIR_SCAN_FIXTURE_DIR "/field_oob_driver.c";
    auto fofr = run(bin + " --entries all --format json " + fof, &rc);
    report::Report fo;
    std::string er;
    CHECK(report::fromJson(fofr.substr(fofr.find('{')), fo, er), "field_oob_driver scan json: " << er);
    std::map<std::string, report::Verdict> fv;
    std::map<std::string, bool> hasFieldOob;
    for (auto &e : fo.entries) {
      fv[e.function] = e.verdict;
      bool fob = false;
      for (auto &f : e.findings) fob |= f.kind == "field_oob";
      hasFieldOob[e.function] = fob;
    }
    CHECK(fv.count("bug_field_write") && fv["bug_field_write"] == report::Verdict::Bug && hasFieldOob["bug_field_write"],
          "bug_field_write: unchecked idx into a 4-element field is a field_oob bug: "
              << (fv.count("bug_field_write") ? report::verdictName(fv["bug_field_write"]) : "missing"));
    CHECK(fv.count("safe_field_write") && fv["safe_field_write"] == report::Verdict::SafeUnderAssumptions,
          "safe_field_write: the `idx >= N_SLOTS` guard makes it safe: "
              << (fv.count("safe_field_write") ? report::verdictName(fv["safe_field_write"]) : "missing"));
    CHECK(fv.count("fam_write") && !hasFieldOob["fam_write"],
          "fam_write: a flexible-array-member field (the last field of its struct) must not be flagged field_oob");
    CHECK(fv.count("union_write") && !hasFieldOob["union_write"],
          "union_write: a union member field must not be flagged field_oob");
    // the historical-bug closure: random_level_raw's threshold_hits-driven loop can make `level` reach
    // HNSW_MAX_LEVEL itself (pre-fix); hnsw_insert_bug then indexes level_queues[] with it, hnsw_insert_fixed
    // clamps first -- a clean vulnerable/fixed differential, exercised through the default symbolic/concolic
    // engine (not a hand-fed concrete harness), closing the loop on the real finding that motivated this feature.
    CHECK(fv.count("hnsw_insert_bug") && fv["hnsw_insert_bug"] == report::Verdict::Bug && hasFieldOob["hnsw_insert_bug"],
          "hnsw_insert_bug: random_level_raw() reaching HNSW_MAX_LEVEL overflows level_queues[] into `node`, a field_oob bug: "
              << (fv.count("hnsw_insert_bug") ? report::verdictName(fv["hnsw_insert_bug"]) : "missing"));
    CHECK(fv.count("hnsw_insert_fixed") && fv["hnsw_insert_fixed"] == report::Verdict::SafeUnderAssumptions,
          "hnsw_insert_fixed: random_level_fixed()'s HNSW_MAX_LEVEL-1 clamp makes it safe: "
              << (fv.count("hnsw_insert_fixed") ? report::verdictName(fv["hnsw_insert_fixed"]) : "missing"));
    CHECK(fv.count("byte_class") && !hasFieldOob["byte_class"],
          "byte_class: an unsigned char index into a 256-entry field cannot be out of bounds");
    CHECK(fv.count("byte_class_signed") && hasFieldOob["byte_class_signed"],
          "byte_class_signed: a negative signed char index is still a field_oob");
    CHECK(fv.count("sip_room") && !hasFieldOob["sip_room"],
          "sip_room: &buf[sizeof buf] is the valid one-past-the-end pointer, not a field_oob");
    CHECK(fv.count("sip_past") && hasFieldOob["sip_past"],
          "sip_past: &buf[i] for i beyond one past the end is still a field_oob");
  }

  // regression: pointer == / != 0 (and bare `if (p)` / `if (!p)`) now compare the full pointer value (object and
  // offset), not just core.is_null's object-id-only check (DESIGN.md P1 gap fix, docs/KNOWN_GAPS_PRIORITIZED.md).
  // A pointer born from an int-to-pointer cast of a non-recoverable value keeps object 0 with its real, possibly
  // nonzero, offset; the old shortcut treated that as indistinguishable from a true null, making any
  // `if (ptr != NULL) *ptr = ...;` guard look permanently false and hiding the dereference. Ground-truth find:
  // libxslt CVE-2025-7424 (`xmlNode.psvi` sentinel ID written by generate-id(), later dereferenced through
  // transform.c's `cur->psvi != NULL` guard).
  if (mine()) {
    const std::string pcf = HLIR_SCAN_FIXTURE_DIR "/ptr_cmp_int2ptr_driver.c";
    auto pcfr = run(bin + " --entries all --include-noarg --format json " + pcf, &rc);
    report::Report pc;
    std::string er;
    CHECK(report::fromJson(pcfr.substr(pcfr.find('{')), pc, er), "ptr_cmp_int2ptr_driver scan json: " << er);
    std::map<std::string, report::Verdict> pv;
    std::map<std::string, bool> hasNullDeref;
    for (auto &e : pc.entries) {
      pv[e.function] = e.verdict;
      bool nd = false;
      for (auto &f : e.findings) nd |= f.kind == "null_deref";
      hasNullDeref[e.function] = nd;
    }
    CHECK(pv.count("bug_int2ptr_deref") && pv["bug_int2ptr_deref"] == report::Verdict::Bug && hasNullDeref["bug_int2ptr_deref"],
          "bug_int2ptr_deref: `p != 0` must be reachable for a nonzero int-cast pointer, exposing the dereference: "
              << (pv.count("bug_int2ptr_deref") ? report::verdictName(pv["bug_int2ptr_deref"]) : "missing"));
    CHECK(pv.count("safe_int2ptr_noderef") && pv["safe_int2ptr_noderef"] == report::Verdict::SafeUnderAssumptions,
          "safe_int2ptr_noderef: same compare shape but never dereferenced stays safe: "
              << (pv.count("safe_int2ptr_noderef") ? report::verdictName(pv["safe_int2ptr_noderef"]) : "missing"));
    CHECK(pv.count("bug_int2ptr_bare_truthy") && pv["bug_int2ptr_bare_truthy"] == report::Verdict::Bug && hasNullDeref["bug_int2ptr_bare_truthy"],
          "bug_int2ptr_bare_truthy: bare `if (p)` goes through FnGen::toBool, the same fix must apply there: "
              << (pv.count("bug_int2ptr_bare_truthy") ? report::verdictName(pv["bug_int2ptr_bare_truthy"]) : "missing"));
    CHECK(pv.count("bug_int2ptr_lnot") && pv["bug_int2ptr_lnot"] == report::Verdict::Bug && hasNullDeref["bug_int2ptr_lnot"],
          "bug_int2ptr_lnot: `if (!p) return;` falling through must be reachable for nonzero raw: "
              << (pv.count("bug_int2ptr_lnot") ? report::verdictName(pv["bug_int2ptr_lnot"]) : "missing"));
    CHECK(pv.count("safe_malloc_null_check") && pv["safe_malloc_null_check"] == report::Verdict::SafeUnderAssumptions,
          "safe_malloc_null_check: the ordinary malloc-fail idiom (real allocation, offset always 0) must be unaffected: "
              << (pv.count("safe_malloc_null_check") ? report::verdictName(pv["safe_malloc_null_check"]) : "missing"));
    CHECK(pv.count("safe_real_null_is_null") && pv["safe_real_null_is_null"] == report::Verdict::SafeUnderAssumptions,
          "safe_real_null_is_null: a true null pointer must still compare equal to 0 (no over-correction): "
              << (pv.count("safe_real_null_is_null") ? report::verdictName(pv["safe_real_null_is_null"]) : "missing"));
    // the historical-bug closure: the CVE-2025-7424 shape collapsed into one function, exercised through the
    // default symbolic/concolic engine (not a hand-fed concrete harness), closing the loop on the real finding
    // that motivated this fix.
    CHECK(pv.count("bug_sentinel_as_ptr_deref") && pv["bug_sentinel_as_ptr_deref"] == report::Verdict::Bug && hasNullDeref["bug_sentinel_as_ptr_deref"],
          "bug_sentinel_as_ptr_deref: the CVE-2025-7424 shape -- `cur->extra != 0` guarding a dereference of a sentinel int -- is a reachable null_deref bug: "
              << (pv.count("bug_sentinel_as_ptr_deref") ? report::verdictName(pv["bug_sentinel_as_ptr_deref"]) : "missing"));
    CHECK(pv.count("fixed_sentinel_never_dereferenced") && pv["fixed_sentinel_never_dereferenced"] == report::Verdict::SafeUnderAssumptions,
          "fixed_sentinel_never_dereferenced: same shape without the dereference stays safe: "
              << (pv.count("fixed_sentinel_never_dereferenced") ? report::verdictName(pv["fixed_sentinel_never_dereferenced"]) : "missing"));
  }

  // regression: declarative ModelDB source:/copy:/fill: effects (recv/read/getenv/strcpy/memset for modules that
  // only declare them) are now bounds-checked against the destination (and, for copy:, the source) object's
  // declared size, the same way a hand-written core.func body (memcpy, fgets, ...) always has been -- previously
  // Memory::bulk()/wr() wrote with no check at all (docs/KNOWN_GAPS_PRIORITIZED.md's "curl CVE-2019-5436" P1 gap:
  // `malloc(10)` then `recv(fd, buf, 500, 0)` used to report safe_under_assumptions regardless of the destination
  // size). `recv` is declared-only in the fixture (no body), so the real ModelDB `source:` entry in
  // models/libc.yaml is exercised, not a hand-written core.func, and its overflow is still classified `oob_write`
  // (Memory::bulk()/wr()'s own bounds check, no separate pointer-arithmetic check). `strcpy` itself gained a real
  // `core.func` body (docs/DESIGN.md's cJSON CVE-2024-31755 ground-truth write-up: the declarative `copy:` size
  // mechanism this fixture originally probed for strcpy went through Memory.h's `cstrlen()` -- an opaque,
  // concrete-bytes-only native primitive the symbolic engine can't evaluate on genuinely symbolic bytes at all --
  // same gap class as plain `strlen()` already fixed the same way), so its overflow is now classified
  // `ptr_arith_oob` instead, same as memcpy/strcat/strncat's existing hand-written bodies (all check
  // `core.check.ptr_arith` before `core.check.oob`, so a destination overflow of any size always trips the
  // former first) -- not a detection regression, the bug is still caught and replay-confirmed, just reclassified
  // consistently with every other hand-written copy-style model in this codebase.
  if (mine()) {
    const std::string dof = HLIR_SCAN_FIXTURE_DIR "/decl_oob_driver.c";
    auto dofr = run(bin + " --entries all --include-noarg --format json " + dof, &rc);
    report::Report dor;
    std::string er;
    CHECK(report::fromJson(dofr.substr(dofr.find('{')), dor, er), "decl_oob_driver scan json: " << er);
    std::map<std::string, report::Verdict> dv;
    std::map<std::string, bool> hasOobWrite;
    std::map<std::string, bool> hasPtrArithOob;
    for (auto &e : dor.entries) {
      dv[e.function] = e.verdict;
      bool w = false, p = false;
      for (auto &f : e.findings) { w |= f.kind == "oob_write"; p |= f.kind == "ptr_arith_oob"; }
      hasOobWrite[e.function] = w;
      hasPtrArithOob[e.function] = p;
    }
    CHECK(dv.count("bug_recv_oob") && dv["bug_recv_oob"] == report::Verdict::Bug && hasOobWrite["bug_recv_oob"],
          "bug_recv_oob: recv()'s source: effect writing 500 bytes into a 10-byte stack buffer is an oob_write: "
              << (dv.count("bug_recv_oob") ? report::verdictName(dv["bug_recv_oob"]) : "missing"));
    CHECK(dv.count("safe_recv_fits") && dv["safe_recv_fits"] == report::Verdict::SafeUnderAssumptions,
          "safe_recv_fits: recv() writing 8 bytes into a 16-byte buffer is safe: "
              << (dv.count("safe_recv_fits") ? report::verdictName(dv["safe_recv_fits"]) : "missing"));
    CHECK(dv.count("bug_strcpy_oob") && dv["bug_strcpy_oob"] == report::Verdict::Bug && hasPtrArithOob["bug_strcpy_oob"],
          "bug_strcpy_oob: strcpy()'s real core.func body copying a 43-byte literal into a 4-byte buffer is a ptr_arith_oob: "
              << (dv.count("bug_strcpy_oob") ? report::verdictName(dv["bug_strcpy_oob"]) : "missing"));
    CHECK(dv.count("safe_strcpy_fits") && dv["safe_strcpy_fits"] == report::Verdict::SafeUnderAssumptions,
          "safe_strcpy_fits: strcpy() of a short literal into a large-enough buffer is safe: "
              << (dv.count("safe_strcpy_fits") ? report::verdictName(dv["safe_strcpy_fits"]) : "missing"));

    // the copy: effect's *source*-side bound: strcpy's size is always strlen(src)+1 (never larger than the real
    // source), so it alone cannot reach a source-side out-of-bounds read -- a test-only ModelDB entry with a
    // size independent of the source's real length exercises that side directly.
    const std::string cy = "/tmp/hlir_decl_copy_src." + std::to_string(getpid()) + ".yaml";
    std::ofstream(cy) << "models:\n  - function: __test_decl_copy\n    copy: [ { dst: arg0, src: arg1, size: arg2 } ]\n";
    auto cofr = run(bin + " --entries all --include-noarg --models " + cy + " --format json " + dof, &rc);
    report::Report cor;
    CHECK(report::fromJson(cofr.substr(cofr.find('{')), cor, er), "decl_oob_driver (copy src) scan json: " << er);
    std::map<std::string, report::Verdict> cv;
    std::map<std::string, bool> hasOobRead;
    for (auto &e : cor.entries) {
      cv[e.function] = e.verdict;
      bool r = false;
      for (auto &f : e.findings) r |= f.kind == "oob_read";
      hasOobRead[e.function] = r;
    }
    CHECK(cv.count("bug_decl_copy_src_oob") && cv["bug_decl_copy_src_oob"] == report::Verdict::Bug && hasOobRead["bug_decl_copy_src_oob"],
          "bug_decl_copy_src_oob: a copy: size (50) exceeding the real 4-byte source object is an oob_read: "
              << (cv.count("bug_decl_copy_src_oob") ? report::verdictName(cv["bug_decl_copy_src_oob"]) : "missing"));
    CHECK(cv.count("safe_decl_copy_src_fits") && cv["safe_decl_copy_src_fits"] == report::Verdict::SafeUnderAssumptions,
          "safe_decl_copy_src_fits: a copy: size (4) that fits the real source and destination is safe: "
              << (cv.count("safe_decl_copy_src_fits") ? report::verdictName(cv["safe_decl_copy_src_fits"]) : "missing"));
    std::remove(cy.c_str());
  }

  // ---------------------------------------------------------------- externally_mutable (double-fetch/TOCTOU)
  if (mine()) {
    // --spec-dir looks up exactly DIR/<function>.yaml, so the "default-off" control and the "declared" case need
    // two separate directories (both define a spec for the same function consume_toctou).
    const std::string ef = HLIR_SCAN_FIXTURE_DIR "/extmut_driver.c";
    std::string edSafe = HLIR_SCAN_FIXTURE_DIR "/../tmp_extmut_specs_safe", edBug = HLIR_SCAN_FIXTURE_DIR "/../tmp_extmut_specs_bug",
                edPtr = HLIR_SCAN_FIXTURE_DIR "/../tmp_extmut_specs_ptr";
    run("mkdir -p " + edSafe + " " + edBug + " " + edPtr);
    // control: h is NOT declared externally_mutable -- default-off, must behave exactly as before this feature
    // existed (the validating read and the using read are the same cached value, so the memcpy can never overflow).
    std::ofstream(edSafe + "/consume_toctou.yaml")
        << "taint_entries:\n  - function: consume_toctou\n    label: network\n    params:\n"
           "      h: { taint: pointee, kind: buffer, size: { min: 68, max: 68 } }\n";
    // h declared externally_mutable: true -- the validating read and the using read may now disagree, so the
    // memcpy can overflow the 16-byte stack buffer: a real double-fetch bug HLIR's deterministic memory model
    // otherwise cannot express.
    std::ofstream(edBug + "/consume_toctou.yaml")
        << "taint_entries:\n  - function: consume_toctou\n    label: network\n    params:\n"
           "      h: { taint: pointee, kind: buffer, size: { min: 68, max: 68 }, externally_mutable: true }\n";
    // pointer-typed loads against an externally-mutable object must keep the ordinary cached-load behaviour
    // (excluded from this MVP): two loads of the same pointer field must still observe the same pointer.
    std::ofstream(edPtr + "/consume_ptr_load.yaml")
        << "taint_entries:\n  - function: consume_ptr_load\n    label: network\n    params:\n"
           "      h:\n        taint: pointee\n        kind: buffer\n        size: { min: 8, max: 8 }\n"
           "        externally_mutable: true\n        fields:\n"
           "          - { offset: 0, kind: buffer, taint: pointee, size: { min: 68, max: 68 } }\n";

    std::string outCtl = run(bin + " --entry consume_toctou --spec-dir " + edSafe + " --format json " + ef, &rc);
    std::string outBug = run(bin + " --entry consume_toctou --spec-dir " + edBug + " --format json " + ef, &rc);
    std::string outPtr = run(bin + " --entry consume_ptr_load --spec-dir " + edPtr + " --format json " + ef, &rc);
    report::Report repCtl, repBug, repPtr;
    std::string eC, eB, eP;
    CHECK(report::fromJson(outCtl.substr(outCtl.find('{')), repCtl, eC), "extmut default-off scan json: " << eC << "\n" << outCtl);
    CHECK(report::fromJson(outBug.substr(outBug.find('{')), repBug, eB), "extmut declared scan json: " << eB << "\n" << outBug);
    CHECK(report::fromJson(outPtr.substr(outPtr.find('{')), repPtr, eP), "extmut ptr-load scan json: " << eP << "\n" << outPtr);
    auto vem = [&](const report::Report &rp, const std::string &fn) {
      for (auto &e : rp.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(vem(repCtl, "consume_toctou") == "safe_under_assumptions",
          "default-off (no externally_mutable): the two reads are the same cached value, memcpy cannot overflow: " << vem(repCtl, "consume_toctou"));
    CHECK(vem(repBug, "consume_toctou") == "bug",
          "externally_mutable: true: the two reads may disagree, the memcpy can overflow the 16-byte buffer: " << vem(repBug, "consume_toctou"));
    bool oobConfirmed = false;
    for (auto &e : repBug.entries)
      if (e.function == "consume_toctou")
        for (auto &f : e.findings) oobConfirmed |= f.kind == "oob_write" && f.replay == report::ReplayStatus::Confirmed;
    CHECK(oobConfirmed, "consume_toctou (externally_mutable): the double-fetch memcpy overflow is replay-confirmed oob_write");
    CHECK(vem(repPtr, "consume_ptr_load") == "safe_under_assumptions",
          "pointer-typed loads against an externally_mutable object are excluded from this MVP (unaffected, still cached): " << vem(repPtr, "consume_ptr_load"));
    run("rm -rf " + edSafe + " " + edBug + " " + edPtr);
  }

  // ---------------------------------------------------------------- @snprintf's return value: models/libc.core
  // used to hardcode it to 0; it's now a bounded tainted nondet (docs/KNOWN_GAPS_PRIORITIZED.md, docs/DESIGN.md
  // Sec.22.205/22.298), modelling glibc's real "length that would have been written, independent of n" semantics.
  // snprintf_chain_oob.c mirrors CVE-2017-7376's real mechanism: `p += snprintf(p, remaining, ...)` chained calls
  // advance a write pointer past a small stack buffer using the (model-supplied) return values, and the last call's
  // unconditional core.check.oob on its (now out-of-bounds) %buf argument is what catches the resulting oob_write --
  // the fix does not need to model how many bytes were actually written, only that the return value can exceed n.
  if (mine()) {
    const std::string sp = HLIR_SCAN_FIXTURE_DIR "/snprintf_chain_oob.c";
    std::string out = run(bin + " --entries all --include-noarg --timeout 30 --format json " + sp, &rc);
    report::Report r;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), r, er), "snprintf_chain_oob scan json: " << er);
    auto verdictOf = [&](const report::Report &rp, const std::string &fn) {
      for (auto &e : rp.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(verdictOf(r, "consume") == "bug",
          "chained p += snprintf(...) can now drive p out of bounds: " << verdictOf(r, "consume"));
    bool oobConfirmed = false;
    for (auto &e : r.entries)
      if (e.function == "consume")
        for (auto &f : e.findings) oobConfirmed |= f.kind == "oob_write" && f.replay == report::ReplayStatus::Confirmed;
    CHECK(oobConfirmed, "the final snprintf's out-of-bounds write through the advanced p is replay-confirmed oob_write");
    // The other direction, and the one DESIGN.md Sec.22.439 adds: with the format and every argument concrete the
    // engine must say the REAL length. `use_folded` advances p by exactly 3 and has no defect; while the return
    // was a nondet up to 64KiB it had one, and it was the model's, not the program's.
    CHECK(verdictOf(r, "use_folded") == "safe_under_assumptions",
          "a fully concrete snprintf chain advances p by the real length, so there is nothing to report: "
              << verdictOf(r, "use_folded"));
  }

  // ---------------------------------------------------------------- a single-point taint:value,range:[N,N]
  // scalar param is now a real constant term (InitGen.cpp), not a free variable + equality constraint, so the
  // SMT term library's existing constant folding (Term.cpp's foldConst) carries it through the loop's
  // arithmetic automatically and TaintDomain::decide() (TaintDomain.h) skips recording an already-constant
  // condition as a flippable branch decision. deep_loop_taint_scalar.c mirrors the brotli CVE-2026-111497
  // investigation's final bottleneck (docs/DESIGN.md Sec.22.301-307): a 2,000,000-iteration loop whose trip
  // count is a tainted-but-single-point-pinned scalar, gating a real 1-byte OOB write. Before this fix it was
  // permanently `unknown`/time-budget-exhausted (Sec.22.303/304; a log-sampling candidate fix attempt in
  // Sec.22.305 caused real regressions and was reverted). Needs a generous --max-steps (~33 interpreter
  // steps/loop iteration) and wall-clock budget: this one case alone takes a few minutes, unlike the rest of
  // this suite -- faithful to the actual investigated scale, not scaled down for speed.
  if (mine()) {
    const std::string dl = HLIR_SCAN_FIXTURE_DIR "/deep_loop_taint_scalar.c";
    const std::string sd = HLIR_SCAN_FIXTURE_DIR "/deep_loop_taint_scalar_spec";
    std::string out = run(bin + " --entry consume --spec-dir " + sd + " --timeout 280 --max-steps 90000000 --format json " + dl, &rc);
    report::Report r;
    std::string er;
    CHECK(report::fromJson(out.substr(out.find('{')), r, er), "deep_loop_taint_scalar scan json: " << er);
    auto verdictOf = [&](const report::Report &rp, const std::string &fn) {
      for (auto &e : rp.entries) if (e.function == fn) return std::string(report::verdictName(e.verdict));
      return std::string("missing");
    };
    CHECK(verdictOf(r, "consume") == "bug",
          "a single-point-pinned tainted trip count no longer stalls the loop: " << verdictOf(r, "consume"));
    bool oobConfirmed = false, noIncomplete = true;
    for (auto &e : r.entries)
      if (e.function == "consume") {
        noIncomplete = e.incomplete.empty();
        for (auto &f : e.findings) oobConfirmed |= f.kind == "oob_write" && f.replay == report::ReplayStatus::Confirmed;
      }
    CHECK(oobConfirmed, "the 2,000,000-iteration loop's gated out-of-bounds write is replay-confirmed oob_write");
    CHECK(noIncomplete, "the verdict is based on a fully completed run, not cut short by a budget");
  }

  // ---------------------------------------------------------------- the SYMBOLIC engine's replay (§22.419).
  // Pipeline.cpp replays symbolic findings itself, separately from Taint.cpp's concolic replay, and it used to
  // do so with a DEFAULT RunConfig: `models == nullptr`, so the first call to a bodyless function ended the run
  // as Unsupported and no symbolic finding whose path touched a ModelDB model could ever be confirmed. Until
  // this block there was not one assertion in the whole suite about `engine == "symbolic"`, which is why
  // tcpdump CVE-2017-12988 was lost to it in a real scan and nothing here went red.
  if (mine()) {
    const std::string sf = HLIR_SCAN_FIXTURE_DIR "/symreplay.c";
    const std::string sj = "/tmp/hlir_symreplay." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry sym_replay --runs 3000 --timeout 90 --format json --output " + sj +
                              " " + sf, &rc);
    std::string js = slurp(sj);
    std::remove(sj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "symreplay json: " << e << " / " << out);
    bool symConfirmed = false, symUnsupported = false;
    std::string symSeen;
    for (auto &er : r.entries)
      for (auto &f : er.findings) {
        if (f.engine != "symbolic") continue;
        symSeen += " " + f.kind + "@" + std::to_string(f.loc.line) + "(" + report::replayStatusName(f.replay) + ")";
        symConfirmed |= f.replay == report::ReplayStatus::Confirmed;
        symUnsupported |= has(f.unconfirmedDetail, "unsupported");
      }
    // The fixture is built so the symbolic engine is the one that finds the pointer defect, and so that
    // `printf` -- a ModelDB model, which is also what tcpdump's ND_PRINT lowers to -- sits on the path to it.
    // A linked body such as memcpy or strtol would NOT exercise this: the replay never needs a ModelProvider
    // for those, and the first version of this fixture passed on the broken binary for exactly that reason.
    CHECK(symConfirmed, "a symbolic-engine finding whose path crosses a ModelDB model is replay-confirmed:"
                            << (symSeen.empty() ? std::string(" no symbolic findings at all") : symSeen));
    CHECK(!symUnsupported, "...and no symbolic replay dies as `unsupported`, which is what a replay with no "
                           "ModelDB does on its first bodyless call:" << symSeen);
  }

  // ---------------------------------------------------------------- the witness has to be REBUILDABLE (§22.417).
  // A `replay: confirmed` finding is evidence only if someone other than the engine can reproduce it. Two
  // separate defects broke that on the same day: the byte list was capped at 16 with a "(+N more)" tail, and
  // the symbolic engine's parameters were looked up under the wrong names so the object size printed blank and
  // the scalars came out as anonymous `nondet` rows. tcpdump CVE-2017-12902's native ASan step was blocked by
  // both. Nothing asserted on witness CONTENT before this block -- only on field presence.
  if (mine()) {
    const std::string wf = HLIR_SCAN_FIXTURE_DIR "/witness.c";
    const std::string wj = "/tmp/hlir_witness." + std::to_string(getpid()) + ".json";
    int rc = 0;
    std::string out = run(bin + " --entry witness_scan --runs 4000 --timeout 90 --buf-max 32 --format json "
                                "--output " + wj + " " + wf, &rc);
    std::string js = slurp(wj);
    std::remove(wj.c_str());
    report::Report r;
    std::string e;
    CHECK(!js.empty() && report::fromJson(js.substr(js.find('{')), r, e), "witness json: " << e << " / " << out);
    const report::Finding *oob = nullptr;
    for (auto &er : r.entries)
      for (auto &f : er.findings)
        if (f.kind == "oob_read" && !f.warning) oob = &f;
    CHECK(oob, "the `<=` scan loop's one-past read is a finding: " << out);
    if (oob) {
      CHECK(oob->replay == report::ReplayStatus::Confirmed, "...and it is replay-confirmed");
      std::string bytes, scalars;
      for (auto &w : oob->witness) {
        if (w.note == "buffer" || w.note == "cstring") bytes = w.value;
        else scalars += " " + w.name + ":" + w.note;
      }
      // Reaching the defect needs all 24 copied bytes non-zero, so a renderer capped at 16 cannot print it.
      unsigned n = 0;
      for (size_t i = bytes.find('['); i != std::string::npos; i = bytes.find('[', i + 1)) ++n;
      CHECK(n >= 24, "every non-zero byte of the witness is printed, not a 16-byte prefix (got " << n << "): " << bytes);
      CHECK(!has(bytes, "more)"), "...and nothing was elided: " << bytes);
      CHECK(!has(bytes, "object of  bytes"), "...and the object's size is printed, not blank: " << bytes);
      // The scalar must appear under the PARAMETER's name and C type. Under the symbolic engine's `nd.<base>`
      // spelling these used to fall through to the anonymous "nondet" list, which is unusable for a reproducer.
      CHECK(has(scalars, " len:"), "the entry's scalar parameter is named and typed in the witness, not an "
                                   "anonymous nondet row:" << scalars);
    }
  }

  std::cout << "scan_tests" << (g_nshard > 1 ? " [shard " + std::to_string(g_shard) + "/" + std::to_string(g_nshard) + "]" : "")
            << ": " << g_pass << " passed, " << g_fail << " failed\n";
  return g_fail ? 1 : 0;
}

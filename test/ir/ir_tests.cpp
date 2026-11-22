// Tests for the `ir` module: builder API, parser/printer round trip, verifier, and golden files in this directory.
//   *.core with a first-line comment `// ERROR: <substring>` must fail (parse or verify) with that message.
//   `// FLAGS: coverage` enables the UB-check coverage rule. All other files must round-trip and verify.
#include <dirent.h>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/ir/Parser.h"
#include "hlir/ir/Printer.h"
#include "hlir/ir/Verifier.h"

using namespace hlir;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                         \
  do {                                                                           \
    if (cond) ++g_pass;                                                          \
    else { ++g_fail; std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static std::string slurp(const std::string &p) {
  std::ifstream in(p);
  std::stringstream ss;
  ss << in.rdbuf();
  return ss.str();
}

// ---------------------------------------------------------------- builder API
static void testBuilder() {
  Module m;
  Context &c = m.ctx;
  Function *f = m.addFunction("f", {c.intTy(32)}, c.intTy(32));
  Builder b(m);
  b.setInsertionPoint(f->entry());
  Value *zero = b.constInt(c.intTy(32), 0);
  Value *neg = b.icmp("slt", f->entry()->args[0].get(), zero);
  Block *t = f->addBlock("t"), *e = f->addBlock("e");
  b.condBr(neg, t, {}, e, {});
  b.setInsertionPoint(t);
  b.ret(b.constInt(c.intTy(32), -1));
  b.setInsertionPoint(e);
  b.ret(zero);
  Diagnostics d;
  CHECK(verifyModule(m, {}, d), "builder-made module must verify: " << d.str());

  // interning
  CHECK(c.intTy(32) == c.intTy(32), "int types are interned");
  CHECK(c.intTy(32) != c.intTy(64), "distinct widths are distinct types");

  // printing is stable and parses back
  std::string t1 = moduleToString(m);
  Diagnostics d2;
  auto m2 = parseModule(t1, "builder", d2);
  CHECK(m2 != nullptr, "printed builder module must parse: " << d2.str());
  if (m2) CHECK(moduleToString(*m2) == t1, "print(parse(print(m))) == print(m)");
}

static void testVerifierCatches() {
  Module m;
  Context &c = m.ctx;
  Function *f = m.addFunction("g", {}, c.intTy(32));
  Builder b(m);
  b.setInsertionPoint(f->entry());
  Value *a = b.constInt(c.intTy(32), 1);
  Value *w = b.constInt(c.intTy(64), 1);
  b.binop(Opc::Add, a, w);  // type mismatch
  b.ret(a);
  Diagnostics d;
  CHECK(!verifyModule(m, {}, d), "type mismatch must be rejected");
}

// ---------------------------------------------------------------- golden files
static std::string firstLineDirective(const std::string &text, const std::string &key) {
  std::istringstream in(text);
  std::string line;
  while (std::getline(in, line)) {
    auto p = line.find("// " + key + ":");
    if (p != std::string::npos) {
      std::string v = line.substr(p + key.size() + 4);
      while (!v.empty() && (v.front() == ' ')) v.erase(v.begin());
      while (!v.empty() && (v.back() == '\r' || v.back() == ' ')) v.pop_back();
      return v;
    }
    if (line.rfind("//", 0) != 0 && !line.empty()) break;
  }
  return "";
}

static void runGolden(const std::string &path, const std::string &name) {
  std::string text = slurp(path);
  std::string expectErr = firstLineDirective(text, "ERROR");
  std::string flags = firstLineDirective(text, "FLAGS");
  VerifyOptions vo;
  vo.checkCoverage = flags.find("coverage") != std::string::npos;

  Diagnostics d;
  auto mod = parseModule(text, name, d);
  bool ok = mod != nullptr;
  if (ok) ok = verifyModule(*mod, vo, d);

  if (!expectErr.empty()) {
    CHECK(!ok, name << ": expected failure '" << expectErr << "' but module was accepted");
    CHECK(d.str().find(expectErr) != std::string::npos, name << ": expected error containing '" << expectErr << "', got:\n" << d.str());
    return;
  }
  CHECK(ok, name << ": unexpected diagnostics:\n" << d.str());
  if (!ok) return;
  std::string p1 = moduleToString(*mod);
  Diagnostics d2;
  auto m2 = parseModule(p1, name + " (reprint)", d2);
  CHECK(m2 != nullptr, name << ": reprinted text does not parse: " << d2.str() << "\n" << p1);
  if (!m2) return;
  CHECK(moduleToString(*m2) == p1, name << ": round trip is not a fixed point");
  Diagnostics d3;
  CHECK(verifyModule(*m2, vo, d3), name << ": reprinted module does not verify: " << d3.str());
}

int main() {
  testBuilder();
  testVerifierCatches();

  std::vector<std::string> files;
  if (DIR *dir = opendir(HLIR_TEST_DIR)) {
    while (auto *e = readdir(dir)) {
      std::string n = e->d_name;
      if (n.size() > 5 && n.substr(n.size() - 5) == ".core") files.push_back(n);
    }
    closedir(dir);
  }
  std::sort(files.begin(), files.end());
  for (auto &n : files) runGolden(std::string(HLIR_TEST_DIR) + "/" + n, n);
  std::cout << "golden files: " << files.size() << ", checks passed: " << g_pass << ", failed: " << g_fail << "\n";
  return g_fail ? 1 : 0;
}

// Detection / false-positive rates on the generated CWE-style corpus (scripts/gen_corpus.py).
// A finding only counts when the concrete interpreter reproduces it (replay), as in the real pipeline.
#include <dirent.h>

#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/ir/Parser.h"
#include "hlir/ir/Verifier.h"
#include "hlir/semantics/Interpreter.h"
#include "hlir/semantics/Symbolic.h"

using namespace hlir;

static std::string slurp(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }

int main() {
  auto z3 = smt::makeZ3ProcessSolver("z3", 20000);
  if (!z3) { std::cout << "z3 not available: corpus tests skipped\n"; return 0; }
  std::vector<std::string> files;
  if (DIR *d = opendir(HLIR_CORPUS_DIR)) {
    while (auto *e = readdir(d)) {
      std::string n = e->d_name;
      if (n.size() > 5 && n.substr(n.size() - 5) == ".core") files.push_back(n);
    }
    closedir(d);
  }
  std::sort(files.begin(), files.end());
  int bad = 0, detected = 0, good = 0, falsePos = 0, errors = 0, unconfirmed = 0;
  for (auto &fn : files) {
    std::string text = slurp(std::string(HLIR_CORPUS_DIR) + "/" + fn);
    std::string expect, entry = "f";
    bool libc = false;
    std::istringstream ls(text);
    for (std::string line; std::getline(ls, line);) {
      if (line.rfind("// EXPECT: ", 0) == 0) expect = line.substr(11);
      else if (line.rfind("// ENTRY: ", 0) == 0) entry = line.substr(10);
      else if (line == "// LIBC") libc = true;
    }
    if (libc) text += "\n" + slurp(HLIR_MODELS_DIR "/libc.core");
    Diagnostics d;
    auto mod = parseModule(text, fn, d);
    if (!mod || d.hasErrors() || !verifyModule(*mod, {}, d)) { std::cerr << fn << ": cannot load\n" << d.str(); ++errors; continue; }
    smt::TermManager tm;
    SymbolicExecutor ex(*mod, tm, *z3);
    SymConfig cfg;
    cfg.maxPaths = 500;
    SymResult r = ex.run(entry, {}, cfg);
    Interpreter in(*mod);
    std::vector<std::string> confirmed;
    for (auto &f : r.findings) {
      SeqEnv env(f.nondets);
      RunResult rr = in.run(entry, f.args, env);
      // Same rule as lib/semantics/Taint.cpp (DESIGN.md §22.418): a UB the engine walks past is recorded in
      // `ubContinued` instead of ending the run. See ENGINE_LIMITATIONS.md §7.12.
      bool ok = f.ub ? ((rr.status == RunStatus::UB && rr.ub && rr.ub->kind == f.ub->kind) ||
                        std::any_of(rr.ubContinued.begin(), rr.ubContinued.end(),
                                    [&](const std::string &k) {
                                      return k.rfind(std::string(ubKindName(f.ub->kind)) + "@", 0) == 0;
                                  }))
                     : rr.status == RunStatus::AssertFailed;
      std::string kind = f.ub ? ubKindName(f.ub->kind) : "assert";
      if (ok) confirmed.push_back(kind);
      else { ++unconfirmed; std::cerr << fn << ": unconfirmed " << kind << " (replay: " << runStatusName(rr.status) << ")\n"; }
    }
    if (!r.complete) std::cerr << fn << ": exploration incomplete: " << r.note << "\n";
    if (expect == "none") {
      ++good;
      if (!confirmed.empty()) { ++falsePos; std::cerr << fn << ": FALSE POSITIVE " << confirmed[0] << "\n"; }
    } else {
      ++bad;
      if (std::find(confirmed.begin(), confirmed.end(), expect) != confirmed.end()) ++detected;
      else {
        std::cerr << fn << ": MISSED " << expect << " (found:";
        for (auto &k : confirmed) std::cerr << " " << k;
        std::cerr << ")\n";
      }
    }
  }
  double det = bad ? 100.0 * detected / bad : 0, fp = good ? 100.0 * falsePos / good : 0;
  std::cout << "corpus: " << files.size() << " programs (" << bad << " bad, " << good << " good); detection " << detected << "/" << bad << " = " << det
            << "%, false positives " << falsePos << "/" << good << " = " << fp << "%, unconfirmed findings " << unconfirmed << ", load errors " << errors << "\n";
  bool pass = errors == 0 && det >= 90.0 && fp <= 5.0;
  return pass ? 0 : 1;
}

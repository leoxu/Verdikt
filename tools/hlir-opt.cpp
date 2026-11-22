// hlir-opt: parse, verify and print `core` IR.
//   hlir-opt [--verify-only] [--coverage] [--no-verify] file.core
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/ir/Parser.h"
#include "hlir/ir/Printer.h"
#include "hlir/ir/Verifier.h"

int main(int argc, char **argv) {
  bool verifyOnly = false, noVerify = false;
  hlir::VerifyOptions vo;
  std::string path;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--verify-only") verifyOnly = true;
    else if (a == "--coverage") vo.checkCoverage = true;
    else if (a == "--no-verify") noVerify = true;
    else if (!a.empty() && a[0] == '-') { std::cerr << "unknown option " << a << "\n"; return 2; }
    else path = a;
  }
  if (path.empty()) { std::cerr << "usage: hlir-opt [--verify-only] [--coverage] [--no-verify] file.core\n"; return 2; }
  std::ifstream in(path);
  if (!in) { std::cerr << "cannot open " << path << "\n"; return 2; }
  std::stringstream ss;
  ss << in.rdbuf();

  hlir::Diagnostics diags;
  auto mod = hlir::parseModule(ss.str(), path, diags);
  if (!mod) { std::cerr << diags.str(); return 1; }
  if (!noVerify && !hlir::verifyModule(*mod, vo, diags)) { std::cerr << diags.str(); return 1; }
  if (!verifyOnly) std::cout << hlir::moduleToString(*mod);
  return 0;
}

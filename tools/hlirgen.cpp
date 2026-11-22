// hlirgen: lower C to `core` text.
//   hlirgen file.c [-o out.core] [--recover] [clang flags...]
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/buildinfo/BuildInfo.h"
#include "hlir/frontend/Frontend.h"

int main(int argc, char **argv) {
  std::string in, out;
  hlir::buildinfo::BuildSource bsrc;
  hlir::frontend::LowerOptions opt;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "-o") out = i + 1 < argc ? argv[++i] : "";
    else if (a == "--makefile" && i + 1 < argc) bsrc.makefile = argv[++i];
    else if (a == "--make-target" && i + 1 < argc) bsrc.target = argv[++i];
    else if (a == "--make-arg" && i + 1 < argc) bsrc.makeArgs.push_back(argv[++i]);
    else if (a == "--make-mode" && i + 1 < argc) bsrc.mode = argv[++i];
    else if (a == "--compile-commands" && i + 1 < argc) bsrc.compileCommands = argv[++i];
    else if (a == "--recover") { opt.recover = true; opt.partial = true; }
    else if (a == "--") {
      // See the matching comment in hlir-scan.cpp: a bare "--" must not be forwarded to clang, or clang's own argv
      // parser treats everything after it as filenames instead of flags.
    }
    else if (a.size() > 1 && a[0] == '-') {
      opt.clangArgs.push_back(a);
      if ((a == "-I" || a == "-D" || a == "-include" || a == "-isystem" || a == "-imacros") && i + 1 < argc) opt.clangArgs.push_back(argv[++i]);
    }
    else in = a;
  }
  if (in.empty()) { std::cerr << "usage: hlirgen file.c [-o out.core] [--recover] [--makefile P [--make-target T] [--make-arg A] [--make-mode dry-run|static] | --compile-commands F] [clang flags...]\n"; return 2; }
  if (!bsrc.makefile.empty() || !bsrc.compileCommands.empty()) {
    hlir::buildinfo::BuildDatabase db;
    std::vector<std::string> notes;
    std::string berr;
    if (!hlir::buildinfo::loadBuildDatabase(bsrc, db, notes, berr)) { std::cerr << berr << "\n"; return 2; }
    for (auto &n : notes) std::cerr << "note: " << n << "\n";
    const hlir::buildinfo::CompileCommand *cc = db.lookup(in);
    if (!cc) cc = db.common();
    if (!cc) { std::cerr << "note: no compile command for " << in << " in the build source\n"; }
    else {
      auto ff = hlir::buildinfo::frontendFlags(*cc);
      for (auto &w : ff.warnings) std::cerr << "warning: " << w << "\n";
      std::vector<std::string> merged = ff.clangArgs;
      merged.insert(merged.end(), opt.clangArgs.begin(), opt.clangArgs.end());
      opt.clangArgs = merged;
      opt.wrapSignedOverflow = ff.wrapSignedOverflow;
      std::cerr << "note: compile options from " << cc->origin << ": " << ff.includeDirs << " include dir(s), " << ff.defines << " define(s)\n";
    }
  }
  std::ifstream f(in);
  if (!f) { std::cerr << "cannot open " << in << "\n"; return 2; }
  std::stringstream ss;
  ss << f.rdbuf();
  auto r = hlir::frontend::lowerC(ss.str(), in, opt);
  std::cerr << r.diagnostics;
  for (auto &h : r.missingHeaders) std::cerr << "note: header not found, treated as empty: " << h << "\n";
  for (auto &t : r.inferredStructs) std::cerr << "note: inferred " << t << "\n";
  for (auto &t : r.assumedTypes) std::cerr << "note: unknown type name given a stub typedef: " << t << "\n";
  for (auto &f : r.functions) if (!f.lowered) std::cerr << "note: @" << f.name << " not lowered: " << f.skipReason << "\n";
  if (!r.ok) return 1;
  if (out.empty()) std::cout << r.core;
  else std::ofstream(out) << r.core;
  return 0;
}

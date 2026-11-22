// hlir-taint: entry spec -> harness -> taint-selective concolic execution -> replay-confirmed report.
//   hlir-taint --spec s.yaml file.core|file.c --entry f [--libc] [--runs N] [--promote name]... [--promote-all]
//              [--format text|json|sarif|dot] [--output file] [--no-escalate] [--fast-ms N --slow-ms N]
// Exit: 0 safe under the assumptions, 1 bug (confirmed), 2 input error, 3 unknown (incomplete / unconfirmed).
//
// --format dot renders the function call graph the taint engine exercised (DESIGN/IMPLEMENTATION_PLAN.md, "call graph
// visualisation"): edges it saw carry tainted data are drawn in red. The DOT text is the deliverable; if a `dot`
// binary (Graphviz) is on PATH and --output is given, an SVG is rendered alongside it as a convenience (not required).
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>

#include "hlir/driver/Pipeline.h"
#ifdef HLIR_WITH_FRONTEND
#include "hlir/frontend/Frontend.h"
#endif

using namespace hlir;

static std::string slurp(const std::string &p, bool &ok) {
  std::ifstream in(p);
  ok = static_cast<bool>(in);
  std::stringstream ss;
  ss << in.rdbuf();
  return ss.str();
}

// "4" or "4,16,64": ascending loop bounds
static bool parseBounds(const std::string &s, std::vector<unsigned> &out) {
  std::stringstream ss(s);
  std::string t;
  while (std::getline(ss, t, ',')) {
    if (t.empty() || t.find_first_not_of("0123456789") != std::string::npos) return false;
    out.push_back(static_cast<unsigned>(std::stoul(t)));
  }
  return !out.empty() && std::is_sorted(out.begin(), out.end());
}

// "LABEL=0102 0304 ..." -> label seed stream (hex bytes; spaces, ':' and '_' ignored). Returns false on a malformed argument.
static bool parseSeedBytes(const std::string &arg, std::map<std::string, std::vector<uint8_t>> &out, std::string &err) {
  size_t eq = arg.find('=');
  if (eq == std::string::npos || eq == 0) { err = "expected LABEL=HEXBYTES"; return false; }
  std::string hex;
  for (char c : arg.substr(eq + 1))
    if (c != ' ' && c != ':' && c != '_') hex += c;
  if (hex.size() % 2) { err = "odd number of hex digits"; return false; }
  std::vector<uint8_t> bytes;
  for (size_t i = 0; i < hex.size(); i += 2) {
    if (!isxdigit(static_cast<unsigned char>(hex[i])) || !isxdigit(static_cast<unsigned char>(hex[i + 1]))) { err = "not a hex digit in '" + hex.substr(i, 2) + "'"; return false; }
    bytes.push_back(static_cast<uint8_t>(std::stoi(hex.substr(i, 2), nullptr, 16)));
  }
  out[arg.substr(0, eq)] = bytes;
  return true;
}

// NAME=VALUE for --seed-value: the initial value of a named scalar input. Decimal, or 0x-prefixed hex.
static bool parseSeedValue(const std::string &arg, std::map<std::string, uint64_t> &out, std::string &err) {
  size_t eq = arg.find('=');
  if (eq == std::string::npos || eq == 0) { err = "expected NAME=VALUE"; return false; }
  std::string name = arg.substr(0, eq), val = arg.substr(eq + 1);
  if (val.empty()) { err = "empty value"; return false; }
  errno = 0;
  char *end = nullptr;
  unsigned long long v = std::strtoull(val.c_str(), &end, 0);
  if (errno != 0 || end == val.c_str() || *end != '\0') { err = "not an integer: '" + val + "'"; return false; }
  out[name] = static_cast<uint64_t>(v);
  return true;
}

int main(int argc, char **argv) {
  driver::AnalysisOptions opt;
  std::string spec, file, format = "text", output;
  bool libc = false, ok0 = false;
  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    auto next = [&]() -> std::string { return i + 1 < argc ? argv[++i] : ""; };
    if (a == "--spec") spec = next();
    else if (a == "--entry") opt.entry = next();
    else if (a == "--libc") libc = true;
    else if (a == "--models") { std::string f = next(); bool mok; std::string t = slurp(f, mok); if (!mok) { std::cerr << "cannot read " << f << "\n"; return 2; } opt.models.push_back({f, t}); }
    else if (a == "--libc-models") { opt.models.push_back({HLIR_MODELS_DIR "/libc.yaml", slurp(HLIR_MODELS_DIR "/libc.yaml", ok0)}); }
    else if (a == "--pre") { std::string f = next(); bool pok; std::string t = slurp(f, pok); if (!pok) { std::cerr << "cannot read " << f << "\n"; return 2; } opt.preconditions.push_back({f, t}); }
    else if (a == "--opaque-externs") opt.opaqueExternals = true;
    else if (a == "--seed-bytes") { std::string perr; if (!parseSeedBytes(next(), opt.taint.labelSeeds, perr)) { std::cerr << "hlir-taint: --seed-bytes: " << perr << "\n"; return 2; } }
    else if (a == "--seed-value") { std::string perr; if (!parseSeedValue(next(), opt.taint.valueSeeds, perr)) { std::cerr << "hlir-taint: --seed-value: " << perr << "\n"; return 2; } }
    else if (a == "--loop-bound") { if (!parseBounds(next(), opt.loopBounds)) { std::cerr << "hlir-taint: --loop-bound expects K or K1,K2,...\n"; return 2; } }
    else if (a == "--wall-seconds") opt.wallSeconds = std::stod(next());
    else if (a == "--runs") opt.taint.maxRuns = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--promote") opt.taint.promote.insert(next());
    else if (a == "--promote-all") opt.taint.promoteAll = true;
    else if (a == "--format") format = next();
    else if (a == "--output") output = next();
    else if (a == "--no-escalate") opt.escalate = false;
    else if (a == "--fast-ms") opt.taint.fastTimeoutMs = static_cast<unsigned>(std::stoul(next()));
    else if (a == "--slow-ms") opt.taint.slowTimeoutMs = static_cast<unsigned>(std::stoul(next()));
    else if (!a.empty() && a[0] != '-') file = a;
    else { std::cerr << "unknown option " << a << "\n"; return 2; }
  }
  if (spec.empty() || file.empty() || opt.entry.empty() || (format != "text" && format != "json" && format != "sarif" && format != "dot")) {
    std::cerr << "usage: hlir-taint --spec s.yaml file.core|file.c --entry f [--libc] [--runs N] [--promote x] [--promote-all] [--format text|json|sarif|dot] [--output file]\n";
    return 2;
  }
  bool ok;
  opt.specText = slurp(spec, ok);
  if (!ok) { std::cerr << "cannot read " << spec << "\n"; return 2; }
  opt.specName = spec;
  opt.coreText = slurp(file, ok);
  if (!ok) { std::cerr << "cannot read " << file << "\n"; return 2; }
  opt.coreName = file;
  if (file.size() > 2 && file.substr(file.size() - 2) == ".c") {  // C source: lower to core first
#ifdef HLIR_WITH_FRONTEND
    auto low = frontend::lowerC(opt.coreText, file, {});
    std::cerr << low.diagnostics;
    if (!low.ok) return 2;
    opt.coreText = low.core;
#else
    std::cerr << "built without the C frontend (needs libclang-cpp-dev)\n";
    return 2;
#endif
  }
  if (libc) opt.libcText = slurp(HLIR_MODELS_DIR "/libc.core", ok) + "\n" + slurp(HLIR_MODELS_DIR "/libstdcxx.core", ok);

  driver::AnalysisOutcome out = driver::analyzeEntry(opt);
  if (!out.ok) { std::cerr << out.error; return 2; }
  report::Report rep;
  rep.entries.push_back(out.entry);
  std::string text = format == "json"  ? report::toJson(rep)
                    : format == "sarif" ? report::toSarif(rep)
                    : format == "dot"   ? report::toDot(rep)
                                         : report::toText(rep);
  if (format == "dot" && text.empty()) std::cerr << "hlir-taint: --format dot: no call-graph edges recorded (taint engine did not run, or found no calls)\n";
  if (output.empty()) std::cout << text;
  else {
    std::ofstream f(output);
    f << text;
    f.close();
    // Convenience only: the DOT text above is the deliverable. If Graphviz's `dot` is available, render it to SVG next
    // to the requested output file so the taint-highlighted graph can be inspected without a separate conversion step.
    if (format == "dot" && !text.empty() && std::system("command -v dot >/dev/null 2>&1") == 0) {
      std::string svg = output.size() > 4 && output.substr(output.size() - 4) == ".dot" ? output.substr(0, output.size() - 4) + ".svg" : output + ".svg";
      std::string cmd = "dot -Tsvg " + output + " -o " + svg + " 2>/dev/null";
      if (std::system(cmd.c_str()) != 0) std::cerr << "hlir-taint: `dot` failed to render " << svg << " (DOT text at " << output << " is still valid)\n";
    }
  }
  switch (out.entry.verdict) {
    case report::Verdict::SafeUnderAssumptions: case report::Verdict::SafeUpToLoopBound: return 0;
    case report::Verdict::Bug: return 1;
    default: return 3;
  }
}

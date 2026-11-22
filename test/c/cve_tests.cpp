// CVE regression suite: every CVE HLIR has detected on a real tree, distilled to a vuln/fixed pair.
//
// Why this exists. The real corpus (`workspace/`, upstream worktrees, native ASan ground truth) is the thing
// that measures recall, and it is slow and driven by hand. Between those runs nothing stopped an engine change
// from silently losing a whole class of defect -- and three such losses were found in a single day
// (DESIGN.md §22.417-§22.419), each of which cost at least one CVE and none of which turned any test red.
//
// What it does NOT claim. A minimised function is not the program the CVE was filed against. Passing here is
// not evidence that HLIR detects CVE-X; it is evidence that the SHAPE which produced that detection still
// produces it. The claim "detected" belongs to (report not included in this repo), which rests on the four criteria and on an
// ASan run. Keeping those two statements apart is the whole point of having this file say so out loud.
//
// The pair is mandatory. A detection fixture on its own measures recall and says nothing about false
// positives, and "the finding disappears on the fixed tree" is one of the four criteria -- so it survives the
// distillation: the fixed entry must not report the kind, and the suite fails if it does.
#include <unistd.h>
#include <dirent.h>

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "hlir/report/Report.h"

using namespace hlir;

static int g_fail = 0, g_pass = 0;
#define CHECK(cond, msg)                                                                         \
  do {                                                                                           \
    if (cond) ++g_pass;                                                                          \
    else { ++g_fail; std::cerr << "FAIL " << __FILE__ << ":" << __LINE__ << ": " << msg << "\n"; } \
  } while (0)

static std::string slurp(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }

static std::string header(const std::string &src, const std::string &key) {
  std::istringstream ls(src);
  const std::string want = "// " + key + ":";
  for (std::string line; std::getline(ls, line);) {
    if (line.rfind(want, 0) != 0) continue;
    std::string v = line.substr(want.size());
    size_t a = v.find_first_not_of(" \t");
    if (a == std::string::npos) return "";
    size_t b = v.find_last_not_of(" \t\r");
    return v.substr(a, b - a + 1);
  }
  return "";
}

int main() {
  const std::string bin = HLIR_SCAN_BIN;
  const std::string dir = HLIR_CVE_FIXTURE_DIR;
  std::vector<std::string> files;
  if (DIR *d = opendir(dir.c_str())) {
    while (auto *e = readdir(d)) {
      std::string n = e->d_name;
      if (n.size() > 2 && n.compare(n.size() - 2, 2, ".c") == 0) files.push_back(n);
    }
    closedir(d);
  }
  std::sort(files.begin(), files.end());
  CHECK(!files.empty(), "there are CVE fixtures to run in " << dir);

  unsigned detected = 0, clean = 0;
  for (const std::string &fn : files) {
    const std::string path = dir + "/" + fn;
    const std::string src = slurp(path);
    const std::string cve = header(src, "CVE"), kind = header(src, "KIND");
    const std::string vuln = header(src, "VULN"), fixed = header(src, "FIXED");
    const std::string args = header(src, "ARGS");
    if (cve.empty() || kind.empty() || vuln.empty() || fixed.empty()) {
      CHECK(false, fn << ": needs CVE/KIND/VULN/FIXED headers (see test/c/cve/README.md)");
      continue;
    }
    // One scan per file: both entries are named, so the lowering and the parse are paid once.
    const std::string js = "/tmp/hlir_cve." + std::to_string(getpid()) + ".json";
    const std::string cmd = bin + " --entry " + vuln + " --entry " + fixed +
                            " --runs 5000 --timeout 90 --buf-max 32 " + args +
                            " --format json --output " + js + " " + path + " > /dev/null 2>&1";
    std::system(cmd.c_str());
    std::string text = slurp(js);
    std::remove(js.c_str());
    report::Report r;
    std::string err;
    if (text.empty() || text.find('{') == std::string::npos ||
        !report::fromJson(text.substr(text.find('{')), r, err)) {
      CHECK(false, fn << " (" << cve << "): scan produced no report: " << err);
      continue;
    }
    const report::EntryReport *ev = nullptr, *ef = nullptr;
    for (auto &e : r.entries) {
      if (e.function == vuln) ev = &e;
      if (e.function == fixed) ef = &e;
    }
    CHECK(ev && ef, fn << " (" << cve << "): both entries were analysed (" << r.entries.size() << " found)");
    if (!ev || !ef) continue;

    // --- the vulnerable shape: the kind must be REPORTED, as a defect and not a warning, and CONFIRMED by a
    // replay. An unconfirmed finding is the failure mode §22.418/§22.419 produced, so it must not count.
    const report::Finding *hit = nullptr;
    std::string sawV;
    for (auto &f : ev->findings) {
      if (f.warning) continue;
      sawV += " " + f.kind + "@" + std::to_string(f.loc.line);
      if (f.kind == kind && f.replay == report::ReplayStatus::Confirmed && !hit) hit = &f;
    }
    CHECK(hit, cve << " (" << fn << "): `" << kind << "` is reported on @" << vuln
                   << " and replay-confirmed; got:" << (sawV.empty() ? std::string(" nothing") : sawV));
    if (hit) {
      ++detected;
      CHECK(ev->verdict == report::Verdict::Bug,
            cve << ": ...and the entry's verdict is `bug`, not " << report::verdictName(ev->verdict));
      // The witness has to be usable by someone other than the engine (§22.417): a reproducer needs the bytes
      // and the scalars, under the parameter's own name.
      bool hasBuffer = false, elided = false;
      for (auto &w : hit->witness) {
        if (w.note == "buffer" || w.note == "cstring") hasBuffer = true;
        elided |= w.value.find("more)") != std::string::npos;
      }
      CHECK(hasBuffer, cve << ": the witness names the attacker buffer");
      CHECK(!elided, cve << ": ...and none of it was elided");
    }

    // --- the fixed shape: the differential criterion. The kind must be gone.
    std::string sawF;
    bool regressed = false;
    for (auto &f : ef->findings) {
      if (f.warning) continue;
      sawF += " " + f.kind + "@" + std::to_string(f.loc.line);
      regressed |= f.kind == kind;
    }
    CHECK(!regressed, cve << " (" << fn << "): @" << fixed << " has the upstream fix applied and must NOT "
                          << "report `" << kind << "`; got:" << sawF);
    if (!regressed) ++clean;
    // A fixed entry that could not be analysed is not evidence of anything. `unknown` means the budget ran
    // out, so "no finding" there is silence, not a negative result.
    CHECK(ef->verdict != report::Verdict::Unknown,
          cve << ": @" << fixed << " was analysed to completion (verdict "
              << report::verdictName(ef->verdict) << "); `unknown` makes the negative control meaningless");
  }

  std::cout << "cve_tests: " << files.size() << " CVE fixture(s); " << detected << " detected, " << clean
            << " clean on the fixed shape; " << g_pass << " passed, " << g_fail << " failed\n";
  return g_fail ? 1 : 0;
}

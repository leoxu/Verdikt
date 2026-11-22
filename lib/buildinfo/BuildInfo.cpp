#include "hlir/buildinfo/BuildInfo.h"

#include <glob.h>
#include <sys/stat.h>

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <map>
#include <optional>
#include <regex>
#include <set>
#include <sstream>

namespace hlir::buildinfo {
namespace {

bool isDirectory(const std::string &p) { struct stat st; return stat(p.c_str(), &st) == 0 && S_ISDIR(st.st_mode); }
bool fileExists(const std::string &p) { struct stat st; return stat(p.c_str(), &st) == 0 && S_ISREG(st.st_mode); }
std::string readFile(const std::string &p) { std::ifstream in(p); std::stringstream ss; ss << in.rdbuf(); return ss.str(); }
bool endsWith(const std::string &s, const std::string &e) { return s.size() >= e.size() && s.compare(s.size() - e.size(), e.size(), e) == 0; }
bool startsWith(const std::string &s, const std::string &b) { return s.compare(0, b.size(), b) == 0; }

// lexical normalisation: "a/./b/../c" -> "a/c"
std::string normalize(const std::string &path) {
  std::vector<std::string> parts;
  std::stringstream ss(path);
  std::string seg;
  bool abs = !path.empty() && path[0] == '/';
  while (std::getline(ss, seg, '/')) {
    if (seg.empty() || seg == ".") continue;
    if (seg == ".." && !parts.empty() && parts.back() != "..") { parts.pop_back(); continue; }
    if (seg == ".." && abs) continue;
    parts.push_back(seg);
  }
  std::string out = abs ? "/" : "";
  for (size_t i = 0; i < parts.size(); ++i) out += (i ? "/" : "") + parts[i];
  return out.empty() ? "." : out;
}
std::string absPath(const std::string &dir, const std::string &p) {
  if (p.empty()) return dir;
  return normalize(p[0] == '/' ? p : dir + "/" + p);
}
std::string baseName(const std::string &p) { auto k = p.rfind('/'); return k == std::string::npos ? p : p.substr(k + 1); }
std::string dirName(const std::string &p) { auto k = p.rfind('/'); return k == std::string::npos ? "." : (k == 0 ? "/" : p.substr(0, k)); }
std::string trim(const std::string &s) {
  size_t b = 0, e = s.size();
  while (b < e && isspace(static_cast<unsigned char>(s[b]))) ++b;
  while (e > b && isspace(static_cast<unsigned char>(s[e - 1]))) --e;
  return s.substr(b, e - b);
}
std::vector<std::string> words(const std::string &s) {
  std::vector<std::string> w;
  std::istringstream in(s);
  std::string x;
  while (in >> x) w.push_back(x);
  return w;
}
std::string join(const std::vector<std::string> &v, const std::string &sep = " ") {
  std::string o;
  for (size_t i = 0; i < v.size(); ++i) o += (i ? sep : "") + v[i];
  return o;
}

// options that take their value as the next argument
bool takesValue(const std::string &a) {
  static const std::set<std::string> v = {"-o", "-MF", "-MT", "-MQ", "-I", "-D", "-U", "-include", "-imacros", "-isystem", "-iquote", "-idirafter",
                                          "-x", "-isysroot", "-L", "-l", "-T", "--param", "-aux-info", "-Xlinker", "-Xassembler", "-Xpreprocessor", "-arch", "-target"};
  return v.count(a) != 0;
}
bool isCompiler(const std::string &argv0) {
  static const std::regex re("^(.*-)?(gcc|g\\+\\+|cc|c\\+\\+|clang|clang\\+\\+)(-[0-9.]+)?$");
  return std::regex_match(baseName(argv0), re);
}

}  // namespace

// ------------------------------------------------------------------------------------------------ shell words
std::vector<std::string> shellSplit(const std::string &line) {
  std::vector<std::string> out;
  std::string cur;
  bool have = false;
  for (size_t i = 0; i < line.size(); ++i) {
    char c = line[i];
    if (c == '\'') {
      have = true;
      for (++i; i < line.size() && line[i] != '\''; ++i) cur += line[i];
    } else if (c == '"') {
      have = true;
      for (++i; i < line.size() && line[i] != '"'; ++i) {
        if (line[i] == '\\' && i + 1 < line.size() && (line[i + 1] == '"' || line[i + 1] == '\\' || line[i + 1] == '$' || line[i + 1] == '`')) ++i;
        cur += line[i];
      }
    } else if (c == '\\' && i + 1 < line.size()) {
      have = true;
      cur += line[++i];
    } else if (isspace(static_cast<unsigned char>(c))) {
      if (have) { out.push_back(cur); cur.clear(); have = false; }
    } else if (c == ';' || c == '|' || c == '&') {  // operators are words of their own: ";" "&&" "||" "|"
      if (have) { out.push_back(cur); cur.clear(); have = false; }
      std::string op(1, c);
      if ((c == '&' || c == '|') && i + 1 < line.size() && line[i + 1] == c) { op += c; ++i; }
      out.push_back(op);
    } else {
      have = true;
      cur += c;
    }
  }
  if (have) out.push_back(cur);
  return out;
}

// ------------------------------------------------------------------------------------------------ flags for the frontend
FrontendFlags frontendFlags(const CompileCommand &c) {
  FrontendFlags f;
  auto addPath = [&](const std::string &flag, const std::string &v) {
    if (flag == "-isystem" && v.find("/lib/gcc/") != std::string::npos) return;  // gcc's own header dir: clang has its own
    f.clangArgs.push_back(flag);
    f.clangArgs.push_back(absPath(c.directory, v));
  };
  std::function<void(const std::vector<std::string> &)> process = [&](const std::vector<std::string> &args) {
    for (size_t i = 0; i < args.size(); ++i) {
      const std::string &a = args[i];
      auto next = [&]() -> std::string { return i + 1 < args.size() ? args[++i] : ""; };
      if (a == "-I" || (startsWith(a, "-I") && a.size() > 2)) {
        std::string v = a == "-I" ? next() : a.substr(2);
        f.clangArgs.push_back("-I" + absPath(c.directory, v));
        ++f.includeDirs;
      } else if (a == "-iquote" || a == "-idirafter" || a == "-isystem") {
        addPath("-isystem", next());
      } else if (startsWith(a, "-isystem") && a.size() > 8) addPath("-isystem", a.substr(8));
      else if (a == "-include" || a == "-imacros") {
        std::string v = next();
        f.clangArgs.push_back(a);
        f.clangArgs.push_back(absPath(c.directory, v));
      } else if (a == "-D" || (startsWith(a, "-D") && a.size() > 2)) {
        f.clangArgs.push_back("-D" + (a == "-D" ? next() : a.substr(2)));
        ++f.defines;
      } else if (a == "-U" || (startsWith(a, "-U") && a.size() > 2)) {
        f.clangArgs.push_back("-U" + (a == "-U" ? next() : a.substr(2)));
      } else if (startsWith(a, "-std=") || a == "-nostdinc" || a == "-fms-extensions" || a == "-funsigned-char" || a == "-fsigned-char" || a == "-fshort-enums" ||
                 startsWith(a, "-fpack-struct") || a == "-pthread" || a == "-ffreestanding") {
        f.clangArgs.push_back(a);
      } else if (a == "-fwrapv" || a == "-fno-strict-overflow") {
        f.wrapSignedOverflow = true;
      } else if (a == "-m32" || a == "-m31" || a == "-mx32") {
        f.warnings.push_back("'" + a + "' is not supported: the analysis models 64-bit pointers; the flag is ignored");
      } else if (startsWith(a, "--sysroot=")) {
        f.clangArgs.push_back("--sysroot=" + absPath(c.directory, a.substr(10)));
      } else if (a == "-isysroot") {
        f.clangArgs.push_back(a);
        f.clangArgs.push_back(absPath(c.directory, next()));
      } else if (startsWith(a, "-Wp,")) {  // options for the preprocessor: -Wp,-MD,file  -Wp,-DX
        std::vector<std::string> sub;
        std::stringstream ss(a.substr(4));
        std::string t;
        while (std::getline(ss, t, ',')) sub.push_back(t);
        std::vector<std::string> keep;
        for (size_t k = 0; k < sub.size(); ++k) {
          if (sub[k] == "-MD" || sub[k] == "-MMD" || sub[k] == "-MF" || sub[k] == "-MT" || sub[k] == "-MQ" || sub[k] == "-MP") { if (sub[k] == "-MF" || sub[k] == "-MT" || sub[k] == "-MQ" || sub[k] == "-MD" || sub[k] == "-MMD") ++k; continue; }
          keep.push_back(sub[k]);
        }
        process(keep);
      } else if (takesValue(a)) {
        next();  // -o file, -MF file, -x c, ...: not relevant to parsing
      }
    }
  };
  process(c.args);
  return f;
}

// ------------------------------------------------------------------------------------------------ compile_commands.json
namespace {
struct J {
  enum K { Null, Str, Arr, Obj, Other } k = Null;
  std::string s;
  std::vector<J> a;
  std::vector<std::pair<std::string, J>> o;
  const J *get(const std::string &key) const { for (auto &kv : o) if (kv.first == key) return &kv.second; return nullptr; }
};
struct JP {
  const std::string &t;
  size_t i = 0;
  std::string err;
  explicit JP(const std::string &x) : t(x) {}
  void ws() { while (i < t.size() && isspace(static_cast<unsigned char>(t[i]))) ++i; }
  bool fail(const char *m) { if (err.empty()) err = std::string(m) + " at offset " + std::to_string(i); return false; }
  bool str(std::string &out) {
    if (i >= t.size() || t[i] != '"') return fail("expected string");
    ++i;
    out.clear();
    while (i < t.size() && t[i] != '"') {
      char c = t[i++];
      if (c != '\\') { out += c; continue; }
      if (i >= t.size()) return fail("bad escape");
      char e = t[i++];
      switch (e) {
        case 'n': out += '\n'; break;
        case 't': out += '\t'; break;
        case 'r': out += '\r'; break;
        case 'u': { if (i + 4 > t.size()) return fail("bad \\u"); unsigned v = static_cast<unsigned>(std::strtoul(t.substr(i, 4).c_str(), nullptr, 16)); i += 4; if (v < 0x80) out += static_cast<char>(v); else out += '?'; break; }
        default: out += e;
      }
    }
    if (i >= t.size()) return fail("unterminated string");
    ++i;
    return true;
  }
  bool value(J &v) {
    ws();
    if (i >= t.size()) return fail("unexpected end");
    char c = t[i];
    if (c == '{') {
      v.k = J::Obj;
      ++i; ws();
      if (i < t.size() && t[i] == '}') { ++i; return true; }
      for (;;) {
        ws();
        std::string key;
        if (!str(key)) return false;
        ws();
        if (i >= t.size() || t[i++] != ':') return fail("expected ':'");
        J child;
        if (!value(child)) return false;
        v.o.emplace_back(std::move(key), std::move(child));
        ws();
        if (i < t.size() && t[i] == ',') { ++i; continue; }
        if (i < t.size() && t[i] == '}') { ++i; return true; }
        return fail("expected ',' or '}'");
      }
    }
    if (c == '[') {
      v.k = J::Arr;
      ++i; ws();
      if (i < t.size() && t[i] == ']') { ++i; return true; }
      for (;;) {
        J child;
        if (!value(child)) return false;
        v.a.push_back(std::move(child));
        ws();
        if (i < t.size() && t[i] == ',') { ++i; continue; }
        if (i < t.size() && t[i] == ']') { ++i; return true; }
        return fail("expected ',' or ']'");
      }
    }
    if (c == '"') { v.k = J::Str; return str(v.s); }
    while (i < t.size() && !strchr(",]} \t\r\n", t[i])) ++i;  // numbers, true, false, null
    v.k = J::Other;
    return true;
  }
};
}  // namespace

std::vector<CompileCommand> parseCompileCommands(const std::string &json, std::string &err) {
  std::vector<CompileCommand> out;
  JP p(json);
  J root;
  if (!p.value(root) || root.k != J::Arr) { err = p.err.empty() ? "compile_commands.json must be a JSON array" : p.err; return out; }
  for (auto &e : root.a) {
    if (e.k != J::Obj) continue;
    CompileCommand c;
    c.origin = "compile_commands.json";
    if (auto *d = e.get("directory")) c.directory = d->s;
    if (auto *f = e.get("file")) c.file = absPath(c.directory.empty() ? "." : c.directory, f->s);
    if (auto *a = e.get("arguments")) {
      for (size_t i = 1; i < a->a.size(); ++i) c.args.push_back(a->a[i].s);  // [0] is the compiler
    } else if (auto *cmd = e.get("command")) {
      auto w = shellSplit(cmd->s);
      for (size_t i = 1; i < w.size(); ++i) c.args.push_back(w[i]);
    }
    if (c.file.empty() || !endsWith(c.file, ".c")) continue;  // C translation units only
    out.push_back(std::move(c));
  }
  return out;
}

// ------------------------------------------------------------------------------------------------ make -n output
std::vector<CompileCommand> parseMakeDryRun(const std::string &output, const std::string &startDir) {
  std::vector<CompileCommand> out;
  std::string dir = startDir;
  std::vector<std::string> dirStack;
  // join backslash continuations
  std::vector<std::string> lines;
  {
    std::istringstream in(output);
    std::string l, acc;
    while (std::getline(in, l)) {
      if (!l.empty() && l.back() == '\\') { l.pop_back(); acc += l + " "; continue; }
      lines.push_back(acc + l);
      acc.clear();
    }
    if (!acc.empty()) lines.push_back(acc);
  }
  static const std::regex enter("Entering directory [`']([^'`]+)'");
  static const std::regex leave("Leaving directory [`']([^'`]+)'");
  for (auto &line : lines) {
    std::smatch m;
    if (std::regex_search(line, m, enter)) { dirStack.push_back(dir); dir = m[1]; continue; }
    if (std::regex_search(line, m, leave)) { if (!dirStack.empty()) { dir = dirStack.back(); dirStack.pop_back(); } continue; }
    auto toks = shellSplit(line);
    // split into commands at the operators
    std::vector<std::vector<std::string>> cmds(1);
    for (auto &t : toks) {
      if (t == ";" || t == "&&" || t == "||" || t == "|") { cmds.emplace_back(); continue; }
      cmds.back().push_back(t);
    }
    std::string cwd = dir;
    for (auto &cmd : cmds) {
      size_t k = 0;
      while (k < cmd.size() && (cmd[k].find('=') != std::string::npos && cmd[k][0] != '-' && cmd[k].find('/') == std::string::npos)) ++k;  // VAR=val prefixes
      if (k >= cmd.size()) continue;
      if (cmd[k] == "cd" && k + 1 < cmd.size()) { cwd = absPath(cwd, cmd[k + 1]); continue; }
      while (k < cmd.size() && (baseName(cmd[k]) == "ccache" || baseName(cmd[k]) == "distcc" || baseName(cmd[k]) == "time" || baseName(cmd[k]) == "env" || baseName(cmd[k]) == "nice")) ++k;
      if (k >= cmd.size() || !isCompiler(cmd[k])) continue;
      std::vector<std::string> args(cmd.begin() + static_cast<long>(k) + 1, cmd.end());
      std::vector<std::string> sources;
      for (size_t i = 0; i < args.size(); ++i) {
        if (!args[i].empty() && args[i][0] == '-') { if (takesValue(args[i])) ++i; continue; }
        if (endsWith(args[i], ".c")) sources.push_back(args[i]);
      }
      for (auto &s : sources) {
        CompileCommand c;
        c.directory = cwd;
        c.file = absPath(cwd, s);
        c.args = args;
        c.origin = "make -n";
        out.push_back(std::move(c));
      }
    }
  }
  return out;
}

bool runMakeDryRun(const std::string &dir, const std::vector<std::string> &makeArgs, unsigned timeoutSeconds, std::string &output, std::string &err) {
  auto q = [](const std::string &s) { std::string o = "'"; for (char c : s) o += c == '\'' ? std::string("'\\''") : std::string(1, c); return o + "'"; };
  std::string cmd = "timeout " + std::to_string(timeoutSeconds) + " make -n -B -k -w -C " + q(dir);
  for (auto &a : makeArgs) cmd += " " + q(a);
  cmd += " 2>/dev/null";
  FILE *p = popen(cmd.c_str(), "r");
  if (!p) { err = "cannot run make"; return false; }
  char buf[65536];
  size_t n;
  output.clear();
  while ((n = fread(buf, 1, sizeof buf, p)) > 0) output.append(buf, n);
  int rc = pclose(p);
  if (output.empty()) { err = "make -n printed nothing (exit status " + std::to_string(rc) + "): is there a Makefile in " + dir + "?"; return false; }
  return true;
}

// ------------------------------------------------------------------------------------------------ static Makefile
namespace {

struct MakeVars {
  struct Var { std::string value; bool recursive = true; };  // recursive (=): expanded at use; simple (:=): already expanded
  std::map<std::string, Var> v;
  std::vector<std::string> order;                           // assignment order of the names
  std::string dir;
  std::vector<std::string> *warnings = nullptr;
  std::set<std::string> warned;

  void warn(const std::string &w) { if (warnings && warned.insert(w).second) warnings->push_back(w); }
  std::string get(const std::string &name, int depth);
  std::string expand(const std::string &s, int depth);
  std::string call(const std::string &fn, const std::vector<std::string> &raw, int depth);
  void set(const std::string &name, const Var &x) { if (!v.count(name)) order.push_back(name); v[name] = x; }
};

std::vector<std::string> splitArgs(const std::string &s) {
  std::vector<std::string> out;
  std::string cur;
  int depth = 0;
  for (char c : s) {
    if (c == '(' || c == '{') ++depth;
    if (c == ')' || c == '}') --depth;
    if (c == ',' && depth == 0) { out.push_back(cur); cur.clear(); continue; }
    cur += c;
  }
  out.push_back(cur);
  return out;
}

// `%` pattern match (patsubst / filter): the stem on success
bool patMatch(const std::string &pat, const std::string &w, std::string &stem) {
  auto k = pat.find('%');
  if (k == std::string::npos) { stem.clear(); return pat == w; }
  std::string pre = pat.substr(0, k), suf = pat.substr(k + 1);
  if (w.size() < pre.size() + suf.size() || w.compare(0, pre.size(), pre) != 0 || w.compare(w.size() - suf.size(), suf.size(), suf) != 0) return false;
  stem = w.substr(pre.size(), w.size() - pre.size() - suf.size());
  return true;
}
std::string patSubst(const std::string &pat, const std::string &repl, const std::string &text) {
  std::vector<std::string> out;
  for (auto &w : words(text)) {
    std::string stem;
    if (patMatch(pat, w, stem)) {
      std::string r = repl;
      auto k = r.find('%');
      if (k != std::string::npos) r = r.substr(0, k) + stem + r.substr(k + 1);
      out.push_back(r);
    } else out.push_back(w);
  }
  return join(out);
}

std::string MakeVars::get(const std::string &name, int depth) {
  auto it = v.find(name);
  if (it == v.end()) {
    if (name == "CURDIR") return dir;
    if (name == "CC") return "cc";
    if (name == "MAKE") return "make";
    return "";
  }
  return it->second.recursive ? expand(it->second.value, depth + 1) : it->second.value;
}

std::string MakeVars::call(const std::string &fn, const std::vector<std::string> &raw, int depth) {
  auto rawArg = [&](size_t i) { return i < raw.size() ? raw[i] : std::string(); };
  // lazy functions
  if (fn == "if") {
    if (!trim(expand(rawArg(0), depth + 1)).empty()) return expand(rawArg(1), depth + 1);
    return expand(rawArg(2), depth + 1);
  }
  if (fn == "or") { for (auto &r : raw) { std::string x = trim(expand(r, depth + 1)); if (!x.empty()) return x; } return ""; }
  if (fn == "and") { std::string x; for (auto &r : raw) { x = trim(expand(r, depth + 1)); if (x.empty()) return ""; } return x; }
  if (fn == "foreach") {
    std::string var = trim(expand(rawArg(0), depth + 1)), list = expand(rawArg(1), depth + 1);
    auto saved = v.find(var) != v.end() ? std::optional<Var>(v[var]) : std::nullopt;
    std::vector<std::string> out;
    for (auto &w : words(list)) { v[var] = Var{w, false}; out.push_back(expand(rawArg(2), depth + 1)); }
    if (saved) v[var] = *saved; else v.erase(var);
    return join(out);
  }
  std::vector<std::string> a;
  for (auto &x : raw) a.push_back(expand(x, depth + 1));
  auto arg = [&](size_t i) { return i < a.size() ? a[i] : std::string(); };
  if (fn == "strip") return join(words(arg(0)));
  if (fn == "subst") {
    std::string from = arg(0), to = arg(1), t = arg(2);
    if (from.empty()) return t;
    std::string out;
    for (size_t i = 0; i < t.size();) {
      if (t.compare(i, from.size(), from) == 0) { out += to; i += from.size(); } else out += t[i++];
    }
    return out;
  }
  if (fn == "patsubst") return patSubst(trim(arg(0)), trim(arg(1)), arg(2));
  if (fn == "filter" || fn == "filter-out") {
    auto pats = words(arg(0));
    std::vector<std::string> out;
    for (auto &w : words(arg(1))) {
      bool m = false;
      std::string stem;
      for (auto &p : pats) m |= patMatch(p, w, stem);
      if (m == (fn == "filter")) out.push_back(w);
    }
    return join(out);
  }
  if (fn == "sort") { auto w = words(arg(0)); std::sort(w.begin(), w.end()); w.erase(std::unique(w.begin(), w.end()), w.end()); return join(w); }
  if (fn == "word") { auto w = words(arg(1)); long n = std::strtol(trim(arg(0)).c_str(), nullptr, 10); return n >= 1 && static_cast<size_t>(n) <= w.size() ? w[static_cast<size_t>(n) - 1] : ""; }
  if (fn == "firstword") { auto w = words(arg(0)); return w.empty() ? "" : w[0]; }
  if (fn == "lastword") { auto w = words(arg(0)); return w.empty() ? "" : w.back(); }
  if (fn == "words") return std::to_string(words(arg(0)).size());
  if (fn == "dir" || fn == "notdir" || fn == "basename" || fn == "suffix" || fn == "abspath" || fn == "realpath") {
    std::vector<std::string> out;
    for (auto &w : words(arg(0))) {
      if (fn == "dir") out.push_back(w.find('/') == std::string::npos ? "./" : w.substr(0, w.rfind('/') + 1));
      else if (fn == "notdir") out.push_back(baseName(w));
      else if (fn == "basename") { auto k = w.rfind('.'), sl = w.rfind('/'); out.push_back(k != std::string::npos && (sl == std::string::npos || k > sl) ? w.substr(0, k) : w); }
      else if (fn == "suffix") { auto k = w.rfind('.'), sl = w.rfind('/'); if (k != std::string::npos && (sl == std::string::npos || k > sl)) out.push_back(w.substr(k)); }
      else out.push_back(absPath(dir, w));
    }
    return join(out);
  }
  if (fn == "addprefix" || fn == "addsuffix") {
    std::vector<std::string> out;
    for (auto &w : words(arg(1))) out.push_back(fn == "addprefix" ? arg(0) + w : w + arg(0));
    return join(out);
  }
  if (fn == "findstring") return arg(1).find(arg(0)) != std::string::npos ? arg(0) : "";
  if (fn == "wildcard") {
    std::vector<std::string> out;
    for (auto &pat : words(arg(0))) {
      glob_t g;
      std::string full = absPath(dir, pat);
      if (glob(full.c_str(), 0, nullptr, &g) == 0) {
        for (size_t i = 0; i < g.gl_pathc; ++i) {
          std::string r = g.gl_pathv[i];
          std::string pre = dir + "/";
          out.push_back(pat[0] == '/' || r.compare(0, pre.size(), pre) != 0 ? r : r.substr(pre.size()));
        }
      }
      globfree(&g);
    }
    return join(out);
  }
  if (fn == "shell") { warn("$(shell " + trim(arg(0)).substr(0, 60) + "...) is not executed in static mode; its value is empty"); return ""; }
  if (fn == "value") return v.count(trim(arg(0))) ? v[trim(arg(0))].value : "";
  return "";  // call, eval, origin, error, warning, info, ...: ignored
}

std::string MakeVars::expand(const std::string &s, int depth) {
  if (depth > 24) return "";
  static const std::set<std::string> fns = {"strip", "subst", "patsubst", "filter", "filter-out", "sort", "word", "firstword", "lastword", "words", "dir", "notdir",
                                            "basename", "suffix", "abspath", "realpath", "addprefix", "addsuffix", "findstring", "wildcard", "shell", "value", "if",
                                            "or", "and", "foreach", "call", "eval", "origin", "error", "warning", "info", "join", "flavor"};
  std::string out;
  for (size_t i = 0; i < s.size(); ++i) {
    if (s[i] != '$') { out += s[i]; continue; }
    if (i + 1 >= s.size()) break;
    char n = s[i + 1];
    if (n == '$') { out += '$'; ++i; continue; }
    if (n == '(' || n == '{') {
      char close = n == '(' ? ')' : '}';
      int d = 1;
      size_t j = i + 2;
      while (j < s.size() && d > 0) { if (s[j] == n) ++d; else if (s[j] == close) --d; ++j; }
      if (d != 0) break;
      std::string inner = s.substr(i + 2, j - i - 3);
      i = j - 1;
      size_t sp = inner.find_first_of(" \t");
      std::string head = sp == std::string::npos ? inner : inner.substr(0, sp);
      if (sp != std::string::npos && fns.count(head)) { out += call(head, splitArgs(trim(inner.substr(sp))), depth); continue; }
      auto colon = inner.find(':');
      if (colon != std::string::npos && inner.find('=', colon) != std::string::npos) {  // $(SRCS:.c=.o)
        std::string name = inner.substr(0, colon), rest = inner.substr(colon + 1);
        auto eq = rest.find('=');
        std::string from = rest.substr(0, eq), to = rest.substr(eq + 1);
        if (from.find('%') == std::string::npos) { from = "%" + from; to = "%" + to; }
        out += patSubst(from, to, expand("$(" + name + ")", depth + 1));
        continue;
      }
      out += get(trim(expand(inner, depth + 1)), depth);
    } else if (isalnum(static_cast<unsigned char>(n)) || n == '_') {
      out += get(std::string(1, n), depth);
      ++i;
    } else {
      ++i;  // automatic variables ($@ $< $^ ...) have no value here
    }
  }
  return out;
}

struct Cond { bool active, taken, parent; };

void processMakefile(const std::string &path, MakeVars &mv, int depth, std::vector<std::string> &files) {
  if (depth > 12 || !fileExists(path)) return;
  files.push_back(path);
  std::string text = readFile(path);
  // logical lines
  std::vector<std::string> lines;
  {
    std::istringstream in(text);
    std::string l, acc;
    while (std::getline(in, l)) {
      if (!l.empty() && l.back() == '\r') l.pop_back();
      if (!l.empty() && l.back() == '\\') { l.pop_back(); acc += l + " "; continue; }
      lines.push_back(acc + l);
      acc.clear();
    }
    if (!acc.empty()) lines.push_back(acc);
  }
  std::vector<Cond> conds;
  auto active = [&] { return conds.empty() || conds.back().active; };
  static const std::regex asg(R"(^\s*(?:export\s+|override\s+)*([A-Za-z0-9_.\-]+)\s*(::=|:=|\+=|\?=|=)\s*(.*)$)");
  bool inDefine = false;
  for (auto &raw : lines) {
    if (!raw.empty() && raw[0] == '\t') continue;  // recipe
    std::string t = raw;
    auto h = t.find('#');
    if (h != std::string::npos) t = t.substr(0, h);
    t = trim(t);
    if (t.empty()) continue;
    if (inDefine) { if (t == "endef") inDefine = false; continue; }
    if (startsWith(t, "define ") || t == "define") { inDefine = true; continue; }
    // conditionals
    auto cmp = [&](const std::string &rest, bool eq) {
      std::string r = trim(rest), a, b;
      if (!r.empty() && r[0] == '(' && r.back() == ')') {
        auto parts = splitArgs(r.substr(1, r.size() - 2));
        a = parts.size() > 0 ? parts[0] : "";
        b = parts.size() > 1 ? parts[1] : "";
      } else {
        auto q = shellSplit(r);
        a = q.size() > 0 ? q[0] : "";
        b = q.size() > 1 ? q[1] : "";
      }
      return (trim(mv.expand(a, 0)) == trim(mv.expand(b, 0))) == eq;
    };
    auto pushCond = [&](bool c) { bool par = active(); conds.push_back({par && c, par && c, par}); };
    if (startsWith(t, "ifeq")) { pushCond(cmp(t.substr(4), true)); continue; }
    if (startsWith(t, "ifneq")) { pushCond(cmp(t.substr(5), false)); continue; }
    if (startsWith(t, "ifdef ")) { std::string n = trim(mv.expand(t.substr(6), 0)); pushCond(mv.v.count(n) && !trim(mv.get(n, 0)).empty()); continue; }
    if (startsWith(t, "ifndef ")) { std::string n = trim(mv.expand(t.substr(7), 0)); pushCond(!(mv.v.count(n) && !trim(mv.get(n, 0)).empty())); continue; }
    if (t == "else" || startsWith(t, "else ")) {
      if (conds.empty()) continue;
      Cond &c = conds.back();
      std::string rest = trim(t.substr(4));
      bool val = true;
      if (startsWith(rest, "ifeq")) val = cmp(rest.substr(4), true);
      else if (startsWith(rest, "ifneq")) val = cmp(rest.substr(5), false);
      else if (startsWith(rest, "ifdef ")) { std::string n = trim(mv.expand(rest.substr(6), 0)); val = mv.v.count(n) && !trim(mv.get(n, 0)).empty(); }
      else if (startsWith(rest, "ifndef ")) { std::string n = trim(mv.expand(rest.substr(7), 0)); val = !(mv.v.count(n) && !trim(mv.get(n, 0)).empty()); }
      c.active = c.parent && !c.taken && val;
      c.taken = c.taken || c.active;
      continue;
    }
    if (t == "endif") { if (!conds.empty()) conds.pop_back(); continue; }
    if (!active()) continue;
    // include
    {
      std::string head;
      if (startsWith(t, "-include ")) head = t.substr(9);
      else if (startsWith(t, "sinclude ")) head = t.substr(9);
      else if (startsWith(t, "include ")) head = t.substr(8);
      if (!head.empty()) {
        for (auto &f : words(mv.expand(head, 0))) processMakefile(absPath(dirName(path), f), mv, depth + 1, files);
        continue;
      }
    }
    std::smatch m;
    if (!std::regex_match(t, m, asg)) continue;
    std::string name = m[1], op = m[2], val = m[3];
    if (op == ":=" || op == "::=") mv.set(name, {mv.expand(val, 0), false});
    else if (op == "?=") { if (!mv.v.count(name)) mv.set(name, {val, true}); }
    else if (op == "+=") {
      auto it = mv.v.find(name);
      if (it == mv.v.end()) mv.set(name, {val, true});
      else it->second.value += " " + (it->second.recursive ? val : mv.expand(val, 0));
    } else mv.set(name, {val, true});
  }
}

bool optionVariable(const std::string &name) {
  std::string u;
  for (char c : name) u += static_cast<char>(toupper(static_cast<unsigned char>(c)));
  for (const char *bad : {"LDFLAGS", "ARFLAGS", "ASFLAGS", "AFLAGS", "RUSTFLAGS", "GOFLAGS", "CXXFLAGS", "YFLAGS", "LFLAGS", "MAKEFLAGS", "LDLIBS", "HOSTLDFLAGS"})
    if (u.find(bad) != std::string::npos) return false;
  if (u.find("FLAGS") != std::string::npos) return true;
  static const std::regex re("^(INC|INCS|INCLUDES?|INCLUDE_DIRS?|INC_DIRS?|DEFS|DEFINES?|CPPDEFS|CPPDEFINES)$|(_INC|_INCS|_INCLUDES?|_DEFS|_DEFINES?)$");
  return std::regex_search(u, re);
}
bool sourceVariable(const std::string &name) {
  static const std::regex re("^(SRC|SRCS|SOURCES?|CSRCS?|C_SRCS?|SRC_FILES|OBJS?|OBJECTS|obj-[ym]|lib-[ym]|[A-Za-z0-9_]+-(objs|y|m))$", std::regex::icase);
  return std::regex_match(name, re);
}

}  // namespace

std::vector<CompileCommand> parseMakefileStatic(const std::string &makefilePath, std::vector<std::string> &warnings) {
  std::string path = makefilePath;
  if (isDirectory(path)) {
    for (const char *n : {"GNUmakefile", "makefile", "Makefile"})
      if (fileExists(path + "/" + n)) { path = path + "/" + n; break; }
  }
  std::vector<CompileCommand> out;
  if (!fileExists(path)) { warnings.push_back("no Makefile at " + makefilePath); return out; }
  MakeVars mv;
  mv.dir = dirName(absPath(".", path));
  mv.warnings = &warnings;
  std::vector<std::string> files;
  processMakefile(absPath(".", path), mv, 0, files);
  std::vector<std::string> flags, sources;
  std::map<std::string, std::vector<std::string>> perFile;  // CFLAGS_foo.o
  for (auto &name : mv.order) {
    std::string value = mv.get(name, 0);
    if (startsWith(name, "CFLAGS_") || startsWith(name, "CPPFLAGS_")) {
      std::string obj = name.substr(name.find('_') + 1);
      if (endsWith(obj, ".o")) obj = obj.substr(0, obj.size() - 2);
      for (auto &w : words(value)) perFile[obj + ".c"].push_back(w);
      continue;
    }
    if (optionVariable(name)) for (auto &w : words(value)) flags.push_back(w);
    else if (sourceVariable(name))
      for (auto &w : words(value)) {
        if (endsWith(w, ".c")) sources.push_back(w);
        else if (endsWith(w, ".o") && fileExists(absPath(mv.dir, w.substr(0, w.size() - 2) + ".c"))) sources.push_back(w.substr(0, w.size() - 2) + ".c");
      }
  }
  std::sort(sources.begin(), sources.end());
  sources.erase(std::unique(sources.begin(), sources.end()), sources.end());
  if (sources.empty()) {  // flags only: the caller pairs them with the files it was given
    CompileCommand c;
    c.directory = mv.dir;
    c.args = flags;
    c.origin = "static Makefile";
    out.push_back(c);
    return out;
  }
  for (auto &s : sources) {
    CompileCommand c;
    c.directory = mv.dir;
    c.file = absPath(mv.dir, s);
    c.args = flags;
    for (auto &w : perFile[s]) c.args.push_back(w);
    c.origin = "static Makefile";
    out.push_back(std::move(c));
  }
  return out;
}


// ------------------------------------------------------------------------------------------------ database
namespace {
std::string realPath(const std::string &p) {
  char buf[4096];
  if (realpath(p.c_str(), buf)) return buf;
  return normalize(p);
}
size_t commonSuffix(const std::string &a, const std::string &b) {
  size_t n = 0, i = a.size(), j = b.size();
  size_t comps = 0;
  while (i > 0 && j > 0 && a[i - 1] == b[j - 1]) { --i; --j; ++n; if (a[i] == '/') ++comps; }
  return comps + (i == 0 || j == 0 || a[i - 1] == '/' || b[j - 1] == '/' ? 1 : 0);
}
}  // namespace

void BuildDatabase::add(std::vector<CompileCommand> cmds) {
  for (auto &c : cmds) {
    if (c.file.empty()) {  // flags only
      if (common_.args.empty()) common_ = c;
      continue;
    }
    c.file = realPath(c.file);
    cmds_.push_back(std::move(c));
  }
}

const CompileCommand *BuildDatabase::lookup(const std::string &path) const {
  std::string rp = realPath(path);
  for (auto &c : cmds_)
    if (c.file == rp) return &c;
  // a path that differs only by its prefix (the build ran in another checkout / chroot): longest shared suffix, must be unique
  const CompileCommand *best = nullptr;
  size_t bestScore = 0;
  bool tie = false;
  for (auto &c : cmds_) {
    if (baseName(c.file) != baseName(rp)) continue;
    size_t sc = commonSuffix(c.file, rp);
    if (sc > bestScore) { best = &c; bestScore = sc; tie = false; }
    else if (sc == bestScore) tie = true;
  }
  return tie ? nullptr : best;
}

std::vector<std::string> BuildDatabase::files() const {
  std::vector<std::string> f;
  for (auto &c : cmds_) f.push_back(c.file);
  std::sort(f.begin(), f.end());
  f.erase(std::unique(f.begin(), f.end()), f.end());
  return f;
}

bool loadBuildDatabase(const BuildSource &src, BuildDatabase &db, std::vector<std::string> &notes, std::string &err) {
  if (!src.compileCommands.empty()) {
    std::string perr;
    auto cmds = parseCompileCommands(readFile(src.compileCommands), perr);
    if (!perr.empty()) { err = src.compileCommands + ": " + perr; return false; }
    notes.push_back(src.compileCommands + ": " + std::to_string(cmds.size()) + " C compile command(s)");
    db.add(std::move(cmds));
  }
  if (!src.makefile.empty()) {
    std::string dir = isDirectory(src.makefile) ? src.makefile : dirName(src.makefile);
    dir = realPath(dir);
    bool got = false;
    if (src.mode != "static") {
      std::vector<std::string> margs = src.makeArgs;
      if (!isDirectory(src.makefile) && fileExists(src.makefile)) { margs.insert(margs.begin(), "-f"); margs.insert(margs.begin() + 1, realPath(src.makefile)); }
      if (!src.target.empty()) margs.push_back(src.target);
      std::string out, merr;
      if (runMakeDryRun(dir, margs, src.timeoutSeconds, out, merr)) {
        auto cmds = parseMakeDryRun(out, dir);
        if (!cmds.empty()) {
          notes.push_back("make -n in " + dir + ": " + std::to_string(cmds.size()) + " C compile command(s)");
          db.add(std::move(cmds));
          got = true;
        } else notes.push_back("make -n in " + dir + " printed no C compiler invocations (a target that only links? try --make-target); falling back to a static parse");
      } else notes.push_back(merr + "; falling back to a static parse");
    }
    if (!got) {
      std::vector<std::string> warnings;
      auto cmds = parseMakefileStatic(src.makefile, warnings);
      for (auto &w : warnings) notes.push_back("static Makefile: " + w);
      size_t withFile = 0;
      for (auto &c : cmds) withFile += !c.file.empty();
      notes.push_back("static parse of " + src.makefile + ": " + (withFile ? std::to_string(withFile) + " source file(s) with flags" : std::string("compiler flags only (no source list found)")) +
                      "; per-file conditions and generated flags may be missing");
      db.add(std::move(cmds));
    }
  }
  if (db.size() == 0 && !db.common()) { err = "no compile commands found in the build source"; return false; }
  return true;
}

}  // namespace hlir::buildinfo

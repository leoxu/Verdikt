#include "hlir/link/Link.h"

#include <algorithm>
#include <cctype>
#include <set>
#include <sstream>

namespace hlir::link {
namespace {

bool nameChar(char c) { return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '.' || c == '$'; }

// every `@token` of a text
std::set<std::string> mentioned(const std::string &t) {
  std::set<std::string> out;
  for (size_t i = 0; i < t.size(); ++i) {
    if (t[i] != '@') continue;
    size_t j = i + 1;
    while (j < t.size() && nameChar(t[j])) ++j;
    if (j > i + 1) out.insert(t.substr(i + 1, j - i - 1));
    i = j - 1;
  }
  return out;
}

std::string renameTokens(const std::string &t, const std::map<std::string, std::string> &rn) {
  if (rn.empty()) return t;
  std::string out;
  out.reserve(t.size() + 64);
  for (size_t i = 0; i < t.size(); ++i) {
    out += t[i];
    if (t[i] != '@') continue;
    size_t j = i + 1;
    while (j < t.size() && nameChar(t[j])) ++j;
    std::string tok = t.substr(i + 1, j - i - 1);
    auto it = rn.find(tok);
    out += it == rn.end() ? tok : it->second;
    i = j - 1;
  }
  return out;
}

struct Block { std::string name; std::string text; };
struct Parsed {
  std::vector<std::pair<std::string, std::string>> declares;  // name, line
  std::vector<Block> funcs;
  std::vector<std::string> other;
};

std::string afterAt(const std::string &line, size_t from) {
  size_t i = line.find('@', from);
  if (i == std::string::npos) return "";
  size_t j = i + 1;
  while (j < line.size() && nameChar(line[j])) ++j;
  return line.substr(i + 1, j - i - 1);
}

Parsed parse(const std::string &text) {
  Parsed p;
  std::istringstream in(text);
  std::string line;
  Block cur;
  bool inFunc = false;
  while (std::getline(in, line)) {
    if (inFunc) {
      cur.text += line + "\n";
      if (line == "}") { p.funcs.push_back(std::move(cur)); cur = Block(); inFunc = false; }
      continue;
    }
    if (line.rfind("core.func @", 0) == 0 || line.rfind("core.func internal @", 0) == 0) {  // `internal` = C static linkage
      inFunc = true;
      cur.name = afterAt(line, 0);
      cur.text = line + "\n";
      if (line.back() != '{') { inFunc = false; p.other.push_back(line); }  // not a body (should not happen)
    } else if (line.rfind("core.declare @", 0) == 0) p.declares.push_back({afterAt(line, 0), line});
    else if (!line.empty() && line.rfind("//", 0) != 0) p.other.push_back(line);
  }
  return p;
}

}  // namespace

std::set<std::string> definedFunctionNames(const std::string &text) {
  std::set<std::string> out;
  for (auto &f : parse(text).funcs) out.insert(f.name);
  return out;
}

Result linkUnits(const std::vector<Unit> &units, const std::set<std::string> &modelDefs,
                 const std::set<std::string> &exposed) {
  Result r;
  r.renames.resize(units.size());
  std::vector<std::set<std::string>> internal(units.size()), seen(units.size());
  for (size_t u = 0; u < units.size(); ++u) {
    internal[u].insert(units[u].internalTokens.begin(), units[u].internalTokens.end());
    seen[u] = mentioned(units[u].core);
  }
  // an internal symbol is renamed when another unit has an internal one of that name, when it refers to an external one of
  // that name, or when it collides with a name the ModelDB text defines (appended as plain text after linking, so invisible
  // to the unit-vs-unit comparison above — a kernel header's own real `isdigit` fallback body colliding with libc.core's
  // generic `@isdigit` model is the concrete case this was added for).
  for (size_t u = 0; u < units.size(); ++u)
    for (auto &t : internal[u]) {
      if (!seen[u].count(t)) continue;
      bool clash = modelDefs.count(t) != 0;
      for (size_t v = 0; v < units.size() && !clash; ++v)
        if (v != u && seen[v].count(t)) clash = true;  // internal in v too (distinct entity), or external in v (would bind to ours)
      if (clash && exposed.count(t)) {
        // The caller asked for this static to be visible to the other units. Only unambiguous when one unit has it.
        unsigned owners = 0;
        for (size_t v = 0; v < units.size(); ++v)
          if (internal[v].count(t)) ++owners;
        if (owners == 1) { r.exposeApplied.push_back(t); continue; }
        r.exposeAmbiguous.push_back(t);
      }
      if (clash) r.renames[u][t] = t + ".u" + std::to_string(u);
    }
  std::vector<std::string> texts;
  for (size_t u = 0; u < units.size(); ++u) texts.push_back(renameTokens(units[u].core, r.renames[u]));

  // globals: one size (the largest) and constness (any) per name
  std::map<std::string, unsigned long long> gsize;
  std::set<std::string> gconst;
  const std::string key = "core.global_addr @";
  auto forEachGlobal = [&](std::string &text, auto &&fn) {
    size_t pos = 0;
    while ((pos = text.find(key, pos)) != std::string::npos) {
      size_t ns = pos + key.size(), ne = ns;
      while (ne < text.size() && nameChar(text[ne])) ++ne;
      size_t sp = text.find("{size=", ne), eol = text.find('\n', ne);
      if (sp == std::string::npos || sp > eol) { pos = ne; continue; }
      size_t ds = sp + 6, de = ds;
      while (de < text.size() && std::isdigit(static_cast<unsigned char>(text[de]))) ++de;
      size_t close = text.find('}', de);
      fn(text.substr(ns, ne - ns), ds, de, close);
      pos = de;
    }
  };
  for (auto &t : texts)
    forEachGlobal(t, [&](const std::string &name, size_t ds, size_t de, size_t close) {
      unsigned long long n = std::stoull(t.substr(ds, de - ds));
      auto &g = gsize[name];
      g = std::max(g, n);
      if (t.substr(de, close - de).find("const") != std::string::npos) gconst.insert(name);
    });
  for (auto &t : texts) {  // rewrite back to front so offsets stay valid
    struct Edit { size_t ds, de, close; std::string name; };
    std::vector<Edit> edits;
    forEachGlobal(t, [&](const std::string &name, size_t ds, size_t de, size_t close) { edits.push_back({ds, de, close, name}); });
    for (auto it = edits.rbegin(); it != edits.rend(); ++it) {
      bool hasConst = t.substr(it->de, it->close - it->de).find("const") != std::string::npos;
      std::string repl = std::to_string(gsize[it->name]) + (gconst.count(it->name) && !hasConst ? ", const" : "");
      t.replace(it->ds, it->de - it->ds, repl);
    }
  }

  // merge: first definition of a function wins; declarations of defined functions are dropped
  std::vector<Parsed> parsed;
  for (auto &t : texts) parsed.push_back(parse(t));
  std::set<std::string> defined;
  std::map<std::string, std::string> definedSig;  // name -> "(ptr, i32) -> i32", from the definition's header line
  for (auto &p : parsed)
    for (auto &f : p.funcs) {
      defined.insert(f.name);
      size_t eol = f.text.find('\n'), open = f.text.find('(');
      if (eol == std::string::npos || open == std::string::npos || open > eol) continue;
      size_t end = f.text.rfind('{', eol);
      if (end == std::string::npos || end <= open) continue;
      while (end > open && std::isspace(static_cast<unsigned char>(f.text[end - 1]))) --end;
      definedSig.emplace(f.name, f.text.substr(open, end - open));
    }
  std::map<std::string, std::string> declares;
  std::set<std::string> otherSeen;
  std::vector<std::string> others;
  std::ostringstream body;
  std::set<std::string> emitted;
  for (size_t u = 0; u < parsed.size(); ++u) {
    for (auto &d : parsed[u].declares)
      if (!defined.count(d.first) && !declares.count(d.first)) declares[d.first] = d.second;
    for (auto &o : parsed[u].other) if (otherSeen.insert(o).second) others.push_back(o);
    for (auto &f : parsed[u].funcs) {
      if (!emitted.insert(f.name).second) {
        // C++ inline functions and template instances are legitimately defined in every unit that uses them (ODR): not worth a note
        if (f.name.rfind("_Z", 0) != 0 && f.name.rfind("__hlir_", 0) != 0)
          r.notes.push_back("'" + f.name + "' is defined more than once; the definition of " + units[u].name + " is ignored");
        continue;
      }
      body << f.text;
    }
  }
  std::ostringstream os;
  os << "// linked from:";
  for (auto &u : units) os << " " << u.name;
  os << "\n";
  for (auto &o : others) os << o << "\n";
  std::string stubs;
  // indirect-call dispatchers
  std::string dispatchers;
  std::set<std::string> unknownDecls;
  {
    // key: declare-style signature, the pointer first; ctype: its C type key, "" when any call of the signature may reach it
    // (its address escaped to an incompatible type in some unit, or no unit knew the type)
    struct Cand { std::string name, key, ctype; };
    std::vector<Cand> cands;
    std::map<std::string, size_t> seenCand;
    for (size_t u = 0; u < units.size(); ++u)
      for (auto &c : units[u].addrTaken) {
        std::string nm = linkedName(r, u, c.first);
        auto ct = units[u].addrTakenCTypes.find(c.first);
        std::string ctype = ct == units[u].addrTakenCTypes.end() ? "" : ct->second;
        auto seen = seenCand.find(nm + "|" + c.second);
        if (seen != seenCand.end()) {
          if (cands[seen->second].ctype != ctype) cands[seen->second].ctype = "";  // units disagree: keep it reachable from every call
          continue;
        }
        size_t open = c.second.find('(');
        if (open == std::string::npos) continue;
        seenCand[nm + "|" + c.second] = cands.size();
        cands.push_back({nm, c.second.substr(0, open + 1) + (c.second[open + 1] == ')' ? "ptr" : "ptr, ") + c.second.substr(open + 1), ctype});
      }
    // `dlsym(handle, "foo")` with a literal name: the frontend lowered the call to `@__hlir_dlsym.foo` because it knew
    // the NAME but not the symbol table (DESIGN.md §22.424). Here the whole program is merged, so the name can be
    // resolved. The generated resolver returns NULL *or* `foo`'s address -- a lookup that fails is real code, usually
    // reachable, and the same `fail=nondet` reasoning as libc.core's @dlopen -- and `foo` joins the indirect-call
    // candidates so the call THROUGH that address reaches the body instead of `__hlir_unknown_indirect`.
    //
    // Its C type key is "": the address came back through `void *`, so C11 6.3.2.3p8 gives no grounds to exclude any
    // call of a compatible signature, exactly as for a function whose address escaped to an incompatible type.
    //
    // A name no unit defines is NOT invented: `@__hlir_dlsym.foo` stays a declare, becomes an opaque external, and is
    // reported in `dlsymUnresolved` (and shows up in the scan's opaque-call list under that name).
    {
      std::set<std::string> want;
      for (auto &u : units) want.insert(u.dlsymNames.begin(), u.dlsymNames.end());
      for (const std::string &sym : want) {
        const std::string tn = "__hlir_dlsym." + sym;
        if (!declares.count(tn)) continue;  // no surviving call site after merging
        auto ds = definedSig.find(sym);
        if (ds == definedSig.end()) { r.dlsymUnresolved.push_back(sym); continue; }
        size_t open = ds->second.find('(');
        if (open == std::string::npos) { r.dlsymUnresolved.push_back(sym); continue; }
        std::string key = ds->second.substr(0, open + 1) + (ds->second[open + 1] == ')' ? "ptr" : "ptr, ") +
                          ds->second.substr(open + 1);
        auto sc = seenCand.find(sym + "|" + ds->second);
        if (sc != seenCand.end()) cands[sc->second].ctype = "";
        else { seenCand[sym + "|" + ds->second] = cands.size(); cands.push_back({sym, key, ""}); }
        dispatchers += "core.func @" + tn + "(ptr) -> ptr {\n^entry(%h: ptr):\n"
                       "  %miss = core.nondet {name=\"dlsym_fail." + sym + "\"} : bool\n"
                       "  core.cond_br %miss, ^none, ^found\n^found:\n"
                       "  %a = core.func_addr @" + sym + " : ptr\n  core.return %a\n^none:\n"
                       "  %z = core.const 0 : i64\n  %n = core.int_to_ptr %z : ptr\n  core.return %n\n}\n";
        declares.erase(tn);
        r.dlsymResolved.push_back(sym);
      }
      if (!r.dlsymResolved.empty())
        r.notes.push_back("dlsym: " + std::to_string(r.dlsymResolved.size()) +
                          " literal symbol name(s) resolved to functions of the linked program");
      if (!r.dlsymUnresolved.empty()) {
        std::string ns;
        for (auto &n : r.dlsymUnresolved) ns += (ns.empty() ? "" : ", ") + n;
        r.notes.push_back("dlsym: no unit defines " + ns + "; the call through the result stays opaque");
      }
    }
    std::map<std::string, std::string> callTypes;  // dispatcher name -> C type key of its calls
    for (auto &u : units) callTypes.insert(u.indirectCallCTypes.begin(), u.indirectCallCTypes.end());
    for (auto &d : declares) {
      if (d.first.rfind("__hlir_indirect.", 0) != 0) continue;
      size_t open = d.second.find('(', d.second.find('@'));
      size_t close = d.second.find(')', open);
      if (open == std::string::npos || close == std::string::npos) continue;
      std::string sig = d.second.substr(open);  // "(ptr, i32) -> i32"
      std::string params = d.second.substr(open + 1, close - open - 1), ret = d.second.substr(d.second.find("->", close) + 3);
      std::vector<std::string> types;
      {
        std::istringstream ps(params);
        std::string t;
        while (std::getline(ps, t, ',')) { size_t b = t.find_first_not_of(' '); types.push_back(b == std::string::npos ? t : t.substr(b)); }
      }
      std::string rest;  // the parameters without the function pointer
      for (size_t i = 1; i < types.size(); ++i) rest += (i > 1 ? ", " : "") + types[i];
      std::string args;
      for (size_t i = 1; i < types.size(); ++i) args += (i > 1 ? ", " : "") + ("%a" + std::to_string(i));
      std::ostringstream f;
      f << "core.func @" << d.first << "(" << params << ") -> " << ret << " {\n^entry(%fp: ptr";
      for (size_t i = 1; i < types.size(); ++i) f << ", %a" << i << ": " << types[i];
      f << "):\n";
      bool isVoid = ret == "void";
      // `__hlir_indirect.<sig>.t<hash>`: the call goes through a pointer of a known C type
      auto ck = callTypes.find(d.first);
      std::string callType = ck == callTypes.end() ? "" : ck->second;
      std::vector<std::string> reach;
      for (auto &c : cands) {
        if (c.key != sig) continue;
        if (!cTypesCompatible(callType, c.ctype)) continue;
        size_t k = reach.size();
        reach.push_back(c.name);
        f << "  %fa" << k << " = core.func_addr @" << c.name << " : ptr\n  %eq" << k << " = core.ptr_cmp eq %fp, %fa" << k << " : bool\n"
          << "  core.cond_br %eq" << k << ", ^hit" << k << ", ^next" << k << "\n^hit" << k << ":\n";
        if (isVoid) f << "  core.call @" << c.name << "(" << args << ")\n  core.return\n";
        else f << "  %r" << k << " = core.call @" << c.name << "(" << args << ") : " << ret << "\n  core.return %r" << k << "\n";
        f << "^next" << k << ":\n";
      }
      std::string un = "__hlir_unknown_indirect." + d.first.substr(16);
      if (isVoid) f << "  core.call @" << un << "(" << args << ")\n  core.return\n}\n";
      else f << "  %ro = core.call @" << un << "(" << args << ") : " << ret << "\n  core.return %ro\n}\n";
      dispatchers += f.str();
      r.dispatchers[d.first] = reach;
      unknownDecls.insert("core.declare @" + un + "(" + rest + ") -> " + ret);
    }
  }
  // libffi: `ffi_call(cif, fn, rvalue, avalue)` calls fn with the values avalue[i] points to. The candidate list is the program's
  // address-taken functions; a function whose parameters are all integers/pointers is loaded from avalue by its own types (the
  // cif only repeats them) and its result is stored through rvalue.
  if (declares.count("ffi_call") && !defined.count("ffi_call")) {
    std::ostringstream f;
    f << "core.func @ffi_call(ptr, ptr, ptr, ptr) -> void {\n^entry(%cif: ptr, %fn: ptr, %rv: ptr, %av: ptr):\n";
    std::set<std::string> seen;
    unsigned k = 0;
    auto scalar = [](const std::string &t) { return t == "i8" || t == "i16" || t == "i32" || t == "i64" || t == "ptr"; };
    auto bytesOf = [](const std::string &t) { return t == "i8" ? 1 : t == "i16" ? 2 : t == "i32" ? 4 : 8; };
    for (size_t u = 0; u < units.size(); ++u)
      for (auto &c : units[u].addrTaken) {
        std::string nm = linkedName(r, u, c.first);
        if (!seen.insert(nm).second) continue;
        size_t open = c.second.find('('), close = c.second.find(')');
        if (open == std::string::npos || close == std::string::npos) continue;
        std::string ret = c.second.substr(c.second.find("->", close) + 3);
        std::vector<std::string> types;
        std::istringstream ps(c.second.substr(open + 1, close - open - 1));
        std::string t;
        bool ok = ret == "void" || scalar(ret);
        while (std::getline(ps, t, ',')) {
          size_t b = t.find_first_not_of(' ');
          t = b == std::string::npos ? t : t.substr(b);
          if (!t.empty()) { types.push_back(t); ok = ok && scalar(t); }
        }
        if (!ok || types.size() > 12) continue;
        f << "  %fa" << k << " = core.func_addr @" << nm << " : ptr\n  %eq" << k << " = core.ptr_cmp eq %fn, %fa" << k << " : bool\n"
          << "  core.cond_br %eq" << k << ", ^hit" << k << ", ^next" << k << "\n^hit" << k << ":\n";
        std::string args;
        for (size_t i = 0; i < types.size(); ++i) {
          f << "  %o" << k << "_" << i << " = core.const " << i * 8 << " : i64\n  %s" << k << "_" << i << " = core.ptr_add %av, %o" << k << "_" << i << " {waived=\"ffi argument vector\"} : ptr\n"
            << "  %p" << k << "_" << i << " = core.load %s" << k << "_" << i << " {waived=\"ffi argument vector\"} : ptr\n"
            << "  %v" << k << "_" << i << " = core.load %p" << k << "_" << i << " {waived=\"ffi argument value\"} : " << types[i] << "\n";
          args += (i ? ", " : "") + ("%v" + std::to_string(k) + "_" + std::to_string(i));
        }
        if (ret == "void") f << "  core.call @" << nm << "(" << args << ")\n  core.return\n";
        else {
          f << "  %r" << k << " = core.call @" << nm << "(" << args << ") : " << ret << "\n  %nn" << k << " = core.is_null %rv : bool\n  core.cond_br %nn" << k << ", ^done" << k << ", ^st" << k << "\n^st" << k << ":\n"
            << "  core.store %r" << k << ", %rv {waived=\"ffi result slot\"}\n  core.return\n^done" << k << ":\n  core.return\n";
          (void)bytesOf;
        }
        f << "^next" << k << ":\n";
        ++k;
      }
    f << "  core.return\n}\n";
    dispatchers += f.str();
    r.notes.push_back("libffi: ffi_call is bridged to the " + std::to_string(k) + " address-taken function(s) with integer/pointer signatures");
    declares.erase("ffi_call");
  }
  for (auto &d : declares) {
    if (d.first.rfind("__hlir_indirect.", 0) == 0) continue;  // defined above
    if (d.first.rfind("__hlir_init.", 0) == 0) {  // initialiser of an extern global that no unit defines one for: nothing to do
      stubs += "core.func @" + d.first + "() -> void {\n^entry:\n  core.return\n}\n";
      continue;
    }
    os << d.second << "\n";
    r.unresolved.push_back(d.first);
  }
  for (auto &u : unknownDecls) os << u << "\n";
  os << body.str() << dispatchers << stubs;
  r.core = os.str();
  return r;
}

std::string linkedName(const Result &r, size_t unit, const std::string &fn) {
  if (unit >= r.renames.size()) return fn;
  auto it = r.renames[unit].find(fn);
  return it == r.renames[unit].end() ? fn : it->second;
}

}  // namespace hlir::link

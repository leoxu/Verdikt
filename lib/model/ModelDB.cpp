#include "hlir/model/Model.h"

#include <cctype>
#include <functional>
#include <set>

#include "hlir/support/Yaml.h"

namespace hlir::model {

using yaml::YNode;

namespace {

struct Reader {
  const std::string &file;
  Diagnostics &d;
  bool ok = true;

  void err(unsigned line, const std::string &msg) {
    ok = false;
    Loc l;
    l.file = file;
    l.line = line;
    l.col = 1;
    d.error(msg, l);
  }
  void keys(const YNode &n, std::initializer_list<const char *> allowed, const char *what) {
    if (n.kind != YNode::Map) { err(n.line, std::string(what) + " must be a mapping"); return; }
    std::set<std::string> a(allowed.begin(), allowed.end());
    for (auto &kv : n.map)
      if (!a.count(kv.first)) err(kv.second.line, "unknown key '" + kv.first + "' in " + what);
  }
  std::string str(const YNode &n) {
    if (n.kind != YNode::Scalar) { err(n.line, "expected a string"); return ""; }
    return n.scalar;
  }
  bool integer(const std::string &s, int64_t &v) {
    try {
      size_t n;
      v = std::stoll(s, &n, 0);
      return n == s.size();
    } catch (...) { return false; }
  }
  bool isArgName(const std::string &s, size_t prefix, unsigned &k) {
    if (s.size() <= prefix) return false;
    for (size_t i = prefix; i < s.size(); ++i) if (!isdigit(static_cast<unsigned char>(s[i]))) return false;
    k = static_cast<unsigned>(std::stoul(s.substr(prefix)));
    return true;
  }

  Ref ref(const YNode &n) {
    Ref r;
    std::string s = str(n);
    int64_t v;
    unsigned k;
    if (s == "ret") r.kind = Ref::Ret;
    else if (s == "ret_pointee") r.kind = Ref::RetPointee;
    else if (s.rfind("arg", 0) == 0 && s.size() > 8 && s.compare(s.size() - 8, 8, "_pointee") == 0 && isArgName(s.substr(0, s.size() - 8), 3, k)) { r.kind = Ref::ArgPointee; r.index = k; }
    else if (s.rfind("arg", 0) == 0 && isArgName(s, 3, k)) { r.kind = Ref::Arg; r.index = k; }
    else if (integer(s, v)) { r.kind = Ref::Const; r.value = v; }
    else err(n.line, "bad reference '" + s + "' (expected argK, argK_pointee, ret, ret_pointee or an integer)");
    return r;
  }

  Size size(const YNode &n) {
    Size z;
    std::string s = str(n);
    int64_t v;
    unsigned k;
    if (s == "ret") z.kind = Size::Ret;
    else if (s.rfind("strlen(arg", 0) == 0) {
      bool plus1 = s.size() > 2 && s.compare(s.size() - 2, 2, "+1") == 0;
      std::string core = plus1 ? s.substr(0, s.size() - 2) : s;
      if (core.size() > 8 && core.back() == ')' && isArgName(core.substr(7, core.size() - 8), 3, k)) { z.kind = plus1 ? Size::StrlenPlus1 : Size::Strlen; z.index = k; }
      else err(n.line, "bad size '" + s + "'");
    } else if (s.rfind("arg", 0) == 0 && isArgName(s, 3, k)) { z.kind = Size::Arg; z.index = k; }
    else if (integer(s, v) && v >= 0) { z.kind = Size::Const; z.value = static_cast<uint64_t>(v); }
    else err(n.line, "bad size '" + s + "' (expected an integer, argK, ret, strlen(argK) or strlen(argK)+1)");
    return z;
  }

  void list(const YNode *n, const char *what, std::function<void(const YNode &)> f) {
    if (!n) return;
    if (n->kind == YNode::Map) { f(*n); return; }
    if (n->kind != YNode::Seq) { err(n->line, std::string(what) + " must be a list"); return; }
    for (auto &x : n->seq) f(x);
  }

  CallModel model(const YNode &n) {
    CallModel m;
    m.file = file;
    m.line = n.line;
    keys(n, {"function", "returns", "source", "copy", "fill", "fills_unknown", "points_to", "flow", "sink", "note", "override", "noreturn"}, "model");
    if (!ok) return m;
    if (auto *f = n.get("function")) m.function = str(*f);
    else err(n.line, "model has no 'function'");
    if (auto *ov = n.get("override")) m.overrideBody = ov->kind == YNode::Scalar && ov->scalar == "true";
    if (auto *nr = n.get("noreturn")) { m.noreturn = nr->kind == YNode::Scalar && nr->scalar == "true"; if (m.noreturn) m.overrideBody = true; }
    if (auto *r = n.get("returns")) {
      keys(*r, {"nondet", "value", "arg", "null", "alloc", "strlen"}, "returns");
      if (auto *nd = r->get("nondet")) {
        m.ret.kind = ReturnSpec::Nondet;
        keys(*nd, {"min", "max", "tainted", "default"}, "nondet");
        if (auto *a = nd->get("min")) m.ret.min = ref(*a);
        if (auto *a = nd->get("max")) m.ret.max = ref(*a);
        if (auto *a = nd->get("default")) m.ret.dflt = ref(*a);
        if (auto *t = nd->get("tainted")) { m.ret.taintLabel = str(*t); if (m.ret.taintLabel == "true") m.ret.taintLabel = "input"; if (m.ret.taintLabel == "false") m.ret.taintLabel.clear(); }
        for (auto *b : {&m.ret.min, &m.ret.max, &m.ret.dflt})
          if (*b && (*b)->kind != Ref::Const && (*b)->kind != Ref::Arg) err(nd->line, "min/max/default must be an integer or argK");
      } else if (auto *v = r->get("value")) {
        m.ret.kind = ReturnSpec::Const;
        if (!integer(str(*v), m.ret.value)) err(v->line, "returns.value must be an integer");
      } else if (auto *a = r->get("arg")) {
        m.ret.kind = ReturnSpec::Arg;
        int64_t k;
        if (integer(str(*a), k) && k >= 0) m.ret.arg = static_cast<unsigned>(k); else err(a->line, "returns.arg must be an argument index");
      } else if (auto *sl = r->get("strlen")) {
        m.ret.kind = ReturnSpec::Strlen;
        int64_t k;
        if (integer(str(*sl), k) && k >= 0) m.ret.arg = static_cast<unsigned>(k); else err(sl->line, "returns.strlen must be an argument index");
      } else if (r->get("null")) {
        m.ret.kind = ReturnSpec::Null;
      } else if (auto *al = r->get("alloc")) {
        m.ret.kind = ReturnSpec::Alloc;
        keys(*al, {"size", "zeroed", "may_fail"}, "alloc");
        if (auto *s = al->get("size")) m.ret.allocSize = size(*s); else err(al->line, "alloc needs a size");
        if (auto *z = al->get("zeroed")) m.ret.zeroed = str(*z) == "true";
        if (auto *f = al->get("may_fail")) m.ret.mayFail = str(*f) != "false";
      }
    }
    list(n.get("source"), "source", [&](const YNode &x) {
      keys(x, {"label", "ptr", "size"}, "source");
      SourceSpec s;
      if (auto *l = x.get("label")) s.label = str(*l); else err(x.line, "source needs a label");
      if (auto *p = x.get("ptr")) s.ptr = ref(*p); else err(x.line, "source needs a ptr");
      if (auto *z = x.get("size")) s.size = size(*z); else err(x.line, "source needs a size");
      if (s.ptr.kind != Ref::Arg && s.ptr.kind != Ref::Ret) err(x.line, "source.ptr must be a pointer argument (argK) or ret");
      m.sources.push_back(s);
    });
    list(n.get("copy"), "copy", [&](const YNode &x) {
      keys(x, {"dst", "src", "size"}, "copy");
      CopySpec c;
      if (auto *p = x.get("dst")) c.dst = ref(*p); else err(x.line, "copy needs dst");
      if (auto *p = x.get("src")) c.src = ref(*p); else err(x.line, "copy needs src");
      if (auto *z = x.get("size")) c.size = size(*z); else err(x.line, "copy needs a size");
      if (c.dst.kind != Ref::Arg || c.src.kind != Ref::Arg) err(x.line, "copy.dst/src must be pointer arguments (argK)");
      m.copies.push_back(c);
    });
    list(n.get("fill"), "fill", [&](const YNode &x) {
      keys(x, {"ptr", "value", "size"}, "fill");
      FillSpec f;
      if (auto *p = x.get("ptr")) f.ptr = ref(*p); else err(x.line, "fill needs ptr");
      if (auto *p = x.get("value")) f.value = ref(*p); else err(x.line, "fill needs value");
      if (auto *z = x.get("size")) f.size = size(*z); else err(x.line, "fill needs a size");
      if (f.ptr.kind != Ref::Arg) err(x.line, "fill.ptr must be a pointer argument (argK)");
      m.fills.push_back(f);
    });
    list(n.get("fills_unknown"), "fills_unknown", [&](const YNode &x) {
      keys(x, {"ptr", "size"}, "fills_unknown");
      FillUnknownSpec f;
      if (auto *p = x.get("ptr")) f.ptr = ref(*p); else err(x.line, "fills_unknown needs ptr");
      if (auto *z = x.get("size")) f.size = size(*z); else err(x.line, "fills_unknown needs a size");
      if (f.ptr.kind != Ref::Arg && f.ptr.kind != Ref::Ret)
        err(x.line, "fills_unknown.ptr must be a pointer argument (argK) or ret");
      m.fillsUnknown.push_back(f);
    });
    // points_to: the returned (or an argument's) object holds a POINTER at `offset`, and it is made to point at
    // a fresh object of `size` whose bytes are the attacker's (`source: LABEL`), nobody's (`unknown: true`) or
    // zero (`zeroed: true`). Exactly one of the three must be said: defaulting would make the most consequential
    // part of the model invisible, and this spec exists precisely to stop a buffer's contents being assumed.
    list(n.get("points_to"), "points_to", [&](const YNode &x) {
      keys(x, {"base", "offset", "size", "source", "unknown", "zeroed"}, "points_to");
      PointsToSpec p;
      if (auto *b = x.get("base")) p.base = ref(*b); else err(x.line, "points_to needs base");
      if (p.base.kind != Ref::Arg && p.base.kind != Ref::Ret)
        err(x.line, "points_to.base must be a pointer argument (argK) or ret");
      if (auto *z = x.get("size")) p.size = size(*z); else err(x.line, "points_to needs a size");
      if (auto *o = x.get("offset")) {
        int64_t v;
        if (integer(str(*o), v) && v >= 0) p.offset = static_cast<uint64_t>(v);
        else err(o->line, "points_to.offset must be a non-negative integer");
      }
      if (auto *s = x.get("source")) p.label = str(*s);
      if (auto *u = x.get("unknown")) p.unknown = u->kind == YNode::Scalar && u->scalar == "true";
      if (auto *z = x.get("zeroed")) p.zeroed = z->kind == YNode::Scalar && z->scalar == "true";
      const int said = (!p.label.empty()) + p.unknown + p.zeroed;
      if (said != 1)
        err(x.line, "points_to needs exactly one of source: LABEL, unknown: true, zeroed: true -- what the "
                    "pointee holds is the whole point of the spec and has no safe default");
      m.pointsTo.push_back(p);
    });
    list(n.get("flow"), "flow", [&](const YNode &x) {
      keys(x, {"from", "to", "clear", "size"}, "flow");
      FlowSpec f;
      if (auto *c = x.get("clear")) { f.clear = true; f.to = ref(*c); if (x.get("from") || x.get("to")) err(x.line, "a clearing flow has no from/to"); }
      else {
        if (auto *p = x.get("from")) f.from = ref(*p); else err(x.line, "flow needs from (or clear)");
        if (auto *p = x.get("to")) f.to = ref(*p); else err(x.line, "flow needs to");
      }
      if (auto *z = x.get("size")) f.size = size(*z);
      bool pointee = f.from.kind == Ref::ArgPointee || f.to.kind == Ref::ArgPointee || f.to.kind == Ref::RetPointee;
      if (pointee && f.size.kind == Size::None) f.size.kind = Size::Const, f.size.value = 1;
      m.flows.push_back(f);
    });
    list(n.get("sink"), "sink", [&](const YNode &x) {
      keys(x, {"kind", "arg"}, "sink");
      SinkSpec s;
      if (auto *k = x.get("kind")) s.kind = str(*k); else err(x.line, "sink needs a kind");
      if (auto *a = x.get("arg")) s.arg = ref(*a); else err(x.line, "sink needs an arg");
      if (s.arg.kind != Ref::Arg && s.arg.kind != Ref::ArgPointee) err(x.line, "sink.arg must be argK or argK_pointee");
      m.sinks.push_back(s);
    });
    return m;
  }
};

}  // namespace

bool loadExterns(const std::string &text, const std::string &path, ExternsFile &out, Diagnostics &diags) {
  YNode root;
  if (!yaml::parseYaml(text, path, root, diags)) return false;
  Reader r{path, diags};
  r.keys(root, {"models", "skip", "argv"}, "externs file");
  ExternsFile f;
  f.path = path;
  std::string dir = path.substr(0, path.find_last_of('/') + 1);  // "" when the path has no directory part
  if (auto *ms = root.get("models")) {
    if (ms->kind != YNode::Seq) r.err(ms->line, "'models' must be a list of paths");
    else
      for (auto &n : ms->seq) {
        std::string p = r.str(n);
        if (p.empty()) continue;
        f.modelPaths.push_back(p[0] == '/' ? p : dir + p);
      }
  }
  if (auto *av = root.get("argv")) {
    if (av->kind != YNode::Seq) r.err(av->line, "'argv' must be a list of strings, argv[0] first");
    else
      for (auto &n : av->seq) f.argv.push_back(r.str(n));
    if (r.ok && f.argv.empty()) r.err(av->line, "'argv' may not be empty: argv[0] is the program name");
  }
  if (auto *ss = root.get("skip")) {
    if (ss->kind != YNode::Seq) r.err(ss->line, "'skip' must be a list");
    else
      for (auto &n : ss->seq) {
        r.keys(n, {"function", "reason"}, "skip entry");
        ExternsFile::Skip sk;
        sk.line = n.line;
        if (auto *fn = n.get("function")) sk.function = r.str(*fn); else r.err(n.line, "a skip entry needs a function");
        // The reason is mandatory on purpose. A skip with no reason is indistinguishable from an omission, which
        // is the exact confusion this file exists to remove.
        if (auto *rs = n.get("reason")) sk.reason = r.str(*rs); else r.err(n.line, "a skip entry needs a reason: it is a claim about the program, not a mute");
        if (sk.reason.empty() && r.ok) r.err(n.line, "a skip entry's reason may not be empty");
        f.skips.push_back(sk);
      }
  }
  if (!r.ok) return false;
  std::set<std::string> seen;
  for (auto &sk : f.skips)
    if (!seen.insert(sk.function).second) { r.err(sk.line, "'" + sk.function + "' is skipped twice"); return false; }
  out = std::move(f);
  return true;
}

bool ModelDB::load(const std::string &text, const std::string &path, Diagnostics &diags) {
  YNode root;
  if (!yaml::parseYaml(text, path, root, diags)) return false;
  Reader r{path, diags};
  r.keys(root, {"models"}, "model file");
  auto *list = root.get("models");
  if (!list || list->kind != YNode::Seq) { r.err(list ? list->line : 1, "'models' must be a list"); return false; }
  std::map<std::string, CallModel> added;
  for (auto &n : list->seq) {
    CallModel m = r.model(n);
    if (!r.ok) return false;
    if (added.count(m.function)) { r.err(n.line, "duplicate model for '" + m.function + "'"); return false; }
    added.emplace(m.function, std::move(m));
  }
  for (auto &kv : added) models_[kv.first] = std::move(kv.second);  // later files override earlier ones
  return true;
}

bool ModelDB::setUntrusted(const std::string &pattern, const std::string &label, unsigned outMax, std::string &err) {
  try {
    utRe_ = std::make_shared<std::regex>(pattern, std::regex::ECMAScript);
  } catch (const std::regex_error &e) {
    err = "bad untrusted-API pattern '" + pattern + "': " + e.what();
    return false;
  }
  utLabel_ = label.empty() ? "untrusted" : label;
  utOut_ = outMax;
  utCache_.clear();
  return true;
}

bool ModelDB::untrusted(const std::string &function, std::string &label, unsigned &outMax) const {
  if (!utRe_ || models_.count(function)) return false;
  auto it = utCache_.find(function);
  if (it == utCache_.end()) it = utCache_.emplace(function, std::regex_search(function, *utRe_)).first;
  if (!it->second) return false;
  label = utLabel_;
  outMax = utOut_;
  return true;
}

const CallModel *ModelDB::lookup(const std::string &function) const {
  auto it = models_.find(function);
  if (it != models_.end()) return &it->second;
  return opaque_ ? &opaqueModel_ : nullptr;
}

}  // namespace hlir::model

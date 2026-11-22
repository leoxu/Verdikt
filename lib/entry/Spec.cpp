#include "hlir/entry/Spec.h"

#include <set>

#include "hlir/support/Yaml.h"

namespace hlir::entry {

using yaml::YNode;
using yaml::parseYaml;

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

  bool asInt(const YNode &n, int64_t &v) {
    if (n.kind != YNode::Scalar) { err(n.line, "expected an integer"); return false; }
    const std::string &s = n.scalar;
    static const struct { const char *n; int64_t v; } names[] = {
        {"INT_MAX", 2147483647LL}, {"INT_MIN", -2147483648LL}, {"UINT_MAX", 4294967295LL}, {"INT64_MAX", INT64_MAX},
        {"UINT16_MAX", 65535}, {"UINT8_MAX", 255}, {"SIZE_MAX", -1}};
    for (auto &e : names)
      if (s == e.n) { v = e.v; return true; }
    try {
      size_t n2;
      bool neg = !s.empty() && s[0] == '-';
      std::string body = neg ? s.substr(1) : s;
      uint64_t u = (body.rfind("0x", 0) == 0) ? std::stoull(body.substr(2), &n2, 16) : std::stoull(body, &n2, 10);
      if (n2 != (body.rfind("0x", 0) == 0 ? body.size() - 2 : body.size())) throw 1;
      v = neg ? -static_cast<int64_t>(u) : static_cast<int64_t>(u);
      return true;
    } catch (...) {
      err(n.line, "expected an integer, got '" + s + "'");
      return false;
    }
  }
  bool asBool(const YNode &n, bool &v) {
    if (n.kind == YNode::Scalar && (n.scalar == "true" || n.scalar == "false")) { v = n.scalar == "true"; return true; }
    err(n.line, "expected true or false");
    return false;
  }
  std::string asStr(const YNode &n) {
    if (n.kind != YNode::Scalar) { err(n.line, "expected a string"); return ""; }
    return n.scalar;
  }
  void checkKeys(const YNode &n, std::initializer_list<const char *> allowed, const char *what) {
    if (n.kind != YNode::Map) { err(n.line, std::string(what) + " must be a mapping"); return; }
    std::set<std::string> ok2(allowed.begin(), allowed.end());
    for (auto &kv : n.map)
      if (!ok2.count(kv.first)) err(kv.second.line, "unknown key '" + kv.first + "' in " + what);
  }

  void field(const YNode &n, FieldSpec &f, unsigned depth) {
    f.line = n.line;
    checkKeys(n, {"offset", "kind", "target", "at", "taint", "content", "size", "nullable", "targets", "fields", "owned", "same_alloc", "externally_mutable", "where"}, "pointer field spec");
    if (n.kind != YNode::Map) return;
    if (depth > 4) { err(n.line, "pointer fields are nested too deeply (max 4 levels)"); return; }
    int64_t v;
    if (auto *o = n.get("offset")) { if (asInt(*o, v) && v >= 0) f.offset = static_cast<uint64_t>(v); else if (ok) err(o->line, "offset must be >= 0"); }
    else err(n.line, "pointer field has no 'offset'");
    if (auto *k = n.get("kind")) {
      f.kind = asStr(*k);
      if (f.kind != "buffer" && f.kind != "funcptr" && f.kind != "self") err(k->line, "field kind must be buffer, funcptr or self");
    }
    if (auto *t = n.get("taint")) {
      f.taint = asStr(*t);
      if (f.taint != "none" && f.taint != "pointee") err(t->line, "field taint must be none or pointee");
    }
    if (auto *c = n.get("content")) {
      f.content = asStr(*c);
      if (f.content != "zero" && f.content != "unknown") err(c->line, "field content must be zero or unknown");
      else if (f.content == "unknown" && f.kind != "buffer") err(c->line, "'content' only applies to buffer fields");
    }
    if (auto *s = n.get("size")) {
      checkKeys(*s, {"min", "max", "from_field"}, "size");
      if (auto *a = s->get("min")) { if (asInt(*a, v) && v >= 0) f.sizeMin = static_cast<uint64_t>(v); else if (ok) err(a->line, "size.min must be >= 0"); }
      if (auto *b = s->get("max")) { if (asInt(*b, v) && v >= 0) f.sizeMax = static_cast<uint64_t>(v); else if (ok) err(b->line, "size.max must be >= 0"); }
      if (f.sizeMin && f.sizeMax && *f.sizeMin > *f.sizeMax) err(s->line, "size.min > size.max");
      if (auto *ff = s->get("from_field")) {
        checkKeys(*ff, {"offset", "type", "elem"}, "size.from_field");
        if (auto *o = ff->get("offset")) { if (asInt(*o, v) && v >= 0) f.sizeFromOffset = static_cast<uint64_t>(v); else if (ok) err(o->line, "size.from_field.offset must be >= 0"); }
        else err(ff->line, "size.from_field needs 'offset'");
        if (auto *ty = ff->get("type")) f.sizeFromType = asStr(*ty);
        else err(ff->line, "size.from_field needs 'type'");
        // `elem`: the sibling holds an element count, so the allocation is `<field> * elem` bytes (see FieldSpec).
        if (auto *el = ff->get("elem")) { if (asInt(*el, v) && v >= 1) f.sizeFromElem = static_cast<uint64_t>(v); else if (ok) err(el->line, "size.from_field.elem must be >= 1"); }
        if (f.sizeMin || f.sizeMax) err(s->line, "size.from_field cannot be combined with min/max");
      }
    }
    if (auto *nl = n.get("nullable")) { bool b; if (asBool(*nl, b)) f.nullable = b; }
    if (auto *ow = n.get("owned")) { asBool(*ow, f.owned); if (f.owned && f.kind != "buffer") err(ow->line, "'owned' only applies to buffer fields"); }
    if (auto *em = n.get("externally_mutable")) {
      asBool(*em, f.externallyMutable);
      if (f.externallyMutable && f.kind != "buffer") err(em->line, "'externally_mutable' only applies to buffer fields");
    }
    if (auto *t = n.get("targets")) {
      if (t->kind != YNode::Seq || t->seq.empty()) err(t->line, "targets must be a non-empty list of function names");
      else for (auto &x : t->seq) f.targets.push_back(asStr(x));
    }
    if (auto *t = n.get("target")) { if (asInt(*t, v) && v >= 0) f.target = static_cast<uint64_t>(v); else if (ok) err(t->line, "target must be >= 0"); }
    if (auto *a = n.get("at")) {
      if (f.kind != "buffer") err(a->line, "'at' only applies to buffer fields");
      else if (asInt(*a, v) && v >= 0) f.at = static_cast<uint64_t>(v);
      else if (ok) err(a->line, "at must be >= 0");
    }
    if (auto *sa = n.get("same_alloc")) {
      if (f.kind != "buffer") err(sa->line, "'same_alloc' only applies to buffer fields");
      checkKeys(*sa, {"offset", "pos"}, "same_alloc");
      if (auto *o = sa->get("offset")) { if (asInt(*o, v) && v >= 0) f.sameAllocOffset = static_cast<uint64_t>(v); else if (ok) err(o->line, "same_alloc.offset must be >= 0"); }
      else err(sa->line, "same_alloc needs 'offset'");
      // `pos`: "end" (default) is one-past-the-end, "inside" a free offset within the sibling's object (see FieldSpec)
      if (auto *ps2 = sa->get("pos")) {
        std::string w = asStr(*ps2);
        if (w == "inside") f.sameAllocInside = true;
        else if (w != "end") err(ps2->line, "same_alloc.pos must be end or inside");
      }
      if (n.get("size")) err(sa->line, "'same_alloc' cannot be combined with 'size'");
      if (n.get("at")) err(sa->line, "'same_alloc' cannot be combined with 'at'");
      if (n.get("fields")) err(sa->line, "'same_alloc' cannot be combined with 'fields'");
      if (n.get("owned")) err(sa->line, "'same_alloc' cannot be combined with 'owned'");
      if (n.get("nullable")) err(sa->line, "'same_alloc' cannot be combined with 'nullable'");
      if (n.get("externally_mutable")) err(sa->line, "'same_alloc' cannot be combined with 'externally_mutable'");
    }
    if (f.kind == "self" && !n.get("target")) err(n.line, "a self field needs 'target' (the offset it points to)");
    if (f.kind != "self" && n.get("target")) err(n.line, "'target' only applies to self fields");
    if (f.kind == "self" && (n.get("size") || n.get("fields") || n.get("taint") || n.get("nullable") || n.get("targets"))) err(n.line, "a self field only has 'offset' and 'target'");
    if (f.kind == "funcptr" && f.targets.empty()) err(n.line, "a funcptr field needs 'targets'");
    if (f.kind == "buffer" && !f.targets.empty()) err(n.line, "'targets' only applies to funcptr fields");
    if (f.sizeFromOffset && n.get("fields")) err(n.line, "size.from_field cannot be combined with 'fields' (its size isn't known until the harness runs)");
    // preconditions on the integers inside the object this field points at (see FieldSpec::where)
    if (auto *wh = n.get("where")) {
      if (f.kind != "buffer") err(wh->line, "'where' only applies to buffer fields");
      else if (wh->kind != YNode::Seq) err(wh->line, "where must be a list");
      else for (auto &x : wh->seq) { WhereSpec w; where(x, w); f.where.push_back(std::move(w)); }
    }
    if (auto *fl = n.get("fields")) {
      if (f.kind == "funcptr") err(fl->line, "a funcptr field has no pointee fields");
      else if (fl->kind != YNode::Seq) err(fl->line, "fields must be a list");
      else for (auto &x : fl->seq) { FieldSpec c; field(x, c, depth + 1); f.fields.push_back(std::move(c)); }
    }
  }

  void bound(const YNode &n, BoundSpec &b, std::initializer_list<const char *> extra, const char *what) {
    b.line = n.line;
    b.file = file;
    std::vector<const char *> keys = {"type", "range", "enum", "value"};
    keys.insert(keys.end(), extra.begin(), extra.end());
    if (n.kind != YNode::Map) { err(n.line, std::string(what) + " must be a mapping"); return; }
    std::set<std::string> ok2(keys.begin(), keys.end());
    for (auto &kv : n.map)
      if (!ok2.count(kv.first)) err(kv.second.line, "unknown key '" + kv.first + "' in " + what);
    if (auto *t = n.get("type")) b.type = asStr(*t);
    else err(n.line, std::string(what) + " needs a 'type' (the integer type of the value)");
    if (auto *r = n.get("range")) {
      if (r->kind != YNode::Seq || r->seq.size() != 2) err(r->line, "range must be [lo, hi]");
      else {
        int64_t lo = 0, hi = 0;
        if (asInt(r->seq[0], lo) && asInt(r->seq[1], hi)) {
          if (lo > hi) err(r->line, "empty range: lo > hi");
          b.lo = lo;
          b.hi = hi;
        }
      }
    }
    if (auto *e = n.get("enum")) {
      if (e->kind != YNode::Seq || e->seq.empty()) err(e->line, "enum must be a non-empty list");
      else for (auto &x : e->seq) { int64_t v; if (asInt(x, v)) b.enumValues.push_back(v); }
    }
    if (auto *v = n.get("value")) { int64_t x; if (asInt(*v, x)) b.value = x; }
    if (!b.lo && b.enumValues.empty() && !b.value) err(n.line, std::string(what) + " needs a range, an enum or a value");
  }
  void elements(const YNode &n, ElementsSpec &e) {
    bound(n, e, {"count"}, "elements spec");
    if (auto *c = n.get("count")) e.count = asStr(*c);
  }
  void where(const YNode &n, WhereSpec &w) {
    bound(n, w, {"offset"}, "where spec");
    if (auto *o = n.get("offset")) { int64_t v; if (asInt(*o, v) && v >= 0) w.offset = static_cast<uint64_t>(v); else if (ok) err(o->line, "offset must be >= 0"); }
    else err(n.line, "where spec needs an 'offset'");
  }

  void param(const std::string &name, const YNode &n, ParamSpec &p) {
    p.name = name;
    p.line = n.line;
    checkKeys(n, {"taint", "content", "kind", "type", "range", "size", "nullable", "enum", "value", "fields", "at", "owned", "elements", "where",
                  "elem_bits", "key_bits", "val_bits", "externally_mutable"}, "parameter spec");
    if (n.kind != YNode::Map) return;
    if (auto *t = n.get("taint")) {
      p.taint = asStr(*t);
      if (p.taint != "none" && p.taint != "value" && p.taint != "pointee" && p.taint != "both") err(t->line, "taint must be none, value, pointee or both");
    }
    if (auto *k = n.get("kind")) {
      p.kind = asStr(*k);
      if (p.kind != "buffer" && p.kind != "cstring" && p.kind != "string" && p.kind != "wstring" && p.kind != "vector" && p.kind != "map")
        err(k->line, "kind must be buffer, cstring, string, wstring, vector or map");
    }
    if (auto *t = n.get("type")) p.type = asStr(*t);
    if (auto *r = n.get("range")) {
      if (r->kind != YNode::Seq || r->seq.size() != 2) err(r->line, "range must be [lo, hi]");
      else {
        int64_t lo = 0, hi = 0;
        if (asInt(r->seq[0], lo) && asInt(r->seq[1], hi)) {
          if (lo > hi) err(r->line, "empty range: lo > hi");
          p.lo = lo;
          p.hi = hi;
        }
      }
    }
    if (auto *s = n.get("size")) {
      checkKeys(*s, {"min", "max", "from_param"}, "size");
      int64_t v;
      if (auto *a = s->get("min")) { if (asInt(*a, v) && v >= 0) p.sizeMin = static_cast<uint64_t>(v); else if (ok) err(a->line, "size.min must be >= 0"); }
      if (auto *b = s->get("max")) { if (asInt(*b, v) && v >= 0) p.sizeMax = static_cast<uint64_t>(v); else if (ok) err(b->line, "size.max must be >= 0"); }
      if (p.sizeMin && p.sizeMax && *p.sizeMin > *p.sizeMax) err(s->line, "size.min > size.max");
      if (auto *fp = s->get("from_param")) {
        checkKeys(*fp, {"name"}, "size.from_param");
        if (auto *nm = fp->get("name")) p.sizeFromParam = asStr(*nm);
        else err(fp->line, "size.from_param needs 'name'");
        if (p.sizeMin || p.sizeMax) err(s->line, "size.from_param cannot be combined with min/max");
        if (n.get("fields")) err(s->line, "size.from_param cannot be combined with 'fields' (its size isn't known until the harness runs)");
        if (n.get("at")) err(s->line, "size.from_param cannot be combined with 'at'");
      }
    }
    if (auto *nl = n.get("nullable")) { bool b; if (asBool(*nl, b)) p.nullable = b; }
    if (auto *e = n.get("enum")) {
      if (e->kind != YNode::Seq || e->seq.empty()) err(e->line, "enum must be a non-empty list");
      else for (auto &x : e->seq) { int64_t v; if (asInt(x, v)) p.enumValues.push_back(v); }
    }
    if (auto *v = n.get("value")) { int64_t x; if (asInt(*v, x)) p.value = x; }
    if (auto *fl = n.get("fields")) {
      if (fl->kind != YNode::Seq) err(fl->line, "fields must be a list");
      else for (auto &x : fl->seq) { FieldSpec f; field(x, f, 1); p.fields.push_back(std::move(f)); }
    }
    if (auto *a = n.get("at")) { int64_t v; if (asInt(*a, v) && v >= 0) p.at = static_cast<uint64_t>(v); else if (ok) err(a->line, "at must be >= 0"); }
    if (auto *o = n.get("owned")) asBool(*o, p.owned);
    if (auto *em = n.get("externally_mutable")) asBool(*em, p.externallyMutable);
    if (auto *c = n.get("content")) {
      p.content = asStr(*c);
      if (p.content != "zero" && p.content != "unknown") err(c->line, "content must be zero or unknown");
    }
    if (auto *el = n.get("elements")) {
      if (el->kind == YNode::Seq) for (auto &x : el->seq) { ElementsSpec e; elements(x, e); p.elements.push_back(std::move(e)); }
      else { ElementsSpec e; elements(*el, e); p.elements.push_back(std::move(e)); }
    }
    if (auto *wh = n.get("where")) {
      if (wh->kind != YNode::Seq) err(wh->line, "where must be a list");
      else for (auto &x : wh->seq) { WhereSpec w; where(x, w); p.where.push_back(std::move(w)); }
    }
    auto bits = [&](const char *key, std::optional<unsigned> &out) {
      if (auto *b = n.get(key)) {
        int64_t v;
        if (asInt(*b, v) && (v == 8 || v == 16 || v == 32 || v == 64)) out = static_cast<unsigned>(v);
        else if (ok) err(b->line, std::string(key) + " must be 8, 16, 32 or 64");
      }
    };
    bits("elem_bits", p.elemBits);
    bits("key_bits", p.keyBits);
    bits("val_bits", p.valBits);
    if (p.elemBits && p.kind != "vector") err(n.line, "elem_bits only applies to kind: vector");
    if ((p.keyBits || p.valBits) && p.kind != "map") err(n.line, "key_bits/val_bits only apply to kind: map");
  }
};

}  // namespace

bool applyPreconditions(const std::string &text, const std::string &path, EntryFile &file, Diagnostics &diags) {
  YNode root;
  if (!parseYaml(text, path, root, diags)) return false;
  Reader r{path, diags};
  r.checkKeys(root, {"preconditions"}, "preconditions file");
  auto *pl = root.get("preconditions");
  if (!pl || pl->kind != YNode::Seq) { r.err(pl ? pl->line : 1, "preconditions must be a list"); return false; }
  for (auto &en : pl->seq) {
    r.checkKeys(en, {"function", "params", "relations"}, "precondition entry");
    if (!r.ok) return false;
    auto *fn = en.get("function");
    if (!fn) { r.err(en.line, "precondition entry has no 'function'"); continue; }
    std::string name = r.asStr(*fn);
    EntrySpec *es = nullptr;
    for (auto &e : file.entries) if (e.function == name) es = &e;
    if (!es) continue;  // preconditions for entries this run does not analyse are fine
    if (auto *ps = en.get("params")) {
      if (ps->kind != YNode::Map) { r.err(ps->line, "params must be a mapping from parameter name to its preconditions"); continue; }
      for (auto &kv : ps->map) {
        ParamSpec *p = nullptr;
        for (auto &x : es->params) if (x.name == kv.first) p = &x;
        const YNode &n = kv.second;
        r.checkKeys(n, {"range", "enum", "size", "nullable", "value", "elements", "where"}, "parameter preconditions");
        if (!r.ok) return false;
        ParamSpec tmp;  // parsed with the ordinary reader, then merged
        r.param(kv.first, n, tmp);
        if (!p) {  // a parameter the entry spec did not mention: it is untainted with legal defaults, now with these constraints
          es->params.push_back(ParamSpec{});
          p = &es->params.back();
          p->name = kv.first;
          p->line = es->line;
        }
        if (tmp.lo) { p->lo = tmp.lo; p->hi = tmp.hi; p->overrideFile = path; p->overrideLine = tmp.line; }
        if (!tmp.enumValues.empty()) { p->enumValues = tmp.enumValues; p->overrideFile = path; p->overrideLine = tmp.line; }
        if (tmp.sizeMin || tmp.sizeMax) { p->sizeMin = tmp.sizeMin; p->sizeMax = tmp.sizeMax; p->overrideFile = path; p->overrideLine = tmp.line; }
        if (tmp.nullable) p->nullable = tmp.nullable;
        if (tmp.value) p->value = tmp.value;
        for (auto &e : tmp.elements) p->elements.push_back(e);
        for (auto &w : tmp.where) p->where.push_back(w);
      }
    }
    if (auto *rl = en.get("relations")) {
      if (rl->kind != YNode::Seq) r.err(rl->line, "relations must be a list of strings");
      else for (auto &x : rl->seq) es->relations.push_back({r.asStr(x), x.line, path});
    }
  }
  return r.ok && !diags.hasErrors();
}

bool parseEntrySpec(const std::string &text, const std::string &path, EntryFile &out, Diagnostics &diags) {
  YNode root;
  if (!parseYaml(text, path, root, diags)) return false;
  Reader r{path, diags};
  out = EntryFile{};
  out.path = path;
  r.checkKeys(root, {"defaults", "init", "taint_entries"}, "specification");
  if (!r.ok) return false;
  if (auto *d = root.get("defaults")) {
    r.checkKeys(*d, {"attacker_model", "max_obj", "ptr_nullable", "depth", "benign_seed", "uninit_param_content"}, "defaults");
    int64_t v;
    if (auto *m = d->get("max_obj")) { if (r.asInt(*m, v) && v > 0) out.defaults.maxObj = static_cast<uint64_t>(v); else if (r.ok) r.err(m->line, "max_obj must be positive"); }
    if (auto *n = d->get("ptr_nullable")) r.asBool(*n, out.defaults.nullable);
    if (auto *b = d->get("benign_seed")) r.asBool(*b, out.defaults.benignSeed);
    if (auto *a = d->get("attacker_model")) {
      if (r.asStr(*a) != "full_type") r.err(a->line, "only attacker_model: full_type is implemented");
    }
  }
  // `init:` -- the project's own initialiser(s), run before the entry (Spec.h InitSpec, DESIGN.md §22.368).
  // Only `functions:` exists: every other part of the design (stop functions, the repair past exit paths, per-
  // configuration prologues) has no consumer yet, and a parsed-but-inert key is the mistake this very feature is
  // fixing elsewhere, so it is an unknown-key error until the code behind it lands.
  if (auto *in = root.get("init")) {
    r.checkKeys(*in, {"functions"}, "init");
    out.init.line = in->line;
    auto *fs = in->get("functions");
    if (!fs || fs->kind != YNode::Seq) {
      r.err(in->line, "init.functions must be a list of function names");
    } else {
      for (auto &f : fs->seq) {
        std::string n = r.asStr(f);
        if (n.empty()) r.err(f.line, "init.functions entries must be function names");
        else out.init.functions.push_back(n);
      }
      if (out.init.functions.empty()) r.err(in->line, "init.functions is empty: drop the `init:` block instead");
    }
  }
  auto *te = root.get("taint_entries");
  if (!te || te->kind != YNode::Seq) { r.err(te ? te->line : 1, "taint_entries must be a list"); return false; }
  for (auto &en : te->seq) {
    r.checkKeys(en, {"function", "label", "setup", "params", "relations", "assumptions", "trusted_len"}, "entry");
    if (!r.ok) return false;
    EntrySpec e;
    e.line = en.line;
    if (auto *f = en.get("function")) e.function = r.asStr(*f);
    else r.err(en.line, "entry has no 'function'");
    if (auto *l = en.get("label")) e.label = r.asStr(*l);
    if (auto *su = en.get("setup")) {
      r.checkKeys(*su, {"function", "session_param", "ctor_param", "success"}, "setup");
      e.setup.line = su->line;
      if (auto *x = su->get("function")) e.setup.function = r.asStr(*x);
      if (auto *x = su->get("session_param")) e.setup.sessionParam = r.asStr(*x);
      if (auto *x = su->get("ctor_param")) e.setup.ctorParam = r.asStr(*x);
      if (auto *x = su->get("success")) e.setup.success = r.asStr(*x);
      if (e.setup.function.empty()) r.err(su->line, "setup needs a 'function': the session constructor to run");
      if (e.setup.sessionParam.empty()) r.err(su->line, "setup needs 'session_param': which parameter of this entry the constructor builds");
      if (e.setup.ctorParam.empty()) r.err(su->line, "setup needs 'ctor_param': which parameter of the constructor is that same object");
    }
    if (auto *ps = en.get("params")) {
      if (ps->kind != YNode::Map) r.err(ps->line, "params must be a mapping from parameter name to its spec");
      else for (auto &kv : ps->map) { ParamSpec p; r.param(kv.first, kv.second, p); e.params.push_back(std::move(p)); }
    }
    if (auto *rl = en.get("relations")) {
      if (rl->kind != YNode::Seq) r.err(rl->line, "relations must be a list of strings");
      else for (auto &x : rl->seq) e.relations.push_back({r.asStr(x), x.line});
    }
    if (auto *as = en.get("assumptions")) {  // narrowings to NAME in the report; they add no constraint (see EntrySpec)
      if (as->kind != YNode::Seq) r.err(as->line, "assumptions must be a list of strings");
      else for (auto &x : as->seq) e.assumptions.push_back({r.asStr(x), x.line});
    }
    if (auto *tl = en.get("trusted_len")) {  // shorthand: buffer size == (size_t) length
      r.checkKeys(*tl, {"buf", "len"}, "trusted_len");
      auto *b = tl->get("buf"), *l = tl->get("len");
      if (!b || !l) r.err(tl->line, "trusted_len needs 'buf' and 'len'");
      else e.relations.push_back({"size(" + r.asStr(*b) + ") == (size_t)" + r.asStr(*l), tl->line});
    }
    out.entries.push_back(std::move(e));
  }
  return r.ok && !diags.hasErrors();
}

}  // namespace hlir::entry

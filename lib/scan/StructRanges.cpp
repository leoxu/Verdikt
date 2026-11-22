// Reader for models/structs/*.yaml (see hlir/scan/StructRanges.h, DESIGN.md §22.480).
//
// Strict like the interface reader and for the same reason: this is a small hand-written file that NARROWS what
// the analysis will consider, and a typo in it would silently delete findings. Unknown keys, missing `why`,
// ranges a field's own type cannot hold -- all errors with a line number, never a shrug.
#include "hlir/scan/StructRanges.h"

#include <set>

#include "hlir/support/Yaml.h"

namespace hlir::structranges {

using yaml::YNode;

namespace {

struct Reader {
  Diagnostics &d;
  std::string file;
  bool ok = true;

  void err(unsigned line, const std::string &m) {
    d.error(m, Loc{file, line, 1});
    ok = false;
  }
  std::string str(const YNode &n) { return n.kind == YNode::Scalar ? n.scalar : std::string(); }
  void keys(const YNode &n, std::initializer_list<const char *> allowed, const char *what) {
    if (n.kind != YNode::Map) return;
    std::set<std::string> a(allowed.begin(), allowed.end());
    for (auto &kv : n.map)
      if (!a.count(kv.first)) err(kv.second.line, "unknown key '" + kv.first + "' in " + what);
  }
  bool integer(const std::string &s, int64_t &v) {
    try {
      size_t n;
      v = std::stoll(s, &n, 0);
      return n == s.size();
    } catch (...) { return false; }
  }
  int64_t num(const YNode &n, bool &good) {
    int64_t v = 0;
    good = integer(str(n), v);
    if (!good) err(n.line, "expected an integer, got '" + str(n) + "'");
    return v;
  }

  void field(const YNode &n, FieldRange &f) {
    f.line = n.line;
    keys(n, {"name", "offset", "bits", "signed", "range", "enum", "why"}, "field range");
    bool g = false;
    if (const YNode *v = n.get("name")) f.name = str(*v);
    else err(n.line, "a field range needs 'name' (for the assumption text)");
    if (const YNode *v = n.get("offset")) { int64_t x = num(*v, g); if (g && x >= 0) f.offset = (uint64_t)x; else if (g) err(v->line, "offset must not be negative"); }
    else err(n.line, "field '" + f.name + "' has no 'offset'");
    if (const YNode *v = n.get("bits")) {
      int64_t x = num(*v, g);
      if (g && (x == 8 || x == 16 || x == 32 || x == 64)) f.bits = (unsigned)x;
      else if (g) err(v->line, "bits must be 8, 16, 32 or 64");
    } else err(n.line, "field '" + f.name + "' has no 'bits'");
    if (const YNode *v = n.get("signed")) f.isSigned = str(*v) == "true";
    if (const YNode *v = n.get("range")) {
      if (v->kind != YNode::Seq || v->seq.size() != 2) err(v->line, "range must be a list of two integers");
      else {
        f.lo = num(v->seq[0], g);
        bool g2 = false;
        f.hi = num(v->seq[1], g2);
        f.hasRange = g && g2;
        if (f.hasRange && f.lo > f.hi) err(v->line, "range low bound is above its high bound");
      }
    }
    if (const YNode *v = n.get("enum")) {
      if (v->kind != YNode::Seq || v->seq.empty()) err(v->line, "enum must be a non-empty list of integers");
      else
        for (auto &x : v->seq) { int64_t e = num(x, g); if (g) f.values.push_back(e); }
    }
    if (f.hasRange && !f.values.empty()) err(n.line, "field '" + f.name + "': state a range OR an enum, not both");
    if (!f.hasRange && f.values.empty()) err(n.line, "field '" + f.name + "' states neither a range nor an enum");
    // `why` is mandatory. A range stated wider than the truth only loses findings; one stated NARROWER hides
    // real ones, and the only defence against that is being able to check the claim against the code.
    if (const YNode *v = n.get("why")) f.why = str(*v);
    if (f.why.empty())
      err(n.line, "field '" + f.name + "' has no 'why': a declared range narrows the analysis, so it must cite "
                  "the code that enforces it");
  }
};

}  // namespace

bool StructRanges::load(const std::string &text, const std::string &path, Diagnostics &diags) {
  Reader r{diags, path};
  YNode root;
  if (!yaml::parseYaml(text, path, root, diags)) return false;
  r.keys(root, {"version", "structs"}, "struct-ranges file");
  const YNode *ss = root.get("structs");
  if (!ss) { r.err(root.line, "no 'structs' list"); return false; }
  if (ss->kind != YNode::Seq) { r.err(ss->line, "'structs' must be a list"); return false; }
  for (auto &s : ss->seq) {
    r.keys(s, {"struct", "size", "fields", "pointers"}, "struct");
    std::string tag;
    uint64_t size = 0;
    bool g = false;
    if (const YNode *v = s.get("struct")) tag = r.str(*v);
    else r.err(s.line, "a struct entry needs 'struct' (its C tag)");
    if (const YNode *v = s.get("size")) { int64_t x = r.num(*v, g); if (g && x > 0) size = (uint64_t)x; else if (g) r.err(v->line, "size must be positive"); }
    else r.err(s.line, "struct '" + tag + "' has no 'size' (it is part of the key: measure it, do not guess)");
    const YNode *fs = s.get("fields");
    const YNode *ps = s.get("pointers");
    if (!fs && !ps) { r.err(s.line, "struct '" + tag + "' has neither 'fields' nor 'pointers'"); continue; }
    std::vector<FieldRange> out;
    if (fs) {
      if (fs->kind != YNode::Seq) { r.err(s.line, "struct '" + tag + "': 'fields' must be a list"); continue; }
      for (auto &f : fs->seq) {
        FieldRange fr;
        r.field(f, fr);
        if (!r.ok) break;
        if (fr.offset + fr.bits / 8 > size)
          r.err(fr.line, "field '" + fr.name + "' ends past the stated size of struct " + tag);
        out.push_back(std::move(fr));
      }
    }
    std::vector<PointerRetype> rts;
    if (ps) {
      if (ps->kind != YNode::Seq) { r.err(s.line, "struct '" + tag + "': 'pointers' must be a list"); continue; }
      for (auto &x : ps->seq) {
        r.keys(x, {"name", "offset", "struct", "size", "why"}, "pointer retype");
        PointerRetype rt;
        rt.line = x.line;
        bool g = false;
        if (const YNode *v = x.get("name")) rt.name = r.str(*v); else r.err(x.line, "a pointer retype needs 'name'");
        if (const YNode *v = x.get("offset")) { int64_t n = r.num(*v, g); if (g && n >= 0) rt.offset = (uint64_t)n; }
        else r.err(x.line, "pointer '" + rt.name + "' has no 'offset'");
        if (const YNode *v = x.get("struct")) rt.structTag = r.str(*v);
        else r.err(x.line, "pointer '" + rt.name + "' has no 'struct' (what it really points at)");
        if (const YNode *v = x.get("size")) { int64_t n = r.num(*v, g); if (g && n > 0) rt.size = (uint64_t)n; else if (g) r.err(v->line, "size must be positive"); }
        else r.err(x.line, "pointer '" + rt.name + "' has no 'size' (sizeof the pointee: measure it, and it is the key of its own ranges)");
        if (const YNode *v = x.get("why")) rt.why = r.str(*v);
        if (rt.why.empty())
          r.err(x.line, "pointer '" + rt.name + "' has no 'why': retyping a void* is subsystem-specific and "
                        "narrows the analysis, so it must cite the cast that justifies it");
        if (rt.offset + 8 > size) r.err(rt.line, "pointer '" + rt.name + "' lies past the stated size of struct " + tag);
        if (r.ok) rts.push_back(std::move(rt));
      }
    }
    if (!tag.empty() && size) {
      const std::string k = tag + "#" + std::to_string(size);
      if (!out.empty()) byKey[k] = std::move(out);
      if (!rts.empty()) retypesByKey[k] = std::move(rts);
    }
  }
  return r.ok;
}

}  // namespace hlir::structranges

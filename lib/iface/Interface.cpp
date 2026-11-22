// Reader for the call-contract models in `models/interfaces/*.yaml` (see hlir/iface/Interface.h, DESIGN.md §22.357).
//
// Deliberately strict: an interface model is a small, hand-written, auditable file, and a typo in it would silently
// change what every handler of that interface is assumed to receive. So every unknown key and every unknown role is
// an error with a line number, not a shrug -- the opposite of how a generated spec is read.
#include "hlir/iface/Interface.h"

#include <set>

#include "hlir/support/Yaml.h"

namespace hlir::iface {

using yaml::YNode;

const char *roleName(Role r) {
  switch (r) {
    case Role::Session:     return "session";
    case Role::SessionOut:  return "session_out";
    case Role::KernelOwned: return "kernel_owned";
    case Role::UserAddr:    return "user_addr";
    case Role::Value:       return "value";
    case Role::Out:         return "out";
  }
  return "?";
}

namespace {

struct Reader {
  Diagnostics &d;
  std::string file;
  bool ok = true;

  void err(unsigned line, const std::string &msg) {
    d.error(msg, Loc{file, line, 1});
    ok = false;
  }
  std::string str(const YNode &n) { return n.kind == YNode::Scalar ? n.scalar : std::string(); }
  void keys(const YNode &n, std::initializer_list<const char *> allowed, const char *what) {
    if (n.kind != YNode::Map) return;
    std::set<std::string> a(allowed.begin(), allowed.end());
    for (auto &kv : n.map)
      if (!a.count(kv.first)) err(kv.second.line, "unknown key '" + kv.first + "' in " + what);
  }

  bool role(const std::string &s, Role &out) {
    if (s == "session") out = Role::Session;
    else if (s == "session_out") out = Role::SessionOut;
    else if (s == "kernel_owned") out = Role::KernelOwned;
    else if (s == "user_addr") out = Role::UserAddr;
    else if (s == "value") out = Role::Value;
    else if (s == "out") out = Role::Out;
    else return false;
    return true;
  }

  void param(const std::string &name, const YNode &n, ParamContract &p) {
    p.name = name;
    p.line = n.line;
    keys(n, {"role", "dir", "size_from", "size"}, "parameter contract");
    if (const YNode *r = n.get("role")) {
      if (!role(str(*r), p.role)) err(r->line, "unknown role '" + str(*r) + "' (see hlir/iface/Interface.h)");
    } else err(n.line, "parameter '" + name + "' has no 'role'");
    if (const YNode *dd = n.get("dir")) {
      std::string v = str(*dd);
      if (v == "in") p.dir = Dir::In;
      else if (v == "out") p.dir = Dir::Out;
      else if (v == "inout") p.dir = Dir::InOut;
      else err(dd->line, "dir must be in, out or inout");
    }
    if (const YNode *sf = n.get("size_from")) p.sizeFrom = str(*sf);
    // `size: { min: N, max: M }` -- the object's real byte count, when the declared pointee type understates it.
    // Both bounds are required: a one-sided form would silently take the other from the declaration, which is the
    // very number this key exists to override.
    if (const YNode *sz = n.get("size")) {
      if (sz->kind != YNode::Map) {
        err(sz->line, "size must be a mapping with 'min' and 'max'");
      } else {
        keys(*sz, {"min", "max"}, "parameter size");
        auto num = [&](const char *k) -> std::optional<uint64_t> {
          const YNode *v = sz->get(k);
          if (!v) return std::nullopt;
          try {
            return static_cast<uint64_t>(std::stoull(str(*v)));
          } catch (...) {
            err(v->line, std::string("size.") + k + " must be a non-negative integer");
            return std::nullopt;
          }
        };
        bool both = sz->get("min") && sz->get("max");
        p.sizeMin = num("min");
        p.sizeMax = num("max");
        if (!p.sizeMin || !p.sizeMax) {
          if (!both) err(sz->line, "size needs both 'min' and 'max'");
          p.sizeMin.reset();
          p.sizeMax.reset();
        } else if (*p.sizeMin > *p.sizeMax) {
          err(sz->line, "size.min is greater than size.max");
          p.sizeMin.reset();
          p.sizeMax.reset();
        }
      }
      if (!p.sizeFrom.empty())
        err(sz->line, "'size' and 'size_from' both state the length of '" + name + "': use one");
    }
  }

  void slot(const std::string &name, const YNode &n, Slot &s) {
    s.name = name;
    s.line = n.line;
    keys(n, {"params", "success"}, "slot");
    if (const YNode *ps = n.get("params")) {
      if (ps->kind != YNode::Map) err(ps->line, "slot params must be a mapping of parameter name -> contract");
      else
        for (auto &kv : ps->map) {
          ParamContract p;
          param(kv.first, kv.second, p);
          s.params.push_back(std::move(p));
        }
    } else err(n.line, "slot '" + name + "' has no 'params'");
    if (const YNode *su = n.get("success")) s.success = str(*su);
  }

  void interface(const YNode &n, InterfaceModel &m) {
    m.line = n.line;
    keys(n, {"interface", "struct", "label", "prologue", "session", "slots", "sequence", "attacker_in_body"}, "interface");
    if (const YNode *v = n.get("interface")) m.name = str(*v);
    else err(n.line, "interface has no 'interface' (its name)");
    if (const YNode *v = n.get("struct")) m.structTag = str(*v);
    else err(n.line, "interface '" + m.name + "' has no 'struct' (the vtable's C struct tag)");
    if (const YNode *v = n.get("label")) m.label = str(*v);
    if (const YNode *v = n.get("attacker_in_body")) m.attackerInBody = str(*v) == "true";
    if (const YNode *v = n.get("prologue")) {
      if (v->kind != YNode::Seq) err(v->line, "prologue must be a list of function names");
      else
        for (auto &x : v->seq) {
          std::string fn = str(x);
          if (!fn.empty() && fn[0] == '@') fn.erase(0, 1);  // `@name` and `name` both read naturally here
          m.prologue.push_back(fn);
        }
    }
    if (const YNode *v = n.get("session")) {
      keys(*v, {"param", "created_by", "released_by", "handle"}, "session");
      if (const YNode *x = v->get("param")) m.sessionParam = str(*x);
      else err(v->line, "session has no 'param' (the parameter that carries it in every slot)");
      if (const YNode *x = v->get("created_by")) m.sessionCtor = str(*x);
      else err(v->line, "session has no 'created_by' (the slot that constructs it)");
      if (const YNode *x = v->get("released_by")) m.sessionDtor = str(*x);
      if (const YNode *x = v->get("handle")) m.sessionHandle = str(*x);
    }
    if (const YNode *v = n.get("slots")) {
      if (v->kind != YNode::Map) err(v->line, "slots must be a mapping of vtable field -> slot");
      else
        for (auto &kv : v->map) {
          Slot sl;
          slot(kv.first, kv.second, sl);
          m.slots.push_back(std::move(sl));
        }
    } else err(n.line, "interface '" + m.name + "' has no 'slots'");
    if (const YNode *v = n.get("sequence")) m.sequence = str(*v);

    // Cross-checks the format itself cannot express. Each of these would otherwise produce a contract that looks
    // plausible and quietly means something else.
    if (!m.sessionCtor.empty() && !m.slot(m.sessionCtor))
      err(m.line, "session.created_by names '" + m.sessionCtor + "', which is not a slot of this interface");
    if (!m.sessionDtor.empty() && !m.slot(m.sessionDtor))
      err(m.line, "session.released_by names '" + m.sessionDtor + "', which is not a slot of this interface");
    for (auto &sl : m.slots) {
      unsigned outs = 0;
      for (auto &p : sl.params) {
        outs += p.role == Role::SessionOut;
        // `session` is the ctor's product, so the ctor itself cannot receive one
        if (p.role == Role::Session && sl.name == m.sessionCtor)
          err(p.line, "the constructing slot '" + sl.name + "' cannot take a 'session' parameter; it produces one");
        if (!p.sizeFrom.empty()) {
          bool found = false;
          for (auto &q : sl.params) found |= q.name == p.sizeFrom;
          if (!found) err(p.line, "size_from names '" + p.sizeFrom + "', which is not a parameter of this slot");
        }
      }
      if (outs > 1) err(sl.line, "slot '" + sl.name + "' has more than one 'session_out' parameter");
      if (sl.name == m.sessionCtor && !outs && !m.sessionParam.empty())
        err(sl.line, "the constructing slot '" + sl.name + "' has no 'session_out' parameter");
    }
  }
};

}  // namespace

bool parseInterfaceFile(const std::string &text, const std::string &file, InterfaceFile &out, Diagnostics &diags) {
  YNode root;
  if (!yaml::parseYaml(text, file, root, diags)) return false;
  Reader r{diags, file};
  r.keys(root, {"version", "interfaces"}, "interface file");
  if (const YNode *v = root.get("version")) {
    if (r.str(*v) != "1") r.err(v->line, "unsupported interface-model version '" + r.str(*v) + "' (expected 1)");
  } else r.err(root.line, "interface file has no 'version'");
  const YNode *is = root.get("interfaces");
  if (!is) { r.err(root.line, "interface file has no 'interfaces'"); return false; }
  if (is->kind != YNode::Seq) { r.err(is->line, "'interfaces' must be a list"); return false; }
  for (auto &x : is->seq) {
    InterfaceModel m;
    r.interface(x, m);
    for (auto &prev : out.interfaces)
      if (!m.structTag.empty() && prev.structTag == m.structTag)
        r.err(m.line, "two interfaces claim the struct tag '" + m.structTag + "'");
    out.interfaces.push_back(std::move(m));
  }
  return r.ok;
}

}  // namespace hlir::iface

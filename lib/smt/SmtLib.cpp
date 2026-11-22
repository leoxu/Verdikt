#include <cassert>
#include <cctype>

#include "hlir/smt/Solver.h"
#include "llvm/ADT/SmallString.h"

namespace hlir::smt {

const char *satResultName(SatResult r) {
  switch (r) {
    case SatResult::Sat: return "sat";
    case SatResult::Unsat: return "unsat";
    case SatResult::Unknown: return "unknown";
  }
  return "?";
}

std::string bvLiteral(const llvm::APInt &v) {
  llvm::SmallString<80> s;
  if (v.getBitWidth() % 4 == 0) {
    v.toStringUnsigned(s, 16);
    std::string h(s);
    for (char &ch : h) ch = static_cast<char>(tolower(static_cast<unsigned char>(ch)));
    h.insert(0, v.getBitWidth() / 4 - h.size(), '0');
    return "#x" + h;
  }
  v.toStringUnsigned(s, 2);
  std::string b(s);
  b.insert(0, v.getBitWidth() - b.size(), '0');
  return "#b" + b;
}

static std::string sortStr(Sort s) {
  if (s.isBool) return "Bool";
  if (s.isArray) return "(Array (_ BitVec " + std::to_string(s.idxWidth) + ") (_ BitVec " + std::to_string(s.width) + "))";
  return "(_ BitVec " + std::to_string(s.width) + ")";
}

// Every non-leaf term becomes `(define-fun t<id> () <sort> <expr>)`: sharing is explicit and the output is linear in
// the number of distinct terms, however large the expression DAG.
std::string SmtLibEmitter::emit(TermRef root, std::string &out) {
  auto name = [](TermRef t) -> std::string {
    switch (t->kind) {
      case Kind::BoolConst: return t->value.getBoolValue() ? "true" : "false";
      case Kind::BvConst: return bvLiteral(t->value);
      case Kind::Var: return "|" + t->name + "|";
      default: return "t" + std::to_string(t->id);
    }
  };
  std::vector<TermRef> stack{root};
  while (!stack.empty()) {
    TermRef t = stack.back();
    if (t->isConst() || (t->id < emitted.size() && emitted[t->id])) { stack.pop_back(); continue; }
    bool ready = true;
    for (auto *c : t->args)
      if (!c->isConst() && !(c->id < emitted.size() && emitted[c->id])) { stack.push_back(c); ready = false; }
    if (!ready) continue;
    stack.pop_back();
    if (t->id >= emitted.size()) emitted.resize(t->id + 1, false);
    emitted[t->id] = true;
    scopeLog.back().push_back(t->id);
    if (t->kind == Kind::Var) {
      out += "(declare-fun " + name(t) + " () " + sortStr(t->sort) + ")\n";
      continue;
    }
    std::string e;
    auto a = [&](size_t i) { return name(t->args[i]); };
    switch (t->kind) {
      case Kind::Not: e = "(not " + a(0) + ")"; break;
      case Kind::ZExt: e = "((_ zero_extend " + std::to_string(t->hi - t->args[0]->sort.width) + ") " + a(0) + ")"; break;
      case Kind::SExt: e = "((_ sign_extend " + std::to_string(t->hi - t->args[0]->sort.width) + ") " + a(0) + ")"; break;
      case Kind::ConstArray: e = "((as const " + sortStr(t->sort) + ") " + a(0) + ")"; break;
      case Kind::Extract: e = "((_ extract " + std::to_string(t->hi) + " " + std::to_string(t->lo) + ") " + a(0) + ")"; break;
      default: {
        e = std::string("(") + kindName(t->kind);
        for (size_t i = 0; i < t->args.size(); ++i) e += " " + a(i);
        e += ")";
      }
    }
    out += "(define-fun " + name(t) + " () " + sortStr(t->sort) + " " + e + ")\n";
  }
  return name(root);
}

void SmtLibEmitter::pop() {
  assert(scopeLog.size() > 1);
  for (uint32_t id : scopeLog.back()) emitted[id] = false;
  scopeLog.pop_back();
}

}  // namespace hlir::smt

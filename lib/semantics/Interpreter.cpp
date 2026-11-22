#include "hlir/semantics/Interpreter.h"

#include "ConcreteDomain.h"
#include "Machine.h"

namespace hlir {

const char *runStatusName(RunStatus s) {
  switch (s) {
    case RunStatus::Returned: return "returned";
    case RunStatus::UB: return "ub";
    case RunStatus::AssertFailed: return "assert_failed";
    case RunStatus::Infeasible: return "infeasible";
    case RunStatus::Unsupported: return "unsupported";
    case RunStatus::StepLimit: return "step_limit";
    case RunStatus::DepthLimit: return "depth_limit";
    case RunStatus::LoopBound: return "loop_bound";
    case RunStatus::BadInput: return "bad_input";
  }
  return "?";
}

RunResult Interpreter::run(const std::string &function, const std::vector<llvm::APInt> &args, Env &env,
                           const RunConfig &cfg) const {
  RunResult bad;
  bad.status = RunStatus::BadInput;
  const Function *f = mod_.findFunction(function);
  if (!f) { bad.message = "unknown function @" + function; return bad; }
  if (f->isDeclaration()) { bad.message = "@" + function + " is only declared, it has no body"; return bad; }
  if (args.size() != f->paramTys.size()) {
    bad.message = "@" + function + " expects " + std::to_string(f->paramTys.size()) + " argument(s), got " + std::to_string(args.size());
    return bad;
  }
  for (size_t i = 0; i < args.size(); ++i) {
    const Type *t = f->paramTys[i];
    if (t->isPtr()) { bad.status = RunStatus::Unsupported; bad.message = "pointer arguments require the memory model"; return bad; }
    unsigned w = t->isBool() ? 1 : t->width();
    if (args[i].getBitWidth() != w) {
      bad.message = "argument " + std::to_string(i) + " has width " + std::to_string(args[i].getBitWidth()) + ", expected " + std::to_string(w);
      return bad;
    }
  }
  ConcreteDomain dom;
  Machine<ConcreteDomain> m(dom, mod_, env, cfg);
  return m.run(*f, args);
}

}  // namespace hlir

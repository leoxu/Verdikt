// Call-graph distance to a target function, for target-guided concolic search (TaintConfig::reachTarget). Purely
// additive: independent of TaintDomain/TaintExecutor, used only when a target is configured; distances are a hint for
// the search frontier's priority order, never a hard filter (DESIGN.md: a sentinel distance for unreachable functions
// keeps them exploring, just last).
#pragma once
#include <deque>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "hlir/ir/IR.h"

namespace hlir {

// Distance (call-graph hops) from each function reachable from `harness` to `target`, computed by reverse BFS from
// `target` over the direct-call edges of the functions forward-reachable from `harness` (mirrors
// driver::computeCoverage's reachability walk). `target` itself gets 0. A function with no call path to `target`
// (including `target` itself if it is not forward-reachable from `harness`, or an unknown `target` name) gets
// `kUnreachable`, a large but finite sentinel -- callers read "finite and smaller is better", not "present or absent".
inline constexpr int kUnreachableTargetDistance = 1 << 20;

inline std::map<std::string, int> computeTargetDistance(const Module &m, const std::string &harness, const std::string &target) {
  std::map<std::string, int> dist;
  const Function *h = m.findFunction(harness);
  if (!h) return dist;

  // Forward-reachable set from the harness, and (callee -> callers) reverse adjacency over the same edges.
  std::set<const Function *> reach{h};
  std::vector<const Function *> work{h};
  std::map<std::string, std::set<std::string>> callers;  // callee name -> caller names
  while (!work.empty()) {
    const Function *f = work.back();
    work.pop_back();
    for (auto &b : f->blocks)
      for (auto &op : b->ops)
        if (op->opc == Opc::Call)
          if (const Function *g = m.findFunction(op->sym)) {
            callers[g->name].insert(f->name);
            if (!g->isDeclaration() && reach.insert(g).second) work.push_back(g);
          }
  }
  for (const Function *f : reach) dist[f->name] = kUnreachableTargetDistance;
  dist[target] = kUnreachableTargetDistance;  // seeded even if target turns out not to be forward-reachable

  std::deque<std::string> q;
  dist[target] = 0;
  q.push_back(target);
  while (!q.empty()) {
    std::string cur = q.front();
    q.pop_front();
    int d = dist[cur];
    auto it = callers.find(cur);
    if (it == callers.end()) continue;
    for (const std::string &caller : it->second) {
      auto dit = dist.find(caller);
      int curD = dit == dist.end() ? kUnreachableTargetDistance : dit->second;
      if (d + 1 < curD) {
        dist[caller] = d + 1;
        q.push_back(caller);
      }
    }
  }
  return dist;
}

}  // namespace hlir

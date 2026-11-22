#include "hlir/ir/Loops.h"

#include <algorithm>
#include <cstdint>
#include <map>
#include <unordered_map>

#include "hlir/ir/Ops.h"

namespace hlir {

std::vector<Loop> loopsOf(const Function &f) {
  const size_t n = f.blocks.size();
  if (!n) return {};
  std::unordered_map<const Block *, size_t> idx;
  for (size_t i = 0; i < n; ++i) idx[f.blocks[i].get()] = i;
  std::vector<std::vector<size_t>> succ(n), pred(n);
  for (size_t i = 0; i < n; ++i)
    if (const Op *t = f.blocks[i]->terminator())
      for (const auto &sc : t->succs) {
        auto it = idx.find(sc.dest);
        if (it == idx.end()) continue;
        succ[i].push_back(it->second);
        pred[it->second].push_back(i);
      }
  // reverse postorder from the entry
  std::vector<size_t> order;
  std::vector<int> state(n, 0);
  std::vector<std::pair<size_t, size_t>> stk{{0, 0}};
  state[0] = 1;
  while (!stk.empty()) {
    auto &top = stk.back();
    if (top.second < succ[top.first].size()) {
      size_t ne = succ[top.first][top.second++];
      if (!state[ne]) { state[ne] = 1; stk.push_back({ne, 0}); }
    } else { order.push_back(top.first); stk.pop_back(); }
  }
  std::reverse(order.begin(), order.end());
  const size_t none = SIZE_MAX;
  std::vector<size_t> rpo(n, none);
  for (size_t i = 0; i < order.size(); ++i) rpo[order[i]] = i;
  // iterative dominators (Cooper/Harvey/Kennedy)
  std::vector<size_t> dom(n, none);
  dom[0] = 0;
  for (bool changed = true; changed;) {
    changed = false;
    for (size_t b : order) {
      if (b == 0) continue;
      size_t idom = none;
      for (size_t p : pred[b]) {
        if (dom[p] == none) continue;
        if (idom == none) { idom = p; continue; }
        size_t x = p, y = idom;
        while (x != y && rpo[x] != none && rpo[y] != none) {
          while (rpo[x] != none && rpo[y] != none && rpo[x] > rpo[y] && dom[x] != x) x = dom[x];
          while (rpo[x] != none && rpo[y] != none && rpo[y] > rpo[x] && dom[y] != y) y = dom[y];
          if (rpo[x] == rpo[y]) break;
        }
        idom = x;
      }
      if (idom != none && dom[b] != idom) { dom[b] = idom; changed = true; }
    }
  }
  auto dominates = [&](size_t a, size_t b) {
    if (rpo[a] == none || rpo[b] == none) return false;
    for (size_t x = b;; x = dom[x]) {
      if (x == a) return true;
      if (x == 0 || dom[x] == none || dom[x] == x) return false;
    }
  };
  std::map<size_t, Loop> loops;
  for (size_t u = 0; u < n; ++u) {
    if (rpo[u] == none) continue;
    for (size_t v : succ[u]) {
      if (!dominates(v, u)) continue;  // not a back edge
      Loop &lp = loops[v];
      lp.header = f.blocks[v].get();
      lp.body.insert(lp.header);
      lp.latches.insert(f.blocks[u].get());
      std::vector<size_t> work{u};
      while (!work.empty()) {
        size_t b = work.back();
        work.pop_back();
        if (!lp.body.insert(f.blocks[b].get()).second) continue;
        for (size_t p : pred[b]) work.push_back(p);
      }
    }
  }
  std::vector<Loop> out;
  for (auto &kv : loops) {
    Loop lp = kv.second;
    unsigned lo = 0;
    for (const Block *b : lp.body)
      for (auto &op : b->ops) {
        if (op->opc == Opc::Call) ++lp.calls;
        if (isCheck(op->opc)) ++lp.checks;
        if (!op->loc.file.empty() && (!lo || op->loc.line < lo)) { lo = op->loc.line; lp.file = op->loc.file; }
      }
    lp.line = lo;
    for (auto &other : loops)
      if (other.first != kv.first && other.second.body.count(lp.header)) { lp.nested = true; break; }
    out.push_back(std::move(lp));
  }
  return out;
}

}  // namespace hlir

// "Nothing can go wrong down there": the branch edges whose own region contains no UB check at all.
//
// The IR marks every site where a defect can be reported with an explicit `core.check.*` op, so this is a
// derivation rather than a guess about which operations look dangerous: a region with no Check op cannot
// produce a finding, no matter what values reach it.
//
// A branch edge's REGION is the set of blocks only that direction can reach -- blocks reachable from this
// successor minus blocks reachable from the sibling successor. Subtracting the sibling is what removes the
// merge point and the whole tail of the function, which plain forward reachability would wrongly count as
// "under" the branch (and would make nearly every edge look dangerous). Calls inside the region pull in the
// callee's whole body, transitively; an unresolved or declaration-only callee makes the region UNKNOWN,
// never barren.
//
// An EMPTY region is never barren. `if (c) { body }` gives the false edge an empty region, and the value of
// that edge is precisely that it skips the body -- DESIGN.md's c-ares CVE-2023-31130 note is the standing
// example of the branch that matters being the one that executes less code, not more.
//
// This is additive and read-only: it computes a property of the module and never changes execution.
#pragma once
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "hlir/ir/IR.h"

namespace hlir {

inline bool isCheckOpc(Opc o) {
  switch (o) {
    case Opc::CheckNull: case Opc::CheckUaf: case Opc::CheckOob: case Opc::CheckPtrArith:
    case Opc::CheckFree: case Opc::CheckUninit: case Opc::CheckAlign: case Opc::CheckConstWrite:
    case Opc::CheckSAddOvf: case Opc::CheckSSubOvf: case Opc::CheckSMulOvf: case Opc::CheckSNegOvf:
    case Opc::CheckDiv: case Opc::CheckShift: case Opc::CheckPtrCmp: case Opc::CheckFieldOob:
      return true;
    default:
      return false;
  }
}

struct BarrenInfo {
  // (branch op, direction taken) pairs whose region provably holds no check. `direction` is the index into
  // op->succs, so it covers Switch as well as CondBr.
  std::set<std::pair<const Op *, unsigned>> barren;
  size_t edgesTotal = 0;      // branch edges considered (conditional terminators only)
  size_t edgesBarren = 0;
  size_t edgesEmpty = 0;      // region empty -> deliberately NOT barren
  size_t edgesUnknown = 0;    // region reaches a callee we cannot see through
};

// `fnHasCheck[f]` -- does f's body, or anything it transitively calls, contain a Check op? A function we
// cannot see (declaration, unresolved symbol, indirect call) is "unknown", which counts as HAS a check:
// barrenness must be proved, never assumed.
// Transitive "can a call to f report a defect at all?" -- f's own body, or anything it can reach, holds a Check op.
// A function we cannot see through (declaration, unresolved symbol, escaping function address) counts as YES:
// barrenness has to be proved, never assumed. Exported because the coverage frontier uses it too, to put the
// never-entered functions that can actually hold a defect in front of the ones that cannot (DESIGN.md §22.415).
inline std::unordered_map<const Function *, bool> computeHasCheck(const Module &m) {
  std::unordered_map<const Function *, bool> own;        // this body alone
  std::unordered_map<const Function *, bool> opaqueCall; // calls something we cannot see through
  std::unordered_map<std::string, const Function *> byName;
  for (auto &fp : m.functions) byName[fp->name] = fp.get();
  for (auto &fp : m.functions) {
    const Function *f = fp.get();
    bool o = false, u = f->isDeclaration();
    for (auto &b : f->blocks)
      for (auto &op : b->ops) {
        if (isCheckOpc(op->opc)) o = true;
        if (op->opc == Opc::Call) {
          auto it = byName.find(op->sym);
          if (op->sym.empty() || it == byName.end() || it->second->isDeclaration()) u = true;
        }
        if (op->opc == Opc::FuncAddr) u = true;  // the address escapes; an indirect call may land anywhere
      }
    own[f] = o;
    opaqueCall[f] = u;
  }
  std::unordered_map<const Function *, bool> hasCheck;
  for (auto &fp : m.functions) hasCheck[fp.get()] = own[fp.get()] || opaqueCall[fp.get()];
  for (bool changed = true; changed;) {
    changed = false;
    for (auto &fp : m.functions) {
      const Function *f = fp.get();
      if (hasCheck[f]) continue;
      for (auto &b : f->blocks) {
        for (auto &op : b->ops) {
          if (op->opc != Opc::Call) continue;
          auto it = byName.find(op->sym);
          if (it != byName.end() && hasCheck[it->second]) { hasCheck[f] = true; changed = true; break; }
        }
        if (hasCheck[f]) break;
      }
    }
  }
  return hasCheck;
}

inline BarrenInfo computeBarrenEdges(const Module &m) {
  BarrenInfo info;
  std::unordered_map<std::string, const Function *> byName;
  for (auto &fp : m.functions) byName[fp->name] = fp.get();
  const std::unordered_map<const Function *, bool> hasCheck = computeHasCheck(m);

  // Per function: does a BLOCK hold a check, directly or through a call?
  for (auto &fp : m.functions) {
    const Function *f = fp.get();
    if (f->blocks.size() < 2) continue;
    std::unordered_map<const Block *, size_t> idx;
    for (size_t i = 0; i < f->blocks.size(); ++i) idx[f->blocks[i].get()] = i;
    std::vector<char> dangerous(f->blocks.size(), 0);
    for (size_t i = 0; i < f->blocks.size(); ++i) {
      for (auto &op : f->blocks[i]->ops) {
        if (isCheckOpc(op->opc)) { dangerous[i] = 1; break; }
        if (op->opc == Opc::FuncAddr) { dangerous[i] = 2; break; }  // 2 == unknown
        if (op->opc == Opc::Call) {
          auto it = byName.find(op->sym);
          if (op->sym.empty() || it == byName.end() || it->second->isDeclaration()) { dangerous[i] = 2; break; }
          { auto hc = hasCheck.find(it->second); if (hc != hasCheck.end() && hc->second) { dangerous[i] = 1; break; } }
        }
      }
    }
    auto reachFrom = [&](const Block *start) {
      std::vector<char> seen(f->blocks.size(), 0);
      std::vector<const Block *> st{start};
      seen[idx[start]] = 1;
      while (!st.empty()) {
        const Block *b = st.back();
        st.pop_back();
        if (const Op *t = b->terminator())
          for (auto &s : t->succs)
            if (s.dest) {
              size_t j = idx[s.dest];
              if (!seen[j]) { seen[j] = 1; st.push_back(s.dest); }
            }
      }
      return seen;
    };
    std::unordered_map<const Block *, std::vector<char>> cache;
    auto reachOf = [&](const Block *b) -> const std::vector<char> & {
      auto it = cache.find(b);
      if (it == cache.end()) it = cache.emplace(b, reachFrom(b)).first;
      return it->second;
    };

    for (auto &b : f->blocks) {
      const Op *t = b->terminator();
      if (!t || t->succs.size() < 2) continue;  // only a real choice has a region to compare
      for (unsigned d = 0; d < t->succs.size(); ++d) {
        if (!t->succs[d].dest) continue;
        ++info.edgesTotal;
        const std::vector<char> &mine = reachOf(t->succs[d].dest);
        // Blocks every OTHER direction can also reach are the merge and the tail: not "under" this edge.
        std::vector<char> shared(f->blocks.size(), 0);
        for (unsigned e = 0; e < t->succs.size(); ++e) {
          if (e == d || !t->succs[e].dest) continue;
          const std::vector<char> &other = reachOf(t->succs[e].dest);
          for (size_t i = 0; i < shared.size(); ++i) shared[i] = shared[i] || other[i];
        }
        size_t own_blocks = 0;
        bool anyDanger = false, anyUnknown = false;
        for (size_t i = 0; i < mine.size(); ++i) {
          if (!mine[i] || shared[i]) continue;
          ++own_blocks;
          if (dangerous[i] == 1) anyDanger = true;
          if (dangerous[i] == 2) anyUnknown = true;
        }
        if (own_blocks == 0) { ++info.edgesEmpty; continue; }   // skipping code is a reason to take an edge
        if (anyUnknown) { ++info.edgesUnknown; continue; }
        if (!anyDanger) { info.barren.emplace(t, d); ++info.edgesBarren; }
      }
    }
  }
  return info;
}

}  // namespace hlir

// Naming and matching shared by the frontend (which emits indirect calls and lists their candidates), hlir::link (which
// builds the dispatchers) and the scan driver (which picks the targets of function pointer fields it synthesizes).
#pragma once
#include <cstdint>
#include <string>
#include <vector>

namespace hlir {

// A function's "C type key" (frontend: cTypeKey): `ret(p1,p2,...)`, one element per position. An element is a pointer to a
// named struct or union -- one '*' per level, then `s:` or `u:` and the tag (`*s:net`) -- or `_` for anything else
// (integers, `void *`, function pointers, anonymous records). The core signature already fixes the machine types; the key
// adds only what tells a `struct net *` from a `struct socket *`, which real code does not mix up through casts.
// "" = unknown (no prototype): compatible with everything.

inline std::vector<std::string> splitCTypeKey(const std::string &k) {
  std::vector<std::string> out;
  size_t open = k.find('(');
  if (open == std::string::npos || k.empty() || k.back() != ')') return out;
  out.push_back(k.substr(0, open));
  std::string body = k.substr(open + 1, k.size() - open - 2);
  size_t at = 0;
  while (at <= body.size() && !body.empty()) {
    size_t c = body.find(',', at);
    out.push_back(body.substr(at, c == std::string::npos ? std::string::npos : c - at));
    if (c == std::string::npos) break;
    at = c + 1;
  }
  return out;
}

// Can a function of key `fn` be the target of a call through a pointer of key `call`? Only a position where both name a
// different struct/union (or a different pointer depth to one) says no: `void *`, integers and unnamed types match
// anything, because generic dispatch (libffi, a `void (*)(void)` table read back as another struct type, qsort) calls
// handlers through such types without ever casting the handler itself.
inline bool cTypesCompatible(const std::string &call, const std::string &fn) {
  if (call.empty() || fn.empty() || call == fn) return true;
  std::vector<std::string> a = splitCTypeKey(call), b = splitCTypeKey(fn);
  if (a.empty() || a.size() != b.size()) return true;
  for (size_t i = 0; i < a.size(); ++i)
    if (a[i] != b[i] && a[i] != "_" && b[i] != "_") return false;
  return true;
}

// The suffix `.t<hash>` of the dispatcher name of an indirect call through a pointer of C type key `k`; the frontend also
// reports name -> key (LowerResult::indirectCallCTypes) so the linker can match candidates with cTypesCompatible.
inline std::string indirectTypeTag(const std::string &k) {
  uint64_t h = 1469598103934665603ull;  // FNV-1a
  for (unsigned char c : k) h = (h ^ c) * 1099511628211ull;
  static const char *hex = "0123456789abcdef";
  std::string s = ".t";
  for (int i = 15; i >= 0; --i) s += hex[(h >> (i * 4)) & 15];
  return s;
}

}  // namespace hlir

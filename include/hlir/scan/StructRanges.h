// Declared per-struct field ranges: `models/structs/*.yaml` (DESIGN.md §22.480).
//
// A filesystem's handler is handed objects the VFS and the mount path built, and the mount path VALIDATED some
// of their fields. `isofs_fill_super` rejects any logical zone size but 512/1024/2048 and stores 9/10/11; the
// VFS blocksize is a power of two; `s_rock_offset` is -1 or a byte off the disk. The synthesised objects know
// none of that, and round 43's triage found that ELEVEN of twelve findings were one sentence: a field mount
// validates is unconstrained here (results/k59_isofs/triage_12.md).
//
// The existing `where:` machinery already expresses exactly this per field -- it is what §22.358 emits from the
// bounds a program ASSERTS about itself. The kernel does not assert these; it validates them with `goto
// out_bad_zone_size`. So this file lets the ranges be DECLARED, in a reviewable file, next to the line of code
// that enforces them, and they then travel the same path an asserted bound does.
//
// Everything here NARROWS. Each struct carries a `why` that must cite the code doing the validating, and every
// entry it applies to says so in the report's assumptions. A range stated wider than the truth only loses
// findings; a range stated NARROWER than the truth hides real ones, which is why `why` is mandatory.
#ifndef HLIR_SCAN_STRUCTRANGES_H
#define HLIR_SCAN_STRUCTRANGES_H

#include <cstdint>
#include <map>
#include <string>
#include <vector>

#include "hlir/support/Diagnostics.h"

namespace hlir::structranges {

struct FieldRange {
  std::string name;          // for the assumption text only
  uint64_t offset = 0;
  unsigned bits = 0;         // 8/16/32/64
  bool isSigned = false;
  bool hasRange = false;
  int64_t lo = 0, hi = 0;
  std::vector<int64_t> values;  // `enum:` -- the exact set, when the code switches on it
  std::string why;              // the code that enforces it, e.g. "fs/isofs/inode.c:746 switch, default goto out_bad_zone_size"
  unsigned line = 0;
};

// A `void *` field whose real pointee type the code knows and the type system does not. Every filesystem hangs
// its superblock state off `super_block::s_fs_info` and reaches it through its own cast macro (`ISOFS_SB(sb)`);
// the frontend sees only `void *`, gives it the generic 64-byte stand-in, and the declared ranges for that type
// can never apply because there is no struct name to match. Measured: it is why `rock_ridge_symlink_read_folio`
// did not move under §22.480 and why zisofs's compress.c:248/:262 reads leave the buffer (§22.481).
//
// THIS IS SUBSYSTEM-SPECIFIC in a way the ranges are not: `super_block::s_fs_info` is a different type in every
// filesystem, and the key cannot tell them apart. A tree holding two filesystems would get one's type on both.
// Each retype is therefore named in the entry's assumptions and printed when the file is loaded.
struct PointerRetype {
  std::string name;          // the field, for the assumption text
  uint64_t offset = 0;
  std::string structTag;     // what it really points at
  uint64_t size = 0;         // sizeof that type -- measured, and the key of its own range entry
  std::string why;
  unsigned line = 0;
};

struct StructRanges {
  // key: "tag#size", the same key shape the lowering prints as `pointee="super_block#1280"`. The SIZE is part of
  // the key on purpose: two subsystems with the same struct tag are different types, and a range meant for one
  // must not silently reshape the other.
  std::map<std::string, std::vector<FieldRange>> byKey;
  std::map<std::string, std::vector<PointerRetype>> retypesByKey;

  bool load(const std::string &yamlText, const std::string &path, Diagnostics &diags);
  const std::vector<FieldRange> *find(const std::string &tag, uint64_t size) const {
    auto it = byKey.find(tag + "#" + std::to_string(size));
    return it == byKey.end() ? nullptr : &it->second;
  }
  const PointerRetype *retype(const std::string &tag, uint64_t size, uint64_t offset) const {
    auto it = retypesByKey.find(tag + "#" + std::to_string(size));
    if (it == retypesByKey.end()) return nullptr;
    for (auto &r : it->second)
      if (r.offset == offset) return &r;
    return nullptr;
  }
  bool empty() const { return byKey.empty() && retypesByKey.empty(); }
};

}  // namespace hlir::structranges

#endif

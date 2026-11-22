#include "hlir/scan/Scan.h"

#include <map>
#include <set>
#include <regex>

#include "hlir/support/IndirectCall.h"
#include "hlir/support/Yaml.h"
#include <sstream>

namespace hlir::scan {
namespace {

using frontend::FunctionInfo;
using frontend::ParamInfo;
using frontend::PtrFieldInfo;

std::string intType(unsigned bits, bool sg) {
  switch (bits) {
    case 8: return sg ? "int8_t" : "uint8_t";
    case 16: return sg ? "int16_t" : "uint16_t";
    case 32: return sg ? "int32_t" : "uint32_t";
    default: return sg ? "int64_t" : "uint64_t";
  }
}

bool matches(const std::string &re, const std::string &s) {
  if (re.empty()) return false;
  try {
    return std::regex_search(s, std::regex(re));
  } catch (const std::regex_error &) {
    return false;
  }
}

bool isLenName(const std::string &n) {
  // "max"/"_max" (a buffer's declared capacity, as distinct from its current fill level -- zlib's
  // gz_header::extra_max is the textbook real-world instance, ground-truth-verified against CVE-2022-37434:
  // extra_max was never recognised, so the top-level "length<->buffer" relation loop in makeEntry() never tied
  // the synthesized extra buffer's size to it, producing an artifact-laden repro that didn't actually
  // distinguish the vulnerable code from the fixed code) is the same kind of length-ish suffix the other
  // entries here already cover, just missing. Same risk profile as every other suffix already in this list:
  // it only generates a relation when paired by position with an adjacent byte-buffer parameter, so a "max"
  // name unrelated to any buffer (e.g. a retry counter) is no more likely to mismatch than an existing
  // "count"/"size" false pairing already accepted by this heuristic.
  static const std::regex re("^(len|length|size|count|n|nbytes|num|sz|nr|cnt|bytes|max|[a-z0-9_]*_(len|length|size|count|sz|bytes|nbytes|cnt|max))$", std::regex::icase);
  static const std::regex camel("^(n[A-Z][A-Za-z0-9]*|[A-Za-z0-9]*[a-z0-9](Size|Len|Length|Count|Num|Bytes|Cnt|Max))$");  // alphaSize, nItems, bufLen, extraMax
  static const std::regex glued("^[a-z0-9]+(len|length|size|count|sz|bytes|nbytes|cnt|max)$", std::regex::icase);  // dstlen, srclen, bufsize, strlen_, extramax
  if (std::regex_match(n, re) || std::regex_match(n, camel) || std::regex_match(n, glued)) return true;
  // a length word followed by a type tag or a role tag: c-ares' `alen_int` (ares_parse_*_reply) was not paired with
  // its abuf, so every reply parser ran with a 64-byte buffer and a length of 45568 (DESIGN.md §22.346). `param`/`arg`
  // are the same shape with a role tag instead of a type tag: libwebp's `ParseHeadersInternal(data_param,
  // data_size_param, ...)` -- the function's own contract says `WEBP_COUNTED_BY(data_size_param) data_param`, but the
  // tag hid the length, so the top-level WebP header parser ran with a 64-byte buffer and data_size 2060 and produced
  // 16 confirmed artefact findings; with the pair tied, all 16 disappear at 80% block coverage.
  // The tag is only stripped, never trusted: the remainder still has to pass isLenName itself, so `flags_param` or
  // `offset_arg` stay unmatched, and a match still only yields a relation when the pairing loop finds an adjacent
  // byte buffer.
  static const std::regex typed("^(.*[A-Za-z0-9])_(int|uint|long|ulong|i8|i16|i32|i64|u8|u16|u32|u64|t|sz|size_t|param|arg)$", std::regex::icase);
  std::smatch m;
  return std::regex_match(n, m, typed) && isLenName(m[1].str());
}

// `struct sockaddr *addr, socklen_t addr_len`-shaped parameter: a real object of up to `addr_len` bytes, most often
// bigger than `sizeof(struct sockaddr)` itself (the caller allocates the concrete address-family struct -- sockaddr_in,
// sockaddr_in6, sockaddr_un, sockaddr_storage, ... -- and passes it through this generic base-struct pointer, exactly
// the "declared base type, real object is a bigger same-prefix struct" shape; see DESIGN.md §22.118/120/123/133 for
// the diagnosis and why a blanket `pointee == "struct"` match is unsafe here: `struct iovec *iov, int iovcnt` has the
// same signature shape but `iovcnt` is an element count, not a byte length, so it must not get this treatment. Matched
// by name prefix (sockaddr/sockaddr_in/sockaddr_in6/sockaddr_un/sockaddr_storage/sockaddr_nl/sockaddr_ll/sockaddr_can/
// sockaddr_l2/... -- every BSD-socket address-family struct in the kernel and in userspace libc follows this naming
// convention) rather than an exhaustive list of every protocol family's struct name.
bool isSockaddrLike(const ParamInfo &p) {
  return p.kind == "ptr" && p.pointee == "struct" && p.structName.rfind("sockaddr", 0) == 0;
}

// sizeof(struct sockaddr_storage) on every platform HLIR targets (x86_64 Linux/glibc, and the kernel's own
// definition agrees): 128 bytes. Stable across libc/kernel, safe to hardcode rather than look up per-target.
constexpr uint64_t kSockaddrStorageSize = 128;

bool isByteBuffer(const ParamInfo &p) {
  return (p.kind == "ptr" && (p.pointee == "void" || p.pointee == "int")) || isSockaddrLike(p);  // byte buffers, arrays of integers (size in bytes = count * element size), and sockaddr-family structs (size in bytes = addr_len, see isSockaddrLike)
}
uint64_t elemSize(const ParamInfo &p) { return p.pointee == "int" && p.pointeeSize > 1 ? p.pointeeSize : 1; }

// `where:` entries bounding each count of an inline fixed array by that array's extent (see InlineCountInfo). The
// bound is `[0, hi]`, never a lower bound: a real producer may legitimately leave the count at zero.
// `where:` entries for the bounds the program itself asserts about this parameter's integer members (see
// Options::assertBounds). Only members of the parameter's OWN pointee, which is where the motivating shape lives
// (`snd_BUG_ON(dp->max_synthdev > ...)` with `dp` a handler parameter); sub-objects are not reached yet.
// `where:` entries for the bounds the program itself asserts about the members of struct `tag` (see
// Options::assertBounds). Indexed by TYPE, so the same lookup serves a parameter's own pointee and the sub-object
// behind one of its pointer fields -- `odev_write` reaches `seq_oss_devinfo` through `file->private_data`, and that
// is the shape the real syscall boundary has (DESIGN.md §22.358).
std::string assertWheres(const std::string &tag, uint64_t recordSize, const Options &opt, bool lead) {
  if (!opt.assertBounds || opt.assertBounds->empty() || tag.empty() || !recordSize) return "";
  std::string out;
  // The key encodes the offset, so walking the few plausible offsets is not an option: scan the map once. It holds
  // one entry per asserted member of the whole program, which is small (tens), not per object.
  const std::string prefix = tag + "#" + std::to_string(recordSize) + "@";
  for (auto &kv : *opt.assertBounds) {
    if (kv.first.compare(0, prefix.size(), prefix) != 0) continue;
    const frontend::AssertedBound &b = kv.second;
    if ((!b.hasLo && !b.hasHi) || !b.bits) continue;
    int64_t tlo = 0, thi = 0;
    if (b.bits >= 64) { tlo = INT64_MIN; thi = INT64_MAX; }
    else if (b.isSigned) { tlo = -(int64_t(1) << (b.bits - 1)); thi = (int64_t(1) << (b.bits - 1)) - 1; }
    else { tlo = 0; thi = (int64_t(1) << b.bits) - 1; }
    int64_t lo = b.hasLo ? b.lo : tlo, hi = b.hasHi ? b.hi : thi;
    // a bound the type cannot exceed anyway states nothing; a contradictory pair says nothing useful either
    if ((lo <= tlo && hi >= thi) || lo > hi) continue;
    if (b.offset + b.bits / 8 > recordSize) continue;  // not a member of an object this size: a tag collision
    out += (out.empty() && !lead ? "" : ", ");
    out += "{ offset: " + std::to_string(b.offset) + ", type: " + intType(b.bits, b.isSigned) +
           ", range: [" + std::to_string(lo) + ", " + std::to_string(hi) + "] }";
  }
  return out;
}

// `where:` entries for the ranges a models/structs/*.yaml file DECLARES about struct `tag` (DESIGN.md §22.480).
// Same shape and same destination as assertWheres above; the difference is where the knowledge comes from -- a
// bound the program asserts about itself, versus one a reviewer wrote down from the code that enforces it. The
// kernel validates these with `goto out_bad_zone_size`, not with BUG_ON, so nothing harvests them.
std::string declaredWheres(const std::string &tag, uint64_t recordSize, const Options &opt, bool lead,
                           std::vector<std::string> *named) {
  if (!opt.structRanges || tag.empty() || !recordSize) return "";
  const std::vector<structranges::FieldRange> *fs = opt.structRanges->find(tag, recordSize);
  if (!fs) return "";
  std::string out;
  for (auto &f : *fs) {
    out += (out.empty() && !lead ? "" : ", ");
    out += "{ offset: " + std::to_string(f.offset) + ", type: " + intType(f.bits, f.isSigned);
    if (f.hasRange) {
      out += ", range: [" + std::to_string(f.lo) + ", " + std::to_string(f.hi) + "] }";
    } else {
      out += ", enum: [";
      for (size_t i = 0; i < f.values.size(); ++i) out += (i ? ", " : "") + std::to_string(f.values[i]);
      out += "] }";
    }
    if (named)
      named->push_back("struct " + tag + "." + f.name + " is " +
                       (f.hasRange ? "within [" + std::to_string(f.lo) + ", " + std::to_string(f.hi) + "]"
                                   : std::string("one of a declared set")) +
                       " because " + f.why + " (declared range, models/structs: it NARROWS the analysis)");
  }
  return out;
}

std::string inlineCountWheres(const std::vector<frontend::InlineCountInfo> &cs, bool lead) {
  std::string out;
  for (auto &c : cs) {
    out += (out.empty() && !lead ? "" : ", ");
    out += "{ offset: " + std::to_string(c.offset) + ", type: " + intType(c.bits, c.isSigned) + ", range: [0, " + std::to_string(c.hi) + "] }";
  }
  return out;
}

// YAML (a flow list) for the pointer fields of a pointee object; parentTainted: the object's content is attacker controlled,
// so what its pointers point to is attacker controlled too (it was "copied in" together with the struct)
std::string fieldsYaml(const std::vector<PtrFieldInfo> &fields, bool parentTainted, const Options &opt, const std::vector<FunctionInfo> &all,
                       const std::string &owner, std::map<std::string, std::pair<unsigned, std::string>> &skipped, unsigned &budget, unsigned &made, unsigned &selfLinks, unsigned &container, uint64_t &need,
                       std::vector<std::string> *declared = nullptr, const std::string &ownerTag = {}, uint64_t ownerSize = 0) {
  // Level by level: every field of this object gets its object before any child object expands (a big nested struct must
  // not use up the budget that the shallow fields of the object that contains it need). Self links allocate nothing.
  struct Item {
    std::string text; const PtrFieldInfo *expand = nullptr; std::string at;
    // (base, cursor, limit) bookkeeping, filled only by the plain element-buffer branch below. `size` is held back
    // until every field has been seen, because whether this one becomes a view depends on whether its owner was
    // emitted at all (the --max-fields budget may have dropped it).
    uint64_t offset = 0; std::string size; bool plainBuf = false; int64_t alias = -1; bool aliasEnd = false;
  };
  std::vector<Item> items;
  for (auto &f : fields) {
    std::string at = owner + "+" + std::to_string(f.offset);
    // a note about a field that IS made, explaining the treatment it got (as opposed to `skip`, which says why a
    // field was left out). Same one-summary-per-reason shape.
    auto skipReasonNote = [&](const std::string &why) {
      auto &e = skipped[why];
      if (e.first++ < 3) e.second += (e.second.empty() ? "" : ", ") + at;
    };
    auto skip = [&](const std::string &why) {
      // one summary note per reason, with the first few fields as examples (a kernel `struct file` has hundreds)
      auto &e = skipped[why];
      if (e.first++ < 3) e.second += (e.second.empty() ? "" : ", ") + at;
    };
    // The field lies inside a UNION and the frontend took the union's FIRST arm to reach it (DESIGN.md §22.484).
    // That is a choice, and it can be the wrong one -- the other arms overlay the same bytes with other types --
    // so it is named rather than made silently. Without it `struct folio` contributed no pointer fields at all.
    if (f.viaUnionArm && declared)
      declared->push_back("a pointer field at offset " + std::to_string(f.offset) + " of struct " +
                          (ownerTag.empty() ? std::string("<anonymous>") : ownerTag) +
                          " lies inside a union: the FIRST arm was taken, and the other arms overlay the same "
                          "bytes with other types (union arm chosen, it is a CHOICE and may be the wrong one)");
    std::string item = "{ offset: " + std::to_string(f.offset);
    if (f.kind == "self") {
      ++made;
      ++selfLinks;
      items.push_back({item + ", kind: self, target: " + std::to_string(f.selfTarget), nullptr, at});
      continue;
    }
    if (budget == 0) { skip("more than " + std::to_string(opt.maxFields) + " pointer fields (--max-fields)"); continue; }
    if (f.kind == "func") {
      std::vector<std::string> targets;
      bool otherCType = false;  // functions with the signature exist, but none of the field's C type
      if (!f.funcSig.empty())
        for (auto &g : all)
          if (g.addrTaken && g.lowered && g.sig == f.funcSig && targets.size() < 8) {
            if (g.cType.empty() || cTypesCompatible(f.funcCType, g.cType)) targets.push_back(g.name);
            else otherCType = true;  // a field of another C type cannot hold it
          }
      // The field may hold NULL only when some visible code tests THIS field for NULL (PtrFieldInfo::nullTested,
      // unioned across every --link unit). Unconditional nullability would manufacture a null_deref at every
      // `obj->ops->fn()` that a real program never checks; this gate makes the program itself say so. The motivating
      // case is FreeType's `FT_StreamRec.read`, NULL for a memory stream and tested in 13 places, which forced non-NULL
      // sent every FT_Stream_Read* into the gzip reader with unsynthesised state (DESIGN.md §22.353).
      const char *nullable = f.nullTested ? ", nullable: true" : "";
      if (targets.empty()) {
        // No candidate for this slot, for either of two reasons: the signature matches functions of another C type
        // (sk_data_ready -> net/core: the real program holds a function of a module we do not have), or there is no
        // signature to match at all -- a VARIADIC field like netdissect_options::ndo_printf, whose `funcSig` is empty.
        //
        // Both get the same treatment, and it is not "leave the field out". Leaving it out leaves the slot holding
        // the object's own bytes, the lowering's NULL guard before every indirect call takes the null edge, and the
        // path ends at `core.unreachable` -- so a non-NULL, no-candidate pointer is strictly better: the call becomes
        // the opaque `__hlir_unknown_indirect` and the path GOES ON. A function of the wrong type would be worse
        // still: it would run code that cannot run there.
        //
        // Measured on tcpdump (DESIGN.md §22.425): `ND_PRINT` goes through ndo_printf at offset 152, which is
        // variadic, so the generated spec modelled ndo_default_print (144) and omitted this one. Every symbolic path
        // into any printer died at its first ND_PRINT -- one path, twelve blocks, for a 400-block function.
        //
        // `nullable` still gates real nullability on the program testing THIS field, exactly as below.
        skipReasonNote("a function pointer with no resolvable target (" +
                       (f.funcSig.empty() ? std::string("variadic: no signature to match")
                                          : "signature " + f.funcSig + " only matches functions of another C type") +
                       ") is non-NULL and opaque, so a call through it continues as __hlir_unknown_indirect");
        item += ", kind: buffer, taint: none, size: { min: 1, max: 1 }";
        item += nullable;
        --budget;
        ++made;
        items.push_back({item, nullptr, at});
        continue;
      }
      item += ", kind: funcptr, targets: [";
      for (size_t i = 0; i < targets.size(); ++i) item += (i ? ", " : "") + targets[i];
      item += "]";
      item += nullable;
      --budget;
      ++made;
      items.push_back({item, nullptr, at});
    } else if (f.kind == "struct") {
      if (f.cyclic) { skip("self-referential link to struct " + f.structName + " (end of the chain)"); continue; }
      if (f.pointeeSize == 0 || f.pointeeSize > opt.maxObjLimit) { skip("struct " + f.structName + " is " + std::to_string(f.pointeeSize) + " bytes (limit " + std::to_string(opt.maxObjLimit) + ")"); continue; }
      need = std::max(need, f.pointeeSize);
      item += ", kind: buffer, taint: " + std::string(parentTainted ? "pointee" : "none");
      // An ARRAY of structs sized by a sibling count field (`FT_UShort num_tables; TT_Table dir_tables;` and
      // `limit = entry + face->num_tables`): without this the object is exactly one element wide while the count is
      // free, so every walk of the array runs off the end -- 20 confirmed ptr_arith_oob at ttload.c:75 in the
      // FreeType round, and the same "struct pointer and count not paired" family that recurs across the kernel
      // rounds (DESIGN.md §22.352). `elem` scales the count to bytes.
      // Only when the struct has no pointer fields of its own: `fields:` and `from_field` are mutually exclusive
      // (Spec.cpp), because a dynamically sized object's layout isn't known until the harness runs. `viaContainerOf`
      // is excluded for the same reason InitGen rejects `at` with from_field, and `ptrArray` has its own
      // fixed-slot synthesis with a `where:` range instead.
      bool countSized = f.lenOffset >= 0 && f.lenBits && f.children.empty() && !f.ptrArray && !f.viaContainerOf;
      if (countSized)
        item += ", size: { from_field: { offset: " + std::to_string(f.lenOffset) + ", type: " + intType(f.lenBits, f.lenSigned) +
                ", elem: " + std::to_string(f.pointeeSize) + " } }";
      else
        item += ", size: { min: " + std::to_string(f.pointeeSize) + ", max: " + std::to_string(f.pointeeSize) + " }";
      if (f.viaContainerOf) { item += ", at: " + std::to_string(f.at); ++container; }
      // the same bounds, one level down: this field's own object has inline arrays with count members of their own.
      // Not when the object's size is derived (`from_field`), where InitGen has no static size to check against.
      if (!countSized) {
        std::string w = inlineCountWheres(f.inlineCounts, false);
        w += assertWheres(f.structName, f.pointeeSize, opt, !w.empty());
        w += declaredWheres(f.structName, f.pointeeSize, opt, !w.empty(), declared);
        if (!w.empty()) item += ", where: [ " + w + " ]";
      }
      --budget;
      ++made;
      items.push_back({item, f.children.empty() ? nullptr : &f, at + "->" + f.structName});
    } else if (f.kind == "handle") {  // a pointer to a type that is never defined: library state, a legal untainted object
      // ... unless a models/structs file says what it REALLY points at (DESIGN.md §22.482). `super_block::s_fs_info`
      // is a `void *` in the type system and an `isofs_sb_info` in every line that touches it; without this the
      // generic 64-byte stand-in has no struct name, so the declared ranges for that type can never apply and
      // the filesystem's own superblock fields stay unconstrained.
      const structranges::PointerRetype *rt =
          opt.structRanges ? opt.structRanges->retype(ownerTag, ownerSize, f.offset) : nullptr;
      if (rt) {
        item += ", kind: buffer, taint: none, size: { min: " + std::to_string(rt->size) + ", max: " + std::to_string(rt->size) + " }";
        std::string w = declaredWheres(rt->structTag, rt->size, opt, false, declared);
        if (!w.empty()) item += ", where: [ " + w + " ]";
        if (declared)
          declared->push_back("the void* " + ownerTag + "." + rt->name + " is read as a struct " + rt->structTag +
                              " of " + std::to_string(rt->size) + " bytes because " + rt->why +
                              " (declared retype, models/structs: subsystem-specific, it NARROWS the analysis)");
      } else {
        item += ", kind: buffer, taint: none, size: { min: 64, max: 64 }";
      }
      --budget;
      ++made;
      items.push_back({item, nullptr, at});
    } else if ((f.kind == "bytes" || f.kind == "int") && opt.structRanges &&
               opt.structRanges->retype(ownerTag, ownerSize, f.offset)) {
      // A `void *` reaches here as a one-byte "byte buffer", not as a `handle`: the generic stand-in is
      // `max(64, 1)` bytes with no struct name, so no declared range for its real type can ever match. See the
      // retype branch above for why this is stated rather than inferred (DESIGN.md §22.482).
      const structranges::PointerRetype *rt = opt.structRanges->retype(ownerTag, ownerSize, f.offset);
      // `content: unknown`, not the zero fill an untainted object would get. A declared range is a PRECONDITION:
      // `zone in {9,10,11}` against a zero-filled object is unsatisfiable, no run completes, and the entry comes
      // back `unknown` with 0% coverage -- measured on the fixture, and the reason the same thing works through
      // an iface contract is only that `kernel_owned` already asks for unknown content (§22.477/§22.481).
      item += ", kind: buffer, taint: none, content: unknown, size: { min: " + std::to_string(rt->size) + ", max: " + std::to_string(rt->size) + " }";
      std::string w = declaredWheres(rt->structTag, rt->size, opt, false, declared);
      if (!w.empty()) item += ", where: [ " + w + " ]";
      if (declared)
        declared->push_back("the void* " + ownerTag + "." + rt->name + " is read as a struct " + rt->structTag + " of " +
                            std::to_string(rt->size) + " bytes because " + rt->why +
                            " (declared retype, models/structs: subsystem-specific, it NARROWS the analysis)");
      --budget;
      ++made;
      items.push_back({item, nullptr, at});
    } else if (f.kind == "bytes" || f.kind == "int") {
      uint64_t lo = std::max<uint64_t>(1, f.pointeeSize);
      item += ", kind: buffer, taint: " + std::string(parentTainted ? "pointee" : "none");
      std::string sz;
      // a byte-buffer pointer field (`char*`/`void*`-shaped, not an array of wider elements) whose struct has a
      // sibling length field (data/datalen, buf/buflen, addr/addr_len, ...; see Frontend.cpp's findSiblingLenField)
      // gets its size tied to that field's real value instead of an independent range -- this is what makes the
      // §22.105 relations-DSL fix actually fire on auto-discovered entries (see DESIGN.md §22.105/127/130).
      // An array of wider integers carries an ELEMENT count, so it needs the same `elem` multiplier the struct
      // arrays got in §22.352; a byte buffer's length is already in bytes and keeps the plain form (§22.355).
      if (f.lenOffset >= 0 && f.lenBits && (f.kind == "bytes" || f.lenIsCount))
        sz = ", size: { from_field: { offset: " + std::to_string(f.lenOffset) + ", type: " + intType(f.lenBits, f.lenSigned) +
             (f.kind == "int" && f.pointeeSize > 1 ? ", elem: " + std::to_string(f.pointeeSize) : "") + " } }";
      else if (parentTainted) sz = ", size: { min: " + std::to_string(lo) + ", max: " + std::to_string(std::max(lo, opt.bufMax)) + " }";
      else sz = ", size: { min: " + std::to_string(std::max<uint64_t>(64, lo)) + ", max: " + std::to_string(std::max<uint64_t>(64, lo)) + " }";
      --budget;
      ++made;
      Item it{item, nullptr, at};
      it.offset = f.offset;
      it.size = sz;
      it.plainBuf = true;  // may own a same_alloc view -- including when its own size is derived from a sibling length
      it.alias = f.aliasOffset;
      it.aliasEnd = f.aliasEnd;
      items.push_back(std::move(it));
    } else {
      skip(f.kind == "pointer" ? "pointer to pointer" : "pointee type is incomplete or unsupported");
    }
  }
  // (base, cursor, limit) over one buffer (PtrFieldInfo::aliasOffset): the limit and the cursor become views into
  // the base's allocation instead of objects of their own, so a `while (cur < limit)` compares two pointers that are
  // provably in the same object (DESIGN.md §22.354). A view is only emitted when the owner really was emitted here
  // as a plain, independently sized buffer; otherwise the field keeps its own size, exactly as before.
  std::set<uint64_t> owners;
  for (auto &it : items)
    if (it.plainBuf) owners.insert(it.offset);
  for (auto &it : items)
    if (it.alias >= 0 && owners.count(static_cast<uint64_t>(it.alias)) && static_cast<uint64_t>(it.alias) != it.offset) {
      it.size = ", same_alloc: { offset: " + std::to_string(it.alias) + (it.aliasEnd ? " }" : ", pos: inside }");
      it.plainBuf = false;  // a view cannot in turn own another view
    } else {
      it.alias = -1;
    }
  for (auto &it : items) it.text += it.size;
  // `same_alloc` must name an EARLIER field of the same list (InitGen resolves it against the fields already
  // planned), and the owner is commonly declared after its cursor (`FT_Byte *cursor, *base, *limit;`). Emit each
  // owner right before the first view that needs it; everything else keeps its original order.
  {
    std::vector<Item> ordered;
    std::vector<bool> placed(items.size(), false);
    for (size_t i = 0; i < items.size(); ++i) {
      if (placed[i]) continue;
      if (items[i].alias >= 0)
        for (size_t j = 0; j < items.size(); ++j)  // the owner: the one plain buffer item at that offset
          if (!placed[j] && items[j].plainBuf && items[j].offset == static_cast<uint64_t>(items[i].alias)) {
            ordered.push_back(items[j]);
            placed[j] = true;
            break;
          }
      ordered.push_back(items[i]);
      placed[i] = true;
    }
    items.swap(ordered);
  }
  std::string out;
  for (auto &it : items) {
    std::string text = it.text;
    if (it.expand) {
      std::string kids = fieldsYaml(it.expand->children, parentTainted, opt, all, it.at, skipped, budget, made, selfLinks, container, need, declared,
                                 it.expand->structName, it.expand->pointeeSize);
      if (!kids.empty()) text += ", fields: [ " + kids + " ]";
    }
    out += (out.empty() ? "" : ", ") + text + " }";
  }
  return out;
}

}  // namespace

Entry makeEntry(const FunctionInfo &fn, const Options &opt, const std::vector<FunctionInfo> &all) {
  Entry e;
  e.function = fn.name;
  e.line = fn.line;
  e.lowered = fn.lowered;
  std::ostringstream y;
  y << "taint_entries:\n  - function: " << fn.name << "\n    label: " << opt.label << "\n";
  if (!fn.params.empty()) y << "    params:\n";  // an empty `params:` key (no params follow it) parses as a null scalar, not a mapping
  unsigned tainted = 0;
  uint64_t need = 0;  // largest object the spec asks the entry module to create (raises max_obj when above the default)
  // ---- the interface contract, when this function is a slot of a modelled dispatch interface (EntryMode::Iface).
  // It replaces the generic synthesis for every parameter it covers: the generic path knows only the TYPES, so it
  // builds a `struct file` field by field and marks all of it attacker-controlled, which is the measured dominant
  // source of false findings (DESIGN.md §22.357). The contract is matched BY POSITION -- `Slot::params` is in the
  // handler's parameter order, and a handler is free to name its parameters `filp`/`cmd`/`arg` or anything else.
  // An arity disagreement means the model and this code are talking about different functions, so the contract is
  // dropped whole rather than applied to a shifted parameter list.
  const iface::InterfaceModel *im = nullptr;
  const iface::Slot *slot = ifaceSlotFor(fn.name, opt, &im);
  std::vector<const iface::ParamContract *> contract(fn.params.size(), nullptr);
  std::vector<std::string> ifaceAssumptions;
  // Declared per-struct ranges that actually applied to THIS entry (DESIGN.md §22.480). Collected while the
  // parameters are written and turned into named assumptions below: a declared range narrows the analysis, so
  // it may never be invisible -- the same rule `same_alloc`, `nullable` and `synthesis_frontier` follow.
  std::vector<std::string> declaredNotes;
  if (slot && slot->params.size() != fn.params.size()) {
    e.notes.push_back("@" + fn.name + " is registered in " + im->name + "." + slot->name + ", but that slot's contract describes " +
                      std::to_string(slot->params.size()) + " parameter(s) and the function takes " + std::to_string(fn.params.size()) +
                      ": the contract was NOT applied, the parameters are synthesised generically");
    slot = nullptr;
  }
  if (slot)
    for (size_t i = 0; i < fn.params.size(); ++i) contract[i] = &slot->params[i];
  // `session`/`session_out` need the ctor slot to be RUN to build the object (Phase C). Until then they degrade to
  // `kernel_owned`: a legal, untainted object. That is a narrowing -- the driver's own state really is influenced by
  // earlier calls from the same attacker -- so each one is named in the report's assumptions, never silently.
  auto roleOf = [&](size_t i) { return contract[i] ? contract[i]->role : iface::Role::Value; };
  auto untaintedRole = [&](size_t i) {
    switch (roleOf(i)) {
      case iface::Role::Value: return false;
      case iface::Role::UserAddr: return false;  // the bytes behind it are the attacker's; see userAddrPtr below
      default: return true;
    }
  };
  // a `user_addr` POINTER is an address in another address space: the handler may pass it to copy_from_user (whose
  // model never dereferences it) but may not follow it itself. Modelled as a real but EMPTY object, so any direct
  // load or store through it is reported out of bounds -- which is exactly what dereferencing a __user pointer is.
  // A `user_addr` SCALAR (ioctl's `unsigned long arg`) is just an attacker-controlled value and takes the normal path.
  auto userAddrPtr = [&](size_t i) { return contract[i] && contract[i]->role == iface::Role::UserAddr && fn.params[i].kind == "ptr"; };
  // length <-> buffer relations, decided before the parameters are written because they also decide which `const char *`
  // is a C string. The byte buffers that belong to a length are those since the previous length parameter (if there are
  // none, those up to the next one). A `const char *` in a group that also holds another buffer is ambiguous from the
  // signature: `ares_inet_net_pton(af, src, dst, size)` parses src as a C string and size describes dst, while
  // `copy(char *dst, const char *src, int n)` memcpy's n bytes of src. It gets both: at least as big as the length AND
  // NUL-terminated (DESIGN.md §22.346). Cost: a function that reads such a string past both is not caught.
  std::vector<std::string> relations;
  std::set<size_t> paired;        // parameter indices given a length
  std::set<size_t> pairedString;  // ... of them, the `const char *` of a mixed group: also NUL-terminated
  for (size_t i = 0; i < fn.params.size(); ++i) {
    const ParamInfo &p = fn.params[i];
    bool ctx = matches(opt.ctxNames, p.name) || p.opaqueHandle;
    // under an interface contract the parameter relations are stated by the model (`size_from`), not guessed from
    // names -- pairing `count` with a __user buffer by name would force the buffer's (empty) size onto it
    if (slot || opt.hostile || p.kind != "int" || ctx || !isLenName(p.name) || p.bits < 8) continue;
    auto isBuf = [&](const ParamInfo &q) { return isByteBuffer(q) && !q.opaqueHandle && !matches(opt.ctxNames, q.name); };
    auto isCStr = [](const ParamInfo &q) { return q.pointee == "int" && q.pointeeIsChar && q.pointeeConst; };
    std::vector<size_t> bufs;
    for (size_t j = i; j-- > 0;) {
      const ParamInfo &q = fn.params[j];
      if (q.kind == "int" && isLenName(q.name)) break;
      if (isBuf(q)) bufs.push_back(j);
    }
    if (bufs.empty())
      for (size_t j = i + 1; j < fn.params.size(); ++j) {
        const ParamInfo &q = fn.params[j];
        if (q.kind == "int" && isLenName(q.name)) break;
        if (isBuf(q)) bufs.push_back(j);
      }
    bool other = false;
    for (size_t j : bufs) other |= !isCStr(fn.params[j]);
    for (size_t j : bufs) {
      const ParamInfo &buf = fn.params[j];
      paired.insert(j);
      if (other && isCStr(buf)) pairedString.insert(j);
      std::string r = (p.isSigned ? p.name + " >= 0 => " : "") + std::string("(size_t)") + p.name + (elemSize(buf) > 1 ? " * " + std::to_string(elemSize(buf)) : std::string()) + " <= size(" + buf.name + ")";
      relations.push_back(r);
      e.notes.push_back("assumed the caller passes a consistent pair: " + r + " (use --hostile to drop this and let '" + p.name + "' disagree with the buffer)");
    }
  }
  for (size_t i = 0; i < fn.params.size(); ++i) {
    const ParamInfo &p = fn.params[i];
    bool ctx = matches(opt.ctxNames, p.name) || p.opaqueHandle;  // an opaque handle is library state, not caller data
    if (contract[i]) ctx = untaintedRole(i);  // the contract is authoritative: it knows what the interface hands this slot
    y << "      " << p.name << ": { ";
    if (userAddrPtr(i)) {
      y << "taint: none, kind: buffer, size: { min: 0, max: 0 } }\n";
      e.notes.push_back("'" + p.name + "' is a userspace address (" + im->name + "." + slot->name +
                        " contract): modelled as an empty object, so the handler dereferencing it directly is reported "
                        "out of bounds; its bytes reach the code only through the copy_from_user/copy_to_user models");
      continue;
    }
    if (p.kind == "int" || p.kind == "bool") {
      y << "taint: " << (ctx ? "none" : "value");
      if (!ctx) ++tainted;
      if (p.kind == "int") y << ", type: " << intType(p.bits, p.isSigned);
    } else if (p.kind == "ptr" && p.isStdString) {
      // std::basic_string<char>/<wchar_t>: a self-consistent SSO-or-heap object (entry::PlannedParam::StdString),
      // not the generic independently-symbolic byte-buffer layout below -- see IMPLEMENTATION_PLAN "std::string 不
      // 变式建模" (entry-parameter synthesis follow-up; this is what turns on the fix for real scans, not just
      // hand-written specs).
      bool taintPointee = !ctx;
      if (taintPointee) ++tainted;
      uint64_t hi = taintPointee ? std::min<uint64_t>(opt.bufMax, 256) : 0;
      const char *kind = p.stdStringCharBits == 32 ? "wstring" : "string";
      y << "taint: " << (taintPointee ? "pointee" : "none") << ", kind: " << kind << ", size: { min: 0, max: " << hi << " }";
      e.notes.push_back("'" + p.name + "' is a std::basic_string<" + std::string(p.stdStringCharBits == 32 ? "wchar_t" : "char") +
                         ">: modelled as a self-consistent libstdc++ object (SSO-or-heap, content length 0.." + std::to_string(hi) +
                         "), not a generic byte buffer");
    } else if (p.kind == "ptr" && p.isStdVector) {
      // std::vector<T>: a self-consistent `_Vector_impl` (entry::PlannedParam::StdVector), not the generic
      // independently-symbolic 3-pointer byte-buffer layout below -- see IMPLEMENTATION_PLAN "std::vector/std::map
      // 入口参数合成自洽化".
      bool taintPointee = !ctx;
      if (taintPointee) ++tainted;
      uint64_t hi = taintPointee ? std::min<uint64_t>(opt.bufMax / std::max<uint64_t>(p.stdVectorElemBits / 8, 1), 64) : 0;
      y << "taint: " << (taintPointee ? "pointee" : "none") << ", kind: vector, elem_bits: " << p.stdVectorElemBits << ", size: { min: 0, max: " << hi << " }";
      e.notes.push_back("'" + p.name + "' is a std::vector<T> (T " + std::to_string(p.stdVectorElemBits) +
                         "-bit scalar): modelled as a self-consistent libstdc++ object (0.." + std::to_string(hi) +
                         " elements), not a generic byte buffer");
    } else if (p.kind == "ptr" && p.isStdMap) {
      // std::map<K,V>: a self-consistent `_Rb_tree` with 0 or 1 nodes (entry::PlannedParam::StdMap) -- a deliberately
      // narrowed approximation, not the generic byte-buffer layout below; see IMPLEMENTATION_PLAN "std::vector/
      // std::map 入口参数合成自洽化" for the full red-black-tree diagnosis and why this scope was chosen.
      bool taintPointee = !ctx;
      if (taintPointee) ++tainted;
      y << "taint: " << (taintPointee ? "pointee" : "none") << ", kind: map, key_bits: " << p.stdMapKeyBits << ", val_bits: " << p.stdMapValBits << "";
      e.notes.push_back("'" + p.name + "' is a std::map<K,V> (K " + std::to_string(p.stdMapKeyBits) + "-bit, V " +
                         std::to_string(p.stdMapValBits) + "-bit scalar): modelled as a self-consistent libstdc++ "
                         "red-black tree with 0 or 1 entries (an approximation -- see docs), not a generic byte buffer");
    } else if (p.kind == "ptr") {
      uint64_t lo = 1, hi = opt.bufMax;
      // a sockaddr-family struct pointer (`struct sockaddr *addr, socklen_t addr_len`) is a real object of up to
      // `addr_len` bytes, not a fixed `sizeof(struct sockaddr)` point -- real callers routinely pass a bigger
      // concrete address-family struct through this generic base pointer (see isSockaddrLike); the `addr_len <=
      // size(addr)` relation generated below (the "length <-> buffer relation" loop) is what actually ties the two
      // together, but it needs this param's own size to be a range for that constraint to mean anything.
      if (isSockaddrLike(p)) {
        // `--linux`: a real Linux syscall argument of this shape is always backed by at least
        // sizeof(struct sockaddr_storage) bytes (kernel-wide convention, see kSockaddrStorageSize) regardless of
        // the declared pointee type -- without this, a param declared `struct sockaddr_un *` (110 bytes) can be
        // synthesized smaller than what real in-kernel code (e.g. unix_mkname_bsd) legally writes up to, a narrow
        // false positive found and diagnosed in DESIGN.md §22.144. Outside `--linux` this guarantee does not
        // generally hold (arbitrary userspace code taking a sockaddr-shaped pointer may allocate exactly
        // sizeof(declared struct), no more), so raising the floor there would trade this false positive for a
        // real false negative -- only apply it when scanning real kernel code.
        lo = opt.linuxApi ? std::max<uint64_t>(p.pointeeSize, kSockaddrStorageSize) : p.pointeeSize;
        hi = std::max<uint64_t>(opt.bufMax, lo);
      }
      else if (p.pointee == "struct" && p.pointeeSize) lo = hi = p.pointeeSize;
      else if (p.pointee == "int" && p.pointeeSize > 1) { lo = p.pointeeSize; hi = std::max<uint64_t>(opt.bufMax, p.pointeeSize); }
      else if (p.pointee == "pointer") { lo = hi = 64; e.notes.push_back("'" + p.name + "' is a pointer to a pointer: modelled as an untainted 64-byte object, the inner pointers are not initialised");  }
      else if (p.pointee == "function" || p.pointee == "other") { lo = hi = 64; e.notes.push_back("'" + p.name + "' has pointee type '" + p.cType + "': modelled as an untainted 64-byte object"); }
      if (!p.udStruct.empty() && !opt.noPtrFields) lo = hi = 64;
      // The interface contract may state the object's real size when the declared pointee type understates it: a
      // QNX resmgr handler is handed the receive buffer, of which `io_devctl_t` is only the 16-byte header
      // (hlir/iface/Interface.h, ParamContract::sizeMin). This is the one contract key that can WIDEN, so it is
      // named in `assumptions` below whenever it departs from the declared size -- the same discipline the
      // narrowing roles are held to (DESIGN.md §22.361, §22.365).
      if (contract[i] && contract[i]->sizeMin && contract[i]->sizeMax) {
        lo = *contract[i]->sizeMin;
        hi = *contract[i]->sizeMax;
        need = std::max(need, hi);
      }
      bool taintPointee = !ctx && p.pointee != "function" && p.pointee != "other" && p.pointee != "pointer";
      if (taintPointee) ++tainted;
      // `kernel_owned` is the same situation as a session and gets the same treatment: the KERNEL built this
      // object before the handler ran, so a zero fill is not a neutral default but one specific state the caller
      // is almost never in. A filesystem handed a zeroed `struct inode` sees i_size 0 and returns before it
      // parses anything -- measured on fs/isofs, where the first run of the VFS contracts left all 23 entries at
      // `checks queried == 0` (DESIGN.md §22.477). Symbolic harness-labelled content instead is a WIDENING, and a
      // finding decided only by such a byte comes back `harness_only`, which is what makes it safe to do.
      bool sessionRole = contract[i] && (contract[i]->role == iface::Role::Session ||
                                         contract[i]->role == iface::Role::SessionOut ||
                                         contract[i]->role == iface::Role::KernelOwned);
      // a `const char *` no length parameter describes (or one of a mixed group, see the relations above) is a C string:
      // NUL-terminated, so reads that run to the terminator stay in the object. Under --hostile nothing is paired, so it
      // was a buffer whenever the function had a length: keep that.
      bool anyLenParam = false;
      for (auto &q : fn.params) anyLenParam |= q.kind == "int" && isLenName(q.name);
      bool cstr = p.pointee == "int" && p.pointeeIsChar && p.pointeeConst && !ctx && (opt.hostile ? !anyLenParam : !paired.count(i) || pairedString.count(i));
      if (cstr) e.notes.push_back("'" + p.name + "' is a `const char *` with no length parameter: modelled as a NUL-terminated C string of 1.." + std::to_string(std::min<uint64_t>(opt.bufMax, 256)) + " bytes");
      if (p.pointee == "struct" && p.pointeeSize > opt.maxObjLimit) e.skipReason = "parameter '" + p.name + "' points to a struct of " + std::to_string(p.pointeeSize) + " bytes (limit " + std::to_string(opt.maxObjLimit) + ")";
      if (p.pointee == "struct") need = std::max(need, isSockaddrLike(p) ? hi : p.pointeeSize);
      y << "taint: " << (taintPointee ? "pointee" : "none") << ", kind: " << (cstr ? "cstring" : "buffer") << ", size: { min: " << lo << ", max: " << (cstr ? std::min<uint64_t>(hi, 256) : hi) << " }";
      // The session object (DESIGN.md §22.381). Its bytes are the DRIVER's, written by a constructor and by every
      // earlier call on the same connection -- so a zero fill is not a neutral default but a specific, usually
      // impossible state: a module's own validity gate (`attr->magic == MAGIC`, `ocb->ctrl != NULL`) can never
      // pass against it, and the handler returns its error path before any of its real work is analysed. Giving
      // them symbolic, harness-labelled content instead is a WIDENING -- the session can now be in states its
      // constructor could never build -- and findings decided only by such a byte come back `harness_only`.
      // Applied even when `setup:` runs the real constructor below: that constructor's own stores override these
      // bytes, and what it does NOT write is exactly what nobody knows.
      if (sessionRole) y << ", content: unknown";
      // consumed by whichever branch below writes this parameter's `where:` list, so only one is ever emitted
      std::string pendingInlineWh = inlineCountWheres(p.inlineCounts, false);
      pendingInlineWh += assertWheres(p.structName, p.pointeeSize, opt, !pendingInlineWh.empty());
      pendingInlineWh += declaredWheres(p.structName, p.pointeeSize, opt, !pendingInlineWh.empty(), &declaredNotes);
      if (!p.udStruct.empty() && !opt.noPtrFields) {
        // the handle is an object whose first 8 bytes are its user data: a pointer to a legal `struct udStruct` (see wayland.core)
        bool st = !opt.userDataZero;
        std::string ud = "{ offset: 0, kind: buffer, taint: " + std::string(st ? "pointee" : "none") + ", size: { min: " + std::to_string(p.udSize) + ", max: " + std::to_string(p.udSize) + " }" + (p.udOwned ? ", owned: true" : "");
        need = std::max(need, p.udSize);
        unsigned budget = opt.maxFields, made = 0, selfLinks = 0, container = 0;
        std::map<std::string, std::pair<unsigned, std::string>> skipped;
        std::string kids = fieldsYaml(*p.udPtrFields, st, opt, all, p.name + "->user_data", skipped, budget, made, selfLinks, container, need, &declaredNotes, p.udStruct, p.udSize);
        for (auto &kv : skipped) e.notes.push_back(std::to_string(kv.second.first) + " pointer field(s) of the user data of '" + p.name + "' left NULL: " + kv.first + " (e.g. " + kv.second.second + ")");
        if (!kids.empty()) ud += ", fields: [ " + kids + " ]";
        y << ", fields: [ " << ud << " } ]";
        e.notes.push_back("'" + p.name + "' is a handle whose user data is a struct " + p.udStruct + " (" + std::to_string(p.udSize) + " bytes, taken from `struct " + p.udStruct + " *x = get_user_data(" + p.name + ")`): modelled as an object holding a pointer to it; its state is " + (p.udOwned ? "a heap object the callee owns (the code frees it); " : "") + (st ? "attacker-influenced (over-approximation; --user-data-zero for zeroes)" : "zero"));
      }
      if (p.freed) {
        y << ", owned: true";
        e.notes.push_back("'" + p.name + "' is passed to free(): modelled as a heap object the callee owns (freeing it is not an invalid free; freeing it twice or using it afterwards still is)");
      }
      if (p.viaContainerOf) {
        y << ", at: " << p.at;
        e.notes.push_back("'" + p.name + "' is used with container_of: it points " + std::to_string(p.at) + " bytes into a struct " + p.structName + " (" + std::to_string(p.pointeeSize) + " bytes)");
      }
      if (p.pointee == "struct" && !p.ptrFields->empty() && !opt.noPtrFields) {
        unsigned budget = opt.maxFields, made = 0, selfLinks = 0, container = 0;
        std::map<std::string, std::pair<unsigned, std::string>> skipped;
        std::string fy = fieldsYaml(*p.ptrFields, taintPointee, opt, all, p.name, skipped, budget, made, selfLinks, container, need, &declaredNotes, p.structName, p.pointeeSize);
        for (auto &kv : skipped)
          e.notes.push_back(std::to_string(kv.second.first) + " pointer field(s) of '" + p.name + "' left NULL: " + kv.first + " (e.g. " + kv.second.second + ")");
        if (container) e.notes.push_back("'" + p.name + "': " + std::to_string(container) + " pointer field(s) are used with container_of: they point at an embedded member inside a larger object (offset taken from the code), not at its start");
        if (selfLinks) e.notes.push_back("'" + p.name + "': " + std::to_string(selfLinks) + " intrusive list link(s) (next/prev) point back at their own list head, i.e. the lists are empty");
        // pointer arrays: the element count the struct stores next to the array (argc for argv) stays within the slots we created
        std::string wh;
        for (auto &f : *p.ptrFields)
          if (f.ptrArray && f.lenOffset >= 0 && f.lenBits)
            wh += (wh.empty() ? "" : ", ") + std::string("{ offset: ") + std::to_string(f.lenOffset) + ", type: " + intType(f.lenBits, f.lenSigned) + ", range: [1, " + std::to_string(f.arraySlots) + "] }";
        // ...and the counts of the struct's own INLINE arrays, which no size mechanism can reach (DESIGN.md §22.356)
        wh += pendingInlineWh.empty() ? "" : (wh.empty() ? "" : ", ") + pendingInlineWh;
        pendingInlineWh.clear();
        if (!wh.empty()) y << ", where: [ " << wh << " ]";
        if (!fy.empty()) {
          y << ", fields: [ " << fy << " ]";
          e.notes.push_back("'" + p.name + "': " + std::to_string(made) + " pointer field(s) of struct " + p.structName + " point to legal objects (instead of NULL); " + (taintPointee ? "their content is attacker controlled" : "their content is zero"));
        }
      } else if (p.pointee == "struct" && p.structHasPointers) {
        e.notes.push_back("'" + p.name + "' points to struct " + p.structName + " that contains pointers: they are zero bytes (NULL), so dereferencing them is reported as a null dereference");
      }
      // a struct with no pointer fields at all never reaches the branch above, but its own inline arrays still
      // bound its count members (DESIGN.md §22.356)
      if (!pendingInlineWh.empty()) y << ", where: [ " << pendingInlineWh << " ]";
    } else {
      y << "taint: none";
      e.notes.push_back("parameter '" + p.name + "' has unsupported type '" + p.cType + "'");
    }
    y << " }\n";
  }
  if (slot) {
    // `size_from`: the contract states which parameter is this buffer's length. It is a real relation, so it is
    // emitted as one -- but only for a buffer that HAS an object. A __user buffer is empty by construction (see
    // userAddrPtr), and "count <= size(buf)" against an empty object would pin count to 0 and analyse nothing.
    for (size_t i = 0; i < fn.params.size(); ++i) {
      if (!contract[i] || contract[i]->sizeFrom.empty()) continue;
      const std::string &len = contract[i]->sizeFrom;
      // `size_from` names a parameter of the SLOT, and the contract is matched by position -- so resolve it to the
      // slot's parameter index and then use the FUNCTION's own name for it. Looking the contract's name up among the
      // function's parameter names instead would drop the relation whenever a handler spells `count` as `nbytes`.
      size_t li = slot->params.size();
      for (size_t k = 0; k < slot->params.size(); ++k)
        if (slot->params[k].name == len) { li = k; break; }
      if (userAddrPtr(i))
        e.notes.push_back("'" + fn.params[i].name + "' is " + len + " bytes long per the " + im->name + "." + slot->name +
                          " contract, but it is a userspace address with no object here, so '" +
                          (li < fn.params.size() ? fn.params[li].name : len) + "' stays unconstrained");
      // A relation needs a VARIABLE on its left. An untainted scalar is a fixed value in the generated spec, and
      // `(size_t)len <= size(str)` against one produced a harness that did not compile -- "integer literal
      // requires an integer type" -- which surfaced only as `unknown` with 0/0 blocks and an input_error, i.e. a
      // contract that silently deleted its own entries (DESIGN.md §22.478: three isofs d_compare slots). Drop it
      // and say so: a buffer no longer tied to its length can be read past, so the reader must know.
      else if (li < fn.params.size() && untaintedRole(li))
        e.notes.push_back("the " + im->name + "." + slot->name + " contract sizes '" + fn.params[i].name + "' by '" +
                          fn.params[li].name + "', but that parameter's role makes it untainted, and an untainted "
                          "scalar is a fixed value with nothing to constrain: the relation was DROPPED, so the "
                          "buffer is not tied to the length and a read past it may be an artefact");
      else if (li >= fn.params.size())
        e.notes.push_back("the " + im->name + "." + slot->name + " contract sizes '" + fn.params[i].name + "' by '" + len +
                          "', which is not a parameter of that slot: the relation was dropped");
      else
        relations.push_back("(size_t)" + fn.params[li].name + " <= size(" + fn.params[i].name + ")");
    }
    ifaceAssumptions.push_back("interface " + im->name + "." + slot->name + ": the parameters are what that slot's contract says they are, not what their types allow");
    // A declared prologue is the module's own initialiser -- the thing that has to have run for the globals this
    // handler reads to hold the values it is really called with. It is NOT executed (DESIGN.md §22.368 §1), and
    // the key used to carry a comment claiming otherwise. Say it here instead of in a comment nobody reads: this
    // is the whole of what declaring a prologue does today, and it sits next to G1's `global_initial_value`
    // assumption, which names the individual branches that uninitialised state decided on its own (§22.362).
    if (!im->prologue.empty()) {
      std::string fns;
      for (auto &p : im->prologue) fns += (fns.empty() ? "" : ", ") + p;
      ifaceAssumptions.push_back("the " + im->name + " contract declares the module initialiser(s) " + fns +
                                 " as this handler's prologue, but they are NOT executed: every global still holds its "
                                 "static initialiser (usually zero), which is a state no handler is ever really called in");
    }
    for (size_t i = 0; i < fn.params.size(); ++i) {
      if (!contract[i]) continue;
      const std::string &n = fn.params[i].name;
      // `size:` on a pointer is the only contract key that can make the object BIGGER than its declaration. A
      // widening cannot hide a defect but it can manufacture one (a payload read that is really in bounds would
      // otherwise be a confirmed OOB, and the other way round once the object is grown), so say it out loud.
      if (contract[i]->sizeMin && contract[i]->sizeMax && fn.params[i].kind == "ptr" &&
          (fn.params[i].pointeeSize != *contract[i]->sizeMin || fn.params[i].pointeeSize != *contract[i]->sizeMax))
        ifaceAssumptions.push_back("'" + n + "' points at an object of " + std::to_string(*contract[i]->sizeMin) + ".." +
                                   std::to_string(*contract[i]->sizeMax) + " bytes per the " + im->name + "." + slot->name +
                                   " contract, not the " + std::to_string(fn.params[i].pointeeSize) +
                                   " bytes its declared type gives: accesses past the declared pointee are judged against "
                                   "that size, in both directions");
      switch (contract[i]->role) {
        case iface::Role::Session:
        case iface::Role::SessionOut:
          ifaceAssumptions.push_back("'" + n + "' is the session object " + im->name + "." +
                                     (im->sessionCtor.empty() ? std::string("<no constructor slot named>") : im->sessionCtor) +
                                     " builds. Its content is UNKNOWN, not zero: every byte it does not get from a "
                                     "constructor this scan actually ran is a free, untainted value, so the session may be "
                                     "in a state no constructor could build (a widening) while still never carrying "
                                     "attacker data (a narrowing -- a previous call from the same attacker really can "
                                     "influence it). A finding decided only by such a byte is reported as harness_only");
          break;
        case iface::Role::KernelOwned:
          ifaceAssumptions.push_back("'" + n + "' is built by the kernel before the handler runs: its content is untainted and its constructor's invariants are assumed");
          break;
        case iface::Role::Out:
          ifaceAssumptions.push_back("'" + n + "' is written by the callee: untainted on entry");
          break;
        case iface::Role::UserAddr:
          if (fn.params[i].kind == "ptr")
            ifaceAssumptions.push_back("'" + n + "' is a userspace address: it backs no kernel object, so only the copy_from_user/copy_to_user models can read its bytes");
          break;
        case iface::Role::Value:
          break;
      }
    }
  }
  if (!relations.empty()) {
    y << "    relations:\n";
    for (auto &r : relations) y << "      - \"" << r << "\"\n";
  }
  if (!declaredNotes.empty()) {
    std::set<std::string> seen;  // one object's range can be reached through several fields of the same entry
    for (auto &n : declaredNotes)
      if (seen.insert(n).second) ifaceAssumptions.push_back(n);
  }
  if (!ifaceAssumptions.empty()) {
    y << "    assumptions:\n";
    for (auto &a : ifaceAssumptions) y << "      - \"" << a << "\"\n";
  }
  // `init:` goes into the generated spec text, not into the plan behind its back: the spec IS the interface, and a
  // reader has to be able to see that the harness calls the module's initialiser before the entry.
  // `setup:` -- the constructor of THIS handler's own session (DESIGN.md §22.371). The interface declares which
  // slot builds the session (`created_by`); the per-table registrations say which concrete function sits in that
  // slot of the SAME table as this handler. Both halves are needed: a module registers many tables of one type, so
  // the interface alone cannot answer "whose `open`".
  //
  // Ambiguity is NOT resolved by picking one. `snd_pcm_ioctl` is registered in both the playback and the capture
  // table, which have different constructors; choosing either would silently decide which device is being
  // analysed. When the tables disagree, no `setup:` is emitted and the note says so -- the entry falls back to the
  // field-by-field session it has today, which is worse but honest.
  std::string setupLine;
  if (slot && im && !im->sessionCtor.empty() && !im->sessionParam.empty() && opt.vtableInstances) {
    const iface::Slot *cs = im->slot(im->sessionCtor);
    // which parameter of THIS entry is the session, and which parameter of the constructor produces it
    std::string sessParam, ctorParamName;
    for (size_t i = 0; i < slot->params.size() && i < fn.params.size(); ++i)
      if (slot->params[i].role == iface::Role::Session) sessParam = fn.params[i].name;
    size_t ctorOutIdx = cs ? cs->params.size() : 0;
    if (cs)
      for (size_t i = 0; i < cs->params.size(); ++i)
        if (cs->params[i].role == iface::Role::SessionOut) ctorOutIdx = i;
    std::set<std::string> ctors;
    for (auto &kv : *opt.vtableInstances) {
      if (kv.second.tag != im->structTag) continue;
      auto me = kv.second.slots.find(slot->name);
      if (me == kv.second.slots.end() || me->second != fn.name) continue;  // not this handler's table
      auto ct = kv.second.slots.find(im->sessionCtor);
      if (ct != kv.second.slots.end()) ctors.insert(ct->second);
    }
    if (!sessParam.empty() && cs && ctorOutIdx < cs->params.size()) {
      if (ctors.size() == 1) {
        const std::string &ctor = *ctors.begin();
        // the constructor's own parameter NAME at that index, from the function the module really registered
        std::string cpName;
        for (auto &g : all)
          if (g.name == ctor && ctorOutIdx < g.params.size()) cpName = g.params[ctorOutIdx].name;
        if (cpName.empty())
          e.notes.push_back("the " + im->name + " contract says @" + ctor + " builds this handler's session, but its parameter #" +
                            std::to_string(ctorOutIdx) + " could not be named: the session is still synthesised field by field");
        else {
          std::string suc = cs->success;
          setupLine = "    setup: { function: " + ctor + ", session_param: " + sessParam + ", ctor_param: " + cpName +
                    (suc.empty() ? "" : ", success: \"" + suc + "\"") + " }\n";
        }
      } else if (ctors.size() > 1) {
        std::string names;
        for (auto &c : ctors) names += (names.empty() ? "" : ", ") + ("@" + c);
        e.notes.push_back("@" + fn.name + " is registered in " + std::to_string(ctors.size()) + " " + im->structTag +
                          " tables whose " + im->sessionCtor + " differs (" + names +
                          "): which session it is handed depends on which device was opened, so no constructor was run and the "
                          "session is synthesised field by field");
      }
    }
  }
  std::string head = need > opt.maxObj ? "defaults:\n  max_obj: " + std::to_string(need) + "\n\n" : "";
  if (!opt.initFunctions.empty()) {
    head += "init:\n  functions:\n";
    for (auto &n : opt.initFunctions) head += "    - " + n + "\n";
    head += "\n";
  }
  // the setup line belongs inside this entry's mapping, right after `label:`, which this generator emitted itself
  std::string body = y.str();
  if (!setupLine.empty()) {
    size_t lab = body.find("\n    label: ");
    size_t eol = lab == std::string::npos ? std::string::npos : body.find('\n', lab + 1);
    if (eol != std::string::npos) body.insert(eol + 1, setupLine);
    else e.notes.push_back("the session constructor could not be placed in the generated spec: it was not run");
  }
  e.specText = head + body;
  if (!fn.lowered) e.skipReason = "not lowered: " + (fn.skipReason.empty() ? std::string("unsupported construct") : fn.skipReason);
  // An interface may state that its attacker data does not come through the parameters at all (a filesystem's
  // does not: it arrives through `sb_bread()` inside the body, DESIGN.md §22.475/§22.477). Then `tainted == 0`
  // is true and beside the point, and skipping on it throws away precisely the parsers worth scanning. The flag
  // suppresses the skip and nothing else -- no taint is granted here -- so the entry is named for what it is.
  else if (tainted == 0 && slot && im && im->attackerInBody && !opt.includeNoArg)
    e.notes.push_back("@" + fn.name + " has no attacker-controlled parameter, and " + im->name +
                      " states that its attacker data arrives inside the body (a mounted image through the block "
                      "layer, not a handler argument): the entry is scanned, and whether anything reaches it is "
                      "then a fact about the models, visible as `checks queried`");
  else if (tainted == 0 && !opt.includeNoArg)
    e.skipReason = slot ? "no attacker-controlled parameter under the " + im->name + "." + slot->name +
                              " contract: everything this slot is handed is kernel-owned or session state (running the "
                              "session constructor is not implemented; --include-noarg runs it anyway)"
                        : "no attacker-controlled parameter (use --include-noarg to run it anyway)";
  return e;
}

// `tag#field` -> the interface model that describes that struct, and the slot inside it. Unknown tags and unknown
// fields both answer "": an interface model is a closed statement about which fields of a vtable are dispatch
// entry points, so a field it does not list is deliberately not one (`.owner`, `.llseek` on an interface that
// does not model seeking), not an omission to be guessed around.
const iface::Slot *ifaceSlotFor(const std::string &function, const Options &opt, const iface::InterfaceModel **model) {
  if (model) *model = nullptr;
  if (!opt.interfaces || !opt.vtableBindings) return nullptr;
  auto it = opt.vtableBindings->find(function);
  if (it == opt.vtableBindings->end()) return nullptr;
  for (const std::string &key : it->second) {  // std::set: sorted, so the answer is deterministic
    size_t h = key.find('#');
    if (h == std::string::npos) continue;
    const iface::InterfaceModel *m = opt.interfaces->byStruct(key.substr(0, h));
    if (!m) continue;
    const iface::Slot *sl = m->slot(key.substr(h + 1));
    if (!sl) continue;
    if (model) *model = m;
    return sl;
  }
  return nullptr;
}

std::string ifaceSlotOf(const std::string &function, const Options &opt) {
  const iface::InterfaceModel *m = nullptr;
  const iface::Slot *sl = ifaceSlotFor(function, opt, &m);
  return sl ? m->name + "." + sl->name : std::string();
}

std::vector<Entry> discover(const std::vector<FunctionInfo> &fns, const Options &opt) {
  std::vector<Entry> out;
  for (auto &f : fns) {
    if (f.name.rfind("__hlir_", 0) == 0) continue;
    std::string why;
    switch (opt.mode) {
      case EntryMode::All: why = "all"; break;
      case EntryMode::Exported: why = f.addrTaken ? "callback" : (!f.isStatic ? "exported" : ""); break;
      case EntryMode::Roots: why = f.addrTaken ? "callback" : (!f.isStatic && f.callers == 0 ? "root" : ""); break;
      case EntryMode::Iface: {
        std::string slot = ifaceSlotOf(f.name, opt);
        why = slot.empty() ? "" : "iface " + slot;
        break;
      }
    }
    if (why.empty()) continue;
    if (!opt.only.empty() && !matches(opt.only, f.name)) continue;
    if (!opt.skip.empty() && matches(opt.skip, f.name)) continue;
    Entry e = makeEntry(f, opt, fns);
    e.why = why;
    out.push_back(std::move(e));
  }
  return out;
}

}  // namespace hlir::scan

namespace hlir::scan {

bool resolvePreconditionFields(const std::string &text, const std::string &path, const std::vector<frontend::FunctionInfo> &fns, std::string &out, std::string &err) {
  out = text;
  if (text.find("field:") == std::string::npos) return true;
  yaml::YNode root;
  Diagnostics d;
  if (!yaml::parseYaml(text, path, root, d)) { err = d.str(); return false; }
  std::vector<std::string> lines;
  {
    std::istringstream in(text);
    std::string l;
    while (std::getline(in, l)) lines.push_back(l);
  }
  auto *pl = root.get("preconditions");
  if (!pl || pl->kind != yaml::YNode::Seq) return true;
  for (auto &en : pl->seq) {
    auto *fn = en.get("function");
    auto *ps = en.get("params");
    if (!fn || !ps || ps->kind != yaml::YNode::Map) continue;
    const FunctionInfo *info = nullptr;
    for (auto &f : fns) if (f.name == fn->scalar) info = &f;
    for (auto &kv : ps->map) {
      auto *wh = kv.second.get("where");
      if (!wh || wh->kind != yaml::YNode::Seq) continue;
      for (auto &w : wh->seq) {
        auto *fld = w.get("field");
        if (!fld) continue;
        auto fail = [&](const std::string &m) { err = path + ":" + std::to_string(fld->line) + ": " + m; return false; };
        if (!info) continue;  // a function this translation unit does not define: resolved where it is
        const ParamInfo *pi = nullptr;
        for (auto &p : info->params) if (p.name == kv.first) pi = &p;
        if (!pi || pi->scalarFields.empty()) return fail("parameter '" + kv.first + "' of @" + info->name + " does not point to a struct with integer members");
        const frontend::ScalarFieldInfo *sf = nullptr;
        for (auto &f : pi->scalarFields) if (f.name == fld->scalar) sf = &f;
        if (!sf) {
          std::string have;
          for (size_t i = 0; i < pi->scalarFields.size() && i < 12; ++i) have += (i ? ", " : "") + pi->scalarFields[i].name;
          return fail("struct " + pi->structName + " has no integer member '" + fld->scalar + "' (members: " + have + ")");
        }
        size_t ln = fld->line - 1;
        if (ln >= lines.size() || lines[ln].find('{') == std::string::npos) return fail("write `field:` entries in flow style: { field: NAME, range: [lo, hi] }");
        std::regex re("field:\\s*" + fld->scalar);
        lines[ln] = std::regex_replace(lines[ln], re, "offset: " + std::to_string(sf->offset) + ", type: " + intType(sf->bits, sf->isSigned), std::regex_constants::format_first_only);
      }
    }
  }
  out.clear();
  for (auto &l : lines) out += l + "\n";
  return true;
}

}  // namespace hlir::scan

// C -> `core` lowering on top of the Clang AST (the only file that includes clang headers).
//
// Scheme (kept deliberately simple; the analysis engines do the clever parts):
//   * every local variable / parameter lives in a `core.alloca`; no SSA construction, mem2reg is not needed;
//   * every memory access is preceded by the explicit `core.check.*` ops that its UB kind requires (§18.4), so the
//     result also passes `hlir-opt --coverage`; accesses to a plain local/param/global object waive the checks that
//     are trivially satisfied (waived="object known"; uninit is kept for locals);
//   * Clang already made conversions explicit (ImplicitCastExpr), so integer promotions/usual arithmetic conversions
//     need no logic here;
//   * `&&`, `||`, `?:` use blocks with block arguments;
//   * every op carries loc("file":line:col) of the C expression it came from.
//
// Constructs that need a lowering convention (all documented in docs/IMPLEMENTATION_PLAN.md):
//   * global/static variables with initializers: `core` globals are zero-initialized, so every initialized global G
//     gets `@__hlir_init.G()` that fills it once (guarded by a flag global) and every access to G calls it first;
//     string literals are const globals initialized the same way;
//   * function pointers: `core.func_addr`; an indirect call is a compare chain over the address-taken functions of the
//     translation unit with the same signature (no match = unreachable, i.e. the call target is not a known function);
//   * struct by value: parameters are passed as a pointer to a caller-made copy, a returned struct is written through a
//     hidden first parameter `%sret`;
//   * bit-fields: byte-wise read-modify-write (no uninit check on the neighbouring bits);
//   * goto/labels: blocks; VLA: a heap object of the computed size; GNU statement expressions, `?:` with omitted middle,
//     case ranges, compound literals, designated initializers, __builtin_*_overflow.
// Anything not handled is reported as "unsupported" and the whole lowering fails; a silent approximation would make
// the analysis unsound without telling the user.
#include "hlir/frontend/Frontend.h"
#include "hlir/support/IndirectCall.h"

#include <algorithm>
#include <deque>
#include <functional>
#include <iterator>
#include <map>
#include <set>
#include <regex>
#include <sstream>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/CXXInheritance.h"
#include "clang/AST/GlobalDecl.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/APSInt.h"
#include "llvm/Support/Path.h"

namespace hlir::frontend {

// see the header: asserted bounds are indexed by TYPE, so one assertion covers every object of that type the
// harness builds -- the parameter's own pointee and the sub-objects behind its pointer fields alike.
std::string assertKey(const std::string &tag, uint64_t recordSize, uint64_t offset) {
  if (tag.empty()) return "";
  return tag + "#" + std::to_string(recordSize) + "@" + std::to_string(offset);
}
namespace {

bool layoutSane(clang::QualType t);

// Constants are carried as int64 bit patterns; unsigned 64-bit values with the top bit set (e.g. ~(uintptr_t)3) wrap.
int64_t apExt(const llvm::APSInt &v) {
  if (v.getBitWidth() > 64) return static_cast<int64_t>(v.trunc(64).getZExtValue());
  return v.isSigned() ? v.getSExtValue() : static_cast<int64_t>(v.getZExtValue());
}

using namespace clang;

struct V {
  std::string n;  // SSA name including '%'; empty for void
  QualType t;     // for a struct-valued call: n is the pointer to the result object
};
struct LV {
  std::string p;
  QualType t;
  bool direct = false;    // a plain local/param/global object: null/uaf/oob are trivially satisfied
  bool zeroInit = false;  // globals: reads need no uninit check
  bool isConst = false;
  bool bit = false;       // bit-field: p is the first byte, bitSh the bit offset inside it, bitW the width
  unsigned bitSh = 0, bitW = 0;
  // A read-modify-write (`a[i] += x`, `p->n |= b`, `++v`): ONE access that both reads and writes. It must
  // be checked ONCE, as access="rw", not as a read followed by a write. Checking it twice is not merely
  // redundant -- it makes the write UNREPORTABLE: the engine continues a path only where a check passed
  // (TaintDomain::check calls addPc(not(bad))), so once the read check has been asked, "the read was in
  // bounds" is in the path condition and the write check on the SAME address is unsatisfiable by
  // construction. Measured on libvorbis CVE-2018-5146, where `a[i++] += t[j++]` running past the
  // partition was reported as oob_read and the oob_write the CVE is named after could never fire.
  // DESIGN.md Sec.22.470.
  bool rmw = false;
};

struct Blk {
  std::string name, params;
  std::vector<std::string> ops;
  bool done = false;
};

struct Module {
  std::string file;
  std::map<std::string, std::string> declares;  // name -> text
  std::set<std::string> defined;
  std::set<const FunctionDecl *> addrTaken;     // canonical decls whose address is taken somewhere
  std::set<const FunctionDecl *> addrEscaped;   // ... and converted to another type or stored in a union (AddrTakenFinder)
  std::ostringstream funcs;
  std::vector<std::string> errors;
  std::map<std::string, unsigned> strIdx;       // string literal content -> global index
  std::vector<std::string> strs;
  std::vector<const VarDecl *> initQueue;       // globals whose init function must be generated
  std::set<const VarDecl *> initSeen;
  std::vector<FunctionInfo> infos;
  std::set<std::string> failedFns;
  std::map<std::string, std::string> failedWhy;
  // recover mode
  bool recover = false;
  bool wrapSigned = false;
  bool lenientPtrArith = false;                 // LowerOptions::lenientPointerArith
  bool spawnCallbacks = false;                  // LowerOptions::spawnCallbacks
  unsigned spawnCallbacksEmitted = 0;           // LowerResult::spawnCallbacksEmitted
  unsigned containerOfWaived = 0;               // LowerResult::containerOfWaived
  std::string containerOfFirstSite;             // LowerResult::containerOfFirstSite
  bool link = false;                            // LowerOptions::link
  std::vector<std::pair<std::string, std::string>> addrTakenSigs;  // LowerResult::addrTakenFunctions
  std::map<std::string, std::string> addrTakenCTypes;             // LowerResult::addrTakenCTypes
  std::map<std::string, std::set<std::string>> vtableBindings;    // LowerResult::vtableBindings
  std::map<std::string, VtableInstance> vtableInstances;         // LowerResult::vtableInstances
  std::map<std::string, std::string> indirectCallCTypes;          // LowerResult::indirectCallCTypes
  std::set<std::string> dlsymNames;                              // LowerResult::dlsymNames
  std::set<std::string> internalTokens;         // LowerResult::internalTokens
  std::set<std::string> ctorWrappers;           // `__hlir_ctor.<prio>.<name>` already emitted
  std::set<std::string> userDataGetters;       // see LowerOptions::userDataGetters
  std::set<std::string> externals;              // names that stay declarations (see LowerOptions::externalFunctions)
  std::set<std::string> missingHeaders, unknownTypes, unknownIdents;
  struct Diag { std::string file; unsigned line; std::string text; };
  std::vector<Diag> clangErrors;
  struct StubUse { std::string structName, member, type; int rank = 0; };
  std::vector<StubUse> stubUses;                // recover: member accesses on structs without a definition
  // C++ virtual dispatch: polymorphic classes of the translation unit and the dispatchers requested by virtual calls
  std::vector<const CXXRecordDecl *> classes;
  struct VCall { const CXXMethodDecl *md = nullptr; bool isDelete = false; };
  std::map<std::string, VCall> vcalls;          // dispatcher name -> what it dispatches
  std::set<std::string> vcallDone;
  // `dynamic_cast`: target == nullptr means `dynamic_cast<void*>` (the complete object). isRef: on no match, trap
  // (simplified `std::bad_cast`) instead of returning null, since a reference form cannot yield null.
  struct DynCast { const CXXRecordDecl *src = nullptr; const CXXRecordDecl *target = nullptr; bool isRef = false; };
  std::map<std::string, DynCast> dynCasts;
  std::set<std::string> dynCastDone;
  // `typeid(polymorphic glvalue)`: which class's vptr marker to look up and (on no match among `classes`, meaning
  // the object's true dynamic type is outside this module's closed-world view) fall back to.
  std::map<std::string, const CXXRecordDecl *> typeIds;
  std::set<std::string> typeIdDone;
  std::vector<const FunctionDecl *> work;       // functions to lower: main-file ones first, then bodies reached from calls (header inlines)
  std::vector<const FunctionDecl *> baseWork;   // constructors/destructors of classes with virtual bases whose base-object variant is needed
  // static-local-variable naming (globalName()): two distinct static locals in the same function, in different
  // lexical scopes, can share a spelling (e.g. two `if` branches each declaring their own `static const char*
  // kRepNames[]`) -- legal C++, but `fnName(fn) + "." + name` alone can't tell them apart. staticLocalNames
  // memoizes the name already assigned to a given VarDecl (so every reference to the same variable agrees);
  // staticLocalNameOwner records which VarDecl first claimed a given base name, so only a genuine second (or
  // later) distinct variable with the same spelling gets a disambiguating suffix -- the overwhelmingly common
  // non-colliding case keeps its plain `fn.name` symbol unchanged.
  std::map<const VarDecl *, std::string> staticLocalNames;
  std::map<std::string, const VarDecl *> staticLocalNameOwner;
  std::set<std::string> fieldUses;              // --link only: LowerResult::fieldUses
  std::set<std::string> fieldNullTests;         // --link only: LowerResult::fieldNullTests
  std::map<std::string, AssertedBound> fieldAsserts;  // --link only: LowerResult::fieldAsserts
  // single-header-library carve-out (docs/DESIGN.md §22.110 + its narrower follow-up): macro names the MAIN file
  // itself `#define`s (never a header, never a command-line `-D` -- both land outside the main file), and the
  // source ranges of "simple" `#ifdef X` / `#ifndef X` / `#if defined(X)` regions (single macro, no `&&`/`||`,
  // first branch only). See MainMacroIfdefs (collects these) and FnCollector (consumes them).
  std::set<std::string> mainFileDefinedMacros;
  struct IfdefRegion { std::string macro; FileID file; unsigned beginOffset = 0, endOffset = 0; };
  std::vector<IfdefRegion> simpleIfdefRegions;
};

std::string attrList(std::initializer_list<std::string> xs) {
  std::string s;
  for (auto &x : xs)
    if (!x.empty()) s += (s.empty() ? "" : ", ") + x;
  return s.empty() ? "" : " {" + s + "}";
}

// ------------------------------------------------------------------------------------------------ types / signatures
// "" when the type has no core representation.
std::string coreTy(ASTContext &ctx, QualType t) {
  t = t.getCanonicalType().getUnqualifiedType();
  // `_Atomic(T)` has T's representation and T's size. The engine explores ONE thread, so an atomic
  // object is just an object -- carrying it as T is exact here, and refusing it is not conservative,
  // it just stops the function from being lowered at all. Redis's networking.c reads
  // `server.unixtime` (a `redisAtomic time_t`) inside processInlineBuffer, so the whole RESP inline
  // parser became an opaque extern and a 300s scan was vacuous (DESIGN.md Sec.22.452).
  if (const auto *at = t->getAs<AtomicType>()) t = at->getValueType().getCanonicalType().getUnqualifiedType();
  if (t->isVoidType()) return "void";
  if (t->isBooleanType()) return "bool";
  if (t->isPointerType() || t->isArrayType() || t->isReferenceType() || t->isNullPtrType()) return "ptr";
  if (t->isEnumeralType() && t->isIncompleteType() && !t->containsErrors()) return "i32";  // a forward-declared enum (GNU extension, e.g. `enum ctxsw_addr_type;`): int-sized like GCC/Clang use it
  if (t->containsErrors() || t->isDependentType() || t->isIncompleteType()) return "";  // e.g. an enum whose definition is in a missing header
  if (t->isIntegerType() || t->isEnumeralType()) return "i" + std::to_string(ctx.getTypeSize(t));
  if (t->isRealFloatingType()) {  // floating point values are carried as their IEEE bit patterns (core.fop computes on them)
    const llvm::fltSemantics &fs = ctx.getFloatTypeSemantics(t);
    if (&fs == &llvm::APFloat::IEEEsingle() || &fs == &llvm::APFloat::IEEEdouble() || &fs == &llvm::APFloat::x87DoubleExtended())
      return "i" + std::to_string(ctx.getTypeSize(t));
  }
  return "";
}
bool isFlt(QualType t) { return t.getCanonicalType()->isRealFloatingType(); }
// float width of the format: 32, 64, 80 (x87 long double, kept in an i128)
unsigned fltWidth(ASTContext &ctx, QualType t) {
  const llvm::fltSemantics &fs = ctx.getFloatTypeSemantics(t.getCanonicalType());
  return &fs == &llvm::APFloat::IEEEsingle() ? 32 : &fs == &llvm::APFloat::IEEEdouble() ? 64 : 80;
}
bool isRecordTy(QualType t) { return t.getCanonicalType()->isRecordType(); }
// type of a parameter / return slot in the core signature (struct values travel as pointers)
std::string slotTy(ASTContext &ctx, QualType t) { return isRecordTy(t) ? "ptr" : coreTy(ctx, t); }

// ---- C++: symbol names and the implicit object parameter
bool isCxxCtx(const ASTContext &ctx) { return ctx.getLangOpts().CPlusPlus; }
bool hasThis(const FunctionDecl *fd) {
  auto *md = dyn_cast<CXXMethodDecl>(fd);
  return md && md->isInstance();
}
// The core symbol of a function: its own name for C and `extern "C"`, the Itanium mangled name for C++ entities (overloads,
// methods, templates, namespaces get distinct symbols).
std::string fnName(const FunctionDecl *fd) {
  ASTContext &ctx = fd->getASTContext();
  if (!isCxxCtx(ctx) || fd->isExternC() || fd->isMain()) return fd->getName().str();
  static std::map<const ASTContext *, std::unique_ptr<MangleContext>> mcs;
  auto &mc = mcs[&ctx];
  if (!mc) mc.reset(ItaniumMangleContext::create(ctx, ctx.getDiagnostics()));
  std::string out;
  llvm::raw_string_ostream os(out);
  if (auto *cd = dyn_cast<CXXConstructorDecl>(fd)) mc->mangleName(GlobalDecl(cd, Ctor_Complete), os);
  else if (auto *dd = dyn_cast<CXXDestructorDecl>(fd)) mc->mangleName(GlobalDecl(dd, Dtor_Complete), os);
  else mc->mangleName(GlobalDecl(fd), os);
  return os.str();
}
// readable name for reports: `ns::Class::method`, constructors and destructors included
std::string fnDisplay(const FunctionDecl *fd) {
  if (!isCxxCtx(fd->getASTContext())) return fd->getName().str();
  return fd->getQualifiedNameAsString();
}
// the marker object that stands for "the vtable of class `rd` at subobject offset `off`": the constructor stores its address in
// the vptr slot, a virtual call compares the slot with the markers of the classes it can reach
std::string vtblName(const CXXRecordDecl *rd, uint64_t off) {
  ASTContext &ctx = rd->getASTContext();
  static std::map<const ASTContext *, std::unique_ptr<MangleContext>> mcs;
  auto &mc = mcs[&ctx];
  if (!mc) mc.reset(ItaniumMangleContext::create(ctx, ctx.getDiagnostics()));
  std::string out;
  llvm::raw_string_ostream os(out);
  static_cast<ItaniumMangleContext *>(mc.get())->mangleCXXVTable(rd, os);
  return "__hlir_vtbl." + os.str() + "." + std::to_string(off);
}
// ---- C++ virtual bases. An object of a class with virtual bases has a vptr slot whose marker carries a table of the offsets of
// those bases (inside the complete object, relative to the subobject): methods read it, constructors and destructors get the
// addresses as hidden parameters (the "base object" variants C2/D2, called for subobjects) or compute them (C1/D1).
bool hasVBases(const CXXRecordDecl *rd) { return rd && rd->hasDefinition() && rd->getNumVBases() > 0; }
// the virtual bases of `c` in table order: those of its primary base first (so that a derived class's table extends its primary
// base's, as in the Itanium ABI), then the others in declaration order
void vbaseTable(ASTContext &ctx, const CXXRecordDecl *c, std::vector<const CXXRecordDecl *> &out) {
  if (!hasVBases(c) || !layoutSane(ctx.getRecordType(c))) return;
  if (const CXXRecordDecl *pb = ctx.getASTRecordLayout(c).getPrimaryBase()) vbaseTable(ctx, pb, out);
  for (auto &v : c->vbases()) {
    const CXXRecordDecl *vd = v.getType()->getAsCXXRecordDecl()->getCanonicalDecl();
    if (std::find(out.begin(), out.end(), vd) == out.end()) out.push_back(vd);
  }
}
// every subobject of a complete object of class `d`: (class, offset, reached through a virtual base)
void forEachSubobject(ASTContext &ctx, const CXXRecordDecl *d, const std::function<void(const CXXRecordDecl *, uint64_t, bool)> &cb) {
  if (!d->hasDefinition() || !layoutSane(ctx.getRecordType(d))) return;
  std::function<void(const CXXRecordDecl *, uint64_t, bool)> walk = [&](const CXXRecordDecl *rd, uint64_t base, bool viaV) {
    cb(rd, base, viaV);
    if (!rd->hasDefinition() || !layoutSane(ctx.getRecordType(rd))) return;
    const ASTRecordLayout &L = ctx.getASTRecordLayout(rd);
    for (auto &b : rd->bases()) {
      if (b.isVirtual()) continue;
      const CXXRecordDecl *brd = b.getType()->getAsCXXRecordDecl();
      walk(brd, base + L.getBaseClassOffset(brd).getQuantity(), viaV);
    }
  };
  walk(d, 0, false);
  if (hasVBases(d)) {
    const ASTRecordLayout &L = ctx.getASTRecordLayout(d);
    for (auto &v : d->vbases()) {
      const CXXRecordDecl *vd = v.getType()->getAsCXXRecordDecl();
      walk(vd, L.getVBaseClassOffset(vd).getQuantity(), true);
    }
  }
}
// bytes of the marker object (the vptr target) of `d` at subobject offset `off`: 8 reserved + the offset table of the class
// (the longest table of the classes sharing that offset)
uint64_t markerBytes(ASTContext &ctx, const CXXRecordDecl *d, uint64_t off) {
  size_t n = 0;
  forEachSubobject(ctx, d, [&](const CXXRecordDecl *c, uint64_t o, bool) {
    if (o != off || !c->isDynamicClass()) return;
    std::vector<const CXXRecordDecl *> t;
    vbaseTable(ctx, c, t);
    n = std::max(n, t.size());
  });
  return 8 + 8 * n;
}
// the global marker (name, byte size) that identifies `t` for RTTI purposes: `typeid`'s result and the comparisons
// `dynamic_cast`'s dispatcher makes against an object's vptr both key off this. A dynamic class (one with its own
// vtable) reuses its existing primary vtable marker (`vtblName(rd, 0)`, the exact value already stored in every
// such object's vptr slot by its constructor and compared at every virtual call through it) rather than inventing
// a second identity for the same class. Anything else (a non-polymorphic class, a scalar type, `typeid(SomeType)`
// on a named type) gets its own lightweight marker keyed by the type's real Itanium RTTI mangling (`_ZTI...`), so
// identical types compare equal wherever they are mentioned, including across `--link`ed translation units, and
// the name doubles as a minimal honest `typeid(...).name()` substitute even though `.name()` itself is not modelled.
std::pair<std::string, uint64_t> typeInfoMarker(ASTContext &ctx, QualType t) {
  t = t.getCanonicalType();
  if (const CXXRecordDecl *rd = t->getAsCXXRecordDecl()) {
    rd = rd->getDefinition();
    if (rd && rd->isDynamicClass()) return {vtblName(rd, 0), markerBytes(ctx, rd, 0)};
  }
  static std::map<const ASTContext *, std::unique_ptr<MangleContext>> mcs;
  auto &mc = mcs[&ctx];
  if (!mc) mc.reset(ItaniumMangleContext::create(ctx, ctx.getDiagnostics()));
  std::string out;
  llvm::raw_string_ostream os(out);
  static_cast<ItaniumMangleContext *>(mc.get())->mangleCXXRTTI(t, os);
  return {"__hlir_typeinfo." + os.str(), 8};
}
std::string baseVariantName(const FunctionDecl *fd) { return fnName(fd) + ".base"; }
// does the constructor/destructor have a separate base-object variant (class with virtual bases)?
bool hasBaseVariant(const FunctionDecl *fd) {
  auto *m = dyn_cast<CXXMethodDecl>(fd);
  return m && (isa<CXXConstructorDecl>(m) || isa<CXXDestructorDecl>(m)) && hasVBases(m->getParent());
}

// Variadic functions of the project (not declared in a system header) take one more parameter: a pointer to the 8-byte slots the
// caller packed the variable arguments into (NULL when there are none). `va_start` reads it, `va_arg` walks the slots. Library
// variadics (printf, ...) keep their plain signature: they are external, their extra arguments are evaluated and dropped.
// A variadic function gets an extra trailing "vararg block" parameter -- unless it is a system one, which the
// library models describe generically without a block (`core.func @snprintf(ptr, i64, ptr)`).
//
// Asking only `getFirstDecl()` made that decision TRANSLATION-UNIT-DEPENDENT, and with `--link` two TUs of the
// same program then disagreed about the same function's arity: the parser reported "redefinition of function
// @snprintf", the whole module failed to parse, and the scan produced `blocks=0` -- no entries analysed, no
// finding, no diagnosis. Six of the 55 tcpdump differential targets were lost to this, every one of them a
// file that passes real varargs to `snprintf` while another file in the same link set does not
// (DESIGN.md §22.422).
//
// Two things settle it, and NEITHER depends on which TU is being lowered: a declaration in a system header,
// or clang knowing the name as a builtin. The builtin half is what the tcpdump case needed:
// `print-isoclns.c` does not include <stdio.h> at all, so its only `snprintf` declaration is the implicit
// builtin one, whose location is not in any header -- while `print-ascii.c`, in the same link set, includes
// <stdio.h> and got the system declaration. One file's call then carried a vararg block and the other's did
// not. Asking every redeclaration instead of only `getFirstDecl()` is also kept: include ORDER must not
// decide a signature either.
bool passesVaBlock(const FunctionDecl *fd) {
  if (!fd->isVariadic()) return false;
  // The printf-family writers whose output the engine computes in closed form when the format string and the
  // arguments are all concrete (DESIGN.md §22.439). They can only be folded if their variable arguments actually
  // reach the interpreter, so unlike the rest of the C library they DO carry a vararg block. The test is the
  // NAME and nothing else: §22.422 is what happens when this decision depends on which translation unit is being
  // lowered -- two TUs of one program disagreed about @snprintf's arity, the module failed to parse, and the scan
  // reported no entries at all.
  if (const IdentifierInfo *ii = fd->getIdentifier()) {
    llvm::StringRef n = ii->getName();
    if ((n == "snprintf" || n == "sprintf") && !hasThis(fd)) return true;
  }
  if (fd->getBuiltinID() != 0) return false;
  const SourceManager &sm = fd->getASTContext().getSourceManager();
  for (const Decl *d : fd->redecls())
    if (sm.isInSystemHeader(d->getLocation())) return false;
  return true;
}
// parameter types of the core signature, the object parameter first
std::vector<QualType> sigParams(const FunctionDecl *fd) {
  std::vector<QualType> ps;
  if (hasThis(fd)) ps.push_back(cast<CXXMethodDecl>(fd)->getThisType());
  for (auto *p : fd->parameters()) ps.push_back(p->getType());
  if (passesVaBlock(fd)) ps.push_back(fd->getASTContext().VoidPtrTy);
  return ps;
}

// "(ptr, i32) -> i32"; a struct result becomes a hidden first ptr parameter and a void result
std::string sigText(ASTContext &ctx, QualType ret, const std::vector<QualType> &params, bool &ok) {
  std::string s = "(";
  bool first = true;
  std::string rt = slotTy(ctx, ret);
  if (rt.empty()) ok = false;
  if (isRecordTy(ret)) { s += "ptr"; first = false; rt = "void"; }
  for (auto &p : params) {
    std::string t = slotTy(ctx, p);
    if (t.empty() || t == "void") ok = false;
    s += (first ? "" : ", ") + t;
    first = false;
  }
  return s + ") -> " + rt;
}
std::string sigOfDecl(ASTContext &ctx, const FunctionDecl *fd, bool &ok) { return sigText(ctx, fd->getReturnType(), sigParams(fd), ok); }

// The C type key of a function type (hlir/support/IndirectCall.h): per position, the struct/union a pointer leads to, `_`
// for anything else. "" for a function without a prototype.
static std::string cTypeElem(QualType t) {
  std::string stars;
  t = t.getCanonicalType().getUnqualifiedType();
  for (;;) {
    if (auto *pt = t->getAs<PointerType>()) t = pt->getPointeeType().getCanonicalType().getUnqualifiedType();
    else if (auto *at = dyn_cast<ArrayType>(t.getTypePtr())) t = at->getElementType().getCanonicalType().getUnqualifiedType();
    else break;
    stars += '*';
  }
  if (auto *rt = t->getAs<RecordType>()) {
    const RecordDecl *rd = rt->getDecl();
    if (!rd->getName().empty()) return stars + (rd->isUnion() ? "u:" : "s:") + rd->getName().str();
  }
  return "_";
}
std::string cTypeKey(QualType t) {
  t = t.getCanonicalType();
  if (auto *pt = t->getAs<PointerType>()) t = pt->getPointeeType().getCanonicalType();
  auto *fp = t->getAs<FunctionProtoType>();
  if (!fp) return "";
  std::string k = cTypeElem(fp->getReturnType()) + "(";
  bool first = true;
  for (QualType p : fp->param_types()) { k += (first ? "" : ",") + cTypeElem(p); first = false; }
  return k + ")";
}

bool isZeroInit(ASTContext &ctx, const Expr *e) {
  e = e->IgnoreParenImpCasts();
  if (auto *il = dyn_cast<InitListExpr>(e)) {
    for (unsigned i = 0; i < il->getNumInits(); ++i)
      if (il->getInit(i) && !isZeroInit(ctx, il->getInit(i))) return false;
    return true;
  }
  if (isa<ImplicitValueInitExpr>(e)) return true;
  Expr::EvalResult r;
  if (e->getType()->isIntegerType() && e->EvaluateAsInt(r, ctx)) return r.Val.getInt() == 0;
  if (e->isNullPointerConstant(ctx, Expr::NPC_ValueDependentIsNotNull) != Expr::NPCK_NotNull) return true;
  return false;
}
bool needsInit(ASTContext &ctx, const VarDecl *vd) {
  const VarDecl *def = vd->getDefinition();
  if (def && def->getInit() && def->getType()->isReferenceType()) return true;  // the reference must be bound
  return def && def->getInit() && !isZeroInit(ctx, def->getInit());
}
std::string globalName(Module &mod, const VarDecl *vd) {
  if (vd->isStaticLocal())
    if (auto *fn = dyn_cast_or_null<FunctionDecl>(vd->getParentFunctionOrMethod())) {
      const VarDecl *canon = vd->getCanonicalDecl();
      auto cached = mod.staticLocalNames.find(canon);
      if (cached != mod.staticLocalNames.end()) return cached->second;
      std::string base = fnName(fn) + "." + vd->getName().str();
      std::string name = base;
      auto owner = mod.staticLocalNameOwner.find(base);
      if (owner == mod.staticLocalNameOwner.end()) {
        mod.staticLocalNameOwner.emplace(base, canon);  // first (and, usually, only) static local with this spelling
      } else if (owner->second != canon) {
        // a different static local in the same function already claimed this spelling: disambiguate with the
        // declaration's line number (stable across rebuilds, unlike pointer identity, and still points a reader
        // at roughly where this one lives); fall back to an ordinal suffix in the vanishingly rare case two
        // colliding declarations also share a line (e.g. macro-expanded).
        unsigned line = vd->getASTContext().getSourceManager().getSpellingLineNumber(vd->getLocation());
        name = base + ".L" + std::to_string(line);
        for (unsigned n = 2; mod.staticLocalNameOwner.count(name) && mod.staticLocalNameOwner[name] != canon; ++n)
          name = base + ".L" + std::to_string(line) + "." + std::to_string(n);
        mod.staticLocalNameOwner.emplace(name, canon);
      }
      mod.staticLocalNames.emplace(canon, name);
      return name;
    }
  if (isCxxCtx(vd->getASTContext()) && !vd->isExternC()) {  // namespaces and classes qualify the name: `ns::x` -> `ns.x`
    std::string q = vd->getQualifiedNameAsString(), out;
    for (size_t i = 0; i < q.size(); ++i) {
      if (q.compare(i, 2, "::") == 0) { out += '.'; ++i; }
      else out += (isalnum(static_cast<unsigned char>(q[i])) || q[i] == '_' || q[i] == '.') ? q[i] : '_';
    }
    return out;
  }
  return vd->getName().str();
}

// ------------------------------------------------------------------------------------------------ function lowering
// does the body contain a goto? (jumping past or back over declarations makes the end-of-scope lifetime markers not dominated)
// Constructs after which a slot's `alloca` can no longer be assumed to dominate every later use of it,
// so the alloca is hoisted to the entry block and no lifetime_end is emitted (see newSlot).
//
// `goto` was the original member. A SWITCH WHOSE BODY DECLARES A VARIABLE is the same hazard without a
// goto anywhere: the switch's own jump table can enter a later case directly, past the declaration, and
// the scope that owns the slot is then popped in whichever block the last case left open. Measured on
// libexif's exif_entry_get_value, where `unsigned short *utf16` is declared inside the XP_* case block
// and the verifier rejected `core.lifetime_end %v2912` in `^default`:
//     definition of %v2912 does not dominate this use [@exif_entry_get_value, ^default59, core.lifetime_end]
// The cost of getting this wrong is not a bad diagnostic: hlir-scan DEMOTES a function whose body does
// not verify to an opaque external, so the function silently drops out of the analysis and the scan
// still reports a verdict. DESIGN.md Sec.22.469.
class GotoFinder : public RecursiveASTVisitor<GotoFinder> {
 public:
  bool found = false;
  bool VisitGotoStmt(GotoStmt *) { found = true; return false; }
  bool VisitIndirectGotoStmt(IndirectGotoStmt *) { found = true; return false; }
  bool VisitSwitchStmt(SwitchStmt *sw) {
    if (sw->getBody() && declaresAVariable(sw->getBody())) { found = true; return false; }
    return true;
  }

 private:
  // Any VarDecl with automatic storage anywhere inside the switch body. Static locals are globals and
  // need no slot, so they do not create the hazard.
  static bool declaresAVariable(const Stmt *s) {
    if (!s) return false;
    if (const auto *ds = dyn_cast<DeclStmt>(s))
      for (const Decl *d : ds->decls())
        if (const auto *vd = dyn_cast<VarDecl>(d))
          if (!vd->hasGlobalStorage()) return true;
    for (const Stmt *c : s->children())
      if (declaresAVariable(c)) return true;
    return false;
  }
};

class FnGen {
 public:
  FnGen(ASTContext &ctx, Module &m) : ctx_(ctx), sm_(ctx.getSourceManager()), mod_(m) {}

  void run(const FunctionDecl *fd, bool baseVariant = false) {
    fd_ = fd;
    base_ = baseVariant;
    if (fd->getBody()) {
      GotoFinder gf;
      gf.TraverseStmt(const_cast<Stmt *>(fd->getBody()));
      noLifetimes_ = gf.found;  // no lifetime_end markers in functions with goto: a jump over a declaration does not dominate the scope end
    }
    std::string params;
    std::set<std::string> usedParamNames{"this", "sret", "__va"};
    bool ok = true;
    std::string sig = sigOfDecl(ctx_, fd, ok);
    if (!ok) failDecl(fd, "function signature of '" + fd->getQualifiedNameAsString() + "'");
    if (isRecordTy(fd->getReturnType())) {
      sret_ = "%sret";
      params = "%sret: ptr";
      namedUsed_.insert(sret_);
    }
    if (hasThis(fd)) {
      this_ = "%this";
      namedUsed_.insert(this_);
      params += (params.empty() ? "" : ", ") + std::string("%this: ptr");
      if (base_) {  // the base-object variant gets the addresses of the class's virtual bases
        std::vector<const CXXRecordDecl *> vbs;
        for (auto &v : dyn_cast<CXXMethodDecl>(fd)->getParent()->vbases()) vbs.push_back(v.getType()->getAsCXXRecordDecl()->getCanonicalDecl());
        std::string extra;
        for (size_t i = 0; i < vbs.size(); ++i) {
          params += ", %vb" + std::to_string(i) + ": ptr";
          extra += ", ptr";
          vbaseLocal_[vbs[i]] = "%vb" + std::to_string(i);
          namedUsed_.insert(vbaseLocal_[vbs[i]]);
        }
        sig.insert(sig.find('(') + 4, extra);  // after the leading "ptr" of the object parameter
      }
      if (auto *crd = dyn_cast<CXXMethodDecl>(fd)->getParent(); crd->isLambda() && crd->getLambdaCallOperator() == fd) crd->getCaptureFields(capFields_, thisCap_);
    }
    for (unsigned i = 0; i < fd->getNumParams(); ++i) {
      const ParmVarDecl *pd = fd->getParamDecl(i);
      std::string nm = pd->getName().empty() ? "arg" + std::to_string(i) : pd->getName().str();
      if (!usedParamNames.insert(nm).second) nm += "_" + std::to_string(i);  // the elements of a parameter pack share one name
      pnames_[pd] = "%" + nm;
      namedUsed_.insert(pnames_[pd]);
      params += (params.empty() ? "" : ", ") + ("%" + nm + ": " + slotTy(ctx_, pd->getType()));
    }
    if (passesVaBlock(fd)) {
      va_ = "%__va";
      namedUsed_.insert(va_);
      params += (params.empty() ? "" : ", ") + std::string("%__va: ptr");
    }
    curBlock_ = newBlock("entry");
    blocks_[curBlock_].params = params;
    loc_ = fd->getLocation();
    pushScope();
    if (!base_ && hasBaseVariant(fd)) {  // complete-object variant: the virtual bases are where the complete layout puts them
      const CXXRecordDecl *crd = cast<CXXMethodDecl>(fd)->getParent();
      if (!layoutSane(ctx_.getRecordType(crd))) failDecl(fd, "class with virtual bases and an invalid layout");
      for (auto &v : crd->vbases()) {
        const CXXRecordDecl *vd = v.getType()->getAsCXXRecordDecl();
        vbaseLocal_[vd->getCanonicalDecl()] = inObj(this_, ctx_.getASTRecordLayout(crd).getVBaseClassOffset(vd).getQuantity());
      }
    }
    for (unsigned i = 0; i < fd->getNumParams(); ++i) {
      const ParmVarDecl *pd = fd->getParamDecl(i);
      if (isRecordTy(pd->getType())) {  // the caller made the copy; the pointer is the parameter object
        locals_[pd] = pnames_[pd];
        continue;
      }
      if (pd->getType()->isReferenceType()) {  // the slot holds the address of the referenced object
        std::string slot = newSlot(ctx_.VoidPtrTy, pd->getName().str());
        locals_[pd] = slot;
        store({slot, ctx_.VoidPtrTy, true, false, false}, {pnames_[pd], ctx_.VoidPtrTy});
        continue;
      }
      std::string slot = newSlot(pd->getType(), pd->getName().str());
      locals_[pd] = slot;
      store({slot, pd->getType(), true, false, false}, {pnames_[pd], pd->getType()});
    }
    auto *dd = dyn_cast<CXXDestructorDecl>(fd);
    if (dd) retBlock_ = newBlock("dtor_epilogue");
    if (auto *cd = dyn_cast<CXXConstructorDecl>(fd)) ctorPrologue(cd);
    if (dd && dd->getParent()->isDynamicClass()) initVptr(this_, dd->getParent());  // virtual calls in a destructor see the class being destroyed
    if (fd->getBody()) stmt(fd->getBody());
    if (!blocks_[curBlock_].done) {
      unwindTo(0);
      if (dd) term("core.br " + bname(retBlock_));
      else if (fd->getReturnType()->isVoidType() || !sret_.empty()) term("core.return");
      else {
        // flowing off the end of a non-void function is undefined only if the caller uses the value (C11 6.9.1p12), and
        // functions ending in a noreturn call or an endless loop are common: return an arbitrary value. The name is
        // qualified by the function (see the inline-asm nondet above for why a bare literal collides under --link:
        // every function needing this shares the same literal name here, so without qualification any two of them
        // with different-width return types would alias the same SMT variable under --link).
        std::string v = def("core.nondet {name=\"" + fnName(fd) + ".falloff\"} : " + ty(fd->getReturnType()), "n");
        term("core.return " + v);
      }
    }
    if (dd) {
      setBlock(retBlock_);
      dtorEpilogue(dd);
      term("core.return");
    }
    popScope(false);
    print("@" + (base_ ? baseVariantName(fd) : fnName(fd)), sig);
  }

  // ---- constructors and destructors
  std::string fieldAddr(const std::string &obj, const FieldDecl *f) {
    if (!layoutSane(ctx_.getRecordType(f->getParent()))) failDecl(f, "member of a record whose layout is invalid or incomplete");
    uint64_t bo = ctx_.getASTRecordLayout(f->getParent()).getFieldOffset(f->getFieldIndex());
    return inObj(obj, bo / 8);
  }
  std::string baseAddr(const std::string &obj, const CXXRecordDecl *derived, const CXXRecordDecl *base) {
    uint64_t off = ctx_.getASTRecordLayout(derived).getBaseClassOffset(base).getQuantity();
    return inObj(obj, off);
  }
  void ctorPrologue(const CXXConstructorDecl *cd) {
    const CXXRecordDecl *rd = cd->getParent();
    bool vptrDone = !rd->isDynamicClass();
    auto initVptrOnce = [&] { if (!vptrDone) { vptrDone = true; initVptr(this_, rd, !base_); } };
    for (const CXXCtorInitializer *ci : cd->inits()) {
      at(ci->getInit());
      if (ci->isBaseInitializer()) {
        const CXXRecordDecl *brd = ci->getBaseClass()->getAsCXXRecordDecl();
        if (ci->isBaseVirtual() && base_) continue;  // the complete-object constructor builds the virtual bases
        std::string b = ci->isBaseVirtual() ? vbaseLocal_.at(brd->getCanonicalDecl()) : baseAddr(this_, rd, brd);
        initObject({b, ctx_.getRecordType(brd), true, false, false}, ci->getInit());
      } else if (ci->isDelegatingInitializer()) {
        initObject({this_, ctx_.getRecordType(rd), true, false, false}, ci->getInit());
        vptrDone = true;  // the delegated-to constructor set it
      } else if (ci->isMemberInitializer() || ci->isIndirectMemberInitializer()) {
        initVptrOnce();
        // a member, or a member of an anonymous struct/union (a chain of fields): the bit offset of the target inside the object
        uint64_t bo = 0;
        const FieldDecl *f = nullptr;
        if (ci->isMemberInitializer()) f = ci->getMember();
        else
          for (auto *nd : ci->getIndirectMember()->chain()) {
            f = cast<FieldDecl>(nd);
            if (!layoutSane(ctx_.getRecordType(f->getParent()))) failDecl(cd, "member of a record whose layout is invalid or incomplete");
            bo += ctx_.getASTRecordLayout(f->getParent()).getFieldOffset(f->getFieldIndex());
          }
        if (ci->isMemberInitializer()) {
          if (!layoutSane(ctx_.getRecordType(f->getParent()))) failDecl(cd, "member of a record whose layout is invalid or incomplete");
          bo = ctx_.getASTRecordLayout(f->getParent()).getFieldOffset(f->getFieldIndex());
        }
        LV fl{inObj(this_, bo / 8), f->getType(), true, false, false};
        if (f->isBitField()) {
          fl.bit = true;
          fl.bitSh = static_cast<unsigned>(bo % 8);
          fl.bitW = f->getBitWidthValue(ctx_);
        }
        initMember(fl, ci->getInit());
      } else failDecl(cd, "constructor initializer");
      flushTemps();
    }
    initVptrOnce();
  }
  // a member (or base) initializer: references bind, everything else is an ordinary initialization
  void initMember(const LV &lv, const Expr *init) {
    if (lv.t->isReferenceType()) {
      LV target = genL(init);
      store({lv.p, ctx_.VoidPtrTy, true, false, false}, {target.p, ctx_.VoidPtrTy});
      return;
    }
    initObject(lv, init);
  }
  void dtorEpilogue(const CXXDestructorDecl *dd) {
    const CXXRecordDecl *rd = dd->getParent();
    std::vector<const FieldDecl *> fs(rd->field_begin(), rd->field_end());
    for (auto it = fs.rbegin(); it != fs.rend(); ++it) {
      QualType ft = (*it)->getType();
      if (needsDtor(ft)) runDtors({cleanupOf(fieldAddr(this_, *it), ft)});
    }
    std::vector<const CXXBaseSpecifier *> bs;
    for (auto &b : rd->bases()) bs.push_back(&b);
    for (auto it = bs.rbegin(); it != bs.rend(); ++it) {
      if ((*it)->isVirtual()) continue;
      const CXXRecordDecl *brd = (*it)->getType()->getAsCXXRecordDecl();
      emitDtor(baseAddr(this_, rd, brd), brd, true);
    }
    if (!base_ && hasVBases(rd)) {  // the complete-object destructor also destroys the virtual bases, last constructed first
      std::vector<const CXXRecordDecl *> vbs;
      for (auto &v : rd->vbases()) vbs.push_back(v.getType()->getAsCXXRecordDecl());
      for (auto it = vbs.rbegin(); it != vbs.rend(); ++it) emitDtor(vbaseLocal_.at((*it)->getCanonicalDecl()), *it, true);
    }
  }
  // initialise the vptr slots of the subobjects of `rd` that have one (a primary base shares its derived class's slot), and the
  // virtual-base offset tables of their markers. `withVirtual`=false (a base-object constructor): the virtual bases' own slots
  // belong to the complete object and are left alone.
  void initVptr(const std::string &obj, const CXXRecordDecl *rd, bool withVirtual = true) {
    if (!rd->hasDefinition() || !rd->isDynamicClass()) return;
    if (!layoutSane(ctx_.getRecordType(rd))) failDecl(rd, "polymorphic class with an invalid layout");
    std::map<uint64_t, const CXXRecordDecl *> slots;  // offset -> the class at that offset with the longest virtual-base table
    std::map<uint64_t, size_t> tableLen;
    forEachSubobject(ctx_, rd, [&](const CXXRecordDecl *c, uint64_t off, bool viaV) {
      if (!c->isDynamicClass() || (viaV && !withVirtual)) return;
      std::vector<const CXXRecordDecl *> t;
      vbaseTable(ctx_, c, t);
      if (!slots.count(off) || t.size() > tableLen[off]) { slots[off] = c; tableLen[off] = t.size(); }
    });
    const ASTRecordLayout &L = ctx_.getASTRecordLayout(rd);
    for (auto &kv : slots) {
      uint64_t o = kv.first;
      std::string slot = inObj(obj, o);
      std::string m = def("core.global_addr @" + vtblName(rd, o) + " {size=" + std::to_string(markerBytes(ctx_, rd, o)) + "} : ptr", "vt");
      emit("core.store " + m + ", " + slot + " {waived=\"object known\"}");
      std::vector<const CXXRecordDecl *> t;
      vbaseTable(ctx_, kv.second, t);
      for (size_t i = 0; i < t.size(); ++i) {  // where each virtual base of this subobject is, relative to the subobject
        int64_t rel = static_cast<int64_t>(L.getVBaseClassOffset(t[i]).getQuantity()) - static_cast<int64_t>(o);
        emit("core.store " + c64(rel) + ", " + inObj(m, 8 + 8 * i) + " {waived=\"object known\"}");
      }
    }
  }
  // address of virtual base `v` of the object that `p` points to, of static class `c`
  std::string vbaseAddr(const std::string &p, const CXXRecordDecl *c, const CXXRecordDecl *v) {
    v = v->getCanonicalDecl();
    if (p == this_ && !this_.empty()) {
      auto it = vbaseLocal_.find(v);  // inside a constructor/destructor of the object's own class
      if (it != vbaseLocal_.end() && fd_ && isa<CXXMethodDecl>(fd_) && cast<CXXMethodDecl>(fd_)->getParent()->getCanonicalDecl() == c->getCanonicalDecl()) return it->second;
    }
    std::vector<const CXXRecordDecl *> t;
    vbaseTable(ctx_, c, t);
    size_t idx = std::find(t.begin(), t.end(), v) - t.begin();
    if (idx == t.size()) fail(nullptr, "virtual base not in the table of its class");
    std::string vp = def("core.load " + p + " {waived=\"object known\"} : ptr", "vp");
    std::string cell = inObj(vp, 8 + 8 * idx);
    std::string off = def("core.load " + cell + " {waived=\"object known\"} : i64", "vo");
    return def("core.ptr_add " + p + ", " + off + " {waived=\"in-bounds by construction\"} : ptr", "vb");
  }

  // `@__hlir_init.G`: fills a global once (flag-guarded). Also reaches the globals/strings its initializer points to.
  void runGlobalInit(const VarDecl *vd) {
    std::string g = globalName(mod_, vd);
    if (!vd->isExternallyVisible()) markInternal(g);
    curBlock_ = newBlock("entry");
    loc_ = vd->getLocation();
    pushScope();
    std::string flag = def("core.global_addr @" + g + ".__init {size=1} : ptr", "g");
    std::string one = def("core.const 1 : i8", "c");
    std::string cur = def("core.load " + flag + " {waived=\"object known\"} : i8", "l");
    std::string zero = def("core.const 0 : i8", "c");
    std::string isz = def("core.icmp eq " + cur + ", " + zero + " : bool");
    size_t doit = newBlock("do"), done = newBlock("done");
    term("core.cond_br " + isz + ", " + bname(doit) + ", " + bname(done));
    setBlock(doit);
    emit("core.store " + one + ", " + flag + " {waived=\"object known\"}");
    const VarDecl *d = vd->getDefinition();
    LV lv;
    lv.t = d->getType();
    lv.direct = true;
    bool isRef = lv.t->isReferenceType();
    lv.p = def("core.global_addr @" + g + " {size=" + std::to_string(isRef ? 8 : sizeOf(lv.t)) + (lv.t.isConstQualified() && !elemRecordOf(lv.t) ? ", const" : "") + "} : ptr", "g");
    if (isRef) initMember(lv, d->getInit());
    else initObject(lv, d->getInit());
    term("core.return");
    setBlock(done);
    term("core.return");
    popScope(false);
    print("@__hlir_init." + g, "() -> void");
  }

 private:
  ASTContext &ctx_;
  SourceManager &sm_;
  Module &mod_;
  const FunctionDecl *fd_ = nullptr;
  bool noLifetimes_ = false;
  std::deque<Blk> blocks_;
  size_t curBlock_ = 0;
  unsigned tmp_ = 0, bbn_ = 0;
  // SSA names assigned directly from a source identifier (parameters, %this/%sret/%__va, virtual-base pointers),
  // as opposed to the "hint+counter" scheme fresh() uses for everything else. A real C identifier can itself look
  // exactly like one of fresh()'s own outputs (e.g. a parameter literally named `v3`), so fresh() must dodge
  // whatever is already claimed here instead of handing out the same text for an unrelated value.
  std::set<std::string> namedUsed_;
  SourceLocation loc_;
  std::string sret_;
  unsigned asmCount_ = 0;
  std::map<const VarDecl *, std::string> locals_, pnames_;
  std::map<const LabelDecl *, size_t> labels_;
  llvm::DenseMap<const VariableArrayType *, std::string> vlaDim_;  // a VLA type node -> the i64 runtime value of its own dimension, computed once where the type was introduced (a declaration, or a VLA-pointer parameter's first use)
  std::map<const OpaqueValueExpr *, V> opaque_;
  const ArraySubscriptExpr *addrOfSubscript_ = nullptr;  // the `a[i]` directly under a `&` being lowered
  // C++: objects with a non-trivial destructor are destroyed when their scope ends (and on return/break/continue); temporaries
  // when the full-expression that created them ends.
  struct Cleanup { std::string obj; const CXXRecordDecl *rd = nullptr; uint64_t n = 1, esz = 0; };  // n elements of an array of objects
  struct Scope { std::vector<std::string> slots; std::vector<Cleanup> dtors, temps; };
  std::vector<Scope> scopes_;
  std::vector<size_t> breaks_, continues_, breakDepth_, contDepth_;
  // `try`/`catch`, same function only (see genThrow): the enclosing `try`s, innermost last, each with the blocks
  // its own `catch` clauses were pre-allocated into (in source order) and the scope depth to unwind (run local
  // destructors) down to before jumping to one of them. A `throw` resolves which clause catches it, if any,
  // entirely at compile time, from the STATIC type of the thrown expression (matching the standard: throwing
  // "slices" to the throw-expression's declared type, it is never the referred object's possibly-more-derived
  // runtime type).
  struct TryFrame { const CXXTryStmt *ts; std::vector<size_t> catchBlocks; size_t scopeDepth; };
  std::vector<TryFrame> tryStack_;
  std::string this_;                 // the object parameter of a method
  uint64_t arrIdx_ = 0;              // the element being initialised by an ArrayInitLoopExpr
  bool base_ = false;                // lowering the base-object variant of a constructor/destructor of a class with virtual bases
  std::map<const CXXRecordDecl *, std::string> vbaseLocal_;  // in such a constructor/destructor: the address of each virtual base of the class
  llvm::DenseMap<const ValueDecl *, FieldDecl *> capFields_;  // in a lambda's call operator: captured variable -> closure member
  FieldDecl *thisCap_ = nullptr;     // ... and the member holding the captured `this`
  std::string va_;                   // the variable-argument block of a variadic function
  size_t retBlock_ = SIZE_MAX;       // destructors/constructors with an epilogue: `return` jumps here
  std::map<const SwitchCase *, size_t> caseBlocks_;

  void print(const std::string &name, const std::string &sig) {
    std::ostringstream os;
    // `internal` marks C `static` / internal-linkage functions: every caller is in this module, which lets an
    // interprocedural analysis (e.g. hlir-wp-probe's parameter-bound summary) see all call sites. isExternallyVisible()
    // is the authoritative clang test, so an externally-callable function is never mis-marked.
    const bool internal = fd_ && !fd_->isExternallyVisible();
    os << "core.func " << (internal ? "internal " : "") << name << sig << " {\n";
    for (auto &b : blocks_) {
      os << "^" << b.name;
      if (!b.params.empty()) os << "(" << b.params << ")";
      os << ":\n";
      for (auto &o : b.ops) os << "  " << o << "\n";
      if (!b.done) os << "  core.unreachable\n";
    }
    os << "}\n";
    mod_.funcs << os.str();
  }

  // ------------------------------------------------------------------ plumbing
  [[noreturn]] void abortFn() { throw std::runtime_error("unsupported"); }
  [[noreturn]] void failAt(SourceLocation l, const std::string &msg) {
    PresumedLoc p = sm_.getPresumedLoc(sm_.getExpansionLoc(l));
    mod_.errors.push_back((p.isValid() ? std::string(p.getFilename()) : mod_.file) + ":" + std::to_string(p.isValid() ? p.getLine() : 0) + ":" +
                          std::to_string(p.isValid() ? p.getColumn() : 0) + ": unsupported: " + msg);
    abortFn();
  }
  [[noreturn]] void fail(const Stmt *s, const std::string &msg) { failAt(s ? s->getBeginLoc() : loc_, msg); }
  [[noreturn]] void failDecl(const Decl *d, const std::string &msg) { failAt(d->getLocation(), msg); }
  std::string locStr() const {
    PresumedLoc p = sm_.getPresumedLoc(sm_.getExpansionLoc(loc_));
    if (!p.isValid()) return "";
    return " loc(\"" + std::string(p.getFilename()) + "\":" + std::to_string(p.getLine()) + ":" + std::to_string(p.getColumn()) + ")";
  }
  size_t newBlock(const std::string &hint) {
    blocks_.push_back(Blk{hint + std::to_string(bbn_++), "", {}, false});
    if (blocks_.size() == 1) blocks_[0].name = hint;
    return blocks_.size() - 1;
  }
  std::string bname(size_t b) const { return "^" + blocks_[b].name; }
  void setBlock(size_t b) { curBlock_ = b; }
  void ensureOpen() {
    if (blocks_[curBlock_].done) curBlock_ = newBlock("dead");  // unreachable code after return/break/goto
  }
  std::string fresh(const char *hint = "t") {
    std::string n;
    do n = "%" + std::string(hint) + std::to_string(tmp_++); while (namedUsed_.count(n));
    return n;
  }
  void emit(const std::string &op) {
    ensureOpen();
    blocks_[curBlock_].ops.push_back(op + locStr());
  }
  std::string def(const std::string &opText, const char *hint = "t") {
    std::string n = fresh(hint);
    emit(n + " = " + opText);
    return n;
  }
  void term(const std::string &op) {
    ensureOpen();
    blocks_[curBlock_].ops.push_back(op + locStr());
    blocks_[curBlock_].done = true;
  }
  void at(const Stmt *s) {
    if (s) loc_ = s->getBeginLoc();
  }

  // ------------------------------------------------------------------ types
  static bool isScalarTy(QualType t) {
    t = t.getCanonicalType();
    if (const auto *at = t->getAs<AtomicType>()) t = at->getValueType().getCanonicalType();  // see coreTy
    return t->isIntegerType() || t->isEnumeralType() || t->isPointerType() || t->isBooleanType() || t->isNullPtrType() || t->isRealFloatingType();
  }
  std::string ty(QualType t) {
    std::string s = coreTy(ctx_, t);
    if (s.empty()) fail(nullptr, "type '" + t.getAsString() + "'");
    return s;
  }
  unsigned bits(QualType t) { return static_cast<unsigned>(ctx_.getTypeSize(t.getCanonicalType())); }
  // A forward-declared-only record referenced by a global whose own initialiser hasn't run its definition through
  // yet (seen on real kernel code, e.g. a `static const struct T ops;` sibling-of-another-global pattern in
  // drivers/gpu/drm/i915/display/intel_display_power_map.c) makes clang's own getTypeSizeInChars() dereference a
  // null record layout instead of returning 0 the way it does for an ordinary incomplete type — guard it here
  // rather than relying on that internal clang path to stay crash-free for every incomplete-type shape.
  uint64_t sizeOf(QualType t) {
    if (t->isIncompleteType()) return 1;
    uint64_t s = ctx_.getTypeSizeInChars(t).getQuantity();
    return s ? s : 1;
  }
  // Caches (and if needed, computes) the runtime i64 value of one VariableArrayType level's own dimension (its
  // getSizeExpr()), asserting it is positive. Keyed by the type node so repeated uses of the same VLA type (e.g.
  // every subscript into it) reuse the value computed where the type was first seen: sound, because a VLA's bound
  // is fixed at the point execution reaches its declaration (or, for a VLA-pointer parameter, its first use here),
  // not re-evaluated on every access.
  std::string vlaDimValue(const VariableArrayType *v) {
    auto it = vlaDim_.find(v);
    if (it != vlaDim_.end()) return it->second;
    std::string cnt = to64(genR(v->getSizeExpr()));
    std::string pos = def("core.icmp sgt " + cnt + ", " + c64(0) + " : bool");
    emit("core.assert " + pos + " {msg=\"variable length array size must be positive\"}");
    vlaDim_[v] = cnt;
    return cnt;
  }
  // Walks a (possibly multi-dimensional) variably-modified array type's chain of VariableArrayType levels,
  // returning the product of their dimension counts as a runtime i64 value ("" if t has none, i.e. is not
  // variably-modified), and sets base to the first non-VLA type reached (whose size is a compile-time constant).
  std::string vlaDimsProduct(QualType t, QualType &base) {
    std::string prod;
    QualType cur = t;
    while (auto *v = ctx_.getAsVariableArrayType(cur)) {
      std::string d = vlaDimValue(v);
      prod = prod.empty() ? d : def("core.mul " + prod + ", " + d + " : i64");
      cur = v->getElementType();
    }
    base = cur;
    return prod;
  }
  // Total byte size of a (possibly multi-dimensional) VLA type t, as a runtime i64 value: product of all its
  // dimensions' counts times the compile-time size of the innermost non-array element type.
  std::string vlaFlatBytes(QualType t) {
    QualType base;
    std::string prod = vlaDimsProduct(t, base);
    std::string sz = c64(static_cast<int64_t>(sizeOf(base)));
    return prod.empty() ? sz : def("core.mul " + prod + ", " + sz + " : i64");
  }
  // Runtime (i64 value, as a string) byte size of t, falling back to the ordinary compile-time sizeOf() for
  // anything that isn't itself variably-modified. Use this instead of sizeOf() anywhere a type could be the
  // pointee of a pointer into (or straight off) a VLA, e.g. a `int (*)[n]`-typed function parameter: sizeOf()
  // cannot be called on a VariableArrayType (its size isn't a compile-time constant).
  std::string dynSize(QualType t) { return t->isVariableArrayType() ? vlaFlatBytes(t) : c64(static_cast<int64_t>(sizeOf(t))); }
  std::string scaleDyn(const V &idx, const std::string &elemBytes) { return def("core.mul " + to64(idx) + ", " + elemBytes + " : i64"); }
  static bool isSigned(QualType t) { return t.getCanonicalType()->isSignedIntegerOrEnumerationType(); }

  // ------------------------------------------------------------------ small op builders
  V fkonst(const llvm::APFloat &f, QualType t) {
    llvm::APInt a = f.bitcastToAPInt().zextOrTrunc(bits(t));
    llvm::SmallString<40> s;
    a.toStringUnsigned(s);
    return {def("core.const " + std::string(s) + " : " + ty(t), "c"), t};
  }
  V fop(const std::string &k, const std::vector<std::string> &ops, QualType opT, QualType resT, QualType floatRes = QualType()) {
    std::string args;
    for (auto &o : ops) args += (args.empty() ? "" : ", ") + o;
    std::string attrs = "{k=\"" + k + "\", fw=" + std::to_string(isFlt(opT) ? fltWidth(ctx_, opT) : 0) +
                        (isFlt(resT) ? ", rw=" + std::to_string(fltWidth(ctx_, resT)) : "") + "}";
    (void)floatRes;
    return {def("core.fop " + args + " " + attrs + " : " + ty(resT)), resT};
  }
  // conversions between integers and floating point values, and between floating point formats
  V convFlt(V v, QualType to) {
    QualType from = v.t.getCanonicalType();
    to = to.getCanonicalType();
    if (isFlt(from) && isFlt(to)) {
      if (fltWidth(ctx_, from) == fltWidth(ctx_, to)) return {v.n, to};
      return fop(fltWidth(ctx_, to) > fltWidth(ctx_, from) ? "fpext" : "fptrunc", {v.n}, from, to);
    }
    if (isFlt(from)) {
      if (to->isBooleanType()) return {toBool(v), to};
      return fop(isSigned(to) ? "fptosi" : "fptoui", {v.n}, from, to);
    }
    if (from->isBooleanType()) v = convInt(v, ctx_.IntTy);
    return fop(isSigned(from) && !from->isBooleanType() ? "sitofp" : "uitofp", {v.n}, from, to);
  }
  V konst(int64_t v, QualType t) {
    if (isFlt(t)) {
      llvm::APFloat f(ctx_.getFloatTypeSemantics(t.getCanonicalType()));
      f.convertFromAPInt(llvm::APInt(64, static_cast<uint64_t>(v), true), true, llvm::APFloat::rmNearestTiesToEven);
      return fkonst(f, t);
    }
    llvm::APInt a(bits(t), static_cast<uint64_t>(v), true);
    llvm::SmallString<24> s;
    a.toStringSigned(s);
    return {def("core.const " + std::string(s) + " : " + ty(t), "c"), t};
  }
  std::string c64(int64_t v) { return def("core.const " + std::to_string(v) + " : i64", "c"); }
  // A pointer's truthiness is "not exactly the null pointer value (object 0, offset 0)". `core.is_null` only
  // checks the object id and is right for compiler-generated checks on allocation/call results (whose offset is
  // always 0 when the object id is 0), but a pointer born from an arbitrary integer (`core.int_to_ptr` of a
  // non-recoverable value, see IntToPtr in Machine.h) keeps object 0 with its real, possibly nonzero, offset --
  // `is_null` would wrongly call that null. Build the real null pointer value and compare both fields.
  std::string ptrIsExactlyNull(const std::string &v) {
    std::string np = def("core.int_to_ptr " + c64(0) + " : ptr", "np");
    return def("core.ptr_cmp eq " + v + ", " + np + " : bool", "isn");
  }
  std::string toBool(const V &v) {
    QualType t = v.t.getCanonicalType();
    if (t->isBooleanType()) return v.n;
    if (isFlt(t)) return fop("cmp.une", {v.n, konst(0, t).n}, t, ctx_.BoolTy).n;
    if (t->isPointerType()) return def("core.not " + ptrIsExactlyNull(v.n) + " : bool");
    return def("core.i2b " + v.n + " : bool");
  }
  // C: comparisons and logical operators have type int; C++: bool
  V fromBool(const std::string &b, QualType T = QualType()) {
    if (!T.isNull() && T.getCanonicalType()->isBooleanType()) return {b, T};
    return {def("core.b2i " + b + " : i32"), ctx_.IntTy};
  }
  // integer conversion by the source's signedness
  V convInt(V v, QualType to) {
    QualType from = v.t.getCanonicalType();
    to = to.getCanonicalType();
    if (isFlt(from) || isFlt(to)) return convFlt(v, to);
    if (from->isBooleanType()) return {to->isBooleanType() ? v.n : def("core.b2i " + v.n + " : " + ty(to)), to};
    if (to->isBooleanType()) return {toBool(v), to};
    unsigned wf = bits(from), wt = bits(to);
    if (wt == wf) return {v.n, to};
    if (wt > wf) return {def(std::string(isSigned(from) ? "core.sext " : "core.zext ") + v.n + " : " + ty(to)), to};
    return {def("core.trunc " + v.n + " : " + ty(to)), to};
  }
  std::string to64(const V &v) { return convInt(v, ctx_.LongTy).n; }
  V convTo(V v, QualType to) {
    if (v.t.getCanonicalType()->isPointerType() || to.getCanonicalType()->isPointerType()) return {v.n, to};
    return convInt(v, to);
  }
  // `container_of(ptr, T, member)` == `(T *)((char *)ptr - offsetof(T, member))`.
  //
  // When the list is EMPTY this computes a pointer BEFORE the object `ptr` belongs to, and that is exactly what
  // `list_for_each_entry` does on its first step: `pos = container_of(head->next, T, member)` with
  // `head->next == head`, immediately followed by the loop test `&pos->member != head`, which is false, so the
  // body never runs and the out-of-bounds pointer is never dereferenced. Strictly UB in C; a sanctioned, universal
  // kernel idiom in practice.
  //
  // It was invisible until the project initialiser started being executed (DESIGN.md §22.368): `snd_info_register`
  // and the four `*_search`/`snd_pcm_get`/`snd_pcm_next` list walks alone accounted for every one of the 87
  // "confirmed" findings of sound/core round 49b and for the bulk of round 49f's 257 `ptr_arith_oob` warnings.
  //
  // What is suppressed is ONLY the pointer-arithmetic check on the container_of expression itself. Every later
  // dereference through that pointer still goes through `core.check.oob`, so a container_of whose result really is
  // used out of bounds is still a finding -- which is what the regression fixture pins down. The constant must be
  // a REAL member offset of the target record (verified against the layout, not assumed from the shape), and the
  // left operand must have a 1-byte pointee, i.e. the `(char *)` form the macro actually expands to; anything else
  // falls through to the ordinary checked path.
  std::optional<std::string> genContainerOf(QualType to, const Expr *sub) {
    QualType toc = to.getCanonicalType();
    if (!toc->isPointerType()) return std::nullopt;
    QualType pointee = toc->getPointeeType();
    const RecordDecl *rd = pointee->getAsRecordDecl();
    if (!rd || !rd->isCompleteDefinition() || !layoutSane(pointee)) return std::nullopt;
    const auto *bo = dyn_cast<BinaryOperator>(sub->IgnoreParenImpCasts());
    if (!bo || bo->getOpcode() != BO_Sub) return std::nullopt;
    QualType lt = bo->getLHS()->getType().getCanonicalType();
    if (!lt->isPointerType()) return std::nullopt;
    // The left operand must step one byte at a time, i.e. be `char *` or `void *` -- the two forms the macro
    // actually expands to (the kernel's goes through a `void *__mptr` local). NOTE: Clang reports `void` as width
    // ZERO, not 1, so asking only for "size == 1" silently rejects every kernel container_of, which is exactly the
    // bug the first version of this had: the fixture used the `(char *)` spelling and passed while sound/core was
    // completely unaffected.
    QualType lpe = lt->getPointeeType();
    if (!lpe->isVoidType() && ctx_.getTypeSizeInChars(lpe).getQuantity() != 1) return std::nullopt;
    if (bo->getRHS()->HasSideEffects(ctx_)) return std::nullopt;
    Expr::EvalResult er;
    if (!bo->getRHS()->EvaluateAsInt(er, ctx_) || er.Val.getInt().isNegative()) return std::nullopt;
    uint64_t off = er.Val.getInt().getZExtValue();
    const clang::ASTRecordLayout &L = ctx_.getASTRecordLayout(rd);
    bool isMember = false;
    for (const FieldDecl *f : rd->fields())
      if (!f->isBitField() && L.getFieldOffset(f->getFieldIndex()) / 8 == off) { isMember = true; break; }
    if (!isMember) return std::nullopt;
    V base = genR(bo->getLHS());
    ++mod_.containerOfWaived;
    if (mod_.containerOfFirstSite.empty()) {
      PresumedLoc pl = sm_.getPresumedLoc(sm_.getExpansionLoc(bo->getExprLoc()));
      if (pl.isValid()) mod_.containerOfFirstSite = std::string(pl.getFilename()) + ":" + std::to_string(pl.getLine());
    }
    return def("core.ptr_add " + base.n + ", " + c64(-static_cast<int64_t>(off)) +
                   " {waived=\"container_of: the result is bounds-checked where it is dereferenced\"} : ptr",
               "p");
  }

  std::string ptrAdd(const std::string &p, const std::string &off) {
    if (!mod_.lenientPtrArith) emit("core.check.ptr_arith " + p + ", " + off);
    return def("core.ptr_add " + p + ", " + off + " : ptr", "p");
  }
  // address inside an object we just sized ourselves (initializers, string bytes)
  std::string inObj(const std::string &p, uint64_t off) {
    if (!off) return p;
    return def("core.ptr_add " + p + ", " + c64(static_cast<int64_t>(off)) + " {waived=\"in-bounds by construction\"} : ptr", "p");
  }
  // track=false: no lifetime_end is emitted (a copy made for a by-value argument can sit in a conditionally executed block, e.g. the
  // condition of an else-if, that does not dominate the end of the enclosing scope; it never escapes the call)
  std::string newSlot(QualType t, const std::string &name, bool track = true) {
    std::string n = fresh("v");
    uint64_t al = ctx_.getTypeAlignInChars(t).getQuantity();
    std::string op = n + " = core.alloca {size=" + std::to_string(sizeOf(t)) + ", align=" + std::to_string(al ? al : 1) + ", name=\"" +
                      name + "\"} : ptr";
    // noLifetimes_ (the function has a goto): a goto/switch-case entry can reach a later use of this slot without
    // passing through the program point where `declare()` would otherwise emit its alloca inline (e.g. SQLite's
    // VDBE-style `switch` with locals declared under one `case` and used, via fallthrough or an explicit `goto`,
    // under a later `case` that the switch's own jump table can reach directly) - the alloca's own SSA value then
    // fails to dominate that use, which the verifier correctly rejects. Real compilers sidestep this by always
    // emitting `alloca` in the function's entry block, which trivially dominates everything; do the same here,
    // for this category of function only (goto-free functions are unaffected: AST-walk order already matches
    // dominance order for them, so emitting inline at the declaration's position, as usual, is exactly right).
    if (noLifetimes_) {
      // The entry block may already have its own terminator by now (we are hoisting from somewhere later in the
      // body): insert before it, a terminator must stay the last op in its block.
      auto &ops = blocks_[0].ops;
      ops.insert(blocks_[0].done ? ops.end() - 1 : ops.end(), op + locStr());
    } else emit(op);
    if (track && !noLifetimes_ && !scopes_.empty()) scopes_.back().slots.push_back(n);
    return n;
  }
  void pushScope() { scopes_.emplace_back(); }
  void popScope(bool endLifetimes) {
    if (endLifetimes && !blocks_[curBlock_].done) {
      flushTemps();
      runDtors(scopes_.back().dtors);
      for (auto it = scopes_.back().slots.rbegin(); it != scopes_.back().slots.rend(); ++it) emit("core.lifetime_end " + *it);
    }
    scopes_.pop_back();
  }
  // ---- destructors
  // destroy the object at `obj`; baseObject: it is a base subobject of the object being destroyed (the base-object destructor
  // variant, which leaves the virtual bases to the complete object's destructor)
  void emitDtor(const std::string &obj, const CXXRecordDecl *rd, bool baseObject = false) {
    if (!rd || !rd->hasDefinition() || rd->hasTrivialDestructor()) return;
    const CXXDestructorDecl *dd = rd->getDestructor();
    if (!dd) return;
    ensureDeclared(dd);
    if (baseObject && hasBaseVariant(dd)) {
      ensureBaseDeclared(dd);
      emit("core.call @" + baseVariantName(dd) + "(" + obj + vbaseArgs(rd) + ")");
      return;
    }
    emit("core.call @" + fnName(dd) + "(" + obj + ")");
  }
  // ", <address of each virtual base of rd>" as seen from the constructor/destructor being lowered
  std::string vbaseArgs(const CXXRecordDecl *rd) {
    std::string a;
    for (auto &v : rd->vbases()) {
      auto it = vbaseLocal_.find(v.getType()->getAsCXXRecordDecl()->getCanonicalDecl());
      if (it == vbaseLocal_.end()) fail(nullptr, "virtual base of a subobject outside a constructor/destructor");
      a += ", " + it->second;
    }
    return a;
  }
  void ensureBaseDeclared(const FunctionDecl *fd) {
    if (const FunctionDecl *def = fd->getDefinition())
      if (!mod_.externals.count(fnName(fd)) && mod_.defined.insert(baseVariantName(def)).second) mod_.baseWork.push_back(def);
    std::string name = baseVariantName(fd);
    if ((mod_.defined.count(name) && !mod_.externals.count(fnName(fd))) || mod_.declares.count(name)) return;
    bool ok = true;
    std::string sg = sigOfDecl(ctx_, fd, ok);
    if (!ok) fail(nullptr, "signature of '" + name + "'");
    std::string extra;
    for (size_t i = 0; i < cast<CXXMethodDecl>(fd)->getParent()->getNumVBases(); ++i) extra += ", ptr";
    sg.insert(sg.find('(') + 4, extra);
    mod_.declares[name] = "core.declare @" + name + sg;
  }
  void runDtors(const std::vector<Cleanup> &v) {
    for (auto it = v.rbegin(); it != v.rend(); ++it)
      for (uint64_t k = it->n; k-- > 0;) emitDtor(k ? inObj(it->obj, k * it->esz) : it->obj, it->rd);  // arrays: last element first
  }
  static const CXXRecordDecl *recordOf(QualType t) { return t.getCanonicalType()->getAsCXXRecordDecl(); }
  // the class of the elements of (possibly nested) arrays too
  static const CXXRecordDecl *elemRecordOf(QualType t) { return t.getCanonicalType()->getBaseElementTypeUnsafe()->getAsCXXRecordDecl(); }
  static bool needsDtor(QualType t) {
    const CXXRecordDecl *rd = elemRecordOf(t);
    return rd && rd->hasDefinition() && !rd->hasTrivialDestructor();
  }
  Cleanup cleanupOf(const std::string &obj, QualType t) {
    Cleanup c{obj, elemRecordOf(t)};
    if (const ConstantArrayType *cat = ctx_.getAsConstantArrayType(t)) {
      c.n = ctx_.getConstantArrayElementCount(cat);
      c.esz = sizeOf(ctx_.getBaseElementType(t));
      if (c.n > 256) fail(nullptr, "array of more than 256 objects with destructors");
    } else if (t.getCanonicalType()->isArrayType()) fail(nullptr, "array of objects with destructors and no constant size");
    return c;
  }
  void registerDtor(const std::string &obj, QualType t) { if (needsDtor(t)) scopes_.back().dtors.push_back(cleanupOf(obj, t)); }
  void registerTemp(const std::string &obj, QualType t) { if (needsDtor(t)) scopes_.back().temps.push_back(cleanupOf(obj, t)); }
  // end of a full-expression: the temporaries it created are destroyed
  void flushTemps() {
    if (scopes_.empty() || scopes_.back().temps.empty() || blocks_[curBlock_].done) { if (!scopes_.empty()) scopes_.back().temps.clear(); return; }
    auto temps = std::move(scopes_.back().temps);
    scopes_.back().temps.clear();
    runDtors(temps);
  }
  // destroy the objects of every scope from the innermost down to (and including) index `from`, without leaving them
  void unwindTo(size_t from) {
    if (blocks_[curBlock_].done) return;
    for (size_t i = scopes_.size(); i-- > from;) {
      auto temps = scopes_[i].temps;
      runDtors(temps);
      runDtors(scopes_[i].dtors);
    }
  }
  void terminateProgram(const std::string &by = "abort") {  // abort()/exit(): the path ends here, it is not undefined behaviour
    V z = konst(0, ctx_.IntTy);
    std::string f = def("core.icmp ne " + z.n + ", " + z.n + " : bool");
    emit("core.assume " + f + " {terminates=\"" + by + "\"}");
    term("core.unreachable");
  }

  // ------------------------------------------------------------------ memory access
  void accessChecks(const LV &lv, uint64_t w, const char *acc) {
    if (lv.direct) return;
    // The store half of a read-modify-write: the load already emitted the whole access's checks as
    // access="rw". Emitting them again would add a check that cannot fail (see LV::rmw).
    if (lv.rmw && acc[0] == 'w') return;
    emit("core.check.null " + lv.p);
    emit("core.check.uaf " + lv.p);
    emit("core.check.oob " + lv.p + " {w=" + std::to_string(w) + ", access=\"" + (lv.rmw ? "rw" : acc) + "\"}");
  }
  V load(const LV &lv) {
    if (lv.bit) return loadBits(lv);
    QualType t = lv.t;
    if (!isScalarTy(t)) fail(nullptr, "load of aggregate type '" + t.getAsString() + "'");
    uint64_t w = t.getCanonicalType()->isBooleanType() ? 1 : sizeOf(t);
    accessChecks(lv, w, "r");
    if (!lv.zeroInit) emit("core.check.uninit " + lv.p + " {w=" + std::to_string(w) + "}");
    // A pointer to a complete, named record: carry the POINTEE's identity ("<tag>#<record size>") down to the
    // engine. Past the synthesis frontier the object this pointer gets is materialised at run time
    // (Memory::lazyFrontier, DESIGN.md §22.364) and nothing out there knows what it IS, so every invariant the
    // program states about that struct -- `snd_BUG_ON(plugin->src_width <= 0)` and the rest of the fieldAsserts
    // harvest (§22.358) -- is collected and then never applied, because those become `where:` preconditions on the
    // objects the InitPlan names and a frontier object is not one of them (§22.365).
    //
    // NOTE what this does NOT say: the size of the record is NOT the size of the allocation, and the pointer is
    // NOT necessarily at its start. `mark_t *top` in libyaml's `mark_stack_t` (test/c/scan/aggregate_rvalue.c) is a
    // CURSOR into an array, and `*(--s.top)` is perfectly legal; laying the object out as exactly one 12-byte
    // mark_t at offset 0 turns that into a confirmed ptr_arith_oob. The key is an identity for looking invariants
    // up, a lower bound at most -- never the extent of the allocation.
    std::string pz;
    if (const auto *pt = t.getCanonicalType()->getAs<clang::PointerType>()) {
      QualType pe = pt->getPointeeType().getCanonicalType();
      if (const auto *rt = pe->getAs<clang::RecordType>()) {
        const RecordDecl *prd = rt->getDecl();
        if (prd->isCompleteDefinition() && !prd->getNameAsString().empty() && layoutSane(pe))
          pz = "pointee=\"" + prd->getNameAsString() + "#" +
               std::to_string(ctx_.getTypeSizeInChars(pe).getQuantity()) + "\"";
      }
    }
    return {def("core.load " + lv.p + attrList({lv.direct ? "waived=\"object known\"" : "", t.isVolatileQualified() ? "volatile" : "", pz}) + " : " + ty(t), "l"), t};
  }
  void store(const LV &lv, const V &v) {
    if (lv.bit) return storeBits(lv, v);
    uint64_t w = v.t.getCanonicalType()->isBooleanType() ? 1 : sizeOf(v.t);
    accessChecks(lv, w, "w");
    if (!lv.direct || lv.isConst) emit("core.check.const_write " + lv.p);
    emit("core.store " + v.n + ", " + lv.p + attrList({lv.direct ? "waived=\"object known\"" : "", lv.t.isVolatileQualified() ? "volatile" : ""}));
  }
  // ---- bit-fields: byte-wise
  std::string byteAddr(const LV &lv, unsigned k) { return k ? (lv.direct ? inObj(lv.p, k) : ptrAdd(lv.p, c64(k))) : lv.p; }
  V loadBits(const LV &lv) {
    unsigned n = (lv.bitSh + lv.bitW + 7) / 8;
    if (n > 8) fail(nullptr, "bit-field spanning more than 8 bytes");
    std::string acc;
    for (unsigned k = 0; k < n; ++k) {
      LV bl = lv;
      bl.bit = false;
      bl.p = byteAddr(lv, k);
      accessChecks(bl, 1, "r");
      std::string b = def("core.load " + bl.p + attrList({lv.direct ? "waived=\"object known\"" : ""}) + " : i8", "l");
      std::string z = def("core.zext " + b + " : i64");
      if (k) z = def("core.shl " + z + ", " + c64(8 * k) + " {waived=\"constant in-range shift\"} : i64");
      acc = acc.empty() ? z : def("core.or " + acc + ", " + z + " : i64");
    }
    // isolate bits [sh, sh+w): shift the field to the top, then back down (arithmetic if the field is signed)
    bool sg = isSigned(lv.t);
    std::string up = def("core.shl " + acc + ", " + c64(64 - lv.bitSh - lv.bitW) + " {waived=\"constant in-range shift\"} : i64");
    std::string down = def(std::string(sg ? "core.ashr " : "core.lshr ") + up + ", " + c64(64 - lv.bitW) + " {waived=\"constant in-range shift\"} : i64");
    V v{down, sg ? ctx_.LongTy : ctx_.UnsignedLongTy};
    if (lv.t.getCanonicalType()->isBooleanType()) return {toBool(v), lv.t};
    return convInt(v, lv.t);
  }
  void storeBits(const LV &lv, const V &v) {
    unsigned n = (lv.bitSh + lv.bitW + 7) / 8;
    if (n > 8) fail(nullptr, "bit-field spanning more than 8 bytes");
    uint64_t fieldMask = lv.bitW >= 64 ? ~0ULL : ((1ULL << lv.bitW) - 1);
    std::string x = to64(v);
    std::string masked = def("core.and " + x + ", " + def("core.const " + std::to_string(static_cast<int64_t>(fieldMask)) + " : i64", "c") + " : i64");
    std::string val = lv.bitSh ? def("core.shl " + masked + ", " + c64(lv.bitSh) + " {waived=\"constant in-range shift\"} : i64") : masked;
    uint64_t mask = fieldMask << lv.bitSh;
    for (unsigned k = 0; k < n; ++k) {
      unsigned mk = static_cast<unsigned>((mask >> (8 * k)) & 0xff);
      std::string sh = k ? def("core.lshr " + val + ", " + c64(8 * k) + " {waived=\"constant in-range shift\"} : i64") : val;
      std::string vk = def("core.trunc " + sh + " : i8");
      LV bl = lv;
      bl.bit = false;
      bl.p = byteAddr(lv, k);
      accessChecks(bl, 1, "w");
      if (!lv.direct) emit("core.check.const_write " + bl.p);
      std::string nw = vk;
      if (mk != 0xff) {
        accessChecks(bl, 1, "r");
        std::string old = def("core.load " + bl.p + attrList({lv.direct ? "waived=\"object known\"" : ""}) + " : i8", "l");
        std::string keep = def("core.and " + old + ", " + def("core.const " + std::to_string(static_cast<int>(static_cast<int8_t>(~mk & 0xff))) + " : i8", "c") + " : i8");
        std::string put = def("core.and " + vk + ", " + def("core.const " + std::to_string(static_cast<int>(static_cast<int8_t>(mk))) + " : i8", "c") + " : i8");
        nw = def("core.or " + keep + ", " + put + " : i8");
      }
      emit("core.store " + nw + ", " + bl.p + attrList({lv.direct ? "waived=\"object known\"" : ""}));
    }
  }
  // struct copy; the engines' memcpy has no range checks of its own, so non-direct objects get them here
  void copyBytes(const LV &d, const LV &s, uint64_t n) {
    accessChecks(d, n, "w");
    accessChecks(s, n, "r");
    emit("core.memcpy " + d.p + ", " + s.p + ", " + c64(static_cast<int64_t>(n)));
  }

  // ------------------------------------------------------------------ globals / strings
  // a callee with a body (e.g. a `static inline` helper from a header) is lowered too -- but NOT one whose
  // body lives in a SYSTEM header. Those are libc, and libc's semantics come from the model database;
  // pulling the implementation in as well produces two definitions of the same name once `--link` puts the
  // lowered units and models/libc.core into one module, and the parser then refuses the whole program
  // ("redefinition of function @tolower") -- no entries, no findings, no diagnosis.
  //
  // It is not a close call about which should win. glibc's `__extern_inline tolower` (ctype.h, only when
  // __OPTIMIZE__ so it appears at -O1 and not at -O0) is
  //     return __c >= -128 && __c < 256 ? (*__ctype_tolower_loc())[__c] : __c;
  // and `__ctype_tolower_loc` has no body here, so the lowered version indexes a table through an opaque
  // pointer: worse than the model and a source of spurious findings. The Redis profile carried
  // `-D__NO_CTYPE` to dodge this, which silently replaced isspace/isdigit with function calls and removed
  // the ctype-table path from every scan that used it (DESIGN.md Sec.22.453).
  //
  // A system-header function with no model is left declared, which is exactly how every other libc
  // function without a model is treated; `opaque_calls` reports it if it matters on a path.
  //
  // The test is "system header AND C language linkage", not "system header" alone. C++'s standard library
  // is header-defined templates and inline members -- `std::vector<int>::push_back`, `std::swap<VH>`,
  // `std::string`'s constructors -- and the ModelDB has no entry for any of them, so excluding every
  // system-header body turns the whole STL into unmodelled externals. (Measured, not guessed: that
  // version of this change left c_tests at 1704 passed / 24 failed, every failure a .cpp one, each
  // "call to external function @_ZNSt... (no model for it)".) Restricting it to C linkage draws the line
  // where the model database actually ends: `extern "C"` in a system header is libc.
  // The one place that decides it. Both useFunction() and the declare-on-call path below must agree:
  // if this returns true the body never enters the module, so the call needs a `core.declare` exactly
  // as if the function had had no definition at all. Disagreeing gives "call to undeclared function".
  bool bodyIsLibcsToModel(const FunctionDecl *def) {
    if (!ctx_.getSourceManager().isInSystemHeader(def->getLocation())) return false;
    if (def->isExternC()) return true;
    // C++ LINKAGE IS NOT ENOUGH TO MAKE IT C++. Under __CORRECT_ISO_CPP_STRING_H_PROTO glibc's
    // <string.h> wraps memchr/strchr/strpbrk/strrchr/strstr in `extern "C++"` OVERLOAD PAIRS -- one
    // taking `char *`, one `const char *` -- each carrying __asm__("strchr") and, from -O1 upward, a
    // body of its own:
    //     __extern_always_inline char *strchr (char *__s, int __c) __THROW
    //     { return __builtin_strchr (__s, __c); }
    // isExternC() is false for those, so the Sec.22.453 test let them through, and because the asm label
    // collapses both overloads onto one symbol the module got `@strchr` TWICE -- the link failed with
    // "redefinition of function @strchr" on the first C++ target that reached it (MariaDB's net_serv.cc,
    // DESIGN.md Sec.22.459).
    //
    // The rule that covers both spellings: in a SYSTEM header, a name that is not C++-mangled is the C
    // library's. Everything the standard library really implements in headers -- the templates and inline
    // members that make the STL work -- is mangled, so this keeps lowering those (Sec.22.453's measured
    // reason for not excluding system headers wholesale).
    return fnName(def).rfind("_Z", 0) != 0;
  }
  void useFunction(const FunctionDecl *fd) {
    if (mod_.externals.count(fnName(fd))) return;
    if (const FunctionDecl *def = fd->getDefinition()) {
      if (bodyIsLibcsToModel(def)) return;
      if (mod_.defined.insert(fnName(def)).second) mod_.work.push_back(def);
    }
  }
  void ensureDeclared(const FunctionDecl *fd) {
    useFunction(fd);
    std::string name = fnName(fd);
    if ((mod_.defined.count(name) && !mod_.externals.count(name)) || mod_.declares.count(name)) return;
    bool ok = true;
    std::string sg = sigOfDecl(ctx_, fd, ok);
    if (!ok) fail(nullptr, "signature of '" + name + "'");
    mod_.declares[name] = "core.declare @" + name + sg;
  }
  void markInternal(const std::string &g) {
    mod_.internalTokens.insert(g);
    mod_.internalTokens.insert(g + ".__init");
    mod_.internalTokens.insert("__hlir_init." + g);
  }
  LV globalLV(const VarDecl *vd) {
    LV lv;
    lv.t = vd->getType();
    lv.direct = true;
    lv.zeroInit = true;
    lv.isConst = vd->getType().isConstQualified() && !elemRecordOf(vd->getType());  // a const class object is writable while its constructor runs
    uint64_t gsize = vd->getType()->isReferenceType() ? 8 : sizeOf(lv.t);
    std::string g = globalName(mod_, vd);
    if (!vd->isExternallyVisible()) markInternal(g);
    if (needsInit(ctx_, vd)) {
      if (mod_.initSeen.insert(vd->getDefinition()).second) mod_.initQueue.push_back(vd->getDefinition());
      emit("core.call @__hlir_init." + g + "()");
      emitExcEscapeGuard();  // the initialiser may call arbitrary user code (see genThrow/emitCall): no local `try` can be wrapped around a global's own lazy-init call site, so an escaping exception here can only be the pre-existing "uncaught" outcome
    } else if (mod_.link && !vd->getDefinition() && vd->isExternallyVisible()) {
      // defined in another unit: its initialiser runs there (the linker supplies an empty one if nobody has an initialiser)
      mod_.declares["__hlir_init." + g] = "core.declare @__hlir_init." + g + "() -> void";
      emit("core.call @__hlir_init." + g + "()");
      emitExcEscapeGuard();
    }
    lv.p = def("core.global_addr @" + g + " {size=" + std::to_string(gsize) + (lv.isConst ? ", const" : "") + "} : ptr", "g");
    return lv;
  }
  std::string stringObject(const StringLiteral *sl) {
    unsigned w = sl->getCharByteWidth();  // 1, 2 (char16_t, wchar_t on Windows) or 4 (char32_t, wchar_t): the byte image of the code units
    std::string s;
    if (w == 1) s = sl->getString().str();
    else {
      for (unsigned i = 0; i < sl->getLength(); ++i) {
        uint32_t cu = sl->getCodeUnit(i);
        for (unsigned b = 0; b < w; ++b) s += static_cast<char>((cu >> (8 * b)) & 0xff);
      }
      s.append(w - 1, '\0');  // with the one terminator byte every string object gets, the terminator is a whole code unit
    }
    std::string key = w == 1 ? s : "\x01w" + std::to_string(w) + ":" + s;
    auto it = mod_.strIdx.find(key);
    unsigned idx;
    if (it == mod_.strIdx.end()) {
      idx = static_cast<unsigned>(mod_.strs.size());
      mod_.strIdx[key] = idx;
      mod_.strs.push_back(s);
    } else idx = it->second;
    for (const char *suffix : {"", ".__init"}) mod_.internalTokens.insert("__str." + std::to_string(idx) + suffix);
    mod_.internalTokens.insert("__hlir_init.str" + std::to_string(idx));
    emit("core.call @__hlir_init.str" + std::to_string(idx) + "()");
    return def("core.global_addr @__str." + std::to_string(idx) + " {size=" + std::to_string(s.size() + 1) + ", const} : ptr", "s");
  }

  // ------------------------------------------------------------------ lvalues
  LV genL(const Expr *E) {
    at(E);
    E = E->IgnoreParens();
    if (auto *dr = dyn_cast<DeclRefExpr>(E)) {
      if (auto *bd = dyn_cast<BindingDecl>(dr->getDecl())) {  // C++17 structured binding (`auto [a, b] = ...`)
        // Tuple-like decomposition (`std::pair`/`std::tuple`/anything with a `get<N>`): clang synthesizes a
        // hidden reference VarDecl ("holding var") initialized to the `get<N>(...)` call; `declare()` on the
        // enclosing DecompositionDecl already materialized it into `locals_`, so this is just a normal
        // reference-variable read.
        if (const VarDecl *hv = bd->getHoldingVar()) {
          auto it = locals_.find(hv);
          if (it != locals_.end()) {
            LV lv;
            lv.p = def("core.load " + it->second + " {waived=\"object known\"} : ptr", "l");
            lv.t = E->getType();
            return lv;
          }
        }
        // Array/struct decomposition: no hidden var, `getBinding()` is the sub-object expression itself
        // (an ArraySubscriptExpr or MemberExpr on the DecompositionDecl) - evaluate it directly.
        if (Expr *b = bd->getBinding()) return genL(b);
        fail(E, "structured binding '" + bd->getNameAsString() + "' without a resolved binding expression");
      }
      if (auto *vd = dyn_cast<VarDecl>(dr->getDecl())) {
        auto it = locals_.find(vd);
        if (it != locals_.end()) {
          if (vd->getType()->isReferenceType()) {  // the slot holds the address of the referenced object
            LV lv;
            lv.p = def("core.load " + it->second + " {waived=\"object known\"} : ptr", "l");
            lv.t = E->getType();
            return lv;
          }
          LV lv;
          lv.p = it->second;
          lv.t = vd->getType();
          lv.direct = true;
          return lv;
        }
        if (vd->hasGlobalStorage()) {
          if (vd->getType()->isReferenceType()) {  // the global holds the address of the referenced object
            LV slot = globalLV(vd);
            LV lv;
            lv.p = def("core.load " + slot.p + " {waived=\"object known\"} : ptr", "l");
            lv.t = E->getType();
            return lv;
          }
          return globalLV(vd);
        }
      }
      if (auto *vd = dyn_cast<VarDecl>(dr->getDecl())) {  // inside a lambda: a captured variable is a member of the closure
        auto cf = capFields_.find(vd);
        if (cf != capFields_.end()) {
          std::string fa = fieldAddr(this_, cf->second);
          LV lv;
          if (cf->second->getType()->isReferenceType()) lv.p = def("core.load " + fa + " {waived=\"object known\"} : ptr", "l");
          else { lv.p = fa; lv.direct = true; }
          lv.t = E->getType();
          return lv;
        }
      }
      if (isa<FunctionDecl>(dr->getDecl())) {  // a function lvalue that didn't decay (e.g. binding a forwarding
        // reference `Fn&&` directly to a named function, as std::function's converting constructor does): the
        // "address" of a function designator is its code address, same bit pattern `funcValue` produces for the
        // ordinary function-to-pointer-decay case; consistent with this project's "a reference is a pointer" rule.
        LV lv;
        lv.p = funcValue(E);
        lv.t = E->getType();
        lv.direct = true;
        return lv;
      }
      fail(E, "reference to '" + dr->getDecl()->getNameAsString() + "' as an lvalue");
    }
    if (auto *uo = dyn_cast<UnaryOperator>(E)) {
      if (uo->getOpcode() == UO_Deref) {
        V p = genR(uo->getSubExpr());
        LV lv;
        lv.p = p.n;
        lv.t = uo->getType();
        return lv;
      }
      if (uo->getOpcode() == UO_Extension) return genL(uo->getSubExpr());
    }
    if (auto *as = dyn_cast<ArraySubscriptExpr>(E)) {
      V base = genR(as->getBase());  // array decayed to a pointer by Clang
      V idx = genR(as->getIdx());
      if (!base.t.getCanonicalType()->isPointerType()) std::swap(base, idx);  // Clang may put the pointer on either side
      // Field-level array-bound check, independent of core.check.oob's whole-object bound (DESIGN.md P1 gap fix:
      // core.check.oob only knows the size of the whole backing allocation, so a write that overflows a fixed-size
      // struct field into an adjacent field -- while staying inside that allocation -- goes undetected). Fires only
      // when the subscripted pointer is literally `expr.field[idx]` / `expr->field[idx]` for a `field` declared as
      // a fixed-size array; skips a field that is the last member of its record (the "struct hack"/flexible-array-
      // member idiom, where an intentionally over-sized access is valid C) or belongs to a union (overlapping
      // members are valid to access across the union's whole size, not just one member's declared extent).
      {
        const Expr *ptrExpr = as->getBase()->IgnoreParenImpCasts();
        if (!as->getBase()->getType().getCanonicalType()->isPointerType())
          ptrExpr = as->getIdx()->IgnoreParenImpCasts();
        if (auto *me0 = dyn_cast<MemberExpr>(ptrExpr)) {
          if (auto *fd = dyn_cast<FieldDecl>(me0->getMemberDecl())) {
            if (const auto *cat = ctx_.getAsConstantArrayType(fd->getType())) {
              const RecordDecl *rd = fd->getParent();
              const FieldDecl *lastF = nullptr;
              for (const FieldDecl *f2 : rd->fields()) lastF = f2;
              // checked at 64 bits: an `unsigned char` index into a 256-element field would otherwise be compared
              // against 256 truncated to its own 8-bit width (0) and fire on every access. Under `&`, nothing is
              // accessed and one past the end is a valid pointer (`&buf[sizeof buf]`, expat's sip_endof()).
              uint64_t n = cat->getSize().getZExtValue() + (as == addrOfSubscript_ ? 1 : 0);
              if (!rd->isUnion() && lastF != fd)
                emit("core.check.field_oob " + to64(idx) + " {n=" + std::to_string(n) + "}");
            }
          }
        }
      }
      QualType et = as->getType();
      LV lv;
      lv.p = ptrAdd(base.n, et->isVariableArrayType() ? scaleDyn(idx, vlaFlatBytes(et)) : scale(idx, sizeOf(et)));
      lv.t = et;
      return lv;
    }
    if (auto *me = dyn_cast<MemberExpr>(E)) return genMember(me);
    if (auto *sl = dyn_cast<StringLiteral>(E)) {
      LV lv;
      lv.t = sl->getType();
      lv.p = stringObject(sl);
      lv.direct = true;
      lv.zeroInit = true;
      lv.isConst = true;
      return lv;
    }
    if (auto *pe = dyn_cast<PredefinedExpr>(E)) return genL(pe->getFunctionName());  // __func__
    if (auto *cl = dyn_cast<CompoundLiteralExpr>(E)) {
      LV lv;
      lv.t = cl->getType();
      lv.p = newSlot(lv.t, "compound");
      lv.direct = true;
      initObject(lv, cl->getInitializer());
      return lv;
    }
    if (auto *uo2 = dyn_cast<UnaryOperator>(E))
      if (uo2->getOpcode() == UO_PreInc || uo2->getOpcode() == UO_PreDec) {  // C++: yields an lvalue
        LV l;
        genIncDec(uo2, &l);
        return l;
      }
    if (auto *bo2 = dyn_cast<BinaryOperator>(E)) {
      if (auto *ca = dyn_cast<CompoundAssignOperator>(bo2)) { LV l; genCompound(ca, &l); return l; }
      // `a = b = c;` (b's type is scalar or a plain struct/union, e.g. `start_mark = end_mark = token->start_mark;`
      // with all three of `yaml_mark_t` type): the inner assignment is used as an lvalue by the outer one.
      if (bo2->getOpcode() == BO_Assign && (isScalarTy(bo2->getLHS()->getType()) || bo2->getLHS()->getType()->isRecordType())) {
        LV l;
        genAssign(bo2, &l);
        return l;
      }
      if (bo2->getOpcode() == BO_Comma) { genR(bo2->getLHS()); return genL(bo2->getRHS()); }
    }
    if (auto *co = dyn_cast<ConditionalOperator>(E); co && co->isLValue()) {  // C++: `c ? a : b` with two lvalues is an lvalue
      std::string c = genCond(co->getCond());
      size_t tb = newBlock("then"), eb = newBlock("else"), end = newBlock("end");
      std::string res = fresh("r");
      blocks_[end].params = res + ": ptr";
      term("core.cond_br " + c + ", " + bname(tb) + ", " + bname(eb));
      setBlock(tb);
      pushScope();
      LV a = genL(co->getTrueExpr());
      popScope(true);
      term("core.br " + bname(end) + "(" + a.p + ")");
      setBlock(eb);
      pushScope();
      LV b = genL(co->getFalseExpr());
      popScope(true);
      term("core.br " + bname(end) + "(" + b.p + ")");
      setBlock(end);
      LV r;
      r.p = res;
      r.t = co->getType();
      r.isConst = a.isConst || b.isConst;
      return r;
    }
    if (auto *ewc = dyn_cast<ExprWithCleanups>(E)) return genL(ewc->getSubExpr());
    if (auto *dae = dyn_cast<CXXDefaultArgExpr>(E)) return genL(dae->getExpr());
    if (auto *die = dyn_cast<CXXDefaultInitExpr>(E)) return genL(die->getExpr());
    if (auto *mte = dyn_cast<MaterializeTemporaryExpr>(E)) {  // a temporary the expression needs an address of
      QualType t = mte->getSubExpr()->getType();
      LV tl{newSlot(t, "temp", false), t, true, false, false};
      initObject(tl, mte->getSubExpr());
      registerTemp(tl.p, t);
      return tl;
    }
    if (auto *bt = dyn_cast<CXXBindTemporaryExpr>(E)) {
      QualType t = bt->getType();
      LV tl{newSlot(t, "temp", false), t, true, false, false};
      initObject(tl, bt->getSubExpr());
      registerTemp(tl.p, t);
      return tl;
    }
    if (auto *le = dyn_cast<LambdaExpr>(E)) {  // a closure object: one member per capture
      QualType t = le->getType();
      LV tl{newSlot(t, "lambda", false), t, true, false, false};
      initObject(tl, le);
      registerTemp(tl.p, t);
      return tl;
    }
    if (auto *cx = dyn_cast<CXXConstructExpr>(E)) {  // a class prvalue used where an object is needed
      QualType t = cx->getType();
      LV tl{newSlot(t, "temp", false), t, true, false, false};
      constructInto(tl.p, cx);
      registerTemp(tl.p, t);
      return tl;
    }
    if (auto *sil = dyn_cast<CXXStdInitializerListExpr>(E)) {  // `{1, 2, 3}` bound to a std::initializer_list<T> parameter/variable
      // The subexpression is always a MaterializeTemporaryExpr of the backing array (`const T[n]`); materialise
      // it as any other temporary (genL below handles MaterializeTemporaryExpr), then build the library's actual
      // initializer_list object by its *real* field layout: libstdc++ uses one pointer field (array base) and one
      // integer field (length); some library/ABI variants instead use two pointer fields (begin/end). Either way,
      // this does not hardcode a specific vendor layout - it drives entirely off the real fields of the real class.
      QualType t = sil->getType();
      LV arr = genL(sil->getSubExpr());  // the backing array, as an addressable temporary
      LV tl{newSlot(t, "ilist", false), t, true, false, false};
      const RecordDecl *rd = t->getAsRecordDecl();
      if (!rd || !layoutSane(t)) fail(E, "std::initializer_list with an unknown layout");
      uint64_t n = 0;
      if (const auto *cat = ctx_.getAsConstantArrayType(arr.t)) n = cat->getSize().getZExtValue();
      const ASTRecordLayout &L = ctx_.getASTRecordLayout(rd);
      unsigned pointerFieldsSeen = 0;
      QualType et = arr.t.getCanonicalType()->isArrayType() ? ctx_.getAsArrayType(arr.t)->getElementType() : arr.t;
      for (auto *f : rd->fields()) {
        uint64_t off = L.getFieldOffset(f->getFieldIndex()) / 8;
        LV fl{inObj(tl.p, off), f->getType(), true, false, false};
        if (f->getType().getCanonicalType()->isPointerType()) {
          if (pointerFieldsSeen == 0) store(fl, {arr.p, f->getType()});  // begin / array base
          else store(fl, {inObj(arr.p, n * sizeOf(et)), f->getType()});  // end (two-pointer ABI variants)
          ++pointerFieldsSeen;
        } else {
          store(fl, konst(static_cast<int64_t>(n), f->getType()));  // length
        }
      }
      registerTemp(tl.p, t);
      return tl;
    }
    if (auto *ce = dyn_cast<CallExpr>(E)) {
      if (!isRecordTy(ce->getType()) && !ce->isGLValue()) fail(E, "call result used as an lvalue");
      V r = genCall(ce);
      LV lv;
      lv.p = r.n;
      lv.t = ce->getType();
      lv.direct = isRecordTy(ce->getType()) && !ce->isGLValue();
      return lv;
    }
    if (auto *ov = dyn_cast<OpaqueValueExpr>(E)) {
      auto it = opaque_.find(ov);
      if (it != opaque_.end() && (isRecordTy(it->second.t) || it->second.t->isArrayType())) return {it->second.n, it->second.t, true, false, false};
    }
    if (auto *ce = dyn_cast<CastExpr>(E)) {
      auto k = ce->getCastKind();
      if (k == CK_NoOp || k == CK_LValueBitCast || (k == CK_LValueToRValue && !isScalarTy(ce->getType()))) return genL(ce->getSubExpr());
      if (k == CK_DerivedToBase || k == CK_UncheckedDerivedToBase) {
        LV d = genL(ce->getSubExpr());
        d.p = adjustToBase(d.p, ce->getSubExpr()->getType(), ce);
        d.t = ce->getType();
        return d;
      }
      if (k == CK_UserDefinedConversion || k == CK_ConstructorConversion) return genL(ce->getSubExpr());
      if (k == CK_Dynamic) return {genDynCast(cast<CXXDynamicCastExpr>(ce)), ce->getType(), true, false, false};
    }
    if (auto *te = dyn_cast<CXXTypeidExpr>(E)) return genTypeid(te);
    fail(E, std::string("lvalue of kind ") + E->getStmtClassName());
  }
  // `typeid(Type)`, or `typeid(expr)` where `expr`'s static type is not a polymorphic class: fully static, resolved
  // to a marker for the named/static type without evaluating `expr` at all (matching the standard: the operand is
  // unevaluated unless it is actually needed to determine a *runtime* type, exactly `isPotentiallyEvaluated()`).
  // `typeid(expr)` where `expr`'s static type IS polymorphic: `expr` is evaluated, its address taken, and a
  // dispatcher (see `typeIdDispatcher`) compares its vptr against every class of this module derived from that
  // static type, same mechanism `dynamic_cast` uses. `.name()` on the result is not modelled (see FEATURE_STATUS);
  // comparing two `typeid(...)` results with `==`/`!=` works, since both sides reduce to one of these markers and
  // the comparison is then an ordinary pointer-identity call like any other reference parameter (`evalArgsFor`).
  LV genTypeid(const CXXTypeidExpr *te) {
    QualType opTy;
    const Expr *opExpr = nullptr;
    if (te->isTypeOperand()) opTy = te->getTypeOperand(ctx_);
    else { opExpr = te->getExprOperand(); opTy = opExpr->getType(); }
    LV lv;
    lv.t = te->getType();
    lv.direct = true;
    if (!te->isPotentiallyEvaluated()) {
      auto [nm, sz] = typeInfoMarker(ctx_, opTy);
      lv.p = def("core.global_addr @" + nm + " {size=" + std::to_string(sz) + ", const} : ptr", "ti");
      return lv;
    }
    const CXXRecordDecl *src = opTy->getAsCXXRecordDecl();
    if (!src || !src->getDefinition()) fail(te, "typeid of an incomplete class type");
    src = src->getDefinition();
    std::string srcTag = typeInfoMarker(ctx_, ctx_.getRecordType(src)).first;
    std::string name = "__hlir_typeid." + srcTag;
    mod_.typeIds[name] = src;
    lv.p = def("core.call @" + name + "(" + genL(opExpr).p + ") : ptr", "ti");
    return lv;
  }
  LV genMember(const MemberExpr *me) {
    const ValueDecl *md = me->getMemberDecl();
    // a field reached through anonymous struct/union members is a chain of fields
    std::vector<const FieldDecl *> chain;
    if (auto *f = dyn_cast<FieldDecl>(md)) chain.push_back(f);
    else if (auto *ind = dyn_cast<IndirectFieldDecl>(md)) {
      for (auto *nd : ind->chain()) chain.push_back(cast<FieldDecl>(nd));
    } else fail(me, "member that is not a field");
    LV lv;
    std::string base;
    if (me->isArrow()) base = genR(me->getBase()).n;
    else {
      LV b = genL(me->getBase());
      base = b.p;
      lv.direct = b.direct;
      lv.zeroInit = b.zeroInit;
      lv.isConst = b.isConst || me->getBase()->getType().isConstQualified();
    }
    uint64_t bitOff = 0;
    for (auto *f : chain)
      if (!layoutSane(ctx_.getRecordType(f->getParent()))) fail(me, "member of a record whose layout is invalid or incomplete");
    for (auto *f : chain) bitOff += ctx_.getASTRecordLayout(f->getParent()).getFieldOffset(f->getFieldIndex());
    const FieldDecl *last = chain.back();
    uint64_t off = bitOff / 8;
    lv.p = off ? ptrAdd(base, c64(static_cast<int64_t>(off))) : base;
    lv.t = last->getType();
    if (me->isArrow()) lv.direct = false;
    if (lv.t->isReferenceType()) {  // a reference member: the field holds the address of the object
      accessChecks(lv, 8, "r");
      std::string ptr = def("core.load " + lv.p + attrList({lv.direct ? "waived=\"object known\"" : ""}) + " : ptr", "l");
      LV r;
      r.p = ptr;
      r.t = me->getType();
      return r;
    }
    if (last->isBitField()) {
      lv.bit = true;
      lv.bitSh = static_cast<unsigned>(bitOff % 8);
      lv.bitW = last->getBitWidthValue(ctx_);
    }
    return lv;
  }
  std::string scale(const V &idx, uint64_t elem) {
    std::string i = to64(idx);
    if (elem == 1) return i;
    return def("core.mul " + i + ", " + c64(static_cast<int64_t>(elem)) + " : i64");
  }

  // ------------------------------------------------------------------ rvalues
  V genR(const Expr *E) {
    at(E);
    E = E->IgnoreParens();
    QualType T = E->getType();
    if (auto *ov = dyn_cast<OpaqueValueExpr>(E)) {
      auto it = opaque_.find(ov);
      if (it == opaque_.end()) fail(E, "opaque value");
      return it->second;
    }
    // exact constant folding (sound: the evaluator refuses anything that would be undefined)
    if (T->isIntegerType() && !T->isBooleanType() && !isa<IntegerLiteral>(E)) {
      Expr::EvalResult r;
      if (E->EvaluateAsInt(r, ctx_, Expr::SE_NoSideEffects)) return konst(apExt(r.Val.getInt()), T);
    }
    if (auto *fl = dyn_cast<FloatingLiteral>(E)) return fkonst(fl->getValue(), T);
    if (auto *il = dyn_cast<IntegerLiteral>(E)) return konst(static_cast<int64_t>(il->getValue().getZExtValue()), T);
    if (auto *cl = dyn_cast<CharacterLiteral>(E)) return konst(static_cast<int64_t>(cl->getValue()), T);
    if (isa<CXXScalarValueInitExpr>(E)) return zeroOf(T);
    if (isa<UnaryExprOrTypeTraitExpr>(E) || isa<ConstantExpr>(E) || isa<OffsetOfExpr>(E)) {
      Expr::EvalResult r;
      if (E->EvaluateAsInt(r, ctx_)) return konst(apExt(r.Val.getInt()), T);
      fail(E, "non-constant sizeof/alignof (VLA?)");
    }
    if (auto *dr = dyn_cast<DeclRefExpr>(E)) {
      if (auto *ec = dyn_cast<EnumConstantDecl>(dr->getDecl())) return konst(apExt(ec->getInitVal()), T);
      if (isa<BindingDecl>(dr->getDecl()) && isScalarTy(T)) return load(genL(E));  // structured binding, same elided-cast situation as below
      // A bare DeclRefExpr reaching genR (not wrapped in its own CK_LValueToRValue node) happens for
      // std::nullptr_t glvalues: clang elides the LValueToRValue node when the immediately enclosing
      // cast is itself CK_NullToPointer (there is no value representation to "load" for nullptr_t, so
      // it folds the two conversions into one cast node). Any other scalar VarDecl/ParmVarDecl read
      // reaching here is the same situation: read it exactly like the normal load(genL(...)) path does.
      if (isa<VarDecl>(dr->getDecl()) && isScalarTy(T)) return load(genL(E));
      fail(E, "use of '" + dr->getDecl()->getNameAsString() + "' as a value");
    }
    if (auto *ce = dyn_cast<CastExpr>(E)) return genCast(ce);
    if (auto *uo = dyn_cast<UnaryOperator>(E)) return genUnary(uo);
    if (auto *bo = dyn_cast<BinaryOperator>(E)) return genBinary(bo);
    if (auto *co = dyn_cast<ConditionalOperator>(E)) return genCondOp(co);
    if (auto *bc = dyn_cast<BinaryConditionalOperator>(E)) return genElvis(bc);
    if (auto *call = dyn_cast<CallExpr>(E)) return genCall(call);
    if (auto *se = dyn_cast<StmtExpr>(E)) return genStmtExpr(se);
    if (isa<ArraySubscriptExpr>(E) || isa<MemberExpr>(E)) return load(genL(E));
    if (auto *sl = dyn_cast<StringLiteral>(E)) return {stringObject(sl), ctx_.getPointerType(ctx_.CharTy)};
    if (isa<ImplicitValueInitExpr>(E)) return zeroOf(T);
    if (isa<CompoundLiteralExpr>(E) && isScalarTy(T)) return load(genL(E));
    if (auto *va = dyn_cast<VAArgExpr>(E)) {  // next 8-byte slot of the caller's block
      LV ap;
      if (va->getSubExpr()->getType()->isArrayType()) { ap.p = genL(va->getSubExpr()).p; ap.t = ctx_.VoidPtrTy; }
      else { ap.p = genR(va->getSubExpr()).n; ap.t = ctx_.VoidPtrTy; }  // a `va_list` parameter is a pointer to the list
      accessChecks({ap.p, ctx_.VoidPtrTy, false, false, false}, 8, "r");
      std::string cur = def("core.load " + ap.p + " : ptr", "va");
      QualType vt = va->getType();
      if (!isScalarTy(vt)) fail(E, "va_arg of type '" + vt.getAsString() + "'");
      emit("core.check.null " + cur);
      V v = load({cur, vt, false, false, false});
      std::string next = def("core.ptr_add " + cur + ", " + c64(8) + " {waived=\"next variable-argument slot\"} : ptr", "va");
      emit("core.store " + next + ", " + ap.p + " {waived=\"object known\"}");
      return v;
    }
    if (isa<ArrayInitIndexExpr>(E)) return konst(static_cast<int64_t>(arrIdx_), T);
    if (isa<CXXThisExpr>(E)) {
      if (thisCap_) return {def("core.load " + fieldAddr(this_, thisCap_) + " {waived=\"object known\"} : ptr", "this"), T};  // `this` of the enclosing method, captured
      if (this_.empty()) fail(E, "this outside a method");
      return {this_, T};
    }
    if (auto *bl = dyn_cast<CXXBoolLiteralExpr>(E)) return {toBool(konst(bl->getValue() ? 1 : 0, ctx_.IntTy)), T};
    if (isa<CXXNullPtrLiteralExpr>(E)) return zeroOf(ctx_.VoidPtrTy);
    if (auto *ewc = dyn_cast<ExprWithCleanups>(E)) return genR(ewc->getSubExpr());
    if (auto *dae = dyn_cast<CXXDefaultArgExpr>(E)) return genR(dae->getExpr());
    if (auto *die = dyn_cast<CXXDefaultInitExpr>(E)) return genR(die->getExpr());
    if (auto *bt = dyn_cast<CXXBindTemporaryExpr>(E)) {
      V v = genR(bt->getSubExpr());
      registerTemp(v.n, bt->getType());
      return v;
    }
    if (auto *mte = dyn_cast<MaterializeTemporaryExpr>(E)) {
      if (isRecordTy(T)) return {genL(E).p, T};
      return load(genL(E));
    }
    if (auto *cx = dyn_cast<CXXConstructExpr>(E)) {
      LV l = genL(cx);
      return {l.p, T};
    }
    if (isa<CXXStdInitializerListExpr>(E)) return {genL(E).p, T};  // e.g. a `{1, 2, 3}` call argument bound to std::initializer_list<T>
    if (auto *ne = dyn_cast<CXXNewExpr>(E)) return genNew(ne);
    if (auto *de = dyn_cast<CXXDeleteExpr>(E)) { genDelete(de); return {"", ctx_.VoidTy}; }
    if (auto *te = dyn_cast<CXXThrowExpr>(E)) { genThrow(te); return {"", ctx_.VoidTy}; }
    if (isa<AddrLabelExpr>(E)) {  // &&label (e.g. a _THIS_IP_ macro): only its value as an identifier matters; computed goto is not supported
      V z = konst(static_cast<int64_t>(0x1000 + 16 * (E->getBeginLoc().getRawEncoding() & 0xffff)), ctx_.LongTy);
      return {def("core.int_to_ptr " + z.n + " : ptr"), E->getType()};
    }
    if (auto *snt = dyn_cast<SubstNonTypeTemplateParmExpr>(E)) return genR(snt->getReplacement());  // a template non-type parameter already resolved to its argument
    if (auto *tt = dyn_cast<TypeTraitExpr>(E)) {  // e.g. __is_trivially_copyable(T): resolved by Sema at parse time for non-dependent code
      if (tt->isValueDependent()) fail(E, "value-dependent type trait");
      return {toBool(konst(tt->getValue() ? 1 : 0, ctx_.IntTy)), T};
    }
    if (auto *ae = dyn_cast<AtomicExpr>(E)) return genAtomic(ae);
    if (auto *il = dyn_cast<InitListExpr>(E); il && isScalarTy(T)) {  // scalar braced-init used as a value, e.g. `std::uint64_t{p1}`
      if (il->getNumInits() == 0) return zeroOf(T);
      return genR(il->getInit(0));
    }
    fail(E, std::string("expression of kind ") + E->getStmtClassName());
  }
  V zeroOf(QualType t) {
    if (t.getCanonicalType()->isPointerType() || t.getCanonicalType()->isNullPtrType()) {  // std::nullptr_t is not isPointerType() in clang's type system, but it is "ptr" in ty()/core IR
      V z = konst(0, ctx_.LongTy);
      return {def("core.int_to_ptr " + z.n + " : ptr"), t};
    }
    if (t.getCanonicalType()->isBooleanType()) {
      V z = konst(0, ctx_.IntTy);
      return {toBool(z), t};
    }
    return konst(0, t);
  }

  V genCast(const CastExpr *ce) {
    const Expr *sub = ce->getSubExpr();
    QualType to = ce->getType();
    switch (ce->getCastKind()) {
      case CK_LValueToRValue: {
        if (!isScalarTy(to)) fail(ce, "use of an aggregate as a value");
        return load(genL(sub));
      }
      case CK_NoOp: return genR(sub);
      case CK_ToVoid:  // evaluated for its side effects only: an lvalue is not even read
        if (sub->isGLValue()) { genL(sub); return {"", ctx_.VoidTy}; }
        if (sub->getType()->isVoidType()) return genR(sub);
        // A record-typed rvalue here is almost always Sema's own `CK_LValueToRValue ... part_of_explicit_cast`
        // wrapper around a genuinely addressable aggregate (e.g. `(void)*structPtr;`): genR can't represent an
        // aggregate as a scalar Value, but genL already knows to unwrap exactly this cast (see the `CK_LValueToRValue
        // && !isScalarTy` rule above) and hand back its address without "loading" anything — which is all a
        // discarded-for-side-effects aggregate needs.
        if (isRecordTy(sub->getType())) { genL(sub); return {"", ctx_.VoidTy}; }
        genR(sub);
        return {"", ctx_.VoidTy};
      case CK_ArrayToPointerDecay: return {genL(sub).p, to};
      case CK_IntegralCast: return convInt(genR(sub), to);
      case CK_IntegralToFloating: case CK_FloatingToIntegral: case CK_FloatingCast: case CK_FloatingToBoolean:
        return convFlt(genR(sub), to);
      case CK_IntegralToBoolean: case CK_PointerToBoolean: { V v = genR(sub); return {toBool(v), to}; }
      case CK_BooleanToSignedIntegral: { V v = genR(sub); return convInt(v, to); }
      case CK_NullToPointer: {
        genR(sub);
        return zeroOf(to);
      }
      case CK_BitCast: case CK_LValueBitCast: {
        if (auto co = genContainerOf(to, sub)) return {*co, to};
        V v = genR(sub);
        return {v.n, to};
      }
      case CK_IntegralToPointer: {
        V v = genR(sub);
        return {def("core.int_to_ptr " + to64(v) + " : ptr"), to};
      }
      case CK_PointerToIntegral: {
        V v = genR(sub);
        V i = {def("core.ptr_to_int " + v.n + " : i64"), ctx_.UnsignedLongTy};
        return convInt(i, to);
      }
      case CK_FunctionToPointerDecay: case CK_BuiltinFnToFnPtr: return {funcValue(sub), to};
      case CK_DerivedToBase: case CK_UncheckedDerivedToBase: {  // pointer to derived -> pointer to base
        V v = genR(sub);
        QualType from = v.t.getCanonicalType()->isPointerType() ? v.t->getPointeeType() : v.t;
        return {adjustPtr(v.n, from, ce, false), to};
      }
      case CK_BaseToDerived: {
        V v = genR(sub);
        QualType from = v.t.getCanonicalType()->isPointerType() ? v.t->getPointeeType() : v.t;
        return {adjustPtr(v.n, from, ce, true), to};
      }
      case CK_UserDefinedConversion: case CK_ConstructorConversion: return genR(sub);
      // _Atomic(T) <-> T. Under the engine's single-thread exploration these change the TYPE, not the
      // value; refusing them stopped whole functions from lowering (see coreTy).
      case CK_AtomicToNonAtomic: case CK_NonAtomicToAtomic: { V v = genR(sub); return {v.n, to}; }
      case CK_Dynamic: return {genDynCast(cast<CXXDynamicCastExpr>(ce)), to};
      default: fail(ce, std::string("cast kind ") + ce->getCastKindName());
    }
  }
  // value of a function designator: its address (`f`, `&f`, `*fp`)
  std::string funcValue(const Expr *e) {
    e = e->IgnoreParens();
    if (auto *dr = dyn_cast<DeclRefExpr>(e))
      if (auto *fd = dyn_cast<FunctionDecl>(dr->getDecl())) {
        ensureDeclared(fd);
        return def("core.func_addr @" + fnName(fd) + " : ptr", "f");
      }
    if (auto *uo = dyn_cast<UnaryOperator>(e))
      if (uo->getOpcode() == UO_Deref) return genR(uo->getSubExpr()).n;
    if (auto *ce = dyn_cast<CastExpr>(e))
      if (ce->getCastKind() == CK_FunctionToPointerDecay || ce->getCastKind() == CK_NoOp) return funcValue(ce->getSubExpr());
    // Any other lvalue of function type (e.g. a `Functor&&` forwarding-reference parameter bound directly to a
    // named function, as libstdc++'s `std::function` constructor does internally): `genL` already resolves such
    // an lvalue to the function's code address in `lv.p` (either via the DeclRefExpr/FunctionDecl branch above,
    // or by loading a reference slot that itself holds that address) - no further load is needed on top of it,
    // unlike an ordinary data lvalue.
    if (e->getType()->isFunctionType()) return genL(e).p;
    fail(e, "function designator");
  }

  std::string cmpName(BinaryOperatorKind k, bool sg) {
    switch (k) {
      case BO_EQ: return "eq";
      case BO_NE: return "ne";
      case BO_LT: return sg ? "slt" : "ult";
      case BO_LE: return sg ? "sle" : "ule";
      case BO_GT: return sg ? "sgt" : "ugt";
      default: return sg ? "sge" : "uge";
    }
  }
  bool isNullConst(const Expr *e) { return e->isNullPointerConstant(ctx_, Expr::NPC_ValueDependentIsNotNull) != Expr::NPCK_NotNull; }

  // condition -> core bool
  std::string genCond(const Expr *E) {
    at(E);
    E = E->IgnoreParens();
    if (auto *bo = dyn_cast<BinaryOperator>(E)) {
      if (bo->isComparisonOp()) return genCompare(bo);
      if (bo->getOpcode() == BO_LAnd || bo->getOpcode() == BO_LOr) return genLogical(bo);
    }
    if (auto *uo = dyn_cast<UnaryOperator>(E))
      if (uo->getOpcode() == UO_LNot) return def("core.not " + genCond(uo->getSubExpr()) + " : bool");
    return toBool(genR(E));
  }
  std::string genCompare(const BinaryOperator *bo) {
    const Expr *l = bo->getLHS(), *r = bo->getRHS();
    QualType lt = l->getType().getCanonicalType();
    if (lt->isPointerType() || r->getType().getCanonicalType()->isPointerType()) {
      bool eq = bo->getOpcode() == BO_EQ || bo->getOpcode() == BO_NE;
      // `ptr == 0`/`ptr != 0`: true pointer-value equality (object and offset), not core.is_null's object-only
      // check -- see ptrIsExactlyNull's comment. genR of the null-constant side still runs (it's a cheap
      // core.int_to_ptr of 0), so this costs nothing beyond what the general core.ptr_cmp path below already does.
      if (eq && (isNullConst(l) || isNullConst(r))) {
        V v = isNullConst(l) ? genR(r) : genR(l);
        std::string n = ptrIsExactlyNull(v.n);
        return bo->getOpcode() == BO_EQ ? n : def("core.not " + n + " : bool");
      }
      V a = genR(l), b = genR(r);
      if (!eq) emit("core.check.ptr_cmp " + a.n + ", " + b.n);
      // offsets inside an object are signed: `p - 1 < base` is true when p == base
      return def("core.ptr_cmp " + cmpName(bo->getOpcode(), true) + " " + a.n + ", " + b.n + " : bool");
    }
    V a = genR(l), b = genR(r);
    if (isFlt(lt)) {
      const char *pr = nullptr;
      switch (bo->getOpcode()) {
        case BO_EQ: pr = "oeq"; break; case BO_NE: pr = "une"; break; case BO_LT: pr = "olt"; break;
        case BO_LE: pr = "ole"; break; case BO_GT: pr = "ogt"; break; default: pr = "oge"; break;
      }
      return fop(std::string("cmp.") + pr, {a.n, b.n}, lt, ctx_.BoolTy).n;
    }
    return def("core.icmp " + cmpName(bo->getOpcode(), isSigned(lt)) + " " + a.n + ", " + b.n + " : bool");
  }
  std::string genLogical(const BinaryOperator *bo) {
    bool isAnd = bo->getOpcode() == BO_LAnd;
    std::string l = genCond(bo->getLHS());
    size_t rhs = newBlock("rhs"), end = newBlock("end");
    std::string res = fresh("r");
    blocks_[end].params = res + ": bool";
    term("core.cond_br " + l + ", " + bname(isAnd ? rhs : end) + (isAnd ? "" : "(" + l + ")") + ", " +
         bname(isAnd ? end : rhs) + (isAnd ? "(" + l + ")" : ""));
    setBlock(rhs);
    pushScope();  // temporaries of the conditionally evaluated operand end with it (they do not dominate the code after the `&&`)
    std::string r = genCond(bo->getRHS());
    popScope(true);
    term("core.br " + bname(end) + "(" + r + ")");
    setBlock(end);
    return res;
  }

  V genUnary(const UnaryOperator *uo) {
    QualType T = uo->getType();
    switch (uo->getOpcode()) {
      case UO_Plus: case UO_Extension: return genR(uo->getSubExpr());
      case UO_Minus: {
        V v = genR(uo->getSubExpr());
        if (isFlt(T)) return fop("neg", {v.n}, T, T);
        bool ov = isSigned(T) && bits(T) >= 32 && !mod_.wrapSigned;
        if (ov) emit("core.check.sneg_ovf " + v.n);
        return {def("core.neg " + v.n + (ov ? " {sov}" : "") + " : " + ty(T)), T};
      }
      case UO_Not: { V v = genR(uo->getSubExpr()); return {def("core.not " + v.n + " : " + ty(T)), T}; }
      case UO_LNot: return fromBool(genCond(uo), uo->getType());
      case UO_AddrOf: {
        const Expr *s = uo->getSubExpr()->IgnoreParens();
        if (auto *dr = dyn_cast<DeclRefExpr>(s))
          if (isa<FunctionDecl>(dr->getDecl())) return {funcValue(s), T};
        const ArraySubscriptExpr *outer = addrOfSubscript_;
        addrOfSubscript_ = dyn_cast<ArraySubscriptExpr>(s);
        LV lv = genL(uo->getSubExpr());
        addrOfSubscript_ = outer;
        if (lv.bit) fail(uo, "address of a bit-field");
        return {lv.p, T};
      }
      case UO_Deref: return load(genL(uo));
      case UO_PreInc: case UO_PreDec: case UO_PostInc: case UO_PostDec: return genIncDec(uo, nullptr);
      default: fail(uo, "unary operator");
    }
  }
  V genIncDec(const UnaryOperator *uo, LV *lvOut) {
    QualType T = uo->getType();
    (void)T;
    {
      {
        bool inc = uo->getOpcode() == UO_PreInc || uo->getOpcode() == UO_PostInc;
        bool pre = uo->getOpcode() == UO_PreInc || uo->getOpcode() == UO_PreDec;
        LV lv = genL(uo->getSubExpr());
        if (lvOut) *lvOut = lv;
        V old = load(lv);
        V nw;
        QualType lt = lv.t.getCanonicalType();
        if (lt->isPointerType()) {
          QualType pet = lt->getPointeeType();
          if (pet->isVariableArrayType()) {
            std::string off = vlaFlatBytes(pet);
            nw = {ptrAdd(old.n, inc ? off : def("core.neg " + off + " : i64")), lv.t};
          } else {
            nw = {ptrAdd(old.n, c64((inc ? 1 : -1) * static_cast<int64_t>(sizeOf(pet)))), lv.t};
          }
        } else if (lt->isBooleanType()) {
          fail(uo, "increment of _Bool");
        } else {
          nw = arith(inc ? BO_Add : BO_Sub, old, konst(1, lv.t), lv.t);
        }
        store(lv, nw);
        return pre ? nw : old;
      }
    }
  }

  // integer arithmetic with the explicit UB checks of §18.4
  V arith(BinaryOperatorKind k, V a, V b, QualType T) {
    if (isFlt(T)) {
      const char *fk = k == BO_Add ? "add" : k == BO_Sub ? "sub" : k == BO_Mul ? "mul" : k == BO_Div ? "div" : nullptr;
      if (!fk) fail(nullptr, "floating point binary operator");
      return fop(fk, {a.n, b.n}, T, T);
    }
    bool sg = isSigned(T);
    bool ov = sg && bits(T) >= 32 && !mod_.wrapSigned;
    const char *chk = nullptr, *op = nullptr;
    switch (k) {
      case BO_Add: op = "add"; chk = "sadd_ovf"; break;
      case BO_Sub: op = "sub"; chk = "ssub_ovf"; break;
      case BO_Mul: op = "mul"; chk = "smul_ovf"; break;
      case BO_And: op = "and"; break;
      case BO_Or: op = "or"; break;
      case BO_Xor: op = "xor"; break;
      case BO_Div: case BO_Rem: {
        emit("core.check.div " + a.n + ", " + b.n + (sg ? " {signed}" : ""));
        const char *o = k == BO_Div ? (sg ? "sdiv" : "udiv") : (sg ? "srem" : "urem");
        return {def(std::string("core.") + o + " " + a.n + ", " + b.n + " : " + ty(T)), T};
      }
      case BO_Shl: case BO_Shr: {
        std::string s = shiftCount(b, T);
        emit("core.check.shift " + a.n + ", " + s + (k == BO_Shl && sg ? " {signed_left}" : ""));
        const char *o = k == BO_Shl ? "shl" : (sg ? "ashr" : "lshr");
        return {def(std::string("core.") + o + " " + a.n + ", " + s + " : " + ty(T)), T};
      }
      default: fail(nullptr, "binary operator");
    }
    if (ov && chk) emit(std::string("core.check.") + chk + " " + a.n + ", " + b.n);
    return {def(std::string("core.") + op + " " + a.n + ", " + b.n + (ov && chk ? " {sov}" : "") + " : " + ty(T)), T};
  }
  // __atomic_*/__c11_atomic_*/__sync_* builtins (used by std::shared_ptr's refcount, std::atomic<T>, ...):
  // the interpreter is single-threaded, so every atomic op reduces to its plain, non-atomic equivalent
  // on the same memory. Pointer-vs-value argument shape is read off the AST (Sema already resolved it
  // per the specific builtin), not guessed from the opcode name.
  V genAtomic(const AtomicExpr *ae) {
    QualType valTy = ae->getValueType();
    LV loc{genR(ae->getPtr()).n, valTy, false, false, false};
    auto asValue = [&](const Expr *a) -> V {  // some builtins pass the operand by value, others pass a pointer to it
      if (a->getType()->isPointerType() && !valTy->isPointerType()) return load({genR(a).n, valTy, false, false, false});
      return genR(a);
    };
    StringRef op = ae->getOpAsString();
    AtomicExpr::AtomicOp aop = ae->getOp();
    if (aop == AtomicExpr::AO__c11_atomic_init || op.ends_with("_store") || op.ends_with("_store_n") || op == "__atomic_init") {
      store(loc, asValue(ae->getVal1()));
      return {"", ctx_.VoidTy};
    }
    if (op.ends_with("_load") || op.ends_with("_load_n")) {
      V v = load(loc);
      if (!op.ends_with("_load_n") && ae->getOp() != AtomicExpr::AO__c11_atomic_load && ae->getOp() != AtomicExpr::AO__opencl_atomic_load && ae->getOp() != AtomicExpr::AO__hip_atomic_load) {
        store({genR(ae->getVal1()).n, valTy, false, false, false}, v);  // GNU __atomic_load(ptr, ret, order): ret is an out-pointer
        return {"", ctx_.VoidTy};
      }
      return v;
    }
    if (op.contains("compare_exchange")) {
      V expectedPtr = genR(ae->getVal1());
      V expected = load({expectedPtr.n, valTy, false, false, false});
      V desired = asValue(ae->getVal2());
      V cur = load(loc);
      std::string eq = def("core.icmp eq " + cur.n + ", " + expected.n + " : bool", "eq");
      size_t tb = newBlock("cx_eq"), fb = newBlock("cx_ne"), end = newBlock("cx_end");
      std::string res = fresh("r");
      blocks_[end].params = res + ": bool";
      term("core.cond_br " + eq + ", " + bname(tb) + ", " + bname(fb));
      setBlock(tb);
      store(loc, desired);
      std::string ok = toBool(konst(1, ctx_.IntTy));
      term("core.br " + bname(end) + "(" + ok + ")");
      setBlock(fb);
      store({expectedPtr.n, valTy, false, false, false}, cur);
      std::string no = toBool(konst(0, ctx_.IntTy));
      term("core.br " + bname(end) + "(" + no + ")");
      setBlock(end);
      return {res, ae->getType()};
    }
    if (op.contains("exchange")) {
      V old = load(loc);
      // Only AO__atomic_exchange/AO__scoped_atomic_exchange carry a Val2 (the out-pointer for the old value); every other
      // "*_exchange" builtin (__c11_atomic_exchange, __opencl_atomic_exchange, __hip_atomic_exchange, *_exchange_n) passes
      // the new value directly and returns the old one as the expression result, with no Val2 slot at all — calling
      // ae->getVal2() on one of those trips clang's own `NumSubExprs > VAL2` assertion. `op.ends_with("_exchange")` matched
      // __c11_atomic_exchange too (it also literally ends with "_exchange"), which crashed the frontend on real code (curl's
      // `lib/easy.c` uses __c11_atomic_exchange for its connection-cache spinlock).
      if (aop == AtomicExpr::AO__atomic_exchange || aop == AtomicExpr::AO__scoped_atomic_exchange) {
        store(loc, asValue(ae->getVal1()));
        store({genR(ae->getVal2()).n, valTy, false, false, false}, old);
        return {"", ctx_.VoidTy};
      }
      store(loc, asValue(ae->getVal1()));
      return old;
    }
    BinaryOperatorKind k;
    bool fetchFirst = op.starts_with("__atomic_fetch_") || op.starts_with("__c11_atomic_fetch_") || op.starts_with("__opencl_atomic_fetch_") || op.starts_with("__scoped_atomic_fetch_");
    // Two mirrored families, and only one of them parsed here before:
    //   __atomic_fetch_add(p, v, m)   returns the OLD value  -> fetchFirst, name ends in the operation
    //   __atomic_add_fetch(p, v, m)   returns the NEW value  -> name ends in `_fetch`
    // Taking the token after the last `_` gives "fetch" for the whole second family, so every one of
    // them came out `unsupported: atomic operation '__atomic_add_fetch'` and the ENCLOSING function
    // stayed a declaration -- libgit2's git_atomic32_inc, and with it every refcount it guards,
    // became an opaque external in the libgit2 scan (Sec.22.489).
    StringRef suffix = op.substr(op.rfind('_') + 1);
    if (suffix == "fetch" && !fetchFirst) {
      StringRef head = op.substr(0, op.size() - 6);   // drop "_fetch"
      suffix = head.substr(head.rfind('_') + 1);
    }
    if (suffix == "add") k = BO_Add;
    else if (suffix == "sub") k = BO_Sub;
    else if (suffix == "and") k = BO_And;
    else if (suffix == "or") k = BO_Or;
    else if (suffix == "xor") k = BO_Xor;
    else if (suffix == "nand") {
      V old = load(loc);
      V anded = arith(BO_And, old, asValue(ae->getVal1()), valTy);
      V nv = {def("core.not " + anded.n + " : " + ty(valTy)), valTy};
      store(loc, nv);
      return fetchFirst ? old : nv;
    } else { fail(ae, "atomic operation '" + op.str() + "'"); return {"", valTy}; }
    V old = load(loc);
    V nv = arith(k, old, asValue(ae->getVal1()), valTy);
    store(loc, nv);
    return fetchFirst ? old : nv;
  }
  std::string shiftCount(V s, QualType lhsT) {
    unsigned wl = bits(lhsT), wr = bits(s.t);
    if (wr == wl) return s.n;
    if (wr < wl) return convInt(s, lhsT).n;
    // wider count: clamp so the truncation cannot turn a huge count into a small one
    std::string big = konst(255, s.t).n;
    std::string gt = def("core.icmp ugt " + s.n + ", " + big + " : bool");
    std::string sel = def("core.select " + gt + ", " + big + ", " + s.n + " : " + ty(s.t));
    return def("core.trunc " + sel + " : " + ty(lhsT));
  }

  V genBinary(const BinaryOperator *bo) {
    QualType T = bo->getType();
    BinaryOperatorKind k = bo->getOpcode();
    if (bo->isComparisonOp()) return fromBool(genCompare(bo), bo->getType());
    if (k == BO_LAnd || k == BO_LOr) return fromBool(genLogical(bo), bo->getType());
    if (k == BO_Comma) {
      genR(bo->getLHS());
      return genR(bo->getRHS());
    }
    if (k == BO_Assign) return genAssign(bo);
    if (bo->isCompoundAssignmentOp()) return genCompound(cast<CompoundAssignOperator>(bo));
    QualType lt = bo->getLHS()->getType().getCanonicalType(), rt = bo->getRHS()->getType().getCanonicalType();
    if (lt->isPointerType() || rt->isPointerType()) {
      V a = genR(bo->getLHS()), b = genR(bo->getRHS());
      if (lt->isPointerType() && rt->isPointerType()) {  // ptr - ptr
        emit("core.check.ptr_cmp " + a.n + ", " + b.n);
        std::string d = def("core.ptr_diff " + a.n + ", " + b.n + " : i64");
        QualType pet = lt->getPointeeType();
        if (!pet->isVariableArrayType()) {
          uint64_t es = sizeOf(pet);
          if (es == 1) return {d, T};
          std::string sz = c64(static_cast<int64_t>(es));
          emit("core.check.div " + d + ", " + sz + " {signed}");
          return {def("core.sdiv " + d + ", " + sz + " : i64"), T};
        }
        std::string sz = vlaFlatBytes(pet);
        emit("core.check.div " + d + ", " + sz + " {signed}");
        return {def("core.sdiv " + d + ", " + sz + " : i64"), T};
      }
      V p = lt->isPointerType() ? a : b, i = lt->isPointerType() ? b : a;
      QualType pet = p.t.getCanonicalType()->getPointeeType();
      std::string off = pet->isVariableArrayType() ? scaleDyn(i, vlaFlatBytes(pet)) : scale(i, sizeOf(pet));
      if (k == BO_Sub) off = def("core.neg " + off + " : i64");
      return {ptrAdd(p.n, off), T};
    }
    V a = genR(bo->getLHS()), b = genR(bo->getRHS());
    return arith(k, a, b, T);
  }

  V genAssign(const BinaryOperator *bo, LV *lvOut = nullptr) {
    QualType lt = bo->getLHS()->getType();
    if (!isScalarTy(lt)) {
      if (!lt->isRecordType()) fail(bo, "assignment of type '" + lt.getAsString() + "'");
      LV s = genL(bo->getRHS()), d = genL(bo->getLHS());
      if (!d.direct) emit("core.check.const_write " + d.p);
      copyBytes(d, s, sizeOf(lt));
      if (lvOut) *lvOut = d;
      return {d.p, lt};
    }
    V v = genR(bo->getRHS());
    LV dl = genL(bo->getLHS());
    store(dl, v);
    if (lvOut) *lvOut = dl;
    return v;
  }
  V genCompound(const CompoundAssignOperator *ca, LV *lvOut = nullptr) {
    LV lv = genL(ca->getLHS());
    lv.rmw = true;   // one access, read and written: see LV::rmw
    if (lvOut) *lvOut = lv;
    QualType lt = lv.t.getCanonicalType();
    V old = load(lv);
    V res;
    if (lt->isPointerType()) {
      V b = genR(ca->getRHS());
      QualType pet = lt->getPointeeType();
      std::string off = pet->isVariableArrayType() ? scaleDyn(b, vlaFlatBytes(pet)) : scale(b, sizeOf(pet));
      if (ca->getOpcode() == BO_SubAssign) off = def("core.neg " + off + " : i64");
      res = {ptrAdd(old.n, off), lv.t};
    } else {
      QualType ct = ca->getComputationResultType();
      V a = convInt(old, ca->getComputationLHSType());
      V b = genR(ca->getRHS());
      V r = arith(BinaryOperator::getOpForCompoundAssignment(ca->getOpcode()), a, b, ct);
      res = convInt(r, lv.t);
    }
    store(lv, res);
    return res;
  }
  V genCondOp(const ConditionalOperator *co) {
    QualType T = co->getType();
    if (isRecordTy(T)) {  // a class prvalue: both arms construct into one temporary
      std::string slot = newSlot(T, "cond", false);
      std::string c = genCond(co->getCond());
      size_t tb = newBlock("then"), eb = newBlock("else"), end = newBlock("end");
      term("core.cond_br " + c + ", " + bname(tb) + ", " + bname(eb));
      setBlock(tb);
      pushScope();
      initObject({slot, T, true, false, false}, co->getTrueExpr());
      popScope(true);
      term("core.br " + bname(end));
      setBlock(eb);
      pushScope();
      initObject({slot, T, true, false, false}, co->getFalseExpr());
      popScope(true);
      term("core.br " + bname(end));
      setBlock(end);
      registerTemp(slot, T);
      return {slot, T};
    }
    if (!isScalarTy(T) && !T->isVoidType()) fail(co, "?: with a non-scalar type");
    std::string c = genCond(co->getCond());
    size_t tb = newBlock("then"), eb = newBlock("else"), end = newBlock("end");
    std::string res = fresh("r");
    if (!T->isVoidType()) blocks_[end].params = res + ": " + ty(T);
    term("core.cond_br " + c + ", " + bname(tb) + ", " + bname(eb));
    setBlock(tb);
    pushScope();
    V a = genR(co->getTrueExpr());
    popScope(true);
    term("core.br " + bname(end) + (T->isVoidType() ? "" : "(" + a.n + ")"));
    setBlock(eb);
    pushScope();
    V b = genR(co->getFalseExpr());
    popScope(true);
    term("core.br " + bname(end) + (T->isVoidType() ? "" : "(" + b.n + ")"));
    setBlock(end);
    return {T->isVoidType() ? "" : res, T};
  }
  // GNU `a ?: b`: a is evaluated once
  V genElvis(const BinaryConditionalOperator *bc) {
    QualType T = bc->getType();
    if (!isScalarTy(T)) fail(bc, "?: with a non-scalar type");
    V common = genR(bc->getCommon());
    opaque_[bc->getOpaqueValue()] = common;
    std::string c = toBool(common);
    size_t tb = newBlock("then"), eb = newBlock("else"), end = newBlock("end");
    std::string res = fresh("r");
    blocks_[end].params = res + ": " + ty(T);
    term("core.cond_br " + c + ", " + bname(tb) + ", " + bname(eb));
    setBlock(tb);
    pushScope();
    V a = genR(bc->getTrueExpr());
    popScope(true);
    term("core.br " + bname(end) + "(" + a.n + ")");
    setBlock(eb);
    pushScope();
    V b = genR(bc->getFalseExpr());
    popScope(true);
    term("core.br " + bname(end) + "(" + b.n + ")");
    setBlock(end);
    return {res, T};
  }
  // GNU statement expression ({ ...; value; })
  V genStmtExpr(const StmtExpr *se) {
    const CompoundStmt *cs = se->getSubStmt();
    pushScope();
    V last{"", ctx_.VoidTy};
    for (auto it = cs->body_begin(); it != cs->body_end(); ++it) {
      if (std::next(it) == cs->body_end()) {
        const Stmt *st = *it;
        while (auto *ls = dyn_cast<LabelStmt>(st)) {  // `({ ...; out: value; })`: the label belongs to the value's block
          size_t b = labelBlock(ls->getDecl());
          if (!blocks_[curBlock_].done) term("core.br " + bname(b));
          setBlock(b);
          st = ls->getSubStmt();
        }
        if (auto *e = dyn_cast<Expr>(st)) { last = genR(e); break; }
        stmt(st);
        continue;
      }
      stmt(*it);
    }
    popScope(false);
    return last;
  }

  // ------------------------------------------------------------------ calls
  // Arguments for a call: references get the address of the object, class objects passed by value are constructed in a
  // temporary the caller destroys after the call, everything else is a value. Arguments of a variadic tail are evaluated
  // but not passed.
  std::vector<std::string> evalArgsFor(const std::vector<const Expr *> &argv, const FunctionDecl *callee, const FunctionProtoType *fpt) {
    std::vector<std::string> out;
    unsigned nparams = callee ? callee->getNumParams() : (fpt ? fpt->getNumParams() : 0);
    bool vaBlock = callee && passesVaBlock(callee);
    std::vector<V> vaVals;
    for (unsigned i = 0; i < argv.size(); ++i) {
      const Expr *a = argv[i];
      bool fixed = i < nparams;
      QualType pt = fixed ? (callee ? callee->getParamDecl(i)->getType() : fpt->getParamType(i)) : a->getType();
      if (fixed && pt->isReferenceType()) {
        out.push_back(genL(a).p);
        continue;
      }
      if (isRecordTy(a->getType())) {
        if (!fixed) { genL(a); continue; }
        QualType t = a->getType();
        std::string slot = newSlot(t, "byval", false);
        initObject({slot, t, true, false, false}, a);
        registerTemp(slot, t);
        out.push_back(slot);
        continue;
      }
      V v = genR(a);
      if (fixed) out.push_back(v.n);
      else if (vaBlock) {  // default argument promotions, then one 8-byte slot each
        QualType at = a->getType();
        if (at->isArrayType()) at = ctx_.getPointerType(ctx_.getAsArrayType(at)->getElementType());
        else if (ctx_.isPromotableIntegerType(at)) { v = convInt(v, ctx_.getPromotedIntegerType(at)); at = v.t; }
        if (!isScalarTy(at)) fail(a, "a variable argument of type '" + at.getAsString() + "'");
        vaVals.push_back({v.n, at});
      }
    }
    if (vaBlock) {
      if (vaVals.empty()) out.push_back(zeroOf(ctx_.VoidPtrTy).n);
      else {
        std::string blk = def("core.alloca {size=" + std::to_string(8 * vaVals.size()) + ", align=8, name=\"varargs\"} : ptr", "va");
        for (size_t k = 0; k < vaVals.size(); ++k) {
          emit("core.memset " + inObj(blk, 8 * k) + ", " + def("core.const 0 : i8", "c") + ", " + c64(8));
          emit("core.store " + vaVals[k].n + ", " + inObj(blk, 8 * k) + " {waived=\"in-bounds by construction\"}");
        }
        out.push_back(blk);
      }
    }
    return out;
  }
  // The one chokepoint every ordinary direct call, virtual call, and `operator new`/`operator delete` call funnels
  // through (see genCallImpl/genVirtualCall/the `new`/`delete` lowering). In a C++ translation unit, every call
  // made here might leave an exception in flight (see "cross-function exception propagation" above `genTry`):
  // after the `core.call`, check for one and dispatch to a matching local `catch` or propagate further before
  // letting the caller of `emitCall` use the (otherwise meaningless, if an exception did escape) result value.
  V emitCall(const std::string &callee, std::vector<std::string> args, QualType ret, const std::string &dest = "") {
    std::string slot;
    if (isRecordTy(ret)) {
      slot = dest.empty() ? newSlot(ret, "sret") : dest;
      args.insert(args.begin(), slot);
    }
    std::string a;
    for (size_t i = 0; i < args.size(); ++i) a += (i ? ", " : "") + args[i];
    V result;
    if (ret->isVoidType() || !slot.empty()) {
      emit("core.call " + callee + "(" + a + ")");
      result = {slot, ret};
    } else {
      result = {def("core.call " + callee + "(" + a + ") : " + ty(ret), "r"), ret};
    }
    if (isCxxCtx(ctx_)) {
      std::string ev = def("core.load " + excObjSlot() + " {waived=\"object known\"} : ptr", "ev");
      std::string isn = def("core.is_null " + ev + " : bool", "isn");
      size_t okB = newBlock("call_ok"), excB = newBlock("call_exc");
      term("core.cond_br " + isn + ", " + bname(okB) + ", " + bname(excB));
      setBlock(excB);
      genExceptionDispatch();
      setBlock(okB);
    }
    return result;
  }

  // A call to a function declared noreturn (attribute / _Noreturn / [[noreturn]]): the call is lowered as usual (a body that is linked in is
  // analysed, a declaration is an opaque/modelled call) and the program ends after it: the code that follows is not reachable.
  // Thread/work creation: `pthread_create`, `kthread_run`, ... take a callback and a data pointer and the callback
  // runs CONCURRENTLY. Without a model the create call is an opaque external, so the callback is never executed
  // from here at all and everything it would write stays unwritten -- a whole subsystem (every QNX resmgr that
  // spawns its workers in main, every driver whose module_init starts a kthread) is simply invisible.
  //
  // `--spawn-callbacks` emits a direct call to the callback, once, where the creation happens. That is a WIDENING
  // in coverage (the body becomes reachable) and a NARROWING in sequencing (it pretends the thread ran to
  // completion at that exact point, so no interleaving is analysed) -- the report names it. A real race still
  // needs the deliberate injection harness; this only stops the body from being a blind spot.
  //
  // Only applied when the callback argument resolves to exactly ONE function with a body: `fnRefs` is the same
  // resolver the vtable-binding collector uses, so `kthread_run(my_fn, data, ...)` works and a callback that comes
  // out of a variable does not (it would be a guess about which function runs).
  struct SpawnShape { const char *name; unsigned fnArg, dataArg, nargsMin; };
  static const SpawnShape *spawnShape(const std::string &n) {
    static const SpawnShape kShapes[] = {
        {"pthread_create", 2, 3, 4},
        {"kthread_create_on_node", 0, 1, 2},
        {"kthread_create_on_cpu", 0, 1, 2},
        {"kthread_run_on_cpu", 0, 1, 2},
    };
    for (auto &sh : kShapes)
      if (n == sh.name) return &sh;
    return nullptr;
  }

  // Emits the callback call for a thread-creation call, if this is one. Returns true if it did.
  bool genSpawnCallback(const CallExpr *call) {
    if (!mod_.spawnCallbacks) return false;
    const FunctionDecl *callee = call->getDirectCallee();
    if (!callee || !callee->getIdentifier()) return false;
    const SpawnShape *sh = spawnShape(callee->getName().str());
    if (!sh || call->getNumArgs() < sh->nargsMin) return false;
    // The function an expression is the address of: `f`, `&f`, `(f)`, a cast of either. Deliberately narrow --
    // anything that needs a guess about WHICH function runs is left alone (the same rule the vtable-binding
    // collector uses, spelled locally because that visitor is declared further down this file).
    std::vector<const FunctionDecl *> cands;
    {
      const Expr *a = call->getArg(sh->fnArg)->IgnoreParenImpCasts();
      for (;;) {
        if (auto *ce2 = dyn_cast<CastExpr>(a)) { a = ce2->getSubExpr()->IgnoreParenImpCasts(); continue; }
        if (auto *uo = dyn_cast<UnaryOperator>(a); uo && uo->getOpcode() == UO_AddrOf) { a = uo->getSubExpr()->IgnoreParenImpCasts(); continue; }
        break;
      }
      if (auto *dr = dyn_cast<DeclRefExpr>(a))
        if (auto *fd = dyn_cast<FunctionDecl>(dr->getDecl()))
          if (fd->hasBody()) cands.push_back(fd->getDefinition() ? fd->getDefinition() : fd);
    }
    if (cands.size() != 1) return false;
    const FunctionDecl *fn = cands.front();
    if (fn->getNumParams() != 1 || !fn->getParamDecl(0)->getType()->isPointerType()) return false;
    V data = genR(call->getArg(sh->dataArg));
    // A non-void call needs a result register even though nothing reads it -- `core.call @f(x) : ptr` on its own
    // is not an op. (The callback's return value is the thread's exit status; no caller here can observe it.)
    if (fn->getReturnType()->isVoidType()) emit("core.call @" + fnName(fn) + "(" + data.n + ")");
    else def("core.call @" + fnName(fn) + "(" + data.n + ") : " + ty(fn->getReturnType()), "sp");
    ++mod_.spawnCallbacksEmitted;
    return true;
  }

  // `noreturn` carried by the callee's TYPE rather than by a FunctionDecl. `__attribute__((noreturn))` is part of
  // the function type (FunctionType::ExtInfo), so it survives on a function POINTER -- which is the only place it can
  // be stated when the call goes through a struct field:
  //
  //     struct netdissect_options { void NORETURN_FUNCPTR (*ndo_error)(netdissect_options *, const char *, ...); };
  //     if (p == NULL) (*ndo->ndo_error)(ndo, "malloc");   /* never returns */
  //     p[0] = ...;                                        /* reached only when p != NULL */
  //
  // Reading only FunctionDecl::isNoReturn() misses this entirely: the indirect call is lowered as an ordinary opaque
  // call, execution continues into code the program says is unreachable, and every dereference guarded that way is
  // reported as a null deref. That is a FALSE POSITIVE on a program that declared the fact in its own header; it
  // showed up on tcpdump's addrtoname.c the moment indirect calls through variadic function-pointer fields stopped
  // killing the path (§22.425). `--noreturn` cannot express it -- it names functions, and there is no function here,
  // only a field whose type says what any callee stored in it must do.
  //
  // This reads the declared TYPE, not a guess: nothing is inferred about which function the pointer holds. If the
  // pointer is assigned a function that does return, the program is already undefined by its own declaration.
  static bool calleeTypeIsNoReturn(const CallExpr *call) {
    const Expr *ce = call->getCallee();
    if (!ce) return false;
    QualType t = ce->IgnoreParenImpCasts()->getType();
    if (t.isNull()) return false;
    if (const auto *pt = t->getAs<clang::PointerType>()) t = pt->getPointeeType();
    else if (const auto *bt = t->getAs<clang::BlockPointerType>()) t = bt->getPointeeType();
    if (t.isNull()) return false;
    const auto *ft = t->getAs<FunctionType>();
    return ft && ft->getNoReturnAttr();
  }

  V genCall(const CallExpr *call, const std::string &dest = "") {
    V r = genCallImpl(call, dest);
    genSpawnCallback(call);
    const FunctionDecl *callee = call->getDirectCallee();
    if (callee && callee->isNoReturn() && callee->getBuiltinID() == 0 && !blocks_[curBlock_].done)
      terminateProgram(callee->getIdentifier() ? callee->getName().str() : "noreturn");
    else if (!callee && calleeTypeIsNoReturn(call) && !blocks_[curBlock_].done)
      terminateProgram("noreturn_funcptr");
    return r;
  }
  V genCallImpl(const CallExpr *call, const std::string &dest = "") {
    // `obj->~T()`/`obj.~T()` where `T` is a scalar/non-class type (a "pseudo-destructor": always a no-op per the
    // standard, since such a type has no destructor to run) is a call whose callee has no FunctionDecl at all —
    // previously unreachable in practice (catch-handler bodies were never lowered before `try`/`catch` support was
    // added, and that is the only place this project's own tests ended up exercising it: libstdc++ vector growth's
    // internal exception-safety rollback path destroys already-constructed elements, including of scalar types,
    // inside a `catch` block). Without this, it fell through to `genIndirectCall`, which has no function-pointer
    // value to call and fails with a confusing "indirect call without a prototype".
    if (auto *pd = dyn_cast<CXXPseudoDestructorExpr>(call->getCallee()->IgnoreParens())) {
      genR(pd->getBase());
      return {"", ctx_.VoidTy};
    }
    const FunctionDecl *callee = call->getDirectCallee();
    if (!callee) return genIndirectCall(call);
    std::string plain = callee->getIdentifier() ? callee->getName().str() : "";
    std::string name = fnName(callee);
    std::string base = plain.rfind("__builtin_", 0) == 0 ? plain.substr(10) : plain;
    // These name-based matches are meant for genuine free-function builtins (C library functions, Clang/GCC
    // `__builtin_*` intrinsics); none of them are ever legitimately a non-static C++ method. `hasThis(callee)`
    // guards against the real collision this project hit: a C++ class with its own method literally named
    // `exit` (e.g. CLI11's `CLI::App::exit(const Error&, ...)`) matched the `base == "exit"` branch below meant
    // for libc's `exit()`, so the method's real (scalar) return type was silently replaced with `void` -
    // surfacing later, confusingly, as "return of an aggregate" at the call site's enclosing `return` statement.
    bool freeFn = !hasThis(callee);
    if (freeFn && (base == "expect" || base == "expect_with_probability")) return genR(call->getArg(0));
    if (freeFn && base == "constant_p") return konst(0, ctx_.IntTy);
    if (freeFn && base == "va_start") {
      if (va_.empty()) fail(call, "va_start in a function without variable arguments");
      std::string ap = genR(call->getArg(0)).n;  // the va_list array decays to a pointer to its first element
      emit("core.store " + va_ + ", " + ap + " {waived=\"object known\"}");
      return {"", ctx_.VoidTy};
    }
    if (freeFn && base == "va_end") { genR(call->getArg(0)); return {"", ctx_.VoidTy}; }
    if (freeFn && base == "va_copy") {
      std::string d = genR(call->getArg(0)).n, sr = genR(call->getArg(1)).n;
      emit("core.memcpy " + d + ", " + sr + ", " + c64(8));
      return {"", ctx_.VoidTy};
    }
    // bit counting (clz/ctz/popcount, any width): sums of single-bit tests, no loop and no branch. clz/ctz of 0 are undefined; here W.
    if (freeFn && call->getNumArgs() == 1 && (base == "clz" || base == "clzl" || base == "clzll" || base == "ctz" || base == "ctzl" || base == "ctzll" ||
                                    base == "popcount" || base == "popcountl" || base == "popcountll")) {
      V a = genR(call->getArg(0));
      unsigned W = bits(a.t);
      std::string x = a.t->isBooleanType() || W == 64 ? a.n : def("core.zext " + a.n + " : i64");
      if (W == 64 && !a.t->isIntegerType()) fail(call, "bit count of a non-integer");
      std::string acc = c64(0);
      for (unsigned i = 0; i < W; ++i) {
        std::string bit;
        if (base[0] == 'p') {
          std::string sh = i ? def("core.lshr " + x + ", " + c64(i) + " {waived=\"constant in-range shift\"} : i64") : x;
          bit = def("core.and " + sh + ", " + c64(1) + " : i64");
        } else {
          std::string t;
          if (base[0] == 'c' && base[1] == 't') t = def("core.and " + x + ", " + c64(i + 1 >= 64 ? -1 : (int64_t)((1ull << (i + 1)) - 1)) + " : i64");
          else t = i + 1 == W ? x : def("core.lshr " + x + ", " + c64(W - 1 - i) + " {waived=\"constant in-range shift\"} : i64");
          std::string e = def("core.icmp eq " + t + ", " + c64(0) + " : bool");
          bit = def("core.b2i " + e + " : i64");
        }
        acc = def("core.add " + acc + ", " + bit + " : i64");
      }
      return convInt({acc, ctx_.UnsignedLongTy}, ctx_.IntTy);
    }
    // byte swap (bswap16/32/64): a pure permutation of the argument's bytes, built from shifts and ors so the
    // result stays a function of the input. Leaving it unmodelled returns a fresh unconstrained value instead,
    // which severs taint: the comparison that consumes it folds to a constant branch, and every path behind it
    // (e.g. yara's whole byte-swapped-Mach-O subtree, reached only when `should_swap_bytes(be32toh(magic))`)
    // becomes unreachable. Measured on yara v4.6.0: 302 runs, swap_mach_header never entered.
    if (freeFn && call->getNumArgs() == 1 && (base == "bswap16" || base == "bswap32" || base == "bswap64")) {
      V a = genR(call->getArg(0));
      if (!a.t->isIntegerType()) fail(call, "byte swap of a non-integer");
      unsigned nbytes = base == "bswap16" ? 2 : base == "bswap32" ? 4 : 8;
      std::string x = bits(a.t) == 64 ? a.n : def("core.zext " + a.n + " : i64");
      std::string acc;
      for (unsigned i = 0; i < nbytes; ++i) {
        std::string sh = i ? def("core.lshr " + x + ", " + c64(8 * i) + " {waived=\"constant in-range shift\"} : i64") : x;
        std::string by = def("core.and " + sh + ", " + c64(0xff) + " : i64");
        unsigned up = 8 * (nbytes - 1 - i);
        if (up) by = def("core.shl " + by + ", " + c64(up) + " {waived=\"constant in-range shift\"} : i64");
        acc = acc.empty() ? by : def("core.or " + acc + ", " + by + " : i64");
      }
      return convInt({acc, ctx_.UnsignedLongTy}, call->getType());
    }
    // A deterministic setup region the HARNESS declares (DESIGN.md §22.438): everything between the two markers
    // is re-executed identically on every concolic run, so the engine runs it once and restores the state it
    // produced. Lowered to the same kind of marker the generated harness already uses for a project initialiser
    // (`hlir.prologue.begin`), which is why this is a trace op and not a call. Declaring the two functions is
    // enough -- they need no body, and a build that does not go through this frontend links them as no-ops.
    if (freeFn && (plain == "hlir_setup_begin" || plain == "hlir_setup_end")) {
      emit(std::string("core.trace {event=\"hlir.setup.") + (plain == "hlir_setup_begin" ? "begin" : "end") + "\"}");
      return {"", ctx_.VoidTy};
    }
    if (freeFn && base == "unreachable") { term("core.unreachable"); return {"", ctx_.VoidTy}; }
    if (freeFn && (base == "trap" || base == "abort" || base == "exit" || base == "_exit")) { terminateProgram(); return {"", ctx_.VoidTy}; }
    if (freeFn && plain == "__assert_fail") {
      V z = konst(0, ctx_.IntTy);
      std::string f = def("core.icmp ne " + z.n + ", " + z.n + " : bool");
      emit("core.assert " + f + " {msg=\"assertion failed\"}");
      term("core.unreachable");
      return {"", ctx_.VoidTy};
    }
    // std::move / forward / as_const / addressof are compiler builtins (no body to lower): a reference to, or the address of, the argument
    if (base == "__builtin_is_constant_evaluated" || base == "is_constant_evaluated") return {toBool(konst(0, ctx_.IntTy)), call->getType()};
    // A fence orders OTHER threads' view of memory and does nothing to this thread's. The scanner runs one
    // thread, so it is exactly a no-op -- and left unmodelled it is an opaque external, which is not a no-op
    // at all: it says "arbitrary result, writes nothing" and, worse, the function containing it fails to
    // lower. libgit2's hash and allocator paths fence on every operation (Sec.22.489).
    if (freeFn && (base == "__atomic_thread_fence" || base == "__atomic_signal_fence" ||
                   base == "atomic_thread_fence" || base == "atomic_signal_fence" ||
                   base == "__sync_synchronize"))
      return konst(0, ctx_.VoidTy.isNull() ? ctx_.IntTy : ctx_.IntTy);
    if (base == "__atomic_always_lock_free" || base == "__atomic_is_lock_free") {  // only depends on the (compile-time) size/alignment, not the runtime pointer: foldable, but its result type is bool, which the generic top-of-genR constant fold above skips
      Expr::EvalResult r;
      if (call->EvaluateAsInt(r, ctx_)) return {toBool(konst(apExt(r.Val.getInt()), ctx_.IntTy)), call->getType()};
      return {toBool(konst(1, ctx_.IntTy)), call->getType()};  // not foldable here: assume lock-free (the common case for libstdc++'s supported word sizes)
    }
    auto oo = callee->getDeclName().getCXXOverloadedOperator();
    bool isNew = base == "operator_new" || ((oo == OO_New || oo == OO_Array_New) && callee->isReplaceableGlobalAllocationFunction());
    bool isDel = base == "operator_delete" || ((oo == OO_Delete || oo == OO_Array_Delete) && callee->isReplaceableGlobalAllocationFunction());
    if (isNew) {
      std::string bytes = genR(call->getArg(0)).n;
      return {def("core.heap_alloc " + bytes + " {fail=never, name=\"new\"} : ptr", "n"), call->getType()};
    }
    if (isDel) {
      std::string pv = genR(call->getArg(0)).n;
      std::string isn = def("core.is_null " + pv + " : bool");
      size_t doB = newBlock("delete"), done = newBlock("deleted");
      term("core.cond_br " + isn + ", " + bname(done) + ", " + bname(doB));
      setBlock(doB);
      emit("core.check.free " + pv + " {expect=heap, origin=\"delete\"}");
      emit("core.free " + pv);
      term("core.br " + bname(done));
      setBlock(done);
      return {"", ctx_.VoidTy};
    }
    if (auto *tm = dyn_cast<CXXMethodDecl>(callee); tm && tm->isTrivial() && (tm->isCopyAssignmentOperator() || tm->isMoveAssignmentOperator()) && isa<CXXOperatorCallExpr>(call) && call->getNumArgs() == 2) {
      // a trivial defaulted assignment (no body in the AST) copies the bytes
      LV sr = genL(call->getArg(1)), d = genL(call->getArg(0));
      if (!d.direct) emit("core.check.const_write " + d.p);
      // An empty class (no data members, e.g. a stateless `std::allocator<char>`) is eligible for the empty-base-
      // optimization: as a *base-class subobject* it occupies 0 bytes and shares its address with whatever
      // non-empty sibling follows it in the derived object (e.g. libstdc++'s `_Alloc_hider : allocator_type`
      // puts its `_M_p` pointer field at that same offset-0 address). `sizeOf()` gives the *standalone* object
      // size, which the standard pads to a minimum of 1 byte precisely so two distinct empty objects never
      // compare equal by address - copying that single padding byte here is meaningless for an empty class, and
      // when the assignment's operands are actually base-class-subobject references bound through this kind of
      // EBO aliasing (`std::__alloc_on_move` assigns through `_Alloc&` references into `_Alloc_hider` members,
      // reached from code like basic_string's move-assignment self-move guard), that 1-byte copy instead
      // corrupts the very first byte of the real sibling field at the same address - observed turning a correct
      // `this+16` local-buffer pointer into `(null)+16` right before a `memcpy`, a false `null_deref`. Skip the
      // copy entirely when there is no data to copy (`isEmpty()`, the same test the standard uses for EBO
      // eligibility: no non-static data members, no virtual functions/bases, no non-empty base classes).
      if (!tm->getParent()->isEmpty()) copyBytes(d, sr, sizeOf(ctx_.getRecordType(tm->getParent())));
      return {d.p, call->getType()};
    }
    if (callee->isInStdNamespace() && callee->getIdentifier()) {
      llvm::StringRef nm = callee->getName();
      if ((nm == "move" || nm == "forward" || nm == "forward_like" || nm == "move_if_noexcept" || nm == "as_const") && call->getNumArgs() >= 1)
        return {genL(call->getArg(call->getNumArgs() - 1)).p, call->getType()};
      // `std::__addressof` is libstdc++'s internal equivalent of `std::addressof` (bypasses a possibly-overloaded
      // `operator&`; used pervasively inside the standard library's own implementation, e.g. basic_string's move
      // assignment self-move guard `std::__addressof(__str) != this`). Previously only the public `addressof`
      // name was matched, so this fell through to an ordinary call; with no body linked in and no ModelDB entry
      // for the mangled `__addressof` symbol, it was treated as an opaque external (NULL-or-arbitrary result) -
      // losing precision on a trivial, always-computable address instead of giving the real one.
      if ((nm == "addressof" || nm == "__addressof") && call->getNumArgs() == 1) return {genL(call->getArg(0)).p, call->getType()};
      if (nm == "launder" && call->getNumArgs() == 1) return genR(call->getArg(0));
    }
    if (base == "add_overflow" || base == "sub_overflow" || base == "mul_overflow") return genOverflow(call, base[0]);
    // ...and the TYPED family: __builtin_{s,u}{add,sub,mul}{,l,ll}_overflow. Identical semantics --
    // the type is in the name instead of in the arguments, and genOverflow reads the result type off
    // the third argument either way, so the same lowering is exact for both.
    //
    // Only the generic three were matched before, which made every typed one an unmodelled external:
    // "returns an unconstrained value and writes nothing". That is the same taint cut as the byte
    // swap of Sec.22.486, and it lands somewhere worse -- libgit2 computes every allocation size
    // through git__multiply_sizet_overflow (__builtin_umull_overflow), so the SIZE of each object a
    // parser allocates stopped depending on the input. Measured on git_object__from_raw: 12 checks
    // queried, 35 of 5932 functions entered.
    if (base.size() > 10 && base.compare(base.size() - 9, 9, "_overflow") == 0 &&
        (base[0] == 's' || base[0] == 'u')) {
      // `umull` is u + mul + l, so the length suffix is AT MOST two `l`s and the third letter of
      // `mul` is not one of them. Stripping every trailing `l` turns `mull` into `mu` and matches
      // nothing -- which is what the first version of this did.
      std::string mid = base.substr(1, base.size() - 10);   // add / addl / addll / sub... / mul...
      for (int k = 0; k < 2 && mid.size() > 3 && mid.back() == 'l'; ++k) mid.pop_back();
      if (mid == "add" || mid == "sub" || mid == "mul") return genOverflow(call, mid[0]);
    }
    // builtin string/memory functions are the library functions
    static const std::set<std::string> libs = {"memcpy", "memmove", "memset", "strlen", "strcpy", "strncpy", "strcmp", "strncmp", "strcat", "memcmp", "memchr"};
    if (base != plain && libs.count(base)) name = base;
    // `dlsym(handle, "foo")` with a LITERAL symbol name (DESIGN.md §22.424). Left alone, the result is an address no
    // call site can match, so every call through it is `__hlir_unknown_indirect` and the shared object's code is
    // invisible -- the whole point of the dlopen path. The name is known here but the symbol table is not (it may be
    // defined in another unit, which is the normal case), so the call is lowered to `@__hlir_dlsym.foo` and hlir::link
    // defines it after merging: NULL or `foo`'s address, with `foo` added to the indirect-call candidates. A name no
    // unit defines is left as a declare and stays an opaque external, reported as such.
    // A computed name (`dlsym(h, buf)`) has nothing to resolve and falls through to the ordinary call.
    // Only in --link mode: hlir::link is what defines `@__hlir_dlsym.<name>`, and a single-file scan never runs it --
    // rewriting the call there would trade libc.core's @dlsym model for an unresolved external, which is worse.
    if (mod_.link && name == "dlsym" && call->getNumArgs() == 2 && !mod_.defined.count(name)) {
      const auto *sl = dyn_cast<StringLiteral>(call->getArg(1)->IgnoreParenImpCasts());
      std::string sym = sl && sl->isOrdinary() ? sl->getString().str() : std::string();
      bool plainName = !sym.empty() && (std::isalpha(static_cast<unsigned char>(sym[0])) || sym[0] == '_');
      for (char c : sym) plainName = plainName && (std::isalnum(static_cast<unsigned char>(c)) || c == '_');
      if (plainName) {
        const std::string tn = "__hlir_dlsym." + sym;
        mod_.declares[tn] = "core.declare @" + tn + "(ptr) -> ptr";
        mod_.dlsymNames.insert(sym);
        std::string h = genR(call->getArg(0)).n;
        return emitCall("@" + tn, {h}, callee->getReturnType(), dest);
      }
    }
    useFunction(callee);
    // C++ calls: the object of a method call, the operator's left operand
    std::vector<const Expr *> argExprs(call->arg_begin(), call->arg_end());
    std::string thisPtr;
    if (hasThis(callee)) {
      const CXXMethodDecl *md = cast<CXXMethodDecl>(callee);
      QualType objTy;
      if (isa<CXXOperatorCallExpr>(call)) {
        if (argExprs.empty()) fail(call, "member operator without an object");
        LV l = genL(argExprs[0]);
        thisPtr = l.p;
        objTy = argExprs[0]->getType();
        argExprs.erase(argExprs.begin());
      } else if (auto *mc = dyn_cast<CXXMemberCallExpr>(call)) {
        auto *me = dyn_cast<MemberExpr>(mc->getCallee()->IgnoreParens());
        if (!me) fail(call, "call through a pointer to member");
        const Expr *obj = me->getBase();
        if (me->isArrow()) { thisPtr = genR(obj).n; objTy = obj->getType()->getPointeeType(); }
        else { thisPtr = genL(obj).p; objTy = obj->getType(); }
        if (md->isVirtual() && !me->hasQualifier()) {
          if (me->isArrow() || !exactObject(obj)) return genVirtualCall(call, md, thisPtr, objTy, argExprs, dest);
          const CXXRecordDecl *dyn = recordOf(objTy);  // the dynamic type is the static type: the overrider in that class
          const CXXMethodDecl *ov = dyn ? md->getCorrespondingMethodInClass(dyn) : nullptr;
          if (ov && ov != md) {
            std::vector<uint64_t> offS, offP;
            subobjectOffsets(dyn, md->getParent(), 0, offS);
            subobjectOffsets(dyn, ov->getParent(), 0, offP);
            if (!offS.empty() && !offP.empty() && offS[0] != offP[0]) thisPtr = def("core.ptr_add " + thisPtr + ", " + c64(static_cast<int64_t>(offP[0]) - static_cast<int64_t>(offS[0])) + " {waived=\"in-bounds by construction\"} : ptr", "p");
            callee = ov;
            name = fnName(ov);
            useFunction(ov);
          }
        }
      } else fail(call, "method call of an unexpected form");
      (void)objTy;
    }
    const FunctionProtoType *fpt = callee->getType()->getAs<FunctionProtoType>();
    if (!fpt && !(callee->getNumParams() == 0 && call->getNumArgs() == 0)) {
      // no prototype (K&R or an implicit declaration): the signature is what this call passes, after the default
      // argument promotions; the result is int
      std::vector<std::string> args;
      std::string sg = "(";
      for (unsigned i = 0; i < call->getNumArgs(); ++i) {
        QualType at = call->getArg(i)->getType();
        if (at->isArrayType()) at = ctx_.getPointerType(ctx_.getAsArrayType(at)->getElementType());
        else if (ctx_.isPromotableIntegerType(at)) at = ctx_.getPromotedIntegerType(at);
        if (!isScalarTy(at)) fail(call, "call to '" + name + "' without a prototype passes an aggregate");
        V v = genR(call->getArg(i));
        args.push_back(convTo(v, at).n);
        sg += (i ? ", " : "") + ty(at);
      }
      sg += ") -> " + ty(callee->getReturnType());
      std::string decl = "core.declare @" + name + sg;
      if (!mod_.defined.count(name)) {
        auto it = mod_.declares.find(name);
        if (it != mod_.declares.end() && it->second != decl) fail(call, "'" + name + "' is called with different argument types and has no prototype");
        mod_.declares[name] = decl;
      }
      return emitCall("@" + name, args, callee->getReturnType());
    }
    std::vector<std::string> args = evalArgsFor(argExprs, callee, fpt);
    if (!thisPtr.empty()) args.insert(args.begin(), thisPtr);
    // `!callee->isDefined()` is not enough: a libc function whose body we deliberately left to the model
    // IS defined (glibc's `__extern_inline tolower`), yet nothing will lower it, so without this the call
    // is emitted against a name the module never declares -- verification then fails with
    // "call to undeclared function @tolower" instead of the old "redefinition of function @tolower".
    const FunctionDecl *cdef = callee->getDefinition();
    const bool bodyWontBeLowered = cdef && bodyIsLibcsToModel(cdef);
    if ((mod_.externals.count(name) || (!mod_.defined.count(name) && (!callee->isDefined() || bodyWontBeLowered))) &&
        !mod_.declares.count(name)) {
      bool ok = true;
      std::string sg = sigOfDecl(ctx_, callee, ok);
      if (!ok) fail(call, "signature of '" + name + "'");
      mod_.declares[name] = "core.declare @" + name + sg;
    }
    return emitCall("@" + name, args, callee->getReturnType(), dest);
  }
  // ---- C++ objects: base-class adjustments, construction, new/delete
  // follow a derived-to-base cast path from the object at `p` (of type startTy); virtual steps read the object's offset table
  bool pathHasVirtual(const CastExpr *ce) {
    for (const CXXBaseSpecifier *b : ce->path()) if (b->isVirtual()) return true;
    return false;
  }
  std::string walkPath(const std::string &p0, const CastExpr *ce, QualType startTy) {
    const CXXRecordDecl *cur = recordOf(startTy);
    std::string p = p0;
    uint64_t off = 0;
    for (const CXXBaseSpecifier *b : ce->path()) {
      const CXXRecordDecl *next = b->getType()->getAsCXXRecordDecl();
      if (!cur || !next) fail(ce, "base class conversion");
      if (!layoutSane(ctx_.getRecordType(cur))) fail(ce, "base class conversion of a record with an invalid layout");
      if (b->isVirtual()) {
        p = vbaseAddr(inObj(p, off), cur, next);
        off = 0;
      } else off += ctx_.getASTRecordLayout(cur).getBaseClassOffset(next).getQuantity();
      cur = next;
    }
    return inObj(p, off);
  }
  uint64_t pathOffset(const CastExpr *ce, QualType startTy) {  // static paths only
    const CXXRecordDecl *cur = recordOf(startTy);
    uint64_t off = 0;
    for (const CXXBaseSpecifier *b : ce->path()) {
      const CXXRecordDecl *next = b->getType()->getAsCXXRecordDecl();
      if (!cur || !next) fail(ce, "base class conversion");
      if (b->isVirtual()) fail(ce, "conversion through a virtual base class");
      if (!layoutSane(ctx_.getRecordType(cur))) fail(ce, "base class conversion of a record with an invalid layout");
      off += ctx_.getASTRecordLayout(cur).getBaseClassOffset(next).getQuantity();
      cur = next;
    }
    return off;
  }
  std::string adjustToBase(const std::string &p, QualType fromObj, const CastExpr *ce) { return pathHasVirtual(ce) ? walkPath(p, ce, fromObj) : inObj(p, pathOffset(ce, fromObj)); }
  // pointer conversions keep null as null
  std::string adjustPtr(const std::string &p, QualType pointee, const CastExpr *ce, bool toDerived) {
    QualType startTy = toDerived ? ce->getType()->getPointeeType() : pointee;
    if (pathHasVirtual(ce)) {
      if (toDerived) fail(ce, "conversion from a virtual base class to a derived class");
      std::string isn = def("core.is_null " + p + " : bool");
      size_t doB = newBlock("vbase"), join = newBlock("vbase_end");
      std::string res = fresh("r");
      blocks_[join].params = res + ": ptr";
      term("core.cond_br " + isn + ", " + bname(join) + "(" + p + "), " + bname(doB));
      setBlock(doB);
      std::string moved = walkPath(p, ce, startTy);
      term("core.br " + bname(join) + "(" + moved + ")");
      setBlock(join);
      return res;
    }
    uint64_t off = pathOffset(ce, startTy);
    if (!off) return p;
    std::string isn = def("core.is_null " + p + " : bool");
    std::string moved = def("core.ptr_add " + p + ", " + c64(toDerived ? -static_cast<int64_t>(off) : static_cast<int64_t>(off)) + " {waived=\"in-bounds by construction\"} : ptr", "p");
    return def("core.select " + isn + ", " + p + ", " + moved + " : ptr", "p");
  }
  // run a constructor on the memory at `dest`
  void constructInto(const std::string &dest, const CXXConstructExpr *ce) {
    if (const ConstantArrayType *cat = ctx_.getAsConstantArrayType(ce->getType())) {  // every element runs the constructor
      QualType et = ctx_.getBaseElementType(ce->getType());
      uint64_t n = ctx_.getConstantArrayElementCount(cat);
      if (n > 256) fail(ce, "construction of an array of more than 256 objects");
      for (uint64_t i = 0; i < n; ++i) constructElem(i ? inObj(dest, i * sizeOf(et)) : dest, ce, et);
      return;
    }
    constructElem(dest, ce, ce->getType());
  }
  void constructElem(const std::string &dest, const CXXConstructExpr *ce, QualType t) {
    const CXXConstructorDecl *cd = ce->getConstructor();
    at(ce);
    if (ce->requiresZeroInitialization()) emit("core.memset " + dest + ", " + def("core.const 0 : i8", "c") + ", " + c64(static_cast<int64_t>(sizeOf(t))));
    if (cd->isTrivial()) {  // nothing to run; a trivial copy/move copies the bytes
      if (cd->isCopyOrMoveConstructor() && ce->getNumArgs() >= 1) copyBytes({dest, t, true, false, false}, genL(ce->getArg(0)), sizeOf(t));
      return;
    }
    useFunction(cd);
    std::vector<const Expr *> argv(ce->arg_begin(), ce->arg_end());
    std::vector<std::string> args = evalArgsFor(argv, cd, nullptr);
    args.insert(args.begin(), dest);
    ensureDeclared(cd);
    // a class with virtual bases: a complete object runs the complete-object constructor; a base subobject (or a delegation from a
    // base-object constructor) runs the base-object variant, which is told where the virtual bases are
    bool asBase = hasBaseVariant(cd) && (ce->getConstructionKind() == CXXConstructionKind::NonVirtualBase || ce->getConstructionKind() == CXXConstructionKind::VirtualBase ||
                                          (ce->getConstructionKind() == CXXConstructionKind::Delegating && base_));
    std::string a;
    for (size_t i = 0; i < args.size(); ++i) a += (i ? ", " : "") + args[i] + (i == 0 && asBase ? vbaseArgs(cd->getParent()) : "");
    if (asBase) {
      ensureBaseDeclared(cd);
      emit("core.call @" + baseVariantName(cd) + "(" + a + ")");
    } else emit("core.call @" + fnName(cd) + "(" + a + ")");
    emitExcEscapeGuard();  // a constructor body can call arbitrary user code and throw; a `try` cannot wrap a construction's own call site here (no local matching: see IMPLEMENTATION_PLAN), so an escaping exception is the pre-existing "uncaught" outcome
  }
  V genNew(const CXXNewExpr *ne) {
    QualType at = ne->getAllocatedType();
    bool isArray = ne->isArray();
    uint64_t esz = sizeOf(at);
    std::string count = c64(1);
    if (isArray) {
      auto sz = ne->getArraySize();
      if (!sz) fail(ne, "array new without a size");
      count = to64(genR(*sz));
      std::string pos = def("core.icmp sge " + count + ", " + c64(0) + " : bool");
      emit("core.assert " + pos + " {msg=\"array new with a negative size\"}");
    }
    std::string bytes = isArray ? def("core.mul " + count + ", " + c64(static_cast<int64_t>(esz)) + " : i64") : c64(static_cast<int64_t>(esz));
    const FunctionDecl *on = ne->getOperatorNew();
    std::string p;
    if (on && on->isReservedGlobalPlacementOperator() && ne->getNumPlacementArgs() == 1) {
      p = genR(*ne->placement_arguments().begin()).n;  // placement new: the object goes where the pointer says
    } else if (on && on->getDefinition() && !on->isReplaceableGlobalAllocationFunction()) {  // a class-specific operator new
      useFunction(on);
      ensureDeclared(on);
      p = emitCall("@" + fnName(on), {bytes}, on->getReturnType()).n;
    } else {
      bool mayFail = ne->shouldNullCheckAllocation();  // new(std::nothrow); a plain new throws instead, which ends the path
      p = def("core.heap_alloc " + bytes + " {fail=" + (mayFail ? "nondet" : "never") + ", name=\"new\"} : ptr", "n");
    }
    if (const Expr *init = ne->getInitializer()) {
      size_t doInit = 0, done = 0;
      bool guard = ne->shouldNullCheckAllocation();
      if (guard) {
        std::string isn = def("core.is_null " + p + " : bool");
        doInit = newBlock("newinit");
        done = newBlock("newdone");
        term("core.cond_br " + isn + ", " + bname(done) + ", " + bname(doInit));
        setBlock(doInit);
      }
      if (!isArray) initObject({p, at, false, false, false}, init);
      else initArrayNew(p, at, count, init);
      if (guard) { term("core.br " + bname(done)); setBlock(done); }
    }
    return {p, ne->getType()};
  }
  void initArrayNew(const std::string &p, QualType et, const std::string &count, const Expr *init) {
    const Expr *e = init->IgnoreParens();
    if (isa<ImplicitValueInitExpr>(e)) {  // new T[n]() : value-initialised
      std::string bytes = def("core.mul " + count + ", " + c64(static_cast<int64_t>(sizeOf(et))) + " : i64");
      emit("core.memset " + p + ", " + def("core.const 0 : i8", "c") + ", " + bytes);
      return;
    }
    if (auto *cx = dyn_cast<CXXConstructExpr>(e)) {  // the same constructor for every element
      if (cx->getConstructor()->isTrivial() && !cx->requiresZeroInitialization()) return;
      size_t head = newBlock("newarr"), body = newBlock("newelem"), end = newBlock("newarrend");
      std::string iSlot = newSlot(ctx_.LongTy, "newi", false);
      store({iSlot, ctx_.LongTy, true, false, false}, {c64(0), ctx_.LongTy});
      term("core.br " + bname(head));
      setBlock(head);
      std::string i = def("core.load " + iSlot + " {waived=\"object known\"} : i64", "l");
      std::string lt = def("core.icmp slt " + i + ", " + count + " : bool");
      term("core.cond_br " + lt + ", " + bname(body) + ", " + bname(end));
      setBlock(body);
      std::string off = def("core.mul " + i + ", " + c64(static_cast<int64_t>(sizeOf(et))) + " : i64");
      std::string ep = def("core.ptr_add " + p + ", " + off + " {waived=\"in-bounds by construction\"} : ptr", "p");
      constructInto(ep, cx);
      std::string i1 = def("core.add " + i + ", " + c64(1) + " : i64");
      store({iSlot, ctx_.LongTy, true, false, false}, {i1, ctx_.LongTy});
      term("core.br " + bname(head));
      setBlock(end);
      return;
    }
    if (auto *il = dyn_cast<InitListExpr>(e)) {
      for (unsigned k = 0; k < il->getNumInits(); ++k) {
        const Expr *ie = il->getInit(k);
        if (!ie || isa<ImplicitValueInitExpr>(ie)) continue;
        initObject({inObj(p, k * sizeOf(et)), et, false, false, false}, ie);
      }
      return;
    }
    fail(init, "initializer of an array new");
  }
  void genDelete(const CXXDeleteExpr *de) {
    V p = genR(de->getArgument());
    QualType dt = de->getDestroyedType();
    std::string isn = def("core.is_null " + p.n + " : bool");
    size_t doB = newBlock("delete"), done = newBlock("deleted");
    term("core.cond_br " + isn + ", " + bname(done) + ", " + bname(doB));
    setBlock(doB);
    const CXXRecordDecl *rd = recordOf(dt);
    if (rd && rd->hasDefinition() && !rd->hasTrivialDestructor()) {
      if (de->isArrayForm()) fail(de, "delete[] of objects with destructors");
      const CXXDestructorDecl *dd = rd->getDestructor();
      if (dd && dd->isVirtual() && !de->isArrayForm()) {  // the dispatcher runs the destructor of the dynamic type and frees the whole object
        std::string name = "__hlir_vdelete." + fnName(dd);
        mod_.vcalls[name] = {dd, true};
        emitCall("@" + name, {p.n}, ctx_.VoidTy);
        term("core.br " + bname(done));
        setBlock(done);
        return;
      }
      emitDtor(p.n, rd);
    }
    const FunctionDecl *od = de->getOperatorDelete();
    if (od && od->getDefinition() && !od->isReplaceableGlobalAllocationFunction()) {  // a class-specific operator delete
      useFunction(od);
      ensureDeclared(od);
      std::vector<std::string> args{p.n};
      if (od->getNumParams() == 2) args.push_back(c64(static_cast<int64_t>(sizeOf(dt))));
      emitCall("@" + fnName(od), args, od->getReturnType());
    } else {
      emit("core.check.free " + p.n + " {expect=heap, origin=\"delete\"}");
      emit("core.free " + p.n);
    }
    term("core.br " + bname(done));
    setBlock(done);
  }
  // ---- virtual functions
  // is the dynamic type of the object known to be its static type? (a variable or temporary of class type, not a reference/pointer)
  static bool exactObject(const Expr *obj) {
    obj = obj->IgnoreParenImpCasts();
    if (auto *dr = dyn_cast<DeclRefExpr>(obj)) if (auto *vd = dyn_cast<VarDecl>(dr->getDecl())) return !vd->getType()->isReferenceType();
    if (auto *me = dyn_cast<MemberExpr>(obj)) return !me->isArrow() && !me->getMemberDecl()->getType()->isReferenceType() && exactObject(me->getBase());
    if (isa<CXXTemporaryObjectExpr>(obj) || isa<CXXConstructExpr>(obj) || isa<MaterializeTemporaryExpr>(obj) || isa<CXXBindTemporaryExpr>(obj)) return true;
    return false;
  }
  // offsets of the subobjects of class `target` inside a complete object of class `rd`
  bool subobjectOffsets(const CXXRecordDecl *rd, const CXXRecordDecl *target, uint64_t base, std::vector<uint64_t> &out) {
    forEachSubobject(ctx_, rd, [&](const CXXRecordDecl *c, uint64_t off, bool) {
      if (c->getCanonicalDecl() == target->getCanonicalDecl()) out.push_back(base + off);
    });
    return !out.empty();
  }
  V genVirtualCall(const CallExpr *call, const CXXMethodDecl *md, const std::string &thisPtr, QualType objTy, const std::vector<const Expr *> &argExprs, const std::string &dest) {
    (void)objTy;
    std::string name = (isa<CXXDestructorDecl>(md) ? "__hlir_vdtor." : "__hlir_vcall.") + fnName(md);
    mod_.vcalls[name] = {md, false};
    std::vector<std::string> args = evalArgsFor(argExprs, md, nullptr);
    args.insert(args.begin(), thisPtr);
    return emitCall("@" + name, args, md->getReturnType(), dest);
  }
  // `dynamic_cast<Target*>`/`<Target&>`/`<void*>`: registers (and later drains, see `dynCastDispatcher`) a dispatcher
  // keyed by the (source, target) class pair and calls it with the operand's address. `objTy` is the operand's
  // static class (the dynamic type is determined at runtime from its vptr); null is special-cased ahead of the
  // call for the pointer form (the standard says `dynamic_cast<T*>(nullptr)` is null, not a null-pointer access).
  std::string genDynCastCall(const CXXRecordDecl *src, const CXXRecordDecl *target, bool isRef, const std::string &objPtr) {
    std::string srcTag = typeInfoMarker(ctx_, ctx_.getRecordType(src)).first;
    std::string tgtTag = target ? typeInfoMarker(ctx_, ctx_.getRecordType(target)).first : "void";
    std::string name = "__hlir_dyncast." + tgtTag + "." + srcTag + (isRef ? ".ref" : "");
    mod_.dynCasts[name] = {src, target, isRef};
    return def("core.call @" + name + "(" + objPtr + ") : ptr", "dc");
  }
  std::string genDynCast(const CXXDynamicCastExpr *dce) {
    QualType to = dce->getType();
    bool isRef = !to->isPointerType();
    QualType targetTy = isRef ? to : to->getPointeeType();
    const CXXRecordDecl *target = nullptr;
    if (!targetTy->isVoidType()) {
      target = targetTy->getAsCXXRecordDecl();
      if (!target || !target->getDefinition()) fail(dce, "dynamic_cast to an incomplete or non-class type");
      target = target->getDefinition();
    }
    const Expr *sub = dce->getSubExpr();
    QualType fromTy = isRef ? sub->getType() : sub->getType().getCanonicalType()->getPointeeType();
    const CXXRecordDecl *src = fromTy->getAsCXXRecordDecl();
    if (!src || !src->getDefinition() || !src->getDefinition()->isPolymorphic()) fail(dce, "dynamic_cast of an operand that is not a pointer or reference to a polymorphic class type");
    src = src->getDefinition();
    if (isRef) return genDynCastCall(src, target, true, genL(sub).p);
    V p = genR(sub);
    std::string isn = def("core.is_null " + p.n + " : bool");
    size_t nb = newBlock("dyncast_null"), lb = newBlock("dyncast_live"), end = newBlock("dyncast_end");
    std::string res = fresh("r");
    blocks_[end].params = res + ": ptr";
    term("core.cond_br " + isn + ", " + bname(nb) + ", " + bname(lb));
    setBlock(nb);
    term("core.br " + bname(end) + "(" + zeroOf(ctx_.VoidPtrTy).n + ")");
    setBlock(lb);
    std::string r = genDynCastCall(src, target, false, p.n);
    term("core.br " + bname(end) + "(" + r + ")");
    setBlock(end);
    return res;
  }
  V genIndirectCall(const CallExpr *call) {
    const Expr *ce = call->getCallee();
    QualType ft = ce->getType().getCanonicalType();
    if (ft->isPointerType()) ft = ft->getPointeeType();
    const FunctionProtoType *fpt = ft->getAs<FunctionProtoType>();
    if (!fpt) fail(call, "indirect call without a prototype");
    std::string fp = genR(ce).n;
    std::vector<std::string> args = evalArgsFor(std::vector<const Expr *>(call->arg_begin(), call->arg_end()), nullptr, fpt);
    bool ok = true;
    std::vector<QualType> ps(fpt->param_type_begin(), fpt->param_type_end());
    std::string want = sigText(ctx_, fpt->getReturnType(), ps, ok);
    if (!ok) fail(call, "signature of an indirect call");
    QualType ret = fpt->getReturnType();
    // the C type the pointer is called through: only functions of that type, or whose address escaped its type, can be the target
    std::string ckey = cTypeKey(QualType(fpt, 0));
    std::vector<const FunctionDecl *> cands;
    if (!mod_.link)  // link mode: one program-wide dispatcher (hlir::link) knows every candidate
    for (auto *f : mod_.addrTaken) {
      bool k = true;
      if (f->isVariadic() == fpt->isVariadic() && sigOfDecl(ctx_, f, k) == want && k &&
          (mod_.addrEscaped.count(f) || cTypesCompatible(ckey, cTypeKey(f->getType()))))
        cands.push_back(f);
    }
    std::sort(cands.begin(), cands.end(), [](auto *a, auto *b) { return a->getName() < b->getName(); });
    size_t join = newBlock("icall_end");
    bool hasVal = !ret->isVoidType() && !isRecordTy(ret);
    std::string res = fresh("r");
    if (hasVal) blocks_[join].params = res + ": " + ty(ret);
    std::string slot;
    if (isRecordTy(ret)) { slot = newSlot(ret, "sret"); args.insert(args.begin(), slot); }
    std::string a;
    for (size_t i = 0; i < args.size(); ++i) a += (i ? ", " : "") + args[i];
    // calling a NULL pointer is undefined behaviour
    {
      std::string isn = def("core.is_null " + fp + " : bool");
      size_t nullc = newBlock("icall_null"), live = newBlock("icall_live");
      term("core.cond_br " + isn + ", " + bname(nullc) + ", " + bname(live));
      setBlock(nullc);
      term("core.unreachable");
      setBlock(live);
    }
    for (auto *f : cands) {
      ensureDeclared(f);
      std::string fa = def("core.func_addr @" + fnName(f) + " : ptr", "f");
      std::string eq = def("core.ptr_cmp eq " + fp + ", " + fa + " : bool");
      size_t hit = newBlock("icall"), next = newBlock("icall_next");
      term("core.cond_br " + eq + ", " + bname(hit) + ", " + bname(next));
      setBlock(hit);
      if (hasVal) {
        std::string r = def("core.call @" + fnName(f) + "(" + a + ") : " + ty(ret), "r");
        emitExcEscapeGuard();  // indirect call to a known candidate with a real body: same reasoning as ctor/dtor chaining, see IMPLEMENTATION_PLAN — the safety net, not full local-catch matching
        term("core.br " + bname(join) + "(" + r + ")");
      } else {
        emit("core.call @" + fnName(f) + "(" + a + ")");
        emitExcEscapeGuard();
        term("core.br " + bname(join));
      }
      setBlock(next);
    }
    // not the address of a function this file registers: a function of some other module. Its body is unknown, so it is
    // an external call (`@__hlir_indirect.<signature>`) that the ModelDB / the opaque-externals assumption describes.
    // Link mode: the call goes to the dispatcher the linker generates; it takes the pointer as its first argument.
    {
      std::string sigName = want;
      for (char &c : sigName) if (!isalnum(static_cast<unsigned char>(c))) c = '_';
      std::string ename = "__hlir_indirect." + sigName;
      std::string callArgs = a;
      if (mod_.link) {
        if (!ckey.empty()) {
          ename += indirectTypeTag(ckey);
          mod_.indirectCallCTypes[ename] = ckey;
        }
        size_t open = want.find('(');
        mod_.declares[ename] = "core.declare @" + ename + want.substr(0, open + 1) + (want[open + 1] == ')' ? "ptr" : "ptr, ") + want.substr(open + 1);
        callArgs = fp + (a.empty() ? "" : ", " + a);
      } else mod_.declares[ename] = "core.declare @" + ename + want;
      if (hasVal) {
        std::string r = def("core.call @" + ename + "(" + callArgs + ") : " + ty(ret), "r");
        term("core.br " + bname(join) + "(" + r + ")");
      } else {
        emit("core.call @" + ename + "(" + callArgs + ")");
        term("core.br " + bname(join));
      }
    }
    setBlock(join);
    return {hasVal ? res : slot, ret};
  }
  // __builtin_{add,sub,mul}_overflow(a, b, &r): computed in 128 bits
  V genOverflow(const CallExpr *call, char which) {
    if (call->getNumArgs() != 3) fail(call, "overflow builtin arity");
    V a = genR(call->getArg(0)), b = genR(call->getArg(1)), dst = genR(call->getArg(2));
    QualType rt = call->getArg(2)->getType().getCanonicalType()->getPointeeType();
    if (bits(rt) > 64 || bits(a.t) > 64 || bits(b.t) > 64) fail(call, "overflow builtin on more than 64 bits");
    V a1 = convInt(a, ctx_.Int128Ty), b1 = convInt(b, ctx_.Int128Ty);
    const char *op = which == 'a' ? "add" : which == 's' ? "sub" : "mul";
    std::string w = def(std::string("core.") + op + " " + a1.n + ", " + b1.n + " : i128");
    V r = convInt({w, ctx_.Int128Ty}, rt);
    V back = convInt(r, ctx_.Int128Ty);
    std::string ovf = def("core.icmp ne " + back.n + ", " + w + " : bool");
    store({dst.n, rt, false, false, false}, r);
    return {ovf, ctx_.BoolTy};
  }

  // ------------------------------------------------------------------ statements
  size_t labelBlock(const LabelDecl *l) {
    auto it = labels_.find(l);
    if (it != labels_.end()) return it->second;
    return labels_[l] = newBlock("L_" + l->getName().str() + "_");
  }
  void stmt(const Stmt *S) {
    if (!S) return;
    at(S);
    if (auto *cs = dyn_cast<CompoundStmt>(S)) {
      bool top = fd_ && cs == fd_->getBody();
      if (!top) pushScope();
      for (auto *c : cs->body()) stmt(c);
      if (!top) popScope(true);
    } else if (auto *ds = dyn_cast<DeclStmt>(S)) {
      for (auto *d : ds->decls()) { declare(d); flushTemps(); }
    } else if (auto *rs = dyn_cast<ReturnStmt>(S)) {
      const Expr *rv = rs->getRetValue();
      bool isVoid = fd_ && fd_->getReturnType()->isVoidType();
      auto leave = [&](const std::string &val) {
        flushTemps();
        unwindTo(0);
        if (retBlock_ != SIZE_MAX) term("core.br " + bname(retBlock_));
        else term(val.empty() ? "core.return" : "core.return " + val);
      };
      if (rv && isVoid) {  // `return f();` in a void function
        genR(rv);
        leave("");
      } else if (rv) {
        if (!sret_.empty()) {
          initObject({sret_, rv->getType(), false, false, false}, rv);
          leave("");
        } else if (fd_ && fd_->getReturnType()->isReferenceType()) {
          LV l = genL(rv);
          leave(l.p);
        } else {
          V v = genR(rv);
          if (!isScalarTy(v.t)) fail(rs, "return of an aggregate");
          leave(v.n);
        }
      } else leave("");
    } else if (auto *is = dyn_cast<IfStmt>(S)) {
      bool scoped = is->getInit() || is->getConditionVariableDeclStmt();
      if (scoped) pushScope();
      if (is->getInit()) stmt(is->getInit());
      if (auto *cv = is->getConditionVariableDeclStmt()) stmt(cv);
      if (is->isConstexpr()) {  // `if constexpr`: only the branch the condition selects is lowered
        if (auto nd = is->getNondiscardedCase(ctx_)) stmt(*nd);
        if (scoped) popScope(true);
        return;
      }
      std::string c = genCond(is->getCond());
      flushTemps();
      size_t tb = newBlock("then"), eb = is->getElse() ? newBlock("else") : 0, end = newBlock("endif");
      term("core.cond_br " + c + ", " + bname(tb) + ", " + bname(is->getElse() ? eb : end));
      setBlock(tb);
      stmt(is->getThen());
      if (!blocks_[curBlock_].done) term("core.br " + bname(end));
      if (is->getElse()) {
        setBlock(eb);
        stmt(is->getElse());
        if (!blocks_[curBlock_].done) term("core.br " + bname(end));
      }
      setBlock(end);
      if (scoped) popScope(true);
    } else if (auto *ws = dyn_cast<WhileStmt>(S)) {
      size_t head = newBlock("while"), body = newBlock("body"), end = newBlock("endwhile");
      bool wscoped = ws->getConditionVariableDeclStmt() != nullptr;  // `while (T *p = next())`: p lives for the whole loop
      if (wscoped) pushScope();
      term("core.br " + bname(head));
      setBlock(head);
      at(ws);
      if (wscoped) stmt(ws->getConditionVariableDeclStmt());
      std::string c = genCond(ws->getCond());
      flushTemps();
      term("core.cond_br " + c + ", " + bname(body) + ", " + bname(end));
      setBlock(body);
      loopBody(ws->getBody(), end, head);
      if (!blocks_[curBlock_].done) term("core.br " + bname(head));
      setBlock(end);
      if (wscoped) popScope(true);
    } else if (auto *dw = dyn_cast<DoStmt>(S)) {
      size_t body = newBlock("do"), cond = newBlock("docond"), end = newBlock("enddo");
      term("core.br " + bname(body));
      setBlock(body);
      loopBody(dw->getBody(), end, cond);
      if (!blocks_[curBlock_].done) term("core.br " + bname(cond));
      setBlock(cond);
      std::string c = genCond(dw->getCond());
      flushTemps();
      term("core.cond_br " + c + ", " + bname(body) + ", " + bname(end));
      setBlock(end);
    } else if (auto *rf = dyn_cast<CXXForRangeStmt>(S)) {  // for (decl : range): the desugared range/begin/end/cond/inc are in the AST
      pushScope();
      if (rf->getInit()) stmt(rf->getInit());
      stmt(rf->getRangeStmt());
      stmt(rf->getBeginStmt());
      stmt(rf->getEndStmt());
      flushTemps();
      size_t head = newBlock("for"), body = newBlock("body"), inc = newBlock("inc"), end = newBlock("endfor");
      term("core.br " + bname(head));
      setBlock(head);
      at(rf->getCond());
      std::string c = genCond(rf->getCond());
      flushTemps();
      term("core.cond_br " + c + ", " + bname(body) + ", " + bname(end));
      setBlock(body);
      breaks_.push_back(end);
      continues_.push_back(inc);
      breakDepth_.push_back(scopes_.size());
      contDepth_.push_back(scopes_.size());
      pushScope();
      stmt(rf->getLoopVarStmt());
      flushTemps();
      stmt(rf->getBody());
      popScope(true);
      breaks_.pop_back();
      continues_.pop_back();
      breakDepth_.pop_back();
      contDepth_.pop_back();
      if (!blocks_[curBlock_].done) term("core.br " + bname(inc));
      setBlock(inc);
      at(rf->getInc());
      genR(rf->getInc());
      flushTemps();
      term("core.br " + bname(head));
      setBlock(end);
      popScope(true);
    } else if (auto *fs = dyn_cast<ForStmt>(S)) {
      pushScope();
      if (fs->getInit()) stmt(fs->getInit());
      size_t head = newBlock("for"), body = newBlock("body"), inc = newBlock("inc"), end = newBlock("endfor");
      term("core.br " + bname(head));
      setBlock(head);
      if (fs->getCond()) {
        at(fs->getCond());
        std::string c = genCond(fs->getCond());
        flushTemps();
        term("core.cond_br " + c + ", " + bname(body) + ", " + bname(end));
      } else term("core.br " + bname(body));
      setBlock(body);
      loopBody(fs->getBody(), end, inc);
      if (!blocks_[curBlock_].done) term("core.br " + bname(inc));
      setBlock(inc);
      if (fs->getInc()) { at(fs->getInc()); genR(fs->getInc()); flushTemps(); }
      term("core.br " + bname(head));
      setBlock(end);
      popScope(true);
    } else if (isa<BreakStmt>(S)) {
      if (breaks_.empty()) fail(S, "break outside loop/switch");
      unwindTo(breakDepth_.back());
      term("core.br " + bname(breaks_.back()));
    } else if (isa<ContinueStmt>(S)) {
      if (continues_.empty()) fail(S, "continue outside loop");
      unwindTo(contDepth_.back());
      term("core.br " + bname(continues_.back()));
    } else if (auto *gs = dyn_cast<GotoStmt>(S)) {
      term("core.br " + bname(labelBlock(gs->getLabel())));
    } else if (auto *ls = dyn_cast<LabelStmt>(S)) {
      size_t b = labelBlock(ls->getDecl());
      if (!blocks_[curBlock_].done) term("core.br " + bname(b));
      setBlock(b);
      stmt(ls->getSubStmt());
    } else if (auto *sw = dyn_cast<SwitchStmt>(S)) {
      genSwitch(sw);
    } else if (auto *cs = dyn_cast<CaseStmt>(S)) {
      enterCase(cs, cs->getSubStmt());
    } else if (auto *dsn = dyn_cast<DefaultStmt>(S)) {
      enterCase(dsn, dsn->getSubStmt());
    } else if (auto *ts = dyn_cast<CXXTryStmt>(S)) {
      genTry(ts);
    } else if (isa<NullStmt>(S)) {
    } else if (auto *ats = dyn_cast<AttributedStmt>(S)) {
      // [[fallthrough]], [[likely]]/[[unlikely]], [[maybe_unused]], ... on a statement: the attributes themselves
      // carry no runtime semantics we model (no branch-probability hints), only the wrapped statement does.
      stmt(ats->getSubStmt());
    } else if (auto *as = dyn_cast<GCCAsmStmt>(S)) {
      // no outputs: a barrier/hint, a no-op. With outputs the instruction is unknown: every output gets an arbitrary
      // value (a havoc) — the kernel's atomics and bit operations end up here.
      for (unsigned i = 0; i < as->getNumOutputs(); ++i) {
        LV lv = genL(as->getOutputExpr(i));
        if (!isScalarTy(lv.t) || lv.bit) fail(S, "inline asm output of a non-scalar type");
        QualType t = lv.t.getCanonicalType();
        // The name only needs to be unique within this function for readability, but engines key SMT variables by
        // it (TaintDomain::nondet/SymbolicDomain::nondet): under `--link`, two different functions' Nth inline-asm
        // output would otherwise both be named "asmN" and collide on the same SMT variable (asserting a crash when
        // their widths differ, silently aliasing unrelated values when they happen to match). Qualify with the
        // enclosing function's name, matching how globalName() disambiguates static locals the same way.
        std::string v = def("core.nondet {name=\"" + fnName(fd_) + ".asm" + std::to_string(asmCount_++) + "\"} : " + ty(t), "n");
        store(lv, {v, lv.t});
      }
      if (as->isAsmGoto()) fail(S, "asm goto");
    } else if (auto *e = dyn_cast<Expr>(S)) {
      genR(e);
      flushTemps();
    } else {
      fail(S, std::string("statement of kind ") + S->getStmtClassName());
    }
  }
  void enterCase(const SwitchCase *sc, const Stmt *sub) {
    auto it = caseBlocks_.find(sc);
    if (it == caseBlocks_.end()) fail(sc, "case label outside switch");
    if (!blocks_[curBlock_].done) term("core.br " + bname(it->second));
    setBlock(it->second);
    stmt(sub);
  }
  void loopBody(const Stmt *body, size_t brk, size_t cont) {
    breaks_.push_back(brk);
    continues_.push_back(cont);
    breakDepth_.push_back(scopes_.size());
    contDepth_.push_back(scopes_.size());
    pushScope();
    stmt(body);
    popScope(true);
    breaks_.pop_back();
    continues_.pop_back();
    breakDepth_.pop_back();
    contDepth_.pop_back();
  }
  // `catch (...)` matches anything; `catch (T e/&e/const T&e)` matches the thrown static type exactly, or any type
  // derived from `T` (public or not: `dynamic_cast`-style accessibility rules do not apply to `catch`, unlike
  // `dynamic_cast` itself). No support for catching by pointer type, nor for a thrown type related to the caught
  // type only through a user-defined conversion — both are rare in practice and are a diagnosed `fail()` instead
  // of a silent non-match if actually written (see genThrow's fallback for the exceptions this can't resolve).
  bool catchMatches(const CXXCatchStmt *ch, QualType thrownTy, const CXXRecordDecl *thrownRd) {
    if (!ch->getExceptionDecl()) return true;
    QualType caughtTy = ch->getCaughtType().getNonReferenceType().getUnqualifiedType().getCanonicalType();
    if (caughtTy == thrownTy.getUnqualifiedType().getCanonicalType()) return true;
    const CXXRecordDecl *caughtRd = caughtTy->getAsCXXRecordDecl();
    if (!caughtRd || !thrownRd) return false;
    caughtRd = caughtRd->getDefinition();
    const CXXRecordDecl *td = thrownRd->getDefinition();
    if (!caughtRd || !td) return false;
    return td->getCanonicalDecl() == caughtRd->getCanonicalDecl() || td->isDerivedFrom(caughtRd);
  }
  // `throw expr;`: resolved entirely at lowering time, from the STATIC type of `expr` (see `tryStack_`'s comment)
  // against the catch clauses of every `try` enclosing this point IN THIS FUNCTION, innermost first, first match
  // in source order within a given `try` wins (exactly the standard's rule — a `catch (Base&)` before a sibling
  // `catch (Derived&)` silently shadows it, matched here too, not specially diagnosed). No match anywhere in this
  // function: the exception is recorded in the cross-function in-flight-exception globals (see the comment above
  // `genTry`) and handed to our own caller via `propagateToCaller()` — it may have a matching `try` of its own
  // around the call into this function, or may not and hand it further up in turn, recursively, until something
  // catches it or it reaches the harness/entry wrapper with nothing left to propagate to (`HarnessGen.cpp`),
  // which is the only place "uuncaught, full stop" still means this project's pre-existing `terminateProgram`
  // modelling of an uncaught exception (the same noreturn machinery a call to `abort()` uses).
  void genThrow(const CXXThrowExpr *te) {
    const Expr *sub = te->getSubExpr();
    if (!sub) {  // `throw;` (rethrow): no in-flight exception object is tracked outside an active handler, so
                 // which exception would be rethrown is not known here; treat like an unmatched throw.
      terminateProgram("rethrow");
      return;
    }
    QualType thrownTy = sub->getType();
    const CXXRecordDecl *thrownRd = thrownTy->getAsCXXRecordDecl();
    for (auto it = tryStack_.rbegin(); it != tryStack_.rend(); ++it) {
      for (size_t i = 0; i < it->ts->getNumHandlers(); ++i) {
        const CXXCatchStmt *ch = it->ts->getHandler(i);
        if (!catchMatches(ch, thrownTy, thrownRd)) continue;
        // the exception object is constructed from `sub` BEFORE stack unwinding starts (required: `sub` may read
        // locals that unwinding is about to destroy, e.g. `throw MyError(localBuffer);`), then local destructors
        // between the throw point and the `try` run (not of the thrown object itself, nor of subexpression
        // temporaries created while evaluating `sub`: see IMPLEMENTATION_PLAN).
        std::string objPtr;
        if (ch->getExceptionDecl()) {
          std::string obj = def("core.heap_alloc " + c64(static_cast<int64_t>(sizeOf(thrownTy))) + " {fail=never, name=\"exc\"} : ptr", "e");
          initObject({obj, thrownTy, true, false, false}, sub);
          objPtr = obj;
        } else {
          genR(sub);  // `catch (...)`: no binding, but the thrown expression is still evaluated (side effects happen)
          objPtr = zeroOf(ctx_.VoidPtrTy).n;
        }
        unwindTo(it->scopeDepth);
        term("core.br " + bname(it->catchBlocks[i]) + "(" + objPtr + ")");
        return;
      }
    }
    // no `try` in this function catches it: always construct the object (some ancestor caller's `catch` may yet
    // bind it, and we cannot know in advance whether that one will be `catch (...)` or a typed one), record it,
    // and propagate to our own caller instead of ending the whole program here.
    std::string obj = def("core.heap_alloc " + c64(static_cast<int64_t>(sizeOf(thrownTy))) + " {fail=never, name=\"exc\"} : ptr", "e");
    initObject({obj, thrownTy, true, false, false}, sub);
    auto [tn, tsz] = typeInfoMarker(ctx_, thrownTy);
    std::string tmark = def("core.global_addr @" + tn + " {size=" + std::to_string(tsz) + "} : ptr", "tm");
    emit("core.store " + obj + ", " + excObjSlot() + " {waived=\"object known\"}");
    emit("core.store " + tmark + ", " + excTypeSlot() + " {waived=\"object known\"}");
    propagateToCaller();
  }
  // `try { B } catch (T1 e1) { H1 } catch (T2 e2) { H2 } ...`: the catch blocks are allocated up front (so a
  // `throw` anywhere inside `B`, found while lowering it, can branch straight to the one it resolves to) but
  // filled in afterwards, in the (popped) context of the *enclosing* try, if any — a `throw` inside a handler body
  // must not be caught by a sibling handler of the same `try`, only by a further-out one.
  // ---- cross-function exception propagation (see IMPLEMENTATION_PLAN "跨函数异常传播"): two plain global `ptr`
  // slots carry an in-flight exception across a function-call boundary without changing any function's signature
  // or the three execution engines at all — `emitCall` (the one chokepoint every ordinary/virtual/operator-new/
  // operator-delete call funnels through) checks them after every call in a C++ translation unit and, if set,
  // either jumps to a matching `catch` of this function (same lookup `genThrow` already does for a local `throw`,
  // just driven by a *runtime* marker comparison here since the callee's thrown type isn't known at this call
  // site's lowering time — unlike `genThrow`'s local case, where it's the throw-expression's compile-time-known
  // static type) or, if nothing here matches, hands it to OUR OWN caller the same way (an early `core.return`,
  // recursively). `@__hlir_exc_obj` holds the exception object's address (null = no exception in flight);
  // `@__hlir_exc_type` holds its RTTI marker (`typeInfoMarker`) for matching.
  std::string excObjSlot() { return def("core.global_addr @__hlir_exc_obj {size=8} : ptr", "eo"); }
  std::string excTypeSlot() { return def("core.global_addr @__hlir_exc_type {size=8} : ptr", "et"); }
  // branchless "terminate if an exception escaped the call just emitted and nothing here is set up to catch it"
  // — call sites that do not get the full matching-and-propagation treatment (constructor/destructor base/member
  // chaining, a lazily-initialised global/string's call, a virtual dispatcher's call to the real overrider: see
  // IMPLEMENTATION_PLAN for why these specific shapes are out of scope) use this instead, exactly
  // `terminateProgram`'s mechanism but with a real (not unconditionally false) assumed condition.
  void emitExcEscapeGuard() {
    if (!isCxxCtx(ctx_)) return;
    std::string ev = def("core.load " + excObjSlot() + " {waived=\"object known\"} : ptr", "ev");
    std::string ok = def("core.is_null " + ev + " : bool", "ok");
    emit("core.assume " + ok + " {terminates=\"uncaught_exception\"}");
  }
  // the RTTI markers a cross-function catch clause declaring `caughtTy` must be checked against: itself, plus
  // every class of this module derived from it (mirrors `dynCastDispatcher`'s candidate enumeration) — a thrown
  // object's marker is always its throw-expression's exact static type's marker (see `genThrow`), never some
  // further-derived runtime type's, so (unlike `dynCastDispatcher`) there is no vptr to load from the object
  // itself here, only the fixed marker `genThrow` recorded at the point it threw.
  std::vector<std::pair<std::string, uint64_t>> candidateMarkers(QualType caughtTy) {
    std::vector<std::pair<std::string, uint64_t>> out;
    out.push_back(typeInfoMarker(ctx_, caughtTy));
    const CXXRecordDecl *caughtRd = caughtTy->getAsCXXRecordDecl();
    if (caughtRd && caughtRd->getDefinition()) {
      caughtRd = caughtRd->getDefinition();
      for (const CXXRecordDecl *D : mod_.classes)
        if (D->getCanonicalDecl() != caughtRd->getCanonicalDecl() && D->isDerivedFrom(caughtRd)) out.push_back(typeInfoMarker(ctx_, ctx_.getRecordType(D)));
    }
    return out;
  }
  // jump into a `try` frame's catch handler from the cross-function path: unwind this function's scopes down to
  // the try's own depth (same mechanism `genThrow` uses for a local throw), clear the in-flight-exception globals
  // (this call site is about to consume it; anything the handler itself calls must see "no exception in flight"
  // until/unless it throws something new), and branch in with the exception object as the handler's parameter.
  void jumpToCatch(const TryFrame &frame, size_t handlerIdx, const std::string &objPtr) {
    unwindTo(frame.scopeDepth);
    std::string z = zeroOf(ctx_.VoidPtrTy).n;
    emit("core.store " + z + ", " + excObjSlot() + " {waived=\"object known\"}");
    emit("core.store " + z + ", " + excTypeSlot() + " {waived=\"object known\"}");
    term("core.br " + bname(frame.catchBlocks[handlerIdx]) + "(" + objPtr + ")");
  }
  // this function does not (or no longer, having exhausted its own `try`s) handle the in-flight exception: unwind
  // everything still live here and hand it to our own caller exactly like a plain `return` would, with a
  // throwaway value of the right shape (void/sret: nothing to write; reference: a null `ptr`; scalar: zero) —
  // the caller's own `emitCall`-inserted check (or, for the handful of call shapes that do not get one, an
  // `emitExcEscapeGuard`) picks it up from here, recursively, until something catches it or it reaches the
  // harness/entry wrapper (`HarnessGen.cpp`), the only place an exception escaping *everything* becomes the
  // pre-existing `terminateProgram`-style "uncaught exception" outcome.
  void propagateToCaller() {
    unwindTo(0);
    if (!fd_ || fd_->getReturnType()->isVoidType() || !sret_.empty()) term("core.return");
    else if (fd_->getReturnType()->isReferenceType()) term("core.return " + zeroOf(ctx_.VoidPtrTy).n);
    else term("core.return " + zeroOf(fd_->getReturnType()).n);
  }
  // after a call this function made has left an exception in flight: look for a matching `catch` among every
  // `try` enclosing THIS point in this function (innermost first, source order within each, exactly `genThrow`'s
  // local search — only driven by runtime marker comparisons here instead of a compile-time-resolved jump);
  // nothing matches anywhere in this function: `propagateToCaller()`.
  void genExceptionDispatch() {
    std::string typev = def("core.load " + excTypeSlot() + " {waived=\"object known\"} : ptr", "tv");
    std::string objv = def("core.load " + excObjSlot() + " {waived=\"object known\"} : ptr", "ov");
    for (auto it = tryStack_.rbegin(); it != tryStack_.rend(); ++it) {
      for (size_t i = 0; i < it->ts->getNumHandlers(); ++i) {
        const CXXCatchStmt *ch = it->ts->getHandler(i);
        if (!ch->getExceptionDecl()) {  // catch (...): matches unconditionally, no marker check needed
          jumpToCatch(*it, i, objv);
          return;
        }
        QualType caughtTy = ch->getCaughtType().getNonReferenceType().getUnqualifiedType();
        std::set<std::string> seen;
        for (auto &marker : candidateMarkers(caughtTy)) {
          if (!seen.insert(marker.first).second) continue;
          std::string m = def("core.global_addr @" + marker.first + " {size=" + std::to_string(marker.second) + "} : ptr", "m");
          std::string eq = def("core.ptr_cmp eq " + typev + ", " + m + " : bool", "eq");
          size_t hit = newBlock("exc_hit"), nx = newBlock("exc_cont");
          term("core.cond_br " + eq + ", " + bname(hit) + ", " + bname(nx));
          setBlock(hit);
          jumpToCatch(*it, i, objv);
          setBlock(nx);  // the chain continues here: next candidate marker, next catch clause, or eventually propagateToCaller()
        }
      }
    }
    propagateToCaller();
  }
  void genTry(const CXXTryStmt *ts) {
    size_t end = newBlock("try_end");
    TryFrame frame{ts, {}, scopes_.size()};
    std::vector<size_t> handlerBlocks;
    for (unsigned i = 0; i < ts->getNumHandlers(); ++i) {
      size_t b = newBlock("catch");
      blocks_[b].params = fresh("exc") + ": ptr";
      handlerBlocks.push_back(b);
      frame.catchBlocks.push_back(b);
    }
    tryStack_.push_back(frame);
    pushScope();
    stmt(ts->getTryBlock());
    popScope(true);
    tryStack_.pop_back();
    if (!blocks_[curBlock_].done) term("core.br " + bname(end));
    for (unsigned i = 0; i < ts->getNumHandlers(); ++i) {
      const CXXCatchStmt *ch = ts->getHandler(i);
      setBlock(handlerBlocks[i]);
      std::string excParam = blocks_[handlerBlocks[i]].params.substr(0, blocks_[handlerBlocks[i]].params.find(':'));
      pushScope();
      if (const VarDecl *ex = ch->getExceptionDecl()) {
        if (ex->getType()->isReferenceType()) {  // same convention as any other reference local: the slot holds the address
          std::string rs = newSlot(ctx_.VoidPtrTy, ex->getName().str());
          store({rs, ctx_.VoidPtrTy, true, false, false}, {excParam, ctx_.VoidPtrTy});
          locals_[ex] = rs;
        } else locals_[ex] = excParam;  // by-value catch: alias the thrown temporary directly (see genThrow's comment)
      }
      stmt(ch->getHandlerBlock());
      popScope(true);
      if (!blocks_[curBlock_].done) term("core.br " + bname(end));
    }
    setBlock(end);
  }
  void collectCases(const Stmt *s, std::vector<const SwitchCase *> &out) {
    if (!s) return;
    if (auto *sc = dyn_cast<SwitchCase>(s)) out.push_back(sc);
    if (isa<SwitchStmt>(s)) return;  // a nested switch owns its labels
    for (auto *c : s->children()) collectCases(c, out);
  }
  void genSwitch(const SwitchStmt *sw) {
    if (sw->getInit()) fail(sw, "switch with init");
    V v = genR(sw->getCond());
    std::vector<const SwitchCase *> cases;
    collectCases(sw->getBody(), cases);
    size_t end = newBlock("endswitch");
    std::string list;
    size_t dflt = end;
    auto addLabel = [&](int64_t val, size_t b) {
      llvm::APInt a(64, static_cast<uint64_t>(val), true);
      a = a.sextOrTrunc(bits(v.t));
      llvm::SmallString<24> s;
      a.toStringSigned(s);
      list += (list.empty() ? "" : ", ") + std::string(s) + ": " + bname(b);
    };
    // GNU case ranges (`case LO ... HI:`) wider than this are checked as an explicit interval compare
    // before the switch dispatch instead of being expanded into individual `core.switch` labels (e.g.
    // `case PT_LOPROC ... PT_HIPROC:` spans ~268M values in real kernel headers) — see below.
    std::vector<std::pair<std::pair<int64_t, int64_t>, size_t>> wideRanges;
    for (auto *sc : cases) {
      size_t b = newBlock(isa<CaseStmt>(sc) ? "case" : "default");
      caseBlocks_[sc] = b;
      if (auto *cs = dyn_cast<CaseStmt>(sc)) {
        Expr::EvalResult r;
        if (!cs->getLHS()->EvaluateAsInt(r, ctx_)) fail(sc, "non-constant case label");
        int64_t lo = apExt(r.Val.getInt());
        if (cs->getRHS()) {  // GNU case range: expand, or check as an interval if too wide to expand
          Expr::EvalResult r2;
          if (!cs->getRHS()->EvaluateAsInt(r2, ctx_)) fail(sc, "non-constant case range");
          int64_t hi = apExt(r2.Val.getInt());
          if (hi - lo > 4096) wideRanges.push_back({{lo, hi}, b});
          else for (int64_t x = lo; x <= hi; ++x) addLabel(x, b);
        } else addLabel(lo, b);
      } else dflt = b;
    }
    // A wide range can't be a `core.switch` label (the label list would be enormous), so each one is a
    // pair of interval compares in its own blocks, tried before the switch itself: match -> branch straight
    // to the case block, no match -> fall through to the next range check (and finally the switch). C
    // forbids overlapping case values/ranges, so at most one of these (and the switch's own labels) ever
    // matches; this doesn't change which block is reached, only how a wide range's membership is tested.
    for (auto &wr : wideRanges) {
      int64_t lo = wr.first.first, hi = wr.first.second;
      size_t caseB = wr.second;
      const char *geOp = isSigned(v.t) ? "sge" : "uge", *leOp = isSigned(v.t) ? "sle" : "ule";
      size_t checkHi = newBlock("rangehi"), next = newBlock("rangenext");
      std::string ge = def("core.icmp " + std::string(geOp) + " " + v.n + ", " + konst(lo, v.t).n + " : bool");
      term("core.cond_br " + ge + ", " + bname(checkHi) + ", " + bname(next));
      setBlock(checkHi);
      std::string le = def("core.icmp " + std::string(leOp) + " " + v.n + ", " + konst(hi, v.t).n + " : bool");
      term("core.cond_br " + le + ", " + bname(caseB) + ", " + bname(next));
      setBlock(next);
    }
    term("core.switch " + v.n + " [" + list + "] default " + bname(dflt));
    breaks_.push_back(end);
    breakDepth_.push_back(scopes_.size());
    // the switch terminator closed the current block; the labels inside the body open their own blocks
    pushScope();
    stmt(sw->getBody());
    popScope(true);
    breaks_.pop_back();
    breakDepth_.pop_back();
    if (!blocks_[curBlock_].done) term("core.br " + bname(end));
    setBlock(end);
  }

  void declare(const Decl *d) {
    auto *vd = dyn_cast<VarDecl>(d);
    if (!vd) {
      if (isa<TypedefDecl>(d) || isa<TypeAliasDecl>(d) || isa<RecordDecl>(d) || isa<EnumDecl>(d) || isa<FunctionDecl>(d) || isa<StaticAssertDecl>(d) || isa<LabelDecl>(d) ||
          isa<UsingDecl>(d) || isa<UsingDirectiveDecl>(d) || isa<UsingShadowDecl>(d) || isa<NamespaceAliasDecl>(d) || isa<FunctionTemplateDecl>(d) || isa<ClassTemplateDecl>(d) || isa<TypeAliasTemplateDecl>(d)) return;  // __label__ x; using ...;
      failDecl(d, "declaration");
    }
    if (vd->hasGlobalStorage()) return;  // static locals are globals, initialized on first access
    QualType t = vd->getType();
    loc_ = vd->getLocation();
    if (ctx_.getAsVariableArrayType(t)) {  // a heap object of the computed size (flat, row-major); never freed
      if (vd->getInit()) failDecl(vd, "initialized variable length array");
      std::string bytes = vlaFlatBytes(t);
      locals_[vd] = def("core.heap_alloc " + bytes + " {fail=never, name=\"vla\"} : ptr", "v");
      return;
    }
    if (t->isReferenceType()) {  // the slot holds the address of the object
      std::string rs = newSlot(ctx_.VoidPtrTy, vd->getName().str());
      locals_[vd] = rs;
      if (!vd->getInit()) failDecl(vd, "reference without an initializer");
      LV target = genL(vd->getInit());
      store({rs, ctx_.VoidPtrTy, true, false, false}, {target.p, ctx_.VoidPtrTy});
      declareBindings(vd);
      return;
    }
    std::string slot = newSlot(t, vd->getName().str());
    locals_[vd] = slot;
    if (const Expr *init = vd->getInit()) initObject({slot, t, true, false, false}, init);
    registerDtor(slot, t);
    declareBindings(vd);
  }
  // A C++17 `auto [a, b] = expr;` is one DecompositionDecl (handled like any other local above, since it
  // IS-A VarDecl) plus a BindingDecl per name that is NOT a VarDecl and so never appears in a DeclStmt's
  // own decls() list - only nested inside the DecompositionDecl. For the tuple-like case (std::pair/tuple/
  // anything with a `get<N>`) each binding has a hidden "holding var": a reference VarDecl initialized to
  // the `get<N>(...)` call, which must be declared (added to `locals_`) the same way any other local is,
  // just like the surrounding DecompositionDecl is. The array/struct decomposition case has no holding var
  // (genL re-evaluates `getBinding()` directly on every use), so there is nothing to declare here for it.
  void declareBindings(const VarDecl *vd) {
    auto *dcd = dyn_cast<DecompositionDecl>(vd);
    if (!dcd) return;
    for (const BindingDecl *bd : dcd->bindings())
      if (VarDecl *hv = bd->getHoldingVar()) declare(hv);
  }
  void initObject(const LV &lv, const Expr *init) {
    QualType t = lv.t.getCanonicalType();
    at(init);
    const Expr *e = init->IgnoreParens();
    for (;;) {  // wrappers that only matter for cleanups: the object is built in place
      if (auto *ewc = dyn_cast<ExprWithCleanups>(e)) { e = ewc->getSubExpr()->IgnoreParens(); continue; }
      if (auto *bt = dyn_cast<CXXBindTemporaryExpr>(e)) { e = bt->getSubExpr()->IgnoreParens(); continue; }
      if (auto *dae = dyn_cast<CXXDefaultArgExpr>(e)) { e = dae->getExpr()->IgnoreParens(); continue; }
      if (auto *die = dyn_cast<CXXDefaultInitExpr>(e)) { e = die->getExpr()->IgnoreParens(); continue; }
      if (isRecordTy(t))
        if (auto *ice = dyn_cast<CastExpr>(e))
          if (ice->getCastKind() == CK_NoOp || ice->getCastKind() == CK_ConstructorConversion || ice->getCastKind() == CK_UserDefinedConversion) { e = ice->getSubExpr()->IgnoreParens(); continue; }
      break;
    }
    if (lv.t->isReferenceType()) {  // a reference member/element: the slot holds the address of the referenced object
      LV target = genL(e);
      store({lv.p, ctx_.VoidPtrTy, lv.direct, false, false}, {target.p, ctx_.VoidPtrTy});
      return;
    }
    if (auto *cx = dyn_cast<CXXConstructExpr>(e)) { constructInto(lv.p, cx); return; }
    if (auto *al = dyn_cast<ArrayInitLoopExpr>(e)) {  // copy of an array of objects, element by element
      OpaqueValueExpr *common = al->getCommonExpr();
      LV src = genL(common->getSourceExpr());
      opaque_[common] = V{src.p, common->getType()};
      uint64_t n = al->getArraySize().getZExtValue();
      if (n > 256) fail(e, "copy of an array of more than 256 objects");
      QualType et = al->getSubExpr()->getType();
      uint64_t saved = arrIdx_;
      for (uint64_t i = 0; i < n; ++i) {
        arrIdx_ = i;
        initObject({i ? inObj(lv.p, i * sizeOf(et)) : lv.p, et, true, false, false}, al->getSubExpr());
      }
      arrIdx_ = saved;
      return;
    }
    if (auto *ic = dyn_cast<CXXInheritedCtorInitExpr>(e)) {  // `using Base::Base`: the inherited constructor gets this constructor's arguments
      const CXXConstructorDecl *bc = ic->getConstructor();
      useFunction(bc);
      ensureDeclared(bc);
      bool asBase = hasBaseVariant(bc) && ic->getConstructionKind() != CXXConstructionKind::Complete;
      std::string a = lv.p + (asBase ? vbaseArgs(bc->getParent()) : "");
      for (const ParmVarDecl *pd : fd_->parameters()) a += ", " + pnames_.at(pd);
      if (asBase) { ensureBaseDeclared(bc); emit("core.call @" + baseVariantName(bc) + "(" + a + ")"); }
      else emit("core.call @" + fnName(bc) + "(" + a + ")");
      emitExcEscapeGuard();
      return;
    }
    if (auto *le = dyn_cast<LambdaExpr>(e)) {  // the captures initialise the closure's members in order
      auto fi = le->getLambdaClass()->field_begin();
      for (const Expr *ci : le->capture_inits()) {
        if (fi == le->getLambdaClass()->field_end()) break;
        LV fl{fieldAddr(lv.p, *fi), (*fi)->getType(), true, false, false};
        initMember(fl, ci);
        ++fi;
      }
      return;
    }
    if (isRecordTy(t))
      if (auto *co = dyn_cast<ConditionalOperator>(e); co && !co->isLValue()) {  // each arm builds the object in place
        std::string c = genCond(co->getCond());
        size_t tb = newBlock("then"), eb = newBlock("else"), end = newBlock("end");
        term("core.cond_br " + c + ", " + bname(tb) + ", " + bname(eb));
        setBlock(tb);
        pushScope();
        initObject(lv, co->getTrueExpr());
        popScope(true);
        term("core.br " + bname(end));
        setBlock(eb);
        pushScope();
        initObject(lv, co->getFalseExpr());
        popScope(true);
        term("core.br " + bname(end));
        setBlock(end);
        return;
      }
    if (isRecordTy(t))
      if (auto *call = dyn_cast<CallExpr>(e))
        if (!call->getDirectCallee() || call->getDirectCallee()->isVariadic() || true) {
          if (call->getDirectCallee()) { genCall(call, lv.p); return; }  // the callee writes the result object in place
        }
    if (isa<CXXScalarValueInitExpr>(e)) { store(lv, zeroOf(lv.t)); return; }
    if (isScalarTy(t)) {
      if (auto *il = dyn_cast<InitListExpr>(e)) {  // int x = {5};
        if (il->getNumInits() == 0) store(lv, zeroOf(lv.t));
        else initObject(lv, il->getInit(0));
        return;
      }
      store(lv, genR(init));
      return;
    }
    if (auto *il = dyn_cast<InitListExpr>(e)) {
      // aggregates: zero everything, then store the explicit initializers
      emit("core.memset " + lv.p + ", " + def("core.const 0 : i8", "c") + ", " + c64(static_cast<int64_t>(sizeOf(t))));
      if (t->isArrayType()) {
        QualType et = ctx_.getAsArrayType(t)->getElementType();
        for (unsigned i = 0; i < il->getNumInits(); ++i) {
          const Expr *ie = il->getInit(i);
          if (!ie || isa<ImplicitValueInitExpr>(ie)) continue;
          initObject({inObj(lv.p, i * sizeOf(et)), et, true, false, false}, ie);
        }
        if (const Expr *fill = il->getArrayFiller())  // the rest of an array of class objects is built by the filler's constructor
          if (!isa<ImplicitValueInitExpr>(fill))
            if (const ConstantArrayType *cat = ctx_.getAsConstantArrayType(t))
              for (uint64_t i = il->getNumInits(); i < cat->getSize().getZExtValue(); ++i) initObject({inObj(lv.p, i * sizeOf(et)), et, true, false, false}, fill);
        return;
      }
      if (auto *rd = t->getAsRecordDecl()) {
        if (rd->isUnion()) {
          const FieldDecl *f = il->getInitializedFieldInUnion();
          if (f && il->getNumInits() && il->getInit(0)) initField(lv, f, il->getInit(0));
          return;
        }
        unsigned i = 0;
        // C++17 aggregates may have public, non-virtual direct base classes; the standard treats
        // those base subobjects as if they were the leading elements of the initializer list, ahead
        // of the derived class's own fields (consumed here in declaration order, same as fields below).
        if (auto *crd = dyn_cast<CXXRecordDecl>(rd); crd && crd->getNumBases()) {
          if (!layoutSane(ctx_.getRecordType(rd))) fail(init, "aggregate initialization of a record whose layout is invalid or incomplete");
          const ASTRecordLayout &L = ctx_.getASTRecordLayout(rd);
          for (const auto &b : crd->bases()) {
            if (i >= il->getNumInits()) break;
            const Expr *bi = il->getInit(i++);
            auto *brd = b.getType()->getAsCXXRecordDecl();
            if (!bi || isa<ImplicitValueInitExpr>(bi) || !brd) continue;
            uint64_t boff = L.getBaseClassOffset(brd).getQuantity();
            initObject({inObj(lv.p, boff), b.getType(), true, false, false}, bi);
          }
        }
        for (auto *f : rd->fields()) {
          if (i >= il->getNumInits()) break;
          const Expr *fi = il->getInit(i++);
          if (f->isUnnamedBitfield() || !fi || isa<ImplicitValueInitExpr>(fi)) continue;
          initField(lv, f, fi);
        }
        return;
      }
    }
    if (auto *sl = dyn_cast<StringLiteral>(e)) {
      StringRef s = sl->getString();
      emit("core.memset " + lv.p + ", " + def("core.const 0 : i8", "c") + ", " + c64(static_cast<int64_t>(sizeOf(t))));
      for (size_t i = 0; i < s.size() && i < sizeOf(t); ++i) {
        std::string b = def("core.const " + std::to_string(static_cast<int>(static_cast<signed char>(s[i]))) + " : i8", "c");
        emit("core.store " + b + ", " + inObj(lv.p, i) + " {waived=\"in-bounds by construction\"}");
      }
      return;
    }
    if (t->isRecordType()) {  // struct copy-initialization from another struct (or a call)
      copyBytes(lv, genL(e), sizeOf(t));
      return;
    }
    fail(init, "initializer of type '" + t.getAsString() + "'");
  }
  void initField(const LV &lv, const FieldDecl *f, const Expr *fi) {
    if (!layoutSane(ctx_.getRecordType(f->getParent()))) fail(fi, "initializer of a record whose layout is invalid or incomplete");
    const ASTRecordLayout &L = ctx_.getASTRecordLayout(f->getParent());
    uint64_t bo = L.getFieldOffset(f->getFieldIndex());
    LV fl{inObj(lv.p, bo / 8), f->getType(), true, false, false};
    if (f->isBitField()) {
      fl.bit = true;
      fl.bitSh = static_cast<unsigned>(bo % 8);
      fl.bitW = f->getBitWidthValue(ctx_);
    }
    initObject(fl, fi);
  }
};

// ---- function facts for the scanner
bool structHasPointers(const RecordDecl *rd, unsigned depth = 0) {
  if (depth > 4) return false;
  for (auto *f : rd->fields()) {
    QualType t = f->getType().getCanonicalType();
    if (t->isPointerType()) return true;
    while (t->isArrayType()) t = cast<ArrayType>(t)->getElementType().getCanonicalType();
    if (t->isPointerType()) return true;
    if (auto *r = t->getAsRecordDecl()) if (structHasPointers(r, depth + 1)) return true;
  }
  return false;
}
// What the code reveals about a pointer that is declared as something else (`void *`, or a pointer to an embedded member):
//   (struct T *)x->f / struct T *t = x->f;               -> f points to a T            (off = 0)
//   container_of(x->f, struct T, member) i.e.
//   (struct T *)((char *)x->f - offsetof(T, member))     -> f points at byte `member offset` of a T
// the same for a pointer parameter. Conflicting uses (different T or offset) drop the hint.
// `viaSub`: this hint came from a genuine container_of subtraction (`off` can legitimately be 0 -- the member is the
// struct's first field), not just a `(T*)x` cast that reveals a `void*`'s real pointee type (where `off` is always 0
// but means nothing -- there is no embedding, just a type reveal). The two cases used to be indistinguishable from
// `off` alone, which made an offset-0 container_of look exactly like "no hint" to any `if (p.at)`-style check.
struct PtrHint { const RecordDecl *rd = nullptr; uint64_t off = 0; bool viaSub = false; };
struct PtrHints {
  std::map<const FieldDecl *, PtrHint> fields;
  std::map<const ParmVarDecl *, PtrHint> params;
  std::map<const ParmVarDecl *, const RecordDecl *> userData;  // handle parameter -> struct its user-data getter result is converted to
  std::set<const RecordDecl *> freedTypes;                      // structs the code frees (the user data of such a type is a heap object)
  // fields the analysed code (main-file functions and the header functions they reach) actually reads or writes: only
  // pointer fields in this set get an object (a kernel `struct file` has hundreds of pointer fields nobody touches)
  std::set<const FieldDecl *> used;
  // pointer fields some body in the analysed set tests for NULL: these, and only these, may be synthesised as NULL
  // (see PtrFieldInfo::nullTested). A subset of `used` by construction -- a test is a read.
  std::set<const FieldDecl *> nullTested;
  bool restrictToUsed = false;
  // --link only: a field that fails the `used` check here is kept anyway (marked pendingLinkUse) instead of dropped,
  // because another, not-yet-seen unit may read it through a call this file cannot see the body of. See LowerResult::fieldUses.
  bool linkMode = false;
  // memoizes collectPtrFields' top-level result per (struct, depth): everything that result depends on (`used`,
  // `fields`, `linkMode`, ...) is fixed for the lifetime of one TU's hints, and every top-level call starts from
  // baseBits=0 with a fresh `path`, so the same (RecordDecl*, depth) always recomputes the identical tree. Without
  // this, a struct passed to many functions in one file (e.g. `struct amdgpu_device *adev`, ~150 functions in a
  // single real-world file) redoes the same multi-thousand-pointer-field walk once per function: this is what
  // actually dominates --list/--link wall time on kernel-sized structs, not any particular field-use/link logic.
  mutable std::map<std::pair<const RecordDecl *, unsigned>, std::shared_ptr<std::vector<PtrFieldInfo>>> ptrFieldsCache;
};
// collects the fields accessed in a function body and the functions it calls (with a body)
class FieldUseFinder : public RecursiveASTVisitor<FieldUseFinder> {
 public:
  FieldUseFinder(ASTContext &ctx, std::set<const FieldDecl *> &used, std::set<const FieldDecl *> &nullTested,
                 std::vector<const FunctionDecl *> &callees)
      : ctx_(ctx), used_(used), nullTested_(nullTested), callees_(callees) {}
  bool VisitMemberExpr(MemberExpr *me) {
    if (auto *f = dyn_cast<FieldDecl>(me->getMemberDecl())) used_.insert(f);
    else if (auto *ind = dyn_cast<IndirectFieldDecl>(me->getMemberDecl()))
      for (auto *nd : ind->chain())
        if (auto *f = dyn_cast<FieldDecl>(nd)) used_.insert(f);
    return true;
  }
  bool VisitCallExpr(CallExpr *c) {
    if (auto *fd = c->getDirectCallee())
      if (auto *def = fd->getDefinition()) callees_.push_back(def);
    return true;
  }
  // the three ways C code says "this pointer field may be NULL": a comparison against a null pointer constant, a
  // `!p->f`, and a bare `p->f` in a condition. Anything else (a cast, an assignment, passing it along) says nothing.
  bool VisitBinaryOperator(BinaryOperator *b) {
    if (b->getOpcode() == BO_EQ || b->getOpcode() == BO_NE) {
      if (isNullConst(b->getRHS())) markPtr(b->getLHS());
      if (isNullConst(b->getLHS())) markPtr(b->getRHS());
    } else if (b->getOpcode() == BO_LAnd || b->getOpcode() == BO_LOr) {
      markPtr(b->getLHS());
      markPtr(b->getRHS());
    }
    return true;
  }
  bool VisitUnaryOperator(UnaryOperator *u) {
    if (u->getOpcode() == UO_LNot) markPtr(u->getSubExpr());
    return true;
  }
  bool VisitIfStmt(IfStmt *s) { markPtr(s->getCond()); return true; }
  bool VisitWhileStmt(WhileStmt *s) { markPtr(s->getCond()); return true; }
  bool VisitDoStmt(DoStmt *s) { markPtr(s->getCond()); return true; }
  bool VisitForStmt(ForStmt *s) { markPtr(s->getCond()); return true; }
  bool VisitConditionalOperator(ConditionalOperator *c) { markPtr(c->getCond()); return true; }

 private:
  bool isNullConst(const Expr *e) {
    return e && e->isNullPointerConstant(ctx_, Expr::NPC_ValueDependentIsNotNull) != Expr::NPCK_NotNull;
  }
  // `e`, once the parens/casts C puts around a condition are stripped, is a read of a pointer-typed field
  void markPtr(const Expr *e) {
    if (!e) return;
    const auto *me = dyn_cast<MemberExpr>(e->IgnoreParenImpCasts());
    if (!me || !me->getType().getCanonicalType()->isPointerType()) return;
    if (auto *f = dyn_cast<FieldDecl>(me->getMemberDecl())) nullTested_.insert(f);
  }
  ASTContext &ctx_;
  std::set<const FieldDecl *> &used_;
  std::set<const FieldDecl *> &nullTested_;
  std::vector<const FunctionDecl *> &callees_;
};
// `struct T *t = wl_resource_get_user_data(res);` with `res` a parameter: the handle's user data is a T. Conflicting types drop the hint.
class UserDataFinder : public RecursiveASTVisitor<UserDataFinder> {
 public:
  UserDataFinder(const std::set<std::string> &getters, const SourceManager &sm) : getters_(getters), sm_(sm) {}
  std::map<const ParmVarDecl *, const RecordDecl *> found;
  std::set<const ParmVarDecl *> conflicts;
  std::set<const RecordDecl *> freedTypes;  // structs whose pointers are passed to free()-like functions
  // `f(res) { g(res); }` where g's parameter has user data: so does f's (the handle is only passed down)
  struct Edge { const ParmVarDecl *caller, *callee; };
  std::vector<Edge> edges;
  bool VisitCallExpr(CallExpr *call) {
    if (!sm_.isInMainFile(sm_.getExpansionLoc(call->getBeginLoc()))) return true;
    if (auto *fd = call->getDirectCallee()) {
      std::string n = fd->getIdentifier() ? fd->getName().str() : "";
      if ((n == "free" || n == "kfree" || n == "g_free" || (n.size() > 5 && n.compare(n.size() - 5, 5, "_free") == 0)) && call->getNumArgs() >= 1) {
        QualType at = call->getArg(0)->IgnoreParenImpCasts()->getType().getCanonicalType();
        if (at->isPointerType())
          if (auto *rd = at->getPointeeType()->getAsRecordDecl())
            if (rd->getDefinition()) freedTypes.insert(rd->getDefinition());
      }
    }
    const FunctionDecl *callee = call->getDirectCallee() ? call->getDirectCallee()->getDefinition() : nullptr;
    if (!callee) return true;
    for (unsigned i = 0; i < call->getNumArgs() && i < callee->getNumParams(); ++i)
      if (auto *dr = dyn_cast<DeclRefExpr>(call->getArg(i)->IgnoreParenImpCasts()))
        if (auto *pd = dyn_cast<ParmVarDecl>(dr->getDecl())) edges.push_back({pd, callee->getParamDecl(i)});
    return true;
  }
  void propagate() {
    for (int pass = 0; pass < 6; ++pass) {
      bool changed = false;
      for (auto &e : edges) {
        auto from = found.find(e.callee);
        if (from == found.end() || found.count(e.caller) || conflicts.count(e.caller)) continue;
        found[e.caller] = from->second;
        changed = true;
      }
      if (!changed) break;
    }
  }
  bool VisitCastExpr(CastExpr *ce) {
    if (ce->getCastKind() != CK_BitCast || !sm_.isInMainFile(sm_.getExpansionLoc(ce->getBeginLoc()))) return true;
    auto *call = dyn_cast<CallExpr>(ce->getSubExpr()->IgnoreParens());
    if (!call || !call->getDirectCallee() || !getters_.count(call->getDirectCallee()->getIdentifier() ? call->getDirectCallee()->getName().str() : "") || call->getNumArgs() < 1) return true;
    QualType to = ce->getType().getCanonicalType();
    if (!to->isPointerType()) return true;
    const RecordDecl *rd = to->getPointeeType()->getAsRecordDecl();
    if (!rd || !rd->getDefinition()) return true;
    rd = rd->getDefinition();
    auto *dr = dyn_cast<DeclRefExpr>(call->getArg(0)->IgnoreParenImpCasts());
    auto *pd = dr ? dyn_cast<ParmVarDecl>(dr->getDecl()) : nullptr;
    if (!pd) return true;
    auto it = found.find(pd);
    if (it == found.end()) found[pd] = rd;
    else if (it->second != rd) conflicts.insert(pd);
    return true;
  }

 private:
  const std::set<std::string> &getters_;
  const SourceManager &sm_;
};

class PtrHintFinder : public RecursiveASTVisitor<PtrHintFinder> {
 public:
  PtrHintFinder(PtrHints &h, std::set<const void *> &conflicts, const SourceManager &sm) : h_(h), conflicts_(conflicts), sm_(sm) {}
  // an opaque handle passed down: `f(void *b) { g(b); }` where g casts its parameter to a struct reveals b's type
  // too. The "handle" can equally be a struct field read into a local first (`struct sock *sk = sock->sk;
  // alg_sk(sk);`, the common kernel `embed struct X as the first member, provide a static-inline (Derived*)
  // accessor` idiom) -- root() already resolves that chain back to the field, so the edge just needs to carry
  // either a parameter or a field as its caller-side key, not only a parameter.
  struct Edge { const ParmVarDecl *callerParam = nullptr; const FieldDecl *callerField = nullptr; const ParmVarDecl *callee = nullptr; };
  std::vector<Edge> edges;
  bool VisitCallExpr(CallExpr *call) {
    if (!sm_.isInMainFile(sm_.getExpansionLoc(call->getBeginLoc()))) return true;
    const FunctionDecl *callee = call->getDirectCallee() ? call->getDirectCallee()->getDefinition() : nullptr;
    if (!callee) return true;
    for (unsigned i = 0; i < call->getNumArgs() && i < callee->getNumParams(); ++i) {
      const FieldDecl *fd = nullptr;
      const ParmVarDecl *pd = nullptr;
      root(call->getArg(i), 0, fd, pd);
      if (pd) edges.push_back({pd, nullptr, callee->getParamDecl(i)});
      else if (fd) edges.push_back({nullptr, fd, callee->getParamDecl(i)});
    }
    return true;
  }
  // Shared pass/inherit rule for one caller-side slot (a parameter or a field), independent of which map it lives
  // in: an opaque (void*) caller unconditionally inherits the callee's revealed type; a typed caller only inherits
  // a container_of-style offset from a callee that is a thin accessor on that *same* record type.
  template <class K, class M>
  bool tryAssign(QualType callerType, M &m, K key, const PtrHint &calleeHint, const ParmVarDecl *callee) {
    QualType callerPt = callerType.getCanonicalType();
    if (!callerPt->isPointerType()) return false;
    if (callerPt->getPointeeType()->isVoidType()) { m[key] = calleeHint; return true; }
    QualType calleePt = callee->getType().getCanonicalType();
    if (!calleePt->isPointerType()) return false;
    const RecordDecl *callerRd = callerPt->getPointeeType().getCanonicalType()->getAsRecordDecl();
    const RecordDecl *calleeRd = calleePt->getPointeeType().getCanonicalType()->getAsRecordDecl();
    if (!callerRd || !calleeRd || callerRd->getDefinition() != calleeRd->getDefinition()) return false;
    m[key] = calleeHint;
    return true;
  }
  void propagate() {
    for (int pass = 0; pass < 6; ++pass) {
      bool changed = false;
      for (auto &e : edges) {
        auto from = h_.params.find(e.callee);
        if (from == h_.params.end()) continue;
        if (e.callerParam) {
          if (h_.params.count(e.callerParam) || conflicts_.count(e.callerParam)) continue;
          changed |= tryAssign(e.callerParam->getType(), h_.params, e.callerParam, from->second, e.callee);
        } else if (e.callerField) {
          if (h_.fields.count(e.callerField) || conflicts_.count(e.callerField)) continue;
          changed |= tryAssign(e.callerField->getType(), h_.fields, e.callerField, from->second, e.callee);
        }
      }
      if (!changed) break;
    }
  }
  bool VisitCastExpr(CastExpr *ce) {
    if (ce->getCastKind() != CK_BitCast) return true;
    QualType to = ce->getType().getCanonicalType();
    if (!to->isPointerType()) return true;
    const RecordDecl *rd = to->getPointeeType()->getAsRecordDecl();
    if (!rd || !rd->isCompleteDefinition()) return true;
    const Expr *sub = ce->getSubExpr()->IgnoreParenImpCasts();
    uint64_t off = 0;
    bool viaSub = false;
    if (auto *bo = dyn_cast<BinaryOperator>(sub)) {
      if (bo->getOpcode() != BO_Sub || !bo->getLHS()->getType().getCanonicalType()->isPointerType()) return true;
      Expr::EvalResult r;
      if (!bo->getRHS()->EvaluateAsInt(r, rd->getASTContext()) || r.Val.getInt().isNegative()) return true;
      off = r.Val.getInt().getZExtValue();
      sub = bo->getLHS();
      viaSub = true;
    }
    // `(Derived*)x` where `x`'s own declared type is `Base*` (not void*) and `Derived`'s first member, at offset 0,
    // is exactly `Base`: the common C hand-rolled-inheritance idiom (`struct Derived { struct Base base; ... };`,
    // cast a `Base*` you were handed back to the `Derived*` you know it really is). This is structurally the same
    // relationship a `container_of(x, Derived, base)` at offset 0 encodes, just spelled as a plain cast instead of
    // the macro -- verified against the real layout (not guessed from the cast alone), so it is exactly as
    // unambiguous as a genuine container_of subtraction and gets the same trust (`viaSub`, TU-wide collection): a
    // `struct weston_data_source *` cast to `struct dnd_data_source *` whose first field is `struct
    // weston_data_source base;` can only ever mean that embedding, wherever in the program it textually appears.
    if (!viaSub && !rd->field_empty() && layoutSane(to->getPointeeType())) {
      const FieldDecl *first = *rd->field_begin();
      if (!first->isBitField() && rd->getASTContext().getASTRecordLayout(rd).getFieldOffset(first->getFieldIndex()) == 0) {
        QualType subTy = sub->getType().getCanonicalType();
        if (subTy->isPointerType()) {
          QualType subPointee = subTy->getPointeeType().getCanonicalType().getUnqualifiedType();
          QualType firstTy = first->getType().getCanonicalType().getUnqualifiedType();
          if (!subPointee->isVoidType() && firstTy == subPointee) viaSub = true;  // off stays 0
        }
      }
    }
    // A plain `(T*)x` conversion (not container_of's pointer-subtraction form, nor the first-member-embedding case
    // just above) is only trustworthy when it happens in the file being analysed: a field like `file->private_data`
    // is cast to different, mutually-conflicting struct types by different subsystems' headers, so collecting those
    // globally would make every hint conflict. A genuine container_of subtraction (`viaSub`) is structurally
    // unambiguous wherever it textually appears: the macro always encodes a fixed, real layout relationship for
    // that one field/parameter. That makes it safe (and necessary) to collect across the whole translation unit,
    // including small accessor helpers defined once in a shared header (e.g. a `drm_to_adev()`-style function used
    // by hundreds of call sites) that are never themselves "the main file" for any of the many .c files that call
    // them.
    if (!viaSub && !sm_.isInMainFile(sm_.getExpansionLoc(ce->getBeginLoc()))) return true;
    const FieldDecl *fd = nullptr;
    const ParmVarDecl *pd = nullptr;
    root(sub, 0, fd, pd);
    // void* and an opaque handle (a struct only ever forward-declared, like a public API's `struct weston_xwayland;`
    // whose one real definition lives behind it as a differently-named internal struct, e.g. `weston_xserver`) play
    // the same role here: there is exactly one real type hiding behind either, so revealing it is unambiguous,
    // unlike a *complete* struct cast to a different, unrelated complete struct (the `file->private_data`-style
    // conflict the comment above is about).
    auto revealable = [](QualType pointee) {
      if (pointee->isVoidType()) return true;
      const RecordDecl *rd2 = pointee->getAsRecordDecl();
      return rd2 && !rd2->getDefinition();
    };
    if (fd) {
      QualType ft = fd->getType().getCanonicalType();
      if (!ft->isPointerType() || (!viaSub && !revealable(ft->getPointeeType()))) return true;  // plain conversions only reveal void*/opaque handles
      add(h_.fields, fd, rd->getDefinition(), off, viaSub);
    } else if (pd) {
      QualType pt = pd->getType().getCanonicalType();
      if (!pt->isPointerType() || (!viaSub && !revealable(pt->getPointeeType()))) return true;
      add(h_.params, pd, rd->getDefinition(), off, viaSub);
    }
    return true;
  }

 private:
  // follows casts and single-assignment locals (`void *__mptr = (void *)(ptr);`) back to a field or a parameter
  void root(const Expr *e, unsigned depth, const FieldDecl *&fd, const ParmVarDecl *&pd) {
    while (true) {
      e = e->IgnoreParens();
      if (auto *c = dyn_cast<CastExpr>(e)) { e = c->getSubExpr(); continue; }
      break;
    }
    if (auto *me = dyn_cast<MemberExpr>(e)) { fd = dyn_cast<FieldDecl>(me->getMemberDecl()); return; }
    // a getter: `i2c_get_clientdata(c)` -> `dev_get_drvdata(&c->dev)` -> `return dev->driver_data;`: the value is that field
    if (auto *call = dyn_cast<CallExpr>(e)) {
      if (depth >= 4) return;
      const FunctionDecl *callee = call->getDirectCallee() ? call->getDirectCallee()->getDefinition() : nullptr;
      if (!callee || !callee->getBody()) return;
      struct FirstReturn : RecursiveASTVisitor<FirstReturn> {
        const Expr *value = nullptr;
        unsigned returns = 0;
        bool VisitReturnStmt(ReturnStmt *r) { ++returns; if (!value) value = r->getRetValue(); return true; }
      } fr;
      fr.TraverseStmt(const_cast<Stmt *>(callee->getBody()));
      if (fr.returns != 1 || !fr.value) return;
      const FieldDecl *cfd = nullptr;
      const ParmVarDecl *cpd = nullptr;
      root(fr.value, depth + 1, cfd, cpd);
      fd = cfd;  // a parameter of the getter is not a parameter of the analysed function: only fields carry over
      return;
    }
    if (auto *dr = dyn_cast<DeclRefExpr>(e)) {
      if (auto *p = dyn_cast<ParmVarDecl>(dr->getDecl())) { pd = p; return; }
      if (auto *v = dyn_cast<VarDecl>(dr->getDecl()))
        if (v->hasInit() && depth < 3 && !v->getType().isVolatileQualified()) root(v->getInit(), depth + 1, fd, pd);
    }
  }
  template <class M, class K> void add(M &m, K key, const RecordDecl *rd, uint64_t off, bool viaSub) {
    auto it = m.find(key);
    if (it == m.end()) m[key] = PtrHint{rd, off, viaSub};
    else if (it->second.rd != rd || it->second.off != off) conflicts_.insert(key);  // used as different things: no hint
    else it->second.viaSub = it->second.viaSub || viaSub;  // the same (rd, off) seen once via container_of is still a real container_of
  }
  PtrHints &h_;
  std::set<const void *> &conflicts_;
  const SourceManager &sm_;
};
using VoidHints = PtrHints;

// True if Clang can lay the type out: a record with errors (a field of unknown type, ...) has no layout and
// ASTContext::getASTRecordLayout / getTypeSize crash on it.
bool layoutSane(QualType t, std::set<const RecordDecl *> &seen) {
  t = t.getCanonicalType();
  if (t->containsErrors() || t->isDependentType()) return false;
  while (auto *at = dyn_cast<ArrayType>(t.getTypePtr())) {
    if (!isa<ConstantArrayType>(at)) return !isa<VariableArrayType>(at) && !isa<DependentSizedArrayType>(at) ? layoutSane(at->getElementType(), seen) : false;
    t = at->getElementType().getCanonicalType();
  }
  if (t->isPointerType()) return true;  // the pointee needs no layout to lay out the pointer
  if (auto *rd0 = t->getAsRecordDecl()) {
    const RecordDecl *rd = rd0->getDefinition();
    if (!rd || rd->isInvalidDecl()) return false;
    if (!seen.insert(rd).second) return true;
    for (auto *f : rd->fields())
      if (f->isInvalidDecl() || !layoutSane(f->getType(), seen)) return false;
    return true;
  }
  if (auto *ed = t->getAs<EnumType>()) return ed->getDecl()->isComplete() && !ed->getDecl()->isInvalidDecl();
  return !t->isIncompleteType();
}
bool layoutSane(QualType t) { std::set<const RecordDecl *> seen; return layoutSane(t, seen); }

// number of fields of `rd` that are pointers to `rd` itself (next/prev of an intrusive list node)
unsigned selfPointers(const RecordDecl *rd) {
  unsigned n = 0;
  for (auto *f : rd->fields()) {
    QualType t = f->getType().getCanonicalType();
    if (!t->isPointerType()) continue;
    const RecordDecl *pr = t->getPointeeType()->getAsRecordDecl();
    if (pr && pr->getDefinition() == rd->getDefinition()) ++n;
  }
  return n;
}

// a stable identity for a field's declaration that two different clang invocations (different units' ASTContexts parsing
// the same shared header) agree on: same absolute path + line + column. Used to match a field across --link units, where
// the FieldDecl pointers themselves are only valid within the ASTContext that produced them.
std::string fieldKey(const SourceManager &sm, const FieldDecl *fd) {
  if (!fd) return "";
  PresumedLoc pl = sm.getPresumedLoc(sm.getExpansionLoc(fd->getCanonicalDecl()->getLocation()));
  if (!pl.isValid()) return "";
  return std::string(pl.getFilename()) + ":" + std::to_string(pl.getLine()) + ":" + std::to_string(pl.getColumn());
}
// flatten `cur`'s fields for sibling-length search, recursing through *anonymous* struct/union members so a length
// field packed inside one is still visible as a candidate -- the motivating case is VFS's
// `struct qstr { union { u64 hash_len; struct { u32 hash, len; }; }; }`: Clang's `RecordDecl::fields()` only ever
// yields the anonymous union as a single unnamed FieldDecl, never `hash`/`len` directly, so without this recursion
// `len` is invisible to both matching loops below no matter how its name looks. `off` comes back already absolute
// (includes `curBase`), ready to divide by 8 for a byte offset -- no separate union/struct-offset-math distinction
// is needed here: `ASTRecordLayout::getFieldOffset` on the anonymous record itself already returns 0 for every
// member of an anonymous *union* (overlaid) and normal accumulating offsets for an anonymous *struct* (packed), so
// adding that to the anonymous member's own offset within `cur` is correct either way.
// Not applied to real C bitfields (`isBitField()` is still skipped, same as before this change) -- only anonymous
// struct/union *members*, which are a distinct, far narrower Clang construct.
void collectFieldsForLenSearch(ASTContext &ctx, const RecordDecl *cur, uint64_t curBase,
                                std::vector<std::pair<const FieldDecl *, uint64_t>> &out) {
  if (!cur || !cur->isCompleteDefinition()) return;
  const ASTRecordLayout &L = ctx.getASTRecordLayout(cur);
  for (auto *sf : cur->fields()) {
    if (sf->isBitField()) continue;
    uint64_t off = curBase + L.getFieldOffset(sf->getFieldIndex());
    if (sf->isAnonymousStructOrUnion()) {
      if (const RecordDecl *inner = sf->getType().getCanonicalType()->getAsRecordDecl())
        collectFieldsForLenSearch(ctx, inner, off, out);
      continue;  // the anonymous member itself is never a usable named candidate
    }
    out.emplace_back(sf, off);
  }
}

// a sibling integer field in `cur` whose name looks like a length/count that goes with field `n` (buf/buflen,
// data/datalen, addr/addr_len, argv/argc, ...); `outOffset` comes back absolute within the top-level pointee object
// (same base as PtrFieldInfo::offset), ready to use as a Spec.cpp `size.from_field.offset`. Candidates nested inside
// an anonymous struct/union member of `cur` are included (see collectFieldsForLenSearch).
// Bounds the program states about its own integer members, harvested from assertion macros (see AssertedBound).
//
// Detection is by MACRO NAME, not by the shape of the lowered `if`: `WARN_ON(c)` moves `c` into a local
// (`int __ret_warn_on = !!(c); if (unlikely(__ret_warn_on)) __WARN();`), so the `IfStmt` no longer mentions the
// member at all. The original comparison is a macro ARGUMENT, though, so its source location walks back up the
// expansion chain to the macro that was written -- which is also what tells an assertion apart from an ordinary
// `if (x) return -EINVAL`, the one thing that must never be harvested (DESIGN.md §22.358).
//
// `.second` is the polarity: true when the condition states what must HOLD (`assert`, `FT_ASSERT`), false when it
// states what must NOT happen (`BUG_ON` and friends), in which case the bound comes from its negation.
const std::vector<std::pair<const char *, bool>> &assertMacros() {
  static const std::vector<std::pair<const char *, bool>> v{
      {"BUG_ON", false},     {"WARN_ON", false},      {"WARN_ON_ONCE", false}, {"snd_BUG_ON", false},
      {"VM_BUG_ON", false},  {"VM_WARN_ON", false},   {"DEBUG_NET_WARN_ON_ONCE", false},
      {"assert", true},      {"FT_ASSERT", true},     {"__assert", true}};
  return v;
}

class AssertBoundFinder : public RecursiveASTVisitor<AssertBoundFinder> {
 public:
  AssertBoundFinder(ASTContext &ctx, std::map<std::string, AssertedBound> &out) : ctx_(ctx), out_(out) {}

  bool VisitBinaryOperator(BinaryOperator *b) {
    BinaryOperatorKind op = b->getOpcode();
    if (op != BO_LT && op != BO_LE && op != BO_GT && op != BO_GE) return true;
    int polarity = assertPolarity(b->getBeginLoc());
    if (polarity < 0) return true;
    // `<member> <op> <integer constant>` only. A comparison of two members states a relation `where:` cannot
    // express, and a bound on something that is not a member of a synthesised object is of no use here.
    const auto *me = dyn_cast<MemberExpr>(b->getLHS()->IgnoreParenImpCasts());
    const Expr *rhs = b->getRHS();
    if (!me) return true;
    QualType mt = me->getType().getCanonicalType();
    if (!(mt->isIntegerType() || mt->isEnumeralType())) return true;
    auto *fd = dyn_cast<FieldDecl>(me->getMemberDecl());
    if (!fd || fd->isBitField()) return true;
    llvm::APSInt v;
    if (auto r = rhs->getIntegerConstantExpr(ctx_)) v = *r;
    else return true;
    if (v.getBitWidth() > 64) return true;
    int64_t k = v.getSExtValue();
    // The macro says the condition HOLDS (polarity 1) or MUST NOT HOLD (polarity 0); fold that into the operator.
    BinaryOperatorKind eff = op;
    if (!polarity) eff = op == BO_LT ? BO_GE : op == BO_LE ? BO_GT : op == BO_GT ? BO_LE : BO_LT;
    AssertedBound ab;
    switch (eff) {
      case BO_LT: ab.hasHi = true; ab.hi = k - 1; break;
      case BO_LE: ab.hasHi = true; ab.hi = k; break;
      case BO_GT: ab.hasLo = true; ab.lo = k + 1; break;
      default:    ab.hasLo = true; ab.lo = k; break;  // BO_GE
    }
    ab.bits = static_cast<unsigned>(ctx_.getTypeSize(mt));
    ab.isSigned = mt->isSignedIntegerOrEnumerationType();
    const RecordDecl *rd = fd->getParent();
    if (!rd || !rd->isCompleteDefinition() || rd->getNameAsString().empty()) return true;
    QualType rt = ctx_.getRecordType(rd);
    if (!layoutSane(rt)) return true;
    ab.offset = ctx_.getASTRecordLayout(rd).getFieldOffset(fd->getFieldIndex()) / 8;
    std::string key = assertKey(rd->getNameAsString(), ctx_.getTypeSizeInChars(rt).getQuantity(), ab.offset);
    if (!key.empty()) merge(key, ab);
    return true;
  }

 private:
  // -1 = not inside an assertion macro, 0 = the condition states what must NOT happen, 1 = what must hold
  int assertPolarity(SourceLocation loc) {
    const SourceManager &sm = ctx_.getSourceManager();
    for (unsigned depth = 0; depth < 8 && loc.isMacroID(); ++depth) {
      llvm::StringRef n = Lexer::getImmediateMacroName(loc, sm, ctx_.getLangOpts());
      for (auto &m : assertMacros())
        if (n == m.first) return m.second ? 1 : 0;
      loc = sm.getImmediateMacroCallerLoc(loc);
    }
    return -1;
  }
  // Two assertions about one member: keep the WEAKER claim. A bound that only one path states is not an invariant
  // of the type, and over-constraining here hides defects rather than inventing them.
  void merge(const std::string &key, const AssertedBound &b) {
    auto it = out_.find(key);
    if (it == out_.end()) { out_[key] = b; return; }
    AssertedBound &a = it->second;
    if (b.hasHi && a.hasHi) a.hi = std::max(a.hi, b.hi);
    else if (!b.hasHi) a.hasHi = false;
    if (b.hasLo && a.hasLo) a.lo = std::min(a.lo, b.lo);
    else if (!b.hasLo) a.hasLo = false;
  }
  ASTContext &ctx_;
  std::map<std::string, AssertedBound> &out_;
};

// The spellings a struct uses for "how much of <field> is there". `.second` marks the ones that assert a count of
// ELEMENTS rather than a number of BYTES -- the two coincide for a byte buffer and differ for everything wider
// (DESIGN.md §22.355).
std::vector<std::pair<std::string, bool>> composeLenNames(const std::string &s) {
  std::vector<std::pair<std::string, bool>> v{
      {s + "c", true},      {s + "_count", true},   {s + "_len", false}, {s + "len", false},
      {s + "_size", false}, {s + "_length", false}, {s + "sz", false},   {s + "_sz", false},
      {"n" + s, true},      {"n_" + s, true},       {"num_" + s, true},  {s + "_num", true}};
  if (!s.empty() && s.back() == 'v') v.push_back({s.substr(0, s.size() - 1) + "c", true});  // argv -> argc
  return v;
}
// does `scalar` name the length of `field`, by one of those spellings?
bool nameComposesTo(const std::string &field, const std::string &scalar, bool &isCount) {
  for (auto &c : composeLenNames(field))
    if (c.first == scalar) { isCount = c.second; return true; }
  return false;
}

// The count of an INLINE fixed array: `CFF_PrivateRec { FT_Fixed blue_values[14]; FT_Byte num_blue_values; }`,
// walked as `for (i = 0; i < num_blue_values; i += 2) ... blues->zone[blues->count++] = blueValues[i]`. The array is
// a member, not a pointer field, so nothing in the size-from-field machinery reaches it; what the harness is missing
// is the bound its real producer enforces (FreeType's CFF parser caps it at 14 via
// `CFF_FIELD_DELTA_FIXED( 6, blue_values, 14, ... )`), leaving the count free to 255 (DESIGN.md §22.356).
//
// Like `same_alloc`, this is a NARROWING assumption -- a bound that does not really hold HIDES a defect rather than
// inventing one, and "the producer forgot to clamp a count against a fixed array" is itself a classic bug class. So:
// only the name forms COMPOSED FROM THE ARRAY'S OWN NAME (no bare `count`/`len` fallback, which says nothing about
// WHICH array it bounds), and only when exactly one array in the struct claims that scalar. Every bound that is
// emitted shows up in the report's assumptions.
void collectInlineArrayCounts(ASTContext &ctx, const RecordDecl *rd, std::vector<InlineCountInfo> &out, uint64_t baseBits = 0,
                              unsigned depth = 0) {
  if (!rd || !rd->isCompleteDefinition() || rd->isUnion()) return;
  if (!layoutSane(ctx.getRecordType(rd))) return;
  // An array and the scalar that counts it are siblings of ONE record, but that record is often an embedded member
  // rather than the pointee itself: FreeType's `CFF_SubFontRec { ...; CFF_PrivateRec private_dict; ... }` holds both
  // `blue_values[14]` and `num_blue_values`, and `collectFieldsForLenSearch` only ever descends into ANONYMOUS
  // members. So pair level by level, with absolute offsets, and recurse into the named embedded records too.
  const ASTRecordLayout &L = ctx.getASTRecordLayout(rd);
  std::vector<std::pair<const FieldDecl *, uint64_t>> flat;
  for (auto *f : rd->fields()) {
    if (f->isBitField()) continue;
    uint64_t off = baseBits + L.getFieldOffset(f->getFieldIndex());
    flat.emplace_back(f, off);
    if (depth < 4)
      if (const RecordDecl *inner = f->getType().getCanonicalType()->getAsRecordDecl())
        collectInlineArrayCounts(ctx, inner->getDefinition(), out, off, depth + 1);
  }
  // scalar FieldDecl -> the bound it would get; a second, different claim drops it
  std::map<const FieldDecl *, std::pair<uint64_t, uint64_t>> claim;  // field -> (hi, offsetBits)
  std::set<const FieldDecl *> conflict;
  for (auto &[af, aoff] : flat) {
    if (!af->getIdentifier()) continue;
    const ConstantArrayType *at = ctx.getAsConstantArrayType(af->getType().getCanonicalType());
    if (!at) continue;
    uint64_t n = at->getSize().getZExtValue();
    if (n == 0 || n > (1u << 20)) continue;
    QualType et = at->getElementType().getCanonicalType();
    if (!layoutSane(et)) continue;
    uint64_t elemBytes = ctx.getTypeSizeInChars(et).getQuantity();
    if (!elemBytes) continue;
    for (auto &[sf, soff] : flat) {
      if (sf == af || !sf->getIdentifier()) continue;
      QualType st = sf->getType().getCanonicalType();
      if (!(st->isIntegerType() && !sf->isBitField() && layoutSane(st))) continue;
      bool isCount = false;
      if (!nameComposesTo(af->getName().str(), sf->getName().str(), isCount)) continue;
      // a count bounds the ELEMENTS, a byte length bounds the array's size in bytes; both are real upper bounds
      // under their own reading, and taking the weaker one when unsure cannot over-constrain.
      uint64_t hi = isCount ? n : n * elemBytes;
      auto it = claim.find(sf);
      if (it != claim.end() && it->second.first != hi) { conflict.insert(sf); continue; }
      claim[sf] = {hi, soff};
    }
  }
  for (auto &[sf, v] : claim) {
    if (conflict.count(sf)) continue;
    QualType st = sf->getType().getCanonicalType();
    unsigned bits = static_cast<unsigned>(ctx.getTypeSize(st));
    uint64_t hi = v.first;
    // a bound the type cannot exceed anyway says nothing; emitting it would only add noise to the assumptions
    if (bits < 64 && hi >= (1ull << (st->isSignedIntegerType() ? bits - 1 : bits))) continue;
    InlineCountInfo ic;
    ic.offset = v.second / 8;
    ic.bits = bits;
    ic.isSigned = st->isSignedIntegerType();
    ic.hi = hi;
    out.push_back(ic);
  }
}

// The (base, cursor, limit) idiom: several pointer fields of one struct that all walk ONE buffer.
// `FT_ValidatorRec { const FT_Byte *base, *limit; }` says it outright in its own comment ("`base' + sizeof(table)"),
// and `PS_ParserRec { FT_Byte *cursor, *base, *limit; }` adds the cursor. Synthesised as independent allocations,
// `while (cur < limit)` compares pointers into unrelated objects, which is UB on its own and makes every bound test
// meaningless -- 11 confirmed `ptr_cmp_diff_obj` at psobjs.c:286 in the FreeType round (DESIGN.md §22.354).
//
// This pairing is a NARROWING assumption: it removes states the harness could otherwise build, so a wrong pairing can
// hide a real defect rather than invent one. The gate is therefore deliberately tight -- exact role names, the same
// pointee type, and exactly one candidate for the owning allocation. Anything ambiguous stays unpaired.
int aliasRole(const std::string &n) {  // 1 = owns the allocation, 2 = one-past-the-end, 3 = somewhere inside, 0 = not part of the idiom
  static const std::set<std::string> kBase{"base", "start", "begin", "buf", "buffer", "data", "bottom"};
  static const std::set<std::string> kEnd{"limit", "end", "top", "tail"};
  static const std::set<std::string> kCursor{"cursor", "cur", "pos"};
  if (kBase.count(n)) return 1;
  if (kEnd.count(n)) return 2;
  if (kCursor.count(n)) return 3;
  return 0;
}
// `fd` plays role `role` (2 or 3); find the single sibling of `cur` that owns the allocation. Both must be pointers to
// the same type -- a `char *base` next to a `struct foo *limit` is two different buffers, whatever the names say.
bool findAliasBase(ASTContext &ctx, const RecordDecl *cur, uint64_t curBase, const FieldDecl *fd, int64_t &outOffset) {
  if (!cur || !fd) return false;
  QualType pt = fd->getType().getCanonicalType();
  if (!pt->isPointerType()) return false;
  QualType elem = pt->getPointeeType().getCanonicalType().getUnqualifiedType();
  std::vector<std::pair<const FieldDecl *, uint64_t>> flat;
  collectFieldsForLenSearch(ctx, cur, curBase, flat);
  const FieldDecl *found = nullptr;
  uint64_t foundOff = 0;
  for (auto &[sf, off] : flat) {
    if (sf == fd || !sf->getIdentifier()) continue;
    if (aliasRole(sf->getName().str()) != 1) continue;
    QualType st = sf->getType().getCanonicalType();
    if (!st->isPointerType()) continue;
    if (st->getPointeeType().getCanonicalType().getUnqualifiedType() != elem) continue;
    if (found) return false;  // two plausible owners: say nothing rather than guess
    found = sf;
    foundOff = off;
  }
  if (!found) return false;
  outOffset = static_cast<int64_t>(foundOff / 8);
  return true;
}
// `outIsCount`, when given, says whether the sibling that matched is named like a COUNT OF ELEMENTS (`n_items`,
// `num_x`, `x_count`, `argc`) rather than like a byte length (`x_len`, `x_size`, `sz`). For a byte buffer the two
// coincide and nobody has to care; for an array of WIDER elements they differ by the element size, and guessing
// wrong in the length direction makes the object `elem` times too big -- which HIDES a real overrun instead of
// inventing one. `countOnly` therefore restricts the search to the count-shaped names (DESIGN.md §22.355).
bool findSiblingLenField(ASTContext &ctx, const RecordDecl *cur, uint64_t curBase, const std::string &n,
                         int64_t &outOffset, unsigned &outBits, bool &outSigned, bool structArray = false,
                         bool *outIsCount = nullptr, bool countOnly = false) {
  if (!cur || n.empty()) return false;
  auto compose = composeLenNames;  // .second: this spelling asserts a count of elements, not a number of bytes
  std::vector<std::pair<std::string, bool>> cands = compose(n);
  // `structArray` (a pointer to an array of structs): the count often names only the TAIL of the pointer's name --
  // FreeType's `TT_FaceRec { FT_UShort num_tables; TT_Table dir_tables; }`, where none of the composites above
  // reach `num_tables` from `dir_tables`. Dropping the leading `<word>_` and retrying gets it. Deliberately NOT
  // offered for byte buffers: there a wrong pairing replaces a free size range with a too-small one, whereas a
  // struct array has no range to lose -- unpaired it is synthesised as exactly ONE element, so any count-derived
  // size is at least as good (DESIGN.md §22.352).
  if (structArray) {
    size_t us = n.find('_');
    if (us != std::string::npos && us + 1 < n.size()) {
      std::vector<std::pair<std::string, bool>> tail = compose(n.substr(us + 1));
      cands.insert(cands.end(), tail.begin(), tail.end());
    }
  }
  std::vector<std::pair<const FieldDecl *, uint64_t>> flat;
  collectFieldsForLenSearch(ctx, cur, curBase, flat);
  for (auto &[sf, off] : flat) {
    QualType st = sf->getType().getCanonicalType();
    if (!(st->isIntegerType() && layoutSane(st))) continue;
    std::string sn = sf->getName().str();
    auto hit = std::find_if(cands.begin(), cands.end(), [&](auto &c) { return c.first == sn; });
    if (hit == cands.end()) continue;
    if (countOnly && !hit->second) continue;
    outOffset = static_cast<int64_t>(off / 8);
    outBits = static_cast<unsigned>(ctx.getTypeSize(st));
    outSigned = st->isSignedIntegerType();
    if (outIsCount) *outIsCount = hit->second;
    return true;
  }
  // Fallback: a *bare* generic length name (not derived from `n` at all) -- the textbook real-world instance is
  // OpenSSL's `SSL3_RECORD { ...; unsigned int length; ...; unsigned char *data; ... }` (CVE-2014-0160/Heartbleed:
  // `tls1_process_heartbeat` reads an attacker-declared `payload` length and memcpy's that many bytes out of
  // `rrec.data`, whose real size is `rrec.length` -- a sibling pair that none of the name-composite candidates
  // above ever match, because a struct with exactly one buffer-ish field has no reason to name its length field
  // after that field's own name). Only applied when the bare name is UNIQUE among `cur`'s own fields (no other
  // field shares it) -- this can't disambiguate which of several pointer fields in the same struct a generic
  // length field actually describes if there's more than one, but a wrong guess here is no worse than today's
  // status quo of leaving the pointer field's size completely unconstrained, and getting it right unblocks
  // real bugs like Heartbleed that the name-composite heuristic structurally cannot reach.
  // Not offered to a struct array: the reasoning above is specific to a byte buffer, where "the one buffer-ish
  // field in this struct" is a safe reading of a bare `length`. A struct pointer has no such claim -- a `ctx`,
  // `parent` or `ops` pointer sitting next to an unrelated `count` would be sized `count * sizeof(*ptr)` and could
  // come out SMALLER than the one object it really points to, which is strictly worse than today's exact-size
  // synthesis. The name-composed forms above (including the tail form) are the only ones that assert an array.
  if (structArray) return false;
  // `countOnly` keeps only the two bare spellings that mean a number of elements; `length`/`len`/`size`/`sz` next
  // to an array of wider elements is exactly the ambiguity this mode exists to refuse.
  static const std::vector<std::string> kBareAll = {"length", "len", "size", "count", "cnt", "sz"};
  static const std::vector<std::string> kBareCount = {"count", "cnt"};
  const std::vector<std::string> &bareNames = countOnly ? kBareCount : kBareAll;
  const FieldDecl *uniqueBare = nullptr;
  uint64_t uniqueBareOff = 0;
  unsigned bareHits = 0;
  for (auto &[sf, off] : flat) {
    if (std::find(bareNames.begin(), bareNames.end(), sf->getName().str()) == bareNames.end()) continue;
    QualType st = sf->getType().getCanonicalType();
    if (!(st->isIntegerType() && layoutSane(st))) continue;
    ++bareHits;
    uniqueBare = sf;
    uniqueBareOff = off;
  }
  if (bareHits == 1 && uniqueBare) {
    QualType st = uniqueBare->getType().getCanonicalType();
    outOffset = static_cast<int64_t>(uniqueBareOff / 8);
    outBits = static_cast<unsigned>(ctx.getTypeSize(st));
    outSigned = st->isSignedIntegerType();
    if (outIsCount) *outIsCount = countOnly;  // only reached with a count-shaped bare name in that mode
    return true;
  }
  return false;
}

// pointer fields of a record, flattened over embedded structs and (small) arrays; pointees are expanded up to `depth`
void collectPtrFields(ASTContext &ctx, const RecordDecl *rd, uint64_t baseBits, unsigned depth, std::vector<const RecordDecl *> &path,
                      std::vector<PtrFieldInfo> &out, const VoidHints &hints) {
  if (!rd->isCompleteDefinition() || rd->isUnion()) return;  // unions overlay their members: no single pointer layout
  if (!layoutSane(ctx.getRecordType(rd))) return;
  const ASTRecordLayout &L = ctx.getASTRecordLayout(rd);
  path.push_back(rd);
  unsigned unionArms = 0;  // >0 while the walk is inside a union arm it CHOSE (see the union branch below)
  std::function<void(QualType, uint64_t, unsigned, const FieldDecl *, const RecordDecl *, uint64_t)> visit =
      [&](QualType t, uint64_t bits, unsigned arrDepth, const FieldDecl *fd, const RecordDecl *cur, uint64_t curBase) {
    t = t.getCanonicalType();
    if (auto *at = ctx.getAsConstantArrayType(t)) {
      uint64_t n = at->getSize().getZExtValue(), esz = ctx.getTypeSize(at->getElementType());
      QualType et = at->getElementType().getCanonicalType();
      if (et->isPointerType() || et->isRecordType())
        for (uint64_t i = 0; i < n && i < 8; ++i) visit(et, bits + i * esz, arrDepth + 1, fd, cur, curBase);
      return;
    }
    if (auto *r = t->getAsRecordDecl()) {
      if (r->isCompleteDefinition() && layoutSane(t)) {
        const ASTRecordLayout &RL = ctx.getASTRecordLayout(r);
        if (!r->isUnion()) {
          for (auto *f : r->fields())
            if (!f->isBitField()) visit(f->getType(), bits + RL.getFieldOffset(f->getFieldIndex()), arrDepth, f, r->getDefinition(), bits);
        } else {
          // A union overlays its members, so there is no single pointer layout -- which is why this walk used to
          // skip unions whole. For `struct folio` that cost everything: its OUTERMOST member is an anonymous
          // union, so the parameter contributed no pointer fields at all and every
          // `folio->mapping->host->i_sb` an address_space_operations handler walks was frontier guesswork
          // (DESIGN.md §22.484). Taking the FIRST arm is better than taking none, by the same argument §22.364
          // made about NULL: nothing out there is a cautious default, and a wrong field can be contradicted by
          // the program while a missing one cannot. It is a CHOICE, so `viaUnionArm` carries it to the report.
          for (auto *f : r->fields()) {
            if (f->isBitField()) continue;
            ++unionArms;
            visit(f->getType(), bits + RL.getFieldOffset(f->getFieldIndex()), arrDepth, f, r->getDefinition(), bits);
            --unionArms;
            break;  // the first arm only: the others overlay it and would contradict it at the same offset
          }
        }
      }
      return;
    }
    if (!t->isPointerType()) return;
    bool locallyUnused = hints.restrictToUsed && fd && !hints.used.count(fd);
    if (locallyUnused && !hints.linkMode) return;  // nobody reads or writes this pointer (and no other unit could change that)
    PtrFieldInfo pf;
    pf.viaUnionArm = unionArms > 0;
    if (locallyUnused) {  // linkMode: keep it, pending the whole-program used-fields set (hlir-scan prunes it back out if still unused)
      pf.pendingLinkUse = true;
      pf.fieldKey = fieldKey(ctx.getSourceManager(), fd);
    }
    pf.offset = bits / 8;
    QualType pt = t->getPointeeType().getCanonicalType().getUnqualifiedType();
    // next/prev of a doubly linked intrusive node: an empty list points back at its own head
    if (cur && selfPointers(cur) >= 2)
      if (const RecordDecl *pr = pt->getAsRecordDecl())
        if (pr->getDefinition() == cur) {
          pf.kind = "self";
          pf.selfTarget = curBase / 8;
          out.push_back(std::move(pf));
          return;
        }
    if (fd) {
      auto h = hints.fields.find(fd);
      if (h != hints.fields.end()) {  // type-erased field, or a pointer to an embedded member: the code reveals the real object
        pt = ctx.getRecordType(h->second.rd).getCanonicalType();
        pf.at = h->second.off;
        pf.viaContainerOf = h->second.viaSub;
      }
    }
    if (pt->isVoidType()) { pf.kind = "bytes"; pf.pointeeSize = 1; }
    else if (pt->isFunctionType()) {
      pf.kind = "func";
      pf.nullTested = fd && hints.nullTested.count(fd);
      // --link: this unit may not be the one that tests the field (it usually is not). Give every function-pointer
      // field a key so hlir-scan can finish the decision against the whole program's null-test set. Only for func
      // fields: building a key for all of a kernel struct's thousands of pointer fields is not free.
      if (hints.linkMode && pf.fieldKey.empty()) pf.fieldKey = fieldKey(ctx.getSourceManager(), fd);
      if (auto *fpt = pt->getAs<FunctionProtoType>()) {
        std::vector<QualType> ps(fpt->param_type_begin(), fpt->param_type_end());
        bool ok = true;
        std::string sg = sigText(ctx, fpt->getReturnType(), ps, ok);
        if (ok && !fpt->isVariadic()) { pf.funcSig = sg; pf.funcCType = cTypeKey(QualType(fpt, 0)); }
      }
    } else if ((pt->isIntegerType() || pt->isEnumeralType()) && layoutSane(pt)) {
      pf.pointeeSize = ctx.getTypeSizeInChars(pt).getQuantity();
      pf.kind = pf.pointeeSize == 1 ? "bytes" : "int";
    } else if (auto *prd = pt->getAsRecordDecl()) {
      pf.kind = "struct";
      pf.structName = prd->getNameAsString();
      if (prd->isCompleteDefinition() && layoutSane(pt)) pf.pointeeSize = ctx.getTypeSizeInChars(pt).getQuantity();
      else if (!prd->getDefinition()) { pf.kind = "handle"; pf.pointeeSize = 64; }  // never defined here (wl_resource *, ...): an opaque handle object
      else pf.kind = "other";  // incomplete: no layout to build
      if (pf.kind == "struct") {
        // the bounds the pointee's own inline arrays put on its count members (DESIGN.md §22.356)
        collectInlineArrayCounts(ctx, prd->getDefinition(), pf.inlineCounts);
        if (std::find(path.begin(), path.end(), prd) != path.end()) pf.cyclic = true;
        // A pendingLinkUse field hasn't earned recursion yet: most of a kernel struct's hundreds of pointer fields turn
        // out to still be unused once the whole program is known and get pruned right back out (hlir-scan), but without
        // this cutoff every one of them would recurse `depth` levels into its own pointee's pointer fields first -- on a
        // struct the size of `amdgpu_device` (close to 2000 pointer fields) that recursion, repeated per field, is what
        // actually dominates --link compile time, not the field-use bookkeeping itself. A field that is confirmed used
        // keeps the same default as any field beyond the ordinary depth cutoff below: a real, zeroed object, not NULL.
        else if (depth > 0 && !pf.pendingLinkUse) collectPtrFields(ctx, prd, 0, depth - 1, path, pf.children, hints);
      }
    } else if (pt->isPointerType() && fd && depth > 0 && !arrDepth) {
      // `T **v`: an array of element pointers. A few slots, each laid out like a `T *` field of its own.
      QualType elemTarget = pt->getPointeeType().getCanonicalType().getUnqualifiedType();
      bool known = elemTarget->isVoidType() || ((elemTarget->isIntegerType() || elemTarget->isEnumeralType()) && layoutSane(elemTarget)) ||
                   (elemTarget->getAsRecordDecl() && elemTarget->getAsRecordDecl()->getDefinition() && layoutSane(elemTarget));
      if (!known) pf.kind = "pointer";
      else {
        constexpr unsigned kSlots = 3;
        pf.kind = "struct";
        pf.ptrArray = true;
        pf.arraySlots = kSlots;
        pf.structName = "(array of " + pt.getAsString() + ")";
        pf.pointeeSize = 8ull * kSlots;
        for (unsigned i = 0; i < kSlots; ++i) {
          size_t before = out.size();
          visit(pt, 8ull * 8 * i, 1, nullptr, nullptr, 0);  // arrDepth 1: an element is not itself an array
          while (out.size() > before) { pf.children.push_back(std::move(out.back())); out.pop_back(); }
        }
        // the count that goes with it: argv/argc, items/nitems, buf/buf_len, ...
        if (cur && fd) {
          int64_t lo; unsigned lb; bool ls;
          if (findSiblingLenField(ctx, cur, curBase, fd->getName().str(), lo, lb, ls)) { pf.lenOffset = lo; pf.lenBits = lb; pf.lenSigned = ls; }
        }
        std::reverse(pf.children.begin(), pf.children.end());  // popped from the back
      }
    } else if (pt->isPointerType()) pf.kind = "pointer";
    else pf.kind = "other";
    // a byte buffer (`void*` pointee, or a `char*`-like 1-byte-element pointee) often has a sibling length field in
    // the same struct (`data`/`datalen`, `buf`/`buflen`, `addr`/`addr_len`, ...) -- Spec.cpp's `size.from_field` lets
    // the harness size the synthesized object from that field's real value instead of an independent range (see
    // DESIGN.md §22.105); this auto-detection is what makes that mechanism actually fire on `--entries all` scans
    // (cmark/Duktape §22.127/130 found the hand-written-spec-only version never did).
    // A pointer to a STRUCT with a sibling count field is the same idiom one element wider: it is an array of
    // `count` elements, not a single object (`FT_UShort num_tables; TT_Table dir_tables;` walked as
    // `limit = entry + face->num_tables`, DESIGN.md §22.352). Scan.cpp turns this into
    // `size: {from_field: {..., elem: sizeof(element)}}`. Only for a struct that has no pointer fields of its own
    // and is not already the `T **` fixed-slot array shape -- both have their own synthesis that `from_field`
    // cannot be combined with.
    // An array of WIDER INTEGERS is the same idiom again (`FT_Outline { unsigned short n_contours; ...;
    // unsigned short *contours; }`, documented as "an array of n_contours shorts"): unpaired it gets a free size
    // range while the count runs to 65535, which is where `ps_builder_close_contour`'s oob_write came from. It is
    // paired only on an unambiguous COUNT spelling, because sizing it from a byte length would make the object
    // `pointeeSize` times too big and hide a real overrun (DESIGN.md §22.355).
    if ((pf.kind == "bytes" || pf.kind == "int" ||
         (pf.kind == "struct" && !pf.ptrArray && !pf.cyclic && pf.children.empty() && pf.pointeeSize)) &&
        cur && fd && !arrDepth) {
      int64_t lo; unsigned lb; bool ls; bool isCount = false;
      if (findSiblingLenField(ctx, cur, curBase, fd->getName().str(), lo, lb, ls, pf.kind == "struct", &isCount,
                              /*countOnly=*/pf.kind == "int")) {
        pf.lenOffset = lo; pf.lenBits = lb; pf.lenSigned = ls; pf.lenIsCount = isCount;
      }
    }
    // ...and the other way a struct says "these pointers belong together": a (base, cursor, limit) group over one
    // buffer (see aliasRole/findAliasBase). A view may well ALSO have found a sibling length -- FreeType's
    // `FT_StreamRec` pairs all three of base/cursor/limit with its `size` field, which gives three separate objects
    // of the same size and leaves `cursor < limit` cross-object. Being a view wins: it is the stronger statement
    // (same allocation AND ordered), and Scan.cpp drops the derived size for it.
    if ((pf.kind == "bytes" || pf.kind == "int") && cur && fd && !arrDepth && fd->getIdentifier()) {
      int role = aliasRole(fd->getName().str());
      int64_t ao;
      if ((role == 2 || role == 3) && findAliasBase(ctx, cur, curBase, fd, ao)) { pf.aliasOffset = ao; pf.aliasEnd = role == 2; }
    }
    out.push_back(std::move(pf));
  };
  for (auto *f : rd->fields())
    if (!f->isBitField()) visit(f->getType(), baseBits + L.getFieldOffset(f->getFieldIndex()), 0, f, rd->getDefinition(), baseBits);
  path.pop_back();
}

// collectPtrFields, memoized by (rd, depth): only for a fresh top-level call (baseBits=0, empty `path`), which is all
// paramInfoOfType ever does. Safe because the result depends only on (rd, depth, hints) in that case -- `hints.used` etc.
// are fixed for the whole translation unit, so a struct reused across many functions (a `struct dev *` parameter
// threaded through a whole kernel subsystem file) is only ever walked once instead of once per function. Returned as a
// shared_ptr (see ParamInfo::ptrFields) so every caller shares the one tree instead of deep-copying it.
std::shared_ptr<std::vector<PtrFieldInfo>> collectPtrFieldsCached(ASTContext &ctx, const RecordDecl *rd, unsigned depth, const VoidHints &hints) {
  auto key = std::make_pair(cast<RecordDecl>(rd->getCanonicalDecl()), depth);
  auto it = hints.ptrFieldsCache.find(key);
  if (it != hints.ptrFieldsCache.end()) return it->second;
  std::vector<const RecordDecl *> path;
  auto out = std::make_shared<std::vector<PtrFieldInfo>>();
  collectPtrFields(ctx, rd, 0, depth, path, *out, hints);
  return hints.ptrFieldsCache.emplace(key, std::move(out)).first->second;
}

// integer members of a record, embedded structs flattened ("a.b"); bit-fields, arrays and pointers are skipped
void collectScalarFields(ASTContext &ctx, const RecordDecl *rd, uint64_t baseBits, const std::string &prefix, unsigned depth, std::vector<ScalarFieldInfo> &out) {
  if (!rd->isCompleteDefinition() || rd->isUnion() || depth > 3 || !layoutSane(ctx.getRecordType(rd)) || out.size() > 512) return;
  const ASTRecordLayout &L = ctx.getASTRecordLayout(rd);
  for (auto *f : rd->fields()) {
    if (f->isBitField() || f->getName().empty()) continue;
    QualType t = f->getType().getCanonicalType();
    uint64_t bits = baseBits + L.getFieldOffset(f->getFieldIndex());
    std::string name = prefix + f->getName().str();
    if (t->isBooleanType()) continue;
    if ((t->isIntegerType() || t->isEnumeralType()) && layoutSane(t)) {
      ScalarFieldInfo sf;
      sf.name = name;
      sf.offset = bits / 8;
      sf.bits = static_cast<unsigned>(ctx.getTypeSize(t));
      sf.isSigned = t->isSignedIntegerOrEnumerationType();
      out.push_back(sf);
    } else if (auto *r = t->getAsRecordDecl()) collectScalarFields(ctx, r, bits, name + ".", depth + 1, out);
  }
}

ParamInfo paramInfoOfType(ASTContext &ctx, QualType type, const std::string &name, const ParmVarDecl *pd, unsigned idx, const VoidHints &hints) {
  ParamInfo p;
  p.name = name.empty() ? "arg" + std::to_string(idx) : name;
  if (type->isReferenceType()) type = ctx.getPointerType(type.getNonReferenceType());  // a reference is a pointer that is never NULL
  QualType t = type.getCanonicalType();
  p.cType = type.getAsString();
  if (t->isBooleanType()) { p.kind = "bool"; p.bits = 1; }
  else if ((t->isIntegerType() || t->isEnumeralType()) && layoutSane(t)) {
    p.kind = "int";
    p.bits = static_cast<unsigned>(ctx.getTypeSize(t));
    p.isSigned = t->isSignedIntegerOrEnumerationType();
  } else if (t->isPointerType()) {
    p.kind = "ptr";
    QualType pt = t->getPointeeType();
    p.pointeeConst = pt.isConstQualified();
    pt = pt.getCanonicalType().getUnqualifiedType();
    auto ph = pd ? hints.params.find(pd) : hints.params.end();
    if (ph != hints.params.end()) {  // `void *` parameter cast to a struct, or container_of on the parameter
      p.opaqueHandle = pt->isVoidType();
      pt = ctx.getRecordType(ph->second.rd).getCanonicalType();
      p.at = ph->second.off;
      p.viaContainerOf = ph->second.viaSub;
    }
    if (pt->isVoidType()) p.pointee = "void";
    else if (pt->isFunctionType()) p.pointee = "function";
    else if (pt->isPointerType()) { p.pointee = "pointer"; p.pointeeSize = ctx.getTypeSizeInChars(pt).getQuantity(); }
    else if ((pt->isIntegerType() || pt->isEnumeralType()) && layoutSane(pt)) {
      p.pointee = "int";
      p.pointeeIsChar = pt->isSpecificBuiltinType(BuiltinType::Char_S) || pt->isSpecificBuiltinType(BuiltinType::Char_U);
      p.pointeeBits = static_cast<unsigned>(ctx.getTypeSize(pt));
      p.pointeeSize = ctx.getTypeSizeInChars(pt).getQuantity();
    } else if (auto *rd = pt->getAsRecordDecl()) {
      p.pointee = "struct";
      p.structName = rd->getNameAsString();
      if (!rd->getDefinition()) p.opaqueHandle = true;  // never defined here (wl_client, wl_resource, ...): library state, the code cannot look inside
      // std::basic_string<char>/<wchar_t> (libstdc++): a self-consistent SSO-aware synthesis (entry::PlannedParam::
      // StdString) replaces the generic byte-buffer layout below for this parameter -- see paramInfoOfType's caller
      // in lib/scan/Scan.cpp ("kind: string"/"kind: wstring") and IMPLEMENTATION_PLAN "std::string 不变式建模".
      if (auto *ctd = llvm::dyn_cast<ClassTemplateSpecializationDecl>(rd); ctd && rd->getQualifiedNameAsString() == "std::basic_string") {
        const auto &args = ctd->getTemplateArgs();
        if (args.size() >= 1 && args[0].getKind() == TemplateArgument::Type) {
          QualType charTy = args[0].getAsType().getCanonicalType();
          if ((charTy->isSpecificBuiltinType(BuiltinType::Char_S) || charTy->isSpecificBuiltinType(BuiltinType::Char_U)) ||
              charTy->isSpecificBuiltinType(BuiltinType::WChar_S) || charTy->isSpecificBuiltinType(BuiltinType::WChar_U)) {
            p.isStdString = true;
            p.stdStringCharBits = static_cast<unsigned>(ctx.getTypeSize(charTy));
          }
        }
      }
      // std::vector<T>/std::map<K,V> (libstdc++), T/K/V a scalar (arithmetic, non-bool) type of at most 8 bytes:
      // self-consistent synthesis (entry::PlannedParam::StdVector/StdMap) replaces the generic byte-buffer layout --
      // see Scan.cpp ("kind: vector"/"kind: map") and IMPLEMENTATION_PLAN "std::vector/std::map 入口参数合成自洽化".
      // `vector<bool>` (a bitset specialization, a different ABI entirely) and any non-scalar element/key/value type
      // (nested containers, std::string, structs -- a correct synthesis of those would need to recurse into this
      // same machinery, out of scope for this pass; the parameter still gets the generic struct-buffer treatment)
      // are deliberately excluded.
      auto scalarBits = [&](QualType t) -> unsigned {
        t = t.getCanonicalType();
        if (t->isBooleanType() || !layoutSane(t)) return 0;
        if (!t->isIntegerType() && !t->isFloatingType()) return 0;
        unsigned bits = static_cast<unsigned>(ctx.getTypeSize(t));
        return (bits == 8 || bits == 16 || bits == 32 || bits == 64) ? bits : 0;
      };
      if (auto *ctd = llvm::dyn_cast<ClassTemplateSpecializationDecl>(rd); ctd && rd->getQualifiedNameAsString() == "std::vector") {
        // `getTemplateArgs()` always has both (resolved) arguments, written or defaulted: T, Alloc. A non-default
        // allocator is excluded (as for std::map's Compare/Alloc above): it could change the object's layout.
        const auto &args = ctd->getTemplateArgs();
        bool defaultAlloc = args.size() == 2 && args[1].getKind() == TemplateArgument::Type &&
                             [&] { auto *ard = args[1].getAsType().getCanonicalType()->getAsRecordDecl();
                                   return ard && ard->getQualifiedNameAsString() == "std::allocator"; }();
        if (args.size() >= 1 && args[0].getKind() == TemplateArgument::Type && defaultAlloc) {
          if (unsigned bits = scalarBits(args[0].getAsType())) {
            p.isStdVector = true;
            p.stdVectorElemBits = bits;
          }
        }
      }
      if (auto *ctd = llvm::dyn_cast<ClassTemplateSpecializationDecl>(rd); ctd && rd->getQualifiedNameAsString() == "std::map") {
        // `getTemplateArgs()` always has all 4 (resolved) arguments, written or defaulted: Key, T, Compare, Alloc.
        // Only the default comparator/allocator is handled -- a custom one could change the (empty-base) object
        // layout this synthesis assumes, or (for a custom comparator) need actual key comparisons, which this
        // deliberately-narrowed model (see InitPlan.h "StdMap") avoids needing at all by only ever having 0 or 1 node.
        const auto &args = ctd->getTemplateArgs();
        auto isRecordNamed = [&](const TemplateArgument &a, const char *qname) {
          if (a.getKind() != TemplateArgument::Type) return false;
          auto *ard = a.getAsType().getCanonicalType()->getAsRecordDecl();
          return ard && ard->getQualifiedNameAsString() == qname;
        };
        if (args.size() == 4 && args[0].getKind() == TemplateArgument::Type && args[1].getKind() == TemplateArgument::Type &&
            isRecordNamed(args[2], "std::less") && isRecordNamed(args[3], "std::allocator")) {
          unsigned kb = scalarBits(args[0].getAsType()), vb = scalarBits(args[1].getAsType());
          if (kb && vb) {
            p.isStdMap = true;
            p.stdMapKeyBits = kb;
            p.stdMapValBits = vb;
          }
        }
      }
      if (rd->isCompleteDefinition() && layoutSane(pt)) {
        p.pointeeSize = ctx.getTypeSizeInChars(pt).getQuantity();
        p.structHasPointers = structHasPointers(rd);
        p.ptrFields = collectPtrFieldsCached(ctx, rd, 2, hints);
        collectScalarFields(ctx, rd, 0, "", 0, p.scalarFields);
        collectInlineArrayCounts(ctx, rd, p.inlineCounts);
      }
    } else p.pointee = "other";
    auto ud = pd ? hints.userData.find(pd) : hints.userData.end();
    if (ud != hints.userData.end() && layoutSane(ctx.getRecordType(ud->second))) {
      p.udStruct = ud->second->getNameAsString();
      p.udSize = ctx.getTypeSizeInChars(ctx.getRecordType(ud->second)).getQuantity();
      p.udOwned = hints.freedTypes.count(ud->second) > 0;
      p.udPtrFields = collectPtrFieldsCached(ctx, ud->second, 2, hints);
    }
  } else p.kind = "other";
  return p;
}
ParamInfo paramInfo(ASTContext &ctx, const ParmVarDecl *pd, unsigned idx, const VoidHints &hints) {
  return paramInfoOfType(ctx, pd->getType(), pd->getName().str(), pd, idx, hints);
}
// counts direct calls between the functions of this file
class CallGraphVisitor : public RecursiveASTVisitor<CallGraphVisitor> {
 public:
  CallGraphVisitor(std::map<std::string, unsigned> &callers, std::vector<std::string> &callees, const std::string &self, const std::set<std::string> &defined)
      : callers_(callers), callees_(callees), self_(self), defined_(defined) {}
  bool VisitCallExpr(CallExpr *c) {
    if (auto *fd = c->getDirectCallee()) {
      std::string n = fnName(fd);
      if (std::find(callees_.begin(), callees_.end(), n) == callees_.end()) callees_.push_back(n);
      if (n != self_ && defined_.count(n)) ++callers_[n];
    }
    return true;
  }

 private:
  std::map<std::string, unsigned> &callers_;
  std::vector<std::string> &callees_;
  const std::string &self_;
  const std::set<std::string> &defined_;
};

// True if the function still contains compile errors after Clang's recovery (unknown types, undeclared identifiers, ...).
class ErrorFinder : public RecursiveASTVisitor<ErrorFinder> {
 public:
  bool found = false;
  bool VisitExpr(Expr *e) { if (e->containsErrors()) found = true; return !found; }
  bool VisitDecl(Decl *d) { if (d->isInvalidDecl()) found = true; return !found; }
  bool VisitTypeLoc(TypeLoc) { return true; }
};

// recover mode: remembers every error (the unknown type names drive the stub typedefs) instead of printing it
class CapturingDiags : public DiagnosticConsumer {
 public:
  explicit CapturingDiags(Module &m) : m_(m) {}
  void HandleDiagnostic(DiagnosticsEngine::Level lvl, const Diagnostic &info) override {
    DiagnosticConsumer::HandleDiagnostic(lvl, info);
    if (lvl < DiagnosticsEngine::Error) return;
    SmallString<256> text;
    info.FormatDiagnostic(text);
    Module::Diag d{"", 0, text.str().str()};
    if (info.hasSourceManager() && info.getLocation().isValid()) {
      PresumedLoc p = info.getSourceManager().getPresumedLoc(info.getSourceManager().getExpansionLoc(info.getLocation()));
      if (p.isValid()) { d.file = p.getFilename(); d.line = p.getLine(); }
    }
    static const std::string idKey = "use of undeclared identifier '";
    auto ik = d.text.find(idKey);
    if (ik != std::string::npos) {
      auto ie = d.text.find('\'', ik + idKey.size());
      if (ie != std::string::npos) m_.unknownIdents.insert(d.text.substr(ik + idKey.size(), ie - ik - idKey.size()));
    }
    static const std::string key = "unknown type name '";
    auto k = d.text.find(key);
    if (k != std::string::npos) {
      auto e = d.text.find('\'', k + key.size());
      if (e != std::string::npos) m_.unknownTypes.insert(d.text.substr(k + key.size(), e - k - key.size()));
    }
    m_.clangErrors.push_back(std::move(d));
  }

 private:
  Module &m_;
};

class MissingHeaders : public PPCallbacks {
 public:
  explicit MissingHeaders(Module &m) : m_(m) {}
  bool FileNotFound(StringRef name) override {
    m_.missingHeaders.insert(name.str());
    return true;  // skip the include, no diagnostic: the header counts as empty
  }

 private:
  Module &m_;
};

// Single-header-library carve-out (docs/DESIGN.md §22.110 + follow-up): the `#define X_IMPLEMENTATION` +
// `#include "x.h"` idiom (stb_image.h, dr_libs, qoi, miniz, nuklear, ...) guards the header's function bodies
// behind an `#ifdef X_IMPLEMENTATION` block whose macro only the file that wants the real implementation ever
// `#define`s. That is structurally different from the shared-header case `isSourceExtension`'s comment warns
// about (a `static inline` helper in a widely-`#include`d header, never gated behind a macro the *including*
// file itself turns on) -- so instead of trusting the `.h` extension, FnCollector asks a much narrower question
// per header function: "is this body inside a simple `#ifdef`/`#ifndef`/`#if defined(...)` region whose single
// controlling macro was `#define`d by the MAIN file itself (not the header, not a command-line `-D`)?". Deliberately
// narrow: only `defined(X)`/`defined X`/`X` single-macro conditions, only the region before any `#elif`/`#else`
// (the "then" branch) -- a compound condition (`defined(X) && defined(Y)`) or a macro defined only via `-D`/an
// `-include`d config header (e.g. `__KERNEL__`, `CONFIG_*` in a kbuild build) is left out on purpose, which is
// exactly what keeps this from recreating the kbuild regression recorded in DESIGN.md §22.110 ("后续尝试了一个
// 简化版修复,发现真实回归,已撤回"): real kernel headers' `static inline` bodies are never gated behind a macro
// the *consuming* .c file itself `#define`s -- their guards are either unconditional, the header's own include
// guard, or a `CONFIG_*`/`__KERNEL__` macro that arrives via `-D`/`-include`, none of which land in the main
// file, so `mainFileDefinedMacros` never contains them and no region is ever allowed for that scan. Registered
// unconditionally (not just in recover mode): single-header libraries routinely compile clean.
class MainMacroIfdefs : public PPCallbacks {
 public:
  MainMacroIfdefs(Module &m, const SourceManager &sm, const LangOptions &lo) : m_(m), sm_(sm), lo_(lo) {}

  void MacroDefined(const Token &nameTok, const MacroDirective *) override {
    if (nameTok.getLocation().isValid() && nameTok.getIdentifierInfo() && sm_.isInMainFile(nameTok.getLocation()))
      m_.mainFileDefinedMacros.insert(nameTok.getIdentifierInfo()->getName().str());
  }

  void Ifdef(SourceLocation loc, const Token &nameTok, const MacroDefinition &) override {
    push(loc, nameTok.getIdentifierInfo() ? nameTok.getIdentifierInfo()->getName().str() : std::string());
  }
  // `#ifndef X` means "body runs when X is NOT defined" -- irrelevant to (and the opposite of) the
  // X_IMPLEMENTATION idiom, so this region is never treated as macro-gated.
  void Ifndef(SourceLocation loc, const Token &, const MacroDefinition &) override { push(loc, ""); }
  void If(SourceLocation loc, SourceRange condRange, ConditionValueKind) override { push(loc, simpleDefinedMacro(condRange)); }
  void Elif(SourceLocation loc, SourceRange, ConditionValueKind, SourceLocation) override { closeTop(loc); }
  void Else(SourceLocation loc, SourceLocation) override { closeTop(loc); }
  void Endif(SourceLocation loc, SourceLocation) override {
    closeTop(loc);
    if (!stack_.empty()) stack_.pop_back();
  }

 private:
  struct Frame { SourceLocation start; std::string macro; bool recorded = false; };
  std::vector<Frame> stack_;

  void push(SourceLocation loc, std::string macro) { stack_.push_back({loc, std::move(macro), false}); }
  // closes the top frame's "then" branch at `endLoc` (an `#elif`/`#else`/`#endif`); a no-op for any later
  // `#elif`/`#else` of the same `#if` (recorded stays true, so only the first branch is ever considered)
  void closeTop(SourceLocation endLoc) {
    if (stack_.empty() || stack_.back().recorded) return;
    stack_.back().recorded = true;
    if (!stack_.back().macro.empty()) record(stack_.back().start, endLoc, stack_.back().macro);
  }
  void record(SourceLocation start, SourceLocation end, const std::string &macro) {
    if (!start.isFileID() || !end.isFileID()) return;  // a region whose bounds are themselves macro-expanded: skip, stay narrow
    FileID fid = sm_.getFileID(start);
    if (fid != sm_.getFileID(end)) return;
    unsigned b = sm_.getFileOffset(start), e = sm_.getFileOffset(end);
    if (e <= b) return;
    m_.simpleIfdefRegions.push_back({macro, fid, b, e});
  }
  // "" unless `condRange`'s full (trimmed) text is exactly `defined(IDENT)` / `defined IDENT` / `IDENT`, optionally
  // wrapped in one or more balanced enclosing parens -- anything else (`&&`, `||`, `!`, comparisons, nested
  // `defined` on different macros, ...) is a compound condition and deliberately bails out to "" (no carve-out).
  std::string simpleDefinedMacro(SourceRange condRange) const {
    bool invalid = false;
    std::string text = Lexer::getSourceText(CharSourceRange::getTokenRange(condRange), sm_, lo_, &invalid).str();
    if (invalid || text.empty()) return "";
    auto trim = [](std::string s) {
      auto issp = [](unsigned char c) { return isspace(c) != 0; };
      size_t b = 0, e = s.size();
      while (b < e && issp(static_cast<unsigned char>(s[b]))) ++b;
      while (e > b && issp(static_cast<unsigned char>(s[e - 1]))) --e;
      return s.substr(b, e - b);
    };
    text = trim(text);
    for (;;) {  // strip one layer of fully-wrapping parens at a time: `(defined(X))` -> `defined(X)`
      if (text.size() < 2 || text.front() != '(' || text.back() != ')') break;
      int depth = 0;
      bool wraps = true;
      for (size_t i = 0; i < text.size(); ++i) {
        if (text[i] == '(') ++depth;
        else if (text[i] == ')') { --depth; if (depth == 0 && i + 1 != text.size()) { wraps = false; break; } }
      }
      if (!wraps) break;
      text = trim(text.substr(1, text.size() - 2));
    }
    size_t p = 0;
    static const std::string kw = "defined";
    if (text.compare(0, kw.size(), kw) == 0 && (text.size() == kw.size() || !(isalnum(static_cast<unsigned char>(text[kw.size()])) || text[kw.size()] == '_'))) {
      p = kw.size();
      while (p < text.size() && isspace(static_cast<unsigned char>(text[p]))) ++p;
      bool paren = p < text.size() && text[p] == '(';
      if (paren) ++p;
      size_t idStart = p;
      while (p < text.size() && (isalnum(static_cast<unsigned char>(text[p])) || text[p] == '_')) ++p;
      std::string ident = text.substr(idStart, p - idStart);
      if (ident.empty()) return "";
      while (p < text.size() && isspace(static_cast<unsigned char>(text[p]))) ++p;
      if (paren) { if (p >= text.size() || text[p] != ')') return ""; ++p; }
      if (p != text.size()) return "";  // trailing junk (e.g. `&& defined(Y)`): not simple, bail
      return ident;
    }
    // bare `#if X` (no `defined`): only treat as simple if the whole condition is a single identifier
    size_t idStart = 0;
    while (p < text.size() && (isalnum(static_cast<unsigned char>(text[p])) || text[p] == '_')) ++p;
    if (p == text.size() && p > idStart && !isdigit(static_cast<unsigned char>(text[0]))) return text;
    return "";
  }
  Module &m_;
  const SourceManager &sm_;
  const LangOptions &lo_;
};

// recover mode: `p->f` where `struct X` has no definition (its header is missing) is a RecoveryExpr. Collect (X, f, type):
// the type comes from how the value is used (initialiser of a typed variable, assigned from/to a typed expression,
// argument of a prototyped call, return value, compared with a typed operand, base of another member access, ...).
class StubUseFinder : public RecursiveASTVisitor<StubUseFinder> {
 public:
  StubUseFinder(ASTContext &ctx, Module &m) : ctx_(ctx), sm_(ctx.getSourceManager()), m_(m) {}
  bool TraverseFunctionDecl(FunctionDecl *fd) {
    const FunctionDecl *saved = fn_;
    fn_ = fd;
    bool r = RecursiveASTVisitor::TraverseFunctionDecl(fd);
    fn_ = saved;
    return r;
  }
  bool VisitRecoveryExpr(RecoveryExpr *r) {
    if (r->subExpressions().size() != 1) return true;
    const Expr *base = r->subExpressions()[0];
    QualType bt = base->getType().getCanonicalType();
    if (bt->isPointerType()) bt = bt->getPointeeType().getCanonicalType();
    const RecordDecl *rd = bt->getAsRecordDecl();
    // a struct without a definition, or one of our own stubs that does not have this member yet
    if (!rd || rd->getName().empty() || (rd->getDefinition() && !rd->getName().starts_with("__hlir_stub_"))) return true;
    // member name: the token where the recovery expression ends; between the base and it there must be `.` or `->`
    SourceLocation memberLoc = sm_.getExpansionLoc(r->getEndLoc());
    SourceLocation baseEnd = Lexer::getLocForEndOfToken(sm_.getExpansionLoc(base->getEndLoc()), 0, sm_, ctx_.getLangOpts());
    if (memberLoc.isInvalid() || baseEnd.isInvalid() || !sm_.isInMainFile(memberLoc)) return true;
    bool inv = false;
    const char *mb = sm_.getCharacterData(memberLoc, &inv), *bb = sm_.getCharacterData(baseEnd, &inv);
    if (inv || mb <= bb || mb - bb > 8) return true;
    std::string between(bb, mb);
    between.erase(std::remove_if(between.begin(), between.end(), [](char c) { return isspace(static_cast<unsigned char>(c)); }), between.end());
    if (between != "." && between != "->") return true;
    const char *e = mb;
    while (isalnum(static_cast<unsigned char>(*e)) || *e == '_') ++e;
    std::string member(mb, e);
    if (member.empty() || isdigit(static_cast<unsigned char>(member[0]))) return true;
    while (isspace(static_cast<unsigned char>(*e))) ++e;
    std::string structName = rd->getName().str();
    std::string stubName = "__hlir_stub_" + structName + "__" + member;
    Module::StubUse u{structName, member, "", 0};
    if (e[0] == '-' && e[1] == '>') { u.type = "struct " + stubName + " *"; u.rank = 90; }      // p->f->g: f points to a struct
    else if (e[0] == '.' && e[1] != '.') { u.type = "struct " + stubName; u.rank = 95; }       // p->f.g: f is a struct
    else if (e[0] == '[') { u.type = "unsigned char *"; u.rank = 60; }                         // p->f[i]: a buffer
    else if (e[0] == '(') return true;                                                         // a call through a pointer needs a prototype
    else {
      QualType t = fromContext(r);
      std::string txt;
      int rank = 0;
      if (!t.isNull() && fieldType(t, txt, rank)) { u.type = txt; u.rank = rank; }
      else { u.type = "unsigned long"; u.rank = 1; }                                           // nothing to go on: a machine word
    }
    m_.stubUses.push_back(u);
    return true;
  }

 private:
  // canonical, storable field type; false for void/array/function/by-value records and error types
  bool fieldType(QualType t, std::string &txt, int &rank) {
    t = t.getCanonicalType().getUnqualifiedType();
    if (t.isNull() || t->containsErrors() || t->isDependentType()) return false;
    if (t->isBooleanType()) { txt = "_Bool"; rank = 8; return true; }
    if (t->isEnumeralType()) { txt = "int"; rank = 32; return true; }
    if (t->isIntegerType()) {
      txt = t.getAsString(ctx_.getPrintingPolicy());
      rank = static_cast<int>(ctx_.getTypeSize(t));
      return true;
    }
    if (t->isPointerType()) {
      QualType pt = t->getPointeeType();
      txt = t.getAsString(ctx_.getPrintingPolicy());
      if (pt->isFunctionType() || txt.find("(") != std::string::npos || txt.find("unnamed") != std::string::npos || txt.find("anonymous") != std::string::npos) txt = "void *";
      rank = 100;
      return true;
    }
    return false;
  }
  QualType exprType(const Expr *e) {
    if (!e) return {};
    QualType t = e->IgnoreParenImpCasts()->getType();
    if (t.isNull() || t->containsErrors() || t->isDependentType()) return {};
    return t;
  }
  // the type the context requires of `r`; climbs through casts and parentheses
  QualType fromContext(const Expr *r) {
    DynTypedNode node = DynTypedNode::create(*r);
    for (int depth = 0; depth < 5; ++depth) {
      auto parents = ctx_.getParents(node);
      if (parents.empty()) break;
      const DynTypedNode &p = parents[0];
      const Expr *self = node.get<Expr>();
      if (auto *vd = p.get<VarDecl>()) return vd->getType();
      if (auto *bo = p.get<BinaryOperator>()) {
        const Expr *other = bo->getLHS()->IgnoreParenImpCasts() == self->IgnoreParenImpCasts() ? bo->getRHS() : bo->getLHS();
        if (bo->isLogicalOp()) return ctx_.IntTy;
        return exprType(other);
      }
      if (auto *ce = p.get<CallExpr>()) {
        const FunctionDecl *callee = ce->getDirectCallee();
        const FunctionProtoType *fpt = callee ? callee->getType()->getAs<FunctionProtoType>() : nullptr;
        for (unsigned i = 0; fpt && i < ce->getNumArgs() && i < fpt->getNumParams(); ++i)
          if (ce->getArg(i)->IgnoreParenImpCasts() == self->IgnoreParenImpCasts()) return fpt->getParamType(i);
        return {};
      }
      if (p.get<ReturnStmt>()) return fn_ ? fn_->getReturnType() : QualType();
      if (p.get<IfStmt>() || p.get<WhileStmt>() || p.get<DoStmt>() || p.get<ForStmt>()) return ctx_.IntTy;
      if (auto *uo = p.get<UnaryOperator>()) {
        if (uo->getOpcode() == UO_LNot) return ctx_.IntTy;
        if (uo->getOpcode() == UO_AddrOf) return {};
      }
      if (p.get<ImplicitCastExpr>() || p.get<ParenExpr>() || p.get<UnaryOperator>() || p.get<CStyleCastExpr>()) { node = p; continue; }
      break;
    }
    return {};
  }
  ASTContext &ctx_;
  const SourceManager &sm_;
  Module &m_;
  const FunctionDecl *fn_ = nullptr;
};

// parameters handed to free()-like functions (directly, through a local that was assigned from them, or by passing them to a
// function that frees its own parameter): the contract of such a function is "pass me a heap object"
class FreeUseFinder : public RecursiveASTVisitor<FreeUseFinder> {
 public:
  std::set<const ParmVarDecl *> freed;
  bool VisitCallExpr(CallExpr *c) {
    const FunctionDecl *fd = c->getDirectCallee();
    if (!fd) return true;
    std::string n = fd->getIdentifier() ? fd->getName().str() : "";
    bool freeLike = n == "free" || n == "kfree" || n == "vfree" || n == "kvfree" || n == "cfree" || (n.size() > 5 && n.compare(n.size() - 5, 5, "_free") == 0);
    if (freeLike && c->getNumArgs() > 0) {
      if (const ParmVarDecl *pd = param(c->getArg(0), 0)) freed.insert(pd);
      return true;
    }
    if (const FunctionDecl *def = fd->getDefinition())
      for (unsigned i = 0; i < c->getNumArgs() && i < def->getNumParams(); ++i)
        if (const ParmVarDecl *pd = param(c->getArg(i), 0)) edges_.push_back({pd, def->getParamDecl(i)});
    return true;
  }
  void propagate() {
    for (int pass = 0; pass < 8; ++pass) {
      bool changed = false;
      for (auto &e : edges_)
        if (freed.count(e.second) && freed.insert(e.first).second) changed = true;
      if (!changed) break;
    }
  }

 private:
  const ParmVarDecl *param(const Expr *e, int depth) {
    while (true) {
      e = e->IgnoreParens();
      if (auto *ce = dyn_cast<CastExpr>(e)) { e = ce->getSubExpr(); continue; }
      break;
    }
    if (auto *dr = dyn_cast<DeclRefExpr>(e)) {
      if (auto *pd = dyn_cast<ParmVarDecl>(dr->getDecl())) return pd;
      if (auto *vd = dyn_cast<VarDecl>(dr->getDecl()))
        if (vd->hasInit() && depth < 3) return param(vd->getInit(), depth + 1);  // bzFile *bzf = (bzFile *)b; ... free(bzf)
    }
    return nullptr;
  }
  std::vector<std::pair<const ParmVarDecl *, const ParmVarDecl *>> edges_;
};

static bool isSourceExtension(llvm::StringRef path);

// Finds the functions whose address is taken (a reference that is not the callee of a call), and those of them whose address
// escapes its own C type. A call through a function pointer of type T can only reach a function of a type compatible with
// T, so the dispatcher of that call lists only them (cTypeKey) -- except functions converted to another type, which real
// code then calls through it (`(void (*)(void *))kfree`, a `void *` callback slot, a union of function pointers): those
// stay candidates of every call with their core signature. Escapes count wherever they are written, headers included.
// The name a record is known by: its tag (`struct file_operations`), or, for `typedef struct { ... } T;`, the
// typedef it was declared through. QNX's `resmgr_io_funcs_t` has no tag at all, so without the fallback every QNX
// dispatch table would be invisible. "" when neither exists (a truly anonymous inline struct), which is not a
// vtable anyone can name in an interface model anyway.
std::string recordTagName(const RecordDecl *rd) {
  if (!rd) return "";
  if (!rd->getName().empty()) return rd->getName().str();
  if (const TypedefNameDecl *td = rd->getTypedefNameForAnonDecl()) return td->getName().str();
  return "";
}

// Is this field a dispatch slot, i.e. does it hold a function pointer? `.owner = THIS_MODULE` is not.
bool isFuncPtrField(const FieldDecl *f) {
  if (!f || f->getName().empty()) return false;
  QualType ft = f->getType().getCanonicalType();
  return ft->isPointerType() && ft->getPointeeType()->isFunctionType();
}

class AddrTakenFinder : public RecursiveASTVisitor<AddrTakenFinder> {
 public:
  AddrTakenFinder(Module &m, const SourceManager &sm) : m_(m), sm_(sm) {}
  // The kernel's __ADDRESSABLE(sym) (every EXPORT_SYMBOL) stores `(void *)(uintptr_t)&sym` into a discarded
  // `__UNIQUE_ID___addressable_sym` only to keep the symbol alive: nothing ever calls through it, so it is no escape.
  // Counted as one, every exported function was a candidate of every call with its signature (dccp_send_reset's
  // rebuild_header(sk) reached dccp_invalid_packet(skb)).
  // The variable a dispatch table is written as (`static const struct file_operations snd_ctl_f_ops = {...}`):
  // the natural name for that table instance. Nested/anonymous ones fall back to their source position.
  bool TraverseVarDecl(VarDecl *v) {
    std::string savedName = initVarName_;
    if (v->hasInit()) initVarName_ = v->getNameAsString();
    bool saved = inAddressable_;
    if (v->getName().contains("__addressable_")) inAddressable_ = true;
    bool r = RecursiveASTVisitor<AddrTakenFinder>::TraverseVarDecl(v);
    inAddressable_ = saved;
    initVarName_ = savedName;
    return r;
  }
  bool VisitCastExpr(CastExpr *c) {
    if (inAddressable_) return true;
    // to another function pointer type: only an incompatible one lets a call of another type reach it; to anything
    // else (`void *`, an integer, bool) the address may come back as any type
    QualType to = c->getType().getCanonicalType();
    bool toFn = to->isPointerType() && to->getPointeeType()->isFunctionProtoType();
    std::string tk = toFn ? cTypeKey(to) : "";
    for (auto *fd : fnRefs(c->getSubExpr()))
      if (!toFn || !cTypesCompatible(tk, cTypeKey(fd->getType()))) m_.addrEscaped.insert(fd->getCanonicalDecl());
    return true;
  }
  bool VisitBinaryOperator(BinaryOperator *b) {
    if (b->getOpcode() == BO_Assign)
      if (auto *me = dyn_cast<MemberExpr>(b->getLHS()->IgnoreParenImpCasts()))
        if (auto *f = dyn_cast<FieldDecl>(me->getMemberDecl())) {
          if (f->getParent()->isUnion())
            for (auto *fd : fnRefs(b->getRHS())) m_.addrEscaped.insert(fd->getCanonicalDecl());
          // `fops->unlocked_ioctl = my_ioctl;` -- the same registration a static initialiser does, written at run
          // time instead. A union member is recorded here too: escaping as a VALUE (just above) and being written
          // to a named slot are separate facts, and the second one stays true.
          if (isFuncPtrField(f)) {
            std::string tag = recordTagName(f->getParent());
            if (!tag.empty()) {
              std::string inst = instanceOf(tag, b->getExprLoc(), exprText(me->getBase(), f->getASTContext()));
              m_.vtableInstances[inst].tag = tag;
              for (auto *fd : fnRefs(b->getRHS())) bind(fd, tag, f->getName().str(), b->getExprLoc(), inst);
            }
          }
        }
    return true;
  }
  bool VisitInitListExpr(InitListExpr *il) {
    if (auto *rt = il->getType()->getAs<RecordType>())
      if (rt->getDecl()->isUnion())
        for (unsigned i = 0; i < il->getNumInits(); ++i)
          for (auto *fd : fnRefs(il->getInit(i))) m_.addrEscaped.insert(fd->getCanonicalDecl());
    recordInitBindings(il);
    return true;
  }
  bool VisitCallExpr(CallExpr *c) {
    if (auto *dr = dyn_cast<DeclRefExpr>(c->getCallee()->IgnoreParenImpCasts())) callees_.insert(dr);
    return true;
  }
  bool VisitDeclRefExpr(DeclRefExpr *dr) {
    // only references written in the analysed file count: they are the handlers/callbacks this module registers (a
    // header's own function-pointer tables would make every indirect call "possibly" reach unrelated functions).
    // A `.c` the file #includes is part of it, as for the functions lowered (isSourceExtension): expat's
    // xmltok_ns.c stores initScanProlog into the encoding it builds, and without it every call through that
    // pointer fell to the opaque fallback.
    if (auto *fd = dyn_cast<FunctionDecl>(dr->getDecl())) {
      SourceLocation eloc = sm_.getExpansionLoc(dr->getLocation());
      if (!callees_.count(dr) && (sm_.isInMainFile(eloc) || isSourceExtension(sm_.getFilename(eloc))))
        m_.addrTaken.insert(fd->getCanonicalDecl());
    }
    return true;
  }

 private:
  Module &m_;
  const SourceManager &sm_;
  std::set<const DeclRefExpr *> callees_;
  bool inAddressable_ = false;
  std::string initVarName_;  // the variable currently being initialised, for vtable instance names

  // `static const struct file_operations f = { .read = r, .unlocked_ioctl = i };` -- which handler was registered
  // in which slot of which vtable struct. hlir::iface matches `tag#field` against an interface model, so the scan
  // driver can take the handlers a module really registers as its entries instead of every root-looking function
  // (DESIGN.md §22.359).
  //
  // Only the SEMANTIC form can be walked: there position i is field i. When designated initialisers were used --
  // which is how the kernel writes every one of these tables -- RecursiveASTVisitor hands us the SYNTACTIC form
  // instead, whose inits are DesignatedInitExprs in SOURCE order, so pairing those with fields() positionally
  // would attribute almost every binding to the wrong field. The semantic form hangs off it but is implicit code
  // that RAV does not descend into by default, so step across to it here.
  //
  // A nested record initialiser (`struct outer o = { .i = { .cb = f } }`) is reached by the visitor in its own
  // right and keyed by ITS own tag, so `cb` binds to `inner`, never to `outer`. Arrays of vtables work the same
  // way: the array's own list has no record type and is skipped, and each element is visited as itself. A list
  // that is reached both ways only ever re-inserts into a set, so double counting is harmless by construction.
  void recordInitBindings(InitListExpr *syn) {
    InitListExpr *il = syn->isSemanticForm() ? syn : syn->getSemanticForm();
    if (!il) return;
    const RecordType *rt = il->getType()->getAs<RecordType>();
    if (!rt) return;
    const RecordDecl *rd = rt->getDecl();
    if (rd->isUnion()) return;  // which member of a union is live is not a fact an initialiser settles
    std::string tag = recordTagName(rd);
    if (tag.empty()) return;
    std::string inst = instanceOf(tag, syn->getBeginLoc(), initVarName_);
    m_.vtableInstances[inst].tag = tag;
    unsigned i = 0;
    for (auto *f : rd->fields()) {
      if (i >= il->getNumInits()) break;
      const Expr *init = il->getInit(i++);  // consumed even when the field is skipped: position i IS field i
      if (!init || !isFuncPtrField(f)) continue;
      for (auto *fd : fnRefs(init)) bind(fd, tag, f->getName().str(), init->getExprLoc(), inst);
    }
  }

  // Only registrations written in the analysed file count -- the same rule VisitDeclRefExpr applies to addrTaken.
  // A dispatch table defined in a header belongs to whoever included it, not to every unit that can see it, and
  // counting those would make every module look as if it registered the others' handlers.
  void bind(const FunctionDecl *fd, const std::string &tag, const std::string &field, SourceLocation site,
            const std::string &instance) {
    SourceLocation eloc = sm_.getExpansionLoc(site);
    if (!eloc.isValid()) return;
    if (!sm_.isInMainFile(eloc) && !isSourceExtension(sm_.getFilename(eloc))) return;
    m_.vtableBindings[fnName(fd)].insert(tag + "#" + field);
    // ... and which TABLE it was: a module registers many tables of the same type (sound/core alone has 14
    // `file_operations`), so "some function is in this interface's `open` slot" does not say WHICH `open` belongs
    // with a given `ioctl`. Pairing them is what a session constructor needs (DESIGN.md §22.368 §7).
    if (!instance.empty()) m_.vtableInstances[instance].slots[field] = fnName(fd);
  }

  // A stable, human-readable identity for one dispatch-table instance. For a table written as an initialiser it is
  // the variable (or, for a nested/anonymous one, its source position); for the field-by-field assignment form it
  // is the object being assigned to, qualified by the function doing it.
  std::string instanceOf(const std::string &tag, SourceLocation loc, const std::string &base) {
    PresumedLoc pl = sm_.getPresumedLoc(sm_.getExpansionLoc(loc));
    std::string where = pl.isValid() ? std::string(pl.getFilename()) + ":" + std::to_string(pl.getLine()) : std::string("?");
    return tag + "@" + (base.empty() ? where : base + " (" + where + ")");
  }
  static std::string exprText(const Expr *e, const ASTContext &ctx) {
    if (!e) return "";
    std::string out;
    llvm::raw_string_ostream os(out);
    e->printPretty(os, nullptr, ctx.getPrintingPolicy());
    os.flush();
    return out.size() > 64 ? out.substr(0, 64) : out;
  }

  // the functions an expression is the address of: `f`, `&f`, `(f)`, `c ? f : g`, `(T)f`, `x, f`
  static std::vector<const FunctionDecl *> fnRefs(const Expr *e) {
    std::vector<const FunctionDecl *> out;
    std::function<void(const Expr *)> walk = [&](const Expr *x) {
      if (!x) return;
      x = x->IgnoreParens();
      if (auto *dr = dyn_cast<DeclRefExpr>(x)) {
        if (auto *fd = dyn_cast<FunctionDecl>(dr->getDecl())) out.push_back(fd);
      } else if (auto *ce = dyn_cast<CastExpr>(x)) walk(ce->getSubExpr());
      else if (auto *uo = dyn_cast<UnaryOperator>(x)) {
        if (uo->getOpcode() == UO_AddrOf) walk(uo->getSubExpr());
      } else if (auto *co = dyn_cast<ConditionalOperator>(x)) { walk(co->getTrueExpr()); walk(co->getFalseExpr()); }
      else if (auto *bc = dyn_cast<BinaryConditionalOperator>(x)) { walk(bc->getCommon()); walk(bc->getFalseExpr()); }
      else if (auto *bo = dyn_cast<BinaryOperator>(x)) {
        if (bo->getOpcode() == BO_Comma) walk(bo->getRHS());
      }
    };
    walk(e);
    return out;
  }
};

// ------------------------------------------------------------------------------------------------ driver
std::string initFunctionForString(unsigned idx, const std::string &s) {
  std::ostringstream os;
  os << "core.func @__hlir_init.str" << idx << "() -> void {\n^entry:\n";
  os << "  %flag = core.global_addr @__str." << idx << ".__init {size=1} : ptr\n";
  os << "  %one = core.const 1 : i8\n  %zero = core.const 0 : i8\n";
  os << "  %cur = core.load %flag {waived=\"object known\"} : i8\n  %isz = core.icmp eq %cur, %zero : bool\n";
  os << "  core.cond_br %isz, ^do, ^done\n^do:\n  core.store %one, %flag {waived=\"object known\"}\n";
  os << "  %g = core.global_addr @__str." << idx << " {size=" << s.size() + 1 << ", const} : ptr\n";
  for (size_t i = 0; i < s.size(); ++i) {
    os << "  %b" << i << " = core.const " << static_cast<int>(static_cast<signed char>(s[i])) << " : i8\n";
    if (i) os << "  %q" << i << " = core.const " << i << " : i64\n  %p" << i << " = core.ptr_add %g, %q" << i << " {waived=\"in-bounds by construction\"} : ptr\n";
    os << "  core.store %b" << i << ", " << (i ? "%p" + std::to_string(i) : "%g") << " {waived=\"in-bounds by construction\"}\n";
  }
  os << "  core.return\n^done:\n  core.return\n}\n";
  return os.str();
}

// every class with a definition that has virtual functions (or dynamic bases): the candidates of a virtual call
class ClassCollector : public RecursiveASTVisitor<ClassCollector> {
 public:
  explicit ClassCollector(std::vector<const CXXRecordDecl *> &out) : out_(out) {}
  bool VisitCXXRecordDecl(CXXRecordDecl *rd) {
    if (rd->isCompleteDefinition() && !rd->isDependentContext() && !rd->isInvalidDecl() && !rd->isLambda() && rd->isDynamicClass()) out_.push_back(rd);
    return true;
  }
  bool shouldVisitTemplateInstantiations() const { return true; }

 private:
  std::vector<const CXXRecordDecl *> &out_;
};

// offsets of the subobjects of class `target` inside a complete object of class `rd`
void subobjectOffsetsOf(ASTContext &ctx, const CXXRecordDecl *rd, const CXXRecordDecl *target, uint64_t base, std::vector<uint64_t> &out) {
  forEachSubobject(ctx, rd, [&](const CXXRecordDecl *c, uint64_t off, bool) {
    if (c->getCanonicalDecl() == target->getCanonicalDecl()) out.push_back(base + off);
  });
}

// `@__hlir_vcall.<method>(this, args...)`: loads the vptr of the object `this` points to and calls the final overrider of the
// dynamic type; `@__hlir_vdelete.<dtor>(this)`: runs the dynamic type's destructor and frees the whole object. Dynamic types are
// the classes of this translation unit derived from the method's class; anything else is an external call (opaque).
std::string vcallDispatcher(ASTContext &ctx, Module &mod, const std::string &name, const Module::VCall &vc) {
  const CXXMethodDecl *md = vc.md;
  const CXXRecordDecl *S = md->getParent();
  std::vector<std::string> ptys;
  std::string retTy = "void";
  bool sret = false;
  if (!vc.isDelete) {
    bool ok = true;
    sigOfDecl(ctx, md, ok);
    if (!ok) return "";
    sret = isRecordTy(md->getReturnType());
    if (sret) ptys.push_back("ptr");
    for (QualType t : sigParams(md)) ptys.push_back(slotTy(ctx, t));
    retTy = sret ? "void" : slotTy(ctx, md->getReturnType());
  } else ptys.push_back("ptr");
  size_t thisIdx = sret ? 1 : 0;
  std::string params, plain;
  for (size_t i = 0; i < ptys.size(); ++i) { params += (i ? ", " : "") + ("%a" + std::to_string(i) + ": " + ptys[i]); plain += (i ? ", " : "") + ptys[i]; }
  std::ostringstream body;
  std::string thisV = "%a" + std::to_string(thisIdx);
  body << "core.func @" << name << "(" << plain << ") -> " << retTy << " {\n^entry(" << params << "):\n";
  body << "  core.check.null " << thisV << "\n  core.check.uaf " << thisV << "\n  core.check.oob " << thisV << " {w=8, access=\"r\"}\n  core.check.uninit " << thisV << " {w=8}\n";
  body << "  %vp = core.load " << thisV << " : ptr\n";
  auto argsWith = [&](const std::string &thisArg) {
    std::string a;
    for (size_t i = 0; i < ptys.size(); ++i) a += (i ? ", " : "") + (i == thisIdx ? thisArg : "%a" + std::to_string(i));
    return a;
  };
  unsigned k = 0;
  std::set<std::string> seen;
  for (const CXXRecordDecl *D : mod.classes) {
    if (D->getCanonicalDecl() != S->getCanonicalDecl() && !D->isDerivedFrom(S)) continue;
    if (D->isAbstract() || !layoutSane(ctx.getRecordType(D))) continue;
    std::vector<uint64_t> offS;
    subobjectOffsetsOf(ctx, D, S, 0, offS);
    const CXXMethodDecl *ov = vc.isDelete ? D->getDestructor() : md->getCorrespondingMethodInClass(D);
    if (!ov || ov->isPureVirtual() || ov->isDeleted()) continue;
    std::vector<uint64_t> offP;
    subobjectOffsetsOf(ctx, D, ov->getParent(), 0, offP);
    for (uint64_t oS : offS) {
      std::string marker = vtblName(D, oS);
      if (!seen.insert(marker).second) continue;
      int64_t delta = 0;
      if (vc.isDelete) delta = -static_cast<int64_t>(oS);
      else {
        int64_t oP = offP.empty() ? static_cast<int64_t>(oS) : static_cast<int64_t>(offP[0]);
        for (uint64_t p : offP) {  // the overrider's subobject that contains the S-subobject at oS
          std::vector<uint64_t> inside;
          subobjectOffsetsOf(ctx, ov->getParent(), S, 0, inside);
          for (uint64_t i : inside) if (p + i == oS) oP = static_cast<int64_t>(p);
        }
        delta = oP - static_cast<int64_t>(oS);
      }
      // the target is lowered / declared like any callee
      if (const FunctionDecl *def = ov->getDefinition()) {
        if (mod.defined.insert(fnName(def)).second) mod.work.push_back(def);
      }
      bool dok = true;
      std::string tname = fnName(ov);
      if (!mod.defined.count(tname) && !mod.declares.count(tname)) {
        std::string sg = sigOfDecl(ctx, ov, dok);
        if (dok) mod.declares[tname] = "core.declare @" + tname + sg;
      }
      std::string kk = std::to_string(k++);
      body << "  %m" << kk << " = core.global_addr @" << marker << " {size=" << markerBytes(ctx, D, oS) << "} : ptr\n  %e" << kk << " = core.ptr_cmp eq %vp, %m" << kk << " : bool\n"
           << "  core.cond_br %e" << kk << ", ^hit" << kk << ", ^nx" << kk << "\n^hit" << kk << ":\n";
      std::string tv = thisV;
      if (delta) {
        body << "  %t" << kk << " = core.const " << delta << " : i64\n  %q" << kk << " = core.ptr_add " << thisV << ", %t" << kk << " {waived=\"in-bounds by construction\"} : ptr\n";
        tv = "%q" + kk;
      }
      std::string call = "@" + tname + "(" + argsWith(tv) + ")";
      // this dispatcher has no `try`/`catch` context of its own (it is never inside a user's try block): an
      // exception escaping the real overrider's call is this project's pre-existing "uncaught" outcome, the same
      // branchless `terminateProgram` mechanism as any other call site that does not get full local-catch
      // matching (see IMPLEMENTATION_PLAN "跨函数异常传播" — virtual dispatch is explicitly out of scope there).
      std::string guard = "  %eo" + kk + " = core.global_addr @__hlir_exc_obj {size=8} : ptr\n  %ev" + kk + " = core.load %eo" + kk +
                           " {waived=\"object known\"} : ptr\n  %ok" + kk + " = core.is_null %ev" + kk + " : bool\n  core.assume %ok" + kk + " {terminates=\"uncaught_exception\"}\n";
      if (vc.isDelete) {
        body << "  core.call " << call << "\n" << guard << "  core.check.free " << tv << " {expect=heap, origin=\"delete\"}\n  core.free " << tv << "\n  core.return\n";
      } else if (retTy == "void") body << "  core.call " << call << "\n" << guard << "  core.return\n";
      else body << "  %r" << kk << " = core.call " << call << " : " << retTy << "\n" << guard << "  core.return %r" << kk << "\n";
      body << "^nx" << kk << ":\n";
    }
  }
  std::string unk = "__hlir_unknown_virtual." + name.substr(name.find('.') + 1);
  mod.declares[unk] = "core.declare @" + unk + "(" + plain + ") -> " + retTy;
  if (retTy == "void") body << "  core.call @" << unk << "(" << argsWith(thisV) << ")\n  core.return\n}\n";
  else body << "  %ro = core.call @" << unk << "(" << argsWith(thisV) << ") : " << retTy << "\n  core.return %ro\n}\n";
  return body.str();
}

// `@__hlir_dyncast.<target>.<src>[.ref](this) -> ptr`: `dynamic_cast<Target*>`/`<Target&>`/`<void*>` on an object
// statically known to be (a subobject of) `src`. Loads the vptr, compares it against the marker of every subobject
// offset of every class of this module that derives from (or is) `src`, and on a match, adjusts the pointer from
// that `src` subobject to the `Target` subobject of the SAME concrete object (or to the start of the complete
// object, for `void*`). A candidate class in which `Target` is not a base at all, or is an AMBIGUOUS base (more
// than one unrelated subobject of that type), does not match — the standard requires an unambiguous base, and
// that is exactly the condition `subobjectOffsetsOf` returning something other than one offset captures. No match
// among this module's classes: the pointer form returns null (the well-defined "cast failed" result); the
// reference form cannot return null, so it traps instead (a simplified stand-in for throwing `std::bad_cast` —
// this module does not keep exceptions alive across a `dynamic_cast` failure; see IMPLEMENTATION_PLAN for why).
std::string dynCastDispatcher(ASTContext &ctx, Module &mod, const std::string &name, const Module::DynCast &dc) {
  std::ostringstream body;
  body << "core.func @" << name << "(ptr) -> ptr {\n^entry(%a0: ptr):\n";
  body << "  core.check.null %a0\n  core.check.uaf %a0\n  core.check.oob %a0 {w=8, access=\"r\"}\n  core.check.uninit %a0 {w=8}\n";
  body << "  %vp = core.load %a0 : ptr\n";
  unsigned k = 0;
  std::set<std::string> seen;
  for (const CXXRecordDecl *D : mod.classes) {
    if (D->getCanonicalDecl() != dc.src->getCanonicalDecl() && !D->isDerivedFrom(dc.src)) continue;
    if (D->isAbstract() || !layoutSane(ctx.getRecordType(D))) continue;
    int64_t targetOff = 0;
    if (dc.target) {
      std::vector<uint64_t> offT;
      subobjectOffsetsOf(ctx, D, dc.target, 0, offT);
      if (offT.size() != 1) continue;  // not a base of D, or an ambiguous one: this candidate cannot match
      targetOff = static_cast<int64_t>(offT[0]);
    }
    std::vector<uint64_t> offS;
    subobjectOffsetsOf(ctx, D, dc.src, 0, offS);
    for (uint64_t oS : offS) {
      std::string marker = vtblName(D, oS);
      if (!seen.insert(marker).second) continue;
      std::string kk = std::to_string(k++);
      body << "  %m" << kk << " = core.global_addr @" << marker << " {size=" << markerBytes(ctx, D, oS) << "} : ptr\n"
           << "  %e" << kk << " = core.ptr_cmp eq %vp, %m" << kk << " : bool\n"
           << "  core.cond_br %e" << kk << ", ^hit" << kk << ", ^nx" << kk << "\n^hit" << kk << ":\n";
      int64_t delta = targetOff - static_cast<int64_t>(oS);
      if (delta) {
        body << "  %t" << kk << " = core.const " << delta << " : i64\n  %q" << kk
             << " = core.ptr_add %a0, %t" << kk << " {waived=\"in-bounds by construction\"} : ptr\n  core.return %q" << kk << "\n";
      } else body << "  core.return %a0\n";
      body << "^nx" << kk << ":\n";
    }
  }
  if (dc.isRef) {  // simplified `std::bad_cast`: terminate, not undefined behaviour (see terminateProgram)
    body << "  %z0 = core.const 0 : i32\n  %z1 = core.icmp ne %z0, %z0 : bool\n  core.assume %z1 {terminates=\"bad_cast\"}\n  core.unreachable\n}\n";
  } else body << "  %zi = core.const 0 : i64\n  %z = core.int_to_ptr %zi : ptr\n  core.return %z\n}\n";
  return body.str();
}

// `@__hlir_typeid.<src>(this) -> ptr`: `typeid(polymorphic glvalue of static type src)`. Loads the vptr and returns
// the RTTI marker (`typeInfoMarker`) of whichever class of this module it matches; falls back to `src`'s own marker
// when the dynamic type is outside this module's closed-world view (an object whose true dynamic type was never
// seen here — the one case where the fallback must return *something*, and `src` itself is the least wrong guess,
// since every such object is statically guaranteed to be at least a `src`).
std::string typeIdDispatcher(ASTContext &ctx, Module &mod, const std::string &name, const CXXRecordDecl *src) {
  std::ostringstream body;
  body << "core.func @" << name << "(ptr) -> ptr {\n^entry(%a0: ptr):\n";
  body << "  core.check.null %a0\n  core.check.uaf %a0\n  core.check.oob %a0 {w=8, access=\"r\"}\n  core.check.uninit %a0 {w=8}\n";
  body << "  %vp = core.load %a0 : ptr\n";
  unsigned k = 0;
  std::set<std::string> seen;
  for (const CXXRecordDecl *D : mod.classes) {
    if (D->getCanonicalDecl() != src->getCanonicalDecl() && !D->isDerivedFrom(src)) continue;
    if (D->isAbstract() || !layoutSane(ctx.getRecordType(D))) continue;
    std::vector<uint64_t> offS;
    subobjectOffsetsOf(ctx, D, src, 0, offS);
    for (uint64_t oS : offS) {
      std::string marker = vtblName(D, oS);
      if (!seen.insert(marker).second) continue;
      std::string kk = std::to_string(k++);
      auto [tn, tsz] = typeInfoMarker(ctx, ctx.getRecordType(D));
      body << "  %m" << kk << " = core.global_addr @" << marker << " {size=" << markerBytes(ctx, D, oS) << "} : ptr\n"
           << "  %e" << kk << " = core.ptr_cmp eq %vp, %m" << kk << " : bool\n"
           << "  core.cond_br %e" << kk << ", ^hit" << kk << ", ^nx" << kk << "\n^hit" << kk << ":\n"
           << "  %r" << kk << " = core.global_addr @" << tn << " {size=" << tsz << ", const} : ptr\n  core.return %r" << kk << "\n"
           << "^nx" << kk << ":\n";
    }
  }
  auto [sn, ssz] = typeInfoMarker(ctx, ctx.getRecordType(src));
  body << "  %so = core.global_addr @" << sn << " {size=" << ssz << ", const} : ptr\n  core.return %so\n}\n";
  return body.str();
}

// A `.c`/`.cc`/`.cpp`/... file textually `#include`d by the main file (the X-macro "paste this translation
// unit's worth of code in, once, with different macros each time" idiom - e.g. expat's xmltok.c pulling in
// xmltok_ns.c twice to generate `Xml*` and `Xml*NS` variants of the same functions) is, by the same C
// convention that makes it safe to `#include` a `.c` file at all, meant to contribute its own standalone
// functions to THIS translation unit - unlike a shared header, it is not designed to be `#include`d from many
// unrelated files with the same unqualified external names (that would already fail to link as a real
// program). So it should be treated like main-file content for `FnCollector`'s purposes. A header still isn't:
// treating every header the same way would re-lower identical shared helpers out of every file that happens to
// include them, which is exactly what `onlyMain_` exists to avoid for the (overwhelmingly more common) shared-
// header case. `--link` already tolerates a function body that genuinely does turn up more than once (a
// shared, non-renamed `.c` helper #include'd from multiple mains) by keeping one definition and noting the
// others as ignored (lib/link/Link.cpp), so accepting `.c`-extension includes here is not a new risk.
static bool isSourceExtension(llvm::StringRef path) {
  if (getenv("HLIR_DEBUG_NO_SRC_EXT_FIX")) return false;
  llvm::StringRef ext = llvm::sys::path::extension(path);
  return ext == ".c" || ext == ".cc" || ext == ".cpp" || ext == ".cxx" || ext == ".C" || ext == ".CC";
}

// single-header-library carve-out (see MainMacroIfdefs above): is `eloc` inside a `simpleIfdefRegions` region
// whose controlling macro is in `m.mainFileDefinedMacros`? A new, independent allow path alongside
// `isSourceExtension` -- it does not change `isSourceExtension` itself or the behaviour of any `.c`/`.cc`/
// `.cpp`/`.cxx` include.
static bool inMainGatedIfdefRegion(const SourceManager &sm, SourceLocation eloc, const Module &m) {
  if (!eloc.isValid() || !eloc.isFileID()) return false;
  FileID fid = sm.getFileID(eloc);
  unsigned off = sm.getFileOffset(eloc);
  for (const auto &r : m.simpleIfdefRegions) {
    if (r.file != fid || off < r.beginOffset || off >= r.endOffset) continue;
    if (m.mainFileDefinedMacros.count(r.macro)) return true;
  }
  return false;
}

// the functions with a body (C and C++: free functions, methods, constructors, functions in namespaces and `extern "C"` blocks);
// template patterns and their instantiations are reached through the calls that use them
class FnCollector : public RecursiveASTVisitor<FnCollector> {
 public:
  FnCollector(const SourceManager &sm, std::vector<const FunctionDecl *> &out, bool onlyMain = true, const Module *mod = nullptr)
      : sm_(sm), out_(out), onlyMain_(onlyMain), mod_(mod) {}
  bool VisitFunctionDecl(FunctionDecl *fd) {
    if (fd->isDependentContext() || fd->isInvalidDecl() || !fd->doesThisDeclarationHaveABody() || fd->isTemplateInstantiation()) return true;
    SourceLocation eloc = sm_.getExpansionLoc(fd->getLocation());
    // A C-linkage body in a SYSTEM header is libc, and libc's behaviour comes from the model database --
    // never from the header. This is the same rule useFunction() applies to callees, and it has to be
    // here too because inMainGatedIfdefRegion() below would otherwise let such a body in through the
    // single-header-library door: that feature exists so `#define STB_IMAGE_IMPLEMENTATION` before a
    // PROJECT header lowers the implementation, but the test "a macro the main file defined gates this
    // region" is also true of `#define __USE_EXTERN_INLINES` (or _GNU_SOURCE, or _XOPEN_SOURCE) before
    // <ctype.h>, and glibc's `__extern_inline tolower` then collides with models/libc.core's @tolower.
    // The result is a link failure, "redefinition of function @tolower", at the last step of scan setup.
    // DESIGN.md Sec.22.453; the C-linkage half keeps C++'s header-defined standard library lowerable.
    // Same rule as bodyIsLibcsToModel(): C linkage, OR an unmangled name, because glibc's <string.h>
    // puts memchr/strchr/strpbrk/strrchr/strstr in `extern "C++"` overload pairs that carry
    // __asm__("strchr") and have bodies from -O1 up. Both overloads collapse onto one symbol, so letting
    // them through produced `@strchr` twice and a "redefinition of function @strchr" link failure on the
    // first C++ target (DESIGN.md Sec.22.459).
    if (sm_.isInSystemHeader(eloc) && (fd->isExternC() || fnName(fd).rfind("_Z", 0) != 0)) return true;
    if (onlyMain_ && !sm_.isInMainFile(eloc) && !isSourceExtension(sm_.getFilename(eloc)) &&
        !(mod_ && inMainGatedIfdefRegion(sm_, eloc, *mod_)))
      return true;
    out_.push_back(fd);
    return true;
  }
  bool shouldVisitTemplateInstantiations() const { return false; }

 private:
  const SourceManager &sm_;
  std::vector<const FunctionDecl *> &out_;
  bool onlyMain_;
  const Module *mod_;
};

class Consumer : public ASTConsumer {
 public:
  explicit Consumer(Module &m) : mod_(m) {}
  void HandleTranslationUnit(ASTContext &ctx) override {
    SourceManager &sm = ctx.getSourceManager();
    if (!mod_.recover && ctx.getDiagnostics().hasErrorOccurred()) return;  // Clang's own errors are reported; the AST is unreliable
    std::vector<const FunctionDecl *> fns;
    {
      FnCollector fc(sm, fns, true, &mod_);
      fc.TraverseDecl(ctx.getTranslationUnitDecl());
    }
    for (auto *fd : fns) mod_.defined.insert(fnName(fd));
    if (isCxxCtx(ctx)) {
      ClassCollector cc(mod_.classes);
      cc.TraverseDecl(ctx.getTranslationUnitDecl());
    }
    {  // functions with internal linkage (also the ones from headers) must not clash across units; a name kept external
      // on purpose (opt.externalFunctions / `// hlir-extern:`, so a ModelDB body binds to it under its plain name) is
      // never this unit's own symbol for that purpose, even when its real declaration has internal (e.g. `static
      // __always_inline`) linkage: every unit that includes the header redeclares it the same way, so without this
      // exclusion the --link clash-rename (lib/link/Link.cpp) renames every call to it to a per-unit `.uN` suffix that
      // the model's un-suffixed definition no longer matches, silently turning it into an undefined/opaque call (see
      // docs/DESIGN.md's "C support test round 6" write-up: `copy_from_user`'s own `static __always_inline` wrapper in
      // <linux/uaccess.h> hit exactly this with --link, producing a spurious uninit_read).
      std::vector<const FunctionDecl *> every;
      FnCollector ec(sm, every, false);
      ec.TraverseDecl(ctx.getTranslationUnitDecl());
      for (auto *fd : every)
        if (!fd->isExternallyVisible() && !mod_.externals.count(fnName(fd))) mod_.internalTokens.insert(fnName(fd));
    }
    AddrTakenFinder finder(mod_, sm);
    finder.TraverseDecl(ctx.getTranslationUnitDecl());
    for (auto *fd : mod_.addrTaken) {
      bool k = true;
      std::string sg = sigOfDecl(ctx, fd, k);
      if (k && !fd->isVariadic()) {
        mod_.addrTakenSigs.push_back({fnName(fd), sg});
        std::string ck = cTypeKey(fd->getType());
        if (!ck.empty() && !mod_.addrEscaped.count(fd->getCanonicalDecl())) mod_.addrTakenCTypes[fnName(fd)] = ck;
      }
    }
    // SORTED, because `mod_.addrTaken` is a std::set of AST POINTERS and this list is an OUTPUT
    // (DESIGN.md §22.443). hlir::link emits the indirect-call dispatcher by walking it, so the order of
    // `core.ptr_cmp` tests inside `@__hlir_indirect.*` was the order clang happened to allocate those Decls
    // -- which moves with the address space. Two runs of the SAME hlir-scan command produced linked modules
    // that differed only in that order, and the analysis that followed differed with them: the same single
    // deterministic first run took 15185 steps or 15188. The non-link path at the `icall` lowering above has
    // sorted its candidates by name all along; this one never did.
    std::sort(mod_.addrTakenSigs.begin(), mod_.addrTakenSigs.end());
    // address-taken functions must be declared even if no direct call mentions them
    for (auto *fd : mod_.addrTaken) {
      std::string name = fnName(fd);
      if (mod_.defined.count(name) || mod_.declares.count(name)) continue;
      bool ok = true;
      std::string sg = sigOfDecl(ctx, fd, ok);
      if (ok) mod_.declares[name] = "core.declare @" + name + sg;
    }
    // facts for the scanner (also available when a function cannot be lowered)
    VoidHints hints;
    hints.linkMode = mod_.link;
    {
      std::set<const void *> conflicts;
      PtrHintFinder vf(hints, conflicts, sm);
      vf.TraverseDecl(ctx.getTranslationUnitDecl());
      vf.propagate();
      for (auto it = hints.fields.begin(); it != hints.fields.end();) it = conflicts.count(it->first) ? hints.fields.erase(it) : std::next(it);
      for (auto it = hints.params.begin(); it != hints.params.end();) it = conflicts.count(it->first) ? hints.params.erase(it) : std::next(it);
    }
    if (!mod_.userDataGetters.empty()) {
      UserDataFinder uf(mod_.userDataGetters, sm);
      uf.TraverseDecl(ctx.getTranslationUnitDecl());
      uf.propagate();
      for (auto &kv : uf.found)
        if (!uf.conflicts.count(kv.first)) hints.userData[kv.first] = kv.second;
      hints.freedTypes = uf.freedTypes;
    }
    {  // fields used by the lowered code: the main-file functions and, transitively, the functions with a body they call
      std::set<const FunctionDecl *> seen;
      std::vector<const FunctionDecl *> work(fns.begin(), fns.end());
      while (!work.empty() && seen.size() < 4000) {
        const FunctionDecl *f = work.back();
        work.pop_back();
        if (!seen.insert(f).second || !f->getBody()) continue;
        std::vector<const FunctionDecl *> callees;
        FieldUseFinder ff(ctx, hints.used, hints.nullTested, callees);
        ff.TraverseStmt(const_cast<Stmt *>(f->getBody()));
        for (auto *c : callees) work.push_back(c);
      }
      hints.restrictToUsed = true;
      // --link: export this same (already-bounded, already-computed) set as the whole-program field-use contribution of
      // this unit -- no extra AST walk needed. This unit's own `fns` are exactly the functions defined here, so a field
      // only ever touched through *this* file's bodies (e.g. field_use_body.c's touch_bug for a field no caller-side file
      // mentions) is still captured: when hlir-scan unions every unit's set, it is just as reachable as if one giant
      // whole-program AST had been walked, at no extra parsing cost.
      {  // bounds the program asserts about its own members (see AssertBoundFinder), keyed by TYPE, not by use site
        AssertBoundFinder af(ctx, mod_.fieldAsserts);
        af.TraverseDecl(ctx.getTranslationUnitDecl());
      }
      if (hints.linkMode) {
        for (auto *f : hints.used) {
          std::string k = fieldKey(sm, f);
          if (!k.empty()) mod_.fieldUses.insert(std::move(k));
        }
        // same union, for the null-test set: the unit that declares a `struct FT_StreamRec *` parameter is almost
        // never the unit that sets `stream->read = NULL` and branches on it, so a per-unit answer is useless here.
        for (auto *f : hints.nullTested) {
          std::string k = fieldKey(sm, f);
          if (!k.empty()) mod_.fieldNullTests.insert(std::move(k));
        }
      }
    }
    FreeUseFinder freeFinder;
    for (auto *fd : fns)
      if (fd->getBody()) freeFinder.TraverseStmt(const_cast<Stmt *>(fd->getBody()));
    freeFinder.propagate();
    const std::set<const ParmVarDecl *> &freedParams = freeFinder.freed;
    std::map<std::string, unsigned> callers;
    std::vector<std::vector<std::string>> callees(fns.size());
    for (size_t i = 0; i < fns.size(); ++i) {
      std::string self = fnName(fns[i]);
      CallGraphVisitor v(callers, callees[i], self, mod_.defined);
      v.TraverseStmt(const_cast<Stmt *>(fns[i]->getBody()));
    }
    for (size_t i = 0; i < fns.size(); ++i) {
      const FunctionDecl *fd = fns[i];
      FunctionInfo fi;
      fi.name = fnName(fd);
      fi.display = fnDisplay(fd);
      PresumedLoc pl = sm.getPresumedLoc(sm.getExpansionLoc(fd->getLocation()));
      fi.file = mod_.file;
      fi.line = pl.isValid() ? pl.getLine() : 0;
      fi.isStatic = fd->getStorageClass() == SC_Static;
      fi.addrTaken = mod_.addrTaken.count(fd->getCanonicalDecl()) != 0;
      if (!mod_.addrEscaped.count(fd->getCanonicalDecl())) fi.cType = cTypeKey(fd->getType());
      fi.callers = callers[fi.name];
      fi.callees = callees[i];
      fi.returnType = fd->getReturnType().getAsString();
      if (!fd->isVariadic()) { bool sok = true; std::string sg = sigOfDecl(ctx, fd, sok); if (sok) fi.sig = sg; }
      if (hasThis(fd)) fi.params.push_back(paramInfoOfType(ctx, cast<CXXMethodDecl>(fd)->getThisType(), "this", nullptr, 0, hints));
      for (unsigned k = 0; k < fd->getNumParams(); ++k) {
        const ParmVarDecl *pd = fd->getParamDecl(k);
        if (pd->isInvalidDecl()) { ParamInfo bad; bad.name = pd->getName().str(); bad.kind = "other"; bad.cType = "<invalid>"; fi.params.push_back(bad); }
        else {
          fi.params.push_back(paramInfo(ctx, pd, k, hints));
          fi.params.back().freed = freedParams.count(pd) != 0;
        }
      }
      mod_.infos.push_back(std::move(fi));
    }
    if (mod_.recover && ctx.getDiagnostics().hasErrorOccurred()) {
      StubUseFinder sf(ctx, mod_);
      for (auto *fd : fns)
        if (fd->getBody()) sf.TraverseDecl(const_cast<FunctionDecl *>(fd));
    }
    mod_.work = fns;
    // Functions (reached from the main file) and init functions of globals reach each other: a global initialiser can take the
    // address of a static function that nothing else mentions, a function body can reach a new global. Drain both queues.
    size_t wi = 0, ii = 0;
    auto lowerOne = [&](const FunctionDecl *fd) {
      std::string name = fnName(fd);
      if (mod_.externals.count(name)) {  // asked to stay a declaration: a model supplies the behaviour
        mod_.failedFns.insert(name);
        mod_.failedWhy[name] = "kept as a declaration on request (a model supplies its behaviour)";
        return;
      }
      if (mod_.recover) {  // a function that still has compile errors is only declared
        ErrorFinder ef;
        ef.TraverseDecl(const_cast<FunctionDecl *>(fd));
        if (ef.found || fd->isInvalidDecl()) {
          unsigned b = sm.getPresumedLoc(sm.getExpansionLoc(fd->getBeginLoc())).getLine(), e = sm.getPresumedLoc(sm.getExpansionLoc(fd->getEndLoc())).getLine();
          std::string why = "clang reported errors in this function";
          for (auto &d : mod_.clangErrors)
            if (d.file == mod_.file && d.line >= b && d.line <= e) { why += ": " + d.text + " (line " + std::to_string(d.line) + ")"; break; }
          mod_.failedFns.insert(name);
          mod_.failedWhy[name] = why;
          return;
        }
      }
      guarded([&] { FnGen(ctx, mod_).run(fd); }, name);
    };
    size_t bi = 0;
    auto lowerBase = [&](const FunctionDecl *fd) {
      std::string name = baseVariantName(fd);
      if (mod_.externals.count(fnName(fd)) || mod_.failedFns.count(fnName(fd))) return;
      guarded([&] { FnGen(ctx, mod_).run(fd, true); }, name);
    };
    auto drain = [&] {
      auto pendingVcalls = [&] {
        for (auto &kv : mod_.vcalls) if (!mod_.vcallDone.count(kv.first)) return true;
        for (auto &kv : mod_.dynCasts) if (!mod_.dynCastDone.count(kv.first)) return true;
        for (auto &kv : mod_.typeIds) if (!mod_.typeIdDone.count(kv.first)) return true;
        return false;
      };
      while (wi < mod_.work.size() || bi < mod_.baseWork.size() || ii < mod_.initQueue.size() || pendingVcalls()) {
        for (auto it = mod_.vcalls.begin(); it != mod_.vcalls.end(); ++it)
          if (mod_.vcallDone.insert(it->first).second) mod_.funcs << vcallDispatcher(ctx, mod_, it->first, it->second);
        for (auto it = mod_.dynCasts.begin(); it != mod_.dynCasts.end(); ++it)
          if (mod_.dynCastDone.insert(it->first).second) mod_.funcs << dynCastDispatcher(ctx, mod_, it->first, it->second);
        for (auto it = mod_.typeIds.begin(); it != mod_.typeIds.end(); ++it)
          if (mod_.typeIdDone.insert(it->first).second) mod_.funcs << typeIdDispatcher(ctx, mod_, it->first, it->second);
        while (wi < mod_.work.size()) lowerOne(mod_.work[wi++]);
        while (bi < mod_.baseWork.size()) lowerBase(mod_.baseWork[bi++]);
        while (ii < mod_.initQueue.size()) {
          const VarDecl *vd = mod_.initQueue[ii++];
          guarded([&] { FnGen(ctx, mod_).runGlobalInit(vd); }, "__hlir_init." + globalName(mod_, vd));
        }
      }
    };
    drain();
    if (mod_.link)  // other units refer to our exported initialised globals through their init functions, used here or not
      for (auto *d : ctx.getTranslationUnitDecl()->decls())
        if (auto *vd = dyn_cast<VarDecl>(d)) {
          // Same X-macro / `#include`d-`.c`-file gap as FnCollector's (see isSourceExtension above): a global whose
          // *definition* with its real initializer lives in a `.c` file `#include`d by this main file (e.g. freetype's
          // `ttdriver.c`, pulled into `truetype.c`, defining `tt_driver_class`) must still be treated as belonging to
          // this translation unit, or a `--link` consumer in another unit (an `extern` declaration of the same global,
          // e.g. freetype's `ftinit.c`) gets no real initializer at all: the global stays all-zero at runtime.
          SourceLocation eloc = sm.getExpansionLoc(vd->getLocation());
          if (vd->isThisDeclarationADefinition() == VarDecl::Definition && vd->isExternallyVisible() &&
              (sm.isInMainFile(eloc) || isSourceExtension(sm.getFilename(eloc))) && needsInit(ctx, vd))
            if (mod_.initSeen.insert(vd->getDefinition()).second) mod_.initQueue.push_back(vd->getDefinition());
        }
    drain();  // the exported globals queued above (link mode), and whatever their initialisers reach

    // ---- ELF constructors (`__attribute__((constructor))`, i.e. llvm.global_ctors).
    //
    // In a real process these have ALREADY RUN before any API of the library is called: the loader runs them at
    // load time. A scan that starts from the static initialisers is therefore not making a cautious assumption,
    // it is making a FALSE one -- libssh's `libssh_constructor` (src/init.c:59) calls `_ssh_init(1)`, so every
    // branch on `_ssh_initialized` is decided the wrong way and the body behind it is never entered. Measured on
    // a minimal reproducer: 4/7 blocks and one branch in G1's `global_init` bucket, against 6/7 and none once
    // the constructor runs (DESIGN.md Sec.22.488).
    //
    // The IR has nowhere to put an attribute, so the fact is written down as a FUNCTION: one wrapper per
    // constructor, named `__hlir_ctor.<priority>.<name>`. Sorting those names is the loader's order (lower
    // priority first), including across translation units in --link mode, and hlir-scan prepends them to the
    // entry's `init:` list -- BEFORE any --init-fn the user named, because the loader runs before main does.
    // A wrapper is also visible: it shows up in --list and in the report's `init_functions`, and an automatic
    // behaviour nobody can see is worse than no automatic behaviour.
    {
      std::vector<std::pair<unsigned, std::string>> ctors;
      for (auto *d : ctx.getTranslationUnitDecl()->decls()) {
        auto *fd = dyn_cast<FunctionDecl>(d);
        if (!fd || !fd->hasAttr<ConstructorAttr>()) continue;
        const FunctionDecl *def = fd->getDefinition();
        if (!def || !def->param_empty()) continue;  // a constructor takes no arguments; anything else is not one
        SourceLocation eloc = sm.getExpansionLoc(def->getLocation());
        if (!(sm.isInMainFile(eloc) || isSourceExtension(sm.getFilename(eloc)))) continue;
        if (mod_.defined.insert(fnName(def)).second) mod_.work.push_back(def);
        unsigned prio = def->getAttr<ConstructorAttr>()->getPriority();
        ctors.push_back({prio, fnName(def)});
      }
      if (!ctors.empty()) {
        std::sort(ctors.begin(), ctors.end());
        drain();  // lower the constructor bodies just queued
        for (auto &c : ctors) {
          if (mod_.failedFns.count(c.second)) continue;  // its body did not lower: a wrapper calling it would be a lie
          char pri[16];
          std::snprintf(pri, sizeof pri, "%05u", c.first);
          std::string w = "__hlir_ctor." + std::string(pri) + "." + c.second;
          if (!mod_.ctorWrappers.insert(w).second) continue;
          mod_.funcs << "core.func @" << w << "() -> void {\n^entry:\n  core.call @" << c.second
                     << "()\n  core.return\n}\n";
          // ...and as a FunctionInfo, so the driver can SEE it: --list shows it, and hlir-scan picks the
          // `__hlir_ctor.` prefix out of this list to build the init order. It takes no parameters, so entry
          // discovery passes over it unless someone asks for no-argument entries explicitly.
          FunctionInfo wi;
          wi.name = w;
          wi.display = w + " (ELF constructor wrapper)";
          wi.file = mod_.file;
          wi.returnType = "void";
          wi.sig = "() -> void";
          wi.isStatic = true;
          mod_.infos.push_back(std::move(wi));
        }
      }
    }

    for (auto *fd : mod_.work)
      if (mod_.failedFns.count(fnName(fd))) {  // a function that could not be lowered stays declared
        bool ok = true;
        std::string sg = sigOfDecl(ctx, fd, ok);
        if (ok) mod_.declares[fnName(fd)] = "core.declare @" + fnName(fd) + sg;
      }
    for (auto *vd : mod_.initQueue) {  // a global whose initializer could not be lowered: its lazy-init thunk stays declared (already-called sites would otherwise reference an undefined function)
      std::string name = "__hlir_init." + globalName(mod_, vd);
      if (mod_.failedFns.count(name)) mod_.declares[name] = "core.declare @" + name + "() -> void";
    }
    for (unsigned i = 0; i < mod_.strs.size(); ++i) mod_.funcs << initFunctionForString(i, mod_.strs[i]);
  }

 private:
  template <class F> void guarded(F f, const std::string &fn = "") {
    try {
      f();
    } catch (std::runtime_error &) {
      // error already recorded; keep going to report every unsupported function in one run
      if (!fn.empty()) {
        mod_.failedFns.insert(fn);
        if (!mod_.errors.empty()) mod_.failedWhy[fn] = mod_.errors.back();
      }
    }
  }
  Module &mod_;
};

class Action : public ASTFrontendAction {
 public:
  explicit Action(Module &m) : mod_(m) {}
  bool BeginSourceFileAction(CompilerInstance &CI) override {
    // unconditional (not just recover mode): single-header libraries routinely compile clean, and this only ever
    // records data FnCollector may *add* to its allow-list, never removes anything.
    CI.getPreprocessor().addPPCallbacks(std::make_unique<MainMacroIfdefs>(mod_, CI.getSourceManager(), CI.getLangOpts()));
    if (mod_.recover) {
      CI.getPreprocessor().addPPCallbacks(std::make_unique<MissingHeaders>(mod_));
      CI.getDiagnostics().setClient(new CapturingDiags(mod_), /*ShouldOwnClient=*/true);
    }
    return true;
  }
  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &, StringRef) override { return std::make_unique<Consumer>(mod_); }

 private:
  Module &mod_;
};

}  // namespace


namespace {

struct StubField { std::string name, type; int rank = 0; };

// text of the stub struct definitions: forward declarations first, then each definition after the structs it contains by value
std::string stubStructBlock(const std::map<std::string, std::vector<StubField>> &stubs, const std::vector<std::string> &consts, std::vector<std::string> &summary) {
  std::set<std::string> names;
  for (auto &kv : stubs) {
    names.insert(kv.first);
    for (auto &f : kv.second) {
      auto k = f.type.find("struct __hlir_stub_");
      if (k != std::string::npos) {
        std::string n = f.type.substr(k + 7);
        while (!n.empty() && (n.back() == ' ' || n.back() == '*')) n.pop_back();
        names.insert(n);
      }
    }
  }
  std::string out = "/* hlirgen: structs whose definition was not found, laid out from the member accesses in this file */\n";
  // identifiers that no header declares (macros from a missing header): distinct integer constants
  for (size_t i = 0; i < consts.size(); ++i) out += "enum { " + consts[i] + " = " + std::to_string(1000 + i) + " };\n";
  for (auto &n : names) out += "struct " + n + ";\n";
  std::set<std::string> done, visiting;
  std::function<void(const std::string &)> emit = [&](const std::string &n) {
    if (done.count(n) || !visiting.insert(n).second) return;
    auto it = stubs.find(n);
    if (it != stubs.end())
      for (auto &f : it->second)  // by-value members need their struct first
        if (f.type.rfind("struct __hlir_stub_", 0) == 0 && f.type.back() != '*') emit(f.type.substr(7));
    std::string def = "struct " + n + " { ";
    std::string sum = "struct " + n + " { ";
    if (it == stubs.end() || it->second.empty()) { def += "char __hlir_pad; "; sum += "/* no member seen */ "; }
    else
      for (auto &f : it->second) {
        def += f.type + " " + f.name + "; ";
        sum += f.type + " " + f.name + ";" + (f.rank <= 1 ? " /* guessed */" : "") + " ";
      }
    out += def + "};\n";
    summary.push_back(sum + "}");
    done.insert(n);
  };
  for (auto &n : names) emit(n);
  return out;
}

// inserts `block` after the last #include of the source, restoring the line numbering afterwards
std::string insertAfterIncludes(const std::string &src, const std::string &block, const std::string &file) {
  std::vector<std::string> lines;
  std::istringstream in(src);
  std::string l;
  while (std::getline(in, l)) lines.push_back(l);
  static const std::regex inc("^\\s*#\\s*include\\b");
  size_t last = 0;
  bool any = false;
  for (size_t i = 0; i < lines.size(); ++i)
    if (std::regex_search(lines[i], inc)) { last = i; any = true; }
  std::ostringstream out;
  size_t at = any ? last + 1 : 0;
  for (size_t i = 0; i < lines.size(); ++i) {
    if (i == at) out << block << "#line " << i + 1 << " \"" << file << "\"\n";
    out << lines[i] << "\n";
  }
  if (at >= lines.size()) out << block;
  return out.str();
}

// stub typedef for a type name that no (found) header declares
std::string stubTypedef(const std::string &n) {
  static const std::regex u("^(u|U|__u|NvU|uint)(8|16|32|64)(_t)?$"), sg("^(s|S|__s|NvS|int)(8|16|32|64)(_t)?$");
  std::smatch m;
  auto ty = [](const std::string &bits, bool isSigned) {
    std::string t = bits == "8" ? "char" : bits == "16" ? "short" : bits == "32" ? "int" : "long long";
    return isSigned ? (bits == "8" ? "signed char" : t) : "unsigned " + t;
  };
  if (std::regex_match(n, m, u)) return "typedef " + ty(m[2], false) + " " + n + ";\n";
  if (std::regex_match(n, m, sg)) return "typedef " + ty(m[2], true) + " " + n + ";\n";
  return "typedef struct __hlir_opaque_" + n + " " + n + ";\n";
}

}  // namespace

static bool isCxxSource(const std::string &file, const std::string &language) {
  if (language == "c++" || language == "cxx" || language == "cpp") return true;
  if (language == "c") return false;
  size_t dot = file.rfind('.');
  if (dot == std::string::npos) return false;
  std::string ext = file.substr(dot + 1);
  return ext == "cc" || ext == "cpp" || ext == "cxx" || ext == "c++" || ext == "C" || ext == "cp" || ext == "CPP";
}

LowerResult lowerC(const std::string &source, const std::string &fileName, const LowerOptions &opt) {
  std::set<std::string> assumed;
  std::string prelude;
  std::map<std::string, std::vector<StubField>> stubs;
  std::vector<std::string> stubSummary, consts;
  std::set<std::string> constSet;
  LowerResult res;
  for (int round = 0;; ++round) {
    Module mod;
    mod.file = fileName;
    mod.recover = opt.recover;
    mod.wrapSigned = opt.wrapSignedOverflow;
    mod.lenientPtrArith = opt.lenientPointerArith;
    mod.spawnCallbacks = opt.spawnCallbacks;
    mod.externals.insert(opt.externalFunctions.begin(), opt.externalFunctions.end());
    mod.link = opt.link;
    mod.userDataGetters.insert(opt.userDataGetters.begin(), opt.userDataGetters.end());
    bool userStd = false;
    for (auto &a : opt.clangArgs) userStd |= a.rfind("-std=", 0) == 0;
    std::vector<std::string> args;
    if (isCxxSource(fileName, opt.language)) {
      if (!userStd) args.push_back("-std=gnu++17");
      args.push_back("-x");
      args.push_back("c++");
    } else if (!userStd) args.push_back("-std=gnu11");
    for (const char *a : {"-fsyntax-only", "-w", "-resource-dir"}) args.push_back(a);
    args.push_back(HLIR_CLANG_RESOURCE_DIR);
    if (opt.recover) {
      args.push_back("-Wno-error=implicit-function-declaration");
      args.push_back("-Wno-implicit-int");
      args.push_back("-ferror-limit=0");
      args.push_back("-fno-caret-diagnostics");
    }
    for (auto &a : opt.clangArgs) args.push_back(a);
    // -nostdinc drops Clang's own headers too (stdarg.h, stddef.h, ...); projects that use it point at gcc's copy instead
    if (std::find(opt.clangArgs.begin(), opt.clangArgs.end(), "-nostdinc") != opt.clangArgs.end()) {
      args.push_back("-isystem");
      args.push_back(std::string(HLIR_CLANG_RESOURCE_DIR) + "/include");
    }
    std::string body = source;
    stubSummary.clear();
    if (!stubs.empty() || !consts.empty()) body = insertAfterIncludes(source, stubStructBlock(stubs, consts, stubSummary), fileName);
    // libstdc++ marks several `basic_string<char>`/`basic_string<wchar_t>` member functions (e.g. find/rfind/compare,
    // out-of-line in <bits/basic_string.tcc>) `extern template`: Sema sees the declaration but, since a real definition
    // is assumed to live in the never-linked libstdc++.so, leaves no body in this TU's AST ("explicit instantiation
    // declaration"). This project's one-and-only policy for a reachable function is "lower its real body" (see
    // FEATURE_STATUS/"精度与健全性"); with no body and no ModelDB entry, such a call instead falls back to the
    // generic opaque-external result (hlir-scan's default `--opaque-externals`: an unconstrained, untainted value) -
    // losing `find`'s own invariant (result < size() or == npos) and corrupting whatever the caller does with it
    // (e.g. a `substr(0, val)` with a `val` that can exceed `size()`, raising a spurious `std::out_of_range`). Flip
    // libstdc++'s own `_GLIBCXX_EXTERN_TEMPLATE` escape hatch (normally only reachable via `-D_GLIBCXX_ASSERTIONS`,
    // which also turns on unrelated `__glibcxx_assert` bounds checks we don't want) to make `basic_string` -- and
    // only `basic_string` -- an ordinary implicitly-instantiated template, so these members get their real,
    // analyzable bodies like every other STL member already does. `__has_include` makes this a no-op on any
    // non-libstdc++ standard library (libc++, MSVC STL: no `<bits/c++config.h>` to find).
    static const char *const cxxExternTemplateFix =
        "#if defined(__cplusplus) && __has_include(<bits/c++config.h>)\n"
        "#include <bits/c++config.h>\n"
        "#undef _GLIBCXX_EXTERN_TEMPLATE\n"
        "#define _GLIBCXX_EXTERN_TEMPLATE -1\n"
        "#endif\n";
    std::string cxxPrelude = isCxxSource(fileName, opt.language) ? cxxExternTemplateFix : "";
    std::string text = cxxPrelude + prelude + "#line 1 \"" + fileName + "\"\n" + body;
    bool ok = tooling::runToolOnCodeWithArgs(std::make_unique<Action>(mod), text, args, fileName);
    // recover: another round declares the type names / struct members that were unknown in this one
    if (opt.recover && round < 8) {
      bool again = false;
      std::string more;
      if (round < 3)
        for (auto &t : mod.unknownTypes)
          if (assumed.insert(t).second) more += stubTypedef(t);
      if (!more.empty()) { prelude += more; again = true; }
      if (opt.inferStructs)
        for (auto &id : mod.unknownIdents)
          if (constSet.insert(id).second) { consts.push_back(id); again = true; }
      if (opt.inferStructs)
        for (auto &u : mod.stubUses) {
          auto &fields = stubs[u.structName];
          auto it = std::find_if(fields.begin(), fields.end(), [&](const StubField &f) { return f.name == u.member; });
          if (it == fields.end()) { fields.push_back({u.member, u.type, u.rank}); again = true; }
          else if (u.rank > it->rank) { it->type = u.type; it->rank = u.rank; again = true; }  // a better-typed use wins
        }
      if (again) continue;
    }
    std::ostringstream diag;
    for (auto &e : mod.errors) diag << e << "\n";
    if (opt.recover) {
      unsigned shown = 0;
      for (auto &d : mod.clangErrors)
        if (d.file == fileName && shown++ < 20) diag << "clang: " << d.file << ":" << d.line << ": " << d.text << "\n";
      if (shown < mod.clangErrors.size()) diag << "clang: ... " << mod.clangErrors.size() - shown << " more error(s)\n";
    }
    res.diagnostics = diag.str();
    if (!ok && mod.errors.empty() && !opt.recover) res.diagnostics = "clang reported errors (see above)\n";
    res.ok = opt.recover ? !mod.infos.empty() || ok : ok && (opt.partial || mod.errors.empty());
    for (auto &f : mod.infos) {
      f.lowered = !mod.failedFns.count(f.name);
      if (!f.lowered) f.skipReason = mod.failedWhy.count(f.name) ? mod.failedWhy[f.name] : "unsupported construct";
    }
    res.functions = std::move(mod.infos);
    res.fieldUses = std::move(mod.fieldUses);
    res.fieldNullTests = std::move(mod.fieldNullTests);
    res.fieldAsserts = std::move(mod.fieldAsserts);
    res.containerOfWaived = mod.containerOfWaived;
    res.spawnCallbacksEmitted = mod.spawnCallbacksEmitted;
    res.containerOfFirstSite = mod.containerOfFirstSite;
    res.internalTokens.assign(mod.internalTokens.begin(), mod.internalTokens.end());
    res.addrTakenFunctions = mod.addrTakenSigs;
    res.addrTakenCTypes = mod.addrTakenCTypes;
    res.vtableBindings = std::move(mod.vtableBindings);
    res.vtableInstances = std::move(mod.vtableInstances);
    res.indirectCallCTypes = mod.indirectCallCTypes;
    res.dlsymNames = mod.dlsymNames;
    res.missingHeaders.assign(mod.missingHeaders.begin(), mod.missingHeaders.end());
    res.assumedTypes.assign(assumed.begin(), assumed.end());
    res.inferredStructs = stubSummary;
    for (auto &c : consts) res.inferredStructs.push_back("enum { " + c + " } /* unknown constant: a distinct integer, the real value is in a missing header */");
    if (res.ok) {
      std::ostringstream os;
      os << "// generated by hlirgen from " << fileName << "\n";
      for (auto &d : mod.declares) os << d.second << "\n";
      os << mod.funcs.str();
      res.core = os.str();
    }
    return res;
  }
}

}  // namespace hlir::frontend

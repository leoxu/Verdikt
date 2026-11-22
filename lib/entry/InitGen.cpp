#include <algorithm>
#include <cstdlib>
#include <functional>
#include <tuple>
#include <utility>

#include "llvm/Demangle/Demangle.h"

#include "Relations.h"
#include "hlir/entry/InitPlan.h"

namespace hlir::entry {

using smt::Kind;
using smt::TermRef;

namespace {

std::string at(const std::string &file, unsigned line) { return "@" + file + ":" + std::to_string(line); }

// A `getFunctionXxxName`-style call out of ItaniumPartialDemangler: NUL-terminated, malloc'd. "" on failure.
std::string demangled(char *(llvm::ItaniumPartialDemangler::*get)(char *, size_t *) const,
                       const llvm::ItaniumPartialDemangler &pd) {
  size_t n = 0;
  char *buf = (pd.*get)(nullptr, &n);
  if (!buf) return "";
  std::string s(buf);
  std::free(buf);
  return s;
}

// The fully qualified name of the class/namespace context a mangled Itanium symbol was declared in ("ns::Outer::Class"
// for "ns::Outer::Class::method"); "" if `mangled` does not demangle as a C++ function. Whether `mangled` actually
// *is* a non-static member function is established separately, from the core IR (does it have a `this` parameter?) —
// `hasFunctionQualifiers()` only reports cv/ref-qualifiers, which most methods do not have, so it cannot be used as a
// general "is this a method" test.
std::string declContextOf(const std::string &mangled) {
  if (mangled.size() < 2 || mangled[0] != '_' || mangled[1] != 'Z') return "";
  llvm::ItaniumPartialDemangler pd;
  if (pd.partialDemangle(mangled.c_str())) return "";
  if (!pd.isFunction()) return "";
  return demangled(&llvm::ItaniumPartialDemangler::getFunctionDeclContextName, pd);
}

// A usable constructor (a body in `m`, `this` plus only scalar/bool extra parameters, the fewest among the class's
// such constructors) of the class `entryFn` is a method of; empty `.first` if none (not a method, no constructor with
// a body in `m`, every constructor takes a pointer/object parameter, or more than one candidate ties for fewest
// extra parameters).
std::pair<std::string, std::vector<Type *>> findDefaultCtor(const Module &m, const std::string &entryFn) {
  std::string cls = declContextOf(entryFn);
  if (cls.empty()) return {};
  std::vector<const Function *> candidates;
  for (auto &fp : m.functions) {
    const Function *g = fp.get();
    if (g->name == entryFn || g->isDeclaration() || g->paramTys.empty()) continue;
    if (g->name.size() < 2 || g->name[0] != '_' || g->name[1] != 'Z') continue;
    bool scalarOnly = true;
    for (size_t i = 1; i < g->paramTys.size(); ++i) scalarOnly &= !g->paramTys[i]->isPtr();
    if (!scalarOnly) continue;  // an extra parameter needs an object the way an entry's own parameters do; skip it
    llvm::ItaniumPartialDemangler pd;
    if (pd.partialDemangle(g->name.c_str())) continue;
    if (!pd.isFunction() || !pd.isCtorOrDtor()) continue;
    std::string base = demangled(&llvm::ItaniumPartialDemangler::getFunctionBaseName, pd);
    if (base.empty() || base[0] == '~') continue;  // a destructor, not a constructor
    if (demangled(&llvm::ItaniumPartialDemangler::getFunctionDeclContextName, pd) != cls) continue;
    candidates.push_back(g);
  }
  if (candidates.empty()) return {};
  const Function *best = *std::min_element(candidates.begin(), candidates.end(),
                                            [](const Function *a, const Function *b) { return a->paramTys.size() < b->paramTys.size(); });
  size_t ties = 0;
  for (auto *g : candidates) ties += g->paramTys.size() == best->paramTys.size();
  if (ties > 1) return {};  // more than one equally-minimal candidate for this class: ambiguous
  return {best->name, std::vector<Type *>(best->paramTys.begin() + 1, best->paramTys.end())};
}

}  // namespace

bool buildInitPlan(const Module &m, const EntryFile &file, const EntrySpec &spec, smt::TermManager &tm, InitPlan &out,
                   Diagnostics &diags) {
  out = InitPlan{};
  out.function = spec.function;
  out.label = spec.label;
  out.specFile = file.path;
  out.specLine = spec.line;
  out.ptrWidth = m.ctx.ptrWidth();
  const unsigned pw = out.ptrWidth;
  bool ok = true;
  auto err = [&](unsigned line, const std::string &msg) {
    ok = false;
    Loc l;
    l.file = file.path;
    l.line = line;
    l.col = 1;
    diags.error(msg, l);
  };

  const Function *f = m.findFunction(spec.function);
  if (!f) { err(spec.line, "entry function @" + spec.function + " does not exist in the module"); return false; }
  if (f->isDeclaration()) { err(spec.line, "entry function @" + spec.function + " has no body"); return false; }
  out.retTy = f->retTy;
  // C++: if the entry is a non-static member function (one of its parameters is the implicit `this`; it need not be
  // first, e.g. a hidden `sret` return-value pointer comes before it), find the class's default constructor so the
  // harness can run it on `this` instead of leaving it zeroed memory.
  bool hasThisParam = false;
  for (auto &a : f->entry()->args) hasThisParam |= a->name == "this";
  if (hasThisParam) std::tie(out.ctorFunction, out.ctorExtraParamTys) = findDefaultCtor(m, spec.function);
  // `init:` -- the project's own initialiser(s). Resolve them here, where the module is in hand, so a name that is
  // wrong fails loudly at plan time with the spec's own location instead of producing a harness that silently does
  // nothing. A wrong initialiser is worse than no initialiser (DESIGN.md §22.368 §2), so none of these is a warning.
  for (auto &n : file.init.functions) {
    const Function *pf = m.findFunction(n);
    if (!pf) {
      err(file.init.line, "init function @" + n + " does not exist in the module");
      continue;
    }
    if (pf->isDeclaration()) {
      err(file.init.line, "init function @" + n + " has no body in the link set: running it would do nothing, and a "
                          "prologue that silently does nothing is the failure this feature exists to remove");
      continue;
    }
    // Parameters are allowed now (DESIGN.md §22.368 §2): `main(int, char **)` is the initialiser of every server
    // and QNX resource manager. Only scalars and pointers, though -- a struct passed by value would need a layout
    // decision the harness has no basis for.
    bool badParam = false;
    for (auto &a : pf->entry()->args)
      if (!a->ty->isPtr() && !a->ty->width() && !a->ty->isBool()) badParam = true;
    if (badParam) {
      err(file.init.line, "init function @" + n + " takes a parameter that is neither a scalar nor a pointer: the "
                          "harness has no basis for synthesising it");
      continue;
    }
    if (n == spec.function) {
      err(file.init.line, "init function @" + n + " is also the entry being analysed: it would run twice");
      continue;
    }
    InitPlan::PrologueCall pc;
    pc.function = n;
    pc.retTy = pf->retTy;
    for (auto &a : pf->entry()->args) pc.paramTys.push_back(a->ty);
    out.prologue.push_back(std::move(pc));
  }
  for (auto &p : spec.params) {
    bool found = false;
    for (auto &a : f->entry()->args) found |= a->name == p.name;
    if (!found) err(p.line, "@" + spec.function + " has no parameter named '" + p.name + "'");
  }
  if (!ok) return false;

  auto named = [&](const std::string &n, unsigned line, const std::string &from = "") { return n + at(from.empty() ? file.path : from, line); };
  auto constraint = [&](const std::string &n, unsigned line, TermRef t) { out.constraints.push_back({named(n, line), t}); };
  // constraints a preconditions file overrode point at that file
  auto constraintAt = [&](const std::string &n, const ParamSpec *ps, unsigned line, TermRef t) {
    bool ov = !ps->overrideFile.empty();
    out.constraints.push_back({named(ov ? "pre." + n.substr(5) : n, ov ? ps->overrideLine : line, ov ? ps->overrideFile : ""), t});
  };
  auto bv = [&](unsigned w, int64_t v) { return tm.bvConst(llvm::APInt(w, static_cast<uint64_t>(v), true)); };

  // pointer fields of a pointee object of at least `parentLo` bytes (see FieldSpec)
  auto planBound = [&](const BoundSpec &b, PlannedBound &pb, const std::string &what, const std::string &pname) {
    unsigned w;
    bool sg;
    if (!lookupTypeName(b.type, w, sg)) { err(b.line, "'" + pname + "': unknown type name '" + b.type + "'"); return false; }
    pb.width = w;
    pb.isSigned = sg;
    pb.lo = b.lo;
    pb.hi = b.hi;
    pb.value = b.value;
    pb.enumValues = b.enumValues;
    auto fits = [&](int64_t v) {
      if (w >= 64) return true;
      if (sg) return v >= -(int64_t(1) << (w - 1)) && v < (int64_t(1) << (w - 1));
      return v >= 0 && v < (int64_t(1) << w);
    };
    bool unsignedMax = !sg && b.hi && *b.hi == -1;
    if ((b.lo && !fits(*b.lo)) || (b.hi && !fits(*b.hi) && !unsignedMax) || (b.value && !fits(*b.value))) { err(b.line, "'" + pname + "': the bound does not fit the type " + b.type); return false; }
    pb.name = named("pre." + pname + "." + what, b.line, b.file);
    return true;
  };
  std::function<void(const std::vector<FieldSpec> &, const std::string &, uint64_t, bool, bool, std::vector<PlannedField> &)> planFields =
      [&](const std::vector<FieldSpec> &specs, const std::string &parent, uint64_t parentLo, bool parentTainted, bool parentUnknown,
          std::vector<PlannedField> &outFields) {
        const uint64_t ptrBytes = pw / 8;
        for (auto &fs : specs) {
          if (fs.offset + ptrBytes > parentLo) { err(fs.line, "pointer field at offset " + std::to_string(fs.offset) + " does not fit in '" + parent + "' (at least " + std::to_string(parentLo) + " bytes)"); continue; }
          bool clash = false;
          for (auto &o : outFields) clash |= fs.offset < o.offset + ptrBytes && o.offset < fs.offset + ptrBytes;
          if (clash) { err(fs.line, "pointer field at offset " + std::to_string(fs.offset) + " overlaps another field of '" + parent + "'"); continue; }
          PlannedField pf;
          pf.name = parent + "." + std::to_string(fs.offset);
          pf.offset = fs.offset;
          pf.line = fs.line;
          pf.tainted = fs.taint == "pointee";
          pf.owned = fs.owned;
          pf.externallyMutable = fs.externallyMutable;
          // `content` (DESIGN.md §22.381). Stated explicitly, or INHERITED: what sits behind a pointer of an
          // object whose own bytes nobody knows is equally unknown. Tainted content wins -- attacker data is a
          // stronger statement than "invented", and the two cannot both be true of one byte.
          pf.unknownContent = !pf.tainted && (fs.content == "unknown" || (parentUnknown && fs.content != "zero"));
          if (fs.kind == "self") {
            if (fs.target >= parentLo) { err(fs.line, "self field target " + std::to_string(fs.target) + " is outside '" + parent + "' (at least " + std::to_string(parentLo) + " bytes)"); continue; }
            pf.kind = PlannedField::Self;
            pf.target = fs.target;
            outFields.push_back(std::move(pf));
            continue;
          }
          if (fs.kind == "funcptr") {
            pf.kind = PlannedField::FuncPtr;
            pf.targets = fs.targets;
            for (auto &t : pf.targets)
              if (!m.findFunction(t)) err(fs.line, "funcptr target @" + t + " does not exist in the module");
            if (pf.targets.size() > 1) {
              pf.selector = tm.bvVar("fn." + pf.name, 8);
              out.vars.push_back({pf.selector, ""});
              constraint("init." + pf.name + ".target", fs.line, tm.mkCmp(Kind::Ult, pf.selector, bv(8, static_cast<int64_t>(pf.targets.size()))));
              out.soft.push_back({"benign.fn." + pf.name, tm.mkEq(pf.selector, bv(8, 0)), 2});
            }
          } else if (fs.sameAllocOffset) {
            // same_alloc: find the sibling field (already planned -- it must appear earlier in this same `fields`
            // list) whose own declared `offset` this one names, and that owns a real allocation of its own. A view
            // of a view is rejected (nothing would own the memory); a sibling whose size comes from a length field
            // is fine, because the harness takes the sibling's emitted size VALUE, whichever way it was computed --
            // FreeType's `FT_StreamRec` pairs base/cursor/limit with its `size` field and still needs them to share
            // one object (DESIGN.md §22.354).
            size_t idx = static_cast<size_t>(-1);
            for (size_t i = 0; i < outFields.size(); ++i)
              if (outFields[i].offset == *fs.sameAllocOffset && outFields[i].kind == PlannedField::Buffer &&
                  !outFields[i].sameAllocIndex) { idx = i; break; }
            if (idx == static_cast<size_t>(-1)) {
              err(fs.line, "'" + pf.name + "': same_alloc.offset " + std::to_string(*fs.sameAllocOffset) +
                             " does not name an earlier buffer field of its own in the same 'fields' list");
              continue;
            }
            pf.sameAllocIndex = idx;
            // pos: inside -- a cursor that has already advanced an unknown distance. Its offset is derived from the
            // sibling's own size term, so `cursor <= limit` holds by construction however big that object turns out
            // to be; `promote` (not a taint label) makes the choice explorable without pretending it is input data.
            if (fs.sameAllocInside) {
              pf.sameAllocInside = true;
              pf.sameAllocOff = tm.bvVar("aoff." + pf.name, pw);
              out.vars.push_back({pf.sameAllocOff, "", /*promote=*/true});
              out.soft.push_back({"benign.aoff." + pf.name, tm.mkEq(pf.sameAllocOff, bv(pw, 0)), 2});
              // The "offset is within the sibling's object" part is clamped in the harness, not asserted here: the
              // sibling's size is not always a plan-time term (size.from_field reads it out of the parent's bytes
              // at run time), and a clamp works the same either way -- see HarnessGen.
            }
          } else if (fs.sizeFromOffset) {
            unsigned w; bool sg;
            if (!lookupTypeName(fs.sizeFromType, w, sg)) { err(fs.line, "'" + pf.name + "': size.from_field: unknown type '" + fs.sizeFromType + "'"); continue; }
            if (*fs.sizeFromOffset + w / 8 > parentLo) { err(fs.line, "'" + pf.name + "': size.from_field offset " + std::to_string(*fs.sizeFromOffset) + " does not fit in '" + parent + "' (at least " + std::to_string(parentLo) + " bytes)"); continue; }
            pf.sizeFromOffset = fs.sizeFromOffset;
            pf.sizeFromWidth = w;
            pf.sizeFromSigned = sg;
            pf.sizeFromElem = fs.sizeFromElem;
            pf.at = fs.at;
            // the real allocation size is only known once the harness runs (it's read from the sibling field's
            // bytes), so there is no static lower bound to check `at`/nested fields against -- Spec.cpp already
            // rejects `fields` alongside `size.from_field` for the same reason.
            if (fs.at != 0) { err(fs.line, "'" + pf.name + "': 'at' cannot be combined with size.from_field"); continue; }
          } else {
            uint64_t lo = fs.sizeMin ? *fs.sizeMin : 1, hi = fs.sizeMax ? *fs.sizeMax : file.defaults.maxObj;
            if (!pf.tainted) {
              uint64_t fixed = fs.sizeMin ? *fs.sizeMin : (fs.sizeMax ? *fs.sizeMax : std::min<uint64_t>(64, file.defaults.maxObj));
              lo = hi = fixed;
            }
            if (hi > file.defaults.maxObj) hi = file.defaults.maxObj;
            if (lo > hi) { err(fs.line, "'" + pf.name + "': size.min exceeds max_obj"); continue; }
            pf.sizeLo = lo;
            pf.sizeHi = hi;
            pf.at = fs.at;
            if (fs.at && fs.at >= lo) { err(fs.line, "'" + pf.name + "': at " + std::to_string(fs.at) + " is outside the object (at least " + std::to_string(lo) + " bytes)"); continue; }
            if (lo == hi) pf.size = bv(pw, static_cast<int64_t>(lo));
            else {
              pf.size = tm.bvVar("size." + pf.name, pw);
              out.vars.push_back({pf.size, ""});
              constraint("init." + pf.name + ".size[" + std::to_string(lo) + "," + std::to_string(hi) + "]", fs.line,
                         tm.mkAnd(tm.mkCmp(Kind::Ule, bv(pw, static_cast<int64_t>(lo)), pf.size), tm.mkCmp(Kind::Ule, pf.size, bv(pw, static_cast<int64_t>(hi)))));
              out.soft.push_back({"benign.size." + pf.name, tm.mkEq(pf.size, bv(pw, static_cast<int64_t>(std::min(std::max<uint64_t>(64, lo), hi)))), 2});
            }
            planFields(fs.fields, pf.name, lo, pf.tainted, pf.unknownContent, pf.fields);
            // preconditions on the integers inside this field's own object (FieldSpec::where). Only for a field
            // with a static lower bound on its size -- the same reason `at` and nested `fields` are: with
            // size.from_field or same_alloc there is nothing to check the offset against until the harness runs.
            for (auto &w : fs.where) {
              PlannedWhere pw2;
              if (!planBound(w, pw2, "where[" + std::to_string(w.offset) + "]", pf.name)) continue;
              pw2.offset = w.offset;
              if (w.offset + pw2.width / 8 > lo) {
                err(w.line, "'" + pf.name + "': where offset " + std::to_string(w.offset) + " is outside the object (at least " + std::to_string(lo) + " bytes)");
                continue;
              }
              pf.wheres.push_back(std::move(pw2));
            }
          }
          if (fs.nullable.value_or(false)) {
            pf.isNull = tm.bvVar("null." + pf.name, 1);
            out.vars.push_back({pf.isNull, "", /*promote=*/true});
            out.soft.push_back({"benign.nonnull." + pf.name, tm.mkEq(pf.isNull, tm.bvConst(1, 0)), 5});
          }
          (void)parentTainted;
          outFields.push_back(std::move(pf));
        }
      };

  for (size_t i = 0; i < f->paramTys.size(); ++i) {
    const std::string &pname = f->entry()->args[i]->name;
    const Type *ty = f->paramTys[i];
    const ParamSpec *ps = nullptr;
    for (auto &p : spec.params)
      if (p.name == pname) ps = &p;
    ParamSpec dflt;
    dflt.name = pname;
    dflt.line = spec.line;
    if (!ps) ps = &dflt;  // unmentioned parameters are untainted with legal defaults

    PlannedParam pl;
    pl.name = pname;
    pl.line = ps->line;
    bool taintedValue = ps->taint == "value" || ps->taint == "both";
    bool taintedPointee = ps->taint == "pointee" || ps->taint == "both";

    if (ty->isPtr()) {
      if (ps->taint == "value") { err(ps->line, "'" + pname + "': a tainted pointer value (taint: value) is not supported yet; use taint: pointee"); continue; }
      if (ps->taint == "both") diags.warning("'" + pname + "': taint: both on a pointer is treated as taint: pointee (the address itself stays caller provided)");

      // std::basic_string<char|wchar_t>: a self-consistent synthetic libstdc++ object (two free variables: content
      // length and SSO-vs-heap representation choice) rather than the generic "every field an independent symbol"
      // path below, which cannot express the SSO invariant (_M_p/_M_string_length/local-buffer-or-capacity must
      // agree with each other) and so lets the solver pick internally contradictory states (see IMPLEMENTATION_PLAN
      // "std::string 不变式建模" / json11 entry-parameter finding).
      if (ps->kind == "string" || ps->kind == "wstring") {
        if (!ps->fields.empty()) { err(ps->line, "'" + pname + "': fields do not apply to kind: " + ps->kind + " (the layout is fixed)"); continue; }
        if (ps->at) { err(ps->line, "'" + pname + "': at does not apply to kind: " + ps->kind); continue; }
        if (ps->owned) { err(ps->line, "'" + pname + "': owned does not apply to kind: " + ps->kind); continue; }
        if (ps->externallyMutable) { err(ps->line, "'" + pname + "': externally_mutable does not apply to kind: " + ps->kind); continue; }
        if (!ps->elements.empty() || !ps->where.empty()) { err(ps->line, "'" + pname + "': elements/where do not apply to kind: " + ps->kind); continue; }
        pl.kind = PlannedParam::StdString;
        pl.charWidth = ps->kind == "wstring" ? 32 : 8;
        pl.tainted = taintedPointee;
        const unsigned charBytes = pl.charWidth / 8;
        const unsigned ptrBytes = pw / 8;
        const unsigned localCap = 15 / charBytes;               // max SSO content length in elements (libstdc++ ABI)
        const unsigned localBufBytes = (localCap + 1) * charBytes;
        const unsigned unionBytes = std::max(localBufBytes, ptrBytes);
        const uint64_t objSize = 2ull * ptrBytes + unionBytes;  // sizeof(std::basic_string<CharT>)
        pl.sizeLo = pl.sizeHi = objSize;
        pl.size = bv(pw, static_cast<int64_t>(objSize));

        uint64_t lenLo = ps->sizeMin ? *ps->sizeMin : 0, lenHi = ps->sizeMax ? *ps->sizeMax : 256;
        if (lenHi > file.defaults.maxObj) lenHi = file.defaults.maxObj;
        if (lenLo > lenHi) { err(ps->line, "'" + pname + "': size.min exceeds size.max"); continue; }
        if (!taintedPointee) {
          uint64_t fixed = ps->sizeMin ? *ps->sizeMin : (ps->sizeMax ? *ps->sizeMax : 0);
          lenLo = lenHi = fixed;
        } else if (lenHi - lenLo > 256) {
          err(ps->line, "'" + pname + "': a symbolic-length " + ps->kind + " needs size.max - size.min <= 256 (got " +
                            std::to_string(lenHi - lenLo) + "); give a smaller size.max");
          continue;
        }
        if (lenLo == lenHi) pl.strLen = bv(pw, static_cast<int64_t>(lenLo));
        else {
          pl.strLen = tm.bvVar("len." + pname, pw);
          out.vars.push_back({pl.strLen, out.label});
          constraintAt("init." + pname + ".strlen[" + std::to_string(lenLo) + "," + std::to_string(lenHi) + "]", ps, ps->line,
                        tm.mkAnd(tm.mkCmp(Kind::Ule, bv(pw, static_cast<int64_t>(lenLo)), pl.strLen),
                                 tm.mkCmp(Kind::Ule, pl.strLen, bv(pw, static_cast<int64_t>(lenHi)))));
          out.soft.push_back({"benign.len." + pname, tm.mkEq(pl.strLen, bv(pw, static_cast<int64_t>(std::min<uint64_t>(lenHi, 5)))), 2});
        }

        pl.strHeap = tm.bvVar("heap." + pname, 1);
        out.vars.push_back({pl.strHeap, ""});  // not attacker data: a choice between two legal internal representations
        // The one real invariant this models: SSO requires length <= local capacity. (The converse is not forced —
        // libstdc++ never heap-allocates a short string on its own, but a heap representation of a short string is
        // still a memory-safe state, so it is not excluded; excluding it would make the model narrower than reality,
        // not just narrower than what libstdc++ happens to produce.)
        TermRef heapChosen = tm.mkEq(pl.strHeap, tm.bvConst(1, 1));
        TermRef ssoFits = tm.mkCmp(Kind::Ule, pl.strLen, bv(pw, static_cast<int64_t>(localCap)));
        constraintAt("init." + pname + ".sso_or_heap", ps, ps->line, tm.mkOr(heapChosen, ssoFits));
        out.soft.push_back({"benign.heap." + pname, tm.mkEq(pl.strHeap, tm.bvConst(1, 0)), 1});  // try SSO first: the common case

        if (ps->nullable.value_or(false)) {  // meaningful only for a `const std::string*` parameter, not a reference
          pl.isNull = tm.bvVar("null." + pname, 1);
          out.vars.push_back({pl.isNull, "", /*promote=*/true});
          out.soft.push_back({"benign.nonnull." + pname, tm.mkEq(pl.isNull, tm.bvConst(1, 0)), 5});
        }
        out.params.push_back(std::move(pl));
        continue;
      }

      // std::vector<T> (T scalar, non-bool): a self-consistent libstdc++ `_Vector_impl` (one free variable, the
      // element count) rather than three independently symbolic pointers, which cannot express "_M_finish is derived
      // from _M_start" at all (see IMPLEMENTATION_PLAN "std::vector/std::map 入口参数合成自洽化").
      if (ps->kind == "vector") {
        if (!ps->fields.empty()) { err(ps->line, "'" + pname + "': fields do not apply to kind: vector (the layout is fixed)"); continue; }
        if (ps->at) { err(ps->line, "'" + pname + "': at does not apply to kind: vector"); continue; }
        if (ps->owned) { err(ps->line, "'" + pname + "': owned does not apply to kind: vector"); continue; }
        if (ps->externallyMutable) { err(ps->line, "'" + pname + "': externally_mutable does not apply to kind: vector"); continue; }
        if (!ps->elements.empty() || !ps->where.empty()) { err(ps->line, "'" + pname + "': elements/where do not apply to kind: vector"); continue; }
        pl.kind = PlannedParam::StdVector;
        pl.elemWidth = ps->elemBits.value_or(32);
        pl.tainted = taintedPointee;
        const unsigned elemBytes = pl.elemWidth / 8;
        const unsigned ptrBytes = pw / 8;
        const uint64_t objSize = 3ull * ptrBytes;  // sizeof(std::vector<T>): _M_start/_M_finish/_M_end_of_storage
        pl.sizeLo = pl.sizeHi = objSize;
        pl.size = bv(pw, static_cast<int64_t>(objSize));

        // `size.min`/`size.max` are reinterpreted as the element count range (same convention as kind: string's
        // content length), not a byte count -- the object itself is always exactly `objSize` bytes.
        uint64_t lenLo = ps->sizeMin ? *ps->sizeMin : 0, lenHi = ps->sizeMax ? *ps->sizeMax : 64;
        uint64_t maxElems = file.defaults.maxObj / std::max<unsigned>(elemBytes, 1);
        if (lenHi > maxElems) lenHi = maxElems;
        if (lenLo > lenHi) { err(ps->line, "'" + pname + "': size.min exceeds size.max"); continue; }
        if (!taintedPointee) {
          uint64_t fixed = ps->sizeMin ? *ps->sizeMin : (ps->sizeMax ? *ps->sizeMax : 0);
          lenLo = lenHi = fixed;
        } else if (lenHi - lenLo > 256) {
          err(ps->line, "'" + pname + "': a symbolic-length vector needs size.max - size.min <= 256 (got " +
                            std::to_string(lenHi - lenLo) + "); give a smaller size.max");
          continue;
        }
        if (lenLo == lenHi) pl.vecLen = bv(pw, static_cast<int64_t>(lenLo));
        else {
          pl.vecLen = tm.bvVar("len." + pname, pw);
          out.vars.push_back({pl.vecLen, out.label});
          constraintAt("init." + pname + ".veclen[" + std::to_string(lenLo) + "," + std::to_string(lenHi) + "]", ps, ps->line,
                        tm.mkAnd(tm.mkCmp(Kind::Ule, bv(pw, static_cast<int64_t>(lenLo)), pl.vecLen),
                                 tm.mkCmp(Kind::Ule, pl.vecLen, bv(pw, static_cast<int64_t>(lenHi)))));
          out.soft.push_back({"benign.len." + pname, tm.mkEq(pl.vecLen, bv(pw, static_cast<int64_t>(std::min<uint64_t>(lenHi, 3)))), 2});
        }

        if (ps->nullable.value_or(false)) {
          pl.isNull = tm.bvVar("null." + pname, 1);
          out.vars.push_back({pl.isNull, "", /*promote=*/true});
          out.soft.push_back({"benign.nonnull." + pname, tm.mkEq(pl.isNull, tm.bvConst(1, 0)), 5});
        }
        out.params.push_back(std::move(pl));
        continue;
      }

      // std::map<K,V> (K, V scalar, non-bool, <=8 bytes, default comparator/allocator): see the "StdMap" comment in
      // InitPlan.h for why this is deliberately narrowed to "empty, or exactly one (black, root) node" rather than a
      // general symbolic red-black tree. 0/1 nodes never need a key comparison at all, which is what makes this
      // tractable without touching the comparator.
      if (ps->kind == "map") {
        if (!ps->fields.empty()) { err(ps->line, "'" + pname + "': fields do not apply to kind: map (the layout is fixed)"); continue; }
        if (ps->at) { err(ps->line, "'" + pname + "': at does not apply to kind: map"); continue; }
        if (ps->owned) { err(ps->line, "'" + pname + "': owned does not apply to kind: map"); continue; }
        if (ps->externallyMutable) { err(ps->line, "'" + pname + "': externally_mutable does not apply to kind: map"); continue; }
        if (!ps->elements.empty() || !ps->where.empty()) { err(ps->line, "'" + pname + "': elements/where do not apply to kind: map"); continue; }
        if (ps->sizeMin || ps->sizeMax) { err(ps->line, "'" + pname + "': size does not apply to kind: map (it always models 0 or 1 entries)"); continue; }
        pl.kind = PlannedParam::StdMap;
        pl.keyWidth = ps->keyBits.value_or(32);
        pl.valWidth = ps->valBits.value_or(32);
        pl.tainted = taintedPointee;
        const unsigned ptrBytes = pw / 8;
        // libstdc++ `_Rb_tree_header` (color+pad, parent, left, right, node_count -- 5 pointer-width words) sits at
        // offset `ptrBytes` within the map object (the empty `_Rb_tree_key_compare<std::less<K>>`/allocator EBO
        // bases ahead of it still occupy one pointer-width word; verified with `-Xclang -fdump-record-layouts` on
        // `std::map<int,int>`/`<long,double>`/`<short,char>`, all three give offset 8 / sizeof 48 at ptrBytes==8 --
        // see IMPLEMENTATION_PLAN). 6*ptrBytes generalises that measurement in terms of the target's pointer width.
        const uint64_t objSize = 6ull * ptrBytes;
        pl.sizeLo = pl.sizeHi = objSize;
        pl.size = bv(pw, static_cast<int64_t>(objSize));

        if (taintedPointee) {
          // Unlike kind: string's `strHeap` (a pure internal-representation detail with no externally observable
          // difference: the same string content either way), whether the map is empty or has an entry is itself
          // part of what an attacker-controlled input chooses and does change observable behaviour (size(), whether
          // the loop body runs, ...), so this must be a tainted/symbolic variable, not an untainted structural one --
          // the engines this project ships (`hlir-scan`'s default taint-guided concolic mode in particular, see
          // lib/semantics/TaintDomain.h `nondet()`: a `core.nondet` without a `taint` attribute is concretised once
          // and never branch-flipped) only explore the *other* value of an untainted nondet var under full symbolic
          // execution (`hlir-entry --analyze`/the unit tests' SymbolicExecutor); a real `hlir-scan` run would never
          // reach the "has an entry" branch at all if this were untainted, silently reducing this kind to "always
          // synthesises an empty map" in practice. Caught by testing this kind end-to-end with `hlir-scan` itself
          // (not just the unit tests), not merely by analogy with kind: string -- see IMPLEMENTATION_PLAN.
          pl.mapHasElem = tm.bvVar("haselem." + pname, 1);
          out.vars.push_back({pl.mapHasElem, out.label});
          out.soft.push_back({"benign.empty." + pname, tm.mkEq(pl.mapHasElem, tm.bvConst(1, 0)), 1});  // try empty first
          pl.mapKey = tm.bvVar("key." + pname, pl.keyWidth);
          out.vars.push_back({pl.mapKey, out.label});
          pl.mapVal = tm.bvVar("val." + pname, pl.valWidth);
          out.vars.push_back({pl.mapVal, out.label});
        } else {
          pl.mapHasElem = tm.bvConst(1, 0);  // untainted: always the empty map (no attacker-chosen content to place in it)
          pl.mapKey = bv(pl.keyWidth, 0);
          pl.mapVal = bv(pl.valWidth, 0);
        }

        if (ps->nullable.value_or(false)) {
          pl.isNull = tm.bvVar("null." + pname, 1);
          out.vars.push_back({pl.isNull, "", /*promote=*/true});
          out.soft.push_back({"benign.nonnull." + pname, tm.mkEq(pl.isNull, tm.bvConst(1, 0)), 5});
        }
        out.params.push_back(std::move(pl));
        continue;
      }

      pl.kind = ps->kind == "cstring" ? PlannedParam::CString : PlannedParam::Buffer;
      pl.tainted = taintedPointee;
      uint64_t lo = 0, hi = 0;
      if (ps->sizeFromParam) {
        // size.from_param: the real object size is the value of an EARLIER top-level scalar parameter (the
        // cross-parameter "pointer + length" idiom, e.g. `int foo(size_t klen, const void *key)`), as opposed to
        // size.from_field's "length lives in a sibling field of the SAME pointee object" idiom. Mirrors the
        // existing earlier-only `elements.count` lookup against `out.params` a few dozen lines below -- not a new
        // ordering restriction.
        if (pl.kind == PlannedParam::CString) { err(ps->line, "'" + pname + "': size.from_param does not apply to kind: cstring"); continue; }
        const PlannedParam *sp = nullptr;
        for (auto &q : out.params) if (q.name == *ps->sizeFromParam) sp = &q;
        if (!sp || sp->kind != PlannedParam::Scalar || sp->width == 0) {
          err(ps->line, "'" + pname + "': size.from_param '" + *ps->sizeFromParam + "' does not name an earlier scalar parameter");
          continue;
        }
        TermRef raw = sp->value;
        if (sp->width < pw) raw = sp->isSigned ? tm.mkSExt(raw, pw) : tm.mkZExt(raw, pw);
        else if (sp->width > pw) raw = tm.mkExtract(raw, pw - 1, 0);
        pl.size = raw;
        pl.sizeLo = 0;
        pl.sizeHi = file.defaults.maxObj;
        // clamp: a real allocator (or this harness's core.heap_alloc) cannot honour an arbitrarily large or
        // negative-cast-to-huge-unsigned request; bound the *harness's* allocation to max_obj the same way an
        // ordinary size.max would, without changing what value the callee itself observes for the parameter.
        constraintAt("init." + pname + ".size[0," + std::to_string(file.defaults.maxObj) + "]", ps, ps->line,
                   tm.mkCmp(Kind::Ule, pl.size, bv(pw, static_cast<int64_t>(file.defaults.maxObj))));
        out.soft.push_back({"benign.size." + pname, tm.mkCmp(Kind::Ule, pl.size, bv(pw, 64)), 2});
        lo = pl.sizeLo;
        hi = pl.sizeHi;
      } else {
      lo = ps->sizeMin ? *ps->sizeMin : 1; hi = ps->sizeMax ? *ps->sizeMax : file.defaults.maxObj;
      if (!pl.tainted) {  // fixed, concrete object
        uint64_t fixed = ps->sizeMin ? *ps->sizeMin : (ps->sizeMax ? *ps->sizeMax : std::min<uint64_t>(64, file.defaults.maxObj));
        lo = hi = fixed;
      }
      if (hi > file.defaults.maxObj) {
        diags.warning("'" + pname + "': size.max " + std::to_string(hi) + " exceeds max_obj; clamped to " + std::to_string(file.defaults.maxObj));
        hi = file.defaults.maxObj;
      }
      if (lo > hi) { err(ps->line, "'" + pname + "': size.min exceeds max_obj (" + std::to_string(file.defaults.maxObj) + ")"); continue; }
      if (pl.kind == PlannedParam::CString && lo == 0) lo = 1;  // a C string needs room for its terminator
      if (pl.kind == PlannedParam::CString && pl.tainted && lo != hi && hi > 256) {
        err(ps->line, "'" + pname + "': a symbolic-size cstring needs size.max <= 256 (got " + std::to_string(hi) + "); give a smaller size.max");
        continue;
      }
      pl.sizeLo = lo;
      pl.sizeHi = hi;
      if (lo == hi) pl.size = bv(pw, static_cast<int64_t>(lo));
      else {
        pl.size = tm.bvVar("size." + pname, pw);
        out.vars.push_back({pl.size, ""});
        constraintAt("init." + pname + ".size[" + std::to_string(lo) + "," + std::to_string(hi) + "]", ps, ps->line,
                   tm.mkAnd(tm.mkCmp(Kind::Ule, bv(pw, static_cast<int64_t>(lo)), pl.size), tm.mkCmp(Kind::Ule, pl.size, bv(pw, static_cast<int64_t>(hi)))));
        uint64_t pick = std::min(std::max<uint64_t>(64, lo), hi);
        out.soft.push_back({"benign.size." + pname, tm.mkEq(pl.size, bv(pw, static_cast<int64_t>(pick))), 2});
      }
      }
      if (ps->nullable.value_or(file.defaults.nullable)) {
        pl.isNull = tm.bvVar("null." + pname, 1);
        out.vars.push_back({pl.isNull, "", /*promote=*/true});
        out.soft.push_back({"benign.nonnull." + pname, tm.mkEq(pl.isNull, tm.bvConst(1, 0)), 5});
      }
      pl.at = ps->at;
      pl.owned = ps->owned;
      pl.externallyMutable = ps->externallyMutable;
      // `content: unknown` (DESIGN.md §22.381): the object's bytes are symbolic and harness-labelled rather than
      // zero. Meaningless on a pointee whose content is already attacker data, and saying both is a contradiction
      // rather than a refinement, so it is an error and not a silent precedence rule.
      if (ps->content == "unknown") {
        if (pl.tainted) { err(ps->line, "'" + pname + "': content: unknown contradicts taint: " + ps->taint + " (its bytes are already the attacker's)"); continue; }
        pl.unknownContent = true;
      }
      // size.from_param forbids 'at'/'fields' at spec-parse time (its real size isn't known until the harness
      // runs, same reasoning as size.from_field) -- skip the static 'at' bound check against a real object size.
      if (!ps->sizeFromParam) {
        // `at == 0` is the default ("the argument IS the object's address") and is legal for any object, including
        // an empty one -- a pointer to the start of a zero-byte allocation is a valid C pointer that may be compared
        // and offset, just not dereferenced. Only a real container_of offset has to land inside. Without the guard,
        // `size: { min: 0, max: 0 }` (what an interface model's `user_addr` lowers to) was rejected outright.
        if (ps->at && ps->at >= lo) { err(ps->line, "'" + pname + "': at " + std::to_string(ps->at) + " is outside the object (at least " + std::to_string(lo) + " bytes)"); continue; }
        planFields(ps->fields, pname, lo, pl.tainted, pl.unknownContent, pl.fields);
      }
    } else {
      if (ps->taint == "pointee") { err(ps->line, "'" + pname + "': taint: pointee on a non-pointer parameter"); continue; }
      if (!ps->fields.empty() || ps->at || ps->owned || ps->externallyMutable) { err(ps->line, "'" + pname + "': fields/at only apply to pointer parameters"); continue; }
      if (ps->content == "unknown") { err(ps->line, "'" + pname + "': content only applies to pointer parameters (a scalar has no bytes of its own; use taint/range)"); continue; }
      if (!ps->kind.empty() || ps->sizeMin || ps->sizeMax || ps->sizeFromParam) { err(ps->line, "'" + pname + "': kind/size only apply to pointer parameters"); continue; }
      pl.kind = PlannedParam::Scalar;
      pl.isBool = ty->isBool();
      pl.width = pl.isBool ? 1 : ty->width();
      pl.tainted = taintedValue;
      if (!ps->type.empty()) {
        unsigned w;
        bool s;
        if (!lookupTypeName(ps->type, w, s)) { err(ps->line, "'" + pname + "': unknown type name '" + ps->type + "'"); continue; }
        if (!pl.isBool && w != pl.width) { err(ps->line, "'" + pname + "': type " + ps->type + " is " + std::to_string(w) + " bits but the parameter is i" + std::to_string(pl.width)); continue; }
        pl.isSigned = s;
      }
      if (pl.isBool) pl.isSigned = false;
      pl.enumValues = ps->enumValues;
      if (!pl.tainted) {
        pl.value = tm.bvConst(llvm::APInt(pl.width, static_cast<uint64_t>(ps->value.value_or(0)), true));
      } else {
        const unsigned w = pl.width;
        auto fits = [&](int64_t v) {
          if (w >= 64) return true;
          if (pl.isSigned) return v >= -(int64_t(1) << (w - 1)) && v < (int64_t(1) << (w - 1));
          return v >= 0 && v < (int64_t(1) << w);
        };
        if (ps->lo && ps->hi && !pl.isBool && *ps->lo == *ps->hi && pl.enumValues.empty()) {
          // A single-point range (taint: value, range: [N, N]) pins this scalar to one known value: make it a
          // real constant term (not a free variable plus an equality constraint) instead of the general case
          // below. `pl.tainted` stays true (unchanged downstream taint propagation/labeling), but the SMT term
          // library's existing constant folding (Term.cpp's foldConst, run by every mkBin/mkUn/mkCmp call)
          // then propagates the constant through arithmetic automatically -- a loop whose trip count is this
          // value folds its own loop condition to a literal boolConst every iteration, instead of staying a
          // genuine free-variable comparison that the taint-concolic engine has to treat as a real (if
          // ultimately unsatisfiable to flip) branch decision each time it's evaluated. Not registered in
          // out.vars (nothing is actually free here, so there's nothing for SeedSolver to diversify) and no
          // constraint/soft-preference is added (vacuously true / meaningless once the value is fixed). See
          // docs/DESIGN.md Sec.22.306 (the KLEE comparison that found this) and the following section (this
          // fix) for the full before/after.
          if (!fits(*ps->lo)) { err(ps->line, "'" + pname + "': range does not fit the parameter's type"); continue; }
          pl.value = bv(w, *ps->lo);
        } else {
          pl.value = tm.bvVar("p." + pname, pl.width);
          out.vars.push_back({pl.value, out.label});
          if (ps->lo && ps->hi && !pl.isBool) {
            bool unsignedMax = !pl.isSigned && *ps->hi == -1;  // SIZE_MAX spelled as -1
            if (!fits(*ps->lo) || (!fits(*ps->hi) && !unsignedMax)) { err(ps->line, "'" + pname + "': range does not fit the parameter's type"); continue; }
            Kind le = pl.isSigned ? Kind::Sle : Kind::Ule;
            TermRef hiT = unsignedMax ? tm.bvConst(llvm::APInt::getAllOnes(w)) : bv(w, *ps->hi);
            constraintAt("init." + pname + ".range[" + std::to_string(*ps->lo) + "," + std::to_string(*ps->hi) + "]", ps, ps->line,
                       tm.mkAnd(tm.mkCmp(le, bv(w, *ps->lo), pl.value), tm.mkCmp(le, pl.value, hiT)));
          }
          if (!pl.enumValues.empty()) {
            TermRef any = tm.boolConst(false);
            for (int64_t v : pl.enumValues) any = tm.mkOr(any, tm.mkEq(pl.value, bv(w, v)));
            constraintAt("init." + pname + ".enum", ps, ps->line, any);
          }
          // benign preferences: small, legal, non-negative values
          if (!pl.enumValues.empty()) out.soft.push_back({"benign." + pname, tm.mkEq(pl.value, bv(w, pl.enumValues[0])), 5});
          else if (pl.isBool) out.soft.push_back({"benign." + pname, tm.mkEq(pl.value, tm.bvConst(1, 0)), 1});
          else {
            int64_t pick = 64;
            if (ps->lo && pick < *ps->lo) pick = *ps->lo;
            if (ps->hi && *ps->hi >= 0 && pick > *ps->hi) pick = *ps->hi;
            Kind le = pl.isSigned ? Kind::Sle : Kind::Ule;
            if (pl.isSigned) out.soft.push_back({"benign." + pname + ".nonneg", tm.mkCmp(le, bv(w, 0), pl.value), 5});
            out.soft.push_back({"benign." + pname + ".small", tm.mkCmp(le, pl.value, bv(w, pick < 0 ? 0 : std::max<int64_t>(pick, 64))), 3});
            out.soft.push_back({"benign." + pname + ".pick", tm.mkEq(pl.value, bv(w, pick)), 1});
          }
        }
      }
    }
    out.params.push_back(std::move(pl));
  }
  if (!ok) return false;

  // constraints on integers in the memory of pointer parameters (preconditions): planned here, stated by the harness
  for (auto &pl : out.params) {
    const ParamSpec *ps = nullptr;
    for (auto &p : spec.params) if (p.name == pl.name) ps = &p;
    if (!ps || (ps->elements.empty() && ps->where.empty())) continue;
    if (pl.kind == PlannedParam::Scalar) { err(ps->line, "'" + pl.name + "': elements/where only apply to pointer parameters"); continue; }
    for (auto &w : ps->where) {
      PlannedWhere pw;
      if (!planBound(w, pw, "where[" + std::to_string(w.offset) + "]", pl.name)) continue;
      pw.offset = w.offset;
      if (w.offset + pw.width / 8 > pl.sizeLo) { err(w.line, "'" + pl.name + "': where offset " + std::to_string(w.offset) + " is outside the object (at least " + std::to_string(pl.sizeLo) + " bytes)"); continue; }
      pl.wheres.push_back(std::move(pw));
    }
    for (auto &el : ps->elements) {
      PlannedElements pe;
      if (!planBound(el, pe, "elements", pl.name)) continue;
      pe.elemBytes = (pe.width + 7) / 8;
      if (pl.sizeLo < pe.elemBytes) { err(el.line, "'" + pl.name + "': the object (at least " + std::to_string(pl.sizeLo) + " bytes) is smaller than one " + el.type); continue; }
      if (!el.count.empty()) {
        bool numeric = std::all_of(el.count.begin(), el.count.end(), [](char c) { return isdigit(static_cast<unsigned char>(c)); });
        if (numeric) pe.count = bv(pw, static_cast<int64_t>(std::stoull(el.count)));
        else {
          const PlannedParam *cp = nullptr;
          for (auto &q : out.params) if (q.name == el.count) cp = &q;
          if (!cp || cp->kind != PlannedParam::Scalar || cp->width == 0) { err(el.line, "'" + pl.name + "': count '" + el.count + "' is not an integer parameter"); continue; }
          pe.count = cp->value;
          pe.countSigned = cp->isSigned;
          pe.countWidth = cp->width;
        }
      }
      pl.elements.push_back(std::move(pe));
    }
  }

  for (auto &r : spec.relations) {
    std::string e;
    TermRef t = compileRelation(r.text, out.params, tm, e);
    if (!t) { err(r.line, "relation '" + r.text + "': " + e); continue; }
    constraint(r.file.empty() ? "init.rel." + r.text : "pre.rel." + r.text, r.line, t);
    if (!r.file.empty()) out.constraints.back().name = "pre.rel." + r.text + at(r.file, r.line);
    // An untainted input (an object size) equated with a tainted one must be symbolic too: the engine fixes an
    // untainted nondet to its seed value, so `bytes == size(ib)` pinned the tainted `bytes` to 64 and every branch
    // that needs another value was unsatisfiable -- ntfs3's check_index_buffer came out safe at 13% coverage
    // (DESIGN.md §22.348). Only equalities: `len <= size(buf)` leaves len free below the seed size, and a symbolic
    // size in every generated length relation cost c-ares' reply parsers up to 45% of their block coverage.
    if (t->kind != Kind::Eq) continue;
    std::vector<TermRef> rv;
    smt::collectVars(t, rv);
    auto inRel = [&](const InitVar &v) { return std::find(rv.begin(), rv.end(), v.var) != rv.end(); };
    if (std::any_of(out.vars.begin(), out.vars.end(), [&](const InitVar &v) { return !v.taint.empty() && inRel(v); }))
      for (auto &v : out.vars)
        if (v.taint.empty() && inRel(v)) v.taint = out.label;
  }
  // `setup:` -- the session constructor. Resolved at the END of the plan, where out.params already exists -- doing it earlier looked up
  // the session parameter in an empty list and reported it missing, so a wrong name fails at plan
  // time with the spec's own location instead of producing a harness that quietly builds the object by hand after
  // all. A constructor that cannot be resolved is an ERROR, never a silent fallback: the whole point is that the
  // report stops claiming the session is kernel-owned state nobody built (DESIGN.md §22.368 §7).
  if (!spec.setup.function.empty()) {
    const Function *cf = m.findFunction(spec.setup.function);
    if (!cf) err(spec.setup.line, "setup function @" + spec.setup.function + " does not exist in the module");
    else if (cf->isDeclaration()) err(spec.setup.line, "setup function @" + spec.setup.function + " has no body in the link set");
    else {
      size_t si = out.params.size(), ci = cf->entry()->args.size();
      for (size_t i = 0; i < out.params.size(); ++i)
        if (out.params[i].name == spec.setup.sessionParam) si = i;
      for (size_t i = 0; i < cf->entry()->args.size(); ++i)
        if (cf->entry()->args[i]->name == spec.setup.ctorParam) ci = i;
      if (si >= out.params.size())
        err(spec.setup.line, "setup.session_param '" + spec.setup.sessionParam + "' is not a parameter of @" + spec.function);
      else if (ci >= cf->entry()->args.size())
        err(spec.setup.line, "setup.ctor_param '" + spec.setup.ctorParam + "' is not a parameter of @" + spec.setup.function);
      else if (out.params[si].kind == PlannedParam::Scalar)
        err(spec.setup.line, "setup.session_param '" + spec.setup.sessionParam + "' is a scalar: a constructor builds an object");
      else {
        out.setup.function = spec.setup.function;
        out.setup.sessionParamIdx = si;
        out.setup.ctorParamIdx = ci;
        out.setup.retTy = cf->retTy;
        out.setup.success = spec.setup.success;
        for (auto &a : cf->entry()->args) out.setup.ctorParamTys.push_back(a->ty);
        out.setup.valid = true;
      }
    }
  }
  std::stable_sort(out.soft.begin(), out.soft.end(), [](const SoftConstraint &a, const SoftConstraint &b) { return a.weight > b.weight; });
  return ok;
}

}  // namespace hlir::entry

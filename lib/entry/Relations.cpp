#include "Relations.h"

#include <cctype>

namespace hlir::entry {

using smt::Kind;
using smt::TermRef;

bool lookupTypeName(const std::string &n, unsigned &w, bool &s) {
  static const struct { const char *n; unsigned w; bool s; } t[] = {
      {"int", 32, true}, {"signed", 32, true}, {"unsigned", 32, false}, {"unsigned int", 32, false},
      {"int32_t", 32, true}, {"uint32_t", 32, false}, {"i32", 32, true}, {"u32", 32, false}, {"s32", 32, true},
      {"long", 64, true}, {"unsigned long", 64, false}, {"ssize_t", 64, true}, {"size_t", 64, false}, {"ptrdiff_t", 64, true},
      {"int64_t", 64, true}, {"uint64_t", 64, false}, {"i64", 64, true}, {"u64", 64, false}, {"s64", 64, true},
      {"short", 16, true}, {"unsigned short", 16, false}, {"int16_t", 16, true}, {"uint16_t", 16, false}, {"i16", 16, true}, {"u16", 16, false},
      {"char", 8, true}, {"signed char", 8, true}, {"unsigned char", 8, false}, {"int8_t", 8, true}, {"uint8_t", 8, false},
      {"i8", 8, true}, {"u8", 8, false}, {"socklen_t", 32, false}, {"off_t", 64, true}};
  for (auto &e : t)
    if (n == e.n) { w = e.w; s = e.s; return true; }
  return false;
}

namespace {

enum class T { Num, Id, Op, End };
struct Tok { T k; std::string s; };

std::vector<Tok> lex(const std::string &s, std::string &err) {
  std::vector<Tok> out;
  size_t i = 0;
  while (i < s.size()) {
    char c = s[i];
    if (isspace(static_cast<unsigned char>(c))) { ++i; continue; }
    if (isdigit(static_cast<unsigned char>(c))) {
      size_t b = i;
      while (i < s.size() && (isalnum(static_cast<unsigned char>(s[i])))) ++i;
      out.push_back({T::Num, s.substr(b, i - b)});
    } else if (isalpha(static_cast<unsigned char>(c)) || c == '_') {
      size_t b = i;
      while (i < s.size() && (isalnum(static_cast<unsigned char>(s[i])) || s[i] == '_')) ++i;
      out.push_back({T::Id, s.substr(b, i - b)});
    } else {
      static const char *two[] = {"=>", "<=", ">=", "==", "!=", "&&", "||"};
      bool done = false;
      for (auto *t : two)
        if (s.compare(i, 2, t) == 0) { out.push_back({T::Op, t}); i += 2; done = true; break; }
      if (done) continue;
      if (std::string("()+-*<>!,").find(c) == std::string::npos) { err = std::string("unexpected character '") + c + "'"; return {}; }
      out.push_back({T::Op, std::string(1, c)});
      ++i;
    }
  }
  out.push_back({T::End, ""});
  return out;
}

struct V {
  TermRef t = nullptr;  // 64-bit BV, or Bool when isBool
  bool isBool = false;
  bool sgn = true;
};

class Compiler {
 public:
  Compiler(const std::vector<PlannedParam> &ps, smt::TermManager &tm, std::string &err) : ps_(ps), tm_(tm), err_(err) {}

  TermRef run(const std::string &text) {
    toks_ = lex(text, err_);
    if (!err_.empty()) return nullptr;
    V v = impl();
    if (!err_.empty()) return nullptr;
    if (toks_[p_].k != T::End) { err_ = "unexpected '" + toks_[p_].s + "'"; return nullptr; }
    if (!v.isBool) { err_ = "a relation must be a condition (comparison, &&, ||, =>)"; return nullptr; }
    return v.t;
  }

 private:
  bool isOp(const char *s) const { return toks_[p_].k == T::Op && toks_[p_].s == s; }
  bool eat(const char *s) { if (isOp(s)) { ++p_; return true; } return false; }
  V fail(const std::string &m) { if (err_.empty()) err_ = m; return V{}; }

  V impl() {
    V a = orE();
    if (!err_.empty()) return V{};
    if (eat("=>")) {
      V b = impl();
      if (!err_.empty()) return V{};
      if (!a.isBool || !b.isBool) return fail("'=>' needs conditions on both sides");
      return {tm_.mkImplies(a.t, b.t), true, true};
    }
    return a;
  }
  V orE() {
    V a = andE();
    while (err_.empty() && eat("||")) {
      V b = andE();
      if (!err_.empty() || !a.t) return V{};
      if (!a.isBool || !b.isBool) return fail("'||' needs conditions");
      a = {tm_.mkOr(a.t, b.t), true, true};
    }
    return a;
  }
  V andE() {
    V a = notE();
    while (err_.empty() && eat("&&")) {
      V b = notE();
      if (!err_.empty() || !a.t) return V{};
      if (!a.isBool || !b.isBool) return fail("'&&' needs conditions");
      a = {tm_.mkAnd(a.t, b.t), true, true};
    }
    return a;
  }
  V notE() {
    if (eat("!")) {
      V a = notE();
      if (!a.isBool) return fail("'!' needs a condition");
      return {tm_.mkNot(a.t), true, true};
    }
    return cmp();
  }
  V cmp() {
    V a = add();
    static const char *ops[] = {"<=", ">=", "==", "!=", "<", ">"};
    for (auto *o : ops)
      if (err_.empty() && eat(o)) {
        V b = add();
      if (!err_.empty() || !a.t) return V{};
        if (a.isBool || b.isBool) return fail("cannot compare conditions");
        bool s = a.sgn && b.sgn;
        std::string op = o;
        TermRef r;
        if (op == "==") r = tm_.mkEq(a.t, b.t);
        else if (op == "!=") r = tm_.mkNot(tm_.mkEq(a.t, b.t));
        else if (op == "<") r = tm_.mkCmp(s ? Kind::Slt : Kind::Ult, a.t, b.t);
        else if (op == "<=") r = tm_.mkCmp(s ? Kind::Sle : Kind::Ule, a.t, b.t);
        else if (op == ">") r = tm_.mkCmp(s ? Kind::Slt : Kind::Ult, b.t, a.t);
        else r = tm_.mkCmp(s ? Kind::Sle : Kind::Ule, b.t, a.t);
        return {r, true, true};
      }
    return a;
  }
  V add() {
    V a = mul();
    while (err_.empty() && (isOp("+") || isOp("-"))) {
      bool plus = toks_[p_++].s == "+";
      V b = mul();
      if (!err_.empty() || !a.t) return V{};
      if (a.isBool || b.isBool) return fail("arithmetic on a condition");
      a = {tm_.mkBin(plus ? Kind::BvAdd : Kind::BvSub, a.t, b.t), false, a.sgn && b.sgn};
    }
    return a;
  }
  V mul() {
    V a = unary();
    while (err_.empty() && eat("*")) {
      V b = unary();
      if (!err_.empty() || !a.t) return V{};
      if (a.isBool || b.isBool) return fail("arithmetic on a condition");
      a = {tm_.mkBin(Kind::BvMul, a.t, b.t), false, a.sgn && b.sgn};
    }
    return a;
  }
  V unary() {
    if (eat("-")) {
      V a = unary();
      if (a.isBool) return fail("arithmetic on a condition");
      return {tm_.mkUn(Kind::BvNeg, a.t), false, a.sgn};
    }
    return primary();
  }

  bool castAhead() const {  // "(" typename ")"
    if (!(isOp("(") && toks_[p_ + 1].k == T::Id)) return false;
    size_t q = p_ + 1;
    std::string name;
    while (toks_[q].k == T::Id) { name += (name.empty() ? "" : " ") + toks_[q].s; ++q; }
    unsigned w; bool s;
    return toks_[q].k == T::Op && toks_[q].s == ")" && lookupTypeName(name, w, s);
  }

  V primary() {
    const Tok t = toks_[p_];
    if (t.k == T::Num) {
      ++p_;
      try {
        size_t n;
        uint64_t v = std::stoull(t.s, &n, 0);
        if (n != t.s.size()) return fail("bad number '" + t.s + "'");
        return {tm_.bvConst(64, v), false, true};
      } catch (...) { return fail("bad number '" + t.s + "'"); }
    }
    if (castAhead()) {
      ++p_;
      std::string name;
      while (toks_[p_].k == T::Id) { name += (name.empty() ? "" : " ") + toks_[p_].s; ++p_; }
      ++p_;  // ')'
      unsigned w; bool s;
      lookupTypeName(name, w, s);
      V a = unary();
      if (a.isBool) return fail("cannot cast a condition");
      TermRef narrow = w >= 64 ? a.t : tm_.mkExtract(a.t, w - 1, 0);
      TermRef wide = w >= 64 ? narrow : (s ? tm_.mkSExt(narrow, 64) : tm_.mkZExt(narrow, 64));
      return {wide, false, s};
    }
    if (eat("(")) {
      V a = impl();
      if (!eat(")")) return fail("expected ')'");
      return a;
    }
    if (t.k == T::Id) {
      ++p_;
      if (t.s == "size" && eat("(")) {
        if (toks_[p_].k != T::Id) return fail("size() needs a parameter name");
        std::string n = toks_[p_++].s;
        if (!eat(")")) return fail("expected ')' after size(...)");
        for (auto &p : ps_)
          if (p.name == n) {
            if (p.kind == PlannedParam::Scalar) return fail("size(" + n + "): '" + n + "' is not a pointer parameter");
            return {p.size->sort.width < 64 ? tm_.mkZExt(p.size, 64) : p.size, false, false};
          }
        return fail("unknown parameter '" + n + "'");
      }
      for (auto &p : ps_)
        if (p.name == t.s) {
          if (p.kind != PlannedParam::Scalar) return fail("'" + t.s + "' is a pointer; use size(" + t.s + ")");
          if (p.isBool) return fail("bool parameter '" + t.s + "' cannot be used in a relation");
          TermRef v = p.value;
          TermRef w = p.width >= 64 ? v : (p.isSigned ? tm_.mkSExt(v, 64) : tm_.mkZExt(v, 64));
          return {w, false, p.isSigned};
        }
      return fail("unknown parameter '" + t.s + "'");
    }
    return fail("unexpected '" + t.s + "'");
  }

  const std::vector<PlannedParam> &ps_;
  smt::TermManager &tm_;
  std::string &err_;
  std::vector<Tok> toks_;
  size_t p_ = 0;
};

}  // namespace

smt::TermRef compileRelation(const std::string &text, const std::vector<PlannedParam> &params, smt::TermManager &tm, std::string &err) {
  err.clear();
  return Compiler(params, tm, err).run(text);
}

}  // namespace hlir::entry

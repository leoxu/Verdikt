#include "hlir/ir/Parser.h"

#include <algorithm>
#include <cctype>
#include <set>
#include <unordered_map>

#include "hlir/ir/Printer.h"

namespace hlir {
namespace {

struct Tok {
  enum Kind { Eof, Percent, Caret, At, Ident, Int, String, Punct } kind = Eof;
  std::string text;  // name/ident/digits/string contents/punct
  unsigned line = 1, col = 1;
};

bool isNameChar(char c) { return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '.' || c == '$' || c == '#'; }

class Lexer {
 public:
  Lexer(const std::string &s, std::string *err) : s_(s), err_(err) {}
  std::vector<Tok> run() {
    std::vector<Tok> out;
    while (true) {
      skipSpace();
      Tok t;
      t.line = line_;
      t.col = col_;
      if (pos_ >= s_.size()) { t.kind = Tok::Eof; out.push_back(t); break; }
      char c = s_[pos_];
      if (c == '%' || c == '^' || c == '@') {
        advance();
        std::string n;
        while (pos_ < s_.size() && isNameChar(s_[pos_])) n += take();
        if (n.empty()) { fail(t, "expected a name after '" + std::string(1, c) + "'"); break; }
        t.kind = c == '%' ? Tok::Percent : c == '^' ? Tok::Caret : Tok::At;
        t.text = n;
      } else if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
        while (pos_ < s_.size() && isNameChar(s_[pos_])) t.text += take();
        t.kind = Tok::Ident;
      } else if (std::isdigit(static_cast<unsigned char>(c))) {
        while (pos_ < s_.size() && std::isalnum(static_cast<unsigned char>(s_[pos_]))) t.text += take();
        t.kind = Tok::Int;
      } else if (c == '"') {
        advance();
        bool closed = false;
        while (pos_ < s_.size()) {
          char d = take();
          if (d == '"') { closed = true; break; }
          if (d == '\\' && pos_ < s_.size()) {
            char e = take();
            t.text += e == 'n' ? '\n' : e;
          } else t.text += d;
        }
        if (!closed) { fail(t, "unterminated string literal"); break; }
        t.kind = Tok::String;
      } else if (c == '-' && pos_ + 1 < s_.size() && s_[pos_ + 1] == '>') {
        advance(); advance();
        t.kind = Tok::Punct; t.text = "->";
      } else if (std::string("(){}[],:=-").find(c) != std::string::npos) {
        advance();
        t.kind = Tok::Punct; t.text = std::string(1, c);
      } else {
        fail(t, std::string("unexpected character '") + c + "'");
        break;
      }
      out.push_back(t);
    }
    return out;
  }
  bool failed() const { return failed_; }

 private:
  char take() { char c = s_[pos_]; advance(); return c; }
  void advance() {
    if (s_[pos_] == '\n') { ++line_; col_ = 1; } else ++col_;
    ++pos_;
  }
  void skipSpace() {
    while (pos_ < s_.size()) {
      char c = s_[pos_];
      if (std::isspace(static_cast<unsigned char>(c))) advance();
      else if (c == '/' && pos_ + 1 < s_.size() && s_[pos_ + 1] == '/') { while (pos_ < s_.size() && s_[pos_] != '\n') advance(); }
      else break;
    }
  }
  void fail(const Tok &t, const std::string &m) {
    failed_ = true;
    if (err_) *err_ = std::to_string(t.line) + ":" + std::to_string(t.col) + ": " + m;
  }
  const std::string &s_;
  std::string *err_;
  size_t pos_ = 0;
  unsigned line_ = 1, col_ = 1;
  bool failed_ = false;
};

struct FnState {
  Function *fn = nullptr;
  std::unordered_map<std::string, Value *> values;
  std::unordered_map<std::string, std::unique_ptr<Value>> placeholders;
  std::unordered_map<std::string, Block *> blocks;                  // defined
  std::unordered_map<std::string, std::unique_ptr<Block>> pending;  // referenced, not yet defined
};

const std::set<std::string> kPreds = {"eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"};

class Parser {
 public:
  // Parses into an already-constructed Module (reusing its Context) — the shared path.
  Parser(std::vector<Tok> toks, const std::string &name, Diagnostics &d, Module &mod)
      : toks_(std::move(toks)), name_(name), diags_(d), mod_(&mod) {}

  // Parses into a fresh Module of its own, for the normal "whole program" entry point.
  Parser(std::vector<Tok> toks, const std::string &name, Diagnostics &d, unsigned ptrw)
      : toks_(std::move(toks)), name_(name), diags_(d), owned_(std::make_unique<Module>(ptrw)), mod_(owned_.get()) {}

  // Parses statements into `mod_` (owned or borrowed, either way). Returns false on a syntax/structure error;
  // whatever functions were added before the failure stay in `mod_` — same tolerance a `nullptr` return from
  // `run()`'s unique_ptr-returning caller already had (the partially-built Module there was simply discarded).
  bool runInto() {
    while (!failed_ && cur().kind != Tok::Eof) {
      if (cur().kind == Tok::Ident && cur().text == "core.func") parseFunction();
      else if (cur().kind == Tok::Ident && cur().text == "core.declare") parseDeclare();
      else fail("expected 'core.func' or 'core.declare'");
    }
    return !failed_;
  }

  std::unique_ptr<Module> run() {
    bool ok = runInto();
    if (!ok) return nullptr;
    return std::move(owned_);
  }

 private:
  // ---- token helpers
  const Tok &cur() const { return toks_[pos_]; }
  const Tok &peek(size_t n = 1) const { return toks_[std::min(pos_ + n, toks_.size() - 1)]; }
  void next() { if (pos_ + 1 < toks_.size()) ++pos_; }
  bool isPunct(const char *p) const { return cur().kind == Tok::Punct && cur().text == p; }
  bool eatPunct(const char *p) { if (isPunct(p)) { next(); return true; } return false; }
  bool expectPunct(const char *p) {
    if (eatPunct(p)) return true;
    fail(std::string("expected '") + p + "'");
    return false;
  }
  void fail(const std::string &msg) {
    if (failed_) return;
    failed_ = true;
    Loc l{name_, cur().line, cur().col};
    diags_.error(msg + (cur().kind == Tok::Eof ? " (at end of input)" : ""), l);
  }

  // ---- types
  Type *parseType() {
    if (cur().kind != Tok::Ident) { fail("expected a type"); return nullptr; }
    std::string t = cur().text;
    Context &c = mod_->ctx;
    Type *r = nullptr;
    if (t == "void") r = c.voidTy();
    else if (t == "bool") r = c.boolTy();
    else if (t == "ptr") r = c.ptrTy();
    else if (t.size() > 1 && t[0] == 'i' && std::all_of(t.begin() + 1, t.end(), [](char ch) { return std::isdigit(static_cast<unsigned char>(ch)); })) {
      unsigned w = static_cast<unsigned>(std::stoul(t.substr(1)));
      if (w == 0 || w > 4096) { fail("invalid integer width in type '" + t + "'"); return nullptr; }
      r = c.intTy(w);
    } else { fail("unknown type '" + t + "'"); return nullptr; }
    next();
    return r;
  }

  // ---- values
  Value *useValue(FnState &fs, const std::string &name) {
    auto it = fs.values.find(name);
    if (it != fs.values.end()) return it->second;
    auto &ph = fs.placeholders[name];
    if (!ph) { ph = std::make_unique<Value>(Value::Placeholder, nullptr); ph->name = name; }
    return ph.get();
  }
  Value *parseOperand(FnState &fs) {
    if (cur().kind != Tok::Percent) { fail("expected a value (%name)"); return nullptr; }
    Value *v = useValue(fs, cur().text);
    next();
    return v;
  }
  bool defineValue(FnState &fs, Value *v, const std::string &name) {
    v->name = name;
    if (!fs.values.emplace(name, v).second) { fail("redefinition of value %" + name); return false; }
    return true;
  }

  Block *refBlock(FnState &fs, const std::string &name) {
    auto it = fs.blocks.find(name);
    if (it != fs.blocks.end()) return it->second;
    auto &p = fs.pending[name];
    if (!p) { p = std::make_unique<Block>(name); p->parent = fs.fn; }
    return p.get();
  }

  bool parseSigned(std::string &digits, bool &neg) {
    neg = eatPunct("-");
    if (cur().kind != Tok::Int) { fail("expected an integer literal"); return false; }
    digits = cur().text;
    next();
    return true;
  }

  bool parseAttrs(Op &op) {
    if (!eatPunct("{")) return true;
    while (!failed_ && !isPunct("}")) {
      if (cur().kind != Tok::Ident) { fail("expected attribute name"); return false; }
      std::string key = cur().text;
      next();
      Attr a = Attr::boolean(true);
      if (eatPunct("=")) {
        if (cur().kind == Tok::String) { a = Attr::string(cur().text); next(); }
        else if (cur().kind == Tok::Ident) {
          if (cur().text == "true") a = Attr::boolean(true);
          else if (cur().text == "false") a = Attr::boolean(false);
          else a = Attr::ident(cur().text);
          next();
        } else {
          std::string d; bool neg;
          if (!parseSigned(d, neg)) return false;
          long long v;
          if (!toI64(d, neg, v)) return false;
          a = Attr::integer(v);
        }
      }
      op.setAttr(key, std::move(a));
      if (!eatPunct(",")) break;
    }
    return expectPunct("}");
  }

  // `%x` starts an operand unless it is the result of the *next* op (`%x = ...`).
  bool atOperand() const { return cur().kind == Tok::Percent && !(peek().kind == Tok::Punct && peek().text == "="); }

  bool parseOperandList(FnState &fs, std::vector<Value *> &out) {
    while (atOperand()) {
      out.push_back(parseOperand(fs));
      if (!eatPunct(",")) break;
      if (cur().kind != Tok::Percent) { fail("expected a value after ','"); return false; }
    }
    return true;
  }

  bool parseSucc(FnState &fs, Succ &s) {
    if (cur().kind != Tok::Caret) { fail("expected a block (^name)"); return false; }
    s.dest = refBlock(fs, cur().text);
    next();
    if (eatPunct("(")) {
      while (!failed_ && cur().kind == Tok::Percent) {
        s.args.push_back(parseOperand(fs));
        if (!eatPunct(",")) break;
      }
      return expectPunct(")");
    }
    return true;
  }


  static unsigned radixOf(std::string &digits) {
    if (digits.size() > 2 && digits[0] == '0' && (digits[1] == 'x' || digits[1] == 'X')) {
      digits = digits.substr(2);
      return 16;
    }
    return 10;
  }

  bool toI64(std::string digits, bool neg, long long &out) {
    unsigned radix = radixOf(digits);
    try {
      size_t used = 0;
      unsigned long long mag = std::stoull(digits, &used, radix);
      if (used != digits.size()) { fail("malformed integer literal"); return false; }
      out = neg ? static_cast<long long>(0 - mag) : static_cast<long long>(mag);
      return true;
    } catch (...) {
      fail("integer literal out of range");
      return false;
    }
  }

  bool makeConst(Type *ty, std::string digits, bool neg, llvm::APInt &out) {
    unsigned radix = radixOf(digits);
    for (char c : digits)
      if (!(radix == 16 ? std::isxdigit(static_cast<unsigned char>(c)) : std::isdigit(static_cast<unsigned char>(c)))) {
        fail("malformed integer literal");
        return false;
      }
    unsigned w = ty->width();
    unsigned bits = llvm::APInt::getBitsNeeded(digits, radix);  // includes a sign bit
    unsigned bw = std::max(bits, w) + 1;
    llvm::APInt big(bw, digits, radix);
    llvm::APInt lim = llvm::APInt::getOneBitSet(bw, neg ? w - 1 : w);
    bool fits = neg ? big.ule(lim) : big.ult(lim);
    if (!fits) { fail("constant does not fit in type " + ty->str()); return false; }
    if (neg) big.negate();
    out = big.zextOrTrunc(w);
    return true;
  }

  // ---- ops
  bool parseOpInto(FnState &fs, Block *blk) {
    std::string resName;
    bool hasRes = false;
    if (cur().kind == Tok::Percent) {
      resName = cur().text;
      hasRes = true;
      next();
      if (!expectPunct("=")) return false;
    }
    if (cur().kind != Tok::Ident || cur().text.rfind("core.", 0) != 0) { fail("expected an op name 'core.<op>'"); return false; }
    Opc opc;
    if (!opcFromName(cur().text.substr(5), opc)) { fail("unknown op '" + cur().text + "'"); return false; }
    const OpInfo &info = opInfo(opc);
    next();
    auto op = std::make_unique<Op>(opc);
    Loc opLoc;

    switch (info.format) {
      case OpFormat::Const: {
        std::string d; bool neg = false;
        Type *ty = nullptr;
        bool isBoolLit = cur().kind == Tok::Ident && (cur().text == "true" || cur().text == "false");
        bool bval = isBoolLit && cur().text == "true";
        if (isBoolLit) next(); else if (!parseSigned(d, neg)) return false;
        if (!expectPunct(":")) return false;
        ty = parseType();
        if (!ty) return false;
        if (isBoolLit) {
          if (!ty->isBool()) { fail("boolean literal requires type bool"); return false; }
          op->constVal = llvm::APInt(1, bval);
        } else {
          if (ty->isBool()) { fail("integer literal requires an integer type"); return false; }
          if (!ty->isInt()) { fail("constant requires an integer type"); return false; }
          if (!makeConst(ty, d, neg, op->constVal)) return false;
        }
        op->result = std::make_unique<Value>(Value::OpResult, ty);
        break;
      }
      case OpFormat::Pred: {
        if (cur().kind != Tok::Ident || !kPreds.count(cur().text)) { fail("expected a comparison predicate"); return false; }
        op->pred = cur().text;
        next();
        if (!parseOperandList(fs, op->operands) || !parseAttrs(*op)) return false;
        if (!expectPunct(":")) return false;
        Type *t = parseType();
        if (!t) return false;
        op->result = std::make_unique<Value>(Value::OpResult, t);
        break;
      }
      case OpFormat::Br: {
        Succ s;
        if (!parseSucc(fs, s)) return false;
        op->succs.push_back(std::move(s));
        break;
      }
      case OpFormat::CondBr: {
        op->operands.push_back(parseOperand(fs));
        if (failed_ || !expectPunct(",")) return false;
        Succ a, b;
        if (!parseSucc(fs, a) || !expectPunct(",") || !parseSucc(fs, b)) return false;
        op->succs.push_back(std::move(a));
        op->succs.push_back(std::move(b));
        break;
      }
      case OpFormat::Switch: {
        op->operands.push_back(parseOperand(fs));
        if (failed_ || !expectPunct("[")) return false;
        while (!failed_ && !isPunct("]")) {
          // case values have the scrutinee's type, which may be unknown yet (forward ref): stored as 64-bit, widened in verifier
          std::string d; bool neg;
          if (!parseSigned(d, neg)) return false;
          long long cv;
          if (!toI64(d, neg, cv)) return false;
          op->caseVals.push_back(llvm::APInt(64, static_cast<uint64_t>(cv), true));
          if (!expectPunct(":")) return false;
          Succ s;
          if (!parseSucc(fs, s)) return false;
          op->succs.push_back(std::move(s));
          if (!eatPunct(",")) break;
        }
        if (!expectPunct("]")) return false;
        if (cur().kind != Tok::Ident || cur().text != "default") { fail("expected 'default'"); return false; }
        next();
        Succ d;
        if (!parseSucc(fs, d)) return false;
        op->succs.push_back(std::move(d));
        break;
      }
      case OpFormat::Ret: {
        if (atOperand()) op->operands.push_back(parseOperand(fs));
        break;
      }
      case OpFormat::Call: {
        if (cur().kind != Tok::At) { fail("expected callee (@name)"); return false; }
        op->sym = cur().text;
        next();
        if (!expectPunct("(")) return false;
        if (!parseOperandList(fs, op->operands) || !expectPunct(")") || !parseAttrs(*op)) return false;
        if (hasRes) {
          if (!expectPunct(":")) return false;
          Type *t = parseType();
          if (!t) return false;
          op->result = std::make_unique<Value>(Value::OpResult, t);
        }
        break;
      }
      case OpFormat::Sym: {
        if (cur().kind != Tok::At) { fail("expected a symbol (@name)"); return false; }
        op->sym = cur().text;
        next();
        if (!parseAttrs(*op) || !expectPunct(":")) return false;
        Type *t = parseType();
        if (!t) return false;
        op->result = std::make_unique<Value>(Value::OpResult, t);
        break;
      }
      case OpFormat::Generic: {
        if (!parseOperandList(fs, op->operands) || !parseAttrs(*op)) return false;
        if (info.hasResult) {
          if (!expectPunct(":")) return false;
          Type *t = parseType();
          if (!t) return false;
          op->result = std::make_unique<Value>(Value::OpResult, t);
        }
        break;
      }
    }
    if (failed_) return false;

    // optional trailing location
    if (cur().kind == Tok::Ident && cur().text == "loc" && peek().kind == Tok::Punct && peek().text == "(") {
      next(); next();
      if (cur().kind != Tok::String) { fail("expected file name string in loc(...)"); return false; }
      opLoc.file = cur().text;
      next();
      std::string l, c;
      if (!expectPunct(":") || cur().kind != Tok::Int) { fail("expected line in loc(...)"); return false; }
      l = cur().text; next();
      if (!expectPunct(":") || cur().kind != Tok::Int) { fail("expected column in loc(...)"); return false; }
      c = cur().text; next();
      if (!expectPunct(")")) return false;
      opLoc.line = static_cast<unsigned>(std::stoul(l));
      opLoc.col = static_cast<unsigned>(std::stoul(c));
    }
    op->loc = opLoc;

    if (hasRes && !op->result) { fail("op '" + std::string(info.name) + "' does not produce a result"); return false; }
    if (!hasRes && info.hasResult) { fail("op '" + std::string(info.name) + "' requires a result (%name = ...)"); return false; }

    Op *raw = blk->append(std::move(op));
    if (hasRes && raw->result && !defineValue(fs, raw->result.get(), resName)) return false;
    return true;
  }

  void parseBlocks(FnState &fs) {
    while (!failed_ && !isPunct("}")) {
      if (cur().kind != Tok::Caret) { fail("expected a block label (^name:)"); return; }
      std::string name = cur().text;
      next();
      if (fs.blocks.count(name)) { fail("redefinition of block ^" + name); return; }
      std::unique_ptr<Block> owned;
      auto pit = fs.pending.find(name);
      if (pit != fs.pending.end()) { owned = std::move(pit->second); fs.pending.erase(pit); }
      else { owned = std::make_unique<Block>(name); }
      owned->parent = fs.fn;
      Block *blk = owned.get();
      fs.fn->blocks.push_back(std::move(owned));
      fs.blocks[name] = blk;
      if (eatPunct("(")) {
        while (!failed_ && cur().kind == Tok::Percent) {
          std::string an = cur().text;
          next();
          if (!expectPunct(":")) return;
          Type *t = parseType();
          if (!t) return;
          Value *a = blk->addArg(t, an);
          if (!defineValue(fs, a, an)) return;
          if (!eatPunct(",")) break;
        }
        if (!expectPunct(")")) return;
      }
      if (!expectPunct(":")) return;
      while (!failed_ && cur().kind != Tok::Caret && !isPunct("}")) {
        if (cur().kind == Tok::Eof) { fail("unexpected end of input inside function"); return; }
        if (!parseOpInto(fs, blk)) return;
      }
    }
  }

  void parseTypeList(std::vector<Type *> &out) {
    if (!expectPunct("(")) return;
    while (!failed_ && !isPunct(")")) {
      Type *t = parseType();
      if (!t) return;
      out.push_back(t);
      if (!eatPunct(",")) break;
    }
    expectPunct(")");
  }

  void parseDeclare() {
    next();
    if (cur().kind != Tok::At) { fail("expected function name (@name)"); return; }
    std::string name = cur().text;
    next();
    std::vector<Type *> params;
    parseTypeList(params);
    if (failed_ || !expectPunct("->")) return;
    Type *ret = parseType();
    if (!ret) return;
    if (mod_->findFunction(name)) { fail("redefinition of function @" + name); return; }
    mod_->addDeclaration(name, std::move(params), ret);
  }

  void parseFunction() {
    next();
    bool internal = false;
    if (cur().kind == Tok::Ident && cur().text == "internal") { internal = true; next(); }
    if (cur().kind != Tok::At) { fail("expected function name (@name)"); return; }
    std::string name = cur().text;
    next();
    std::vector<Type *> params;
    parseTypeList(params);
    if (failed_ || !expectPunct("->")) return;
    Type *ret = parseType();
    if (!ret || !expectPunct("{")) return;
    Function *f = mod_->findFunction(name);
    if (f && !(f->isDeclaration() && f->paramTys == params && f->retTy == ret)) { fail("redefinition of function @" + name); return; }
    if (!f) f = mod_->addDeclaration(name, std::move(params), ret);  // a body may complete an earlier `core.declare`
    if (internal) f->internal = true;
    FnState fs;
    fs.fn = f;
    parseBlocks(fs);
    if (failed_) return;
    if (!expectPunct("}")) return;
    if (f->blocks.empty()) { fail("function @" + name + " has no blocks"); return; }
    if (!fs.pending.empty()) { fail("reference to undefined block ^" + fs.pending.begin()->first); return; }
    // entry block arguments must match the function signature
    Block *entry = f->blocks[0].get();
    bool ok = entry->args.size() == f->paramTys.size();
    for (size_t i = 0; ok && i < f->paramTys.size(); ++i) ok = entry->args[i]->ty == f->paramTys[i];
    if (!ok) { fail("entry block arguments of @" + name + " do not match the function signature"); return; }
    // resolve forward references
    for (auto &b : f->blocks)
      for (auto &op : b->ops)
        op->forEachUse([&](Value *&v) {
          if (failed_ || !v || v->kind != Value::Placeholder) return;
          auto it = fs.values.find(v->name);
          if (it == fs.values.end()) { fail("use of undefined value %" + v->name); return; }
          v = it->second;
        });
  }

  std::vector<Tok> toks_;
  size_t pos_ = 0;
  std::string name_;
  Diagnostics &diags_;
  std::unique_ptr<Module> owned_;  // non-null only for the "fresh Module" constructor
  Module *mod_ = nullptr;
  bool failed_ = false;
};

}  // namespace

std::unique_ptr<Module> parseModule(const std::string &text, const std::string &bufferName, Diagnostics &diags,
                                    unsigned ptrWidth) {
  // version check on the first "core.version N" marker, if present
  auto pos = text.find("core.version");
  if (pos != std::string::npos) {
    int v = std::atoi(text.c_str() + pos + 12);
    if (v != kCoreTextVersion) {
      diags.error("unsupported core text version " + std::to_string(v) + " (this build reads version " +
                      std::to_string(kCoreTextVersion) + ")",
                  Loc{bufferName, 1, 1});
      return nullptr;
    }
  }
  std::string lexErr;
  Lexer lx(text, &lexErr);
  auto toks = lx.run();
  if (lx.failed()) {
    diags.error(lexErr, Loc{bufferName, 1, 1});
    return nullptr;
  }
  Parser p(std::move(toks), bufferName, diags, ptrWidth);
  return p.run();
}

bool parseModuleInto(Module &mod, const std::string &text, const std::string &bufferName, Diagnostics &diags) {
  // same version check and lex as parseModule() — duplicated rather than factored out, to keep parseModule()'s own
  // control flow (and its existing tests) untouched by this addition.
  auto pos = text.find("core.version");
  if (pos != std::string::npos) {
    int v = std::atoi(text.c_str() + pos + 12);
    if (v != kCoreTextVersion) {
      diags.error("unsupported core text version " + std::to_string(v) + " (this build reads version " +
                      std::to_string(kCoreTextVersion) + ")",
                  Loc{bufferName, 1, 1});
      return false;
    }
  }
  std::string lexErr;
  Lexer lx(text, &lexErr);
  auto toks = lx.run();
  if (lx.failed()) {
    diags.error(lexErr, Loc{bufferName, 1, 1});
    return false;
  }
  Parser p(std::move(toks), bufferName, diags, mod);
  return p.runInto();
}

}  // namespace hlir

#include "hlir/ir/Printer.h"

#include <set>
#include <unordered_map>

#include "llvm/ADT/SmallString.h"

namespace hlir {
namespace {

std::string quote(const std::string &s) {
  std::string r = "\"";
  for (char c : s) {
    if (c == '"' || c == '\\') r += '\\';
    if (c == '\n') { r += "\\n"; continue; }
    r += c;
  }
  return r + "\"";
}

class FuncPrinter {
 public:
  FuncPrinter(const Function &f, llvm::raw_ostream &os) : f_(f), os_(os) { assignNames(); }

  void print() {
    os_ << "core.func " << (f_.internal ? "internal " : "") << "@" << f_.name << "(";
    for (size_t i = 0; i < f_.paramTys.size(); ++i) os_ << (i ? ", " : "") << f_.paramTys[i]->str();
    os_ << ") -> " << f_.retTy->str() << " {\n";
    for (auto &b : f_.blocks) printBlock(*b);
    os_ << "}\n";
  }

 private:
  void assignNames() {
    std::set<std::string> used;
    unsigned vn = 0, bn = 0;
    auto fresh = [&](const std::string &pref, unsigned &ctr) {
      std::string n;
      do n = pref + std::to_string(ctr++); while (used.count(n));
      return n;
    };
    // Reserve user-provided names first (first occurrence wins).
    for (auto &b : f_.blocks) {
      if (!b->name.empty() && used.insert("^" + b->name).second) bnames_[b.get()] = b->name;
      for (auto &a : b->args)
        if (!a->name.empty() && used.insert(a->name).second) vnames_[a.get()] = a->name;
      for (auto &op : b->ops)
        if (op->result && !op->result->name.empty() && used.insert(op->result->name).second)
          vnames_[op->result.get()] = op->result->name;
    }
    for (auto &b : f_.blocks) {
      if (!bnames_.count(b.get())) {
        std::string n;
        do n = "bb" + std::to_string(bn++); while (used.count("^" + n));
        used.insert("^" + n);
        bnames_[b.get()] = n;
      }
      for (auto &a : b->args)
        if (!vnames_.count(a.get())) vnames_[a.get()] = fresh("v", vn);
      for (auto &op : b->ops)
        if (op->result && !vnames_.count(op->result.get())) vnames_[op->result.get()] = fresh("v", vn);
    }
  }

  std::string v(const Value *x) const {
    auto it = vnames_.find(x);
    return "%" + (it == vnames_.end() ? std::string("<unnamed>") : it->second);
  }
  std::string b(const Block *x) const {
    auto it = bnames_.find(x);
    return "^" + (it == bnames_.end() ? std::string("<unknown>") : it->second);
  }

  void printSucc(const Succ &s) {
    os_ << b(s.dest);
    if (!s.args.empty()) {
      os_ << "(";
      for (size_t i = 0; i < s.args.size(); ++i) os_ << (i ? ", " : "") << v(s.args[i]);
      os_ << ")";
    }
  }

  void printAttrs(const Op &op) {
    if (op.attrs.empty()) return;
    os_ << " {";
    bool first = true;
    for (auto &p : op.attrs) {
      os_ << (first ? "" : ", ") << p.first;
      first = false;
      const Attr &a = p.second;
      if (a.kind == Attr::Bool && a.i) continue;  // bare key == true
      os_ << "=";
      switch (a.kind) {
        case Attr::Int: os_ << a.i; break;
        case Attr::Str: os_ << quote(a.s); break;
        case Attr::Bool: os_ << "false"; break;
        case Attr::Ident: os_ << a.s; break;
      }
    }
    os_ << "}";
  }

  void printOperands(const Op &op) {
    for (size_t i = 0; i < op.operands.size(); ++i) os_ << (i ? ", " : " ") << v(op.operands[i]);
  }

  void printOp(const Op &op) {
    os_ << "  ";
    if (op.result) os_ << v(op.result.get()) << " = ";
    const OpInfo &info = opInfo(op.opc);
    os_ << "core." << info.name;
    switch (info.format) {
      case OpFormat::Const:
        if (op.result->ty->isBool()) os_ << (op.constVal.getBoolValue() ? " true" : " false");
        else { llvm::SmallString<32> s; op.constVal.toStringSigned(s); os_ << " " << s; }
        break;
      case OpFormat::Pred:
        os_ << " " << op.pred;
        for (size_t i = 0; i < op.operands.size(); ++i) os_ << (i ? ", " : " ") << v(op.operands[i]);
        printAttrs(op);
        break;
      case OpFormat::Br:
        os_ << " ";
        printSucc(op.succs[0]);
        break;
      case OpFormat::CondBr:
        os_ << " " << v(op.operands[0]) << ", ";
        printSucc(op.succs[0]);
        os_ << ", ";
        printSucc(op.succs[1]);
        break;
      case OpFormat::Switch: {
        os_ << " " << v(op.operands[0]) << " [";
        size_t n = op.caseVals.size();
        for (size_t i = 0; i < n; ++i) {
          llvm::SmallString<32> s;
          op.caseVals[i].toStringSigned(s);
          os_ << (i ? ", " : "") << s << ": ";
          printSucc(op.succs[i]);
        }
        os_ << "] default ";
        if (op.succs.size() == n + 1) printSucc(op.succs[n]);
        break;
      }
      case OpFormat::Ret:
        printOperands(op);
        break;
      case OpFormat::Call:
        os_ << " @" << op.sym << "(";
        for (size_t i = 0; i < op.operands.size(); ++i) os_ << (i ? ", " : "") << v(op.operands[i]);
        os_ << ")";
        printAttrs(op);
        break;
      case OpFormat::Sym:
        os_ << " @" << op.sym;
        printAttrs(op);
        break;
      case OpFormat::Generic:
        printOperands(op);
        printAttrs(op);
        break;
    }
    if (op.result) os_ << " : " << op.result->ty->str();
    if (op.loc.valid()) os_ << " loc(" << quote(op.loc.file) << ":" << op.loc.line << ":" << op.loc.col << ")";
    os_ << "\n";
  }

  void printBlock(const Block &blk) {
    os_ << b(&blk);
    if (!blk.args.empty()) {
      os_ << "(";
      for (size_t i = 0; i < blk.args.size(); ++i)
        os_ << (i ? ", " : "") << v(blk.args[i].get()) << ": " << blk.args[i]->ty->str();
      os_ << ")";
    }
    os_ << ":\n";
    for (auto &op : blk.ops) printOp(*op);
  }

  const Function &f_;
  llvm::raw_ostream &os_;
  std::unordered_map<const Value *, std::string> vnames_;
  std::unordered_map<const Block *, std::string> bnames_;
};

}  // namespace

void printModule(const Module &m, llvm::raw_ostream &os) {
  os << "// core.version " << kCoreTextVersion << "\n";
  for (auto &f : m.functions) {
    if (f->isDeclaration()) {
      os << "core.declare @" << f->name << "(";
      for (size_t i = 0; i < f->paramTys.size(); ++i) os << (i ? ", " : "") << f->paramTys[i]->str();
      os << ") -> " << f->retTy->str() << "\n";
    } else {
      FuncPrinter(*f, os).print();
    }
  }
}

std::string moduleToString(const Module &m) {
  std::string s;
  llvm::raw_string_ostream os(s);
  printModule(m, os);
  return os.str();
}

}  // namespace hlir

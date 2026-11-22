#include "hlir/support/Yaml.h"

#include <cctype>

namespace hlir::yaml {

namespace {

struct Line {
  unsigned indent;
  std::string text;  // comment-stripped, right-trimmed, without indentation
  unsigned no;
};

std::string stripComment(const std::string &s) {
  char q = 0;
  for (size_t i = 0; i < s.size(); ++i) {
    char c = s[i];
    if (q) { if (c == q) q = 0; continue; }
    if (c == '"' || c == '\'') q = c;
    else if (c == '#' && (i == 0 || isspace(static_cast<unsigned char>(s[i - 1])))) return s.substr(0, i);
  }
  return s;
}

std::string rtrim(std::string s) {
  while (!s.empty() && isspace(static_cast<unsigned char>(s.back()))) s.pop_back();
  return s;
}
std::string ltrim(std::string s) {
  size_t i = 0;
  while (i < s.size() && isspace(static_cast<unsigned char>(s[i]))) ++i;
  return s.substr(i);
}

class Parser {
 public:
  Parser(std::vector<Line> lines, std::string file, Diagnostics &d) : L_(std::move(lines)), file_(std::move(file)), d_(d) {}

  bool run(YNode &out) {
    if (L_.empty()) { out = YNode{}; return true; }
    out = block(L_[0].indent);
    if (ok_ && i_ < L_.size()) fail(L_[i_].no, "unexpected content (bad indentation?)");
    return ok_;
  }

 private:
  void fail(unsigned line, const std::string &msg) {
    if (!ok_) return;
    ok_ = false;
    Loc l;
    l.file = file_;
    l.line = line;
    l.col = 1;
    d_.error(msg, l);
  }

  // `key: rest` split; returns false if the text is not a mapping entry.
  static bool splitKey(const std::string &t, std::string &key, std::string &rest) {
    if (t.empty() || t[0] == '"' || t[0] == '\'' || t[0] == '{' || t[0] == '[') return false;
    for (size_t i = 0; i < t.size(); ++i)
      if (t[i] == ':' && (i + 1 == t.size() || isspace(static_cast<unsigned char>(t[i + 1])))) {
        key = rtrim(t.substr(0, i));
        rest = ltrim(t.substr(i + 1));
        return true;
      }
    return false;
  }

  YNode block(unsigned indent) {
    if (i_ >= L_.size()) return YNode{};
    if (L_[i_].text.rfind("- ", 0) == 0 || L_[i_].text == "-") return sequence(indent);
    return mapping(indent);
  }

  YNode sequence(unsigned indent) {
    YNode n;
    n.kind = YNode::Seq;
    n.line = L_[i_].no;
    while (ok_ && i_ < L_.size() && L_[i_].indent == indent && (L_[i_].text.rfind("- ", 0) == 0 || L_[i_].text == "-")) {
      Line &ln = L_[i_];
      std::string rest = ltrim(ln.text.substr(1));
      if (rest.empty()) {
        ++i_;
        if (i_ < L_.size() && L_[i_].indent > indent) n.seq.push_back(block(L_[i_].indent));
        else n.seq.push_back(YNode{});
        continue;
      }
      std::string k, r;
      if (splitKey(rest, k, r)) {  // "- key: value" starts an inline mapping whose entries line up after the dash
        unsigned inner = indent + static_cast<unsigned>(ln.text.size() - rest.size());
        ln.indent = inner;
        ln.text = rest;
        n.seq.push_back(mapping(inner));
      } else {
        n.seq.push_back(inlineValue(rest, ln.no));
        ++i_;
      }
    }
    return n;
  }

  YNode mapping(unsigned indent) {
    YNode n;
    n.kind = YNode::Map;
    n.line = L_[i_].no;
    while (ok_ && i_ < L_.size() && L_[i_].indent == indent) {
      Line &ln = L_[i_];
      std::string k, rest;
      if (!splitKey(ln.text, k, rest)) { fail(ln.no, "expected 'key: value'"); break; }
      if (!k.empty() && (k[0] == '"' || k[0] == '\'') && k.size() >= 2) k = k.substr(1, k.size() - 2);
      unsigned no = ln.no;
      ++i_;
      YNode v;
      if (rest.empty()) {
        if (i_ < L_.size() && L_[i_].indent > indent) v = block(L_[i_].indent);
        else if (i_ < L_.size() && L_[i_].indent == indent && (L_[i_].text.rfind("- ", 0) == 0)) v = sequence(indent);  // "key:\n- item"
        else { v.kind = YNode::Null; v.line = no; }
      } else {
        v = inlineValue(rest, no);
      }
      n.map.emplace_back(k, std::move(v));
    }
    if (ok_ && i_ < L_.size() && L_[i_].indent > indent) fail(L_[i_].no, "unexpected indentation");
    return n;
  }

  YNode inlineValue(const std::string &s, unsigned line) {
    size_t pos = 0;
    YNode v = flow(s, pos, line, /*inFlow=*/false);
    pos = s.find_first_not_of(" \t", pos);
    if (ok_ && pos != std::string::npos) fail(line, "unexpected text after value");
    return v;
  }

  YNode flow(const std::string &s, size_t &p, unsigned line, bool inFlow) {
    auto skip = [&] { while (p < s.size() && isspace(static_cast<unsigned char>(s[p]))) ++p; };
    skip();
    YNode n;
    n.line = line;
    if (p >= s.size()) return n;
    if (s[p] == '{' || s[p] == '[') {
      bool isMap = s[p] == '{';
      char close = isMap ? '}' : ']';
      ++p;
      n.kind = isMap ? YNode::Map : YNode::Seq;
      for (;;) {
        skip();
        if (p >= s.size()) { fail(line, "unterminated flow collection"); return n; }
        if (s[p] == close) { ++p; break; }
        if (isMap) {
          YNode key = flow(s, p, line, true);
          skip();
          if (p >= s.size() || s[p] != ':') { fail(line, "expected ':' in flow mapping"); return n; }
          ++p;
          YNode val = flow(s, p, line, true);
          n.map.emplace_back(key.scalar, std::move(val));
        } else {
          n.seq.push_back(flow(s, p, line, true));
        }
        skip();
        if (p < s.size() && s[p] == ',') ++p;
      }
      return n;
    }
    n.kind = YNode::Scalar;
    if (s[p] == '"' || s[p] == '\'') {
      char q = s[p++];
      while (p < s.size() && s[p] != q) n.scalar += s[p++];
      if (p >= s.size()) { fail(line, "unterminated string"); return n; }
      ++p;
      return n;
    }
    size_t b = p;
    while (p < s.size()) {
      char c = s[p];
      if (inFlow && (c == ',' || c == '}' || c == ']' || (c == ':' && (p + 1 >= s.size() || isspace(static_cast<unsigned char>(s[p + 1])))))) break;
      ++p;
    }
    n.scalar = rtrim(s.substr(b, p - b));
    if (n.scalar == "~" || n.scalar == "null") n.kind = YNode::Null;
    return n;
  }

  std::vector<Line> L_;
  std::string file_;
  Diagnostics &d_;
  size_t i_ = 0;
  bool ok_ = true;
};

}  // namespace

bool parseYaml(const std::string &text, const std::string &file, YNode &out, Diagnostics &diags) {
  std::vector<Line> lines;
  unsigned no = 0;
  size_t pos = 0;
  while (pos <= text.size()) {
    size_t e = text.find('\n', pos);
    std::string raw = text.substr(pos, e == std::string::npos ? std::string::npos : e - pos);
    ++no;
    std::string t = rtrim(stripComment(raw));
    size_t ind = 0;
    while (ind < t.size() && t[ind] == ' ') ++ind;
    if (ind < t.size() && t[ind] != '\t' && !ltrim(t).empty()) lines.push_back({static_cast<unsigned>(ind), t.substr(ind), no});
    else if (ind < t.size() && t[ind] == '\t') {
      Loc l; l.file = file; l.line = no; l.col = static_cast<unsigned>(ind + 1);
      diags.error("tabs are not allowed for indentation", l);
      return false;
    }
    if (e == std::string::npos) break;
    pos = e + 1;
  }
  Parser p(std::move(lines), file, diags);
  return p.run(out);
}

}  // namespace hlir::yaml

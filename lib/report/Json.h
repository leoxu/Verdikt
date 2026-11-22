// Private. Minimal streaming JSON writer (objects/arrays/strings/numbers/bools), pretty-printed with 2 spaces.
#pragma once
#include <cstdio>
#include <cstdint>
#include <string>
#include <vector>

namespace hlir::report {

class Json {
 public:
  std::string str() const { return out_ + "\n"; }
  Json &beginObject(const char *key = nullptr) { return open('{', key); }
  Json &endObject() { return close('}'); }
  Json &beginArray(const char *key = nullptr) { return open('[', key); }
  Json &endArray() { return close(']'); }
  Json &str(const char *key, const std::string &v) { prefix(key); quote(v); return *this; }
  Json &num(const char *key, double v) {
    prefix(key);
    char buf[64];
    if (v == static_cast<int64_t>(v)) snprintf(buf, sizeof buf, "%lld", static_cast<long long>(v));
    else snprintf(buf, sizeof buf, "%.6g", v);
    out_ += buf;
    return *this;
  }
  Json &boolean(const char *key, bool v) { prefix(key); out_ += v ? "true" : "false"; return *this; }
  Json &item(const std::string &v) { return str(nullptr, v); }

 private:
  void indent() { out_ += "\n" + std::string(first_.size() * 2, ' '); }
  void prefix(const char *key) {
    if (!first_.empty()) {
      if (!first_.back()) out_ += ",";
      first_.back() = false;
      indent();
    }
    if (key) { quote(key); out_ += ": "; }
  }
  Json &open(char c, const char *key) {
    prefix(key);
    out_ += c;
    first_.push_back(true);
    return *this;
  }
  Json &close(char c) {
    bool empty = first_.back();
    first_.pop_back();
    if (!empty) indent();
    out_ += c;
    return *this;
  }
  void quote(const std::string &s) {
    out_ += '"';
    for (unsigned char ch : s) {
      switch (ch) {
        case '"': out_ += "\\\""; break;
        case '\\': out_ += "\\\\"; break;
        case '\n': out_ += "\\n"; break;
        case '\r': out_ += "\\r"; break;
        case '\t': out_ += "\\t"; break;
        default:
          if (ch < 0x20) { char b[8]; snprintf(b, sizeof b, "\\u%04x", ch); out_ += b; }
          else out_ += static_cast<char>(ch);
      }
    }
    out_ += '"';
  }
  std::string out_;
  std::vector<bool> first_;
};

}  // namespace hlir::report

// Private. IEEE-754 evaluation of core.fop on bit patterns (float = 32 bits, double = 64, x87 long double = 80 bits in an i128).
#pragma once
#include <cmath>
#include <cstring>
#include <optional>
#include <string>
#include <vector>

#include "llvm/ADT/APInt.h"

namespace hlir {

namespace fp {
inline long double load(const llvm::APInt &b, unsigned fw) {
  if (fw == 32) { uint32_t u = static_cast<uint32_t>(b.getZExtValue()); float f; std::memcpy(&f, &u, 4); return f; }
  if (fw == 64) { uint64_t u = b.getZExtValue(); double d; std::memcpy(&d, &u, 8); return d; }
  unsigned char raw[16] = {0};
  uint64_t lo = b.trunc(64).getZExtValue(), hi = b.getBitWidth() > 64 ? b.lshr(64).trunc(64).getZExtValue() : 0;
  std::memcpy(raw, &lo, 8);
  std::memcpy(raw + 8, &hi, 8);
  long double l;
  std::memcpy(&l, raw, sizeof(long double) < 16 ? sizeof(long double) : 16);
  return l;
}
inline llvm::APInt store(long double v, unsigned fw, unsigned width) {
  if (fw == 32) { float f = static_cast<float>(v); uint32_t u; std::memcpy(&u, &f, 4); return llvm::APInt(width, u); }
  if (fw == 64) { double d = static_cast<double>(v); uint64_t u; std::memcpy(&u, &d, 8); return llvm::APInt(width, u); }
  unsigned char raw[16] = {0};
  std::memcpy(raw, &v, sizeof(long double) < 16 ? sizeof(long double) : 16);
  uint64_t lo, hi;
  std::memcpy(&lo, raw, 8);
  std::memcpy(&hi, raw + 8, 8);
  hi &= 0xffff;  // the 6 padding bytes of the 80-bit format are zero
  llvm::APInt r(128, lo);
  r |= llvm::APInt(128, hi).shl(64);
  return r.zextOrTrunc(width);
}
// round-trips through the narrower format for + - * / so that float arithmetic rounds as float, not as long double
inline long double round(long double v, unsigned fw) { return fw == 32 ? static_cast<float>(v) : fw == 64 ? static_cast<double>(v) : v; }
}  // namespace fp

// k: add sub mul div rem neg cmp.<oeq|one|olt|ole|ogt|oge|une|ord|uno> sitofp uitofp fptosi fptoui fpext fptrunc.
// fw: float width of the (float) operands; rw: float width of a float result; rwidth: bit width of the result value.
inline std::optional<llvm::APInt> fpEval(const std::string &k, unsigned fw, unsigned rw, const std::vector<llvm::APInt> &a, unsigned rwidth) {
  using namespace fp;
  auto bin = [&](auto f) -> std::optional<llvm::APInt> {
    if (a.size() != 2) return std::nullopt;
    long double x = load(a[0], fw), y = load(a[1], fw);
    return store(round(f(x, y), fw), fw, rwidth);
  };
  if (k == "add") return bin([](long double x, long double y) { return x + y; });
  if (k == "sub") return bin([](long double x, long double y) { return x - y; });
  if (k == "mul") return bin([](long double x, long double y) { return x * y; });
  if (k == "div") return bin([](long double x, long double y) { return x / y; });
  if (k == "rem") return bin([](long double x, long double y) { return std::fmod(x, y); });
  if (k == "neg") return a.size() == 1 ? std::optional<llvm::APInt>(store(-load(a[0], fw), fw, rwidth)) : std::nullopt;
  if (k.compare(0, 4, "cmp.") == 0 && a.size() == 2) {
    long double x = load(a[0], fw), y = load(a[1], fw);
    std::string p = k.substr(4);
    bool uno = std::isnan(x) || std::isnan(y), r;
    if (p == "oeq") r = !uno && x == y;
    else if (p == "one") r = !uno && x != y;
    else if (p == "olt") r = !uno && x < y;
    else if (p == "ole") r = !uno && x <= y;
    else if (p == "ogt") r = !uno && x > y;
    else if (p == "oge") r = !uno && x >= y;
    else if (p == "une") r = uno || x != y;
    else if (p == "ord") r = !uno;
    else if (p == "uno") r = uno;
    else return std::nullopt;
    return llvm::APInt(1, r);
  }
  if (a.size() != 1) return std::nullopt;
  if (k == "sitofp") return store(round(static_cast<long double>(a[0].getSExtValue()), rw), rw, rwidth);
  if (k == "uitofp") return store(round(static_cast<long double>(a[0].getZExtValue()), rw), rw, rwidth);
  if (k == "fpext" || k == "fptrunc") return store(round(load(a[0], fw), rw), rw, rwidth);
  if (k == "fptosi" || k == "fptoui") {
    long double x = load(a[0], fw);
    bool sg = k == "fptosi";
    if (std::isnan(x)) return llvm::APInt(rwidth, 0);  // out of range is UB in C; the result here is saturated
    long double lim = std::ldexp(1.0L, rwidth > 64 ? 63 : sg ? rwidth - 1 : rwidth);
    if (sg) {
      if (x >= lim) return llvm::APInt::getSignedMaxValue(rwidth);
      if (x < -lim) return llvm::APInt::getSignedMinValue(rwidth);
      return llvm::APInt(rwidth, static_cast<uint64_t>(static_cast<int64_t>(x)), true);
    }
    if (x <= 0) return llvm::APInt(rwidth, 0);
    if (x >= lim) return llvm::APInt::getAllOnes(rwidth);
    return llvm::APInt(rwidth, static_cast<uint64_t>(x));
  }
  return std::nullopt;
}

}  // namespace hlir

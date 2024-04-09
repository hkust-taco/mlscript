#include <cassert>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <new>
#include <tuple>
#include <typeinfo>
#include <utility>

constexpr std::size_t _mlsAlignment = 8;

struct _mlsObject {
  virtual const char *name() const = 0;
};

struct _mls_True;
struct _mls_False;

class _mlsValue {
  using uintptr_t = std::uintptr_t;
  using uint64_t = std::uint64_t;

  alignas(_mlsAlignment) void *value;

  bool isInt63() const { return (reinterpret_cast<uintptr_t>(value) & 1) == 1; }

  bool isPtr() const { return (reinterpret_cast<uintptr_t>(value) & 1) == 0; }

  uint64_t asInt63() const { return reinterpret_cast<uintptr_t>(value) >> 1; }

  uintptr_t asRawInt() const { return reinterpret_cast<uintptr_t>(value); }

  static _mlsValue fromRawInt(uintptr_t i) {
    return _mlsValue(reinterpret_cast<void *>(i));
  }

  static _mlsValue fromInt63(uint64_t i) {
    return _mlsValue(reinterpret_cast<void *>((i << 1) | 1));
  }

  void *asPtr() const {
    assert(!isInt63());
    return value;
  }

  _mlsObject *asObject() const {
    assert(isPtr());
    return static_cast<_mlsObject *>(value);
  }

  bool eqInt63(_mlsValue other) const { return asRawInt() == other.asRawInt(); }

  _mlsValue addInt63(_mlsValue other) const {
    return fromRawInt(asRawInt() + other.asRawInt() - 1);
  }

  _mlsValue subInt63(_mlsValue other) const {
    return fromRawInt(asRawInt() - other.asRawInt() + 1);
  }

  _mlsValue mulInt63(_mlsValue other) const {
    return fromInt63(asInt63() * other.asInt63());
  }

  _mlsValue divInt63(_mlsValue other) const {
    return fromInt63(asInt63() / other.asInt63());
  }

  _mlsValue gtInt63(_mlsValue other) const {
    return asInt63() > other.asInt63() ? _mlsValue::create<_mls_True>()
                                       : _mlsValue::create<_mls_False>();
  }

  _mlsValue ltInt63(_mlsValue other) const {
    return asInt63() < other.asInt63() ? _mlsValue::create<_mls_True>()
                                       : _mlsValue::create<_mls_False>();
  }

  _mlsValue geInt63(_mlsValue other) const {
    return asInt63() >= other.asInt63() ? _mlsValue::create<_mls_True>()
                                        : _mlsValue::create<_mls_False>();
  }

  _mlsValue leInt63(_mlsValue other) const {
    return asInt63() <= other.asInt63() ? _mlsValue::create<_mls_True>()
                                        : _mlsValue::create<_mls_False>();
  }

public:
  _mlsValue() : value(nullptr) {}
  _mlsValue(const _mlsValue &other) : value(other.value) {}
  _mlsValue(_mlsValue &&other) : value(other.value) {}
  _mlsValue(void *value) : value(value) {}

  template <typename T, typename ... U> static _mlsValue create(U&&... args) {
    return _mlsValue(T::template create<_mlsAlignment>(std::forward<U>(args)...));
  }

  template <typename T> static bool isValueOf(_mlsValue v) {
    return dynamic_cast<T *>(v.asObject()) != nullptr;
  }

  template <typename T> static T *as(_mlsValue v) {
    return dynamic_cast<T *>(v.asObject());
  }

  static _mlsValue fromIntLit(uint64_t i) { return fromInt63(i); }

  _mlsValue &operator=(_mlsValue other) {
    value = other.value;
    return *this;
  }

  _mlsValue operator==(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return eqInt63(other) ? _mlsValue::create<_mls_True>()
                            : _mlsValue::create<_mls_False>();
    assert(false);
  }

  _mlsValue operator+(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return addInt63(other);
    assert(false);
  }

  _mlsValue operator-(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return subInt63(other);
    assert(false);
  }

  _mlsValue operator*(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return mulInt63(other);
    assert(false);
  }

  _mlsValue operator/(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return divInt63(other);
    assert(false);
  }

  _mlsValue operator>(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return gtInt63(other);
    assert(false);
  }

  _mlsValue operator<(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return ltInt63(other);
    assert(false);
  }

  _mlsValue operator>=(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return geInt63(other);
    assert(false);
  }

  _mlsValue operator<=(const _mlsValue &other) const {
    if (isInt63() && other.isInt63())
      return leInt63(other);
    assert(false);
  }

  static void print(const _mlsValue &v) {
    if (v.isInt63())
      std::printf("i63 %" PRIu64, v.asInt63());
    else if (v.isPtr() && v.asObject() && v.asObject()->name() != nullptr)
      std::printf("ptr to %s", v.asObject()->name());
    else
      std::printf("ptr %p", v.asPtr());
  }
};

_mlsValue _mlsMain();

int main() {
  auto res = _mlsMain();
  _mlsValue::print(res);
}

struct _mls_True final : public _mlsObject {
  virtual const char *name() const override { return "True"; }
  template <std::size_t align> static _mlsValue create() {
    static _mls_True mlsTrue alignas(align);
    return &mlsTrue;
  }
};

struct _mls_False final : public _mlsObject {
  virtual const char *name() const override { return "True"; }
  template <std::size_t align> static _mlsValue create() {
    static _mls_False mlsFalse alignas(align);
    return &mlsFalse;
  }
};

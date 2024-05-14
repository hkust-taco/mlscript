#include <cassert>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <new>
#include <stdexcept>
#include <tuple>
#include <typeinfo>
#include <utility>

constexpr std::size_t _mlsAlignment = 8;

struct _mlsObject {
  uint32_t refCount;
  uint32_t tag;
  constexpr static inline uint32_t stickyRefCount =
      std::numeric_limits<decltype(refCount)>::max();

  void incRef() { ++refCount; }
  bool decRef() {
    if (refCount != stickyRefCount && --refCount == 0)
      return true;
    return false;
  }

  virtual void print() const = 0;
  virtual void destroy() = 0;
};
struct _mlsCallable;
struct _mls_True;
struct _mls_False;

class _mlsValue {
  using uintptr_t = std::uintptr_t;
  using uint64_t = std::uint64_t;

  void *value alignas(_mlsAlignment);

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

  bool eqInt63(const _mlsValue &other) const {
    return asRawInt() == other.asRawInt();
  }

  _mlsValue addInt63(const _mlsValue &other) const {
    return fromRawInt(asRawInt() + other.asRawInt() - 1);
  }

  _mlsValue subInt63(const _mlsValue &other) const {
    return fromRawInt(asRawInt() - other.asRawInt() + 1);
  }

  _mlsValue mulInt63(const _mlsValue &other) const {
    return fromInt63(asInt63() * other.asInt63());
  }

  _mlsValue divInt63(const _mlsValue &other) const {
    return fromInt63(asInt63() / other.asInt63());
  }

  _mlsValue gtInt63(const _mlsValue &other) const {
    return asInt63() > other.asInt63() ? _mlsValue::create<_mls_True>()
                                       : _mlsValue::create<_mls_False>();
  }

  _mlsValue ltInt63(const _mlsValue &other) const {
    return asInt63() < other.asInt63() ? _mlsValue::create<_mls_True>()
                                       : _mlsValue::create<_mls_False>();
  }

  _mlsValue geInt63(const _mlsValue &other) const {
    return asInt63() >= other.asInt63() ? _mlsValue::create<_mls_True>()
                                        : _mlsValue::create<_mls_False>();
  }

  _mlsValue leInt63(const _mlsValue &other) const {
    return asInt63() <= other.asInt63() ? _mlsValue::create<_mls_True>()
                                        : _mlsValue::create<_mls_False>();
  }

public:
  explicit _mlsValue() : value(nullptr) {}
  explicit _mlsValue(void *value) : value(value) {}
  _mlsValue(const _mlsValue &other) : value(other.value) {
    if (isPtr())
      asObject()->incRef();
  }

  _mlsValue &operator=(const _mlsValue &other) {
    if (value != nullptr && isPtr())
      asObject()->decRef();
    value = other.value;
    if (isPtr())
      asObject()->incRef();
    return *this;
  }

  ~_mlsValue() {
    if (isPtr())
      if (asObject()->decRef()) {
        asObject()->destroy();
        value = nullptr;
      }
  }

  // Factory functions

  static _mlsValue fromIntLit(uint64_t i) { return fromInt63(i); }

  template <typename T, typename... U> static _mlsValue create(U... args) {
    return _mlsValue(T::template create<_mlsAlignment>(args...));
  }

  static void destroy(_mlsValue &v) { v.~_mlsValue(); }

  template <typename T> static bool isValueOf(const _mlsValue &v) {
    return v.asObject()->tag == T::typeTag;
  }

  static bool isIntLit(const _mlsValue &v, uint64_t n) {
    return v.asInt63() == n;
  }

  template <typename T> static T *as(const _mlsValue &v) {
    return dynamic_cast<T *>(v.asObject());
  }

  // Operators

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

  // Auxiliary functions

  void print() const {
    if (isInt63())
      std::printf("%" PRIu64, asInt63());
    else if (isPtr() && asObject())
      asObject()->print();
  }
};

struct _mlsCallable : public _mlsObject {
  virtual _mlsValue apply0() { throw std::runtime_error("Not implemented"); }
  virtual _mlsValue apply1(_mlsValue arg1) {
    throw std::runtime_error("Not implemented");
  }
  virtual _mlsValue apply2(_mlsValue arg1, _mlsValue arg2) {
    throw std::runtime_error("Not implemented");
  }
  virtual _mlsValue apply3(_mlsValue arg1, _mlsValue arg2, _mlsValue arg3) {
    throw std::runtime_error("Not implemented");
  }
  virtual _mlsValue apply4(_mlsValue arg1, _mlsValue arg2, _mlsValue arg3,
                           _mlsValue arg4) {
    throw std::runtime_error("Not implemented");
  }
};

inline _mlsCallable *_mlsToCallable(_mlsValue fn) {
  auto *ptr = _mlsValue::as<_mlsCallable>(fn);
  if (!ptr)
    throw std::runtime_error("Not a callable object");
  return ptr;
}

template <typename... U>
static _mlsValue _mlsCall(_mlsValue f, U... args) {
  static_assert(sizeof...(U) <= 5, "Too many arguments");
  if constexpr (sizeof...(U) == 0)
    return _mlsToCallable(f)->apply0();
  else if constexpr (sizeof...(U) == 1)
    return _mlsToCallable(f)->apply1(args...);
  else if constexpr (sizeof...(U) == 2)
    return _mlsToCallable(f)->apply2(args...);
  else if constexpr (sizeof...(U) == 3)
    return _mlsToCallable(f)->apply3(args...);
  else if constexpr (sizeof...(U) == 4)
    return _mlsToCallable(f)->apply4(args...);
}

_mlsValue _mlsMain();

struct _mls_Boolean : public _mlsObject {};

struct _mls_True final : public _mls_Boolean {
  constexpr static inline const char *typeName = "True";
  constexpr static inline uint32_t typeTag = 1;
  virtual void print() const override { std::printf(typeName); }
  template <std::size_t align> static _mlsValue create() {
    static _mls_True mlsTrue alignas(align);
    mlsTrue.refCount = stickyRefCount;
    mlsTrue.tag = typeTag;
    return _mlsValue(&mlsTrue);
  }
  virtual void destroy() override {}
};

struct _mls_False final : public _mls_Boolean {
  constexpr static inline const char *typeName = "False";
  constexpr static inline uint32_t typeTag = 2;
  virtual void print() const override { std::printf(typeName); }
  template <std::size_t align> static _mlsValue create() {
    static _mls_False mlsFalse alignas(align);
    mlsFalse.refCount = stickyRefCount;
    mlsFalse.tag = typeTag;
    return _mlsValue(&mlsFalse);
  }
  virtual void destroy() override {}
};

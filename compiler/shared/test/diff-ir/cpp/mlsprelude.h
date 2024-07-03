#include <cassert>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <new>
#include <pthread.h>
#include <stdexcept>
#include <sys/resource.h>
#include <tuple>
#include <typeinfo>
#include <utility>

constexpr std::size_t _mlsAlignment = 8;

template <typename T, size_t N> class tuple_type {
  template <typename = std::make_index_sequence<N>> struct impl;
  template <size_t... Is> struct impl<std::index_sequence<Is...>> {
    template <size_t> using wrap = T;
    using type = std::tuple<wrap<Is>...>;
  };

public:
  using type = typename impl<>::type;
};
template <auto Id> struct counter {
  using tag = counter;

  struct generator {
    friend consteval auto is_defined(tag) { return true; }
  };
  friend consteval auto is_defined(tag);

  template <typename Tag = tag, auto = is_defined(Tag{})>
  static consteval auto exists(auto) {
    return true;
  }

  static consteval auto exists(...) { return generator(), false; }
};

template <auto Id = int{}, typename = decltype([] {})>
consteval auto nextTypeTag() {
  if constexpr (not counter<Id>::exists(Id))
    return Id;
  else
    return nextTypeTag<Id + 1>();
}

struct _mlsObject {
  uint32_t refCount;
  uint32_t tag;
  constexpr static inline uint32_t stickyRefCount =
      std::numeric_limits<decltype(refCount)>::max();

  void incRef() {
    if (refCount != stickyRefCount)
      ++refCount;
  }
  bool decRef() {
    if (refCount != stickyRefCount && --refCount == 0)
      return true;
    return false;
  }

  virtual void print() const = 0;
  virtual void destroy() = 0;
};

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

  uint64_t asInt() const {
    assert(isInt63());
    return asInt63();
  }

  static _mlsValue fromIntLit(uint64_t i) { return fromInt63(i); }

  template <unsigned N> static tuple_type<_mlsValue, N> never() {
    __builtin_unreachable();
  }
  static _mlsValue never() { __builtin_unreachable(); }

  template <typename T, typename... U> static _mlsValue create(U... args) {
    return _mlsValue(T::create(args...));
  }

  static void destroy(_mlsValue &v) { v.~_mlsValue(); }

  template <typename T> static bool isValueOf(const _mlsValue &v) {
    return v.asObject()->tag == T::typeTag;
  }

  static bool isIntLit(const _mlsValue &v, uint64_t n) {
    return v.asInt63() == n;
  }

  static bool isIntLit(const _mlsValue &v) { return v.isInt63(); }

  template <typename T> static T *as(const _mlsValue &v) {
    return dynamic_cast<T *>(v.asObject());
  }

  template <typename T> static T *cast(_mlsValue &v) {
    return static_cast<T *>(v.asObject());
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

struct _mls_Callable : public _mlsObject {
  virtual _mlsValue _mls_apply0() { throw std::runtime_error("Not implemented"); }
  virtual _mlsValue _mls_apply1(_mlsValue) {
    throw std::runtime_error("Not implemented");
  }
  virtual _mlsValue _mls_apply2(_mlsValue, _mlsValue) {
    throw std::runtime_error("Not implemented");
  }
  virtual _mlsValue _mls_apply3(_mlsValue, _mlsValue, _mlsValue) {
    throw std::runtime_error("Not implemented");
  }
  virtual _mlsValue _mls_apply4(_mlsValue, _mlsValue, _mlsValue, _mlsValue) {
    throw std::runtime_error("Not implemented");
  }
  virtual void destroy() override {}
};

inline static _mls_Callable *_mlsToCallable(_mlsValue fn) {
  auto *ptr = _mlsValue::as<_mls_Callable>(fn);
  if (!ptr)
    throw std::runtime_error("Not a callable object");
  return ptr;
}

template <typename... U>
inline static _mlsValue _mlsCall(_mlsValue f, U... args) {
  static_assert(sizeof...(U) <= 4, "Too many arguments");
  if constexpr (sizeof...(U) == 0)
    return _mlsToCallable(f)->_mls_apply0();
  else if constexpr (sizeof...(U) == 1)
    return _mlsToCallable(f)->_mls_apply1(args...);
  else if constexpr (sizeof...(U) == 2)
    return _mlsToCallable(f)->_mls_apply2(args...);
  else if constexpr (sizeof...(U) == 3)
    return _mlsToCallable(f)->_mls_apply3(args...);
  else if constexpr (sizeof...(U) == 4)
    return _mlsToCallable(f)->_mls_apply4(args...);
}

template <typename T>
inline static T *_mlsMethodCall(_mlsValue self) {
  auto *ptr = _mlsValue::as<T>(self);
  if (!ptr)
    throw std::runtime_error("unable to convert object for method calls");
  return ptr;
}

inline int _mlsLargeStack(void *(*fn)(void *)) {
  pthread_t thread;
  pthread_attr_t attr;

  size_t stacksize = 512 * 1024 * 1024;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, stacksize);

  int rc = pthread_create(&thread, &attr, fn, nullptr);
  if (rc) {
    printf("ERROR: return code from pthread_create() is %d\n", rc);
    return 1;
  }
  pthread_join(thread, NULL);
  return 0;
}

_mlsValue _mlsMain();

inline void *_mlsMainWrapper(void *) {
  _mlsValue res = _mlsMain();
  res.print();
  return nullptr;
}

struct _mls_Unit final : public _mlsObject {
  constexpr static inline const char *typeName = "Unit";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf(typeName); }
  static _mlsValue create() {
    static _mls_Unit mlsUnit alignas(_mlsAlignment);
    mlsUnit.refCount = stickyRefCount;
    mlsUnit.tag = typeTag;
    return _mlsValue(&mlsUnit);
  }
  virtual void destroy() override {}
};

struct _mls_Boolean : public _mlsObject {};

struct _mls_True final : public _mls_Boolean {
  constexpr static inline const char *typeName = "True";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf(typeName); }
  static _mlsValue create() {
    static _mls_True mlsTrue alignas(_mlsAlignment);
    mlsTrue.refCount = stickyRefCount;
    mlsTrue.tag = typeTag;
    return _mlsValue(&mlsTrue);
  }
  virtual void destroy() override {}
};

struct _mls_False final : public _mls_Boolean {
  constexpr static inline const char *typeName = "False";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf(typeName); }
  static _mlsValue create() {
    static _mls_False mlsFalse alignas(_mlsAlignment);
    mlsFalse.refCount = stickyRefCount;
    mlsFalse.tag = typeTag;
    return _mlsValue(&mlsFalse);
  }
  virtual void destroy() override {}
};

#include <boost/multiprecision/gmp.hpp>

struct _mls_ZInt final : public _mlsObject {
  boost::multiprecision::mpz_int z;
  constexpr static inline const char *typeName = "Z";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override {
    std::printf(typeName);
    std::printf("(");
    std::printf("%s", z.str().c_str());
    std::printf(")");
  }
  virtual void destroy() override {
    z.~number();
    operator delete(this, std::align_val_t(_mlsAlignment));
  }
  static _mlsValue create() {
    auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_ZInt;
    _mlsVal->refCount = 1;
    _mlsVal->tag = typeTag;
    return _mlsValue(_mlsVal);
  }
  static _mlsValue create(_mlsValue z) {
    auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_ZInt;
    _mlsVal->z = z.asInt();
    _mlsVal->refCount = 1;
    _mlsVal->tag = typeTag;
    return _mlsValue(_mlsVal);
  }
  _mlsValue operator+(const _mls_ZInt &other) const {
    auto _mlsVal = _mlsValue::create<_mls_ZInt>();
    _mlsValue::cast<_mls_ZInt>(_mlsVal)->z = z + other.z;
    return _mlsVal;
  }

  _mlsValue operator-(const _mls_ZInt &other) const {
    auto _mlsVal = _mlsValue::create<_mls_ZInt>();
    _mlsValue::cast<_mls_ZInt>(_mlsVal)->z = z - other.z;
    return _mlsVal;
  }

  _mlsValue operator*(const _mls_ZInt &other) const {
    auto _mlsVal = _mlsValue::create<_mls_ZInt>();
    _mlsValue::cast<_mls_ZInt>(_mlsVal)->z = z * other.z;
    return _mlsVal;
  }

  _mlsValue operator/(const _mls_ZInt &other) const {
    auto _mlsVal = _mlsValue::create<_mls_ZInt>();
    _mlsValue::cast<_mls_ZInt>(_mlsVal)->z = z / other.z;
    return _mlsVal;
  }

  _mlsValue operator%(const _mls_ZInt &other) const {
    auto _mlsVal = _mlsValue::create<_mls_ZInt>();
    _mlsValue::cast<_mls_ZInt>(_mlsVal)->z = z % other.z;
    return _mlsVal;
  }

  _mlsValue operator==(const _mls_ZInt &other) const {
    return z == other.z ? _mlsValue::create<_mls_True>()
                        : _mlsValue::create<_mls_False>();
  }

  _mlsValue operator>(const _mls_ZInt &other) const {
    return z > other.z ? _mlsValue::create<_mls_True>()
                       : _mlsValue::create<_mls_False>();
  }

  _mlsValue operator<(const _mls_ZInt &other) const {
    return z < other.z ? _mlsValue::create<_mls_True>()
                       : _mlsValue::create<_mls_False>();
  }

  _mlsValue operator>=(const _mls_ZInt &other) const {
    return z >= other.z ? _mlsValue::create<_mls_True>()
                        : _mlsValue::create<_mls_False>();
  }

  _mlsValue operator<=(const _mls_ZInt &other) const {
    return z <= other.z ? _mlsValue::create<_mls_True>()
                        : _mlsValue::create<_mls_False>();
  }

  _mlsValue toInt() const {
    return _mlsValue::fromIntLit(z.convert_to<uint64_t>());
  }

  static _mlsValue fromInt(uint64_t i) {
    return _mlsValue::create<_mls_ZInt>(_mlsValue::fromIntLit(i));
  }
};

__attribute__((noinline)) inline void _mlsNonExhaustiveMatch() {
  throw std::runtime_error("Non-exhaustive match");
}

inline _mlsValue _mls_builtin_z_add(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) + *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_sub(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) - *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_mul(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) * *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_div(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) / *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_mod(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) % *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_equal(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) == *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_gt(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) > *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_lt(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) < *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_geq(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) >= *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_leq(_mlsValue a, _mlsValue b) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) <= *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_to_int(_mlsValue a) {
  assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  return _mlsValue::cast<_mls_ZInt>(a)->toInt();
}

inline _mlsValue _mls_builtin_z_of_int(_mlsValue a) {
  assert(_mlsValue::isIntLit(a));
  return _mlsValue::create<_mls_ZInt>(a);
}

inline _mlsValue _mls_builtin_print(_mlsValue a) {
  a.print();
  return _mlsValue::create<_mls_Unit>();
}

inline _mlsValue _mls_builtin_println(_mlsValue a) {
  a.print();
  std::puts("");
  return _mlsValue::create<_mls_Unit>();
}

inline _mlsValue _mls_builtin_debug(_mlsValue a) {
  a.print();
  std::puts("");
  return a;
}

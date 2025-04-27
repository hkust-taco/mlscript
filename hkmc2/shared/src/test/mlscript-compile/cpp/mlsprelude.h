#include <cassert>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <limits>
#include <new>
#include <pthread.h>
#include <stdexcept>
#include <string>
#include <string_view>
#include <sys/resource.h>
#include <tuple>
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

constexpr static inline uint32_t unitTag = nextTypeTag();
constexpr static inline uint32_t floatTag = nextTypeTag();
constexpr static inline uint32_t strTag = nextTypeTag();
constexpr static inline uint32_t lazyTag = nextTypeTag();

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

#define BOOST_STACKTRACE_GNU_SOURCE_NOT_REQUIRED
#include <boost/stacktrace.hpp>

class _mlsUtil {
public:
  [[noreturn]] static void panic(const char *msg) {
    std::fprintf(stderr, "Panic: %s\n", msg);
    std::string st =
        boost::stacktrace::to_string(boost::stacktrace::stacktrace());
    std::fprintf(stderr, "%s\n", st.c_str());
    std::abort();
  }
  [[noreturn]] static void panic_with(const char *msg, const char *func,
                                      const char *file, int line) {
    std::fprintf(stderr, "Panic: %s at %s %s:%d\n", msg, func, file, line);
    std::string st =
        boost::stacktrace::to_string(boost::stacktrace::stacktrace());
    std::fprintf(stderr, "%s\n", st.c_str());
    std::abort();
  }
};

#define _mls_assert(e)                                                         \
  (__builtin_expect(!(e), 0)                                                   \
       ? _mlsUtil::panic_with("assertion failed", __func__,                    \
                              __FILE__, __LINE__)                              \
       : (void)0)

struct _mlsFloatShape : public _mlsObject {
  double f;
};

class _mlsValue {
  using uintptr_t = std::uintptr_t;
  using intptr_t = std::intptr_t;
  using int64_t = std::int64_t;

  void *value;

  bool isInt63() const { return (reinterpret_cast<uintptr_t>(value) & 1) == 1; }

  bool isFloat() const { return isPtr() && asObject()->tag == floatTag; }

  bool isPtr() const { return (reinterpret_cast<uintptr_t>(value) & 1) == 0; }

  int64_t asInt63() const { return reinterpret_cast<intptr_t>(value) >> 1; }

  uintptr_t asRawInt() const { return reinterpret_cast<uintptr_t>(value); }

  static _mlsValue fromRawInt(uintptr_t i) {
    return _mlsValue(reinterpret_cast<void *>(i));
  }

  static _mlsValue fromInt63(int64_t i) {
    return _mlsValue(reinterpret_cast<void *>((i << 1) | 1));
  }

  void *asPtr() const {
    _mls_assert(!isInt63());
    return value;
  }

  _mlsObject *asObject() const {
    _mls_assert(isPtr());
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

  _mlsValue modInt63(const _mlsValue &other) const {
    return fromInt63(asInt63() % other.asInt63());
  }

  _mlsValue gtInt63(const _mlsValue &other) const {
    return fromBoolLit(asInt63() > other.asInt63());
  }

  _mlsValue ltInt63(const _mlsValue &other) const {
    return fromBoolLit(asInt63() < other.asInt63());
  }

  _mlsValue geInt63(const _mlsValue &other) const {
    return fromBoolLit(asInt63() >= other.asInt63());
  }

  _mlsValue leInt63(const _mlsValue &other) const {
    return fromBoolLit(asInt63() <= other.asInt63());
  }

  _mlsValue minInt63(const _mlsValue &other) const {
    int64_t a = asInt63();
    int64_t b = other.asInt63();
    return fromInt63(a < b ? a : b);
  }

  _mlsValue maxInt63(const _mlsValue &other) const {
    int64_t a = asInt63();
    int64_t b = other.asInt63();
    return fromInt63(a > b ? a : b);
  }

  _mlsValue absInt63() const {
    int64_t a = asInt63();
    return fromInt63(a < 0 ? -a : a);
  }

  _mlsValue floorDivInt63(const _mlsValue &other) const {
    int64_t a = asInt63();
    int64_t b = other.asInt63();
    int64_t q = a / b;
    int64_t r = a % b;
    if ((r > 0 && b < 0) || (r < 0 && b > 0))
      q = q - 1;
    return fromInt63(q);
  }

  _mlsValue floorModInt63(const _mlsValue &other) const {
    int64_t a = asInt63();
    int64_t b = other.asInt63();
    long r = a % b;
    if ((r > 0 && b < 0) || (r < 0 && b > 0))
      r = r + b;
    return fromInt63(r);
  }

public:
  struct inc_ref_tag {};
  explicit _mlsValue() : value(nullptr) {}
  explicit _mlsValue(void *value) : value(value) {}
  explicit _mlsValue(void *value, inc_ref_tag) : value(value) {
    if (isPtr())
      asObject()->incRef();
  }
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

  int64_t asInt() const {
    _mls_assert(isInt63());
    return asInt63();
  }

  static _mlsValue fromIntLit(int64_t i) { return fromInt63(i); }

  static _mlsValue fromBoolLit(bool b) { return fromInt63(b); }

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

  static bool isIntLit(const _mlsValue &v, int64_t n) {
    return v.asInt63() == n;
  }

  static bool isInt(const _mlsValue &v) { return v.isInt63(); }

  template <typename T> static T *as(const _mlsValue &v) {
    return dynamic_cast<T *>(v.asObject());
  }

  template <typename T> static T *cast(_mlsValue &v) {
    return static_cast<T *>(v.asObject());
  }

  _mlsValue floorDiv(const _mlsValue &other) const;

  _mlsValue floorMod(const _mlsValue &other) const;

  _mlsValue pow(const _mlsValue &other) const;

  _mlsValue abs() const;

  // Operators

  _mlsValue operator==(const _mlsValue &other) const;

  _mlsValue operator!=(const _mlsValue &other) const;

  _mlsValue operator&&(const _mlsValue &other) const;

  _mlsValue operator||(const _mlsValue &other) const;

  _mlsValue operator+(const _mlsValue &other) const;

  _mlsValue operator-(const _mlsValue &other) const;

  _mlsValue operator-() const;

  _mlsValue operator*(const _mlsValue &other) const;

  _mlsValue operator/(const _mlsValue &other) const;

  _mlsValue operator%(const _mlsValue &other) const;

  _mlsValue operator>(const _mlsValue &other) const;

  _mlsValue operator<(const _mlsValue &other) const;

  _mlsValue operator>=(const _mlsValue &other) const;

  _mlsValue operator<=(const _mlsValue &other) const;

  // Auxiliary functions

  void print() const {
    if (isInt63())
      std::printf("%" PRIu64, asInt63());
    else if (isPtr() && asObject())
      asObject()->print();
  }
};

struct _mls_Callable : public _mlsObject {
  virtual _mlsValue _mls_apply0() {
    throw std::runtime_error("Not implemented");
  }
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

template <typename T> inline static T *_mlsMethodCall(_mlsValue self) {
  auto *ptr = _mlsValue::as<T>(self);
  if (!ptr)
    throw std::runtime_error("unable to convert object for method calls");
  return ptr;
}

inline int _mlsLargeStack(void *(*fn)(void *)) {
  pthread_t thread;
  pthread_attr_t attr;

  size_t stacksize = 1024 * 1024 * 1024;
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
  constexpr static inline uint32_t typeTag = unitTag;
  virtual void print() const override { std::printf(typeName); }
  static _mlsValue create() {
    static _mls_Unit mlsUnit alignas(_mlsAlignment);
    mlsUnit.refCount = stickyRefCount;
    mlsUnit.tag = typeTag;
    return _mlsValue(&mlsUnit);
  }
  virtual void destroy() override {}
};

struct _mls_Float final : public _mlsFloatShape {
  constexpr static inline const char *typeName = "Float";
  constexpr static inline uint32_t typeTag = floatTag;
  virtual void print() const override {
    std::printf(typeName);
    std::printf("(");
    std::printf("%f", f);
    std::printf(")");
  }
  static _mlsValue create(double f) {
    auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Float;
    _mlsVal->f = f;
    _mlsVal->refCount = 1;
    _mlsVal->tag = typeTag;
    return _mlsValue(_mlsVal);
  }
  _mlsValue operator+(const _mls_Float &other) const {
    return _mlsValue::create<_mls_Float>(f + other.f);
  }
  _mlsValue operator-(const _mls_Float &other) const {
    return _mlsValue::create<_mls_Float>(f - other.f);
  }
  _mlsValue operator*(const _mls_Float &other) const {
    return _mlsValue::create<_mls_Float>(f * other.f);
  }
  _mlsValue operator/(const _mls_Float &other) const {
    return _mlsValue::create<_mls_Float>(f / other.f);
  }
  _mlsValue operator==(const _mls_Float &other) const {
    return _mlsValue::fromBoolLit(f == other.f);
  }
  _mlsValue operator!=(const _mls_Float &other) const {
    return _mlsValue::fromBoolLit(f == other.f);
  }
  _mlsValue operator>(const _mls_Float &other) const {
    return _mlsValue::fromBoolLit(f > other.f);
  }
  _mlsValue operator<(const _mls_Float &other) const {
    return _mlsValue::fromBoolLit(f < other.f);
  }
  _mlsValue operator>=(const _mls_Float &other) const {
    return _mlsValue::fromBoolLit(f >= other.f);
  }
  _mlsValue operator<=(const _mls_Float &other) const {
    return _mlsValue::fromBoolLit(f <= other.f);
  }
  virtual void destroy() override {
    operator delete(this, std::align_val_t(_mlsAlignment));
  }
};

struct _mls_Str final : public _mlsObject {
  std::string str;
  constexpr static inline const char *typeName = "Str";
  constexpr static inline uint32_t typeTag = strTag;
  virtual void print() const override {
    std::printf("\"");
    for (const auto c : str) {
      switch (c) {
      case '\'':
        std::printf("\\\'");
        break;
      case '\"':
        std::printf("\\\"");
        break;
      case '\?':
        std::printf("\\\?");
        break;
      case '\\':
        std::printf("\\\\");
        break;
      case '\a':
        std::printf("\\a");
        break;
      case '\b':
        std::printf("\\b");
        break;
      case '\f':
        std::printf("\\f");
        break;
      case '\n':
        std::printf("\\n");
        break;
      case '\r':
        std::printf("\\r");
        break;
      case '\t':
        std::printf("\\t");
        break;
      case '\v':
        std::printf("\\v");
        break;
      default:
        if (c < 32 || c > 126)
          std::printf("\\x%02x", c);
        else
          std::putchar(c);
      }
    }
    std::printf("\"");
    std::fflush(stdout);
  }
  static _mlsValue create(const std::string_view str) {
    auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Str;
    _mlsVal->str = str;
    _mlsVal->refCount = 1;
    _mlsVal->tag = typeTag;
    return _mlsValue(_mlsVal);
  }
  static _mlsValue create(const std::string_view str1,
                          const std::string_view str2) {
    auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Str;
    _mlsVal->str = str1;
    _mlsVal->str += str2;
    _mlsVal->refCount = 1;
    _mlsVal->tag = typeTag;
    return _mlsValue(_mlsVal);
  }
  virtual void destroy() override {
    str.~basic_string();
    operator delete(this, std::align_val_t(_mlsAlignment));
  }
};

struct _mls_Lazy final : public _mlsObject {
  _mlsValue init;
  _mlsValue value;
  bool evaluated;
  constexpr static inline const char *typeName = "Lazy";
  constexpr static inline uint32_t typeTag = lazyTag;
  virtual void print() const override { std::printf(typeName); }
  static _mlsValue create(_mlsValue init) {
    auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Lazy;
    _mlsVal->refCount = 1;
    _mlsVal->tag = typeTag;
    _mlsVal->init = init;
    _mlsVal->value = _mlsValue::create<_mls_Unit>();
    _mlsVal->evaluated = false;
    return _mlsValue(_mlsVal);
  }
  virtual void destroy() override {
    _mlsValue::destroy(init);
    _mlsValue::destroy(value);
    operator delete(this, std::align_val_t(_mlsAlignment));
  }
  _mlsValue _mls_get() {
    if (!evaluated) {
      value = _mlsCall(init);
      evaluated = true;
    }
    return value;
  }
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
    return _mlsValue::fromBoolLit(z == other.z);
  }

  _mlsValue operator>(const _mls_ZInt &other) const {
    return _mlsValue::fromBoolLit(z > other.z);
  }

  _mlsValue operator<(const _mls_ZInt &other) const {
    return _mlsValue::fromBoolLit(z < other.z);
  }

  _mlsValue operator>=(const _mls_ZInt &other) const {
    return _mlsValue::fromBoolLit(z >= other.z);
  }

  _mlsValue operator<=(const _mls_ZInt &other) const {
    return _mlsValue::fromBoolLit(z <= other.z);
  }

  _mlsValue toInt() const {
    return _mlsValue::fromIntLit(z.convert_to<int64_t>());
  }

  static _mlsValue fromInt(int64_t i) {
    return _mlsValue::create<_mls_ZInt>(_mlsValue::fromIntLit(i));
  }
};

[[noreturn, gnu::noinline]] inline void _mlsNonExhaustiveMatch() {
  _mlsUtil::panic("Non-exhaustive match");
}

inline _mlsValue _mls_builtin_pow(_mlsValue a, _mlsValue b) { return a.pow(b); }

inline _mlsValue _mls_builtin_abs(_mlsValue a) { return a.abs(); }

inline _mlsValue _mls_builtin_floor_div(_mlsValue a, _mlsValue b) {
  return a.floorDiv(b);
}

inline _mlsValue _mls_builtin_floor_mod(_mlsValue a, _mlsValue b) {
  return a.floorMod(b);
}

inline _mlsValue _mls_builtin_trunc_div(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isInt(a));
  _mls_assert(_mlsValue::isInt(b));
  return a / b;
}

inline _mlsValue _mls_builtin_trunc_mod(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isInt(a));
  _mls_assert(_mlsValue::isInt(b));
  return a % b;
}

inline _mlsValue _mls_builtin_int2str(_mlsValue a) {
  _mls_assert(_mlsValue::isInt(a));
  char buf[32];
  std::snprintf(buf, sizeof(buf), "%" PRIu64, a.asInt());
  return _mlsValue::create<_mls_Str>(buf);
}

inline _mlsValue _mls_builtin_float2str(_mlsValue a) {
  _mls_assert(_mlsValue::isValueOf<_mls_Float>(a));
  char buf[128];
  std::snprintf(buf, sizeof(buf), "%f", _mlsValue::cast<_mls_Float>(a)->f);
  return _mlsValue::create<_mls_Str>(buf);
}

inline _mlsValue _mls_builtin_int2float(_mlsValue a) {
  return _mlsValue::create<_mls_Float>(a.asInt());
}

inline _mlsValue _mls_builtin_str_concat(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_Str>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_Str>(b));
  auto *strA = _mlsValue::cast<_mls_Str>(a);
  auto *strB = _mlsValue::cast<_mls_Str>(b);
  return _mlsValue::create<_mls_Str>(strA->str.c_str(), strB->str.c_str());
}

inline _mlsValue _mls_builtin_z_add(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) + *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_sub(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) - *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_mul(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) * *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_div(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) / *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_mod(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) % *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_equal(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) == *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_gt(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) > *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_lt(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) < *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_geq(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) >= *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_leq(_mlsValue a, _mlsValue b) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(b));
  return *_mlsValue::cast<_mls_ZInt>(a) <= *_mlsValue::cast<_mls_ZInt>(b);
}

inline _mlsValue _mls_builtin_z_to_int(_mlsValue a) {
  _mls_assert(_mlsValue::isValueOf<_mls_ZInt>(a));
  return _mlsValue::cast<_mls_ZInt>(a)->toInt();
}

inline _mlsValue _mls_builtin_z_of_int(_mlsValue a) {
  _mls_assert(_mlsValue::isInt(a));
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

inline _mlsValue _mlsValue::floorDiv(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return floorDivInt63(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::floorMod(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return floorModInt63(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::pow(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return fromInt63(std::pow(asInt63(), other.asInt63()));
  if (isFloat() && other.isFloat())
    return _mlsValue::create<_mls_Float>(
        std::pow(as<_mls_Float>(*this)->f, as<_mls_Float>(other)->f));
  _mls_assert(false);
}

inline _mlsValue _mlsValue::abs() const {
  if (isInt63())
    return absInt63();
  if (isFloat())
    return _mlsValue::create<_mls_Float>(std::abs(as<_mls_Float>(*this)->f));
  _mls_assert(false);
}

// Operators

inline _mlsValue _mlsValue::operator==(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return _mlsValue::fromBoolLit(eqInt63(other));
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) == *as<_mls_Float>(other);
  bool sameTag =
      isPtr() && other.isPtr() && asObject()->tag == other.asObject()->tag;
  if (!sameTag)
    return _mlsValue::fromBoolLit(false);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator!=(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return _mlsValue::fromBoolLit(!eqInt63(other));
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) != *as<_mls_Float>(other);
  bool sameTag =
      isPtr() && other.isPtr() && asObject()->tag == other.asObject()->tag;
  if (!sameTag)
    return _mlsValue::fromBoolLit(true);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator&&(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return _mlsValue::fromBoolLit(asInt63() && other.asInt63());
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator||(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return _mlsValue::fromBoolLit(asInt63() || other.asInt63());
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator+(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return addInt63(other);
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) + *as<_mls_Float>(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator-(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return subInt63(other);
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) - *as<_mls_Float>(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator-() const {
  if (isInt63())
    return fromInt63(-asInt63());
  if (isFloat())
    return _mlsValue::create<_mls_Float>(-as<_mls_Float>(*this)->f);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator*(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return mulInt63(other);
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) * *as<_mls_Float>(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator/(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return divInt63(other);
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) / *as<_mls_Float>(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator%(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return modInt63(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator>(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return gtInt63(other);
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) > *as<_mls_Float>(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator<(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return ltInt63(other);
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) < *as<_mls_Float>(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator>=(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return geInt63(other);
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) >= *as<_mls_Float>(other);
  _mls_assert(false);
}

inline _mlsValue _mlsValue::operator<=(const _mlsValue &other) const {
  if (isInt63() && other.isInt63())
    return leInt63(other);
  if (isFloat() && other.isFloat())
    return *as<_mls_Float>(*this) <= *as<_mls_Float>(other);
  _mls_assert(false);
}

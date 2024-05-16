#include "mlsprelude.h"
struct _mls_Nat;
struct _mls_Boolean;
struct _mls_Z;
struct _mls_S;
struct _mls_True;
struct _mls_False;
struct _mls_fib;
struct _mls_main;
struct _mls_to_nat;
struct _mls_j_5;
struct _mls_j_3;
struct _mls_to_int;
struct _mls_pred;
struct _mls_plus;
struct _mls_j_4;
struct _mls_j_1;
struct _mls_j_0;
struct _mls_j_2;
_mlsValue _mls_pred(_mlsValue);
_mlsValue _mls_fib(_mlsValue);
_mlsValue _mls_j_5(_mlsValue);
_mlsValue _mls_j_2(_mlsValue);
_mlsValue _mls_j_3(_mlsValue);
_mlsValue _mls_main();
_mlsValue _mls_j_1(_mlsValue);
_mlsValue _mls_j_4(_mlsValue);
_mlsValue _mls_j_0(_mlsValue);
_mlsValue _mls_to_nat(_mlsValue);
_mlsValue _mls_to_int(_mlsValue);
_mlsValue _mls_plus(_mlsValue, _mlsValue);
_mlsValue _mlsMain();
struct _mls_Nat: public _mlsObject {

  constexpr static inline const char *typeName = "Nat";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_Nat; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_Z: public _mls_Nat {

  constexpr static inline const char *typeName = "Z";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_Z; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_S: public _mls_Nat {
  _mlsValue _mls_x;
  constexpr static inline const char *typeName = "S";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_x.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_x);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create(_mlsValue _mls_x) { auto _mlsVal = new (std::align_val_t(align)) _mls_S; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_x = _mls_x;  return _mlsValue(_mlsVal); }
};
struct _mlsFn__mls_j_1: public _mlsCallable {

  constexpr static inline const char *typeName = "<j$1>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_j_1 mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_j_1(arg0);
  }
};
struct _mlsFn__mls_fib: public _mlsCallable {

  constexpr static inline const char *typeName = "<fib>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_fib mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_fib(arg0);
  }
};
struct _mlsFn__mls_to_nat: public _mlsCallable {

  constexpr static inline const char *typeName = "<to_nat>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_to_nat mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_to_nat(arg0);
  }
};
struct _mlsFn__mls_j_5: public _mlsCallable {

  constexpr static inline const char *typeName = "<j$5>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_j_5 mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_j_5(arg0);
  }
};
struct _mlsFn__mls_pred: public _mlsCallable {

  constexpr static inline const char *typeName = "<pred>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_pred mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_pred(arg0);
  }
};
struct _mlsFn__mls_plus: public _mlsCallable {

  constexpr static inline const char *typeName = "<plus>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_plus mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply2(_mlsValue arg0, _mlsValue arg1) override{
    return _mls_plus(arg0, arg1);
  }
};
struct _mlsFn__mls_j_2: public _mlsCallable {

  constexpr static inline const char *typeName = "<j$2>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_j_2 mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_j_2(arg0);
  }
};
struct _mlsFn__mls_j_4: public _mlsCallable {

  constexpr static inline const char *typeName = "<j$4>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_j_4 mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_j_4(arg0);
  }
};
struct _mlsFn__mls_to_int: public _mlsCallable {

  constexpr static inline const char *typeName = "<to_int>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_to_int mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_to_int(arg0);
  }
};
struct _mlsFn__mls_main: public _mlsCallable {

  constexpr static inline const char *typeName = "<main>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_main mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply0() override{
    return _mls_main();
  }
};
struct _mlsFn__mls_j_3: public _mlsCallable {

  constexpr static inline const char *typeName = "<j$3>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_j_3 mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_j_3(arg0);
  }
};
struct _mlsFn__mls_j_0: public _mlsCallable {

  constexpr static inline const char *typeName = "<j$0>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_j_0 mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_j_0(arg0);
  }
};
_mlsValue _mls_to_int(_mlsValue _mls_n_2){
  _mlsValue _mls_retval;
  if (_mlsValue::isValueOf<_mls_Z>(_mls_n_2)){
    _mls_retval = _mls_j_4(_mlsValue::fromIntLit(0));
  } else if (_mlsValue::isValueOf<_mls_S>(_mls_n_2)){
    auto _mls_x_19 = _mlsValue::cast<_mls_S>(_mls_n_2)->_mls_x;
    auto _mls_x_20 = _mls_to_int(_mls_x_19);
    auto _mls_x_21 = (_mlsValue::fromIntLit(1)+_mls_x_20);
    _mls_retval = _mls_j_4(_mls_x_21);
  } else _mlsNonExhaustiveMatch();
  return _mls_retval;
}
_mlsValue _mls_j_0(_mlsValue _mls_x_0){
  _mlsValue _mls_retval;
  _mls_retval = _mls_x_0;
  return _mls_retval;
}
_mlsValue _mls_j_2(_mlsValue _mls_x_7){
  _mlsValue _mls_retval;
  _mls_retval = _mls_x_7;
  return _mls_retval;
}
_mlsValue _mls_j_1(_mlsValue _mls_x_3){
  _mlsValue _mls_retval;
  _mls_retval = _mls_x_3;
  return _mls_retval;
}
_mlsValue _mls_to_nat(_mlsValue _mls_n_3){
  _mlsValue _mls_retval;
  auto _mls_x_22 = (_mls_n_3==_mlsValue::fromIntLit(0));
  if (_mlsValue::isValueOf<_mls_True>(_mls_x_22)){
    auto _mls_x_24 = _mlsValue::create<_mls_Z>();
    _mls_retval = _mls_j_5(_mls_x_24);
  } else if (_mlsValue::isValueOf<_mls_False>(_mls_x_22)){
    auto _mls_x_25 = (_mls_n_3-_mlsValue::fromIntLit(1));
    auto _mls_x_26 = _mls_to_nat(_mls_x_25);
    auto _mls_x_27 = _mlsValue::create<_mls_S>(_mls_x_26);
    _mls_retval = _mls_j_5(_mls_x_27);
  } else _mlsNonExhaustiveMatch();
  return _mls_retval;
}
_mlsValue _mls_j_3(_mlsValue _mls_x_11){
  _mlsValue _mls_retval;
  _mls_retval = _mls_j_2(_mls_x_11);
  return _mls_retval;
}
_mlsValue _mls_j_5(_mlsValue _mls_x_23){
  _mlsValue _mls_retval;
  _mls_retval = _mls_x_23;
  return _mls_retval;
}
_mlsValue _mls_main(){
  _mlsValue _mls_retval;
  auto _mls_x_28 = _mls_to_nat(_mlsValue::fromIntLit(30));
  auto _mls_x_29 = _mls_fib(_mls_x_28);
  auto _mls_x_30 = _mls_to_int(_mls_x_29);
  _mls_retval = _mls_x_30;
  return _mls_retval;
}
_mlsValue _mls_j_4(_mlsValue _mls_x_18){
  _mlsValue _mls_retval;
  _mls_retval = _mls_x_18;
  return _mls_retval;
}
_mlsValue _mls_fib(_mlsValue _mls_n_1){
  _mlsValue _mls_retval;
  if (_mlsValue::isValueOf<_mls_Z>(_mls_n_1)){
    auto _mls_x_8 = _mlsValue::create<_mls_Z>();
    auto _mls_x_9 = _mlsValue::create<_mls_S>(_mls_x_8);
    _mls_retval = _mls_j_2(_mls_x_9);
  } else if (_mlsValue::isValueOf<_mls_S>(_mls_n_1)){
    auto _mls_x_10 = _mlsValue::cast<_mls_S>(_mls_n_1)->_mls_x;
    if (_mlsValue::isValueOf<_mls_Z>(_mls_x_10)){
      auto _mls_x_12 = _mlsValue::create<_mls_Z>();
      auto _mls_x_13 = _mlsValue::create<_mls_S>(_mls_x_12);
      _mls_retval = _mls_j_3(_mls_x_13);
    } else if (_mlsValue::isValueOf<_mls_S>(_mls_x_10)){
      auto _mls_x_14 = _mlsValue::cast<_mls_S>(_mls_x_10)->_mls_x;
      auto _mls_x_15 = _mls_fib(_mls_x_10);
      auto _mls_x_16 = _mls_fib(_mls_x_14);
      auto _mls_x_17 = _mls_plus(_mls_x_15, _mls_x_16);
      _mls_retval = _mls_j_3(_mls_x_17);
    } else _mlsNonExhaustiveMatch();
  } else _mlsNonExhaustiveMatch();
  return _mls_retval;
}
_mlsValue _mls_pred(_mlsValue _mls_n_0){
  _mlsValue _mls_retval;
  if (_mlsValue::isValueOf<_mls_S>(_mls_n_0)){
    auto _mls_x_1 = _mlsValue::cast<_mls_S>(_mls_n_0)->_mls_x;
    _mls_retval = _mls_j_0(_mls_x_1);
  } else if (_mlsValue::isValueOf<_mls_Z>(_mls_n_0)){
    auto _mls_x_2 = _mlsValue::create<_mls_Z>();
    _mls_retval = _mls_j_0(_mls_x_2);
  } else _mlsNonExhaustiveMatch();
  return _mls_retval;
}
_mlsValue _mls_plus(_mlsValue _mls_n1_0, _mlsValue _mls_n2_0){
  _mlsValue _mls_retval;
  if (_mlsValue::isValueOf<_mls_Z>(_mls_n1_0)){
    _mls_retval = _mls_j_1(_mls_n2_0);
  } else if (_mlsValue::isValueOf<_mls_S>(_mls_n1_0)){
    auto _mls_x_4 = _mlsValue::cast<_mls_S>(_mls_n1_0)->_mls_x;
    auto _mls_x_5 = _mls_plus(_mls_x_4, _mls_n2_0);
    auto _mls_x_6 = _mlsValue::create<_mls_S>(_mls_x_5);
    _mls_retval = _mls_j_1(_mls_x_6);
  } else _mlsNonExhaustiveMatch();
  return _mls_retval;
}
_mlsValue _mlsMain(){
  _mlsValue _mls_retval;
  auto _mls_x_31 = _mls_main();
  _mls_retval = _mls_x_31;
  return _mls_retval;
}
int main() { auto res = _mlsMain(); res.print(); }

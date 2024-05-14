
#include "mlsprelude.h"
struct _mls_Box;
struct _mls_Option;
struct _mls_List;
struct _mls_Some;
struct _mls_None;
struct _mls_Nil;
struct _mls_Cons;
struct _mls_map;
struct _mls_inc;
struct _mls_testMap;
struct _mls_j_0;
_mlsValue _mls_map(_mlsValue, _mlsValue);
_mlsValue _mls_inc(_mlsValue);
_mlsValue _mls_testMap();
_mlsValue _mls_j_0(_mlsValue);
_mlsValue _mlsMain();
struct _mls_Box: public _mlsObject {
  _mlsValue _mls_inner;
  constexpr static inline const char *typeName = "Box";
  constexpr static inline uint32_t typeTag = 6;
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_inner.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_inner);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create(_mlsValue _mls_inner) { auto _mlsVal = new (std::align_val_t(align)) _mls_Box; _mlsVal->refCount = 1; _mlsVal->tag = 6; _mlsVal->_mls_inner = _mls_inner;  return _mlsValue(_mlsVal); }
};
struct _mls_Option: public _mlsObject {

  constexpr static inline const char *typeName = "Option";
  constexpr static inline uint32_t typeTag = 3;
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_Option; _mlsVal->refCount = 1; _mlsVal->tag = 3;  return _mlsValue(_mlsVal); }
};
struct _mls_List: public _mlsObject {

  constexpr static inline const char *typeName = "List";
  constexpr static inline uint32_t typeTag = 0;
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_List; _mlsVal->refCount = 1; _mlsVal->tag = 0;  return _mlsValue(_mlsVal); }
};
struct _mls_Some: public _mls_Option {
  _mlsValue _mls_x;
  constexpr static inline const char *typeName = "Some";
  constexpr static inline uint32_t typeTag = 4;
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_x.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_x);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create(_mlsValue _mls_x) { auto _mlsVal = new (std::align_val_t(align)) _mls_Some; _mlsVal->refCount = 1; _mlsVal->tag = 4; _mlsVal->_mls_x = _mls_x;  return _mlsValue(_mlsVal); }
};
struct _mls_None: public _mls_Option {

  constexpr static inline const char *typeName = "None";
  constexpr static inline uint32_t typeTag = 5;
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_None; _mlsVal->refCount = 1; _mlsVal->tag = 5;  return _mlsValue(_mlsVal); }
};
struct _mls_Nil: public _mls_List {

  constexpr static inline const char *typeName = "Nil";
  constexpr static inline uint32_t typeTag = 2;
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_Nil; _mlsVal->refCount = 1; _mlsVal->tag = 2;  return _mlsValue(_mlsVal); }
};
struct _mls_Cons: public _mls_List {
  _mlsValue _mls_h;
  _mlsValue _mls_t;
  constexpr static inline const char *typeName = "Cons";
  constexpr static inline uint32_t typeTag = 1;
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_h.print(); std::printf(", "); this->_mls_t.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_h); _mlsValue::destroy(this->_mls_t);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create(_mlsValue _mls_h, _mlsValue _mls_t) { auto _mlsVal = new (std::align_val_t(align)) _mls_Cons; _mlsVal->refCount = 1; _mlsVal->tag = 1; _mlsVal->_mls_h = _mls_h; _mlsVal->_mls_t = _mls_t;  return _mlsValue(_mlsVal); }
};
struct _mlsFn__mls_map: public _mlsCallable {

  constexpr static inline const char *typeName = "<map>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_map mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply2(_mlsValue arg0, _mlsValue arg1) override{
    return _mls_map(arg0, arg1);
  }
};
struct _mlsFn__mls_inc: public _mlsCallable {

  constexpr static inline const char *typeName = "<inc>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_inc mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_inc(arg0);
  }
};
struct _mlsFn__mls_testMap: public _mlsCallable {

  constexpr static inline const char *typeName = "<testMap>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_testMap mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply0() override{
    return _mls_testMap();
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
_mlsValue _mls_map(_mlsValue _mls_f_0, _mlsValue _mls_xs_0){
  _mlsValue _mls_retval;
  if (_mlsValue::isValueOf<_mls_Nil>(_mls_xs_0)){
    auto _mls_x_1 = _mlsValue::create<_mls_Nil>();
    _mls_retval = _mls_j_0(_mls_x_1);
  } else if (_mlsValue::isValueOf<_mls_Cons>(_mls_xs_0)){
    auto _mls_x_2 = _mlsValue::as<_mls_Cons>(_mls_xs_0)->_mls_t;
    auto _mls_x_3 = _mlsValue::as<_mls_Cons>(_mls_xs_0)->_mls_h;
    auto _mls_x_4 = _mlsValue::as<_mls_Box>(_mls_f_0)->_mls_inner;
    auto _mls_x_5 = _mlsCall(_mls_x_4, _mls_x_3);
    auto _mls_x_6 = _mls_map(_mls_f_0, _mls_x_2);
    auto _mls_x_7 = _mlsValue::create<_mls_Cons>(_mls_x_5, _mls_x_6);
    _mls_retval = _mls_j_0(_mls_x_7);
  } else throw std::runtime_error("Non-exhaustive match");
  return _mls_retval;
}
_mlsValue _mls_inc(_mlsValue _mls_x_8){
  _mlsValue _mls_retval;
  auto _mls_x_9 = (_mls_x_8+_mlsValue::fromIntLit(1));
  _mls_retval = _mls_x_9;
  return _mls_retval;
}
_mlsValue _mls_testMap(){
  _mlsValue _mls_retval;
  auto _mls_x_10 = _mlsValue::create<_mls_Nil>();
  auto _mls_x_11 = _mlsValue::create<_mls_Cons>(_mlsValue::fromIntLit(2), _mls_x_10);
  auto _mls_x_12 = _mlsValue::create<_mls_Cons>(_mlsValue::fromIntLit(1), _mls_x_11);
  auto _mls_x_13 = _mlsValue::create<_mls_Box>(_mlsValue::create<_mlsFn__mls_inc>());
  auto _mls_x_14 = _mls_map(_mls_x_13, _mls_x_12);
  _mls_retval = _mls_x_14;
  return _mls_retval;
}
_mlsValue _mls_j_0(_mlsValue _mls_x_0){
  _mlsValue _mls_retval;
  _mls_retval = _mls_x_0;
  return _mls_retval;
}
_mlsValue _mlsMain(){
  _mlsValue _mls_retval;
  auto _mls_x_15 = _mls_testMap();
  _mls_retval = _mls_x_15;
  return _mls_retval;
}
int main() { auto res = _mlsMain(); res.print(); }
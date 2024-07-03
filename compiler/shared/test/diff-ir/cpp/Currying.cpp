#include "mlsprelude.h"
struct _mls_Option;
struct _mls_Some;
struct _mls_None;
struct _mls_List;
struct _mls_Nil;
struct _mls_Cons;
struct _mls_Callable;
struct _mls_Lambda_0;
struct _mls_Lambda_2;
struct _mls_Lambda_1;
struct _mls_True;
struct _mls_False;
_mlsValue _mls_add2c(_mlsValue);
_mlsValue _mls_add2(_mlsValue, _mlsValue);
_mlsValue _mls_add3c(_mlsValue);
_mlsValue _mls_main();
_mlsValue _mlsMain();
struct _mls_Option: public _mlsObject {

  constexpr static inline const char *typeName = "Option";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create() { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Option; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_Some: public _mls_Option {
  _mlsValue _mls_x;
  constexpr static inline const char *typeName = "Some";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_x.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_x);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create(_mlsValue _mls_x) { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Some; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_x = _mls_x;  return _mlsValue(_mlsVal); }
};
struct _mls_None: public _mls_Option {

  constexpr static inline const char *typeName = "None";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create() { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_None; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_List: public _mlsObject {

  constexpr static inline const char *typeName = "List";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create() { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_List; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_Nil: public _mls_List {

  constexpr static inline const char *typeName = "Nil";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create() { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Nil; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_Cons: public _mls_List {
  _mlsValue _mls_h;
  _mlsValue _mls_t;
  constexpr static inline const char *typeName = "Cons";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_h.print(); std::printf(", "); this->_mls_t.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_h); _mlsValue::destroy(this->_mls_t);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create(_mlsValue _mls_h, _mlsValue _mls_t) { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Cons; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_h = _mls_h; _mlsVal->_mls_t = _mls_t;  return _mlsValue(_mlsVal); }
};
struct _mls_Lambda_0: public _mls_Callable {
  _mlsValue _mls_a;
  constexpr static inline const char *typeName = "Lambda$0";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_a.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_a);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create(_mlsValue _mls_a) { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Lambda_0; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_a = _mls_a;  return _mlsValue(_mlsVal); }
  virtual _mlsValue _mls_apply1(_mlsValue _mls_b_0){
    _mlsValue _mls_retval;
    auto _mls_x_2 = (_mls_a+_mls_b_0);
    _mls_retval = _mls_x_2;
    return _mls_retval;
  }
};
struct _mls_Lambda_2: public _mls_Callable {
  _mlsValue _mls_a;
  _mlsValue _mls_b;
  constexpr static inline const char *typeName = "Lambda$2";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_a.print(); std::printf(", "); this->_mls_b.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_a); _mlsValue::destroy(this->_mls_b);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create(_mlsValue _mls_a, _mlsValue _mls_b) { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Lambda_2; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_a = _mls_a; _mlsVal->_mls_b = _mls_b;  return _mlsValue(_mlsVal); }
  virtual _mlsValue _mls_apply1(_mlsValue _mls_c_0){
    _mlsValue _mls_retval;
    auto _mls_x_9 = (_mls_a+_mls_b);
    auto _mls_x_10 = (_mls_x_9+_mls_c_0);
    _mls_retval = _mls_x_10;
    return _mls_retval;
  }
};
struct _mls_Lambda_1: public _mls_Callable {
  _mlsValue _mls_a;
  constexpr static inline const char *typeName = "Lambda$1";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_a.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_a);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  static _mlsValue create(_mlsValue _mls_a) { auto _mlsVal = new (std::align_val_t(_mlsAlignment)) _mls_Lambda_1; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_a = _mls_a;  return _mlsValue(_mlsVal); }
  virtual _mlsValue _mls_apply1(_mlsValue _mls_b_2){
    _mlsValue _mls_retval;
    auto _mls_x_11 = _mlsValue::create<_mls_Lambda_2>(_mls_a, _mls_b_2);
    _mls_retval = _mls_x_11;
    return _mls_retval;
  }
};
_mlsValue _mls_add2c(_mlsValue _mls_a_0){
  _mlsValue _mls_retval;
  auto _mls_x_3 = _mlsValue::create<_mls_Lambda_0>(_mls_a_0);
  _mls_retval = _mls_x_3;
  return _mls_retval;
}
_mlsValue _mls_add2(_mlsValue _mls_a_1, _mlsValue _mls_b_1){
  _mlsValue _mls_retval;
  auto _mls_x_4 = (_mls_a_1+_mls_b_1);
  _mls_retval = _mls_x_4;
  return _mls_retval;
}
_mlsValue _mls_add3c(_mlsValue _mls_a_2){
  _mlsValue _mls_retval;
  auto _mls_x_12 = _mlsValue::create<_mls_Lambda_1>(_mls_a_2);
  _mls_retval = _mls_x_12;
  return _mls_retval;
}
_mlsValue _mls_main(){
  _mlsValue _mls_retval;
  auto _mls_x_13 = _mls_add2c(_mlsValue::fromIntLit(1));
  auto _mls_x_14 = _mlsCall(_mls_x_13, _mlsValue::fromIntLit(2));
  auto _mls_x_15 = _mls_add2(_mlsValue::fromIntLit(1), _mlsValue::fromIntLit(2));
  auto _mls_x_16 = _mls_add3c(_mlsValue::fromIntLit(1));
  auto _mls_x_17 = _mlsCall(_mls_x_16, _mlsValue::fromIntLit(2));
  auto _mls_x_18 = _mlsCall(_mls_x_17, _mlsValue::fromIntLit(3));
  _mls_retval = _mls_x_18;
  return _mls_retval;
}
_mlsValue _mlsMain(){
  _mlsValue _mls_retval;
  auto _mls_x_19 = _mls_main();
  _mls_retval = _mls_x_19;
  return _mls_retval;
}
int main() { return _mlsLargeStack(_mlsMainWrapper); }

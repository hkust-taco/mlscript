#include "mlsprelude.h"
struct _mls_Base;
struct _mls_Child;
struct _mls_Option;
struct _mls_Some;
struct _mls_None;
struct _mls_List;
struct _mls_Nil;
struct _mls_Cons;
struct _mls_Callable;
struct _mls_True;
struct _mls_False;
_mlsValue _mls_main();
_mlsValue _mlsMain();
struct _mls_Base: public _mlsObject {

  constexpr static inline const char *typeName = "Base";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_Base; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
  virtual _mlsValue _mls_f(){
    _mlsValue _mls_retval;
    _mls_retval = _mlsValue::fromIntLit(1);
    return _mls_retval;
  }
};
struct _mls_Child: public _mls_Base {

  constexpr static inline const char *typeName = "Child";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_Child; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
  virtual _mlsValue _mls_f(){
    _mlsValue _mls_retval;
    _mls_retval = _mlsValue::fromIntLit(2);
    return _mls_retval;
  }
};
struct _mls_Option: public _mlsObject {

  constexpr static inline const char *typeName = "Option";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_Option; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_Some: public _mls_Option {
  _mlsValue _mls_x;
  constexpr static inline const char *typeName = "Some";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_x.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_x);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create(_mlsValue _mls_x) { auto _mlsVal = new (std::align_val_t(align)) _mls_Some; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_x = _mls_x;  return _mlsValue(_mlsVal); }
};
struct _mls_None: public _mls_Option {

  constexpr static inline const char *typeName = "None";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_None; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_List: public _mlsObject {

  constexpr static inline const char *typeName = "List";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_List; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_Nil: public _mls_List {

  constexpr static inline const char *typeName = "Nil";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); }
  virtual void destroy() override {  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create() { auto _mlsVal = new (std::align_val_t(align)) _mls_Nil; _mlsVal->refCount = 1; _mlsVal->tag = typeTag;  return _mlsValue(_mlsVal); }
};
struct _mls_Cons: public _mls_List {
  _mlsValue _mls_h;
  _mlsValue _mls_t;
  constexpr static inline const char *typeName = "Cons";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_h.print(); std::printf(", "); this->_mls_t.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_h); _mlsValue::destroy(this->_mls_t);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create(_mlsValue _mls_h, _mlsValue _mls_t) { auto _mlsVal = new (std::align_val_t(align)) _mls_Cons; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_h = _mls_h; _mlsVal->_mls_t = _mls_t;  return _mlsValue(_mlsVal); }
};
_mlsValue _mls_main(){
  _mlsValue _mls_retval;
  auto _mls_x_0 = _mlsValue::create<_mls_Child>();
  auto _mls_x_1 = _mlsMethodCall<_mls_Base>(_mls_x_0)->_mls_f();
  _mls_retval = _mls_x_1;
  return _mls_retval;
}
_mlsValue _mlsMain(){
  _mlsValue _mls_retval;
  auto _mls_x_2 = _mls_main();
  _mls_retval = _mls_x_2;
  return _mls_retval;
}
int main() { return _mlsLargeStack(_mlsMainWrapper); }

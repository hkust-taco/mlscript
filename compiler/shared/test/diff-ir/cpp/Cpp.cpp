#include "mlsprelude.h"
struct _mls_Box;
struct _mls_unbox;
struct _mls_f;
_mlsValue _mls_unbox(_mlsValue);
_mlsValue _mls_f();
_mlsValue _mlsMain();
struct _mls_Box: public _mlsObject {
  _mlsValue _mls_inner;
  constexpr static inline const char *typeName = "Box";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_inner.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_inner);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create(_mlsValue _mls_inner) { auto _mlsVal = new (std::align_val_t(align)) _mls_Box; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_inner = _mls_inner;  return _mlsValue(_mlsVal); }
};
struct _mlsFn__mls_unbox: public _mlsCallable {

  constexpr static inline const char *typeName = "<unbox>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_unbox mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply1(_mlsValue arg0) override{
    return _mls_unbox(arg0);
  }
};
struct _mlsFn__mls_f: public _mlsCallable {

  constexpr static inline const char *typeName = "<f>";
  constexpr static inline uint32_t typeTag = -1;
  virtual void print() const override { std::printf("%s", typeName); }
  template <std::size_t align> static _mlsValue create() { static _mlsFn__mls_f mlsFn alignas(align); mlsFn.refCount = stickyRefCount; mlsFn.tag = typeTag; return _mlsValue(&mlsFn); }
  _mlsValue virtual apply0() override{
    return _mls_f();
  }
};
_mlsValue _mls_unbox(_mlsValue _mls_x_0){
  _mlsValue _mls_retval;
  auto _mls_x_1 = _mlsValue::cast<_mls_Box>(_mls_x_0)->_mls_inner;
  _mls_retval = _mls_x_1;
  return _mls_retval;
}
_mlsValue _mls_f(){
  _mlsValue _mls_retval;
  auto _mls_x_2 = _mlsValue::create<_mls_Box>(_mlsValue::fromIntLit(1));
  auto _mls_x_3 = _mls_unbox(_mls_x_2);
  auto _mls_x_4 = (_mls_x_3+_mlsValue::fromIntLit(1));
  _mls_retval = _mls_x_4;
  return _mls_retval;
}
_mlsValue _mlsMain(){
  _mlsValue _mls_retval;
  auto _mls_x_5 = _mls_f();
  _mls_retval = _mls_x_5;
  return _mls_retval;
}
int main() { auto res = _mlsMain(); res.print(); }

#include "mlsprelude.h"
struct _mls_Callable;
struct _mls_Lambda_0;
_mlsValue _mls_add_y(_mlsValue);
_mlsValue _mls_add_z(_mlsValue, _mlsValue);
_mlsValue _mls_main();
_mlsValue _mlsMain();
struct _mls_Lambda_0: public _mls_Callable {
  _mlsValue _mls_a;
  constexpr static inline const char *typeName = "Lambda$0";
  constexpr static inline uint32_t typeTag = nextTypeTag();
  virtual void print() const override { std::printf("%s", typeName); std::printf("("); this->_mls_a.print();  std::printf(")"); }
  virtual void destroy() override { _mlsValue::destroy(this->_mls_a);  operator delete (this, std::align_val_t(_mlsAlignment)); }
  template <std::size_t align> static _mlsValue create(_mlsValue _mls_a) { auto _mlsVal = new (std::align_val_t(align)) _mls_Lambda_0; _mlsVal->refCount = 1; _mlsVal->tag = typeTag; _mlsVal->_mls_a = _mls_a;  return _mlsValue(_mlsVal); }
  _mlsValue _mls_apply1(_mlsValue _mls_b_0) override{
    _mlsValue _mls_retval;
    auto _mls_x_2 = (_mls_a+_mls_b_0);
    _mls_retval = _mls_x_2;
    return _mls_retval;
  }
};
_mlsValue _mls_add_y(_mlsValue _mls_a_0){
  _mlsValue _mls_retval;
  auto _mls_x_3 = _mlsValue::create<_mls_Lambda_0>(_mls_a_0);
  _mls_retval = _mls_x_3;
  return _mls_retval;
}
_mlsValue _mls_add_z(_mlsValue _mls_a_1, _mlsValue _mls_b_1){
  _mlsValue _mls_retval;
  auto _mls_x_4 = (_mls_a_1+_mls_b_1);
  _mls_retval = _mls_x_4;
  return _mls_retval;
}
_mlsValue _mls_main(){
  _mlsValue _mls_retval;
  auto _mls_x_5 = _mls_add_y(_mlsValue::fromIntLit(1));
  auto _mls_x_6 = _mlsCall(_mls_x_5, _mlsValue::fromIntLit(2));
  auto _mls_x_7 = _mls_add_z(_mlsValue::fromIntLit(1), _mlsValue::fromIntLit(2));
  _mls_retval = _mls_x_7;
  return _mls_retval;
}
_mlsValue _mlsMain(){
  _mlsValue _mls_retval;
  auto _mls_x_8 = _mls_main();
  _mls_retval = _mls_x_8;
  return _mls_retval;
}
int main() { return _mlsLargeStack(_mlsMainWrapper); }

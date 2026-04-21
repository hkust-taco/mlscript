(module
  (type $Object (sub (struct (field $$tag (mut i32)))))
  (type $plus_impl (func (param $lhs (ref null any)) (param $rhs (ref null any)) (result (ref null any))))
  (type $entry1 (func (result (ref null any))))
  (import "system" "plus_impl" (func $plus_impl (type $plus_impl)))
  (func $entry (export "entry") (type $entry1) (result (ref null any))
    (call $plus_impl
      (ref.i31
        (i32.const 40))
      (ref.i31
        (i32.const 2))))
  (elem $entry declare func $entry))
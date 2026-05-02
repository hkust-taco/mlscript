(module
  (type $Object (sub (struct (field $$tag (mut i32)))))
  (type $SimpleTarget (sub $Object (struct (field $$tag (mut i32)))))
  (type $SimpleTarget_init (func (param $this (ref null any)) (result (ref null any))))
  (type $SimpleTarget_ctor (func (result (ref null any))))
  (type $Unit (sub $Object (struct (field $$tag (mut i32)))))
  (type $Unit_init (func (param $this (ref null any)) (result (ref null any))))
  (type $Unit_ctor (func (result (ref null any))))
  (type $entry1 (func (result (ref null any))))
  (type $start (func))
  (global $Unit$inst (export "Unit$inst") (mut (ref null $Unit)) (ref.null $Unit))
  (func $SimpleTarget_init (type $SimpleTarget_init) (param $this (ref null any)) (result (ref null any))
    (block (result (ref null any))
      (nop)
      (nop)
      (return
        (local.get $this))))
  (func $SimpleTarget_ctor (export "SimpleTarget") (type $SimpleTarget_ctor) (result (ref null any))
    (local $this (ref null any))
    (block (result (ref null any))
      (local.set $this
        (struct.new_default $SimpleTarget))
      (struct.set $SimpleTarget $$tag
        (ref.cast (ref $SimpleTarget)
          (local.get $this))
        (i32.const 1))
      (drop
        (call $SimpleTarget_init
          (local.get $this)))
      (return
        (local.get $this))))
  (func $Unit_init (export "Unit_init") (type $Unit_init) (param $this (ref null any)) (result (ref null any))
    (block (result (ref null any))
      (nop)
      (nop)
      (return
        (local.get $this))))
  (func $Unit_ctor (export "Unit_ctor") (type $Unit_ctor) (result (ref null any))
    (local $this (ref null any))
    (block (result (ref null any))
      (local.set $this
        (struct.new_default $Unit))
      (struct.set $Unit $$tag
        (ref.cast (ref $Unit)
          (local.get $this))
        (i32.const 2))
      (drop
        (call $Unit_init
          (local.get $this)))
      (return
        (local.get $this))))
  (func $start1 (type $start)
    (block
      (global.set $Unit$inst
        (ref.cast (ref null $Unit)
          (call $Unit_ctor)))))
  (func $entry (export "entry") (type $entry1) (result (ref null any))
    (block (result (ref null any))
      (block
        (nop)
        (nop))
      (global.get $Unit$inst)))
  (elem $SimpleTarget_init declare func $SimpleTarget_init)
  (elem $SimpleTarget_ctor declare func $SimpleTarget_ctor)
  (elem $Unit_init declare func $Unit_init)
  (elem $Unit_ctor declare func $Unit_ctor)
  (elem $start1 declare func $start1)
  (elem $entry declare func $entry)
  (start $start1))
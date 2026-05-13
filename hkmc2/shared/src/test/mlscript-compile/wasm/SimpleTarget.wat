(module
  (type $TypeInfoBase (sub (struct (field $$tag i32) (field $$parent (ref null $TypeInfoBase)))))
  (type $Object (sub (struct (field $$typeinfo (mut (ref $TypeInfoBase))))))
  (type $SimpleTarget_typeinfo (sub $TypeInfoBase (struct (field $$tag i32) (field $$parent (ref null $TypeInfoBase)))))
  (type $SimpleTarget (sub $Object (struct (field $$typeinfo (mut (ref $TypeInfoBase))))))
  (type $SimpleTarget_init (func (param $this (ref null any)) (result (ref null any))))
  (type $SimpleTarget_ctor (func (result (ref null any))))
  (type $Unit_typeinfo (sub $TypeInfoBase (struct (field $$tag i32) (field $$parent (ref null $TypeInfoBase)))))
  (type $Unit (sub $Object (struct (field $$typeinfo (mut (ref $TypeInfoBase))))))
  (type $Unit_init (func (param $this (ref null any)) (result (ref null any))))
  (type $Unit_ctor (func (result (ref null any))))
  (type $entry (func (result (ref null any))))
  (type $start (func))
  (global $SimpleTarget_typeinfo (export "SimpleTarget_typeinfo") (ref $SimpleTarget_typeinfo) (struct.new $SimpleTarget_typeinfo
    (i32.const 1)
    (ref.null $TypeInfoBase)))
  (global $Unit_typeinfo (export "Unit_typeinfo") (ref $Unit_typeinfo) (struct.new $Unit_typeinfo
    (i32.const 2)
    (ref.null $TypeInfoBase)))
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
        (struct.new $SimpleTarget
          (global.get $SimpleTarget_typeinfo)))
      (drop
        (call $SimpleTarget_init
          (local.get $this)))
      (return
        (local.get $this))))
  (func $Unit_init (type $Unit_init) (param $this (ref null any)) (result (ref null any))
    (block (result (ref null any))
      (nop)
      (nop)
      (return
        (local.get $this))))
  (func $Unit_Unit (export "Unit_ctor") (type $Unit_ctor) (result (ref null any))
    (local $this (ref null any))
    (block (result (ref null any))
      (local.set $this
        (struct.new $Unit
          (global.get $Unit_typeinfo)))
      (drop
        (call $Unit_init
          (local.get $this)))
      (return
        (local.get $this))))
  (func $start (type $start)
    (block
      (global.set $Unit$inst
        (ref.cast (ref null $Unit)
          (call $Unit_Unit)))))
  (func $entry (export "entry") (type $entry) (result (ref null any))
    (block (result (ref null any))
      (block
        (nop)
        (nop))
      (global.get $Unit$inst)))
  (elem $SimpleTarget_init declare func $SimpleTarget_init)
  (elem $SimpleTarget_ctor declare func $SimpleTarget_ctor)
  (elem $Unit_init declare func $Unit_init)
  (elem $Unit_Unit declare func $Unit_Unit)
  (elem $start declare func $start)
  (elem $entry declare func $entry)
  (start $start))
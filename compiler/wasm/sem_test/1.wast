(module

(import "host" "print" (func $print (param i32)))

(func $f (param $a i32) (param $b i32) (result i32 i32)
  (local.get $a)
  (local.get $b)
  (i32.add)
  (local.get $a)
  (local.get $b)
  (i32.sub)
)

(func $start
  (i32.const 4)
  (i32.const 3)
  (call $f)
  (call $print) ;; => 1
  (call $print) ;; => 7
)

(start $start)

)

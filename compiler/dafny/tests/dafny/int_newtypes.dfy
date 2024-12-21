// Adapted from GeneralNewtypes.dfy (Dafny integration test)
module Numerics {
  newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  newtype j32 = i32

  newtype k32 = j: j32 | true

  newtype nn = x: int | 0 <= x
  newtype byte = n: nn | n < 256

  method Test() {
    var i: i32 := 100;
    var j: j32 := 100;

    print i, " ", j, "\n"; // 100 100
    print i == i, " ", j == j, "\n"; // true true
    print i == j as i32, " ", i as j32 == j, "\n"; // true true
    print i as int == j as int, "\n"; // true

    var k: k32 := 99;
    var n: nn := 99;
    var b: byte := 99;

    print k, " ", n, " ", b, "\n"; // 99 99
    print k == k, " ", n == n, " ", b == b, "\n"; // true true true
    print k == n as k32, " ", n == b as nn, " ", b == k as byte, "\n"; // true true true
  }
}

method Main() {
	Numerics.Test();
}

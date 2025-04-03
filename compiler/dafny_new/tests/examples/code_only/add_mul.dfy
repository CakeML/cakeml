// Adapted from Dafny (MIT License): https://github.com/dafny-lang/dafny

method Add(x: int, y: int) returns (r: int)
{
  r := x;
  if (y < 0) {
    var n := y;
    while (n != 0)
    {
      r := r - 1;
      n := n + 1;
    }
  } else {
    var n := y;
    while (n != 0)
    {
      r := r + 1;
      n := n - 1;
    }
  }
}

method Mul(x: int, y: int) returns (r: int)
{
  if (x == 0) {
    r := 0;
  } else if (x < 0) {
    r := Mul(-x, y);
    r := -r;
  } else {
    r := Mul(x-1, y);
    r := Add(r, y);
  }
}

// ---------------------------

method Main() {
  TestAdd(3, 180);
  TestAdd(3, -180);
  TestAdd(0, 1);

  TestMul(3, 180);
  TestMul(3, -180);
  TestMul(180, 3);
  TestMul(-180, 3);
  TestMul(0, 1);
  TestMul(1, 0);
}

method TestAdd(x: int, y: int) {
  print x, " + ", y, " = ";
  var z := Add(x, y);
  print z, "\n";
}

method TestMul(x: int, y: int) {
  print x, " * ", y, " = ";
  var z := Mul(x, y);
  print z, "\n";
}
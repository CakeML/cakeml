// Extended https://dafny.org/dafny/OnlineTutorial/guide

method Abs(x: int) returns (y: int)
  ensures 0 <= y && (y == x || y == -x)
{
  if x < 0 {
    return -x;
  } else {
    return x;
  }
}

method Main() {
  TestAbs(-5);
  TestAbs(-1);
  TestAbs(0);
  TestAbs(1);
  TestAbs(7);
}

method TestAbs(x: int)
{
  var r := Abs(x);
  print "Abs(", x, ") = ", r, "\n";
}

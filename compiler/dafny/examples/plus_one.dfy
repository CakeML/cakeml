method PlusOne(n: int) returns (r: int)
  ensures n < r
{
  return n + 1;
}

method TestPlusOne(n: int) {
  var r := PlusOne(n);
  print "PlusOne(", n, ") = ", r, "\n";
}

method Main() {
  TestPlusOne(0);
  TestPlusOne(1);
  TestPlusOne(-5);
  TestPlusOne(100);
  TestPlusOne(999999);
}

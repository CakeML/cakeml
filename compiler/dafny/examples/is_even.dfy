method IsEven(n: int) returns (b: bool)
  requires n >= 0
  ensures b == (n % 2 == 0)
{
  if n == 0 {
    b := true;
  } else if n == 1 {
    b := false;
  } else {
    b := IsEven(n-2);
  }
}

method Main() {
  TestIsEven(0);
  TestIsEven(1);
  TestIsEven(2);
  TestIsEven(5);
  TestIsEven(10);
}

method TestIsEven(n: int)
{
  var r := IsEven(n);
  print "IsEven(", n, ") = ", r, "\n";
}

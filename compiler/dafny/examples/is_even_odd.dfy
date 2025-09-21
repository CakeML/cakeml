method IsEven(n: int) returns (b: bool)
  requires n >= 0
  ensures b == (n % 2 == 0)
{
  if n == 0 {
    b := true;
  } else {
    b := IsOdd(n - 1);
  }
}

method IsOdd(n: int) returns (b: bool)
  requires n >= 0
  ensures b == (n % 2 == 1)
{
  if n == 0 {
    b := false;
  } else {
    b := IsEven(n - 1);
  }
}

method Main() {
  TestIsEven(0);
  TestIsEven(1);
  TestIsEven(2);
  TestIsEven(5);
  TestIsEven(10);

  TestIsOdd(0);
  TestIsOdd(1);
  TestIsOdd(2);
  TestIsOdd(5);
  TestIsOdd(10);
}

method TestIsEven(n: int)
{
  var r := IsEven(n);
  print "IsEven(", n, ") = ", r, "\n";
}

method TestIsOdd(n: int)
{
  var r := IsOdd(n);
  print "IsOdd(", n, ") = ", r, "\n";
}

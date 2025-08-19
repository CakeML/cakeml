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

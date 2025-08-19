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

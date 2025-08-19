method SumToN(n: int) returns (sum: int)
  requires n >= 0
  ensures sum == n * (n + 1) / 2
  ensures n >= 0
{
  var i := 1;
  sum := 0;

  while i <= n
    invariant 1 <= i <= n + 1
    invariant sum == (i - 1) * i / 2
  {
    sum := sum + i;
    i := i + 1;
  }
}

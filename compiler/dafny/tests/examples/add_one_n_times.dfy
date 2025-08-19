method AddOneNTimes(n: int) returns (r: int)
  requires n >= 0
  ensures r == n
  ensures n >= 0
{
  r := 0;

  while r < n
    invariant 0 <= r <= n
  {
    r := r + 1;
  }
}

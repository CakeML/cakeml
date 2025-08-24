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

method Main() {
  TestAddOneNTimes(0);
  TestAddOneNTimes(1);
  TestAddOneNTimes(5);
}

method TestAddOneNTimes(n: int)
{
  var r := AddOneNTimes(n);
  print "AddOneNTimes(", n, ") = ", r, "\n";
}

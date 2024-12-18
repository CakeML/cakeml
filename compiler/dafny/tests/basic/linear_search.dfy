// Adapted from dafny/firstSteps/7_Arrays.dfy
method LinearSearch(a: array<int>, key: int) returns (n: nat)
  ensures 0 <= n <= a.Length
  ensures n == a.Length || a[n] == key
{
  n := 0;
  while n < a.Length
    invariant n <= a.Length
  {
    if a[n] == key {
      return;
    }
    n := n + 1;
  }
}

method Main() {
  var a := new int[23];
  var i := 0;
  while i < 23 {
    a[i] := i;
    i := i + 1;
  }
  var n := LinearSearch(a, 17);
  print "a:", a[0..a.Length], "\n";
	print "LinearSearch(a, 17): ", n, "\n";
}

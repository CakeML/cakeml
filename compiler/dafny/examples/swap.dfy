method Swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  modifies a
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

method Main() {
  var a1 := new int[3]; a1[0], a1[1], a1[2] := 1, 2, 3;
  var a2 := new int[3]; a2[0], a2[1], a2[2] := 4, 5, 6;

  TestSwap(a1, 0, 1);  // swap first two
  TestSwap(a1, 1, 2);  // swap last two
  TestSwap(a2, 0, 2);  // swap first and last
}

method TestSwap(a: array<int>, i: int, j: int)
{
  print "Swap([";
  var k := 0;
  while k < a.Length
  {
    if 0 < k { print ", "; }
    print a[k];
    k := k + 1;
  }
  print "], ", i, ", ", j, ")\n";

  Swap(a, i, j);

  print "After Swap: [";
  k := 0;
  while k < a.Length
  {
    if 0 < k { print ", "; }
    print a[k];
    k := k + 1;
  }
  print "]\n";
}

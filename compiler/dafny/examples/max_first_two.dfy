method MaxFirstTwo(a: array<int>) returns (m: int)
  requires a.Length >= 2
  ensures m == a[0] || m == a[1]
  ensures m >= a[0] && m >= a[1]
{
  if a[0] >= a[1] {
    m := a[0];
  } else {
    m := a[1];
  }
}

method Main() {
  var a1 := new int[2];
  a1[0] := 3;
  a1[1] := 5;

  var a2 := new int[2];
  a2[0] := 7;
  a2[1] := 2;

  var a3 := new int[2];
  a3[0] := 4;
  a3[1] := 4;

  TestMaxFirstTwo(a1);
  TestMaxFirstTwo(a2);
  TestMaxFirstTwo(a3);
}

method TestMaxFirstTwo(a: array<int>)
{
  var r := MaxFirstTwo(a);
  print "MaxFirstTwo([", a[0], ", ", a[1], "]) = ", r, "\n";
}

// Adapted from Dafny (MIT License): https://github.com/dafny-lang/dafny

method M(N: int, a: array<int>) returns (sum: int, max: int)
{
  sum := 0;
  max := 0;
  var i := 0;
  while (i < N)
  {
    if (max < a[i]) {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}

method Main()
{
  var a := new int[10];
  a[0] := 9;
  a[1] := 5;
  a[2] := 0;
  a[3] := 2;
  a[4] := 7;
  a[5] := 3;
  a[6] := 2;
  a[7] := 1;
  a[8] := 10;
  a[9] := 6;
  var s, m := M(10, a);
  print "N = ", a.Length, "  sum = ", s, "  max = ", m, "\n";
}
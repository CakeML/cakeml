// Adapted from Dafny (MIT License): https://github.com/dafny-lang/dafny

method M(n: int) returns (r: int)
  ensures r == if n <= 100 then 91 else n - 10
  decreases 100 - n
{
  if n <= 100 {
    r := M(n + 11);
    r := M(r);
  } else {
    r := n - 10;
  }
}

method TestM(n: int) {
  var m := M(n);
  print "M(", n, ") = ", m, "\n";
}

method Main() {
  TestM(3);
  TestM(99);
  TestM(100);
  TestM(101);
  TestM(1013);
}
// Adapted from Dafny (MIT License): https://github.com/dafny-lang/dafny

function fib(n: int): int
  requires n >= 0
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: int) returns (b: int)
  requires n >= 0
  ensures b == fib(n)
{
  if n == 0 { return 0; }
  var i: int := 1;
  var a := 0;
  b := 1;
  while i < n
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}

method Main() {
  TestComputeFib(0);
  TestComputeFib(1);
  TestComputeFib(2);
  TestComputeFib(5);
  TestComputeFib(10);

  TestFib(0);
  TestFib(1);
  TestFib(2);
  TestFib(5);
  TestFib(10);
}

method TestComputeFib(n: int)
{
  var r := ComputeFib(n);
  print "ComputeFib(", n, ") = ", r, "\n";
}

method TestFib(n: int)
{
  var r := fib(n);
  print "fib(", n, ") = ", r, "\n";
}

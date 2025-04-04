// Adapted from Dafny (MIT License): https://github.com/dafny-lang/dafny

function fib(n: int): int
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: int) returns (b: int)
{
  if n == 0 { return 0; }
  var i: int := 1;
  var a := 0;
  b := 1;
  while i < n
  {
    a, b := b, a + b;
    i := i + 1;
  }
}
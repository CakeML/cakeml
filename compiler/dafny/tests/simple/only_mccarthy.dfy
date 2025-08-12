// Adapted from Dafny (MIT License): https://github.com/dafny-lang/dafny

method M(n: int) returns (tmp:int, r: int)
  ensures r == if n <= 100 then 91 else n - 10
  decreases 100 - n
{
  if n <= 100 {
    tmp := M(n + 11);
    r := M(tmp);
  } else {
    r := n - 10;
  }
}

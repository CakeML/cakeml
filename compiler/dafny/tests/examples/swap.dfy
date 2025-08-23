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

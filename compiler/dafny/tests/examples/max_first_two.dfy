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

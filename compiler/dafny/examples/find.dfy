// From https://dafny.org/dafny/OnlineTutorial/guide

method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key { return; }
    index := index + 1;
  }
  index := -1;
}

method Main() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 1, 4, 1, 5;

  TestFind(a, 3);   // key at start
  TestFind(a, 4);   // key in middle
  TestFind(a, 5);   // key at end
  TestFind(a, 9);   // key not present
}

method TestFind(a: array<int>, key: int)
{
  var r := Find(a, key);
  print "Find(", key, ") = ", r, "\n";
}

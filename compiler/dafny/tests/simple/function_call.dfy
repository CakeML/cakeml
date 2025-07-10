// Adapted from Dafny (MIT License): https://github.com/dafny-lang/dafny

function F(x: int, y: bool): int {
  x + if y then 2 else 3
}

method Main() {
  var w;
  w := F(2, false);
  print w, "\n";
}

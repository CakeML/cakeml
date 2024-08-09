method Main() {
  var x := 0;
  while x < 10 {
    x := x + 1;
    if x % 2 == 0 {
      continue;
    }
    print x, "\n";
  }
}

method Main() {
  var x := 0;
  while x < 5 {
    x := x + 1;
    if x % 2 == 0 {
      continue;
    }
		print "x: ", x, "\n";
    var y := 0;
    while y < 5 {
      y := y + 1;
      if y % 2 == 0 {
        continue;
      }
			print "y: ", y, "\n";
    }
  }
}

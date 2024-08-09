method Main() {
	var x := 0;
  while x < 5 {
    var y := 0;
    while y != 5 {
			print 5 * x + y, "\n";
			y := y + 1;
    }
		x := x + 1;
  }

	var sum := 0;
	var n := 10;

	var i := 1;
  while i <= n
  {
    sum := sum + i;
    i := i + 1;
  }

	print sum;
}

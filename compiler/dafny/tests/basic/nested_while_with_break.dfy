method Main() {
	var x := 0;
  while x < 5 {
		print "x: ", x, "\n";
    var y := 0;
    while y != 5 {
			print "y: ", y, "\n";
			if (x == 2) {
				if (y == 3) {
          break;
        }
			}
			y := y + 1;
    }

		if (x == 3) {
      break;
    }
		x := x + 1;
	}
}

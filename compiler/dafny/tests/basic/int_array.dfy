method Main() {
	var a := new int[4];
	print "a: ", a[0..a.Length], "\n";

	var b := new int[] [1, 2, 4, 8];
	print "b: ", b[0..b.Length], "\n";
	print "length of b: ", b.Length, "\n";

	print "b[3]: ", b[3], "\n";

	b[3] := 6;
	print "b after update: ", b[0..b.Length], "\n";
}

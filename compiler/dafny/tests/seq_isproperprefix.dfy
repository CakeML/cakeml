method Main() {
	var empty: seq<int> := [];
  print "[] < [1, 2, 3]: ", [] < [1, 2, 3], "\n";
  print "[1, 2] < [1, 2, 3]: ", [1, 2] < [1, 2, 3], "\n";
  print "[1, 2] < [1, 2]: ", [1, 2] < [1, 2], "\n";
  print "[] < []: ", empty < empty, "\n";
}

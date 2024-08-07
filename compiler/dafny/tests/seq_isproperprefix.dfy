method Main() {
	var empty: seq<int> := [];
  print "[] < [1, 2, 3]: ", [] < [1, 2, 3], " ";
  print "[1, 2] < [1, 2, 3]: ", [1, 2] < [1, 2, 3], " ";
  print "[1, 2] < [1, 2]: ", [1, 2] < [1, 2], " ";
  print "[] < []: ", empty < empty, " ";
}

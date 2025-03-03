method Main() {
  var a := new int[1, 0, 2];
  // Length2 must be accessible, even if the second dimension is 0
  print "a (length): ", (a.Length0, a.Length1, a.Length2), "\n\n";
}
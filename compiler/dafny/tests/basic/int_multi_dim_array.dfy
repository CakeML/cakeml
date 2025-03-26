method Main() {
  var dim0 := 3;
  var dim1 := 4;

  // Sanity check to see whether array or loop implementation is broken
  print "Sanity Check (Loop): \n";
  print_zeros(dim0, dim1);

  var a := new int[dim0, dim1];
  print "a (length): ", (a.Length0, a.Length1), "\n\n";
  print_multi_dim_array(a);

  a[0, 0] := 1;
  a[0, 1] := 2;
  a[0, 2] := 3;
  a[0, 3] := 4;

  a[1, 0] := 5;
  a[1, 1] := 6;
  a[1, 2] := 7;
  a[1, 3] := 8;

  a[2, 0] := 9;
  a[2, 1] := 10;
  a[2, 2] := 11;
  a[2, 3] := 12;
  print_multi_dim_array(a);

  a[2, 3], a[0, 0] := a[0, 0], a[2, 3];
  print_multi_dim_array(a);
}

method print_multi_dim_array(arr: array2<int>) {
  var i := 0;
  var j := 0;

  print "arr (length): ", (arr.Length0, arr.Length1), "\n";
  while (i < arr.Length0) {
    while (j < arr.Length1) {
      var elem := arr[i, j];
      print "i: ", i, " j: ", j, " elem: ", elem, "\n";
      j := j + 1;
    }

   print "\n";
   j := 0;
   i := i + 1;
  }
  print "\n";
}

method print_zeros(a: int, b: int) {
  var i := 0;
  var j := 0;

  while (i < a) {
    while (j < b) {
      print 0, "  ";
      j := j + 1;
    }

    print "\n";
    j := 0;
    i := i + 1;
  }
  print "\n";
}
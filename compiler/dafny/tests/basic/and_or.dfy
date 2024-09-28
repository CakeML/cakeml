method Main() {
    PrintResults(true, true);
    PrintResults(true, false);
    PrintResults(false, true);
    PrintResults(false, false);
}

method PrintResults(b1: bool, b2: bool) {
    print "b1 = ", b1, ", b2 = ", b2, "\n";
    print "b1 && b2 = ", b1 && b2, "\n";
    print "b1 || b2 = ", b1 || b2, "\n";
    print "\n";
}

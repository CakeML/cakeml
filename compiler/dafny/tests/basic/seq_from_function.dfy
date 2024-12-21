method Main() {
    testSequenceGeneration();
}

function max(a: int, b: int): int {
	if a > b then a else b
}

method testSequenceGeneration() {
    var seq0 := seq(0, n => n);
    print "seq0 = ", seq0, "\n";

    var seq1 := seq(10, n => n);
    print "seq1 = ", seq1, "\n";

    var seq2 := seq(10, n => n + 1);
    print "seq2 = ", seq2, "\n";

    var seq3 := seq(5, n => n * 2);
    print "seq3 = ", seq3, "\n";

    var seq4 := seq(5, n => n * 2 + 1);
    print "seq4 = ", seq4, "\n";

    var seq5 := seq(5, n => n * n);
    print "seq5 = ", seq5, "\n";

    var seq6 := seq(5, n => n * n * n);
    print "seq6 = ", seq6, "\n";

    var seq7 := seq(5, n => -n);
    print "seq7 = ", seq7, "\n";

    var seq8 := seq(0, n => n % 2 == 0);
    print "seq8 = ", seq8, "\n";

    var seq9 := seq(10, n => n % 2 == 0);
    print "seq9 = ", seq9, "\n";

    var seq10 := seq(5, n => true);
    print "seq10 = ", seq10, "\n";

    var seq11 := seq(5, n => false);
    print "seq11 = ", seq11, "\n";

    var seq12 := seq(3, n => seq(max(0, n + 1), m => m % 2 == 0));
    print "seq12 = ", seq12, "\n";

    var seq13 := seq(3, n => [n % 2 == 0, (n + 1) % 2 == 0, (n + 2) % 2 == 0]);
    print "seq13 = ", seq13, "\n";
}

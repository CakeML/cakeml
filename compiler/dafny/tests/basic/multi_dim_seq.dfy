method Main() {
    testMultiDimensionalSequences();
}

method testMultiDimensionalSequences() {
    // Create a 2D sequence
    var seq2D := [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9]
    ];

    // Access elements using multi-dimensional indexing
    print "seq2D[0][0] = ", seq2D[0][0], "\n";
    print "seq2D[1][1] = ", seq2D[1][1], "\n";
    print "seq2D[2][2] = ", seq2D[2][2], "\n";

    // Create a 3D sequence
    var seq3D := [
        [
            [1, 2],
            [3, 4]
        ],
        [
            [5, 6],
            [7, 8]
        ]
    ];

    // Access elements using multi-dimensional indexing
    print "seq3D[0][0][0] = ", seq3D[0][0][0], "\n";
    print "seq3D[0][1][1] = ", seq3D[0][1][1], "\n";
    print "seq3D[1][1][1] = ", seq3D[1][1][1], "\n";
}

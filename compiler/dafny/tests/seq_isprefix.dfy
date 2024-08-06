function bool_to_string(b: bool) : string {
	if b then "true" else "false"
}

method Main() {
    print ("[] <= [1, 2, 3]: ");
    print bool_to_string([] <= [1, 2, 3]) + " ";
    print ("[1, 2] <= [1, 2, 3]: ");
    print bool_to_string([1, 2] <= [1, 2, 3]) + " ";
    print ("[1, 2] <= [1, 2]: ");
    print bool_to_string([1, 2] <= [1, 2]) + " ";
    print ("[] <= []: ");
    var empty: seq<int> := [];
    print bool_to_string(empty <= empty) + " ";
}

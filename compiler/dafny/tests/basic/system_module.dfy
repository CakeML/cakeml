method Main() {
	var n_ni: nat;
	n_ni := 0;
	var n_i: nat := 1;
	print n_ni, " ", n_i, "\n";

	var uni_ni: ();
	uni_ni := ();
	var uni_i := ();
	print uni_ni, " ", uni_i, "\n";

	var tup_ni: (nat, int);
	tup_ni := (0, 1);
	var tup_i: (nat, int) := (0, 1);
	print tup_ni, " ", tup_i, "\n";

	print "(", tup_i.0, ", ", tup_i.1, ")\n";
}

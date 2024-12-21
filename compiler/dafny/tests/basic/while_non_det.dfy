// This test case is supposed to exercise a Break NONE statement, as
// "normal" breaks seem to get translated into labeled ones.
// Comparing with Dafny's output is a bit sketchy, since the while
// is non-deterministic, so there is probably no requirement for the outputs
// to be equal.
method Main() {
	assume {:axiom} false;

	var i := 1;
  while *
  {
		print "hello from while", "\n";
  }

}

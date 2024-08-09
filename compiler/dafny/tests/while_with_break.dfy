method Main() {
	assume {:axiom} false;
	var x := 0;

  while true {
    x := x + 1;
    print x, "\n";
    if x == 10 {
      break;
    }
  }
}

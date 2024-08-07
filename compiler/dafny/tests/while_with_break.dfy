method Main() {
	assume {:axiom} false;
	var x := 0;

  while true {
    x := x + 1;
    print x;
    if x == 10 {
      break;
    }
  }
}

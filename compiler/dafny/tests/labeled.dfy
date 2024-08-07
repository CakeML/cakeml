method Main() {
	foo(false);
	foo(true);
}

method foo(brk: bool) {
	label A: {
		print "A ";
		label B : {
			print "B ";
			label C : {
				print "C ";
				if brk {break A;}
			}
			print "left C ";
		}
		print "left B ";
	}
	print "left A " ;

}

method Main() {
	foo(false);
	foo(true);
}

method foo(brk: bool) {
	label A: {
		print "A\n";
		label B : {
			print "B\n";
			label C : {
				print "C\n";
				if brk {break A;}
			}
			print "left C\n";
		}
		print "left B\n";
	}
	print "left A\n" ;
}

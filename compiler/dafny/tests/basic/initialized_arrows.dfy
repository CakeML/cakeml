function foo(): int { 3 }
method Main() {
	var f0 := () =>  42;
	var f1 := (x: int) => -x;
	var f2 := (x: int, y: int) =>  x+y;

	var outside := 4;
	var f3 := (x: int) =>  x+4;

	var f4 := (x: int, y: int) =>  x;
	var f5 := foo;

	print f0(), "\n";
	print f1(1), "\n";
	print f2(1, 2), "\n";
	print f3(1), "\n";
	print f4(6, outside), "\n";
	print f5(), "\n";
}

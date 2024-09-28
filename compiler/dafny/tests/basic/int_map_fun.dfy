function {:tailrecursion false} mymap(f: int -> int, xs: seq<int>) : seq<int> {
	if |xs| == 0 then [] else [f(xs[0])] + mymap(f, xs[1..])
}

function incr(x: int): int {
	x + 1
}

method Main() {
	print mymap(x => x, [1, 2, 3, 4]), "\n";
	print mymap(x => x*x, [1, 2, 3, 4]), "\n";
	print mymap(incr, [1, 2, 3, 4]), "\n";
}

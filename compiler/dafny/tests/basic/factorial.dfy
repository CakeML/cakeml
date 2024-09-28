method Main() {
	print factorial(0), "\n";
	print factorial(1), "\n";
	print factorial(3), "\n";
	print factorial(5), "\n";
	print factorial(23), "\n";
}

function {:tailrecursion false} factorial(x: int): int
	requires x >= 0
{
	if x == 0 then 1 else x * factorial(x-1)
}

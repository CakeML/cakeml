method Main() {
	print factorial(0), " ";
	print factorial(1), " ";
	print factorial(3), " ";
	print factorial(5), " ";
	print factorial(23), " ";
}

function {:tailrecursion false} factorial(x: int): int
	requires x >= 0
{
	if x == 0 then 1 else x * factorial(x-1)
}

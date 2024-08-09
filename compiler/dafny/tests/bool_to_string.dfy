method Main()
{
	print bool_to_string(true), "\n";
	print bool_to_string(false), "\n";
}

function bool_to_string(b: bool) : string {
	if b then "true" else "false"
}

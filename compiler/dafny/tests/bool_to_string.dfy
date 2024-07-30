method Main()
{
	print bool_to_string(true);
	print bool_to_string(false);
}

function bool_to_string(b: bool) : string {
	if b then "true" else "false"
}

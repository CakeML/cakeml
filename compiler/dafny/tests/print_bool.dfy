method Main()
{
	var b : bool;
	var r : string;

	b := true;
	r := if b then "true" else "false";
	print r;

	b := false;
	r := if b then "true" else "false";
	print r;
}

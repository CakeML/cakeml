function bool_to_string(b: bool) : string {
	if b then "true" else "false"
}

method Main() {
	var meal := ["cookies"] + ["milk"];
	print bool_to_string("veggies" in meal);
	print bool_to_string("cookies" in meal);
}

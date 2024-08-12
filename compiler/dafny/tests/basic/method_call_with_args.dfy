method Main()
{
	print_wrapper("choose your slice: ");
	concat_and_print("left slice or ", "right slice?\n");
}

method print_wrapper(s: string) {
	print s;
}

method concat_and_print(left: string, right: string) {
	print (left + right);
}

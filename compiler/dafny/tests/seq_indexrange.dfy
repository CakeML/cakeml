method print_seq_string(s: seq<string>)
{
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    print s[i], " ";
    i := i + 1;
  }
}

method Main() {
	var nums := ["0", "1", "2", "3", "4"];
	print "nums: ";
	print_seq_string(nums);
	print "nums[0..|nums|]: ";
	print_seq_string(nums[0..|nums|]);
	print "nums[..]: ";
	print_seq_string(nums[..]);
	print "nums[..2]: ";
	print_seq_string(nums[..2]);
	print "nums[2..]: ";
	print_seq_string(nums[2..]);
	print "num[1..4]: ";
	print_seq_string(nums[1..4]);
}

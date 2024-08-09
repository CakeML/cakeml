// datatype List = Nil(a: int) | Cons(head: int, tail: List)

method Main() {
	// TODO does not work
	var a_string: string := "ab";
	var a_char_list: string := ['a','b'];

	print a_string;
	print a_char_list;
	// print ['\\'];
	// print "\\";
	// print ["\\"];
	// print @"\\";
	// print [@"\\"];


	// print "hello\n";
	// print ["hello\n"];
	// print '\n';
	// print 'n';
	// print "\n";
	// print @"\n";
	// print @"""";
	// var list1 := Cons(1, Cons(2, Cons(3, Nil(0))));
	// var list2 := Nil(0);

	// print(list1.Nil?);
	// print(list1.head);
	// print(list2.a);

	// printList(list1);
	// printList(list2);
}

// method {:tailrecursion false} printList(lst: List)
//   decreases lst
// {
//   match lst
//   case Nil(e) => {
//     print "The list is empty\n";
//   }
//   case Cons(hd, tl) => {
//     print hd, " ";
//     printList(tl);
//   }
// }

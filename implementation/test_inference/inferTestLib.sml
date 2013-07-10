open inferTestTheory repl_computeLib stringSyntax;
open TextIO;

fun do_test filename =
  let 
    val i = openIn filename;
    val s = inputAll i;
    val _ = closeIn i;
    val res = (rhs o concl o EVAL) ``(infer_test_repl_fun ^(fromMLstring s))``
  in
    if term_eq res ``Terminate`` then
      NONE
    else 
      SOME res
  end;

val _ = mesonLib.chatting := 0;

fun do_all_tests files =
let val x = ref 0 in
List.app (fn d => (x := (!x) + 1;
                   (case do_test d of 
                        SOME tm => print (Int.toString (!x) ^ ": error " ^ term_to_string tm ^ "\n")
                      | NONE => print (Int.toString (!x) ^ ": ok\n"))))
        files
end;

do_all_tests
["test1.ml", 
 "test2.ml", 
 "test3.ml",
 "test4.ml"]


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


fun do_all_tests files =
let val x = ref 0 in
List.app (fn d => (x := (!x) + 1;
                   (case do_test d of 
                        SOME tm => print (": error " ^ term_to_string tm ^ " ")
                      | NONE => ());
                    print ((Int.toString (!x)) ^ "\n")))
        files
end

do_all_tests 
["test3.ml"]

["test1.ml", 
 "test2.ml", 
 "test3.ml"]


open inferTestTheory repl_computeLib;
open TextIO;

fun do_test filename =
  let 
    val i = openIn filename;
    val s = input_all i;
    val _ = closeIns i;
  in
    s
  end

  do_test "test1.ml";

open wholeProgTheory repl_computeLib stringSyntax optionSyntax;
open bytecodeLabelsTheory;
open TextIO;

val _ = computeLib.add_funs [compile_decs_def, compile_print_vals_def, 
                             bc_inst_to_string_def, encode_bc_insts_def,
                             encode_bc_inst_def, encode_num_def, encode_loc_def,
                             encode_char_def, bc_loc_to_string_def];

fun do_test filename =
  let 
    val i = openIn filename;
    val s = inputAll i;
    val _ = closeIn i;
    val res = (rhs o concl o EVAL) ``case wp_main_loop initial_repl_fun_state ^(fromMLstring s) of Failure msg => SOME msg | Success _ => NONE``
  in
    if is_none res then
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

fun do_compile_string infile outfile =
  let
    val i = openIn infile;
    val s = inputAll i;
    val _ = closeIn i;
    (* TODO: there is an assumption on this theorem.  Where does it come from? *)
    val res = (rhs o concl o EVAL) ``whole_prog_compile T ^(fromMLstring s)``
    val res = fromHOLstring res
    val out = openOut outfile
    val _ = output (out, res)
    val _ = closeOut out
  in
    ()
  end

fun do_compile_binary infile outfile =
  let
    val i = openIn infile;
    val s = inputAll i;
    val _ = closeIn i;
    val res = (rhs o concl o EVAL) ``(whole_prog_compile_encode T ^(fromMLstring s):word64 list option)``
    val res = fromHOLstring res
    val out = BinIO.openOut outfile
    (*val _ = ...*)
    val _ = BinIO.closeOut out
  in
    ()
  end



(*
do_all_tests
["test1.ml", 
 "test2.ml", 
 "test3.ml",
 "test4.ml"]

val filename = "fib.ml";
val i = openIn filename;
val s = inputAll i;
val _ = closeIn i;
val res = EVAL ``wp_main_loop initial_repl_fun_state ^(fromMLstring s)``

do_compile_string "test0.ml" "test0.byte"
do_compile_string "fib.ml" "fib.byte"


 *)


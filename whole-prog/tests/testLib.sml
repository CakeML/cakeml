open wholeProgTheory repl_computeLib stringSyntax optionSyntax;
open bytecodeLabelsTheory wordsLib;
open TextIO;

val _ = computeLib.add_funs [compile_decs_def, compile_print_vals_def, 
                             bc_inst_to_string_def, encode_bc_insts_def,
                             encode_bc_inst_def, encode_num_def, encode_loc_def,
                             encode_char_def, bc_loc_to_string_def, dimword_64];

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
    val thm = EVAL ``whole_prog_compile_string T ^(fromMLstring s)``
    val _ = assert (fn x => hyp x = []) thm;
    val res = fromHOLstring (rhs (concl thm))
    val out = openOut outfile
    val _ = output (out, res)
    val _ = closeOut out
  in
    ()
  end

fun strip_list tm =
  if listSyntax.is_nil tm then
    []
  else
    let val (h, t) = listSyntax.dest_cons tm in
      h::strip_list t
    end

(* Specialised for 64-bit little endian *)
local
open IntInf;
infix ~>>
in
fun encode (i:int) =
  Word8Vector.fromList 
    (List.map Word8.fromInt [i, (i ~>> 0w8), (i ~>> 0w16), (i ~>> 0w24), 
                             (i ~>> 0w32), (i ~>> 0w40), (i ~>> 0w48), (i ~>> 0w56)])
end;

fun do_compile_binary infile outfile =
  let
    val i = openIn infile;
    val s = inputAll i;
    val _ = closeIn i;
    val thm = EVAL ``(whole_prog_compile_encode T ^(fromMLstring s):word64 list option)``;
    val _ = assert (fn x => hyp x = []) thm;
    val res = thm |> concl 
                  |> rhs 
                  |> dest_some 
                  |> strip_list 
                  |> List.map wordsSyntax.uint_of_word
                  |> List.map encode
    val out = BinIO.openOut outfile;
    val _ = List.app (fn ws => BinIO.output (out, ws)) res;
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
val res = EVAL ``whole_prog_compile F ^(fromMLstring s)``

val filename = "test0.ml";
val i = openIn filename;
val s = inputAll i;
val _ = closeIn i;
val res = EVAL ``(whole_prog_compile_string F ^(fromMLstring s))``


time (do_compile_binary "fib.ml") "fib.bbyte"
runtime: 4m03s,    gctime: 3m53s,     systime: 6.918s.

time (do_compile_string "fib.ml") "fib.byte"

time (do_compile_binary "test0.ml") "test0.bbyte"
time (do_compile_string "test0.ml") "test0.byte"


 *)


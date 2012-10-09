structure bytecode_testerLib :> bytecode_testerLib =
struct

open HolKernel boolLib bossLib;
open bytecode_x64Theory wordsTheory wordsLib intLib;

fun write_file filename strs = let
  val t = TextIO.openOut(filename)
  val _ = map (fn s => TextIO.output(t,s)) strs
  val _ = TextIO.closeOut(t)
  in () end;

fun build_and_run asm_strs reps = let
  val path = Globals.HOLDIR ^ "/examples/miniML/compiler/bytecode/benchmarking"
  val _ = write_file (path ^ "/generated_asm.s") asm_strs
  val command = "cd " ^ path ^ " && make && ./bytecode_tester " ^ (int_to_string reps)
  val _ = Process.system command
  in () end

fun run_bytecode reps bytecode_tm = let
  fun pad2 s = if size s < 2 then pad2 ("0" ^ s) else s
  fun asm_line [] = "\n"
    | asm_line xs = foldl (fn (x,y) => y ^ ", 0x" ^ x) ("\t.byte\t0x" ^ (hd xs)) (tl xs) ^ "\n"
  val res = EVAL ``bytecode_to_x64 ^bytecode_tm`` |> concl |> rand
            |> listSyntax.dest_list |> fst |> map optionSyntax.dest_some
            |> map (fn tm => tm |> listSyntax.dest_list |> fst |>
                   map (fn tm => tm |> listSyntax.dest_list |> fst |>
                       map (fn tm => tm |> rand |> numSyntax.dest_numeral
                                        |> Arbnum.toHexString |> pad2)))
            |> map (fn xs => []::xs) |> Lib.flatten |> map asm_line
  in build_and_run res reps end;

(* examples:

  val reps = 1000000;
  val bytecode_tm = ``[Stack (PushInt 1); Stack (PushInt 2); Stack (PushInt 3)]``;
  val _ = run_bytecode reps bytecode_tm;

  val reps = 1000000;
  val bytecode_tm = ``[Stack (PushInt 1);
                       Jump (Addr 30); (* skips next instruction *)
                       Stack (PushInt 3);
                       Stack (PushInt 2)]``;
  val _ = run_bytecode reps bytecode_tm;

*)

end

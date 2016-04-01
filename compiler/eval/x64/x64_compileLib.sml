structure x64_compileLib =
struct

open HolKernel boolLib bossLib
open x64_targetLib asmLib;
open compilerComputeLib;
open x64AssemblerLib

(* open x64_targetTheory *)

val cmp = wordsLib.words_compset ()
val () = computeLib.extend_compset
    [computeLib.Extenders
      [compilerComputeLib.add_compiler_compset
      ,x64_targetLib.add_x64_encode_compset
      ,asmLib.add_asm_compset
      ]
    ] cmp

val eval = computeLib.CBV_CONV cmp

fun print_asm res =
  let val res = (rand o concl) res
      val bytes = hd(pairSyntax.strip_pair (optionSyntax.dest_some res))
      val dis = x64_disassemble_term bytes
      val maxlen = 30
      fun pad 0 = ()
      |   pad n = (print" ";pad (n-1))
      fun printAsm [] = ()
      |   printAsm (x::xs) = case x of (hex,dis) =>
          ( print hex
          ; pad (maxlen-String.size hex)
          ; print dis;print"\n"
          ; printAsm xs)
      in
        print"Bytes";pad (maxlen -5);print"Instruction\n";
        printAsm dis
      end

(*
open x64_targetTheory lab_to_targetTheory;
open x64_exportLib wordsTheory wordsLib;

val _ = computeLib.add_funs [x64Theory.e_imm32_def,x64Theory.encode_def];

lab_to_targetTheory.compile_lab_def

val conf = ``<| encoder := x64_enc; labels := LN; asm_conf := x64_config |>``

eval
  ``remove_labels x64_config x64_enc
      [Section 0 [LabAsm (Jump (Lab 0 50)) 0w [] 0;
                  Label 0 50 0;
                  LabAsm Halt 0w [] 0]] LN``

val bytes_tm =
  eval ``lab_to_target$compile ^conf [Section 0 [LabAsm (Jump (Lab 0 50)) 0w [] 0;
                  Label 0 50 0;
                  LabAsm Halt 0w [] 0]]``
  |> concl |> rand |> rand |> pairSyntax.dest_pair |> fst

val _ = write_cake_S 1 1 0 bytes_tm ""

Try:   gcc cake.S -o cake && ./cake

*)

end

structure x64_compileLib =
struct

open HolKernel boolLib bossLib lcsymtacs;

open x64_targetTheory lab_to_targetTheory;
open x64_exportLib wordsTheory wordsLib;

(*

val _ = computeLib.add_funs [x64Theory.e_imm32_def,x64Theory.encode_def];

val bytes_tm =
  EVAL ``compile x64_config x64_enc [Section 0 [LabAsm Halt 0w [] 0]]``
  |> concl |> rand |> rand

val _ = write_cake_S 1 1 0 bytes_tm ""

Try:   gcc cake.S -o cake && ./cake

*)

end

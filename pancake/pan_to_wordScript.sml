(*
  Correctness proof for --
*)

open preamble
     pan_to_crepTheory crep_to_loopTheory
     loop_to_wordTheory

val _ = new_theory "pan_to_word";


Definition compile_prog_def:
  compile_prog prog =
  let prog = pan_to_crep$compile_prog prog;
      prog = crep_to_loop$compile_prog prog in
    loop_to_word$compile prog
End


val _ = export_theory();

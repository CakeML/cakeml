(*
  Compiler from pan to word
*)

open preamble
     pan_simpTheory pan_to_crepTheory pan_globalsTheory
     crep_to_loopTheory loop_to_wordTheory

val _ = new_theory "pan_to_word";


Definition compile_prog_def:
  compile_prog arch prog =
  let prog = pan_simp$compile_prog prog;
      prog = pan_globals$compile_top prog «main»;
      prog = pan_to_crep$compile_prog prog;
      prog = crep_to_loop$compile_prog arch prog in
    loop_to_word$compile prog
End


val _ = export_theory();

(*
  Compiler from pan to word
*)
Theory pan_to_word
Ancestors
  pan_simp pan_to_crep crep_to_loop loop_to_word
Libs
  preamble


Definition compile_prog_def:
  compile_prog arch prog =
  let prog = pan_simp$compile_prog prog;
      prog = pan_to_crep$compile_prog prog;
      prog = crep_to_loop$compile_prog arch prog in
    loop_to_word$compile prog
End



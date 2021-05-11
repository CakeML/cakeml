(*
  Compiler from Pancake to machine code
*)

open preamble
     pan_to_wordTheory backendTheory
     word_depthTheory word_to_wordTheory;

val _ = new_theory "pan_to_target";


Definition compile_prog_def:
  compile_prog c prog =
    let prog = pan_to_word$compile_prog prog in
    let (col,prog) = compile c.word_to_word_conf c.lab_conf.asm_conf prog in
      from_word c LN prog
End

(*  TODO: evaluate max_depth ... (full_call_graph dest (fromAList prog))  *)

val _ = export_theory();

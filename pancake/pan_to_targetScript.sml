(*
  Compiler from Pancake to machine code
*)

open preamble
     pan_to_wordTheory backendTheory
     word_depthTheory word_to_wordTheory;

val _ = new_theory "pan_to_target";


Definition compile_prog_def:
  compile_prog c prog =
    let prog2 = pan_to_word$compile_prog c.lab_conf.asm_conf.ISA prog in
    let (col,prog3) = word_to_word$compile c.word_to_word_conf c.lab_conf.asm_conf prog2 in
    let names = fromAList (ZIP (MAP FST prog2,  (* func numbers *)
                                MAP FST prog    (* func names *)
                )) : mlstring$mlstring num_map in
    let c = c with exposed := MAP FST prog in
      from_word c names prog3
End

(*  TODO: evaluate max_depth ... (full_call_graph dest (fromAList prog))  *)

val _ = export_theory();

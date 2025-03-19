(*
  Compiler from timeLang to machine code
*)

open preamble
     time_to_panTheory pan_to_targetTheory;

val _ = new_theory "time_to_target";

Definition compile_prog_def:
  compile_prog asm_conf c prog =
    let prog = time_to_pan$compile_prog prog in
    let prog = MAP (\(n,p,b). (n,F,p,b)) prog in
      pan_to_target$compile_prog asm_conf c prog
End

val _ = export_theory();

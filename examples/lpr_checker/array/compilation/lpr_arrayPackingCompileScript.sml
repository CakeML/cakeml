(*
  Compiles the packing example by evaluation inside the logic of HOL
*)
open preamble compilationLib lpr_arrayPackingProgTheory

val _ = new_theory "lpr_arrayPackingCompile"

val lpr_array_compiled = save_thm("lpr_packing_compiled",
  compile_x64 "cake_direct" main_prog_def);

val _ = export_theory ();

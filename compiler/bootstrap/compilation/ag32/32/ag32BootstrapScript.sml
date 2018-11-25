open preamble to_lab_ag32BootstrapTheory compilationLib

val _ = new_theory "ag32Bootstrap";

val () = ml_translatorLib.reset_translation();

val bootstrap_thm =
  compilationLib.cbv_to_bytes_ag32
    stack_to_lab_thm lab_prog_def
    0 0 "code" "data" "config" "cake.S";

val cake_compiled = save_thm("cake_compiled", bootstrap_thm);

val _ = export_theory();

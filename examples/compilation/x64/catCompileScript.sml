open preamble compilationLib catProgTheory

val _ = new_theory "catCompile"

val cat_compiled = save_thm("cat_compiled",
  compile_x64 500 500 "cat" cat_prog_def);

val _ = export_theory ();


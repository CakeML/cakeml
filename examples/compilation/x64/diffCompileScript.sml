open preamble compilationLib diffProgTheory

val _ = new_theory "diffCompile"

val diff_compiled = save_thm("diff_compiled",
  compile_x64 1000 1000 "diff" diff_prog_def);

val _ = export_theory ();

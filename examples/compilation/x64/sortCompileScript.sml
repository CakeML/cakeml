open preamble compilationLib sortProgTheory

val _ = new_theory "sortCompile"

val sort_compiled = save_thm("sort_compiled",
  compile_x64 1000 1000 "sort" sort_prog_def);

val _ = export_theory ();

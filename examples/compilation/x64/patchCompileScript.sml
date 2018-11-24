open preamble compilationLib patchProgTheory

val _ = new_theory "patchCompile"

val patch_compiled = save_thm("patch_compiled",
  compile_x64 1000 1000 "patch" patch_prog_def);

val _ = export_theory ();

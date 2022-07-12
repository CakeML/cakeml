(**
  renaming theory to unify naming of theorems
**)

open preambleDandelion;

val _ = new_theory "rename";

val _ = map save_thm [
    ("OPTION_MAP_def", OPTION_MAP_DEF)
  ]

val _ = export_theory();

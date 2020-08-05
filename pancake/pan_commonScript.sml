(*
  Common definitions for Pancake compiler
*)
open preamble

val _ = new_theory "pan_common"

Definition distinct_lists_def:
  distinct_lists xs ys =
    EVERY (\x. ~MEM x ys) xs
End


val _ = export_theory();

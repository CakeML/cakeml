(*
  Common definiations for Pancake compiler
*)
open preamble

val _ = new_theory "pan_common"

Definition distinct_lists_def:
  distinct_lists xs ys =
    EVERY (\x. ~MEM x ys) xs
End


(* list$oHD has type 'a list -> 'a option,
   we need 'a list -> 'a *)

Definition ooHD_def:
  (ooHD a [] = (a:num)) ∧
  (ooHD a (n::ns) = n)
End


val _ = export_theory();

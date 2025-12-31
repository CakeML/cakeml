(*
  Common definitions for Pancake compiler
*)
Theory pan_common
Libs
  preamble

Definition distinct_lists_def:
  distinct_lists xs ys =
    EVERY (\x. ~MEM x ys) xs
End



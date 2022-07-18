(*
  Parse and print for pb_preconstraint, pb_check
*)

open preamble pb_preconstraintTheory pb_normaliseTheory pb_checkTheory;

val _ = new_theory "pb_parse";

val _ = numLib.prefer_num();

(* printing of string pbc *)
Definition lit_string_def:
  (lit_string (Pos v) = v) ∧
  (lit_string (Neg v) = strlit "~" ^ v)
End

Definition lhs_string_def:
  lhs_string xs =
  concatWith (strlit" ") (MAP(λ(c,l). concat [int_to_string #"-" c; strlit " " ; lit_string l]) xs)
End

Definition pbc_string_def:
  (pbc_string (Equal xs i) = concat [lhs_string xs; strlit " = "; int_to_string #"-" i]) ∧
  (pbc_string (GreaterEqual xs i) = concat [lhs_string xs; strlit " >= "; int_to_string #"-" i])
End


val _ = export_theory();


(*
  Definition of Scheme values
*)
Theory scheme_values
Ancestors
  arithmetic list string
Libs
  preamble

(* Values in the source semantics are binary trees *)
Datatype:
  v = Pair v v | Num int | Bool bool | Word string | Nil
End

Definition head_def[simp]:
  head (Pair x y) = x ∧
  head v = v
End

Definition tail_def[simp]:
  tail (Pair x y) = y ∧
  tail v = v
End

Definition cons_def[simp]:
  cons x y = Pair x y
End

Theorem v_size_def[simp,allow_rebind] = fetch "-" "v_size_def";

(*
  Replaces assert with skip to ignore the former during compilation.
*)
Theory dafny_remove_assert
Ancestors
  dafny_ast
Libs
  preamble

Definition remove_assert_stmt_def:
  remove_assert_stmt (Assert _) = Skip ∧
  remove_assert_stmt (Then stmt₁ stmt₂) =
    Then (remove_assert_stmt stmt₁) (remove_assert_stmt stmt₂) ∧
  remove_assert_stmt (If cnd thn els) =
    If cnd (remove_assert_stmt thn) (remove_assert_stmt els) ∧
  remove_assert_stmt (Dec lcl stmt) =
    Dec lcl (remove_assert_stmt stmt) ∧
  remove_assert_stmt (While grd invs decrs mod body) =
    While grd invs decrs mod (remove_assert_stmt body) ∧
  remove_assert_stmt stmt = stmt
End

Definition remove_assert_member_def:
  remove_assert_member (Method name ins req ens reads decreases outs mod body) =
    Method name ins req ens reads decreases outs mod (remove_assert_stmt body) ∧
  remove_assert_member member = member
End

Definition remove_assert_def:
  remove_assert (Program members) =
    Program (MAP remove_assert_member members)
End

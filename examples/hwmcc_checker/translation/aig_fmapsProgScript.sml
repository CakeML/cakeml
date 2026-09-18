(*
  Setting up translator for the fmap instances that are used in xaig_to_cnf.
*)
Theory aig_fmapsProg
Ancestors
  aig_cert_encodeProg xaig_to_cnf
Libs
  preamble ml_translatorLib MapProgLib

val _ = translation_extends "aig_cert_encodeProg";

(*----------------------------------------------------------------------*
   specific types to target

   ty1-ty3 are the input and latch types of the encoded conditions; ty4-ty9
   are their gate name types, which is what the renaming in xrename_to_cnf
   is keyed by.  Everything after that renaming is at ty1.
 *----------------------------------------------------------------------*)

Type ty1[local] = “:num”;
Type ty2[local] = “:num + num”;
Type ty3[local] = “:ty2 + num”;
Type ty4[local] = “:num ext”;
Type ty5[local] = “:ty2 ext”;
Type ty6[local] = “:(ty2 + ty2) ext”;
Type ty7[local] = “:((ty2 + ty2) + ty2) ext”;
Type ty8[local] = “:ty3 ext”;
Type ty9[local] = “:(ty3 + ty2) ext”;

(*----------------------------------------------------------------------*
   ty1
 *----------------------------------------------------------------------*)

Theorem TotOrd_ty1:
  TotOrd (num_cmp : ty1 -> ty1 -> ordering)
Proof
  rewrite_tac [TotOrd_num_cmp]
QED

(*----------------------------------------------------------------------*
   ty2
 *----------------------------------------------------------------------*)

Definition num_sum_num_cmp_def:
  num_sum_num_cmp = sum_cmp num_cmp num_cmp
End

Theorem num_sum_num_cmp_eq[local] =
  num_sum_num_cmp_def |> SRULE [sum_cmp_def, num_cmp_thm, FUN_EQ_THM];

val r = translate num_sum_num_cmp_eq;

Theorem TotOrd_ty2:
  TotOrd (num_sum_num_cmp : ty2 -> ty2 -> ordering)
Proof
  rewrite_tac [num_sum_num_cmp_def]
  \\ irule TotOrd_sum \\ simp [TotOrd_ty1]
QED

(*----------------------------------------------------------------------*
   ty3
 *----------------------------------------------------------------------*)

Definition ty3_cmp_def:
  ty3_cmp = sum_cmp num_sum_num_cmp num_cmp
End

Theorem ty3_cmp_eq[local] =
  ty3_cmp_def |> SRULE [sum_cmp_def, num_sum_num_cmp_eq, num_cmp_thm, FUN_EQ_THM];

val r = translate ty3_cmp_eq;

Theorem TotOrd_ty3:
  TotOrd (ty3_cmp : ty3 -> ty3 -> ordering)
Proof
  rewrite_tac [ty3_cmp_def]
  \\ irule TotOrd_sum \\ simp [TotOrd_ty2, TotOrd_ty1]
QED

(*----------------------------------------------------------------------*
   the ext wrapper
 *----------------------------------------------------------------------*)

Definition ext_cmp_def:
  ext_cmp cmp (x1: 'a ext) (x2: 'a ext) =
    case x1 of
    | Orig n1 =>
        (case x2 of
         | Orig n2 => cmp n1 n2
         | _ => LESS)
    | Ext n1 =>
        (case x2 of
         | Orig _ => GREATER
         | Ext n2 => mlstring$compare n1 n2
         | Anon _ => LESS)
    | Anon n1 =>
        (case x2 of
         | Anon n2 => num_cmp n1 n2
         | _ => GREATER)
End

Theorem ext_forall:
  (∀x. P x) ⇔ (∀y. P (Orig y)) ∧ (∀y. P (Ext y)) ∧ (∀y. P (Anon y))
Proof
  eq_tac \\ rw [] \\ simp [] \\ Cases_on ‘x’ \\ fs []
QED

Theorem TotOrd_ext:
  TotOrd c1 ⇒ TotOrd (ext_cmp c1)
Proof
  strip_tac
  \\ mp_tac mlstringTheory.TotOrd_compare
  \\ mp_tac TotOrd_ty1
  \\ fs [totoTheory.TotOrd, ext_cmp_def, AllCaseEqs(), ext_forall]
  \\ simp [SF DNF_ss, PULL_EXISTS] \\ rw [] \\ res_tac
QED

(*----------------------------------------------------------------------*
   ty4 - ty9
 *----------------------------------------------------------------------*)

Definition ty4_cmp_def:
  ty4_cmp = ext_cmp num_cmp
End

Theorem ty4_cmp_eq[local] =
  ty4_cmp_def |> SRULE [ext_cmp_def, num_cmp_thm, FUN_EQ_THM];

val r = translate ty4_cmp_eq;

Theorem TotOrd_ty4:
  TotOrd (ty4_cmp : ty4 -> ty4 -> ordering)
Proof
  rewrite_tac [ty4_cmp_def] \\ irule TotOrd_ext \\ simp [TotOrd_ty1]
QED

Definition ty5_cmp_def:
  ty5_cmp = ext_cmp num_sum_num_cmp
End

Theorem ty5_cmp_eq[local] =
  ty5_cmp_def
  |> SRULE [ext_cmp_def, num_sum_num_cmp_eq, num_cmp_thm, FUN_EQ_THM];

val r = translate ty5_cmp_eq;

Theorem TotOrd_ty5:
  TotOrd (ty5_cmp : ty5 -> ty5 -> ordering)
Proof
  rewrite_tac [ty5_cmp_def] \\ irule TotOrd_ext \\ simp [TotOrd_ty2]
QED

Definition ty6_cmp_def:
  ty6_cmp = ext_cmp (sum_cmp num_sum_num_cmp num_sum_num_cmp)
End

Theorem ty6_cmp_eq[local] =
  ty6_cmp_def
  |> SRULE [ext_cmp_def, sum_cmp_def, num_sum_num_cmp_eq, num_cmp_thm,
            FUN_EQ_THM];

val r = translate ty6_cmp_eq;

Theorem TotOrd_ty6:
  TotOrd (ty6_cmp : ty6 -> ty6 -> ordering)
Proof
  rewrite_tac [ty6_cmp_def]
  \\ irule TotOrd_ext \\ irule TotOrd_sum \\ simp [TotOrd_ty2]
QED

Definition ty7_cmp_def:
  ty7_cmp =
    ext_cmp (sum_cmp (sum_cmp num_sum_num_cmp num_sum_num_cmp) num_sum_num_cmp)
End

Theorem ty7_cmp_eq[local] =
  ty7_cmp_def
  |> SRULE [ext_cmp_def, sum_cmp_def, num_sum_num_cmp_eq, num_cmp_thm,
            FUN_EQ_THM];

val r = translate ty7_cmp_eq;

Theorem TotOrd_ty7:
  TotOrd (ty7_cmp : ty7 -> ty7 -> ordering)
Proof
  rewrite_tac [ty7_cmp_def]
  \\ irule TotOrd_ext \\ irule TotOrd_sum
  \\ irule_at (Pos hd) TotOrd_sum
  \\ simp [TotOrd_ty2]
QED

Definition ty8_cmp_def:
  ty8_cmp = ext_cmp ty3_cmp
End

Theorem ty8_cmp_eq[local] =
  ty8_cmp_def |> SRULE [ext_cmp_def, ty3_cmp_eq, num_cmp_thm, FUN_EQ_THM];

val r = translate ty8_cmp_eq;

Theorem TotOrd_ty8:
  TotOrd (ty8_cmp : ty8 -> ty8 -> ordering)
Proof
  rewrite_tac [ty8_cmp_def] \\ irule TotOrd_ext \\ simp [TotOrd_ty3]
QED

Definition ty9_cmp_def:
  ty9_cmp = ext_cmp (sum_cmp ty3_cmp num_sum_num_cmp)
End

Theorem ty9_cmp_eq[local] =
  ty9_cmp_def
  |> SRULE [ext_cmp_def, sum_cmp_def, ty3_cmp_eq, num_sum_num_cmp_eq,
            num_cmp_thm, FUN_EQ_THM];

val r = translate ty9_cmp_eq;

Theorem TotOrd_ty9:
  TotOrd (ty9_cmp : ty9 -> ty9 -> ordering)
Proof
  rewrite_tac [ty9_cmp_def]
  \\ irule TotOrd_ext \\ irule TotOrd_sum \\ simp [TotOrd_ty3, TotOrd_ty2]
QED

(*----------------------------------------------------------------------*
   translating them all
 *----------------------------------------------------------------------*)

val _ = add_fmap_for_cmp TotOrd_ty1;
val _ = add_fmap_for_cmp TotOrd_ty2;
val _ = add_fmap_for_cmp TotOrd_ty3;
val _ = add_fmap_for_cmp TotOrd_ty4;
val _ = add_fmap_for_cmp TotOrd_ty5;
val _ = add_fmap_for_cmp TotOrd_ty6;
val _ = add_fmap_for_cmp TotOrd_ty7;
val _ = add_fmap_for_cmp TotOrd_ty8;
val _ = add_fmap_for_cmp TotOrd_ty9;

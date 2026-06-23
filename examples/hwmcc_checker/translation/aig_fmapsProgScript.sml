(*
  Setting up translator for the fmap instances that are used in aig_to_cnf.
*)
Theory aig_fmapsProg
Ancestors
  aig_cert_encodeProg aig_to_cnf
Libs
  preamble ml_translatorLib MapProgLib

val _ = translation_extends "aig_cert_encodeProg";

(*----------------------------------------------------------------------*
   specific types to target
 *----------------------------------------------------------------------*)

Type ty1[local] = “:num”;
Type ty2[local] = “:num + num”;
Type ty3[local] = “:num iext”;
Type ty4[local] = “:(num + num) iext”;
Type ty5[local] = “:(num iext + num iext) iext”;
Type ty6[local] = “:((num + num) iext + (num + num) iext) iext”;
Type ty7[local] = “:(ty6 + ty4) iext”
Type ty8[local] = “:(ty5 + ty3) iext”
Type ty9[local] = “:(((ty8 + ty3) iext) + ty3) iext”
Type ty10[local] = “:(ty8 + ty4) iext”
Type ty11[local] = “:(num + num) + num”

(*----------------------------------------------------------------------*
   ty1
 *----------------------------------------------------------------------*)

val _ = translate num_cmp_def;

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
  num_sum_num_cmp_def |> SRULE [sum_cmp_def, num_cmp_def, FUN_EQ_THM];

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

Definition ext_cmp_def:
  ext_cmp cmp (x1: 'a ext) (x2: 'a ext) =
    case x1 of
    | Orig n1 =>
        (case x2 of
         | Orig n2 => cmp n1 n2
         | Ext _ => LESS)
    | Ext n1 =>
        (case x2 of
         | Orig _ => GREATER
         | Ext n2 => mlstring$compare n1 n2)
End

Definition iext_cmp_def:
  iext_cmp cmp (x1: 'a iext) (x2: 'a iext) =
    case x1 of
    | Named n1 =>
        (case x2 of
         | Named n2 => ext_cmp cmp n1 n2
         | Anon _ => LESS)
    | Anon n1 =>
        (case x2 of
         | Named _ => GREATER
         | Anon n2 => num_cmp n1 n2)
End

Theorem ext_forall:
  (∀x. P x) ⇔ (∀y. P (Orig y)) ∧ (∀y. P (Ext y))
Proof
  eq_tac \\ rw [] \\ simp [] \\ Cases_on ‘x’ \\ fs []
QED

Theorem iext_forall:
  (∀x. P x) ⇔ (∀y. P (Named y)) ∧ (∀y. P (Anon y))
Proof
  eq_tac \\ rw [] \\ simp [] \\ Cases_on ‘x’ \\ fs []
QED

Theorem TotOrd_ext:
  TotOrd c1 ⇒ TotOrd (ext_cmp c1)
Proof
  mp_tac mlstringTheory.TotOrd_compare
  \\ fs [totoTheory.TotOrd, ext_cmp_def, AllCaseEqs(), ext_forall]
  \\ simp [SF DNF_ss, PULL_EXISTS] \\ rw [] \\ res_tac
QED

Theorem TotOrd_iext:
  TotOrd c1 ⇒ TotOrd (iext_cmp c1)
Proof
  strip_tac \\ dxrule TotOrd_ext
  \\ mp_tac TotOrd_ty1
  \\ fs [totoTheory.TotOrd, iext_cmp_def, AllCaseEqs(), iext_forall]
  \\ simp [SF DNF_ss, PULL_EXISTS] \\ rw [] \\ res_tac
QED

Definition num_iext_cmp_def:
  num_iext_cmp = iext_cmp num_cmp
End

Theorem num_iext_cmp_eq[local] =
  num_iext_cmp_def |> SRULE [iext_cmp_def, num_cmp_def, FUN_EQ_THM, ext_cmp_def];

val r = translate num_iext_cmp_eq;

Theorem TotOrd_ty3:
  TotOrd (num_iext_cmp : ty3 -> ty3 -> ordering)
Proof
  rewrite_tac [num_iext_cmp_def]
  \\ irule TotOrd_iext \\ simp [TotOrd_ty1]
QED

(*----------------------------------------------------------------------*
   ty4
 *----------------------------------------------------------------------*)

Definition ty4_cmp_def:
  ty4_cmp = iext_cmp num_sum_num_cmp
End

Theorem ty4_cmp_eq[local] =
  ty4_cmp_def
  |> SRULE [iext_cmp_def, num_sum_num_cmp_eq, FUN_EQ_THM, ext_cmp_def, num_cmp_def];

val r = translate ty4_cmp_eq;

Theorem TotOrd_ty4:
  TotOrd (ty4_cmp : ty4 -> ty4 -> ordering)
Proof
  rewrite_tac [ty4_cmp_def]
  \\ irule TotOrd_iext \\ simp [TotOrd_ty2]
QED

(*----------------------------------------------------------------------*
   ty5
 *----------------------------------------------------------------------*)

Definition ty5_cmp_def:
  ty5_cmp = iext_cmp (sum_cmp num_iext_cmp num_iext_cmp)
End

Theorem ty5_cmp_eq[local] =
  ty5_cmp_def
  |> SRULE [iext_cmp_def, FUN_EQ_THM, ext_cmp_def, num_cmp_def, sum_cmp_def];

val r = translate ty5_cmp_eq;

Theorem TotOrd_ty5:
  TotOrd (ty5_cmp : ty5 -> ty5 -> ordering)
Proof
  rewrite_tac [ty5_cmp_def]
  \\ irule TotOrd_iext
  \\ irule TotOrd_sum
  \\ simp [TotOrd_ty3]
QED

(*----------------------------------------------------------------------*
   ty6
 *----------------------------------------------------------------------*)

Definition ty6_cmp_def:
  ty6_cmp = iext_cmp (sum_cmp ty4_cmp ty4_cmp)
End

Theorem ty6_cmp_eq[local] =
  ty6_cmp_def
  |> SRULE [iext_cmp_def, FUN_EQ_THM, ext_cmp_def, num_cmp_def, sum_cmp_def];

val r = translate ty6_cmp_eq;

Theorem TotOrd_ty6:
  TotOrd (ty6_cmp : ty6 -> ty6 -> ordering)
Proof
  rewrite_tac [ty6_cmp_def]
  \\ irule TotOrd_iext
  \\ irule TotOrd_sum
  \\ simp [TotOrd_ty4]
QED

(*----------------------------------------------------------------------*
   ty7
 *----------------------------------------------------------------------*)

Definition ty7_cmp_def:
  ty7_cmp = iext_cmp (sum_cmp ty6_cmp ty4_cmp)
End

Theorem ty7_cmp_eq[local] =
  ty7_cmp_def
  |> SRULE [iext_cmp_def, FUN_EQ_THM, ext_cmp_def, num_cmp_def, sum_cmp_def];

val r = translate ty7_cmp_eq;

Theorem TotOrd_ty7:
  TotOrd (ty7_cmp : ty7 -> ty7 -> ordering)
Proof
  rewrite_tac [ty7_cmp_def]
  \\ irule TotOrd_iext
  \\ irule TotOrd_sum
  \\ simp [TotOrd_ty6, TotOrd_ty4]
QED

(*----------------------------------------------------------------------*
   ty8
 *----------------------------------------------------------------------*)

Definition ty8_cmp_def:
  ty8_cmp = iext_cmp (sum_cmp ty5_cmp num_iext_cmp)
End

Theorem ty8_cmp_eq[local] =
  ty8_cmp_def
  |> SRULE [iext_cmp_def, FUN_EQ_THM, ext_cmp_def, num_cmp_def, sum_cmp_def];

val r = translate ty8_cmp_eq;

Theorem TotOrd_ty8:
  TotOrd (ty8_cmp : ty8 -> ty8 -> ordering)
Proof
  rewrite_tac [ty8_cmp_def]
  \\ irule TotOrd_iext
  \\ irule TotOrd_sum
  \\ simp [TotOrd_ty5, TotOrd_ty3]
QED

(*----------------------------------------------------------------------*
   ty9
 *----------------------------------------------------------------------*)

Definition ty9_cmp_def:
  ty9_cmp = iext_cmp (sum_cmp (iext_cmp (sum_cmp ty8_cmp num_iext_cmp)) num_iext_cmp)
End

Theorem ty9_cmp_eq[local] =
  ty9_cmp_def
  |> SRULE [iext_cmp_def, FUN_EQ_THM, ext_cmp_def, num_cmp_def, sum_cmp_def];

val r = translate ty9_cmp_eq;

Theorem TotOrd_ty9:
  TotOrd (ty9_cmp : ty9 -> ty9 -> ordering)
Proof
  rewrite_tac [ty9_cmp_def]
  \\ irule TotOrd_iext
  \\ irule TotOrd_sum
  \\ irule_at (Pos hd) TotOrd_iext
  \\ irule_at (Pos hd) TotOrd_sum
  \\ simp [TotOrd_ty8, TotOrd_ty3]
QED

(*----------------------------------------------------------------------*
   ty10
 *----------------------------------------------------------------------*)

Definition ty10_cmp_def:
  ty10_cmp = iext_cmp (sum_cmp ty8_cmp ty4_cmp)
End

Theorem ty10_cmp_eq[local] =
  ty10_cmp_def
  |> SRULE [iext_cmp_def, FUN_EQ_THM, ext_cmp_def, num_cmp_def, sum_cmp_def];

val r = translate ty10_cmp_eq;

Theorem TotOrd_ty10:
  TotOrd (ty10_cmp : ty10 -> ty10 -> ordering)
Proof
  rewrite_tac [ty10_cmp_def]
  \\ irule TotOrd_iext
  \\ irule TotOrd_sum
  \\ simp [TotOrd_ty8, TotOrd_ty4]
QED

(*----------------------------------------------------------------------*
   ty11
 *----------------------------------------------------------------------*)

Definition ty11_cmp_def:
  ty11_cmp = sum_cmp num_sum_num_cmp num_cmp
End

Theorem ty11_cmp_eq[local] =
  ty11_cmp_def
  |> SRULE [sum_cmp_def, num_sum_num_cmp_eq, num_cmp_def, FUN_EQ_THM];

val r = translate ty11_cmp_eq;

Theorem TotOrd_ty11:
  TotOrd (ty11_cmp : ty11 -> ty11 -> ordering)
Proof
  rewrite_tac [ty11_cmp_def]
  \\ irule TotOrd_sum
  \\ simp [TotOrd_ty2, TotOrd_ty1]
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
val _ = add_fmap_for_cmp TotOrd_ty10;
val _ = add_fmap_for_cmp TotOrd_ty11;

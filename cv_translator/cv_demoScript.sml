(*
  Demo use of cv translator
*)
open HolKernel Parse boolLib bossLib;
open cv_typeTheory cvTheory cv_typeLib cv_repLib;
open arithmeticTheory wordsTheory cv_repTheory cv_primTheory cv_transLib wordsLib;

val _ = new_theory "cv_demo";

Overload c2n[local] = “cv$c2n”
Overload c2b[local] = “cv$c2b”
Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

Definition add1_def:
  add1 a xs = MAP (λx. x + a:num) xs
End

val _ = cv_auto_trans add1_def;

Definition genlist_def:
  genlist i f 0 = [] ∧
  genlist i f (SUC n) = f i :: genlist (i+1:num) f n
End

Theorem genlist_eq_GENLIST[cv_inline]:
  GENLIST = genlist 0
Proof
  qsuff_tac ‘∀i f n. genlist i f n = GENLIST (f o (λk. k + i)) n’
  >- (gvs [FUN_EQ_THM] \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FUN_EQ_THM])
  \\ Induct_on ‘n’ \\ gvs [genlist_def]
  \\ rewrite_tac [listTheory.GENLIST_CONS] \\ gvs []
  \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FUN_EQ_THM,arithmeticTheory.ADD1]
QED

Definition mult_table_def:
  mult_table n = GENLIST (λi. GENLIST (λj. i * j) n) n
End

val _ = cv_auto_trans mult_table_def;

Datatype:
  rec = <| abc : num ; def : num; rest : rec list |>
End

Definition rec_test1_def:
  rec_test1 r = r.abc + 1
End

val _ = cv_auto_trans rec_test1_def;

Definition rec_test2_def:
  rec_test2 r = r with <| rest := r :: r.rest |>
End

val _ = cv_auto_trans rec_test2_def;

Definition rec_test3_def:
  rec_test3 r = <| abc := 4; def := 45; rest := r.rest |>
End

val _ = cv_auto_trans rec_test3_def;

Definition fac_def:
  fac (n:num) = if n = 0:num then 1 else n * fac (n-1)
End

Definition inc_def:
  inc n = n + 1:num
End

Definition risky_def:
  risky n = if n = 0 then ARB else n+1:num
End

Definition foo_def:
  foo (n:num) k i = if n = 0:num then k + i + 1:num else
                    if 500 < n then ARB else n * foo (n-1) i k
End

Definition use_foo_def:
  use_foo n = foo 1 (n + 2) 3
End

Theorem cond_def_lemma:
  ∃(f:num -> num). ∀n. n ≠ 0 ⇒ f n = n - 1
Proof
  qexists_tac ‘λn. n - 1’ \\ fs []
QED

val cond_def = new_specification("cond_sub_def",["cond_sub"],cond_def_lemma);

val res = cv_trans fac_def;
val res = cv_trans_pre foo_def;
val res = cv_trans_pre use_foo_def;
val res = cv_trans_pre risky_def;
val res = cv_trans inc_def;
val res = cv_trans_pre cond_def;

Datatype:
  a_type = A_cons | B_cons | C_cons num num | D_cons (a_type list)
End

Definition a_fun_def:
  a_fun n = D_cons [A_cons; C_cons n 5]
End

val res = cv_trans a_fun_def;

open sptreeTheory

Datatype:
  b_type = B1 | B2 | B3 | B4 | B5 | B6 | B7
End

Datatype:
  c_type = C1 num | C2 c_type | C3 c_type
End

Definition num_sum_def:
  num_sum ns =
    case ns of [] => 0:num | (n::ns) => n + num_sum ns
End

val res = cv_trans num_sum_def;
val res = cv_trans listTheory.LENGTH;
(* val res = cv_trans_pre lookup_def; *)

Definition f1_def:
  f1 (n:num) = 1:num
End

Definition f2_def:
  f2 n = f1 n
End

Definition f3_def:
  f3 n = f2 n
End

val res = cv_auto_trans f3_def;

Definition fw1_def:
  fw1 w = w + 1w
End

Definition fw2_def:
  fw2 w = fw1 (w:word8)
End

val res = cv_auto_trans fw2_def;

Definition hello_def:
  hello xs = "HELLO!" ++ xs
End

val res = cv_auto_trans hello_def;

val res = time cv_eval “f3 (1+2)”;

Definition even_def:
  even 0 = T ∧
  even (SUC n) = odd n ∧
  odd 0 = F ∧
  odd (SUC n) = even n
End

val res = cv_trans_pre even_def

Theorem even_pre[local,cv_pre]:
  (∀a0. even_pre a0) ∧
  (∀a1. odd_pre a1)
Proof
  ho_match_mp_tac even_ind \\ rpt strip_tac
  \\ once_rewrite_tac [res] \\ fs []
QED

val th = cv_eval “even 10”
val th = cv_eval “even 999999”

Definition test_u2_def:
  test_u2 n = (n+1:num,())
End

val _ = cv_trans test_u2_def;

val _ = export_theory();

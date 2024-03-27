(*
  Define cv_rep and prove a few lemmas used in proof automation
*)
open HolKernel Parse boolLib bossLib;
open cvTheory cv_typeTheory;

val _ = new_theory "cv_rep";

Overload c2n[local] = “cv$c2n”
Overload c2b[local] = “cv$c2b”
Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

Definition cv_rep_def:
  cv_rep pre_cond (cv_tm:cv) (from_fun:'a -> cv) hol_tm <=>
    pre_cond ==>
    from_fun hol_tm = cv_tm
End

Theorem cv_rep_trivial:
  !f n. cv_rep T (f n) f n
Proof
  fs [cv_rep_def]
QED

Theorem cv_rep_move:
  (b ==> cv_rep p x y z) = cv_rep (b /\ p) x y z
Proof
  Cases_on ‘b’ \\ gvs [cv_rep_def]
QED

Theorem cv_rep_eval:
  cv_rep p y f (x:'a) ==>
  from_to f t ==>
  p ==> x = t y
Proof
  rw [] \\ gvs [cv_rep_def,from_to_def]
QED

Theorem cv_rep_assum:
  cv_rep p (cv (g a)) (f:'a -> cv) x ==>
  !cv_a p_a.
    cv_rep p_a cv_a g a ==>
    cv_rep (p_a /\ p) (cv cv_a) f x
Proof
  gvs [cv_rep_def]
QED

Theorem IMP_COMM:
  (b1 ==> b2 ==> c) = (b2 ==> b1 ==> c)
Proof
  Cases_on ‘b1’ \\ Cases_on ‘b2’ \\ rewrite_tac []
QED

Theorem IMP_CANCEL:
  (b ==> b ==> c) = (b ==> c)
Proof
  Cases_on ‘b’ \\ fs []
QED

Theorem if_eq_zero:
  (if n = 0 then x else y) = (if 0 < (n:num) then y else x:'a)
Proof
  Cases_on ‘n’ \\ gvs []
QED

Theorem lt_zero:
  0 < n <=> n <> 0:num
Proof
  Cases_on ‘n’ \\ gvs []
QED

Theorem cv_eval[compute]:
  c2n (Num n) = n /\
  c2n (Pair x y) = 0 /\
  c2b (Num n) = (n <> 0) /\
  c2b (Pair x y) = F
Proof
  gvs [cvTheory.c2n_def,cvTheory.c2b_def]
  \\ Cases_on ‘n’ \\ gvs []
QED

Theorem UNCURRY_pair_case:
  !f. UNCURRY f = \x. case x of (x,y) => f x y
Proof
  strip_tac \\ fs [FUN_EQ_THM] \\ Cases \\ fs []
QED

Definition cv_sum_depth_def[simp]:
  cv_sum_depth (Num n) = n /\
  cv_sum_depth (Pair x y) = 1 + cv_sum_depth x + cv_sum_depth y
End

Definition cv_proj_def:
  cv_proj [] v = v /\
  cv_proj (T::xs) v = cv_fst (cv_proj xs v) /\
  cv_proj (F::xs) v = cv_snd (cv_proj xs v)
End

Theorem cv_proj_less_eq:
  !v xs. cv_sum_depth (cv_proj xs v) <= cv_sum_depth v
Proof
  gen_tac \\ Induct \\ gvs [cv_proj_def]
  \\ Cases \\ gvs [cv_proj_def] \\ rw []
  \\ irule arithmeticTheory.LESS_EQ_TRANS
  \\ pop_assum $ irule_at (Pos last)
  \\ Cases_on ‘cv_proj xs v’ \\ gvs [cv_sum_depth_def]
QED

Theorem to_cv_proj:
  cv_fst = cv_proj [T] /\
  cv_snd = cv_proj [F] /\
  cv_proj xs (cv_proj ys b) = cv_proj (xs ++ ys) b
Proof
  gvs [FUN_EQ_THM,cv_proj_def]
  \\ Induct_on ‘xs’ \\ gvs [cv_proj_def]
  \\ Cases \\ gvs [cv_proj_def]
QED

Theorem cv_termination_simp:
  (c2b (cv_ispair cv_v) = ?x1 x2. cv_v = Pair x1 x2) /\
  (c2b (cv_lt (Num 0) cv_v) = ?k. cv_v = Num (SUC k)) /\
  (c2b (cv_lt (Num (NUMERAL (BIT1 n))) (cv_fst cv_v)) <=>
   ?k z. cv_v = Pair (Num k) z /\ NUMERAL (BIT1 n) < k) /\
  (c2b (cv_lt (Num (NUMERAL (BIT2 n))) (cv_fst cv_v)) <=>
   ?k z. cv_v = Pair (Num k) z /\ NUMERAL (BIT2 n) < k) /\
  (cv_fst cv_v = Pair x y <=> ?z. cv_v = Pair (Pair x y) z) /\
  (cv_snd cv_v = Pair x y <=> ?z. cv_v = Pair z (Pair x y)) /\
  (cv_fst cv_v = Num (SUC k) <=> ?z. cv_v = Pair (Num (SUC k)) z) /\
  (cv_snd cv_v = Num (SUC k) <=> ?z. cv_v = Pair z (Num (SUC k)))
Proof
  Cases_on ‘cv_v’ \\ gvs [] \\ rw []
  \\ gvs [c2b_def,arithmeticTheory.NUMERAL_DEF]
  \\ rpt $ pop_assum mp_tac
  \\ rewrite_tac [arithmeticTheory.BIT1,arithmeticTheory.BIT2] \\ gvs []
  >- (Cases_on ‘m’ \\ gvs [])
  \\ rename [‘cv_lt _ g’] \\ Cases_on ‘g’ \\ fs [] \\ rw []
QED

Definition implies_def:
  implies x y <=> (x ==> y)
End

Theorem cv_postprocess:
  cv_if c x x = x
Proof
  fs [cv_if_def]
QED

val _ = export_theory();

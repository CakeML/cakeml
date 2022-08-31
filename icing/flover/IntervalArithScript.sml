(**
  Formalization of real valued interval arithmetic
  Used in soundness proofs for error bound validator.
**)
open realTheory realLib RealArith
open AbbrevsTheory ExpressionsTheory RealSimpsTheory FloverTactics;
open preambleFloVer;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "IntervalArith";

Overload abs[local] = “realax$abs”
Overload max[local] = “realax$max”
Overload min[local] = “realax$min”

(**
  Define validity of an interval, requiring that the lower bound is less than or equal to the upper bound.
  Containement is defined such that if x is contained in the interval, it must lie between the lower and upper bound.
**)
Definition valid_def:
  valid (iv:interval) = (IVlo iv <= IVhi iv)
End

Definition contained_def:
  contained (a:real) (iv:interval) = (IVlo iv <= a /\ a <= IVhi iv)
End

(**
Subset definition; when an interval is a subinterval of another
**)
Definition isSupersetInterval_def:
  isSupersetInterval (iv1:interval) (iv2:interval) =
  ((IVlo iv2 <= IVlo iv1) /\ (IVhi iv1 <= IVhi iv2))
End

Definition pointInterval_def:
  pointInterval (x:real) = (x,x)
End

(**
Definitions of validity conditions for interval operations: Addition,
Subtraction, Multiplication and Division
**)
Definition validIntervalAdd_def:
validIntervalAdd (iv1:interval) (iv2:interval) (iv3:interval) =
(! a b. contained a iv1 /\ contained b iv2 ==> contained (a + b) iv3)
End

val validIntervalSub_def = Define `
validIntervalSub (iv1:interval) (iv2:interval) (iv3:interval) =
(! a b. contained a iv1 /\ contained b iv2 ==> contained (a - b) iv3)`;

val validIntervalMult_def = Define`
validIntervalMult (iv1:interval) (iv2:interval) (iv3:interval) =
(! a b. contained a iv1 /\ contained b iv2 ==> contained (a * b) iv3)`;

val validIntervalDiv_def = Define `
validIntervalDiv (iv1:interval) (iv2:interval) (iv3:interval) =
(! a b. contained a iv1 /\ contained b iv2 ==> contained (a / b) iv3)`;

Definition min4_def:
  min4 a b c d = min a (min b (min c d))
End

Definition max4_def:
  max4 a b c d = max a (max b (max c d))
End

Definition absIntvUpd_def:
  absIntvUpd (op:real->real->real) (iv1:interval) (iv2:interval) =
  (
  min4 (op (IVlo iv1) (IVlo iv2))
       (op (IVlo iv1) (IVhi iv2))
       (op (IVhi iv1) (IVlo iv2))
       (op (IVhi iv1) (IVhi iv2)),
  max4 (op (IVlo iv1) (IVlo iv2))
       (op (IVlo iv1) (IVhi iv2))
       (op (IVhi iv1) (IVlo iv2))
       (op (IVhi iv1) (IVhi iv2))
  )
End

Definition widenInterval_def:
  widenInterval (iv:interval) (v:real) = ((IVlo iv - v), (IVhi iv + v))
End

Definition negateInterval_def:
  negateInterval (iv:interval) = ((- IVhi iv), (- IVlo iv))
End

Definition invertInterval_def:
  invertInterval (iv:interval)  = (1 /(IVhi iv), 1 /(IVlo iv))
End

Definition sqrtInterval_def:
  sqrtInterval (iv:interval) = (sqrt (IVlo iv), sqrt (IVhi iv))
End

Definition addInterval_def:
  addInterval (iv1:interval) (iv2:interval) = absIntvUpd (+) iv1 iv2
End

Definition subtractInterval_def:
  subtractInterval (iv1:interval) (iv2:interval) = addInterval iv1 (negateInterval iv2)
End

Definition multInterval_def:
  multInterval (iv1:interval) (iv2:interval) = absIntvUpd ( * ) iv1 iv2
End

Definition divideInterval_def:
  divideInterval iv1 iv2 = multInterval iv1 (invertInterval iv2)
End

Definition minAbsFun_def:
  minAbsFun iv = min (abs (FST iv)) (abs (SND iv))
End

val iv_ss = [IVlo_def, IVhi_def, valid_def, contained_def, isSupersetInterval_def,
                     pointInterval_def, validIntervalAdd_def,
                     validIntervalSub_def, validIntervalMult_def,
                     validIntervalDiv_def,
                     min4_def, max4_def,
                     absIntvUpd_def, widenInterval_def,
                     negateInterval_def,
                     invertInterval_def,
                     addInterval_def, subtractInterval_def,
                     multInterval_def, divideInterval_def,
                     maxAbs_def, minAbsFun_def
                    ];

Theorem contained_implies_valid:
  !(a:real) (iv:interval).
  contained a iv ==> valid iv
Proof
  metis_tac (iv_ss @ [REAL_LE_TRANS])
QED

Theorem contained_implies_subset:
  !(a:real) (iv:interval).
    contained a iv ==> isSupersetInterval (pointInterval a) iv
Proof
  fs iv_ss
QED

Theorem validPointInterval:
  !(a:real). contained a (pointInterval a)
Proof
  fs iv_ss
QED

Theorem min4_correct:
  !a b c d.
    let m = min4 a b c d in
      m <= a /\ m <= b /\ m <= c /\ m <= d
Proof
rpt strip_tac \\fs [min4_def] \\ conj_tac \\
try (fs [REAL_MIN_LE1]) \\ conj_tac
>- (`min b (min c d) <= b` by fs[REAL_MIN_LE1] \\
   match_mp_tac REAL_LE_TRANS \\
   HINT_EXISTS_TAC \\
   fs [REAL_MIN_LE2])
>- (conj_tac
    >- (`min c d <= c` by fs [REAL_MIN_LE1] \\
       match_mp_tac REAL_LE_TRANS \\
       HINT_EXISTS_TAC \\
       fs [REAL_MIN_LE2] \\
       match_mp_tac REAL_LE_TRANS \\
       `min b (min c d) <= min c d` by fs[REAL_MIN_LE2] \\
       HINT_EXISTS_TAC \\
       fs [REAL_MIN_LE2] )
    >- (`min c d <= d` by fs [REAL_MIN_LE2] \\
       match_mp_tac REAL_LE_TRANS \\
       HINT_EXISTS_TAC \\
       fs [REAL_MIN_LE2] \\
       match_mp_tac REAL_LE_TRANS \\
       `min b (min c d) <= min c d` by fs[REAL_MIN_LE2] \\
       HINT_EXISTS_TAC \\
        fs [REAL_MIN_LE2]))
QED

Theorem max4_correct:
  !a b c d.
  let m = max4 a b c d in
    a <= m /\ b <= m /\ c <= m /\ d <= m
Proof
rpt strip_tac \\fs [max4_def] \\ conj_tac \\
try (fs [REAL_LE_MAX1]) \\ conj_tac
>-(`b <= max b (max c d)` by fs[REAL_LE_MAX1] \\
match_mp_tac REAL_LE_TRANS \\
HINT_EXISTS_TAC \\
fs [REAL_LE_MAX2])
>- (conj_tac
    >- (`c <= max c d` by fs [REAL_LE_MAX1] \\
       match_mp_tac REAL_LE_TRANS \\
       HINT_EXISTS_TAC \\
       fs [REAL_LE_MAX2] \\
       match_mp_tac REAL_LE_TRANS \\
       `max c d <= max b (max c d)` by fs[REAL_LE_MAX2] \\
       HINT_EXISTS_TAC \\
       fs [REAL_LE_MAX2] )
    >- (`d <= max c d` by fs [REAL_LE_MAX2] \\
       match_mp_tac REAL_LE_TRANS \\
       HINT_EXISTS_TAC \\
       fs [REAL_LE_MAX2] \\
       match_mp_tac REAL_LE_TRANS \\
       `max c d <= max b (max c d)` by fs[REAL_LE_MAX2] \\
       HINT_EXISTS_TAC \\
        fs [REAL_LE_MAX2] ))
QED

Theorem interval_negation_valid:
  !iv a. contained a iv ==> contained (- a) (negateInterval iv)
Proof
  fs iv_ss
QED

Theorem iv_neg_preserves_valid:
  !iv.
    valid iv ==> valid (negateInterval iv)
Proof
  fs [valid_def, negateInterval_def, IVlo_def, IVhi_def]
QED

Theorem interval_inversion_valid:
  !iv a.
    (IVhi iv < 0 \/ 0 < IVlo iv) /\ contained a iv ==>
    contained (inv a) (invertInterval iv)
Proof
  fs iv_ss \\ rpt strip_tac \\ once_rewrite_tac [GSYM REAL_INV_1OVER]
  (* First subgoal *)
  >- (once_rewrite_tac [GSYM REAL_LE_NEG]
      \\ `0 < - a` by REAL_ASM_ARITH_TAC
      \\ `a <> 0` by REAL_ASM_ARITH_TAC
      \\ `0 < - SND iv` by REAL_ASM_ARITH_TAC
      \\ `SND iv <> 0` by REAL_ASM_ARITH_TAC
      \\ `-a⁻¹ = (-a)⁻¹` by (match_mp_tac REAL_NEG_INV \\ simp[])
      \\ `-(SND iv)⁻¹ = (-(SND iv))⁻¹` by (match_mp_tac REAL_NEG_INV \\ simp [])
      \\ asm_rewrite_tac []
      \\ `inv(-a) ≤ inv (-SND iv) <=> (- SND iv) <= - a` by (match_mp_tac REAL_INV_LE_ANTIMONO \\ fs [])
      \\ fs [])
  (* Second subgoal *)
  >- (once_rewrite_tac [GSYM REAL_LE_NEG]
      \\ `a < 0` by REAL_ASM_ARITH_TAC
      \\ `0 < -a` by REAL_ASM_ARITH_TAC
      \\ `- a <> 0` by REAL_ASM_ARITH_TAC
      \\ `a <> 0` by REAL_ASM_ARITH_TAC
      \\ `-a⁻¹ = (-a)⁻¹` by (match_mp_tac REAL_NEG_INV \\ simp [])
      \\ `-(FST iv)⁻¹ = (-(FST iv))⁻¹`
           by (match_mp_tac REAL_NEG_INV \\ simp []
               \\ try REAL_ASM_ARITH_TAC \\ asm_rewrite_tac [])
      \\ `inv (- (FST iv)) <= inv (- a) <=> - a <= - (FST iv)`
           by (match_mp_tac REAL_INV_LE_ANTIMONO \\ REAL_ASM_ARITH_TAC)
      \\ REAL_ASM_ARITH_TAC)
  (* Third subgoal *)
  >- (rewrite_tac [GSYM REAL_INV_1OVER]
      \\ `inv (SND iv) <= inv a <=> a <= SND iv`
           by (match_mp_tac REAL_INV_LE_ANTIMONO \\ REAL_ASM_ARITH_TAC)
      \\ REAL_ASM_ARITH_TAC)
  (* Fourth subgoal *)
  >- (rewrite_tac [GSYM REAL_INV_1OVER]
      \\ `inv a <= inv (FST iv) <=> FST iv <= a`
           by (match_mp_tac REAL_INV_LE_ANTIMONO \\ REAL_ASM_ARITH_TAC)
      \\ REAL_ASM_ARITH_TAC)
QED

Theorem iv_inv_preserves_valid:
  ∀ iv.
   (IVhi iv < 0 ∨ 0 < IVlo iv) ∧ valid iv ⇒ valid (invertInterval iv)
Proof
  fs [valid_def, invertInterval_def, IVlo_def, IVhi_def]
  \\ rpt strip_tac
  >- (fs [GSYM REAL_INV_1OVER]
      \\ `- (inv (FST iv)) <= - (inv (SND iv))` suffices_by fs []
      \\ `0 < - SND iv` by REAL_ASM_ARITH_TAC
      \\ `- (inv (FST iv)) = inv (- (FST iv))` by (match_mp_tac REAL_NEG_INV \\ REAL_ASM_ARITH_TAC)
      \\ `- (inv (SND iv)) = inv (- (SND iv))` by (match_mp_tac REAL_NEG_INV \\ REAL_ASM_ARITH_TAC)
      \\ rpt (qpat_x_assum `- (inv _) = _` (fn thm => rewrite_tac [thm]))
      \\ match_mp_tac REAL_INV_LE_ANTIMONO_IMPR
      \\ rpt CONJ_TAC \\ fs []
      \\ match_mp_tac REAL_LET_TRANS
      \\ asm_exists_tac \\ fs [])
  \\ rewrite_tac [GSYM REAL_INV_1OVER]
  \\ match_mp_tac REAL_INV_LE_ANTIMONO_IMPR
  \\ rpt CONJ_TAC \\ fs []
  \\ match_mp_tac REAL_LTE_TRANS
  \\ asm_exists_tac \\ fs []
QED

Theorem iv_sqrt_preserves_valid:
  ∀ iv.
    0 ≤ IVlo iv ∧ valid iv ⇒ valid (sqrtInterval iv)
Proof
  gs[valid_def, sqrtInterval_def] \\ rpt strip_tac
  \\ irule SQRT_MONO_LE \\ gs[]
QED

Theorem interval_addition_valid:
  !iv1 iv2. validIntervalAdd iv1 iv2 (addInterval iv1 iv2)
Proof
fs iv_ss \\ rpt strip_tac
(* First subgoal, lower bound *)
>- (`FST iv1 + FST iv2 <= a + b`
     by (match_mp_tac REAL_LE_ADD2 \\ fs []) \\
   match_mp_tac REAL_LE_TRANS \\
   HINT_EXISTS_TAC \\ strip_tac \\ fs[REAL_MIN_LE1])
(* Second subgoal, upper bound *)
>- (`a + b <= SND iv1 + SND iv2`
     by (match_mp_tac REAL_LE_ADD2 \\ fs []) \\
   match_mp_tac REAL_LE_TRANS \\
    HINT_EXISTS_TAC \\ strip_tac \\ fs [REAL_LE_MAX])
QED

Theorem iv_add_preserves_valid:
  !iv1 iv2.
      valid iv1 /\ valid iv2 ==>
      valid (addInterval iv1 iv2)
Proof
  fs [valid_def, addInterval_def, IVlo_def, IVhi_def, absIntvUpd_def, min4_def, max4_def]
  \\ rpt strip_tac
  \\ match_mp_tac REAL_LE_TRANS
  \\ qexists_tac `FST iv1 + FST iv2` \\ fs [REAL_MIN_LE1]
  \\ match_mp_tac REAL_LE_TRANS
  \\ qexists_tac `FST iv1 + FST iv2` \\ fs [REAL_LE_MAX1]
QED

Theorem interval_subtraction_valid:
  !iv1 iv2. validIntervalSub iv1 iv2 (subtractInterval iv1 iv2)
Proof
rpt gen_tac \\ Cases_on `iv2` \\ rewrite_tac (iv_ss @ [real_sub]) \\
rpt gen_tac \\ strip_tac \\
(** TODO: FIXME, use qspecl_then or sth else **)
match_mp_tac (REWRITE_RULE (iv_ss @ [FST,SND]) (SPECL [``iv1:interval``,``(-r,-q):interval``] interval_addition_valid)) \\
fs []
QED

Theorem iv_sub_preserves_valid:
  !iv1 iv2.
      valid iv1 /\ valid iv2 ==>
      valid (subtractInterval iv1 iv2)
Proof
  once_rewrite_tac [subtractInterval_def]
  \\ rpt strip_tac
  \\ match_mp_tac iv_add_preserves_valid
  \\ conj_tac \\ fs []
  \\ match_mp_tac iv_neg_preserves_valid \\ fs []
QED

Theorem interval_multiplication_valid:
  !iv1 iv2 a b.
    contained a iv1 /\ contained b iv2 ==>
    contained (a * b) (multInterval iv1 iv2)
Proof
  fs iv_ss \\ rpt strip_tac
  (* Lower Bound *)
  (* Case distinction for a *)
  >- (
    qspecl_then [`a`,`0`] assume_tac REAL_LTE_TOTAL \\ fs[]
    (* First case: a < 0 *)
    >- (
      `a <= 0 /\ a <> 0` by fs[REAL_LT_LE]
      (* Case distinction for SND iv2 *)
      \\ qspecl_then [`SND iv2`, `0`] assume_tac REAL_LTE_TOTAL \\ fs[]
      (* First case: SND iv2 < 0 *)
      >- (match_mp_tac REAL_LE_TRANS
          \\ qexists_tac `SND iv1 * SND iv2`
          \\ conj_tac
          >- metis_tac [CONV_RULE (DEPTH_CONV let_CONV) min4_correct, min4_def]
          \\ irule REAL_LE_TRANS
          \\ qexists_tac `a * SND iv2` \\ conj_tac
          >- (
             once_rewrite_tac[REAL_MUL_SYM]
             \\ irule REAL_MUL_LE_COMPAT_NEG_L \\ fs[REAL_LT_LE])
           \\ irule REAL_MUL_LE_COMPAT_NEG_L
           \\ fs [REAL_LT_LE])
      (* Second case: 0 <= SND iv2 *)
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `FST iv1 * SND iv2` \\ conj_tac
      >- metis_tac [CONV_RULE (DEPTH_CONV let_CONV) min4_correct, min4_def]
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `a * SND iv2` \\ conj_tac
      \\ fs[REAL_LE_RMUL_IMP, REAL_MUL_LE_COMPAT_NEG_L])
    (* Second case: 0 <= a*)
    (* Case distinction for FST iv2 *)
    \\ qspecl_then [`FST iv2`, `0`] assume_tac REAL_LTE_TOTAL \\ fs[]
    >- (
      irule REAL_LE_TRANS
      \\ qexists_tac `FST iv2 * SND iv1`
      \\ conj_tac
      >- metis_tac [CONV_RULE (DEPTH_CONV let_CONV) min4_correct, min4_def]
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `FST iv2 * a` \\ conj_tac
      >- (irule REAL_MUL_LE_COMPAT_NEG_L \\ fs[REAL_LT_LE])
      \\ metis_tac [REAL_MUL_COMM, REAL_LE_RMUL_IMP])
    (* Second case: 0 <= FST iv2 *)
    \\ irule REAL_LE_TRANS
    \\ qexists_tac `FST iv1 * FST iv2` \\ conj_tac
    >- metis_tac [CONV_RULE (DEPTH_CONV let_CONV) min4_correct, min4_def]
    \\ irule REAL_LE_TRANS
    \\ qexists_tac `a * FST iv2` \\ conj_tac
    \\ fs [REAL_LE_RMUL_IMP, REAL_LE_LMUL_IMP])
  (* Upper Bound *)
  (* Case distinction for a *)
  \\ qspecl_then [`a`, `0`] assume_tac REAL_LTE_TOTAL \\ fs[]
  (* First case: a < 0 *)
  >- (
    `a <= 0 /\ a <> 0` by fs[REAL_LT_LE]
    (* Case distinction for SND iv2 *)
    \\ qspecl_then [`FST iv2`, `0`] assume_tac REAL_LTE_TOTAL \\ fs[]
    (* First case: FST iv2 < 0 *)
    >- (irule REAL_LE_TRANS
        \\ qexists_tac `FST iv1 * FST iv2` \\ conj_tac
        \\ TRY (metis_tac [CONV_RULE (DEPTH_CONV let_CONV) max4_correct, max4_def])
        \\ irule REAL_LE_TRANS
        \\ qexists_tac ` a *  FST iv2 ` \\ conj_tac
        \\ metis_tac [REAL_MUL_LE_COMPAT_NEG_L, REAL_MUL_COMM, REAL_LT_LE])
    (* Second case: 0 <= FST iv2 *)
    \\ irule REAL_LE_TRANS
    \\ qexists_tac `FST iv2 * SND iv1` \\ conj_tac
    \\ TRY (metis_tac [CONV_RULE (DEPTH_CONV let_CONV) max4_correct, max4_def])
    \\ irule REAL_LE_TRANS
    \\ qexists_tac `FST iv2 * a` \\ conj_tac
    \\ metis_tac [REAL_LE_RMUL_IMP, REAL_MUL_LE_COMPAT_NEG_L, REAL_MUL_COMM])
  (* Second case  0 <= a *)
  (* Case distinction for FST iv2 *)
  \\ qspecl_then [`SND iv2`, `0`] assume_tac REAL_LTE_TOTAL \\ fs[]
  (* First case: FST iv2 < 0 *)
  >- (irule REAL_LE_TRANS
      \\ qexists_tac `FST iv1 * SND iv2` \\ conj_tac
      \\ TRY (metis_tac [CONV_RULE (DEPTH_CONV let_CONV) max4_correct, max4_def])
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `a * SND iv2 ` \\ conj_tac
      \\ metis_tac [REAL_LE_RMUL_IMP, REAL_MUL_LE_COMPAT_NEG_L, REAL_MUL_COMM,
                    REAL_LT_LE])
  (* Second case: 0 <= FST iv2 *)
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `SND iv1 * SND iv2` \\ conj_tac
  \\ TRY (metis_tac [CONV_RULE (DEPTH_CONV let_CONV) max4_correct, max4_def])
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `a:real * SND iv2` \\ conj_tac
  \\ fs [REAL_LE_RMUL_IMP, REAL_LE_LMUL_IMP]
QED

Theorem iv_mult_preserves_valid:
  !iv1 iv2.
    valid iv1 /\ valid iv2 ==>
    valid (multInterval iv1 iv2)
Proof
  fs [valid_def, multInterval_def, IVlo_def, IVhi_def, absIntvUpd_def, min4_def, max4_def]
  \\ rpt strip_tac
  \\ match_mp_tac REAL_LE_TRANS
  \\ qexists_tac `FST iv1 * FST iv2`
  \\ fs [REAL_MIN_LE1]
  \\ match_mp_tac REAL_LE_TRANS
  \\ qexists_tac `FST iv1 * FST iv2`
  \\ fs [REAL_LE_MAX1]
QED

Theorem interval_division_valid:
  ∀ (iv1:interval) (iv2:interval) (a:real) (b:real).
    (IVhi iv2 < 0 ∨ 0 < IVlo iv2) ∧
    contained a iv1 ∧
    contained b iv2 ⇒
    contained (a / b) (divideInterval iv1 iv2)
Proof
rpt gen_tac \\ Cases_on `iv2` \\ rewrite_tac (iv_ss @ [real_div, REAL_MUL_LID])
\\ rpt gen_tac \\ strip_tac
(** TODO: FIXME use qspecl_then **)
\\ match_mp_tac
  (REWRITE_RULE (iv_ss @ [FST,SND])
    (SPECL [``iv1:interval``, ``(inv r, inv q):interval``] interval_multiplication_valid))
\\ rpt conj_tac \\ TRY (fs[] \\ NO_TAC)
\\ imp_res_tac
  (REWRITE_RULE
    (iv_ss @ [FST, SND, real_div, REAL_MUL_LID]) (SPECL [``(q,r):interval``, ``b:real``] interval_inversion_valid))
QED

Theorem iv_div_preserves_valid:
  !iv1 iv2.
    valid iv1 /\ valid iv2 /\ (IVhi iv2 < 0 \/ 0 < IVlo iv2) ==>
    valid (divideInterval iv1 iv2)
Proof
  once_rewrite_tac [divideInterval_def]
  \\ rpt strip_tac
  \\ match_mp_tac iv_mult_preserves_valid
  \\ fs []
  \\ match_mp_tac iv_inv_preserves_valid
  \\ fs []
QED

(** Properties of the maxAbs function **)
Theorem contained_leq_maxAbs:
  !a iv. contained a iv ==> abs a <= maxAbs iv
Proof
  rpt strip_tac\\ fs iv_ss \\ match_mp_tac maxAbs \\ fs []
QED

Theorem contained_leq_maxAbs_val:
  !a iv. contained a iv ==> a <= maxAbs iv
Proof
  rpt strip_tac \\ fs iv_ss \\
  `abs a <= max (abs (FST iv)) (abs (SND iv))`
    by (match_mp_tac (REWRITE_RULE iv_ss contained_leq_maxAbs) \\ fs []) \\
  REAL_ASM_ARITH_TAC
QED

Theorem contained_leq_maxAbs_neg_val:
  !a iv. contained a iv ==> - a <= maxAbs iv
Proof
  rpt strip_tac\\ fs iv_ss \\
  `abs a <= max (abs (FST iv)) (abs (SND iv))` by (match_mp_tac (REWRITE_RULE iv_ss contained_leq_maxAbs) \\ fs []) \\
  REAL_ASM_ARITH_TAC
QED

Theorem distance_gives_iv:
  !a b e iv. contained a iv /\ abs (a - b) <= e ==> contained b (widenInterval iv e)
Proof
  fs iv_ss \\ rpt strip_tac \\
  `(b:real) - e <= a /\ a <= b + e` by REAL_ASM_ARITH_TAC \\
  REAL_ASM_ARITH_TAC
QED

Theorem minAbs_positive_iv_is_lo:
  !(a b:real).
    (0 < a) /\
    (a <= b) ==>
    (minAbsFun (a,b) = a)
Proof
  rpt (strip_tac) \\
  fs[minAbsFun_def] \\
  `abs a = a` by (fs[ABS_REFL] \\ REAL_ASM_ARITH_TAC) \\
  `abs b = b` by (fs[ABS_REFL] \\ REAL_ASM_ARITH_TAC) \\
  metis_tac[REAL_MIN_ALT]
QED

Theorem minAbs_negative_iv_is_hi:
  !(a b:real).
    (b < 0) /\
  (a <= b) ==>
    (minAbsFun (a,b) = - b)
Proof
  rpt (strip_tac) \\
  fs[minAbsFun_def] \\
  `abs a = - a` by REAL_ASM_ARITH_TAC \\
  `abs b = - b` by REAL_ASM_ARITH_TAC \\
  ntac 2 (pop_assum (fn thm => rewrite_tac [thm])) \\
  `-b <= -a` by fs[] \\
  metis_tac[REAL_MIN_ALT]
QED

val _ = export_theory();

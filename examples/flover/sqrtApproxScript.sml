(**
  Simple approximation of sqrt as it is not computable in HOL4 using
  newton iterations.
  As the iteration may fail, the process "self-validates", checkign that
  the result is an over/under-approximation of the real sqrt
**)
open transcTheory realTheory realLib RealArith bossLib limTheory;
open preambleFloVer;

val _ = new_theory "sqrtApprox";

Definition newton_def:
  newton 0 n (x:real) = x ∧
  newton (SUC n) (m:real) x = newton n m ((x + (m / x)) / 2)
End

Definition validate_newton_down_def:
  validate_newton_down estimate lb ⇔ (estimate pow 2) ≤ lb
End

Theorem validate_newton_lb_valid:
  0 ≤ estimate ∧
  0 ≤ lb ∧
  validate_newton_down estimate lb ⇒
  estimate ≤ sqrt lb
Proof
  rw[validate_newton_down_def]
  >> qspecl_then [‘estimate pow 2’, ‘estimate’] mp_tac SQRT_POS_UNIQ
  >> impl_tac >- gs[POW_POS]
  >> disch_then $ once_rewrite_tac o single o GSYM
  >> irule SQRT_MONO_LE >> gs[POW_POS]
QED

Definition validate_newton_up_def:
  validate_newton_up estimate ub ⇔ ub ≤ (estimate pow 2)
End

Theorem validate_newton_ub_valid:
  0 ≤ estimate ∧
  0 ≤ ub ∧
  validate_newton_up estimate ub ⇒
  sqrt ub ≤ estimate
Proof
  rw[validate_newton_up_def]
  >> qspecl_then [‘estimate pow 2’, ‘estimate’] mp_tac SQRT_POS_UNIQ
  >> impl_tac >- gs[POW_POS]
  >> disch_then $ once_rewrite_tac o single o GSYM
  >> irule SQRT_MONO_LE >> gs[POW_POS]
QED

Theorem deriv_exp = DIFF_EXP
Theorem deriv_ln = DIFF_LN

Theorem inv2_lemma[local]:
2 * inv (2 * 2) = inv 2
Proof
  gs[REAL_DIV_REFL]
QED

Theorem lnDiv2_diff =
  MP
  (MP
   (List.nth (CONJ_LIST 3 DIFF_COMPOSITE, 1)
     |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
     |> GEN “f:real->real” |> Q.SPEC ‘ln’
     |> GEN “l:real” |> Q.SPEC ‘inv x’)
   (SPEC_ALL deriv_ln |> UNDISCH_ALL)
     |> GEN “g:real->real” |> Q.SPEC ‘λ x. 2’
     |> GEN “m:real” |> Q.SPEC ‘0’)
  (limTheory.DIFF_CONST |> Q.SPEC ‘2’ |> SPEC_ALL)
    |> SIMP_RULE std_ss [REAL_MUL_LZERO, REAL_SUB_RZERO, REAL_ARITH “2:real ≠ 0”,
                         POW_2, real_div, GSYM REAL_MUL_ASSOC, inv2_lemma]
    |> SIMP_RULE std_ss [GSYM REAL_INV_MUL', GSYM real_div]

Theorem exp_lnDiv2_diff =
  MP
  (List.nth (CONJ_LIST 9 DIFF_COMPOSITE, 7)
    |> GEN “g:real->real” |> Q.SPEC ‘λ x. ln x / 2’
    |> GEN “m:real” |> Q.SPEC ‘inv (x * 2)’)
  lnDiv2_diff
  |> DISCH_ALL

Theorem exp_lnDiv2_contl =
  MP
  (limTheory.DIFF_CONT
    |> Q.SPEC ‘λ x. (exp ((λ x. ln x / 2) x))’
    |> Q.SPEC ‘exp ((λx. ln x / 2) x) * (x * 2)⁻¹’
    |> Q.SPEC ‘x’)
  (exp_lnDiv2_diff |> UNDISCH_ALL)
  |> SIMP_RULE std_ss []
  |> DISCH_ALL

Theorem exp_lnDiv2_contl_iv:
  ∀ x. 0 < a ⇒ a ≤ x ⇒ x ≤ b ⇒ (λ x. exp (ln x / 2)) contl x
Proof
  rpt strip_tac >> irule exp_lnDiv2_contl >> REAL_ASM_ARITH_TAC
QED

Theorem exp_lnDiv2_differentiable_iv:
  ∀ x. 0 < a ⇒ a < x ⇒ x < b ⇒ (λ x. exp (ln x / 2)) differentiable x
Proof
  gs[differentiable]
  >> rpt strip_tac
  >> qexists_tac ‘exp (ln x / 2) * (inv (x * 2))’
  >> gs[]
  >> mp_tac (SIMP_RULE std_ss [] exp_lnDiv2_diff)
  >> impl_tac >- REAL_ASM_ARITH_TAC
  >> gs[]
QED

Theorem MVT_sqrt_lemma =
  limTheory.MVT
  |> Q.SPEC ‘λ x. (exp ((λ x. ln x / 2) x))’
  |> SPEC_ALL
  |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
  |> UNDISCH
  |> (fn th => MP th (exp_lnDiv2_contl_iv |> SPEC_ALL |> UNDISCH |> GEN “x:real”))
  |> (fn th => MP th (exp_lnDiv2_differentiable_iv |> SPEC_ALL |> UNDISCH |> GEN “x:real”))
  |> DISCH_ALL |> GEN_ALL

Theorem MVT_sqrt:
  ∀ a b.
    0 < a ∧ a < b ⇒
    ∃ z.
      a < z ∧ z < b ∧
      sqrt b - sqrt a = (b - a) * (exp (ln z / 2) * inv (z * 2))
Proof
  rpt strip_tac
  >> ‘0 < b’ by (irule REAL_LT_TRANS >> qexists_tac ‘a’ >> gs[])
  >> mp_tac MVT_sqrt_lemma
  >> disch_then $ qspecl_then [‘b’, ‘a’] mp_tac >> impl_tac >- gs[]
  >> impl_tac >- gs[]
  >> strip_tac
  >> ‘0 < z’ by (irule REAL_LT_TRANS >> qexists_tac ‘a’ >> gs[])
  >> qexists_tac ‘z’ >> rpt conj_tac
  >- gs[]
  >- gs[]
  >> rewrite_tac[sqrt]
  >> mp_tac $ GEN_ALL exp_lnDiv2_diff
  >> disch_then $ qspec_then ‘z’ mp_tac >> impl_tac
  >- (irule REAL_LT_TRANS >> qexists_tac ‘a’ >> gs[])
  >> disch_then $ mp_then Any mp_tac DIFF_UNIQ
  >> disch_then $ qspec_then ‘l’ mp_tac
  >> gs[Q.SPEC ‘1’ ROOT_LN |> SIMP_RULE std_ss []]
  >> disch_then $ gs o single o GSYM
QED

Theorem sqrt_diff_ub:
  ∀ a b.
    0 < a ∧ a < b ⇒
      sqrt b - sqrt a ≤ (b - a) * sqrt b * inv (a * 2)
Proof
  rpt strip_tac
  >> drule MVT_sqrt >> rpt $ disch_then drule
  >> strip_tac >> pop_assum $ once_rewrite_tac o single
  >> rewrite_tac[GSYM REAL_MUL_ASSOC]
  >> irule REAL_LE_LMUL_IMP >> reverse conj_tac
  >- REAL_ASM_ARITH_TAC
  >> ‘0 < z’
     by (REAL_ASM_ARITH_TAC)
  >> ‘exp (ln z / 2) = sqrt z’
     by (gs[Q.SPEC ‘1’ ROOT_LN |> SIMP_RULE std_ss [] |> GSYM, GSYM sqrt])
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_LE_MUL2 >> rpt conj_tac
  >- (
    irule SQRT_MONO_LE >> conj_tac >> REAL_ASM_ARITH_TAC)
  >- (
    gs[nonzerop_def]
    >> COND_CASES_TAC >> gs[]
    >> COND_CASES_TAC >> gs[]
    >> REAL_ASM_ARITH_TAC)
  >- (
     irule SQRT_POS_LE
     >> REAL_ASM_ARITH_TAC)
  >> irule REAL_LE_INV
  >> REAL_ASM_ARITH_TAC
QED

Theorem sqrt_diff_ub_concrete:
    0 < ivlo ∧
    0 < ivlo - err1 ∧
    0 ≤ err1 ∧
    abs (x - y) ≤ err1 ∧
    ivlo ≤ x ∧ x ≤ ivhi ∧
    ivlo - err1 ≤ y ∧ y ≤ ivhi + err1 ∧
    sqrt (ivhi + err1) ≤ ubSqrt ⇒
    abs( sqrt x - sqrt y ) ≤ err1 * ubSqrt * inv ((ivlo - err1) * 2)
Proof
  rpt strip_tac
  >> rewrite_tac[Once ABS_SUB, abs]
  >> COND_CASES_TAC
  >- (
    Cases_on ‘sqrt y - sqrt x = 0’
    >- (
      pop_assum $ rewrite_tac o single
      >> irule REAL_LE_MUL >> conj_tac
      >- (
        irule REAL_LE_MUL >> conj_tac >> gs[]
        >> irule REAL_LE_TRANS >> once_rewrite_tac[CONJ_COMM]
        >> asm_exists_tac >> gs[]
        >> irule SQRT_POS_LE
        >> REAL_ASM_ARITH_TAC)
      >> irule REAL_LE_INV
      >> irule REAL_LE_MUL >> conj_tac >> REAL_ASM_ARITH_TAC)
    >> ‘sqrt x < sqrt y’ by REAL_ASM_ARITH_TAC
    >> ‘x < y’
      by (
      CCONTR_TAC >> ‘y ≤ x’ by REAL_ASM_ARITH_TAC
      >> ‘sqrt y ≤ sqrt x’ by (irule SQRT_MONO_LE >> gs[] >> REAL_ASM_ARITH_TAC)
      >> REAL_ASM_ARITH_TAC)
    >> qspecl_then [‘x’, ‘y’] mp_tac sqrt_diff_ub
    >> impl_tac >- REAL_ASM_ARITH_TAC
    >> strip_tac
    >> irule REAL_LE_TRANS >> asm_exists_tac >> conj_tac >- gs[]
    >> irule REAL_LE_MUL2 >> rpt conj_tac
    >- (
      irule REAL_LE_MUL2 >> rpt conj_tac >> TRY REAL_ASM_ARITH_TAC
      >- (
        irule REAL_LE_TRANS >> once_rewrite_tac[CONJ_COMM] >> asm_exists_tac
        >> gs[] >> irule SQRT_MONO_LE >> REAL_ASM_ARITH_TAC)
      >> irule SQRT_POS_LE >> REAL_ASM_ARITH_TAC)
    >- (
      irule REAL_INV_LE_ANTIMONO_IMPR
      >> rpt conj_tac >> TRY REAL_ASM_ARITH_TAC)
    >- (
      irule REAL_LE_MUL
      >> rpt conj_tac >> TRY REAL_ASM_ARITH_TAC
      >> irule SQRT_POS_LE >> REAL_ASM_ARITH_TAC)
    >> irule REAL_LE_INV >> irule REAL_LE_MUL >> conj_tac >> REAL_ASM_ARITH_TAC)
  >> ‘sqrt y < sqrt x’ by REAL_ASM_ARITH_TAC
  >> ‘y < x’
    by (
    CCONTR_TAC >> ‘x ≤ y’ by REAL_ASM_ARITH_TAC
    >> ‘sqrt x ≤ sqrt y’ by (irule SQRT_MONO_LE >> gs[] >> REAL_ASM_ARITH_TAC)
    >> REAL_ASM_ARITH_TAC)
  >> qspecl_then [‘y’, ‘x’] mp_tac sqrt_diff_ub
  >> impl_tac >- REAL_ASM_ARITH_TAC
  >> strip_tac
  >> once_rewrite_tac[REAL_NEG_SUB]
  >> irule REAL_LE_TRANS >> asm_exists_tac >> conj_tac >- gs[]
  >> irule REAL_LE_MUL2 >> rpt conj_tac
  >- (
    irule REAL_LE_MUL2 >> rpt conj_tac >> TRY REAL_ASM_ARITH_TAC
    >- (
      irule REAL_LE_TRANS >> once_rewrite_tac[CONJ_COMM] >> asm_exists_tac
      >> gs[] >> irule SQRT_MONO_LE >> REAL_ASM_ARITH_TAC)
    >> irule SQRT_POS_LE >> REAL_ASM_ARITH_TAC)
  >- (
    irule REAL_INV_LE_ANTIMONO_IMPR
    >> rpt conj_tac >> TRY REAL_ASM_ARITH_TAC)
  >- (
    irule REAL_LE_MUL
    >> rpt conj_tac >> TRY REAL_ASM_ARITH_TAC
    >> irule SQRT_POS_LE >> REAL_ASM_ARITH_TAC)
  >> irule REAL_LE_INV >> irule REAL_LE_MUL >> conj_tac >> REAL_ASM_ARITH_TAC
QED

(*
Theorem pow_lt:
  1 ≤ x ∧
  1 < n ⇒
  x < x pow n
Proof
  Induct_on ‘n’
  >> gs[pow]
  >> rpt strip_tac >> reverse $ Cases_on ‘1 < n’
  >- (
    ‘n = 0 ∨ n = 1’ by (Cases_on ‘n’ >> gs[])
    >- (
      gs[pow])
    >> pop_assum $ once_rewrite_tac o single
    >> gs[pow]
    >> irule REAL_LT_TRANS >> qexists_tac ‘1 * x’
    >> conj_tac >- gs[]
    >> once_rewrite_tac [POW_2]
    >> irule REAL_LE_MUL2 >> gs[]
    >> REAL_ASM_ARITH_TAC)
  >> irule REAL_LE_TRANS >> qexists_tac ‘1 * x’
  >> conj_tac >- gs[]
  >> irule REAL_LE_MUL2 >> gs[]
  >> REAL_ASM_ARITH_TAC
QED
Theorem sqrt_less:
  1 ≤ x ⇒
  sqrt x ≤ x
Proof
  rpt strip_tac >> imp_res_tac REAL_LE1_POW2
  >> CCONTR_TAC
  >> ‘x < sqrt x’ by (REAL_ASM_ARITH_TAC)
  >> ‘x pow 2 < (sqrt x) pow 2’ by (qspec_then ‘1’ mp_tac POW_LT \\ gs[] \\ disch_then irule \\ gs[] \\ REAL_ASM_ARITH_TAC)
  >> imp_res_tac pow_lt
  >> rpt $ first_x_assum $ qspec_then ‘2’ assume_tac
  >> gs[]
  >> ‘(sqrt x) pow 2 = x’ by (irule SQRT_POW_2 \\ REAL_ASM_ARITH_TAC)
  >> gs[]
Theorem HAS_DERIVATIVE_SQRT:
  !z. (sqrt has_derivative (λ x:real. inv ((2:real) * sqrt x))) (at z)
Proof
  rpt strip_tac
  >> mp_tac $ Q.ISPECL [
      ‘interval((&0), (z:real))’,
      `\n z. z pow n / (&(FACT n):real)`,
    ] HAS_DERIVATIVE_SERIES'
  REPEAT GEN_TAC THEN MP_TAC(Q.ISPECL
   [`ball((&0),abs(z:real) + &1)`,
    `\n z. z pow n / (&(FACT n):real)`,
    `\n z:real. if n = 0 then (&0) else z pow (n-1) / (&(FACT(n-1)))`,
    `exp:real->real`, `from (0)`]
   HAS_DERIVATIVE_SERIES') THEN
  SIMP_TAC real_ss [CONVEX_BALL, OPEN_BALL, IN_BALL, dist] THEN
  SIMP_TAC real_ss [HAS_DERIVATIVE_WITHIN_OPEN, OPEN_BALL, IN_BALL,
           dist, REAL_SUB_LZERO, REAL_SUB_RZERO, ABS_NEG] THEN
  Q_TAC SUFF_TAC `(!n x.
    abs x < abs z + 1 ==>
    ((\z. z pow n / &FACT n) has_derivative
     (\y. (if n = 0 then 0 else x pow (n - 1) / &FACT (n - 1)) * y))
      (at x)) /\
   (!e. 0 < e ==>
      ?N. !n x. n >= N /\ abs x < abs z + 1 ==>
        abs (sum (from 0 INTER (0 .. n))
             (\i. if i = 0 then 0 else x pow (i - 1) / &FACT (i - 1)) -
           exp x) <= e) /\
   (?x l. abs x < abs z + 1 /\ ((\n. x pow n / &FACT n) sums l) (from 0))` THENL
 [DISCH_TAC THEN ASM_REWRITE_TAC [] THEN POP_ASSUM K_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN ``g:real->real`` MP_TAC) THEN
  REWRITE_TAC[EXP_CONVERGES_UNIQUE] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY Q.EXISTS_TAC [`g`, `&1`] THEN
  REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
  [ALL_TAC,
   FIRST_X_ASSUM(MP_TAC o Q.SPEC `z`) THEN
   Q_TAC SUFF_TAC `abs z < abs z + 1` THENL
   [METIS_TAC [ETA_AX], REAL_ARITH_TAC]] THEN
  GEN_TAC THEN POP_ASSUM (MP_TAC o Q.SPEC `x'`) THEN
  MATCH_MP_TAC MONO_IMP THEN SIMP_TAC std_ss [dist] THEN
  REAL_ARITH_TAC, ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC,
    REPEAT STRIP_TAC THEN
    MP_TAC(Q.SPECL [`abs(z) + &1`, `e`] EXP_CONVERGES_UNIFORMLY) THEN
    ASM_SIMP_TAC std_ss [ABS_POS, REAL_ARITH ``&0 <= x ==> &0 < x + &1:real``] THEN
    DISCH_THEN(X_CHOOSE_TAC ``N:num``) THEN Q.EXISTS_TAC `N + 1` THEN
    MAP_EVERY X_GEN_TAC [``n:num``, ``w:real``] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o Q.SPECL [`n - 1`, `w`]) THEN
    ASM_SIMP_TAC std_ss [ARITH_PROVE ``n >= m + 1 ==> n - 1 >= m:num``] THEN
    REWRITE_TAC[FROM_0, INTER_UNIV] THEN MATCH_MP_TAC EQ_IMPLIES THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN ``((0:num)..n) = 0 INSERT (IMAGE SUC ((0:num)..n-1))`` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION, IN_INSERT, IN_IMAGE, IN_NUMSEG] THEN
     INDUCT_TAC THEN SIMP_TAC arith_ss [] THEN
     UNDISCH_TAC ``n >= N + 1:num`` THEN ARITH_TAC,
     ALL_TAC] THEN
    SIMP_TAC std_ss [SUM_CLAUSES, IMAGE_FINITE, FINITE_NUMSEG] THEN
    SIMP_TAC real_ss [IN_IMAGE, NOT_SUC, SUC_NOT, REAL_ADD_LID] THEN
    SIMP_TAC std_ss [SUM_IMAGE, FINITE_NUMSEG] THEN
    MATCH_MP_TAC SUM_EQ THEN SIMP_TAC real_ss [IN_NUMSEG, NOT_SUC, o_THM, SUC_SUB1],
    MAP_EVERY Q.EXISTS_TAC [`(&0)`, `exp((&0))`] THEN
    REWRITE_TAC[EXP_CONVERGES, ABS_0] THEN
    SIMP_TAC std_ss [REAL_ARITH ``&0 <= z ==> &0 < z + &1:real``, ABS_POS]] THEN
  X_GEN_TAC ``n:num`` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC ``n = 0:num`` THEN ASM_REWRITE_TAC [] THENL
  [SIMP_TAC real_ss [pow, FACT, HAS_DERIVATIVE_CONST], ALL_TAC] THEN
  SIMP_TAC std_ss [real_div] THEN ONCE_REWRITE_TAC [REAL_MUL_COMM] THEN
  ONCE_REWRITE_TAC [REAL_ARITH ``a * (b * c) = c * b * a:real``] THEN
  Q_TAC SUFF_TAC `!y. inv (&FACT (n - 1)) * x pow (n - 1) * y =
                      inv (&FACT n) * (&n * x pow (n - 1) * y)` THENL
  [DISC_RW_KILL,
   RW_TAC real_ss [REAL_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN `0 < n` by ASM_SIMP_TAC arith_ss [] THEN
   `?m. n = SUC m` by (Q.EXISTS_TAC `PRE n` THEN ASM_SIMP_TAC arith_ss [SUC_PRE]) THEN
   ASM_SIMP_TAC std_ss [SUC_SUB1, FACT, GSYM REAL_OF_NUM_MUL] THEN
   `~(&SUC m = &0:real)` by ASM_SIMP_TAC arith_ss [NOT_SUC, REAL_OF_NUM_EQ] THEN
   ASM_SIMP_TAC real_ss [REAL_FACT_NZ, REAL_INV_MUL] THEN
   ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c = a * c * b:real``] THEN
   ASM_SIMP_TAC real_ss [REAL_MUL_LINV]] THEN
  Q_TAC SUFF_TAC `((\z. inv (&FACT n) * (\z. z pow n) z) has_derivative
             (\y. inv (&FACT n) * (\y. (&n * x pow (n - 1) * y)) y)) (at x)` THENL
  [SIMP_TAC std_ss [], ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  Q_TAC SUFF_TAC `(\y. &n * x pow (n - 1) * y) =
    (\y. sum (1 .. n) (\i. x pow (n - i) * y * x pow (i - 1)))` THENL
  [DISC_RW_KILL THEN SIMP_TAC std_ss [HAS_DERIVATIVE_POW], ALL_TAC] THEN
  `FINITE (1 .. n)` by SIMP_TAC std_ss [FINITE_NUMSEG] THEN
  POP_ASSUM (MP_TAC o MATCH_MP SUM_CONST) THEN
  DISCH_THEN (MP_TAC o Q.SPEC `x pow (n - 1)`) THEN SIMP_TAC arith_ss [CARD_NUMSEG] THEN
  DISCH_THEN (ASSUME_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]) THEN
  ASM_REWRITE_TAC [] THEN ONCE_REWRITE_TAC [REAL_ARITH ``a * b * c = (a * c) * b:real``] THEN
  ABS_TAC THEN SIMP_TAC std_ss [SUM_RMUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN SIMP_TAC arith_ss [GSYM POW_ADD, IN_NUMSEG]);
Theorem foo:
  ∀ net. (sqrt has_derivative (λ x:real. inv ((2:real) * sqrt x))) net
Proof
  rpt strip_tac
  irule HAS_DERIVATIVE_LINEAR
open simpLib realLib computeLib;
  val [newton] = decls "newton";
computeLib.monitoring := SOME (same_const newton);
EVAL “ 4 ≤ (newton 4 4 (4 * 1.01)) pow 2”
Theorem newton_mono:
  ∀ n x y.
    n ≠ 0 ∧
    x ≤ y ⇒
    newton n y ≤ newton n x
Proof
  Induct_on ‘n’ >> gs[newton_def]
  >> rpt strip_tac >> first_x_assum irule
  >> gs[real_div]
  >> irule REAL_LE_RMUL_IMP >> gs[]
  >> irule REAL_LE_ADD2 >> gs[]
  >> irule REAL_LE_LMUL_IMP >> gs[]
Theorem REAL_EXP_BOUND_LEMMA:
  ∀ x.
    0 ≤ x ∧ x ≤ inv 2 ⇒ exp(x) ≤ &1 + &2 * x
Proof
  rpt strip_tac
  >> irule REAL_LE_TRANS
  >> qexists_tac `suminf (\n. x pow n)` >> conj_tac
  >- (
    gs[exp] >> irule seqTheory.SER_LE >> rpt conj_tac
    >> gs[seqTheory.summable]
    >- (
      gen_tac >> gs[]
      >> jrhUtils.GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID]
      >> irule REAL_LE_RMUL_IMP >> conj_tac
      >- (
        once_rewrite_tac[GSYM REAL_INV1] >> irule REAL_INV_LE_ANTIMONO_IMPR
        >> gs[arithmeticTheory.FACT_LESS]
        >> Induct_on ‘n’ >> gs[arithmeticTheory.FACT] >> irule arithmeticTheory.LESS_EQ_TRANS
        >> qexists_tac ‘FACT n’ >> gs[])
      >> irule POW_POS >> gs[])
    >- (qexists_tac ‘exp x’ >> gs[BETA_RULE EXP_CONVERGES])
    >> qexists_tac ‘inv (1 - x)’ >> irule seqTheory.GP
    >> gs[abs] >> irule REAL_LET_TRANS >> qexists_tac ‘inv 2’
    >> gs[] >> once_rewrite_tac[GSYM REAL_INV1] >> irule REAL_LT_INV
    >> gs[])
  >> ‘(λ n. x pow n) sums inv (1 - x)’
    by (
      irule seqTheory.GP
      >> gs[abs] >> irule REAL_LET_TRANS >> qexists_tac ‘inv 2’
      >> gs[] >> once_rewrite_tac[GSYM REAL_INV1] >> irule REAL_LT_INV
      >> gs[])
  >> gs[seqTheory.SUMS_EQ]
  >> qspec_then ‘1- x’ mp_tac REAL_LE_LMUL
  >> gs[GSYM PULL_FORALL]
  >> impl_tac
  >- (
    asm_rewrite_tac[REAL_ARITH “&0 < x - y <=> y < x”]
    >> irule REAL_LET_TRANS >> qexists_tac ‘inv 2’
    >> gs[] >> once_rewrite_tac[GSYM REAL_INV1] >> irule REAL_LT_INV
    >> gs[])
  >> disch_then $ once_rewrite_tac o single o GSYM
  >> ‘(&1 - x) * inv (&1 - x) = &1’
     by (irule REAL_MUL_RINV
         >> rewrite_tac [REAL_ARITH “(&1 - x = &0) <=> (x = &1)”]
         >> strip_tac >> gs[]
         >> ‘inv 2 < 1’ by
           (once_rewrite_tac[GSYM REAL_INV1] >> irule REAL_LT_INV
            >> gs[])
         >> ‘1 < 1’ by (irule REAL_LET_TRANS >> qexists_tac ‘inv 2’ >> gs[])
         >> gs[])
  >> pop_assum $ gs o single
  >> rewrite_tac[REAL_ADD_LDISTRIB, REAL_SUB_RDISTRIB]
  >> rewrite_tac[REAL_MUL_RID, REAL_MUL_LID]
  >> rewrite_tac[REAL_ARITH “&1 <= (&1 + &2 * x) - (x + x * (&2 * x)) <=>
                             x * (&2 * x) <= x * &1”]
  >> irule REAL_LE_LMUL_IMP >> gs[]
  >> qspec_then ‘inv 2’ mp_tac REAL_LE_LMUL
  >> gs[GSYM PULL_FORALL]
  >> disch_then $ once_rewrite_tac o single o GSYM
  >> rewrite_tac [REAL_MUL_ASSOC]
  >> gs[REAL_MUL_LINV]
QED
Theorem sqrt_range_red:
  0 ≤ x ⇒
  sqrt(x / 10) * sqrt 10 = sqrt x
Proof
  ‘0 < sqrt 10’ by (irule SQRT_POS_LT >> REAL_ARITH_TAC)
  >> gs[SQRT_DIV, real_div, GSYM REAL_MUL_ASSOC, REAL_MUL_LINV]
  >> ‘inv (sqrt 10) * sqrt 10 = 1’
    by (irule REAL_MUL_LINV >> CCONTR_TAC >> gs[])
  >> pop_assum $ gs o single
QED
Definition range_red_helper_def:
  range_red_helper 0 _ _ = 0:real ∧
  range_red_helper (SUC n) f x =
    if x < 0 then
      - (range_red_helper n f (- x))
    else if 1 ≤ x then
      (range_red_helper n f (x/10)) * f 10
    else f x
End
Definition range_reduce_def:
  range_reduce_app f x = range_red_helper (2 * clg x) f x
End
Theorem REAL_EXP_LINAPPROX_LEMMA:
  !x. abs(x) < 1 ⇒
      abs(exp x - (&1 + x)) < (&4 / &100) * inv(&2 pow 24)
Proof
  GEN_TAC THEN
  DISCH_TAC THEN MP_TAC(Q.SPECL [`x:real`, `2`] MCLAURIN_EXP_LE) THEN
  strip_tac >> gs[SUM_2, arithmeticTheory.FACT, EVAL “FACT 1”, EVAL “FACT 2”]
  >> qmatch_goalsub_abbrev_tac ‘abs exp_err < _’
  >> ‘exp_err = exp t / 2 * x pow 2’
     by (unabbrev_all_tac >> gs[real_div] >> REAL_ARITH_TAC)
  >> pop_assum $ rewrite_tac o single
  >> unabbrev_all_tac
  >> gs[real_div]
  REWRITE_TAC[REAL_ABS_MUL, ABS_POW2] THEN
  (* *)
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[real_pow, REAL_POW_1, ARITH] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_FACT_CONV) THEN
  REWRITE_TAC[real_div, REAL_MUL_LID, REAL_MUL_RID, REAL_INV_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  REWRITE_TAC[REAL_ARITH `(a + b:real) - a = b`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&1 + &2 * abs(t)) * inv(&2) * abs(x) pow 2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(abs t)` THEN
      CONJ_TAC THENL
       [SUBGOAL_THEN `abs(exp t) = exp t` SUBST1_TAC THENL
         [MESON_TAC[REAL_EXP_POS_LE, REAL_ABS_REFL], ALL_TAC] THEN
        REWRITE_TAC[REAL_EXP_MONO_LE, REAL_ABS_LE],
        MATCH_MP_TAC REAL_EXP_BOUND_LEMMA THEN
        REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(x:real)` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_TRANS THEN
        EXISTS_TAC `&1 / &33554432` THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV],
      MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS]],
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `(&1 + &2 * ( &1 / &33554432)) * inv (&2) * abs(x) pow 2` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC, MATCH_MP_TAC REAL_POW_LE THEN
        REWRITE_TAC[REAL_ABS_POS]] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN
      REWRITE_TAC[REAL_LE_LADD] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_OF_NUM_LE, ARITH] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs(x:real)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      ASM_REWRITE_TAC[],
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `(&1 + &2 * (&1 / &33554432)) * inv (&2) *
                  (&1 / &33554432) pow 2` THEN
      CONJ_TAC THENL
       [ALL_TAC, CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LT_LMUL THEN
      CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV, ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LT_MUL2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]]]),,
sqrt (x) = exp (ln (x
ROOT_LN |> Q.SPEC ‘1’ |> SIMP_RULE std_ss [real_div]
Theorem mk_abs_thm:
a = b + c ⇒
abs (a - b) = abs c
Proof
  rw[] >> gs[abs] >> ‘b + c - b = c’ by REAL_ASM_ARITH_TAC
  >> pop_assum $ gs o single
QED
Theorem MCLAURIN_EXP_BOUND:
  ∀ x n.
    ∃ t.
      abs t ≤ abs x ∧
      abs (exp x - sum (0,n) (λm. x pow m / &FACT m)) = abs (exp t / &FACT n * x pow n)
Proof
  rpt gen_tac >> strip_assume_tac $ Q.SPECL [‘x’, ‘n’] MCLAURIN_EXP_LE
  >> qexists_tac ‘t’ >> conj_tac >- gs[]
  >> imp_res_tac mk_abs_thm
QED
Theorem MCLAURIN_LN_POS :
   !x n.
     &0 < x /\ 0 < n
     ==> ?t. &0 < t /\
             t < x  /\
             (ln(&1 + x)
              = sum(0,n) (\m. ~(&1) pow (SUC m) * (x pow m) / &m)
                +
               ~(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n))
Proof
  cheat
QED
Theorem MCLAURIN_LN_BOUND:
   !x n.
     &0 < x /\ 0 < n
     ==> ?t. &0 < t /\
             t < x  /\
             abs ((ln(&1 + x) - sum(0,n) (\m. ~(&1) pow (SUC m) * (x pow m) / &m))) =
               abs (~(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n))
Proof
  rpt strip_tac >> mp_tac $ Q.SPECL [‘x’, ‘n’] MCLAURIN_LN_POS
  >> impl_tac >- gs[]
  >> strip_tac
  >> qexists_tac ‘t’
  >> imp_res_tac mk_abs_thm >> gs[]
QED
MCLAURIN_LN_BOUND |> SPEC_ALL |> GEN “n:num” |> Q.SPEC ‘10:num’ |> GEN_ALL |> SIMP_RULE std_ss []
                  EVAL “sum (0,10) (λ m. 184/12 pow m / &FACT m)”
*)

val _ = export_theory();

(**
  Function that computes a polynomial approximation for a single elementary
  function on a fixed interval, and its soundness proof.
  Function approxPoly is reused in transcApproxSemScript.sml to build the overall
  function implementing the first phase of Dandelion
**)
open realTheory realLib RealArith transcTheory;
open realPolyTheory realPolyProofsTheory mcLaurinApproxTheory transcLangTheory;
open preambleDandelion;

val _ = new_theory "approxPoly";

(** functions computing the McLaurin series for transcendental functions **)
Definition expPoly_def:
  expPoly 0 = [] ∧ (* x pow 0 * inv FACT 0 *)
  expPoly (SUC n) = (expPoly n) ++ [inv (&FACT n)]
End

Definition cosPoly_def:
  cosPoly 0 = [] ∧
  cosPoly (SUC n) =
    if (EVEN n) then
      cosPoly n ++ [-1 pow (n DIV 2) * inv (&FACT n)]
    else cosPoly n ++ [0]
End

Definition sinPoly_def:
  sinPoly 0 = [] ∧
  sinPoly (SUC n) =
    if (EVEN n) then sinPoly n ++ [0]
    else sinPoly n ++ [-1 pow ((n - 1) DIV 2) * inv (&FACT n)]
End

Definition sqrtPoly_def:
  sqrtPoly 0 = [] ∧
  sqrtPoly (SUC n) = sqrtPoly n ++
                     [ -1 pow (n - 1) * &FACT (2 * PRE n)
                        * (2 pow n)⁻¹ * (2 pow (n - 1))⁻¹ *
                        (&FACT (n - 1))⁻¹ * inv( &FACT n)]
End

Definition logPoly_def:
  logPoly 0 = [] ∧
  logPoly (SUC n) =
    if (n = 0) then [0]
    else (logPoly n ++ [ - 1 pow (SUC n) * inv (&n)])
End

(** Define an approximation function that translates transcendental functions into
    polynomials **)
(* Error for exp if upper bound ≤ 1/2 *)
Definition expErrSmall_def:
  expErrSmall approxSteps = inv (&FACT approxSteps * 2 pow (approxSteps - 1))
End

(* General, more coarse bound *)
Definition expErrBig_def:
  expErrBig n approxSteps =
    2 pow n * &n pow approxSteps * inv (&FACT approxSteps * 2 pow approxSteps)
End

Definition cosErr_def:
  cosErr iv approxSteps =
    (max (abs (FST iv)) (abs (SND iv))) pow approxSteps * (* ^(cosErr_EVAL_THM |> concl |> rhs)*)
    inv (&FACT approxSteps)
End

Definition sinErr_def:
  sinErr iv approxSteps =
    (max (abs (FST iv)) (abs (SND iv))) pow approxSteps * (* ^(sinErr_EVAL_THM |> concl |> rhs) *)
    inv (&FACT approxSteps)
End

Definition atnErr_def:
  atnErr iv approxSteps =
  (max (abs (FST iv)) (abs (SND iv))) pow approxSteps /
    (1 - (max (abs (FST iv)) (abs (SND iv))) )
End

Definition sqrtErr_def:
  sqrtErr iv approxSteps =
  abs
  (sum (0,approxSteps)
   (λm.
      (if m = 0 then 1
       else
         &FACT (2 * PRE m) *
         (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹ * (&FACT (m − 1))⁻¹) /
           &FACT m *  (max (abs (FST iv)) (abs (SND iv))) pow approxSteps)) +
   abs( -1 pow (approxSteps - 1) * &FACT (2 * PRE approxSteps)
        * (2 pow approxSteps)⁻¹ * (2 pow (approxSteps - 1))⁻¹ *
        (&FACT (approxSteps - 1))⁻¹ * inv( &FACT approxSteps) *
        (max (abs (FST iv)) (abs (SND iv))) pow approxSteps)
End

Definition logErr_def:
  logErr iv approxSteps =
    abs(-1 pow (SUC approxSteps) *
    ((SND iv) pow approxSteps) / &approxSteps)
End

(**
  Approximate a function described by transcLang with a real-number polynomial,
  also returns the approximation error incurred from the polynomial only
**)
Definition approxPoly_def:
  approxPoly (transc:trFun) (iv:real#real) approxSteps :(poly#real) option =
  case transc of
  | Exp =>
      if iv = (0, inv 2) then
        SOME (expPoly approxSteps, expErrSmall approxSteps)
      else if 0 ≤ FST iv then
        SOME (expPoly approxSteps, expErrBig (clg (SND iv * 2)) approxSteps)
      else NONE
  | Sin => SOME (sinPoly approxSteps, sinErr iv approxSteps)
  | Cos => SOME (cosPoly approxSteps, cosErr iv approxSteps)
  | Atn =>
      if max (abs (FST iv)) (abs (SND iv)) < 1 then SOME (atnPoly approxSteps, atnErr iv approxSteps)
      else NONE
  | Tan => NONE
  | Sqrt => if ((1 < (FST iv)) ∧ (1 < (SND iv))) then
             SOME (sqrtPoly approxSteps, sqrtErr iv approxSteps) else NONE
  | Log => if ((1 < (FST iv)) ∧ (1 < (SND iv))) then
             SOME (compose (logPoly approxSteps) [-1;1], logErr (FST iv -1, SND iv -1) approxSteps) else NONE
End

(** Simple properties of polynomials used for proofs later **)
Theorem expPoly_LENGTH:
  LENGTH (expPoly n) = n
Proof
  Induct_on ‘n’ >> gs[expPoly_def]
QED

Theorem cosPoly_LENGTH:
  LENGTH (cosPoly n) = n
Proof
  Induct_on ‘n’ >> gs[cosPoly_def]
  >> cond_cases_tac >> gs[]
QED

Theorem sinPoly_LENGTH:
  LENGTH (sinPoly n) = n
Proof
  Induct_on ‘n’ >> gs[sinPoly_def]
  >> cond_cases_tac >> gs[]
QED

Theorem sqrtPoly_LENGTH:
  LENGTH (sqrtPoly n) = n
Proof
  Induct_on ‘n’ >> gs[sqrtPoly_def]
QED

Theorem logPoly_LENGTH:
  LENGTH (logPoly n) = n
Proof
  Induct_on ‘n’ >> gs[logPoly_def]
  >> Cases_on ‘n’ >> gs[logPoly_def]
QED

(** The polynomials compute the sum part of the McLaurin series **)
Theorem exp_sum_to_poly:
  ∀ n x. evalPoly (expPoly n) x = sum (0,n) (λ m. x pow m / &FACT m)
Proof
  Induct_on ‘n’ >> gs[expPoly_def, evalPoly_def, sum]
  >> rpt strip_tac >> gs[evalPoly_app, evalPoly_def, expPoly_LENGTH]
QED

Theorem cos_sum_to_poly:
  ∀ n x. evalPoly (cosPoly n) x =
       sum(0,n)
          (λm.
             (&FACT m)⁻¹ * x pow m *
             if EVEN m then cos 0 * -1 pow (m DIV 2)
             else sin 0 * -1 pow ((SUC m) DIV 2))
Proof
  Induct_on ‘n’ >> gs[sum, evalPoly_def, cosPoly_def]
  >> cond_cases_tac
  >> gs[evalPoly_app, COS_0, SIN_0, evalPoly_def, cosPoly_LENGTH]
QED

Theorem sin_sum_to_poly:
  ∀ n x.
    evalPoly (sinPoly n) x =
    sum(0,n)
       (λm.
          (&FACT m)⁻¹ * x pow m *
          if EVEN m then sin 0 * -1 pow (m DIV 2)
          else cos 0 * -1 pow ((m - 1) DIV 2))
Proof
  Induct_on ‘n’ >> gs[sum, evalPoly_def, sinPoly_def]
  >> cond_cases_tac
  >> gs[evalPoly_app, SIN_0, COS_0, evalPoly_def, sinPoly_LENGTH]
QED

Theorem sqrt_sum_to_poly:
  ∀n x. evalPoly (sqrtPoly n) x =
        sum (0,n)
            (λm.
                 (λm x.
                      if m = 0 then  exp ((\x. (ln (1+x)) / &2) x)
                      else
                        -1 pow (m - 1) * &FACT (2 * PRE m) *
                        (exp ((\x. &(2 * PRE m + 1) * (ln (1+x)) / &2) x))⁻¹
                 * (2 pow m)⁻¹ *
                        (2 pow (m - 1))⁻¹ * (&FACT (m - 1))⁻¹) m 0 /
                 &FACT m * x pow m)
Proof
  Induct_on ‘n’
  >- gs[sum, sqrtPoly_def, evalPoly_def]
  >> strip_tac >> gs[sqrtPoly_def, evalPoly_app, sum]
  >> Cases_on ‘n=0’
  >- gs[sqrtPoly_def, LENGTH, FACT, evalPoly_def, LN_1, EXP_0]
  >> gs[evalPoly_def, LN_1, EXP_0, sqrtPoly_LENGTH]
QED

Theorem log_sum_to_poly:
  ∀n x. (0 < n) ⇒
        evalPoly (logPoly n) x =
        sum (0,n) (λm. -1 pow SUC m * x pow m / &m)
Proof
  Induct_on ‘n’
  >- gs[]
  >> rpt strip_tac
  >> ‘0 ≤ n ’ by gs[]
  >> Cases_on ‘n = 0’
  >- (
    rpt VAR_EQ_TAC
    >> rewrite_tac[sum, REAL_ADD_LID, logPoly_def, APPEND_NIL]
    >> BETA_TAC
    >> rewrite_tac[evalPoly_def, REAL_MUL_RZERO, REAL_ADD_RID, ADD,
                   real_div]
    >> ‘0 = -1 * 0:real’ by real_tac
    >> rewrite_tac[pow0, REAL_MUL_RID, EVAL “-1 pow SUC 0”]
    >> pop_assum $ once_rewrite_tac o single
    >> AP_TERM_TAC >> rewrite_tac[REAL_MUL_RZERO]
    >> gs[REAL_INV_EQ_0])
  >> gs[logPoly_def, sum, evalPoly_app, evalPoly_def, logPoly_LENGTH]
QED

Theorem log_sum_to_poly_indexshift:
  ∀ n x. (0 < n) ⇒
  evalPoly (compose (logPoly n) [-1;1]) x =
  sum (0,n) (λm. -1 pow SUC m * (x-1) pow m / &m)
Proof
  rpt strip_tac
  >> rewrite_tac[compose_correct]
  >> ‘evalPoly [-1; 1] x = x - 1’ by (gs[evalPoly_def] >> real_tac)
  >> pop_assum $ once_rewrite_tac o single
  >> irule log_sum_to_poly >> gs[]
QED

(** Theorems about the remainder term of the McLaurin series **)
Theorem exp_remainder_bounded_small:
  ∀ n x t.
    0 < n ∧ abs t ≤ abs x ∧ 0 ≤ x ∧
    t ≤ inv 2 ∧ x ≤ inv 2 ⇒
    abs (exp t / &FACT n * x pow n) ≤ inv (&FACT n * 2 pow (n - 1))
Proof
  rpt strip_tac >> rewrite_tac[real_div, abs]
  >> qmatch_goalsub_abbrev_tac ‘(if 0 ≤ exp_bound then _ else _) ≤ _’
  >> ‘0 ≤ exp_bound’
    by (
    unabbrev_all_tac
    >> rpt (irule REAL_LE_MUL >> gs[POW_POS, EXP_POS_LE]))
  >> simp[] >> unabbrev_all_tac
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘(1 + 2 * inv 2) * (inv (&FACT n) * x pow n)’
  >> conj_tac
  >- (
    rewrite_tac[GSYM REAL_MUL_ASSOC]
    >> irule REAL_LE_RMUL_IMP
    >> conj_tac
    >- (
      Cases_on ‘0 ≤ t’
      >- (
        irule REAL_LE_TRANS
        >> qexists_tac ‘1 + 2 * t’ >> conj_tac
        >- (irule REAL_EXP_BOUND_LEMMA >> gs[])
        >> real_tac)
      >> ‘t = - (- t)’ by real_tac
      >> pop_assum $ once_rewrite_tac o single
      >> once_rewrite_tac[EXP_NEG]
      >> ‘- (inv 2) ≤ -t’ by real_tac
      >> irule REAL_LE_TRANS
      >> qexists_tac ‘inv (exp (- (inv 2)))’
      >> conj_tac
      >- (irule REAL_INV_LE_ANTIMONO_IMPR >> gs[EXP_POS_LT, EXP_MONO_LE])
      >> rewrite_tac[EXP_NEG, REAL_INV_INV]
      >> irule REAL_EXP_BOUND_LEMMA >> gs[])
    >> irule REAL_LE_MUL >> gs[REAL_LE_INV, POW_POS])
  >> ‘1 + 2 * inv 2 = 2’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac[GSYM REAL_MUL_ASSOC, REAL_INV_MUL']
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘2 * (inv (&FACT n) * inv 2 pow n)’
  >> conj_tac
  >- (
    irule REAL_LE_LMUL_IMP >> reverse conj_tac >- gs[]
    >> irule REAL_LE_LMUL_IMP >> reverse conj_tac >- gs[REAL_LE_INV]
    >> irule POW_LE >> gs[])
  >> Cases_on ‘n’ >- gs[]
  >> rewrite_tac[pow]
  >> gs[REAL_INV_MUL']
QED

Theorem exp_remainder_bounded_big:
  ∀ n m x t.
    0 < n ∧ abs t ≤ abs x ∧ EVEN n ∧
    abs x ≤ &m * (inv 2) ∧
    t ≤ &m * (inv 2) ⇒
    abs (exp t / &FACT n * x pow n) ≤ 2 pow m * &m pow n * (inv (&FACT n * 2 pow n))
Proof
  rpt strip_tac >> rewrite_tac[real_div, abs]
  >> qmatch_goalsub_abbrev_tac ‘(if 0 ≤ exp_bound then _ else _) ≤ _’
  >> ‘0 ≤ exp_bound’
    by (
    unabbrev_all_tac
    >> rpt (irule REAL_LE_MUL >> gs[POW_POS, EXP_POS_LE]))
  >> pop_assum $ rewrite_tac o single
  >> unabbrev_all_tac
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘exp (&m * inv 2) * (inv (&FACT n) * x pow n)’
  >> conj_tac
  >- (
    rewrite_tac[GSYM REAL_MUL_ASSOC]
    >> irule REAL_LE_RMUL_IMP
    >> conj_tac
    >- gs[EXP_MONO_LE]
    >> irule REAL_LE_MUL >> gs[REAL_LE_INV, POW_POS])
  >> rewrite_tac[EXP_N]
  >> qmatch_goalsub_abbrev_tac ‘_ * cst_err ≤ _’
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘(1 + 2 * inv 2) pow m * cst_err’
  >> conj_tac
  >- (
    irule REAL_LE_RMUL_IMP
    >> conj_tac
    >- (
      irule POW_LE >> rewrite_tac[EXP_POS_LE]
      >> irule REAL_EXP_BOUND_LEMMA >> gs[])
    >> unabbrev_all_tac
    >> irule REAL_LE_MUL >> gs[REAL_LE_INV, POW_POS])
  >> ‘1 + 2 * inv 2 = 2’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> unabbrev_all_tac
  >> rewrite_tac[REAL_MUL_ASSOC]
  >> qmatch_goalsub_abbrev_tac ‘cst_err * x pow n’
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘cst_err * (&m * inv 2) pow n’ >> conj_tac
  >- (
    irule REAL_LE_LMUL_IMP >> conj_tac
    >- (irule REAL_LE_TRANS >> qexists_tac ‘abs x pow n’
        >> gs[POW_LE, POW_ABS, ABS_LE])
    >> unabbrev_all_tac >> irule REAL_LE_MUL
    >> gs[REAL_LE_INV, POW_POS])
  >> rewrite_tac [POW_MUL]
  >> unabbrev_all_tac
  >> qmatch_goalsub_abbrev_tac ‘curr_bound ≤ _’
  >> ‘curr_bound = 2 pow m * &m pow n * (inv (&FACT n * 2 pow n))’
     by (unabbrev_all_tac >> gs[REAL_POW_INV])
  >> pop_assum $ rewrite_tac o single
  >> unabbrev_all_tac >> gs[]
QED

Theorem sin_even_remainder_bounded:
  ∀ n.
    EVEN n ⇒
    inv (&FACT n) * sin t * x pow n * -1 pow (n DIV 2) ≤
    abs(inv (&FACT n) * x pow n * -1 pow (n DIV 2))
Proof
  rpt strip_tac
  >> ‘inv (&FACT n) * x pow n * -1 pow (n DIV 2) = inv (&FACT n) * 1 * x pow n * -1 pow (n DIV 2)’
     by real_tac
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac[GSYM REAL_MUL_ASSOC]
  >> once_rewrite_tac[REAL_ABS_MUL]
  >> ‘0 ≤ inv (&FACT n)’
     by gs[REAL_LE_INV]
  >> ‘abs (inv (&FACT n)) = inv (&FACT n)’ by gs[abs]
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_LE_LMUL_IMP
  >> reverse conj_tac >- gs[]
  >> once_rewrite_tac[REAL_ABS_MUL]
  >> Cases_on ‘0 ≤ x pow n * -1 pow (n DIV 2)’
  >- (
    ‘abs (x pow n * -1 pow (n DIV 2)) = x pow n * -1 pow (n DIV 2)’ by gs[abs]
    >> pop_assum $ rewrite_tac o single
    >> irule REAL_LE_RMUL_IMP >> gs[SIN_BOUNDS])
  >> ‘x pow n * -1 pow (n DIV 2) < 0’ by real_tac
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘-1 * (x pow n * -1 pow (n DIV 2))’
  >> conj_tac
  >- (
    once_rewrite_tac [REAL_MUL_COMM]
    >> drule REAL_LE_LMUL_NEG
    >> disch_then $ qspecl_then [‘sin t’, ‘-1’] $ rewrite_tac o single
    >> gs[SIN_BOUNDS])
  >> ‘∃ y. x pow n * -1 pow (n DIV 2) = -1 * y ∧ 0 ≤ y’
    by (qexists_tac ‘-1 * x pow n * -1 pow (n DIV 2)’
        >> real_tac)
  >> qpat_x_assum `_ = -1 * y` $ rewrite_tac o single
  >> gs[ABS_LE]
QED

Theorem cos_even_remainder_bounded:
  ∀ n.
    EVEN n ⇒
    inv (&FACT n) * cos t * x pow n * -1 pow (n DIV 2) ≤
    abs(inv (&FACT n) * x pow n * -1 pow (n DIV 2))
Proof
  rpt strip_tac
  >> ‘inv (&FACT n) * x pow n * -1 pow (n DIV 2) = inv (&FACT n) * 1 * x pow n * -1 pow (n DIV 2)’
     by real_tac
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac[GSYM REAL_MUL_ASSOC]
  >> once_rewrite_tac[REAL_ABS_MUL]
  >> ‘0 ≤ inv (&FACT n)’
     by gs[REAL_LE_INV]
  >> ‘abs (inv (&FACT n)) = inv (&FACT n)’ by gs[abs]
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_LE_LMUL_IMP
  >> reverse conj_tac >- gs[]
  >> once_rewrite_tac[REAL_ABS_MUL]
  >> Cases_on ‘0 ≤ x pow n * -1 pow (n DIV 2)’
  >- (
    ‘abs (x pow n * -1 pow (n DIV 2)) = x pow n * -1 pow (n DIV 2)’ by gs[abs]
    >> pop_assum $ rewrite_tac o single
    >> irule REAL_LE_RMUL_IMP >> gs[COS_BOUNDS])
  >> ‘x pow n * -1 pow (n DIV 2) < 0’ by real_tac
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘-1 * (x pow n * -1 pow (n DIV 2))’
  >> conj_tac
  >- (
    once_rewrite_tac [REAL_MUL_COMM]
    >> drule REAL_LE_LMUL_NEG
    >> disch_then $ qspecl_then [‘cos t’, ‘-1’] $ rewrite_tac o single
    >> gs[COS_BOUNDS])
  >> ‘∃ y. x pow n * -1 pow (n DIV 2) = -1 * y ∧ 0 ≤ y’
    by (qexists_tac ‘-1 * x pow n * -1 pow (n DIV 2)’
        >> real_tac)
  >> qpat_x_assum `_ = -1 * y` $ rewrite_tac o single
  >> gs[ABS_LE]
QED

Definition approxPolySideCond_def:
  approxPolySideCond approxSteps =
    (0 < approxSteps ∧ EVEN approxSteps ∧ EVEN (approxSteps DIV 2))
End

Theorem sum_sub:
  ∀ (n:num) (f: num -> real) (g: num -> real).
    sum (0, n) f - sum (0, n) g = sum (0,n) (\n. f n - g n)
Proof
  Induct_on ‘n’
  >- gs[sum]
  >> rpt strip_tac >> gs[sum]
  >> ‘sum (0,n) f + f n − (sum (0,n) g + g n) =
      ( sum (0,n) f − sum (0,n) g) + (f n - g n)’ by REAL_ARITH_TAC
  >> pop_assum $ rewrite_tac o single
  >> gs[]
QED

Theorem SUM_LE:
  ∀f g m n.
          (∀r. m ≤ r ∧ r < n + m ⇒ f r <= g r) ∧ 0 < n ⇒
          sum (m,n) f <= sum (m,n) g
Proof
  rpt strip_tac
  >> Induct_on ‘n’
  >- gs[]
  >> rpt strip_tac
  >> gs[sum]
  >> Cases_on ‘n=0’
  >- gs[sum]
  >> ‘0 < n’ by gs[] >> res_tac
  >> irule REAL_LE_ADD2
  >> gs[]
QED

Theorem sum_abs_bound:
  ∀n. 0< n ⇒ sum (0,n) (λm. abs (&m)⁻¹) ≤ &n
Proof
  Induct_on ‘n’
  >- gs[]
  >> Cases_on ‘n=0’
  >- ( pop_assum $ rewrite_tac o single
       >> strip_tac
       >> rewrite_tac[sum] >> BETA_TAC
       >> rewrite_tac[ADD, REAL_ADD_LID] >> gs[]
     )
  >> gs[sum, REAL]
  >> rewrite_tac[GSYM REAL_OF_NUM_ADD]
  >> irule REAL_LE_ADD2 >> conj_tac
  >- gs[]
  >> ‘ abs (&n)⁻¹ = inv (abs (&n))’ by gs[ABS_INV]
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_INV_LE_1 >> gs[ABS_N]
QED

Triviality POW4_MINUS1[simp]:
  -1 pow (4 * x) = 1
Proof
  ‘4 * x = 2 * (2 * x)’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> rewrite_tac[POW_MINUS1]
QED

Triviality POW4_DIV2[simp]:
  -1 pow (4 * x DIV 2) = 1
Proof
  ‘4 * x = (x * 2) * 2’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> gs[MULT_DIV]
QED

Theorem approxPoly_soundness:
  ∀ transc iv approxSteps p err.
    approxPolySideCond approxSteps ∧
    approxPoly transc iv approxSteps = SOME (p, err) ⇒
    ∀ x.
      FST iv ≤ x ∧ x ≤ SND iv ⇒
      abs (getFun transc x - evalPoly p x) ≤ err
Proof
  Cases_on ‘transc’ >> gs[approxPoly_def]
  >> rpt strip_tac >> gs[approxPolySideCond_def]
  (* exp function *)
  >- (
    gs[interp_def, getFun_def]
    >> Cases_on ‘iv = (0, inv 2)’ >> gs[]
    (* exp function, 0 to 1/2 *)
    >- (
      qspecl_then [‘x’, ‘approxSteps’] strip_assume_tac MCLAURIN_EXP_LE
      >> pop_assum $ rewrite_tac o single
      >> rpt VAR_EQ_TAC
      >> rewrite_tac[exp_sum_to_poly]
      >> qmatch_goalsub_abbrev_tac ‘abs (exp_taylor + taylor_rem - exp_taylor) ≤ _’
      >> ‘exp_taylor + taylor_rem - exp_taylor = taylor_rem’ by real_tac
      >> pop_assum $ rewrite_tac o single
      >> unabbrev_all_tac
      >> ‘expErrSmall approxSteps = inv (&FACT approxSteps * 2 pow (approxSteps - 1))’
         by gs[expErrSmall_def]
      >> rename1 ‘exp t’
      >> qspecl_then [‘approxSteps’, ‘x’,‘t’] mp_tac exp_remainder_bounded_small
      >> impl_tac >> gs[]
      >> real_tac)
    (* exp function, 0 to 1 *)
    >> ‘1 ≠ inv 2’
      by (once_rewrite_tac [GSYM REAL_INV1]
          >> CCONTR_TAC
          >> pop_assum $ mp_tac o SIMP_RULE std_ss []
          >> rewrite_tac[REAL_INV_INJ] >> real_tac)
    >> rpt VAR_EQ_TAC
    >> rewrite_tac[GSYM poly_compat, eval_simps]
    >> pop_assum $ rewrite_tac o single
    >> rewrite_tac[exp_sum_to_poly]
    >> qspecl_then [‘x’, ‘approxSteps’] strip_assume_tac MCLAURIN_EXP_LE
    >> pop_assum $ rewrite_tac o single
    >> qmatch_goalsub_abbrev_tac ‘abs (exp_taylor + taylor_rem - exp_taylor) ≤ _’
    >> ‘exp_taylor + taylor_rem - exp_taylor = taylor_rem’ by real_tac
    >> pop_assum $ rewrite_tac o single
    >> unabbrev_all_tac
    >> qmatch_goalsub_abbrev_tac ‘expErrBig n _’
    >> ‘expErrBig n approxSteps =
        2 pow n * &n pow approxSteps * inv (&FACT approxSteps * 2 pow approxSteps)’
      by (rewrite_tac[] >> gs[expErrBig_def])
    >> pop_assum $ rewrite_tac o single
    >> qspecl_then [‘approxSteps’, ‘n’, ‘x’,‘t’] mp_tac exp_remainder_bounded_big
    >> impl_tac
    >- (
      rpt conj_tac >> TRY (gs[] >> real_tac >> NO_TAC)
      >> ‘2 * x ≤ &n’
        by (unabbrev_all_tac >> cond_cases_tac
            >> gs[]
            >- (
             ‘SND iv = 0’ by real_tac
             >> pop_assum $ rewrite_tac o single
             >> ‘x = 0’ by real_tac
             >> pop_assum $ rewrite_tac o single
             >> gs[REAL_MUL_RZERO, REAL_DIV_LZERO, EVAL “flr 0”])
            >- (
             pop_assum $ rewrite_tac o single o GSYM
             >> real_tac)
            >> irule REAL_LE_TRANS
            >> qexists_tac ‘&clg (2 * x)’
            >> gs[LE_NUM_CEILING]
            >> cond_cases_tac >> gs[]
            >> rewrite_tac[GSYM REAL_OF_NUM_LE]
            >> irule REAL_LE_TRANS >> qexists_tac ‘&flr (2 * SND iv)’
            >> conj_tac
            >> gs[REAL_OF_NUM_LE]
            >> irule NUM_FLOOR_MONO
            >> rpt conj_tac >> real_tac)
      >- (‘0 ≤ x’ by real_tac >> gs[abs])
      >> irule REAL_LE_TRANS >> qexists_tac ‘abs t’
      >> conj_tac >- gs[ABS_LE]
      >> irule REAL_LE_TRANS >> qexists_tac ‘abs x’
      >> ‘0 ≤ x’ by real_tac
      >> gs[abs])
    >> rewrite_tac[])
    (* sin *)
  >- (
    gs[interp_def, getFun_def] >> rpt VAR_EQ_TAC
    >> qspecl_then [‘x’, ‘approxSteps’] strip_assume_tac MCLAURIN_SIN_LE
    >> gs[]
    >> pop_assum $ rewrite_tac o single
    >> gs[sin_sum_to_poly]
    >> qmatch_goalsub_abbrev_tac ‘abs (sin_taylor + taylor_rem - sin_taylor) ≤ _’
    >> ‘sin_taylor + taylor_rem - sin_taylor = taylor_rem’ by real_tac
    >> pop_assum $ rewrite_tac o single
    >> unabbrev_all_tac
    >> ‘inv (&FACT approxSteps) * sin t  * x pow approxSteps * -1 pow (approxSteps DIV 2) =
        (sin t * ((x pow approxSteps) * inv (&FACT approxSteps) * -1 pow (approxSteps DIV 2)))’
      by real_tac
    >> ‘-(x pow approxSteps) * inv (&FACT approxSteps) * sin t =
        -(sin t * ((x pow approxSteps) * inv (&FACT approxSteps)))’
      by real_tac
    >> rewrite_tac []
    >> ntac 2 $ pop_assum $ rewrite_tac o single
    >> rewrite_tac[GSYM REAL_MUL_ASSOC]
    >> qmatch_goalsub_abbrev_tac ‘_ * err_sin_concr’
    >> rewrite_tac [ABS_NEG, Once ABS_MUL]
    >> irule REAL_LE_TRANS
    >> qexists_tac ‘ 1 * abs err_sin_concr’ >> conj_tac
    >- (irule REAL_LE_RMUL_IMP >> unabbrev_all_tac >> gs[SIN_BOUND, ABS_POS])
    >> rewrite_tac [REAL_MUL_LID, sinErr_def, ABS_MUL]
    >> ‘abs err_sin_concr = err_sin_concr’
      by (unabbrev_all_tac
          >> rewrite_tac[ABS_REFL]
          >> irule REAL_LE_MUL >> conj_tac
          >> gs[REAL_POW_GE0]
          >> irule REAL_LE_MUL >> gs[REAL_POS, REAL_POW_GE0])
    >> pop_assum $ rewrite_tac o single
    >> unabbrev_all_tac
    >> rewrite_tac [sinErr_def]
    >> imp_res_tac EVEN_ODD_EXISTS >> gs[POW_MINUS1]
    >> irule REAL_LE_LMUL_IMP >> gs[POW_ABS]
    >> irule REAL_LE_TRANS
    >> qexists_tac ‘abs (x pow (2 * m'))’ >> gs[ABS_LE, POW_ABS]
    >> rewrite_tac[GSYM POW_ABS]
    >> irule POW_LE >> gs[ABS_POS]
    >> irule RealSimpsTheory.maxAbs >> gs[])
    (* cos function *)
    >- (
      gs[interp_def, getFun_def] >> rpt VAR_EQ_TAC
      >> qspecl_then [‘x’, ‘approxSteps’] strip_assume_tac MCLAURIN_COS_LE
      >> gs[]
      >> pop_assum $ rewrite_tac o single
      >> gs[cos_sum_to_poly]
      >> qmatch_goalsub_abbrev_tac ‘abs (cos_taylor + taylor_rem - cos_taylor) ≤ _’
      >> ‘cos_taylor + taylor_rem - cos_taylor = taylor_rem’ by real_tac
      >> pop_assum $ rewrite_tac o single
      >> unabbrev_all_tac
      >> ‘(x pow approxSteps) * cos t * inv (&FACT approxSteps) =
          (cos t * ((x pow approxSteps) * inv (&FACT approxSteps)))’
        by real_tac
      >> ‘-(x pow approxSteps) * cos t * inv (&FACT approxSteps) =
          -(cos t * ((x pow approxSteps) * inv (&FACT approxSteps)))’
        by real_tac
      >> rewrite_tac []
      >> ntac 2 $ pop_assum $ rewrite_tac o single
      >> rewrite_tac [GSYM REAL_MUL_ASSOC]
      >> qmatch_goalsub_abbrev_tac ‘abs (cos _ * err_cos_concr)’
      >> irule REAL_LE_TRANS
      >> qexists_tac ‘ 1 * abs err_cos_concr’ >> conj_tac
      >- (rewrite_tac[ABS_MUL] >> irule REAL_LE_RMUL_IMP >> unabbrev_all_tac >> gs[COS_BOUND, ABS_POS])
      >> rewrite_tac[REAL_MUL_LID]
      >> ‘abs err_cos_concr = err_cos_concr’
        by (unabbrev_all_tac
            >> rewrite_tac[ABS_REFL]
            >> irule REAL_LE_MUL >> conj_tac
            >- (irule REAL_LE_INV >> gs[REAL_POS])
            >> irule REAL_LE_MUL >> conj_tac
            >> gs[REAL_POW_GE0])
      >> pop_assum $ rewrite_tac o single
      >> unabbrev_all_tac
      >> rewrite_tac [cosErr_def]
      >> imp_res_tac EVEN_ODD_EXISTS >> gs[POW_MINUS1]
      >> irule REAL_LE_LMUL_IMP >> gs[GSYM POW_ABS]
      >> irule REAL_LE_TRANS
      >> qexists_tac ‘abs (x pow (2 * m'))’ >> gs[ABS_LE, POW_ABS]
      >> rewrite_tac [GSYM POW_ABS]
      >> irule POW_LE >> gs[ABS_POS]
      >> irule RealSimpsTheory.maxAbs >> gs[])
  (* atn *)
  >- (
    gs[interp_def, getFun_def] >> rpt VAR_EQ_TAC
    >> qspecl_then [‘x’, ‘approxSteps’] mp_tac MCLAURIN_ATN
    >> impl_tac
    >- (
      irule REAL_LET_TRANS >> qexists_tac ‘max (abs (FST iv)) (abs (SND iv))’
      >> gs[RealSimpsTheory.maxAbs])
    >> strip_tac
    >> gs[atnPoly_correct]
    >> irule REAL_LE_TRANS
    >> qexists_tac ‘abs x pow approxSteps / (1 - abs x)’ >> gs[atnErr_def]
    >> rewrite_tac[real_div]
    >> irule REAL_LE_MUL2 >> rpt conj_tac
    >- (
      irule POW_LE >> gs[ABS_POS]
      >> gs[RealSimpsTheory.maxAbs])
    >- (
      irule REAL_LE_INV2 >> rpt conj_tac
      >- gs[REAL_SUB_LT]
      >> rewrite_tac [real_sub]
      >> irule REAL_LE_LADD_IMP
      >> gs[REAL_LE_NEG]
      >> irule RealSimpsTheory.maxAbs >> gs[])
    >- (
      irule POW_POS >> gs[ABS_POS])
    >> irule REAL_LE_INV
    >> gs[REAL_SUB_LE]
    >> ‘abs x < 1’ suffices_by real_tac
    >> irule REAL_LET_TRANS
    >> qexists_tac ‘max (abs (FST iv)) (abs (SND iv))’ >> gs[]
    >> gs[RealSimpsTheory.maxAbs])
  (* sqrt *)
  >- (
    gs[interp_def, getFun_def]
    >> qspecl_then [‘x-1’, ‘approxSteps’] mp_tac MCLAURTIN_SQRT_LE
    >> impl_tac
    >- ( gs[GSYM REAL_LT_ADD_SUB]
         >> irule REAL_LTE_TRANS
         >> qexists_tac ‘FST iv’ >> gs[]
       )
    >> strip_tac
    >> rewrite_tac[sqrt_sum_to_poly, sqrtErr_def]
    >> pop_assum  mp_tac
    >> BETA_TAC
    >> ‘(1 + (x − 1)) = x’ by REAL_ARITH_TAC
    >> ASM_REWRITE_TAC[]
    >> ‘sqrt (x) = exp ((\x. (ln (x)) / &2) x)’ by
      ( irule SQRT_EXPLN_GENERAL
        >> irule REAL_LTE_TRANS
        >> qexists_tac ‘FST iv’ >> gs[]
        >> irule REAL_LT_TRANS
        >> qexists_tac ‘&1’ >> gs[]
      )
    >> ASM_REWRITE_TAC[]
    >> strip_tac >> BETA_TAC >> ASM_REWRITE_TAC[]
    >> ‘approxSteps ≠ 0 ’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> ‘∀ x y z: real. x + y -z = -(z-x) + y’ by REAL_ARITH_TAC
    >> pop_assum $ rewrite_tac o single
    >> rewrite_tac[sum_sub]
    >> irule REAL_LE_TRANS
    >> qexists_tac ‘abs
              (- sum (0,approxSteps)
                 (λn.
                      (λm.
                           (if m = 0 then exp (ln (1 + 0) / 2)
                            else
                              -1 pow (m − 1) * &FACT (2 * PRE m) *
                              (exp (&(2 * PRE m + 1) * ln (1 + 0) / 2))⁻¹ *
                              (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹ *
                              (&FACT (m − 1))⁻¹) / &FACT m * x pow m) n −
                      (λm.
                           (if m = 0 then exp (ln (1 + 0) / 2)
                            else
                               -1 pow (m − 1) * &FACT (2 * PRE m) *
                              (exp (&(2 * PRE m + 1) * ln (1 + 0) / 2))⁻¹ *
                              (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹ *
                              (&FACT (m − 1))⁻¹) / &FACT m * (x-1) pow m) n)) +
                    abs ( -1 pow (approxSteps − 1) *
                          &FACT (2 * PRE approxSteps) *
                        (exp (&(2 * PRE approxSteps + 1) * ln (1 + t) / 2))⁻¹ *
                        (2 pow approxSteps)⁻¹ * (2 pow (approxSteps − 1))⁻¹ *
                        (&FACT (approxSteps − 1))⁻¹ / &FACT approxSteps *
                        (x − 1) pow approxSteps) ’
    >> conj_tac
    >- gs[ABS_TRIANGLE]
    >> rewrite_tac[ABS_NEG]
    >> ‘(λn.
                  (λm.
                       (if m = 0 then exp (ln (1 + 0) / 2)
                        else
                          -1 pow (m − 1) * &FACT (2 * PRE m) *
                          (exp (&(2 * PRE m + 1) * ln (1 + 0) / 2))⁻¹ *
                          (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹ * (&FACT (m − 1))⁻¹) /
                       &FACT m * x pow m) n −
                  (λm.
                       (if m = 0 then exp (ln (1 + 0) / 2)
                        else
                          -1 pow (m − 1) * &FACT (2 * PRE m) *
                          (exp (&(2 * PRE m + 1) * ln (1 + 0) / 2))⁻¹ *
                          (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹ * (&FACT (m − 1))⁻¹) /
                       &FACT m * (x − 1) pow m) n) =
        \m. (if m = 0 then exp (ln (1 + 0) / 2)
                        else
                          -1 pow (m − 1) * &FACT (2 * PRE m) *
                          (exp (&(2 * PRE m + 1) * ln (1 + 0) / 2))⁻¹ *
                          (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹ * (&FACT (m − 1))⁻¹) /
                                                                               &FACT m * (x pow m - (x-1) pow m)’
      by
      ( gs[FUN_EQ_THM] >> rpt strip_tac
        >> cond_cases_tac
        >- gs[]
        >> real_tac
      )
    >> pop_assum $ rewrite_tac o single
    >> irule REAL_LE_ADD2 >> conj_tac
    >- ( gs[LN_1, EXP_0]
         >> irule REAL_LE_TRANS
         >> qexists_tac ‘sum (0,approxSteps)
                         (λm. abs
                     ( (&FACT m)⁻¹ * (x pow m − (x − 1) pow m) *
                      if m = 0 then 1
                      else
                        &FACT (2 * PRE m) * (&FACT (m − 1))⁻¹ *
                        -1 pow (m − 1) * (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹))’
         >> conj_tac
         >- gs[SUM_ABS_LE]
         >> ‘ (λm.
                  (&FACT m)⁻¹ *
                  max (abs (FST iv)) (abs (SND iv)) pow approxSteps *
                  if m = 0 then 1
                  else
                    &FACT (2 * PRE m) * (&FACT (m − 1))⁻¹ *
                    (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹) =
             (λm. abs
                 ((\m. (&FACT m)⁻¹ *
                  max (abs (FST iv)) (abs (SND iv)) pow approxSteps *
                  if m = 0 then 1
                  else
                    &FACT (2 * PRE m) * (&FACT (m − 1))⁻¹ *
                    (2 pow m)⁻¹ * (2 pow (m − 1))⁻¹) m))’ by
           ( gs[FUN_EQ_THM] >> rpt strip_tac
             >> cond_cases_tac
             >- gs[REAL_MUL_RID, FACT]
             >> irule REAL_LE_MUL
             >> conj_tac
             >- ( irule REAL_LE_MUL
                  >> conj_tac
                  >- ( irule REAL_LT_IMP_LE
                       >> irule REAL_INV_POS >> irule REAL_NZ_IMP_LT
                       >> ‘∀ m: num. 0 < m ⇒ m ≠ 0’ by gs[]
                       >> first_assum irule
                       >> gs[FACT_LESS]
                     )
                  >> irule POW_POS
                  >> gs[REAL_LE_MAX]
                )
             >> gs[] >> irule REAL_LE_MUL
             >> conj_tac
             >- ( irule REAL_LT_IMP_LE >> irule REAL_NZ_IMP_LT
                  >> ‘∀ m: num. 0 < m ⇒ m ≠ 0’ by gs[]
                  >> first_assum irule
                  >> gs[FACT_LESS]
                )
             >> irule REAL_LT_IMP_LE
             >> irule REAL_INV_POS >> irule REAL_NZ_IMP_LT
             >> ‘∀ m: num. 0 < m ⇒ m ≠ 0’ by gs[]
             >> first_assum irule
             >> gs[FACT_LESS]
           )
         >> pop_assum $ once_rewrite_tac o single
         >> once_rewrite_tac[SUM_ABS]
         >> irule SUM_LE >> conj_tac
         >- (rpt strip_tac
             >> BETA_TAC
             >> cond_cases_tac
             >- gs[]
             >> gs[ABS_MUL]
             >> ‘abs (&FACT r)⁻¹ * abs (&FACT (r − 1))⁻¹ *
                 abs (x pow r − (x − 1) pow r) * &FACT (2 * PRE r) =
                 (abs (&FACT r)⁻¹ * abs (&FACT (r − 1))⁻¹ * &FACT (2 * PRE r))*
                 abs (x pow r − (x − 1) pow r)’ by real_tac
             >> pop_assum $ rewrite_tac o single
             >> ‘ abs (&FACT r)⁻¹ * abs (&FACT (r − 1))⁻¹ *
                  abs (max (abs (FST iv)) (abs (SND iv)) pow approxSteps) *
                  &FACT (2 * PRE r) =
                  (abs (&FACT r)⁻¹ * abs (&FACT (r − 1))⁻¹ * &FACT (2 * PRE r))*
                  abs (max (abs (FST iv)) (abs (SND iv)) pow approxSteps)’ by
               real_tac
             >> pop_assum $ rewrite_tac o single
             >> irule REAL_LE_MUL2
             >> gs[] >> rpt conj_tac
             >- ( ‘abs (x pow r − (x − 1) pow r) =
                   (x pow r − (x − 1) pow r)’ by
                   ( ‘0 ≤ x pow r − (x − 1) pow r’ by
                      ( ‘∀x y:real. x ≤ y ⇒ 0 ≤ y - x’ by REAL_ARITH_TAC
                        >> first_assum irule
                        >> irule POW_LE >> real_tac
                      )
                     >> gs[ABS_REFL]
                   )
                  >> pop_assum $ rewrite_tac o single
                  >> ‘abs (max (abs (FST iv)) (abs (SND iv)) pow approxSteps) =
                      (max (abs (FST iv)) (abs (SND iv)) pow approxSteps) ’ by
                    ( ‘0≤ (max (abs (FST iv)) (abs (SND iv)) pow approxSteps)’
                       by
                       ( irule POW_POS
                         >> gs[REAL_LE_MAX]
                       )
                      >> gs[ABS_REFL]
                    )
                  >> pop_assum $ rewrite_tac o single
                  >> irule REAL_LE_TRANS
                  >> qexists_tac ‘x pow r’
                  >> conj_tac
                  >- ( ‘∀ x y: real. 0 ≤ x ∧ 0≤ y ∧ y ≤ x ⇒
                                     x - y ≤ x’ by REAL_ARITH_TAC
                       >> first_assum irule
                       >> rpt conj_tac
                       >- ( irule POW_LE >> real_tac )
                       >- ( irule POW_POS >> real_tac )
                       >> irule POW_POS >> real_tac
                     )
                  >> irule REAL_LE_TRANS
                  >> qexists_tac ‘x pow approxSteps’
                  >> conj_tac
                  >- ( irule REAL_POW_MONO
                       >> gs[] >> real_tac
                     )
                  >> irule POW_LE
                  >> conj_tac
                  >- ( irule REAL_LE_TRANS
                       >> qexists_tac ‘SND iv’
                       >> conj_tac
                       >- gs[]
                       >> irule REAL_LE_TRANS
                       >> qexists_tac ‘abs (SND iv)’
                       >> conj_tac
                       >- gs[ABS_LE]
                       >> irule REAL_LE_MAX2
                     )
                  >> real_tac
                )
             >> irule REAL_LE_MUL >> gs[]
             >> irule REAL_LE_MUL >> gs[]
            )
         >> gs[]
       )
    >> once_rewrite_tac[real_div] >> gs[ABS_MUL]
    >> ‘abs (exp (ln (1 + t) * &(2 * PRE approxSteps + 1) / 2))⁻¹ *
        abs (&FACT approxSteps)⁻¹ * abs (&FACT (approxSteps − 1))⁻¹ *
        abs ((x − 1) pow approxSteps) * &FACT (2 * PRE approxSteps) =
        ( abs (&FACT approxSteps)⁻¹ * abs (&FACT (approxSteps − 1))⁻¹ *
          &FACT (2 * PRE approxSteps)) *
        (abs (exp (ln (1 + t) * &(2 * PRE approxSteps + 1) / 2))⁻¹ *
         abs ((x − 1) pow approxSteps)) ’ by real_tac
    >> pop_assum $ rewrite_tac o single
    >> ‘abs (&FACT approxSteps)⁻¹ *  abs (&FACT (approxSteps − 1))⁻¹ *
        abs (max (abs (FST iv)) (abs (SND iv)) pow approxSteps) *
        &FACT (2 * PRE approxSteps) =
         ( abs (&FACT approxSteps)⁻¹ * abs (&FACT (approxSteps − 1))⁻¹ *
           &FACT (2 * PRE approxSteps)) *
         ( abs (max (abs (FST iv)) (abs (SND iv)) pow approxSteps))’ by
      real_tac
    >> pop_assum $ rewrite_tac o single
    >> irule REAL_LE_MUL2
    >> gs[]
    >> rpt conj_tac
    >- ( ‘abs (max (abs (FST iv)) (abs (SND iv)) pow approxSteps) =
          &1 * abs (max (abs (FST iv)) (abs (SND iv)) pow approxSteps)’ by
          gs[]
         >> pop_assum $ once_rewrite_tac o single
         >> irule REAL_LE_MUL2
         >> gs[] >> conj_tac
         >- ( ‘ 0 ≠ (exp (ln (1 + t) * &(2 * PRE approxSteps + 1) / 2))’
               by gs[EXP_NZ]
              >> ‘0 ≠  (exp
                        (1 / 2 *
                         (ln (1 ) *
                          &(2 * PRE approxSteps + 1))))’
                by gs[EXP_NZ]
              >> gs[ABS_INV]
              >> ‘0 ≤ exp (ln (1 + t) * &(2 * PRE approxSteps + 1) / 2)’ by
                gs[EXP_POS_LE]
              >> ‘abs (exp (ln (1 + t) * &(2 * PRE approxSteps + 1) / 2)) =
                  exp (ln (1 + t) * &(2 * PRE approxSteps + 1) / 2)’ by
                gs[ABS_REFL]
              >> pop_assum $ rewrite_tac o single
              >> ‘1 = exp 0’ by gs[EXP_0]
              >> pop_assum $ rewrite_tac o single
              >> gs[EXP_MONO_LE]
              >> gs[EXP_0]
              >> irule REAL_LE_MUL
              >> conj_tac
              >- ( irule LN_POS >> real_tac )
              >> gs[]
            )
         >> ‘ abs ((x − 1) pow approxSteps) =  ((x − 1) pow approxSteps)’ by
           ( ‘0 ≤  ((x − 1) pow approxSteps)’ by
              ( irule POW_POS
                >> real_tac
              )
             >> gs[ABS_REFL]
           )
         >> pop_assum $ rewrite_tac o single
         >> ‘abs (max (abs (FST iv)) (abs (SND iv)) pow approxSteps) =
             (max (abs (FST iv)) (abs (SND iv)) pow approxSteps)’ by
           ( ‘0 ≤ max (abs (FST iv)) (abs (SND iv)) pow approxSteps’ by
              ( irule POW_POS
                >> gs[REAL_LE_MAX]
              )
             >> gs[ABS_REFL]
           )
         >> pop_assum $ rewrite_tac o single
         >> irule POW_LE
         >> conj_tac
         >- ( irule REAL_LE_TRANS
              >> qexists_tac ‘x’ >> conj_tac
              >- real_tac
              >> irule REAL_LE_TRANS >> qexists_tac ‘SND iv’
              >> gs[]
              >> irule REAL_LE_TRANS
              >> qexists_tac ‘abs (SND iv)’ >> conj_tac
              >- gs[ABS_LE]
              >> gs[REAL_LE_MAX2]
            )
         >> real_tac
       )
    >- ( once_rewrite_tac[GSYM REAL_MUL_ASSOC]
         >> irule REAL_LE_MUL
         >> gs[]
         >> irule REAL_LE_MUL >> gs[]
       )
    >> once_rewrite_tac[GSYM REAL_MUL_ASSOC]
    >> irule REAL_LE_MUL >> gs[]
  )
  (* ln *)
  >> gs[interp_def, getFun_def]
  >> qspecl_then [‘x-1’, ‘approxSteps’] mp_tac MCLAURIN_LN_POS
  >> impl_tac
  >- (
    gs[] >> gs[GSYM REAL_LT_ADD_SUB]
    >> irule REAL_LTE_TRANS
    >> qexists_tac ‘FST iv’ >> gs[])
  >> strip_tac
  >> gs[log_sum_to_poly_indexshift]
  >> ‘(1 + (x − 1)) = x’ by REAL_ARITH_TAC
  >> gs[]
  >> pop_assum $ kall_tac
  >> qspecl_then [‘approxSteps’, ‘x’] mp_tac log_sum_to_poly_indexshift
  >> impl_tac >- gs[]
  >> disch_then $ rewrite_tac o single
  >> ‘∀ x y z: real. x + y - z = (x - z) + y’ by REAL_ARITH_TAC
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac[logErr_def, REAL_SUB_REFL, REAL_ADD_LID, real_div, ABS_MUL]
  >> rewrite_tac [GSYM REAL_MUL_ASSOC]
  >> irule REAL_LE_LMUL_IMP >> reverse conj_tac
  >- gs[ABS_POS]
  >> irule REAL_LE_MUL2
  >> ‘abs (SND iv - 1) = SND iv - 1’ by real_tac
  >> rpt conj_tac >> gs[ABS_POS, GSYM POW_ABS]
  >- (
    irule POW_LE >> gs[ABS_POS]
    >> ‘0 ≤ x - 1’ by real_tac
    >> gs[abs] >> real_tac)
  >> ‘0 ≤ &approxSteps * (1 + t) pow approxSteps’
    by (irule REAL_LE_MUL >> conj_tac >> gs[])
  >> gs[abs, REAL_INV_MUL']
  >> once_rewrite_tac [GSYM REAL_INV1]
  >> irule REAL_LE_INV2 >> rpt conj_tac >> gs[]
  >> qspec_then ‘approxSteps’ (once_rewrite_tac o single) $ GSYM POW_ONE
  >> irule POW_LE >> gs[] >> real_tac
  (* Tan function missing here as they are unimplemented *)
QED

val _ = export_theory();

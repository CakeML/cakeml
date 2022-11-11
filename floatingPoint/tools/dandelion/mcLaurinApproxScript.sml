(***
  Proofs of McLaurin series for the supported elementary functions
  described in transcLang file
**)

open moreRealTheory realPolyTheory realPolyProofsTheory;
open preambleDandelion;

val _ = new_theory "mcLaurinApprox";

val _ = realLib.deprecate_real();

Theorem SUCC_minus_1[local]:
  ∀ m. 0 < m ⇒ (SUC m DIV 2) = (m - 1) DIV 2 + 1
Proof
  rpt gen_tac
  >> ‘0 < m ⇒ SUC m = (m - 1) + 2’ by gs[]
  >> strip_tac >> res_tac
  >> pop_assum $ rewrite_tac o single
  >> gs[ADD_DIV_RWT]
QED

Theorem minus_1_div_2[local]:
  ∀ m. 0 < m ⇒ -1 pow (SUC m DIV 2) = - ( -1 pow ((m - 1) DIV 2))
Proof
  rpt strip_tac  >> gs[SUCC_minus_1, REAL_POW_ADD]
QED

Theorem plus_1_div_2[local]:
  ∀ m. 0 < m ⇒ -1 pow (SUC (SUC m) DIV 2) = - (-1 pow (m DIV 2))
Proof
  rpt strip_tac
  >> ‘SUC (SUC m) = m + 2’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> gs[ADD_DIV_RWT, REAL_POW_ADD]
QED

Theorem MCLAURIN_SIN_LE:
  ∀ x n.
    ∃ t.
      abs(t) ≤ abs (x) ∧
      (\n. if EVEN n then
             (sin x =
              sum(0,n)
                 (λm.
                    inv (&FACT m) * x pow m *
                    if EVEN m then sin 0 * -1 pow (m DIV 2)
                    else cos 0 * -1 pow ((m - 1) DIV 2)) +
              inv (&FACT n) * sin t * x pow n * -1 pow (n DIV 2))
           else
             (sin x =
              sum (0,n)
                  (λm.
                     inv (&FACT m) * x pow m *
                     if EVEN m then sin 0 * -1 pow (m DIV 2)
                     else cos 0 * -1 pow ((m - 1) DIV 2)) +
              cos t * inv (&FACT n) * x pow n *
              -1 pow ((n - 1) DIV 2))) n
Proof
  rpt strip_tac
  >> assume_tac MCLAURIN_ALL_LE
  >> pop_assum $ qspec_then ‘sin’ assume_tac
  >> pop_assum $ qspec_then ‘\n x. if EVEN n then (((-1) pow (n DIV 2)) * sin x)
                                 else (((-1) pow ((n-1) DIV 2)) * cos x)’
               assume_tac
  >> ‘(λn x.
             if EVEN n then -1 pow (n DIV 2) * sin x
             else -1 pow ((n - 1) DIV 2) * cos x) 0 =
        sin /\
        (!m x.
           ((λn x.
                 if EVEN n then -1 pow (n DIV 2) * sin x
                 else -1 pow ((n - 1) DIV 2) * cos x) m diffl
            (λn x.
                 if EVEN n then -1 pow (n DIV 2) * sin x
                 else -1 pow ((n - 1) DIV 2) * cos x) (SUC m) x) x)’ by
    ( conj_tac
      >- ( BETA_TAC >> gs[FUN_EQ_THM] )
      >> rpt strip_tac
      >> BETA_TAC
      >> Cases_on ‘m=0’
      >- ( gs[EVEN] >> ‘(λx. sin x) = sin’ by gs[FUN_EQ_THM]
           >> pop_assum $ rewrite_tac o single
           >> gs[ DIFF_SIN]
         )
      >> Cases_on ‘EVEN m’
      >- ( gs[EVEN]
           >> ‘(λx. sin x * -1 pow (m DIV 2)) = (λx. -1 pow (m DIV 2) * sin x)’
             by gs[FUN_EQ_THM]
           >> pop_assum $ rewrite_tac o single
           >> ‘(cos x * -1 pow (m DIV 2)) = ( -1 pow (m DIV 2) * cos x)’ by
             gs[FUN_EQ_THM]
           >> pop_assum $ rewrite_tac o single
           >> irule limTheory.DIFF_CMUL
           >> gs[DIFF_SIN]
         )
      >> gs[EVEN]
      >> ‘(λx. cos x * -1 pow ((m - 1) DIV 2)) =
          (λx. -1 pow ((m - 1) DIV 2) * cos x)’ by gs[FUN_EQ_THM]
      >> pop_assum $ rewrite_tac o single
      >> ‘(sin x * -1 pow (SUC m DIV 2)) = ( -1 pow (SUC m DIV 2) * sin x)’
        by gs[FUN_EQ_THM]
      >> pop_assum $ rewrite_tac o single
      >>‘-1 pow (SUC m DIV 2) = - (-1 pow ((m - 1) DIV 2))’ by
        ( irule minus_1_div_2 >> gs[] )
      >> pop_assum $ rewrite_tac o single
      >> ‘(-(-1 pow ((m - 1) DIV 2)) * sin x) =
          ((-1 pow ((m - 1) DIV 2)) *(- sin x))’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> irule limTheory.DIFF_CMUL
      >> gs[DIFF_COS]
    )
  >> res_tac
  >> pop_assum mp_tac
  >> DISCH_THEN (fn th => REPEAT GEN_TAC THEN STRIP_ASSUME_TAC (SPEC_ALL th))
  >> qexists_tac ‘t’
  >> gs[]
QED

Theorem MCLAURIN_COS_LE:
  ∀ x n.
    ∃ t.
      abs(t) <= abs (x) ∧
      (\n. if EVEN n then
             (cos x = sum(0,n)
                         (λm.
                            (&FACT m)⁻¹ * x pow m *
                            if EVEN m then cos 0 * -1 pow (m DIV 2)
                            else sin 0 * -1 pow ((SUC m) DIV 2)) +
                      (&FACT n)⁻¹ * cos t * x pow n * -1 pow (n DIV 2))
           else
             (cos x = sum (0,n)
                          (λm.
                             (&FACT m)⁻¹ * x pow m *
                             if EVEN m then cos 0 * -1 pow (m DIV 2)
                             else sin 0 * -1 pow ((SUC m) DIV 2)) +
                      sin t * (&FACT n)⁻¹ * x pow n *
                      -1 pow ((SUC n) DIV 2))) n
Proof
  rpt strip_tac
  >> assume_tac MCLAURIN_ALL_LE
  >> pop_assum $ qspec_then ‘cos’ assume_tac
  >> pop_assum $ qspec_then ‘\n x. if EVEN n then (((-1) pow (n DIV 2)) * cos x)
                                 else (((-1) pow ((SUC n) DIV 2)) * sin x)’
               assume_tac
  >> ‘(λn x.
             if EVEN n then -1 pow (n DIV 2) * cos x
             else -1 pow (SUC n DIV 2) * sin x) 0 =
        cos /\
        (!m x.
           ((λn x.
                 if EVEN n then -1 pow (n DIV 2) * cos x
                 else -1 pow (SUC n DIV 2) * sin x) m diffl
            (λn x.
                 if EVEN n then -1 pow (n DIV 2) * cos x
                 else -1 pow (SUC n DIV 2) * sin x) (SUC m) x) x)’ by
    ( conj_tac
      >- ( BETA_TAC >> gs[FUN_EQ_THM] )
      >> rpt strip_tac
      >> BETA_TAC
      >> Cases_on ‘m=0’
      >- ( gs[EVEN] >> ‘(λx. cos x) = cos’ by gs[FUN_EQ_THM]
           >> pop_assum $ rewrite_tac o single
           >> gs[DIFF_COS]
         )
      >> Cases_on ‘EVEN m’
      >- ( gs[EVEN]
           >> ‘(λx. cos x * -1 pow (m DIV 2)) = (λx. -1 pow (m DIV 2) * cos x)’
             by gs[FUN_EQ_THM]
           >> pop_assum $ rewrite_tac o single
           >>‘-1 pow (SUC (SUC m) DIV 2) = - (-1 pow (m DIV 2))’
             by gs[plus_1_div_2]
           >> pop_assum $ rewrite_tac o single
           >> ‘(sin x * -(-1 pow (m DIV 2))) = (-1 pow (m DIV 2) * - sin x)’
             by gs[]
           >> pop_assum $ rewrite_tac o single
           >> irule limTheory.DIFF_CMUL
           >> gs[DIFF_COS]
         )
      >> gs[EVEN]
      >> ‘(λx. sin x * -1 pow (SUC m DIV 2)) =
          (λx.  -1 pow (SUC m DIV 2) * sin x )’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> ‘(cos x * -1 pow (SUC m DIV 2)) =
          (-1 pow (SUC m DIV 2)) * cos x’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> irule limTheory.DIFF_CMUL
      >> gs[DIFF_SIN]
    )
  >> res_tac
  >> pop_assum mp_tac
  >> DISCH_THEN (fn th => REPEAT GEN_TAC THEN STRIP_ASSUME_TAC (SPEC_ALL th))
  >> qexists_tac ‘t’
  >> gs[]
QED

(*** Prove lemma for bound on exp in the interval, x IN [0, 0.5]
based on John Harrison's paper **)
Theorem REAL_EXP_BOUND_LEMMA:
  ! x.
    &0 <= x /\ x <= inv 2 ==>
    exp(x) <= &1 + &2 * x
Proof
  rpt strip_tac >> irule REAL_LE_TRANS
  >> qexists_tac ‘suminf (λ n. x pow n)’ >> conj_tac
  >- (
    gs[exp] >> irule seqTheory.SER_LE
    >> gs[seqTheory.summable] >> rpt conj_tac
    >- (
      rpt strip_tac
      >> jrhUtils.GEN_REWR_TAC RAND_CONV [GSYM REAL_MUL_LID]
      >> irule REAL_LE_RMUL_IMP >> gs[POW_POS]
      >> irule REAL_INV_LE_1
      >> gs[REAL_OF_NUM_LE, LESS_EQ_IFF_LESS_SUC]
      >> ‘1 = SUC 0’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> gs[LESS_MONO_EQ, FACT_LESS])
    >- (qexists_tac ‘exp x’ >> gs[BETA_RULE EXP_CONVERGES] )
    >> qexists_tac ‘inv (1 - x)’
    >> irule seqTheory.GP
    >> gs[abs] >> irule REAL_LET_TRANS >> qexists_tac ‘inv 2’
    >> conj_tac >> gs[])
  >> ‘suminf (λ n. x pow n) = inv (1 - x)’
     by (
      irule $ GSYM seqTheory.SUM_UNIQ
      >> irule seqTheory.GP
      >> gs[abs] >> irule REAL_LET_TRANS >> qexists_tac ‘inv 2’
      >> conj_tac >> gs[])
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_LE_RCANCEL_IMP
  >> qexists_tac ‘1 - x’
  >> ‘1 - x <> 0’ by (CCONTR_TAC >> gs[])
  >> simp[REAL_MUL_LINV]
  >> conj_tac
  >- (
    irule REAL_LET_TRANS >> qexists_tac ‘inv 2 - x’
    >> rewrite_tac[REAL_ARITH “&0 <= x:real - y <=> y <= x”]
    >> rewrite_tac[REAL_ARITH “a - x < b - x <=> a < b:real”]
    >> gs[])
  >> gs[REAL_SUB_LDISTRIB, REAL_ADD_LDISTRIB]
  >> rewrite_tac[POW_2,
                 REAL_ARITH “&1 <= &1 + &2 * x:real - (x + &2 * (x * x)) <=>
                             x * (&2 * x) <= x * &1”]
  >> irule REAL_LE_LMUL_IMP >> gs[]
  >> irule REAL_LE_RCANCEL_IMP >> qexists_tac ‘inv 2’
  >> rewrite_tac[REAL_MUL_LID, REAL_ARITH “2 * x * inv 2 = x:real * (2 * inv 2)”]
  >> gs[REAL_MUL_RINV]
QED

Theorem REAL_EXP_MINUS1_BOUND_LEMMA:
  !x. &0 <= x /\ x <= inv(&2) ==> &1 - exp(-x) <= &2 * x
Proof
  REPEAT STRIP_TAC >> REWRITE_TAC[REAL_LE_SUB_RADD]
  >> ONCE_REWRITE_TAC[REAL_ADD_SYM]
  >> REWRITE_TAC[GSYM REAL_LE_SUB_RADD]
  >> irule REAL_LE_RCANCEL_IMP
  >> EXISTS_TAC “exp(x)”
  >> REWRITE_TAC[REAL_ADD_LINV, EXP_0, EXP_POS_LT]
  >> MATCH_MP_TAC REAL_LE_TRANS
  >> EXISTS_TAC “(&1 - &2 * (x:real)) * (&1 + &2 * x)”
  >> CONJ_TAC
  >- ( irule REAL_LE_LMUL_IMP >> reverse conj_tac
       >- ( REWRITE_TAC[REAL_LE_SUB_LADD, REAL_ADD_LID]
            >> MATCH_MP_TAC REAL_LE_TRANS
            >> EXISTS_TAC “&2 * inv(&2)”
            >> reverse CONJ_TAC
            >- gs[]
            >> irule REAL_LE_LMUL_IMP >> gs[]
          )
       >> MATCH_MP_TAC REAL_EXP_BOUND_LEMMA >> gs[]
     )
  >> ONCE_REWRITE_TAC[REAL_MUL_SYM]
  >> REWRITE_TAC[REAL_DIFFSQ]
  >> REWRITE_TAC[REAL_MUL_LID, REAL_LE_SUB_RADD, EXP_NEG_MUL]
  >> REWRITE_TAC[REAL_LE_ADDR]
  >> MATCH_MP_TAC REAL_LE_MUL >> REWRITE_TAC[]
  >> MATCH_MP_TAC REAL_LE_MUL >> gs[]
QED

(** Mclaurin series for sqrt fucntion **)
(** Idea is to convert the sqrt function to exp (ln x /2) **)
Theorem SQRT_EXPLN_DIFF:
  !x. 0 <= x ==> ((λx. exp ((\x. (ln (1+x)) / &2) x)) diffl
               (exp ((\x. (ln (1+x)) / &2) x) * (inv (1+x) / &2))) x
Proof
  rpt strip_tac >> irule DIFF_COMPOSITE_EXP
  >> ‘(λx. ln (1+x) / 2) = (λx. (1/ &2) * (ln (1+x)))’ by
    ( gs[FUN_EQ_THM])
  >> pop_assum $ rewrite_tac o single
  >> ‘((1+x)⁻¹ / 2) = (1/ &2) * (inv (1+x))’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx. 1 / 2 * ln (1 + x)) = (λx. 1 / 2 * ((\x. ln (1 + x)) x))’ by
    ( gs[FUN_EQ_THM])
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘(1 + x)⁻¹ = ((\x. (1 + x)) x)⁻¹ * &1’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> ‘(λx. ln (1 + x)) = (λx. ln ((\x. (1 + x)) x))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> irule DIFF_LN_COMPOSITE
  >> rpt conj_tac
  >- ( gs[] >> ‘&1+x = x+ &1 ’ by REAL_ARITH_TAC
       >> pop_assum $ rewrite_tac o single
       >> gs[REAL_LET_ADD]
     )
  >> gs[diff_chain]
QED

Theorem SQRT_EXPLN_GENERAL:
  !x. 0 < x ==> sqrt (x) = exp ((\x. (ln (x)) / &2) x)
Proof
  rpt strip_tac >> gs[sqrt]
  >> ‘2 = SUC 1’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule ROOT_LN >> gs[]
QED

Theorem SQRT_EXPLN:
  !x. 0 <= x ==> sqrt (1+x) = exp ((\x. (ln (1+x)) / &2) x)
Proof
  rpt strip_tac >> gs[sqrt]
  >> ‘2 = SUC 1’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule ROOT_LN
  >> ‘&1 + x = x + &1’ by REAL_ARITH_TAC
  >> pop_assum $ rewrite_tac o single
  >> gs[REAL_LET_ADD]
QED

Theorem exp_add_EXPLN:
  ! m t. m <> 0 ==> 0 <= t ==>
   exp (ln (1 + t) * &(2 * m + 1) / &2) =
   exp (ln (1 + t)) * exp ((ln (1 + t) * &(2 * PRE m + 1) / &2))
Proof
  rpt strip_tac
  >> ‘ exp (ln (1 + t)) * exp (ln (1 + t) * &(2 * PRE m + 1) / &2) =
       exp ((ln (1 + t)) + (ln (1 + t) * &(2 * PRE m + 1) / &2))’ by
    ( ABBREV_TAC “x = ln (1 + t) ”
      >> ‘ &(2 * PRE m + 1) / 2 =  &(2 * PRE m + 1) * inv(&2)’ by gs[]
      >> ‘x * &(2 * PRE m + 1) / 2 = x * &(2 * PRE m + 1) * inv(&2) ’
        by gs[]
      >> pop_assum $ rewrite_tac o single
      >> ‘exp (x + x * &(2 * PRE m + 1) * 2⁻¹) =
          exp x * exp (x * &(2 * PRE m + 1) * 2⁻¹)’ by
        ( ABBREV_TAC “y = x * &(2 * PRE m + 1) * 2⁻¹”
          >> rw[transcTheory.EXP_ADD]
        )
      >> gs[]
    )
  >> pop_assum $ rewrite_tac o single
  >> ‘(ln (1 + t) * &(2 * m + 1) / &2) =
      (ln (1 + t) + (ln (1 + t) * &(2 * PRE m + 1) / &2))  ’ by
    ( ‘ ln (1 + t) * &(2 * PRE m + 1) / 2 =
        ln (1 + t) *( &(2 * PRE m + 1) * inv(&2))’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> ‘ln (1 + t) + ln (1 + t) * (&(2 * PRE m + 1) * 2⁻¹) =
          ln (1 + t) * &1 + ln (1 + t) * (&(2 * PRE m + 1) * 2⁻¹)’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> ‘ln (1 + t) * 1 + ln (1 + t) * (&(2 * PRE m + 1) * 2⁻¹) =
          ln (1 + t) * (1 + (&(2 * PRE m + 1) * 2⁻¹))’ by gs[GSYM REAL_LDISTRIB]
      >> pop_assum $ rewrite_tac o single
      >> gs[]
      >> DISJ2_TAC
      >> ‘ 1 / &2 = inv(&2)’ by gs[GSYM REAL_INV_1OVER]
      >> pop_assum $ rewrite_tac o single
      >> gs[REAL_LDISTRIB]
    )
  >> pop_assum $ once_rewrite_tac o single
  >> gs[]
QED

Theorem sqrt_mth_derivative:
  !m t.
    m <> 0 ==> 0 <= t ==>
    ((λx. (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹) diffl
         (-1 / 2 * ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * &(2 * m - 1))))
    t
Proof
  rpt strip_tac
  >> ‘(λx. (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹) =
      (λx. (exp (- (ln (1 + x) * &(2 * PRE m + 1) / 2))))’ by
    ( gs[FUN_EQ_THM, EXP_NEG] )
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx. exp (-(ln (1 + x) * &(2 * PRE m + 1) / 2))) =
      (λx. exp ( (\x. (-(ln (1 + x) * &(2 * PRE m + 1) / 2))) x))’ by
    gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘(-1 / 2 * ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * &(2 * m - 1))) =
     exp ( (\x. (-(ln (1 + x) * &(2 * PRE m + 1) / 2))) t) * (&(2 * PRE m + 1)
                        / &2 * - inv (1+t))’ by
    ( gs[]
      >> ‘ (exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ =
           (exp (- ((ln (1 + t) * &(2 * m + 1) / 2))))’ by gs[EXP_NEG]
      >> pop_assum $ rewrite_tac o single
      >> ‘(1 + t)⁻¹ = exp (- (ln (1+t)))’ by
        ( ‘- ln (1 + t) = ln (inv (1+t))’ by
           ( ‘0 < &1 + t’ by
              ( ‘&1+t = t+ &1 ’ by REAL_ARITH_TAC
                >> pop_assum $ rewrite_tac o single
                >> gs[REAL_LET_ADD]
              )
             >> gs[LN_INV]
           )
          >> pop_assum $ rewrite_tac o single
          >> gs[EXP_LN]
          >>‘&1+t = t+ &1 ’ by REAL_ARITH_TAC
          >> pop_assum $ rewrite_tac o single
          >> gs[REAL_LET_ADD]
        )
      >> pop_assum $ rewrite_tac o single
      >> ‘ exp (-(ln (1 + t) * &(2 * PRE m + 1)) / 2) * &(2 * PRE m + 1) *
           exp (-ln (1 + t)) =
           ( exp (-(ln (1 + t) * &(2 * PRE m + 1)) / 2) *  exp (-ln (1 + t))) *
           &(2 * PRE m + 1)’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> ‘&(2 * m - 1) =  &(2 * PRE m + 1)’ by gs[]
      >> ‘ exp (-(ln (1 + t) * &(2 * m + 1) / 2)) =
           ( exp (-(ln (1 + t) * &(2 * PRE m + 1) / 2)) *  exp (-ln (1 + t)))’
        by ( gs[EXP_NEG] >> gs[GSYM REAL_INV_MUL']
             >> gs[exp_add_EXPLN]
           )
      >> gs[]
    )
  >> pop_assum $ rewrite_tac o single
  >> irule DIFF_COMPOSITE_EXP
  >> ‘(λx. -(ln (1 + x) * &(2 * PRE m + 1) / 2)) =
      (λx. (-(&(2 * PRE m + 1) / 2)) *((\x. ln (1+x)) x))’ by
    ( gs[FUN_EQ_THM] )
  >> pop_assum $ rewrite_tac o single
  >> ‘ (&(2 * PRE m + 1) / 2 * -(1 + t)⁻¹) =
       (-(&(2 * PRE m + 1) / 2)) * (1 + t)⁻¹’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘(λx. ln (1 + x)) = (λx. ln ((\x. (1 + x)) x))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘(1 + t)⁻¹ = (((\x . (1 + x)) t)⁻¹) * &1 ’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> irule DIFF_LN_COMPOSITE
  >> conj_tac
  >- ( gs[] >> ‘&1+t = t+ &1 ’ by REAL_ARITH_TAC
       >> pop_assum $ rewrite_tac o single
       >> gs[REAL_LET_ADD]
     )
  >> gs[diff_chain]
QED

Theorem SQRT_DIFF_m_not_0:
  ! m x t. 0 <= t ==> m <> 0 ==>
           ((λx'.
               (exp (ln (1 + x') * &(2 * PRE m + 1) / 2))⁻¹ *
               &FACT (2 * PRE m) * (&FACT (m - 1))⁻¹ * -1 pow (m - 1) *
               (2 pow m)⁻¹ * (2 pow (m - 1))⁻¹) diffl
            ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&FACT m)⁻¹ *
             &FACT (2 * m) * -1 pow m * (2 pow m)⁻¹ * (2 pow SUC m)⁻¹)) t
Proof
  rpt strip_tac
  >> ‘(λx'.
         (exp (ln (1 + x') * &(2 * PRE m + 1) / 2))⁻¹ *
         &FACT (2 * PRE m) * (&FACT (m - 1))⁻¹ * -1 pow (m - 1) *
         (2 pow m)⁻¹ * (2 pow (m - 1))⁻¹) =
      (λx'.
         -1 pow (m - 1) * ((\x. ((exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ *
             &FACT (2 * PRE m) * (&FACT (m - 1))⁻¹ *
               (2 pow m)⁻¹ * (2 pow (m - 1))⁻¹)) x'))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘-1 pow m = -1 pow (m-1) * -1 pow 1’ by
    ( ‘m = (m-1) + 1’ by gs[]
      >> ‘-1 pow m  = -1 pow ((m-1) + 1)’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> gs[REAL_POW_ADD]
    )
  >> pop_assum $ rewrite_tac o single
  >> ‘ ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&FACT m)⁻¹ *
          &FACT (2 * m) * (-1 pow (m - 1) * -1 pow 1) * (2 pow m)⁻¹ *
          (2 pow SUC m)⁻¹) =
      -1 pow (m - 1) *  ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&FACT m)⁻¹ *
          &FACT (2 * m)  * -1 pow 1 * (2 pow m)⁻¹ *
          (2 pow SUC m)⁻¹)’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘inv (&FACT m) = inv (&FACT (m-1)) * inv (&m)’ by
    ( ‘FACT m = m * FACT(m-1)’ by
       ( ‘m = SUC (m-1)’ by gs[]
         >> pop_assum $ once_rewrite_tac o single
         >> ‘FACT (SUC (m - 1) - 1) = FACT (m - 1)’ by gs[]
         >> pop_assum $ rewrite_tac o single
         >> gs[FACT]
       )
      >> pop_assum $ rewrite_tac o single
      >> once_rewrite_tac[GSYM REAL_OF_NUM_MUL]
      >> gs[REAL_INV_MUL']
    )
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx.
         (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ *
         &FACT (2 * PRE m) * (&FACT (m - 1))⁻¹ * (2 pow m)⁻¹ *
         (2 pow (m - 1))⁻¹) =
      (λx.
         (&FACT (m - 1))⁻¹ * ((\x. (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ *
                                   &FACT (2 * PRE m) *  (2 pow m)⁻¹ *
                                   (2 pow (m - 1))⁻¹) x))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘ ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ *
          ((&FACT (m - 1))⁻¹ * (&m)⁻¹) * &FACT (2 * m) * -1 pow 1 *
          (2 pow m)⁻¹ * (2 pow SUC m)⁻¹) =
      ((&FACT (m - 1))⁻¹ * (((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ *
           (&m)⁻¹) * &FACT (2 * m) * -1 pow 1 *
                            (2 pow m)⁻¹ * (2 pow SUC m)⁻¹))’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘(λx.
         (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ *
         &FACT (2 * PRE m) * (2 pow m)⁻¹ * (2 pow (m - 1))⁻¹) =
      (λx.
         (2 pow m)⁻¹ * ((\x. (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ *
                             &FACT (2 * PRE m) * (2 pow (m - 1))⁻¹) x))’
    by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘ ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&m)⁻¹ * &FACT (2 * m) *
        -1 pow 1 * (2 pow m)⁻¹ * (2 pow SUC m)⁻¹) =
       (2 pow m)⁻¹ *
       (((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&m)⁻¹ * &FACT (2 * m) *
         -1 pow 1 *  (2 pow SUC m)⁻¹))’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘2 pow (SUC m) = 2 pow (m-1) * 2 pow 2’ by
    ( ‘SUC m = (m-1) + 2’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> gs[REAL_POW_ADD]
    )
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx.
         (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ *
         &FACT (2 * PRE m) * (2 pow (m - 1))⁻¹) =
      (λx.
         (2 pow (m - 1))⁻¹ * ((\x. (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ *
                                   &FACT (2 * PRE m)) x)) ’  by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘(2 pow (m - 1) * 2²)⁻¹ =  (2 pow (m - 1))⁻¹ * inv (2²)’ by
    gs[REAL_INV_MUL']
  >> pop_assum $ rewrite_tac o single
  >> ‘ ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&m)⁻¹ * &FACT (2 * m) *
        -1 pow 1 * ((2 pow (m - 1))⁻¹ * 2² ⁻¹)) =
       (2 pow (m - 1))⁻¹ *
       ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&m)⁻¹ * &FACT (2 * m) *
        -1 pow 1 * inv (2²))’ by REAL_ARITH_TAC
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘ &FACT (2 * m) = &(2 * m) * &(2 * m - 1) * &FACT (2 * PRE m) ’ by
    ( ‘&FACT (2 * m) = &(2 * m) * &FACT(2 * m - 1)’ by
       ( ‘&FACT (2 * m) = &FACT (SUC (2* m - 1))’ by
          ( ‘(2 * m) = (SUC (2* m - 1))’ by gs[]
            >> pop_assum $ once_rewrite_tac o single
            >> ‘(SUC (SUC (2 * m - 1) - 1)) = (SUC (2 * m - 1))’ by gs[]
            >> gs[]
          )
         >> ‘ &(2 * m) = &(SUC (2 * m - 1))’ by gs[]
         >> pop_assum $ rewrite_tac o single
         >> gs[FACT]
       )
      >> pop_assum $ rewrite_tac o single
      >> ‘ &FACT (2 * m - 1) = &(2 * m - 1) * &FACT (2 * PRE m)’ by
        ( ‘(2 * m - 1)  = SUC (2 * PRE m)’ by gs[]
          >> pop_assum $ rewrite_tac o single
          >> gs[FACT]
        )
      >> gs[]
    )
  >> ‘((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&m)⁻¹ * &FACT (2 * m) *
       -1 pow 1 * 2² ⁻¹) =
      &FACT (2 * PRE m) *
      ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&m)⁻¹ * &(2 * m) *
       &(2 * m - 1) *  -1 pow 1 * 2² ⁻¹)’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx. (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ * &FACT (2 * PRE m))  =
      (λx. &FACT (2 * PRE m) *( (\x.
                   (exp (ln (1 + x) * &(2 * PRE m + 1) / 2))⁻¹ ) x)) ’
    by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘ &(2 * m)  = &2 * &m ’ by   gs[GSYM REAL_OF_NUM_MUL]
  >> ‘ ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&m)⁻¹ * &(2 * m) *
        &(2 * m - 1) * -1 pow 1 * 2² ⁻¹) =
      ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * ((&m)⁻¹ * &m) * &2 *
       &(2 * m - 1) * -1 pow 1 * 2² ⁻¹)’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> gs[]
  >> pop_assum $ kall_tac
  >> gs[sqrt_mth_derivative]
QED

Theorem MCLAURTIN_SQRT_LE:
  ! x n. 0 < x ==>
         ?t. (0 < t ∧ t ≤ x) /\
             (\n.  exp ((\x. (ln (1+x)) / &2) x) =  sum (0,n)
            (λm.
                 (λm x.
                      if m = 0 then  exp ((\x. (ln (1+x)) / &2) x)
                      else
                        -1 pow (m - 1) * &FACT (2 * PRE m) *
                        (exp ((\x. &(2 * PRE m + 1) * (ln (1+x)) / &2) x))⁻¹
                 * (2 pow m)⁻¹ *
                        (2 pow (m - 1))⁻¹ * (&FACT (m - 1))⁻¹) m 0 /
                 &FACT m * x pow m) +
          (λm x.
               if m = 0 then  exp ((\x. (ln (1+x)) / &2) x)
               else
                 -1 pow (m - 1) * &FACT (2 * PRE m) *
                 (exp ((\x. &(2 * PRE m + 1) * (ln (1+x)) / &2) x))⁻¹
          * (2 pow m)⁻¹ *
                 (2 pow (m - 1))⁻¹ * (&FACT (m - 1))⁻¹) n t / &FACT n *
          x pow n)  n
Proof
  rpt strip_tac
  >> assume_tac MCLAURIN
  >> pop_assum $ qspec_then ‘(\x. exp ((\x. (ln (1+x)) / &2) x))’ assume_tac
  >> pop_assum $ qspec_then ‘ \m x.
                                if m = 0 then  exp ((\x. (ln (1+x)) / &2) x)
                                else
                                  -1 pow (m - 1) * &FACT (2 * PRE m) *
                            (exp ((\x. &(2 * PRE m + 1) * (ln (1+x)) / &2) x))⁻¹
                            * (2 pow m)⁻¹ *
                            (2 pow (m - 1))⁻¹ * (&FACT (m - 1))⁻¹’
              assume_tac
  >> pop_assum $ qspecl_then [‘x’, ‘n’] assume_tac
  >> ‘n= 0:num \/ (0<n) ’ by gs[]
  >- ( gs[sum] >> qexists_tac ‘x’ >> gs[FACT] )
  >> gs[]
  >> ‘(!m t.
           m < n /\ 0 <= t /\ t <= x ==>
           ((λx'.
                 if m = 0 then exp (ln (1 + x') / 2)
                 else
                   (exp (ln (1 + x') * &(2 * PRE m + 1) / 2))⁻¹ *
                   &FACT (2 * PRE m) * (&FACT (m - 1))⁻¹ * -1 pow (m - 1) *
                   (2 pow m)⁻¹ * (2 pow (m - 1))⁻¹) diffl
            ((exp (ln (1 + t) * &(2 * m + 1) / 2))⁻¹ * (&FACT m)⁻¹ *
             &FACT (2 * m) * -1 pow m * (2 pow m)⁻¹ * (2 pow SUC m)⁻¹)) t)’ by
    ( rpt strip_tac
      >> Cases_on ‘m=0’
      >- ( gs[FACT]
           >> ‘ (1 / 2 * (exp (ln (1 + t) / 2))⁻¹) =
                (exp ((\x. (ln (1+x)) / &2) t) * (inv (1+t) / &2)) ’ by
             ( gs[] >> DISJ2_TAC
               >> gs[GSYM EXP_N]
               >> ‘exp (ln (1 + t)) = (1+t)’ by
                 ( gs[EXP_LN] >> ‘&1 + t = t + &1’ by REAL_ARITH_TAC
                   >> pop_assum $ rewrite_tac o single
                   >> gs[REAL_LET_ADD]
                 )
               >> pop_assum $ rewrite_tac o single
               >> ‘(1 + t) * (1 + t)⁻¹ =  (1 + t)⁻¹ * (1 + t)’ by REAL_ARITH_TAC
               >> pop_assum $ rewrite_tac o single
               >> irule REAL_MUL_LINV
               >> ‘&0 < 1 + t ==> 1 + t <> &0’ by REAL_ARITH_TAC
               >> first_x_assum irule
               >> ‘&1 + t = t + &1’ by REAL_ARITH_TAC
               >> pop_assum $ rewrite_tac o single
               >> gs[REAL_LET_ADD]
             )
           >> pop_assum $ rewrite_tac o single
           >> ‘(λx'. exp (ln (1 + x') / 2)) =
               (λx'. exp ((λx. ln (1 + x) / 2) x'))’ by gs[FUN_EQ_THM]
           >> pop_assum $ rewrite_tac o single
           >> gs[SQRT_EXPLN_DIFF]
         )
      >> gs[SQRT_DIFF_m_not_0]
    )
  >> res_tac
  >> qexists_tac ‘t’
  >> rpt conj_tac
  >- gs[]
  >- gs[REAL_LT_IMP_LE]
  >> gs[]
QED



(** Mclaurin approximation for tangent function. The idea is to
    to write tan x = sin x / cos x. We know the series
    expansion of sin. We need to figure out series expansion of
    inverse function. and then multiply the two series expansion
 **)

(* McLaurin series for the inverse function : 1/ (1-x) *)
Theorem EXP_inv_intermed:
  0 ≤ t ∧ t < 1 ⇒
   ((λx'. exp (-ln (1 − x'))) diffl (exp (-2 * ln (1 − t)) * &FACT 1)) t
Proof
  rpt strip_tac
  >> ‘(exp (-2 * ln (1 - t)) * &FACT 1) =  exp (-2 * ln (1 - t))’
    by ( gs[FACT] >> DISJ2_TAC >> EVAL_TAC)
  >> pop_assum $ rewrite_tac o single
  >> ‘exp (-2 * ln (1 - t)) =
      exp ((\x. -(ln (1-x))) t) * ( exp (- ln (1-t)))’ by
    ( gs[]
      >> ‘-2 * ln (1 - t) = &2 * (-ln(1-t))’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> gs[EXP_N]
    )
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx. exp (-ln (1 - x))) = (\x. exp ((\x. -(ln (1-x))) x))’ by
    gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> irule DIFF_COMPOSITE_EXP
  >> ‘exp (-ln (1 - t)) = inv (1-t)’ by
    ( ‘ ln (inv (1-t)) = - ln(1-t)’ by
       ( irule LN_INV
         >> ‘0+t < 1 ==> 0 < 1 - t’ by gs[REAL_LT_ADD_SUB]
         >> first_assum irule
         >> gs[]
       )
      >> ‘-ln (1 - t) = ln (1 - t)⁻¹ ’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> gs[EXP_LN]
      >> ‘0+t < 1 ==> 0 < 1 - t’ by gs[REAL_LT_ADD_SUB]
      >> first_assum irule
      >> gs[]
    )
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx. -ln (1 - x)) = (λx. (-1) * ((\x. ln (1 - x)) x))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘(1 - t)⁻¹ = (-1) * (-(1 - t)⁻¹)’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘(λx. ln (1 - x)) = (λx. ln ((\x. (1 - x)) x))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘-(1 - t)⁻¹ = (((\x . (1 - x)) t)⁻¹) * -1 ’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> irule DIFF_LN_COMPOSITE
  >> conj_tac
  >- ( gs[]  >> ‘0+t < 1 ==> 0 < 1 - t’ by gs[REAL_LT_ADD_SUB]
       >> first_assum irule
       >> gs[]
     )
  >> gs[diff_chain_sub]
QED

Theorem EXP_inv_intermed_m_neq_0:
  m ≠ 0 ∧ 0 ≤ t ∧ t < 1 ⇒
   ((λx'. exp (-ln (1 - x') * &SUC m) * &FACT m) diffl
    (exp (-ln (1 - t) * &SUC (SUC m)) * &FACT (SUC m))) t
Proof
  rpt strip_tac
  >> ‘(λx'. exp (-ln (1 - x') * &SUC m) * &FACT m) =
      (λx'.  &FACT m * ((\x. exp (-ln (1 - x) * &SUC m)) x'))’ by
    gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘(exp (-ln (1 - t) * &SUC (SUC m)) * &FACT (SUC m)) =
      &FACT m * (exp (-ln (1 - t) * &SUC (SUC m)) * &(SUC m))’ by
    (  ‘&FACT (SUC m) = &(SUC m) *  &FACT m’ by gs[FACT]
       >> gs[]
    )
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘exp (-ln (1 - t) * &SUC (SUC m)) =
      exp (-ln (1 - t) * &SUC m) * exp (-ln (1-t))’ by (
    ‘exp (-ln (1 - t)) = exp (-ln (1 - t) * &1)’ by gs[]
    >> pop_assum $ rewrite_tac o single
    >> ‘ exp (-ln (1 - t) * &SUC m) * exp (-ln (1 - t) * 1) =
         exp ((-ln (1 - t) * &SUC m) + (-ln (1 - t) * 1))’
      by gs[transcTheory.EXP_ADD]
    >> pop_assum $ rewrite_tac o single
    >> ‘(-ln (1 - t) * &SUC (SUC m)) =
        (-ln (1 - t) * &SUC m + -ln (1 - t) * 1) ’ by (
      ‘(-ln (1 - t) * &SUC m + -ln (1 - t) * 1) =
       (-ln (1 - t) * (&SUC m + 1))’
         by gs[GSYM REAL_LDISTRIB]
      >> pop_assum $ rewrite_tac o single
      >> ‘&(SUC (SUC m)) = &SUC m + 1’ suffices_by gs[]
      >> gs[integerTheory.INT])
    >> pop_assum $ rewrite_tac o single)
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx. exp (-ln (1 - x) * &SUC m)) =
      (λx. exp ((\x. (-ln (1 - x) * &SUC m)) x))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘exp (-ln (1 - t) * &SUC m) = exp ((λx. -ln (1 - x) * &SUC m) t)’
    by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘(exp ((λx. -ln (1 - x) * &SUC m) t) * exp (-ln (1 - t)) * &SUC m) =
      (exp ((λx. -ln (1 - x) * &SUC m) t) * (exp (-ln (1 - t)) * &SUC m))’ by
    gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule DIFF_COMPOSITE_EXP
  >> ‘(λx. -ln (1 - x) * &SUC m) = (λx. &SUC m * ((\x. -ln (1 - x)) x))’ by
    gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘(exp (-ln (1 - t)) * &SUC m) = &(SUC m) * exp (-ln (1 - t))’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘exp (-ln (1 - t)) = inv (1-t)’ by
    ( ‘ ln (inv (1-t)) = - ln(1-t)’ by
       ( irule LN_INV
         >> ‘0+t < 1 ==> 0 < 1 - t’ by gs[REAL_LT_ADD_SUB]
         >> first_assum irule
         >> gs[]
       )
      >> ‘-ln (1 - t) = ln (1 - t)⁻¹ ’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> gs[EXP_LN]
      >> ‘0+t < 1 ==> 0 < 1 - t’ by gs[REAL_LT_ADD_SUB]
      >> first_assum irule
      >> gs[]
    )
  >> pop_assum $ rewrite_tac o single
  >> ‘(λx. -ln (1 - x)) = (λx. (-1) * ((\x. ln (1 - x)) x))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘(1 - t)⁻¹ = (-1) * (-(1 - t)⁻¹)’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> irule limTheory.DIFF_CMUL
  >> ‘(λx. ln (1 - x)) = (λx. ln ((\x. (1 - x)) x))’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> ‘-(1 - t)⁻¹ = (((\x . (1 - x)) t)⁻¹) * -1 ’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> irule DIFF_LN_COMPOSITE
  >> conj_tac
  >- ( gs[]  >> ‘0+t < 1 ==> 0 < 1 - t’ by gs[REAL_LT_ADD_SUB]
       >> first_assum irule
       >> gs[]
     )
  >> gs[diff_chain_sub]
QED

Theorem MCLAURIN_INV:
  ∀ x n.
    0 < x ∧ x < 1 ⇒
    ∃ t.
      0 < t ∧ t ≤ x ∧
      (λ n.
         exp ((λ x. -(ln (1 - x))) x) =
         sum (0,n) (λm.
                      inv (&FACT m) * x pow m *
                      if m = 0 then exp (-ln 1)
                      else exp (-ln 1 * &SUC m) * &FACT m) +
         inv (&FACT n) * x pow n *
         (if n = 0 then exp (-ln (1 - t))
          else exp (-ln (1 - t) * &SUC n) * &FACT n))  n
Proof
  rpt strip_tac
  >> assume_tac MCLAURIN
  >> pop_assum $ qspec_then ‘(\x. exp ((\x. -(ln (1-x))) x))’
               assume_tac
  >> pop_assum $ qspec_then ‘ \m x.
                                if m = 0 then exp ((\x. -(ln (1-x))) x)
                                else
                                   &(FACT m) *
                                  (exp ((\x. - &(SUC m) * ln(1-x) ) x))’
               assume_tac
  >> pop_assum $ qspecl_then [‘x’, ‘n’] assume_tac
  >> ‘n= 0:num \/ (0<n) ’ by gs[]
  >- ( gs[sum] >> qexists_tac ‘x’ >> gs[FACT] )
  >> gs[]
  >> ‘ (!m t.
           m < n /\ 0 <= t /\ t <= x ==>
           ((λx'.
               if m = 0 then exp (-ln (1 - x'))
                 else exp (-ln (1 - x') * &SUC m) * &FACT m) diffl
            (exp (-ln (1 - t) * &SUC (SUC m)) * &FACT (SUC m))) t)’ by
    ( rpt strip_tac
      >> Cases_on ‘m=0’
      >- ( gs[]
           >> ‘ t < 1 ’ by
             ( UNDISCH_TAC “x:real < &1” >> UNDISCH_TAC “t:real <= x”
               >> REAL_ARITH_TAC
             )
           >> gs[EXP_inv_intermed]
         )
      >> gs[]
      >> ‘ t < 1 ’ by
        ( UNDISCH_TAC “x:real < &1” >> UNDISCH_TAC “t:real <= x”
          >> REAL_ARITH_TAC
        )
      >> gs[EXP_inv_intermed_m_neq_0]
    )
  >> res_tac
  >> qexists_tac ‘t’
  >> rpt conj_tac
  >- gs[]
  >- ( UNDISCH_TAC “t < (x:real)” >> REAL_ARITH_TAC )
  >> gs[]
QED

Theorem  MCLAURIN_COS_INV:
  ∀ x n.
    0 < x ∧ x < (pi / &2) ⇒
    ∃ t.
      0 < t ∧ t ≤ x ∧
      inv (cos x) =
      sum (0,n)
          (λm.
             inv (&FACT m) * (1-cos x) pow m *
             if m = 0 then exp (-ln 1)
             else exp (-ln 1 * &SUC m) * &FACT m) +
      inv (&FACT n) * (1 - cos x) pow n *
      (if n = 0 then (inv (cos t))
       else (inv(cos t) pow  &SUC n) * &FACT n)
Proof
  rpt strip_tac
  >> assume_tac MCLAURIN_INV
  >> pop_assum $ qspecl_then [‘1- cos x’, ‘n’] assume_tac
  >> ‘ 0 < 1 - cos x /\ 1 - cos x < 1’ by
    ( conj_tac
      >- ( ‘cos x < 1 ==> 0 < 1 - cos x’ by REAL_ARITH_TAC
           >> first_assum irule
           >> gs[cos_lt_1]
         )
      >> ‘0 < cos x ==>  1 - cos x < 1’ by REAL_ARITH_TAC
      >> first_assum irule
      >> irule COS_POS_PI
      >> gs[] >> irule REAL_LT_TRANS >> qexists_tac ‘0’
      >> gs[PI_POS]
    )
  >> res_tac
  >> qexists_tac ‘acs (1-t)’
  >> rpt conj_tac
  >- ( assume_tac ACS_BOUNDS_LT
       >> pop_assum $ qspec_then ‘1-t’ assume_tac
       >> ‘-1 < 1 - t /\ 1 - t < 1’ by
         ( conj_tac
           >- ( ‘t < &2 ==> -1 < 1 - t’ by REAL_ARITH_TAC
                >> first_assum irule
                >> irule REAL_LET_TRANS
                >> qexists_tac ‘1 - cos x’
                >> conj_tac
                >- ( ‘- 1 < cos x ==> 1 - cos x < 2’ by REAL_ARITH_TAC
                     >> first_assum irule
                     >> irule REAL_LT_TRANS
                     >> qexists_tac ‘0:real’
                     >> conj_tac
                     >- gs[]
                     >> gs[COS_POS_PI2]
                   )
                >> gs[]
              )
           >> UNDISCH_TAC “(0:real) < t” >> REAL_ARITH_TAC
         )
       >> gs[]
     )
  >- ( irule cos_decreasing
       >> rpt conj_tac
       >- ( irule REAL_LT_TRANS
            >> qexists_tac ‘pi / &2’
            >> conj_tac
            >- gs[]
            >> gs[PI2_lt_PI] )
       >- ( assume_tac ACS_BOUNDS_LT
            >> pop_assum $ qspec_then ‘1-t’ assume_tac
            >> ‘-1 < 1 - t /\ 1 - t < 1’ by
              ( conj_tac
                >- ( ‘t < &2 ==> -1 < 1 - t’ by REAL_ARITH_TAC
                     >> first_assum irule
                     >> irule REAL_LET_TRANS
                     >> qexists_tac ‘1 - cos x’
                     >> conj_tac
                     >- ( ‘- 1 < cos x ==> 1 - cos x < 2’ by REAL_ARITH_TAC
                          >> first_assum irule
                          >> irule REAL_LT_TRANS
                          >> qexists_tac ‘0:real’
                          >> conj_tac
                          >- gs[]
                          >> gs[COS_POS_PI2]
                        )
                     >> gs[]
                   )
                >> UNDISCH_TAC “(0:real) < t” >> REAL_ARITH_TAC
              )
            >> gs[] )
       >- gs[]
       >- (
         assume_tac ACS_BOUNDS_LT
         >> pop_assum $ qspec_then ‘1-t’ assume_tac
         >> ‘-1 < 1 - t /\ 1 - t < 1’ by
           ( conj_tac
             >- ( ‘t < &2 ==> -1 < 1 - t’ by REAL_ARITH_TAC
                  >> first_assum irule
                  >> irule REAL_LET_TRANS
                  >> qexists_tac ‘1 - cos x’
                  >> conj_tac
                  >- ( ‘- 1 < cos x ==> 1 - cos x < 2’ by REAL_ARITH_TAC
                       >> first_assum irule
                       >> irule REAL_LT_TRANS
                       >> qexists_tac ‘0:real’
                       >> conj_tac
                       >- gs[]
                       >> gs[COS_POS_PI2])
                >> gs[] )
           >> UNDISCH_TAC “(0:real) < t” >> REAL_ARITH_TAC )
       >> gs[] )
       >> ‘(cos (acs (1 - t))) = 1-t’ by
         ( irule ACS_COS
           >> conj_tac
           >- ( ‘0 <= t ==> 1 - t <= 1’ by REAL_ARITH_TAC
                >> first_assum irule
                >> UNDISCH_TAC “(0:real) < t”
                >> REAL_ARITH_TAC
              )
           >> ‘t <= 2 ==> -1 <= 1 - t’ by REAL_ARITH_TAC
           >> first_assum irule
           >> irule REAL_LE_TRANS
           >> qexists_tac ‘1 - cos x’
           >> conj_tac
           >- gs[]
           >> irule REAL_LT_IMP_LE
           >>‘- 1 < cos x ==> 1 - cos x < 2’ by REAL_ARITH_TAC
           >> first_assum irule
           >> irule REAL_LT_TRANS
           >> qexists_tac ‘0:real’
           >> conj_tac
           >- gs[]
           >> gs[COS_POS_PI2]
         )
       >> pop_assum $ rewrite_tac o single
       >> UNDISCH_TAC “t <= 1 - cos x”
       >> REAL_ARITH_TAC )
  >> pop_assum kall_tac
  >> pop_assum kall_tac
  >> pop_assum kall_tac
  >> ‘(cos x)⁻¹ = exp ((λx. -ln (1 - x)) (1 - cos x))’ by
    ( ‘(λx. -ln (1 - x)) (1 - cos x) = -ln (cos x)’ by
       ( ‘ (λx. -ln (1 - x)) (1 - cos x) =  -ln (1 - (1 - cos x))’ by gs[]
         >> pop_assum $ rewrite_tac o single
         >> ‘(1 - (1 - cos x)) = cos x’ by REAL_ARITH_TAC
         >> gs[]
       )
      >> pop_assum $ rewrite_tac o single
      >> ‘ln (inv (cos x)) = -ln(cos x)’ by
        ( irule LN_INV >> irule COS_POS_PI
          >> gs[] >> irule REAL_LT_TRANS >> qexists_tac ‘0’
          >> gs[PI_POS]
        )
      >> ‘-ln (cos x) = ln (inv (cos x))’ by gs[]
      >> pop_assum $ rewrite_tac o single
      >> ‘exp (ln (cos x)⁻¹) = (cos x)⁻¹’ by
        ( gs[EXP_LN]
          >> irule COS_POS_PI
          >> gs[] >> irule REAL_LT_TRANS >> qexists_tac ‘0’
          >> gs[PI_POS]
        )
      >> gs[]
    )
  >> pop_assum $ rewrite_tac o single
  >>‘(cos (acs (1 - t))) = 1-t’ by
    ( irule ACS_COS
      >> conj_tac
      >- ( ‘0 <= t ==> 1 - t <= 1’ by REAL_ARITH_TAC
           >> first_assum irule
           >> UNDISCH_TAC “(0:real) < t”
           >> REAL_ARITH_TAC
         )
      >> ‘t <= 2 ==> -1 <= 1 - t’ by REAL_ARITH_TAC
      >> first_assum irule
      >> irule REAL_LE_TRANS
      >> qexists_tac ‘1 - cos x’
      >> conj_tac
      >- gs[]
      >> irule REAL_LT_IMP_LE
      >>‘- 1 < cos x ==> 1 - cos x < 2’ by REAL_ARITH_TAC
      >> first_assum irule
      >> irule REAL_LT_TRANS
      >> qexists_tac ‘0:real’
      >> conj_tac
      >- gs[]
      >> gs[COS_POS_PI2]
    )
  >> pop_assum $ rewrite_tac o single
  >> ‘(1 - t)⁻¹ = exp (-ln (1 - t))’ by
    (‘ ln (inv (1-t)) = - ln(1-t)’ by
       ( irule LN_INV
         >> ‘0+t < 1 ==> 0 < 1 - t’ by gs[REAL_LT_ADD_SUB]
         >> first_assum irule
         >> ‘0 + t = t ’ by REAL_ARITH_TAC
         >> pop_assum $ rewrite_tac o single
         >> irule REAL_LET_TRANS
         >> qexists_tac ‘1 - cos x’
         >> conj_tac
         >- gs[]
         >> gs[]
       )
     >> ‘-ln (1 - t) = ln (1 - t)⁻¹ ’ by gs[]
     >> pop_assum $ rewrite_tac o single
     >> ‘ exp (ln (1 - t)⁻¹) = (1 - t)⁻¹’ by
       ( rewrite_tac[EXP_LN]
         >> ‘0 < 1 - t ’ by
           ( ‘0 + t < 1 ==> 0 < 1 - t ’ by REAL_ARITH_TAC
             >> first_assum irule
             >> ‘0 + t = t’ by REAL_ARITH_TAC
             >> pop_assum $ rewrite_tac o single
             >> irule REAL_LET_TRANS
             >> qexists_tac ‘1 - cos x’
             >> conj_tac
             >- gs[]
             >> gs[]
           )
         >> gs[]
       )
     >> gs[]
    )
  >> pop_assum $ rewrite_tac o single
  >> gs[GSYM EXP_N]
QED

(** McLaurin Series for atan x **)
Theorem REAL_ATN_POWSER_SUMMABLE:
 ∀ x. abs(x) < &1 ⇒
      summable (λ n.
                  (if EVEN n then &0
                   else -(&1) pow ((n - 1) DIV 2) / &n) * x pow n)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC seqTheory.SER_COMPAR THEN
  EXISTS_TAC “\n. abs(x) pow n” THEN CONJ_TAC
  >- ( EXISTS_TAC “0:num” THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
       gs[] >> COND_CASES_TAC
       >- gs[REAL_ABS_POS]
       >> ‘ODD (n)’ by gs[ODD_EVEN]
       >> ‘∃p. (n) = SUC (2 * p)’ by gs[ODD_EXISTS]
       >> pop_assum $ rewrite_tac o single
       >> gs[GSYM DIV2_def, ABS_MUL, ABS_DIV, GSYM POW_ABS]
       >> ‘(abs x pow SUC (2 * p)) = 1 * (abs x pow SUC (2 * p))’ by gs[]
       >> pop_assum $ once_rewrite_tac o single
       >> ‘ &SUC (2 * p) * (1 * abs x pow SUC (2 * p)) =
            &SUC (2 * p) * abs x pow SUC (2 * p)’ by gs[]
       >> pop_assum $ rewrite_tac o single
       >> irule REAL_LE_MUL2
       >> rpt conj_tac >> gs[]
     )
  >> REWRITE_TAC[seqTheory.summable]
  >> EXISTS_TAC “inv(&1 - abs x)”
  >> MATCH_MP_TAC seqTheory.GP
  >> ASM_REWRITE_TAC[ABS_ABS]
QED

Theorem REAL_ATN_POWSER_SUMMABLE :
  ∀ x.
    abs(x) < &1 ⇒
    summable (λ n. (if EVEN n then &0
                   else -(&1) pow ((n - 1) DIV 2) / &n) * x pow n)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC seqTheory.SER_COMPAR THEN
  EXISTS_TAC “\n. abs(x) pow n” THEN CONJ_TAC
  >- ( EXISTS_TAC “0:num” THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN gs[]
       >>  COND_CASES_TAC
       >-  gs[]
       >> gs[] >> gs[REAL_ABS_MUL]
       >> ‘abs x pow n = &1 * abs x pow n’ by gs[]
       >> pop_assum $ once_rewrite_tac o single
       >> irule REAL_LE_MUL2
       >> rpt conj_tac
       >- ( ‘ abs (&n)⁻¹ = ( abs &n)⁻¹’ by gs[ABS_INV]
            >> pop_assum $ rewrite_tac o single
            >> irule REAL_INV_LE_1 >> gs[]
            >> ‘ODD n’ by gs[EVEN_ODD]
            >> ‘∃m. n = SUC (2 * m)’ by gs[ODD_EXISTS]
            >> pop_assum $ rewrite_tac o single
            >> gs[]
          )
       >- gs[POW_ABS]
       >- gs[]
       >> gs[]
     )
  >> REWRITE_TAC[seqTheory.summable] >> EXISTS_TAC “inv(&1 - abs x)”
  >> MATCH_MP_TAC seqTheory.GP >> gs[]
QED

Theorem REAL_ATN_POWSER_DIFFS_SUMMABLE:
  ∀ x.
    abs(x) < &1 ⇒
    summable (λ n. diffs (λ n. (if EVEN n then &0
                                else -(&1) pow ((n - 1) DIV 2) / &n)) n *
                   x pow n)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[powserTheory.diffs] THEN
  MATCH_MP_TAC seqTheory.SER_COMPAR THEN
  EXISTS_TAC “\n. abs(x) pow n” THEN CONJ_TAC
  >- ( EXISTS_TAC “0:num” THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN gs[]
       >>  COND_CASES_TAC
       >- gs[]
       >> gs[] >> gs[REAL_ABS_MUL, GSYM POW_ABS]
     )
  >> REWRITE_TAC[seqTheory.summable] THEN EXISTS_TAC “inv(&1 - abs x)” THEN
  MATCH_MP_TAC seqTheory.GP THEN  gs[]
QED

Theorem REAL_ATN_POWSER_DIFFS_SUM:
  ∀ x.
    abs(x) < &1 ⇒
    (λ n. diffs
          (λ n. (if EVEN n then &0 else -(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)
    sums (inv(&1 + x pow 2))
Proof
  rpt strip_tac
  >> first_assum $ mp_then Any mp_tac REAL_ATN_POWSER_DIFFS_SUMMABLE
  >> disch_then $ (fn th =>
                     mp_then Any mp_tac seqTheory.SUMMABLE_SUM th
                   >> mp_then Any mp_tac seqTheory.SER_PAIR th)
  >> ‘(λ n. sum (2 * n,2)
                (λ n. diffs
                      (λ n. (if EVEN n then &0
                             else -(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)) =
      (λ n. -(x pow 2) pow n)’
     by (
      ABS_TAC
      >> gs[CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV sum, powserTheory.diffs, ADD_CLAUSES, EVEN_MULT, EVEN]
      >> ‘~ EVEN (2 * n + 1)’
        by (gs[GSYM ODD_EVEN, ODD_EXISTS] >> qexists_tac ‘n’ >> gs[])
      >> gs[GSYM REAL_POW_POW]
      >> ‘((2 * n) DIV 2) = n’
        by (‘2 * n = n * 2’ by gs[] >> pop_assum $ rewrite_tac o single >> irule MULT_DIV >> gs[])
      >> pop_assum $ rewrite_tac o single
      >> gs[GSYM POW_MUL])
  >> pop_assum $ rewrite_tac o single
  >> ‘(λ n. - (x pow 2) pow n) sums inv (&1 + x pow 2)’
    by (
    once_rewrite_tac [REAL_ARITH “&1 + x:real = &1 - (- x)”]
    >> irule seqTheory.GP
    >> rewrite_tac[ABS_NEG, ABS_MUL, POW_2]
    >> ‘1:real = 1 * 1’ by real_tac
    >> pop_assum $ once_rewrite_tac o single
    >> irule REAL_LT_MUL2
    >> gs[ABS_POS])
  >> pop_assum mp_tac
  >> mesonLib.MESON_TAC [seqTheory.SUM_UNIQ]
QED

Theorem REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE:
  ∀ x.
    abs(x) < &1 ⇒
    summable (λ n. diffs (diffs
                          (λ n. (if EVEN n then &0
                                 else -(&1) pow ((n - 1) DIV 2) / &n))) n * x pow n)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[powserTheory.diffs] THEN
  MATCH_MP_TAC seqTheory.SER_COMPAR THEN
  EXISTS_TAC “\n. &(SUC n) * abs(x) pow n” THEN CONJ_TAC
  >- ( EXISTS_TAC “0:num” THEN REPEAT STRIP_TAC THEN gs[]
       >> REWRITE_TAC[ABS_N, REAL_ABS_MUL, GSYM REAL_MUL_ASSOC] THEN
       ‘&SUC n * abs x pow n = abs x pow n *  &SUC n ’ by gs[]
       >> pop_assum $ rewrite_tac o single
       >> gs[POW_ABS]
       >> ‘ abs (x pow n) *
            abs
          (if EVEN (SUC (SUC n)) then 0
           else -1 pow (SUC n DIV 2) / &SUC (SUC n)) * &(SUC n * SUC (SUC n)) =
            abs (x pow n) *
          (  abs
          (if EVEN (SUC (SUC n)) then 0
           else -1 pow (SUC n DIV 2) / &SUC (SUC n)) * &(SUC n * SUC (SUC n)))’ by
         gs[]
       >> pop_assum $ rewrite_tac o single
       >> irule  REAL_LE_LMUL1
       >> conj_tac
       >- ( gs[]
            >> COND_CASES_TAC
            >- gs[]
            >> gs[ABS_DIV] >> gs[]
          )
       >> gs[]
     )
  >> MATCH_MP_TAC seqTheory.SER_RATIO THEN
  SUBGOAL_THEN “?c. abs(x) < c /\ c < &1” STRIP_ASSUME_TAC
  >- ( EXISTS_TAC “(&1 + abs(x)) / &2”
       >> gs[] >> UNDISCH_TAC “abs(x) < &1” >> REAL_ARITH_TAC
     )
  >> EXISTS_TAC “c:real” THEN ASM_REWRITE_TAC[]
  >> ‘?N. !n. n >= N ==> &(SUC(SUC n)) * abs(x) <= &(SUC n) * c’ by
    ( ASM_CASES_TAC  “x : real= &0”
      >- ( ASM_REWRITE_TAC[ABS_N, REAL_MUL_RZERO] THEN
           EXISTS_TAC “0:num” THEN REPEAT STRIP_TAC THEN
           MATCH_MP_TAC REAL_LE_MUL THEN
           REWRITE_TAC[REAL_POS] THEN
           UNDISCH_TAC “abs(x) < c” THEN REAL_ARITH_TAC
         )
      >> ‘?N. &1 <= &N * (c / abs x - &1)’ by
        ( assume_tac SIMP_REAL_ARCH
          >> pop_assum $ qspec_then ‘&1 / (c / abs x − 1)’ assume_tac
          >> pop_assum mp_tac
          >> rpt strip_tac
          >> qexists_tac ‘n:num’
          >> assume_tac REAL_LE_LDIV_EQ
          >> pop_assum $ qspecl_then [‘&1’, ‘&n’, ‘(c / abs x − 1)’] assume_tac
          >> ‘0 < c / abs x − 1’ by
            (  ‘ 0 < abs x’ by gs[GSYM ABS_NZ]
               >> ‘&1 < c / abs x ⇒  0 < c / abs x − 1 ’ by REAL_ARITH_TAC
               >> first_assum irule
               >> assume_tac REAL_LT_RDIV_EQ
               >> pop_assum $ qspecl_then [‘&1’, ‘c’, ‘abs x’] assume_tac
               >> res_tac
               >> first_assum irule
               >> gs[]
            )
          >> res_tac
        )
      >> qexists_tac ‘N:num’ >> rpt strip_tac
      >> gs[GSYM REAL_OF_NUM_SUC]
      >> once_rewrite_tac[GSYM REAL_OF_NUM_ADD]
      >> gs[REAL_ADD_LDISTRIB]
      >> irule REAL_LE_ADD2
      >> conj_tac
      >- ( gs[GSYM REAL_OF_NUM_SUC]
           >> once_rewrite_tac[GSYM REAL_OF_NUM_ADD]
           >> ‘ abs x * (&n + 1) =  (&n + 1) *  abs x ’ by gs[]
           >> pop_assum $ rewrite_tac o single
           >> assume_tac REAL_LE_RDIV_EQ
           >> pop_assum $ qspecl_then [‘(&n + 1)’, ‘c * &n’, ‘abs x’] assume_tac
           >> ‘  0 < abs x’ by gs[GSYM ABS_NZ]
           >> res_tac
           >> pop_assum kall_tac
           >> first_assum irule
           >> ‘c * &n / abs x = &n * (c / abs x)’ by gs[]
           >> pop_assum $ rewrite_tac o single
           >> ‘1 ≤ &n * ((c / abs x) - &1) ⇒ &n + 1 ≤ &n * (c / abs x)’ by
             REAL_ARITH_TAC
           >> first_assum irule
           >> irule REAL_LE_TRANS
           >> qexists_tac ‘&N * (c / abs x − 1)’
           >> conj_tac
           >- gs[]
           >> ‘&N * (c / abs x − 1) = (c / abs x − 1) *  &N ’ by gs[]
           >> pop_assum $ rewrite_tac o single
           >> ‘&n * (c / abs x − 1) = (c / abs x − 1) *  &n’ by gs[]
           >> pop_assum $ rewrite_tac o single
           >> irule REAL_LE_LMUL_IMP
           >> conj_tac
           >- gs[REAL_LE]
           >> ‘&1 ≤ c / abs x ⇒   0 ≤ c / abs x − 1 ’ by  REAL_ARITH_TAC
           >> first_assum irule
           >> irule REAL_LE_RDIV
           >> gs[REAL_LT_IMP_LE]
         )
      >> gs[REAL_LT_IMP_LE]
    )
  >> qexists_tac ‘N:num’
  >> rpt strip_tac
  >> gs[pow, REAL_ABS_MUL]
  >> ‘abs x * abs (abs x pow n) * &SUC (SUC n) =
      (abs x * &SUC (SUC n)) *  abs x pow n’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> ‘ c * abs (abs x pow n) * &SUC n  =
       (c * &SUC n) * (abs x pow n)  ’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_LE_MUL2
  >> rpt conj_tac
  >- gs[]
  >- gs[]
  >- ( irule REAL_LE_MUL >> gs[] )
  >> gs[]
QED

Theorem REAL_ATN_POWSER_DIFFL:
  ∀ x.
    abs(x) < &1 ⇒
    ((λ x. suminf (λ n. (if EVEN n then &0
                         else -(&1) pow ((n - 1) DIV 2) / &n) * x pow n))
     diffl (inv(&1 + x pow 2))) x
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER_DIFFS_SUM) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP seqTheory.SUM_UNIQ) THEN
  ‘(λx. suminf
                (λn.
                     (if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n) *
                     x pow n)) =
   (λx.  suminf
                (λn.
                    ( (\m. (if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n)) n) *
                    x pow n)) ’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> assume_tac  powserTheory.TERMDIFF
  >> SUBGOAL_THEN “?K. abs(x) < abs(K) /\ abs(K) < &1” STRIP_ASSUME_TAC
  >- ( EXISTS_TAC “(&1 + abs(x)) / &2” THEN
       gs[REAL_LT_LDIV_EQ, ABS_DIV, ABS_N,
          REAL_LT_RDIV_EQ, REAL_LT]
       >> UNDISCH_TAC “abs(x) < &1” THEN REAL_ARITH_TAC
     )
  >> qpat_x_assum ‘∀c k' x. _’ $ qspecl_then [‘(λn. if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n)’,
                                              ‘K'’, ‘x’] assume_tac
  >> ‘summable
          (λn.
               (λn. if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n) n *
               K' pow n) ∧
        summable
          (λn.
               diffs (λn. if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n)
                 n * K' pow n) ∧
        summable
          (λn.
               diffs
                 (diffs
                    (λn. if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n))
                 n * K' pow n) ∧ abs x < abs K'’ by
    ( rpt conj_tac
      >- ( ‘summable
          (λn.
               (λn. if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n) n *
               K' pow n) =
            summable
            (λn. (if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n)  *
                 K' pow n)’ by gs[]
           >> pop_assum $ rewrite_tac o single
           >> gs[ REAL_ATN_POWSER_SUMMABLE]
         )
      >-  gs[REAL_ATN_POWSER_DIFFS_SUMMABLE]
      >- gs[REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE]
      >> gs[]
    )
  >> res_tac
  >> gs[]
QED

Theorem REAL_ATN_POWSER:
  ∀ x.
    abs(x) < &1 ⇒
    (λ n. (if EVEN n then &0
           else -(&1) pow ((n - 1) DIV 2) / &n) * x pow n)
    sums (atn x)
Proof
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP seqTheory.SUMMABLE_SUM) THEN
  SUBGOAL_THEN
   “suminf (\n. (if EVEN n then &0
                 else -(&1) pow ((n - 1) DIV 2) / &n) * x pow n) = atn(x)”
   (fn th =>  REWRITE_TAC[th]) THEN
  ONCE_REWRITE_TAC[REAL_ARITH “(a = b) <=> ((a:real) - (b:real) = &0)”] THEN
  SUBGOAL_THEN
   “suminf (\n. (if EVEN n then &0
                 else -(&1) pow ((n - 1) DIV 2) / &n) * &0 pow n) -
    atn(&0) = &0”
   MP_TAC
  >- ( MATCH_MP_TAC(REAL_ARITH “(a = &0) /\ (b = &0) ==> ((a:real) - (b:real) = &0)”)
       >> CONJ_TAC
       >- ( CONV_TAC SYM_CONV THEN MATCH_MP_TAC seqTheory.SUM_UNIQ THEN
            MP_TAC(SPEC “&0:real” seqTheory.GP) THEN
            gs[ABS_N, REAL_LT] THEN
            DISCH_THEN(MP_TAC o SPEC “&0:real” o MATCH_MP seqTheory.SER_CMUL) THEN
            REWRITE_TAC[REAL_MUL_LZERO] THEN
            MATCH_MP_TAC(tautLib.TAUT `(a = b) ==> a ==> b`) THEN
            AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
            COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
            CONV_TAC SYM_CONV THEN gs[] THEN
            ‘ODD (n)’ by gs[ODD_EVEN]
            >> ‘∃p. (n) = SUC (2 * p)’ by gs[ODD_EXISTS]
            >> pop_assum $ rewrite_tac o single
            >> gs[POW_0]
          )
       >> gs[ATN_0]
     )
  >> ASM_CASES_TAC “x = &0 : real” THEN ASM_REWRITE_TAC[] THEN
  strip_tac
  >> ‘&0 = suminf
          (λn. (if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n) * 0 pow n) −
          atn 0’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> MP_TAC(SPEC “\x. suminf (\n. (if EVEN n then &0
                       else -(&1) pow ((n - 1) DIV 2) / &n) * x pow n) -
          atn x” DIFF_ISCONST_END_SIMPLE) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
    “~(x = &0) ==> &0 < (x:real) \/ (x:real) < &0”))
  >- ( rpt strip_tac
       >> pop_assum $ qspecl_then [‘&0:real’, ‘x: real’] assume_tac
       >> res_tac >> gs[]
       >> first_assum irule
       >> rpt strip_tac >> gs[]
       >> ‘&0 = (inv(&1 + x' pow 2)) - (inv(&1 + x' pow 2))’ by gs[]
       >> ‘  ((λx''.
                 suminf
                 (λn.
                    x'' pow n *
                    if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n) −
                 atn x'') diffl 0) x' =
             ((λx''.
                 ((\x.  suminf
                        (λn.
                           x pow n *
                     if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n)) x'')  −
              ( (\x. atn x) x'')) diffl ( (inv(&1 + x' pow 2)) - (inv(&1 + x' pow 2)))) x'’
         by (pop_assum $ once_rewrite_tac o single >> gs[])
       >> pop_assum $ rewrite_tac o single
       >> irule limTheory.DIFF_SUB
       >> conj_tac
       >- ( ‘(λx.
              suminf
                (λn.
                     x pow n *
                     if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n))  =
            (\x. suminf (\n. (if EVEN n then &0
                              else -(&1) pow ((n - 1) DIV 2) / &n) * x pow n)) ’
             by (pop_assum $ once_rewrite_tac o single >> gs[])
            >> pop_assum $ rewrite_tac o single
            >> irule REAL_ATN_POWSER_DIFFL
            >> pop_assum $ kall_tac
            >> gs[ABS_BOUNDS_LT]
            >> conj_tac
            >- (irule REAL_LTE_TRANS >> qexists_tac ‘&0’ >> gs[])
            >> irule REAL_LET_TRANS >> qexists_tac ‘x’ >> gs[])
       >> pop_assum $ kall_tac
       >> ‘(λx. atn x) = atn’ by gs[FUN_EQ_THM]
       >> pop_assum $ rewrite_tac o single
       >> gs[DIFF_ATN]
     )
  >> rpt strip_tac
  >> pop_assum $ qspecl_then [‘x: real’, ‘&0:real’ ] assume_tac
  >> res_tac >> gs[]
  >> first_assum irule
  >> rpt strip_tac
  >> ‘&0 = (inv(&1 + x' pow 2)) - (inv(&1 + x' pow 2))’ by gs[]
  >> ‘  ((λx''.
              suminf
                (λn.
                     x'' pow n *
                     if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n) −
                atn x'') diffl 0) x' =
       ((λx''.
             ((\x.  suminf
                (λn.
                     x pow n *
                     if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n)) x'')  −
              ( (\x. atn x) x'')) diffl ( (inv(&1 + x' pow 2)) - (inv(&1 + x' pow 2)))) x'’
    by (pop_assum $ rewrite_tac o single >> gs[])
  >> pop_assum $ rewrite_tac o single
  >> pop_assum kall_tac
  >> irule limTheory.DIFF_SUB
  >> conj_tac
  >- (‘(λx.
              suminf
                (λn.
                     x pow n *
                     if EVEN n then 0 else -1 pow ((n − 1) DIV 2) / &n))  =
            (\x. suminf (\n. (if EVEN n then &0
                              else -(&1) pow ((n - 1) DIV 2) / &n) * x pow n)) ’
             by gs[]
      >> pop_assum $ rewrite_tac o single
      >> irule REAL_ATN_POWSER_DIFFL
      >> gs[ABS_BOUNDS_LT]
      >> conj_tac
      >- ( irule REAL_LTE_TRANS >> qexists_tac ‘x’ >> gs[] )
      >> irule REAL_LET_TRANS >> qexists_tac ‘&0’ >> gs[]
     )
  >> ‘(λx. atn x) = atn’ by gs[FUN_EQ_THM]
  >> pop_assum $ rewrite_tac o single
  >> gs[DIFF_ATN]
QED

Theorem MCLAURIN_ATN:
  ∀ x n.
    abs(x) < &1 ⇒
    abs(atn x -
        sum(0,n) (\m. (if EVEN m then &0
                       else -(&1) pow ((m - 1) DIV 2) / &m) *
                      x pow m)) ≤
    abs(x) pow n / (&1 - abs x)
Proof
  REPEAT STRIP_TAC
  >> FIRST_ASSUM(MP_TAC o MATCH_MP REAL_ATN_POWSER) THEN
  DISCH_THEN(fn th => ASSUME_TAC(SYM(MATCH_MP seqTheory.SUM_UNIQ th)) THEN
                       MP_TAC(MATCH_MP seqTheory.SUM_SUMMABLE th)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP seqTheory.SER_OFFSET) THEN
  DISCH_THEN(MP_TAC o SPEC “n:num”) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP seqTheory.SUM_UNIQ) THEN
  MATCH_MP_TAC(REAL_ARITH
   “abs(r) <= e ==> (f - s = r) ==> abs(f - s) <= e”) THEN
  SUBGOAL_THEN
   “(\m. abs(x) pow (m + n)) sums ((abs(x) pow n) * inv(&1 - abs(x)))”
  ASSUME_TAC
  >- ( FIRST_ASSUM(MP_TAC o MATCH_MP seqTheory.GP o MATCH_MP (REAL_ARITH
        “abs(x) < &1 ==> abs(abs x) < &1”)) THEN
       DISCH_THEN(MP_TAC o SPEC “abs(x) pow n” o MATCH_MP seqTheory.SER_CMUL)
       THEN ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM REAL_POW_ADD]
       >> gs[] >> strip_tac >> REWRITE_TAC[REAL_POW_ADD] >> gs[]
       >> ‘(λm. abs x pow m * abs x pow n) = (λn'. abs x pow n * abs x pow n')’
         by gs[FUN_EQ_THM]
       >> pop_assum $ rewrite_tac o single
       >> gs[]
     )
  >> FIRST_ASSUM(SUBST1_TAC o MATCH_MP seqTheory.SUM_UNIQ o
                 REWRITE_RULE[GSYM real_div])
  THEN
  SUBGOAL_THEN
   “!m. abs((if EVEN (m + n) then &0
             else -(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
             x pow (m + n))
        <= abs(x) pow (m + n)”
  ASSUME_TAC
  >- ( GEN_TAC THEN COND_CASES_TAC THEN
       gs[REAL_MUL_LZERO, ABS_N, POW_POS, REAL_ABS_POS] THEN
       REWRITE_TAC[REAL_ABS_MUL, ABS_DIV, GSYM POW_ABS, ABS_NEG] THEN
       REWRITE_TAC[ABS_N, POW_ONE, REAL_MUL_LID] THEN
       rewrite_tac[REAL_MUL_RID]
       >> ‘abs x pow (m + n) = &1 * abs x pow (m + n) ’ by
         gs[REAL_MUL_LID]
       >> pop_assum $ once_rewrite_tac o single
       >> ‘abs (&(m + n))⁻¹ * (1 * abs x pow (m + n)) =
           abs (&(m + n))⁻¹ *  abs x pow (m + n)’ by gs[]
       >> pop_assum $ rewrite_tac o single
       >> irule REAL_LE_MUL2
       >> rpt conj_tac
       >- ( ‘ abs (&(m + n))⁻¹ =  (abs (&(m + n)))⁻¹’ by
             ( irule ABS_INV
               >> ‘ODD (m+n)’ by gs[ODD_EVEN]
               >> ‘?p. (m+n) = SUC (2 * p)’ by gs[ODD_EXISTS]
               >> pop_assum $ rewrite_tac o single
               >> gs[]
             )
            >> pop_assum $ rewrite_tac o single
            >> irule REAL_INV_LE_1
            >> rewrite_tac[ABS_N]
            >> ‘ODD (m+n)’ by gs[ODD_EVEN]
            >> ‘?p. (m+n) = SUC (2 * p)’ by gs[ODD_EXISTS]
            >> pop_assum $ rewrite_tac o single
            >> gs[]
          )
       >- gs[]
       >- gs[ABS_POS]
       >> gs[ABS_POS]
     )
  >> MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
  “suminf (\m. abs((if EVEN (m + n) then &0
                     else -(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
                    x pow (m + n)))” THEN
  CONJ_TAC
  >- ( gs[]
       >> ‘ suminf
          (λm.
               abs
                 (x pow (m + n) *
                  if EVEN (m + n) then 0
                  else -1 pow ((m + n - 1) DIV 2) / &(m + n))) =
           suminf
          (λm.
               abs
               ( ( \n'. (x pow (n + n') *
                        if EVEN (n + n') then 0
                        else -1 pow ((n + n' - 1) DIV 2) / &(n + n'))) m))’ by
         gs[]
       >> pop_assum $ rewrite_tac o single
       >> irule seqTheory.SER_ABS THEN MATCH_MP_TAC seqTheory.SER_COMPARA THEN
       EXISTS_TAC “\m. abs(x) pow (m + n)” THEN
       ASM_REWRITE_TAC[] THEN conj_tac
       >- ( qexists_tac ‘0’ >> rpt strip_tac
            >> gs[] >> pop_assum $ qspec_then ‘n'’ assume_tac
            >> gs[]
          )
       >> mesonLib.ASM_MESON_TAC[seqTheory.SUM_SUMMABLE]
     )
  >> MATCH_MP_TAC seqTheory.SER_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC
  >- ( strip_tac >> gs[] >> pop_assum $ qspec_then ‘n'’ assume_tac >> gs[] )
  >> conj_tac
  >- ( ‘ (λm.
               abs
                 ((if EVEN (m + n) then 0
                   else -1 pow ((m + n - 1) DIV 2) / &(m + n)) *
                  x pow (m + n))) =
        (λm.
               abs
                ((\n'. ((if EVEN (n' + n) then 0
                   else -1 pow ((n' + n - 1) DIV 2) / &(n' + n)) *
                        x pow (n' + n))) m))’ by gs[]
       >> pop_assum $ rewrite_tac o single
       >> MATCH_MP_TAC seqTheory.SER_COMPARA THEN
       EXISTS_TAC “\m. abs (x) pow (m + n)” THEN
       ASM_REWRITE_TAC[] >> conj_tac
       >- ( qexists_tac ‘0’ >> rpt strip_tac
            >> gs[] >> pop_assum $ qspec_then ‘n'’ assume_tac
            >> gs[]
          )
       >> mesonLib.ASM_MESON_TAC[seqTheory.SUM_SUMMABLE]
     )
  >> mesonLib.ASM_MESON_TAC[seqTheory.SUM_SUMMABLE]
QED

Theorem MCLAURIN_EXP_COMPOSITE:
  ! x y err.
    0 <= err /\
    abs (x - y) <= err ==>
    abs (exp x - exp y) <= exp x * (exp err - 1)
Proof
  rpt strip_tac
  >> mp_with_then strip_assume_tac ‘abs (x - y) <= err’ ERR_ABS_SIMP
  >> gs[abs]
  >> Cases_on ‘0 <= x - y’ >> gs[REAL_NOT_LE]
  >- (
    ‘y <= x’ by real_tac
    >> ‘exp y <= exp x /\ exp x <= exp (x  + err) /\ exp (x - err) <=  exp y ’
      by gs[EXP_MONO_LE]
    >> ‘0 <= exp x - exp y’ by real_tac
    >> gs[]
    >> transitivity_for ‘exp (y + err) - exp y’ >> conj_tac
    >> rewrite_tac [real_sub]
    >- gs[REAL_LE_RADD, EXP_MONO_LE]
    >> rewrite_tac[EXP_ADD]
    >> ‘exp y * exp err = exp y * (1 + (exp err - 1))’ by real_tac
    >> pop_assum $ once_rewrite_tac o single
    >> real_rw ‘exp y * (1 + (exp err - 1)) + - exp y = exp y * (exp err - 1)’
    >> rewrite_tac[real_sub]
    >> irule REAL_LE_RMUL_IMP
    >> gs[EXP_MONO_LE, GSYM real_sub, EXP_MINUS_ONE_POS])
  >> ‘x < y’ by real_tac
  >> ‘exp x < exp y’ by gs[EXP_MONO_LT]
  >> ‘~ (0 <= exp x - exp y)’ by (gs[REAL_NOT_LE] >> real_tac)
  >> gs[]
  >> ‘x <= y’ by real_tac
  >> ‘exp x <= exp y /\ exp y <= exp (x  + err) /\ exp (x - err) <= exp y’
      by gs[EXP_MONO_LE]
  >> rewrite_tac [REAL_NEG_ADD, real_sub, REAL_NEG_NEG]
  >> ‘- exp x + exp y = exp y - exp x’ by real_tac
  >> pop_assum $ rewrite_tac o single
  >> transitivity_for ‘exp (x + err) - exp x’
  >> conj_tac >- gs[real_sub, REAL_LE_RADD]
  >> rewrite_tac[EXP_ADD, real_sub]
  >> real_rw ‘exp x * exp err + -exp x = exp x * (1 + (exp err - 1)) + - exp x’
  >> real_rw ‘exp x * (1 + (exp err - 1)) + - exp x = exp x * (exp err + -  1)’
  >> gs[]
QED

Theorem cos_sub_1_neg:
  ∀ x. cos x - 1 ≤ 0
Proof
  rpt strip_tac
  >> transitivity_for ‘1 - 1’
  >> reverse conj_tac >- real_tac
  >> rewrite_tac[real_sub]
  >> gs[REAL_LE_LADD, COS_BOUNDS]
QED

Definition abs_alt_def:
  abs_alt (x:real) = if x ≤ 0 then - x else x
End

Theorem abs_alt_abs:
  abs_alt x = abs x
Proof
  gs[abs_alt_def, abs] >> cond_cases_tac
  >- (
    Cases_on ‘x = 0’ >> gs[]
    >> ‘~ (0 ≤ x)’ by real_tac
    >> gs[])
  >> gs[REAL_NOT_LE, REAL_LE_LT]
QED

Theorem cos_decreasing_abs:
  0 ≤ x ∧ x ≤ pi / 2 ∧
  abs y ≤ x ⇒
  cos x ≤ cos y
Proof
  rpt strip_tac >> gs[abs]
  >> ‘x ≤ pi’ by (transitivity_for ‘pi/2’ >> conj_tac >- gs[]
                  >> rewrite_tac [REAL_LE_LT] >> gs[PI2_lt_PI])
  >> Cases_on ‘0 ≤ y’ >> gs[]
  >- (
    irule cos_decr_0_pi >> gs[]
    >> real_tac)
  >> ‘cos y = cos (- y)’ by gs[COS_NEG]
  >> pop_assum $ rewrite_tac o single
  >> irule cos_decr_0_pi >> gs[REAL_NOT_LE]
  >> conj_tac >> real_tac
QED

Theorem sin_increasing_abs:
  0 ≤ x ∧ x ≤ pi / 2 ∧
  abs y ≤ x ⇒
  abs (sin y) ≤ abs(sin x)
Proof
  rpt strip_tac >> gs[abs]
  >> ‘0 ≤ sin x’ by (irule SIN_POS_PI2_LE >> gs[])
  >> gs[] >> Cases_on ‘0 ≤ y’ >> gs[]
  >- (
    ‘y ≤ pi / 2’ by (transitivity_for ‘x’ >> gs[])
    >> ‘0 ≤ sin y’ by (irule SIN_POS_PI2_LE >> gs[])
    >> gs[]
    >> irule sin_incr_0_pi2 >> gs[])
  >> gs[REAL_NOT_LE]
  >> ‘y ≤ 0’ by real_tac
  >> ‘- (pi/2) ≤ y’ by (irule REAL_NEG_LE1 >> transitivity_for ‘x’ >> gs[])
  >> ‘sin y ≤ 0’
     by (drule sin_negpi2_0_le >> disch_then drule >> gs[])
  >> gs[GSYM abs, GSYM abs_alt_abs, abs_alt_def, GSYM SIN_NEG]
  >> ‘-y ≤ pi/2’ by (transitivity_for ‘x’ >> gs[])
  >> irule sin_incr_0_pi2 >> gs[]
QED

Theorem MCLAURIN_SIN_COMPOSITE:
  ∀ x y err.
    0 ≤ err ∧ err ≤ pi / 2 ∧
    abs (x - y) ≤ err ⇒
    abs (sin x - sin y) ≤ abs (cos err - 1) + sin err
Proof
  rpt strip_tac  >> imp_res_tac abs_exists
  >> VAR_EQ_TAC
  >> rewrite_tac[SIN_ADD]
  >> ‘cos d = 1 + (cos d - 1)’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> rewrite_tac[REAL_LDISTRIB, REAL_MUL_RID]
  >> rewrite_tac[real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC]
  >> ‘sin x + - sin x = 0’ by real_tac
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac[REAL_ADD_LID]
  >> qmatch_goalsub_abbrev_tac ‘abs (sin_cos_1 + cos_sin)’
  >> transitivity_for ‘abs sin_cos_1 + abs cos_sin’
  >> conj_tac >- gs[REAL_ABS_TRIANGLE]
  >> unabbrev_all_tac
  >> irule REAL_LE_ADD2 >> rewrite_tac[ABS_NEG, ABS_MUL]
  >> conj_tac
  >- (
    transitivity_for ‘1 * abs (cos d + -1)’ >> conj_tac
    >- (
      irule REAL_LE_RMUL_IMP >> gs[ABS_POS]
      >> qspec_then ‘x’ assume_tac SIN_BOUNDS
      >> qspec_then ‘- x’ assume_tac SIN_BOUNDS
      >> gs[abs, SIN_NEG] >> cond_cases_tac >> gs[])
    >> rewrite_tac[REAL_MUL_LID]
    >> simp[GSYM abs_alt_abs]
    >> simp[abs_alt_def, GSYM real_sub, cos_sub_1_neg]
    >> gs[real_sub]
    >> irule cos_decreasing_abs >> gs[])
  >> ‘sin err = 1 * sin err’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_LE_MUL2
  >> gs[ABS_POS] >> conj_tac
  >- (
    qspec_then ‘x’ assume_tac COS_BOUNDS
    >> qspec_then ‘-x’ assume_tac COS_BOUNDS
    >> gs[abs] >> cond_cases_tac >> gs[COS_NEG]
    >> irule REAL_NEG_LE1 >> gs[])
  >> ‘0 ≤ sin err’ by (irule SIN_POS_PI2_LE >> gs[])
  >> transitivity_for ‘abs (sin err)’ >> conj_tac
  >- (irule sin_increasing_abs >> gs[])
  >> gs[abs]
QED

Theorem MCLAURIN_COS_COMPOSITE:
  ∀ x y err.
    0 ≤ err ∧ err ≤ pi / 2 ∧
    abs (x - y) ≤ err ⇒
    abs (cos x - cos y) ≤ abs (cos err - 1) + sin err
Proof
  rpt strip_tac  >> imp_res_tac abs_exists
  >> VAR_EQ_TAC
  >> rewrite_tac[COS_ADD]
  >> ‘cos d = 1 + (cos d - 1)’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> rewrite_tac[REAL_LDISTRIB, REAL_MUL_RID]
  >> rewrite_tac[real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC]
  >> ‘cos x + - cos x = 0’ by real_tac
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac[REAL_ADD_LID]
  >> qmatch_goalsub_abbrev_tac ‘abs (cos_cos_1 + sin_sin)’
  >> transitivity_for ‘abs cos_cos_1 + abs sin_sin’
  >> conj_tac >- gs[REAL_ABS_TRIANGLE]
  >> unabbrev_all_tac
  >> irule REAL_LE_ADD2 >> rewrite_tac[ABS_NEG, ABS_MUL]
  >> conj_tac
  >- (
    transitivity_for ‘1 * abs (cos d + -1)’ >> conj_tac
    >- (
      irule REAL_LE_RMUL_IMP >> gs[ABS_POS]
      >> qspec_then ‘x’ assume_tac COS_BOUNDS
      >> qspec_then ‘x + pi’ assume_tac COS_BOUNDS
      >> gs[abs, GSYM COS_PERIODIC_PI] >> cond_cases_tac >> gs[])
    >> rewrite_tac[REAL_MUL_LID]
    >> simp[GSYM abs_alt_abs]
    >> simp[abs_alt_def, GSYM real_sub, cos_sub_1_neg]
    >> gs[real_sub]
    >> irule cos_decreasing_abs >> gs[])
  >> ‘sin err = 1 * sin err’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_LE_MUL2
  >> gs[ABS_POS] >> conj_tac
  >- (
    qspec_then ‘x’ assume_tac SIN_BOUNDS
    >> qspec_then ‘-x’ assume_tac SIN_BOUNDS
    >> gs[abs, SIN_NEG] >> cond_cases_tac >> gs[])
  >> ‘0 ≤ sin err’ by (irule SIN_POS_PI2_LE >> gs[])
  >> transitivity_for ‘abs (sin err)’ >> conj_tac
  >- (irule sin_increasing_abs >> gs[])
  >> gs[abs]
QED

Theorem MCLAURIN_LN_COMPOSITE:
  ∀ x y err.
    0 ≤ err ∧ 0 < x ∧ 0 < y ∧
    abs (x - y) ≤ err ⇒
    abs (ln x - ln y) ≤ abs (ln (1 + err / min x y))
Proof
  rw[REAL_NEG_SUB]
  >> gs[SimpR“($<=):real->real->bool”, abs]
  >> ‘0 < min x y’
    by (gs[min_def] >> cond_cases_tac >> gs[])
  >> ‘0 ≤ err / min x y’ by (gs[nonzerop_def] >> cond_cases_tac >> gs[])
  >> ‘1 ≤ 1 + err / min x y’ by gs[nonzerop_def]
  >> pop_assum $ mp_then Any assume_tac LN_POS >> gs[abs]
  >> Cases_on ‘0 ≤ x - y’ >> gs[]
  >- (
    ‘y ≤ x’ by real_tac
    >> ‘ln y ≤ ln x’ by gs[GSYM LN_MONO_LE]
    >> ‘0 ≤ ln x - ln y’ by real_tac
    >> ‘x ≤ y + err’ by real_tac
    >> ‘0 < y + err’ by real_tac
    >> ‘ln x ≤ ln (y + err)’ by gs [GSYM LN_MONO_LE]
    >> gs[]
    >> irule REAL_LE_TRANS
    >> qexists_tac ‘ln (y + err) - ln y’ >> conj_tac
    >- (rewrite_tac[real_sub] >> irule REAL_LE_ADD2 >> gs[])
    >> ‘0 ≤ err / y ’ by (gs[nonzerop_def] >> cond_cases_tac >> gs[])
    >> ‘0 < 1 + err / y’ by (irule REAL_LTE_ADD >> gs[])
    >> ‘y + err = y * (1 + err / y)’
      by (gs[REAL_LDISTRIB, REAL_MUL_RID, nonzerop_def] >> cond_cases_tac >> gs[])
    >> pop_assum $ once_rewrite_tac o single
    >> gs[LN_MUL]
    >> ‘ln y + ln (1 + err / y) - ln y = ln (1 + err / y)’ by real_tac
    >> pop_assum $ rewrite_tac o single
    >> ‘0 < 1 + err / min x y’ by (irule REAL_LTE_ADD >> gs[])
    >> qpat_x_assum ‘0 < 1 + err / y’ $ mp_then Any mp_tac LN_MONO_LE
    >> disch_then drule >> strip_tac >> gs[]
    >> gs[nonzerop_def] >> rpt (cond_cases_tac >> gs[])
    >> irule REAL_LE_LMUL_IMP >> gs[REAL_MIN_LE2])
  >> gs[REAL_NOT_LE]
  >> ‘x < y’ by real_tac
  >> ‘ln x < ln y’
    by (qpat_x_assum ‘0 < x’ $ mp_then Any mp_tac $ LN_MONO_LT
        >> disch_then $ qspec_then ‘y’ mp_tac >> impl_tac >> gs[])
  >> ‘~ (0 ≤ ln x - ln y)’ by (gs[REAL_NOT_LE] >> real_tac)
  >> gs[REAL_NEG_SUB]
  >> ‘0 < x + err’ by real_tac
  >> ‘y ≤ x + err’ by real_tac
  >> ‘ln y ≤ ln (x + err)’ by gs [LN_MONO_LE]
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘ln (x + err) - ln x’ >> conj_tac
  >- (rewrite_tac[real_sub] >> irule REAL_LE_ADD2 >> gs[])
  >> ‘0 ≤ err / x ’ by (gs[nonzerop_def] >> cond_cases_tac >> gs[])
  >> ‘0 < 1 + err / x’ by (irule REAL_LTE_ADD >> gs[])
  >> ‘x + err = x * (1 + err / x)’
    by (gs[REAL_LDISTRIB, REAL_MUL_RID, nonzerop_def] >> cond_cases_tac >> gs[])
  >> pop_assum $ once_rewrite_tac o single
  >> gs[LN_MUL]
  >> ‘ln x + ln (1 + err / x) - ln x = ln (1 + err / x)’ by real_tac
  >> pop_assum $ rewrite_tac o single
  >> ‘0 < 1 + err / min x y’ by (irule REAL_LTE_ADD >> gs[])
  >> qpat_x_assum ‘0 < 1 + err / x’ $ mp_then Any mp_tac LN_MONO_LE
  >> disch_then drule >> strip_tac >> gs[]
  >> gs[nonzerop_def] >> rpt (cond_cases_tac >> gs[])
  >> irule REAL_LE_LMUL_IMP >> gs[REAL_MIN_LE1]
QED

Definition atnPoly_def:
  atnPoly 0 = [] /\
  atnPoly (SUC n) =
    if EVEN n then (atnPoly n) ++ [0]
    else ( atnPoly n) ++ [-(&1) pow ((n - 1) DIV 2) / &n]
End

Theorem atnPoly_LENGTH[simp]:
  LENGTH (atnPoly n) = n
Proof
  Induct_on ‘n’ >> gs[atnPoly_def]
  >> cond_cases_tac >> gs[]
QED

Theorem atnPoly_correct:
  ∀ n x.
  evalPoly (atnPoly n) x =
    sum(0,n) (\m. (if EVEN m then &0
                   else -(&1) pow ((m - 1) DIV 2) / &m) *
                  x pow m)
Proof
  Induct_on ‘n’ >> gs[atnPoly_def, evalPoly_def, sum]
  >> Cases_on ‘EVEN n’ >> gs[sum, evalPoly_app, evalPoly_def]
QED

local
  val specThm = Q.SPEC ‘4’ (SPEC_ALL REAL_LT_RDIV_EQ |> GEN “z:real”)
  val validHyp = specThm |> UNDISCH_ALL |> hyp |> hd |> EVAL |> SIMP_RULE std_ss [EQ_CLAUSES]
in
Theorem REAL_LT_DIV_EQ[local] = MATCH_MP specThm validHyp;
end

fun mk_pi_lb_thm cval iters = let
  fun revApp f x = fn y => f y x
  val abs_9 = EVAL “abs ^cval < 1” |> SIMP_RULE std_ss [EQ_CLAUSES]
  val atnPoly_eq = EVAL “evalPoly (atnPoly ^iters) ^cval”
  val ERR_ATN = EVAL “abs ^cval pow ^iters / (1 - abs ^cval)”
  val ATN_CONCR_LT_PI4 = MATCH_MP (Q.SPEC ‘^cval’ ATN_LT_PI4_POS) (EVAL “^cval < 1” |> SIMP_RULE std_ss [EQ_CLAUSES])
  in
    REWRITE_RULE [GSYM atnPoly_correct] MCLAURIN_ATN
    |> SPEC_ALL |> GEN “x:real” |> GEN “n:num”
    |> SPEC “^iters:num”
    |> SPEC “^cval:real”
    |> (fn th => MATCH_MP th abs_9)
    |> REWRITE_RULE [atnPoly_eq, ERR_ATN]
    |> MATCH_MP ERR_ABS_SIMP
    |> CONJ_LIST 4 |> (fn ls => List.nth (ls, 3))
    |> MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] REAL_LET_TRANS)
    |> revApp MATCH_MP ATN_CONCR_LT_PI4
    |> REWRITE_RULE [REAL_LT_DIV_EQ]
    |> CONV_RULE $ RATOR_CONV $ RAND_CONV EVAL
  end;

Theorem PI_LB = mk_pi_lb_thm “0.97:real” “150:num”

Theorem inv2_le_pi2:
  inv 2 ≤ pi/2
Proof
  ‘2 * inv 2 ≤ pi’ suffices_by gs[]
  >> rewrite_tac[REAL_INV_1OVER]
  >> ‘2 * (1 / 2) = 1:real’ by EVAL_TAC
  >> pop_assum $ rewrite_tac o single
  >> ‘1 < pi’ suffices_by real_tac
  >> irule REAL_LET_TRANS
  >> qexists_tac ‘^(PI_LB|> concl |> rator |> rand)’
  >> gs[PI_LB]
QED

val _ = export_theory();

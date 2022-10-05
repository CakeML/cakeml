(**
  small theorems extending HOL4's realTheory
  used throughout the development
**)
open preambleDandelion;

val _ = new_theory "moreReal";

val _ = realLib.deprecate_real();

Theorem REAL_LE_RCANCEL_IMP:
  ∀ x y z:real.
    &0 < z ∧
    x * z ≤ y * z ⇒
    x ≤ y
Proof
  rpt strip_tac
  >> gs[REAL_LE_LMUL]
QED

Theorem diff_chain:
  ∀ x. ((λx. 1 + x) diffl 1) x
Proof
  rpt strip_tac
  >> ‘& 1 = &0 + &1’ by gs[]
  >> ‘(λx. 1 + x) = (λx. ((\x. 1) x) + ((\x. x) x))’ by gs[FUN_EQ_THM]
  >> ‘ ((λx. ((\x. 1) x) + ((\x. x) x)) diffl  (&0 + &1)) x ==>
       ((λx. 1 + x) diffl 1) x ’ by gs[]
  >> first_assum irule
  >> irule limTheory.DIFF_ADD
  >> rpt conj_tac
  >- rewrite_tac[limTheory.DIFF_CONST]
  >> rewrite_tac[limTheory.DIFF_X]
QED

Theorem diff_chain_sub:
  ∀ x. ((λx. 1 - x) diffl -1) x
Proof
  rpt strip_tac
  >> ‘-1 = &0 -1’ by gs[]
  >> ‘(λx:real. 1 - x) = (λx. ((\x. 1) x) + ((\x. -x) x))’ by
    ( rw[FUN_EQ_THM] >> REAL_ARITH_TAC )
  >> ‘ ((λx:real. ((\x. 1) x) + ((\x:real. -x) x)) diffl  (&0 + -1)) x ==>
       ((λx:real. 1 - x) diffl -1) x ’ by gs[]
  >> first_assum irule
  >> irule limTheory.DIFF_ADD
  >> rpt conj_tac
  >- rewrite_tac[limTheory.DIFF_CONST]
  >> ‘ ((λx. (-1) * ((\x. x) x))  diffl ((-1) * &1)) x ==>
       ((λx:real. -x) diffl -1) x’ by rw[]
  >> first_assum irule
  >> irule limTheory.DIFF_CMUL
  >> rewrite_tac[limTheory.DIFF_X]
QED

Theorem cos_lt_1:
  !x. 0 < x /\ x < (pi / &2) ==>
      cos x < 1
Proof
  rpt strip_tac
  >> ‘!a:bool. a = ~~a’ by gs[]
  >> pop_assum $ once_rewrite_tac o single
  >> PURE_ONCE_REWRITE_TAC[REAL_NOT_LT]
  >> DISCH_THEN(MP_TAC o MATCH_MP REAL_LE1_POW2)
  >> DISCH_THEN(MP_TAC o ONCE_REWRITE_RULE[GSYM REAL_SUB_LE])
  >> DISCH_THEN(MP_TAC o CONJ(SPEC “sin(x)” REAL_LE_SQUARE))
  >> REWRITE_TAC[GSYM POW_2]
  >> rw[]
  >> rewrite_tac[GSYM SIN_CIRCLE]
  >> ‘(cos x)² - ((sin x)² + (cos x)²) = - ((sin x) pow 2)’ by
    REAL_ARITH_TAC
  >> pop_assum $ rewrite_tac o single
  >> gs[]
  >> assume_tac REAL_NOT_LE
  >> pop_assum $ qspecl_then [‘(sin x) pow 2’, ‘&0’] assume_tac
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_POW_LT
  >> gs[SIN_POS_PI2]
QED

Theorem DIFF_DEC_LT:
  ∀ f x lo hi.
    lo < x ∧ x < hi ∧
    (∀ z. lo ≤ z ∧ z ≤ hi ⇒ f contl z) ∧
    (∀ z. ∃ l. lo < z ∧ z < hi ⇒ (f diffl l) z ∧ l < 0) ⇒
    (∀ y. lo < y ∧ y < hi ∧ x < y ⇒ f y < f x)
Proof
  rpt strip_tac
  >> qspecl_then [‘f’, ‘x’, ‘y’] mp_tac limTheory.MVT >> impl_tac
  >- (
    rpt conj_tac
    >- gs[]
    >- (
      rpt strip_tac >> rename [‘z <= y’]
      >> first_x_assum irule >> conj_tac >> real_tac)
    >> rpt strip_tac >> rename [‘z < y’]
    >> ‘lo < z /\ z < hi’ by (conj_tac >> real_tac)
    >> first_x_assum $ qspec_then ‘z’ strip_assume_tac
    >> res_tac >> rewrite_tac[limTheory.differentiable]
    >> qexists_tac ‘l’ >> gs[])
  >> rpt strip_tac
  >> ‘lo < z /\ z < hi’ by (conj_tac >> real_tac)
  >> first_x_assum $ qspec_then ‘z’ strip_assume_tac
  >> res_tac
  >> ‘l = l'’
    by (irule limTheory.DIFF_UNIQ >> qexists_tac ‘f’ >> qexists_tac ‘z’ >> res_tac >> gs[])
  >> rpt VAR_EQ_TAC
  >> ‘0 < y - x’ by real_tac
  >> Cases_on ‘l = 0’ >- (rpt VAR_EQ_TAC >> real_tac)
  >> ‘l < 0’ by real_tac
  >> ‘(y - x) * l < 0’ suffices_by real_tac
  >> ‘0:real = (y - x) * 0’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_LT_LMUL_IMP >> gs[]
QED

Theorem DIFF_DEC_LE:
  ∀ f x lo hi.
    lo ≤ x ∧ x ≤ hi ∧
    (∀ z. ∃ l. lo ≤ z ∧ z ≤ hi ⇒ (f diffl l) z ∧ l ≤ 0) ⇒
    (∀ y. lo ≤ y ∧ y ≤ hi ∧ x ≤ y ⇒ f y ≤ f x)
Proof
  rpt strip_tac
  >> Cases_on ‘x = y’ >- gs[]
  >> ‘x < y’ by real_tac
  >> qspecl_then [‘f’, ‘x’, ‘y’] mp_tac limTheory.MVT >> impl_tac
  >- (
    rpt conj_tac
    >- gs[]
    >- (
      rpt strip_tac >> rename [‘z <= y’]
      >> ‘lo <= z /\ z <= hi’ by (conj_tac >> real_tac)
      >> irule limTheory.DIFF_CONT
      >> first_x_assum $ qspec_then ‘z’ strip_assume_tac
      >> res_tac >> qexists_tac ‘l’ >> gs[])
    >> rpt strip_tac >> rename [‘z < y’]
    >> ‘lo <= z /\ z <= hi’ by (conj_tac >> real_tac)
    >> first_x_assum $ qspec_then ‘z’ strip_assume_tac
    >> res_tac >> rewrite_tac[limTheory.differentiable]
    >> qexists_tac ‘l’ >> gs[])
  >> rpt strip_tac
  >> ‘lo <= z /\ z <= hi’ by (conj_tac >> real_tac)
  >> first_x_assum $ qspec_then ‘z’ strip_assume_tac
  >> res_tac
  >> ‘l = l'’
    by (irule limTheory.DIFF_UNIQ >> qexists_tac ‘f’ >> qexists_tac ‘z’ >> gs[])
  >> rpt VAR_EQ_TAC
  >> ‘0 < y - x’ by real_tac
  >> Cases_on ‘l = 0’ >- (rpt VAR_EQ_TAC >> real_tac)
  >> ‘l < 0’ by real_tac
  >> ‘(y - x) * l < 0’ suffices_by real_tac
  >> ‘0:real = (y - x) * 0’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_LT_LMUL_IMP >> gs[]
QED

Theorem DIFF_INC:
  ∀ f x lo hi.
    lo ≤ x ∧ x ≤ hi ∧
    (∀ z. ∃ l. lo ≤ z ∧ z ≤ hi ⇒ (f diffl l) z ∧ 0 ≤ l) ⇒
    (∀ y. lo ≤ y ∧ y ≤ hi ∧ x ≤ y ⇒ f x ≤ f y)
Proof
  rpt strip_tac
  >> Cases_on ‘x = y’ >- gs[]
  >> ‘x < y’ by real_tac
  >> qspecl_then [‘f’, ‘x’, ‘y’] mp_tac limTheory.MVT
  >> impl_tac
  >- (
    rpt conj_tac
    >- gs[]
    >- (
      rpt strip_tac >> rename [‘z <= y’]
      >> ‘lo <= z /\ z <= hi’ by (conj_tac >> real_tac)
      >> irule limTheory.DIFF_CONT
      >> first_x_assum $ qspec_then ‘z’ strip_assume_tac
      >> res_tac >> qexists_tac ‘l’ >> gs[])
    >> rpt strip_tac >> rename [‘z < y’]
    >> ‘lo <= z /\ z <= hi’ by (conj_tac >> real_tac)
    >> first_x_assum $ qspec_then ‘z’ strip_assume_tac
    >> res_tac >> rewrite_tac[limTheory.differentiable]
    >> qexists_tac ‘l’ >> gs[])
  >> rpt strip_tac
  >> ‘lo <= z /\ z <= hi’ by (conj_tac >> real_tac)
  >> first_x_assum $ qspec_then ‘z’ strip_assume_tac
  >> res_tac
  >> ‘l = l'’
    by (irule limTheory.DIFF_UNIQ >> qexists_tac ‘f’ >> qexists_tac ‘z’ >> gs[])
  >> rpt VAR_EQ_TAC
  >> Cases_on ‘l = 0’
  >- (rpt VAR_EQ_TAC >> real_tac)
  >> ‘0 < l’ by real_tac
  >> ‘0 < y - x’ by real_tac
  >> ‘0 < (y - x) * l’ suffices_by real_tac
  >> irule REAL_LT_MUL >> gs[]
QED

Theorem REAL_LE_ZERO_MUL1:
  ∀ x (y:real).
      x ≤ 0 ∧ 0 ≤ y ⇒ x * y ≤ 0
Proof
  rpt strip_tac
  >> transitivity_for ‘0 * y’ >> reverse conj_tac
  >- real_tac
  >> irule REAL_LE_RMUL_IMP >> gs[]
QED

Theorem REAL_LE_ZERO_MUL2:
  ∀ x (y:real).
      0 ≤ x ∧ y ≤ 0 ⇒ x * y ≤ 0
Proof
  rpt strip_tac
  >> transitivity_for ‘x * 0’ >> reverse conj_tac
  >- real_tac
  >> irule REAL_LE_LMUL_IMP >> gs[]
QED

Theorem REAL_ZERO_LE_MUL1:
  ∀ x (y:real).
      0 ≤ x ∧ 0 ≤ y ⇒ 0 ≤ x * y
Proof
  rpt strip_tac
  >> transitivity_for ‘0 * 0’ >> conj_tac
  >- real_tac
  >> irule REAL_LE_MUL2 >> gs[]
QED

Theorem REAL_ZERO_LE_MUL2:
  ∀ x (y:real).
      x ≤ 0 ∧ y ≤ 0 ⇒ 0 ≤ x * y
Proof
  rpt strip_tac
  >> ‘0 ≤ -x’ by real_tac
  >> ‘0 ≤ -y’ by real_tac
  >> ‘x * y = - - (x * y)’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> rewrite_tac[Once REAL_NEG_LMUL, Once REAL_NEG_RMUL]
  >> irule REAL_ZERO_LE_MUL1 >> gs[]
QED

Theorem REAL_NEG_LE1:
  - y ≤ x ⇒ - x ≤ y:real
Proof
  rpt strip_tac
  >> ‘y = - - y’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> gs[REAL_LE_NEG]
QED

Theorem REAL_NEG_LE2:
  y ≤ - x ⇒ x ≤ -y:real
Proof
  rpt strip_tac
  >> ‘x = - - x’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> gs[REAL_LE_NEG]
QED

Theorem MVT_ALT:
 ∀ f f' a b.
   a < b ∧ (∀ x. a ≤ x ∧ x ≤ b ⇒ (f diffl f'(x))(x)) ⇒
   ∃ z. a < z ∧ z < b ∧ (f b - f a = (b - a) * f'(z))
Proof
  rpt strip_tac
  >> drule limTheory.MVT >> rewrite_tac[limTheory.differentiable]
  >> disch_then $ qspec_then ‘f’ mp_tac >> impl_tac
  >- (
    rpt conj_tac >> rpt strip_tac >> res_tac
    >- drule_then MATCH_ACCEPT_TAC limTheory.DIFF_CONT
    >> qexists_tac ‘f' x’ >> first_x_assum irule
    >> gs[REAL_LT_IMP_LE])
  >> rpt strip_tac
  >> ‘(f diffl f' z) z’ by (first_x_assum irule >> gs[REAL_LT_IMP_LE])
  >> ‘f' z = l’
    by (drule limTheory.DIFF_UNIQ >> disch_then $ qspec_then ‘l’ mp_tac >> gs[])
  >> rpt VAR_EQ_TAC
  >> qexists_tac ‘z’ >> gs[]
QED

(** intervals where cosine is negative **)

Theorem cos_pi2_pi_le:
  ∀ x.
    pi / 2 ≤ x ∧ x ≤ pi ⇒
    cos x ≤ 0
Proof
  rpt strip_tac >> Cases_on ‘x = pi/2’
  >- (VAR_EQ_TAC >> gs[COS_PI2])
  >> ‘pi/2 < x’ by real_tac
  >> qspecl_then [‘cos’, ‘λ x. - sin x’, ‘pi/2’, ‘x’] mp_tac MVT_ALT
  >> impl_tac
  >- gs[BETA_THM, DIFF_COS]
  >> BETA_TAC >> rewrite_tac[COS_PI2, REAL_SUB_RZERO]
  >> rpt strip_tac
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_LE_ZERO_MUL2 >> reverse conj_tac
  >- real_tac
  >> rewrite_tac[REAL_NEG_LE0]
  >> irule SIN_POS_PI_LE >> conj_tac
  >- (transitivity_for ‘x’ >> gs[REAL_LE_LT])
  >> transitivity_for ‘pi/2’ >> gs[REAL_LE_LT, PI2_BOUNDS]
QED

Theorem cos_negpi_negpi2_le:
  ∀ x.
    - pi ≤ x ∧ x ≤ - (pi / 2) ⇒
    cos x ≤ 0
Proof
  rpt strip_tac >> Cases_on ‘- (pi/2) = x’
  >- (VAR_EQ_TAC >> gs[COS_NEG, COS_PI2])
  >> ‘x < - (pi / 2)’ by real_tac
  >> qspecl_then [‘cos’, ‘λ x. - sin x’, ‘x’, ‘- (pi/2)’] mp_tac MVT_ALT
  >> impl_tac
  >- gs[BETA_THM, DIFF_COS]
  >> BETA_TAC >> rewrite_tac[COS_PI2, COS_NEG, REAL_SUB_LZERO]
  >> rpt strip_tac
  >> ‘0:real = -0’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_NEG_LE2
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_LE_MUL >> conj_tac
  >- real_tac
  >> rewrite_tac[GSYM SIN_NEG]
  >> ‘pi/2 ≤ - z’ by real_tac
  >> ‘-z ≤ pi’ by real_tac
  >> irule SIN_POS_PI_LE >> conj_tac >- gs[]
  >> transitivity_for ‘pi/2’ >> gs[REAL_LE_LT, PI2_BOUNDS]
QED

(** intervals where sine is negative**)

Theorem SIN_NEGPI:
  sin (- pi) = 0
Proof
  gs[SIN_NEG, SIN_PI]
QED

Theorem SIN_NEGPI2:
  sin (- (pi/2)) = -1
Proof
  gs[SIN_NEG, SIN_PI2]
QED

Theorem sin_negpi2_0_le:
  ∀ x.
    - (pi/2) ≤ x ∧ x ≤ 0 ⇒
    sin x ≤ 0
Proof
  rpt strip_tac >> Cases_on ‘x = 0’
  >- gs[SIN_0]
  >> ‘x < 0’ by real_tac
  >> qspecl_then [‘sin’, ‘cos’, ‘x’, ‘0’] mp_tac MVT_ALT
  >> impl_tac
  >- gs[BETA_THM, DIFF_SIN]
  >> BETA_TAC >> rewrite_tac[SIN_0, REAL_SUB_LZERO]
  >> rpt strip_tac
  >> ‘0 = - 0:real’ by real_tac
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_NEG_LE2
  >> pop_assum $ once_rewrite_tac o single
  >> rewrite_tac [GSYM REAL_NEG_LMUL]
  >> irule REAL_NEG_LE2 >> real_rw ‘- 0 = 0:real’
  >> irule REAL_LE_ZERO_MUL1 >> conj_tac
  >- real_tac
  >> irule COS_POS_PI_LE >> conj_tac
  >- (transitivity_for ‘0’ >> gs[REAL_LE_LT, PI2_BOUNDS])
  >> transitivity_for ‘x’ >> gs[REAL_LE_LT]
QED

Theorem sin_negpi_negpi2_le:
  ∀ x.
    - pi ≤ x ∧ x ≤ - (pi / 2) ⇒
    sin x ≤ 0
Proof
  rpt strip_tac >> Cases_on ‘x = - pi’
  >- (VAR_EQ_TAC >> gs[SIN_NEGPI])
  >> ‘- pi < x ’ by real_tac
  >> qspecl_then [‘sin’, ‘cos’, ‘- pi’, ‘x’] mp_tac MVT_ALT
  >> impl_tac
  >- gs[BETA_THM, DIFF_SIN]
  >> BETA_TAC >> rewrite_tac[SIN_NEGPI, REAL_SUB_RZERO]
  >> rpt strip_tac
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_LE_ZERO_MUL2 >> reverse conj_tac
  >- real_tac
  >> irule cos_negpi_negpi2_le >> conj_tac
  >- (transitivity_for ‘x’ >> gs[REAL_LE_LT])
  >> gs[REAL_LE_LT]
QED

Theorem sin_negpi_0_le:
  ∀ x.
    - pi ≤ x ∧ x ≤ 0 ⇒
    sin x ≤ 0
Proof
  rpt strip_tac >> Cases_on ‘x ≤ - (pi / 2)’
  >- (irule sin_negpi_negpi2_le >> gs[])
  >> irule sin_negpi2_0_le
  >> gs[REAL_NOT_LE, REAL_LE_LT]
QED

(** monotonicity of cosine **)

Theorem cos_incr_negpi_0:
  ∀ x y.
    - pi ≤ x ∧ x ≤ 0 ∧
    - pi ≤ y ∧ y ≤ 0 ∧
    x ≤ y ⇒
    cos x ≤ cos y
Proof
  rpt strip_tac >> irule DIFF_INC >> conj_tac >- gs[]
  >> qexists_tac ‘0’ >> qexists_tac ‘- pi’
  >> reverse conj_tac >- gs[]
  >> rpt strip_tac >> qexists_tac ‘- sin z’
  >> gs[DIFF_COS, sin_negpi_0_le]
QED

Theorem cos_decr_0_pi:
  ∀ x y.
    0 ≤ x ∧ x ≤ pi ∧
    0 ≤ y ∧ y ≤ pi ∧
    x ≤ y ⇒
    cos y ≤ cos x
Proof
  rpt strip_tac >> irule DIFF_DEC_LE >> conj_tac >- gs[]
  >> qexists_tac ‘pi’ >> qexists_tac ‘0’
  >> reverse conj_tac >- gs[]
  >> rpt strip_tac >> qexists_tac ‘- sin z’
  >> gs[DIFF_COS, SIN_POS_PI_LE]
QED

Theorem cos_decr_0_pi_lt:
  ∀ x y.
    0 < x ∧ x < pi ∧
    0 < y ∧ y < pi ∧
    x < y ⇒
    cos y < cos x
Proof
  rpt strip_tac >> irule DIFF_DEC_LT >> conj_tac >- gs[]
  >> qexists_tac ‘pi’ >> qexists_tac ‘0’
  >> conj_tac
  >- (
    rpt strip_tac >> qexists_tac ‘- sin z’
    >> gs[DIFF_COS, SIN_POS_PI])
  >> reverse conj_tac >- gs[]
  >> rpt strip_tac >> irule limTheory.DIFF_CONT
  >> qexists_tac ‘- sin z’ >> gs[DIFF_COS]
QED

Theorem sin_incr_0_pi2:
  ∀ x y.
    0 ≤ x ∧ x ≤ pi/2 ∧
    0 ≤ y ∧ y ≤ pi/2 ∧
    x ≤ y ⇒
    sin x ≤ sin y
Proof
  rpt strip_tac >> irule DIFF_INC >> conj_tac >- gs[]
  >> qexists_tac ‘pi/2’ >> qexists_tac ‘0’ >> reverse conj_tac
  >- gs[]
  >> gen_tac >> qexists_tac ‘cos z’
  >> rpt strip_tac >- gs[DIFF_SIN]
  >> irule COS_POS_PI2_LE >> gs[]
QED

Theorem sin_incr_negpi2_0:
  ∀ x y.
    - pi / 2 ≤ x ∧ x ≤ 0 ∧
    - pi / 2 ≤ y ∧ y ≤ 0 ∧
    x ≤ y ⇒
    sin x ≤ sin y
Proof
  rpt strip_tac >> qspecl_then [‘-y’, ‘-x’] mp_tac sin_incr_0_pi2
  >> impl_tac
  >> gs[REAL_NEG_LE1, SIN_NEG]
QED

Theorem sin_decr_pi2_pi:
  ∀ x y.
    pi/2 ≤ x ∧ x ≤ pi ∧
    pi/2 ≤ y ∧ y ≤ pi ∧
    x ≤ y ⇒
    sin y ≤ sin x
Proof
  rpt strip_tac >> irule DIFF_DEC_LE >> conj_tac >- gs[]
  >> qexists_tac ‘pi’ >> qexists_tac ‘pi / 2’ >> reverse conj_tac
  >- gs[]
  >> gen_tac >> qexists_tac ‘cos z’
  >> rpt strip_tac >- gs[DIFF_SIN]
  >> irule cos_pi2_pi_le >> gs[]
QED

Theorem sin_decr_negpi_negpi2:
  ∀ x y.
    - pi ≤ x ∧ x ≤ - (pi/2) ∧
    - pi ≤ y ∧ y ≤ - (pi/2) ∧
    x ≤ y ⇒
    sin y ≤ sin x
Proof
  rpt strip_tac >> qspecl_then [‘-y’, ‘-x’] mp_tac sin_decr_pi2_pi
  >> impl_tac
  >> rpt conj_tac >> gs[REAL_NEG_LE1, REAL_NEG_LE2, SIN_NEG]
QED

Theorem cos_decreasing:
  ∀ x y.
    0 < x ∧ x < pi ∧
    0 < y ∧ y < pi ∧
    cos x ≤ cos y ⇒
    y ≤ x
Proof
  rpt strip_tac >> CCONTR_TAC >> gs[REAL_NOT_LE]
  >> qspecl_then [‘x’, ‘y’] mp_tac cos_decr_0_pi_lt
  >> impl_tac >- gs[]
  >> strip_tac >> real_tac
QED

Theorem PI2_lt_PI:
  (pi / &2) < pi
Proof
  gs[]
  >> ‘0 < pi ==> pi < 2 * pi’   by REAL_ARITH_TAC
  >> first_assum irule
  >> gs[PI_POS]
QED

Theorem ATN_0:
  atn(&0) = &0
Proof
  ‘atn(&0) = atn(tan(&0))’ by
    ( ‘tan(&0) = &0’ by gs[TAN_0]
      >> gs[]
    )
  >> pop_assum $ rewrite_tac o single
  >> irule TAN_ATN
  >> gs[PI_POS]
QED

Theorem  DIFF_ISCONST_END_SIMPLE:
 !f a b. a < b /\
           (!x. a <= x /\ x <= b ==> (f diffl &0)(x))
         ==> (f b = f a)
Proof
  REPEAT STRIP_TAC THEN MATCH_MP_TAC limTheory.DIFF_ISCONST_END THEN
  mesonLib.ASM_MESON_TAC[limTheory.DIFF_CONT, REAL_LT_IMP_LE]
QED

Theorem ERR_ABS_SIMP:
  abs (a - b) <= err ==>
  b <= a + err /\
  a - err <= b /\
  a <= b + err /\
  b - err <= a
Proof
  strip_tac >> rpt conj_tac >> real_tac
QED

Theorem EXP_MINUS_ONE_POS:
  ! x. 0 <= x ==>
  0 <= exp x - 1
Proof
  rpt strip_tac
  >> gs[REAL_SUB_LE]
  >> transitivity_for ‘exp 0’
  >> gs[EXP_0, EXP_MONO_LE]
QED

(** Ported from HOL-Light **)
Theorem TAN_PI4:
  tan(pi / &4) = &1
Proof
  REWRITE_TAC[tan, COS_SIN, real_div, GSYM REAL_SUB_LDISTRIB] >> gs[]
  >> once_rewrite_tac [REAL_MUL_SYM]
  >> rewrite_tac [REAL_INV_1OVER]
  >> rewrite_tac[EVAL “1 / 2 - 1 / (4:real)”]
  >> rewrite_tac [GSYM REAL_INV_1OVER]
  >> ‘inv 4 * pi = pi * inv 4’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> irule REAL_MUL_RINV
  >> rewrite_tac[SIN_ZERO]
  >> rewrite_tac[real_div, GSYM REAL_MUL_LNEG]
  >> simp[REAL_MUL_LID, REAL_EQ_MUL_LCANCEL, PI_POS]
  >> rpt strip_tac
  >> ‘0 < pi / 2’ by gs[PI2_BOUNDS]
  >> ‘0 < pi’ by gs[]
  >> gs[]
QED

Theorem ATN_1:
  atn(&1) = pi / &4
Proof
  MP_TAC(AP_TERM “atn” TAN_PI4)
  >> DISCH_THEN(SUBST1_TAC o SYM)
  >> irule TAN_ATN
  >> gs[PI2_BOUNDS] >> conj_tac >> gs[PI_POS]
QED

Theorem ATN_MONO_LT:
 ∀ x y. x < y ⇒ atn x < atn y
Proof
  rpt strip_tac
  >> qspecl_then [‘atn’, ‘λ x. inv (1 + x pow 2)’, ‘x’, ‘y’] mp_tac MVT_ALT
  >> BETA_TAC >> gs[DIFF_ATN]
  >> strip_tac
  >> FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
    “(l:real - r = d) ==> l < d + e ==> r < e”))
  >> REWRITE_TAC[REAL_ARITH “a < b + a <=> &0 < b:real”]
  >> MATCH_MP_TAC REAL_LT_MUL
  >> ASM_REWRITE_TAC[REAL_LT_SUB_LADD, REAL_ADD_LID]
  >> REWRITE_TAC[REAL_LT_INV_EQ]
  >> MATCH_MP_TAC(REAL_ARITH “&0 <= x ==> &0 < &1 + x:real”)
  >> REWRITE_TAC[POW_2, REAL_LE_SQUARE]
QED

Theorem ATN_NEG:
  ∀ x. atn(-x) = -(atn x)
Proof
  GEN_TAC THEN MP_TAC(Q.SPEC `atn(x)` TAN_NEG) THEN
  REWRITE_TAC[ATN_TAN] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC TAN_ATN THEN
  MATCH_MP_TAC(REAL_ARITH
   “-a < x /\ x < a ⇒ -a < -x ∧ -x < a:real”) THEN
  REWRITE_TAC[ATN_BOUNDS]
QED

Theorem ATN_LT_PI4_POS:
 ∀ x. x < &1 ⇒ atn(x) < pi / &4
Proof
  rewrite_tac [GSYM ATN_1]
  >> gs[ATN_MONO_LT]
QED

Theorem ATN_LT_PI4_NEG:
  ∀ x. -(&1) < x ⇒ -(pi / &4) < atn(x)
Proof
  rewrite_tac [GSYM ATN_1, GSYM ATN_NEG]
  >> gs[ATN_MONO_LT]
QED

Theorem abs_exists:
  abs (x - y) ≤ eps ⇒
  ∃ d. y = x + d ∧ abs d ≤ eps
Proof
  rpt strip_tac
  >> qexists_tac ‘y - x’ >> conj_tac >> real_tac
QED

Theorem pow_simp:
  x * x = x pow 2 /\ x pow n * x = x pow (SUC n)
Proof
  gs[pow]
QED

Theorem REAL_ABS_TRIANGLE_PRE:
  ! (lb:real) ub tr p1 p2 v err1 err2.
  (! x. lb <= x /\ x <= ub ==> abs (optionGet (interp tr [(v, x)]) - evalPoly p1 x) <= err1) ==>
  (! x. lb <= x /\ x <= ub ==> abs (evalPoly p1 x - evalPoly p2 x) <= err2) ==>
  (! x. lb <= x /\ x <= ub ==> abs (optionGet (interp tr [(v, x)]) - evalPoly p2 x) <= err1 + err2)
Proof
  rpt strip_tac >> res_tac
  >> ntac 2 $ pop_assum mp_tac
  >> qmatch_goalsub_abbrev_tac ‘abs (r2 - r3) <= err2’ >> strip_tac
  >> qmatch_goalsub_abbrev_tac ‘abs (r1 - r2) <= err1’ >> strip_tac
  >> ‘r1 - r3 = (r1 - r2) + (r2 - r3)’ by real_tac
  >> pop_assum $ rewrite_tac o single
  >> transitivity_for ‘abs (r1 - r2) + abs (r2 - r3)’
  >> gs[REAL_ABS_TRIANGLE] >> irule REAL_LE_ADD2
  >> gs[]
QED

Theorem IMP_SPLIT:
(! x. xlo <= x /\ x <= xhi ==> (P x /\ Q x)) <=>
((! x. xlo <= x /\ x <= xhi ==> P x) /\ (! x. xlo <= x /\ x <= xhi ==> Q x))
Proof
  rpt strip_tac >> EQ_TAC >> rpt strip_tac >> res_tac >> gs[]
QED

val _ = export_theory();

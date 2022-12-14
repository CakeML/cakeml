(**
  Some simple properties of polynomials on reals
**)
open realTheory realLib RealArith renameTheory polyTheory;
open realPolyTheory;
open preambleDandelion;

val _ = new_theory "realPolyProofs";

(**
  Evaluation properties
**)
Triviality evalPoly_neg = SIMP_RULE std_ss [polyEvalsTo_def] polyEvalsTo_Neg
Triviality evalPoly_add = SIMP_RULE std_ss [polyEvalsTo_def] polyEvalsTo_Add
Triviality evalPoly_sub = SIMP_RULE std_ss [polyEvalsTo_def] polyEvalsTo_Sub
Triviality evalPoly_mulcst = SIMP_RULE std_ss [polyEvalsTo_def] polyEvalsTo_MulCst
Triviality evalPoly_mul = SIMP_RULE std_ss [polyEvalsTo_def] polyEvalsTo_Mul
Triviality evalPoly_pow = SIMP_RULE std_ss [polyEvalsTo_def] polyEvalsTo_Pow

Theorem eval_simps = LIST_CONJ [evalPoly_neg, evalPoly_add, evalPoly_sub,
                                evalPoly_mulcst, evalPoly_mul, evalPoly_pow]

val field_prove = gs[eval_simps] >> real_tac;

(**
  Identities
**)
Theorem mul_cst1:
  (1 *c p) = reduce p
Proof
  Induct_on ‘p’ >> gs[poly_mul_cst_def, reduce_def, poly_mul_cst_aux_def]
  >> rpt strip_tac >> cond_cases_tac >> gs[]
QED

Theorem mul_cst_1:
  reduce p = p ⇒
  1 *c p = p
Proof
  Induct_on ‘p’
  >- gs[poly_mul_cst_def, reduce_def, poly_mul_cst_aux_def]
  >> rpt strip_tac
  >> gs[poly_mul_cst_def]
  >> ‘reduce p = p’
    by (gs[reduce_def] >> pop_assum mp_tac >> rpt (COND_CASES_TAC >> gs[]))
  >> gs[poly_mul_cst_aux_def, reduce_def]
QED

Theorem evalPoly_mul_cst1:
  ∀ p x.
    evalPoly (1 *c p) x = evalPoly p x
Proof
  gs[evalPoly_mulcst]
QED

Theorem poly_mul_cst_0:
  0 *c p = []
Proof
  Induct_on ‘p’ >- EVAL_TAC
  >> rpt strip_tac >> gs[poly_mul_cst_def, Once poly_mul_cst_aux_def, reduce_def]
QED

Theorem mul_0_right[compute]:
  (p *p []) = []
Proof
  Induct_on ‘p’ >> gs[poly_mul_def]
  >> rpt strip_tac >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
  >> cond_cases_tac >> gs[poly_add_def, poly_add_aux_def, reduce_def]
QED

Theorem mul_0_left[compute]:
  ([] *p p) = []
Proof
  Induct_on ‘p’
  >- gs[mul_0_right]
  >> strip_tac
  >> gs[poly_mul_def]
QED

Theorem poly_cst_mult_nul:
  ∀a. (a *c []) = []
Proof
  strip_tac >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
QED

Theorem poly_add_rid:
  ∀p. [] +p p = reduce p
Proof
  Induct_on ‘p’
  >- gs[poly_add_def, poly_add_aux_def, reduce_def]
  >> strip_tac
  >> gs[poly_add_def, poly_add_aux_def]
QED

(**
  Algebraic properties
**)
Theorem evalPoly_add_comm:
  ∀ p1 p2 x.
    evalPoly (p1 +p p2) x = evalPoly (p2 +p p1) x
Proof
  field_prove
QED

Theorem evalPoly_add_assoc:
  ∀ p1 p2 p3 x.
    evalPoly (p1 +p (p2 +p p3)) x = evalPoly ((p1 +p p2) +p p3) x
Proof
  field_prove
QED

Theorem evalPoly_mul_comm:
  ∀ p1 p2 x.
    evalPoly (p1 *p p2) x = evalPoly (p2 *p p1) x
Proof
  gs[evalPoly_mul] >> real_tac
QED

Theorem evalPoly_mul_assoc:
  ∀ p1 p2 p3 x.
    evalPoly (p1 *p (p2 *p p3)) x = evalPoly ((p1 *p p2) *p p3) x
Proof
  gs[evalPoly_mul] >> real_tac
QED

Theorem evalPoly_mul_distrib_l:
  ∀ p1 p2 p3 x.
    evalPoly (p1 *p (p2 +p p3)) x = evalPoly ((p1 *p p2) +p (p1 *p p3)) x
Proof
  gs[evalPoly_mul, evalPoly_add] >> real_tac
QED

Theorem poly_mul_cst_reduce:
  c *c reduce p = c *c p
Proof
  Induct_on ‘p’ >> gs[poly_mul_cst_def]
  >- gs[reduce_def, poly_mul_cst_aux_def]
  >> strip_tac >> gs[reduce_def, poly_mul_cst_aux_def]
  >> Cases_on ‘reduce p’ >> gs[]
  >- (
    Cases_on ‘h = 0’ >> gs[]
    >> qpat_x_assum `reduce (poly_mul_cst_aux _ _) = _` $ rewrite_tac o single o GSYM
    >> gs[poly_mul_cst_aux_def, reduce_def])
  >> qpat_x_assum `reduce (poly_mul_cst_aux _ _) = _` $ rewrite_tac o single o GSYM
  >> gs[poly_mul_cst_aux_def, reduce_def]
QED

(** Properties of deg function **)

Theorem deg_oEL:
  ∀ p n.
    deg p < n ⇒
    oEL n p = NONE ∨ oEL n p = SOME 0
Proof
  Induct_on ‘p’ >> gs[deg_def, reduce_def, oEL_def]
  >> rpt strip_tac
  >> Cases_on ‘reduce p = []’ >> gs[]
  >- (
    Cases_on ‘n’ >> gs[]
    >> rename1 ‘oEL n p = NONE’
    >> Cases_on ‘n’ >> gs[]
    >> Cases_on ‘oEL 0 p’ >> gs[]
    >> ‘∃ y ys. p = y::ys’ by (Cases_on ‘p’ >> gs[oEL_def])
    >> VAR_EQ_TAC >> gs[oEL_def, reduce_def]
    >> Cases_on ‘reduce ys = []’ >> gs[]
    >> Cases_on ‘x = 0’ >> gs[])
  >> Cases_on ‘n’ >> gs[]
  >> rename1 ‘oEL n p = NONE’
  >> Cases_on ‘n’ >> gs[]
  >> Cases_on ‘p’ >> gs[reduce_def, oEL_def]
  >> Cases_on ‘reduce t = []’ >> gs[]
  >> Cases_on ‘h = 0’ >> gs[]
QED

Theorem coeff_eq_0:
  ∀ p n.
    deg p < n ⇒
    coeff p n = 0
Proof
  rpt strip_tac >> drule deg_oEL
  >> gs[coeff_def] >> strip_tac >> gs[]
QED

Theorem le_degree:
  ∀ p n.
    coeff p n ≠ 0 ⇒ n ≤ deg p
Proof
  CCONTR_TAC >> gs[]
  >> ‘deg p < n’ by gs[]
  >> imp_res_tac coeff_eq_0
QED

(** Properties of monom function **)

Theorem monom_n:
  ∀ n. coeff (monom n [p]) n = p
Proof
  Induct_on ‘n’ >> gs[coeff_def, monom_def, monom_def, oEL_def]
QED

Theorem monom_SUC:
  monom (SUC n) p = 0 :: monom n p
Proof
  gs[monom_def, monom_def]
QED

Theorem monom_0_mul:
  ∀ n p. monom n [0] *p p = []
Proof
  Induct_on ‘n’
  >- gs[monom_def, monom_def, poly_mul_def, poly_mul_cst_0, poly_add_def,
        reduce_def, poly_add_aux_def]
  >> gs[Once monom_SUC] >> rpt strip_tac
  >> gs[Once poly_mul_def, poly_mul_cst_0]
  >> COND_CASES_TAC >> gs[poly_add_def, reduce_def, poly_add_aux_def]
QED

(** Properties of coeff function **)

Theorem coeff_monom_0_mul:
  ∀ n m p. coeff (monom n [0] *p p) m = 0
Proof
  gs[monom_0_mul, coeff_def, oEL_def]
QED

Theorem coeff_empty:
  coeff [] n = 0
Proof
  gs[coeff_def, oEL_def]
QED

Theorem deg_le:
  ∀ p n.
    (∀ i. n < i ⇒ coeff p i = 0) ⇒
    deg p ≤ n
Proof
  Induct_on ‘n’
  >- (
    Induct_on ‘p’ >> gs[deg_def, reduce_def]
    >> rpt strip_tac >> cond_cases_tac
    >- (cond_cases_tac >> gs[])
    >> gs[]
    >> ‘∀ i. 0 < i ⇒ coeff p i = 0’
      by (
      rpt strip_tac
      >> res_tac
      >> gs[coeff_def]
      >> first_x_assum $ qspec_then ‘SUC i’ mp_tac >> gs[oEL_def])
    >> res_tac
    >> Cases_on ‘p’ >> gs[reduce_def]
    >> last_x_assum $ qspec_then ‘1’ mp_tac
    >> gs[coeff_def, oEL_def] >> rpt strip_tac
    >> ‘reduce t = []’ by (Cases_on ‘reduce t’ >> gs[])
    >> gs[])
  >> rpt strip_tac
  >> Cases_on ‘p’ >> gs[deg_def, reduce_def]
  >> ‘∀ i. n < i ⇒ coeff t i = 0’
    by (
      rpt strip_tac
      >> ‘SUC n < SUC i’ by gs[]
      >> res_tac >> fs[coeff_def, oEL_def])
  >> res_tac
  >> rpt (cond_cases_tac >> fs[])
QED

Theorem eq_zero_or_degree_less:
  ∀ p n.
    deg p ≤ n ∧ coeff p n = 0 ⇒
    zerop p  ∨ deg p < n
Proof
  rpt strip_tac >> Cases_on ‘n’
  >- (
    ‘coeff p (deg p) = 0’ by gs[]
    >> ‘deg p = 0’ by gs[]
    >> Cases_on ‘p’ >> gs[deg_def, coeff_def, oEL_def, zerop_def, reduce_def]
    >> Cases_on ‘reduce t’ >> gs[])
  >> rename1 ‘deg p ≤ SUC m’
  >> ‘∀ i. SUC m < i ⇒ coeff p i = 0’
    by (rpt strip_tac
        >> ‘deg p < i’ by gs[]
        >> imp_res_tac coeff_eq_0)
  >> ‘∀ i. SUC m ≤ i ⇒ coeff p i = 0’
     by (gs[LESS_OR_EQ] >> rpt strip_tac >> gs[])
  >> ‘∀ i. m < i ⇒ coeff p i = 0’ by gs[]
  >> imp_res_tac deg_le
  >> gs[]
QED

Theorem coeff_0_degree_minus_1:
  coeff p n = 0 ∧ deg p ≤ n ⇒ deg p ≤ n - 1
Proof
  rpt strip_tac
  >> ‘zerop p ∨ deg p < n’ by (drule_then drule eq_zero_or_degree_less >> gs[])
  >- gs[zerop_def, deg_def]
  >> gs[]
QED

Theorem coeff_cst_mul:
  ∀c p n. coeff (c *c p) n = c * coeff p n
Proof
  gen_tac >>
  ‘c = 0 ∨ c ≠ 0’ by gs[]
  >- ( pop_assum $ rewrite_tac o single >> gs[poly_mul_cst_0, coeff_empty] )
  >> Induct_on ‘n’
  >- ( gs[coeff_def] >> gs[poly_mul_cst_def]
       >> Induct_on ‘p’
       >- gs[oEL_def, poly_mul_cst_aux_def, reduce_def]
       >> strip_tac >> gs[oEL_def] >> gs[poly_mul_cst_aux_def]
       >> gs[reduce_def] >> cond_cases_tac
       >- ( cond_cases_tac >> gs[oEL_def] )
       >> gs[oEL_def]
       >> gs[oEL_def]
     )
  >> strip_tac
  >> gs[coeff_def] >> Induct_on ‘p’
  >- gs[poly_cst_mult_nul, oEL_def]
  >> strip_tac >> gs[poly_mul_cst_def] >> gs[poly_mul_cst_aux_def]
  >> gs[reduce_def] >> cond_cases_tac
  >- ( gs[oEL_def] >> cond_cases_tac
       >- ( gs[oEL_def]
            >> qpat_x_assum ‘ ∀p'. _ ’ $  qspec_then ‘p’ assume_tac
            >> gs[oEL_def]
          )
       >> gs[oEL_def]
       >> qpat_x_assum ‘∀p'. _’ $ qspec_then ‘p’ assume_tac
       >> gs[oEL_def]
     )
  >> gs[oEL_def]
QED

Theorem coeff_add:
  ∀p1 p2 n. coeff (p1 +p p2) n = coeff p1 n + coeff p2 n
Proof
  Induct_on ‘n’
  >- ( rpt strip_tac >> gs[coeff_def, oEL_def]
       >> Cases_on ‘p1’
       >- ( gs[oEL_def, poly_add_rid]
            >> Induct_on ‘p2’
            >- gs[reduce_def, oEL_def]
            >> strip_tac >> gs[reduce_def]
            >> cond_cases_tac
            >- ( gs[oEL_def] >> cond_cases_tac >> gs[oEL_def] )
            >> gs[oEL_def]
          )
       >> gs[oEL_def] >> Induct_on ‘p2’
       >- ( gs[poly_add_def, poly_add_aux_def] >> gs[reduce_def, oEL_def]
            >> cond_cases_tac
            >- ( cond_cases_tac >> gs[oEL_def] )
            >> gs[oEL_def]
          )
       >> strip_tac >> gs[oEL_def]
       >> gs[poly_add_def, poly_add_aux_def]
       >> gs[reduce_def] >> cond_cases_tac
       >- ( cond_cases_tac >> gs[oEL_def] )
       >> gs[oEL_def]
     )
  >> rpt strip_tac >> gs[coeff_def]
  >> Cases_on ‘p1’
  >- ( gs[oEL_def, poly_add_rid]
       >> Induct_on ‘p2’
       >- gs[reduce_def, oEL_def]
       >> strip_tac >> gs[reduce_def]
       >> cond_cases_tac
       >- ( gs[oEL_def] >> cond_cases_tac >> gs[oEL_def]
            >> last_x_assum $ qspecl_then [‘[]’, ‘p2’] assume_tac
            >> gs[poly_add_rid, oEL_def]
          )
       >> gs[oEL_def]
       >> last_x_assum $ qspecl_then [‘[]’, ‘p2’] assume_tac
       >> gs[poly_add_rid, oEL_def]
     )
  >> gs[oEL_def] >> Induct_on ‘p2’
  >- ( gs[poly_add_lid]
       >> gs[oEL_def] >> gs[reduce_def]
       >> cond_cases_tac
       >- ( cond_cases_tac >> gs[oEL_def]
            >> last_x_assum $ qspecl_then [‘[]’, ‘t’] assume_tac
            >> gs[poly_add_rid, oEL_def]
          )
       >> gs[oEL_def]
       >> last_x_assum $ qspecl_then [‘[]’, ‘t’] assume_tac
       >> gs[poly_add_rid, oEL_def]
     )
  >> strip_tac >> gs[oEL_def]
  >> gs[poly_add_def, poly_add_aux_def]
  >> gs[reduce_def] >> cond_cases_tac
  >- ( cond_cases_tac >> gs[oEL_def]
       >> last_x_assum $ qspecl_then [‘t’, ‘p2’] assume_tac
       >> gs[oEL_def]
     )
  >> gs[oEL_def]
QED

Theorem length_gt_0:
  ∀ t. t ≠ [] ⇒ 0 < LENGTH t
Proof
  Induct_on ‘t’
  >- gs[]
  >> rpt strip_tac
  >> gs[LENGTH]
QED

Theorem deg_suc:
  ∀p. 0 < deg p ⇒
      deg (h::p) = SUC (deg p)
Proof
  rpt strip_tac
  >> gs[deg_def, reduce_def]
  >> cond_cases_tac >> gs[LENGTH]
QED

Theorem deg_1:
  ∀p. deg p = 0 ⇒ 0 < deg (h::p) ⇒ deg (h::p) = 1
Proof
  gs[deg_def]
  >> Induct_on ‘p’
  >- ( gs[reduce_def, LENGTH] >> cond_cases_tac >> gs[])
  >> rpt strip_tac
  >> gs[reduce_def]
  >> Cases_on ‘reduce p = []’
  >- ( gs[] >> Cases_on ‘h' = 0’ >> gs[] )
  >> gs[] >> last_x_assum mp_tac >> gs[]
  >> ‘∀m:num. 0 < m ⇒ 1 ≤ m’ by gs[]
  >> first_assum irule
  >> gs[length_gt_0]
QED

Theorem deg_length:
  ∀p. 0 < deg p ⇒
      LENGTH (reduce p) > 1
Proof
  Induct_on ‘p’
  >- gs[deg_def, reduce_def, LENGTH]
  >> gs[deg_def]
QED

Theorem deg_p_ge_0:
  ∀p. p ≠ [] ⇒ 0 ≤ deg p
Proof
  Induct_on ‘p’
  >- gs[]
  >> rpt strip_tac
  >> gs[deg_def]
QED

Theorem deg_eq_arg:
  ∀ x y p. deg (x::p) = 0 ∧ deg p = 0 ⇒
  deg (y::p) = 0
Proof
  Induct_on ‘p’
  >- (gs[deg_def, reduce_def] >> rpt strip_tac >> COND_CASES_TAC >> gs[])
  >> rpt strip_tac
  >> gs[deg_def, reduce_def]
  >> Cases_on ‘reduce p = []’ >> gs[]
  >> Cases_on ‘h = 0’ >> gs[]
  >> COND_CASES_TAC >> gs[]
QED

Theorem coeff_single:
  coeff [x] (deg [x]) = x
Proof
  gs[deg_def, coeff_def, reduce_def]
  >> Cases_on ‘x = 0’ >> gs[oEL_def]
QED

Theorem deg_single:
  deg [x] = 0
Proof
  gs[deg_def, reduce_def]
  >> Cases_on ‘x = 0’ >> gs[]
QED

Theorem coeff_cons:
  0 < deg (x::p) ⇒
    coeff (x::p) (deg (x::p)) = coeff p (deg p)
Proof
  rpt strip_tac >> gs[coeff_def, oEL_def]
  >> ‘deg (x::p) = SUC (deg p)’
    by (gs[deg_def, reduce_def] >> every_case_tac >> gs[])
  >> gs[]
QED

Theorem deg_pos:
  0 < deg (x::p) ⇒
    deg (x::p) = 1 + deg p
Proof
  gs[deg_def, reduce_def]
  >> rpt (cond_cases_tac >> gs[])
QED

Theorem reduce_mult:
  reduce p *p q = p *p q
Proof
  Induct_on ‘p’ >> gs[reduce_def]
  >> rpt strip_tac
  >> Cases_on ‘reduce p’ >> gs[]
  >- (
    Cases_on ‘h = 0’ >> gs[] >> rpt VAR_EQ_TAC
    >- (
      simp[SimpR“$=”, poly_mul_def, poly_mul_cst_0, poly_add_rid]
      >> Cases_on ‘p’ >> gs[mul_0_left ,reduce_def])
    >> gs[poly_mul_def, poly_add_lid]
    >> cond_cases_tac >> gs[poly_add_lid])
  >> gs[poly_mul_def]
  >> ‘p ≠ []’ by (Cases_on ‘p’ >> gs[reduce_def])
  >> gs[]
QED

Theorem mult_zerop_l:
  zerop p ⇒
  p *p q = []
Proof
  rpt strip_tac >> gs[zerop_def] >> once_rewrite_tac [GSYM reduce_mult] >> gs[mul_0_left]
QED

Theorem coeff_mult_degree_sum:
  ∀ p q. coeff (p *p q) (deg p + deg q) = coeff p (deg p) * coeff q (deg q)
Proof
  Induct_on ‘p’ >> gs[poly_mul_def]
  >- gs[coeff_empty]
  >> Cases_on ‘p’ >> gs[]
  >> rpt strip_tac
  >- gs[poly_add_lid, poly_mul_cst_reduced, mul_0_left, coeff_empty,
        coeff_single, deg_single, coeff_cst_mul]
  >> gs[coeff_add, coeff_cst_mul]
  >> rename1 ‘x1 * coeff q (deg q + deg (x1::x2::p))’
  >> ‘deg q < deg q + deg (x1::x2::p) ∨
      (deg q = deg q + deg (x1::x2::p) ∧ deg (x1::x2::p) = 0)’
     by (gs[deg_def, reduce_def]
         >> Cases_on ‘reduce p’ >> gs[]
         >> Cases_on ‘x2 = 0’ >> gs[]
         >> Cases_on ‘x1 = 0’ >> gs[])
  >- (
    imp_res_tac coeff_eq_0 >> gs[]
    >> ‘0 < deg q + deg (x1::x2::p)’ by gs[]
    >> ‘∃ n. deg q + deg (x1::x2::p) = SUC n’
      by (Cases_on ‘deg q + deg (x1::x2::p)’ >> gs[])
    >> gs[SimpL “$=”, coeff_def, oEL_def]
    >> first_x_assum $ qspec_then ‘q’ mp_tac
    >> gs[coeff_cons]
    >> disch_then $ rewrite_tac o single o GSYM
    >> gs[deg_pos] >> ‘n = deg q + deg (x2::p)’ by gs[]
    >> VAR_EQ_TAC >> gs[])
  >> fs[coeff_def, oEL_def]
  >> ‘deg (x2::p) = 0’ by (gs[deg_def, reduce_def] >> every_case_tac >> gs[])
  >> ‘x2 = 0’ by (gs[deg_def, reduce_def]
                  >> Cases_on ‘reduce p’ >> gs[]
                  >> Cases_on ‘x2 = 0’ >> gs[])
  >> ‘zerop (x2::p)’
    by (
    ‘coeff (x2::p) 0 = 0’ by (gs[coeff_def, oEL_def])
    >> imp_res_tac eq_zero_or_degree_less >> gs[])
  >> gs[mult_zerop_l, oEL_def]
  >> cond_cases_tac >> gs[]
QED

(**
  Properties of deg
**)

Theorem deg_monom_eq:
  a ≠ 0 ⇒ deg (monom n [a]) = n
Proof
  Induct_on ‘n’ >> gs[monom_def, monom_def, deg_def, reduce_def]
  >> rpt strip_tac >> res_tac
  >> COND_CASES_TAC >- gs[reduce_def, monom_def]
  >> Cases_on ‘reduce (monom n [a])’ >> gs[]
QED

Theorem reduce_p_poly_mul_holds:
  ∀p. reduce p = [] ⇒
      reduce (poly_mul_cst_aux c p) = []
Proof
  Induct_on ‘p’
  >- gs[poly_mul_cst_aux_def, reduce_def]
  >> rpt strip_tac
  >> gs[poly_mul_cst_aux_def]
  >> gs[reduce_def]
  >> pop_assum mp_tac
  >> cond_cases_tac
  >- ( res_tac >> gs[] >> cond_cases_tac >> gs[] )
  >> gs[]
QED

Theorem reduce_poly_mul_cst:
  ∀ c p. reduce p = [] ⇒
       c *c p = []
Proof
  gs[poly_mul_cst_def, reduce_p_poly_mul_holds]
QED

Theorem reduce_p_poly_mul_holds_not:
  ∀p. c ≠ 0 ⇒ reduce p ≠ [] ⇒
      reduce (poly_mul_cst_aux c p) ≠ []
Proof
  Induct_on ‘p’
  >- gs[reduce_def]
  >> rpt strip_tac
  >> pop_assum mp_tac >> gs[]
  >> gs[poly_mul_cst_aux_def]
  >> gs[reduce_def]
  >> pop_assum mp_tac
  >> cond_cases_tac
  >- ( gs[reduce_p_poly_mul_holds] >> cond_cases_tac >> gs[] )
  >> gs[]
QED

Theorem deg_leq_mul_cst:
  deg (c *c p) ≤ deg p
Proof
  ‘c = 0 ∨ c ≠ 0’ by gs[]
  >- ( pop_assum $ rewrite_tac o single >> gs[poly_mul_cst_0]
       >> ‘deg [] = 0’ by
         ( gs[deg_def, reduce_def] )
       >> pop_assum $ rewrite_tac o single
       >> gs[deg_def]
     )
  >> gs[deg_def]
  >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_idempotent]
  >> Induct_on ‘p’
  >- gs[poly_mul_cst_aux_def, reduce_def]
  >> gs[poly_mul_cst_aux_def] >> strip_tac
  >> gs[reduce_def]
  >> Cases_on ‘reduce p = []’
  >- (
    gs[reduce_p_poly_mul_holds]
    >> cond_cases_tac >> gs[]
  )
  >> gs[reduce_p_poly_mul_holds_not]
  >> ‘∀m n:num. m ≤ n ⇒ SUC m ≤ n+1’ by gs[]
  >> first_x_assum irule
  >> ‘1 ≤ LENGTH (reduce p) ⇒
      LENGTH (reduce p) = 1 + (LENGTH (reduce p) - 1) ’ by gs[]
  >> ‘ 1 ≤ LENGTH (reduce p)’ by
    ( qpat_x_assum ‘reduce p ≠ []’ mp_tac
      >> POP_ASSUM_LIST kall_tac
      >> strip_tac
      >> Induct_on ‘p’
      >- gs[reduce_def]
      >> rpt strip_tac
      >> gs[reduce_def]
      >> cond_cases_tac
      >- (
        gs[] >> cond_cases_tac
        >- gs[]
        >> gs[LENGTH]
      )
      >> gs[LENGTH]
    )
  >> res_tac
  >> gs[]
QED

Theorem deg_of_const_mul:
  ∀ c p.  c ≠ 0 ⇒ deg (c *c p) = deg p
Proof
  rpt strip_tac
  >> gs[deg_def] >> gs[poly_mul_cst_reduced]
  >> gs[poly_mul_cst_def, poly_mul_cst_aux_def]
  >> Induct_on ‘p’
  >- gs[poly_mul_cst_aux_def, reduce_def, LENGTH]
  >> gs[poly_mul_cst_aux_def] >> gs[reduce_def]
  >> Cases_on ‘reduce p = []’
  >- ( gs[reduce_p_poly_mul_holds] >> strip_tac >> cond_cases_tac >> gs[LENGTH] )
  >> strip_tac
  >> gs[reduce_p_poly_mul_holds_not]
  >> ‘∀m n:num. 0 < m ∧ 0 < n ⇒ m - 1 = n - 1 ⇒ m = n’ by gs[]
  >> first_assum irule >> rpt conj_tac
  >- gs[length_gt_0,reduce_p_poly_mul_holds_not]
  >> gs[length_gt_0]
  >> gs[]
QED

Theorem reduce_h_not_null:
  ∀h. reduce [h] ≠ [] ⇒ h ≠ 0
Proof
  rpt strip_tac
  >> last_assum mp_tac
  >> gs[reduce_def]
QED

Theorem reduce_0_scal:
  ∀h:real. reduce (0 :: [h]) ≠ [] ⇒ reduce [h] ≠ []
Proof
  rpt strip_tac >> gs[reduce_def]
QED

Theorem deg_0_scal:
  ∀h. h ≠ 0 ⇒ deg (0 :: [h]) = 1
Proof
  rpt strip_tac
  >> gs[deg_def, reduce_def]
QED

Theorem reduce_add_zero_r:
  ∀ p1 p2. reduce p2 = [] ⇒
           reduce (poly_add_aux p1 p2) = reduce p1
Proof
  Induct_on ‘p1’ >> gs[poly_add_aux_def, reduce_def]
  >> rpt strip_tac >> res_tac
  >> Cases_on ‘p2’ >> gs[reduce_def]
  >> Cases_on ‘reduce t’ >> gs[]
  >> Cases_on ‘h' = 0’ >> gs[]
QED

Theorem reduce_add_zero_l:
  ∀p1 p2.
    reduce p1 = [] ⇒
    reduce (poly_add_aux p1 p2) = reduce p2
Proof
  Induct_on ‘p1’ >> rpt strip_tac
  >- gs[reduce_def, poly_add_aux_def]
  >> gs[poly_add_aux_def]
  >> Cases_on ‘p2’
  >- gs[reduce_def]
  >> gs[] >> gs[reduce_def]
  >> Cases_on ‘reduce t = []’ >> gs[]
  >- (
    Cases_on ‘reduce p1 = []’ >> gs[]
    >> Cases_on ‘h=0’ >> gs[]
    >> Cases_on ‘reduce (poly_add_aux p1 t) = []’ >> gs[]
    >> cond_cases_tac
    >> gs[reduce_add_zero_r])
  >> Cases_on ‘reduce p1 = []’ >> gs[reduce_add_zero_r]
  >> Cases_on ‘h=0’ >> gs[]
QED


Theorem reduce_add_zero_r:
  ∀p1 p2.
    reduce p2 = [] ⇒
    reduce (poly_add_aux p1 p2) = reduce p1
Proof
  Induct_on ‘p1’
  >- gs[poly_add_aux_def, reduce_def]
  >> rpt strip_tac
  >> gs[poly_add_aux_def]
  >> Cases_on ‘p2’
  >- gs[]
  >> gs[] >> gs[reduce_def]
  >> Cases_on ‘reduce p1 = []’
  >- ( gs[reduce_add_zero_l]
       >> Cases_on ‘reduce t = []’
       >- ( gs[] >> Cases_on ‘h=0’
            >- gs[]
            >> gs[] >> Cases_on ‘h' = 0’ >> gs[]
          )
       >> gs[]
     )
  >> gs[]
  >> Cases_on ‘reduce t = []’
  >- ( gs[] >> Cases_on ‘h' = 0’ >> gs[] )
  >> gs[]
QED

Theorem mult_zerop_r:
  ∀p q. zerop q ⇒ p *p q = []
Proof
  Induct_on ‘p’
  >- gs[mul_0_left ]
  >> rpt strip_tac
  >> gs[zerop_def, poly_mul_def]
  >> Cases_on ‘p = []’
  >> gs[poly_add_lid, poly_mul_cst_reduced]
  >> ‘ h *c q = h *c reduce q’ by gs[poly_mul_cst_reduce]
  >> gs[poly_cst_mult_nul]
QED

Theorem reduce_poly_add_not_null:
  ∀ p q. reduce p ≠ [] ⇒ reduce q ≠ [] ⇒
         deg p < deg q ⇒
         reduce (poly_add_aux p q) ≠ []
Proof
  Induct_on ‘p’
  >- gs[reduce_def]
  >> rpt strip_tac
  >> gs[poly_add_aux_def]
  >> Cases_on ‘q’
  >- gs[]
  >> gs[] >> gs[reduce_def, deg_def]
  >> Cases_on ‘reduce t = []’
  >- ( gs[reduce_add_zero_r]
       >> Cases_on ‘h' = 0’
       >- gs[]
       >> gs[]
     )
  >> gs[]
  >> Cases_on ‘reduce p = []’
  >- gs[reduce_add_zero_l]
  >> gs[]
  >> last_x_assum $ qspec_then ‘t’ assume_tac
  >> gs[]
  >> Cases_on ‘reduce (poly_add_aux p t) = []’
  >- ( gs[]
       >> ‘LENGTH (reduce t) = 1’ by
         ( ‘0 < LENGTH(reduce t)’ by gs[length_gt_0]
           >> gs[]
         )
       >> last_x_assum mp_tac
       >> gs[]
       >> ‘∀m:num. 1 ≤ m ⇒ ~ ( m < 1)’ by gs[]
       >> pop_assum irule
       >> ‘0 < LENGTH(reduce p)’ by gs[length_gt_0]
       >> gs[]
     )
  >> gs[]
QED

Theorem deg_cast :
  ∀ p1 p2. deg p1 < deg p2 ⇒
           deg (reduce (poly_add_aux p1 p2)) = deg p2
Proof
  Induct_on ‘p1’
  >- ( gs[poly_add_aux_def]
       >> rpt strip_tac
       >> gs[deg_def, reduce_idempotent]
     )
  >> rpt strip_tac
  >> gs[poly_add_aux_def]
  >> Cases_on ‘p2’
  >- ( gs[] >> gs[deg_def, reduce_def] )
  >> gs[] >> gs[deg_def, reduce_def]
  >> Cases_on ‘reduce t = []’
  >- ( gs[reduce_add_zero_r] >> cond_cases_tac
       >-  ( gs[] >> Cases_on ‘h'=0’
             >- ( gs[] >> cond_cases_tac >> gs[reduce_def, LENGTH] )
             >> gs[] >> cond_cases_tac >> gs[reduce_def, LENGTH]
           )
       >> gs[reduce_def, reduce_idempotent]
       >> Cases_on ‘h'=0’
       >- gs[]
       >> gs[]
     )
  >> gs[]
  >> Cases_on ‘reduce p1 = []’
  >- ( gs[reduce_add_zero_l]
       >> gs[reduce_def, reduce_idempotent]
     )
  >> last_x_assum $ qspec_then ‘t’ assume_tac
  >> gs[]
  >> ‘reduce (poly_add_aux p1 t) ≠ []’ by
    ( irule reduce_poly_add_not_null >> gs[]
      >> ‘deg p1 = LENGTH (reduce p1) - 1’ by gs[deg_def]
      >> pop_assum $ rewrite_tac o single
      >> ‘deg t = LENGTH (reduce t) - 1’ by gs[deg_def]
      >> pop_assum $ rewrite_tac o single
      >> ‘∀ m n:num. 0 < m ⇒ 0 < n ⇒ m < n ⇒ m - 1 < n-1’ by gs[]
      >> first_assum irule >> gs[length_gt_0]
    )
  >> gs[reduce_def, reduce_idempotent]
  >> ‘∀m n:num. 0 < m ∧ 0 < n ⇒ m-1 = n-1 ⇒ m = n’ by gs[]
  >> pop_assum irule >> gs[] >> conj_tac
  >- ( irule length_gt_0 >> gs[] )
  >> ‘1 < LENGTH (reduce t)’ by
    ( ‘∀m n: num. m -1  < n - 1 ⇒ m < n ’ by gs[]
      >> pop_assum irule
      >> ‘1-1 = 0 ’ by gs[]
      >> gs[]
      >> irule LESS_LESS_EQ_TRANS
      >> qexists_tac ‘LENGTH (reduce p1)’
      >> gs[length_gt_0]
    )
  >> first_assum irule >> gs[]
QED

Theorem length_reduce_eq:
  ∀ h p. reduce p ≠ [] ⇒ h ≠ 0 ⇒ LENGTH (h *c reduce p) = LENGTH (reduce p)
Proof
  rpt strip_tac
  >> ‘∀m n:num. 0 < m ⇒ 0 < n ⇒ m - 1 = n -1 ⇒ m = n’ by gs[]
  >> first_assum irule
  >> ‘ LENGTH (reduce (h *c p)) - 1 = deg (h *c p) ’ by gs[deg_def]
  >> ‘LENGTH (reduce p) -1 = deg p ’ by gs[deg_def]
  >> gs[poly_mul_cst_reduced, poly_mul_cst_reduce ]
  >> gs[deg_of_const_mul]
  >> gs[length_gt_0]
  >> irule length_gt_0
  >> gs[poly_mul_cst_def]
  >> pop_assum kall_tac
  >> pop_assum kall_tac
  >> gs[reduce_p_poly_mul_holds_not]
QED

Theorem reduce_mul_zero_r:
  ∀ p1 p2.
    reduce p2 = [] ⇒
    p1 *p p2 = []
Proof
  Induct_on ‘p1’ >> gs[poly_mul_def]
  >> rpt strip_tac
  >> gs[reduce_poly_mul_cst, poly_add_rid]
  >> cond_cases_tac >> gs[reduce_def]
QED

Theorem reduce_mul_zero_l:
  ∀ p1 p2.
    reduce p1 = [] ⇒
    p1 *p p2 = []
Proof
  Induct_on ‘p1’ >> gs[poly_mul_def]
  >> rpt strip_tac
  >> ‘h = 0’ by (gs[reduce_def] >> every_case_tac >> gs[])
  >> gs[poly_mul_cst_0, poly_add_rid]
  >> ‘reduce p1 = []’ by (gs[reduce_def] >> every_case_tac >> gs[])
  >> cond_cases_tac >> gs[reduce_def]
QED

Theorem reduce_poly_mul_cst_not_null:
  ∀ p1 c.
    reduce p1 ≠ [] ∧
    c ≠ 0 ⇒
    c *c p1 ≠ []
Proof
  Induct_on ‘p1’ >> gs[reduce_def]
  >> rpt strip_tac >> Cases_on ‘reduce p1’
  >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
  >> imp_res_tac reduce_p_poly_mul_holds >> gs[]
  >> Cases_on ‘h = 0’ >> gs[]
QED

Theorem deg_reduce:
  deg (reduce p) = deg p
Proof
  gs[deg_def, reduce_idempotent]
QED

Theorem deg_add_poly:
  ∀ p1 p2. deg (p1 +p p2) ≤ MAX (deg p1) (deg p2)
Proof
  Induct_on ‘p1’
  >- (gs[poly_add_rid, deg_reduce])
  >> rpt strip_tac
  >> gs[poly_add_def, poly_add_aux_def, deg_reduce]
  >> Cases_on ‘p2’ >> gs[deg_def, reduce_def]
  >> Cases_on ‘reduce (poly_add_aux p1 t) = []’ >> gs[]
  >- (Cases_on ‘h + h' = 0’ >> gs[])
  >> Cases_on ‘reduce p1 = []’ >> gs[]
  >- (Cases_on ‘h = 0’ >> gs[reduce_add_zero_l])
  >> first_x_assum $ qspec_then ‘t’ assume_tac
  >> gs[]
  >- (
    DISJ1_TAC
    >> ‘LENGTH (reduce (poly_add_aux p1 t)) ≤ LENGTH (reduce p1)’ suffices_by gs[]
    >> ‘0 < LENGTH (reduce p1)’ by (Cases_on ‘reduce p1’ >> gs[])
    >> gs[])
  >> Cases_on ‘reduce t = []’ >> gs[]
  >- (
    DISJ1_TAC
    >> ‘LENGTH (reduce (poly_add_aux p1 t)) ≤ LENGTH (reduce p1)’ suffices_by gs[]
    >> ‘1 ≤ LENGTH (reduce p1)’ by (Cases_on ‘reduce p1’ >> gs[])
    >> gs[])
  >> DISJ2_TAC
  >> ‘LENGTH (reduce (poly_add_aux p1 t)) ≤ LENGTH (reduce t)’ suffices_by gs[]
  >> ‘0 < LENGTH (reduce t)’ by (Cases_on ‘reduce t’ >> gs[])
  >> ‘1 + (LENGTH (reduce t) - 1) = LENGTH (reduce t)’ by gs[]
  >> gs[]
QED

Theorem deg_poly_neg:
  deg (--p p) = deg p
Proof
  gs[poly_neg_def, deg_of_const_mul]
QED

Theorem deg_sub_poly:
  deg (p1 -p p2) ≤ MAX (deg p1) (deg p2)
Proof
  once_rewrite_tac[poly_sub_def]
  >> qspecl_then [‘p1’, ‘--p p2’] assume_tac deg_add_poly
  >> gs[deg_poly_neg]
QED

Theorem deg_mul_poly:
  ∀ p1 p2.
    deg (p1 *p p2) ≤
    if (zerop p1 ∨ zerop p2) then 0 else deg p1 + deg p2
Proof
  Induct_on ‘p1’
  >> rpt strip_tac
  >> gs[zerop_def]
  >- gs[deg_def, reduce_def, mul_0_left]
  >> cond_cases_tac >> gs[]
  >- ( gs[poly_mul_def]
       >> Cases_on ‘h=0’
       >- ( gs[poly_mul_cst_0, poly_add_rid]
            >> gs[reduce_def]
            >> Cases_on ‘reduce p1 = []’
            >- ( gs[] >> Cases_on ‘p1 = []’
                 >- gs[deg_def, reduce_def, LENGTH]
                 >> gs[] >> gs[reduce_def]
                 >> ‘reduce (p1 *p p2) = []’ by
                   ( gs[poly_mul_reduced] >> irule mult_zerop_l
                     >> gs[zerop_def]
                   )
                 >> gs[deg_def, reduce_def, LENGTH]
               )
            >> gs[]
          )
       >> Cases_on ‘p1 = []’
       >- gs[reduce_def]
       >> gs[poly_add_def] >> gs[reduce_def]
       >> ‘reduce (0::(p1 *p p2)) = []’ by
         ( gs[reduce_def] >> Cases_on ‘reduce p1 = []’
           >- gs[]
           >> gs[]
         )
       >> gs[reduce_add_zero_r, poly_mul_cst_reduced]
       >> gs[deg_of_const_mul]
       >> last_x_assum $ qspec_then ‘p2’ assume_tac
       >> ‘reduce p1 = []’ by
         ( gs[reduce_def] >> Cases_on ‘reduce p1 = []’
           >- gs[]
           >> gs[]
         )
       >> gs[] >> gs[deg_def]
       >> gs[reduce_def]
     )
  >- ( gs[poly_mul_def]
       >> Cases_on ‘h=0’
       >- ( gs[poly_mul_cst_0, poly_add_rid]
            >> Cases_on ‘p1 = []’
            >- gs[reduce_def, deg_def, LENGTH]
            >> gs[]
            >> ‘reduce (0::(p1 *p p2)) = []’ by
              ( gs[reduce_def]
                >> ‘reduce (p1 *p p2) = []’ by
                  ( gs[poly_mul_reduced] >> irule mult_zerop_r
                    >> gs[zerop_def]
                  )
                >> gs[]
              )
            >> gs[deg_def, reduce_def, LENGTH]
          )
       >> gs[] >> Cases_on ‘p1 = []’
       >- ( gs[poly_add_def]
            >> ‘reduce (poly_add_aux (h *c p2) []) = reduce (h *c p2)’
              by ( irule reduce_add_zero_r >> gs[reduce_def] )
            >> gs[poly_mul_cst_reduced,deg_of_const_mul ]
            >> gs[deg_def]
          )
       >> gs[poly_add_def]
       >> ‘reduce (0::(p1 *p p2)) = []’ by
         ( gs[reduce_def]
           >> ‘reduce (p1 *p p2) = []’ by
             ( gs[poly_mul_reduced] >> irule mult_zerop_r
               >> gs[zerop_def]
             )
           >> gs[]
         )
       >> gs[reduce_add_zero_r, poly_mul_cst_reduced]
       >> gs[deg_of_const_mul]
       >> gs[deg_def]
     )
  >> gs[poly_mul_def]
  >> Cases_on ‘p1 = []’
  >- ( gs[poly_add_lid, poly_mul_cst_reduced]
       >> Cases_on ‘h=0’
       >- ( gs[poly_mul_cst_0] >> gs[deg_def, reduce_def] )
       >> gs[deg_of_const_mul]
       >> ‘deg [h] = 0’ by gs[deg_def, reduce_def, LENGTH]
       >> gs[]
     )
  >> gs[]
  >> last_x_assum $ qspec_then ‘p2’ assume_tac
  >> gs[]
  >> Cases_on ‘reduce p1 = []’
  >- ( gs[poly_add_def]
       >> ‘p1 *p p2 = []’ by
         ( irule mult_zerop_l >> gs[zerop_def] )
       >> gs[]
       >> ‘reduce (poly_add_aux t []) = reduce t’ by
         ( irule reduce_add_zero_r >> gs[reduce_def] )
       >> gs[poly_add_aux_lid]
       >> Cases_on ‘h=0’
       >- ( gs[poly_mul_cst_0] >> gs[reduce_def, deg_def] )
       >> ‘ h *c p2 ≠ []’ by
         gs[poly_mul_cst_def, reduce_p_poly_mul_holds_not]
       >> gs[]
       >> gs[poly_mul_cst_reduced]
       >> gs[deg_of_const_mul]
       >> ‘deg (h :: p1) = 0’ by gs[deg_def, reduce_def]
       >> gs[]
     )
  >> irule LESS_EQ_TRANS
  >> qexists_tac ‘MAX (deg (h *c p2)) (deg (0::(p1 *p p2)))’
  >> gs[deg_add_poly]
  >> conj_tac
  >- (
    Cases_on ‘h = 0’ >> gs[poly_mul_cst_0, deg_of_const_mul, deg_def, reduce_def])
  >> gs[deg_def, reduce_def]
  >> cond_cases_tac >> gs[]
  >> irule LESS_EQ_TRANS
  >> qexists_tac ‘SUC (1 + (LENGTH (reduce p1) - 1 + (LENGTH (reduce p2) - 1)))’
  >> gs[]
  >> once_rewrite_tac [LESS_OR_EQ] >> DISJ2_TAC >> gs[SUC_ONE_ADD]
  >> ‘0 < LENGTH (reduce p1) ∧ 0 < LENGTH (reduce p2)’ by gs[length_gt_0]
  >> gs[]
QED

Theorem reduce_monom_0:
  reduce (monom n [0]) = []
Proof
  Induct_on ‘n’ >> gs[reduce_def, monom_def]
QED

Theorem deg_monom_0:
  deg (monom n [0]) = 0
Proof
  gs[monom_def]
  >> Induct_on ‘n’
  >> gs[monom_def, deg_def, reduce_def]
  >> cond_cases_tac
  >> gs[LENGTH, reduce_monom_0]
QED

Theorem deg_coeff_zerop:
  deg p = 0 ∧
  coeff p 0 = 0 ⇒
  zerop p
Proof
  rpt strip_tac >> CCONTR_TAC
  >> gs[zerop_def, deg_def]
  >> Cases_on ‘reduce p’ >> gs[]
  >> ‘t = []’ by (Cases_on ‘t’ >> gs[])
  >> VAR_EQ_TAC >> gs[coeff_def]
  >> Cases_on ‘p’ >> gs[reduce_def]
  >> Cases_on ‘reduce t’ >> gs[oEL_def]
QED

Theorem poly_sub_id:
  ∀ p1. p1 -p p1 = []
Proof
  Induct_on ‘p1’ >> gs[poly_sub_def, poly_add_rid, reduce_def,
                       poly_neg_def, poly_mul_cst_def, poly_mul_cst_aux_def]
  >> rpt strip_tac
  >> gs[poly_add_def]
  >> cond_cases_tac >> gs[]
  >- (
    cond_cases_tac >> gs[poly_add_aux_lid, poly_add_aux_def, reduce_def]
    >> ‘h + -1 * h = 0’ by real_tac
    >> gs[])
  >> ‘h + -1 * h = 0’ by real_tac
  >> gs[poly_add_aux_def, reduce_def]
QED

Theorem poly_add_comm:
  ∀ p1 p2.
    p1 +p p2 = p2 +p p1
Proof
  Induct_on ‘p1’ >> gs[poly_add_def, poly_add_aux_def, poly_add_aux_lid]
  >> rpt strip_tac
  >> Cases_on ‘p2’ >> gs[poly_add_aux_def, reduce_def]
  >> ‘h + h' = h' + h’ by gs[REAL_ADD_COMM]
  >> pop_assum $ once_rewrite_tac o single
  >> pop_assum $ qspec_then ‘t’ $ once_rewrite_tac o single
  >> gs[]
QED

Theorem reduce_add_l:
  ∀ p1 p2. reduce p1 +p p2 = p1 +p p2
Proof
  Induct_on ‘p1’ >> gs[reduce_def, poly_add_def, poly_add_aux_def, poly_add_rid]
  >> rpt strip_tac >> cond_cases_tac >> gs[]
  >- (
    cond_cases_tac >> gs[]
    >> last_x_assum $ qspec_then ‘p2’ assume_tac >> gs[poly_add_aux_def]
    >> pop_assum $ once_rewrite_tac o single o GSYM
    >> Cases_on ‘p2’ >> gs[reduce_def]
    >> cond_cases_tac >> gs[reduce_add_zero_l])
  >> Cases_on ‘p2’ >> gs[poly_add_aux_lid, reduce_def, reduce_idempotent,
                         poly_add_aux_def]
QED

Theorem reduce_add_r = ONCE_REWRITE_RULE [poly_add_comm] reduce_add_l

Theorem reduce_add_aux_l = ONCE_REWRITE_RULE [poly_add_def] reduce_add_l

Theorem reduce_add_aux_r = ONCE_REWRITE_RULE [poly_add_def] reduce_add_r

Theorem reduce_poly_reduced:
  ∀ p x q. reduce p = x :: q ⇒ reduce q = q
Proof
  Induct_on ‘p’ >> gs[reduce_def]
  >> rpt strip_tac >> Cases_on ‘reduce p’ >> gs[] >> rpt VAR_EQ_TAC
  >- (Cases_on ‘h = 0’ >> gs[reduce_def])
  >> gs[reduce_idempotent]
QED

Theorem poly_add_assoc:
  ∀ p1 p2 p3.
    p1 +p (p2 +p p3) = (p1 +p p2) +p p3
Proof
  Induct_on ‘p1’
  >- (
    Cases_on ‘p2’ >> rpt strip_tac
    >- gs[poly_add_def, poly_add_aux_lid, poly_add_aux_def, reduce_idempotent,
          reduce_def]
    >> gs[poly_add_rid, poly_add_reduced, reduce_add_l])
  >> rpt strip_tac >> gs[poly_add_def, reduce_add_aux_l, reduce_add_aux_r, poly_add_aux_def]
  >> Cases_on ‘p2’ >> gs[poly_add_aux_lid, poly_add_aux_def]
  >- (
    Cases_on ‘p3’ >> gs[poly_add_aux_lid, poly_add_aux_def, reduce_def]
    >> Cases_on ‘reduce t’ >> gs[reduce_add_zero_r]
    >- (Cases_on ‘h' = 0’ >> gs[reduce_def, poly_add_aux_lid])
    >> gs[reduce_def]
    >> ‘reduce (poly_add_aux p1 t) = reduce (poly_add_aux p1 (h'' :: t'))’
      by (qpat_x_assum ‘reduce _ = _’ $ once_rewrite_tac o single o GSYM
          >> gs[reduce_add_aux_r])
    >> pop_assum $ rewrite_tac o single
    >> Cases_on ‘h + h' = 0’ >> gs[])
  >> Cases_on ‘p3’ >> gs[poly_add_aux_lid, poly_add_aux_def, reduce_def]
  >- (
    Cases_on ‘reduce t’ >> gs[reduce_add_zero_r]
    >- (Cases_on ‘h' = 0’ >> gs[reduce_def, poly_add_aux_lid])
    >> ‘reduce (poly_add_aux p1 t) = reduce (poly_add_aux p1 (h'' :: t'))’
      by (qpat_x_assum ‘reduce _ = _’ $ once_rewrite_tac o single o GSYM
          >> gs[reduce_add_aux_r])
    >> pop_assum $ rewrite_tac o single
    >> Cases_on ‘h + h' = 0’ >> gs[reduce_def])
  >> first_x_assum $ qspecl_then [‘t’, ‘t'’] $ rewrite_tac o single o GSYM
  >> Cases_on ‘reduce (poly_add_aux t t')’ >> gs[reduce_add_zero_r]
  >- (
    Cases_on ‘h' +  h'' = 0’ >> gs[reduce_def, poly_add_aux_lid]
    >- (
      Cases_on ‘reduce p1’ >> gs[] >> TRY real_tac
      >> Cases_on ‘h = 0’ >> gs[]
      >> ‘h + h' + h'' ≠ 0’ by real_tac
      >> gs[]
      >> real_tac)
    >> Cases_on ‘reduce p1’ >> gs[REAL_ADD_ASSOC])
  >> ‘reduce (poly_add_aux p1 (poly_add_aux t t')) = reduce (poly_add_aux p1 (h'3' :: t''))’
      by (qpat_x_assum ‘reduce _ = _’ $ once_rewrite_tac o single o GSYM
          >> gs[reduce_add_aux_r])
  >> pop_assum $ rewrite_tac o single
  >> gs[reduce_def]
  >> rpt (cond_cases_tac >> gs[REAL_ADD_ASSOC])
QED

Theorem poly_mul_zero_r:
  ∀p. p *p [0] = []
Proof
  Induct_on ‘p’
  >- gs[poly_mul_def]
  >> rpt strip_tac
  >> gs[poly_mul_def]
  >> cond_cases_tac
  >- ( gs[poly_add_lid, poly_mul_cst_reduced, poly_mul_cst_def]
       >> gs[poly_mul_cst_aux_def, reduce_def]
     )
  >> gs[poly_add_lid, poly_mul_cst_reduced]
  >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
QED

Theorem poly_mul_cst_mul_l:
  ∀t. reduce (poly_mul_cst_aux 0 t) = []
Proof
  gen_tac
  >> ‘reduce (poly_mul_cst_aux 0 t) = 0 *c t’ by gs[poly_mul_cst_def]
  >> gs[poly_mul_cst_0]
QED

Theorem poly_mul_scal:
  ∀t h. t *p [h] = reduce (poly_mul_cst_aux h t)
Proof
  Induct_on ‘t’
  >- gs[mul_0_left, poly_mul_cst_aux_def, reduce_def]
  >> rpt strip_tac
  >> gs[poly_mul_def, poly_mul_cst_def, poly_mul_cst_aux_def]
  >> cond_cases_tac
  >- ( gs[poly_add_lid, reduce_def]
       >> cond_cases_tac
       >- gs[reduce_def, poly_mul_cst_aux_def]
       >> gs[poly_mul_cst_aux_def, reduce_def]
     )
  >> gs[reduce_def]
  >> cond_cases_tac
  >- gs[poly_add_rid, reduce_def, reduce_idempotent]
  >> gs[poly_add_def, poly_add_aux_def, reduce_def, reduce_idempotent]
QED

Theorem poly_shift_add:
  ∀p q. reduce (poly_add_aux p q) ≠ [] ⇒
        0 :: (p +p q) = 0 :: p +p 0::q
Proof
  rpt strip_tac
  >> gs[poly_add_def, poly_add_aux_def, reduce_def]
QED

Theorem poly_mul_scal_in:
  ∀ h h' p. h ≠ 0 ∧ h' ≠ 0 ⇒ h *c h'::p = (h * h') :: (h *c p)
Proof
  rpt strip_tac
  >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
  >> cond_cases_tac >> gs[]
QED

Theorem poly_mul_cst_scal_comm:
  ∀h c p. h *c (c *c p) = c *c (h *c p)
Proof
  rpt strip_tac
  >> Cases_on ‘h=0’
  >- gs[poly_mul_cst_0, poly_cst_mult_nul]
  >> Cases_on ‘c=0’
  >- gs[poly_mul_cst_0, poly_cst_mult_nul]
  >> gs[poly_mul_cst_def]
  >> Induct_on ‘p’
  >- gs[poly_mul_cst_aux_def, reduce_def]
  >> gs[poly_mul_cst_aux_def, reduce_def]
  >> gen_tac
  >> Cases_on ‘reduce p = []’
  >- ( gs[reduce_p_poly_mul_holds]
       >> cond_cases_tac
       >> gs[poly_mul_cst_aux_def, reduce_def]
     )
  >> gs[reduce_p_poly_mul_holds_not, poly_mul_cst_aux_def, reduce_def]
QED

Theorem poly_add_aux_comm:
  ∀ p1 p2. reduce (poly_add_aux p1 p2) = reduce (poly_add_aux p2 p1)
Proof
  rpt strip_tac
  >> ‘reduce (poly_add_aux p1 p2) = p1 +p p2’ by gs[poly_add_def]
  >> ‘reduce (poly_add_aux p2 p1) = p2 +p p1’ by gs[poly_add_def]
  >> gs[poly_add_comm]
QED

Theorem poly_add_aux_reduce_add:
  ∀p t. reduce (poly_add_aux t p) = reduce (poly_add_aux t (reduce p))
Proof
  Induct_on ‘p’
  >- gs[reduce_def]
  >> rpt strip_tac
  >> ‘ reduce (poly_add_aux t (h::p)) =  reduce (poly_add_aux (h::p) t)’
    by gs[poly_add_aux_comm]
  >> pop_assum $ rewrite_tac o single
  >> ‘reduce (poly_add_aux t (reduce (h::p))) =
      reduce (poly_add_aux (reduce (h::p)) t)’ by gs[poly_add_aux_comm]
  >> pop_assum $ rewrite_tac o single
  >> gs[reduce_def, poly_add_aux_def]
  >> Cases_on ‘t’
  >- ( gs[reduce_def]
       >> cond_cases_tac
       >- (gs[poly_add_aux_lid] >> cond_cases_tac >> gs[reduce_def])
       >> gs[poly_add_aux_lid, poly_add_aux_def, reduce_def, reduce_idempotent]
     )
  >> gs[reduce_def]
  >> Cases_on ‘reduce p = []’
  >- ( gs[reduce_add_zero_l]
       >> Cases_on ‘h=0’
       >- gs[poly_add_aux_def, reduce_def]
       >> gs[poly_add_aux_def, reduce_def]
     )
  >> gs[poly_add_aux_def, reduce_def]
  >> last_x_assum $ qspec_then ‘t'’ assume_tac
  >> ‘reduce (poly_add_aux (reduce p) t') =
      reduce (poly_add_aux t' (reduce p))’ by gs[poly_add_aux_comm]
  >> pop_assum $ rewrite_tac o single
  >> ‘reduce (poly_add_aux p t') = reduce (poly_add_aux t' p)’ by
    gs[poly_add_aux_comm]
  >> pop_assum $ rewrite_tac o single
  >> gs[]
QED

Theorem poly_mul_cst_aux_reduce_mul:
  ∀ c p. reduce (poly_mul_cst_aux c p) =
         reduce (poly_mul_cst_aux c (reduce p))
Proof
  rpt strip_tac
  >> ‘ reduce (poly_mul_cst_aux c p) = c *c p’ by gs[poly_mul_cst_def]
  >> pop_assum $ rewrite_tac o single
  >> ‘reduce (poly_mul_cst_aux c (reduce p)) = c *c (reduce p)’ by
    gs[poly_mul_cst_def]
  >> pop_assum $ rewrite_tac o single
  >> gs[poly_mul_cst_reduce]
QED

Theorem poly_add_aux_cst_mul_distrib:
  ∀ c t t'.
    reduce (poly_add_aux (reduce (poly_mul_cst_aux c t))
            (reduce (poly_mul_cst_aux c t'))) =
    reduce (poly_mul_cst_aux c (reduce (poly_add_aux t t')))
Proof
  gen_tac
  >> Cases_on ‘c=0’
  >- gs[poly_mul_cst_mul_l, poly_add_aux_lid, reduce_def]
  >> Induct_on ‘t’
  >- ( gs[poly_add_aux_def, poly_mul_cst_aux_def, reduce_def, reduce_idempotent]
       >> gen_tac >> gs[GSYM poly_mul_cst_aux_reduce_mul]
     )
  >> gs[poly_mul_cst_aux_def, poly_add_aux_def, reduce_def]
  >> rpt strip_tac
  >> Cases_on ‘t'’
  >- ( gs[reduce_def]
       >> Cases_on ‘reduce t = []’
       >- ( gs[reduce_p_poly_mul_holds]
            >> Cases_on ‘h=0’
            >- gs[poly_add_aux_def, poly_add_aux_lid, poly_mul_cst_aux_def,
                  reduce_def]
            >> gs[poly_mul_cst_aux_def, reduce_def, poly_add_aux_lid]
          )
       >> gs[reduce_p_poly_mul_holds_not, poly_mul_cst_aux_def, reduce_def,
             poly_add_aux_lid, reduce_idempotent,
             GSYM poly_mul_cst_aux_reduce_mul]
     )
  >> gs[reduce_def]
  >> Cases_on ‘reduce t = []’
  >- ( gs[reduce_p_poly_mul_holds, reduce_add_zero_l, poly_add_aux_def]
       >> Cases_on ‘reduce t'' = []’
       >- ( gs[]
            >> Cases_on ‘h=0’
            >- ( gs[poly_add_aux_def, poly_mul_cst_aux_def, reduce_def,
                    reduce_p_poly_mul_holds]
                 >> Cases_on ‘h'=0’
                 >- gs[poly_mul_cst_aux_def, reduce_def]
                 >> gs[poly_mul_cst_aux_def, reduce_def]
               )
            >> gs[poly_add_aux_def, poly_mul_cst_aux_def, reduce_def,
                    reduce_p_poly_mul_holds]
            >> Cases_on ‘h'=0’
            >- gs[reduce_def, poly_mul_cst_aux_def]
            >> gs[reduce_def, poly_mul_cst_aux_def]
            >> Cases_on ‘h + h' = 0’
            >- ( gs[poly_mul_cst_aux_def, reduce_def]
                 >> ‘c * h + c * h' = 0’ by
                   ( ‘c * h + c * h'  = c * (h + h') ’ by REAL_ARITH_TAC
                     >> gs[]
                   )
                 >> gs[]
               )
            >> gs[poly_mul_cst_aux_def, reduce_def]
            >> ‘c * h + c * h' ≠ 0’ by
              ( ‘c * h + c * h'  = c * (h + h') ’ by REAL_ARITH_TAC
                >> gs[]
              )
            >> gs[] >> REAL_ARITH_TAC
          )
       >> gs[poly_mul_cst_aux_def, reduce_def]
       >> ‘reduce (poly_mul_cst_aux c (reduce t'')) ≠ []’ by
         gs[reduce_p_poly_mul_holds_not, reduce_idempotent]
       >> gs[reduce_p_poly_mul_holds_not]
       >> Cases_on ‘h=0’
       >- gs[poly_add_aux_def, reduce_def]
       >> gs[poly_add_aux_def, reduce_def]
       >> REAL_ARITH_TAC
     )
  >> gs[reduce_p_poly_mul_holds_not, poly_add_aux_def, poly_mul_cst_aux_def,
        reduce_def]
  >> Cases_on ‘reduce (poly_mul_cst_aux c t)’
  >- gs[reduce_p_poly_mul_holds_not]
  >> gs[]
  >> Cases_on ‘reduce t'' = []’
  >- ( gs[reduce_p_poly_mul_holds, reduce_add_zero_r, poly_mul_cst_aux_def,
          reduce_def, GSYM poly_mul_cst_aux_reduce_mul,
          reduce_p_poly_mul_holds_not  ]
       >> Cases_on ‘ h' = 0 ’
       >- ( gs[reduce_def]
            >> Cases_on ‘reduce t' = []’
            >- ( gs[]
                 >> Cases_on ‘h'' = 0’
                 >- ( gs[]
                      >> qpat_x_assum ‘ ∀t'³'. _ ’ $ qspec_then ‘t''’ assume_tac
                      >> gs[poly_add_aux_def]
                      >> Cases_on ‘reduce (poly_mul_cst_aux c t'')’
                      >- ( gs[reduce_def]
                           >> ‘reduce (poly_mul_cst_aux c (poly_add_aux t t'')) =
                               reduce (poly_mul_cst_aux c
                                       (reduce (poly_add_aux t t'')))’
                         by gs[GSYM poly_mul_cst_aux_reduce_mul]
                           >> gs[reduce_add_zero_r]
                           >> gs[GSYM poly_mul_cst_aux_reduce_mul]
                         )
                      >> gs[reduce_def, reduce_p_poly_mul_holds]
                    )
                 >> gs[poly_add_aux_def]
                 >> qpat_x_assum ‘ ∀t'³'. _ ’ $ qspec_then ‘t''’ assume_tac
                 >> Cases_on ‘reduce (poly_mul_cst_aux c t'')’
                 >-  ( gs[reduce_def]
                       >> ‘reduce (poly_mul_cst_aux c (poly_add_aux t t'')) =
                          reduce (poly_mul_cst_aux c (reduce (poly_add_aux t t'')))’
                         by gs[GSYM poly_mul_cst_aux_reduce_mul]
                       >> gs[reduce_add_zero_r]
                       >> gs[GSYM poly_mul_cst_aux_reduce_mul]
                     )
                 >> gs[reduce_def, reduce_p_poly_mul_holds]
               )
            >> gs[]
            >> qpat_x_assum ‘ ∀t'³'. _ ’ $ qspec_then ‘t''’ assume_tac
            >> gs[poly_add_aux_def]
            >> Cases_on ‘reduce (poly_mul_cst_aux c t'')’
            >- ( gs[reduce_def]
                 >> ‘reduce (poly_mul_cst_aux c (poly_add_aux t t'')) =
                     reduce (poly_mul_cst_aux c (reduce (poly_add_aux t t'')))’
                   by gs[GSYM poly_mul_cst_aux_reduce_mul]
                 >> gs[reduce_add_zero_r]
                 >> gs[GSYM poly_mul_cst_aux_reduce_mul]
               )
            >> gs[reduce_def, reduce_p_poly_mul_holds]
          )
       >> gs[reduce_def, poly_add_aux_lid]
       >> Cases_on ‘reduce t' = []’
       >- ( gs[]
            >> Cases_on ‘h'' = 0’
            >- ( gs[]
                 >> qpat_x_assum ‘ ∀t'³'. _ ’ $ qspec_then ‘t''’ assume_tac
                 >> gs[poly_add_aux_def]
                 >> Cases_on ‘reduce (poly_mul_cst_aux c t'')’
                 >- ( gs[reduce_def]
                      >> ‘reduce (poly_mul_cst_aux c (poly_add_aux t t'')) =
                          reduce (poly_mul_cst_aux c
                                  (reduce (poly_add_aux t t'')))’
                        by gs[GSYM poly_mul_cst_aux_reduce_mul]
                      >> gs[reduce_add_zero_r]
                      >> gs[GSYM poly_mul_cst_aux_reduce_mul]
                    )
                 >> gs[reduce_def, reduce_p_poly_mul_holds]
               )
            >> gs[] >> conj_tac
            >- REAL_ARITH_TAC
            >> qpat_x_assum ‘ ∀t'³'. _ ’ $ qspec_then ‘t''’ assume_tac
            >> gs[poly_add_aux_def]
            >> Cases_on ‘reduce (poly_mul_cst_aux c t'')’
            >- ( gs[reduce_def]
                 >> ‘reduce (poly_mul_cst_aux c (poly_add_aux t t'')) =
                     reduce (poly_mul_cst_aux c (reduce (poly_add_aux t t'')))’
                   by gs[GSYM poly_mul_cst_aux_reduce_mul]
                 >> gs[reduce_add_zero_r]
                 >> gs[GSYM poly_mul_cst_aux_reduce_mul]
               )
            >> gs[reduce_def, reduce_p_poly_mul_holds]
          )
       >> gs[reduce_def, poly_add_aux_lid]
       >> conj_tac
       >- REAL_ARITH_TAC
       >> qpat_x_assum ‘ ∀t'³'. _ ’ $ qspec_then ‘t''’ assume_tac
       >> gs[poly_add_aux_def]
       >> Cases_on ‘reduce (poly_mul_cst_aux c t'')’
       >- ( gs[reduce_def]
            >> ‘reduce (poly_mul_cst_aux c (poly_add_aux t t'')) =
                reduce (poly_mul_cst_aux c (reduce (poly_add_aux t t'')))’
              by gs[GSYM poly_mul_cst_aux_reduce_mul]
            >> gs[reduce_add_zero_r]
            >> gs[GSYM poly_mul_cst_aux_reduce_mul]
          )
       >> gs[reduce_def, reduce_p_poly_mul_holds]
     )
  >> gs[reduce_p_poly_mul_holds_not, reduce_def]
  >> Cases_on ‘reduce (poly_add_aux t t'') = []’
  >- ( gs[reduce_p_poly_mul_holds, reduce_idempotent]
       >> Cases_on ‘h + h' = 0’
       >- ( gs[poly_mul_cst_aux_def, reduce_def]
            >> ‘c * h + c * h' = 0’ by
              ( ‘c * h + c * h'  = c * (h + h') ’ by REAL_ARITH_TAC
                >> gs[]
              )
            >> gs[]
          )
       >> gs[poly_mul_cst_aux_def, reduce_def]
       >> ‘c * h + c * h' ≠ 0’ by
         ( ‘c * h + c * h'  = c * (h + h') ’ by REAL_ARITH_TAC
           >> gs[]
         )
       >> gs[] >> REAL_ARITH_TAC
     )
  >> gs[reduce_p_poly_mul_holds_not, reduce_idempotent]
  >> gs[poly_mul_cst_aux_def, reduce_def]
  >> gs[reduce_p_poly_mul_holds_not, reduce_idempotent]
  >> REAL_ARITH_TAC
QED

Theorem poly_mul_cst_distrib:
  ∀ c p1 p2.
    c *c p1 +p c *c p2 = c *c (p1 +p p2)
Proof
  Induct_on ‘p1’ >> rpt strip_tac
  >> ‘c *c [] = []’ by gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
  >- gs[poly_add_rid, poly_mul_cst_reduced, poly_mul_cst_reduce]
  >> Cases_on ‘c=0’
  >- gs[poly_mul_cst_0, poly_add_lid, reduce_def]
  >> Cases_on ‘p2’
  >- gs[poly_add_rid, poly_add_lid, poly_mul_cst_reduced, poly_mul_cst_reduce]
  >> rename1 ‘h1:: p1 +p h2 :: p2’
  >> ‘h1::p1 +p h2::p2 = reduce ((h1 + h2) :: (p1 +p p2))’
     by gs[poly_add_def, poly_add_aux_def, reduce_def, reduce_idempotent]
  >> pop_assum $ once_rewrite_tac o single
  >> ‘c *c (h1::p1) = reduce(c*h1 :: (c *c p1))’
     by gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def, reduce_idempotent]
  >> pop_assum $ once_rewrite_tac o single
  >> ‘c *c (h2::p2) = reduce(c*h2 :: (c *c p2))’
     by gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def, reduce_idempotent]
  >> pop_assum $ once_rewrite_tac o single
  >> gs[reduce_add_l, reduce_add_r]
  >> qmatch_goalsub_abbrev_tac ‘c * h1 :: poly1 +p c * h2 :: poly2’
  >> ‘c * h1 :: poly1 +p c * h2 :: poly2 =
      reduce (c * h1 + c * h2 :: (poly1 +p poly2))’
    by gs[poly_add_def, poly_add_aux_def, reduce_def, reduce_idempotent]
  >> pop_assum $ once_rewrite_tac o single
  >> unabbrev_all_tac
  >> gs[reduce_def, poly_mul_cst_def, reduce_idempotent]
  >> Cases_on ‘reduce (p1 +p p2)’
  >> gs[reduce_p_poly_mul_holds_not, reduce_p_poly_mul_holds]
  >- (
    Cases_on ‘h1 + h2 = 0’ >> gs[]
    >- (‘c * h1 + c * h2 = 0’ suffices_by gs[]
        >> ‘c * (h1 + h2) = 0’ suffices_by real_tac
        >> gs[])
    >> ‘c * h1 + c * h2 ≠ 0’ by (
      CCONTR_TAC >> gs[]
      >>‘ c * (h1 + h2) = 0’ by real_tac
      >> gs[])
    >> gs[reduce_def, poly_mul_cst_aux_def]
    >> real_tac)
  >> simp[Once poly_mul_cst_aux_def, reduce_def]
  >> ‘reduce (poly_mul_cst_aux c (h::t)) ≠ []’ by (
    irule reduce_p_poly_mul_holds_not
    >> first_assum $ once_rewrite_tac o single o GSYM
    >> gs[reduce_idempotent])
  >> gs[] >> conj_tac >- real_tac
  >> qpat_x_assum `reduce (_ +p _ ) = _` $ once_rewrite_tac o single o GSYM
  >> gs[SIMP_RULE std_ss [poly_mul_cst_def] poly_mul_cst_reduce]
QED

Theorem poly_mul_mul_cst:
  ∀ c p1 p2.
    p1 *p (c *c p2) = c *c (p1 *p p2)
Proof
  gen_tac
  >> Cases_on ‘c=0’
  >- gs[poly_mul_cst_0, mul_0_right]
  >> Induct_on ‘p1’
  >- gs[mul_0_left, poly_cst_mult_nul]
  >> gs[poly_mul_def]
  >> Cases_on ‘p1= []’
  >- ( rpt strip_tac
       >> gs[poly_add_lid, poly_mul_cst_reduced, poly_mul_cst_reduce]
       >> gs[poly_mul_cst_scal_comm]
     )
  >> gs[]
  >> rpt strip_tac
  >> ‘c *c (h *c p2 +p 0::(p1 *p p2)) =
      c *c (h *c p2) +p c *c ( 0 :: (p1 *p p2))’ by
    gs[poly_mul_cst_distrib]
  >> pop_assum $ rewrite_tac o single
  >> Cases_on ‘reduce (p1 *p p2) = []’
  >- ( gs[poly_mul_cst_scal_comm]
       >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def,
             reduce_p_poly_mul_holds, poly_add_lid]
     )
  >> ‘0::(c *c (p1 *p p2))  = c *c 0::(p1 *p p2)’ by
    ( gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
      >> gs[reduce_p_poly_mul_holds_not]
    )
  >> gs[poly_mul_cst_scal_comm]
QED

Theorem poly_mul_cst_shift:
  ∀ a b p. b ≠ 0 ∧ a ≠ 0 ⇒
         (a * b) *c p = a *c (b *c p)
Proof
  gen_tac >> gen_tac
  >> Induct_on ‘p’
  >- gs[poly_cst_mult_nul]
  >> rpt strip_tac >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
  >> Cases_on ‘reduce (poly_mul_cst_aux b p) = []’
  >- ( gs[reduce_p_poly_mul_holds, poly_mul_cst_aux_def, reduce_def]
       >> cond_cases_tac
       >- gs[poly_mul_cst_aux_def, reduce_def]
       >> gs[poly_mul_cst_aux_def, reduce_def]
     )
  >> gs[reduce_p_poly_mul_holds_not, poly_mul_cst_aux_def, reduce_def,
        reduce_idempotent]
QED

Theorem poly_mul_cst_pow:
  ∀ c n p.
      c pow n *c (c *c p) = c pow (n + 1) *c p
Proof
  gen_tac
  >> Cases_on ‘c=0’
  >- gs[poly_mul_cst_0, poly_cst_mult_nul, POW_0']
  >> gen_tac
  >> Induct_on ‘n’
  >- ( strip_tac >> gs[pow0, mul_cst1, poly_mul_cst_reduced] )
  >> gs[GSYM SUC_ADD_SYM, pow]
  >> gen_tac
  >> pop_assum $ qspec_then ‘p’ assume_tac
  >> gs[poly_mul_cst_shift]
QED

Theorem reduce_add:
  reduce (p1 +p p2) = p1 +p p2
Proof
  Induct_on ‘p1’
  >- gs[poly_add_def, poly_add_aux_def, reduce_def, reduce_idempotent]
  >> strip_tac
  >> gs[poly_add_def, poly_add_aux_def, reduce_idempotent]
QED

Theorem reduce_mul_cst:
  ∀ p c. reduce (c *c p) = c *c p
Proof
  Induct_on ‘p’ >> gs[poly_mul_cst_def, reduce_def, poly_mul_cst_aux_def, reduce_idempotent]
  >> rpt strip_tac
  >> cond_cases_tac >> gs[reduce_def, reduce_idempotent]
  >> cond_cases_tac >> gs[reduce_def]
QED

Theorem reduce_neg =
        REWRITE_RULE [PROVE [] “(A ⇔ T) ⇔ A”] $ SIMP_CONV std_ss [poly_neg_def, reduce_mul_cst] “reduce (--p p) = --p p”

Theorem reduce_mul_poly:
  ∀ p1 p2.
    reduce (p1 *p p2) = p1 *p p2
Proof
  Induct_on ‘p1’ >> gs[poly_mul_def, reduce_def]
  >> rpt strip_tac
  >> cond_cases_tac >> gs[reduce_add]
QED

Theorem evalPoly_app:
  ∀ p1 p2 x. evalPoly (p1 ++ p2) x = evalPoly p1 x + evalPoly p2 x * x pow (LENGTH p1)
Proof
  Induct_on ‘p1’ >> gs[evalPoly_def]
  >> rpt strip_tac >> pop_assum kall_tac
  >> gs[REAL_LDISTRIB, pow]
  >> real_tac
QED

Theorem compose_correct:
  ∀ p q. evalPoly (compose p q) x = evalPoly p (evalPoly q x)
Proof
  Induct_on ‘p’ >- gs[compose_def, evalPoly_def]
  >> once_rewrite_tac[compose_def]
  >> rewrite_tac [evalPoly_def, eval_simps, REAL_MUL_RZERO, REAL_ADD_RID]
  >> gs[]
QED

Theorem poly_neg_evals:
  ∀p x. poly (--p p) x = - poly p x
Proof
  gs[GSYM poly_compat, eval_simps]
QED

Theorem poly_nill_left_add:
  ∀ p x. poly ([] +p p) x = poly p x
Proof
  gs[poly_add_rid] >> gs[GSYM poly_compat, reduce_preserving]
QED

Theorem poly_reduce_evals:
  ∀ p x. poly (reduce p) x = poly p x
Proof
  gs[GSYM poly_compat, reduce_preserving]
QED

Theorem poly_neg_neg_evals:
  ∀ t. poly (--p (--p t)) = poly t
Proof
  rpt strip_tac >> rewrite_tac[FUN_EQ_THM, GSYM poly_compat, eval_simps]
  >> real_tac
QED

Theorem poly_add_aux_evals:
  ∀p t x. poly (poly_add_aux p t) x = poly p x + poly t x
Proof
  Induct_on ‘p’
  >- gs[poly_add_aux_def, poly_def]
  >> rpt strip_tac >> gs[poly_add_aux_def]
  >> Cases_on ‘t’
  >- gs[poly_add_aux_lid, poly_def]
  >> gs[poly_def]
  >> ‘h + x * poly p x + (h' + x * poly t' x) = h + h' +
        x * (poly p x + poly t' x)’ by REAL_ARITH_TAC
  >> pop_assum $ rewrite_tac o single
QED

Theorem poly_sub_evals:
  ∀ p q x. poly (p -p q) x = poly p x - poly q x
Proof
  gs[GSYM poly_compat, eval_simps]
QED

Theorem poly_cst_evals:
  ∀ p c x. c * poly p x = poly (c *c p) x
Proof
  gs[GSYM poly_compat, eval_simps]
QED

Theorem poly_shift_eval:
  ∀p q. q ≠ [] ⇒ p ≠ [] ⇒ deg q < deg p ⇒
        poly (monom (deg p − deg q) [LAST p / LAST q]) x * poly q x =
        poly (LAST p / LAST q *c monom (deg p − deg q) q) x
Proof
  rpt strip_tac
  >> assume_tac LESS_ADD
  >> pop_assum $ qspecl_then [‘deg p’, ‘deg q’] assume_tac
  >> res_tac
  >> ‘deg p - deg q = p'’ by gs[]
  >> pop_assum $ rewrite_tac o single
  >> pop_assum kall_tac
  >> pop_assum kall_tac
  >> pop_assum kall_tac
  >> Induct_on ‘p'’
  >- (
    gs[monom_def, poly_def]
    >> gs[poly_cst_evals, real_div]
  )
  >> gs[monom_def, poly_def, GSYM poly_cst_evals]
  >> gs[poly_def, GSYM REAL_MUL_ASSOC] >> REAL_ARITH_TAC
QED

Theorem deg_p_not_0:
  ∀p. deg p ≠ 0 ⇒ p ≠ []
Proof
  gen_tac
  >> rpt strip_tac >> CCONTR_TAC
  >> ‘deg p = 0’ suffices_by gs[]
  >> VAR_EQ_TAC
  >> gs[deg_def, reduce_def, LENGTH]
QED

(** Theorem on Euclidean division **)
Theorem poly_const_2_mul:
  ∀ p a b x.
    poly (a ## poly_mul_cst_aux b p) x  =
    poly (poly_mul_cst_aux (a * b) p) x
Proof
  Induct_on ‘p’
  >- ( rpt strip_tac >> gs[poly_mul_cst_aux_def, POLY_CMUL_CLAUSES] )
  >> rpt strip_tac >> gs[poly_mul_cst_aux_def, poly_cmul_def]
  >> gs[REAL_MUL_ASSOC, poly_def]
QED

Theorem poly_cst_one_mul:
  ∀p x. poly (poly_mul_cst_aux 1 p) x = poly p x
Proof
  Induct_on ‘p’
  >- ( gen_tac >> gs[poly_mul_cst_aux_def] )
  >> rpt strip_tac
  >> gs[poly_mul_cst_aux_def, poly_def]
QED

Theorem poly_one_mul:
  ∀ p q. poly (p + 1 ## q) = poly (p + q)
Proof
  gen_tac
  >> Induct_on ‘q’
  >-  gs[POLY_CMUL_CLAUSES]
  >> gen_tac
  >> gs[poly_cmul_def] >> gs[FUN_EQ_THM] >> gen_tac
  >> gs[POLY_ADD, poly_def]
QED

Theorem nonzero_coeff:
  ~ zerop p ⇒
  coeff p (deg p) ≠ 0
Proof
  Induct_on ‘p’ >> gs[deg_def, coeff_def, zerop_def, oEL_def, reduce_def]
  >> Cases_on ‘reduce p’ >> gs[]
  >- (
    rpt strip_tac
    >> Cases_on ‘h = 0’ >> gs[])
  >> ‘SUC (SUC (LENGTH t)) - 2 = LENGTH t’ by gs[]
  >> pop_assum $ rewrite_tac o single >> gs[]
QED

Theorem normalized_normal:
  ~ zerop p ⇒
  coeff ((inv (coeff p (deg p))) *c p) (deg ((inv (coeff p (deg p))) *c p)) = 1
Proof
  Induct_on ‘p’
  >- gs[zerop_def, coeff_def, deg_def, oEL_def, reduce_def, poly_mul_cst_0]
  >> rpt strip_tac
  >> gs[coeff_cst_mul]
  >> Cases_on ‘reduce p’
  >- (
    gs[deg_def, reduce_def, zerop_def]
    >> ‘h ≠ 0’ by (Cases_on ‘h = 0’ >> gs[])
    >> ‘coeff (h::p) 0 = h’ by (gs[coeff_def, oEL_def])
    >> ‘inv h ≠ 0’ by (CCONTR_TAC >> gs[])
    >> gs o single $ SIMP_RULE std_ss [deg_def] deg_of_const_mul
    >> gs[reduce_def, REAL_MUL_LINV])
  >> ‘0 < deg (h::p)’ by gs[deg_def, reduce_def]
  >> gs[coeff_cons]
  >> ‘~ zerop p’ by gs[zerop_def]
  >> imp_res_tac nonzero_coeff
  >> gs[deg_of_const_mul, coeff_cons]
QED

Theorem nonzero_normalize:
  ~ zerop p ⇒
  ~ zerop ((inv (coeff p (deg p))) *c p)
Proof
  Induct_on ‘p’
  >- gs[zerop_def, reduce_def]
  >> rpt strip_tac
  >> Cases_on ‘reduce p = []’
  >- ( gs[zerop_def, reduce_def, coeff_def, poly_mul_cst_def, oEL_def,
          poly_mul_cst_aux_def]
       >> ‘deg (h :: p) = 0’ by
         ( gs[deg_def, reduce_def]
           >> cond_cases_tac >> gs[]
         )
       >> gs[]
       >> Cases_on ‘h=0’
       >- gs[]
       >> gs[reduce_p_poly_mul_holds]
       >> ‘h⁻¹ * h = &1 ’ by gs[REAL_MUL_LINV]
       >> gs[reduce_def]
     )
  >> ‘0 < deg (h::p)’ by gs[deg_def, reduce_def, length_gt_0]
  >> ‘ coeff (h::p) (deg (h::p)) = coeff p (deg p)’ by gs[coeff_cons]
  >> ‘¬zerop p’ by gs[zerop_def]
  >> gs[poly_mul_cst_def, poly_mul_cst_aux_def, reduce_def]
  >> Cases_on ‘reduce (poly_mul_cst_aux (coeff p (deg p))⁻¹ p) = []’
  >- gs[zerop_def, reduce_def]
  >> gs[zerop_def, reduce_def, reduce_idempotent]
QED

Theorem nonzero_last_coeff:
  ~ zerop p2 ⇒
  coeff p2 (deg p2) ≠ 0
Proof
  Induct_on ‘p2’
  >- gs[zerop_def, reduce_def]
  >> rpt strip_tac
  >> Cases_on ‘reduce p2 = []’
  >- ( gs[zerop_def, reduce_def, coeff_def, oEL_def]
       >> ‘deg (h :: p2) = 0’ by
         ( gs[deg_def, reduce_def]
           >> cond_cases_tac >> gs[]
         )
       >> gs[]
     )
  >>  ‘0 < deg (h::p2)’ by gs[deg_def, reduce_def, length_gt_0]
  >> ‘ coeff (h::p2) (deg (h::p2)) = coeff p2 (deg p2)’ by gs[coeff_cons]
  >> ‘¬zerop p2’ by gs[zerop_def]
  >> gs[]
QED

Theorem poly_eq_eval_eq:
  ∀ p1 p2.
    p1 = p2 ⇒ evalPoly p1 = evalPoly p2
Proof
  gs[]
QED

val _ = export_theory();

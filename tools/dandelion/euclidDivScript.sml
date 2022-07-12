(**
  Computable version of polynomial division and a correctness proof.
  Inspired by the implementation in Isabelle/HOL
  https://isabelle.in.tum.de/library/HOL/HOL-Computational_Algebra/Polynomial.html
  used to implement a computable version of Sturm sequences **)
open pred_setTheory listTheory bossLib RealArith realTheory polyTheory;
open realPolyTheory sturmTheory realPolyProofsTheory;
open renameTheory;
open bitArithLib;
open preambleDandelion;

val _ = new_theory "euclidDiv";

(** Definition of polynomial division, following Isabelle/HOL's definition in
    HOL/Computational_Algebra/Polynomial.thy.
 **)
Definition divmod_aux_def:
  divmod_aux lc q r d (dr:num) 0 = (q,r) ∧
  divmod_aux lc q r d dr (SUC n) =
  let rr = lc *c r;
      qq = coeff r dr;
      rrr = rr -p ((monom n [qq]) *p d);
      qqq = (lc *c q) +p (monom n [qq]) in
    divmod_aux lc qqq rrr d (dr-1) n
End

Definition divmod_def:
  divmod (p: poly) (q: poly) =
  if (q = []) then ([], p)
  else divmod_aux (coeff q (deg q)) [] p q (deg p) (1 + (deg p) - (deg q))
End

(* Define quotient as the first projection of the tuple *)
Definition quo_def:
  quo (p:poly) (q:poly) = FST (divmod p q)
End

(* Define remainder as the second projection of the tuple *)
Definition rm_def:
  rm (p:poly) (q:poly) = SND (divmod p q)
End

Theorem divmod_aux_correct:
  ∀ lc q r d dr n q' r'.
    divmod_aux lc q r d dr n = (q',r') ∧
    d ≠ [] ∧ lc = coeff d (deg d) ∧ deg r ≤ dr ∧
    (n = 1 + dr - deg d ∨ dr = 0 ∧ n = 0 ∧ zerop r ) ⇒
    (zerop r' ∨ deg r' < deg d) ∧
    evalPoly ((lc pow n) *c (d *p q +p r)) = evalPoly (d *p q' +p r')
Proof
  Induct_on ‘n’
  >- (rpt strip_tac >> gs[divmod_aux_def, mul_cst1, zerop_def, reduce_preserving])
  >> rpt gen_tac >> simp[Once divmod_aux_def]
  >> qmatch_goalsub_abbrev_tac ‘divmod_aux lc _ (rr -p monom _ [ qq ] *p _) _ _ _ = _’
  >> qmatch_goalsub_abbrev_tac ‘divmod_aux lc _ (_ -p b *p _) _ _ _ = _’
  >> qmatch_goalsub_abbrev_tac ‘divmod_aux lc qqq rrr _ _ _ = _’
  >> rpt $ disch_then strip_assume_tac
  >> ‘dr = n + deg d’ by gs[]
  >> ‘coeff (b *p d) dr = coeff b n * coeff d (deg d)’
    by (
      Cases_on ‘qq = 0’ >> rpt VAR_EQ_TAC
      >- (unabbrev_all_tac >> gs[monom_n, monom_0_mul, coeff_empty])
      >> ‘n = deg b’
        by (gs[Abbr‘b’] >> irule $ GSYM deg_monom_eq >> gs[])
      >> VAR_EQ_TAC >> gs [coeff_mult_degree_sum])
  >> ‘coeff (b *p d) dr = lc * coeff b n’ by (rpt VAR_EQ_TAC >> gs[REAL_MUL_COMM])
  >> ‘coeff rr dr = lc * coeff r dr’ by gs[Abbr‘rr’, coeff_cst_mul]
  >> ‘coeff rrr dr = 0’
    by (
      rpt VAR_EQ_TAC
      >> gs[Abbr‘rrr’, Abbr‘qq’, Abbr‘b’, poly_sub_def, poly_neg_def, coeff_add,
            coeff_cst_mul, monom_n]
      >> REAL_ARITH_TAC)
  >> ‘deg (lc *c r) ≤ dr’
    by (
      irule LESS_EQ_TRANS >> qexists_tac ‘deg r’
      >> gs[deg_leq_mul_cst])
  >> ‘deg (b *p d) ≤ dr’
    by (
       VAR_EQ_TAC >> gs[Abbr‘rrr’, Abbr‘b’]
       >> irule LESS_EQ_TRANS
       >> qexists_tac ‘if zerop (monom n [qq]) ∨ zerop d then 0 else deg (monom n [qq]) + deg d’
       >> gs[deg_mul_poly]
       >> cond_cases_tac >> gs[]
       >> Cases_on ‘qq = 0’ >> gs[]
       >- (
         ‘deg (monom n [0]) ≤ n’ suffices_by gs[]
         >> gs[deg_monom_0])
       >> gs[deg_monom_eq])
  >> ‘deg rrr ≤ dr - 1’
     by (VAR_EQ_TAC >> irule coeff_0_degree_minus_1 >> gs[Abbr ‘rrr’]
         >> irule LESS_EQ_TRANS
         >> qexists_tac ‘n + deg d’
         >> reverse conj_tac >- gs[]
         >> irule LESS_EQ_TRANS
         >> qexists_tac ‘MAX (deg rr) (deg (b *p d))’
         >> conj_tac
         >- irule deg_sub_poly
         >> gs[])
  >> first_x_assum $ qspecl_then [‘lc’, ‘qqq’, ‘rrr’, ‘d’, ‘dr - 1’, ‘q'’, ‘r'’] mp_tac
  >> impl_tac
  >- (
    gs[] >> reverse $ Cases_on ‘dr’ >- gs[]
    >> ‘n = 0’ by gs[] >> ‘deg d = 0’ by (rpt VAR_EQ_TAC >> gs[])
    >> ‘deg rrr = 0’ by (ntac 2 $ pop_assum kall_tac >> gs[])
    >> DISJ2_TAC >> fs[]
    >> irule deg_coeff_zerop >> gs[])
  >> rpt $ disch_then assume_tac
  >> conj_tac >- gs[]
  >> pop_assum (fn th => assume_tac $ CONJUNCT2 th)
  >> pop_assum $ rewrite_tac o single o GSYM
  >> rpt VAR_EQ_TAC
  >> gs[]
  >> unabbrev_all_tac
  >> gs[FUN_EQ_THM, eval_simps]
  >> rpt gen_tac
  >> qmatch_goalsub_abbrev_tac ‘_ = lc pow _ * ( _ * (_ * _ + mnm) + _)’
  >> ‘evalPoly d x * (lc * evalPoly q x + mnm) = lc * (evalPoly d x * evalPoly q x) + evalPoly d x * mnm’
     by real_tac
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac [GSYM REAL_ADD_ASSOC]
  >> ‘evalPoly d x * mnm + (lc * evalPoly r x - evalPoly d x * mnm) = lc * evalPoly r x’ by real_tac
  >> pop_assum $ rewrite_tac o single
  >> rewrite_tac [GSYM REAL_LDISTRIB]
  >> rewrite_tac [REAL_MUL_ASSOC]
  >> ‘lc pow (n + 1) = lc pow n * lc’ suffices_by gs[]
  >> gs[GSYM ADD1, pow]
QED

Theorem divmod_correct:
  ~ zerop g  ∧
  divmod f g = (q,r) ⇒
  evalPoly ((coeff g (deg g) pow (SUC (deg f) - deg g)) *c f) = evalPoly (g *p q +p r) ∧
  (zerop r ∨ deg r < deg g)
Proof
  simp[divmod_def] >> rpt $ disch_then strip_assume_tac
  >> ‘g ≠ []’ by (Cases_on ‘g’ >> gs[zerop_def, reduce_def])
  >> gs[]
  >> drule divmod_aux_correct >> gs[] >> strip_tac
  >> gs[mul_0_right, poly_add_rid, poly_mul_cst_reduce, ADD1]
QED

Theorem divmod_coeff_1:
  ~zerop g ∧ coeff g (deg g) = 1 ∧
  divmod f g = (q,r) ⇒
  evalPoly f = evalPoly (g *p q +p r) ∧
  (zerop r ∨ deg r < deg g)
Proof
  rpt strip_tac >> drule divmod_correct
  >> disch_then drule
  >> strip_tac
  >> gs[FUN_EQ_THM, eval_simps]
QED

Theorem divmod_coeff_1_reduce:
  c ≠ 0 ∧
  ~zerop (c *c g) ∧ coeff (c *c g) (deg (c *c g)) = 1 ∧
  divmod (c *c f) (c *c g) = (q,r) ⇒
  evalPoly f = evalPoly (g *p q +p (inv c *c r)) ∧
  (zerop r ∨ deg r < deg (c *c g))
Proof
  rpt strip_tac
  >> first_assum $ mp_then Any mp_tac divmod_coeff_1
  >> impl_tac >> gs[deg_of_const_mul]
  >> gs[FUN_EQ_THM, eval_simps]
  >> rpt strip_tac
  >> ‘evalPoly f x = inv c * (c * evalPoly f x)’ by
    (‘evalPoly f x = 1 * evalPoly f x’ by real_tac
     >> pop_assum $ once_rewrite_tac o single
     >> ‘1 = inv c * c’ by gs[REAL_MUL_LINV]
     >> pop_assum $ once_rewrite_tac o single
     >> gs[])
  >> pop_assum $ once_rewrite_tac o single
  >> first_x_assum $ qspec_then ‘x’ $ once_rewrite_tac o single
  >> gs[REAL_LDISTRIB]
QED

val _ = export_theory();

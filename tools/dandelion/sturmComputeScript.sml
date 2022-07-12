(**
    Define a computable version of the sturm sequence and
    prove its equivalence with the non-computable version
    of John Harrison
 **)
open pred_setTheory listTheory bossLib RealArith realTheory polyTheory;
open realPolyTheory sturmTheory realPolyProofsTheory euclidDivTheory;
open renameTheory;
open bitArithLib;
open preambleDandelion;

val _ = new_theory "sturmCompute";

Definition sturm_seq_aux_def:
  sturm_seq_aux (0:num) (p:poly) (q:poly) =
  (if (rm p (inv (coeff q (deg q)) *c q) = [] ∧ ~ zerop q)
   then SOME []
   else NONE)
  ∧
  sturm_seq_aux (SUC d:num) p q =
  (let g = (rm p (inv (coeff q (deg q)) *c q)) in
     if g = [] ∧ ~ zerop q then SOME []
     else if zerop q ∨ LENGTH (reduce q) < 2 then NONE else
       case sturm_seq_aux d q (--p g) of
       | SOME ss => SOME (--p g::ss)
       | _ => NONE)
End

Definition sturm_seq_def:
  sturm_seq (p:poly) (q:poly) : poly list option =
  if zerop q ∨ deg p ≤ 1 then NONE
  else
    case sturm_seq_aux (deg p - 1) p q of
    | NONE => NONE
    | SOME sseq =>
        case oEL (PRE (LENGTH sseq)) sseq of
        | SOME [x] => if x ≠ 0 then SOME sseq
                   else NONE
        | _ => NONE
End

(* a / b = c where c * b + r = a*)
(* b divides (a + k * r) ⇔ ∃ c. (a + k * r) = b * c *)
(* We say p2 divides p1 if ∃ q. p1 * q = p2 *)
Theorem poly_long_div_poly_divides:
  ∀ p q.
    ~ zerop q ∧
    deg q < deg p ∧
    reduce p = p ∧
    coeff q (deg q) = 1 ⇒
    q poly_divides (p +p (--p (rm p q)))
Proof
  rpt strip_tac >> gs[poly_divides, FUN_EQ_THM, GSYM poly_compat]
  >> Cases_on ‘divmod p q’ >> gs[rm_def]
  >> drule divmod_coeff_1
  >> rpt $ disch_then drule
  >> strip_tac
  >- (
    gs[zerop_def, eval_simps]
    >> ‘evalPoly r = evalPoly (reduce r)’ by gs[reduce_preserving]
    >> pop_assum $ rewrite_tac o single >> gs[evalPoly_def]
    >> qexists_tac ‘q'’ >> gs[poly_compat, POLY_MUL])
  >> qexists_tac ‘q'’ >> gs[eval_simps] >> gs[poly_compat, POLY_MUL]
  >> real_tac
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

Theorem sturm_equiv:
  ∀ n p1 p2 ps.
    sturm_seq_aux n p1 p2 = SOME ps ⇒
    STURM p1 p2 ps
Proof
  Induct_on ‘n’
  >- (
    gs[STURM_def, sturm_seq_aux_def, poly_divides, rm_def]
    >> rpt gen_tac
    >> qmatch_goalsub_abbrev_tac ‘SND (divmod p1 p2_norm) = _’
    >> rpt strip_tac
    >> Cases_on ‘divmod p1 p2_norm’ >> gs[FUN_EQ_THM, POLY_MUL]
    >> ‘coeff p2_norm (deg p2_norm) = 1’
      by (unabbrev_all_tac >> gs[normalized_normal])
    >> ‘~ zerop p2_norm’
      by (unabbrev_all_tac >> gs[nonzero_normalize])
    >> drule divmod_coeff_1
    >> rpt $ disch_then drule
    >> gs[poly_add_lid, reduce_preserving]
    >> gs[FUN_EQ_THM, eval_simps, poly_compat]
    >> rpt strip_tac
    >> unabbrev_all_tac
    >> qexists_tac ‘inv (coeff p2 (deg p2)) *c q’
    >> gs[GSYM poly_compat, eval_simps]
    >> rpt strip_tac
    >> qpat_x_assum ‘∀ x. _ = _’ kall_tac >> real_tac)
  >> gs[sturm_seq_aux_def]
  >> rpt gen_tac >> cond_cases_tac
  >- (
    gs[STURM_def, sturm_seq_aux_def, poly_divides, rm_def]
    >> ntac 2 $ pop_assum $ mp_tac
    >> qmatch_goalsub_abbrev_tac ‘SND (divmod p1 p2_norm) = _’
    >> rpt strip_tac
    >> Cases_on ‘divmod p1 p2_norm’ >> gs[FUN_EQ_THM, POLY_MUL]
    >> ‘coeff p2_norm (deg p2_norm) = 1’
      by (unabbrev_all_tac >> gs[normalized_normal])
    >> ‘~ zerop p2_norm’
      by (unabbrev_all_tac >> gs[nonzero_normalize])
    >> drule divmod_coeff_1
    >> rpt $ disch_then drule
    >> gs[poly_add_lid, reduce_preserving]
    >> gs[FUN_EQ_THM, eval_simps, poly_compat]
    >> rpt strip_tac
    >> unabbrev_all_tac
    >> qexists_tac ‘inv (coeff p2 (deg p2)) *c q’
    >> gs[GSYM poly_compat, eval_simps])
  >> cond_cases_tac
  >> gs[CaseEq"option"]
  >> rpt strip_tac >> VAR_EQ_TAC
  >> gs[STURM_def] >> reverse conj_tac
  >- (
    gs[GSYM deg_degree, rm_def]
    >> qmatch_goalsub_abbrev_tac ‘deg (--p (SND (divmod _ p2_norm)))’
    >> Cases_on ‘divmod p1 p2_norm’ >> gs[]
    >> ‘~ zerop p2_norm’
      by (unabbrev_all_tac >> gs[nonzero_normalize])
    >> drule_then drule divmod_correct
    >> ‘coeff p2 (deg p2) ≠ 0’ by gs[nonzero_last_coeff]
    >> rpt strip_tac >> unabbrev_all_tac
    >> gs[deg_poly_neg, deg_of_const_mul, deg_def, zerop_def])
  >> gs[poly_divides, FUN_EQ_THM, POLY_ADD, POLY_CMUL]
  >> gs[GSYM poly_compat, eval_simps]
  >> qexists_tac ‘1’ >> gs[poly_compat, POLY_MUL]
  >> gs[GSYM poly_compat, rm_def]
  >> qmatch_goalsub_abbrev_tac ‘SND (divmod _ p2_norm)’
  >> Cases_on ‘divmod p1 p2_norm’ >> gs[]
  >> ‘~ zerop p2_norm’
    by (unabbrev_all_tac >> gs[nonzero_normalize])
  >> ‘coeff p2_norm (deg p2_norm) = 1’
    by (unabbrev_all_tac >> gs[normalized_normal])
  >> drule divmod_coeff_1
  >> rpt $ disch_then drule
  >> disch_then (fn th => assume_tac $ CONJUNCT1 th)
  >> unabbrev_all_tac
  >> gs[FUN_EQ_THM, eval_simps]
  >> qexists_tac ‘inv (coeff p2 (deg p2)) *c q’
  >> strip_tac >> gs[eval_simps]
  >> pop_assum kall_tac >> last_x_assum kall_tac >> real_tac
QED

Theorem reduce_nonzero:
  reduce p ≠ [] ⇒
  ~ (EVERY (λ c. c = 0) p)
Proof
  Induct_on ‘p’ >> gs[reduce_def]
  >> cond_cases_tac >> gs[]
QED

Theorem reduce_not_zero:
  reduce p ≠ [] ⇒
  ∃ x. evalPoly (reduce p) x ≠ 0
Proof
  gs[reduce_preserving] >> gs[poly_compat] >> rpt strip_tac
  >> CCONTR_TAC >> gs[]
  >> ‘poly p = poly []’ by (gs[FUN_EQ_THM, poly_def])
  >> gs[POLY_ZERO]
  >> imp_res_tac reduce_nonzero
QED

Theorem sturm_seq_aux_length:
  ∀ n p q sseq.
    sturm_seq_aux n p q = SOME sseq ⇒
    LENGTH sseq ≤ n
Proof
  Induct_on ‘n’ >> gs[sturm_seq_aux_def]
  >> rpt gen_tac >> cond_cases_tac
  >> rpt strip_tac >> gs[CaseEq"option"]
  >> rpt VAR_EQ_TAC >> res_tac >> gs[]
QED

Theorem sturm_seq_equiv:
  sturm_seq p q = SOME sseq ⇒
  poly q ≠ poly [] ∧ sseq ≠ [] ∧
  (∃ d. d ≠ 0 ∧ LAST sseq = [d]) ∧
  STURM p q sseq
Proof
  gs[sturm_seq_def, CaseEq"option", CaseEq"list"]
  >> rpt $ disch_then strip_assume_tac
  >> imp_res_tac sturm_equiv >> gs[]
  >> gs[zerop_def]
  >> rpt conj_tac
  >- (
    gs[FUN_EQ_THM, GSYM poly_compat, Once $ GSYM reduce_preserving,
       evalPoly_def]
    >> imp_res_tac reduce_not_zero
    >> fsrw_tac [SATISFY_ss] [reduce_idempotent])
  >- ( imp_res_tac oEL_EQ_EL >> Cases_on ‘sseq’ >> gs[])
  >> imp_res_tac oEL_EQ_EL
  >> ‘sseq ≠ []’ by (Cases_on ‘sseq’ >> gs[])
  >> pop_assum $mp_then Any mp_tac LAST_EL
  >> disch_then $ once_rewrite_tac o single
  >> pop_assum $ once_rewrite_tac o single o GSYM
  >> gs[]
QED

val _ = export_theory();

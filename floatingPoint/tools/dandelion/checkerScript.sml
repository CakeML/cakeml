(**
  Define high-level functions used by Dandelion and prove their
  soundness by composing soundness proofs from the included files
**)
open realTheory realLib RealArith stringTheory polyTheory transcTheory;
open renameTheory realPolyTheory transcLangTheory sturmComputeTheory sturmTheory
     drangTheory checkerDefsTheory pointCheckerTheory mcLaurinApproxTheory
     realPolyProofsTheory approxPolyTheory transcIntvSemTheory
     transcApproxSemTheory transcReflectTheory;
(* open bitArithLib; *)
open preambleDandelion;

val _ = new_theory "checker";

(**
  Checks that the zero intervals encoded in the certificate actually are
  all of the zeros of derivative of the difference between the approximated
  polynomial and the transcendental function
**)
Definition numZeros_def:
  numZeros deriv1 deriv2 iv sseq =
  let numZeros =
      (variation (MAP (λp. poly p (FST iv)) (deriv1::deriv2::sseq)) -
       variation (MAP (λp. poly p (SND iv)) (deriv1::deriv2::sseq)))
  in
    if (poly deriv1 (FST iv) = 0) then
      (Invalid "Lower bound of derivative is 0", 0)
    else if (poly deriv1 (SND iv) = 0) then
      (Invalid "Upper bound of derivative is 0", 0)
    else (Valid, numZeros)
End

Definition getMaxWidth_def:
  getMaxWidth [] = 0 /\
  getMaxWidth ((u,v)::xs) = max (abs(u-v)) (getMaxWidth xs)
End

Definition getMaxAbsLb_def:
  getMaxAbsLb p [] = 0 ∧
  getMaxAbsLb p ((u,v)::xs) = max (abs (poly p u)) (getMaxAbsLb p xs)
End

Definition validBounds_def:
  validBounds iv [] = T ∧
  validBounds (iv:real#real) (zeroIv::zeros) =
    (FST iv ≤ FST zeroIv ∧ SND zeroIv ≤ SND iv ∧ validBounds iv zeros)
End

(**
  Either find a sublist of length n where P is true, or return the empty list
**)
Definition findN_def:
  findN n P l =
    let subL = FILTER P l in
      if (LENGTH subL = n) then subL else []
End

(**
  Checks that the certificate encoded error eps is an upper bound to the
  error that can be proven in HOL4.
  The provable error is computed following the assumptions of theorem
  BOUND_THEOREM_INEXACT.
  First we compute the maximum absolute value of the input interval
  and use it to get an upper bound on the maxmimum value of the derivate B.
  The error e, i.e. the width of the intervals in which the zeros can be
  found is computed using function getMaxWidth,
  and finally the upper bound ub is computed using function getMaxAbsLb.
  After computing these values, only the outer points of the interval need
  to be validated.
**)
Definition validateZerosLeqErr_def:
  validateZerosLeqErr errorp iv zeros eps numZeros =
    let mAbs = max (abs (FST iv)) (abs (SND iv));
        realZeros = (findN numZeros (λ (u,v). poly (diff errorp) u * poly (diff errorp) v ≤ 0) zeros);
        B = poly (MAP abs (diff errorp)) mAbs;
        e = getMaxWidth realZeros;
        ub = getMaxAbsLb errorp realZeros;
        globalErr = max (abs (poly errorp (FST iv)))
                        (max (abs (poly errorp (SND iv)))
                         (ub + B * e))
    in
      if ~ (validBounds iv realZeros ∧ recordered (FST iv) realZeros (SND iv)) then
          (Invalid "Zeros not correctly spaced", 0)
      else if LENGTH realZeros < numZeros then
          (Invalid "Did not find sufficient zeros", 0)
      else if globalErr ≤ eps
      then (Valid, globalErr)
      else (Invalid "Bounding error too large", 0)
End

(**
   Overall certificate checker combines all of the above functions into one that
   runs over the full certificate **)
Definition checker_def:
  checker (cert:certificate) approxSteps zeroGuess :checkerDefs$result =
  if ~ EVEN approxSteps ∨ ~ EVEN (approxSteps DIV 2) ∨ approxSteps = 0 ∨ LENGTH cert.iv ≠ 1
  then Invalid "Need even number of approximation steps"
  else
    (** Interval bounds **)
    case interpIntv cert.transc cert.iv of
    | NONE => Invalid "Could not compute IV bounds"
    | SOME ivAnn =>
    (** High-accuracy Taylor series **)
    case approxTransc <| steps := approxSteps |> ivAnn of
    | NONE => Invalid "Could not compute high-accuracy series"
    | SOME errAnn =>
    (** Get a polynomial representation **)
    case reflectToPoly (erase errAnn) (FST (HD cert.iv)) of
    | NONE => Invalid "Could not translate to polynomial"
    | SOME transp =>
      let errorp = transp -p cert.poly;
          deriv1 = diff errorp;
          deriv2 = diff deriv1;
      in
      if ~(FST (SND (HD cert.iv)) ≤ SND (SND (HD cert.iv)))
      then Invalid "Internal error"
      else
      case sturm_seq deriv1 deriv2 of
        NONE => Invalid "Could not compute sturm sequence"
      | SOME sseq =>
      case numZeros deriv1 deriv2 (SND (HD cert.iv)) sseq of
      | (Invalid s, _) => Invalid s
      | (Valid, zeros ) =>
          FST (validateZerosLeqErr errorp (SND (HD cert.iv)) zeroGuess (cert.eps - (getAnn errAnn)) zeros)
End

Theorem numZeros_sound:
  ∀ sseq deriv1 iv.
    sturm_seq deriv1 (diff deriv1) = SOME sseq ∧
    numZeros deriv1 (diff deriv1) iv sseq = (Valid, n) ∧
    FST iv ≤ SND iv ⇒
    {x | FST iv ≤ x ∧ x ≤ SND iv ∧ (poly deriv1 x = &0)} HAS_SIZE n
Proof
  rpt gen_tac
  >> rewrite_tac[numZeros_def]
  >> CONV_TAC $ DEPTH_CONV let_CONV
  >> rpt (cond_cases_tac >- gs[])
  >> rpt $ pop_assum $ mp_tac o SIMP_RULE std_ss []
  >> rpt strip_tac
  >> qpat_x_assum ‘_ = (_, n)’ $ strip_assume_tac o REWRITE_RULE [PAIR_EQ]
  >> pop_assum $ once_rewrite_tac o single o GSYM
  >> imp_res_tac sturm_seq_equiv
  >> irule STURM_THEOREM >> gs[]
QED

Theorem getMaxWidth_is_max:
  ∀ l. EVERY (λ (u,v). abs (u - v) <= getMaxWidth l) l
Proof
  Induct_on ‘l’ >> rpt strip_tac >> gs[getMaxWidth_def]
  >> rename1 ‘getMaxWidth (iv1::ivs)’
  >> PairCases_on ‘iv1’ >> rename1 ‘getMaxWidth ((iv1Lo, iv1Hi)::ivs)’
  >> gs[getMaxWidth_def, max_def]
  >> cond_cases_tac >> gs[]
  >> ‘getMaxWidth ivs < abs (iv1Lo - iv1Hi)’ by real_tac
  >> irule EVERY_MONOTONIC
  >> qexists_tac ‘λ (u,v). abs (u - v) <= getMaxWidth ivs’ >> gs[]
  >> rpt strip_tac >> Cases_on ‘x’ >> gs[]
  >> real_tac
QED

Theorem getMaxAbsLb_is_max:
  ∀ (l:(real#real) list) p. EVERY (λ (u,v). abs (poly p u) ≤ getMaxAbsLb p l) l
Proof
  Induct_on ‘l’ >> rpt strip_tac >> gs[getMaxAbsLb_def]
  >> rename1 ‘getMaxAbsLb p (iv1::ivs)’
  >> PairCases_on ‘iv1’ >> rename1 ‘getMaxAbsLb p ((iv1Lo, iv1Hi)::ivs)’
  >> gs[getMaxAbsLb_def, max_def]
  >> cond_cases_tac >> gs[]
  >> ‘getMaxAbsLb p ivs < abs (poly p iv1Lo)’
    by (last_x_assum kall_tac >> real_tac)
  >> irule EVERY_MONOTONIC
  >> qexists_tac ‘λ (u,v). abs (poly p u) ≤ getMaxAbsLb p ivs’ >> gs[]
  >> rpt strip_tac >> Cases_on ‘x’ >> gs[]
  >> last_x_assum kall_tac >> real_tac
QED

Theorem validBounds_is_valid:
  ∀ zeros iv.
    validBounds iv zeros ⇒
    EVERY (λ (u,v). FST iv ≤ u ∧ v ≤ SND iv) zeros
Proof
  Induct_on ‘zeros’ >> rpt strip_tac >> gs[validBounds_def]
  >> Cases_on ‘h’ >> gs[]
QED

Theorem validateZerosLeqErr_EVERY:
  ∀ err errorp iv zeroList zeros eps.
    validateZerosLeqErr errorp iv zeroList err zeros = (Valid, eps) ⇒
    let realZeros =
        (findN zeros (λ(u,v). poly (diff errorp) u * poly (diff errorp) v ≤ 0)
         zeroList)
    in
    EVERY (λ (u,v). FST iv ≤ u ∧ v ≤ SND iv ∧
                    abs (u - v) ≤ getMaxWidth realZeros ∧
                    abs (poly errorp u) ≤ getMaxAbsLb errorp realZeros )
          realZeros
Proof
  gs[validateZerosLeqErr_def, isValid_def]
  >> rpt gen_tac >> rpt (cond_cases_tac >> gs[])
  >> disch_then kall_tac
  >> qmatch_goalsub_abbrev_tac ‘EVERY all_conds_pred realZeros’
  >> ‘all_conds_pred =
      λ x. (λ (u,v). FST iv ≤ u ∧ v ≤ SND iv) x ∧
           (λ (u,v). abs (u - v) ≤ getMaxWidth realZeros) x ∧
           (λ (u,v). abs (poly errorp u) ≤ getMaxAbsLb errorp realZeros) x’
     by (unabbrev_all_tac >> gs[FUN_EQ_THM]
         >> rpt strip_tac >> Cases_on ‘x’ >> gs[] >> metis_tac[])
  >> pop_assum $ rewrite_tac o single
  >> gs[EVERY_CONJ] >> unabbrev_all_tac
  >> gs[findN_def] >> cond_cases_tac >> gs[]
  >> qmatch_goalsub_abbrev_tac ‘_ ∧ _ ∧ EVERY _ realZeros’
  >> rpt conj_tac
  >- (
    imp_res_tac validBounds_is_valid
    >> irule EVERY_MONOTONIC
    >> qexists_tac ‘λ (u,v). FST iv ≤ u ∧ v ≤ SND iv’ >> gs[])
  >- (
    assume_tac getMaxWidth_is_max
    >> irule EVERY_MONOTONIC
    >> qexists_tac ‘λ (u,v). abs (u - v) ≤ getMaxWidth realZeros’
    >> gs[])
  >> assume_tac getMaxAbsLb_is_max
  >> irule EVERY_MONOTONIC
  >> qexists_tac ‘λ (u,v). abs (poly errorp u) ≤ getMaxAbsLb errorp realZeros’
  >> gs[]
QED

Theorem EVERY_FILTER_TRUE:
  ∀ P l.
    EVERY P (FILTER P l)
Proof
  Induct_on ‘l’ >> gs[]
  >> rpt strip_tac
  >> cond_cases_tac >> gs[]
QED

Theorem validateZerosLeqErr_sound:
  ∀ derivative errorp iv zerosList zeros err eps.
    derivative = diff errorp ∧
    {x | FST iv ≤ x ∧ x ≤ SND iv ∧ (poly derivative x = &0)} HAS_SIZE zeros ∧
    validateZerosLeqErr errorp iv zerosList err zeros = (Valid, eps) ⇒
    ∀ x.
      FST iv ≤ x ∧ x ≤ SND iv ⇒
      abs(poly errorp x) ≤ err
Proof
  rpt strip_tac
  >> ‘∀ x. FST iv ≤ x ∧ x ≤ SND iv ⇒ ((λ x. poly errorp x) diffl poly derivative x) x’
     by (rpt strip_tac >> gs[polyTheory.POLY_DIFF])
  >> imp_res_tac validateZerosLeqErr_EVERY
  >> qpat_x_assum ‘validateZerosLeqErr _ _ _ _ _ = _’ mp_tac
  >> gs[validateZerosLeqErr_def, isValid_def]
  >> rpt (cond_cases_tac >> gs[])
  >> disch_then kall_tac
  >> pop_assum mp_tac
  >> qmatch_goalsub_abbrev_tac ‘computed_ub ≤ err’
  >> strip_tac >> irule REAL_LE_TRANS
  >> qexists_tac ‘computed_ub’ >> gs[]
  >> unabbrev_all_tac
  >> once_rewrite_tac [REAL_MUL_COMM]
  >> drule $ GEN_ALL BOUND_THEOREM_INEXACT
  >> disch_then $ irule o SIMP_RULE std_ss [BETA_THM]
  >> gs[] >> conj_tac
  >- (
    rpt strip_tac
    >> irule POLY_MONO
    >> gs[REAL_LE_MAX, abs]
    >> ntac 2 $ pop_assum mp_tac
    >> rpt $ pop_assum kall_tac
    >> every_case_tac >> real_tac)
  >> qexists_tac ‘findN zeros (λ (u,v). poly (diff errorp) u * poly (diff errorp) v ≤ 0) zerosList’ >> gs[]
  >> rpt strip_tac
  >> irule RECORDERED_ROOTCOUNT
  >> qexists_tac ‘FST iv’ >> qexists_tac ‘SND iv’ >> gs[]
  >> qexists_tac ‘diff errorp’ >> gs[findN_def]
  >> cond_cases_tac >> gs[EVERY_FILTER_TRUE]
QED

Theorem ivAnnot_is_inp:
  ∀ f env g. interpIntv f env = SOME g ⇒ erase g = f
Proof
  Induct_on ‘f’ >> simp[Once interpIntv_def]
  >> rpt strip_tac >> res_tac
  >> rpt VAR_EQ_TAC >> gs[erase_def]
QED

Theorem checker_soundness:
  ∀ cert approxSteps zeros.
    checker cert approxSteps zeros = Valid ⇒
    ∀ x.
      let iv = SND (HD (cert.iv)); var = FST (HD (cert.iv)) in
      FST(iv) ≤ x ∧ x ≤ SND (iv) ⇒
      ∃ r. interp cert.transc [(var,x)] = SOME r ∧
      abs (r - poly cert.poly x) ≤ cert.eps
Proof
  rpt gen_tac >> gs[checker_def]
  >> cond_cases_tac
  >> gs[checker_def, approxPoly_def,
        CaseEq"option", CaseEq"prod", CaseEq"checkerDefs$result", CaseEq"transc"]
  >> rpt strip_tac >> rpt VAR_EQ_TAC
  >> qpat_x_assum ‘_ = Valid’ mp_tac >> cond_cases_tac
  >> gs[CaseEq"option", CaseEq"prod", CaseEq"checkerDefs$result", CaseEq"transc"]
  >> rpt strip_tac >> rpt VAR_EQ_TAC
  (* Step 1: Approximate the transcendental fun with its taylor series *)
  >> mp_with_then strip_assume_tac ‘interpIntv _ _ = SOME _’ interpIntv_sound
  >> first_assum $ mp_then Any (drule_then mp_tac) approxTransc_sound
  >> disch_then $ qspec_then ‘[(FST (HD cert.iv), x)]’ mp_tac
  >> impl_tac
  >- (
    gs[varsContained_def] >> Cases_on ‘cert.iv’ >> gs[]
    >> rpt strip_tac >> gs[FIND_def] >> rpt VAR_EQ_TAC
    >> gs[INDEX_FIND_def] >> PairCases_on ‘h’ >> gs[]
    >> VAR_EQ_TAC >> gs[])
  >> disch_then strip_assume_tac
  >> ‘interp cert.transc [(FST (HD cert.iv), x)] = SOME r1’
    by (imp_res_tac ivAnnot_is_inp >> gs[])
  >> qexists_tac ‘r1’ >> gs[]
  >> real_rw ‘r1 - poly cert.poly x = r1 - r2 + (r2 - poly cert.poly x)’
  >> irule REAL_LE_TRANS
  >> qexists_tac ‘abs (r1 - r2) + abs (r2 - poly cert.poly x)’
  >> gs[REAL_ABS_TRIANGLE]
  >> real_once_rw ‘cert.eps = getAnn errAnn + (cert.eps - getAnn errAnn)’
  >> irule REAL_LE_ADD2 >> gs[]
  >> Cases_on ‘validateZerosLeqErr (transp -p cert.poly) (SND (HD cert.iv)) zeros (cert.eps - getAnn errAnn) zeros'’
  >> gs[] >> rpt VAR_EQ_TAC
  >> mpx_with_then strip_assume_tac ‘reflectToPoly _ _ = _’ (GEN_ALL reflectSemEquiv)
  >> ‘r2 = evalPoly transp x’ by gs[]
  >> VAR_EQ_TAC
  >> rewrite_tac [GSYM poly_compat, GSYM eval_simps]
  >> rewrite_tac [poly_compat]
  >> drule numZeros_sound >> disch_then $ drule_then drule
  >> strip_tac
  >> pop_assum $ mp_then Any mp_tac validateZerosLeqErr_sound
  >> disch_then $ qspec_then ‘transp -p cert.poly’ mp_tac
  >> simp[]
  >> disch_then drule
  >> disch_then $ qspec_then ‘x’ mp_tac
  >> impl_tac >> gs[]
QED

val _ = export_theory();

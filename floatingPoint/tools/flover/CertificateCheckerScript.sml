(**
  This file contains the HOL4 implementation of the certificate checker as well
  as its soundness proof. The checker is a composition of the range analysis
  validator and the error bound validator. Running this function on the encoded
  analysis result gives the desired theorem as shown in the soundness theorem.
**)
open simpLib realTheory realLib RealArith RealSimpsTheory;
open AbbrevsTheory ExpressionsTheory FloverTactics ExpressionAbbrevsTheory
     ExpressionSemanticsTheory ErrorBoundsTheory IntervalArithTheory
     RealRangeArithTheory IntervalValidationTheory ErrorValidationTheory
     ssaPrgsTheory FPRangeValidatorTheory TypeValidatorTheory FloverMapTheory;

open preambleFloVer;

val _ = new_theory "CertificateChecker";

Overload abs[local] = “realax$abs”;

(** Certificate checking function **)
Definition CertificateChecker_def:
  CertificateChecker (e:real expr) (A:analysisResult) (P:precond)
     (defVars: typeMap)=
  (case getValidMap defVars e FloverMapTree_empty of
  | Fail s => NONE
  | FailDet _ _ => NONE
  | Succes Gamma =>
    if (validIntervalbounds e A P LN /\
        FPRangeValidator e A Gamma LN)
    then
      if validErrorbound e Gamma A LN
      then SOME Gamma
      else NONE
    else NONE)
End

(**
   Soundness proof for the certificate checker.
   Apart from assuming two executions, one in R and one on floats, we assume that
   the real valued execution respects the precondition.
**)
Theorem Certificate_checking_is_sound:
  !(e:real expr) (A:analysisResult) (P:precond) (E1 E2:env) defVars fVars Gamma.
      (!v.
          v IN (domain fVars) ==>
          ?vR.
            (E1 v = SOME vR) /\
            FST (P v) <= vR /\ vR <= SND (P v)) /\
      (domain (usedVars e)) SUBSET (domain fVars) /\
      CertificateChecker e A P defVars = SOME Gamma /\
      approxEnv E1 (toRExpMap Gamma) A fVars LN E2 ==>
      ?iv err vR vF m.
        FloverMapTree_find e A = SOME (iv,err) /\
        eval_expr E1 (toRTMap (toRExpMap Gamma)) (toREval e) vR REAL /\
        eval_expr E2 (toRExpMap Gamma) e vF m /\
        (!vF m.
           eval_expr E2 (toRExpMap Gamma) e vF m ==>
           abs (vR - vF) <= err /\ validFloatValue vF m)
Proof
(**
   The proofs is a simple composition of the soundness proofs for the range
   validator and the error bound validator.
**)
  simp [CertificateChecker_def]
  \\ rpt strip_tac
  \\ Cases_on `getValidMap defVars e FloverMapTree_empty` \\ fs[]
  \\ IMP_RES_TAC getValidMap_top_correct
  \\ rveq
  \\ `validTypes e Gamma`
    by (first_x_assum irule
        \\ fs[FloverMapTree_empty_def, FloverMapTree_mem_def, FloverMapTree_find_def])
  \\ drule validIntervalbounds_sound
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`fVars`,`E1`, `Gamma`] destruct)
  \\ fs[dVars_range_valid_def, fVars_P_sound_def]
  \\ drule validErrorbound_sound
  \\ rpt (disch_then drule)
  \\ IMP_RES_TAC validRanges_single
  \\ disch_then (qspecl_then [`vR`, `err`, `FST iv`, `SND iv`] destruct)
  \\ fs[]
  \\ rpt (find_exists_tac \\ fs[])
  \\ rpt strip_tac
  >- (first_x_assum irule \\ fs[]
      \\ asm_exists_tac \\ fs[])
  \\ drule FPRangeValidator_sound
  \\ rpt (disch_then drule)
  \\ disch_then irule \\ fs[]
QED

Definition CertificateCheckerCmd_def:
  CertificateCheckerCmd (f:real cmd) (absenv:analysisResult) (P:precond)
     defVars =
    (case getValidMapCmd defVars f FloverMapTree_empty of
    | Fail _ => NONE
    | FailDet _ _ => NONE
    | Succes Gamma =>
      if (validSSA f (freeVars f))
        then
          if ((validIntervalboundsCmd f absenv P LN) /\
             FPRangeValidatorCmd f absenv Gamma LN)
          then
            if validErrorboundCmd f Gamma absenv LN
            then SOME Gamma
            else NONE
          else NONE
          else NONE)
End

Theorem CertificateCmd_checking_is_sound:
  !(f:real cmd) (A:analysisResult) (P:precond) defVars
     (E1 E2:env) (fVars:num_set) Gamma.
      (!v.
          v IN (domain (freeVars f)) ==>
          ?vR.
            (E1 v = SOME vR) /\
            FST (P v) <= vR /\ vR <= SND (P v)) /\
      domain (freeVars f) SUBSET (domain fVars) /\
      CertificateCheckerCmd f A P defVars = SOME Gamma /\
      approxEnv E1 (toRExpMap Gamma) A (freeVars f) LN E2 ==>
        ?iv err vR vF m.
          FloverMapTree_find (getRetExp f) A = SOME (iv, err) /\
          bstep (toREvalCmd f) E1 (toRTMap (toRExpMap Gamma)) vR REAL /\
          bstep f E2 (toRExpMap Gamma) vF m /\
          (!vF m. bstep f E2 (toRExpMap Gamma) vF m ==> abs (vR - vF) <= err)
Proof
  simp [CertificateCheckerCmd_def]
  \\ rpt strip_tac
  \\ Cases_on `getValidMapCmd defVars f FloverMapTree_empty` \\ fs[]
  \\ rveq \\ imp_res_tac getValidMapCmd_correct
  \\ `validTypesCmd f Gamma`
    by (first_x_assum irule
        \\ fs[FloverMapTree_empty_def, FloverMapTree_mem_def, FloverMapTree_find_def])
  \\ `?outVars. ssa f (freeVars f) outVars` by (match_mp_tac validSSA_sound \\ fs[])
  \\ qspecl_then
       [`f`, `A`, `E1`, `freeVars f`, `LN`, `outVars`, `P`, `Gamma`]
       destruct validIntervalboundsCmd_sound
  \\ fs[dVars_range_valid_def, fVars_P_sound_def]
  \\ IMP_RES_TAC validRangesCmd_single
  \\ qspecl_then
       [`f`, `A`, `E1`, `E2`, `outVars`, `freeVars f`, `LN`, `vR`, `FST iv_e`,
        `SND iv_e`, `err_e`, `m`, `Gamma`]
       destruct validErrorboundCmd_gives_eval
  \\ fs[]
  \\ rpt (find_exists_tac \\ fs[])
  \\ rpt strip_tac
  \\ drule validErrorboundCmd_sound
  \\ rpt (disch_then drule)
  \\ rename1 `bstep f E2 _ vF2 m2`
  \\ disch_then
      (qspecl_then
        [`outVars`, `vR`, `vF2`, `FST iv_e`, `SND iv_e`, `err_e`, `m2`] destruct)
  \\ fs[]
QED

Theorem CertificateCheckerCmd_Gamma_is_getValidMapCmd:
  CertificateCheckerCmd f A P dVars = SOME Gamma ⇒
  getValidMapCmd dVars f FloverMapTree_empty = Succes Gamma
Proof
  fs[CertificateCheckerCmd_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
QED

val _ = export_theory();

(*
  Supporting proofs for automation
*)
(* Dandelion *)
open realZeroLib floverConnTheory;
(* CakeML & FloVer *)
open pureExpsTheory FloVerToCakeMLTheory FloVerToCakeMLProofsTheory
     expressionsLib basisProgTheory basis_ffiTheory cfHeapsBaseTheory basis
     cfTacticsLib ml_translatorLib cfSupportTheory;

val _ = new_theory "libm";

Theorem nsBind_nsAppend:
  nsBind x v env = nsAppend (Bind [(x,v)] []) env
Proof
  Cases_on ‘env’ >> gs[namespaceTheory.nsAppend_def, namespaceTheory.nsBind_def]
QED

Definition value_has_err_of_def:
  value_has_err_of f x (rv:v) err =
    case rv of
    |FP_WordTree fp =>
       (realax$abs
        (optionGet (interp f [("x", x)]) - (fp64_to_real (compress_word fp)))
          ≤ err)
    | _ => F
End

Theorem theFunSpec_thm_general:
  ∀ cert lo hi exp expRat fun_v prog progReal env env2 Gamma P typeAnn A iv
     err ply delta v.
    getPrecondFromCert cert = P ∧
    poly2FloVer ply = toREval exp ∧
    ply ≠ [] ∧
    cert.poly = ply ∧
    P 0 = (lo,hi) ∧
    is64BitEval exp ∧
    noDowncast exp ∧
    is64BitEnv Gamma ∧
    usedVars exp = LS () ∧ (* usedVars exp = { 0 } *)
    CertificateChecker exp A P Gamma = SOME typeAnn ∧
    (∀ x. lo ≤ x ∧ x ≤ hi ⇒
          realax$abs (optionGet (interp (cert.transc) [("x", x)]) - evalPoly ply x) ≤ delta) ∧
    FloverMapTree_find exp A = SOME (iv, err) ∧
    SOME prog = toCmlFloatProg exp ∧
    do_opapp [fun_v; v] =
      SOME (env2, prog) ∧
    env2 = env with v := nsAppend (Bind [("x0", v)] []) env.v ∧
    isPureExpList [prog] ⇒
    ∀ fp (st:unit semanticPrimitives$state).
      lo <= fp64_to_real (compress_word (Fp_const fp)) /\
      fp64_to_real (compress_word (Fp_const fp)) <= hi /\
      fp64_isFinite (compress_word (Fp_const fp)) /\
      DOUBLE (Fp_const fp) v ⇒
        app (p:unit ffi_proj) fun_v [v] (emp)
          (POSTv rv. &(value_has_err_of (cert.transc) (fp64_to_real fp) rv (delta + err)))
Proof
  rpt strip_tac
  >> qpat_x_assum ‘_ = env with v := nsAppend _ _’ mp_tac
  >> qmatch_goalsub_abbrev_tac ‘nsAppend flEnv _’ >> strip_tac
  >> drule $ INST_TYPE [“:'ffi”|->“:unit”] FloVer_CakeML_sound_error
  >> rpt $ disch_then drule
  >> disch_then $ qspec_then ‘flEnv’ mp_tac >> impl_tac
  >- (
    unabbrev_all_tac >> gs[usedVars_P_sound_def]
    >> gvs[namespaceTheory.nsLookup_def, DOUBLE_def])
  >> disch_then $ qspec_then ‘env’ strip_assume_tac
  >> gs[app_def, app_basic_def] >> rpt strip_tac
  >> Q.REFINE_EXISTS_TAC ‘Val fpN’
  >> simp[evaluate_to_heap_def, evaluate_ck_def]
  >> gs[emp_def, value_has_err_of_def]
  >> first_x_assum $
       qspec_then ‘(st' with fp_state := st'.fp_state with
                                           <| real_sem := F; canOpt := FPScope Opt |>)’
       strip_assume_tac
  >> first_x_assum $
       mp_then Any mp_tac
         (INST_TYPE [“:'a”|->“:unit”, “:'b”|->“:unit”] isPureExpList_swap_state)
  >> gs[]
  >> strip_tac
  >> qexists_tac ‘EMPTY’ >> qexists_tac ‘EMPTY’
  >> gs[SPLIT_def, SPLIT3_def, cond_def, DOUBLE_def]
  >> qmatch_goalsub_abbrev_tac ‘realax$abs ( f_eval - double_eval)’
  >> ‘f_eval - double_eval =
      (f_eval - evalPoly ply (fp64_to_real fp)) + (evalPoly ply (fp64_to_real fp) - double_eval)’
     by REAL_ARITH_TAC
  >> pop_assum $ once_rewrite_tac o single
  >> irule REAL_LE_TRANS
  >> irule_at Any REAL_ABS_TRIANGLE
  >> irule REAL_LE_ADD2 >> conj_tac
  >- (
    unabbrev_all_tac
    >> first_x_assum irule >> gs[fpSemTheory.compress_word_def])
  >> ‘evalPoly ply (fp64_to_real fp) = r’ suffices_by gs[]
  >> rewrite_tac[evalPoly_Flover_eval_bisim]
  >> gs[]
  >> ‘toREnv (toFloVerEnv flEnv exp') = λ v. if v = 0 then SOME (fp64_to_real fp) else NONE’
     by (
       unabbrev_all_tac
       >> gs[FUN_EQ_THM, IEEE_connectionTheory.toREnv_def, toFloVerEnv_def]
       >> rpt strip_tac
       >> Cases_on ‘v' = 0’ >> gs[]
       >> gs[lookup_def, namespaceTheory.nsLookup_def,
             machine_ieeeTheory.fp64_to_real_def, fpSemTheory.compress_word_def])
  >> gs[]
QED

val _ = export_theory();

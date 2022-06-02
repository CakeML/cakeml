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

Definition sem_returns_with_err_def:
  sem_returns_with_err st envFl envReal prog progReal rv err =
    (case evaluate st envFl [prog] of
     | (_, Rval [FP_WordTree fp]) =>
         (DOUBLE fp rv ∧
          (case evaluate (empty_state with
                    fp_state := empty_state.fp_state with
                    <|real_sem := T; canOpt := FPScope NoOpt|>)
                         envReal
                    [progReal] of
           | (_, Rval [Real r]) =>
               real$abs (r - fp64_to_real (compress_word fp)) <= err
           | _ => F))
          | _ => F)
End

Theorem theFunSpec_thm_general:
  ∀ cert lo hi exp expRat fun_v prog progReal env env2 Gamma P typeAnn A iv
     err.
    getPrecondFromCert cert = P ∧
    P 0 = (lo,hi) ∧
    exp = ratExp2realExp expRat ∧
    is64BitEval exp ∧
    noDowncast exp ∧
    is64BitEnv Gamma ∧
    usedVars exp = LS () ∧ (* usedVars exp = { 0 } *)
    CertificateChecker exp A P Gamma = SOME typeAnn ∧
    FloverMapTree_find exp A = SOME (iv, err) ∧
    SOME prog = toCmlFloatProg exp ∧
    SOME progReal = toCmlRealExp expRat ∧
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
          (POSTv rv.
           &(sem_returns_with_err st
             (env with v := nsAppend (Bind [("x0",v)] []) env.v)
             (env with v := toRspace (nsAppend (Bind [("x0",v)] []) env.v))
             prog progReal rv err))
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac ‘nsAppend flEnv _’
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
  >> gs[emp_def, sem_returns_with_err_def]
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
QED

val _ = export_theory();

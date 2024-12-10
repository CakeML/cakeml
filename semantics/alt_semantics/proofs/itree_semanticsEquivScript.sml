(*
  Relating the itree- and FFI state-based CakeML semantics
*)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open optionTheory relationTheory pairTheory listTheory arithmeticTheory llistTheory;
open namespaceTheory astTheory ffiTheory lprefix_lubTheory semanticPrimitivesTheory
     semanticsTheory evaluatePropsTheory smallStepTheory smallStepPropsTheory primSemEnvTheory;
open itreeTheory itree_semanticsTheory itree_semanticsPropsTheory;

val _ = new_theory "itree_semanticsEquiv";


(******************** Useful simplifications ********************)

(* Deliberately no `application_def` here *)
val smallstep_ss = simpLib.named_rewrites "smallstep_ss" [
    smallStepTheory.continue_def,
    smallStepTheory.return_def,
    smallStepTheory.push_def,
    smallStepTheory.e_step_def
    ];

val dsmallstep_ss = simpLib.named_rewrites "dsmallstep_ss" [
    smallStepPropsTheory.collapse_env_def,
    smallStepTheory.decl_continue_def,
    smallStepTheory.decl_step_def
    ];

val itree_ss = simpLib.named_rewrites "itree_ss" [
    itree_semanticsTheory.exn_continue_def,
    itree_semanticsTheory.continue_def,
    itree_semanticsTheory.return_def,
    itree_semanticsTheory.push_def,
    itree_semanticsTheory.estep_def,
    get_ffi_def
    ];

val ditree_ss = simpLib.named_rewrites "ditree_ss" [
    itree_semanticsTheory.dcontinue_def,
    itree_semanticsTheory.dreturn_def,
    itree_semanticsTheory.dpush_def,
    itree_semanticsTheory.dstep_def,
    dget_ffi_def
    ];


(******************** Simpler lemmas ********************)

Theorem do_app_cases =
  ``do_app st op vs = SOME (st',v)`` |> SIMP_CONV (srw_ss()) [
    do_app_def, AllCaseEqs(), SF DNF_ss, LET_THM, GSYM DISJ_ASSOC];

Theorem do_app_rel:
  (∀s. op ≠ FFI s) ⇒
  OPTREL (λ(a,b) (c,d). a = c ∧ result_rel b d)
    (do_app st op vs)
    (OPTION_MAP (λ(a,b). (FST a, b)) (do_app (st, ffi) op vs))
Proof
  cheat (*
  rw[] >> reverse $ Cases_on `do_app (st,ffi) op vs` >> gvs[]
  >- (
    PairCases_on `x` >> gvs[semanticPrimitivesPropsTheory.do_app_cases] >>
    simp[do_app_def, result_rel_cases] >> every_case_tac >> gvs[]
    ) >>
  Cases_on `do_app st op vs` >> gvs[] >> PairCases_on `x` >>
  gvs[do_app_cases, semanticPrimitivesTheory.do_app_def, store_alloc_def] >>
  every_case_tac >> gvs[] *)
QED

Theorem ctxt_rel_fix_fp_state:
  ∀ fp cs1 cs2.
    ctxt_rel cs1 cs2 ⇒
    fix_fp_state cs1 fp = fix_fp_state cs2 fp
Proof
  Induct_on ‘cs1’ >>
  gs[ctxt_rel_def, fix_fp_state_def, smallStepTheory.fix_fp_state_def] >>
  rpt strip_tac >> rpt VAR_EQ_TAC >>
  Cases_on ‘h’ >> gs[] >>
  Cases_on ‘y’ >> gs[] >> rpt VAR_EQ_TAC >>
  qpat_x_assum ‘ctxt_frame_rel _ _’ mp_tac >>
  Cases_on ‘q’ >> gs[] >> Cases_on ‘q'’ >>
  simp[ctxt_frame_rel_cases, fix_fp_state_def, smallStepTheory.fix_fp_state_def]
QED

Theorem do_fprw_id:
  result_rel r1 r2 ⇒
  OPTREL result_rel (itree_semantics$do_fprw r1 opts rws)
  (semanticPrimitives$do_fprw r2 opts rws)
Proof
  Cases_on ‘r1’ >> Cases_on ‘r2’ >> gs[result_rel_cases] >> rw[OPTREL_def] >>
  gs[do_fprw_def, semanticPrimitivesTheory.do_fprw_def] >>
  every_case_tac >> gs[result_rel_cases]
QED

Theorem application_rel:
  (∀s. op ≠ FFI s) ∧
  ctxt_rel cs1 cs2 ⇒
  step_result_rel
    (application op env st fp vs cs1)
    (application op env (st,ffi) fp vs cs2)
Proof
  cheat (*
  rw[] >>
  drule do_app_rel >> disch_then $ qspecl_then [`vs`,`st`,`ffi`] assume_tac >>
  Cases_on ‘getOpClass op’
  >- (
    Cases_on ‘op’ >> gs[getOpClass_def, application_def, cml_application_thm] >>
    simp[step_result_rel_cases, AllCaseEqs(), PULL_EXISTS] >>
    Cases_on ‘do_app (st,ffi) Eval vs’ >> gvs[] >>
    Cases_on ‘do_app st Eval vs’ >> gvs[]
    >- (
      irule $ GSYM ctxt_rel_fix_fp_state >> simp[])>>
    PairCases_on ‘x’ >> PairCases_on ‘x'’ >>
    gvs[result_rel_cases, SF smallstep_ss, SF itree_ss] >>
    gs[do_app_def, semanticPrimitivesTheory.do_app_def] >> every_case_tac >>
    gs[])
  >- (
    rw[application_def, cml_application_thm] >>
    simp[step_result_rel_cases, AllCaseEqs(), PULL_EXISTS] >>
    Cases_on `do_opapp vs` >> simp[ctxt_rel_fix_fp_state] >>
    PairCases_on `x` >> simp[]
    )
  >- (
    rw[application_def, cml_application_thm] >>
    Cases_on `do_app (st,ffi) op vs` >> gvs[] >>
    Cases_on `do_app st op vs` >> gvs[]
    >- (simp[step_result_rel_cases, AllCaseEqs()] >> Cases_on `op` >> gvs[ctxt_rel_fix_fp_state]) >>
    PairCases_on `x` >> PairCases_on `x'` >> gvs[] >>
    gvs[result_rel_cases, SF smallstep_ss, SF itree_ss] >>
    simp[step_result_rel_cases, AllCaseEqs()] >>
    qexists_tac `cs1` >> simp[] >> Cases_on `op` >> gvs[] >>
    gs[do_app_def, semanticPrimitivesTheory.do_app_def] >> every_case_tac >> gs[store_alloc_def])
  >- (
    rw[application_def, cml_application_thm] >>
    Cases_on `do_app (st,ffi) op vs` >> gvs[] >>
    Cases_on `do_app st op vs` >> gvs[]
    >- (simp[step_result_rel_cases, AllCaseEqs()] >> Cases_on `op` >> gvs[ctxt_rel_fix_fp_state]) >>
    gs[step_result_rel_cases,ctxt_rel_fix_fp_state] >>
    PairCases_on `x` >> PairCases_on `x'` >> gvs[] >>
    imp_res_tac do_fprw_id >>
    first_x_assum $ qspecl_then [‘fp.rws’, ‘fp.opts 0’] assume_tac >>
    gvs[result_rel_cases, SF smallstep_ss, SF itree_ss] >>
    simp[step_result_rel_cases, AllCaseEqs()]
    >- (qexists_tac `cs1` >> simp[isFpBool_def] >> Cases_on `op` >> gvs[] >>
        Cases_on ‘semanticPrimitives$do_fprw (Rval v) (fp.opts 0) fp.rws’ >> gs[] >>
        TRY $ first_x_assum $ irule_at Any >> gs[OPTREL_def, result_rel_cases] >>
        rpt VAR_EQ_TAC >|
        [ Cases_on ‘v’,
          Cases_on ‘v'’] >>
        gs[do_fprw_def] >> every_case_tac >> gs[])
    >- (
      qexists_tac `cs1` >> simp[] >> Cases_on `op` >> gvs[] >>
      gvs[ctxt_rel_def] >> simp[ctxt_frame_rel_cases] >>
      gs[do_app_def, semanticPrimitivesTheory.do_app_def] >> every_case_tac >>
      gs[store_alloc_def]
    )
    >- (qexists_tac `cs1` >> simp[isFpBool_def] >> Cases_on `op` >> gvs[] >>
        gs[OPTREL_def, result_rel_cases] >> rpt VAR_EQ_TAC
        >- (Cases_on ‘v’ >> gs[])
        >- (Cases_on ‘v'’ >> gs[do_fprw_def] >> every_case_tac >> gs[]) >>
        gs[do_fprw_def] >> every_case_tac >> gs[])
  )
  >- (
    rw[application_def, cml_application_thm]
    >- (
      Cases_on `do_app (st,ffi) op vs` >> gvs[] >>
      Cases_on `do_app st op vs` >> gvs[]
      >- (simp[step_result_rel_cases, AllCaseEqs()] >> Cases_on `op` >> gvs[ctxt_rel_fix_fp_state]) >>
      gs[step_result_rel_cases,ctxt_rel_fix_fp_state] >>
      PairCases_on `x` >> PairCases_on `x'` >> gvs[] >>
      gvs[result_rel_cases, SF smallstep_ss, SF itree_ss] >>
      simp[step_result_rel_cases, AllCaseEqs()] >>
      gvs[ctxt_rel_def] >> simp[ctxt_frame_rel_cases])
    >- (gs[step_result_rel_cases, ctxt_rel_fix_fp_state]
       )) *)
QED

Theorem application_rel_FFI_type_error:
  application (FFI s) env st fp vs cs1 = Etype_error (fix_fp_state cs1 fp) ⇔
  application (FFI s) env (st, ffi) fp vs cs2 = Eabort (fix_fp_state cs2 fp, Rtype_error)
Proof
  rw[application_def, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[SF smallstep_ss] >>
  gvs[store_lookup_def, store_assign_def, store_v_same_type_def]
QED

Theorem application_rel_FFI_step:
  application (FFI s) env st fp vs cs1 = Estep (env, st, fp2, Val v, cs1) ⇔
  application (FFI s) env (st, ffi) fp vs cs2 = Estep (env, (st,ffi), fp2, Val v, cs2)
Proof
  rw[application_def, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[SF smallstep_ss] >>
  gvs[call_FFI_def, store_lookup_def, store_assign_def, store_v_same_type_def]
  >- (eq_tac >> rw[] >> metis_tac[LUPDATE_SAME]) >>
  every_case_tac >> gvs[] >> rw[] >> gvs[ffi_state_component_equality]
QED

Theorem dstep_ExpVal_Exp:
  dstep env st (ExpVal env' (Exp e) cs locs p) dcs =
  case estep (env',st.refs,st.fp_state,Exp e,cs) of
  | Estep (env',refs',fp', ev',ec') =>
      dreturn (st with <| refs := refs'; fp_state := fp' |>) dcs (ExpVal env' ev' ec' locs p)
  | Effi s ws1 ws2 n env'' refs'' ec'' =>
    Dffi (st with refs := refs'') (s,ws1,ws2,n,env'',ec'') locs p dcs
  | Edone => Ddone
  | Etype_error fp => Dtype_error fp
Proof
  Cases_on `cs` >> rw[SF ditree_ss]
QED

Theorem decl_step_ExpVal_Exp:
  decl_step env (st,ExpVal env' (Exp e) ec locs p,c) =
  case e_step (env',(st.refs,st.ffi),st.fp_state,Exp e,ec) of
    Estep (env',(refs',ffi'),fp',ev',ec') =>
      Dstep
        (st with <|refs := refs'; ffi := ffi'; fp_state := fp'|>,
         ExpVal env' ev' ec' locs p,c)
  | Eabort a => Dabort a
  | Estuck => Ddone
Proof
  rw[decl_step_def] >> TOP_CASE_TAC >> simp[] >>
  rpt TOP_CASE_TAC >> gs[]
QED


(******************** Relating non-FFI steps ********************)

Triviality FST_THM:
  FST = λ(x,y,z). x
Proof
  rw[FUN_EQ_THM, UNCURRY]
QED

Theorem step_result_rel_single:
  ∀ea eb.
    step_result_rel (Estep ea) (Estep eb) ∧
    ¬ is_Effi (estep ea)
  ⇒ step_result_rel (estep ea) (e_step eb) ∧
    ∀ffi. get_ffi (e_step eb) = SOME ffi ⇒ get_ffi (Estep eb) = SOME ffi
Proof
  rpt PairCases >> rename1 `_ (_ (env,st,fp,ev,cs1)) (_ (env',(st',ffi),fp',ev',cs2))` >>
  gvs[e_step_def] >> reverse $ TOP_CASE_TAC >> gvs[]
  >- (
    simp[Once step_result_rel_cases] >> strip_tac >> gvs[] >>
    TOP_CASE_TAC >> gvs[]
    >- (gvs[ctxt_rel_def, SF smallstep_ss, SF itree_ss, step_result_rel_cases]) >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >> gvs[ctxt_frame_rel_cases] >>
    pairarg_tac >> gvs[SF smallstep_ss, SF itree_ss, step_result_rel_cases] >>
    simp[ctxt_rel_def] >> simp[GSYM ctxt_rel_def] >> simp[ctxt_frame_rel_cases]
    )
  >- (
    gvs[estep_def, step_result_rel_cases] >> strip_tac >>
    gvs[SF smallstep_ss, SF itree_ss, ctxt_rel_def, ctxt_frame_rel_cases, get_ffi_def] >>
    gvs[GSYM ctxt_frame_rel_cases, GSYM step_result_rel_cases] >>
    CASE_TAC >- gvs[continue_def, get_ffi_def] >>
    PairCases_on `h` >> gvs[] >> PairCases_on `x` >> gvs[] >>
    rename1 `ctxt_frame_rel c1 c2` >> rename1 `(c1,env)` >>
    rename1 `LIST_REL _ rest1 rest2` >>
    Cases_on `c1` >> gvs[SF itree_ss, ctxt_frame_rel_cases] >>
    gvs[GSYM ctxt_frame_rel_cases, get_ffi_def]
    >- (
      reverse CASE_TAC >>
      gvs[PULL_EXISTS, EXISTS_PROD, get_ffi_def, SF itree_ss]
      >- simp[ctxt_frame_rel_cases] >>
      rename1 `application op _ _ _ vs _` >>
      reverse $ Cases_on `∃s. op = FFI s` >> gvs[]
      >- (
        reverse $ rw[]
        >- (
          drule application_ffi_unchanged >>
          Cases_on `application op env (st,ffi) fp vs rest2` >> gvs[get_ffi_def] >>
          PairCases_on `p` >> disch_then drule >> gvs[get_ffi_def]
          )
        >- (
          drule application_rel >> gvs[ctxt_rel_def] >> disch_then drule >>
          disch_then $ qspecl_then [`vs`,`st`,‘fp’,`ffi`,`env`] assume_tac >>
          gvs[step_result_rel_cases, ctxt_rel_def]
          )
        ) >>
      qspecl_then [`vs`,`st`,`s`,‘fp’,`env`,`rest1`]
        assume_tac $ GEN_ALL application_FFI_results >> gvs[] >>
      csimp[] >> gvs[is_Effi_def, get_ffi_def]
      >- (imp_res_tac $ SIMP_RULE std_ss [ctxt_rel_def] ctxt_rel_fix_fp_state >>
          metis_tac[application_rel_FFI_type_error]) >>
      imp_res_tac application_rel_FFI_step >> gvs[get_ffi_def]
      )
    >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases] >>
        irule $ GSYM ctxt_rel_fix_fp_state >> gs[ctxt_rel_def, ctxt_frame_rel_cases])
    >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases] >>
        irule $ GSYM ctxt_rel_fix_fp_state >> gs[ctxt_rel_def, ctxt_frame_rel_cases])
    >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases] >>
        irule $ GSYM ctxt_rel_fix_fp_state >> gs[ctxt_rel_def, ctxt_frame_rel_cases])
    >- (
      CASE_TAC >> simp[SF itree_ss] >>
      PairCases_on `h` >> simp[continue_def] >>
      EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases] >>
      irule $ GSYM ctxt_rel_fix_fp_state >> gs[ctxt_rel_def, ctxt_frame_rel_cases])
    >- (
      TOP_CASE_TAC >> gvs[SF itree_ss] >>
      EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases] >>
      irule $ GSYM ctxt_rel_fix_fp_state >> gs[ctxt_rel_def, ctxt_frame_rel_cases]
      )
    )
  >- (
    reverse $ every_case_tac >> gvs[estep_def, step_result_rel_cases] >> strip_tac >>
    gvs[SF smallstep_ss, SF itree_ss, ctxt_rel_def, ctxt_frame_rel_cases, get_ffi_def] >>
    gvs[GSYM ctxt_frame_rel_cases, GSYM step_result_rel_cases]
    >- gvs[FST_THM, LAMBDA_PROD] >>
    TRY (gvs[FST_THM, LAMBDA_PROD] >>
        irule ctxt_rel_fix_fp_state >> gs[ctxt_rel_def, ctxt_frame_rel_cases] >> NO_TAC) >>
    TRY (irule ctxt_rel_fix_fp_state >> gs[ctxt_rel_def] >> NO_TAC) >>
    rename1 `application op _ _ _ _ _` >>
    reverse $ Cases_on `∃s. op = FFI s` >> gvs[]
    >- (
      reverse $ rw[]
      >- (
        drule application_ffi_unchanged >>
        Cases_on `application op env (st,ffi) fp [] cs2` >> gvs[get_ffi_def] >>
        PairCases_on `p` >> disch_then drule >> gvs[get_ffi_def]
        )
      >- (
        drule application_rel >> gvs[ctxt_rel_def] >> disch_then drule >>
        disch_then $ qspecl_then [`[]`,`st`,‘fp’,`ffi`,`env`] assume_tac >>
        gvs[step_result_rel_cases, ctxt_rel_def]
        )
      )
    >- (
      qspecl_then [`[]`,`st`,`s`,‘fp’,`env`,`cs1`]
        assume_tac $ GEN_ALL application_FFI_results >> gvs[] >>
      csimp[] >> gvs[is_Effi_def, get_ffi_def]
      >- (imp_res_tac application_rel_FFI_type_error >> gs[] >>
        irule $ GSYM ctxt_rel_fix_fp_state >> gs[ctxt_rel_def]) >>
      imp_res_tac application_rel_FFI_step >> simp[get_ffi_def]
      )
    >- (
      reverse $ rw[]
      >- (
        drule application_ffi_unchanged >>
        Cases_on `application op env (st,ffi) fp [] cs2` >> gvs[get_ffi_def] >>
        PairCases_on `p` >> disch_then drule >> gvs[get_ffi_def]
        )
      >- (
        drule application_rel >> gvs[ctxt_rel_def] >> disch_then drule >>
        disch_then $ qspecl_then [`[]`,`st`,‘fp’,`ffi`,`env`] assume_tac >>
        gvs[step_result_rel_cases, ctxt_rel_def]
        )
      )
    >- (
      qspecl_then [`[]`,`st`,`s`,‘fp’,`env`,`cs1`]
        assume_tac $ GEN_ALL application_FFI_results >> gvs[] >>
      csimp[] >> gvs[is_Effi_def, get_ffi_def]
      >- (imp_res_tac application_rel_FFI_type_error >> gs[] >>
        irule $ GSYM ctxt_rel_fix_fp_state >> gs[ctxt_rel_def]) >>
      imp_res_tac application_rel_FFI_step >> simp[get_ffi_def]
      ))
QED

Theorem is_Dffi_eq_is_Effi_single:
  is_Dffi (dstep env dsta (ExpVal env' ev cs l p) dcs) ⇔
  is_Effi (estep (env',dsta.refs,dsta.fp_state,ev,cs))
Proof
  Cases_on `ev` >> rw[SF ditree_ss, SF itree_ss] >>
  Cases_on `cs` >> rw[SF ditree_ss, SF itree_ss, is_Effi_def, is_Dffi_def] >>
  every_case_tac >> gvs[is_Effi_def, is_Dffi_def]
QED

Theorem dstep_result_rel_single:
  ∀dsta deva dcsa db env.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep db) ∧
    ¬is_Dffi (dstep env dsta deva dcsa)
  ⇒ dstep_result_rel (dstep env dsta deva dcsa) (decl_step env db) ∧
    ∀ffi. dget_ffi (decl_step env db) = SOME ffi ⇒ dget_ffi (Dstep db) = SOME ffi
Proof
  ntac 3 gen_tac >> PairCases >> gen_tac >>
  simp[Once dstep_result_rel_cases] >> strip_tac >> gvs[deval_rel_cases]
  >- (
    Cases_on `d` >> gvs[decl_step_def, dstep_def] >>
    every_case_tac >> gvs[FST_THM, LAMBDA_PROD] >>
    simp[dstep_result_rel_cases, deval_rel_cases, ctxt_rel_def] >>
    gvs[dstate_rel_def, dget_ffi_def]
    )
  >- (
    Cases_on `db2` >> gvs[SF dsmallstep_ss, SF ditree_ss]
    >- simp[dstep_result_rel_cases] >>
    Cases_on `h` >> gvs[SF dsmallstep_ss, SF ditree_ss] >>
    Cases_on `l` >> gvs[SF dsmallstep_ss, SF ditree_ss] >>
    simp[dstep_result_rel_cases, deval_rel_cases, dget_ffi_def]
    ) >>
  Cases_on `ev` >> gvs[]
  >- (
    `¬is_Effi (estep (env',dsta.refs,dsta.fp_state,Exp e,cs))` by gvs[is_Dffi_eq_is_Effi_single] >>
    simp[dstep_ExpVal_Exp, decl_step_ExpVal_Exp] >>
    drule_at Any step_result_rel_single >>
    simp[Once step_result_rel_cases, PULL_EXISTS] >>
    disch_then drule >> disch_then $ qspec_then `db0.ffi` assume_tac >>
    rgs[dstate_rel_def, get_ffi_def] >>
    pop_assum mp_tac >> rw[step_result_rel_cases] >> gvs[dget_ffi_def, get_ffi_def] >>
    simp[dstep_result_rel_cases, deval_rel_cases, dstate_rel_def]
    )
  >- (
    Cases_on `cs` >> gvs[]
    >- (
      gvs[ctxt_rel_def, SF dsmallstep_ss, SF ditree_ss, dstate_rel_def] >>
      every_case_tac >> gvs[] >>
      gvs[dstep_result_rel_cases, deval_rel_cases, dstate_rel_def, dget_ffi_def]
      ) >>
    gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    gvs[is_Dffi_eq_is_Effi_single] >>
    drule_at Any step_result_rel_single >> simp[FORALL_PROD] >>
    simp[step_result_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, PULL_EXISTS, FORALL_PROD] >> disch_then drule_all >>
    disch_then $ qspec_then `db0.ffi` mp_tac >> rw[] >> gvs[] >>
    gvs[SF dsmallstep_ss, SF ditree_ss] >>
    gvs[dstate_rel_def, dget_ffi_def, get_ffi_def] >>
    gvs[dstep_result_rel_cases, dstate_rel_def, deval_rel_cases, ctxt_rel_def]
    )
  >- (
    Cases_on `cs` >> gvs[]
    >- (
      gvs[ctxt_rel_def, SF dsmallstep_ss, SF ditree_ss, dstate_rel_def] >>
      gvs[dstep_result_rel_cases]
      ) >>
    gvs[ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    gvs[is_Dffi_eq_is_Effi_single] >>
    drule_at Any step_result_rel_single >> simp[FORALL_PROD] >>
    simp[step_result_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, PULL_EXISTS, FORALL_PROD] >> disch_then drule_all >>
    disch_then $ qspec_then `db0.ffi` mp_tac >> rw[] >> gvs[] >>
    gvs[SF dsmallstep_ss, SF ditree_ss] >>
    gvs[dstate_rel_def, dget_ffi_def, get_ffi_def] >>
    gvs[dstep_result_rel_cases, dstate_rel_def, deval_rel_cases, ctxt_rel_def]
    )
QED

Theorem dstep_result_rel_n:
  ∀n dsta deva dcsa db env.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep db) ∧
    ¬ is_Dffi (step_n env n (Dstep dsta deva dcsa))
  ⇒ dstep_result_rel
      (step_n env n (Dstep dsta deva dcsa)) (step_n_cml env n (Dstep db))∧
    ∀ffi. dget_ffi (step_n_cml env n (Dstep db)) = SOME ffi
      ⇒ dget_ffi (Dstep db) = SOME ffi
Proof
  Induct >- simp[step_n_def, step_n_cml_def] >>
  simp[step_n_alt_def, step_n_cml_alt_def] >>
  rpt gen_tac >> strip_tac >>
  last_x_assum drule >> disch_then $ qspec_then `env` mp_tac >>
  impl_tac >- (every_case_tac >> gvs[is_Dffi_def]) >> strip_tac >>
  imp_res_tac dstep_result_rel_cases >> gvs[dget_ffi_def] >>
  drule dstep_result_rel_single >> disch_then $ qspec_then `env` mp_tac >>
  simp[] >> rw[] >> gvs[dget_ffi_def]
QED


(******************** Relating FFI steps ********************)

Theorem estep_to_Effi:
  estep ea = Effi (ExtCall s) conf ws lnum env st cs ⇔
  ∃env' conf' fp' b.
    conf = MAP (λc. n2w (ORD c)) (EXPLODE conf') ∧
    ea = (env',st,fp',Val (Litv (StrLit conf')),
            (Capp (FFI s) [Loc b lnum] [],env)::cs) ∧
    store_lookup lnum st = SOME (W8array ws) ∧ s ≠ ""
Proof
  PairCases_on `ea` >> Cases_on `ea3` >> gvs[SF itree_ss]
  >- (
    Cases_on `e` >> gvs[SF itree_ss] >> every_case_tac >> gvs[] >>
    simp[application_thm] >> every_case_tac >> gvs[SF itree_ss]
    ) >>
  Cases_on `ea4` >> gvs[SF itree_ss] >>
  PairCases_on `h` >> reverse $ Cases_on `h0` >> gvs[SF itree_ss] >>
  every_case_tac >> gvs[]
  >- (Cases_on `l0` >> gvs[SF itree_ss] >> every_case_tac >> gvs[])
  >- (
    Cases_on `l` >> gvs[SF itree_ss] >>
    Cases_on `h` >> gvs[SF itree_ss] >> every_case_tac >> gvs[]
    ) >>
  Cases_on `l0` >> gvs[SF itree_ss] >> reverse eq_tac >> rw[]
  >- simp[application_thm] >>
  drule application_eq_Effi_fields >> rw[] >>
  gvs[application_thm] >> every_case_tac >> gvs[]
QED

Theorem dstep_to_Dffi:
  dstep env dst dev dcs =
  Dffi dst' (ExtCall s,ws1,ws2,lnum,env',cs) locs pat dcs' ⇔
  ∃env'' conf b.
    dst = dst' ∧ dcs = dcs' ∧
    dev = ExpVal env'' (Val (Litv (StrLit conf)))
            ((Capp (FFI s) [Loc b lnum] [],env')::cs) locs pat ∧
    ws1 = MAP (λc. n2w (ORD c)) (EXPLODE conf) ∧
    store_lookup lnum dst.refs = SOME (W8array ws2) ∧ s ≠ ""
Proof
  Cases_on `∃d. dev = Decl d` >> gvs[dstep_def]
  >- (Cases_on `d` >> gvs[dstep_def] >> every_case_tac >> gvs[]) >>
  Cases_on `∃e. dev = Env e` >> gvs[dstep_def]
  >- (
    Cases_on `dcs` >> gvs[SF ditree_ss] >>
    Cases_on `h` >> Cases_on `l` >> gvs[SF ditree_ss]
    ) >>
  Cases_on `dev` >> gvs[SF ditree_ss] >> rw[] >> reverse eq_tac >> rw[]
  >- simp[SF ditree_ss, SF itree_ss, application_thm, dstate_component_equality] >>
  `is_Dffi (dstep env dst (ExpVal s' e l l0 p) dcs)` by gvs[is_Dffi_def] >>
  gvs[is_Dffi_eq_is_Effi_single, is_Effi_def, estep_to_Effi] >>
  rw[] >> gvs[SF ditree_ss, SF itree_ss, application_thm] >>
  simp[dstate_component_equality]
QED

Theorem decl_step_ffi_changed_dstep_to_Dffi:
  decl_step env (dst2, dev2, dcs) = Dstep (dst2', dev2', dcs') ∧
  dst2.ffi ≠ dst2'.ffi ∧
  dstate_rel dst1 dst2 ∧ deval_rel dev1 dev2 ⇒
  ∃env' env'' conf s lnum ccs locs pat ws b.
    dev1 = ExpVal env' (Val $ Litv $ StrLit conf)
            ((Capp (FFI s) [Loc b lnum] [], env'') :: ccs) locs pat ∧
    store_lookup lnum dst1.refs = SOME (W8array ws) ∧
    dstep env dst1 dev1 dcs = Dffi dst1
      (ExtCall s,MAP (λc. n2w $ ORD c) (EXPLODE conf),ws,lnum,env'',ccs)
      locs pat dcs'
Proof
  rw[] >> drule_all decl_step_ffi_changed >> rw[] >>
  gvs[deval_rel_cases, ctxt_rel_def, dstate_rel_def] >>
  pairarg_tac >> gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
  gvs[SF ditree_ss, SF itree_ss] >>
  simp[application_thm, dstate_component_equality] >>
  gvs[SF dsmallstep_ss, SF smallstep_ss, cml_application_thm] >>
  gvs[semanticPrimitivesTheory.do_app_def, ffiTheory.call_FFI_def] >>
  gvs[store_assign_def, store_lookup_def, store_v_same_type_def]
QED

Theorem dstep_result_rel_single_FFI:
  ∀dsta deva dcsa db env dsta' s ws1 ws2 n env' cs ffi_call locs pat dcsa'.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep db) ∧
    dstep env dsta deva dcsa =
    Dffi dsta' (ExtCall s,ws1,ws2,n,env',cs) locs pat dcsa'
  ⇒ ∃ffi.
      dget_ffi (Dstep db) = SOME ffi ∧
      ((∃ffi'. dget_ffi (decl_step env db) = SOME ffi' ∧ ffi' ≠ ffi) ∨
       (∃outcome fp.
          decl_step env db =
          Dabort (fp, (Rffi_error $ Final_event (ExtCall s) ws1 ws2 outcome))))
Proof
  ntac 3 gen_tac >> PairCases >> rw[] >>
  gvs[dstep_result_rel_cases, dstep_to_Dffi, dget_ffi_def] >>
  gvs[deval_rel_cases, ctxt_rel_def] >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> pairarg_tac >> gvs[] >>
  simp[SF dsmallstep_ss, SF smallstep_ss, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def, ffiTheory.call_FFI_def] >>
  every_case_tac >> gvs[dget_ffi_def] >>
  gvs[store_lookup_def, store_assign_def, store_v_same_type_def, dstate_rel_def] >>
  rw[ffi_state_component_equality] >>
  simp[combinTheory.o_DEF, stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem step_result_rel_single_FFI_error:
  ∀ea eb.
    step_result_rel (Estep ea) (Estep eb) ∧
    e_step eb = Eabort (fp, (Rffi_error (Final_event s conf ws outcome)))
  ⇒ ∃lnum env. estep ea =
    Effi s conf ws lnum env (FST $ SND ea) (TL $ SND $ SND $ SND $ SND ea)
Proof
  cheat (*
  rpt $ PairCases >> rw[e_step_def] >> gvs[AllCaseEqs(), SF smallstep_ss] >>
  gvs[cml_application_thm, AllCaseEqs(), SF smallstep_ss] >>
  gvs[semanticPrimitivesPropsTheory.do_app_cases, AllCaseEqs()] >>
  gvs[step_result_rel_cases, ctxt_rel_def] >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> pairarg_tac >> gvs[] >>
  simp[SF itree_ss, application_def] >> gvs[call_FFI_def, AllCaseEqs()] >>
  gs[semanticPrimitivesTheory.do_fprw_def] >> every_case_tac >> gs[] >>
  simp[combinTheory.o_DEF, stringTheory.IMPLODE_EXPLODE_I] *)
QED

Theorem dstep_result_rel_single_FFI_strong:
  ∀dsta deva dcsa dstb devb dcsb env dsta' s conf ws lnum eenv cs1 locs pat
   dcsa'.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep (dstb, devb, dcsb)) ∧
    dstep env dsta deva dcsa =
    Dffi dsta' (ExtCall s,conf,ws,lnum,eenv,cs1) locs pat dcsa'
  ⇒ ∃env' ffi conf' cs2 fp b.
      conf = MAP (λc. n2w (ORD c)) (EXPLODE conf') ∧
      deva = ExpVal env' (Val (Litv $ StrLit conf'))
              ((Capp (FFI s) [Loc b lnum] [], eenv)::cs1) locs pat ∧
      devb = ExpVal env' (Val (Litv $ StrLit conf'))
              ((Capp (FFI s) [Loc b lnum] () [], eenv)::cs2) locs pat ∧
      store_lookup lnum dsta.refs = SOME (W8array ws) ∧ s ≠ "" ∧
      dget_ffi (Dstep (dstb, devb, dcsb)) = SOME ffi ∧
      decl_step env (dstb, devb, dcsb) =
        case ffi.oracle (ExtCall s) ffi.ffi_state conf ws of
        | Oracle_return ffi' ws' =>
            if LENGTH ws' ≠ LENGTH ws then
              Dabort (fp,
                      Rffi_error $ Final_event (ExtCall s) conf ws FFI_failed)
            else
              Dstep (
                dstb with <|
                  refs := LUPDATE (W8array ws') lnum dstb.refs;
                  ffi := dstb.ffi with <|
                    ffi_state := ffi';
                    io_events := dstb.ffi.io_events ++
                                 [IO_event (ExtCall s) conf (ZIP (ws,ws'))]
                    |>
                  |>,
                ExpVal eenv (Val $ Conv NONE []) cs2 locs pat, dcsb)
        | Oracle_final outcome =>
            Dabort (fp, Rffi_error $ Final_event (ExtCall s) conf ws outcome)
Proof
  rw[] >> gvs[dstep_to_Dffi, dstep_result_rel_cases, deval_rel_cases, ctxt_rel_def] >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> pairarg_tac >> gvs[] >>
  simp[dget_ffi_def, SF dsmallstep_ss, SF smallstep_ss, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def, ffiTheory.call_FFI_def] >>
  gvs[dstate_rel_def] >> every_case_tac >> gvs[] >>
  gvs[store_assign_def, store_lookup_def, store_v_same_type_def,
      semanticPrimitivesTheory.state_component_equality] >>
  gvs[combinTheory.o_DEF, stringTheory.IMPLODE_EXPLODE_I]
QED

Theorem dstep_result_rel_single_FFI_error:
  ∀dsta deva dcsa dstb devb dcsb.
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep (dstb,devb,dcsb)) ∧
    decl_step env (dstb,devb,dcsb) =
    Dabort (fp, (Rffi_error (Final_event (ExtCall s) conf ws outcome)))
  ⇒ ∃lnum env' cs locs pat.
      dstep env dsta deva dcsa =
      Dffi dsta (ExtCall s,conf,ws,lnum,env',cs) locs pat dcsa
Proof
  rw[] >> Cases_on `∃d. deva = Decl d` >> gvs[]
  >- (
    gvs[dstep_result_rel_cases, deval_rel_cases] >>
    Cases_on `d` >> gvs[SF dsmallstep_ss, SF ditree_ss] >>
    every_case_tac >> gvs[]
    ) >>
  Cases_on `∃e. deva = Env e` >> gvs[]
  >- (
    gvs[dstep_result_rel_cases, deval_rel_cases] >>
    Cases_on `e` >> gvs[SF dsmallstep_ss, SF ditree_ss] >>
    every_case_tac >> gvs[]
    ) >>
  Cases_on `deva` >> gvs[dstep_result_rel_cases, deval_rel_cases] >>
  gvs[SF dsmallstep_ss] >>
  qmatch_asmsub_abbrev_tac `e_step_result_CASE foo` >>
  qspec_then `(s',(dstb.refs,dstb.ffi),dstb.fp_state,e,scs)` mp_tac $
    (step_result_rel_single_FFI_error
       |> Q.INST [‘s’ |-> ‘ExtCall ss’]
       |> Q.INST [‘ss’ |-> ‘s’]
       |> SIMP_RULE std_ss [Once SWAP_FORALL_THM])  >>
  simp[step_result_rel_cases, PULL_EXISTS] >> disch_then drule >>
  simp[estep_to_Effi] >> strip_tac >> unabbrev_all_tac >>
  Cases_on `e` >> gvs[] >- (every_case_tac >> gvs[]) >>
  Cases_on `scs` >> gvs[ctxt_rel_def] >- (every_case_tac >> gvs[]) >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  every_case_tac >> gvs[] >>
  gvs[SF ditree_ss, SF itree_ss, application_thm, dstate_rel_def] >>
  simp[dstate_component_equality]
QED

Theorem dstep_result_rel_single':
  ∀dsta deva dcsa d2 env.
    (∀ffi. dget_ffi (decl_step env d2) = SOME ffi ⇒ dget_ffi (Dstep d2) = SOME ffi) ∧
    (∀a fp. decl_step env d2 ≠ Dabort (fp, Rffi_error a)) ∧
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep d2)
    ⇒ dstep_result_rel (dstep env dsta deva dcsa) (decl_step env d2)
Proof
  rw[] >> drule dstep_result_rel_single >> rw[] >>
  gvs[IMP_CONJ_THM, FORALL_AND_THM] >>
  first_x_assum irule >> CCONTR_TAC >> gvs[is_Dffi_def] >>
  PairCases_on `ev0` >> drule_all dstep_result_rel_single_FFI >> rw[] >> gvs[]
QED

Theorem dstep_result_rel_n':
  ∀n dsta deva dcsa db env.
    dget_ffi (step_n_cml env n (Dstep db)) = dget_ffi (Dstep db) ∧
    dstep_result_rel (Dstep dsta deva dcsa) (Dstep db)
  ⇒ dstep_result_rel
      (step_n env n (Dstep dsta deva dcsa)) (step_n_cml env n (Dstep db))
Proof
  Induct >- rw[step_n_def, step_n_cml_def] >> rw[] >>
  `dstep_result_rel
    (step_n env n (Dstep dsta deva dcsa)) (step_n_cml env n (Dstep db))` by (
    last_x_assum irule >> simp[] >>
    qspecl_then [`SUC n`,`Dstep db`] mp_tac step_n_cml_preserved_FFI >>
    Cases_on `step_n_cml env (SUC n) (Dstep db)` >> gvs[dget_ffi_def] >>
    PairCases_on `db` >> gvs[dget_ffi_def]) >>
  simp[step_n_alt_def, step_n_cml_alt_def] >>
  rgs[dstep_result_rel_cases] >> gvs[] >>
  gvs[GSYM dstep_result_rel_cases, PULL_EXISTS, dget_ffi_def] >>
  qspecl_then [`SUC n`,`Dstep (st',dev2',dcsa)`]
    mp_tac step_n_cml_preserved_FFI >>
  gvs[step_n_cml_alt_def] >>
  Cases_on `decl_step env (st,dev2,dcs)` >> gvs[dget_ffi_def] >>
  disch_then $ qspecl_then [`p`,`env`] mp_tac >> simp[] >>
  disch_then $ qspec_then `n` mp_tac >> simp[dget_ffi_def] >> rw[] >> gvs[] >>
  qpat_assum `decl_step _ _ = _` $ once_rewrite_tac o single o GSYM >>
  irule dstep_result_rel_single' >>
  simp[dget_ffi_def, dstep_result_rel_cases]
QED


(******************** interp ********************)
Theorem st_fp_state_st[local,simp]:
  st with fp_state := st.fp_state = (st:'a semanticPrimitives$state)
Proof
  gs[semanticPrimitivesTheory.state_component_equality]
QED

Theorem interp_Ret_Termination:
  dstate_rel dst st ∧ deval_rel deva devb ⇒
  (
    interp env (Dstep dst deva dcs) = Ret Termination ⇔
    (∃v st'. small_eval_dec env (st,devb,dcs) (st', Rval v) ∧ st.ffi = st'.ffi) ∨
    (∃v st'. small_eval_dec env (st,devb,dcs) (st', Rerr (Rraise v)) ∧ st.ffi = st'.ffi)
  )
Proof
  rw[Once interp] >> eq_tac >> rw[]
  >- (
    every_case_tac >> gvs[step_until_halt_def] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >>
    every_case_tac >> gvs[is_halt_def]
    >- (
      Induct_on `x` >> gvs[step_n_alt_def] >>
      reverse every_case_tac >> gvs[] >- metis_tac[] >- metis_tac[] >>
      rw[dstep_to_Ddone] >> disj1_tac >>
      rw[small_eval_dec_eq_step_n_cml, PULL_EXISTS] >>
      qspecl_then [`x`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
        assume_tac dstep_result_rel_n >>
      gvs[is_Dffi_def, dstep_result_rel_cases, deval_rel_cases] >>
      goal_assum drule >> gvs[dget_ffi_def]
      )
    >- (
      Induct_on `x` >> gvs[step_n_alt_def] >>
      every_case_tac >> gvs[] >> rw[] >>
      rw[small_eval_dec_eq_step_n_cml, PULL_EXISTS] >> disj2_tac >>
      qspecl_then [`x`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
        assume_tac dstep_result_rel_n >>
      gvs[is_Dffi_def, dstep_result_rel_cases]  >>
      qspecl_then [`d`,`d0`,`l`,`(st',dev2,l)`,`env`]
        assume_tac dstep_result_rel_single >>
      gvs[is_Dffi_def, dstep_result_rel_cases, dget_ffi_def] >>
      PairCases_on ‘p’ >> qexists_tac ‘p1’ >>
      qexists_tac ‘st' with fp_state := p0’ >> gs[] >>
      qexists_tac ‘x’ >> qexists_tac ‘dev2’ >> qexists_tac ‘l’ >>
      qexists_tac ‘st'.fp_state’ >> gs[]
      )
    )
  >- (
    gvs[small_eval_dec_eq_step_n_cml, step_until_halt_def] >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n >>
    gvs[dstep_result_rel_cases, dget_ffi_def] >>
    pop_assum mp_tac >> impl_tac
    >- (
      irule dstep_result_rel_not_Dffi >> irule_at Any dstep_result_rel_n' >>
      qexists_tac `(st,devb,dcs)` >> simp[dget_ffi_def, dstep_result_rel_cases]
      ) >>
    strip_tac >> pop_assum mp_tac >> rw[deval_rel_cases] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (qexists_tac `SUC n` >> simp[step_n_alt_def, SF ditree_ss, is_halt_def]) >>
    `step_n env x (Dstep dst deva dcs) = step_n env (SUC n) (Dstep dst deva dcs)` by (
      irule is_halt_step_n_eq >> simp[step_n_alt_def, SF ditree_ss, is_halt_def]) >>
    gvs[step_n_alt_def, SF ditree_ss]
    )
  >- (
    gvs[small_eval_dec_eq_step_n_cml, step_until_halt_def] >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n >>
    gvs[dstep_result_rel_cases, dget_ffi_def] >>
    pop_assum mp_tac >> impl_tac
    >- (
      irule dstep_result_rel_not_Dffi >> irule_at Any dstep_result_rel_n' >>
      qexists_tac `(st,devb,dcs)` >> simp[dget_ffi_def, dstep_result_rel_cases]
      ) >>
    strip_tac >>
    qspecl_then [`dst'`,`dev1`,`dcs'`,`(st' with fp_state := fp,dev,dcs')`,`env`]
      assume_tac dstep_result_rel_single' >>
    gvs[dget_ffi_def, dstep_result_rel_cases] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (qexists_tac `SUC n` >> simp[step_n_alt_def, SF ditree_ss, is_halt_def]) >>
    `step_n env x (Dstep dst deva dcs) = step_n env (SUC n) (Dstep dst deva dcs)` by (
      irule is_halt_step_n_eq >> simp[step_n_alt_def, SF ditree_ss, is_halt_def]) >>
    gvs[step_n_alt_def, SF ditree_ss]
    )
QED

Theorem interp_Ret_Error:
  dstate_rel dst st ∧ deval_rel deva devb ⇒
  (
    interp env (Dstep dst deva dcs) = Ret Error ⇔
    ∃st'. small_eval_dec env (st,devb,dcs) (st',Rerr $ Rabort Rtype_error) ∧
          st.ffi = st'.ffi
  )
Proof
  rw[Once interp] >> eq_tac >> rw[]
  >- (
    every_case_tac >> gvs[step_until_halt_def] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >>
    every_case_tac >> gvs[is_halt_def] >>
    simp[small_eval_dec_eq_step_n_cml, PULL_EXISTS] >>
    qspecl_then [`x`,`env`,`Dstep dst deva dcs`]
      assume_tac is_halt_step_n_min >>
    gvs[is_halt_def] >> qpat_x_assum `step_n _ x _ = _` kall_tac >>
    Cases_on `m` >> gvs[step_n_alt_def] >>
    reverse every_case_tac >> gvs[]
    >- (first_x_assum $ qspec_then `n` mp_tac >> simp[is_halt_def]) >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n >>
    gvs[dstep_result_rel_cases, is_Dffi_def] >>
    qspecl_then [`d`,`d0`,`l`,`(st',dev2,l)`,`env`]
      assume_tac dstep_result_rel_single >>
    gvs[dstep_result_rel_cases, is_Dffi_def, dget_ffi_def] >>
    qexists_tac ‘st' with fp_state := f’ >> gs[] >>
    qexists_tac ‘n’ >> qexists_tac ‘dev2’ >> qexists_tac ‘l’ >>
    qexists_tac ‘st'.fp_state’ >> gs[]
    )
  >- (
    gvs[small_eval_dec_eq_step_n_cml] >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n' >>
    gvs[dstep_result_rel_cases, is_Dffi_def, dget_ffi_def] >>
    qspecl_then [`dst'`,`dev1`,`dcs'`,`(st' with fp_state := fp,dev,dcs')`,`env`]
      assume_tac dstep_result_rel_single' >>
    gvs[dstep_result_rel_cases, dget_ffi_def] >>
    simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (qexists_tac `SUC n` >> simp[step_n_alt_def, is_halt_def]) >>
    `step_n env x (Dstep dst deva dcs) = step_n env (SUC n) (Dstep dst deva dcs)` by (
      irule is_halt_step_n_eq >> simp[step_n_alt_def, is_halt_def]) >>
    gvs[step_n_alt_def]
    )
QED

Theorem interp_Div:
  dstate_rel dst st ∧ deval_rel deva devb ⇒
  (
    interp env (Dstep dst deva dcs) = Div ⇔
    ∀n. ∃st2.
      step_n_cml env n (Dstep (st,devb,dcs)) = Dstep st2 ∧
      ¬is_halt_cml (Dstep st2) ∧
      dget_ffi (Dstep st2) = SOME st.ffi
  )
Proof
  rw[Once interp] >> eq_tac >> rw[]
  >- (
    gvs[step_until_halt_def] >> every_case_tac >> gvs[] >>
    pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> rw[] >>
    pop_assum $ qspec_then `n` assume_tac >>
    Cases_on `step_n env n (Dstep dst deva dcs)` >> gvs[is_halt_def] >>
    qspecl_then [`n`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n >>
    gvs[dstep_result_rel_cases, is_Dffi_def] >>
    gvs[is_halt_cml_def, dget_ffi_def]
    )
  >- (
    simp[step_until_halt_def] >>
    DEEP_INTRO_TAC some_intro >> rw[] >>
    first_x_assum $ qspec_then `x` assume_tac >> gvs[is_halt_cml_def] >>
    qspecl_then [`x`,`dst`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      assume_tac dstep_result_rel_n' >>
    gvs[dstep_result_rel_cases, dget_ffi_def, is_halt_def]
    )
QED


(******************** trace_prefix ********************)

Theorem dstep_not_SharedMem:
  ∀benv st decl c st' ffiname ws1 ws2 n env' ec locs p c'.
  dstep benv st decl c = Dffi st' (ffiname,ws1,ws2,n,env',ec) locs p c' ==>
  ffiname <> SharedMem mop
Proof
  recInduct dstep_ind >>
  rw[dstep_def] >>
  gvs[DefnBase.one_line_ify NONE dcontinue_def,AllCaseEqs()] >>
  gvs[DefnBase.one_line_ify NONE estep_def,AllCaseEqs(),
    push_def,return_def] >>
  gvs[DefnBase.one_line_ify NONE application_def,AllCaseEqs(),
    return_def,push_def] >>
  gvs[DefnBase.one_line_ify NONE continue_def,AllCaseEqs(),
     return_def,push_def,
     DefnBase.one_line_ify NONE application_def] >>
  gvs[DefnBase.one_line_ify NONE exn_continue_def,AllCaseEqs(),
    return_def,push_def]
QED

(* use FFI instead of SharedMem *)
Theorem do_app_not_SharedMem:
  semanticPrimitives$do_app s op vs ≠ SOME (v, Rerr (Rabort (Rffi_error (Final_event (SharedMem
  s') conf ws outcome))))
Proof
  cheat (*
  rpt strip_tac >>
  gvs[DefnBase.one_line_ify NONE semanticPrimitivesTheory.do_app_def,
    AllCaseEqs(),call_FFI_def] >>
  rw[] >>
  pairarg_tac >> fs[] *)
QED

Theorem application_not_SharedMem:
  smallStep$application op env (refs,ffi) fp_state vs vs' ≠
    Eabort (fp,Rffi_error (Final_event (SharedMem s') conf ws outcome))
Proof
  rpt strip_tac >>
  gvs[smallStepTheory.application_def,AllCaseEqs(),SF smallstep_ss,
    do_app_not_SharedMem] >>
  gvs[semanticPrimitivesTheory.do_fprw_def,AllCaseEqs()]
QED

Theorem decl_step_not_SharedMem:
  decl_step env (st,devb,dcs) ≠ Dabort (fp,Rffi_error (Final_event (SharedMem
  s') conf ws outcome))
Proof
  strip_tac >>
  gvs[decl_step_def,AllCaseEqs(),decl_continue_def] >>
  gvs[DefnBase.one_line_ify NONE e_step_def,AllCaseEqs(),SF smallstep_ss] >>
  gvs[application_not_SharedMem]
QED

Theorem trace_prefix_dec_Error:
  dstate_rel dsta st ∧ deval_rel deva devb ⇒

  ((∃n. trace_prefix n (oracle, ffi_st)
    (interp env (Dstep dsta deva dcs)) = (io, SOME Error)) ⇔

  ∃dst ffi' fp.
    (decl_step_reln env)^*
      (st with ffi := st.ffi with <| oracle := oracle; ffi_state := ffi_st |>,
       devb, dcs) dst ∧
    dget_ffi (Dstep dst) = SOME ffi' ∧
    ffi'.io_events = st.ffi.io_events ++ io ∧
    decl_step env dst = Dabort (fp, Rtype_error))
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`devb`,`env`,`io`,`n`] >>
    Induct >> rw[trace_prefix_interp] >>
    gvs[step_until_halt_def] >> every_case_tac >> gvs[]
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n env l (Dstep dsta deva dcs)` >> gvs[] >>
      gvs[step_n_alt_def, is_halt_def] >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      qmatch_goalsub_abbrev_tac `RTC _ (st',_)` >>
      qspecl_then [`l`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[dstep_result_rel_cases, is_Dffi_def] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      rw[decl_step_reln_eq_step_n_cml, PULL_EXISTS] >> goal_assum drule >>
      simp[dget_ffi_def] >> unabbrev_all_tac >>
      gvs[state_component_equality, ffi_state_component_equality] >>
      qspecl_then [`dsta'`,`deva'`,`dcs'`,`(st'',dev2,dcs')`,`env`]
        mp_tac dstep_result_rel_single >>
      simp[dstep_result_rel_cases, is_Dffi_def]
      )
    >- (pairarg_tac >> gvs[trace_prefix_def])
    >- (
      pairarg_tac >> gvs[] >>
      rename1 `ExpVal env' _ cs locs pat` >>
      rename1 `Dffi dst (s,ws1,ws2,lnum,env'',_) _ _ dcs'` >>
      rename1 `_ conf ws = Oracle_return ffi_st' ws'` >>
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
      pop_assum $ qspec_then `l` assume_tac >> gvs[] >>
      Cases_on `step_n env l (Dstep dsta deva dcs)` >> gvs[is_halt_def] >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`l`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[dstep_result_rel_cases, is_Dffi_def, dget_ffi_def] >>
      impl_tac >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      gvs[step_n_alt_def] >>
      rw[Once RTC_CASES_RTC_TWICE, PULL_EXISTS] >>
      rw[Once RTC_CASES2] >> irule_at Any OR_INTRO_THM2 >>
      simp[PULL_EXISTS, GSYM CONJ_ASSOC] >>
      rw[decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      goal_assum drule >> rw[decl_step_reln_def] >>
      Cases_on ‘s’>>fs[]>-
               (
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases, PULL_EXISTS] >>
      disch_then drule_all >> strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[ffi_state_component_equality] >>
      qmatch_goalsub_abbrev_tac `Dstep (st2,ev,ll)` >>
      last_x_assum $ drule_at $ Pos last >>
      qpat_x_assum `deval_rel _ _` mp_tac >>
      simp[deval_rel_cases, ctxt_rel_def, PULL_EXISTS] >>
      simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> strip_tac >>
      disch_then $ drule_at Any >>
      disch_then $ qspec_then `st2` mp_tac >>
      impl_tac >- (unabbrev_all_tac >> gvs[dstate_rel_def, dstep_to_Dffi]) >>
      simp[decl_step_reln_eq_step_n_cml] >> rw[] >> gvs[] >>
      qmatch_asmsub_abbrev_tac `step_n_cml _ _ (Dstep (st3,_))` >>
      `st3 = st2` by (unabbrev_all_tac >>
        gvs[semanticPrimitivesTheory.state_component_equality,
            ffi_state_component_equality]) >>
      gvs[dstep_to_Dffi] >> goal_assum drule >> simp[] >>
      unabbrev_all_tac >> gvs[]
               )>>
        metis_tac[dstep_not_SharedMem]
      )
    )
  >- (
    simp[decl_step_reln_eq_step_n_cml] >>
    simp[PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >> gen_tac >>
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`ffi'`,
        `dst`,`devb`,`env`,`io`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[step_n_cml_def] >>
      qexists_tac `SUC 0` >> once_rewrite_tac[trace_prefix_interp] >>
      simp[step_until_halt_def] >>
      `dstep env dsta deva dcs = Dtype_error fp` by (
        qmatch_asmsub_abbrev_tac `Dstep (st',_)` >>
        qspecl_then [`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
          assume_tac dstep_result_rel_single' >>
        gvs[dget_ffi_def, dstep_result_rel_cases] >>
        pop_assum irule >> unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >> simp[is_halt_def]) >>
      Cases_on `x` >> gvs[step_n_def, is_halt_def] >> gvs[dget_ffi_def]
      ) >>
    gvs[step_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `decl_step _ (st2,_)` >>
    Cases_on `decl_step env (st2,devb,dcs)` >> gvs[] >>
    Cases_on `dget_ffi (Dstep p) = SOME st2.ffi`
    >- (
      qspecl_then [`dsta`,`deva`,`dcs`,`(st2,devb,dcs)`,`env`]
        mp_tac dstep_result_rel_single' >>
      simp[dget_ffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      last_x_assum $ qspecl_then [
        `io`,`env`,`dev2`,`dst`,`ffi'`,
        `st'`,`ffi_st`,`oracle`,`dcs'`,`dev1`,`dst'`] mp_tac >>
      simp[] >> qpat_x_assum `_.ffi = _` $ assume_tac o GSYM >> simp[] >>
      `st' with ffi := st'.ffi = st'` by
        rw[semanticPrimitivesTheory.state_component_equality] >> rw[] >>
      qexists_tac `n'` >> pop_assum mp_tac >>
      Cases_on `n'` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
      ) >>
    PairCases_on `p` >> gvs[dget_ffi_def] >>
    rename1 `dget_ffi _ = SOME ffi_new` >>
    rename1 `Dstep (st2',devb',dcs')` >>
    drule decl_step_ffi_changed >> simp[] >>
    drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >>
    disch_then $ qspecl_then [`dsta`,`deva`] mp_tac >> simp[] >> impl_tac
    >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
    strip_tac >> strip_tac >> gvs[] >>
    unabbrev_all_tac >>
    qpat_x_assum `dstate_rel _ _` mp_tac >> rw[dstate_rel_def] >> gvs[] >>
    gvs[ffi_state_component_equality] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
    simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >>
      simp[dstep_def, SF ditree_ss, is_halt_def]
      ) >>
    Cases_on `x` >> gvs[step_n_def, is_halt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >> simp[deval_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    qmatch_asmsub_abbrev_tac `step_n_cml _ _ (Dstep (st2,dev2,_))` >>
    last_x_assum $ qspecl_then [
      `TL io`,`env`,`dev2`,`dst`,`ffi_new`,`st2`,`ffi_st'`,`oracle`,`dcs`] mp_tac >>
    simp[Abbr `dev2`, deval_rel_cases, PULL_EXISTS] >> disch_then $ drule_at Any >>
    disch_then $
      qspec_then `dsta with refs := LUPDATE (W8array ws'') lnum dsta.refs` mp_tac >>
    qmatch_goalsub_abbrev_tac `Dstep (st3,_)` >>
    `st3 = st2` by (unabbrev_all_tac >> gvs[dstate_rel_def]) >> gvs[] >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[] >> unabbrev_all_tac >> gvs[]
    >- (qexists_tac `n'` >> simp[])
    >- gvs[dstate_rel_def] >>
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `dst` >> gvs[dget_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_dec_Termination:
  dstate_rel dsta st ∧ deval_rel deva devb ⇒

  ((∃n. trace_prefix n (oracle, ffi_st)
    (interp env (Dstep dsta deva dcs)) = (io, SOME Termination)) ⇔

  ∃dst ffi'.
    (decl_step_reln env)^*
      (st with ffi := st.ffi with <| oracle := oracle; ffi_state := ffi_st |>,
       devb, dcs) dst ∧
    dget_ffi (Dstep dst) = SOME ffi' ∧
    ffi'.io_events = st.ffi.io_events ++ io ∧
    (decl_step env dst = Ddone ∨ ∃v. decl_step env dst = Draise v))
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`devb`,`env`,`io`,`dcs`,`n`] >>
    Induct >> rw[trace_prefix_interp] >>
    gvs[step_until_halt_def] >> every_case_tac >> gvs[]
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      Cases_on `x` >- gvs[step_n_def, is_halt_def] >>
      gvs[step_n_alt_def] >> every_case_tac >> gvs[is_halt_def]
      )
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[step_n_def, is_halt_def] >>
      gvs[step_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[is_halt_def]) >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> simp[decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[ffi_state_component_equality] >>
      disj1_tac >> rgs[dstep_to_Ddone, Once deval_rel_cases, SF dsmallstep_ss]
      )
    >- (
      qpat_x_assum `(some n. _ ) = _` mp_tac >>
      DEEP_INTRO_TAC some_intro >> rw[] >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      drule is_halt_step_n_min >> strip_tac >> gvs[] >>
      qpat_x_assum `step_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[step_n_def, is_halt_def] >>
      gvs[step_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[is_halt_def]) >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> simp[decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[ffi_state_component_equality] >>
      disj2_tac >>
      qspecl_then [`d`,`d0`,`l`,`(st'',dev2,l)`,`env`]
       mp_tac dstep_result_rel_single >>
      simp[is_Dffi_def, dstep_result_rel_cases]
      )
    >- gvs[trace_prefix_interp]
    >- (
      pairarg_tac >> gvs[] >>
      last_x_assum $ drule_at $ Pos last >> simp[deval_rel_cases, PULL_EXISTS] >>
      strip_tac >> qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`x`,`env`,`Dstep dsta deva dcs`]
        assume_tac is_halt_step_n_min >> gvs[is_halt_def] >>
      qpat_x_assum `step_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[step_n_def, is_halt_def] >>
      gvs[step_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[is_halt_def]) >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >>
      simp[Once RTC_CASES_RTC_TWICE, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      simp[Once decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      rename1 `Dffi dst (s,conf,ws,lnum,env',cs) locs pat` >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      qmatch_goalsub_abbrev_tac `_ ++ [new_event]` >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      Cases_on ‘s’>>fs[]>- (
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then drule_all >>
      strip_tac >> gvs[Abbr `st'`] >>
      gvs[dget_ffi_def, ffi_state_component_equality] >>
      rgs[Once deval_rel_cases, ctxt_rel_def] >> gvs[] >>
      gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
      first_x_assum $ drule_at Any >>
      disch_then $ qspec_then
        `st'' with <|
          refs := LUPDATE (W8array l') lnum st''.refs;
          ffi := st''.ffi with io_events := st''.ffi.io_events ++ [new_event]
          |>` mp_tac >>
      impl_tac >- (unabbrev_all_tac >> gvs[dstep_to_Dffi, dstate_rel_def]) >>
      strip_tac >> gvs[] >>
      simp[Once RTC_CASES1] >> irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
      simp[decl_step_reln_def] >>
      qmatch_goalsub_abbrev_tac `(sta,_)` >>
      qmatch_asmsub_abbrev_tac `RTC _ (stb,_)` >>
      `sta = stb` by (
        unabbrev_all_tac >> gvs[dstep_to_Dffi] >>
        rw[semanticPrimitivesTheory.state_component_equality,
           ffi_state_component_equality]) >>
      unabbrev_all_tac >> gvs[dstep_to_Dffi] >>
      goal_assum drule >> goal_assum drule >> simp[])>>
      metis_tac[dstep_not_SharedMem]
      )
    )
  >- (
    simp[decl_step_reln_eq_step_n_cml] >>
    simp[PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >> gen_tac >>
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`ffi'`,
        `dst`,`devb`,`env`,`io`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[step_n_cml_def] >>
      qexists_tac `SUC 0` >> once_rewrite_tac[trace_prefix_interp] >>
      simp[step_until_halt_def] >>
      `dstep env dsta deva dcs = Ddone` by (
        qmatch_asmsub_abbrev_tac `Dstep (st',_)` >>
        qspecl_then [`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
          assume_tac dstep_result_rel_single' >>
        gvs[dget_ffi_def, dstep_result_rel_cases] >>
        pop_assum irule >> unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >> simp[is_halt_def]) >>
      Cases_on `x` >> gvs[step_n_def, is_halt_def] >> gvs[dget_ffi_def]
      ) >>
    gvs[step_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `(st2,_)` >>
    Cases_on `decl_step env (st2,devb,dcs)` >> gvs[] >>
    Cases_on `dget_ffi (Dstep p) = SOME st2.ffi`
    >- (
      qspecl_then [`dsta`,`deva`,`dcs`,`(st2,devb,dcs)`,`env`]
        mp_tac dstep_result_rel_single' >>
      simp[dget_ffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      last_x_assum $ qspecl_then [
        `io`,`env`,`dev2`,`dst`,`ffi'`,
        `st'`,`ffi_st`,`oracle`,`dcs'`,`dev1`,`dst'`] mp_tac >>
      simp[] >> qpat_x_assum `_.ffi = _` $ assume_tac o GSYM >> simp[] >>
      `st' with ffi := st'.ffi = st'` by
        rw[semanticPrimitivesTheory.state_component_equality] >> rw[] >>
      qexists_tac `n'` >> pop_assum mp_tac >>
      Cases_on `n'` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
      ) >>
    PairCases_on `p` >> gvs[dget_ffi_def] >>
    rename1 `dget_ffi _ = SOME ffi_new` >>
    rename1 `Dstep (st2',devb',dcs')` >>
    drule decl_step_ffi_changed >> simp[] >>
    drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >>
    disch_then $ qspecl_then [`dsta`,`deva`] mp_tac >> simp[] >> impl_tac
    >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
    strip_tac >> strip_tac >> gvs[] >>
    unabbrev_all_tac >>
    qpat_x_assum `dstate_rel _ _` mp_tac >> rw[dstate_rel_def] >> gvs[] >>
    gvs[ffi_state_component_equality] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
    simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >>
      simp[dstep_def, SF ditree_ss, is_halt_def]
      ) >>
    Cases_on `x` >> gvs[step_n_def, is_halt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >> simp[deval_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    qmatch_asmsub_abbrev_tac `step_n_cml _ _ (Dstep (st2,dev2,_))` >>
    last_x_assum $ qspecl_then [
      `TL io`,`env`,`dev2`,`dst`,`ffi_new`,`st2`,`ffi_st'`,`oracle`,`dcs`] mp_tac >>
    simp[Abbr `dev2`, deval_rel_cases, PULL_EXISTS] >> disch_then $ drule_at Any >>
    disch_then $
      qspec_then `dsta with refs := LUPDATE (W8array ws'') lnum dsta.refs` mp_tac >>
    qmatch_goalsub_abbrev_tac `Dstep (st3,_)` >>
    `st3 = st2` by (unabbrev_all_tac >> gvs[dstate_rel_def]) >> gvs[] >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[] >> unabbrev_all_tac >> gvs[]
    >- (qexists_tac `n'` >> simp[])
    >- gvs[dstate_rel_def] >>
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `dst` >> gvs[dget_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
  >- (
    simp[decl_step_reln_eq_step_n_cml] >>
    simp[PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >> gen_tac >>
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`ffi'`,
        `dst`,`devb`,`env`,`io`,`v`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[step_n_cml_def] >>
      qexists_tac `SUC 0` >> once_rewrite_tac[trace_prefix_interp] >>
      simp[step_until_halt_def] >>
      `dstep env dsta deva dcs = Draise v` by (
        qmatch_asmsub_abbrev_tac `Dstep (st',_)` >>
        qspecl_then [`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
          assume_tac dstep_result_rel_single' >>
        gvs[dget_ffi_def, dstep_result_rel_cases] >>
        pop_assum irule >> unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >> simp[is_halt_def]) >>
      Cases_on `x` >> gvs[step_n_def, is_halt_def] >> gvs[dget_ffi_def]
      ) >>
    gvs[step_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `(st2,_)` >>
    Cases_on `decl_step env (st2,devb,dcs)` >> gvs[] >>
    Cases_on `dget_ffi (Dstep p) = SOME st2.ffi`
    >- (
      qspecl_then [`dsta`,`deva`,`dcs`,`(st2,devb,dcs)`,`env`]
        mp_tac dstep_result_rel_single' >>
      simp[dget_ffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      last_x_assum $ qspecl_then [
        `v`,`io`,`env`,`dev2`,`dst`,`ffi'`,
        `st'`,`ffi_st`,`oracle`,`dcs'`,`dev1`,`dst'`] mp_tac >>
      simp[] >> qpat_x_assum `_.ffi = _` $ assume_tac o GSYM >> simp[] >>
      `st' with ffi := st'.ffi = st'` by
        rw[semanticPrimitivesTheory.state_component_equality] >> rw[] >>
      qexists_tac `n'` >> pop_assum mp_tac >>
      Cases_on `n'` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
      ) >>
    PairCases_on `p` >> gvs[dget_ffi_def] >>
    rename1 `dget_ffi _ = SOME ffi_new` >>
    rename1 `Dstep (st2',devb',dcs')` >>
    drule decl_step_ffi_changed >> simp[] >>
    drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >>
    disch_then $ qspecl_then [`dsta`,`deva`] mp_tac >> simp[] >> impl_tac
    >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
    strip_tac >> strip_tac >> gvs[] >>
    unabbrev_all_tac >>
    qpat_x_assum `dstate_rel _ _` mp_tac >> rw[dstate_rel_def] >> gvs[] >>
    gvs[ffi_state_component_equality] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
    simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >>
      simp[dstep_def, SF ditree_ss, is_halt_def]
      ) >>
    Cases_on `x` >> gvs[step_n_def, is_halt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >> simp[deval_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    qmatch_asmsub_abbrev_tac `step_n_cml _ _ (Dstep (st2,dev2,_))` >>
    last_x_assum $ qspecl_then [
      `v`,`TL io`,`env`,`dev2`,`dst`,`ffi_new`,`st2`,`ffi_st'`,`oracle`,`dcs`] mp_tac >>
    simp[Abbr `dev2`, deval_rel_cases, PULL_EXISTS] >> disch_then $ drule_at Any >>
    disch_then $
      qspec_then `dsta with refs := LUPDATE (W8array ws'') lnum dsta.refs` mp_tac >>
    qmatch_goalsub_abbrev_tac `Dstep (st3,_)` >>
    `st3 = st2` by (unabbrev_all_tac >> gvs[dstate_rel_def]) >> gvs[] >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[] >> unabbrev_all_tac >> gvs[]
    >- (qexists_tac `n'` >> simp[])
    >- gvs[dstate_rel_def] >>
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `dst` >> gvs[dget_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_dec_FinalFFI:
  dstate_rel dsta st ∧ deval_rel deva devb ⇒

  ((∃n. trace_prefix n (oracle, ffi_st)
    (interp env (Dstep dsta deva dcs)) = (io, SOME $ FinalFFI (s,conf,ws) outcome)) ⇔

  ∃dst ffi' fp.
    (decl_step_reln env)^*
      (st with ffi := st.ffi with <| oracle := oracle; ffi_state := ffi_st |>,
       devb, dcs) dst ∧
    dget_ffi (Dstep dst) = SOME ffi' ∧
    ffi'.io_events = st.ffi.io_events ++ io ∧
    decl_step env dst = Dabort (fp, Rffi_error $ Final_event s conf ws outcome))
Proof
  rw[] >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`devb`,`env`,`io`,`n`] >>
    Induct >> rw[trace_prefix_interp] >>
    gvs[step_until_halt_def] >> every_case_tac >> gvs[]
    >- gvs[trace_prefix_interp]
    >- (
      qspecl_then [`x`,`env`,`Dstep dsta deva dcs`]
        assume_tac is_halt_step_n_min >> gvs[is_halt_def] >>
      qpat_x_assum `step_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[step_n_def, is_halt_def] >>
      gvs[step_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[is_halt_def]) >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >>
      simp[Once decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      rename1 `Dffi dst (s,conf,ws,lnum,env',cs) locs pat dcs''` >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      Cases_on ‘s’>>fs[]>- (
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then drule_all >>
      strip_tac >> gvs[Abbr `st'`] >>
      gvs[dget_ffi_def, ffi_state_component_equality])>>
      metis_tac[dstep_not_SharedMem]
      )
    >- (
      pairarg_tac >> gvs[] >>
      last_x_assum $ drule_at $ Pos last >>
      simp[deval_rel_cases, PULL_EXISTS] >> strip_tac >>
      qspecl_then [`x`,`env`,`Dstep dsta deva dcs`]
        assume_tac is_halt_step_n_min >> gvs[is_halt_def] >>
      qpat_x_assum `step_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[step_n_def, is_halt_def] >>
      gvs[step_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[is_halt_def]) >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> simp[Once RTC_CASES_RTC_TWICE, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      simp[Once decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      rename1 `Dffi dst (s',conf',ws',lnum,env',cs) locs pat dcs''` >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      Cases_on ‘s'’>>fs[]>- (
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then drule_all >>
      strip_tac >> gvs[Abbr `st'`] >>
      gvs[dget_ffi_def, ffi_state_component_equality] >>
      rgs[Once deval_rel_cases, ctxt_rel_def] >> gvs[GSYM ctxt_rel_def] >>
      simp[Once RTC_CASES1] >> irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
      simp[decl_step_reln_def] >>
      first_x_assum $ drule_at Any >> gvs[dstep_to_Dffi] >>
      qmatch_goalsub_abbrev_tac `RTC _ (st1,_)` >>
      disch_then $ qspec_then `st1` mp_tac >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >> strip_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `RTC _ (st2,_)` >>
      `st1 = st2` by (
        unabbrev_all_tac >>
        rw[semanticPrimitivesTheory.state_component_equality,
           ffi_state_component_equality]) >>
      gvs[] >> goal_assum drule >> simp[] >>
      unabbrev_all_tac >> gvs[])>>
      metis_tac[dstep_not_SharedMem]
      )
    >- (
      qspecl_then [`x`,`env`,`Dstep dsta deva dcs`]
        assume_tac is_halt_step_n_min >> gvs[is_halt_def] >>
      qpat_x_assum `step_n _ x _ = _` kall_tac >>
      qpat_x_assum `_ ≤ x` kall_tac >>
      Cases_on `m` >- gvs[step_n_def, is_halt_def] >>
      gvs[step_n_alt_def] >> reverse every_case_tac >> gvs[] >> rename1 `SUC m`
      >- (first_x_assum $ qspec_then `m` assume_tac >> gvs[is_halt_def]) >>
      qmatch_goalsub_abbrev_tac `(st',_)` >>
      qspecl_then [`m`,`dsta`,`deva`,`dcs`,`(st',devb,dcs)`,`env`]
        mp_tac dstep_result_rel_n >>
      simp[is_Dffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >>
      simp[Once decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
      rename1 `Dffi dst (s',conf',ws',lnum,env',cs) locs pat dcs''` >>
      rename1 `_ = Dstep dsta' deva' dcs'` >>
      goal_assum drule >> gvs[dget_ffi_def] >>
      Cases_on ‘s'’>>fs[] >- (
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then drule_all >>
      strip_tac >> gvs[Abbr `st'`] >>
      gvs[dget_ffi_def, ffi_state_component_equality]) >>
      metis_tac[dstep_not_SharedMem]
      )
    )
  >- (
    simp[decl_step_reln_eq_step_n_cml] >>
    simp[PULL_EXISTS, AND_IMP_INTRO, GSYM CONJ_ASSOC] >> gen_tac >>
    map_every qid_spec_tac
      [`dsta`,`deva`,`dcs`,`oracle`,`ffi_st`,`st`,`ffi'`,
        `dst`,`devb`,`env`,`io`,`n`] >>
    Induct >> rw[]
    >- (
      gvs[step_n_cml_def] >>
      qexists_tac `SUC $ SUC 0` >> once_rewrite_tac[trace_prefix_interp] >>
      simp[step_until_halt_def] >>
      Cases_on ‘s’>>fs[] >- (
      drule_at Any dstep_result_rel_single_FFI_error >>
      simp[dstep_result_rel_cases] >> disch_then $ drule_at Any >>
      disch_then $ qspec_then `dsta` mp_tac >>
      impl_tac >- gvs[dstate_rel_def] >> strip_tac >> gvs[] >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `SUC 0` >> simp[step_n_def, is_halt_def]) >>
      drule_at Any is_halt_step_n_eq >>
      disch_then $ qspec_then `SUC 0` $ mp_tac >> simp[step_n_def, is_halt_def] >>
      disch_then kall_tac >> pop_assum kall_tac >>
      drule_at Any dstep_result_rel_single_FFI_strong >>
      simp[dstep_result_rel_cases] >> disch_then $ drule_at Any >>
      qmatch_asmsub_abbrev_tac `Dstep (st1,_)` >>
      disch_then $ qspec_then `st1` mp_tac >>
      impl_tac >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[] >> unabbrev_all_tac >> gvs[dget_ffi_def] >>
      every_case_tac >> rgs[]) >>
      metis_tac[decl_step_not_SharedMem]
      ) >>
    gvs[step_n_cml_def] >>
    qmatch_asmsub_abbrev_tac `decl_step _ (st2,_)` >>
    Cases_on `decl_step env (st2,devb,dcs)` >> gvs[] >>
    Cases_on `dget_ffi (Dstep p) = SOME st2.ffi`
    >- (
      qspecl_then [`dsta`,`deva`,`dcs`,`(st2,devb,dcs)`,`env`]
        mp_tac dstep_result_rel_single' >>
      simp[dget_ffi_def, dstep_result_rel_cases] >> impl_tac
      >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
      strip_tac >> gvs[dget_ffi_def] >>
      unabbrev_all_tac >> gvs[] >>
      last_x_assum $ qspecl_then [
        `io`,`env`,`dev2`,`dst`,`ffi'`,
        `st'`,`ffi_st`,`oracle`,`dcs'`,`dev1`,`dst'`] mp_tac >>
      simp[] >> qpat_x_assum `_.ffi = _` $ assume_tac o GSYM >> simp[] >>
      `st' with ffi := st'.ffi = st'` by
        rw[semanticPrimitivesTheory.state_component_equality] >> rw[] >>
      qexists_tac `n'` >> pop_assum mp_tac >>
      Cases_on `n'` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
      DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
      ) >>
    PairCases_on `p` >> gvs[dget_ffi_def] >>
    rename1 `dget_ffi _ = SOME ffi_new` >>
    rename1 `Dstep (st2',devb',dcs')` >>
    drule decl_step_ffi_changed >> simp[] >>
    drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >>
    disch_then $ qspecl_then [`dsta`,`deva`] mp_tac >> simp[] >> impl_tac
    >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
    strip_tac >> strip_tac >> gvs[] >>
    unabbrev_all_tac >>
    qpat_x_assum `dstate_rel _ _` mp_tac >> rw[dstate_rel_def] >> gvs[] >>
    gvs[ffi_state_component_equality] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
    simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
    >- (
      qexists_tac `SUC 0` >> rewrite_tac[step_n_def] >>
      simp[dstep_def, SF ditree_ss, is_halt_def]
      ) >>
    Cases_on `x` >> gvs[step_n_def, is_halt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >> simp[deval_rel_cases, ctxt_rel_def] >>
    simp[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >> rw[] >> gvs[] >>
    qmatch_asmsub_abbrev_tac `_ ++ [new_event]` >>
    qmatch_asmsub_abbrev_tac `step_n_cml _ _ (Dstep (st2,dev2,_))` >>
    rename1 `ZIP (ws1,ws2)` >>
    last_x_assum $ qspecl_then [
      `TL io`,`env`,`dev2`,`dst`,`ffi_new`,`st2`,`ffi_st'`,`oracle`,`dcs`] mp_tac >>
    simp[Abbr `dev2`, deval_rel_cases, PULL_EXISTS] >> disch_then $ drule_at Any >>
    disch_then $
      qspec_then `dsta with refs := LUPDATE (W8array ws2) lnum dsta.refs` mp_tac >>
    qmatch_goalsub_abbrev_tac `Dstep (st3,_)` >>
    `st3 = st2` by (unabbrev_all_tac >> gvs[dstate_rel_def]) >> gvs[] >>
    simp[] >> reverse $ impl_keep_tac >> gvs[] >> rw[] >> unabbrev_all_tac >> gvs[]
    >- (qexists_tac `n'` >> simp[])
    >- gvs[dstate_rel_def] >>
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
    PairCases_on `dst` >> gvs[dget_ffi_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem decl_step_trace_prefix_io_events_lemma:
  dstate_rel dsta st ∧ deval_rel deva devb ∧
  (decl_step_reln env)^* (st, devb, dcs) dst ∧
  (FST dst).ffi.io_events = st.ffi.io_events ++ io ⇒
  ∃n.
    trace_prefix n (st.ffi.oracle, st.ffi.ffi_state)
      (interp env (Dstep dsta deva dcs)) = (io, NONE)
Proof
  simp[decl_step_reln_eq_step_n_cml, PULL_EXISTS] >> gen_tac >>
  map_every qid_spec_tac
    [`dsta`,`deva`,`dcs`,`st`,`devb`,`env`,`io`,`dst`,`n`] >>
  Induct >> rw[step_n_cml_def] >> gvs[]
  >- (qexists_tac `0` >> simp[trace_prefix_interp]) >>
  Cases_on `decl_step env (st,devb,dcs)` >> gvs[] >>
  Cases_on `dget_ffi (Dstep p) = SOME st.ffi`
  >- (
    qspecl_then [`dsta`,`deva`,`dcs`,`(st,devb,dcs)`,`env`]
      mp_tac dstep_result_rel_single' >>
    simp[dget_ffi_def, dstep_result_rel_cases] >> strip_tac >> gvs[] >>
    last_x_assum drule >> disch_then drule >>
    disch_then $ drule_at Any >> gvs[dget_ffi_def] >> rw[] >> gvs[] >>
    rename1 `trace_prefix m _` >> qexists_tac `m` >> pop_assum mp_tac >>
    Cases_on `m` >> once_rewrite_tac[trace_prefix_interp] >> rw[] >>
    DEP_ONCE_REWRITE_TAC[step_until_halt_take_step] >> simp[is_halt_def]
    ) >>
  PairCases_on `p` >> gvs[dget_ffi_def] >>
  rename1 `Dstep (st',devb',dcs')` >>
  drule decl_step_ffi_changed >> simp[] >>
  drule decl_step_ffi_changed_dstep_to_Dffi >> simp[] >> disch_then $ drule_all >>
  strip_tac >> strip_tac >> gvs[] >>
  rgs[Once deval_rel_cases, ctxt_rel_def] >> gvs[] >>
  gvs[GSYM ctxt_rel_def, ctxt_frame_rel_cases] >>
  Q.REFINE_EXISTS_TAC `SUC m` >> once_rewrite_tac[trace_prefix_interp] >>
  simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (
    pop_assum $ qspec_then `SUC 0` mp_tac >> rewrite_tac[step_n_def] >>
    simp[SF ditree_ss, is_halt_def]
    ) >>
  drule_at Any is_halt_step_n_eq >>
  disch_then $ qspec_then `SUC 0` mp_tac >> simp[step_n_def, is_halt_def] >>
  strip_tac >> rgs[dstep_to_Dffi, Once dstate_rel_def] >>
  qmatch_asmsub_abbrev_tac `step_n_cml _ _ (Dstep (st1,ev,dcs))` >>
  last_x_assum $ qspecl_then [
    `dst`,`TL io`,`env`,`ev`,`st1`,`dcs`] mp_tac >>
  simp[Abbr `ev`, deval_rel_cases, PULL_EXISTS] >>
  disch_then $ drule_at Any >>
  disch_then $ qspec_then
    `dsta with refs := LUPDATE (W8array ws'') lnum st.refs` mp_tac >>
  unabbrev_all_tac >> simp[dstate_rel_def] >> reverse impl_keep_tac >> gvs[] >> rw[]
  >- (qexists_tac `n'` >> simp[])
  >- (
    imp_res_tac io_events_mono_decl_step >>
    imp_res_tac io_events_mono_step_n_cml >> gvs[io_events_mono_def] >>
    Cases_on `io` >> gvs[]
    )
QED

Theorem trace_prefix_decl_step_io_events_lemma:
  ∀env n io oracle ffi_st dsta st deva devb dcs.
  dstate_rel dsta st ∧ deval_rel deva devb ∧
  trace_prefix n (oracle, ffi_st) (interp env (Dstep dsta deva dcs)) = (io, NONE)
  ⇒ ∃st' devb' dcs'.
      RTC (decl_step_reln env)
        (st with ffi := st.ffi with <| oracle := oracle; ffi_state := ffi_st |>,devb,dcs)
        (st',devb',dcs') ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  gen_tac >> Induct >> rw[] >> gvs[trace_prefix_interp]
  >- (irule_at Any RTC_REFL >> rw[]) >>
  pop_assum mp_tac >> TOP_CASE_TAC >> rw[] >- (irule_at Any RTC_REFL >> simp[]) >>
  qpat_x_assum `step_until_halt _ _ = _` mp_tac >>
  simp[step_until_halt_def] >> DEEP_INTRO_TAC some_intro >> rw[] >>
  pop_assum mp_tac >> simp[AllCaseEqs()] >> strip_tac >>
  drule is_halt_step_n_min >> strip_tac >> gvs[] >>
  qpat_x_assum `step_n _ x _ = _` kall_tac >>
  qpat_x_assum `_ ≤ x` kall_tac >>
  `∃l. m = SUC l` by (Cases_on `m` >> gvs[step_n_def]) >> gvs[] >>
  pop_assum $ qspec_then `l'` assume_tac >> gvs[] >>
  gvs[step_n_alt_def] >> FULL_CASE_TAC >> gvs[] >>
  PairCases_on `p` >>
  rename1 `dstep _ _ _ _ = Dffi _ (ffiname,_) _ _ _` >>
  reverse $ Cases_on `ffiname`
  >- metis_tac[dstep_not_SharedMem] >>
  gvs[dstep_to_Dffi] >>
  simp[decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
  qmatch_goalsub_abbrev_tac `st0,_,_` >>
  qspecl_then [`l'`,`dsta`,`deva`,`dcs`,`(st0,devb,dcs)`,`env`]
    mp_tac dstep_result_rel_n >>
  simp[dstep_result_rel_cases, is_Dffi_def, get_ffi_def] >>
  impl_keep_tac >- (unabbrev_all_tac >> gvs[dstate_rel_def]) >>
  rw[] >> gvs[dget_ffi_def] >> every_case_tac >> gvs[]
  >- (goal_assum drule >> unabbrev_all_tac >>
    gvs[ffi_state_component_equality])
  >- (
    gvs[trace_prefix_interp,stringTheory.IMPLODE_EXPLODE_I] >>
    `step_n_cml env (SUC l') (Dstep (st0,devb,dcs)) = decl_step env (st',dev2,l'')` by
      simp[step_n_cml_alt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >>
    simp[deval_rel_cases, ctxt_rel_def] >> simp[GSYM ctxt_rel_def] >>
    simp[ctxt_frame_rel_cases, EXISTS_PROD] >> rw[] >> gvs[] >>
    qpat_x_assum `_ = decl_step _ _` mp_tac >>
    simp[decl_step_def, e_step_def, smallStepTheory.continue_def, cml_application_thm,
         semanticPrimitivesTheory.do_app_def,call_FFI_def,
         combinTheory.o_DEF] >>
    unabbrev_all_tac >> simp[] >>
    gvs[dstate_rel_def] >> gvs[ffi_state_component_equality] >>
    gvs[store_assign_def, store_lookup_def, store_v_same_type_def] >>
    rw[smallStepTheory.return_def] >> goal_assum drule >> simp[]
  )
  >- (goal_assum drule >> unabbrev_all_tac >> gvs[ffi_state_component_equality])
  >- (
    pairarg_tac >> gvs[stringTheory.IMPLODE_EXPLODE_I] >>
    `step_n_cml env (SUC l') (Dstep (st0,devb,dcs)) = decl_step env (st',dev2,l'')` by
      simp[step_n_cml_alt_def] >>
    qpat_x_assum `deval_rel _ _` mp_tac >>
    simp[deval_rel_cases, ctxt_rel_def] >> simp[GSYM ctxt_rel_def] >>
    simp[ctxt_frame_rel_cases, EXISTS_PROD] >> rw[] >> gvs[] >>
    qpat_x_assum `_ = decl_step _ _` mp_tac >>
    simp[decl_step_def, e_step_def, smallStepTheory.continue_def, cml_application_thm,
         semanticPrimitivesTheory.do_app_def, call_FFI_def,
         combinTheory.o_DEF] >>
    unabbrev_all_tac >> simp[] >>
    gvs[dstate_rel_def] >> gvs[ffi_state_component_equality] >>
    gvs[store_assign_def, store_lookup_def, store_v_same_type_def] >>
    rw[smallStepTheory.return_def] >>
    qmatch_asmsub_abbrev_tac `Dstep (st1,ExpVal _ _ _ _ _,_)` >>
    last_x_assum $ drule_at $ Pos last >> simp[deval_rel_cases, PULL_EXISTS] >>
    disch_then $ drule_at Any >> disch_then $ qspec_then `st1` mp_tac >>
    impl_tac >- (unabbrev_all_tac >> gvs[]) >>
    rw[decl_step_reln_eq_step_n_cml] >> rename1 `_ = Dstep (st3,_,_)` >>
    qexistsl_tac [`st3`,`devb''`,`dcs'`,`n' + SUC l'`] >>
    simp[step_n_cml_add] >>
    qmatch_asmsub_abbrev_tac `_ (Dstep (st1',_,_)) = _` >>
    `st1' = st1` by (unabbrev_all_tac >>
      simp[semanticPrimitivesTheory.state_component_equality,
           ffi_state_component_equality]) >>
    gvs[] >> unabbrev_all_tac >> gvs[]
  )
QED


(******************** Collected results for declarations ********************)

Definition dstate_of_def:
  dstate_of (st :α semanticPrimitives$state) :dstate = <|
    refs := st.refs;
    next_type_stamp := st.next_type_stamp;
    next_exn_stamp := st.next_exn_stamp;
    eval_state := st.eval_state;
    fp_state := st.fp_state|>
End

Theorem dstate_rel_dstate_of:
  dstate_rel dst st ⇔ dstate_of st = dst
Proof
  rw[dstate_of_def, dstate_rel_def] >>
  eq_tac >> rw[] >> gvs[state_component_equality, dstate_component_equality]
QED

Definition itree_of_def:
  itree_of st env prog =
  interp env (Dstep (dstate_of st) (Decl (Dlocal [] prog)) [])
End

Overload itree_ffi = `` λst. (st.ffi.oracle,st.ffi.ffi_state)``;

Triviality evaluate_decs_NIL[simp]:
  evaluate_decs ck env st [] res ⇔ res = (st, Rval empty_dec_env)
Proof
  simp[Once bigStepTheory.evaluate_dec_cases, empty_dec_env_def]
QED

Theorem small_eval_decs_eq_Dlocal:
  small_eval_dec env (st,Decl (Dlocal [] prog),[]) = small_eval_decs env st prog
Proof
  rw[FUN_EQ_THM] >> rename1 `_ prog res` >>
  rw[GSYM bigSmallEquivTheory.small_big_dec_equiv,
     GSYM bigSmallEquivTheory.small_big_decs_equiv] >>
  map_every qid_spec_tac [`env`,`st`,`res`,`prog`] >>
  Induct >> rw[] >> simp[Once bigStepTheory.evaluate_dec_cases]
QED

Theorem small_eval_decs_trace_prefix_termination:
  (small_eval_decs env st ds (st',Rval e) ∨
   small_eval_decs env st ds (st',Rerr (Rraise v)))
  ⇒ ∃n io.
      trace_prefix n (itree_ffi st) (itree_of st env ds) = (io, SOME Termination) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[GSYM small_eval_decs_eq_Dlocal, itree_of_def] >>
  gvs[small_eval_dec_def, decl_step_reln_eq_step_n_cml] >>
  imp_res_tac io_events_mono_step_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `_ ⇒ _` kall_tac >> rename1 `_ ++ io` >>
  `dstate_rel (dstate_of st) st` by gvs[dstate_rel_dstate_of] >>
  drule $ iffRL trace_prefix_dec_Termination >>
  disch_then $ qspecl_then [`st.ffi.oracle`,`io`,`st.ffi.ffi_state`,
    `env`,`Decl (Dlocal [] ds)`,`Decl (Dlocal [] ds)`,`[]`] mp_tac >>
  simp[deval_rel_cases, decl_step_reln_eq_step_n_cml, PULL_EXISTS] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (unabbrev_all_tac >>
    rw[semanticPrimitivesTheory.state_component_equality,
       ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  disch_then drule >> simp[dget_ffi_def, SF dsmallstep_ss]
QED

Theorem trace_prefix_small_eval_decs_termination:
  trace_prefix n (itree_ffi st) (itree_of st env ds) = (io, SOME Termination)
  ⇒ ∃st' e v.
      (small_eval_decs env st ds (st', Rval e) ∨
       small_eval_decs env st ds (st', Rerr (Rraise v))) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[GSYM small_eval_decs_eq_Dlocal, itree_of_def, small_eval_dec_def] >>
  `dstate_rel (dstate_of st) st` by gvs[dstate_rel_dstate_of] >>
  drule $ iffLR trace_prefix_dec_Termination >> simp[PULL_EXISTS] >>
  disch_then $ drule_at Any >> simp[deval_rel_cases, PULL_EXISTS] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (unabbrev_all_tac >>
    rw[semanticPrimitivesTheory.state_component_equality,
       ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >> rw[] >> gvs[] >>
  PairCases_on `dst` >> gvs[decl_step_to_Ddone]
  >- (irule_at Any OR_INTRO_THM1 >> goal_assum drule >> gvs[dget_ffi_def])
  >- (
    irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS, GSYM CONJ_ASSOC, EXISTS_PROD] >>
    gvs[dget_ffi_def] >> Cases_on ‘v’ >> rename1 ‘Draise (fpN, res)’ >>
    qexists_tac ‘res’ >> qexists_tac ‘dst0 with fp_state := fpN’ >>
    qexists_tac ‘dst1’ >> qexists_tac ‘dst2’ >> qexists_tac ‘dst0.fp_state’ >>
    gs[]
    )
QED

Theorem small_eval_decs_trace_prefix_type_error:
  small_eval_decs env st ds (st', Rerr (Rabort Rtype_error))
  ⇒ ∃n io.
      trace_prefix n (itree_ffi st) (itree_of st env ds) = (io, SOME Error) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[GSYM small_eval_decs_eq_Dlocal, itree_of_def] >>
  gvs[small_eval_dec_def, decl_step_reln_eq_step_n_cml] >>
  imp_res_tac io_events_mono_step_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `_ ⇒ _` kall_tac >> rename1 `_ ++ io` >>
  `dstate_rel (dstate_of st) st` by gvs[dstate_rel_dstate_of] >>
  drule $ iffRL trace_prefix_dec_Error >>
  disch_then $ qspecl_then [`st.ffi.oracle`,`io`,`st.ffi.ffi_state`,
    `env`,`Decl (Dlocal [] ds)`,`Decl (Dlocal [] ds)`,`[]`] mp_tac >>
  simp[deval_rel_cases, PULL_EXISTS, decl_step_reln_eq_step_n_cml] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (unabbrev_all_tac >>
    rw[semanticPrimitivesTheory.state_component_equality,
       ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  disch_then drule >> simp[dget_ffi_def]
QED

Theorem trace_prefix_small_eval_decs_type_error:
  trace_prefix n (itree_ffi st) (itree_of st env ds) = (io, SOME Error)
  ⇒ ∃st'. small_eval_decs env st ds (st', Rerr (Rabort Rtype_error))
Proof
  rw[GSYM small_eval_decs_eq_Dlocal, itree_of_def] >>
  `dstate_rel (dstate_of st) st` by gvs[dstate_rel_dstate_of] >>
  drule $ iffLR trace_prefix_dec_Error >> simp[PULL_EXISTS] >>
  disch_then $ drule_at Any >> simp[deval_rel_cases] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (unabbrev_all_tac >>
    rw[semanticPrimitivesTheory.state_component_equality,
       ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  simp[small_eval_dec_def, PULL_EXISTS, EXISTS_PROD] >> rw[] >> gvs[] >>
  PairCases_on `dst` >> simp[] >> rename1 ‘Dabort (fpN, _)’ >>
  qexists_tac ‘dst0 with fp_state := fpN’ >>
  qexists_tac ‘dst1’ >> qexists_tac ‘dst2’ >> qexists_tac ‘dst0.fp_state’ >>
  gs[]
QED

Theorem small_eval_decs_trace_prefix_ffi_error:
  small_eval_decs env st ds
    (st', Rerr (Rabort $ Rffi_error $ Final_event s conf ws outcome))
  ⇒ ∃n io.
      trace_prefix n (itree_ffi st) (itree_of st env ds) =
        (io, SOME $ FinalFFI (s,conf,ws) outcome) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[GSYM small_eval_decs_eq_Dlocal, itree_of_def] >>
  gvs[small_eval_dec_def, decl_step_reln_eq_step_n_cml] >>
  imp_res_tac io_events_mono_step_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `_ ⇒ _` kall_tac >> rename1 `_ ++ io` >>
  `dstate_rel (dstate_of st) st` by gvs[dstate_rel_dstate_of] >>
  drule $ iffRL trace_prefix_dec_FinalFFI >>
  disch_then $ qspecl_then [`ws`,`s`,`outcome`,`st.ffi.oracle`,`io`,`st.ffi.ffi_state`,
    `env`,`Decl (Dlocal [] ds)`,`Decl (Dlocal [] ds)`,`[]`,`conf`] mp_tac >>
  simp[deval_rel_cases, PULL_EXISTS, decl_step_reln_eq_step_n_cml] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (unabbrev_all_tac >>
    rw[semanticPrimitivesTheory.state_component_equality,
       ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  disch_then drule >> simp[dget_ffi_def]
QED

Theorem trace_prefix_small_eval_decs_ffi_error:
  trace_prefix n (itree_ffi st) (itree_of st env ds) =
    (io, SOME $ FinalFFI (s,conf,ws) outcome)
  ⇒ ∃st'. small_eval_decs env st ds
            (st', Rerr (Rabort $ Rffi_error $ Final_event s conf ws outcome)) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  rw[GSYM small_eval_decs_eq_Dlocal, itree_of_def] >>
  `dstate_rel (dstate_of st) st` by gvs[dstate_rel_dstate_of] >>
  drule $ iffLR trace_prefix_dec_FinalFFI >> simp[PULL_EXISTS] >>
  disch_then $ drule_at Any >> simp[deval_rel_cases] >>
  qmatch_goalsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (unabbrev_all_tac >>
    rw[semanticPrimitivesTheory.state_component_equality,
       ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >>
  simp[small_eval_dec_def, PULL_EXISTS, EXISTS_PROD] >> rw[] >> gvs[] >>
  PairCases_on `dst` >> gvs[dget_ffi_def] >> rename1 ‘Dabort (fpN, _)’ >>
  qexists_tac ‘dst0 with fp_state := fpN’ >>
  qexists_tac ‘dst1’ >> qexists_tac ‘dst2’ >> qexists_tac ‘dst0.fp_state’ >>
  gs[]
QED

Theorem decl_step_trace_prefix_io_events:
  (decl_step_reln env)^* (st,Decl (Dlocal [] ds),[]) (st',dev,dcs)
  ⇒ ∃n io.
      trace_prefix n (itree_ffi st) (itree_of st env ds) = (io, NONE) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  `dstate_rel (dstate_of st) st` by gvs[dstate_rel_dstate_of] >> rw[] >>
  drule decl_step_trace_prefix_io_events_lemma >>
  disch_then $ drule_at Any >> simp[deval_rel_cases] >> strip_tac >>
  gvs[decl_step_reln_eq_step_n_cml] >>
  imp_res_tac io_events_mono_step_n_cml >>
  gvs[io_events_mono_def, rich_listTheory.IS_PREFIX_APPEND, itree_of_def] >>
  goal_assum drule
QED

Theorem trace_prefix_decl_step_io_events:
  trace_prefix n (itree_ffi st) (itree_of st env ds) = (io, NONE)
  ⇒ ∃st' dev dcs.
      (decl_step_reln env)^* (st,Decl (Dlocal [] ds),[]) (st',dev,dcs) ∧
      st'.ffi.io_events = st.ffi.io_events ++ io
Proof
  `dstate_rel (dstate_of st) st` by gvs[dstate_rel_dstate_of] >> rw[] >>
  drule trace_prefix_decl_step_io_events_lemma >> gvs[itree_of_def] >>
  disch_then $ drule_at Any >> simp[deval_rel_cases] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `(st1,_)` >>
  `st1 = st` by (unabbrev_all_tac >>
    rw[semanticPrimitivesTheory.state_component_equality,
       ffi_state_component_equality]) >>
  unabbrev_all_tac >> gvs[] >> goal_assum drule >> simp[]
QED


(******************** Initial state/environment ********************)

Theorem start_dstate:
  ∀ffi:'ffi ffi_state. dstate_of (FST $ THE $ prim_sem_env ffi) = start_dstate
Proof
  rw[prim_sem_env_eq, dstate_of_def, start_dstate_def]
QED

Theorem start_env:
  ∀ffi:'ffi ffi_state. SND $ THE $ prim_sem_env ffi = start_env
Proof
  rw[prim_sem_env_eq, start_env_def]
QED

Theorem prim_sem_env_change_ffi[simp]:
  (FST $ THE $ prim_sem_env f) with ffi := f' = (FST $ THE $ prim_sem_env f')
Proof
  rw[prim_sem_env_eq, semanticPrimitivesTheory.state_component_equality]
QED

Theorem itree_semantics_itree_of:
  ∀(ffi:'ffi ffi_state) prog.
    itree_of (FST $ THE $ prim_sem_env ffi) start_env prog =
    itree_semantics prog
Proof
  rw[itree_semantics_def, itree_of_def, start_dstate]
QED


(****************************************)

val _ = export_theory();

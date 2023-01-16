(*
  Big step/small step equivalence
*)
open preamble;
open astTheory libTheory semanticPrimitivesTheory bigStepTheory smallStepTheory;
open bigSmallInvariantsTheory semanticPrimitivesPropsTheory determTheory bigClockTheory;
open smallStepPropsTheory bigStepPropsTheory evaluatePropsTheory interpTheory funBigStepEquivTheory;

val _ = new_theory "bigSmallEquiv";

Triviality result_cases:
  !r.
    (?s v. r = (s, Rval v)) ∨
    (?s v. r = (s, Rerr (Rraise v))) ∨
    (?s a. r = (s, Rerr (Rabort a)))
Proof
  cases_on `r` >>
  srw_tac[][] >>
  cases_on `r'` >>
  full_simp_tac(srw_ss())[] >>
  cases_on `e` >>
  full_simp_tac(srw_ss())[]
QED

Definition to_small_st_def:
  to_small_st s = (s.refs,s.ffi)
End

Theorem to_small_st_with_clock[simp]:
  to_small_st (s with clock := ck) = to_small_st s
Proof
  rw[to_small_st_def]
QED

Definition to_small_res_def:
  to_small_res r = (to_small_st (FST r), (FST r).fp_state, SND r)
End

Triviality do_opapp_too_many:
  !vs'. do_opapp (REVERSE (v''::vs') ++ [v'] ++ [v]) = NONE
Proof
  rw[do_opapp_def] >> ntac 3 (TOP_CASE_TAC >> gvs[])
QED

val s = ``s:'ffi state``;
val _ = temp_delsimps["getOpClass_def"]

Definition compress_v_def:
  compress_v op v =
  if isFpBool op then
    case v of
    | FP_BoolTree fv => Boolv (compress_bool fv)
    | _ => v
  else v
End

Theorem compress_if_bool_compress_v:
  compress_if_bool op (Rval r) = Rval (compress_v op r) ∧
  compress_if_bool op (Rerr err) = Rerr err
Proof
  gs[compress_if_bool_def, compress_v_def] >> rpt TOP_CASE_TAC
QED

Theorem big_exp_to_small_exp:
  (∀ck env ^s e r.
     evaluate ck env s e r ⇒
     (ck = F) ⇒ small_eval env (to_small_st s) s.fp_state e [] (to_small_res r)) ∧
  (∀ck env ^s es r.
     evaluate_list ck env s es r ⇒
     (ck = F) ⇒ small_eval_list env (to_small_st s) s.fp_state es (to_small_res r)) ∧
  (∀ck env ^s v pes err_v r.
     evaluate_match ck env s v pes err_v r ⇒
     (ck = F) ⇒ small_eval_match env (to_small_st s) s.fp_state v pes err_v (to_small_res r))
Proof
   ho_match_mp_tac evaluate_ind >>
   srw_tac[][small_eval_log, small_eval_if, small_eval_match, small_eval_lannot,
             small_eval_handle, small_eval_let, small_eval_letrec, small_eval_tannot, to_small_res_def, small_eval_raise]
   >- (srw_tac[][return_def, small_eval_def, Once RTC_CASES1, e_step_reln_def, e_step_def] >>
       metis_tac [RTC_REFL])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       simp[Once RTC_CASES2] >>
       drule e_step_add_ctxt >> simp[] >> disch_then $ irule_at Any >>
       simp[e_step_reln_def, e_step_def, continue_def])
   >- (`small_eval env (to_small_st s) s.fp_state e ([] ++ [(Craise (),env)]) (to_small_st s2, s2.fp_state, Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Chandle () pes,env)]) (env',to_small_st s2,s2.fp_state,Val v,[(Chandle () pes,env)])`
                   by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s2,s2.fp_state,Val v,[(Chandle () pes,env)]) (env,to_small_st s2,s2.fp_state,Val v,[])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
       metis_tac [transitive_def, transitive_RTC, RTC_SINGLE])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state, Exp e,[(Chandle () pes,env)])
                      (env',to_small_st s',s'.fp_state,Exn v,[(Chandle () pes,env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s',s'.fp_state,Exn v,[(Chandle () pes,env)])
                    (env',to_small_st s',s'.fp_state,Val v,[(Cmat_check () pes v, env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
       `e_step_reln (env',to_small_st s',s'.fp_state,Val v,[(Cmat_check () pes v, env)])
                    (env,to_small_st s',s'.fp_state,Val v,[(Cmat () pes v, env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]
                       \\ fs [to_small_st_def]) >>
       imp_res_tac small_eval_match_thm >>
       Q.ISPEC_THEN`r`assume_tac result_cases >>
       srw_tac[][] >>
       full_simp_tac(srw_ss())[small_eval_def, alt_small_eval_def] >- (
       irule_at Any (SIMP_RULE std_ss [transitive_def] transitive_RTC) >>
       first_x_assum $ irule_at Any >>
       simp[Once RTC_CASES1] >>
       first_x_assum $ irule_at Any >>
       simp[Once RTC_CASES1] >>
       first_x_assum $ irule_at Any >>
       first_x_assum $ qspec_then ‘env’ strip_assume_tac >>
       first_x_assum $ irule_at Any) >>
       metis_tac [transitive_def, transitive_RTC, RTC_SINGLE])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Chandle () pes,env)])
                      (env',to_small_st s2,fp'',e',c'++[(Chandle () pes,env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       first_x_assum $ irule_at Any >> irule e_single_error_add_ctxt >> gs[])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Chandle () pes,env)])
                      (env',to_small_st s2,s2.fp_state,Exn v,[(Chandle () pes,env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s2,s2.fp_state,Exn v,[(Chandle () pes,env)])
                    (env',to_small_st s2,s2.fp_state,Val v,[(Cmat_check () pes v, env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
        `e_step (env',to_small_st s2,s2.fp_state,Val v,[(Cmat_check () pes v, env)]) =
         Eabort (s2.fp_state,Rtype_error)` by
          (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]
           \\ fs [to_small_st_def, fix_fp_state_def]) >>
        goal_assum (first_assum o mp_then Any mp_tac) >>
        metis_tac [transitive_def, transitive_RTC, RTC_SINGLE])
   >- (`es = [] ∨ ?e es'. es = es' ++ [e]` by
        metis_tac [SRULE [SNOC_APPEND] SNOC_CASES] >>
       full_simp_tac(srw_ss())[LENGTH] >>
       srw_tac[][small_eval_con] >|
       [srw_tac[][small_eval_def] >>
            full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
            srw_tac[][return_def, small_eval_def, Once RTC_CASES1, e_step_reln_def, e_step_def] >>
            metis_tac [RTC_REFL],
        full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
            srw_tac[][small_eval_def] >>
            qexists_tac `env` >>
            match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] small_eval_list_step) >>
            MAP_EVERY qexists_tac [`s2`, ‘fp2’, `v'`, `vs'`, `env'`] >>
            srw_tac[][] >>
            full_simp_tac(srw_ss())[] >>
            imp_res_tac small_eval_list_length >>
            full_simp_tac(srw_ss())[] >>
            metis_tac [arithmeticTheory.ADD_COMM]])
   >- (srw_tac[][small_eval_def, e_step_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Con cn es)` >>
       srw_tac[][] >>
       qexists_tac ‘[]’ >> gs[fix_fp_state_def] >>
       metis_tac [RTC_REFL])
   >- (`es = [] ∨ ?e es'. es = es' ++ [e]` by
          metis_tac [SRULE [SNOC_APPEND] SNOC_CASES] >>
       srw_tac[][small_eval_con] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
       srw_tac[][small_eval_def]
       >- (
        `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Ccon cn [] () (REVERSE es'),env)])
                       (env',to_small_st s',s'.fp_state,Exn err_v,[(Ccon cn [] () (REVERSE es'),env)])`
                   by metis_tac [APPEND,e_step_add_ctxt] >>
            `e_step_reln^* (env',to_small_st s',s'.fp_state,Exn err_v,[(Ccon cn [] () (REVERSE es'),env)])
                         (env',to_small_st s',s'.fp_state,Exn err_v,[])`
                   by (irule e_step_raise_lemma >> simp[]) >>
            metis_tac [transitive_def, transitive_RTC, RTC_SINGLE]
          )
        >- (
        `LENGTH ([]:v list) + 1 + LENGTH es' = SUC (LENGTH es')` by
                   (full_simp_tac(srw_ss())[] >>
                    DECIDE_TAC) >>
            metis_tac [small_eval_list_err, LENGTH_REVERSE, arithmeticTheory.ADD1]
            )
        >- (
          first_x_assum $ mp_then Any mp_tac e_step_add_ctxt >>
          disch_then $ qspec_then ‘[(Ccon cn [] () (REVERSE es'), env)]’ mp_tac >> simp[] >>
          disch_then $ irule_at Any >>
          irule_at Any e_single_error_add_ctxt >> gs[]
          )
        >- (
        `LENGTH ([]:v list) + 1 + LENGTH es' = SUC (LENGTH es')` by
                   (full_simp_tac(srw_ss())[] >>
                    DECIDE_TAC) >>
            metis_tac [small_eval_list_terr, arithmeticTheory.ADD1, LENGTH_REVERSE]
          )
        )
   >- (srw_tac[][small_eval_def] >>
       qexists_tac `env` >>
       srw_tac[][Once RTC_CASES1, e_step_reln_def, return_def, e_step_def])
   >- (srw_tac[][small_eval_def, e_step_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Var n)` >>
       srw_tac[][] >>  qexists_tac ‘[]’ >> gs[fix_fp_state_def])
   >- (srw_tac[][small_eval_def] >>
       qexists_tac `env` >>
       srw_tac[][Once RTC_CASES1, e_step_reln_def, return_def, e_step_def])
   >- (
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >- full_simp_tac(srw_ss())[do_opapp_def] >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >- full_simp_tac(srw_ss())[do_opapp_def] >>
     reverse(full_simp_tac(srw_ss())[Once small_eval_list_cases, SWAP_REVERSE_SYM]) >> srw_tac[][]
     >- metis_tac [do_opapp_too_many, NOT_SOME_NONE] >>
     srw_tac[][Once small_eval_app] >>
     match_mp_tac small_eval_prefix >>
     Q.PAT_ABBREV_TAC`ctx = (Capp B X Y Z,env)` >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[ctx]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     qabbrev_tac`ctx2 = (Capp Opapp [v] () [],env)` >>
     `e_step_reln^* (env'',s2',fp2,Val v,[ctx]) (env,s2',fp2,Exp e'',[ctx2])` by (
       simp[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] >>
       Cases_on ‘op’ >> gs[opClass_cases]) >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[ctx2]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     qmatch_assum_abbrev_tac`e_step_reln^* b c` >>
     qmatch_assum_abbrev_tac`e_step_reln^* a b` >>
     `e_step_reln^* a c` by metis_tac[transitive_RTC, transitive_def] >>
     qpat_x_assum`X b c`kall_tac >>
     qpat_x_assum`X a b`kall_tac >>
     qunabbrev_tac`b` >>
     ONCE_REWRITE_TAC[CONJ_COMM] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     qmatch_assum_abbrev_tac`e_step_reln^* d a` >>
     qmatch_abbrev_tac`e_step_reln^* d f` >>
     qsuff_tac`e_step_reln^* c f` >- metis_tac[transitive_RTC,transitive_def] >>
     unabbrev_all_tac >>
     simp[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,application_thm, getOpClass_def] )
   >- (
     full_simp_tac(srw_ss())[] >>
     srw_tac[][small_eval_def] >>
     ‘getOpClass op = FunApp’ by (Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]) >>
     srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,
        application_thm,do_opapp_def] >>
     srw_tac[boolSimps.DNF_ss][] >>
     srw_tac[][Once e_step_def,application_thm,do_opapp_def] >>
     BasicProvers.CASE_TAC >- full_simp_tac(srw_ss())[Once small_eval_list_cases, fix_fp_state_def] >>
     qpat_x_assum ‘getOpClass _ = _’ kall_tac >>
     disj2_tac >>
     srw_tac[][push_def] >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
     first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[(Capp Opapp [] () t,env)]`strip_assume_tac) >>
     full_simp_tac(srw_ss())[] >> srw_tac[][] >>
     Cases_on`LENGTH t = 1` >- (
       Cases_on`t`>>full_simp_tac(srw_ss())[LENGTH_NIL]>>srw_tac[][]>>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       qmatch_assum_abbrev_tac`e_step_reln^* a b` >>
       qpat_x_assum`e_step_reln^* a b`mp_tac >>
       first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`[Capp Opapp [v] () [],env]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
       qmatch_assum_abbrev_tac`e_step_reln^* c d` >>
       `e_step_reln^* b c` by (
         srw_tac[][Once RTC_CASES1,Abbr`b`,e_step_reln_def,e_step_def] >>
         srw_tac[][continue_def,push_def] ) >>
       strip_tac >>
       `e_step_reln^* a d` by metis_tac[transitive_RTC,transitive_def] >>
       qunabbrev_tac`d` >> Cases_on ‘op’ >> gs[opClass_cases] >>
       first_assum(match_exists_tac o concl) >>
       simp[e_step_def,continue_def,application_thm, getOpClass_def, fix_fp_state_def] ) >>
     imp_res_tac small_eval_opapp_err >> full_simp_tac(srw_ss())[] >>
     first_x_assum(qspec_then`[]`mp_tac) >> simp[] >>
     disch_then(qspecl_then[`v`,`env'`]strip_assume_tac) >>
     Cases_on ‘op’ >> gs[opClass_cases] >>
     metis_tac[transitive_RTC,transitive_def])
  >- (
    ‘getOpClass op = Simple’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
    gvs[] >> Cases_on `es` using SNOC_CASES >> gvs[]
    >- (
      gvs[Once small_eval_list_cases, to_small_st_def,
          do_app_def, AllCaseEqs(), store_alloc_def] >>
      simp[small_eval_def] >> irule_at Any RTC_SUBSET >>
      simp[e_step_reln_def, e_step_def, application_thm, do_app_def,
           store_alloc_def, return_def]
      ) >>
    gvs[REVERSE_SNOC] >> Cases_on `l` >> gvs[]
    >- (
      ntac 2 $ gvs[Once small_eval_list_cases] >>
      dxrule e_step_add_ctxt >>
      disch_then $ qspec_then `[Capp op [] () [],env]` assume_tac >> gvs[] >>
      `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op [x],[])
        (env',to_small_st s2,s2.fp_state,Val v,[(Capp op [] () [],env)])` by
          simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def] >>
      Cases_on `res` >> gvs[small_eval_def]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def]
        ) >>
      Cases_on `e` >> gvs[small_eval_def]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def]
        )
      >- (
        imp_res_tac do_app_type_error >> gvs[] >>
        `s2 with <|refs := s2.refs; ffi := s2.ffi|> = s2` by
          gvs[state_component_equality] >> simp[] >>
        goal_assum drule >>
        simp[e_step_def, continue_def, application_thm, to_small_st_def, fix_fp_state_def]
        )
      ) >>
    last_x_assum mp_tac >> once_rewrite_tac[GSYM APPEND] >>
    rewrite_tac[small_eval_list_Rval_APPEND] >> rw[] >> gvs[REVERSE_APPEND] >>
    pop_assum mp_tac >> ntac 2 $ simp[Once small_eval_list_cases] >> rw[] >> gvs[] >>
    dxrule e_step_to_App_mid >>
    disch_then $ qspecl_then [`h`,`[]`,`op`,`[]`] mp_tac >> rw[] >>
    `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op (h::SNOC x t), [])
      (env',to_small_st s2,s2.fp_state,Val v,[(Capp op (REVERSE lvs) () [],env)])` by (
      simp[Once RTC_CASES1, e_step_reln_def, e_step_def, REVERSE_SNOC, push_def] >>
      simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
      rev_drule e_step_add_ctxt >> simp[]) >>
    Cases_on `res` >> gvs[small_eval_def]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def]
      ) >>
    Cases_on `e` >> gvs[small_eval_def]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def]
      )
    >- (
      imp_res_tac do_app_type_error >> gvs[] >>
      `s2 with <|refs := s2.refs; ffi := s2.ffi|> = s2` by
        gvs[state_component_equality] >> simp[] >>
      goal_assum drule >>
      simp[e_step_def, continue_def, application_thm, to_small_st_def, fix_fp_state_def]
      )
    )
  >- (
    ‘getOpClass op = Icing’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
    gvs[] >> Cases_on `es` using SNOC_CASES >> gvs[]
    >- (gvs[Once small_eval_list_cases, to_small_st_def,
          do_app_def, AllCaseEqs(), store_alloc_def, getOpClass_def]) >>
    gvs[REVERSE_SNOC] >> Cases_on `l` >> gvs[]
    >- (
      ntac 2 $ gvs[Once small_eval_list_cases] >>
      dxrule e_step_add_ctxt >>
      disch_then $ qspec_then `[Capp op [] () [],env]` assume_tac >> gvs[] >>
      `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op [x],[])
        (env',to_small_st s2,s2.fp_state,Val v,[(Capp op [] () [],env)])` by
          simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def] >>
      Cases_on `vFp` >> gvs[small_eval_def, compress_if_bool_compress_v]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def] >>
        every_case_tac >> simp[compress_v_def]) >>
      Cases_on `e` >> gvs[small_eval_def]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def]
        )
      >- (
        imp_res_tac do_app_type_error >> gvs[] >>
        `s2 with <|refs := s2.refs; ffi := s2.ffi|> = s2` by
          gvs[state_component_equality] >> simp[] >>
        goal_assum drule >>
        simp[e_step_def, continue_def, application_thm, to_small_st_def, fix_fp_state_def]
        )
      ) >>
    last_x_assum mp_tac >> once_rewrite_tac[GSYM APPEND] >>
    rewrite_tac[small_eval_list_Rval_APPEND] >> rw[] >> gvs[REVERSE_APPEND] >>
    pop_assum mp_tac >> ntac 2 $ simp[Once small_eval_list_cases] >> rw[] >> gvs[] >>
    dxrule e_step_to_App_mid >>
    disch_then $ qspecl_then [`h`,`[]`,`op`,`[]`] mp_tac >> rw[] >>
    `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op (h::SNOC x t), [])
      (env',to_small_st s2,s2.fp_state,Val v,[(Capp op (REVERSE lvs) () [],env)])` by (
      simp[Once RTC_CASES1, e_step_reln_def, e_step_def, REVERSE_SNOC, push_def] >>
      simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
      rev_drule e_step_add_ctxt >> simp[]) >>
    Cases_on `vFp` >> gvs[small_eval_def, compress_if_bool_compress_v]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def] >>
      every_case_tac >> simp[compress_v_def]) >>
    Cases_on `e` >> gvs[small_eval_def]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def]
      )
    >- (
      imp_res_tac do_app_type_error >> gvs[] >>
      `s2 with <|refs := s2.refs; ffi := s2.ffi|> = s2` by
        gvs[state_component_equality] >> simp[] >>
      goal_assum drule >>
      simp[e_step_def, continue_def, application_thm, to_small_st_def, fix_fp_state_def]
      )
    )
  >- (
    ‘getOpClass op = Icing’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
    gvs[] >> Cases_on `es` using SNOC_CASES >> gvs[]
    >- (gvs[Once small_eval_list_cases, to_small_st_def,
          do_app_def, AllCaseEqs(), store_alloc_def, getOpClass_def]) >>
    gvs[REVERSE_SNOC] >> Cases_on `l` >> gvs[]
    >- (
      ntac 2 $ gvs[Once small_eval_list_cases] >>
      dxrule e_step_add_ctxt >>
      disch_then $ qspec_then `[Capp op [] () [],env]` assume_tac >> gvs[] >>
      `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op [x],[])
        (env',to_small_st s2,s2.fp_state,Val v,[(Capp op [] () [],env)])` by
          simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def] >>
      Cases_on `vFp` >> gvs[small_eval_def, compress_if_bool_compress_v]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def] >>
        every_case_tac >> simp[compress_v_def, shift_fp_opts_def, shift_fp_state_def, fix_fp_state_def]) >>
      Cases_on `e` >> gvs[small_eval_def]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def, shift_fp_opts_def, shift_fp_state_def]
        )
      >- (
        imp_res_tac do_app_type_error >> gvs[] >>
        `shift_fp_opts s2 with <|refs := s2.refs; ffi := s2.ffi|> = shift_fp_opts s2` by
          gvs[state_component_equality, shift_fp_opts_def] >> simp[] >>
        ‘to_small_st (shift_fp_opts s2) = to_small_st s2’ by
          gvs[state_component_equality, to_small_st_def, shift_fp_opts_def] >>
        simp[] >>
        goal_assum drule >>
        simp[e_step_def, continue_def, application_thm, to_small_st_def,
             shift_fp_state_def, shift_fp_opts_def, fix_fp_state_def]
        )
      ) >>
    last_x_assum mp_tac >> once_rewrite_tac[GSYM APPEND] >>
    rewrite_tac[small_eval_list_Rval_APPEND] >> rw[] >> gvs[REVERSE_APPEND] >>
    pop_assum mp_tac >> ntac 2 $ simp[Once small_eval_list_cases] >> rw[] >> gvs[] >>
    dxrule e_step_to_App_mid >>
    disch_then $ qspecl_then [`h`,`[]`,`op`,`[]`] mp_tac >> rw[] >>
    `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op (h::SNOC x t), [])
      (env',to_small_st s2,s2.fp_state,Val v,[(Capp op (REVERSE lvs) () [],env)])` by (
      simp[Once RTC_CASES1, e_step_reln_def, e_step_def, REVERSE_SNOC, push_def] >>
      simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
      rev_drule e_step_add_ctxt >> simp[]) >>
    Cases_on `vFp` >> gvs[small_eval_def, compress_if_bool_compress_v]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def] >>
      every_case_tac >> simp[compress_v_def, shift_fp_state_def, shift_fp_opts_def]) >>
    Cases_on `e` >> gvs[small_eval_def]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def, shift_fp_state_def, shift_fp_opts_def]
      )
    >- (
      imp_res_tac do_app_type_error >> gvs[] >>
      `shift_fp_opts s2 with <|refs := s2.refs; ffi := s2.ffi|> = shift_fp_opts s2` by
        gvs[state_component_equality, shift_fp_opts_def] >> simp[] >>
      ‘to_small_st (shift_fp_opts s2) = to_small_st s2’ by
        gvs[state_component_equality, to_small_st_def, shift_fp_opts_def] >>
      simp[] >>
      goal_assum drule >>
      simp[e_step_def, continue_def, application_thm, to_small_st_def,
           shift_fp_state_def, shift_fp_opts_def, fix_fp_state_def]
      )
    )
  >- (
    ‘getOpClass op = Icing’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
    gvs[] >> Cases_on `es` using SNOC_CASES >> gvs[]
    >- (gvs[Once small_eval_list_cases, to_small_st_def,
          do_app_def, AllCaseEqs(), store_alloc_def, getOpClass_def]) >>
    gvs[REVERSE_SNOC] >> Cases_on `l` >> gvs[]
    >- (
      ntac 2 $ gvs[Once small_eval_list_cases] >>
      dxrule e_step_add_ctxt >>
      disch_then $ qspec_then `[Capp op [] () [],env]` assume_tac >> gvs[] >>
      `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op [x],[])
        (env',to_small_st s2,s2.fp_state,Val v,[(Capp op [] () [],env)])` by
          simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def] >>
      Cases_on `rOpt` >> gvs[small_eval_def, compress_if_bool_compress_v]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def] >>
        every_case_tac >> simp[compress_v_def, shift_fp_opts_def, shift_fp_state_def, fix_fp_state_def]) >>
      Cases_on `e` >> gvs[small_eval_def]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def, shift_fp_opts_def, shift_fp_state_def]
        )
      >- (
        imp_res_tac $ INST_TYPE [beta |-> alpha] fpSemPropsTheory.fpOp_determ >> gvs[] >>
        first_x_assum $ qspec_then ‘s2.ffi’ assume_tac >> gs[] >>
        `shift_fp_opts s2 with <|refs := s2.refs; ffi := s2.ffi|> = shift_fp_opts s2` by
          gvs[state_component_equality, shift_fp_opts_def] >> simp[] >>
        ‘to_small_st (shift_fp_opts s2) = to_small_st s2’ by
          gvs[state_component_equality, to_small_st_def, shift_fp_opts_def] >>
        simp[] >>
        goal_assum drule >>
        simp[e_step_def, continue_def, application_thm, to_small_st_def,
             shift_fp_state_def, shift_fp_opts_def, fix_fp_state_def]
        )
      ) >>
    imp_res_tac $ INST_TYPE [beta |-> alpha] fpSemPropsTheory.fpOp_determ >> gvs[] >>
    first_x_assum $ qspec_then ‘s2.ffi’ assume_tac >> gs[] >>
    last_x_assum mp_tac >> once_rewrite_tac[GSYM APPEND] >>
    rewrite_tac[small_eval_list_Rval_APPEND] >> rw[] >> gvs[REVERSE_APPEND] >>
    pop_assum mp_tac >> ntac 2 $ simp[Once small_eval_list_cases] >> rw[] >> gvs[] >>
    dxrule e_step_to_App_mid >>
    disch_then $ qspecl_then [`h`,`[]`,`op`,`[]`] mp_tac >> rw[] >>
    `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op (h::SNOC x t), [])
      (env',to_small_st s2,s2.fp_state,Val v,[(Capp op (REVERSE lvs) () [],env)])` by (
      simp[Once RTC_CASES1, e_step_reln_def, e_step_def, REVERSE_SNOC, push_def] >>
      simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
      rev_drule e_step_add_ctxt >> simp[]) >>
    Cases_on `rOpt` >> gvs[small_eval_def, compress_if_bool_compress_v]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def] >>
      every_case_tac >> simp[compress_v_def, shift_fp_state_def, shift_fp_opts_def]) >>
    Cases_on `e` >> gvs[small_eval_def]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def, shift_fp_state_def, shift_fp_opts_def]
      )
    >- (
      imp_res_tac do_app_type_error >> gvs[] >>
      `shift_fp_opts s2 with <|refs := s2.refs; ffi := s2.ffi|> = shift_fp_opts s2` by
        gvs[state_component_equality, shift_fp_opts_def] >> simp[] >>
      ‘to_small_st (shift_fp_opts s2) = to_small_st s2’ by
        gvs[state_component_equality, to_small_st_def, shift_fp_opts_def] >>
      simp[] >>
      goal_assum drule >>
      simp[e_step_def, continue_def, application_thm, to_small_st_def,
           shift_fp_state_def, shift_fp_opts_def, fix_fp_state_def]
      )
    )
  >- (
    ‘getOpClass op = Reals’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
    gvs[] >> Cases_on `es` using SNOC_CASES >> gvs[]
    >- (
      gvs[Once small_eval_list_cases, to_small_st_def,
          do_app_def, AllCaseEqs(), store_alloc_def] >>
      simp[small_eval_def] >> irule_at Any RTC_SUBSET >>
      simp[e_step_reln_def, e_step_def, application_thm, do_app_def,
           store_alloc_def, return_def]
      ) >>
    gvs[REVERSE_SNOC] >> Cases_on `l` >> gvs[]
    >- (
      ntac 2 $ gvs[Once small_eval_list_cases] >>
      dxrule e_step_add_ctxt >>
      disch_then $ qspec_then `[Capp op [] () [],env]` assume_tac >> gvs[] >>
      `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op [x],[])
        (env',to_small_st s2,s2.fp_state,Val v,[(Capp op [] () [],env)])` by
          simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def] >>
      Cases_on `res` >> gvs[small_eval_def]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def]
        ) >>
      Cases_on `e` >> gvs[small_eval_def]
      >- (
        simp[Once RTC_CASES2] >> goal_assum drule >>
        simp[e_step_reln_def, e_step_def, continue_def, application_thm,
             to_small_st_def, return_def]
        )
      >- (
        imp_res_tac do_app_type_error >> gvs[] >>
        `s2 with <|refs := s2.refs; ffi := s2.ffi|> = s2` by
          gvs[state_component_equality] >> simp[] >>
        goal_assum drule >>
        simp[e_step_def, continue_def, application_thm, to_small_st_def, fix_fp_state_def]
        )
      ) >>
    last_x_assum mp_tac >> once_rewrite_tac[GSYM APPEND] >>
    rewrite_tac[small_eval_list_Rval_APPEND] >> rw[] >> gvs[REVERSE_APPEND] >>
    pop_assum mp_tac >> ntac 2 $ simp[Once small_eval_list_cases] >> rw[] >> gvs[] >>
    dxrule e_step_to_App_mid >>
    disch_then $ qspecl_then [`h`,`[]`,`op`,`[]`] mp_tac >> rw[] >>
    `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op (h::SNOC x t), [])
      (env',to_small_st s2,s2.fp_state,Val v,[(Capp op (REVERSE lvs) () [],env)])` by (
      simp[Once RTC_CASES1, e_step_reln_def, e_step_def, REVERSE_SNOC, push_def] >>
      simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
      rev_drule e_step_add_ctxt >> simp[]) >>
    Cases_on `res` >> gvs[small_eval_def]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def]
      ) >>
    Cases_on `e` >> gvs[small_eval_def]
    >- (
      simp[Once RTC_CASES2] >> goal_assum drule >>
      simp[e_step_reln_def, e_step_def, continue_def, application_thm,
           to_small_st_def, return_def]
      )
    >- (
      imp_res_tac do_app_type_error >> gvs[] >>
      `s2 with <|refs := s2.refs; ffi := s2.ffi|> = s2` by
        gvs[state_component_equality] >> simp[] >>
      goal_assum drule >>
      simp[e_step_def, continue_def, application_thm, to_small_st_def, fix_fp_state_def]
      )
    )
  >- (
    ‘getOpClass op = Reals’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
    gvs[] >> Cases_on `es` using SNOC_CASES >> gvs[]
    >- (
      gvs[Once small_eval_list_cases, to_small_st_def,
          do_app_def, AllCaseEqs(), store_alloc_def] >>
      simp[small_eval_def] >>
      ‘(shift_fp_opts s2).refs = s2.refs ∧ (shift_fp_opts s2).ffi = s2.ffi’ by simp[state_component_equality, shift_fp_opts_def] >>
      gvs[] >> irule_at Any RTC_REFL >>
      simp[e_step_reln_def, e_step_def, application_thm, do_app_def,
           store_alloc_def, return_def, shift_fp_state_def, shift_fp_opts_def, fix_fp_state_def]
      ) >>
    gvs[REVERSE_SNOC] >> Cases_on `l` >> gvs[]
    >- (
      ntac 2 $ gvs[Once small_eval_list_cases] >>
      dxrule e_step_add_ctxt >>
      disch_then $ qspec_then `[Capp op [] () [],env]` assume_tac >> gvs[] >>
      `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op [x],[])
        (env',to_small_st s2,s2.fp_state,Val v,[(Capp op [] () [],env)])` by
          simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def] >>
      gvs[small_eval_def] >>
      ‘to_small_st (shift_fp_opts s2) = to_small_st s2’ by
        simp[state_component_equality, shift_fp_opts_def, to_small_st_def] >>
      gs[] >>
      first_x_assum $ irule_at Any >>
      simp[e_step_reln_def, e_step_def, application_thm, do_app_def, continue_def,
           store_alloc_def, return_def, shift_fp_state_def, shift_fp_opts_def, fix_fp_state_def]) >>
    last_x_assum mp_tac >> once_rewrite_tac[GSYM APPEND] >>
    rewrite_tac[small_eval_list_Rval_APPEND] >> rw[] >> gvs[REVERSE_APPEND] >>
    pop_assum mp_tac >> ntac 2 $ simp[Once small_eval_list_cases] >> rw[] >> gvs[] >>
    dxrule e_step_to_App_mid >>
    disch_then $ qspecl_then [`h`,`[]`,`op`,`[]`] mp_tac >> rw[] >>
    `RTC e_step_reln (env,to_small_st s,s.fp_state,Exp $ App op (h::SNOC x t), [])
      (env',to_small_st s2,s2.fp_state,Val v,[(Capp op (REVERSE lvs) () [],env)])` by (
      simp[Once RTC_CASES1, e_step_reln_def, e_step_def, REVERSE_SNOC, push_def] >>
      simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
      rev_drule e_step_add_ctxt >> simp[]) >>
    gvs[small_eval_def] >>
    ‘to_small_st (shift_fp_opts s2) = to_small_st s2’ by
      simp[state_component_equality, shift_fp_opts_def, to_small_st_def] >>
    gs[] >>
    first_x_assum $ irule_at Any >>
    simp[e_step_reln_def, e_step_def, application_thm, do_app_def, continue_def,
         store_alloc_def, return_def, shift_fp_state_def, shift_fp_opts_def, fix_fp_state_def])
  >- (
    gvs[small_eval_def] >> Cases_on `es` using SNOC_CASES >> gvs[]
    >- (
      gvs[Once small_eval_list_cases, to_small_st_def] >>
      irule_at Any RTC_REFL >> simp[e_step_def, application_thm] >>
      Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases, fix_fp_state_def]
      ) >>
    gvs[REVERSE_SNOC] >> Cases_on `l` >> gvs[]
    >- (
      ntac 2 $ gvs[Once small_eval_list_cases] >>
      irule_at Any $ cj 2 RTC_RULES >>
      simp[e_step_reln_def, Once e_step_def, push_def] >>
      dxrule e_step_add_ctxt >> simp[] >> disch_then $ irule_at Any >>
      simp[e_step_def, continue_def, application_thm, to_small_st_def] >>
      Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases, fix_fp_state_def]
      ) >>
    last_x_assum mp_tac >> once_rewrite_tac[GSYM APPEND] >>
    rewrite_tac[small_eval_list_Rval_APPEND] >> rw[] >> gvs[REVERSE_APPEND] >>
    pop_assum mp_tac >> ntac 2 $ simp[Once small_eval_list_cases] >> rw[] >> gvs[] >>
    dxrule e_step_to_App_mid >>
    disch_then $ qspecl_then [`h`,`[]`,`op`,`[]`] mp_tac >> rw[] >>
    irule_at Any $ cj 2 RTC_RULES >>
    simp[e_step_reln_def, Once e_step_def, push_def, REVERSE_SNOC] >>
    irule_at Any $ iffRL RTC_CASES_RTC_TWICE >> goal_assum dxrule >>
    dxrule e_step_add_ctxt >> simp[] >> disch_then $ irule_at Any >>
    simp[e_step_def, continue_def, application_thm, to_small_st_def] >>
    Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases, fix_fp_state_def]
    )
   >- (
     full_simp_tac(srw_ss())[] >>
     srw_tac[][Once small_eval_app] >>
     `es = [] ∨ ?e es'. es = es'++[e]` by
        metis_tac [SRULE [SNOC_APPEND] SNOC_CASES]
     >- full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
     srw_tac[][] >>
     Cases_on`err`>>srw_tac[][small_eval_def] >>
     TRY (imp_res_tac small_eval_list_not_timeout >> full_simp_tac(srw_ss())[] >> NO_TAC) >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
     TRY (
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>full_simp_tac(srw_ss())[] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       irule e_single_error_add_ctxt >> unabbrev_all_tac >> gs[]) >>
     TRY (
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>full_simp_tac(srw_ss())[] >>
       srw_tac[][Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
       metis_tac[RTC_REFL]) >>
     TRY (
       imp_res_tac small_eval_list_app_type_error >> full_simp_tac(srw_ss())[] >>
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>full_simp_tac(srw_ss())[] >>
       srw_tac[][Once RTC_CASES_RTC_TWICE,PULL_EXISTS] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
       NO_TAC ) >>
     imp_res_tac small_eval_list_app_error >> full_simp_tac(srw_ss())[] >>
     imp_res_tac e_step_add_ctxt >>
     Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
     first_x_assum(qspec_then`ctx`strip_assume_tac)>>full_simp_tac(srw_ss())[] >>
     srw_tac[][Once RTC_CASES_RTC_TWICE,PULL_EXISTS] >>
     first_assum(match_exists_tac o concl) >> srw_tac[][] >>
     srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
     srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def] >>
     irule_at Any RTC_REFL
     )
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s',s'.fp_state,Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',s'.fp_state,Val v,[(Clog op () e2,env)])
                    (env,to_small_st s',s'.fp_state,Exp e',[])`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def] >>
       every_case_tac >>
       srw_tac[][] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def, small_eval_prefix])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s2,s2.fp_state,Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s2,s2.fp_state,Val v,[(Clog op () e2,env)])
                    (env,to_small_st s2,s2.fp_state,Val bv,[])`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, return_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def, small_eval_prefix])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s2,s2.fp_state,Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step (env',to_small_st s2,s2.fp_state,Val v,[(Clog op () e2,env)]) = Eabort (s2.fp_state,Rtype_error)`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def, fix_fp_state_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) s.fp_state e ([] ++ [(Clog op () e2,env)]) (to_small_st s', s'.fp_state, Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Cif () e2 e3,env)])
                      (env',to_small_st s',s'.fp_state,Val v,[(Cif () e2 e3,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',s'.fp_state,Val v,[(Cif () e2 e3,env)])
                    (env,to_small_st s',s'.fp_state,Exp e',[])`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def] >>
       every_case_tac >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def,
                  small_eval_prefix])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Cif () e2 e3,env)])
                      (env',to_small_st s2,s2.fp_state,Val v,[(Cif () e2 e3,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step (env',to_small_st s2,s2.fp_state,Val v,[(Cif () e2 e3,env)]) = Eabort (s2.fp_state, Rtype_error)`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def, fix_fp_state_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) s.fp_state e ([] ++ [(Cif () e2 e3,env)]) (to_small_st s', s'.fp_state, Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
   >- (full_simp_tac(srw_ss())[small_eval_def, bind_exn_v_def] >>
       imp_res_tac small_eval_match_thm >>
       PairCases_on `r` >>
       full_simp_tac(srw_ss())[] >>
       cases_on `r1` >|
       [all_tac,
        cases_on `e'`] >>
       srw_tac[][] >>
       full_simp_tac(srw_ss())[small_eval_def, alt_small_eval_def] >>
       `e_step_reln^*
          (env,to_small_st s,s.fp_state,Exp e,[(Cmat_check () pes (Conv (SOME bind_stamp) []),env)])
          (env',to_small_st s',s'.fp_state,Val v,[(Cmat_check () pes (Conv (SOME bind_stamp) []),env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln
          (env',to_small_st s',s'.fp_state,Val v,[(Cmat_check () pes (Conv (SOME bind_stamp) []),env)])
          (env,to_small_st s',s'.fp_state,Val v,[(Cmat () pes (Conv (SOME bind_stamp) []),env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]
                       \\ fs [to_small_st_def]) >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (match_mp_tac (small_eval_err_add_ctxt |> SPEC_ALL |> Q.INST [`c`|->`[]`]
          |> SIMP_RULE std_ss [APPEND]) \\ fs [])
   >- (full_simp_tac(srw_ss())[small_eval_def, bind_exn_v_def]
       \\ qexists_tac `env'`
       \\ qexists_tac `Val v`
       \\ qexists_tac `[(Cmat_check () pes (Conv (SOME bind_stamp) []),env)]`
       \\ qexists_tac ‘s2.fp_state’
       \\ srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]
       \\ fs [to_small_st_def, fix_fp_state_def]
       \\ metis_tac [e_step_add_ctxt, APPEND])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,s.fp_state,Exp e,[(Clet n () e',env)])
                      (env',to_small_st s',s'.fp_state,Val v,[(Clet n () e',env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',s'.fp_state,Val v,[(Clet n () e',env)])
                    (env with v := nsOptBind n v env.v,to_small_st s',s'.fp_state,Exp e',[])`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def] >>
       Q.ISPEC_THEN`r`assume_tac result_cases >>
       full_simp_tac(srw_ss())[small_eval_def, sem_env_component_equality] >>
       full_simp_tac(srw_ss())[small_eval_def, sem_env_component_equality] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) s.fp_state e ([] ++ [(Clet n () e2,env)]) (to_small_st s', s'.fp_state, Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
   >- (srw_tac[][small_eval_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Letrec funs e)` >>
       qexists_tac `[]` >>
       srw_tac[][RTC_REFL, e_step_def, fix_fp_state_def])
   >- (
     fs []
     >> Cases_on `SND r`
     >| [all_tac,
        cases_on `e'`]
     >- (
       fs [small_eval_def]
       >> simp [Once RTC_CASES2]
       >> qexists_tac `env`
       >> qexists_tac `(env',to_small_st (FST r),(FST r).fp_state,Val a,[(Ctannot () t,env)])`
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> simp [e_step_reln_def, e_step_def, continue_def, return_def])
     >- (
       fs [small_eval_def]
       >> simp [Once RTC_CASES2]
       >> qexists_tac `env'`
       >> drule e_step_add_ctxt >> simp[] >> disch_then $ irule_at Any
       >> simp [e_step_reln_def, e_step_def, continue_def, return_def])
     >- (
       fs [small_eval_def]
       >> qexists_tac `env'`
       >> qexists_tac `e'`
       >> qexists_tac `c'++[(Ctannot () t,env)]`
       >> qexists_tac ‘fp''’
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> irule e_single_error_add_ctxt >> gs[]))
   >- (
     fs []
     >> Cases_on `SND r`
     >| [all_tac,
        cases_on `e'`]
     >- (
       fs [small_eval_def]
       >> simp [Once RTC_CASES2]
       >> qexists_tac `env`
       >> qexists_tac `(env',to_small_st (FST r),(FST r).fp_state,Val a,[(Clannot () l,env)])`
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> simp [e_step_reln_def, e_step_def, continue_def, return_def])
     >- (
       fs [small_eval_def]
       >> simp [Once RTC_CASES2]
       >> qexists_tac `env'`
       >> drule e_step_add_ctxt >> simp[] >> disch_then $ irule_at Any
       >> simp [e_step_reln_def, e_step_def, continue_def, return_def])
     >- (
       fs [small_eval_def]
       >> qexists_tac `env'`
       >> qexists_tac `e'`
       >> qexists_tac `c'++[(Clannot () l,env)]`
       >> qexists_tac ‘fp''’
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> irule e_single_error_add_ctxt >> gs[]))
   >- (gs[small_eval_def]
       >> ‘∀ fp (s:'ffi state). to_small_st (s with fp_state := fp) = to_small_st s’
         by gs[to_small_st_def, state_component_equality]
       >> gs[]
       >> first_x_assum $ mp_then Any mp_tac e_step_add_ctxt
       >> disch_then $ qspec_then ‘[(Coptimise s.fp_state.canOpt sc (), env)]’ mp_tac
       >> simp[] >> strip_tac
       >> simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def]
       >> simp[Once RTC_CASES2]
       >> first_x_assum $ irule_at Any
       >> simp[e_step_reln_def, e_step_def, continue_def, return_def])
   >- (gs[small_eval_def]
       >> ‘∀ fp (s:'ffi state). to_small_st (s with fp_state := fp) = to_small_st s’
         by gs[to_small_st_def, state_component_equality]
       >> gs[]
       >> first_x_assum $ mp_then Any mp_tac e_step_add_ctxt
       >> disch_then $ qspec_then ‘[(Coptimise s.fp_state.canOpt sc (), env)]’ mp_tac
       >> simp[] >> strip_tac
       >> simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def]
       >> simp[Once RTC_CASES2]
       >> first_x_assum $ irule_at Any
       >> simp[e_step_reln_def, e_step_def, continue_def, return_def])
   >- (Cases_on ‘err’ >> gs[small_eval_def]
       >> ‘∀ fp (s:'ffi state). to_small_st (s with fp_state := fp) = to_small_st s’
         by gs[to_small_st_def, state_component_equality]
       >> gs[]
       >- (
        first_x_assum $ mp_then Any mp_tac e_step_add_ctxt
        >> disch_then $ qspec_then ‘[(Coptimise s.fp_state.canOpt sc (), env)]’ mp_tac
        >> simp[] >> strip_tac
        >> simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def]
        >> simp[Once RTC_CASES2]
        >> first_x_assum $ irule_at Any
        >> simp[e_step_reln_def, e_step_def, continue_def])
       >> first_x_assum $ mp_then Any mp_tac e_step_add_ctxt
       >> disch_then $ qspec_then ‘[(Coptimise s.fp_state.canOpt sc (), env)]’ mp_tac
       >> simp[] >> strip_tac
       >> simp[Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def]
       >> first_x_assum $ mp_then Any mp_tac e_single_error_add_ctxt_optimise
       >> disch_then $ qspec_then ‘[(Coptimise s.fp_state.canOpt sc (), env)]’ assume_tac
       >> qexistsl_tac [‘env'’, ‘e'’, ‘c' ++ [(Coptimise s.fp_state.canOpt sc (), env)]’, ‘fp''’]
       >> gs[fix_fp_state_def])
   >- (Cases_on ‘err’ >> gs[small_eval_def]
       >> ‘∀ fp (s:'ffi state). to_small_st (s with fp_state := fp) = to_small_st s’
         by gs[to_small_st_def, state_component_equality]
       >> gs[]
       >- (
        first_x_assum $ mp_then Any mp_tac e_step_add_ctxt
        >> disch_then $ qspec_then ‘[(Coptimise s.fp_state.canOpt sc (), env)]’ mp_tac
        >> simp[] >> strip_tac
        >> simp[Once RTC_CASES1, e_step_reln_def, e_step_def, push_def]
        >> simp[Once RTC_CASES2]
        >> first_x_assum $ irule_at Any
        >> simp[e_step_reln_def, e_step_def, continue_def])
       >> first_x_assum $ mp_then Any mp_tac e_step_add_ctxt
       >> disch_then $ qspec_then ‘[(Coptimise s.fp_state.canOpt sc (), env)]’ mp_tac
       >> simp[] >> strip_tac
       >> simp[Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def]
       >> first_x_assum $ mp_then Any mp_tac e_single_error_add_ctxt_optimise
       >> disch_then $ qspec_then ‘[(Coptimise s.fp_state.canOpt sc (), env)]’ assume_tac
       >> qexistsl_tac [‘env'’, ‘e'’, ‘c' ++ [(Coptimise s.fp_state.canOpt sc (), env)]’, ‘fp''’]
       >> gs[fix_fp_state_def])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules])
   >- (cases_on `err` >>
       full_simp_tac(srw_ss())[small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules]
       )
   >- (cases_on `err` >>
       full_simp_tac(srw_ss())[small_eval_def] >-
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules] >-
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases])
   >- metis_tac [small_eval_match_rules]
   >- metis_tac [small_eval_match_rules, FST, pair_CASES, to_small_st_def]
   >- metis_tac [small_eval_match_rules, FST, pair_CASES, to_small_st_def]
   >- metis_tac [small_eval_match_rules, FST, pair_CASES, to_small_st_def]
   >- metis_tac [small_eval_match_rules]
QED

Theorem evaluate_ctxts_cons:
  !ck s1 f cs res1 bv.
    evaluate_ctxts ck s1 (f::cs) res1 bv =
    ((?c s2 env v' res2 v.
        (res1 = Rval v) ∧
        (f = (c,env)) ∧
        evaluate_ctxt ck env s1 c v (s2, res2) ∧
        evaluate_ctxts ck s2 cs res2 bv) ∨
     (?c env err.
        (res1 = Rerr err) ∧
        (f = (c,env)) ∧
        ((∀pes. c ≠ Chandle () pes) ∨ (∀v. err ≠ Rraise v)) ∧
        (∀ oldSc sc. c ≠ Coptimise oldSc sc ()) ∧
        evaluate_ctxts ck s1 cs res1 bv) ∨
     (? env oldSc sc err.
        (res1 = Rerr err) ∧
        (f = (Coptimise oldSc sc (),env)) ∧
        evaluate_ctxts ck (s1 with fp_state := s1.fp_state with canOpt := oldSc) cs res1 bv) ∨
     (?pes s2 env v' res2 v.
        (res1 = Rerr (Rraise v)) ∧
        (f = (Chandle () pes,env)) ∧
        can_pmatch_all env.c s1.refs (MAP FST pes) v ∧
        evaluate_match ck env s1 v pes v (s2, res2) ∧
        evaluate_ctxts ck s2 cs res2 bv) ∨
     (?pes env v' res2 v.
        (res1 = Rerr (Rraise v)) ∧
        (f = (Chandle () pes,env)) ∧
        ~can_pmatch_all env.c s1.refs (MAP FST pes) v ∧
        evaluate_ctxts ck s1 cs (Rerr (Rabort Rtype_error)) bv))
Proof
  srw_tac[][] >>
  srw_tac[][Once evaluate_ctxts_cases] >>
  EQ_TAC >>
  srw_tac[][] >>
  metis_tac []
QED

val tac1 =
full_simp_tac(srw_ss())[evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_ctxts_cases, evaluate_ctxt_cases] >>
srw_tac[][] >>
metis_tac [oneTheory.one];

val tac3 =
full_simp_tac(srw_ss())[evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
srw_tac[][] >>
full_simp_tac(srw_ss())[evaluate_ctxts_cons, evaluate_ctxt_cases] >>
ONCE_REWRITE_TAC [hd (tl (CONJUNCTS evaluate_cases))] >>
srw_tac[][] >>
full_simp_tac(srw_ss())[evaluate_ctxts_cons, evaluate_ctxt_cases] >>
srw_tac [boolSimps.DNF_ss] [] >>
metis_tac [DECIDE ``SUC x = x + 1``, pair_CASES, REVERSE_APPEND];

Theorem evaluate_state_app_cons:
  evaluate_state ck (env,s,Exp e,(Capp op [] () es,env)::c) bv
  ⇒ evaluate_state ck (env,s,Exp (App op (REVERSE es++[e])),c) bv
Proof
  rw[evaluate_state_cases] >> rw[Once evaluate_cases] >>
  reverse $ gvs[evaluate_ctxts_cons] >> goal_assum $ drule_at Any >>
  qexists_tac `clk` >> simp[]
  >- (rpt disj2_tac >> simp[Once evaluate_cases]) >>
  full_simp_tac(srw_ss())[Once evaluate_ctxt_cases, REVERSE_REVERSE, REVERSE_APPEND] >>
  rw[Once evaluate_cases, PULL_EXISTS] >> gvs[]
  >- (disj1_tac >> simp[SF SFY_ss, opClass_cases])
  >- (disj2_tac >> disj1_tac >>
      simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss, opClass_cases])
  >- (disj2_tac >> disj1_tac >>
      simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss, opClass_cases])
  >- (‘~ opClass op FunApp ∧ ~ opClass op Icing ∧ ~ opClass op Reals’
         by (Cases_on ‘op’ >> gs[opClass_cases]) >>
      gs[] >>
      disj1_tac >> irule_at Any EQ_REFL >>
      simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss])
  >- (‘~ opClass op FunApp ∧ ~ opClass op Simple ∧ ~ opClass op Reals’
         by (Cases_on ‘op’ >> gs[opClass_cases]) >>
      gs[] >>
      disj1_tac >> ntac 2 $ irule_at Any EQ_REFL >>
      first_x_assum $ irule_at Any >>
      simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss])
  >- (‘~ opClass op FunApp ∧ ~ opClass op Simple ∧ ~ opClass op Reals’
         by (Cases_on ‘op’ >> gs[opClass_cases]) >>
      gs[] >>
      disj2_tac >> disj1_tac >> irule_at Any EQ_REFL >>
      first_x_assum $ irule_at Any >>
      simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss])
  >- (‘~ opClass op FunApp ∧ ~ opClass op Simple ∧ ~ opClass op Reals’
         by (Cases_on ‘op’ >> gs[opClass_cases]) >>
      gs[] >>
      disj2_tac >> disj2_tac >> disj1_tac >> ntac 2 $ irule_at Any EQ_REFL >>
      ntac 2 $ first_x_assum $ irule_at Any >>
      simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss])
  >- (‘~ opClass op FunApp ∧ ~ opClass op Simple ∧ ~ opClass op Icing’
         by (Cases_on ‘op’ >> gs[opClass_cases]) >>
      gs[] >>
      disj1_tac >> irule_at Any EQ_REFL >>
      simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss])
  >- (‘~ opClass op FunApp ∧ ~ opClass op Simple ∧ ~ opClass op Icing’
         by (Cases_on ‘op’ >> gs[opClass_cases]) >>
      gs[] >>
      disj2_tac >> disj1_tac >> irule_at Any EQ_REFL >>
      simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss])
  >- (gs[] >> ntac 6 disj2_tac >> disj1_tac >> simp[Once evaluate_cases, PULL_EXISTS, SF SFY_ss])
  >- (rpt disj2_tac >> simp[Once evaluate_cases, SF SFY_ss])
QED

Theorem one_step_backward:
  ∀env (s:α state) e c env' e' c' ck (bv:α state # (v,v) result)
   refs ffi refs' ffi' fp fp'.
    e_step (env,(refs,ffi),fp,e,c) = Estep (env',(refs',ffi'),fp',e',c') ∧
    evaluate_state ck (env',s with <| refs := refs'; ffi := ffi' ; fp_state := fp' |>,e',c') bv
  ⇒ evaluate_state ck (env,s with <| refs := refs; ffi := ffi ; fp_state := fp|>,e,c) bv
Proof
  rw[e_step_def] >> Cases_on `e` >> gvs[]
  >- (
    Cases_on `e''` >> gvs[push_def, return_def]
    >- (
      gvs[evaluate_ctxts_cons, evaluate_state_cases, evaluate_ctxt_cases] >>
      simp[Once evaluate_cases] >> metis_tac[]
      )
    >- (
      gvs[evaluate_ctxts_cons, evaluate_state_cases, evaluate_ctxt_cases] >>
      goal_assum $ drule_at Any >> simp[Once evaluate_cases]
      >- metis_tac[]
      >- (Cases_on `err` >> gvs[] >> metis_tac[]) >>
      metis_tac[]
      )
    >- tac3
    >- (every_case_tac >> gvs[SWAP_REVERSE_SYM, evaluate_state_cases] >> tac3)
    >- (every_case_tac >> gvs[] >> tac3)
    >- tac3
    >- (
      FULL_CASE_TAC >> gvs[application_thm, do_opapp_def, do_app_def]
      >- (
        gvs[AllCaseEqs(), store_alloc_def, return_def] >>
        simp[Once evaluate_state_cases] >> gvs[Once evaluate_state_cases, getOpClass_def] >>
        goal_assum $ dxrule_at Any >> ntac 2 $ simp[Once evaluate_cases, opClass_cases] >>
        simp[do_app_def, store_alloc_def] >> irule_at Any EQ_REFL
        ) >>
      gvs[SWAP_REVERSE_SYM] >> metis_tac[evaluate_state_app_cons]
      ) >>
    every_case_tac >> gvs[] >> tac3
    )
  >- (
    gvs[continue_def] >>
    Cases_on `c` >> gvs[] >> PairCases_on `h` >> gvs[] >> Cases_on `h0` >> gvs[] >>
    every_case_tac >> gvs[push_def, return_def, application_thm] >>
    gvs[evaluate_state_cases, evaluate_ctxts_cons, evaluate_ctxt_cases,
        evaluate_ctxts_cons, evaluate_ctxt_cases, ADD1, SF SFY_ss]
    >- (
      rename1 ‘getOpClass op’ >> Cases_on ‘getOpClass op’ >> gs[] >>
      once_rewrite_tac[cj 2 evaluate_cases] >> simp[] >>
      every_case_tac >> gvs[SF DNF_ss, SF SFY_ss]
      >- (‘opClass op FunApp’ by (Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]) >>
          ‘~ opClass op Simple ∧ ~ opClass op Icing ∧ ~ opClass op Reals’ by (Cases_on ‘op’ >> gs[opClass_cases]) >>
          gs[] >>
          disj1_tac >> qexists_tac `clk + 1` >> simp[SF SFY_ss])
      >- (‘opClass op FunApp’ by (Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]) >>
          ‘~ opClass op Simple ∧ ~ opClass op Icing ∧ ~ opClass op Reals’ by (Cases_on ‘op’ >> gs[opClass_cases]) >>
          gs[] >> first_x_assum $ irule_at Any >> gs[])
      )
    >- (
      rename1 ‘getOpClass op’ >> Cases_on ‘getOpClass op’ >> gs[] >>
      once_rewrite_tac[cj 2 evaluate_cases] >> simp[] >>
      every_case_tac >> gvs[SF DNF_ss, SF SFY_ss] >>
      Cases_on ‘op’ >>
      gs[do_app_def, getOpClass_def, opClass_cases, shift_fp_state_def,
         shift_fp_opts_def, compress_if_bool_def] >>
      gvs[evaluate_ctxts_cons] >> gvs[evaluate_ctxt_cases, SF SFY_ss]
      )
    >- (
      rename1 ‘getOpClass op’ >> Cases_on ‘getOpClass op’ >> gs[] >>
      once_rewrite_tac[cj 2 evaluate_cases] >> simp[] >>
      every_case_tac >> gvs[SF DNF_ss, SF SFY_ss] >>
      Cases_on ‘op’ >>
      gs[do_app_def, getOpClass_def, opClass_cases, shift_fp_state_def,
         shift_fp_opts_def, compress_if_bool_def] >>
      gvs[evaluate_ctxts_cons] >> gvs[evaluate_ctxt_cases, SF SFY_ss]
      )
    >~ [`evaluate_match`]
    >- simp[Once evaluate_cases, SF SFY_ss]
    >~ [‘pmatch _ _ _ _ _ = _’]
    >- simp[Once evaluate_cases, SF SFY_ss]
    >~ [‘pmatch _ _ _ _ _ = _’]
    >- simp[Once evaluate_cases, SF SFY_ss] >>
    once_rewrite_tac[cj 2 evaluate_cases] >> simp[SF DNF_ss] >>
    metis_tac[CONS_APPEND, APPEND_ASSOC]
  )
  >- (
    gvs[AllCaseEqs()] >>
    gvs[evaluate_state_cases, evaluate_ctxts_cons, evaluate_ctxt_cases,
        evaluate_ctxts_cons, evaluate_ctxt_cases, ADD1, SF SFY_ss, getOpClass_opClass]
    )
QED

Theorem evaluate_ctxts_type_error:
  !a s c ck fp. evaluate_ctxts ck (s with fp_state := fp) c (Rerr (Rabort a)) (s with fp_state := fix_fp_state c fp,Rerr (Rabort a))
Proof
  induct_on `c` >>
  srw_tac[][] >>
  srw_tac[][Once evaluate_ctxts_cases, fix_fp_state_def, state_component_equality] >>
  PairCases_on `h` >>
  srw_tac[][] >>
  Cases_on ‘h0’ >> gs[fix_fp_state_def]
  (* first_x_assum $ qspecl_then [‘a’, ‘s with fp_state := s.fp_state with canOpt := o'’, ‘ck’] mp_tac >>
  gs[state_component_equality] *)
QED

Theorem state_update_fp_later:
  s with <| clock := clk; fp_state := fp |> = (s with <| clock := clk |>) with fp_state := fp
Proof
  gs[state_component_equality]
QED

Theorem evaluate_ctxts_type_error_matchable:
  !a s c ck fp. s' = s ⇒
             evaluate_ctxts ck (s with fp_state := fp) c (Rerr (Rabort a))
                            (s' with fp_state := fix_fp_state c fp,Rerr (Rabort a))
Proof
  metis_tac[evaluate_ctxts_type_error]
QED

Theorem fix_fp_state_shift_fp_state:
  ∀ fp.
    fix_fp_state c (shift_fp_state fp) =
    shift_fp_state (fix_fp_state c fp)
Proof
  Induct_on ‘c’ >> rpt strip_tac >> gs[shift_fp_state_def, fix_fp_state_def]
  >> Cases_on ‘h’ >> gs[] >> Cases_on ‘q’ >> gs[fix_fp_state_def]
  >> first_x_assum $ qspec_then ‘fp with canOpt := o'’ mp_tac
  >> gs[fpState_component_equality, state_component_equality]
QED

Theorem shift_fp_state_shift_fp_opts:
  shift_fp_state s.fp_state = (shift_fp_opts s).fp_state
Proof
  gs[shift_fp_state_def, shift_fp_opts_def, state_component_equality]
QED

Theorem fix_fp_state_alt:
  s with fp_state := fix_fp_state c (shift_fp_opts s).fp_state =
  (shift_fp_opts s) with fp_state := fix_fp_state c (shift_fp_opts s).fp_state
Proof
  Induct_on ‘c’ >> gs[fix_fp_state_def, shift_fp_opts_def]
QED

Theorem one_step_backward_type_error:
  !env s e c fp fp'.
    e_step (env,to_small_st s,fp,e,c) = Eabort (fp',a)
    ⇒
    evaluate_state ck (env,s with fp_state := fp,e,c) (s with fp_state := fp', Rerr (Rabort a))
Proof
  srw_tac[][e_step_def] >>
  cases_on `e` >>
  full_simp_tac(srw_ss())[]
  >- (
  reverse (cases_on `e'`) >>
  full_simp_tac(srw_ss())[push_def, return_def] >>
  every_case_tac >>
  srw_tac[][evaluate_state_cases] >>
  srw_tac[][Once evaluate_cases] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][to_small_st_def] >> gs[] >>
  rewrite_tac[state_update_fp_later]
  >> TRY (
    irule_at Any evaluate_ctxts_type_error_matchable >>
    srw_tac[SFY_ss][state_component_equality] >> rpt $ irule_at Any EQ_REFL)
  >- (
    full_simp_tac(srw_ss())[application_thm] >>
    rename1 ‘getOpClass op’ >> Cases_on ‘getOpClass op’ >> gs[getOpClass_opClass]
    >- (Cases_on ‘op’ >> gs[getOpClass_def, to_small_st_def, do_app_def] >>
        rveq >> gs[opClass_cases] >> qexists_tac ‘s.clock’ >> simp[Once evaluate_cases] >>
        irule_at Any evaluate_ctxts_type_error_matchable >> gs[state_component_equality])
    >- (every_case_tac >> gs[] >>
        ‘~ opClass op Icing ∧ ~ opClass op Reals ∧ ~ opClass op Simple’
          by (Cases_on ‘op’ >> gs[opClass_cases]) >>
        gs[] >> qexists_tac ‘s.clock’ >> ntac 4 $ simp[Once evaluate_cases] >> rveq >>
        rewrite_tac[state_update_fp_later] >>
        irule evaluate_ctxts_type_error_matchable >> gs[state_component_equality])
    >- (‘~ opClass op Icing ∧ ~ opClass op Reals ∧ ~ opClass op FunApp’
          by (Cases_on ‘op’ >> gs[opClass_cases]) >>
        gs[] >>
        qexists_tac ‘s.clock’ >> ntac 3 $ simp[Once evaluate_cases] >>
        every_case_tac >> gs[return_def] >> rveq >> gs[to_small_st_def] >>
        imp_res_tac do_app_type_error >> gs[] >>
        rewrite_tac[state_update_fp_later] >>
        irule_at Any evaluate_ctxts_type_error_matchable >> gs[state_component_equality])
    >- (‘~ opClass op Simple ∧ ~ opClass op Reals ∧ ~ opClass op FunApp’
          by (Cases_on ‘op’ >> gs[opClass_cases]) >>
        gs[] >>
        qexists_tac ‘s.clock’ >> ntac 5 $ simp[Once evaluate_cases] >>
        every_case_tac >> gs[return_def] >> rveq >> gs[to_small_st_def] >>
        imp_res_tac do_app_type_error >>
        gs[compress_if_bool_def, shift_fp_state_shift_fp_opts, fix_fp_state_alt] >>
        ‘getOpClass op = Icing’ by gs[GSYM getOpClass_opClass] >>
          TRY (Cases_on ‘q’ >> imp_res_tac (INST_TYPE [beta |-> alpha] fpSemPropsTheory.fpOp_determ) >>
          res_tac >> first_x_assum $ qspec_then ‘s.ffi’ assume_tac >> gs[]) >>
        rewrite_tac[state_update_fp_later] >>
        irule_at Any evaluate_ctxts_type_error_matchable >>
        gs[state_component_equality, shift_fp_opts_def, shift_fp_state_def])
    >- (‘~ opClass op Simple ∧ ~ opClass op Icing ∧ ~ opClass op FunApp’
          by (Cases_on ‘op’ >> gs[opClass_cases]) >>
        gs[] >>
        qexists_tac ‘s.clock’ >> ntac 4 $ simp[Once evaluate_cases] >>
        every_case_tac >> gs[to_small_st_def, return_def] >> rveq >>
        gs[shift_fp_state_shift_fp_opts, fix_fp_state_alt] >>
        ‘getOpClass op = Reals’ by gs[GSYM getOpClass_opClass] >>
        TRY (Cases_on ‘q’ >> gs[] >>
             imp_res_tac (INST_TYPE [beta |-> alpha] fpSemPropsTheory.realOp_determ) >>
             res_tac >> first_x_assum $ qspec_then ‘s.ffi’ assume_tac >> gs[]) >>
        rewrite_tac[state_update_fp_later] >>
        irule_at Any evaluate_ctxts_type_error_matchable >>
        gs[state_component_equality, shift_fp_opts_def, shift_fp_state_def])) >>
  metis_tac[do_con_check_build_conv,NOT_SOME_NONE]
  ) >>
  full_simp_tac(srw_ss())[continue_def] >>
  cases_on `c` >> full_simp_tac(srw_ss())[] >>
  cases_on `h` >> full_simp_tac(srw_ss())[] >>
  cases_on `q` >> full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[evaluate_state_cases, push_def, return_def] >>
  srw_tac[][evaluate_ctxts_cons, evaluate_ctxt_cases, to_small_st_def] >>
  srw_tac[][PULL_EXISTS]
  >- (
    full_simp_tac(srw_ss())[application_thm] >>
    rename1 ‘getOpClass op’ >> Cases_on ‘getOpClass op’ >> gs[getOpClass_opClass]
    >- (Cases_on ‘op’ >> gs[getOpClass_def, to_small_st_def, do_app_def] >>
        rveq >> gs[opClass_cases] >> qexists_tac ‘s.clock’ >> simp[Once evaluate_cases] >>
        irule_at Any evaluate_ctxts_type_error_matchable >> gs[state_component_equality])
    >- (every_case_tac >> gs[] >>
        ‘~ opClass op Icing ∧ ~ opClass op Reals ∧ ~ opClass op Simple’
          by (Cases_on ‘op’ >> gs[opClass_cases]) >>
        gs[] >> qexists_tac ‘s.clock’ >> ntac 4 $ simp[Once evaluate_cases] >> rveq >>
        rewrite_tac[state_update_fp_later] >>
        irule evaluate_ctxts_type_error_matchable >> gs[state_component_equality])
    >- (‘~ opClass op Icing ∧ ~ opClass op Reals ∧ ~ opClass op FunApp’
          by (Cases_on ‘op’ >> gs[opClass_cases]) >>
        gs[] >>
        qexists_tac ‘s.clock’ >> ntac 3 $ simp[Once evaluate_cases] >>
        every_case_tac >> gs[return_def] >> rveq >> gs[to_small_st_def] >>
        imp_res_tac do_app_type_error >> gs[] >>
        rewrite_tac[state_update_fp_later] >>
        irule_at Any evaluate_ctxts_type_error_matchable >> gs[state_component_equality])
    >- (‘~ opClass op Simple ∧ ~ opClass op Reals ∧ ~ opClass op FunApp’
          by (Cases_on ‘op’ >> gs[opClass_cases]) >>
        gs[] >>
        qexists_tac ‘s.clock’ >> ntac 5 $ simp[Once evaluate_cases] >>
        every_case_tac >> gs[return_def] >> rveq >> gs[to_small_st_def] >>
        imp_res_tac do_app_type_error >>
        gs[compress_if_bool_def, shift_fp_state_shift_fp_opts, fix_fp_state_alt] >>
        ‘getOpClass op = Icing’ by gs[GSYM getOpClass_opClass] >>
          TRY (Cases_on ‘q’ >> imp_res_tac (INST_TYPE [beta |-> alpha] fpSemPropsTheory.fpOp_determ) >>
          res_tac >> first_x_assum $ qspec_then ‘s.ffi’ assume_tac >> gs[]) >>
        rewrite_tac[state_update_fp_later] >>
        irule_at Any evaluate_ctxts_type_error_matchable >>
        gs[state_component_equality, shift_fp_opts_def, shift_fp_state_def])
    >- (‘~ opClass op Simple ∧ ~ opClass op Icing ∧ ~ opClass op FunApp’
          by (Cases_on ‘op’ >> gs[opClass_cases]) >>
        gs[] >>
        qexists_tac ‘s.clock’ >> ntac 4 $ simp[Once evaluate_cases] >>
        every_case_tac >> gs[to_small_st_def, return_def] >> rveq >>
        gs[shift_fp_state_shift_fp_opts, fix_fp_state_alt] >>
        ‘getOpClass op = Reals’ by gs[GSYM getOpClass_opClass] >>
        TRY (Cases_on ‘q’ >> gs[] >>
             imp_res_tac (INST_TYPE [beta |-> alpha] fpSemPropsTheory.realOp_determ) >>
             res_tac >> first_x_assum $ qspec_then ‘s.ffi’ assume_tac >> gs[]) >>
        rewrite_tac[state_update_fp_later] >>
        irule_at Any evaluate_ctxts_type_error_matchable >>
        gs[state_component_equality, shift_fp_opts_def, shift_fp_state_def])) >>
  srw_tac[][Once evaluate_cases] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [arithmeticTheory.ADD1,to_small_st_def] >>
  srw_tac[][Once evaluate_cases] >>
  srw_tac[DNF_ss][] >> full_simp_tac(srw_ss())[to_small_st_def] >>
  rewrite_tac[state_update_fp_later] >>
  ((irule_at Any evaluate_ctxts_type_error_matchable >>
    srw_tac[][state_component_equality] >> rpt $ irule_at Any EQ_REFL) ORELSE
   metis_tac[do_con_check_build_conv,NOT_SOME_NONE])
QED

Theorem small_exp_to_big_exp:
  ∀ck env refs (ffi:α ffi_state) e c fp env' refs' ffi' fp' e' c'.
    RTC e_step_reln (env,(refs,ffi),fp,e,c) (env',(refs',ffi'),fp',e',c') ⇒
    ∀(s:α state) r.
      evaluate_state ck (env',s with <| refs := refs'; ffi := ffi'; fp_state := fp' |>,e',c') r
    ⇒ evaluate_state ck (env,s with <| refs := refs; ffi := ffi; fp_state := fp|>,e,c) r
Proof
  Induct_on `RTC` >> rw[e_step_reln_def] >> simp[] >>
  metis_tac[one_step_backward, PAIR]
QED

Theorem evaluate_state_no_ctxt:
  !env (s:'a state) e r ck.
    evaluate_state F (env,s,Exp e,[]) r ⇔
    evaluate F env (s with clock := (FST r).clock) e r
Proof
  rw[evaluate_state_cases, Once evaluate_ctxts_cases] >>
  eq_tac >> rw[] >> gvs[]
  >- (imp_res_tac big_unclocked >> gvs[])
  >- (PairCases_on `r` >> gvs[SF SFY_ss])
QED

Theorem evaluate_state_val_no_ctxt:
  !env (s:'a state) e.
    evaluate_state F (env,s,Val e,[]) r ⇔
    ∃clk. r = (s with clock := clk, Rval e)
Proof
  rw[evaluate_state_cases, Once evaluate_ctxts_cases] >>
  rw[Once evaluate_ctxts_cases]
QED

Theorem evaluate_state_val_raise_ctxt:
  !env (s:'a state) v env'.
    evaluate_state F (env,s,Val v,[(Craise (), env')]) r ⇔
    ∃clk. r = (s with clock := clk, Rerr (Rraise v))
Proof
  rw[evaluate_state_cases, Once evaluate_ctxts_cases] >>
  ntac 2 $ rw[Once evaluate_ctxts_cases] >>
  rw[evaluate_ctxt_cases]
QED

Triviality evaluate_change_state = Q.prove(
  `evaluate a b c d (e,f) ∧ c = c' ∧ e = e' ⇒
   evaluate a b c' d (e',f)`,
   srw_tac[][] >> srw_tac[][]) |> GEN_ALL;

Theorem small_big_exp_equiv:
 !env s e s' r.
   small_eval env (to_small_st s) s.fp_state e [] (to_small_st s', s'.fp_state, r) ∧
   s.clock = s'.clock ∧ s.next_type_stamp = s'.next_type_stamp ∧
   s.next_exn_stamp = s'.next_exn_stamp ∧ s.eval_state = s'.eval_state
   ⇔
   evaluate F env s e (s',r)
Proof
  rw[] >> reverse eq_tac
  >- (
    rw[] >> imp_res_tac big_exp_to_small_exp >>
    gvs[small_eval_def, to_small_res_def] >>
    metis_tac[evaluate_no_new_types_exns, big_unclocked, FST]
    ) >>
  rw[] >> reverse (Cases_on `r` >| [all_tac, Cases_on `e'`]) >>
  gvs[small_eval_def, to_small_st_def] >>
  imp_res_tac $ Q.SPEC `F` small_exp_to_big_exp >>
  gvs[evaluate_state_val_no_ctxt, evaluate_state_no_ctxt,
      evaluate_state_val_raise_ctxt, PULL_EXISTS]
  >- (
    imp_res_tac $ SRULE [to_small_st_def] one_step_backward_type_error >>
    pop_assum $ qspec_then `F` assume_tac >>
    irule evaluate_change_state >> first_x_assum $ irule_at Any >>
    simp[state_component_equality] >> irule_at Any EQ_REFL >> simp[] >>
    ‘s' with fp_state := s'.fp_state = s'’ by gs[state_component_equality] >>
    gs[] >>
    qsuff_tac `s' with <| refs := s'.refs; ffi := s'.ffi; fp_state := fp'' |> = s' with <| fp_state := fp'' |>` >>
    rw[] >> simp[state_component_equality]
    )
  >- (
    gvs[Once evaluate_state_cases] >> gvs[Once evaluate_ctxts_cases, PULL_EXISTS] >>
    pop_assum $ qspecl_then [`s'`,`s'.clock`] assume_tac >>
    imp_res_tac evaluate_ignores_types_exns_eval >> gvs[] >>
    pop_assum $ qspecl_then
      [`s.eval_state`,`s.next_exn_stamp`,`s.next_type_stamp`] assume_tac >>
    irule evaluate_change_state >> first_x_assum $ irule_at Any >>
    imp_res_tac big_unclocked >> gvs[state_component_equality]
    )
  >- (
    pop_assum $ qspecl_then [`s'`,`s'.clock`] assume_tac >>
    imp_res_tac evaluate_ignores_types_exns_eval >> gvs[] >>
    pop_assum $ qspecl_then
      [`s.eval_state`,`s.next_exn_stamp`,`s.next_type_stamp`] assume_tac >>
    irule evaluate_change_state >> first_x_assum $ irule_at Any >>
    imp_res_tac big_unclocked >> gvs[state_component_equality]
    )
QED

Theorem e_diverges_big_clocked:
  e_diverges env (to_small_st s) s.fp_state e ⇔
  ∀ck. ∃s'. evaluate T env (s with clock := ck) e (s', Rerr (Rabort Rtimeout_error))
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    drule_at Concl $ iffLR untyped_safety_exp >> rw[] >>
    `∀r. ¬evaluate F env s e r` by (
      CCONTR_TAC >> gvs[] >> drule $ cj 1 big_exp_to_small_exp >> gvs[]) >>
    gvs[big_clocked_unclocked_equiv_timeout] >> metis_tac[]
    )
  >- (
    `∀r. ¬evaluate F env s e r` by (
      simp[big_clocked_unclocked_equiv_timeout] >> rw[] >>
      pop_assum $ qspec_then `c` assume_tac >> gvs[] >>
      goal_assum drule >> drule $ cj 1 big_clocked_timeout_0 >> simp[]) >>
    `∀r. ¬small_eval env (to_small_st s) s.fp_state e [] r` by (
      CCONTR_TAC >> gvs[] >>
      PairCases_on `r` >>
      ‘r2 = (s with <| refs := r0; ffi := r1; fp_state := r2 |>).fp_state’ by
        simp[state_component_equality] >>
      pop_assum SUBST_ALL_TAC >>
      `(r0,r1) = to_small_st (s with <| refs := r0; ffi := r1; fp_state := r2 |>)` by
        simp[to_small_st_def] >>
      pop_assum SUBST_ALL_TAC >> drule $ iffLR small_big_exp_equiv >> simp[]) >>
    CCONTR_TAC >> gvs[GSYM untyped_safety_exp]
    )
QED



(**********

  Big-step safety

**********)

Theorem untyped_safety_decs:
  (∀d (s:'ffi state) env.
     (∃r. evaluate_dec F env s d r) = ¬dec_diverges env s d) ∧
  (∀ds (s:'ffi state) env.
     (∃r. evaluate_decs F env s ds r) = ¬decs_diverges env s ds)
Proof
  ho_match_mp_tac astTheory.dec_induction >> rw[] >>
  rw[Once evaluate_dec_cases, Once dec_diverges_cases, GSYM untyped_safety_exp] >>
  gvs[]
  >- (
    Cases_on `ALL_DISTINCT (pat_bindings p []) ∧
              every_exp (one_con_check env.c) e` >>
    gvs[GSYM small_big_exp_equiv, to_small_st_def] >>
    eq_tac >- metis_tac[] >> rw[] >>
    PairCases_on `r` >>
    Q.REFINE_EXISTS_TAC `(s with <| refs := r0; ffi := r1; fp_state := r2 |>, res)` >> simp[] >>
    reverse $ Cases_on `r3` >> gvs[]
    >- (qexists_tac `Rerr e'` >> gvs[]) >>
    Cases_on `pmatch env.c r0 p a []` >> gvs[]
    >- (
      qexists_tac `Rerr (Rraise bind_exn_v)` >> gvs[] >>
      disj1_tac >> goal_assum drule >> simp[]
      )
    >- (
      qexists_tac `Rerr (Rabort Rtype_error)` >> gvs[] >>
      disj1_tac >> goal_assum drule >> simp[]
      )
    >- (
      qexists_tac `Rval <| v := alist_to_ns a' ; c := nsEmpty |>` >> gvs[] >>
      goal_assum drule >> simp[]
      )
    )
  >- metis_tac[NOT_EVERY]
  >- metis_tac[NOT_EVERY]
  >- (
    eq_tac >> rw[] >> gvs[EXISTS_PROD, PULL_EXISTS] >>
    metis_tac[result_nchotomy]
    )
  >- (
    gvs[EXISTS_PROD, PULL_EXISTS, declare_env_def] >>
    ntac 2 $ pop_assum $ mp_tac o GSYM >>
    gvs[] >> rw[] >> eq_tac >> rw[] >> gvs[] >>
    metis_tac[result_nchotomy, decs_determ, PAIR_EQ, result_11, result_distinct]
    )
  >- (
    gvs[EXISTS_PROD, SF DNF_ss] >>
    Cases_on `declare_env s'.eval_state env` >> gvs[] >> Cases_on `x` >> gvs[]
    )
  >- (
    gvs[EXISTS_PROD, declare_env_def] >>
    ntac 2 $ pop_assum $ mp_tac o GSYM >> rw[] >> eq_tac >> rw[] >>
    metis_tac[result_nchotomy, result_distinct, decs_determ, PAIR_EQ, result_11]
    )
QED

Theorem untyped_safety_decs_alt:
  (∀d (s:'ffi state) env.
    (∀r. ¬evaluate_dec F env s d r) = dec_diverges env s d) ∧
  (∀ds (s:'ffi state) env.
    (∀r. ¬evaluate_decs F env s ds r) = decs_diverges env s ds)
Proof
  rw[] >> metis_tac[untyped_safety_decs]
QED

Theorem dec_diverges_big_clocked:
  dec_diverges env st d ⇔
  ∀ck. ∃st'.
    evaluate_dec T env (st with clock := ck) d (st', Rerr (Rabort Rtimeout_error))
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    gvs[GSYM untyped_safety_decs_alt] >>
    qspecl_then [`env`,`st with clock := ck`,`d`]
      assume_tac big_clocked_dec_total >> gvs[] >>
    qsuff_tac `∃st'. r = (st', Rerr (Rabort Rtimeout_error))` >>
    rw[] >> gvs[SF SFY_ss] >>
    CCONTR_TAC >> gvs[] >> PairCases_on `r` >> gvs[] >>
    drule $ cj 1 evaluate_decs_clocked_to_unclocked >> simp[] >>
    qexists_tac `st.clock` >> simp[with_same_clock]
    )
  >- (
    simp[GSYM untyped_safety_decs_alt] >> rw[] >>
    CCONTR_TAC >> gvs[] >> PairCases_on `r` >>
    drule $ cj 1 evaluate_decs_unclocked_to_clocked >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `c` assume_tac >> gvs[] >>
    drule $ cj 1 decs_determ >> disch_then rev_drule >> strip_tac >> gvs[] >>
    rev_drule $ cj 1 big_dec_unclocked_no_timeout >> simp[]
    )
QED

Theorem decs_diverges_big_clocked:
  decs_diverges env st ds ⇔
  ∀ck. ∃st'.
    evaluate_decs T env (st with clock := ck) ds (st', Rerr (Rabort Rtimeout_error))
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    gvs[GSYM untyped_safety_decs_alt] >>
    qspecl_then [`ds`,`env`,`st with clock := ck`]
      assume_tac big_clocked_decs_total >> gvs[] >>
    qsuff_tac `∃st'. r = (st', Rerr (Rabort Rtimeout_error))` >>
    rw[] >> gvs[SF SFY_ss] >>
    CCONTR_TAC >> gvs[] >> PairCases_on `r` >> gvs[] >>
    drule $ cj 2 evaluate_decs_clocked_to_unclocked >> simp[] >>
    qexists_tac `st.clock` >> simp[with_same_clock]
    )
  >- (
    simp[GSYM untyped_safety_decs_alt] >> rw[] >>
    CCONTR_TAC >> gvs[] >> PairCases_on `r` >>
    drule $ cj 2 evaluate_decs_unclocked_to_clocked >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `c` assume_tac >> gvs[] >>
    drule $ cj 2 decs_determ >> disch_then rev_drule >> strip_tac >> gvs[] >>
    rev_drule $ cj 2 big_dec_unclocked_no_timeout >> simp[]
    )
QED



(**********

  Prove equivalence between small-step and big-step semantics for declarations.

**********)

val decl_step_ss = simpLib.named_rewrites "decl_step_ss"
  [decl_step_reln_def, decl_step_def, decl_continue_def];

Theorem update_fp_state_id[local,simp]:
  s with fp_state := s.fp_state = s
Proof
  gs[state_component_equality]
QED

Theorem big_dec_to_small_dec:
  (∀ck env (st:'ffi state) d r.
    evaluate_dec ck env st d r ⇒ ¬ck
  ⇒ small_eval_dec env (st, Decl d, []) r) ∧

  (∀ck env (st:'ffi state) ds r.
    evaluate_decs ck env st ds r ⇒ ¬ck
  ⇒ small_eval_decs env st ds r)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[small_eval_dec_def] >> gvs[]
  >- (
    simp[Once RTC_CASES1, SF decl_step_ss] >>
    drule_all $ iffRL small_big_exp_equiv >> strip_tac >>
    gvs[small_eval_def] >>
    drule e_step_reln_decl_step_reln >>
    disch_then $ qspecl_then [`env`,`st`,`locs`,`p`,`[]`] mp_tac >>
    simp[to_small_st_def] >>
    qmatch_goalsub_abbrev_tac `RTC _ (sta,_) (stb,_)` >> strip_tac >>
    `sta = st ∧ stb = s2` by (
      unabbrev_all_tac >> gvs[state_component_equality]) >> gvs[] >>
    qmatch_goalsub_abbrev_tac `Env new_env` >>
    drule small_eval_dec_prefix >>
    disch_then $ qspec_then `(s2, Rval new_env)` mp_tac >>
    simp[small_eval_dec_def, collapse_env_def] >> disch_then irule >>
    irule RTC_SINGLE >> simp[SF decl_step_ss, collapse_env_def]
    )
  >- (
    simp[Once RTC_CASES1, SF decl_step_ss] >>
    irule_at Any OR_INTRO_THM2 >>
    drule_all $ iffRL small_big_exp_equiv >> strip_tac >>
    gvs[small_eval_def] >>
    drule e_step_reln_decl_step_reln >>
    disch_then $ qspecl_then [`env`,`st`,`locs`,`p`,`[]`] mp_tac >>
    simp[to_small_st_def] >>
    qmatch_goalsub_abbrev_tac `RTC _ (sta,_) (stb,_)` >> strip_tac >>
    `sta = st ∧ stb = s2` by (
      unabbrev_all_tac >> gvs[state_component_equality]) >> gvs[] >>
    qexists_tac ‘s2.fp_state’ >>
    simp[collapse_env_def] >> goal_assum drule >>
    simp[decl_step_def, collapse_env_def]
    )
  >- (
    simp[Once RTC_CASES1, SF decl_step_ss] >>
    irule_at Any OR_INTRO_THM2 >>
    drule_all $ iffRL small_big_exp_equiv >> strip_tac >>
    gvs[small_eval_def] >>
    drule e_step_reln_decl_step_reln >>
    disch_then $ qspecl_then [`env`,`st`,`locs`,`p`,`[]`] mp_tac >>
    simp[to_small_st_def] >>
    qmatch_goalsub_abbrev_tac `RTC _ (sta,_) (stb,_)` >> strip_tac >>
    `sta = st ∧ stb = s2` by (
      unabbrev_all_tac >> gvs[state_component_equality]) >> gvs[] >>
    qexists_tac ‘s2.fp_state’ >>
    simp[collapse_env_def] >> goal_assum drule >>
    simp[decl_step_def, collapse_env_def]
    )
  >- (qexists_tac ‘st.fp_state’ >> simp[] >>
      irule_at Any RTC_REFL >> simp[decl_step_def])
  >- (qexists_tac ‘st.fp_state’ >> simp[] >>
      irule_at Any RTC_REFL >> simp[decl_step_def,collapse_env_def])
  >- (
    Cases_on `err` >> gvs[small_eval_dec_def] >>
      simp[Once RTC_CASES1, SF decl_step_ss] >>
      irule_at Any OR_INTRO_THM2 >>
      drule_all $ iffRL small_big_exp_equiv >> strip_tac >>
      gvs[small_eval_def] >>
      drule e_step_reln_decl_step_reln >>
      disch_then $ qspecl_then [`env`,`st`,`locs`,`p`,`[]`] mp_tac >>
      simp[to_small_st_def] >>
      qmatch_goalsub_abbrev_tac `RTC _ (sta,_) (stb,_)` >> strip_tac >>
      (`sta = st ∧ stb = s'` by (
        unabbrev_all_tac >> gvs[state_component_equality]) ORELSE
      `sta = st ∧ stb = s' with fp_state := fp''` by (
        unabbrev_all_tac >> gvs[state_component_equality])) >> gvs[] >|
      [ qexists_tac ‘s'.fp_state’, qexists_tac ‘fp''’] >>
      simp[collapse_env_def] >> goal_assum drule >>
      simp[decl_step_def] >> gvs[to_small_st_def] >>
      rpt (TOP_CASE_TAC >> gvs[]) >> gvs[e_step_def, continue_def]
    )
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss, collapse_env_def])
  >- (qexists_tac ‘st.fp_state’ >> simp[] >>
      irule_at Any RTC_REFL >> simp[decl_step_def])
  >- (qexists_tac ‘st.fp_state’ >> simp[] >>
      irule_at Any RTC_REFL >> simp[decl_step_def] >>
      IF_CASES_TAC >> fs [collapse_env_def] >>
      gvs [EVERY_MEM,EXISTS_MEM])
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss])
  >- (
    qexists_tac ‘st.fp_state’ >> simp[] >>
    irule_at Any RTC_REFL >> simp[decl_step_def] >>
    IF_CASES_TAC >> gvs[] >> pop_assum mp_tac >> simp[]
    )
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss, collapse_env_def])
  >- (qexists_tac ‘st.fp_state’ >> simp[] >>
     irule_at Any RTC_REFL >> simp[SF decl_step_ss, collapse_env_def])
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss, empty_dec_env_def])
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss])
  >- (
    drule small_eval_decs_Rval_Dmod >> simp[small_eval_dec_def, lift_dec_env_def]
    )
  >- (
    simp[GSYM small_eval_dec_def] >> irule small_eval_decs_Rerr_Dmod >> simp[]
    )
  >- (
    PairCases_on `r` >> gvs[] >> Cases_on `r1` >> gvs[]
    >- (
      irule small_eval_decs_Rval_Dlocal >> simp[] >>
      goal_assum drule >> first_x_assum irule >>
      rpt $ goal_assum drule
      )
    >- (
      irule small_eval_decs_Rerr_Dlocal >> simp[] >> disj2_tac >>
      goal_assum drule >> first_x_assum irule >>
      rpt $ goal_assum drule
      )
    )
  >- (
    simp[GSYM small_eval_dec_def] >> irule small_eval_decs_Rerr_Dlocal >> simp[]
    )
  >- simp[Once small_eval_decs_cases, empty_dec_env_def]
  >- (
    simp[Once small_eval_decs_cases] >> disj2_tac >>
    simp[small_eval_dec_def] >> goal_assum drule >> simp[]
    )
  >- (
    simp[Once small_eval_decs_cases] >> disj1_tac >>
    irule_at Any EQ_REFL >> simp[small_eval_dec_def] >>
    goal_assum drule >> simp[]
    )
QED

Theorem dec_diverges_imp_small_decl_diverges:
  (∀env (st:'ffi state) d. dec_diverges env st d ⇒
    ∀env' cs. collapse_env env' cs = env ⇒
      small_decl_diverges env' (st, Decl d, cs)) ∧

  (∀env (st:'ffi state) ds. decs_diverges env st ds ⇒
    (∀env' cs enva envb mn.
      enva +++ envb +++ collapse_env env' cs = env
     ⇒ small_decl_diverges env' (st, Env enva, Cdmod mn envb ds :: cs)) ∧
    (∀env' cs enva envb gds.
      enva +++ envb +++ collapse_env env' cs = env
     ⇒ small_decl_diverges env' (st, Env enva, CdlocalL envb ds gds :: cs)) ∧
    (∀env' cs enva lenv genv.
      enva +++ genv +++ lenv +++ collapse_env env' cs = env
     ⇒ small_decl_diverges env' (st, Env enva, CdlocalG lenv genv ds :: cs)))
Proof
  ho_match_mp_tac dec_diverges_ind >> rw[]
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    irule small_decl_diverges_ExpVal >> simp[]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss]
    )
  >- (
    irule small_decl_diverges_prefix >>
    simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
    drule $ cj 2 big_dec_to_small_dec >> simp[] >> strip_tac >>
    drule small_eval_decs_Rval_Dlocal_lemma_1 >> simp[] >>
    disch_then $ qspecl_then [`empty_dec_env`,`empty_dec_env`] mp_tac >> simp[] >>
    disch_then $ qspec_then `ds` assume_tac >>
    drule RTC_decl_step_reln_ctxt_weaken >> simp[] >> disch_then $ irule_at Any >>
    first_x_assum $ irule >> simp[]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    first_x_assum irule >> simp[collapse_env_def]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    first_x_assum irule >> simp[collapse_env_def]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    first_x_assum irule >> simp[collapse_env_def]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    drule $ cj 1 big_dec_to_small_dec >> simp[] >> strip_tac >>
    irule small_decl_diverges_prefix >>
    qspecl_then [`env'`,`Cdmod mn (enva +++ envb) ds :: cs`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> gvs[small_eval_dec_def] >>
    disch_then drule >> simp[] >> disch_then $ irule_at Any >>
    first_x_assum irule >> simp[]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    drule $ cj 1 big_dec_to_small_dec >> simp[] >> strip_tac >>
    irule small_decl_diverges_prefix >>
    qspecl_then [`env'`,`CdlocalL (enva +++ envb) ds gds :: cs`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> gvs[small_eval_dec_def] >>
    disch_then drule >> simp[] >> disch_then $ irule_at Any >>
    first_x_assum irule >> simp[]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    drule $ cj 1 big_dec_to_small_dec >> simp[] >> strip_tac >>
    irule small_decl_diverges_prefix >>
    qspecl_then [`env'`,`CdlocalG lenv (enva +++ genv) ds :: cs`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> gvs[small_eval_dec_def] >>
    disch_then drule >> simp[] >> disch_then $ irule_at Any >>
    first_x_assum irule >> simp[]
    )
QED

Theorem small_big_dec_equiv:
  ∀env (st:'ffi state) d r.
    evaluate_dec F env st d r = small_eval_dec env (st, Decl d, []) r
Proof
  rw[] >> eq_tac >> rw[]
  >- (drule $ cj 1 big_dec_to_small_dec >> simp[]) >>
  Cases_on `∃res. evaluate_dec F env st d res` >> gvs[]
  >- (
    drule small_eval_dec_determ >>
    drule $ cj 1 big_dec_to_small_dec >> simp[] >> strip_tac >>
    disch_then drule >> rw[] >> gvs[]
    ) >>
  drule $ iffLR $ cj 1 untyped_safety_decs_alt >> strip_tac >>
  drule_at Any $ cj 1 dec_diverges_imp_small_decl_diverges >> simp[] >>
  qexistsl_tac [`env`,`[]`] >> simp[collapse_env_def] >>
  simp[small_decl_diverges_def] >>
  PairCases_on `r` >> Cases_on `r1` >> gvs[small_eval_dec_def] >>
  goal_assum drule >> simp[SF decl_step_ss] >>
  Cases_on `e` >> simp[]
QED

Theorem small_big_decs_equiv:
  ∀env (st:'ffi state) d r.
    evaluate_decs F env st ds r = small_eval_decs env st ds r
Proof
  rw[] >> eq_tac >> rw[]
  >- (drule $ cj 2 big_dec_to_small_dec >> simp[]) >>
  Cases_on `∃res. evaluate_decs F env st ds res` >> gvs[]
  >- (
    drule small_eval_decs_determ >>
    drule $ cj 2 big_dec_to_small_dec >> simp[] >> strip_tac >>
    disch_then drule >> rw[] >> gvs[]
    ) >>
  qspecl_then [`ds`,`st`,`env`] assume_tac $ iffRL $ cj 2 untyped_safety_decs >> gvs[] >>
  drule_at Any $ cj 3 $ cj 2 dec_diverges_imp_small_decl_diverges >> simp[] >>
  qexistsl_tac [`env`,`[]`,`empty_dec_env`,`empty_dec_env`,`empty_dec_env`] >>
  simp[collapse_env_def, small_decl_diverges_def] >>
  PairCases_on `r` >> Cases_on `r1` >> gvs[]
  >- (
    qspecl_then [`env`,`st`,`[]`,`st`,`empty_dec_env`,`ds`,`r0`,`a`]
      mp_tac small_eval_decs_Rval_Dlocal >>
    simp[Once small_eval_decs_cases] >> simp[small_eval_dec_def] >>
    simp[Once RTC_CASES1, decl_step_reln_def, decl_step_def] >>
    simp[Once RTC_CASES1, decl_step_reln_def, decl_step_def, decl_continue_def] >>
    strip_tac >> goal_assum drule >> simp[decl_step_def, decl_continue_def]
    )
  >- (
    qspecl_then [`env`,`st`,`[]`,`ds`,`r0`,`e`]
      mp_tac small_eval_decs_Rerr_Dlocal >>
    ntac 2 $ simp[Once small_eval_decs_cases] >>
    rw[small_eval_dec_def] >>
    gvs[Once RTC_CASES1, decl_step_reln_def, decl_step_def]
    >- (Cases_on `e` >> gvs[]) >>
    gvs[Once RTC_CASES1, decl_step_reln_def, decl_step_def, decl_continue_def]
    >- (Cases_on `e` >> gvs[]) >>
    goal_assum drule >> Cases_on `e` >> gvs[]
    )
QED

Theorem small_big_dec_equiv_diverge:
  ∀env (st:'ffi state) d.
    dec_diverges env st d = small_decl_diverges env (st, Decl d, [])
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    irule $ cj 1 dec_diverges_imp_small_decl_diverges >> simp[collapse_env_def]
    ) >>
  CCONTR_TAC >> qpat_x_assum `small_decl_diverges _ _` mp_tac >> simp[] >>
  drule_all $ iffRL $ cj 1 untyped_safety_decs >> strip_tac >> gvs[] >>
  simp[GSYM small_decl_total] >>
  drule $ cj 1 big_dec_to_small_dec >> simp[] >> disch_then $ irule_at Any
QED

Theorem small_big_decs_equiv_diverge:
  ∀env (st:'ffi state) ds.
    decs_diverges env st ds = small_decl_diverges env (st, Decl (Dlocal [] ds), [])
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    drule $ cj 3 $ cj 2 dec_diverges_imp_small_decl_diverges >>
    disch_then $ qspecl_then
      [`env`,`[]`,`empty_dec_env`,`empty_dec_env`,`empty_dec_env`] mp_tac >>
    simp[collapse_env_def] >> rw[small_decl_diverges_def] >>
    pop_assum mp_tac >> simp[Once RTC_CASES1] >>
    rw[] >> gvs[decl_step_reln_def, decl_step_def] >>
    pop_assum mp_tac >> simp[Once RTC_CASES1] >>
    rw[] >> gvs[decl_step_reln_def, decl_step_def, decl_continue_def]
    ) >>
  CCONTR_TAC >> qpat_x_assum `small_decl_diverges _ _` mp_tac >> simp[] >>
  drule_all $ iffRL $ cj 2 untyped_safety_decs >> strip_tac >> gvs[] >>
  simp[GSYM small_decl_total] >>
  drule $ cj 2 big_dec_to_small_dec >> simp[] >>
  PairCases_on `r` >> Cases_on `r1` >> rw[]
  >- (
    irule_at Any small_eval_decs_Rval_Dlocal >>
    simp[Once small_eval_decs_cases] >> goal_assum drule
    )
  >- (
    irule_at Any small_eval_decs_Rerr_Dlocal >>
    ntac 2 $ simp[Once small_eval_decs_cases] >> goal_assum drule
    )
QED


(**********

  Equate IO events for diverging executions.

**********)

Theorem big_exp_to_small_exp_timeout_lemma:
  (∀ck env ^s e r.
     evaluate ck env s e r ⇒ ∀s'. r = (s', Rerr (Rabort Rtimeout_error)) ∧ ck ⇒
     ∃env' fp ev cs.
      RTC e_step_reln (env, to_small_st s, s.fp_state, Exp e, [])
        (env', to_small_st s', fp, ev, cs)) ∧
  (∀ck env ^s es r.
     evaluate_list ck env s es r ⇒ ∀s'. r = (s', Rerr (Rabort Rtimeout_error)) ∧ ck ⇒
     ∃left mid right sl vs env' ev cs fp fp'. es = left ++ [mid] ++ right ∧
      small_eval_list env (to_small_st s) s.fp_state left (sl, fp', Rval vs) ∧
      RTC e_step_reln (env, sl, fp', Exp mid, [])
        (env', to_small_st s', fp, ev, cs)) ∧
  (∀ck env (s:'ffi state) v pes err_v r.
     evaluate_match ck env s v pes err_v r ⇒
     ∀s'. r = (s', Rerr (Rabort Rtimeout_error)) ∧ ck ⇒
     ∃ fp. e_step_to_match env (to_small_st s) s.fp_state v pes (to_small_st s') fp)
Proof
  ho_match_mp_tac evaluate_strongind >> rw[]
  >- ( (* Raise *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    drule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* Handle - match *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    last_x_assum assume_tac >> dxrule big_clocked_to_unclocked >> rw[] >>
    dxrule $ cj 1 big_exp_to_small_exp >> rw[to_small_res_def, small_eval_def] >>
    dxrule e_step_add_ctxt >> simp[] >>
    disch_then $ qspec_then `[Chandle () pes,env]` assume_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def] >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, Once to_small_st_def] >>
    qexists_tac ‘fp’ >>
    dxrule e_step_to_match_Cmat >> disch_then $ irule_at Any
    )
  >- ( (* Handle - expression timeout *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    drule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* Con *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    Cases_on `left` >> gvs[]
    >- (gvs[Once small_eval_list_cases] >> drule e_step_add_ctxt >> simp[SF SFY_ss]) >>
    dxrule e_step_to_Con >>
    disch_then $ qspecl_then [`mid`,`right`,`cn`,`[]`] mp_tac >> simp[] >>
    `LENGTH (h::(t ++ [mid] ++ right)) = LENGTH (REVERSE es)` by asm_rewrite_tac[] >>
    gvs[ADD1] >> rw[] >> simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* App Opapp - after application *)
    dxrule big_clocked_to_unclocked_list >> rw[] >>
    dxrule $ cj 2 big_exp_to_small_exp >> rw[] >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def, application_thm] >>
    Cases_on `es` using SNOC_CASES >> gvs[REVERSE_SNOC, GSYM getOpClass_opClass]
    >- (
      gvs[Once small_eval_list_cases, to_small_res_def] >>
      last_x_assum $ assume_tac o GSYM >> simp[SF SFY_ss]
      ) >>
    Cases_on ‘op’ >> gs[getOpClass_def] >>
    gvs[to_small_res_def] >> dxrule e_step_over_App_Opapp >>
    disch_then $ qspecl_then [`env'`,`e`,`[]`] assume_tac >> gvs[] >>
    simp[Once RTC_CASES_RTC_TWICE, SF SFY_ss]
    )
  >- ( (* App Opapp - at application *)
    dxrule big_clocked_to_unclocked_list >> rw[] >>
    dxrule $ cj 2 big_exp_to_small_exp >> rw[] >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def, application_thm] >>
    Cases_on `es` using SNOC_CASES >> gvs[REVERSE_SNOC, GSYM getOpClass_opClass]
    >- (
      gvs[Once small_eval_list_cases, to_small_res_def] >>
      last_x_assum $ assume_tac o GSYM >> simp[] >> irule_at Any $ cj 1 RTC_rules
      ) >>
    Cases_on ‘op’ >> gs[getOpClass_def] >>
    gvs[to_small_res_def] >> dxrule e_step_over_App_Opapp >>
    disch_then $ qspecl_then [`env'`,`e`,`[]`] assume_tac >> gvs[SF SFY_ss]
    )
  >- ( (* App - do_app timeout *)
    drule do_app_not_timeout >> simp[]
    )
  >- ( (* App - Icing *)
    gs[GSYM getOpClass_opClass, compress_if_bool_def]
    >> Cases_on ‘isFpBool op’ >> Cases_on ‘vFp’ >> gs[]
    >- (every_case_tac >> gs[])
    >> rveq >> imp_res_tac do_app_not_timeout >> gs[])
  >- ( (* App - Icing 2 *)
    gs[GSYM getOpClass_opClass, compress_if_bool_def]
    >> Cases_on ‘isFpBool op’ >> Cases_on ‘vFp’ >> gs[]
    >- (every_case_tac >> gs[])
    >> rveq >> imp_res_tac do_app_not_timeout >> gs[])
  >- ( (* App - Icing 3 *)
    gs[GSYM getOpClass_opClass, compress_if_bool_def]
    >> Cases_on ‘isFpBool op’ >> Cases_on ‘rOpt’ >> gs[]
    >- (every_case_tac >> gs[])
    >> rveq >> gs[do_fprw_def] >> every_case_tac >> gs[])
  >- ( (* App - Reals *)
    drule do_app_not_timeout >> simp[]
     )
  >- ( (* App - before application *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def, application_thm] >>
    Cases_on `left` >> simp[]
    >- (gvs[Once small_eval_list_cases] >> dxrule e_step_add_ctxt >> simp[SF SFY_ss]) >>
    dxrule e_step_to_App_mid >>
    disch_then $ qspecl_then [`mid`,`right`,`op`,`[]`] assume_tac >> gvs[] >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* Log - after do_log *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    rev_dxrule big_clocked_to_unclocked >> rw[] >>
    dxrule $ cj 1 big_exp_to_small_exp >> rw[to_small_res_def, small_eval_def] >>
    dxrule e_step_add_ctxt >> simp[] >>
    disch_then $ qspec_then `[Clog op () e2,env]` assume_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, SF SFY_ss]
    )
  >- ( (* Log - before do_log *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* If - after do_if *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    rev_dxrule big_clocked_to_unclocked >> rw[] >>
    dxrule $ cj 1 big_exp_to_small_exp >> rw[to_small_res_def, small_eval_def] >>
    dxrule e_step_add_ctxt >> simp[] >>
    disch_then $ qspec_then `[Cif () e2 e3,env]` assume_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, SF SFY_ss]
    )
  >- ( (* If - before do_if *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* Mat - after match *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    rev_dxrule big_clocked_to_unclocked >> rw[] >>
    dxrule $ cj 1 big_exp_to_small_exp >> rw[to_small_res_def, small_eval_def] >>
    dxrule e_step_add_ctxt >> simp[] >>
    disch_then $ qspec_then `[Cmat_check () pes bind_exn_v,env]` assume_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, Once to_small_st_def] >>
    pop_assum mp_tac >> ntac 2 $ pop_assum kall_tac >>
    Induct_on `e_step_to_match` >> rw[] >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, SF SFY_ss]
    )
  >- ( (* Mat - before match *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* Let - after binding *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    rev_dxrule big_clocked_to_unclocked >> rw[] >>
    dxrule $ cj 1 big_exp_to_small_exp >> rw[to_small_res_def, small_eval_def] >>
    dxrule e_step_add_ctxt >> simp[] >>
    disch_then $ qspec_then `[Clet n () e',env]` assume_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, SF SFY_ss]
    )
  >- ( (* Let - before binding *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def] >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* Letrec - after binding *)
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, push_def, SF SFY_ss]
    )
  >- ( (* Tannot *)
    irule_at Any $ cj 2 RTC_rules >> simp[e_step_reln_def, e_step_def, push_def] >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* Lannot *)
    irule_at Any $ cj 2 RTC_rules >> simp[e_step_reln_def, e_step_def, push_def] >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss]
    )
  >- ( (* FpOptimise *)
    irule_at Any $ cj 2 RTC_rules >> simp[e_step_reln_def, e_step_def, push_def] >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss] >>
    disch_then $ qspec_then `[Coptimise Strict sc (),env]` assume_tac >>
    ‘to_small_st (s2 with fp_state := s2.fp_state with canOpt := Strict) = to_small_st s2’ by
      gs[to_small_st_def, state_component_equality, fpState_component_equality] >>
    gs[] >> goal_assum dxrule
  )
  >- ( (* FpOptimise 2 *)
    irule_at Any $ cj 2 RTC_rules >> simp[e_step_reln_def, e_step_def, push_def] >>
    dxrule e_step_add_ctxt >> simp[SF SFY_ss] >>
    disch_then $ qspec_then `[Coptimise s.fp_state.canOpt sc (),env]` assume_tac >>
    ‘∀ fps. to_small_st (s with fp_state := fps) = to_small_st s’ by
      gs[to_small_st_def, state_component_equality] >>
    gs[] >>
    ‘to_small_st (s2 with fp_state := s2.fp_state with canOpt := s.fp_state.canOpt) = to_small_st s2’ by
      gs[to_small_st_def, state_component_equality] >>
    gs[] >> qexists_tac ‘fp’ >> goal_assum dxrule
  )
  >- ( (* list - base case *)
    qexists_tac `[]` >> simp[Once small_eval_list_cases, SF SFY_ss]
    )
  >- ( (* list *)
    qexists_tac `e::left` >> simp[Once small_eval_list_cases, PULL_EXISTS] >>
    rpt $ goal_assum $ drule_at Any >>
    dxrule big_clocked_to_unclocked >> rw[] >>
    dxrule $ cj 1 big_exp_to_small_exp >> rw[to_small_res_def, small_eval_def] >>
    simp[SF SFY_ss]
    )
  >- ( (* match - base case *)
    simp[Once e_step_to_match_cases] >> qexists_tac ‘fp’ >> disj1_tac >>
    simp[Once to_small_st_def, SF SFY_ss]
    )
  >- ( (* match *)
    simp[Once e_step_to_match_cases] >> qexists_tac ‘fp’ >>  disj2_tac >>
    simp[Once to_small_st_def, SF SFY_ss]
    )
QED

Theorem big_exp_to_small_exp_timeout:
  ∀env ^s e s'.
    evaluate T env s e (s', Rerr (Rabort Rtimeout_error)) ⇒
    ∃env' fp ev cs.
      RTC e_step_reln (env, to_small_st s, s.fp_state, Exp e, []) (env', to_small_st s', fp, ev, cs)
Proof
  rw[big_exp_to_small_exp_timeout_lemma]
QED

Theorem big_dec_to_small_dec_timeout_lemma:
  (∀ck env ^s d r.
     evaluate_dec ck env s d r ⇒ ∀s'. r = (s', Rerr (Rabort Rtimeout_error)) ∧ ck ⇒
     ∃dev dcs fp.
      RTC (decl_step_reln env)
        (s with clock := s'.clock, Decl d, []) (s' with fp_state := fp, dev, dcs)) ∧
  (∀ck env ^s ds r.
     evaluate_decs ck env s ds r ⇒ ∀s'. r = (s', Rerr (Rabort Rtimeout_error)) ∧ ck ⇒
     ∃left mid right sl envl dev dcs fp fp'. ds = left ++ [mid] ++ right ∧
      small_eval_decs env
        (s with clock := s'.clock) left (sl with <| clock := s'.clock; fp_state := fp'|>, Rval envl) ∧
      RTC (decl_step_reln (envl +++ env))
        (sl with <| clock := s'.clock; fp_state := fp'|>, Decl mid, []) (s' with fp_state := fp, dev, dcs))
Proof
  ho_match_mp_tac evaluate_dec_strongind >> rw[]
  >- ( (* Dlet *)
    drule big_exp_to_small_exp_timeout >> rw[] >>
    dxrule e_step_reln_decl_step_reln >>
    disch_then $ qspecl_then [`env`,`s with clock := s'.clock`,`locs`,`p`,`[]`] mp_tac >>
    gvs[to_small_st_def] >>
    `s with <| clock := s'.clock; refs := s.refs; ffi := s.ffi |> =
     s with clock := s'.clock ` by gvs[state_component_equality] >>
    qsuff_tac `s with <| clock := s'.clock; refs := s'.refs; ffi := s'.ffi; fp_state := fp |> = s' with fp_state := fp` >>
    rw[]
    >- (
      irule_at Any $ cj 2 RTC_RULES >>
      simp[decl_step_reln_def, decl_step_def, collapse_env_def, SF SFY_ss]
      )
    >- (
      gvs[state_component_equality] >>
      drule $ cj 1 evaluate_no_new_types_exns >> simp[]
      )
    )
  >- ( (* Dmod *)
    irule_at Any $ cj 2 RTC_RULES >> simp[decl_step_reln_def, decl_step_def] >>
    dxrule decl_step_to_Dmod >>
    disch_then $ qspecl_then
      [`mid`,`right`,`empty_dec_env`,`empty_dec_env`,`env`,`mn`] mp_tac >> rw[] >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    qspecl_then [`env`,`[Cdmod mn envl right]`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> disch_then dxrule >>
    strip_tac >> qexists_tac ‘fp’ >>
    gs[SF SFY_ss]
    )
  >- (
    rev_dxrule $ cj 2 evaluate_decs_clocked_to_unclocked >> simp[] >>
    disch_then $ qspec_then `s''.clock` assume_tac >> gvs[with_same_clock] >>
    dxrule $ cj 2 big_dec_to_small_dec >> simp[] >> strip_tac >>
    dxrule small_eval_decs_Rval_Dlocal_lemma_1 >>
    disch_then $ qspecl_then
      [`empty_dec_env`,`empty_dec_env`,`env`,`left ++ [mid] ++ right`] mp_tac >>
    rw[] >>
    irule_at Any $ cj 2 RTC_RULES >> simp[decl_step_reln_def, decl_step_def] >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    drule decl_step_to_Dlocal_global >>
    disch_then $ qspecl_then
      [`mid`,`right`,`empty_dec_env`,`empty_dec_env`,`new_env`,`env`] mp_tac >>
    rw[] >> simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    qspecl_then [`env`,`[CdlocalG new_env envl right]`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> disch_then dxrule >>
    strip_tac >> qexists_tac ‘fp’ >>
    gs[SF SFY_ss]
    )
  >- (
    irule_at Any $ cj 2 RTC_RULES >> simp[decl_step_reln_def, decl_step_def] >>
    drule decl_step_to_Dlocal_local >>
    disch_then $ qspecl_then
      [`mid`,`right`,`empty_dec_env`,`empty_dec_env`,`env`,`ds'`] mp_tac >>
    rw[] >> simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
    qspecl_then [`env`,`[CdlocalL envl right ds']`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> disch_then dxrule >>
    strip_tac >> qexists_tac ‘fp’ >>
    gs[SF SFY_ss]
    )
  >- (
    qexists_tac `[]` >> simp[Once small_eval_decs_cases] >>
    qexists_tac ‘s’ >> qexists_tac ‘dev’ >> qexists_tac ‘dcs’ >>
    qexists_tac ‘fp’ >> qexists_tac ‘s.fp_state’ >>
    simp[SF SFY_ss]
    )
  >- (
    Cases_on `r` >> gvs[combine_dec_result_def] >>
    qexists_tac `d::left` >> simp[] >>
    simp[Once small_eval_decs_cases, SF DNF_ss, GSYM CONJ_ASSOC] >>
    rpt $ goal_assum $ dxrule_at Any >>
    simp[combine_dec_result_def, extend_dec_env_def] >>
    rev_dxrule $ cj 1 evaluate_decs_clocked_to_unclocked >> simp[] >>
    disch_then $ qspec_then `s3.clock` assume_tac >>
    dxrule $ cj 1 big_dec_to_small_dec >> simp[]
    )
QED

Theorem big_dec_to_small_dec_timeout:
  ∀env ^s d s'.
    evaluate_dec T env s d (s', Rerr (Rabort Rtimeout_error)) ⇒
    ∃dev dcs fp.
      RTC (decl_step_reln env)
        (s with clock := s'.clock, Decl d, []) (s' with fp_state := fp, dev, dcs)
Proof
  rw[big_dec_to_small_dec_timeout_lemma]
QED

Theorem big_decs_to_small_decs_timeout:
  ∀env ^s ds s'.
    evaluate_decs T env s ds (s', Rerr (Rabort Rtimeout_error)) ⇒
    ∃dev dcs fp.
      RTC (decl_step_reln env)
        (s with clock := s'.clock, Decl (Dlocal [] ds), []) (s' with fp_state := fp, dev, dcs)
Proof
  rw[] >> drule $ cj 2 big_dec_to_small_dec_timeout_lemma >> rw[] >> gvs[] >>
  ntac 2 $ irule_at Any $ cj 2 RTC_RULES >>
  simp[decl_step_reln_def, decl_step_def, decl_continue_def] >>
  simp[Once RTC_CASES_RTC_TWICE] >> irule_at Any decl_step_to_Dlocal_global >>
  goal_assum drule >> simp[] >>
  qspecl_then [`env`,`[CdlocalG empty_dec_env envl right]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[SF SFY_ss]
QED

Triviality combine_dec_result_alt:
  combine_dec_result env (Rval env') = Rval (env' +++ env) ∧
  combine_dec_result env (Rerr e) = Rerr e
Proof
  rw[combine_dec_result_def, extend_dec_env_def]
QED

Triviality evaluate_state_no_ctxt_alt:
  evaluate_state ck (env,s,Exp e,[]) r ⇔
  ∃clk. evaluate ck env (s with clock := clk) e r
Proof
  ntac 2 $ rw[evaluate_state_cases, Once evaluate_ctxts_cases] >>
  PairCases_on `r` >> simp[]
QED

Triviality evaluate_state_val_no_ctxt_alt:
  evaluate_state ck (env,s,Val e,[]) r ⇔
  ∃clk. r = (s with clock := clk, Rval e)
Proof
  ntac 2 $ rw[evaluate_state_cases, Once evaluate_ctxts_cases]
QED

Theorem evaluate_dec_ctxts_Rerr[simp]:
  evaluate_dec_ctxts ck benv s dcs (Rerr err) r ⇔ r = (s, Rerr err)
Proof
  rw[Once evaluate_dec_ctxts_cases] >> eq_tac >> rw[]
QED

Theorem combine_dec_result_simps[simp]:
  combine_dec_result empty_dec_env r = r ∧
  (combine_dec_result env r = Rerr err ⇔ r = Rerr err) ∧
  (Rerr err = combine_dec_result env r ⇔ r = Rerr err) ∧
  (combine_dec_result env (Rerr err) = Rerr err)
Proof
  rw[combine_dec_result_def, empty_dec_env_def] >> CASE_TAC >> simp[] >>
  eq_tac >> rw[]
QED

Theorem one_step_backward_dec:
  decl_step benv (st, dev, dcs) = Dstep (st', dev', dcs') ∧
  evaluate_dec_state ck benv (st', dev', dcs') res
  ⇒ evaluate_dec_state ck benv (st, dev, dcs) res
Proof
  rw[decl_step_def] >> Cases_on `dev` >> gvs[]
  >- (
    Cases_on `d` >> gvs[]
    >~ [`Dlet`]
    >- (
      every_case_tac >> gvs[] >> last_x_assum mp_tac >>
      once_rewrite_tac[evaluate_dec_state_cases] >> rw[] >> gvs[] >>
      simp[Once evaluate_dec_cases, SF DNF_ss] >>
      gvs[evaluate_state_no_ctxt_alt] >> metis_tac[]
      )
    >~ [`Dmod`]
    >- (
      gvs[evaluate_dec_state_cases] >>
      gvs[Once evaluate_dec_ctxts_cases, evaluate_dec_ctxt_cases] >>
      simp[Once evaluate_dec_cases, SF DNF_ss] >>
      Cases_on `r'` >>
      gvs[combine_dec_result_alt, lift_dec_result_def, lift_dec_env_def, SF SFY_ss]
      )
    >~ [`Dlocal`]
    >- (
      every_case_tac >> gvs[] >> gvs[evaluate_dec_state_cases] >>
      gvs[Once evaluate_dec_ctxts_cases, evaluate_dec_ctxt_cases] >>
      simp[Once evaluate_dec_cases, SF DNF_ss, SF SFY_ss]
      ) >>
    every_case_tac >> gvs[] >> gvs[evaluate_dec_state_cases, empty_dec_env_def] >>
    simp[Once evaluate_dec_cases, SF DNF_ss, SF SFY_ss]
    )
  >- (
    Cases_on `e` >> gvs[]
    >- (
      every_case_tac >> gvs[] >> gvs[evaluate_dec_state_cases] >>
      imp_res_tac one_step_backward >>
      qsuff_tac `st with <| refs := st.refs; ffi := st.ffi |> = st` >>
      rw[] >> gvs[state_component_equality, SF SFY_ss]
      )
    >- (
      Cases_on `l = []` >> gvs[AllCaseEqs()]
      >- (
        gvs[evaluate_dec_state_cases] >>
        simp[evaluate_state_val_no_ctxt_alt, PULL_EXISTS, SF SFY_ss]
        ) >>
      gvs[evaluate_dec_state_cases] >> imp_res_tac one_step_backward >>
      qsuff_tac `st with <| refs := st.refs; ffi := st.ffi |> = st` >>
      rw[] >> gvs[state_component_equality, SF SFY_ss]
      )
    >- (
      gvs[AllCaseEqs()] >>
      gvs[evaluate_dec_state_cases] >> imp_res_tac one_step_backward >>
      qsuff_tac `st with <| refs := st.refs; ffi := st.ffi |> = st` >>
      rw[] >> gvs[state_component_equality, SF SFY_ss]
      )
    )
  >- (
    gvs[decl_continue_def] >> Cases_on `dcs` >> gvs[] >>
    Cases_on `h` >> gvs[] >> Cases_on `l` >> gvs[evaluate_dec_state_cases] >>
    simp[Once evaluate_dec_ctxts_cases, evaluate_dec_ctxt_cases, SF DNF_ss] >>
    gvs[collapse_env_def]
    >- (
      simp[Once evaluate_dec_cases] >>
      gvs[combine_dec_result_def, lift_dec_result_def, SF SFY_ss]
      )
    >- (
      simp[Once evaluate_dec_cases, SF DNF_ss] >>
      simp[combine_dec_result_alt, lift_dec_result_def] >>
      reverse $ Cases_on `r` >> gvs[] >- metis_tac[] >>
      disj2_tac >> goal_assum drule >>
      gvs[Once evaluate_dec_ctxts_cases, evaluate_dec_ctxt_cases] >>
      goal_assum drule >>
      Cases_on `r'` >> gvs[combine_dec_result_alt, lift_dec_result_def]
      )
    >- (
      ntac 2 $ simp[Once evaluate_dec_cases] >>
      gvs[Once evaluate_dec_ctxts_cases, evaluate_dec_ctxt_cases] >>
      gvs[extend_dec_env_def, SF SFY_ss]
      )
    >- (
      simp[Once evaluate_dec_cases, SF DNF_ss, GSYM DISJ_ASSOC] >>
      Cases_on `r` >> gvs[SF SFY_ss] >> disj2_tac >>
      gvs[Once evaluate_dec_ctxts_cases, evaluate_dec_ctxt_cases, SF SFY_ss] >>
      disj2_tac >> simp[Once evaluate_dec_cases, SF DNF_ss, GSYM CONJ_ASSOC] >>
      rpt $ goal_assum $ drule_at Any >> simp[combine_dec_result_alt]
      )
    >- (
      simp[Once evaluate_dec_cases, combine_dec_result_alt] >>
      gvs[extend_dec_env_def, SF SFY_ss]
      )
    >- (
      simp[Once evaluate_dec_cases, SF DNF_ss] >>
      Cases_on `r` >> gvs[SF SFY_ss] >> disj2_tac >>
      gvs[Once evaluate_dec_ctxts_cases, evaluate_dec_ctxt_cases] >>
      rpt $ goal_assum drule >> Cases_on `r'` >> gvs[combine_dec_result_alt]
      )
    )
QED

Theorem small_dec_to_big_dec:
  ∀env st dev dcs st' dev' dcs' ck.
    RTC (decl_step_reln env) (st,dev,dcs) (st',dev',dcs') ⇒
    evaluate_dec_state ck env (st',dev',dcs') r
    ⇒ evaluate_dec_state ck env (st,dev,dcs) r
Proof
  gen_tac >> Induct_on `RTC` >> rw[decl_step_reln_def] >> simp[] >>
  metis_tac[one_step_backward_dec, PAIR]
QED

Theorem evaluate_dec_state_no_ctxt:
  evaluate_dec_state ck env (st, Decl d, []) r ⇔
  ∃clk. evaluate_dec ck env (st with clock := clk) d r
Proof
  rw[evaluate_dec_state_cases] >>
  rw[Once evaluate_dec_ctxts_cases, SF DNF_ss] >>
  eq_tac >> rw[] >> gvs[collapse_env_def, SF SFY_ss] >>
  PairCases_on `r` >> gvs[SF SFY_ss]
QED

Theorem evaluate_match_T_total:
  ∀pes env s v err. ∃r. evaluate_match T env s v pes err r
Proof
  Induct >> rw[Once evaluate_cases, SF DNF_ss] >> PairCases_on `h` >> gvs[] >>
  Cases_on `ALL_DISTINCT (pat_bindings h0 [])` >> gvs[] >>
  Cases_on `pmatch env.c s.refs h0 v []` >> gvs[] >>
  metis_tac[big_clocked_total]
QED

Theorem evaluate_ctxt_T_total:
  ∀env s c v. ∃r.  evaluate_ctxt T env s c v r
Proof
  rw[] >> simp[Once evaluate_ctxt_cases] >> Cases_on `c` >> gvs[SF DNF_ss]
  >- (
    qspecl_then [`l0`,`env`,`s`] assume_tac big_clocked_list_total >> gvs[] >>
    PairCases_on `r` >> Cases_on `r1` >> gvs[SF SFY_ss] >>
    rename1 ‘opClass op FunApp’ >> Cases_on ‘opClass op FunApp’ >>
    gvs[getOpClass_opClass]
    >- (
      Cases_on `do_opapp (REVERSE a ++ [v] ++ l)` >> gvs[SF SFY_ss] >>
      PairCases_on `x` >> Cases_on `r0.clock = 0` >> gvs[SF SFY_ss] >>
      metis_tac[big_clocked_total]
      ) >>
    Cases_on ‘opClass op Simple’ >> gvs[]
    >- (
      ‘~ opClass op Reals ∧ ~ opClass op Icing’ by (Cases_on ‘op’ >> gs[opClass_cases]) >>
      Cases_on `do_app (r0.refs,r0.ffi) op (REVERSE a ++ [v] ++ l)` >> gvs[SF SFY_ss] >>
      PairCases_on `x` >> gvs[SF SFY_ss]) >>
    Cases_on ‘opClass op Icing’ >> gvs[]
    >- (
      ‘~ opClass op Reals’ by (Cases_on ‘op’ >> gs[opClass_cases]) >>
      Cases_on `do_app (r0.refs,r0.ffi) op (REVERSE a ++ [v] ++ l)` >> gvs[SF SFY_ss] >>
      PairCases_on `x` >> gvs[SF SFY_ss] >>
      reverse $ Cases_on ‘r0.fp_state.canOpt = FPScope Opt’ >> gvs[SF SFY_ss] >>
      Cases_on ‘do_fprw x2 (r0.fp_state.opts 0) (r0.fp_state.rws)’ >> gvs[SF SFY_ss]) >>
    Cases_on ‘opClass op Reals’ >> gvs[]
    >- (
      Cases_on ‘r0.fp_state.real_sem’ >> gvs[SF SFY_ss] >>
      Cases_on `do_app (r0.refs,r0.ffi) op (REVERSE a ++ [v] ++ l)` >> gvs[SF SFY_ss] >>
      PairCases_on `x` >> gvs[SF SFY_ss]) >>
    Cases_on ‘op’ >> gs[opClass_cases, do_app_def] >> disj1_tac >>
    first_x_assum $ irule_at Any >> every_case_tac >> gvs[SF SFY_ss]
  )
  >- (
    Cases_on `do_log l v e` >> gvs[] >> Cases_on `x` >> gvs[] >>
    metis_tac[big_clocked_total]
    )
  >- (Cases_on `do_if v e e0` >> gvs[] >> metis_tac[big_clocked_total])
  >- (
    Cases_on `can_pmatch_all env.c s.refs (MAP FST l) v` >> gvs[] >>
    metis_tac[evaluate_match_T_total]
    )
  >- metis_tac[evaluate_match_T_total]
  >- metis_tac[big_clocked_total]
  >- (
    Cases_on `do_con_check env.c o' (LENGTH l0 + (LENGTH l + 1))` >> gvs[] >>
    qspecl_then [`l0`,`env`,`s`] assume_tac big_clocked_list_total >> gvs[] >>
    PairCases_on `r` >> Cases_on `r1` >> gvs[SF SFY_ss] >>
    metis_tac[do_con_check_build_conv]
    )
QED

Theorem evaluate_ctxts_T_total:
  ∀cs s res. ∃r.  evaluate_ctxts T s cs res r
Proof
  Induct >> rw[] >> simp[Once evaluate_ctxts_cases] >> gvs[SF DNF_ss] >>
  PairCases_on `h` >> simp[] >> Cases_on `res` >> rw[]
  >- metis_tac[evaluate_ctxt_T_total, PAIR] >>
  Cases_on `∃pes. h0 = Chandle () pes` >> gvs[]
  >- (Cases_on `e` >> gvs[] >>
      Cases_on `can_pmatch_all h1.c s.refs (MAP FST pes) a` >> gvs[] >>
      metis_tac[evaluate_match_T_total, PAIR]) >>
  Cases_on ‘∃ oldSc sc. h0 = Coptimise oldSc sc ()’ >> gvs[]
QED

Theorem evaluate_state_T_total:
  ∀env s ev cs. ∃r. evaluate_state T (env,s,ev,cs) r
Proof
  rw[] >> simp[Once evaluate_state_cases] >>
  Cases_on `ev` >> gvs[] >>
  metis_tac[evaluate_ctxts_T_total, big_clocked_total, PAIR]
QED

Theorem evaluate_dec_ctxt_T_total:
  ∀env st dc env'. ∃r. evaluate_dec_ctxt T env st dc env' r
Proof
  rw[] >> simp[evaluate_dec_ctxt_cases, SF DNF_ss] >>
  Cases_on `dc` >> gvs[] >>
  metis_tac[big_clocked_decs_total, PAIR, result_nchotomy]
QED

Theorem evaluate_dec_ctxts_T_total:
  ∀dcs env st res. ∃r. evaluate_dec_ctxts T env st dcs res r
Proof
  Induct >> rw[Once evaluate_dec_ctxts_cases, SF DNF_ss] >>
  Cases_on `res` >> gvs[] >>
  qspecl_then [`collapse_env env dcs`,`st`,`h`,`a`]
    assume_tac evaluate_dec_ctxt_T_total >>
  metis_tac[PAIR]
QED

Theorem evaluate_dec_state_T_total:
  ∀env s. ∃r. evaluate_dec_state T env s r
Proof
  rw[evaluate_dec_state_cases, SF DNF_ss] >>
  PairCases_on `s` >> gvs[] >> Cases_on `s1` >> gvs[]
  >- (
    qspecl_then [`collapse_env env s2`,`s0`,`d`] assume_tac big_clocked_dec_total >>
    metis_tac[with_same_clock, evaluate_dec_ctxts_T_total, PAIR]
    )
  >- (
    qspecl_then [`s`,`s0`,`e`,`l`] assume_tac evaluate_state_T_total >>
    gvs[] >> PairCases_on `r` >>
    Cases_on `r1` >> gvs[SF SFY_ss] >> disj2_tac >>
    Cases_on `ALL_DISTINCT (pat_bindings p [])` >> gvs[SF SFY_ss] >>
    Cases_on `pmatch (collapse_env env s2).c r0.refs p a []` >> gvs[SF SFY_ss] >>
    metis_tac[evaluate_dec_ctxts_T_total]
    )
  >- metis_tac[evaluate_dec_ctxts_T_total]
QED

Theorem evaluate_ctxt_io_events_mono:
  ∀ck env ^s c v r.
    evaluate_ctxt ck env s c v r ⇒
    io_events_mono s.ffi (FST r).ffi
Proof
  rw[evaluate_ctxt_cases] >> gvs[] >> every_case_tac >> gvs[shift_fp_opts_def] >>
  imp_res_tac big_evaluate_io_events_mono >> gvs[] >>
  imp_res_tac do_app_io_events_mono >>
  metis_tac[io_events_mono_trans]
QED

Theorem evaluate_ctxts_io_events_mono:
  ∀ck ^s cs v r.
    evaluate_ctxts ck s cs v r ⇒
    io_events_mono (s.ffi) (FST r).ffi
Proof
  gen_tac >> ho_match_mp_tac evaluate_ctxts_ind >> rw[] >>
  imp_res_tac big_evaluate_io_events_mono >>
  imp_res_tac evaluate_ctxt_io_events_mono >> gvs[] >>
  metis_tac[io_events_mono_trans]
QED

Theorem evaluate_state_io_events_mono:
  ∀ck env st ev cs r.
    evaluate_state ck (env, st, ev, cs) r ⇒
    io_events_mono (st.ffi) (FST r).ffi
Proof
  rw[evaluate_state_cases] >> gvs[] >>
  imp_res_tac big_evaluate_io_events_mono >>
  imp_res_tac evaluate_ctxts_io_events_mono >> gvs[] >>
  metis_tac[io_events_mono_trans]
QED

Theorem evaluate_dec_ctxt_io_events_mono:
  ∀ck env ^s c v r.
    evaluate_dec_ctxt ck env s c v r ⇒
    io_events_mono s.ffi (FST r).ffi
Proof
  rw[evaluate_dec_ctxt_cases] >> gvs[] >>
  imp_res_tac evaluate_dec_io_events_mono >> gvs[] >>
  metis_tac[io_events_mono_trans]
QED

Theorem evaluate_dec_ctxts_io_events_mono:
  ∀ck env ^s cs v r.
    evaluate_dec_ctxts ck env s cs v r ⇒
    io_events_mono s.ffi (FST r).ffi
Proof
  ntac 2 gen_tac >> Induct_on `evaluate_dec_ctxts` >> rw[] >>
  imp_res_tac evaluate_dec_ctxt_io_events_mono >> gvs[] >>
  metis_tac[io_events_mono_trans]
QED

Theorem evaluate_dec_state_io_events_mono:
  ∀ck env s r.
    evaluate_dec_state ck env s r ⇒
    io_events_mono (FST s).ffi (FST r).ffi
Proof
  rw[evaluate_dec_state_cases] >>
  map_every imp_res_tac [
    evaluate_state_io_events_mono,
    evaluate_dec_io_events_mono,
    evaluate_dec_ctxts_io_events_mono] >> gvs[] >>
  metis_tac[io_events_mono_trans]
QED

Theorem lprefix_chain_evaluate_decs:
  st.eval_state = NONE ⇒
  lprefix_chain
    { fromList s.ffi.io_events |
        ∃k r. evaluate_decs T env (st with clock := k) prog (^s,r) }
Proof
  rw[lprefix_chain_def] >> simp[LPREFIX_fromList, from_toList] >>
  `(st with clock := k).eval_state = NONE ∧
   (st with clock := k').eval_state = NONE` by gvs[] >>
  dxrule_all $ iffRL functional_evaluate_decs >>
  rev_dxrule_all $ iffRL functional_evaluate_decs >> rw[] >>
  Cases_on `k ≤ k'` >> gvs[]
  >- (
    drule $ INST_TYPE [alpha |-> ``:'ffi``] evaluate_decs_ffi_mono_clock >>
    disch_then $ qspecl_then [`st`,`env`,`prog`] assume_tac >> gvs[io_events_mono_def]
    )
  >- (
    `k' ≤ k` by gvs[] >>
    drule $ INST_TYPE [alpha |-> ``:'ffi``] evaluate_decs_ffi_mono_clock >>
    disch_then $ qspecl_then [`st`,`env`,`prog`] assume_tac >> gvs[io_events_mono_def]
    )
QED

Theorem lprefix_lub_big_small:
  st.eval_state = NONE ∧ decs_diverges env st prog ⇒
  lprefix_lub
    { fromList s.ffi.io_events |
        ∃k r. evaluate_decs T env (st with clock := k) prog (s,r) } =
  lprefix_lub
    { fromList (FST s).ffi.io_events |
        (decl_step_reln env)꙳ (st, Decl (Dlocal [] prog), []) s }
Proof
  rw[FUN_EQ_THM] >> irule lprefix_lub_equiv_chain >>
  irule_at Any IMP_equiv_lprefix_chain >>
  simp[lprefix_chain_evaluate_decs, lprefix_chain_RTC_decl_step_reln] >>
  rw[lprefix_rel_def, PULL_EXISTS, LPREFIX_fromList, from_toList]
  >- (
    gvs[decs_diverges_big_clocked] >>
    `r = Rerr (Rabort Rtimeout_error)` by (
      first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
      drule $ cj 2 decs_determ >> disch_then rev_drule >> simp[]) >>
    gvs[] >> drule big_decs_to_small_decs_timeout >> rw[] >>
    drule RTC_decl_step_reln_ignore_clock >>
    disch_then $ qspec_then `st.clock` mp_tac >> rw[with_same_clock, SF SFY_ss] >>
    goal_assum drule >> simp[]
    )
  >- (
    PairCases_on `s` >> drule small_dec_to_big_dec >>
    qspecl_then [`env`,`(s0,s1,s2)`] assume_tac evaluate_dec_state_T_total >> gvs[] >>
    disch_then drule >> strip_tac >> gvs[evaluate_dec_state_no_ctxt] >>
    ntac 2 $ gvs[Once evaluate_dec_cases] >> gvs[extend_dec_env_def] >>
    PairCases_on `r` >> gvs[] >> goal_assum drule >>
    imp_res_tac evaluate_dec_state_io_events_mono >> gvs[io_events_mono_def]
    )
QED


val _ = export_theory ();

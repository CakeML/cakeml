(**
  Proof of a new overall compiler correctness theorem for
  the global constant lifting, showing that it is semantics preserving
**)
open semanticPrimitivesTheory evaluateTheory
     icing_rewriterTheory icing_optimisationsTheory
     icing_optimisationProofsTheory fpOptTheory fpValTreeTheory
     namespacePropsTheory ml_progTheory
     optPlannerTheory source_to_source2Theory source_to_source2ProofsTheory
     pull_wordsTheory backendProofTheory;

open preamble;

val _ = new_theory "new_backendProof";

(*
Theorem pull_words_correct:
 let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
  semantics_prog s env prog = semantics_prog s env (lift_constants_decl prog)
Proof
  fs[primSemEnvTheory.prim_sem_env_eq, FUN_EQ_THM]
  >> qmatch_goalsub_abbrev_tac ‘semantics_prog init_ffi initEnv’
  >> gen_tac >> Cases_on ‘x’ >> gs[semanticsTheory.semantics_prog_def]
  (* Timeout *)
  >- (
    EQ_TAC >> rpt gen_tac >> disch_then strip_assume_tac
    >> gs[semanticsTheory.evaluate_prog_with_clock_def, PULL_FORALL]
    >> rpt gen_tac >> first_x_assum $ qspec_then ‘k’ strip_assume_tac
    >- (
      Cases_on ‘evaluate_decs (init_ffi with clock := k) initEnv prog’
      >> gs[lift_constants_decl_def, evaluate_decs_app] >> rveq
      >> qmatch_goalsub_abbrev_tac
           ‘evaluate_decs _ initEnv (build_decl_list cst_lst)’
      >> qspecl_then [‘init_ffi with clock := k’, ‘initEnv’, ‘initEnv’, ‘[]’,
                      ‘cst_lst’]
                     mp_tac build_decl_list_lemma
      >> impl_tac
      >- (
        unabbrev_all_tac >> gs[env_rel_def]
        >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
        >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
        >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
      )
      >> rpt $ disch_then strip_assume_tac >> gs[]
      >> qpat_x_assum `evaluate_decs _ _ prog = _` $
           mp_then Any mp_tac replace_constants_decl_thm
      >> disch_then $
           qspecl_then [‘init_ffi with clock := k’,
                        ‘extend_dec_env env2 initEnv’,‘cst_lst’]
           mp_tac
      >> gs[] >> impl_tac
      >- (
        rpt conj_tac
        >- (
          unabbrev_all_tac
          >> qspecl_then [‘gather_constants_decl prog’,
                          ‘gather_used_identifiers_decl prog’, ‘0’]
                         mp_tac build_cnst_list_disjoint_res
          >> metis_tac[IN_DISJOINT,SUBSET_DEF])
        >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
      >> disch_then strip_assume_tac >> gs[]
      >> Cases_on ‘res1’
      >> gs[dec_res_rel_def, combine_dec_result_def, state_rel_def]
      >> Cases_on ‘e’ >> gs[dec_res_rel_def, lprefix_lub_def]
      >> rpt conj_tac >> rpt strip_tac
      >- (
        first_x_assum irule >> qexists_tac ‘k'’
        >> rveq
        >> qspecl_then [‘init_ffi with clock := k'’, ‘initEnv’, ‘initEnv’, ‘[]’,
                        ‘cst_lst’]
                       mp_tac build_decl_list_lemma
        >> impl_tac
        >- (
          unabbrev_all_tac >> gs[env_rel_def]
          >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
          >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
          >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
        )
        >> disch_then strip_assume_tac >> gs[]
        >> Cases_on ‘evaluate_decs (init_ffi with clock := k') initEnv prog’
        >> gs[]
        >> pop_assum $ mp_then Any mp_tac replace_constants_decl_thm
        >> disch_then $
                      qspecl_then [‘init_ffi with clock := k'’,
                                   ‘extend_dec_env env2' initEnv’,‘cst_lst’]
                      mp_tac
        >> gs[] >> impl_tac
        >- (
          rpt conj_tac
          >- (
            unabbrev_all_tac
            >> qspecl_then [‘gather_constants_decl prog’,
                            ‘gather_used_identifiers_decl prog’, ‘0’]
                           mp_tac build_cnst_list_disjoint_res
            >> metis_tac[IN_DISJOINT,SUBSET_DEF])
          >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
        >> rpt strip_tac >> gs[state_rel_def])
      >> last_x_assum $ qspec_then ‘ub’ assume_tac
      >> pop_assum irule
      >> rpt strip_tac >> first_x_assum $ qspec_then ‘ll’ irule >> rveq
      >> qexists_tac ‘k'’ >> gs[]
      >> qspecl_then [‘init_ffi with clock := k'’, ‘initEnv’, ‘initEnv’, ‘[]’,
                      ‘cst_lst’]
                     mp_tac build_decl_list_lemma
      >> impl_tac
      >- (
        unabbrev_all_tac >> gs[env_rel_def]
        >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
        >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
        >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
      )
      >> disch_then strip_assume_tac >> gs[]
      >> Cases_on ‘evaluate_decs (init_ffi with clock := k') initEnv prog’
      >> gs[]
      >> pop_assum $ mp_then Any mp_tac replace_constants_decl_thm
      >> disch_then $
                    qspecl_then [‘init_ffi with clock := k'’,
                                 ‘extend_dec_env env2' initEnv’,‘cst_lst’]
                    mp_tac
      >> gs[] >> impl_tac
      >- (
        rpt conj_tac
        >- (
          unabbrev_all_tac
          >> qspecl_then [‘gather_constants_decl prog’,
                          ‘gather_used_identifiers_decl prog’, ‘0’]
                         mp_tac build_cnst_list_disjoint_res
          >> metis_tac[IN_DISJOINT,SUBSET_DEF])
        >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
      >> rpt strip_tac >> gs[state_rel_def])
    >> Cases_on ‘evaluate_decs (init_ffi with clock := k) initEnv prog’
    >> qpat_x_assum `(λ (st, r). (st.ffi, r))
                    (evaluate_decs _ _ (lift_constants_decl _)) = _`
         mp_tac
    >> gs[lift_constants_decl_def, evaluate_decs_app] >> rveq
    >> qmatch_goalsub_abbrev_tac ‘evaluate_decs _ initEnv
                                  (build_decl_list cst_lst)’
    >> qspecl_then [‘init_ffi with clock := k’, ‘initEnv’, ‘initEnv’, ‘[]’,
                    ‘cst_lst’]
                   mp_tac build_decl_list_lemma
    >> impl_tac
    >- (
      unabbrev_all_tac >> gs[env_rel_def]
      >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
      >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
      >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
      )
    >> disch_then strip_assume_tac >> gs[]
    >> qpat_x_assum `evaluate_decs _ _ prog = _` $
         mp_then Any mp_tac replace_constants_decl_thm
    >> disch_then $
         qspecl_then [‘init_ffi with clock := k’, ‘extend_dec_env env2 initEnv’,
                      ‘cst_lst’] mp_tac
    >> gs[] >> impl_tac
    >- (
      rpt conj_tac
      >- (
        unabbrev_all_tac
        >> qspecl_then [‘gather_constants_decl prog’,
                        ‘gather_used_identifiers_decl prog’, ‘0’]
                       mp_tac build_cnst_list_disjoint_res
        >> metis_tac[IN_DISJOINT,SUBSET_DEF])
      >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
    >> rpt $ disch_then strip_assume_tac >> gs[] >> rveq
    >> Cases_on ‘r’ >> Cases_on ‘res1’
    >> gs[dec_res_rel_def, combine_dec_result_def, state_rel_def]
    >> Cases_on ‘e’ >> gs[dec_res_rel_def, lprefix_lub_def]
    >> rpt conj_tac >> rpt strip_tac
    >- (
      first_x_assum irule >> qexists_tac ‘k'’ >> rveq
      >> qspecl_then [‘init_ffi with clock := k'’, ‘initEnv’, ‘initEnv’, ‘[]’,
                      ‘cst_lst’]
                     mp_tac build_decl_list_lemma
      >> impl_tac
      >- (
        unabbrev_all_tac >> gs[env_rel_def]
        >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
        >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
        >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
      )
      >> disch_then strip_assume_tac >> gs[]
      >> Cases_on ‘evaluate_decs (init_ffi with clock := k') initEnv prog’
      >> gs[]
      >> pop_assum $ mp_then Any mp_tac replace_constants_decl_thm
      >> disch_then $
                    qspecl_then [‘init_ffi with clock := k'’,
                                 ‘extend_dec_env env2' initEnv’,‘cst_lst’]
                    mp_tac
      >> gs[] >> impl_tac
      >- (
        rpt conj_tac
        >- (
          unabbrev_all_tac
          >> qspecl_then [‘gather_constants_decl prog’,
                          ‘gather_used_identifiers_decl prog’, ‘0’]
                         mp_tac build_cnst_list_disjoint_res
          >> metis_tac[IN_DISJOINT,SUBSET_DEF])
        >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
      >> rpt strip_tac >> gs[state_rel_def])
    >> last_x_assum $ qspec_then ‘ub’ assume_tac
    >> pop_assum irule
    >> rpt strip_tac >> first_x_assum $ qspec_then ‘ll’ irule >> rveq
    >> qexists_tac ‘k'’ >> gs[]
    >> qspecl_then [‘init_ffi with clock := k'’, ‘initEnv’, ‘initEnv’, ‘[]’,
                    ‘cst_lst’]
                   mp_tac build_decl_list_lemma
    >> impl_tac
    >- (
      unabbrev_all_tac >> gs[env_rel_def]
      >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
      >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
      >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
    )
    >> disch_then strip_assume_tac >> gs[]
    >> Cases_on ‘evaluate_decs (init_ffi with clock := k') initEnv prog’
    >> gs[]
    >> pop_assum $ mp_then Any mp_tac replace_constants_decl_thm
    >> disch_then $
                  qspecl_then [‘init_ffi with clock := k'’,
                               ‘extend_dec_env env2' initEnv’,‘cst_lst’]
                  mp_tac
    >> gs[] >> impl_tac
    >- (
      rpt conj_tac
      >- (
        unabbrev_all_tac
        >> qspecl_then [‘gather_constants_decl prog’,
                        ‘gather_used_identifiers_decl prog’, ‘0’]
                       mp_tac build_cnst_list_disjoint_res
        >> metis_tac[IN_DISJOINT,SUBSET_DEF])
      >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
    >> rpt strip_tac >> gs[state_rel_def])
  (* Termination *)
  >- (
    EQ_TAC >> rpt strip_tac >> gs[semanticsTheory.evaluate_prog_with_clock_def]
    >- (
      Cases_on ‘evaluate_decs (init_ffi with clock := k) initEnv prog’
      >> gs[lift_constants_decl_def, evaluate_decs_app] >> rveq
      >> qmatch_goalsub_abbrev_tac
           ‘evaluate_decs _ initEnv (build_decl_list cst_lst)’
      >> qspecl_then [‘init_ffi with clock := k’, ‘initEnv’, ‘initEnv’, ‘[]’,
                      ‘cst_lst’]
                     mp_tac build_decl_list_lemma
      >> impl_tac
      >- (
        unabbrev_all_tac >> gs[env_rel_def]
        >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
        >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
        >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
      )
      >> rpt strip_tac >> qexists_tac ‘k’ >> gs[]
      >> qpat_x_assum `evaluate_decs _ _ prog = _` $
           mp_then Any mp_tac replace_constants_decl_thm
      >> disch_then $
           qspecl_then [‘init_ffi with clock := k’,
                        ‘extend_dec_env env2 initEnv’,‘cst_lst’]
           mp_tac
      >> gs[] >> impl_tac
      >- (
        rpt conj_tac
        >- (
          unabbrev_all_tac
          >> qspecl_then [‘gather_constants_decl prog’,
                          ‘gather_used_identifiers_decl prog’, ‘0’]
                         mp_tac build_cnst_list_disjoint_res
          >> metis_tac[IN_DISJOINT,SUBSET_DEF])
        >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
      >> rpt strip_tac >> gs[]
      >> Cases_on ‘r’ >> Cases_on ‘res1’
      >> gs[dec_res_rel_def, combine_dec_result_def, state_rel_def]
      >> Cases_on ‘e’ >> Cases_on ‘e'’ >> gs[dec_res_rel_def])
    >> Cases_on ‘evaluate_decs (init_ffi with clock := k) initEnv prog’
    >> qpat_x_assum `(λ (st, r). (st.ffi, r))
                    (evaluate_decs _ _ (lift_constants_decl _)) = _`
         mp_tac
    >> gs[lift_constants_decl_def, evaluate_decs_app] >> rveq
    >> qmatch_goalsub_abbrev_tac ‘evaluate_decs _ initEnv
                                  (build_decl_list cst_lst)’
    >> qspecl_then [‘init_ffi with clock := k’, ‘initEnv’, ‘initEnv’, ‘[]’,
                    ‘cst_lst’]
                   mp_tac build_decl_list_lemma
    >> impl_tac
    >- (
      unabbrev_all_tac >> gs[env_rel_def]
      >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
      >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
      >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
      )
    >> rpt strip_tac >> qexists_tac ‘k’ >> gs[]
    >> qpat_x_assum `evaluate_decs _ _ prog = _` $
         mp_then Any mp_tac replace_constants_decl_thm
    >> disch_then $
         qspecl_then [‘init_ffi with clock := k’, ‘extend_dec_env env2 initEnv’,
                      ‘cst_lst’] mp_tac
    >> gs[] >> impl_tac
    >- (
      rpt conj_tac
      >- (
        unabbrev_all_tac
        >> qspecl_then [‘gather_constants_decl prog’,
                        ‘gather_used_identifiers_decl prog’, ‘0’]
                       mp_tac build_cnst_list_disjoint_res
        >> metis_tac[IN_DISJOINT,SUBSET_DEF])
      >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
    >> rpt strip_tac >> gs[] >> rveq
    >~ [‘dec_res_rel _ _ (Rerr (Rabort Rtype_error)) _ _’]
    >- (
      Cases_on ‘res1’ >> gs[dec_res_rel_def, combine_dec_result_def, state_rel_def]
      >> Cases_on ‘e’ >> gs[dec_res_rel_def])
    >> Cases_on ‘r'’ >> Cases_on ‘res1’ >> gs[dec_res_rel_def, combine_dec_result_def, state_rel_def]
    >> Cases_on ‘e’ >> Cases_on ‘e'’ >> gs[dec_res_rel_def]
  )
  >> EQ_TAC >> rpt strip_tac >> gs[semanticsTheory.evaluate_prog_with_clock_def]
    >- (
      Cases_on ‘evaluate_decs (init_ffi with clock := k) initEnv prog’
      >> gs[lift_constants_decl_def, evaluate_decs_app] >> rveq
      >> qmatch_goalsub_abbrev_tac
           ‘evaluate_decs _ initEnv (build_decl_list cst_lst)’
      >> qspecl_then [‘init_ffi with clock := k’, ‘initEnv’, ‘initEnv’, ‘[]’,
                      ‘cst_lst’]
                     mp_tac build_decl_list_lemma
      >> impl_tac
      >- (
        unabbrev_all_tac >> gs[env_rel_def]
        >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
        >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
        >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
      )
      >> rpt strip_tac >> qexists_tac ‘k’ >> gs[]
      >> qpat_x_assum `evaluate_decs _ _ prog = _` $
           mp_then Any mp_tac replace_constants_decl_thm
      >> disch_then $
           qspecl_then [‘init_ffi with clock := k’,
                        ‘extend_dec_env env2 initEnv’,‘cst_lst’]
           mp_tac
      >> gs[] >> impl_tac
      >- (
        rpt conj_tac
        >- (
          unabbrev_all_tac
          >> qspecl_then [‘gather_constants_decl prog’,
                          ‘gather_used_identifiers_decl prog’, ‘0’]
                         mp_tac build_cnst_list_disjoint_res
          >> metis_tac[IN_DISJOINT,SUBSET_DEF])
        >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
      >> rpt strip_tac >> gs[]
      >> Cases_on ‘res1’
      >> gs[dec_res_rel_def, combine_dec_result_def, state_rel_def]
      >> Cases_on ‘e’ >> gs[dec_res_rel_def])
  >> Cases_on ‘evaluate_decs (init_ffi with clock := k) initEnv prog’
  >> qpat_x_assum `SND ((λ (st, r). (st.ffi, r))
                        (evaluate_decs _ _ (lift_constants_decl _))) = _`
       mp_tac
  >> gs[lift_constants_decl_def, evaluate_decs_app] >> rveq
  >> qmatch_goalsub_abbrev_tac ‘evaluate_decs _ initEnv
                                (build_decl_list cst_lst)’
  >> qspecl_then [‘init_ffi with clock := k’, ‘initEnv’, ‘initEnv’, ‘[]’,
                  ‘cst_lst’]
                 mp_tac build_decl_list_lemma
  >> impl_tac
  >- (
    unabbrev_all_tac >> gs[env_rel_def]
    >> rpt conj_tac >> gs[namespaceTheory.nsLookup_def]
    >- (rpt strip_tac >> drule build_cnst_list_unique >> gs[])
    >> rpt strip_tac >> Cases_on ‘n’ >> gs[namespaceTheory.nsLookup_def]
  )
  >> rpt strip_tac >> qexists_tac ‘k’ >> gs[]
  >> qpat_x_assum `evaluate_decs _ _ prog = _` $
       mp_then Any mp_tac replace_constants_decl_thm
  >> disch_then $
       qspecl_then [‘init_ffi with clock := k’, ‘extend_dec_env env2 initEnv’,
                    ‘cst_lst’] mp_tac
  >> gs[] >> impl_tac
  >- (
    rpt conj_tac
    >- (
      unabbrev_all_tac
      >> qspecl_then [‘gather_constants_decl prog’,
                      ‘gather_used_identifiers_decl prog’, ‘0’]
                     mp_tac build_cnst_list_disjoint_res
      >> metis_tac[IN_DISJOINT,SUBSET_DEF])
    >> unabbrev_all_tac >> gs[state_rel_def, ref_rel_def])
  >> rpt strip_tac >> gs[] >> rveq
  >> Cases_on ‘r’ >> Cases_on ‘res1’ >> gs[dec_res_rel_def, combine_dec_result_def, state_rel_def]
  >> Cases_on ‘e’ >> gs[dec_res_rel_def]
QED

Theorem pull_words_correct_simp =
  SIMP_RULE std_ss [primSemEnvTheory.prim_sem_env_eq,
                    GSYM ml_progTheory.init_state_def,
                    GSYM ml_progTheory.init_env_def] pull_words_correct
  |> CONV_RULE pairLib.let_CONV;
*)

val _ = export_theory();

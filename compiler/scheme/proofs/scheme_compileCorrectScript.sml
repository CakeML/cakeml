(*
  Top-level semantic preservation proof for Scheme
*)
Theory scheme_compileCorrect
Ancestors
  scheme_ast scheme_semantics scheme_to_cake
  scheme_to_cakeProof primSemEnv primTypes
  ffi semantics evaluate evaluateProps
  semanticPrimitives scheme_to_cake_env
  evaluate_dec ml_prog ast namespace
  scheme_semanticsProps
Libs
  preamble

(* avoid wasting time printing *)
val _  = (max_print_depth := 30);

Theorem scheme_init_evaluate_dec:
  ! ffi . ∃ ck1 ck2.
    evaluate_decs (init_state ffi with clock := ck1) init_env
      scheme_init =
    (scheme_to_cake_env_st_1 ffi with clock := ck2,
     Rval scheme_to_cake_env_env_13)
Proof
  `IS_SOME (check_cons_dec_list init_env.c scheme_init)`
    by (EVAL_TAC >> simp[init_env_def] >> EVAL_TAC)
  >> simp[GSYM evaluate_dec_list_eq_evaluate_decs]
  >> simp[evaluate_decs_scheme_init_thm]
QED

Definition v_to_string_def:
  v_to_string (SBool F) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "#f") [] /\
  v_to_string (SBool T) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "#t") [] /\
  v_to_string _ = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "other") []
End

Theorem every_one_con_check:
  (! prog k .
    every_exp
      (one_con_check scheme_cons_env)
      (cps_transform prog k)) /\
  (! tfn ts es k .
    every_exp (one_con_check scheme_cons_env) tfn /\
    EVERY (every_exp (one_con_check scheme_cons_env)) ts
    ==>
    every_exp
      (one_con_check scheme_cons_env)
      (cps_transform_app tfn ts es k)) /\
  (! xts bs e k .
    EVERY (every_exp (one_con_check scheme_cons_env)) (MAP SND xts)
    ==>
    every_exp
      (one_con_check scheme_cons_env)
      (cps_transform_letinit xts bs e k)) /\
  (! k es e .
    every_exp
      (one_con_check scheme_cons_env)
      (cps_transform_seq k es e))
Proof
  simp [scheme_cons_env_simp]
  >> ho_match_mp_tac cps_transform_ind
  >> rpt strip_tac
  >> simp[cps_transform_def]
  >- (
    Cases_on `v`
    >> simp[lit_to_ml_val_def, do_con_check_def, nsLookup_def]
    >- (
      Cases_on `p`
      >> simp[do_con_check_def, nsLookup_def]
    )
    >> Cases_on `b`
    >> simp[do_con_check_def, nsLookup_def]
  )
  >> simp[refunc_set_def, do_con_check_def, nsLookup_def]
  >- (
    Induct_on `xs` >- (
      Cases_on `xp`
      >> simp[proc_ml_def, do_con_check_def, nsLookup_def]
    )
    >> simp[proc_ml_def, do_con_check_def, nsLookup_def]
  )
  >- (
    rename1 `letpreinit_ml _ exp`
    >> Induct_on `bs`
    >> simp[letpreinit_ml_def, do_con_check_def, nsLookup_def]
  )
  >- (
    gvs[cps_transform_def]
    >> rename1 `letpreinit_ml _ exp`
    >> Induct_on `bs`
    >> simp[letpreinit_ml_def, do_con_check_def, nsLookup_def]
  )
  >-(
    Induct_on `ts` using SNOC_INDUCT
    >> simp[cons_list_def, do_con_check_def, nsLookup_def, REVERSE_SNOC]
  )
  >> Induct_on `xts`
  >> simp[letinit_ml_def, do_con_check_def, nsLookup_def]
  >> PairCases
  >> simp[letinit_ml_def, do_con_check_def, nsLookup_def]
QED

Theorem scheme_semantics_preservation_terminates:
  ! prog cml_prog v st env (ffi :'ffi ffi_state) .
    scheme_semantics_prog prog (STerminate v) /\
    static_scope_check prog = INR prog /\
    codegen prog = INR cml_prog
    ==>
    semantics_prog (init_state ffi) init_env cml_prog (Terminate Success [v_to_string v])
Proof
  simp[semantics_prog_def, scheme_semantics_prog_def]
  >> simp[static_scope_check_def]
  >> simp_tac std_ss [codegen_def]
  >> simp[evaluate_prog_with_clock_def]
  >> rpt strip_tac
  >> qspec_then `ffi` assume_tac scheme_init_evaluate_dec
  >> gvs[]
  >> qrefine `ck1 + k`
  >> gvs[scheme_init_def]
  >> simp[Once evaluate_decs_append]
  >> dxrule_then assume_tac evaluate_decs_add_to_clock
  >> gvs[]
  >> pop_assum kall_tac
  >> simp[Ntimes evaluate_decs_def 2]
  >> simp[compile_scheme_prog_def]
  >> simp[pat_bindings_def]
  >> simp[extend_dec_env_def]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[Once scheme_init_env_defs]
  >> simp[GSYM scheme_cons_env_def]
  >> simp[every_one_con_check]

  >> simp[GSYM merge_env_def]
  >> simp[GSYM scheme_to_cake_env_def]
  >> simp[pmatch_def]
  >> simp[Ntimes evaluate_def 2, nsOptBind_def]

  >> gvs[scheme_semanticsTheory.steps_def]
  >> drule_then assume_tac value_terminating
  >> gvs[Once cont_rel_cases, Once valid_state_cases]
  >> gvs[Once valid_cont_cases, can_lookup_cases, FEVERY_FEMPTY]
  >> gvs[Once cps_rel_cases]
  >> qmatch_goalsub_abbrev_tac `evaluate _ newenv [_]`
  >> first_x_assum $ qspecl_then [`scheme_to_cake_env_st_1 ffi`, `newenv`] assume_tac
  >> unabbrev_all_tac
  >> gvs[scheme_init_st_defs]
  >> gvs[scheme_env_sub, scheme_runtime_funs_def, basis_scheme_env]
  >> Cases_on `ck2 <= ck`
  >>> HEADGOAL (
    qexists `ck - ck2`
    >> simp[Once ADD_COMM]
  )
  >>> LASTGOAL (
    qexists `0`
    >> simp[]
    >> dxrule_then assume_tac evaluate_add_to_clock
    >> gvs[]
    >> pop_assum $ qspec_then `ck2 - ck` assume_tac
    >> gvs[]
  )
  >> simp[Ntimes evaluate_decs_def 2]
  >> simp[pat_bindings_def]
  >> `nsAppend scheme_to_cake_env_env_13.c init_env.c = scheme_cons_env` by (
    simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[Once scheme_init_env_defs]
    >> simp[GSYM scheme_cons_env_def]
  )
  >> simp[scheme_cons_env_simp]
  >> gvs[Once ml_v_vals_cases]
  >~ [`bool_val_rel b mlb`] >>> HEADGOAL $ gvs[Once bool_val_rel_cases]
  >> simp[Ntimes evaluate_def 2]
  >> simp[evaluate_match_def, can_pmatch_all_def, pmatch_def,
    nsLookup_def, same_type_def, same_ctor_def, pat_bindings_def]
  >> simp[Ntimes evaluate_def 4, do_app_def, store_alloc_def, store_lookup_def,
    EL_APPEND_EQN, call_FFI_def, store_assign_def, store_v_same_type_def]
  >> cheat (*seems to depend on the ffi oracle here*)
QED

Theorem imp_semantics_prog:
  evaluate_decs (st with clock := ck) env p = (st1, Rval r) ∧
  st1.ffi.io_events = out ⇒
  semantics_prog st env p (Terminate Success out)
Proof
  fs [semantics_prog_def,evaluate_prog_with_clock_def] \\ rw []
  \\ qexists_tac ‘ck’ \\ simp []
QED

(*
Theorem scheme_imp_cake:
  codegen prog = INR cake_code ∧
  static_scope ∅ prog ∧
  scheme_semantics_prog prog (STerminate res)
  ⇒
  semantics_prog
    (FST (THE (prim_sem_env ffi)))
    (SND (THE (prim_sem_env (ffi:'ffi ffi_state))))
    cake_code (Terminate Success [v_to_string res])
Proof
  rewrite_tac [scheme_semantics_prog_def,codegen_def,APPEND_ASSOC]
  \\ rewrite_tac [GSYM start_up_def] \\ rw []
  \\ irule imp_semantics_prog
  \\ rewrite_tac [evaluate_decs_append]
  \\ simp [evaluate_decs_start_up]
  \\ simp [CaseEq"prod",CaseEq"result",PULL_EXISTS,combine_dec_result_def]
  \\ simp [Once evaluate_decs_def]
  \\ simp [Once evaluate_decs_def]
  \\ simp [astTheory.pat_bindings_def,every_one_con_check]
  \\ fs [steps_eq_FUNPOW_step]
  \\ qabbrev_tac ‘st0 = λ ck.
                  <|clock := ck; refs := [];
                    ffi := (ffi:'ffi ffi_state);
                    next_type_stamp := 5;
                    next_exn_stamp := 4;
                    fp_state :=
                    <|rws := []; opts := (λx. []); choices := 0;
                      canOpt := Strict; real_sem := F|>;
                    eval_state := NONE|>’
  \\ simp []
  \\ simp [evaluate_def,compile_scheme_prog_def,namespaceTheory.nsOptBind_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate _ env [e]’ \\ simp []
  \\ drule value_terminating
  \\ simp [scheme_semanticsPropsTheory.valid_state_cases,
           scheme_semanticsPropsTheory.can_lookup_cases]
  \\ simp [Once scheme_semanticsPropsTheory.valid_cont_cases]
  \\ simp [FEVERY_DEF,pmatch_def]
  \\ simp [Once cont_rel_cases,PULL_EXISTS]
  \\ disch_then $ qspecl_then [‘e’,‘st0 0’,‘env’] mp_tac
  \\ simp [Abbr‘st0’]
  \\ simp [Once cps_rel_cases]
  \\ simp [Abbr‘env’,combine_dec_result_def]
  \\ impl_tac
  >- cheat (* proving envs *)
  \\ strip_tac
  \\ qexists_tac ‘ck’ \\ fs []
  \\ qpat_x_assum ‘_ = (_,Rval [_])’ kall_tac
  \\ gvs [Abbr‘e’,every_one_con_check]
  \\ cheat (* not too bad *)
QED
*)


(*

Theorem add_to_sem_env_THE:
  ! st st' env env' prog .
    (st', env') = THE (add_to_sem_env (st, env) prog)
    ==>
    evaluate_decs st env prog = (st', Rval env')
Proof
  rpt strip_tac
  >> gvs[add_to_sem_env_def]
  >> Cases_on `evaluate_decs st env prog`
  >> Cases_on `r`
  >> gvs[THE_DEF]
  >> CASE_TAC
QED



Theorem eval_scheme_env':
  ! st env .
    (st, env) = THE (prim_sem_env empty_ffi)
    ==>
    evaluate_decs
      (FST (THE (prim_sem_env empty_ffi)))
      (SND (THE (prim_sem_env empty_ffi)))
      (scheme_basis_types ++ scheme_basis ++ [scheme_basis_list; scheme_basis_app]) =
      (st1, test)
Proof
  simp [prim_sem_env_eq] >> EVAL_TAC

max_print_depth := 10

(*

  simp [scheme_basis_types_def]
  simp [Once evaluate_decs_def,check_dup_ctors_def,combine_dec_result_def,
        scheme_basis_def,do_con_check_def,extend_dec_env_def]

  >> EVAL_TAC
  >> simp[scheme_env'_def]
  >> simp[add_to_sem_env_def]
  >> gvs[]
  >> pop_assum $ simp o single o GSYM
  >> rpt (pairarg_tac >> gvs[])
  >> simp[evaluate_decs_append]
  >> CASE_TAC
  >> CASE_TAC
  >> simp[]

  >> CASE_TAC
  >> CASE_TAC
  >> simp[Once evaluate_decs_cons]

  >> CASE_TAC
  >> CASE_TAC
  >> simp[]

  >> CASE_TAC
  >> simp[]
*)
QED

Theorem scheme_semantics_preservation_terminates:
  ! prog cml_prog v st env ffi .
    scheme_semantics_prog prog (STerminate v) /\
    static_scope_check prog = INR prog /\
    codegen prog = INR cml_prog /\
    (st, env) = THE (prim_sem_env empty_ffi)
    ==>
    semantics_prog st ednv cml_prog (Terminate Success [v_to_string v])
Proof
  (*Somewhere in here, I need a lemma that evaluate st env (...) = (st', Rval scheme_env')*)
  simp[semantics_prog_def, scheme_semantics_prog_def]
  >> simp[codegen_def, static_scope_check_def]
  >> simp[evaluate_prog_with_clock_def]
  >> rpt (pairarg_tac \\ fs [])
  >> SRULE [] scheme_env'_def
  >> extend_dec_env_def
  >> evaluate_decs_append
QED

*)

val _  = (max_print_depth := 0); (* don't print stuff in docs *)

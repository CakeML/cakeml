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
  v_to_string (SNum _) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "num") [] /\
  v_to_string (SBool F) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "#f") [] /\
  v_to_string (SBool T) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "#t") [] /\
  v_to_string (Wrong _) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "unspecified") [] /\
  v_to_string (PairP _) = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "pair") [] /\
  v_to_string Null = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "null") [] /\
  v_to_string _ = IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) "proc") []
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

Definition scheme_out_oracle_def:
  scheme_out_oracle =
    <| oracle      := (λffi_name _ _ _.
                         (* accepts calls to scheme_out *)
                         if ffi_name = ExtCall "scheme_out"
                         then Oracle_return () [] (* returns empty *)
                         else Oracle_final FFI_failed)
     ; ffi_state   := ()
     ; io_events   := []  |>  :unit ffi_state
End

Theorem scheme_semantics_preservation_value_terminates:
  ∀ prog cml_prog v st env .
    scheme_semantics_prog prog (STerminate v) /\
    static_scope_check prog = INR prog /\
    codegen prog = INR cml_prog
    ==>
    semantics_prog (init_state scheme_out_oracle) init_env cml_prog
                   (Terminate Success [v_to_string v])
Proof
  simp[semantics_prog_def, scheme_semantics_prog_def]
  >> simp[static_scope_check_def]
  >> simp_tac std_ss [codegen_def]
  >> simp[evaluate_prog_with_clock_def]
  >> rpt strip_tac
  >> qspec_then `scheme_out_oracle` assume_tac scheme_init_evaluate_dec
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
  >> drule_then assume_tac (value_terminating |> INST_TYPE [“:'ffi”|->“:unit”])

  >> gvs[Once cont_rel_cases, Once valid_state_cases]
  >> gvs[Once valid_cont_cases, can_lookup_cases, FEVERY_FEMPTY]
  >> gvs[Once cps_rel_cases]
  >> qmatch_goalsub_abbrev_tac `evaluate _ newenv [_]`
  >> first_x_assum $ qspecl_then
       [`scheme_to_cake_env_st_1 scheme_out_oracle`, `newenv`] assume_tac
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
    EL_APPEND_EQN, call_FFI_def, store_assign_def, store_v_same_type_def,
    scheme_out_oracle_def]
  >> fs [combine_dec_result_def,v_to_string_def]
  >> gvs [bool_val_rel_cases,pmatch_def,nsLookup_def,same_type_def,same_ctor_def]
  >> simp[Ntimes evaluate_def 4, do_app_def, store_alloc_def, store_lookup_def,
    EL_APPEND_EQN, call_FFI_def, store_assign_def, store_v_same_type_def,
    scheme_out_oracle_def,v_to_string_def]
QED

Theorem scheme_semantics_preservation_exception_terminates:
  ∀ prog cml_prog s st env .
    scheme_semantics_prog prog (SError s) /\
    static_scope_check prog = INR prog /\
    codegen prog = INR cml_prog
    ==>
    semantics_prog (init_state scheme_out_oracle) init_env cml_prog
                   (Terminate Success [IO_event (ExtCall "scheme_out") (MAP (n2w o ORD) (explode s)) []])
Proof
  simp[semantics_prog_def, scheme_semantics_prog_def]
  >> simp[static_scope_check_def]
  >> simp_tac std_ss [codegen_def]
  >> simp[evaluate_prog_with_clock_def]
  >> rpt strip_tac
  >> qspec_then `scheme_out_oracle` assume_tac scheme_init_evaluate_dec
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
  >> drule_then assume_tac (exception_terminating |> INST_TYPE [“:'ffi”|->“:unit”])

  >> gvs[Once cont_rel_cases, Once valid_state_cases]
  >> gvs[Once valid_cont_cases, can_lookup_cases, FEVERY_FEMPTY]
  >> gvs[Once cps_rel_cases]
  >> qmatch_goalsub_abbrev_tac `evaluate _ newenv [_]`
  >> first_x_assum $ qspecl_then
       [`scheme_to_cake_env_st_1 scheme_out_oracle`, `newenv`] assume_tac
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
  >> simp[Ntimes evaluate_def 2]
  >> simp[evaluate_match_def, can_pmatch_all_def, pmatch_def,
    nsLookup_def, same_type_def, same_ctor_def, pat_bindings_def]
  >> simp[Ntimes evaluate_def 4, do_app_def, store_alloc_def, store_lookup_def,
    EL_APPEND_EQN, call_FFI_def, store_assign_def, store_v_same_type_def,
    scheme_out_oracle_def]
  >> fs [combine_dec_result_def,v_to_string_def]
  >> gvs [bool_val_rel_cases,pmatch_def,nsLookup_def,same_type_def,same_ctor_def]
  >> simp[Ntimes evaluate_def 4, do_app_def, store_alloc_def, store_lookup_def,
    EL_APPEND_EQN, call_FFI_def, store_assign_def, store_v_same_type_def,
    scheme_out_oracle_def,v_to_string_def]
QED

Theorem lprefix_lub_LNIL:
  s = { [||] } ⇒ lprefix_lub s [||]
Proof
  fs [lprefix_lubTheory.lprefix_lub_def]
QED

Theorem decs_smaller_clock_io_mono[local] =
  cj 4 $ SRULE [PULL_FORALL] $ cj 6 $
    SRULE [is_clock_io_mono_def, pair_CASE_eq_forall] $
      cj 1 is_clock_io_mono_evaluate_decs;

Theorem evaluate_decs_timeout_smaller_clock[local]:
  ∀ (st:'ffi state) st' ck env e .
    evaluate_decs st env e = (st', Rerr (Rabort Rtimeout_error)) ∧
    ck ≤ st.clock
    ⇒
    ∃ st'' .
      evaluate_decs (st with clock := ck) env e = (st'', Rerr (Rabort Rtimeout_error)) /\
      io_events_mono st''.ffi st'.ffi
Proof
  rpt strip_tac
  >> gvs[LESS_EQ_EXISTS]
  >> Cases_on ‘evaluate_decs (st with clock := ck) env e’
  >> gvs[]
  >> conj_tac >- (
    spose_not_then assume_tac
    >> drule_all_then assume_tac evaluate_decs_add_to_clock
    >> gvs[]
    >> pop_assum $ qspec_then `p` assume_tac
    >> gvs[]
    >> qpat_assum `_ = _ + _` $ gvs o single o GSYM
  )
  >> irule decs_smaller_clock_io_mono
  >> pop_assum $ irule_at $ Pos last
  >> gvs[]
QED

Theorem TRUE_AND_IMP_FALSE_IND:
  ! P . P T /\ (P T ==> P F) ==> ! b . P b
Proof
  rpt strip_tac
  >> Cases_on `b`
  >> gvs[]
QED

Theorem scheme_semantics_preservation_diverges_lemma:
  ∀ prog cml_prog v st env .
    scheme_semantics_prog prog (SDiverge) /\
    static_scope_check prog = INR prog /\
    codegen prog = INR cml_prog
    ==>
    ∀k.
      ∃ffi.
        evaluate_prog_with_clock
          (init_state scheme_out_oracle) init_env k cml_prog
        =
        (ffi, Rerr (Rabort Rtimeout_error)) ∧ ffi.io_events = []
Proof
  simp[semantics_prog_def, scheme_semantics_prog_def]
  >> simp[static_scope_check_def]
  >> simp_tac std_ss [codegen_def]
  >> simp[evaluate_prog_with_clock_def]
  >> rpt strip_tac
  >> qspec_then `scheme_out_oracle` assume_tac scheme_init_evaluate_dec
  >> gvs[]
  >> reverse $ Induct_on `ck1 <= k` using TRUE_AND_IMP_FALSE_IND
  >> rpt strip_tac
  >> gvs[]
  >- (
    spose_not_then assume_tac
    >> first_x_assum $ qspecl_then [`ck1`, `ck1`] assume_tac
    >> gvs[]
    >> rpt (pairarg_tac >> gvs[])
    >> drule_then assume_tac evaluate_decs_timeout_smaller_clock
    >> pop_assum $ qspec_then `k` assume_tac
    >> gvs[io_events_mono_def]
  )
  >> gvs[LESS_EQ_EXISTS]
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
  >> drule_then assume_tac (diverges |> INST_TYPE [“:'ffi”|->“:unit”] |> SRULE [])

  >> gvs[Once cont_rel_cases, Once valid_state_cases]
  >> gvs[Once valid_cont_cases, can_lookup_cases, FEVERY_FEMPTY]
  >> gvs[Once cps_rel_cases]
  >> qmatch_goalsub_abbrev_tac `evaluate _ newenv [_]`
  >> first_x_assum $ qspecl_then
       [`scheme_to_cake_env_st_1 scheme_out_oracle`, `newenv`] assume_tac
  >> unabbrev_all_tac
  >> gvs[scheme_init_st_defs]
  >> gvs[scheme_env_sub, scheme_runtime_funs_def, basis_scheme_env]
  >> pop_assum $ qspec_then `ck2 + p` assume_tac
  >> gvs[]
  >> simp[combine_dec_result_def]
  >> simp[scheme_out_oracle_def]
QED

Theorem div_lnil_lemma[local]:
  (∀k. f k = [||]) ⇒ ((∃k. x = f k) ⇔ x = [||])
Proof
  metis_tac []
QED

Theorem scheme_semantics_preservation_diverges:
  ∀ prog cml_prog v st env .
    scheme_semantics_prog prog (SDiverge) /\
    static_scope_check prog = INR prog /\
    codegen prog = INR cml_prog
    ==>
    semantics_prog (init_state scheme_out_oracle) init_env cml_prog
                   (Diverge [||])
Proof
  rpt strip_tac
  \\ dxrule_all scheme_semantics_preservation_diverges_lemma
  \\ simp [] \\ strip_tac
  \\ simp [semantics_prog_def]
  \\ conj_tac >- metis_tac []
  \\ irule lprefix_lub_LNIL \\ simp [EXTENSION] \\ rw []
  \\ ho_match_mp_tac div_lnil_lemma \\ rw []
  \\ last_x_assum $ qspec_then ‘k’ strip_assume_tac \\ fs []
QED

Theorem imp_semantics_prog:
  evaluate_decs (st with clock := ck) env p = (st1, Rval r) ∧
  st1.ffi.io_events = out ⇒
  semantics_prog st env p (Terminate Success out)
Proof
  fs [semantics_prog_def,evaluate_prog_with_clock_def] \\ rw []
  \\ qexists_tac ‘ck’ \\ simp []
QED

val _  = (max_print_depth := 0); (* don't print stuff in docs *)

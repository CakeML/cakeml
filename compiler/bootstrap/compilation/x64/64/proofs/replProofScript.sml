(*
  Verification of the function (called repl) that implements the REPL
*)
Theory replProof
Ancestors
  semanticsProps backendProof x64_configProof compiler64X64Prog
  compiler64MainProg compiler64ReplProof
  evaluate semanticPrimitives ml_translator repl_types
  repl_check_and_tweak repl_init
Libs
  preamble

val _ = (max_print_depth := 12);

Theorem BACKEND_CONFIG_TYPE_v[local]:
  BACKEND_CONFIG_TYPE conf u ⇒
  u = BACKEND_CONFIG_v conf
Proof
  rw [] \\ imp_res_tac BACKEND_CONFIG_IMP \\ fs []
QED

Theorem repl_prog_isPREFIX:
  repl_prog ≼ FRONT compiler64_x64_prog
Proof
  rewrite_tac [listTheory.isPREFIX_THM,repl_moduleProgTheory.repl_prog_def,
               compiler64X64ProgTheory.compiler64_x64_prog_def,FRONT_CONS,
               locationTheory.unknown_loc_def]
  \\ EVAL_TAC
QED

val ffi_inst = type_of “basis_ffi _ _ _” |> dest_type |> snd |> hd

(*
  max_print_depth := 15
*)

Theorem evaluate_decs_compiler64_x64_prog:
  s.compiler = compiler_inst x64_config ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v DEC_v) ∧
  s.env_id_counter = (0,0,1) ∧ prog_syntax_ok compiler64_x64_prog ∧
  has_repl_flag (TL cl) ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  s.compiler_state = BACKEND_CONFIG_v conf ∧
  file_content fs «config_enc_str.txt» = SOME (encode_backend_config conf) ∧
  evaluate_decs (init_state (basis_ffi ext cl fs) with
                            <| clock := ck; eval_state := (SOME (EvalDecs s)) |>)
      init_env compiler64_x64_prog = (s1,res) ⇒
  res ≠ Rerr (Rabort Rtype_error)
Proof
  rw [] \\ pop_assum mp_tac
  \\ ‘~NULL compiler64_x64_prog’ by
   (once_rewrite_tac [compiler64_x64_prog_def] \\ rewrite_tac [NULL])
  \\ drule BUTLAST_LAST
  \\ disch_then (once_rewrite_tac o single)
  \\ strip_tac
  \\ assume_tac (Decls_FRONT_compiler64_x64_prog
       |> REWRITE_RULE [ml_progTheory.ML_code_env_def]
       |> Q.GEN ‘ffi’ |> Q.ISPEC ‘basis_ffi ext cl fs’
       |> Q.INST [‘eval_state_var’|->‘s’])
  \\ dxrule ml_progTheory.Decls_IMP_Prog
  \\ ‘prog_syntax_ok (FRONT compiler64_x64_prog)’ by
    (irule ml_progTheory.prog_syntax_ok_isPREFIX
     \\ first_x_assum $ irule_at Any
     \\ Cases_on ‘compiler64_x64_prog’ using SNOC_CASES
     \\ gvs [])
  \\ ‘prog_syntax_ok repl_prog’ by
    (irule ml_progTheory.prog_syntax_ok_isPREFIX
     \\ irule_at Any repl_prog_isPREFIX \\ fs [])
  \\ impl_tac >- fs [] \\ strip_tac
  \\ drule (repl_types_repl_prog |> Q.INST [`entry_cost` |-> `3`])
  \\ disch_then drule
  \\ disch_then (qspec_then ‘encode_backend_config conf’ mp_tac)
  \\ impl_tac >-
   (fs [] \\ simp (DB.find "repl_moduleProg_st" |> map (#1 o #2))
    \\ simp (repl_prog_isPREFIX :: (DB.find "refs_def" |> map (#1 o #2)))
    \\ fs [repl_prog_st_def, ml_progTheory.init_state_def])
  \\ fs [repl_prog_st_def]
  \\ qpat_abbrev_tac ‘ppp = W8array _ :: _’ \\ pop_assum kall_tac
  \\ qpat_x_assum ‘Prog _ _ _ _ _’ kall_tac
  \\ qpat_x_assum ‘evaluate_decs _ _ _ = _’ kall_tac
  \\ strip_tac \\ fs [LAST_compiler64_x64_prog]
  \\ qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
  (* calling main *)
  \\ fs [evaluate_decs_def,astTheory.pat_bindings_def,
         check_exp_constructors_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [do_con_check_def]
  \\ rewrite_tac [main_v_def]
  \\ rewrite_tac [EVAL “semanticPrimitives$do_opapp
       [Recclosure env [(«main»,«u», e)] «main»; Conv NONE []]”] \\ simp []
  \\ IF_CASES_TAC >- (fs [] \\ rw [] \\ fs [combine_dec_result_def])
  \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [do_con_check_def,build_conv_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [evaluate_App_Opapp,evaluate_Var]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rewrite_tac [main_host_v_def,EVAL
       ``semanticPrimitives$do_opapp [Recclosure env [(n,u,e)] n; arg]``]
  \\ simp []
  \\ IF_CASES_TAC >- (rw [] \\ fs [combine_dec_result_def])
  \\ simp [dec_clock_def,Once evaluate_def,evaluate_Var,
           namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def]
  \\ simp [astTheory.pat_bindings_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ IF_CASES_TAC >- (rw [] \\ fs [combine_dec_result_def])
  (* evaluate e_cl *)
  \\ fs [dec_clock_def]
  \\ qabbrev_tac ‘ev = (EvalDecs (s with env_id_counter := (0,1,1)))’
  \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> hd)
  \\ disch_then (qspec_then ‘SOME ev’ mp_tac)
  \\ impl_tac >- (fs [] \\ Cases_on ‘res_cl’ \\ fs [combine_dec_result_def])
  \\ strip_tac \\ fs []
  \\ Cases_on ‘res_cl = Rerr (Rabort Rtimeout_error)’
  >- (rw [] \\ fs [combine_dec_result_def])
  \\ fs []
  (* call compiler_has_repl_flag *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ assume_tac compiler64mainprog_has_repl_flag_v_thm
  \\ drule_all (Arrow_IMP |> INST_TYPE [“:'ffi”|->ffi_inst])
  \\ disch_then (qspec_then `(dec_clock (s_cl with eval_state := SOME ev))`
       (qx_choosel_then [`flag_env`,`flag_exp`,`junk`,`flag_value`,
                        `ck`,`flag_state`,`flag_res`] strip_assume_tac))
  \\ fs []
  \\ IF_CASES_TAC >- (rw[] \\ fs [combine_dec_result_def])
  \\ fs []
  \\ Cases_on `flag_res = Rerr (Rabort Rtimeout_error)`
  >- (rw [] \\ fs [combine_dec_result_def])
  \\ gvs []
  (* if *)
  \\ gvs [BOOL_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit,do_if_def]
  \\ fs [dec_clock_def]
  (* call run_interactive_repl *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [evaluate_App_Opapp,evaluate_Var]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ rewrite_tac [run_interactive_repl_v_def,EVAL “semanticPrimitives$do_opapp
       [Recclosure env [(n, u, e)] n; cl_v]”] \\ simp []
  \\ IF_CASES_TAC >- (fs [] \\ rw [] \\ fs [combine_dec_result_def])
  \\ fs [dec_clock_def]
  \\ simp [Once evaluate_def,evaluate_Var,namespaceTheory.nsOptBind_def]
  \\ simp [Once evaluate_def,can_pmatch_all_def,pmatch_def,
           astTheory.pat_bindings_def]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [dec_clock_def]
  (* charsFrom *)
  \\ first_x_assum (qspecl_then [`ck`,`junk`]
       (qx_choosel_then [`env_pr`,`e_pr`,`res_pr`,`s_pr`] strip_assume_tac))
  \\ simp []
  \\ IF_CASES_TAC >- (fs [] \\ rw [] \\ fs [combine_dec_result_def])
  \\ drule (evaluatePropsTheory.eval_no_eval_simulation |> CONJUNCTS |> hd)
  \\ disch_then (qspec_then ‘SOME ev’ mp_tac)
  \\ impl_tac >- (fs [] \\ Cases_on ‘res_pr’ \\ fs [combine_dec_result_def])
  \\ strip_tac \\ fs []
  \\ Cases_on ‘res_pr = Rerr (Rabort Rtimeout_error)’
  >- (rw [] \\ fs [combine_dec_result_def])
  \\ fs []
  (* decode_backend_config *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [dec_clock_def]
  \\ assume_tac decodeProgTheory.decode_backend_config_v_thm
  \\ drule_all (Arrow_IMP |> INST_TYPE [“:'ffi”|->ffi_inst])
  \\ disch_then (qspec_then `s_pr with <|clock := s_pr.clock − 1;
                                        eval_state := SOME ev|>`
       (qx_choosel_then [`decode_env`,`decode_exp`,`decode_junk`,`decode_value`,
                        `decode_cost`,`decode_state`,`decode_res`] strip_assume_tac))
  \\ fs []
  \\ IF_CASES_TAC >- (rw[] \\ fs [combine_dec_result_def])
  \\ fs []
  \\ Cases_on `decode_res = Rerr (Rabort Rtimeout_error)`
  >- (rw [] \\ fs [combine_dec_result_def])
  \\ gvs []
  (* start_repl *)
  \\ simp [Once evaluate_def,evaluate_Var,evaluate_Con,evaluate_list,
           namespaceTheory.nsOptBind_def,evaluate_Lit]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st8 env8’
  \\ qspecl_then
       [‘st8’,‘env8’,‘Short «start_repl»’,‘Short « v0»’,‘basis_ffi ext cl fs’,‘TL cl’] mp_tac
    (evaluate_start_repl
     |> Q.INST [`host` |-> `HostX64`,
                `host_v` |-> `COMPILER64MAINPROG_COMPILER64_HOST_v HostX64`]
     |> Q.GENL [`st`,`env`,`start_repl_str`,`arg_str`,`ffi`,`cl`,`s1`,`s`])
  \\ simp [Abbr`st8`,Abbr`env8`,Abbr`ev`,host_config_def,
           COMPILER64MAINPROG_COMPILER64_HOST_TYPE_def,
           COMPILER64MAINPROG_COMPILER64_HOST_v_def]
  \\ fs [backend_enc_decTheory.encode_backend_config_thm]
  \\ drule BACKEND_CONFIG_TYPE_v \\ strip_tac
  \\ gvs []
  \\ disch_then drule
  \\ gvs []
  \\ impl_tac
  >-
   (CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp [dec_clock_def]
    \\ drule_then irule repl_types_input_skip_alt \\ simp [])
  \\ strip_tac \\ simp []
  \\ rename [‘res9 ≠ Rerr (Rabort Rtype_error)’]
  \\ Cases_on ‘res9 = Rerr (Rabort Rtype_error)’ >- fs [combine_dec_result_def]
  \\ fs []
  \\ reverse (Cases_on ‘res9’) \\ fs [] >- (rw [] \\ fs [combine_dec_result_def])
  \\ simp [pmatch_def] \\ rw [combine_dec_result_def] \\ fs []
QED

Theorem semantics_prog_compiler64_x64_prog:
  s.compiler = compiler_inst x64_config ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v DEC_v) ∧
  s.env_id_counter = (0,0,1) ∧ has_repl_flag (TL cl) ∧ wfcl cl ∧ wfFS fs ∧
  STD_streams fs ∧ hasFreeFD fs ∧ prog_syntax_ok compiler64_x64_prog ∧
  s.compiler_state = BACKEND_CONFIG_v conf ∧
  file_content fs «config_enc_str.txt» = SOME (encode_backend_config conf) ⇒
  Fail ∉ semantics_prog
           (init_state (basis_ffi ext cl fs) with eval_state := SOME (EvalDecs s))
           init_env compiler64_x64_prog
Proof
  fs [IN_DEF,semanticsTheory.semantics_prog_def] \\ rpt strip_tac
  \\ mp_tac (Q.GENL [‘ck’,‘res’,‘s1’] evaluate_decs_compiler64_x64_prog) \\ fs []
  \\ fs [semanticsTheory.evaluate_prog_with_clock_def]
  \\ pairarg_tac \\ gvs []
  \\ qexists_tac ‘k’ \\ fs []
QED

val _ = check_thm semantics_prog_compiler64_x64_prog;

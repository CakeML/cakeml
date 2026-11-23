(*
  Verification of the function (called repl) that implements the REPL
*)
Theory replProof
Ancestors
  semanticsProps backendProof x64_configProof compiler_x64Prog
  compiler_mainProg compiler_replProof
  evaluate semanticPrimitives ml_translator repl_types
  repl_check_and_tweak repl_init
Libs
  preamble

val _ = (max_print_depth := 12);

Theorem repl_prog_isPREFIX:
  repl_prog ≼ FRONT compiler_x64_prog
Proof
  rewrite_tac [listTheory.isPREFIX_THM,repl_moduleProgTheory.repl_prog_def,
               compiler_x64ProgTheory.compiler_x64_prog_def,FRONT_CONS,
               locationTheory.unknown_loc_def]
  \\ EVAL_TAC
QED

val ffi_inst = type_of “basis_ffi _ _ _” |> dest_type |> snd |> hd

(*
  max_print_depth := 15
*)

Theorem evaluate_decs_compiler_x64_prog:
  ¬s.initialised ∧
  s.init_ok (BACKEND_CONFIG_v conf)
    (compiler_fun_cl (COMPILER_MAINPROG_COMPILER_HOST_v HostX64)) ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v DEC_v) ∧
  s.env_id_counter = (0,0,1) ∧ prog_syntax_ok compiler_x64_prog ∧
  has_repl_flag (TL cl) ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧ hasFreeFD fs ∧
  file_content fs «config_enc_str.txt» = SOME (encode_backend_config conf) ∧
  evaluate_decs (init_state (basis_ffi ext cl fs) with
                            <| clock := ck; eval_state := SOME s;
                               ptr_eq_oracle := po; eval_oracle := eo |>)
      init_env compiler_x64_prog = (s1,res) ⇒
  res ≠ Rerr (Rabort Rtype_error)
Proof
  rw [] \\ pop_assum mp_tac
  \\ ‘~NULL compiler_x64_prog’ by
   (once_rewrite_tac [compiler_x64_prog_def] \\ rewrite_tac [NULL])
  \\ drule BUTLAST_LAST
  \\ disch_then (once_rewrite_tac o single)
  \\ strip_tac
  \\ assume_tac (Decls_FRONT_compiler_x64_prog
       |> REWRITE_RULE [ml_progTheory.ML_code_env_def]
       |> Q.GEN ‘ffi’ |> Q.ISPEC ‘basis_ffi ext cl fs’
       |> Q.INST [‘eval_state_var’|->‘s’]
       |> MATCH_MP ml_progTheory.Decls_with_oracles |> Q.INST [‘po'’ |-> ‘po’])
  \\ dxrule ml_progTheory.Decls_IMP_Prog
  \\ ‘prog_syntax_ok (FRONT compiler_x64_prog)’ by
    (irule ml_progTheory.prog_syntax_ok_isPREFIX
     \\ first_x_assum $ irule_at Any
     \\ Cases_on ‘compiler_x64_prog’ using SNOC_CASES
     \\ gvs [])
  \\ ‘prog_syntax_ok repl_prog’ by
    (irule ml_progTheory.prog_syntax_ok_isPREFIX
     \\ irule_at Any repl_prog_isPREFIX \\ fs [])
  \\ impl_tac >- fs [] \\ strip_tac
  \\ qpat_x_assum ‘Prog _ _ _ _ _’ (assume_tac o SIMP_RULE (srw_ss()) [])
  \\ drule (repl_types_repl_prog |> Q.INST [`entry_cost` |-> `3`]
             |> SIMP_RULE (srw_ss()) [])
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
  \\ strip_tac \\ fs [LAST_compiler_x64_prog]
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
  (* main_host (Hostx64, u) *)
  \\ qmatch_goalsub_abbrev_tac ‘evaluate$evaluate st8 env8 [App Opapp [Var mh; Var av]]’
  \\ Cases_on ‘evaluate$evaluate st8 env8 [App Opapp [Var mh; Var av]]’
  \\ rename1 ‘_ = (st9,res9)’
  \\ mp_tac (Q.INST [‘st’|->‘st8’,‘env’|->‘env8’,‘main_host_str’|->‘mh’,
                     ‘arg_str’|->‘av’,‘st1’|->‘st9’,‘res’|->‘res9’,
                     ‘host’|->‘HostX64’,
                     ‘host_v’|->‘COMPILER_MAINPROG_COMPILER_HOST_v HostX64’,
                     ‘cl’|->‘TL cl’,‘ffi’|->‘basis_ffi ext cl fs’,
                     ‘s’|->‘s with env_id_counter := (0,1,1)’]
                (INST_TYPE [“:'ffi”|->ffi_inst] evaluate_main_host))
  \\ impl_tac
  >- (
    simp [Abbr ‘st8’,Abbr ‘env8’,Abbr ‘mh’,Abbr ‘av’,
          COMPILER_MAINPROG_COMPILER_HOST_TYPE_def,
          COMPILER_MAINPROG_COMPILER_HOST_v_def]
    \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv)
    \\ gvs [COMPILER_MAINPROG_COMPILER_HOST_v_def])
  \\ rw [] \\ gvs []
  \\ Cases_on ‘res9’ \\ gvs [pmatch_def,combine_dec_result_def]
QED

Theorem semantics_prog_compiler_x64_prog:
  ¬s.initialised ∧
  s.init_ok (BACKEND_CONFIG_v conf)
    (compiler_fun_cl (COMPILER_MAINPROG_COMPILER_HOST_v HostX64)) ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v DEC_v) ∧
  s.env_id_counter = (0,0,1) ∧ has_repl_flag (TL cl) ∧ wfcl cl ∧ wfFS fs ∧
  STD_streams fs ∧ hasFreeFD fs ∧ prog_syntax_ok compiler_x64_prog ∧
  file_content fs «config_enc_str.txt» = SOME (encode_backend_config conf) ⇒
  Fail ∉ semantics_prog
           (init_state (basis_ffi ext cl fs) with eval_state := SOME s)
           init_env compiler_x64_prog
Proof
  fs [IN_DEF,semanticsTheory.semantics_prog_def,
      semanticsTheory.semantics_determ_def] \\ rpt strip_tac
  \\ mp_tac (Q.GENL [‘ck’,‘res’,‘s1’,‘po’,‘eo’] evaluate_decs_compiler_x64_prog) \\ fs []
  \\ fs [semanticsTheory.evaluate_prog_with_clock_def]
  \\ pairarg_tac \\ gvs []
  \\ qexists_tac ‘k’ \\ fs []
  \\ metis_tac []
QED

val _ = check_thm semantics_prog_compiler_x64_prog;

(* check_thm inspects only tags; an open hypothesis of any lemma used would
   appear here. *)
val _ = if null (hyp semantics_prog_compiler_x64_prog) then ()
        else failwith "semantics_prog_compiler_x64_prog has hypotheses";

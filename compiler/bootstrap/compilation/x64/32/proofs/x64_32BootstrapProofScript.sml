(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)
Theory x64_32BootstrapProof
Ancestors
  repl_decs_allowed semanticsProps backendProof x64_configProof
  compiler32Prog x64_32Bootstrap
Libs
  preamble

Theorem with_clos_conf_simp[local]:
    (mc_init_ok x64_config (x64_backend_config with <| clos_conf := z ; bvl_conf updated_by
                    (λc. c with <|inline_size_limit := t1; exp_cut := t2|>) |>) =
     mc_init_ok x64_config x64_backend_config) /\
    (x.max_app <> 0 /\ (case x.known_conf of NONE => T | SOME k => k.val_approx_spt = LN) ==>
     (backend_config_ok x64_config (x64_backend_config with clos_conf := x) =
      backend_config_ok x64_config x64_backend_config))
Proof
  fs [mc_init_ok_def,FUN_EQ_THM,backend_config_ok_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ EVAL_TAC
QED

Definition compiler_instance_def:
  compiler_instance =
    <| init_state := info;
       compiler_fun := compile_inc_progs_for_eval x64_config ;
       config_dom := UNIV ;
       config_v := BACKEND_CONFIG_v ;
       decs_dom := decs_allowed ;
       decs_v := LIST_v DEC_v |>
End

Theorem compiler_instance_lemma[local]:
  INJ compiler_instance.config_v 𝕌(:backend$config) 𝕌(:semanticPrimitives$v) ∧
  compiler_instance.init_state = info ∧
  compiler_instance.compiler_fun = compile_inc_progs_for_eval x64_config
Proof
  fs [compiler_instance_def]
QED

val cake_terminate = semantics_compiler32_prog
  |> Q.INST[‘eval_state_var’|->‘the_EvalDecs (mk_init_eval_state compiler_instance)’]
  |> SIMP_RULE (srw_ss()) [source_evalProofTheory.mk_init_eval_state_def,the_EvalDecs_def]
  |> SIMP_RULE (srw_ss()) [GSYM source_evalProofTheory.mk_init_eval_state_def
                           |> SIMP_RULE (srw_ss()) []]
  |> UNDISCH_ALL
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [compiler32_compiled];

Theorem cake_compiled_thm =
  MATCH_MP compile_correct_eval (cj 1 compiler32_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,
                         GSYM AND_IMP_INTRO,with_clos_conf_simp]
  |> Q.INST [‘ev’|->‘SOME compiler_instance’]
  |> SIMP_RULE (srw_ss()) [add_eval_state_def,opt_eval_config_wf_def,
                           compiler_instance_lemma]
  |> C MATCH_MP (cj 1 cake_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 cake_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (UNDISCH is_x64_machine_config_IMP)
  |> SRULE [SF CONJ_ss] |> CONJUNCT2 |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> check_thm;

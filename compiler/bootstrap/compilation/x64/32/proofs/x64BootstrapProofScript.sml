(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     compiler32ProgTheory x64BootstrapTheory

val _ = new_theory"x64BootstrapProof";

val with_clos_conf_simp = prove(
  ``(mc_init_ok (x64_backend_config with <| clos_conf := z ; bvl_conf updated_by
                    (λc. c with <|inline_size_limit := t1; exp_cut := t2|>) |>) =
     mc_init_ok x64_backend_config) /\
    (x.max_app <> 0 /\ (case x.known_conf of NONE => T | SOME k => k.val_approx_spt = LN) ==>
     (backend_config_ok (x64_backend_config with clos_conf := x) =
      backend_config_ok x64_backend_config))``,
  fs [mc_init_ok_def,FUN_EQ_THM,backend_config_ok_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ EVAL_TAC);

Definition compiler_instance_def:
  compiler_instance =
    <| init_state := config_to_inc_config cake_config ;
       compiler_fun := compile_inc_progs_for_eval cake_config.lab_conf.asm_conf ;
       config_dom := UNIV ;
       config_v := BACKEND_INC_CONFIG_v ;
       decs_dom := decs_allowed ;
       decs_v := LIST_v AST_DEC_v |>
End

Triviality compiler_instance_lemma:
  INJ compiler_instance.config_v 𝕌(:inc_config) 𝕌(:semanticPrimitives$v) ∧
  compiler_instance.init_state = config_to_inc_config cake_config ∧
  compiler_instance.compiler_fun =
    compile_inc_progs_for_eval cake_config.lab_conf.asm_conf
Proof
  fs [compiler_instance_def]
QED

Theorem cake_config_lab_conf_asm_conf:
  cake_config.lab_conf.asm_conf = x64_config
Proof
  once_rewrite_tac [cake_config_def] \\ EVAL_TAC
QED

val cake_io_events_def = new_specification("cake_io_events_def",["cake_io_events"],
  semantics_compiler32_prog
  |> Q.INST[‘eval_state_var’|->‘the_EvalDecs (mk_init_eval_state compiler_instance)’]
  |> SIMP_RULE (srw_ss()) [source_evalProofTheory.mk_init_eval_state_def,the_EvalDecs_def]
  |> SIMP_RULE (srw_ss()) [GSYM source_evalProofTheory.mk_init_eval_state_def
                           |> SIMP_RULE (srw_ss()) []]
  |> Q.GENL[`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_sem,cake_output) = cake_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (cake_not_fail,cake_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail cake_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct_eval cake_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO,
                         with_clos_conf_simp]
  |> Q.INST [‘ev’|->‘SOME compiler_instance’]
  |> SIMP_RULE (srw_ss()) [add_eval_state_def,opt_eval_config_wf_def,compiler_instance_lemma]
  |> C MATCH_MP cake_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cake_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_compiled_thm =
  CONJ compile_correct_applied cake_output
  |> DISCH_ALL
  |> check_thm;

val _ = export_theory();

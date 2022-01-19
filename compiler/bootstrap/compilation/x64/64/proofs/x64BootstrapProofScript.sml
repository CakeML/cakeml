(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     compiler64ProgTheory x64BootstrapTheory replProofTheory

val _ = new_theory"x64BootstrapProof";

Theorem compile_correct_eval:
  compile c prog = SOME (bytes,bitmaps,c') ⇒
   let (s0,env) = THE (prim_sem_env (ffi: 'ffi ffi_state)) in
   ¬semantics_prog (add_eval_state ev s0) env prog Fail ∧ backend_config_ok c ∧
   mc_conf_ok mc ∧ mc_init_ok c mc ∧ opt_eval_config_wf c' ev ∧
   installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names ffi
     (heap_regs c.stack_conf.reg_names) mc ms ⇒
   machine_sem mc ffi ms ⊆
     extend_with_resource_limit
       (semantics_prog (add_eval_state ev s0) env prog)
Proof
  fs [LET_THM] \\ pairarg_tac \\ rw []
  \\ mp_tac compile_correct' \\ fs []
  \\ rw [extend_with_resource_limit'_def]
  \\ fs [extend_with_resource_limit_def,SUBSET_DEF]
QED

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

Definition the_EvalDecs_def:
  the_EvalDecs (EvalDecs x) = x
End

val cake_io_events_def = new_specification("cake_io_events_def",["cake_io_events"],
  semantics_compiler64_prog
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

val cake_compiled_thm =
  CONJ compile_correct_applied cake_output
  |> DISCH_ALL
 (* |> check_thm *)
  |> curry save_thm "cake_compiled_thm";

(* --- *)

Triviality mk_compiler_fun_from_ci_tuple:
  mk_compiler_fun_from_ci c = (λ(x,y,z). mk_compiler_fun_from_ci c (x,y,z))
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

Theorem mk_init_eval_state_lemma =
  “mk_init_eval_state compiler_instance”
  |> SIMP_CONV (srw_ss()) [compiler_instance_def,
       source_evalProofTheory.mk_init_eval_state_def]
  |> ONCE_REWRITE_RULE [mk_compiler_fun_from_ci_tuple]
  |> SIMP_RULE (srw_ss()) [source_evalProofTheory.mk_compiler_fun_from_ci_def,
        GSYM compiler_inst_def,cake_config_lab_conf_asm_conf];

val _ = export_theory();

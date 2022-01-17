(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     compiler64ProgTheory x64BootstrapTheory

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

Definition decs_allowed_def:
  decs_allowed (s:ast$dec list) = T
End

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
  |> check_thm
  |> curry save_thm "cake_compiled_thm";

(* TODO: compose this with a correctness theorem for compiler_x64? *)

open evaluateTheory
open semanticPrimitivesTheory
open backendProofTheory

Definition compiler_inst_def:
  compiler_inst c = (λ(x,y,z).
                do
                  cfg <- v_fun_abs 𝕌(:inc_config) BACKEND_INC_CONFIG_v y;
                  (cfg2,bs,ws) <- compile_inc_progs_for_eval c (x,cfg,z);
                  SOME (BACKEND_INC_CONFIG_v cfg2,bs,ws)
                od)
End

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

Theorem no_closures_IMP_concrete_v:
  (∀v. no_closures v ⇒ concrete_v v) ∧
  (∀v. EVERY no_closures v ⇒ concrete_v_list v)
Proof
  ho_match_mp_tac concrete_v_ind \\ rw []
  \\ Cases_on ‘v’ \\ fs [ml_translatorTheory.no_closures_def, SF ETA_ss]
QED

Triviality EqualityType_concrete_v:
  a x v ∧ EqualityType a ⇒ concrete_v v
Proof
  fs [ml_translatorTheory.EqualityType_def]
  \\ rw [] \\ res_tac \\ imp_res_tac no_closures_IMP_concrete_v
QED

Theorem EqualityType_LIST_TYPE_AST_DEC_TYPE:
  EqualityType (LIST_TYPE AST_DEC_TYPE)
Proof
  cheat
QED

Theorem EqualityType_BACKEND_INC_CONFIG_TYPE:
  EqualityType BACKEND_INC_CONFIG_TYPE
Proof
  cheat
QED

Theorem concrete_v_decs:
  LIST_TYPE AST_DEC_TYPE decs v ⇒ concrete_v v
Proof
  rw [] \\ drule EqualityType_concrete_v
  \\ fs [EqualityType_LIST_TYPE_AST_DEC_TYPE]
QED

Theorem concrete_v_inc_config:
  BACKEND_INC_CONFIG_TYPE c v ⇒ concrete_v v
Proof
  rw [] \\ drule EqualityType_concrete_v
  \\ fs [EqualityType_BACKEND_INC_CONFIG_TYPE]
QED

Theorem cake_config_lab_conf_asm_conf:
  cake_config.lab_conf.asm_conf = x64_config
Proof
  once_rewrite_tac [cake_config_def] \\ EVAL_TAC
QED

Theorem LIST_TYPE_AST_DEC_IMP:
  LIST_TYPE AST_DEC_TYPE decs decs_v ⇒
  ∀x. LIST_v AST_DEC_v x = decs_v ⇔ x = decs
Proof
  assume_tac EqualityType_LIST_TYPE_AST_DEC_TYPE
  \\ rw []
  \\ ‘IsTypeRep (LIST_v AST_DEC_v) (LIST_TYPE AST_DEC_TYPE)’ by
      (irule decProgTheory.IsTypeRep_LIST_v
       \\ fs [decProgTheory.IsTypeRep_AST_DEC_v])
  \\ fs [ml_translatorTheory.IsTypeRep_def]
  \\ fs [ml_translatorTheory.EqualityType_def]
QED

Theorem BACKEND_INC_CONFIG_IMP:
  BACKEND_INC_CONFIG_TYPE c v ⇒
  ∀x. BACKEND_INC_CONFIG_v x = v ⇔ x = c
Proof
  assume_tac EqualityType_BACKEND_INC_CONFIG_TYPE
  \\ rw [] \\ assume_tac decodeProgTheory.IsTypeRep_BACKEND_INC_CONFIG_v
  \\ fs [ml_translatorTheory.IsTypeRep_def]
  \\ fs [ml_translatorTheory.EqualityType_def]
QED

Theorem v_fun_abs_BACKEND_INC_CONFIG_v:
  BACKEND_INC_CONFIG_TYPE s1 s1_v ⇒
  v_fun_abs 𝕌(:inc_config) BACKEND_INC_CONFIG_v s1_v = SOME s1
Proof
  fs [source_evalProofTheory.v_rel_abs,BACKEND_INC_CONFIG_TYPE_IMP]
  \\ strip_tac \\ imp_res_tac BACKEND_INC_CONFIG_IMP \\ fs []
QED

Theorem v_to_word64_list_thm:
  ∀ws ws_v. LIST_TYPE WORD ws ws_v ⇒ v_to_word64_list ws_v = SOME ws
Proof
  Induct \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word64_list_def,
                v_to_list_def,list_type_num_def]
  THEN1 EVAL_TAC \\ rw []
  \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word64_list_def,
         v_to_list_def,list_type_num_def]
  \\ res_tac \\ fs []
  \\ gvs [AllCaseEqs(),PULL_EXISTS]
  \\ res_tac \\ fs []
  \\ simp [Once maybe_all_list_def,AllCaseEqs()]
  \\ gvs [ml_translatorTheory.WORD_def]
  \\ EVAL_TAC
QED

Theorem v_to_word8_list_thm:
  ∀bs bs_v. LIST_TYPE WORD bs bs_v ⇒ v_to_word8_list bs_v = SOME bs
Proof
  Induct \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word8_list_def,
                v_to_list_def,list_type_num_def]
  THEN1 EVAL_TAC \\ rw []
  \\ fs [ml_translatorTheory.LIST_TYPE_def,v_to_word8_list_def,
         v_to_list_def,list_type_num_def]
  \\ res_tac \\ fs []
  \\ gvs [AllCaseEqs(),PULL_EXISTS]
  \\ res_tac \\ fs []
  \\ simp [Once maybe_all_list_def,AllCaseEqs()]
  \\ gvs [ml_translatorTheory.WORD_def]
  \\ EVAL_TAC
QED

Theorem evaliate_Eval:
  nsLookup env.v (Short "env") = SOME (Env env1 id1) ⇒
  nsLookup env.v (Short "decs") = SOME decs_v ⇒
  nsLookup env.v (Short "s1") = SOME s1_v ⇒
  nsLookup env.v (Short "s2") = SOME s2_v ⇒
  nsLookup env.v (Short "bs") = SOME bs_v ⇒
  nsLookup env.v (Short "ws") = SOME ws_v ⇒
  LIST_TYPE AST_DEC_TYPE decs decs_v ∧ decs_allowed decs ∧
  BACKEND_INC_CONFIG_TYPE s1 s1_v ∧
  BACKEND_INC_CONFIG_TYPE s2 s2_v ∧
  LIST_TYPE WORD ws ws_v ∧
  LIST_TYPE WORD bs bs_v ∧
  compile_inc_progs_for_eval x64_config (id1,s1,decs) = SOME (s2,bs,ws) ∧
  st.eval_state = SOME (EvalDecs s) ∧
  s.compiler = compiler_inst x64_config ∧
  s.compiler_state = s1_v ∧
  s.decode_decs = v_fun_abs decs_allowed (LIST_v AST_DEC_v) ⇒
  evaluate st env [App Eval [Var (Short "env"); Var (Short "s1");
                             Var (Short "decs"); Var (Short "s2");
                             Var (Short "bs"); Var (Short "ws")]] =
    let st = (st with eval_state := SOME (EvalDecs
                   (add_decs_generation (s with compiler_state := s2_v)))) in
      if st.clock = 0 then (st, Rerr (Rabort Rtimeout_error)) else
        case evaluate_decs (dec_clock st) env1 decs of
        | (st2,Rval env2) =>
            (case declare_env st2.eval_state (extend_dec_env env2 env1) of
               NONE => (st2,Rerr (Rabort Rtype_error))
             | SOME (x,es2) =>
               (st2 with
                eval_state :=
                  reset_env_generation (SOME (EvalDecs s)) es2,Rval [x]))
        | (st2,Rerr (Rraise v7)) =>
            (st2 with
             eval_state :=
               reset_env_generation (SOME (EvalDecs s)) st2.eval_state,
             Rerr (Rraise v7))
        | (st2,Rerr (Rabort a)) => (st2,Rerr (Rabort a))
Proof
  fs [evaluate_def,do_eval_res_def]
  \\ fs [do_eval_def]
  \\ rpt strip_tac
  \\ ‘v_fun_abs decs_allowed (LIST_v AST_DEC_v) decs_v = SOME decs’ by
   (fs [source_evalProofTheory.v_rel_abs]
    \\ drule LIST_TYPE_AST_DEC_IMP \\ fs []
    \\ DEEP_INTRO_TAC some_intro \\ fs [IN_DEF])
  \\ ‘compiler_agrees (compiler_inst x64_config) (id1,s1_v,decs) (s2_v,bs_v,ws_v)’ by
   (fs [compiler_agrees_def,compiler_inst_def]
    \\ imp_res_tac v_fun_abs_BACKEND_INC_CONFIG_v \\ fs []
    \\ imp_res_tac v_to_word64_list_thm
    \\ imp_res_tac v_to_word8_list_thm
    \\ imp_res_tac BACKEND_INC_CONFIG_IMP
    \\ imp_res_tac concrete_v_inc_config \\ fs [])
  \\ fs [concrete_v_decs,SF SFY_ss]
QED

val _ = export_theory();

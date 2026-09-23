(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)
Theory arm8BootstrapProof
Ancestors
  holLightConsistency
  semanticsProps backendProof arm8_configProof arm8_asl_configProof
  compiler64Arm8Prog arm8Bootstrap arm8ReplProof compiler64ReplProof
  candle_prover_semantics mlstring
Libs
  preamble

Theorem with_clos_conf_simp[local]:
    (mc_init_ok arm8_config (arm8_backend_config with <| clos_conf := z ; bvl_conf updated_by
                    (λc. c with <|inline_size_limit := t1; exp_cut := t2|>) |>) =
     mc_init_ok arm8_config arm8_backend_config) /\
    (x.max_app <> 0 /\ (case x.known_conf of NONE => T | SOME k => k.val_approx_spt = LN) ==>
     (backend_config_ok arm8_config (arm8_backend_config with clos_conf := x) =
      backend_config_ok arm8_config arm8_backend_config))
Proof
  fs [mc_init_ok_def,FUN_EQ_THM,backend_config_ok_def]
  \\ rw [] \\ eq_tac \\ rw [] \\ EVAL_TAC
QED

Definition compiler_instance_def:
  compiler_instance =
    <| init_state := info;
       compiler_fun := compile_inc_progs_for_eval arm8_config ;
       config_dom := UNIV ;
       config_v := BACKEND_CONFIG_v ;
       decs_dom := decs_allowed ;
       decs_v := LIST_v DEC_v |>
End

Theorem compiler_instance_lemma[local]:
  INJ compiler_instance.config_v 𝕌(:backend$config) 𝕌(:semanticPrimitives$v) ∧
  compiler_instance.init_state = info ∧
  compiler_instance.compiler_fun = compile_inc_progs_for_eval arm8_config
Proof
  fs [compiler_instance_def]
QED

Theorem backend_config_ok_init_conf:
  backend_config_ok arm8_config init_conf
Proof
  assume_tac arm8_backend_config_ok
  \\ gvs [backendProofTheory.backend_config_ok_def,init_conf_def]
  \\ EVAL_TAC
QED

Theorem mc_init_ok_init_conf:
  mc_init_ok arm8_config init_conf mc = mc_init_ok arm8_config arm8_backend_config mc
Proof
  simp [mc_init_ok_def,init_conf_def]
QED

val cake_io_events_def = new_specification("cake_io_events_def",["cake_io_events"],
  semantics_compiler64_arm8_prog
  |> SRULE [ml_progTheory.prog_syntax_ok_semantics, compiler64_compiled]
  |> Q.INST[‘eval_state_var’|->‘the_EvalDecs (mk_init_eval_state compiler_instance)’]
  |> SIMP_RULE (srw_ss()) [source_evalProofTheory.mk_init_eval_state_def,the_EvalDecs_def]
  |> SIMP_RULE (srw_ss()) [GSYM source_evalProofTheory.mk_init_eval_state_def
                           |> SIMP_RULE (srw_ss()) []]
  |> Q.GENL[`ext`,`cl`,`fs`]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM)]);

val (cake_sem,cake_output) = cake_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (cake_not_fail,cake_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail cake_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct_eval (cj 1 compiler64_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,
                         GSYM AND_IMP_INTRO,with_clos_conf_simp]
  |> Q.INST [‘ev’|->‘SOME compiler_instance’]
  |> SIMP_RULE (srw_ss()) [add_eval_state_def,opt_eval_config_wf_def,
                           compiler_instance_lemma,mc_init_ok_init_conf]
  |> C MATCH_MP cake_not_fail
  |> C MATCH_MP backend_config_ok_init_conf
  |> REWRITE_RULE[cake_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH arm8_machine_config_ok)(UNDISCH arm8_init_ok))
  |> DISCH(#1(dest_imp(concl arm8_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_compiled_thm =
  CONJ compile_correct_applied cake_output
  |> DISCH_ALL

val compile_correct_applied_asl =
  MATCH_MP compile_correct_eval (cj 1 compiler64_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,
                         GSYM AND_IMP_INTRO,with_clos_conf_simp]
  |> Q.INST [‘ev’|->‘SOME compiler_instance’]
  |> SIMP_RULE (srw_ss()) [add_eval_state_def,opt_eval_config_wf_def,
                           compiler_instance_lemma,mc_init_ok_init_conf]
  |> C MATCH_MP cake_not_fail
  |> C MATCH_MP backend_config_ok_init_conf
  |> REWRITE_RULE[cake_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH arm8_asl_machine_config_ok)
                     (UNDISCH arm8_asl_init_ok))
  |> DISCH(#1(dest_imp(concl arm8_asl_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

Theorem cake_compiled_asl_thm =
  CONJ compile_correct_applied_asl cake_output
  |> DISCH_ALL

(* --- *)

Theorem mk_compiler_fun_from_ci_tuple[local]:
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
        GSYM compiler64ReplProofTheory.compiler_inst_def];

Overload init_eval_state_for =
  “λext cl fs. (init_state (basis_ffi ext cl fs) with
        eval_state := SOME (mk_init_eval_state compiler_instance))”

Theorem candle_soundness:
  res ∈ semantics_prog (init_eval_state_for ext cl fs) init_env (candle_code ++ prog) ∧
  EVERY safe_dec prog ∧ prog_syntax_ok candle_code ∧ res ≠ Fail
  ⇒
  ∀e. e ∈ events_of res ⇒ ok_event e
Proof
  rw [IN_DEF]
  \\ drule_then irule events_of_semantics_with_eval_state
  \\ fs [IN_DEF]
  \\ simp [basis_ffiTheory.basis_ffi_def]
  \\ fs [candle_prover_invTheory.eval_state_ok_def,mk_init_eval_state_lemma]
  \\ fs [source_evalProofTheory.v_rel_abs]
  \\ rpt gen_tac
  \\ DEEP_INTRO_TAC some_intro
  \\ fs [repl_decs_allowedTheory.decs_allowed_def,IN_DEF]
QED

Theorem repl_not_fail =
  semantics_prog_compiler64_arm8_prog
  |> Q.GEN ‘s’ |> ISPEC (mk_init_eval_state_lemma |> concl |> rand |> rand)
  |> REWRITE_RULE [GSYM mk_init_eval_state_lemma]
  |> SIMP_RULE (srw_ss()) [IN_DEF]
  |> Q.GEN ‘conf’ |> Q.SPEC ‘info’
  |> REWRITE_RULE [GSYM (SIMP_CONV (srw_ss()) [] “hasFreeFD fs”)];

Overload basis_init_ok =
  “λcl fs. STD_streams fs ∧ wfFS fs ∧ wfcl cl ∧ hasFreeFD fs ∧
           file_content fs «config_enc_str.txt» = SOME conf”;

Theorem repl_not_fail_thm:
  has_repl_flag (TL cl) ∧ basis_init_ok cl fs ⇒
  Fail ∉ semantics_prog (init_eval_state_for ext cl fs) init_env compiler64_arm8_prog
Proof
  rw [IN_DEF] \\ irule repl_not_fail \\ fs []
  \\ simp [compiler64_compiled]
QED

val compile_correct_applied2 =
  MATCH_MP compile_correct_eval (cj 1 compiler64_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,
                         GSYM AND_IMP_INTRO,with_clos_conf_simp]
  |> Q.INST [‘ev’|->‘SOME compiler_instance’]
  |> SIMP_RULE (srw_ss()) [add_eval_state_def,opt_eval_config_wf_def,
      arm8_configProofTheory.arm8_backend_config_ok,compiler_instance_lemma]
  |> Q.GEN ‘ffi’ |> Q.ISPEC ‘basis_ffi ext cl fs’

Definition repl_ready_to_run_def:
  repl_ready_to_run cl fs (mc,ms) ⇔
    ∃cbspace data_sp.
      has_repl_flag (TL cl) ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧
      hasFreeFD fs ∧
      file_content fs «config_enc_str.txt» = SOME conf ∧
      is_arm8_asl_machine_config mc ∧
      installed code cbspace data data_sp
        info.lab_conf.ffi_names
        (heap_regs arm8_backend_config.stack_conf.reg_names)
        mc info.lab_conf.shmem_extra ms
End

Overload machine_sem = “λffi (mc,ms). targetSem$machine_sem mc ffi ms”

Theorem compile_correct_applied:
  Fail ∉ semantics_prog (init_eval_state_for ext cl fs) init_env compiler64_arm8_prog ∧
  repl_ready_to_run cl fs ms ⇒
  machine_sem (basis_ffi ext cl fs) ms ⊆
    extend_with_resource_limit
      (semantics_prog (init_eval_state_for ext cl fs) init_env compiler64_arm8_prog)
Proof
  PairCases_on ‘ms’ \\ rw [IN_DEF,repl_ready_to_run_def]
  \\ irule compile_correct_applied2 \\ fs []
  \\ ‘init_conf.stack_conf.reg_names =
      arm8_backend_config.stack_conf.reg_names’ by EVAL_TAC
  \\ gvs [] \\ first_x_assum $ irule_at Any
  \\ gvs [backend_config_ok_init_conf,mc_init_ok_init_conf,
          arm8_asl_machine_config_ok,arm8_asl_init_ok]
QED

Theorem isPREFIX_MEM[local]:
  ∀xs ys. isPREFIX xs ys ⇒ ∀x. MEM x xs ⇒ MEM x ys
Proof
  Induct \\ fs [] \\ Cases_on ‘ys’ \\ fs [] \\ metis_tac []
QED

Theorem LPREFIX_MEM[local]:
  ∀xs ys. LPREFIX (fromList xs) ys ⇒ ∀x. MEM x xs ⇒ x IN LSET ys
Proof
  Induct \\ fs [] \\ Cases_on ‘ys’ \\ fs []
  \\ fs [LPREFIX_LCONS] \\ metis_tac []
QED

Theorem repl_ready_to_run_imp:
  repl_ready_to_run cl fs ms ⇒
  has_repl_flag (TL cl) ∧ basis_init_ok cl fs
Proof
  PairCases_on ‘ms’ \\ rw [repl_ready_to_run_def] \\ fs []
QED

Theorem prog_syntax_ok_candle_code[local]:
  prog_syntax_ok candle_code
Proof
  ‘prog_syntax_ok compiler64_arm8_prog’ by fs [compiler64_compiled]
  \\ irule ml_progTheory.prog_syntax_ok_isPREFIX
  \\ first_x_assum $ irule_at Any
  \\ strip_assume_tac compiler64_arm8_prog_eq_candle_code_append
  \\ gvs []
QED

Theorem events_of_extend_with_resource_limit:
  e ∈ events_of res1 ∧ res1 ∈ sem1 ∧
  sem1 ⊆ extend_with_resource_limit sem2 ⇒
  ∃res2. e ∈ events_of res2 ∧ res2 ∈ sem2
Proof
  fs [IN_DEF,SUBSET_DEF,extend_with_resource_limit_def] \\ rw []
  \\ first_x_assum drule \\ fs [] \\ rw []
  \\ first_assum $ irule_at Any \\ fs [events_of_def]
  \\ imp_res_tac isPREFIX_MEM \\ fs [IN_DEF]
  \\ imp_res_tac LPREFIX_MEM \\ fs [IN_DEF]
QED

Theorem candle_top_level_soundness:
  repl_ready_to_run cl fs ms ∧ res ∈ machine_sem (basis_ffi ext cl fs) ms ⇒
  res ≠ Fail ∧
  ∀e. e ∈ events_of res ⇒ ok_event e
Proof
  strip_tac
  \\ drule_all_then strip_assume_tac repl_ready_to_run_imp
  \\ imp_res_tac repl_not_fail_thm
  \\ first_x_assum $ qspec_then ‘ext’ assume_tac
  \\ drule_all compile_correct_applied
  \\ strip_tac
  \\ ‘res ≠ Fail’ by
   (CCONTR_TAC \\ gvs [IN_DEF,extend_with_resource_limit_def,SUBSET_DEF]
    \\ first_x_assum drule \\ fs [])
  \\ rw []
  \\ drule_all events_of_extend_with_resource_limit \\ rw []
  \\ strip_assume_tac compiler64_arm8_prog_eq_candle_code_append \\ gvs []
  \\ drule_then irule candle_soundness
  \\ fs [prog_syntax_ok_candle_code] \\ CCONTR_TAC \\ fs []
QED

(* Every byte string the kernel writes on its own channel decodes back to the
   theorem and the context it was proved in, and that context extends the
   initial one. So a reader of the channel can decide the shape of the context
   and, when it is one of the shapes a HOL Light session builds, conclude that
   the theory the theorem lives in is consistent. *)

Theorem candle_top_level_consistency_axiom_free:
  repl_ready_to_run cl fs ms ∧ res ∈ machine_sem (basis_ffi ext cl fs) ms ⇒
  res ≠ Fail ∧
  ∀out y. IO_event (ExtCall kernel_ffi) out y ∈ events_of res ⇒
    ∃ctxt th.
      THM ctxt th ∧ thm2bytes ctxt th = out ∧
      string_to_thm (bytes2str out) = (ctxt,th) ∧
      ctxt extends init_ctxt ∧
      (axiom_free ctxt ⇒ consistent_theory (thyof ctxt))
Proof
  strip_tac
  \\ drule_all candle_top_level_soundness
  \\ strip_tac \\ simp []
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ simp [candle_kernel_valsTheory.ok_event_def]
  \\ strip_tac
  \\ first_assum $ irule_at Any
  \\ gvs [candle_kernel_valsTheory.bytes2str_thm2bytes,
          print_thmTheory.string_to_thm_thm_to_string]
  \\ strip_tac
  \\ irule init_light_consistent \\ gs []
QED

Theorem candle_top_level_consistency_fhol_light:
  repl_ready_to_run cl fs ms ∧ res ∈ machine_sem (basis_ffi ext cl fs) ms ⇒
  res ≠ Fail ∧
  ∀out y. IO_event (ExtCall kernel_ffi) out y ∈ events_of res ⇒
    ∃ctxt th.
      THM ctxt th ∧ thm2bytes ctxt th = out ∧
      string_to_thm (bytes2str out) = (ctxt,th) ∧
      ctxt extends init_ctxt ∧
      (fhol_light_ctxt ctxt ⇒ consistent_theory (thyof ctxt))
Proof
  strip_tac
  \\ drule_all candle_top_level_soundness
  \\ strip_tac \\ simp []
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ simp [candle_kernel_valsTheory.ok_event_def]
  \\ strip_tac
  \\ first_assum $ irule_at Any
  \\ gvs [candle_kernel_valsTheory.bytes2str_thm2bytes,
          print_thmTheory.string_to_thm_thm_to_string]
  \\ strip_tac
  \\ irule fhol_light_consistent \\ gs []
QED

Theorem candle_top_level_consistency_hol_light:
  repl_ready_to_run cl fs ms ∧ res ∈ machine_sem (basis_ffi ext cl fs) ms ⇒
  res ≠ Fail ∧
  ∀out y. IO_event (ExtCall kernel_ffi) out y ∈ events_of res ⇒
    ∃ctxt th.
      THM ctxt th ∧ thm2bytes ctxt th = out ∧
      string_to_thm (bytes2str out) = (ctxt,th) ∧
      ctxt extends init_ctxt ∧
      (hol_light_ctxt ctxt ∧ (∃inf. is_infinite V_mem inf) ⇒
         consistent_theory (thyof ctxt))
Proof
  strip_tac
  \\ drule_all candle_top_level_soundness
  \\ strip_tac \\ simp []
  \\ rpt strip_tac
  \\ first_x_assum drule
  \\ simp [candle_kernel_valsTheory.ok_event_def]
  \\ strip_tac
  \\ first_assum $ irule_at Any
  \\ gvs [candle_kernel_valsTheory.bytes2str_thm2bytes,
          print_thmTheory.string_to_thm_thm_to_string]
  (* keep the existential intact: hol_light_consistent's hypothesis is where
     the set-theory universe type gets fixed, and the conclusion does not
     mention it *)
  \\ disch_then (CONJUNCTS_THEN assume_tac)
  \\ drule_then irule hol_light_consistent \\ gs []
QED

val _ = print "Checking that no cheats were used in the proofs.\n";
val _ = candle_top_level_soundness |> check_thm;
val _ = candle_top_level_consistency_axiom_free |> check_thm;
val _ = candle_top_level_consistency_fhol_light |> check_thm;
val _ = candle_top_level_consistency_hol_light |> check_thm;
val _ = cake_compiled_thm |> check_thm;
val _ = cake_compiled_asl_thm |> check_thm;

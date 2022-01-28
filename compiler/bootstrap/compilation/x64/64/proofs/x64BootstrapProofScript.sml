(*
  Proves an end-to-end correctness theorem for the bootstrapped compiler.
*)
open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     compiler64ProgTheory x64BootstrapTheory replProofTheory
     candle_prover_semanticsTheory

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

Theorem cake_compiled_thm =
  CONJ compile_correct_applied cake_output
  |> DISCH_ALL
(*  |> check_thm;  *)

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

Overload config_env_str = “encode_backend_config (config_to_inc_config cake_config)”

Theorem repl_not_fail =
  semantics_prog_compiler64_prog
  |> Q.GEN ‘s’ |> ISPEC (mk_init_eval_state_lemma |> concl |> rand |> rand)
  |> REWRITE_RULE [GSYM mk_init_eval_state_lemma]
  |> SIMP_RULE (srw_ss()) [IN_DEF]
  |> Q.INST [‘conf’|->‘config_to_inc_config cake_config’]
  |> REWRITE_RULE [GSYM (SIMP_CONV (srw_ss()) [] “hasFreeFD fs”)];

val compile_correct_applied2 =
  MATCH_MP compile_correct_eval cake_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO,
                         with_clos_conf_simp]
  |> Q.INST [‘ev’|->‘SOME compiler_instance’]
  |> SIMP_RULE (srw_ss()) [add_eval_state_def,opt_eval_config_wf_def,
      x64_configProofTheory.x64_backend_config_ok,compiler_instance_lemma]
  |> Q.GEN ‘ffi’ |> Q.ISPEC ‘basis_ffi cl fs’

Definition repl_ready_to_run_def:
  repl_ready_to_run cl fs (mc,ms) ⇔
    ∃cbspace data_sp.
      has_repl_flag (TL cl) ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ∧
      hasFreeFD fs ∧
      file_content fs «config_enc_str.txt» = SOME config_env_str ∧
      mc_conf_ok mc ∧ mc_init_ok x64_backend_config mc ∧
      installed cake_code cbspace cake_data data_sp
        cake_config.lab_conf.ffi_names (basis_ffi cl fs)
        (heap_regs x64_backend_config.stack_conf.reg_names) mc ms
End

Overload machine_sem = “λffi (mc,ms). targetSem$machine_sem mc ffi ms”

Triviality isPREFIX_MEM:
  ∀xs ys. isPREFIX xs ys ⇒ ∀x. MEM x xs ⇒ MEM x ys
Proof
  Induct \\ fs [] \\ Cases_on ‘ys’ \\ fs [] \\ metis_tac []
QED

Triviality LPREFIX_MEM:
  ∀xs ys. LPREFIX (fromList xs) ys ⇒ ∀x. MEM x xs ⇒ x IN LSET ys
Proof
  Induct \\ fs [] \\ Cases_on ‘ys’ \\ fs []
  \\ fs [LPREFIX_LCONS] \\ metis_tac []
QED

val _ = (max_print_depth := 12)

Definition safe_dec'_def:
  safe_dec' (Dlet locs pat x) = safe_exp x ∧
  safe_dec' (Dletrec locs' funs) = EVERY safe_exp (MAP (SND ∘ SND) funs) ∧
  safe_dec' _ = T
End

Theorem safe_dec_thm:
  safe_dec = every_dec safe_dec'
Proof
  fs [candle_prover_invTheory.safe_dec_def]
  \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM]
  \\ Cases
  \\ fs [safe_dec'_def]
QED

Definition safe_exp'_def:
  (safe_exp' (Con (SOME i) _) = (id_to_n i ∉ kernel_ctors)) ∧
  (safe_exp' (App (FFI n) _) = (n ≠ kernel_ffi)) ∧
  (safe_exp' _ = T)
End

Theorem safe_exp_thm:
  safe_exp = every_exp safe_exp'
Proof
  fs [candle_prover_invTheory.safe_exp_def]
  \\ AP_TERM_TAC
  \\ fs [FUN_EQ_THM]
  \\ Cases
  \\ fs [safe_exp'_def]
  \\ rw [] \\ Cases_on ‘o'’ \\ fs [safe_exp'_def]
QED

Triviality MAP_SND:
  MAP SND [] = [] ∧
  MAP SND ((x1,x2)::xs) = x2 :: MAP SND xs
Proof
  fs []
QED

Triviality MAP_SND_SND:
  MAP (SND ∘ SND) [] = [] ∧
  MAP (SND ∘ SND) ((x1,x2,x3)::xs) = x3 :: MAP (SND ∘ SND) xs
Proof
  fs []
QED

local
  fun cross [] xs = []
    | cross (y::ys) xs = map (fn x => (y,x)) xs @ cross ys xs;
  val cs = List.tabulate(256,(fn n => stringSyntax.mk_chr(numSyntax.term_of_int n)))
in
  val char_eq_lemmas = cross cs cs |> map mk_eq |> map EVAL;
end

Theorem candle_top_level_soundness:
  repl_ready_to_run cl fs ms ∧ machine_sem (basis_ffi cl fs) ms res ⇒
  res ≠ Fail ∧
  ∀e. e IN events_of res ⇒ ok_event e
Proof
  PairCases_on ‘ms’ \\ rewrite_tac [repl_ready_to_run_def]
  \\ strip_tac
  \\ mp_tac repl_not_fail
  \\ impl_tac >- fs []
  \\ strip_tac
  \\ drule_all compile_correct_applied2
  \\ fs [SUBSET_DEF,extend_with_resource_limit_def]
  \\ strip_tac
  \\ ‘res ≠ Fail’ by
   (CCONTR_TAC \\ gvs [IN_DEF]
    \\ first_x_assum drule \\ fs [])
  \\ rw []
  \\ ‘∃res1.
        semantics_prog
          (init_state (basis_ffi cl fs) with
           eval_state := SOME (mk_init_eval_state compiler_instance))
          init_env compiler64_prog res1 ∧
        e ∈ events_of res1 ∧ res1 ≠ Fail’ by
   (fs [IN_DEF]
    \\ first_x_assum drule \\ fs [] \\ rw []
    \\ first_assum $ irule_at Any \\ fs [events_of_def]
    \\ imp_res_tac isPREFIX_MEM \\ fs [IN_DEF]
    \\ imp_res_tac LPREFIX_MEM \\ fs [IN_DEF])
  \\ qsuff_tac ‘∃prog. compiler64_prog = candle_code ++ prog ∧ EVERY safe_dec prog’
  >-
   (strip_tac \\ gvs []
    \\ drule events_of_semantics_with_eval_state
    \\ disch_then irule \\ fs []
    \\ simp [basis_ffiTheory.basis_ffi_def]
    \\ fs [candle_prover_invTheory.eval_state_ok_def,mk_init_eval_state_lemma]
    \\ fs [source_evalProofTheory.v_rel_abs]
    \\ rpt gen_tac
    \\ DEEP_INTRO_TAC some_intro
    \\ fs [repl_decs_allowedTheory.decs_allowed_def,IN_DEF])
  \\ qexists_tac ‘DROP (LENGTH candle_code) compiler64_prog’
  \\ once_rewrite_tac [candle_kernelProgTheory.candle_code_def]
  \\ rewrite_tac [LENGTH]
  \\ once_rewrite_tac [compiler64_prog_def]
  \\ PURE_REWRITE_TAC [rich_listTheory.DROP]
  \\ rewrite_tac [APPEND]
  \\ rewrite_tac [safe_dec_thm,EVERY_DEF,safe_dec'_def,MAP_SND_SND,
                  safe_exp_thm,safe_exp'_def,MAP_SND,namespaceTheory.id_to_n_def,
                  ast_extrasTheory.every_exp_def
                    |> CONV_RULE (DEPTH_CONV ETA_CONV),
                  ast_extrasTheory.every_dec_def
                    |> CONV_RULE (DEPTH_CONV ETA_CONV)]
  \\ rewrite_tac [EVAL “"[]" ∉ kernel_ctors”, EVAL “"::" ∉ kernel_ctors”]
  \\ rewrite_tac
       ([EVAL “kernel_ctors”,CONS_11,NOT_CONS_NIL,NOT_NIL_CONS,
           IN_INSERT,NOT_IN_EMPTY,EVAL “kernel_ffi”] @ char_eq_lemmas)
QED

val _ = export_theory();

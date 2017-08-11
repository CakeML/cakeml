open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     compiler_x64ProgTheory x64BootstrapTheory

val _ = new_theory"x64BootstrapProof";

val cake_io_events_def = new_specification("cake_io_events_def",["cake_io_events"],
  semantics_entire_program
  |> CONV_RULE(RENAME_VARS_CONV["inp","fs","cl"])
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["inp","cl","fs"]))
  |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (cake_sem,cake_output) = cake_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (cake_not_fail,cake_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail cake_sem |> CONJ_PAIR

(* TODO: move *)
val backend_config_ok_with_bvl_conf_updated = Q.store_thm("backend_config_ok_with_bvl_conf_updated[simp]",
  `backend_config_ok (cc with bvl_conf updated_by f) ⇔ backend_config_ok cc`,
  rw[backend_config_ok_def]);
val backend_config_ok_with_word_to_word_conf_updated = Q.store_thm("backend_config_ok_with_word_to_word_conf_updated[simp]",
  `backend_config_ok (cc with word_to_word_conf updated_by f) ⇔ backend_config_ok cc`,
  rw[backend_config_ok_def]);
val mc_init_ok_with_bvl_conf_updated = Q.store_thm("mc_init_ok_with_bvl_conf_updated[simp]",
  `mc_init_ok (cc with bvl_conf updated_by f) mc ⇔ mc_init_ok cc mc`,
  rw[mc_init_ok_def]);
val mc_init_ok_with_word_to_word_conf_updated = Q.store_thm("mc_init_ok_with_word_to_word_conf_updated[simp]",
  `mc_init_ok (cc with word_to_word_conf updated_by f) mc ⇔ mc_init_ok cc mc`,
  rw[mc_init_ok_def]);
(* -- *)

val compile_correct_applied =
  MATCH_MP compile_correct cake_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP cake_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[cake_sem_sing]

val cake_compiled_thm =
  CONJ compile_correct_applied cake_output
  |> DISCH_ALL
  |> curry save_thm "cake_compiled_thm";

(* TODO: compose this with a correctness theorem for compiler_x64? *)

val _ = export_theory();

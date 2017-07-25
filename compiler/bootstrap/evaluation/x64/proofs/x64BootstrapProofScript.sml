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

(* TODO: this might be better done in x64BootstrapTheory *)
val cake_bytes_def = mk_abbrev "cake_bytes" (bootstrap_thm |> compilationLib.extract_bytes_ffis |> #1)
val cake_compiled = bootstrap_thm |> PURE_REWRITE_RULE[GSYM cake_bytes_def]

(* TODO: move *)
val conf_ok_with_bvl_conf_updated = Q.store_thm("conf_ok_with_bvl_conf_updated[simp]",
  `conf_ok (cc with bvl_conf updated_by f) mc ⇔ conf_ok cc mc`,
  rw[conf_ok_def,lower_conf_ok_def]);

val compile_correct_applied =
  MATCH_MP compile_correct cake_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP x64_conf_ok
  |> C MATCH_MP cake_not_fail
  |> REWRITE_RULE[cake_sem_sing]

val cake_compiled_thm =
  CONJ compile_correct_applied cake_output
  |> DISCH_ALL
  |> curry save_thm "cake_compiled_thm";

(* TODO: compose this with a correctness theorem for compiler_x64? *)

val _ = export_theory();

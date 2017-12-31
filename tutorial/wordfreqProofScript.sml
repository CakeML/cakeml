open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     wordfreqProgTheory wordfreqCompileTheory

val _ = new_theory"wordfreqProof";

val wordfreq_io_events_def = new_specification("wordfreq_io_events_def",["wordfreq_io_events"],
  wordfreq_semantics |> Q.GENL[`fs`,`pname`,`fname`(*,`contents`*)]
  |> SIMP_RULE bool_ss [SKOLEM_THM,Once(GSYM RIGHT_EXISTS_IMP_THM),RIGHT_EXISTS_AND_THM]);

val (wordfreq_sem,wordfreq_output) = wordfreq_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR
val (wordfreq_not_fail,wordfreq_sem_sing) = MATCH_MP semantics_prog_Terminate_not_Fail wordfreq_sem |> CONJ_PAIR

val compile_correct_applied =
  MATCH_MP compile_correct wordfreq_compiled
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP wordfreq_not_fail
  |> C MATCH_MP x64_backend_config_ok
  |> REWRITE_RULE[wordfreq_sem_sing,AND_IMP_INTRO]
  |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
  |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
  |> DISCH(#1(dest_imp(concl x64_init_ok)))
  |> REWRITE_RULE[AND_IMP_INTRO]

val wordfreq_compiled_lemma =
  CONJ compile_correct_applied wordfreq_output
  |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> DISCH_ALL;

val compiler_output_def = Define `
  compiler_output = (code,data,config)`;

(* TODO: move  *)

val get_file_contents_def = Define `
  get_file_contents fs fname =
    if inFS_fname fs (File fname) then
      case ALOOKUP fs.files (File fname) of
      | NONE => NONE
      | SOME s => SOME (implode s)
    else NONE`

val wfFS_def = Define `
  wfFS fs <=> fsFFIProps$wfFS fs ∧ STD_streams fs`;

val x64_installed_def = Define `
  x64_installed (c,d,conf) ffi mc ms <=>
    is_x64_machine_config mc ∧
    backendProof$installed c d conf.ffi_names ffi
      (heap_regs x64_backend_config.stack_conf.reg_names) mc ms`

(* -- *)

val wordfreq_compiled_thm = store_thm("wordfreq_compiled_thm",
  ``wfcl [pname; fname] ∧ wfFS fs ∧ hasFreeFD fs ∧
    (get_file_contents fs fname = SOME file_contents) ∧
    x64_installed compiler_output (basis_ffi [pname; fname] fs) mc ms ⇒
    ∃io_events ascii_output ll.
      machine_sem mc (basis_ffi [pname; fname] fs) ms ⊆
      extend_with_resource_limit {Terminate Success io_events} ∧
      (extract_fs fs io_events = SOME (add_stdout fs ascii_output with numchars := ll)) ∧
      valid_wordfreq_output file_contents ascii_output``,
  strip_tac
  \\ assume_tac wordfreq_compiled_lemma
  \\ rfs [get_file_contents_def,wfFS_def,compiler_output_def,x64_installed_def]
  \\ asm_exists_tac \\ fs []
  \\ FULL_CASE_TAC \\ fs []
  \\ qexists_tac `wordfreq_output_spec file_contents` \\ fs []
  \\ qexists_tac `ll`
  \\ rveq \\ fs [wordfreqProgTheory.wordfreq_output_spec_def]);

val _ = export_theory();

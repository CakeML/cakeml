(*
  Constructs the end-to-end correctness theorem for wordfreq example
  by composing the application-specific correctness theorem, the
  compiler evaluation theorem and the compiler correctness theorem.
*)
Theory wordfreqProof
Ancestors
  semanticsProps backendProof x64_configProof wordfreqProg
  wordfreqCompile
Libs
  preamble

val wordfreq_terminate = UNDISCH_ALL (SPEC_ALL wordfreq_semantics)
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [wordfreq_compiled];

val wordfreq_compiled_lemma =
  MATCH_MP compile_correct (cj 1 wordfreq_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 wordfreq_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 wordfreq_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (UNDISCH is_x64_machine_config_IMP)
  |> SRULE [SF CONJ_ss] |> CONJUNCT2 |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC];

Definition compiler_output_def:
  compiler_output = (code,data,info)
End

(* TODO: move  *)

Definition get_file_contents_def:
  get_file_contents fs fname =
    if inFS_fname fs fname then
      case ALOOKUP fs.files fname of
      | NONE => NONE
      | SOME ino =>
          case ALOOKUP fs.inode_tbl (File ino) of
          | NONE => NONE
          | SOME s => SOME (implode s)
    else NONE
End

Definition wfFS_def:
  wfFS fs <=> fsFFIProps$wfFS fs ∧ STD_streams fs
End

Definition x64_installed_def:
  x64_installed (c,d,conf) cbspace data_sp mc ms <=>
    is_x64_machine_config mc ∧
    targetSem$installed c cbspace d data_sp conf.lab_conf.ffi_names
      (heap_regs x64_backend_config.stack_conf.reg_names) mc conf.lab_conf.shmem_extra ms
End

(* -- *)

Theorem wordfreq_compiled_thm:
   wfcl [pname; fname] ∧ wfFS fs ∧ hasFreeFD fs ∧
    (get_file_contents fs fname = SOME file_contents) ∧
    x64_installed compiler_output cbspace data_sp mc ms ⇒
    ∃io_events ascii_output.
      machine_sem mc (basis_ffi ext [pname; fname] fs) ms ⊆
      extend_with_resource_limit {Terminate Success io_events} ∧
      (extract_fs ext ([pname; fname],fs) io_events = SOME (add_stdout fs ascii_output)) ∧
      valid_wordfreq_output file_contents ascii_output
Proof
  strip_tac
  \\ assume_tac wordfreq_compiled_lemma
  \\ rfs [get_file_contents_def,wfFS_def,x64_installed_def,compiler_output_def]
  \\ asm_exists_tac \\ fs [option_case_eq]
  \\ metis_tac [wordfreqProgTheory.wordfreq_output_spec_def]
QED


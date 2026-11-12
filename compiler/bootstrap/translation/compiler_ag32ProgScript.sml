(*
  Native AG32 batch entry point for the compiler.
*)
Theory compiler_ag32Prog[no_sig_docs]
Ancestors
  compiler_commonProg basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];
val _ = translation_extends "compiler_commonProg";
val _ = ml_translatorLib.use_sub_check true;
val _ = use_long_names := true;

Quote add_cakeml:
  fun main u =
    let
      val cl = CommandLine.arguments ()
    in
      if compiler_common_has_help_flag cl then
        print compiler_help_string
      else if compiler_common_has_version_flag cl then
        print compiler_current_build_info_str
      else
        case compiler_compile_main cl (String.explode (TextIO.inputAll (TextIO.openStdIn ()))) of
          (c,e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                     compiler_commonprog_nonzero_exit_code_for_error_msg e)
    end
End

val main_v_def = fetch "-" "main_v_def";
val compiler_help_string_v_thm = compiler_commonProgTheory.compiler_help_string_v_thm;
val compiler_current_build_info_str_v_thm = compiler_commonProgTheory.compiler_current_build_info_str_v_thm;

Theorem main_spec:
   IS_SOME (stdin_content fs) ⇒
   app (p:'ffi ffi_proj) main_v
     [Conv NONE []] (STDIO fs * COMMANDLINE cl)
     (POSTv uv.
       &UNIT_TYPE () uv
       * STDIO (full_compile (TL cl) (get_stdin fs) fs)
       * COMMANDLINE cl)
Proof
  strip_tac
  \\ xcf_with_def main_v_def
  \\ xlet_auto
  >- (xcon \\ xsimpl)
  \\ xlet_auto
  >- (
    CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `cl`
    \\ xsimpl)
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  \\ reverse(Cases_on`∃inp pos. stdin fs inp pos`)
  >- (
    fs[STDIO_def,IOFS_def] \\ xpull \\ fs[stdin_def]
    \\ `F` suffices_by fs[]
    \\ fs[wfFS_def,STD_streams_def,MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]
    \\ fs[EXISTS_PROD]
    \\ metis_tac[ALOOKUP_FAILS,ALOOKUP_MEM,NOT_SOME_NONE,SOME_11,
                 PAIR_EQ,option_CASES])
  \\ fs[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ simp[FORALL_PROD,EXISTS_PROD]
  \\ conj_tac >- metis_tac []
  \\ rw[]
  \\ imp_res_tac stdin_11 \\ rw[]
  \\ imp_res_tac stdin_get_fd_content
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    simp [compilerTheory.full_compile_def]
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ irule_at (Pos hd) compiler_help_string_v_thm
    \\ qexists_tac `fs`
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    xapp
    \\ irule_at (Pos hd) compiler_current_build_info_str_v_thm
    \\ qexists_tac `fs`
    \\ simp [compilerTheory.full_compile_def]
    \\ xsimpl)
  \\ rename1 `stdin fs source_input stdin_position`
  \\ `stdin_content fs = SOME source_input /\ stdin_position = 0` by (
    gvs [stdin_def,get_fd_content_def]
    \\ fs [stdin_content_def,IS_SOME_EXISTS])
  \\ gvs []
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto_spec (SOME openStdIn_spec_str) >- xsimpl
  \\ xlet `POSTv v. &STRING_TYPE (implode source_input) v *
                   STDIO (fastForwardFD fs 0) * COMMANDLINE cl`
  >- (
    xapp
    \\ qexistsl_tac [`COMMANDLINE cl`,`source_input`,`fs`,`0`]
    \\ fs [STD_streams_get_mode]
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ namedCases_on `compiler$compile_main (TL cl) source_input`
       ["compiler_output compiler_diagnostics"]
  \\ gvs [compilerTheory.full_compile_def,ml_translatorTheory.PAIR_TYPE_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ qmatch_goalsub_abbrev_tac `STDIO output_fs`
  \\ xlet `POSTv uv. &UNIT_TYPE () uv *
                   STDIO (add_stderr output_fs compiler_diagnostics) *
                   COMMANDLINE cl`
  >- (
    xapp_spec output_stderr_spec
    \\ xsimpl
    \\ qexists_tac `COMMANDLINE cl`
    \\ asm_exists_tac \\ xsimpl
    \\ qexists_tac `output_fs` \\ xsimpl)
  \\ xapp
  \\ asm_exists_tac \\ simp [] \\ xsimpl
QED

Theorem main_whole_prog_spec:
  IS_SOME (stdin_content fs) ⇒
   whole_prog_spec main_v cl fs NONE
    ((=) (full_compile (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ simp [basis_ffiTheory.whole_prog_spec_def,UNCURRY]
  \\ qmatch_goalsub_abbrev_tac `output_fs = _ with numchars := _`
  \\ qexists_tac `output_fs`
  \\ reverse conj_tac
  >- (
    rw [Abbr `output_fs`,compilerTheory.full_compile_def,UNCURRY,
        GSYM fastForwardFD_with_numchars,
        GSYM add_stdo_with_numchars,with_same_numchars]
    \\ PURE_FULL_CASE_TAC
    \\ rw [GSYM fastForwardFD_with_numchars,
           GSYM add_stdo_with_numchars,with_same_numchars,UNCURRY])
  \\ simp [SEP_CLAUSES]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (UNDISCH main_spec)))
  \\ xsimpl
QED

val sem_thm = prove_sem_thm "main" "compiler_ag32_prog" main_whole_prog_spec;
val compiler_ag32_prog_def = fetch "-" "compiler_ag32_prog_def";

Theorem semantics_compiler_ag32_prog:
  IS_SOME (stdin_content fs) ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  sem_satisfies
    (semantics_dec_list
      (init_state (basis_ffi ext cl fs) with
       eval_state :=
         SOME (EvalDecs (eval_state_var with env_id_counter := (0,0,1))))
      init_env compiler_ag32_prog)
    (λbehaviour.
       ∃io_events.
         behaviour = Terminate Success io_events ∧
         extract_fs ext (cl,fs) io_events =
           SOME (full_compile (TL cl) (get_stdin fs) fs))
Proof
  strip_tac
  \\ irule sem_thm
  \\ fs []
QED

val _ = ml_translatorLib.reset_translation(); (* because this translation won't be continued *)

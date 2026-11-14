(*
  Shared command-line entry point for the Pancake compiler.
*)
Theory pancake_compilerProg[no_sig_docs]
Ancestors
  from_pancakeProg pancake_compiler compiler_common export ml_translator basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"];
val _ = translation_extends "from_pancakeProg";
val _ = ml_translatorLib.use_sub_check true;
val _ = use_long_names := true;

val _ = translate pancake_compilerTheory.error_to_str_def;
val _ = translate pancake_compilerTheory.compile_pancake_def;
val _ = translate pancake_compilerTheory.parse_target_def;
val _ = translate pancake_compilerTheory.extend_conf_def;
val _ = translate pancake_compilerTheory.parse_pancake_feature_def;
val _ = translate (newsTheory.query_news_def |> REWRITE_RULE [MEMBER_INTRO]);
val _ = translate pancake_compilerTheory.current_build_info_str_def;
val _ = translate pancake_compilerTheory.print_bool_def;
val _ = translate (pancake_compilerTheory.help_string_def
                   |> CONV_RULE (RAND_CONV EVAL));

val res = translate (pancake_compilerTheory.compile_main_def
                     |> REWRITE_RULE [MEMBER_INTRO]);
val _ = null (hyp res) orelse failwith "Unproved Pancake compiler side condition";

Definition nonzero_exit_code_for_error_msg_def:
  nonzero_exit_code_for_error_msg e =
    if compiler_common$is_error_msg e then
      (let a = empty_ffi «nonzero_exit» in
         ml_translator$force_out_of_memory_error ())
    else ()
End

val _ = translate nonzero_exit_code_for_error_msg_def;

Quote add_cakeml:
  fun main_target (native,u) =
    let val cl = CommandLine.arguments () in
      if compiler_common_has_help_flag cl then
        print pancake_compiler_help_string
      else if compiler_common_has_version_flag cl then
        print pancake_compiler_current_build_info_str
      else
        case pancake_compiler_parse_pancake_feature cl of
          Some feature => print (pancake_compiler_print_bool (news_query_news feature))
        | None =>
            case pancake_compiler_compile_main native cl
                   (String.explode (TextIO.inputAll (TextIO.openStdIn ()))) of
              (c,e) => (print_app_list c; TextIO.output TextIO.stdErr e;
                         pancake_compilerprog_nonzero_exit_code_for_error_msg e)
    end
End

val main_target_v_def = fetch "-" "main_target_v_def";

Theorem main_target_spec:
  PANCAKE_COMPILER_TARGET_TYPE native native_v /\
  IS_SOME (stdin_content fs) ==>
  app (p:'ffi ffi_proj) main_target_v
      [Conv NONE [native_v; Conv NONE []]] (STDIO fs * COMMANDLINE cl)
      (POSTv uv. &UNIT_TYPE () uv *
       STDIO (pancake_compiler$full_compile native (TL cl) (get_stdin fs) fs) *
       COMMANDLINE cl)
Proof
  rpt strip_tac
  \\ xcf_with_def main_target_v_def
  \\ xmatch
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto
  >- (
    qexistsl_tac [`STDIO fs`, `cl`]
    \\ xsimpl)
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [STDIO_def] \\ xpull)
  \\ reverse (Cases_on `?input position. stdin fs input position`)
  >- (
    fs [STDIO_def,IOFS_def] \\ xpull \\ fs [stdin_def]
    \\ `F` suffices_by fs []
    \\ fs [wfFS_def,STD_streams_def,MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]
    \\ fs [EXISTS_PROD]
    \\ metis_tac [ALOOKUP_FAILS,ALOOKUP_MEM,NOT_SOME_NONE,SOME_11,
                  PAIR_EQ,option_CASES])
  \\ qpat_x_assum `?input position. stdin fs input position`
    (qx_choosel_then [`input_chars`, `input_pos`] assume_tac)
  \\ `stdin_content fs = SOME input_chars /\ input_pos = 0` by (
    gvs [stdin_def,get_fd_content_def]
    \\ fs [stdin_content_def,IS_SOME_EXISTS])
  \\ gvs []
  \\ imp_res_tac stdin_get_stdin
  \\ imp_res_tac stdin_get_fd_content
  \\ gvs []
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    simp [pancake_compilerTheory.full_compile_def]
    \\ xapp
    \\ qexistsl_tac [`COMMANDLINE cl`, `pancake_compiler$help_string`, `fs`]
    \\ simp [fetch "-" "pancake_compiler_help_string_v_thm"]
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xif
  >- (
    simp [pancake_compilerTheory.full_compile_def]
    \\ xapp
    \\ qexistsl_tac [`COMMANDLINE cl`,
                     `pancake_compiler$current_build_info_str`, `fs`]
    \\ simp [fetch "-" "pancake_compiler_current_build_info_str_v_thm"]
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ reverse (namedCases_on `pancake_compiler$parse_pancake_feature (TL cl)`
       ["", "feature_name"])
  \\ gvs [oneline std_preludeTheory.OPTION_TYPE_def]
  >- (
    xmatch
    \\ xlet_auto >- xsimpl
    \\ xlet_auto >- xsimpl
    \\ simp [pancake_compilerTheory.full_compile_def]
    \\ xapp
    \\ qexistsl_tac [`COMMANDLINE cl`,
                     `pancake_compiler$print_bool (news$query_news feature_name)`,
                     `fs`]
    \\ xsimpl)
  \\ xmatch
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto_spec (SOME openStdIn_spec_str) >- xsimpl
  \\ xlet `POSTv v. &STRING_TYPE (implode (get_stdin fs)) v *
                  STDIO (fastForwardFD fs 0) * COMMANDLINE cl`
  >- (
    xapp
    \\ qexistsl_tac [`COMMANDLINE cl`, `get_stdin fs`, `fs`, `0`]
    \\ xsimpl)
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ namedCases_on `pancake_compiler$compile_main native (TL cl) (get_stdin fs)`
       ["compiler_output compiler_diagnostics"]
  \\ gvs [ml_translatorTheory.PAIR_TYPE_def]
  \\ simp [pancake_compilerTheory.full_compile_def]
  \\ xmatch
  \\ xlet_auto >- xsimpl
  \\ qmatch_goalsub_abbrev_tac `STDIO output_fs`
  \\ xlet `POSTv uv. &UNIT_TYPE () uv *
                   STDIO (add_stderr output_fs compiler_diagnostics) *
                   COMMANDLINE cl`
  >- (
    xapp_spec output_stderr_spec \\ xsimpl
    \\ qexists_tac `COMMANDLINE cl`
    \\ asm_exists_tac \\ xsimpl
    \\ qexists_tac `output_fs` \\ xsimpl)
  \\ xapp
  \\ asm_exists_tac \\ simp [] \\ xsimpl
QED

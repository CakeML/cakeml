open preamble
     compiler_x64Theory
     x64_configTheory export_x64Theory
     ml_translatorLib cfLib basis x64ProgTheory

val () = new_theory "compiler_x64Prog";

val () = translation_extends "x64Prog";

val res = translate x64_names_def;

val res = translate ffi_asm_def;
val res = translate x64_export_def;

val res = translate
  (x64_backend_config_def
   |> SIMP_RULE(srw_ss())[FUNION_FUPDATE_1])

val res = translate compiler_x64_def

val main = process_topdecs`
  fun main u =
    let
      val cl = CommandLine.arguments ()
    in
      if compiler_has_version_flag cl then
        TextIO.print_string compiler_current_build_info_str
      else
        case compiler_x64 cl (String.explode (TextIO.inputAll TextIO.stdIn))  of
          (c, e) => (print_app_list c; TextIO.prerr_string e)
    end`;

val res = append_prog main;

val st = get_ml_prog_state()

val full_compiler_x64_def = Define `
  full_compiler_x64 cl inp =
    if has_version_flag cl then
      (List [current_build_info_str], implode"", F)
    else
      let (a,b) = compiler_x64 cl inp in (a,b,T)`

val main_spec = Q.store_thm("main_spec",
  `app (p:'ffi ffi_proj) ^(fetch_v "main" st)
     [Conv NONE []] (STDIO fs * COMMANDLINE cl)
     (POSTv uv.
       &UNIT_TYPE () uv *
       (let (out,err,b) = full_compiler_x64 (TL (MAP implode cl)) (get_stdin fs) in
        let fs' = if b then fastForwardFD fs 0 else fs in
         STDIO (add_stderr (add_stdout fs' (explode (concat (append out)))) (explode err)))
      * COMMANDLINE cl)`,
  xcf "main" st
  \\ xlet_auto >- (xcon \\ xsimpl)
  \\ xlet_auto
  >- (
    (* TODO: xlet_auto: why doesn't xsimpl work here on its own? *)
    CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`cl`
    \\ xsimpl )
  \\ reverse(Cases_on`STD_streams fs`) >- (fs[STDIO_def] \\ xpull)
  (* TODO: it would be nice if this followed more directly.
           either (or both):
             - make STD_streams assert "stdin" is in the files
             - make wfFS separate from wfFS, so STDIO fs will imply wfFS fs *)
  \\ reverse(Cases_on`∃inp pos. stdin fs inp pos`)
  >- (
    fs[STDIO_def,IOFS_def] \\ xpull \\ fs[stdin_def]
    \\ `F` suffices_by fs[]
    \\ fs[wfFS_def,STD_streams_def,MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]
    \\ fs[EXISTS_PROD]
    \\ metis_tac[ALOOKUP_FAILS,ALOOKUP_MEM,NOT_SOME_NONE,SOME_11,PAIR_EQ,option_CASES] )
  \\ fs[get_stdin_def]
  \\ SELECT_ELIM_TAC
  \\ simp[FORALL_PROD,EXISTS_PROD]
  \\ conj_tac >- metis_tac[] \\ rw[]
  \\ imp_res_tac stdin_11 \\ rw[]
  \\ imp_res_tac stdin_get_file_content
  \\ xlet_auto >- xsimpl
  \\ xif
  >-
   (pairarg_tac \\ fs []
    \\ rfs [full_compiler_x64_def] \\ rw []
    \\ xapp
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `current_build_info_str`
    \\ fs [compilerTheory.current_build_info_str_def,
           compiler64ProgTheory.compiler_current_build_info_str_v_thm]
    \\ xsimpl
    \\ rename1 `add_stdout _ string`
    \\ fs [concat_def, explode_thm]
    \\ `!str. ?pos. stderr (add_stdout fs str) pos` by
      metis_tac [stdo_def, STD_streams_def, STD_streams_add_stdout]
    \\ pop_assum (qspec_then `string` strip_assume_tac)
    \\ imp_res_tac add_stdo_nil \\ xsimpl
    \\ qexists_tac `COMMANDLINE cl` \\ xsimpl
    \\ qexists_tac `fs` \\ xsimpl)
  \\ xlet_auto >- (xsimpl \\ metis_tac[stdin_v_thm,stdIn_def])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ fs [full_compiler_x64_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ fs[ml_translatorTheory.PAIR_TYPE_def]
  \\ xmatch
  (* TODO: xlet_auto: why does xlet_auto not work? *)
  \\ xlet_auto_spec(SOME (Q.SPEC`fastForwardFD fs 0`(Q.GEN`fs`basisProgTheory.print_app_list_spec)))
  >- xsimpl
  \\ xapp_spec output_stderr_spec
  \\ xsimpl
  \\ qmatch_goalsub_abbrev_tac`STDIO fs'`
  \\ CONV_TAC(RESORT_EXISTS_CONV List.rev)
  \\ qexists_tac`fs'` \\ xsimpl
  \\ instantiate
  \\ simp[Abbr`fs'`,mlstringTheory.concat_thm]
  \\ xsimpl);

val spec = main_spec |> UNDISCH_ALL |> SIMP_RULE (srw_ss())[STDIO_def,LET_THM,UNCURRY] |> add_basis_proj;
val name = "main"
val (semantics_thm,prog_tm) = call_thm st name spec;

val compiler_prog_def = Define`compiler_prog = ^prog_tm`;

val th =
  semantics_thm
  |> PURE_ONCE_REWRITE_RULE[GSYM compiler_prog_def]

val semantics_compiler_prog =
  th
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [STD_streams_add_stderr,STD_streams_add_stdout,STD_streams_fastForwardFD,
                           AND_IMP_INTRO,GSYM CONJ_ASSOC, full_compiler_x64_def]
  |> curry save_thm "semantics_compiler_prog";

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val () = export_theory();

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
      case compiler_x64 cl (String.explode (TextIO.inputAll TextIO.stdIn))  of
        (c, e) => (print_app_list c; TextIO.prerr_string e)
    end`;

val res = append_prog main;

val st = get_ml_prog_state()

val main_spec = Q.store_thm("main_spec",
  `app (p:'ffi ffi_proj) ^(fetch_v "main" st)
     [Conv NONE []] (STDIO fs * COMMANDLINE cl)
     (POSTv uv. &UNIT_TYPE () uv *
      (let (out,err) = compiler_x64 (TL(MAP implode cl)) (get_stdin fs) in
         STDIO (add_stderr (add_stdout (fastForwardFD fs 0) (explode (concat (append out)))) (explode err)))
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
  \\ xlet_auto >- (xsimpl \\ metis_tac[stdin_v_thm,stdIn_def])
  \\ xlet_auto >- xsimpl
  \\ xlet_auto >- xsimpl
  \\ pairarg_tac \\ fs[ml_translatorTheory.PAIR_TYPE_def]
  \\ xmatch
  (* TODO: xlet_auto: why does xlet_auto not work? *)
  \\ xlet_auto_spec(SOME (Q.SPEC`fastForwardFD fs 0`(Q.GEN`fs`basisProgTheory.print_app_list_spec)))
  >- xsimpl
  \\ xapp
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
                           AND_IMP_INTRO,GSYM CONJ_ASSOC]
  |> curry save_thm "semantics_compiler_prog";

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val () = export_theory();

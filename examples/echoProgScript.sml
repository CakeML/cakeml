open preamble basis

val _ = new_theory "echoProg";

val _ = translation_extends"basisProg";

val echo = process_topdecs
  `fun echo u =
      let
        val cl = CommandLine.arguments ()
        val cls = String.concatWith " " cl
        val ok = TextIO.print_string cls
      in TextIO.print_newline() end`;

val () = append_prog echo;

val st = get_ml_prog_state()

val echo_spec = Q.store_thm("echo_spec",
  `!fs ls b bv.
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDIO fs * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv *
      (STDIO (add_stdout fs (CONCAT_WITH " " (TL cl) ++ "\n"))) *
      COMMANDLINE cl)`,
  xcf "echo" st \\
  cases_on`¬ STD_streams fs` >-(fs[STDIO_def] >> xpull) >>
  xlet_auto >- (xcon \\ xsimpl) \\
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull) \\
  `¬NULL cl` by fs[wfcl_def] \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet`POSTv uv.  &UNIT_TYPE () uv * COMMANDLINE cl *
        STDIO (add_stdout fs ((explode (concatWith (strlit " ") (TL (MAP implode cl))))))`
  >- (xapp >> xsimpl >> instantiate >> xsimpl >>
      (* TODO: why? *)
      qexists_tac`COMMANDLINE cl` >> xsimpl >>
      qexists_tac`fs` >> xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xapp >> xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fs'` \\
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`fs'` \\
  unabbrev_all_tac \\
  simp[concatWith_CONCAT_WITH,MAP_TL,implode_def] \\
  xsimpl >> fs[] >>
  imp_res_tac STD_streams_stdout >>
  imp_res_tac add_stdo_o >> xsimpl);

val st = get_ml_prog_state();
val spec = echo_spec |> SPEC_ALL |> UNDISCH_ALL |>
            SIMP_RULE(srw_ss())[STDIO_def] |>
            add_basis_proj;
val name = "echo";
val (call_thm_echo, echo_prog_tm) = call_thm st name spec;
val echo_prog_def = Define`echo_prog = ^echo_prog_tm`;

val echo_semantics = save_thm("echo_semantics",
  call_thm_echo
  |> ONCE_REWRITE_RULE[GSYM echo_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE std_ss [LENGTH,APPEND,AND_IMP_INTRO,STD_streams_add_stdout,GSYM CONJ_ASSOC]);

val _ = export_theory();

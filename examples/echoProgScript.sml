open preamble ml_progLib ml_translatorLib
     basisFunctionsLib fsioProgLib
     cfTacticsLib cfLetAutoLib fsioConstantsProgTheory

val _ = new_theory "echoProg";

val _ = translation_extends"fsioProg";

val echo = process_topdecs
  `fun echo u =
      let
        val cl = Commandline.arguments ()
        val cls = String.concatwith " " cl
        val ok = IO.print_string cls
      in IO.print_newline() end`;

val () = append_prog echo;

val st = get_ml_prog_state()

val echo_spec = Q.store_thm("echo_spec",
  `!fs ls b bv.
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDIO fs * &stdout fs output * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv * 
      (STDIO (up_stdout (output ++ (CONCAT_WITH " " (TL cl)) ++ [CHR 10]) fs)) *
      COMMANDLINE cl)`,
  xcf "echo" st \\ xpull \\
  cases_on`¬ STD_streams fs` >-(fs[STDIO_def] >> xpull) >>
  xlet_auto >- (xcon \\ xsimpl) \\
  reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull) \\
  `¬NULL cl` by fs[mlcommandLineProgTheory.wfcl_def] \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet`POSTv uv.  &UNIT_TYPE () uv * COMMANDLINE cl *
        STDIO (up_stdout (output ++ (explode (concatWith (strlit " ") (TL (MAP implode cl)))))
               fs)`
  >- (xapp >> xsimpl >> instantiate >>  xsimpl) >>
  xlet_auto >- (xcon >> xsimpl) >>
  xapp >> xsimpl >> 
  qmatch_goalsub_abbrev_tac`up_stdout output'` \\
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`output'` \\
  qmatch_goalsub_abbrev_tac`STDIO fs'` \\
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`fs'` \\
  unabbrev_all_tac \\
  simp[mlstringTheory.concatWith_CONCAT_WITH,MAP_TL,mlstringTheory.implode_def] \\
  xsimpl >> fs[up_stdout_def] >>
  rw[] >- fs[stdout_def,up_stdout_def,fsFFITheory.fsupdate_def,ALIST_FUPDKEY_ALOOKUP] >>
  fs[GC_def] >> xsimpl >> qexists_tac`emp` >> xsimpl >>
  rw[STDIO_def,IOFS_def] >> 
  xsimpl >> rw[] >> qexists_tac`x` >>
  fs[fsFFIProofTheory.fsupdate_numchars] >>
  `liveFS (fs with numchars := x)` 
    by fs[fsFFIProofTheory.liveFS_def,fsFFITheory.fsupdate_def] >>
  rfs[fsFFIProofTheory.fsupdate_o] >> fs[fsFFIProofTheory.fsupdate_o] >> xsimpl >>
  irule STD_streams_fsupdate >> fs[STD_streams_fsupdate]);

val st = get_ml_prog_state();
val spec = echo_spec |> SPEC_ALL |> UNDISCH_ALL |> 
            SIMP_RULE(srw_ss())[fsioConstantsProgTheory.STDIO_def] |>
            add_basis_proj;
val name = "echo";
val (call_thm_echo, echo_prog_tm) = call_thm st name spec;
val echo_prog_def = Define`echo_prog = ^echo_prog_tm`;

val echo_semantics = save_thm("echo_semantics",
  call_thm_echo
  |> ONCE_REWRITE_RULE[GSYM echo_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE std_ss [APPEND]);

val _ = export_theory();

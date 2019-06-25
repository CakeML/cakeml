(*
  echo program example: print the command line arguments.
*)
open preamble basis

val _ = new_theory "echoProg";

val _ = translation_extends"basisProg";

val echo = process_topdecs
  `fun echo u =
      let
        val cl = CommandLine.arguments ()
        val cls = String.concatWith " " cl
        val ok = TextIO.print cls
      in TextIO.output1 TextIO.stdOut #"\n" end`;

val () = append_prog echo;

val st = get_ml_prog_state()

Theorem echo_spec:
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDIO fs * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv *
      (STDIO (add_stdout fs (concatWith (strlit" ") (TL cl) ^ (strlit"\n")))) *
      COMMANDLINE cl)
Proof
  xcf "echo" st \\
  cases_on`¬ STD_streams fs` >-(fs[STDIO_def] >> xpull) >>
  xlet_auto >- (xcon \\ xsimpl) \\
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull) \\
  `¬NULL cl` by fs[wfcl_def,NULL_EQ] \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet`POSTv uv.  &UNIT_TYPE () uv * COMMANDLINE cl *
        STDIO (add_stdout fs ((concatWith (strlit " ") (TL cl))))`
  >- (xapp >> xsimpl >> instantiate >> xsimpl >>
      (* TODO: why? *)
      qexists_tac`COMMANDLINE cl` >> xsimpl >>
      qexists_tac`fs` >> xsimpl) >>
  xapp_spec output1_stdout_spec >> xsimpl >>
  qmatch_goalsub_abbrev_tac`STDIO fs'` \\
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`fs'` \\
  unabbrev_all_tac \\
  xsimpl >> fs[] >>
  imp_res_tac STD_streams_stdout >>
  simp[str_def,implode_def] >>
  imp_res_tac add_stdo_o >> xsimpl
QED

Theorem echo_whole_prog_spec:
   whole_prog_spec ^(fetch_v "echo" st) cl fs NONE
    ((=) (add_stdout fs (concatWith (strlit" ") (TL cl) ^ (strlit"\n"))))
Proof
  rw[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe echo_spec))
  \\ xsimpl
QED

val (call_thm_echo, echo_prog_tm) = whole_prog_thm st "echo" echo_whole_prog_spec;
val echo_prog_def = Define`echo_prog = ^echo_prog_tm`;

val echo_semantics = save_thm("echo_semantics",
  call_thm_echo |> ONCE_REWRITE_RULE[GSYM echo_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]);

val _ = export_theory();

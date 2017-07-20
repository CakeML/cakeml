open preamble ml_progLib ml_translatorLib
     basisFunctionsLib ioProgLib
     cfTacticsLib cfLetAutoLib

val _ = new_theory "echoProg";

val _ = translation_extends"basisProg";

val echo = process_topdecs
  `fun echo u =
      let
        val cl = Commandline.arguments ()
        val cls = String.concatwith " " cl
        val ok = print cls
      in CharIO.write #"\n" end`;

val () = append_prog echo;

val st = get_ml_prog_state()

val echo_spec = Q.store_thm("echo_spec",
  `!ls b bv.
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDOUT output * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ (CONCAT_WITH " " (TL cl)) ++ [CHR 10]) * COMMANDLINE cl)`,
  xcf "echo" st \\
  xlet_auto >- (xcon \\ xsimpl) \\
  reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull) \\
  `¬NULL cl` by fs[mlcommandLineProgTheory.wfcl_def] \\
  xlet_auto >- xsimpl \\
  xlet_auto >- xsimpl \\
  xlet_auto >- (
    CONV_TAC SWAP_EXISTS_CONV \\
    qexists_tac`output` \\ xsimpl
  ) \\
  xapp \\ xsimpl \\
  qmatch_goalsub_abbrev_tac`STDOUT output'` \\
  CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`output'` \\
  simp[Abbr`output'`,mlstringTheory.concatWith_CONCAT_WITH,MAP_TL,mlstringTheory.implode_def] \\
  xsimpl
);

val st = get_ml_prog_state();
val spec = echo_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "echo";
val (call_thm_echo, echo_prog_tm) = call_thm st name spec;
val echo_prog_def = Define`echo_prog = ^echo_prog_tm`;

val echo_semantics = save_thm("echo_semantics",
  call_thm_echo
  |> ONCE_REWRITE_RULE[GSYM echo_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE std_ss [APPEND]);

val _ = export_theory();

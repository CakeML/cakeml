open  preamble ml_progLib ioProgLib ml_translatorLib
      cfTacticsLib

val _ = new_theory "echoProg";

val _ = translation_extends"ioProg";

(* This is the expected workflow for getting the semantics and the output of
  a program using basis_projs, basis_oracle and basis_ffi, as well as
  preparing it for compilation. Note that the main call should be of type
  unit->unit   *)

val echo = process_topdecs
  `fun echo u =
      let
        val cl = Commandline.arguments ()
        val cls = String.concatwith " " cl
        val ok = print cls
      in CharIO.write #"\n" end`

val res = ml_prog_update(ml_progLib.add_prog echo pick_name)

val st = get_ml_prog_state()

val echo_spec = Q.store_thm("echo_spec",
  `!ls b bv.
   app (p:'ffi ffi_proj) ^(fetch_v "echo" st) [Conv NONE []]
   (STDOUT output * COMMANDLINE cl)
   (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ (CONCAT_WITH " " (TL cl)) ++ [CHR 10]) * COMMANDLINE cl)`,
    xcf "echo" st
    \\ xlet `POSTv zv. & UNIT_TYPE () zv * STDOUT output * COMMANDLINE cl`
    >-(xcon \\ xsimpl)
    \\ reverse(Cases_on`wfcl cl`) >- (fs[mlcommandLineProgTheory.COMMANDLINE_def] \\ xpull)
    \\ `¬NULL cl` by fs[mlcommandLineProgTheory.wfcl_def]
    \\ xlet `POSTv argv. & LIST_TYPE STRING_TYPE (TL (MAP implode cl)) argv * STDOUT output
      * COMMANDLINE cl`
    >-(xapp \\ xsimpl \\
       CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac`cl` \\ xsimpl)
    \\ xlet `POSTv clv. STDOUT output * COMMANDLINE cl * & STRING_TYPE (implode (CONCAT_WITH " " (TL cl))) clv`
    >-(xapp \\ xsimpl \\ instantiate
      \\ rw[mlstringTheory.concatWith_CONCAT_WITH, mlstringTheory.implode_explode, Once mlstringTheory.implode_def]
      \\ Cases_on `cl` \\ fs[mlstringTheory.implode_def])
    \\ xlet `POSTv xv. &UNIT_TYPE () xv * STDOUT (output ++ (CONCAT_WITH " " (TL cl))) * COMMANDLINE cl`
    >-(xapp \\ qexists_tac `COMMANDLINE cl` \\ xsimpl \\ qexists_tac `implode (CONCAT_WITH " " (TL cl))` \\ qexists_tac `output`
      \\ rw[mlstringTheory.explode_implode] \\ xsimpl)
    \\ xapp \\ map_every qexists_tac [`COMMANDLINE cl`, `output ++ (CONCAT_WITH " " (TL cl))`, `(CHR 10)`] \\ xsimpl
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

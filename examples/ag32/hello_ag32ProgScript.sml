open preamble basis PrinterProofTheory

val _ = new_theory "hello_ag32Prog"

val _ = translation_extends"PrinterProg";

val hello = process_topdecs
  `fun hello u = Printer.print "Hello World!\n"`;

val () = append_prog hello

val st = get_ml_prog_state ()

val hello_spec = Q.store_thm ("hello_spec",
  ` app (p:'ffi ffi_proj) ^(fetch_v "hello" st)
        [Conv NONE []]
        (PRINTER out)
        (POSTv uv. &UNIT_TYPE () uv * PRINTER (out ++ "Hello World!\n"))`,
  xcf "hello" st \\ xapp \\ xsimpl
  \\ CONV_TAC SWAP_EXISTS_CONV
  \\ qexists_tac`out` \\ xsimpl);

(*
val hello_whole_prog_spec = Q.store_thm("hello_whole_prog_spec",
  `whole_prog_spec ^(fetch_v "hello" st) cl fs
    ((=) (add_stdout fs (strlit "Hello World!\n")))`,
  rw[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe hello_spec))
  \\ xsimpl);

val spec = hello_whole_prog_spec
val name = "hello";

val (call_thm_hello, hello_prog_tm) = whole_prog_thm st name spec;
val hello_prog_def = Define`hello_prog = ^hello_prog_tm`;

val hello_semantics = save_thm("hello_semantics",
  call_thm_hello |> ONCE_REWRITE_RULE[GSYM hello_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]);
*)

val _ = export_theory ()

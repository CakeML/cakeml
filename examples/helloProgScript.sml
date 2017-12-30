open preamble basis

val _ = new_theory "helloProg"

val _ = translation_extends"basisProg";

val hello = process_topdecs
  `fun hello u = TextIO.print "Hello World!\n"`

val res = ml_prog_update(ml_progLib.add_prog hello pick_name)

val st = get_ml_prog_state ()

val hello_spec = Q.store_thm ("hello_spec",
  ` app (p:'ffi ffi_proj) ^(fetch_v "hello" st)
        [Conv NONE []]
        (STDIO fs)
        (POSTv uv. &UNIT_TYPE () uv *  (* TODO: emp required because fsioProgLib.call_thm is too fragile *)
            (STDIO (add_stdout fs (strlit "Hello World!\n"))) * emp)`,
  xcf "hello" st \\ xapp \\ xsimpl \\
  (* TODO: xsimpl should get this already *)
  map_every qexists_tac[`emp`,`fs`] \\ xsimpl);

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
  |> DISCH_ALL);

val _ = export_theory ()

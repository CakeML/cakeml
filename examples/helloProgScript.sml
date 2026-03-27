(*
  Hello World example, printing to standard output.
*)
Theory helloProg
Ancestors
  basis_ffi
Libs
  preamble basis

val _ = translation_extends"basisProg";

Quote add_cakeml:
  fun hello u = TextIO.print "Hello World!\n"
End

val st = get_ml_prog_state ()

Theorem hello_spec:
    app (p:'ffi ffi_proj) ^(fetch_v "hello" st)
        [Conv NONE []]
        (STDIO fs)
        (POSTv uv. &UNIT_TYPE () uv * STDIO (add_stdout fs (strlit "Hello World!\n")))
Proof
  xcf "hello" st \\ xapp \\ xsimpl
QED

Theorem hello_whole_prog_spec:
   whole_prog_spec ^(fetch_v "hello" st) cl fs NONE
    ((=) (add_stdout fs (strlit "Hello World!\n")))
Proof
  rw[whole_prog_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac`fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe hello_spec))
  \\ xsimpl
QED

val spec = hello_whole_prog_spec
val name = "hello";

val (call_thm_hello, hello_prog_tm) = whole_prog_thm st name spec;
Definition hello_prog_def:
  hello_prog = ^hello_prog_tm
End

Theorem hello_semantics =
  call_thm_hello |> ONCE_REWRITE_RULE[GSYM hello_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]

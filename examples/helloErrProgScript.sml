(*
  Hello World on standard error.
*)
open preamble basis

val _ = new_theory "helloErrProg"

val _ = translation_extends"basisProg";

val helloErr = process_topdecs
  `fun helloErr u =
     (TextIO.output TextIO.stdErr "Well oH lord!\n";
      Runtime.abort())`

val () = append_prog helloErr;

val st = get_ml_prog_state ()

val helloErr_spec = Q.store_thm ("helloErr_spec",
  `app (p:'ffi ffi_proj) ^(fetch_v "helloErr" st)
        [Conv NONE []]
        (RUNTIME * STDIO fs)
        (POSTf n. λ c b. RUNTIME * &(n = "exit" /\ c = [] /\ b = [1w]) *
                   STDIO (add_stderr fs (strlit "Well oH lord!\n")))`,
  xcf "helloErr" st
  \\ xlet `(POSTv uv. &(UNIT_TYPE () uv) * RUNTIME *
                      STDIO (add_stderr fs (strlit "Well oH lord!\n")))`
  >- (xapp_spec output_stderr_spec
      \\ xsimpl \\ MAP_EVERY qexists_tac [`RUNTIME`,`fs`] \\ xsimpl)
  \\ xlet_auto
  >- (xcon \\ xsimpl)
  \\ xapp \\ xsimpl);

val helloErr_whole_prog_spec = Q.store_thm("helloErr_whole_prog_spec",
  `whole_prog_ffidiv_spec ^(fetch_v "helloErr" st) cl fs
    (λn c b fs'. n = "exit" /\ c = [] /\ b = [1w] /\ add_stderr fs (strlit "Well oH lord!\n") = fs')`,
  rw[basis_ffiTheory.whole_prog_ffidiv_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac `fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe helloErr_spec))
  \\ xsimpl);

val (helloErr_sem_thm, helloErr_prog_tm) = whole_prog_thm st "helloErr" helloErr_whole_prog_spec;
val helloErr_prog_def = Define`helloErr_prog = ^helloErr_prog_tm`;

val helloErr_semantics = save_thm("helloErr_semantics",
  helloErr_sem_thm |> ONCE_REWRITE_RULE[GSYM helloErr_prog_def]
  |> DISCH_ALL |> SIMP_RULE std_ss [AND_IMP_INTRO,GSYM CONJ_ASSOC]);

val _ = export_theory ()

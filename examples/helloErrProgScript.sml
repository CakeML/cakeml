(*
  Hello World on standard error.
*)
Theory helloErrProg
Ancestors
  basis_ffi
Libs
  preamble basis

val _ = translation_extends"basisProg";

Quote add_cakeml:
  fun helloErr u =
     (TextIO.output TextIO.stdErr "Well oH lord!\n";
      Runtime.abort())
End

val st = get_ml_prog_state ()

Theorem helloErr_spec:
   app (p:'ffi ffi_proj) ^(fetch_v "helloErr" st)
        [Conv NONE []]
        (RUNTIME * STDIO fs)
        (POSTf n. λ c b. RUNTIME * &(n = «exit» /\ c = [] /\ b = [1w]) *
                   STDIO (add_stderr fs «Well oH lord!\n»))
Proof
  xcf "helloErr" st
  \\ xlet `(POSTv uv. &(UNIT_TYPE () uv) * RUNTIME *
                      STDIO (add_stderr fs «Well oH lord!\n»))`
  >- (xapp_spec output_stderr_spec
      \\ xsimpl \\ MAP_EVERY qexists_tac [`RUNTIME`,`fs`] \\ xsimpl)
  \\ xlet_auto
  >- (xcon \\ xsimpl)
  \\ xapp \\ xsimpl
QED

Theorem helloErr_whole_prog_spec:
   whole_prog_ffidiv_spec ^(fetch_v "helloErr" st) cl fs
    (λn c b fs'. n = «exit» /\ c = [] /\ b = [1w] /\ add_stderr fs «Well oH lord!\n» = fs')
Proof
  rw[basis_ffiTheory.whole_prog_ffidiv_spec_def]
  \\ qmatch_goalsub_abbrev_tac`fs1 = _ with numchars := _`
  \\ qexists_tac `fs1`
  \\ simp[Abbr`fs1`,GSYM add_stdo_with_numchars,with_same_numchars]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe helloErr_spec))
  \\ xsimpl
QED

Theorem helloErr_semantics =
  prove_sem_thm "helloErr" "helloErr_prog" helloErr_whole_prog_spec;

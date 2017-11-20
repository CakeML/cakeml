open preamble basis

val _ = new_theory "helloErrProg"

val _ = translation_extends"basisProg";

val helloErr = process_topdecs
  `fun helloErr u = TextIO.prerr_string "Well oH lord!\n"`

val res = ml_prog_update(ml_progLib.add_prog helloErr pick_name)

val st = get_ml_prog_state ()

val helloErr_spec = Q.store_thm ("helloErr_spec",
  `!err.
      app (p:'ffi ffi_proj) ^(fetch_v "helloErr" st)
        [Conv NONE []]
        (STDIO fs)
        (POSTv uv. &UNIT_TYPE () uv *
                   (STDIO (add_stderr fs "Well oH lord!\n")) * emp)`,
  xcf "helloErr" st
  \\ xapp \\ xsimpl
  \\ qexists_tac`emp` \\ qexists_tac`fs`
  \\ xsimpl);

val st = get_ml_prog_state();
val spec = helloErr_spec |> SPEC_ALL |> UNDISCH_ALL
            |> SIMP_RULE(srw_ss())[STDIO_def] |> add_basis_proj;
val name = "helloErr";
val (call_thm_helloErr, helloErr_prog_tm) = call_thm st name spec;
val helloErr_prog_def = Define`helloErr_prog = ^helloErr_prog_tm`;

val helloErr_semantics = save_thm("helloErr_semantics",
  call_thm_helloErr |> ONCE_REWRITE_RULE[GSYM helloErr_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE std_ss [APPEND,LENGTH,STD_streams_add_stderr]);

val _ = export_theory ()

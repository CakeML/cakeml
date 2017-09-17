open  preamble ml_progLib fsioProgLib ml_translatorLib cfTacticsLib

val _ = new_theory "helloErrProg"

val _ = translation_extends"fsioProg";

val helloErr = process_topdecs
  `fun helloErr u = IO.prerr_string "Well oH lord!\n"`

val res = ml_prog_update(ml_progLib.add_prog helloErr pick_name)

val st = get_ml_prog_state ()

val helloErr_spec = Q.store_thm ("helloErr_spec",
  `!err.
      app (p:'ffi ffi_proj) ^(fetch_v "helloErr" st)
        [Conv NONE []]
        (STDIO fs * &stderr fs err)
        (POSTv uv. &UNIT_TYPE () uv * 
                   (STDIO (up_stderr (err ++ "Well oH lord!\n") fs)) * emp)`,
  xcf "helloErr" st \\ xpull
  \\ xapp \\ xsimpl
  \\instantiate \\xsimpl);

val st = get_ml_prog_state();
val spec = helloErr_spec |> SPEC_ALL |> UNDISCH_ALL
            |> SIMP_RULE(srw_ss())[fsioProgConstantsTheory.STDIO_def] |> add_basis_proj;
val name = "helloErr";
val (call_thm_helloErr, helloErr_prog_tm) = call_thm st name spec;
val helloErr_prog_def = Define`helloErr_prog = ^helloErr_prog_tm`;

val helloErr_semantics = save_thm("helloErr_semantics",
  call_thm_helloErr |> ONCE_REWRITE_RULE[GSYM helloErr_prog_def]
  |> SIMP_RULE std_ss [APPEND]);

val _ = export_theory ()

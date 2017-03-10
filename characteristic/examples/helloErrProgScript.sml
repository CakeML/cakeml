open  preamble ml_progLib ioProgLib ml_translatorLib
      cfTacticsLib

val _ = new_theory "helloErrProg"

val _ = translation_extends"ioProg";

val helloErr = process_topdecs
  `fun helloErr u = print_err "Well oH lord!\n"`

val res = ml_prog_update(ml_progLib.add_prog helloErr pick_name)

val st = get_ml_prog_state ()

val helloErr_spec = Q.store_thm ("helloErr_spec",
  `!s cv input output.
      app (p:'ffi ffi_proj) ^(fetch_v "helloErr" st)
        [Conv NONE []]
        (STDOUT s * STDERR [])
        (POSTv uv. &UNIT_TYPE () uv * (STDOUT s * STDERR ("Well oH lord!\n")))`,
  xcf "helloErr" st
  \\ xapp \\ xsimpl \\ 
  qexists_tac `STDOUT s` \\ qexists_tac `[]` \\ xsimpl
);

val st = get_ml_prog_state();
val spec = helloErr_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "helloErr";
val (call_thm_helloErr, helloErr_prog_tm) = call_thm st name spec;
val helloErr_prog_def = Define`helloErr_prog = ^helloErr_prog_tm`;

val helloErr_semantics = save_thm("helloErr_semantics",
  call_thm_helloErr |> ONCE_REWRITE_RULE[GSYM helloErr_prog_def]);

val _ = export_theory ()

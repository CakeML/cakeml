open  preamble ml_progLib ioProgLib ml_translatorLib
      cfTacticsLib

val _ = new_theory "helloProg"

val _ = translation_extends"ioProg";

val hello = process_topdecs
  `fun hello u = print "Hello World!\n"`

val res = ml_prog_update(ml_progLib.add_prog hello pick_name)

val st = get_ml_prog_state ()

val hello_spec = Q.store_thm ("hello_spec",
  `!cv input output.
      app (p:'ffi ffi_proj) ^(fetch_v "hello" st)
        [Conv NONE []]
        (STDOUT output)
        (POSTv uv. &UNIT_TYPE () uv * STDOUT (output ++ "Hello World!\n"))`,
  xcf "hello" st
  \\ xapp \\ xsimpl \\ CONV_TAC(SWAP_EXISTS_CONV)
  \\ qexists_tac `output` \\ xsimpl
);

val st = get_ml_prog_state();
val spec = hello_spec |> SPEC_ALL |> UNDISCH_ALL |> add_basis_proj;
val name = "hello";
val (call_thm_hello, hello_prog_tm) = call_thm st name spec;
val hello_prog_def = Define`hello_prog = ^hello_prog_tm`;

val hello_semantics = save_thm("hello_semantics",
  call_thm_hello |> ONCE_REWRITE_RULE[GSYM hello_prog_def]
  |> SIMP_RULE std_ss [APPEND]);

val _ = export_theory ()

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
            (STDIO (add_stdout fs "Hello World!\n")) * emp)`,
  xcf "hello" st \\ xapp \\ xsimpl \\
  (* TODO: xsimpl should get this already *)
  map_every qexists_tac[`emp`,`fs`] \\ xsimpl);

val spec = hello_spec |> SPEC_ALL |> UNDISCH_ALL
        |> SIMP_RULE(srw_ss())[STDIO_def]|> add_basis_proj;

val name = "hello";
val (call_thm_hello, hello_prog_tm) = call_thm st name spec;
val hello_prog_def = Define`hello_prog = ^hello_prog_tm`;

val hello_semantics = save_thm("hello_semantics",
  call_thm_hello |> ONCE_REWRITE_RULE[GSYM hello_prog_def]
  |> DISCH_ALL
  (* TODO: call_thm to remove the STD_streams_add_stdout? *)
  |> SIMP_RULE std_ss [APPEND,LENGTH,STD_streams_add_stdout]);

val _ = export_theory ()

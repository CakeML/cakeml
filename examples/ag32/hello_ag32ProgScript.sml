open preamble basis PrinterProofTheory ag_ffiTheory ag_ffiLib

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

val hello_ag_prog_spec = Q.store_thm("hello_ag_prog_spec",
  `ag_prog_spec ^(fetch_v "hello" st) (combin$C (=) "Hello World!\n")`,
  rw[ag_prog_spec_def]
  \\ match_mp_tac (MP_CANON (MATCH_MP app_wgframe (Q.SPEC`""`(Q.GEN`out`hello_spec))))
  \\ xsimpl);

val spec = hello_ag_prog_spec
val name = "hello";

val (call_thm_hello, hello_prog_tm) = ag_prog_thm st name spec;
val hello_prog_def = Define`hello_prog = ^hello_prog_tm`;

val hello_semantics = save_thm("hello_semantics",
  call_thm_hello |> ONCE_REWRITE_RULE[GSYM hello_prog_def]
  |> SIMP_RULE std_ss []);

val _ = export_theory ()

(* TODO: this library is a stop-gap measure for compiling
         characteristic/examples. See issue #249. *)
structure compilationLib = struct

open preamble x64_compileLib x64_exportLib

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20;
val _ = PolyML.print_depth 5;

fun to_bytes alg conf prog =
  let
  val _ = println "Compile to livesets"
  val init = Count.apply eval``to_livesets ^(conf) ^(prog)``
  val _ = println "External oracle"
  val oracles = reg_allocComputeLib.get_oracle alg (fst (pairSyntax.dest_pair (rconc init)))
  val wc = ``<|reg_alg:=3;col_oracle:= ^(oracles)|>``
  val _ = println "Repeat compilation with oracle"
  (*This repeats the "to_livesets" step, but that isn't very costly*)
  val compile_thm = Count.apply eval``
    compile (^(conf) with word_to_word_conf := ^(wc)) ^(prog)``
  (* Alternatively: we can use the theories to manipulate init directly
  however, running the simplifier on the result takes quite long as well
  val rw = backendTheory.to_livesets_invariant |> SIMP_RULE std_ss[LET_THM]
   |> GEN_ALL |> ISPECL [wc,prog,``x64_compiler_config``]
   |> ONCE_REWRITE_RULE[init] |> SIMP_RULE std_ss []
  val test2 = Count.apply eval``
    let (rcm,c,p) = ^(rconc init) in
    from_livesets (rcm,c with word_to_word_conf:= ^(wc),p)``
   *)
  in
    compile_thm
  end

val extract_bytes_ffis = pairSyntax.dest_pair o optionSyntax.dest_some o rconc
val extract_oracle = find_term listSyntax.is_list o lhs o concl

val to_x64_bytes = to_bytes 3 ``x64_compiler_config``

val extract_ffi_names = map stringSyntax.fromHOLstring o fst o listSyntax.dest_list

fun compile_x64 heap_size stack_size name prog_def =
  let
    val result = to_x64_bytes (prog_def |> rconc)
    val oracle = extract_oracle result
    val (bytes,ffis) = extract_bytes_ffis result
    val oracle_def = mk_abbrev(name^"_oracle") oracle
    val bytes_def = mk_abbrev(name^"_bytes") bytes
    val ffis_def = mk_abbrev(name^"_ffis") ffis
    val () = write_cake_S heap_size stack_size (extract_ffi_names ffis) bytes (name^".S")
  in
     result |> ONCE_REWRITE_RULE[SYM oracle_def, SYM bytes_def, SYM ffis_def, SYM prog_def]
  end

end

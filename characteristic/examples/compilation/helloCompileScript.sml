open HolKernel boolLib bossLib lcsymtacs
open x64_compileLib x64_exportLib helloProgTheory

val _ = new_theory "helloCompile"

val rconc = rhs o concl

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20;
val _ = PolyML.print_depth 5;

fun println s = print (strcat s "\n");


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

val extract_bytes = pairSyntax.dest_pair o optionSyntax.dest_some o rconc
val extract_ffi_names = rev o map stringSyntax.fromHOLstring o fst o listSyntax.dest_list

fun write_asm [] = ()
  | write_asm ((name,(bytes,ffi_names))::xs) =
    (write_cake_S 1000 1000 (extract_ffi_names ffi_names)
       bytes (name ^ ".S") ;
    write_asm xs)

val hello_prog = hello_prog_def |> REWRITE_RULE [listTheory.SNOC_APPEND, listTheory.APPEND] |> concl |> rand

val hello_compiled = to_bytes 3 ``x64_compiler_config`` hello_prog

val hello_bytes = extract_bytes hello_compiled

val store2 = save_thm ("hello", hello_compiled)
val store1 = write_asm [ ("hello", hello_bytes) ]

val _ = export_theory ();

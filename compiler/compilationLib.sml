(* TODO: this library is a stop-gap measure for compiling
         characteristic/examples. See issue #249. *)
structure compilationLib = struct

open preamble backendTheory x64_compileLib x64_exportLib

val _ = PolyML.timing true;
val _ = Globals.max_print_depth := 20;
val _ = PolyML.print_depth 5;

fun compilation_compset() =
  let
    val cs = wordsLib.words_compset();
    val () = computeLib.extend_compset
      [computeLib.Extenders [
        basicComputeLib.add_basic_compset,
        semanticsComputeLib.add_ast_compset,
        compilerComputeLib.add_compiler_compset]
      ] cs
  in cs end;

val num_threads = ref 8
val chunk_size = ref 40

fun compile_to_data cs conf_def prog_def data_prog_name =
  let
    val () = computeLib.extend_compset
       [computeLib.Defs [conf_def, prog_def]] cs
    val eval = computeLib.CBV_CONV cs;
    val conf_tm = lhs(concl conf_def)
    val prog_tm = lhs(concl prog_def)

    val to_mod_thm0 = timez "to_mod" eval ``to_mod ^conf_tm ^prog_tm``;
    val (c,p) = to_mod_thm0 |> rconc |> dest_pair
    val mod_conf_def = zDefine`mod_conf = ^c`;
    val mod_prog_def = zDefine`mod_prog = ^p`;
    val to_mod_thm =
      to_mod_thm0 |> CONV_RULE(RAND_CONV(
        FORK_CONV(REWR_CONV(SYM mod_conf_def),
                  REWR_CONV(SYM mod_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [mod_prog_def]] cs;

    val mod_conf_mod_conf =
      ``mod_conf.mod_conf``
      |> (RAND_CONV(REWR_CONV mod_conf_def) THENC eval)

    val mod_conf_source_conf =
      ``mod_conf.source_conf``
      |> (RAND_CONV(REWR_CONV mod_conf_def) THENC eval)

    val mod_conf_clos_conf =
      ``mod_conf.clos_conf``
      |> (RAND_CONV(REWR_CONV mod_conf_def) THENC eval)

    val mod_conf_bvl_conf =
      ``mod_conf.bvl_conf``
      |> (RAND_CONV(REWR_CONV mod_conf_def) THENC eval)

    val to_con_thm0 =
      ``to_con ^conf_tm ^prog_tm``
      |> (REWR_CONV to_con_def THENC
          RAND_CONV (REWR_CONV to_mod_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV THENC
          PATH_CONV"rlr"(REWR_CONV mod_conf_mod_conf))
      |> timez "to_con" (CONV_RULE(RAND_CONV eval))
    val (c,p) = to_con_thm0 |> rconc |> dest_pair
    val con_conf_def = zDefine`con_conf = ^c`;
    val con_prog_def = zDefine`con_prog = ^p`;
    val to_con_thm =
      to_con_thm0 |> CONV_RULE(RAND_CONV(
        FORK_CONV(REWR_CONV(SYM con_conf_def),
                  REWR_CONV(SYM con_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [con_prog_def]] cs;

    val con_conf_source_conf_next_global =
      ``con_conf.source_conf.next_global`` |>
        (RAND_CONV(RAND_CONV(REWR_CONV con_conf_def)) THENC eval
         THENC RAND_CONV(REWR_CONV mod_conf_source_conf) THENC eval)

    val con_conf_mod_conf_exh_ctors_env =
      ``con_conf.mod_conf.exh_ctors_env``
      |> (RAND_CONV(RAND_CONV(REWR_CONV con_conf_def)) THENC eval)

    val con_conf_clos_conf =
      ``con_conf.clos_conf``
      |> (RAND_CONV(REWR_CONV con_conf_def) THENC eval
          THENC REWR_CONV mod_conf_clos_conf)

    val con_conf_bvl_conf =
      ``con_conf.bvl_conf``
      |> (RAND_CONV(REWR_CONV con_conf_def) THENC eval
          THENC REWR_CONV mod_conf_bvl_conf)

    val to_dec_thm0 =
      ``to_dec ^conf_tm ^prog_tm``
      |> (REWR_CONV to_dec_def THENC
          RAND_CONV (REWR_CONV to_con_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV THENC
          PATH_CONV"rlr"(REWR_CONV con_conf_source_conf_next_global))
      |> timez "to_dec" (CONV_RULE(RAND_CONV eval))
    val (c,p) = to_dec_thm0 |> rconc |> dest_pair
    val dec_conf_def = zDefine`dec_conf = ^c`;
    val dec_prog_def = zDefine`dec_prog = ^p`;
    val to_dec_thm =
      to_dec_thm0 |> CONV_RULE(RAND_CONV(
        FORK_CONV(REWR_CONV(SYM dec_conf_def),
                  REWR_CONV(SYM dec_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [dec_prog_def]] cs;

    val dec_conf_mod_conf_exh_ctors_env =
      ``dec_conf.mod_conf.exh_ctors_env``
      |> (RAND_CONV(RAND_CONV(REWR_CONV dec_conf_def) THENC eval) THENC
          REWR_CONV con_conf_mod_conf_exh_ctors_env)

    val dec_conf_clos_conf =
      ``dec_conf.clos_conf``
      |> (RAND_CONV(REWR_CONV dec_conf_def) THENC eval
          THENC REWR_CONV con_conf_clos_conf)

    val dec_conf_bvl_conf =
      ``dec_conf.bvl_conf``
      |> (RAND_CONV(REWR_CONV dec_conf_def) THENC eval
          THENC REWR_CONV con_conf_bvl_conf)

    val to_exh_thm0 =
      ``to_exh ^conf_tm ^prog_tm``
      |> (REWR_CONV to_exh_def THENC
          RAND_CONV (REWR_CONV to_dec_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV THENC
          PATH_CONV"rlr"(REWR_CONV dec_conf_mod_conf_exh_ctors_env))
      |> timez "to_exh" (CONV_RULE(RAND_CONV eval))
    val (_,p) = to_exh_thm0 |> rconc |> dest_pair
    val exh_prog_def = zDefine`exh_prog = ^p`;
    val to_exh_thm =
      to_exh_thm0 |> CONV_RULE(RAND_CONV(
        RAND_CONV(REWR_CONV(SYM exh_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [exh_prog_def]] cs;

    val to_pat_thm0 =
      ``to_pat ^conf_tm ^prog_tm``
      |> (REWR_CONV to_pat_def THENC
          RAND_CONV (REWR_CONV to_exh_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV)
      |> timez "to_pat" (CONV_RULE(RAND_CONV(RAND_CONV eval)))
      |> CONV_RULE(RAND_CONV(REWR_CONV LET_THM THENC BETA_CONV))
    val (_,p) = to_pat_thm0 |> rconc |> dest_pair
    val pat_prog_def = zDefine`pat_prog = ^p`;
    val to_pat_thm =
      to_pat_thm0 |> CONV_RULE(RAND_CONV(
        RAND_CONV(REWR_CONV(SYM pat_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [pat_prog_def]] cs;

    val to_clos_thm0 =
      ``to_clos ^conf_tm ^prog_tm``
      |> (REWR_CONV to_clos_def THENC
          RAND_CONV (REWR_CONV to_pat_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV)
      |> timez "to_clos" (CONV_RULE(RAND_CONV(RAND_CONV eval)))
      |> CONV_RULE(RAND_CONV(REWR_CONV LET_THM THENC BETA_CONV))
    val (_,p) = to_clos_thm0 |> rconc |> dest_pair
    val clos_prog_def = zDefine`clos_prog = ^p`;
    val to_clos_thm =
      to_clos_thm0 |> CONV_RULE(RAND_CONV(
        RAND_CONV(REWR_CONV(SYM clos_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [clos_prog_def]] cs;

    val to_bvl_thm0 =
      ``to_bvl ^conf_tm ^prog_tm``
      |> (REWR_CONV to_bvl_def THENC
          RAND_CONV (REWR_CONV to_clos_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV THENC
          PATH_CONV"rlr"(REWR_CONV dec_conf_clos_conf))
      |> timez "to_bvl" (CONV_RULE(RAND_CONV eval))
    val (c,p) = to_bvl_thm0 |> rconc |> dest_pair
    val bvl_conf_def = zDefine`bvl_conf = ^c`;
    val bvl_prog_def = zDefine`bvl_prog = ^p`;
    val to_bvl_thm =
      to_bvl_thm0 |> CONV_RULE(RAND_CONV(
        FORK_CONV(REWR_CONV(SYM bvl_conf_def),
                  REWR_CONV(SYM bvl_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [bvl_prog_def]] cs;

    val bvl_conf_clos_conf_next_loc =
      ``bvl_conf.clos_conf.next_loc``
      |> (RAND_CONV(RAND_CONV(REWR_CONV bvl_conf_def)) THENC eval)

    val bvl_conf_clos_conf_start =
      ``bvl_conf.clos_conf.start``
      |> (RAND_CONV(RAND_CONV(REWR_CONV bvl_conf_def)) THENC eval)

    val bvl_conf_bvl_conf =
      ``bvl_conf.bvl_conf``
      |> (RAND_CONV(REWR_CONV bvl_conf_def) THENC eval
          THENC REWR_CONV dec_conf_bvl_conf)

    val to_bvi_thm0 =
      ``to_bvi ^conf_tm ^prog_tm``
      |> (REWR_CONV to_bvi_def THENC
          RAND_CONV (REWR_CONV to_bvl_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV THENC
          PATH_CONV"rllr"(REWR_CONV bvl_conf_clos_conf_next_loc) THENC
          PATH_CONV"rlllr"(REWR_CONV bvl_conf_clos_conf_start) THENC
          PATH_CONV"rlr"(REWR_CONV bvl_conf_bvl_conf))

    val th1 =
      to_bvi_thm0 |> rconc |> rand |>
      (REWR_CONV bvl_to_bviTheory.compile_def THENC
       RAND_CONV(
         RAND_CONV(RATOR_CONV(RAND_CONV eval)) THENC
         RATOR_CONV(RAND_CONV eval) THENC
         REWR_CONV bvl_to_bviTheory.optimise_def THENC
         RAND_CONV (timez "bvl inline" eval)))

    val mapfn = th1 |> rconc |> rand |> rator |> rand
    fun eval_fn i n t = eval(mk_comb(mapfn,t)) (* before Lib.say(String.concat[Int.toString i,".",Int.toString n,"\n"]) *)
    val els = th1 |> rconc |> rand |> rand |> listSyntax.dest_list |> #1

    val mapths = time_with_size thms_size "bvl optimise (par)" (parlist (!num_threads) (!chunk_size) eval_fn) els;

    val th2 = th1 |> CONV_RULE(RAND_CONV(
      RAND_CONV(map_ths_conv mapths) THENC
      timez "bvl compile" eval))

    val to_bvi_thm1 = to_bvi_thm0 |> CONV_RULE(RAND_CONV(
      RAND_CONV(REWR_CONV th2) THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC BETA_CONV))

    val (c,p) = to_bvi_thm1 |> rconc |> dest_pair
    val bvi_conf_def = zDefine`bvi_conf = ^c`;
    val bvi_prog_def = zDefine`bvi_prog = ^p`;
    val to_bvi_thm =
      to_bvi_thm1 |> CONV_RULE(RAND_CONV(
        FORK_CONV(REWR_CONV(SYM bvi_conf_def),
                  REWR_CONV(SYM bvi_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [bvi_prog_def]] cs;

    val to_data_thm0 =
      ``to_data ^conf_tm ^prog_tm``
      |> (REWR_CONV to_data_def THENC
          RAND_CONV (REWR_CONV to_bvi_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC BETA_CONV)
      |> timez "to_data" (CONV_RULE(RAND_CONV(RAND_CONV eval)))
    val (_,p) = to_data_thm0 |> rconc |> dest_pair

    val data_prog_def = mk_abbrev data_prog_name p
    val to_data_thm =
      to_data_thm0 |> CONV_RULE(RAND_CONV(
        RAND_CONV(REWR_CONV(SYM data_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [data_prog_def]] cs;

    val () = app delete_const
      ["mod_prog","con_prog","dec_prog","exh_prog","pat_prog","clos_prog","bvl_prog","bvi_prog"]
  in to_data_thm end

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

val to_x64_bytes = to_bytes 3 ``x64_backend_config``

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

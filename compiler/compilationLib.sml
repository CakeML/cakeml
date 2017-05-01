structure compilationLib = struct

open preamble backendTheory
     x64_compileLib x64_exportLib

val _ = Globals.max_print_depth := 20;

fun compilation_compset() =
  let
    val cs = wordsLib.words_compset();
    val () = computeLib.extend_compset
      [computeLib.Extenders [
        basicComputeLib.add_basic_compset,
        semanticsComputeLib.add_ast_compset,
        compilerComputeLib.add_compiler_compset,
        asmLib.add_asm_compset ]
      ] cs
  in cs end;

val num_threads = ref 8
val chunk_size = ref 50

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

fun compile_to_lab_x64 data_prog_x64_def to_data_thm =
  let
    val cs = compilation_compset()
    val () =
      computeLib.extend_compset [
        computeLib.Extenders [
          x64_targetLib.add_x64_encode_compset ],
        computeLib.Defs [
          x64_backend_config_def,
          x64_names_def,
          data_prog_x64_def ]
      ] cs
    val eval = computeLib.CBV_CONV cs;
    fun parl f = parlist (!num_threads) (!chunk_size) f

    val (_,[conf_tm,prog_tm]) =
      to_data_thm |> concl |> lhs |> strip_comb

    val to_livesets_thm0 =
      ``to_livesets ^conf_tm ^prog_tm``
      |> (REWR_CONV to_livesets_def THENC
          RAND_CONV (REWR_CONV to_data_thm) THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC BETA_CONV THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC
          PATH_CONV "rlrraraalralrarllr" eval THENC
          PATH_CONV"rlrraraalralralralralrar"
            (RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
             REWR_CONV(CONJUNCT1 bool_case_thm)))
    val tm0 = to_livesets_thm0 |> rconc |> rand |> rand
    val thm0 = timez "data_to_word" eval tm0;

    val tm1 = to_livesets_thm0 |> rconc |> rand
    val (args,body) = tm1 |> rator |> rand |> dest_pabs
    val word_to_word_fn_def = zDefine`word_to_word_fn ^args = ^body`;
    val temp_defs = ["word_to_word_fn_def"];
    val word_to_word_fn_eq =
      word_to_word_fn_def
      |> SPEC_ALL
      |> PairRules.PABS args
      |> CONV_RULE(LAND_CONV PairRules.PETA_CONV)

    val word_to_word_fn = word_to_word_fn_eq|>concl|>lhs
    val word_prog = thm0 |> rconc |> listSyntax.dest_list |> #1
    val num_progs = length word_prog

    fun eval_fn i n p =
      let
        val tm = mk_comb(word_to_word_fn,p)
        val conv = RATOR_CONV(REWR_CONV word_to_word_fn_eq) THENC eval
      in
        conv tm
      end
    val ths = time_with_size thms_size "inst,ssa,two-reg (par)"
                (parl eval_fn) word_prog;
    val thm1 =
      tm1
      |> (RATOR_CONV(RAND_CONV(REWR_CONV(SYM word_to_word_fn_eq))) THENC
          RAND_CONV(REWR_CONV thm0) THENC map_ths_conv ths)

    val word_prog0_def = mk_abbrev "word_prog0" (thm1 |> rconc)
    val temp_defs = "word_prog0_def"::temp_defs;

    val thm1' = thm1 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM word_prog0_def)))

    val to_livesets_thm1 =
      to_livesets_thm0
      |> CONV_RULE (RAND_CONV (
           RAND_CONV(REWR_CONV thm1') THENC
           BETA_CONV THENC
           REWR_CONV LET_THM))

    val tm2 = to_livesets_thm1 |> rconc |> rand
    val (args,body) = tm2 |> rator |> rand |> dest_pabs
    val clash_fn_def = zDefine`clash_fn ^args = ^body`;
    val temp_defs = "clash_fn_def"::temp_defs;
    val clash_fn_eq =
      clash_fn_def
      |> SPEC_ALL
      |> PairRules.PABS args
      |> CONV_RULE(LAND_CONV PairRules.PETA_CONV)
    val clash_fn = clash_fn_eq|>concl|>lhs

    val word_prog0 = thm1 |> rconc |> listSyntax.dest_list |> #1

    fun eval_fn i n p =
      let
        val tm = mk_comb(clash_fn,p)
        val conv = RATOR_CONV(REWR_CONV clash_fn_eq) THENC eval
      in
        conv tm
      end
    val ths = time_with_size thms_size "get_clash (par)"
                (parl eval_fn) word_prog0;
    val thm2 =
      tm2
      |> (RATOR_CONV(RAND_CONV(REWR_CONV(SYM clash_fn_eq))) THENC
          RAND_CONV(REWR_CONV word_prog0_def) THENC map_ths_conv ths)

    val to_livesets_thm =
      to_livesets_thm1
      |> CONV_RULE (RAND_CONV (
           RAND_CONV(REWR_CONV thm2) THENC
           BETA_CONV THENC
           PATH_CONV"lrlr"eval))

    val oracles =
      to_livesets_thm
      |> rconc |> pairSyntax.dest_pair |> #1
      |> time_with_size term_size "external oracle" (reg_allocComputeLib.get_oracle 3)

    val x64_oracle_def = mk_abbrev"x64_oracle" oracles;

    val wc =
      ``^conf_tm.word_to_word_conf
        with col_oracle := x64_oracle``
      |> eval |> rconc

    val args = to_livesets_thm |> concl |> lhs |> strip_comb |> #2

    val word_prog1_def = mk_abbrev"word_prog1"(thm2 |> rconc);
    val temp_defs = "word_prog1_def" :: temp_defs

    val to_livesets_thm' =
      to_livesets_thm
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"lrr"(REWR_CONV(SYM word_prog1_def))))

    val to_livesets_oracle_thm =
      to_livesets_invariant
      |> Q.GEN`wc` |> SPEC wc
      |> Q.GENL[`p`,`c`] |> ISPECL args
      |> CONV_RULE(RAND_CONV(
           REWR_CONV LET_THM THENC
           RAND_CONV(REWR_CONV to_livesets_thm') THENC
           PAIRED_BETA_CONV))

    val args = to_livesets_oracle_thm |> concl |> lhs |> strip_comb |> #2

    val LENGTH_word_prog0 =
      listSyntax.mk_length(lhs(concl(word_prog0_def)))
      |> (RAND_CONV(REWR_CONV word_prog0_def) THENC
          listLib.LENGTH_CONV)

    val LENGTH_word_prog1 =
      listSyntax.mk_length(lhs(concl(word_prog1_def)))
      |> (RAND_CONV(REWR_CONV word_prog1_def) THENC
          listLib.LENGTH_CONV)

    val ZIP_GENLIST_lemma =
      MATCH_MP LENGTH_ZIP
        (TRANS LENGTH_word_prog1 (SYM LENGTH_word_prog0))
      |> CONJUNCT1
      |> C TRANS LENGTH_word_prog1
      |> MATCH_MP ZIP_GENLIST1
      |> ISPEC (lhs(concl(x64_oracle_def)))

    val x64_oracle_list_def = mk_abbrev"x64_oracle_list" (x64_oracle_def |> rconc |> rand);
    val temp_defs = "x64_oracle_list_def" :: temp_defs

    val x64_oracle_thm = Q.prove(
      `n < LENGTH x64_oracle_list ⇒
       (x64_oracle n = SOME (EL n x64_oracle_list))`,
      strip_tac
      \\ CONV_TAC(LAND_CONV(
           RATOR_CONV(REWR_CONV x64_oracle_def THENC
                      REWR_CONV LET_THM THENC
                      (RAND_CONV(REWR_CONV(SYM x64_oracle_list_def))) THENC
                      BETA_CONV)
           THENC BETA_CONV))
      \\ rw[]);

    val LENGTH_x64_oracle_list =
      listSyntax.mk_length(lhs(concl(x64_oracle_list_def)))
      |> (RAND_CONV(REWR_CONV x64_oracle_list_def) THENC
          listLib.LENGTH_CONV)

    val GENLIST_EL_ZIP_lemma = Q.prove(
      `(LENGTH l1 = n) ∧ (LENGTH l2 = n) ∧ (LENGTH x64_oracle_list = n) ⇒
       (GENLIST (λx. f (x64_oracle x, EL x (ZIP (l1,l2)))) n =
        MAP3 (λa (b1,b2,b3) (c1,c2,c3). f (SOME a, ((b1,b2,b3), (c1,c2,c3)))) x64_oracle_list l1 l2)`,
      rw[LIST_EQ_REWRITE,EL_MAP3,EL_ZIP,x64_oracle_thm,UNCURRY])
      |> C MATCH_MP (CONJ LENGTH_word_prog1 (CONJ LENGTH_word_prog0 LENGTH_x64_oracle_list))

    val compile_thm0 =
      compile_oracle |> SYM
      |> Q.GENL[`p`,`c`] |> ISPECL args
      |> CONV_RULE(RAND_CONV(
           RAND_CONV(REWR_CONV to_livesets_oracle_thm) THENC
           REWR_CONV from_livesets_def THENC
           REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
           RAND_CONV(
             RAND_CONV eval THENC
             RATOR_CONV(RAND_CONV(REWR_CONV LENGTH_word_prog0)) THENC
             REWR_CONV word_to_wordTheory.next_n_oracle_def) THENC
           REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
           RAND_CONV eval THENC
           REWR_CONV LET_THM THENC BETA_CONV THENC
           REWR_CONV LET_THM THENC BETA_CONV THENC
           RAND_CONV(
             RAND_CONV(REWR_CONV ZIP_GENLIST_lemma) THENC
             REWR_CONV MAP_GENLIST THENC
             RATOR_CONV(RAND_CONV(
               REWR_CONV o_DEF THENC
               ABS_CONV(RAND_CONV BETA_CONV))) THENC
             REWR_CONV GENLIST_EL_ZIP_lemma THENC
             PATH_CONV"lllrararaararaa" (
               PAIRED_BETA_CONV THENC
               PATH_CONV"llr"(
                 REWR_CONV word_allocTheory.oracle_colour_ok_def THENC
                 REWR_CONV(CONJUNCT2 option_case_def) THENC
                 BETA_CONV))) THENC
           REWR_CONV LET_THM THENC BETA_CONV THENC
           REWR_CONV LET_THM THENC BETA_CONV))

    val tm3 = compile_thm0 |> rconc |> rand
    val check_fn = tm3 |> funpow 3 rator |> rand
    val check_fn_def = mk_abbrev"check_fn"check_fn;
    val temp_defs = "check_fn_def" :: temp_defs

    fun eval_fn i n (a,b,c) =
      let val tm = list_mk_comb(check_fn,[a,b,c])
      in eval tm end

    val x64_oracle_list_els =
      x64_oracle_list_def |> rconc |> listSyntax.dest_list |> #1
    val word_prog1_els =
       word_prog1_def |> rconc |> listSyntax.dest_list |> #1
    val word_prog0_els =
       word_prog0_def |> rconc |> listSyntax.dest_list |> #1

    val lss = zip3
      (x64_oracle_list_els, word_prog1_els, word_prog0_els)

    val map3els = time_with_size thms_size "apply colour (par)"
                    (parl eval_fn) lss

    val word_prog1_defs = make_abbrevs "word_prog1_el_" num_progs word_prog1_els []
    val temp_defs = List.tabulate(num_progs,(fn i => "word_prog1_el_"^(Int.toString(i+1))^"_def")) @ temp_defs

    val word_prog1_thm =
      word_prog1_def |> CONV_RULE(RAND_CONV(intro_abbrev (List.rev word_prog1_defs)))

    val map3els' =
      mapi (fn i =>
        CONV_RULE(
          LAND_CONV(
            funpow 3 RATOR_CONV(REWR_CONV(SYM check_fn_def)) THENC
            RATOR_CONV(RAND_CONV(REWR_CONV(SYM(List.nth(word_prog1_defs,i))))))))
      map3els

      local
        val next_thm = ref map3els'
        val remain = ref num_progs
        (*
        fun str n =
          String.concat[Int.toString n,if n mod 10 = 0 then "\n" else " "]
        *)
        fun el_conv _ =
          case !next_thm of th :: rest =>
            let
              val () = next_thm := rest
              (*
              val () = Lib.say(str (!remain))
              *)
              val () = remain := !remain-1
            in th end
      in
        val map3_conv = MAP3_CONV el_conv
      end

      val compile_thm1 =
        compile_thm0
        |> CONV_RULE(RAND_CONV(
             RAND_CONV (
               RATOR_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM check_fn_def))))) THENC
               RAND_CONV(REWR_CONV word_prog0_def) THENC
               RATOR_CONV(RAND_CONV(REWR_CONV word_prog1_thm)) THENC
               RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV x64_oracle_list_def))) THENC
               timez "check colour" map3_conv)))

      val word_prog2_def = mk_abbrev"word_prog2" (compile_thm1 |> rconc |> rand);
      val temp_defs = "word_prog2_def" :: temp_defs

      val compile_thm1' = compile_thm1
        |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM word_prog2_def))))

      val () = computeLib.extend_compset[computeLib.Defs[word_prog2_def]] cs;

      (* slow; cannot parallelise easily due to bitmaps accumulator *)
      val from_word_thm =
        compile_thm1'
        |> CONV_RULE(RAND_CONV(
             REWR_CONV from_word_def THENC
             REWR_CONV LET_THM THENC
             RAND_CONV(timez "word_to_stack" eval) THENC
             PAIRED_BETA_CONV THENC
             REWR_CONV LET_THM THENC
             BETA_CONV))

      val stack_prog_def = mk_abbrev"stack_prog" (from_word_thm |> rconc |> rand);
      val temp_defs = "stack_prog_def" :: temp_defs

      val from_word_thm' = from_word_thm
        |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM stack_prog_def))))

      val () = computeLib.extend_compset[computeLib.Defs[stack_prog_def]] cs;

      val bare_cs = wordsLib.words_compset()
      val () =
        computeLib.extend_compset[
          computeLib.Extenders[compilerComputeLib.add_compiler_compset]]
        bare_cs
      val bare_eval = computeLib.CBV_CONV bare_cs

      val stack_to_lab_thm0 =
        from_word_thm'
        |> timez "expand stack_to_lab_def" (CONV_RULE(RAND_CONV(
             REWR_CONV from_stack_def THENC
             RAND_CONV bare_eval THENC
             REWR_CONV LET_THM THENC BETA_CONV THENC
             RAND_CONV(RATOR_CONV(RAND_CONV eval)) THENC
             RAND_CONV(funpow 2 RATOR_CONV(RAND_CONV bare_eval)) THENC
             RAND_CONV(funpow 3 RATOR_CONV(RAND_CONV bare_eval)) THENC
             RAND_CONV(funpow 4 RATOR_CONV(RAND_CONV bare_eval)) THENC
             REWR_CONV LET_THM THENC BETA_CONV)))

      val tm4 = stack_to_lab_thm0 |> rconc |> rand

      val prog_comp_tm =
        stack_allocTheory.prog_comp_def
        |> SPEC_ALL |> concl |> lhs |> strip_comb |> #1
        |> inst[alpha |-> fcpSyntax.mk_int_numeric_type 64]

      fun eval_fn i n p =
        let val tm = mk_comb(prog_comp_tm,p)
        in eval tm end

      val stack_prog_els =
        stack_prog_def |> rconc |> listSyntax.dest_list |> #1

      val ths = time_with_size thms_size "stack_alloc (par)"
                  (parl eval_fn) stack_prog_els;

      val stack_alloc_thm =
        tm4 |>
        (REWR_CONV stack_to_labTheory.compile_def THENC
         RAND_CONV(
           REWR_CONV stack_allocTheory.compile_def THENC
           FORK_CONV(eval,
             RAND_CONV(REWR_CONV stack_prog_def) THENC
             map_ths_conv ths) THENC
           listLib.APPEND_CONV))

      val stack_alloc_prog_def =
        mk_abbrev"stack_alloc_prog" (stack_alloc_thm |> rconc |> rand);
      val temp_defs = "stack_alloc_prog_def" :: temp_defs

      val stack_to_lab_thm1 =
        stack_to_lab_thm0
        |> CONV_RULE(RAND_CONV(
             RAND_CONV (
               REWR_CONV stack_alloc_thm THENC
               RAND_CONV(REWR_CONV(SYM stack_alloc_prog_def)) THENC
               REWR_CONV LET_THM THENC BETA_CONV)))

      val tm5 = stack_to_lab_thm1 |> rconc |> rand

      val stack_remove_thm0 =
        tm5 |>
        timez "expand stack_remove_def"(
        (RAND_CONV(
          RATOR_CONV(RAND_CONV eval) THENC
          funpow 3 RATOR_CONV(RAND_CONV bare_eval) THENC
          funpow 4 RATOR_CONV(RAND_CONV eval) THENC
          REWR_CONV stack_removeTheory.compile_def THENC
          LAND_CONV eval)))

      val tm6 = stack_remove_thm0 |> rconc |> rand |> rand

      val prog_comp_n_tm = tm6 |> rator |> rand

      fun eval_fn i n p =
        let val tm = mk_comb(prog_comp_n_tm,p)
        in  eval tm end

      val stack_alloc_prog_els =
        stack_alloc_prog_def |> rconc |> listSyntax.dest_list |> #1

      val ths = time_with_size thms_size "stack_remove (par)"
                  (parl eval_fn) stack_alloc_prog_els;

      val stack_remove_thm =
        stack_remove_thm0
        |> CONV_RULE(RAND_CONV(
           RAND_CONV(
             RAND_CONV (
               RAND_CONV(REWR_CONV stack_alloc_prog_def) THENC
               map_ths_conv ths) THENC
             listLib.APPEND_CONV)))

      val stack_remove_prog_def =
        mk_abbrev"stack_remove_prog" (stack_remove_thm |> rconc |> rand);
      val temp_defs = "stack_remove_prog_def" :: temp_defs

      val stack_to_lab_thm2 =
        stack_to_lab_thm1
        |> CONV_RULE(RAND_CONV(
             RAND_CONV(
               REWR_CONV stack_remove_thm THENC
               RAND_CONV(REWR_CONV(SYM stack_remove_prog_def)) THENC
               REWR_CONV LET_THM THENC BETA_CONV THENC
               RAND_CONV(RATOR_CONV(RAND_CONV eval)) THENC
               REWR_CONV LET_THM THENC BETA_CONV THENC
               RAND_CONV(REWR_CONV stack_namesTheory.compile_def))))

      val tm7 = stack_to_lab_thm2 |> rconc |> rand |> rand

      val prog_comp_nm_tm = tm7 |> rator |> rand

      fun eval_fn i n p =
        let val tm = mk_comb(prog_comp_nm_tm,p)
        in eval tm end

      val stack_remove_prog_els =
        stack_remove_prog_def |> rconc |> listSyntax.dest_list |> #1

      val ths = time_with_size thms_size "stack_names (par)"
                   (parl eval_fn) stack_remove_prog_els;

      val stack_names_thm0 =
        tm7
        |> (RAND_CONV(REWR_CONV stack_remove_prog_def) THENC
            map_ths_conv ths)

      val stack_names_prog_def =
        mk_abbrev"stack_names_prog" (stack_names_thm0 |> rconc);
      val temp_defs = "stack_names_prog_def" :: temp_defs

      val stack_names_thm = stack_names_thm0
        |> CONV_RULE(RAND_CONV(REWR_CONV(SYM stack_names_prog_def)))

      val stack_to_lab_thm3 =
        stack_to_lab_thm2
        |> CONV_RULE(RAND_CONV(RAND_CONV(
             RAND_CONV(REWR_CONV stack_names_thm))))

      val tm8 = stack_to_lab_thm3 |> rconc |> rand

      val prog_to_section_tm = tm8 |> rator |> rand

      fun eval_fn i n p =
        let val tm = mk_comb(prog_to_section_tm,p)
        in  eval tm end

      val stack_names_prog_els =
        stack_names_prog_def |> rconc |> listSyntax.dest_list |> #1

      val ths = time_with_size thms_size "stack_to_lab (par)"
                  (parl eval_fn) stack_names_prog_els;

      val stack_to_lab_thm4 =
        stack_to_lab_thm3
        |> CONV_RULE(RAND_CONV(RAND_CONV(
             RAND_CONV(REWR_CONV stack_names_prog_def) THENC
             map_ths_conv ths)))

      val lab_prog_def = mk_abbrev"lab_prog" (stack_to_lab_thm4 |> rconc |> rand);

      val stack_to_lab_thm =
        stack_to_lab_thm4 |>
        CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM lab_prog_def))))

      val () = List.app delete_binding temp_defs

  in stack_to_lab_thm end

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

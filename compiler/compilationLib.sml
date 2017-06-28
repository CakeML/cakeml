structure compilationLib = struct

open preamble backendTheory
     arm6_compileLib arm6_exportLib
     arm8_compileLib arm8_exportLib
     mips_compileLib mips_exportLib
     riscv_compileLib riscv_exportLib
     x64_compileLib x64_exportLib

val _ = Globals.max_print_depth := 20;

fun compilation_compset() =
  let
    val cs = wordsLib.words_compset();
    val () = computeLib.extend_compset
      [computeLib.Extenders [
        basicComputeLib.add_basic_compset,
        semanticsComputeLib.add_ast_compset,
        backendComputeLib.add_backend_compset,
        asmLib.add_asm_compset ]
      ] cs
  in cs end;

val bare_compiler_cs = wordsLib.words_compset()
val () =
  computeLib.extend_compset[
    computeLib.Extenders[backendComputeLib.add_backend_compset]]
  bare_compiler_cs
val bare_compiler_eval = computeLib.CBV_CONV bare_compiler_cs

fun REWR_CONV_BETA th tm = Thm.Beta (REWR_CONV th tm)

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
      |> CONV_RULE(RAND_CONV(REWR_CONV_BETA LET_THM))
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
      |> CONV_RULE(RAND_CONV(REWR_CONV_BETA LET_THM))
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
      REWR_CONV_BETA LET_THM))

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
          REWR_CONV_BETA LET_THM)
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

fun compile_to_lab data_prog_def to_data_thm lab_prog_name =
  let
    val cs = compilation_compset()
    val () =
      computeLib.extend_compset [
        computeLib.Extenders [
          arm6_targetLib.add_arm6_encode_compset,
          arm8_targetLib.add_arm8_encode_compset,
          mips_targetLib.add_mips_encode_compset,
          riscv_targetLib.add_riscv_encode_compset,
          x64_targetLib.add_x64_encode_compset],
        computeLib.Defs [
          arm6_backend_config_def, arm6_names_def,
          arm8_backend_config_def, arm8_names_def,
          mips_backend_config_def, mips_names_def,
          riscv_backend_config_def, riscv_names_def,
          x64_backend_config_def, x64_names_def,
          data_prog_def ]
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
          REWR_CONV_BETA LET_THM THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC
          PATH_CONV "rlrraraalralrarllr" eval THENC
          PATH_CONV"rlrraraalralralralralrar"
            (RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
             (FIRST_CONV (map REWR_CONV (CONJUNCTS bool_case_thm)))))
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
    val temp_defs = (mk_abbrev_name"word_prog0")::temp_defs;

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
    val temp_defs = (mk_abbrev_name"clash_fn")::temp_defs;
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

    val oracle_def = mk_abbrev"oracle" oracles;

    val wc =
      ``^conf_tm.word_to_word_conf
        with col_oracle := oracle``
      |> eval |> rconc

    val args = to_livesets_thm |> concl |> lhs |> strip_comb |> #2

    val word_prog1_def = mk_abbrev"word_prog1"(thm2 |> rconc);
    val temp_defs = (mk_abbrev_name"word_prog1") :: temp_defs

    val to_livesets_thm' =
      to_livesets_thm
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"lrr"(REWR_CONV(SYM word_prog1_def))))

    val to_livesets_oracle_thm =
      to_livesets_invariant
      |> Q.GEN`wc` |> SPEC wc
      |> Q.GENL[`c`,`p`] |> ISPECL args
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
      |> ISPEC (lhs(concl(oracle_def)))

    val oracle_list_def = mk_abbrev"oracle_list" (oracle_def |> rconc |> rand);
    val temp_defs = (mk_abbrev_name"oracle_list") :: temp_defs

    val oracle_thm = Q.prove(
      `n < LENGTH oracle_list ⇒
       (oracle n = SOME (EL n oracle_list))`,
      strip_tac
      \\ CONV_TAC(LAND_CONV(
           RATOR_CONV(REWR_CONV oracle_def THENC
                      REWR_CONV LET_THM THENC
                      (RAND_CONV(REWR_CONV(SYM oracle_list_def))) THENC
                      BETA_CONV)
           THENC BETA_CONV))
      \\ rw[]);

    val LENGTH_oracle_list =
      listSyntax.mk_length(lhs(concl(oracle_list_def)))
      |> (RAND_CONV(REWR_CONV oracle_list_def) THENC
          listLib.LENGTH_CONV)

    val GENLIST_EL_ZIP_lemma = Q.prove(
      `(LENGTH l1 = n) ∧ (LENGTH l2 = n) ∧ (LENGTH oracle_list = n) ⇒
       (GENLIST (λx. f (oracle x, EL x (ZIP (l1,l2)))) n =
        MAP3 (λa (b1,b2,b3) (c1,c2,c3). f (SOME a, ((b1,b2,b3), (c1,c2,c3)))) oracle_list l1 l2)`,
      rw[LIST_EQ_REWRITE,EL_MAP3,EL_ZIP,oracle_thm,UNCURRY])
      |> C MATCH_MP (CONJ LENGTH_word_prog1 (CONJ LENGTH_word_prog0 LENGTH_oracle_list))

    val compile_thm0 =
      compile_oracle |> SYM
      |> Q.GENL[`c`,`p`] |> ISPECL args
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
           REWR_CONV_BETA LET_THM THENC
           REWR_CONV_BETA LET_THM THENC
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
                 REWR_CONV_BETA(CONJUNCT2 option_case_def)))) THENC
           REWR_CONV_BETA LET_THM THENC
           REWR_CONV_BETA LET_THM))

    val tm3 = compile_thm0 |> rconc |> rand
    val check_fn = tm3 |> funpow 3 rator |> rand
    val check_fn_def = mk_abbrev"check_fn"check_fn;
    val temp_defs = (mk_abbrev_name"check_fn") :: temp_defs

    fun eval_fn i n (a,b,c) =
      let val tm = list_mk_comb(check_fn,[a,b,c])
      in eval tm end

    val oracle_list_els =
      oracle_list_def |> rconc |> listSyntax.dest_list |> #1
    val word_prog1_els =
       word_prog1_def |> rconc |> listSyntax.dest_list |> #1
    val word_prog0_els =
       word_prog0_def |> rconc |> listSyntax.dest_list |> #1

    val lss = zip3
      (oracle_list_els, word_prog1_els, word_prog0_els)

    val map3els = time_with_size thms_size "apply colour (par)"
                    (parl eval_fn) lss

    val word_prog1_defs = make_abbrevs "word_prog1_el_" num_progs word_prog1_els []
    val temp_defs = List.tabulate(num_progs,(fn i => mk_abbrev_name("word_prog1_el_"^(Int.toString(i+1))))) @ temp_defs

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
               RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV oracle_list_def))) THENC
               timez "check colour" map3_conv)))

      val word_prog2_def = mk_abbrev"word_prog2" (compile_thm1 |> rconc |> rand);
      val temp_defs = (mk_abbrev_name"word_prog2") :: temp_defs

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
             REWR_CONV_BETA LET_THM))

      val stack_prog_def = mk_abbrev"stack_prog" (from_word_thm |> rconc |> rand);
      val temp_defs = (mk_abbrev_name"stack_prog") :: temp_defs

      val from_word_thm' = from_word_thm
        |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM stack_prog_def))))

      val () = computeLib.extend_compset[computeLib.Defs[stack_prog_def]] cs;

      val stack_to_lab_thm0 =
        from_word_thm'
        |> timez "expand stack_to_lab_def" (CONV_RULE(RAND_CONV(
             REWR_CONV from_stack_def THENC
             RAND_CONV bare_compiler_eval THENC
             REWR_CONV_BETA LET_THM THENC
             RAND_CONV(RATOR_CONV(RAND_CONV eval)) THENC
             RAND_CONV(funpow 2 RATOR_CONV(RAND_CONV bare_compiler_eval)) THENC
             RAND_CONV(funpow 3 RATOR_CONV(RAND_CONV bare_compiler_eval)) THENC
             RAND_CONV(funpow 4 RATOR_CONV(RAND_CONV bare_compiler_eval)) THENC
             REWR_CONV_BETA LET_THM)))

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
      val temp_defs = (mk_abbrev_name"stack_alloc_prog") :: temp_defs

      val stack_to_lab_thm1 =
        stack_to_lab_thm0
        |> CONV_RULE(RAND_CONV(
             RAND_CONV (
               REWR_CONV stack_alloc_thm THENC
               RAND_CONV(REWR_CONV(SYM stack_alloc_prog_def)) THENC
               REWR_CONV_BETA LET_THM)))

      val tm5 = stack_to_lab_thm1 |> rconc |> rand

      val stack_remove_thm0 =
        tm5 |>
        timez "expand stack_remove_def"(
        (RAND_CONV(
          RATOR_CONV(RAND_CONV eval) THENC
          funpow 3 RATOR_CONV(RAND_CONV bare_compiler_eval) THENC
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
      val temp_defs = (mk_abbrev_name"stack_remove_prog") :: temp_defs

      val stack_to_lab_thm2 =
        stack_to_lab_thm1
        |> CONV_RULE(RAND_CONV(
             RAND_CONV(
               REWR_CONV stack_remove_thm THENC
               RAND_CONV(REWR_CONV(SYM stack_remove_prog_def)) THENC
               REWR_CONV_BETA LET_THM THENC
               RAND_CONV(RATOR_CONV(RAND_CONV eval)) THENC
               REWR_CONV_BETA LET_THM THENC
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
      val temp_defs = (mk_abbrev_name"stack_names_prog") :: temp_defs

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

      val lab_prog_def = mk_abbrev lab_prog_name (stack_to_lab_thm4 |> rconc |> rand);

      val stack_to_lab_thm =
        stack_to_lab_thm4 |>
        CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM lab_prog_def))))

      val () = List.app delete_binding temp_defs

  in stack_to_lab_thm end

val spec64 = INST_TYPE[alpha |-> fcpSyntax.mk_int_numeric_type 64]
val (COND_T,COND_F) = COND_CLAUSES |> SPEC_ALL |> CONJ_PAIR;
val (T_AND::AND_T::_) = AND_CLAUSES |> SPEC_ALL |> CONJUNCTS;
val [ela1,ela2,ela3,ela4] = CONJUNCTS lab_to_targetTheory.enc_lines_again_def;
val (cln,clc) =
  lab_to_targetTheory.compute_labels_alt_def |> spec64 |> CONJ_PAIR
val (esn,esc) = lab_to_targetTheory.enc_secs_again_def |> spec64 |> CONJ_PAIR
val (uln,ulc) = lab_to_targetTheory.upd_lab_len_def |> spec64 |> CONJ_PAIR
val [lul1,lul2,lul3,lul4] = CONJUNCTS lab_to_targetTheory.lines_upd_lab_len_def;

val add_pos_conv = PATH_CONV "llr" numLib.REDUCE_CONV

val extract_ffi_names = map stringSyntax.fromHOLstring o fst o listSyntax.dest_list
val extract_bytes_ffis = pairSyntax.dest_pair o optionSyntax.dest_some o rconc

fun to_bytes_x64 stack_to_lab_thm lab_prog_def heap_mb stack_mb filename =
  let
    val cs = compilation_compset()
    val () =
      computeLib.extend_compset [
        computeLib.Extenders [
          x64_targetLib.add_x64_encode_compset ],
        computeLib.Defs [
          x64_backend_config_def,
          x64_names_def ]
      ] cs
    val eval = computeLib.CBV_CONV cs;
    fun parl f = parlist (!num_threads) (!chunk_size) f

    val lab_to_target_thm0 =
      stack_to_lab_thm
      |> CONV_RULE(RAND_CONV(
           REWR_CONV from_lab_def THENC
           RATOR_CONV(RAND_CONV bare_compiler_eval)))

    val tm9 = lab_to_target_thm0 |> rconc

    val lab_prog_els =
      lab_prog_def |> rconc |> listSyntax.dest_list |> #1

    val filter_skip_lab_prog =
      ISPEC(lhs(concl(lab_prog_def)))lab_filterTheory.filter_skip_MAP

    val filter_skip_fn =
      filter_skip_lab_prog |> rconc |> rator |> rand

    fun eval_fn i n p =
      let val tm = mk_comb(filter_skip_fn,p)
      in eval tm end

    val ths = time_with_size thms_size "filter_skip (par)"
                (parl eval_fn) lab_prog_els;

    val filter_skip_thm =
      tm9 |> (
        REWR_CONV lab_to_targetTheory.compile_def THENC
        RAND_CONV(
          REWR_CONV filter_skip_lab_prog THENC
          RAND_CONV(REWR_CONV lab_prog_def) THENC
          map_ths_conv ths))

    val skip_prog_def = mk_abbrev"skip_prog" (filter_skip_thm |> rconc |> rand);
    val temp_defs = [mk_abbrev_name"skip_prog"]

    val filter_skip_thm' = filter_skip_thm
      |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM skip_prog_def))))

    (* could parallelise? *)
    val ffi_names_thm =
      ``find_ffi_names skip_prog``
      |> (RAND_CONV(REWR_CONV skip_prog_def) THENC timez "ffi_names" eval)

    val lab_to_target_thm1 =
      lab_to_target_thm0
      |> CONV_RULE (RAND_CONV(
         REWR_CONV filter_skip_thm' THENC
         REWR_CONV lab_to_targetTheory.compile_lab_def THENC
         RAND_CONV(REWR_CONV ffi_names_thm) THENC
         REWR_CONV_BETA LET_THM))

    val tm10 = lab_to_target_thm1 |> rconc |> rator |> rator |> rand

    val remove_labels_thm0 =
      tm10 |>
      (REWR_CONV lab_to_targetTheory.remove_labels_def THENC
       RAND_CONV(
         REWR_CONV lab_to_targetTheory.enc_sec_list_def THENC
         RAND_CONV eval THENC
         REWR_CONV_BETA LET_THM THENC
         PATH_CONV"lrlr"eval) THENC
       PATH_CONV"llr"eval)

    val tm11 = remove_labels_thm0 |> rconc |> rand

    val enc_sec_tm = tm11 |> rator |> rand

    val skip_prog_els = skip_prog_def |> rconc |> listSyntax.dest_list |> #1

    fun eval_fn i n p =
      let val tm = mk_comb(enc_sec_tm,p)
      in eval tm end

    val ths = time_with_size thms_size "enc_sec (par)"
                (parl eval_fn) skip_prog_els;

    val remove_labels_thm1 =
      remove_labels_thm0
      |> CONV_RULE(RAND_CONV(
           RAND_CONV(
             RAND_CONV(REWR_CONV skip_prog_def) THENC
             map_ths_conv ths)))

    val encoded_prog_def = mk_abbrev"encoded_prog" (remove_labels_thm1 |> rconc |> rand);
    val temp_defs = (mk_abbrev_name"encoded_prog") :: temp_defs

    val remove_labels_thm1' =
      remove_labels_thm1 |>
      CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM encoded_prog_def))))

    val lab_to_target_thm2 =
      lab_to_target_thm1
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"llr"(
             REWR_CONV remove_labels_thm1' THENC
             REWR_CONV lab_to_targetTheory.remove_labels_loop_def THENC
             REWR_CONV LET_THM)))

    val tm12 =
      lab_to_target_thm2 |> rconc
      |> funpow 2 rator
      |> funpow 2 rand

    val encoded_prog_els =
      encoded_prog_def |> rconc |> listSyntax.dest_list |> #1

    val encoded_prog_lines = encoded_prog_els |> map rand

    val num_enc = length encoded_prog_els
    val encoded_prog_defs = make_abbrevs "encoded_prog_el" num_enc encoded_prog_lines []
    val temp_defs = List.tabulate(num_enc,(fn i => mk_abbrev_name("encoded_prog_el"^(Int.toString(i+1))))) @ temp_defs

    val Section_encoded_prog_defs =
      map2 AP_TERM (map rator encoded_prog_els) (List.rev encoded_prog_defs)

    val encoded_prog_thm =
      encoded_prog_def |>
          CONV_RULE(RAND_CONV(intro_abbrev Section_encoded_prog_defs))

    fun compute_labels_alt_rule [] th = th |> CONV_RULE (RAND_CONV (REWR_CONV cln))
      | compute_labels_alt_rule (dth::dths) th =
        let
          val th1 = th |> CONV_RULE (
            RAND_CONV (
              REWR_CONV clc THENC
              RAND_CONV (RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC eval) THENC
              REWR_CONV LET_THM THENC
              PAIRED_BETA_CONV THENC
              RAND_CONV eval))
        in compute_labels_alt_rule dths th1 end

    val compute_labels_thm =
      tm12 |> timez "compute_labels" (fn tm =>
        let
          val th = RATOR_CONV(RAND_CONV(REWR_CONV encoded_prog_thm)) tm
        in compute_labels_alt_rule (List.rev encoded_prog_defs) th end)

    val computed_labs_def = mk_abbrev"computed_labs"(compute_labels_thm |> rconc)
    val temp_defs = (mk_abbrev_name"computed_labs") :: temp_defs
    val compute_labels_thm' =
      compute_labels_thm |>
      CONV_RULE(RAND_CONV(REWR_CONV(SYM computed_labs_def)))

    val lab_to_target_thm3 =
      lab_to_target_thm2
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"llr"(
             RAND_CONV(REWR_CONV compute_labels_thm') THENC
             BETA_CONV)))

    val tm13 =
      lab_to_target_thm3 |> rconc |> funpow 2 rator |> funpow 2 rand

    fun enc_secs_again_conv str ela_conv n [] tm = REWR_CONV esn tm
      | enc_secs_again_conv str ela_conv n (dth::dths) tm =
        let
          val th1 = tm |>
           (REWR_CONV esc THENC
            RAND_CONV(
              RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
              ela_conv))
          val def = mk_abbrev(str^Int.toString n)
                      (th1 |> rconc |> rand |> rator |> rand)
          (* val () = print (String.concat[Int.toString n," "]) *)
          val rec_conv = enc_secs_again_conv str ela_conv (n+1) dths
        in
          th1 |> CONV_RULE(RAND_CONV(
            RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM def)))) THENC
            let_CONV THENC
            RAND_CONV rec_conv THENC
            let_CONV THENC
            RAND_CONV(REWR_CONV T_AND)))
        end

    val enc_secs_again_thm =
      tm13 |> timez "enc_secs_again" (
        RAND_CONV(REWR_CONV encoded_prog_thm) THENC
        enc_secs_again_conv
          "enc_again_"
          (* (enc_lines_again_conv computed_labs_def) *)
          (PATH_CONV "lllllr" (REWR_CONV computed_labs_def) THENC eval)
          0
          (List.rev encoded_prog_defs))
    val temp_defs = List.tabulate(num_enc,(fn i => mk_abbrev_name("enc_again"^(Int.toString i)))) @ temp_defs

    val lab_to_target_thm4 =
      lab_to_target_thm3
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"llr"(
             RAND_CONV(REWR_CONV enc_secs_again_thm) THENC
             REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
             REWR_CONV COND_T THENC
             REWR_CONV LET_THM)))

    val tm14 =
      lab_to_target_thm4 |> rconc |> funpow 2 rator |> funpow 2 rand

    val enc_again_defs =
      for 0 (num_enc-1) (fn i => definition(mk_abbrev_name("enc_again_"^(Int.toString i))))

    fun lines_upd_lab_len_rule th =
      CONV_RULE(RAND_CONV (REWR_CONV lul1 THENC RATOR_CONV(RAND_CONV eval))) th
      handle HOL_ERR _ =>
      let
        val th =
        CONV_RULE(RAND_CONV (REWR_CONV lul2 THENC
          RAND_CONV eval THENC REWR_CONV LET_THM THENC BETA_CONV THENC
          add_pos_conv)) th
        handle HOL_ERR _ =>
        CONV_RULE(RAND_CONV (REWR_CONV lul3 THENC add_pos_conv)) th
        handle HOL_ERR _ =>
        CONV_RULE(RAND_CONV (REWR_CONV lul4 THENC add_pos_conv)) th
      in lines_upd_lab_len_rule th end

    val lines_upd_lab_len_conv = lines_upd_lab_len_rule o REFL

    (*
    val tm = tm14
    val (dth::_) = enc_again_defs
    val n = 0
    *)

    fun upd_lab_len_conv _ [] tm = REWR_CONV uln tm
      | upd_lab_len_conv n (dth::dths) tm =
        let
          val th1 =
            tm |> (
              REWR_CONV ulc THENC
              RAND_CONV(
                RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
                lines_upd_lab_len_conv))
          val def = mk_abbrev ("upd_lab_"^(Int.toString n)) (rand(rator(rand(rconc th1))))
        in
          th1 |> CONV_RULE(RAND_CONV(
            RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM def)))) THENC
            REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
            REWR_CONV LET_THM THENC
            RAND_CONV(upd_lab_len_conv (n+1) dths) THENC
            BETA_CONV))
        end

    val upd_lab_len_thm =
      tm14 |> timez "upd_lab_len" (upd_lab_len_conv 0 enc_again_defs)
    val temp_defs = List.tabulate(num_enc,(fn i => mk_abbrev_name("upd_lab_"^(Int.toString i)))) @ temp_defs

    val lab_to_target_thm5 =
      lab_to_target_thm4
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"llr"(
             RAND_CONV(REWR_CONV upd_lab_len_thm) THENC
             BETA_CONV)))

    val tm15 =
      lab_to_target_thm5 |> rconc |> funpow 2 rator |> funpow 2 rand

    val upd_lab_defs =
      for 0 (num_enc-1) (fn i => definition(mk_abbrev_name("upd_lab_"^(Int.toString i))))

    val compute_labels_thm2 =
      tm15 |> timez "compute_labels2" (compute_labels_alt_rule upd_lab_defs o REFL)

    val computed_labs2_def = mk_abbrev"computed_labs2"(compute_labels_thm2 |> rconc)
    val temp_defs = (mk_abbrev_name"computed_labs2") :: temp_defs
    val compute_labels_thm2' =
      compute_labels_thm2 |>
      CONV_RULE(RAND_CONV(REWR_CONV(SYM computed_labs2_def)))

    val lab_to_target_thm6 =
      lab_to_target_thm5
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"llr" (
             RAND_CONV (REWR_CONV compute_labels_thm2') THENC
             REWR_CONV_BETA LET_THM)))

    val tm16 =
      lab_to_target_thm6 |> rconc |> funpow 2 rator |> funpow 2 rand

    val enc_secs_again_thm2 =
      tm16 |> timez "enc_secs_again2" (enc_secs_again_conv
        "enc_again2_"
        (*(enc_lines_again_conv computed_labs2_def)*)
        (PATH_CONV "lllllr" (REWR_CONV computed_labs2_def) THENC eval)
        0
        upd_lab_defs)
    val temp_defs = List.tabulate(num_enc,(fn i => mk_abbrev_name("enc_again2_"^(Int.toString i)))) @ temp_defs

    val lab_to_target_thm7 =
      lab_to_target_thm6 |> CONV_RULE(RAND_CONV(
        PATH_CONV"llr"(
          RAND_CONV(REWR_CONV enc_secs_again_thm2) THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          REWR_CONV LET_THM THENC
          RAND_CONV(RATOR_CONV(REWR_CONV lab_to_targetTheory.pad_code_MAP)))))

    val tm17 =
      lab_to_target_thm7 |> rconc |> funpow 2 rator |> funpow 2 rand

    val () = PolyML.fullGC();

    val pad_section_tm =
      tm17 |> rator |> rand

    val enc_again2_defs =
      for 0 (num_enc-1) (fn i => definition(mk_abbrev_name("enc_again2_"^(Int.toString i))));

    (*
    val (dth::_) = enc_again2_defs
    val p = tm17 |> rand |> rator |> rand
    *)

    fun eval_fn i n (dth, p) =
      let
        val tm = mk_comb(pad_section_tm,p)
        val conv =
          BETA_CONV THENC
          RATOR_CONV(RAND_CONV(REWR_CONV labLangTheory.Section_num_def)) THENC
          RAND_CONV(
            RATOR_CONV(RAND_CONV(
              REWR_CONV labLangTheory.Section_lines_def THENC
              REWR_CONV dth)) THENC eval)
      in conv tm end

    val enc_again2_els =
      tm17 |> rand |> listSyntax.dest_list |> #1

    val pad_code_thms =
      time_with_size thms_size "pad_section" (parl eval_fn)
        (zip enc_again2_defs enc_again2_els);

    val pad_code_defs =
      make_abbrevs "pad_code_" num_enc (pad_code_thms |> map (rand o rconc)) [];
    val temp_defs = List.tabulate(num_enc,(fn i => mk_abbrev_name("pad_code_"^(Int.toString (i+1))))) @ temp_defs

    val pad_code_thms' =
        map2 (CONV_RULE o RAND_CONV o RAND_CONV o REWR_CONV o SYM)
          (List.rev pad_code_defs) pad_code_thms;

    val pad_code_thm =
      tm17 |> (map_ths_conv pad_code_thms')

    val padded_code_def = mk_abbrev"padded_code"(rconc pad_code_thm);
    val temp_defs = (mk_abbrev_name"padded_code") :: temp_defs

    val pad_code_thm' =
      pad_code_thm |> CONV_RULE(RAND_CONV(REWR_CONV(SYM padded_code_def)))

    val lab_to_target_thm8 =
      lab_to_target_thm7
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"llr"(
             RAND_CONV(REWR_CONV pad_code_thm') THENC
             BETA_CONV THENC
             RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV T_AND))))))

    val tm18 =
      lab_to_target_thm8 |> rconc
      |> funpow 2 rator |> rand
      |> funpow 2 rator |> rand

    val assum_all_enc_ok_light_lab_to_target_thm =
      lab_to_target_thm8 |> DISCH ``all_enc_ok_light x64_config padded_code`` |>
      CONV_RULE (SIMP_CONV std_ss [pair_case_def,lab_to_targetTheory.prog_to_bytes_MAP])
      |> UNDISCH

    val tm19 =
      assum_all_enc_ok_light_lab_to_target_thm |> rconc |> rand |> rator |> rand |> rand

    val line_bytes_tm =
      tm19 |> rator |> rand

    val padded_code_els =
      padded_code_def |> rconc |> listSyntax.dest_list |> #1

    val pad_code_defs =
      for 1 num_enc (fn i => definition(mk_abbrev_name("pad_code_"^(Int.toString i))));

    (*
      val p = el 1 padded_code_els
      val dth = el 1 pad_code_defs
    *)

    fun eval_fn i n (p,dth) =
      let
        val tm = mk_comb(line_bytes_tm,p)
        val conv =
          (REWR_CONV o_THM THENC
           RAND_CONV(REWR_CONV o_THM) THENC
           RAND_CONV(RAND_CONV(REWR_CONV labLangTheory.Section_lines_def)) THENC
           RAND_CONV(RAND_CONV(REWR_CONV dth)) THENC eval)
        in conv tm end

    val line_bytes =
      time_with_size thms_size "prog_to_bytes (par)" (parl eval_fn)
        (zip padded_code_els pad_code_defs);

    val map_line_bytes =
      tm19 |>
        (RAND_CONV(REWR_CONV padded_code_def) THENC
         map_ths_conv line_bytes);

    val bytes_defs =
      make_abbrevs "bytes_" num_enc (map_line_bytes |> rconc |> listSyntax.dest_list |> #1) [];
    val temp_defs = List.tabulate(num_enc,(fn i => mk_abbrev_name("bytes_"^(Int.toString (i+1))))) @ temp_defs

    val map_line_bytes' =
      map_line_bytes |> CONV_RULE(RAND_CONV(intro_abbrev (List.rev bytes_defs)));

    fun app_conv _ [] tm = raise UNCHANGED
      | app_conv n (dth::dths) tm =
        let
          val th = FORK_CONV(REWR_CONV dth, app_conv (n+1) dths) tm
          val def = mk_abbrev ("all_bytes_"^(Int.toString n)) (rand(rconc th))
        in
          CONV_RULE(RAND_CONV
            (RAND_CONV(REWR_CONV(SYM def)) THENC listLib.APPEND_CONV))
          th
        end

    val flat_bytes =
      listSyntax.mk_flat(rconc map_line_bytes')
      |> (REWR_CONV FLAT_FOLDR
          THENC listLib.FOLDR_CONV (QCONV ALL_CONV) THENC
          timez "flat_bytes" (app_conv 0 (List.rev bytes_defs)));
    val temp_defs = List.tabulate(num_enc,(fn i => mk_abbrev_name("all_bytes_"^(Int.toString i)))) @ temp_defs

    fun expand_defs_conv [] tm = raise UNCHANGED
      | expand_defs_conv (dth::dths) tm =
        ((RAND_CONV(expand_defs_conv (dth::dths))) ORELSEC
         (REWR_CONV dth THENC expand_defs_conv dths))
        tm

    val all_bytes_defs =
      for 0 (num_enc-1) (fn i => definition(mk_abbrev_name("all_bytes_"^(Int.toString i))));

    val flat_bytes' =
      flat_bytes |> timez "expand_defs" (CONV_RULE(RAND_CONV(expand_defs_conv all_bytes_defs)));

    val assum_all_enc_ok_light_bootstrap_thm =
      assum_all_enc_ok_light_lab_to_target_thm
      |> CONV_RULE(RAND_CONV(
           PATH_CONV"rlr"(
             RAND_CONV(
               REWR_CONV map_line_bytes') THENC
             REWR_CONV flat_bytes')));

    val (bytes_tm,ffi_names_tm) =
      assum_all_enc_ok_light_bootstrap_thm |> rconc
      |> optionSyntax.dest_some
      |> pairSyntax.dest_pair

    val () = time (
      x64_exportLib.write_cake_S stack_mb heap_mb
        (extract_ffi_names ffi_names_tm) bytes_tm ) filename

    val sec_ok_light_tm =
      tm18 |> rator |> rand

    fun eval_T tm =
      let
        val th = eval tm
      in
        if aconv (rconc th) boolSyntax.T then th
        else raise (mk_HOL_ERR"compilationLib""to_bytes_x64.sec_ok"(Parse.thm_to_string th))
      end

    (*
      val p = el 5 padded_code_els
      val d = el 5 pad_code_defs
    *)

    fun eval_fn i n (p,d) =
      let
        val conv = (
          REWR_CONV lab_to_targetTheory.sec_ok_light_def THENC
          RAND_CONV (REWR_CONV d) THENC
          listLib.ALL_EL_CONV eval_T)
        val tm = mk_comb(sec_ok_light_tm, p)
      in
        conv tm
      end

    val pad_code_els_defs = zip padded_code_els pad_code_defs;

    val secs_ok = time_with_size thms_size "sec_ok (par)" (parl eval_fn) pad_code_els_defs;

    val all_secs_ok =
      time_with_size (term_size o concl) "all_secs_ok" (listLib.join_EVERY sec_ok_light_tm)
        (rev_itlist (cons o EQT_ELIM) secs_ok [])

    val encs_ok =
      tm18
      |> (RAND_CONV(REWR_CONV padded_code_def) THENC
          REWR_CONV (EQT_INTRO all_secs_ok))

    val thm =
      MP (DISCH_ALL assum_all_enc_ok_light_bootstrap_thm)
         (EQT_ELIM encs_ok)

    val () = List.app delete_binding temp_defs;
  in
    thm
  end

fun cbv_compile_to_data cs conf_def prog_def data_prog_name =
  let
    val () = computeLib.extend_compset
       [computeLib.Defs [conf_def, prog_def]] cs
    val eval = computeLib.CBV_CONV cs;
    val conf_tm = lhs(concl conf_def)
    val prog_tm = lhs(concl prog_def)
    val to_data_thm0 = timez "cbv_compile_to_data" eval ``to_data ^conf_tm ^prog_tm``;
    val (_,p) = to_data_thm0 |> rconc |> dest_pair
    val data_prog_def = mk_abbrev data_prog_name p
    val to_data_thm =
      to_data_thm0 |> CONV_RULE(RAND_CONV(
        RAND_CONV(REWR_CONV(SYM data_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [data_prog_def]] cs;
  in to_data_thm end

(* TODO: move? but may be unnecessary if cbv_compile_to_lab_x64 is unused *)
val compile_oracle_to_lab =
  let
    val from_livesets_unpaired =
    ``from_livesets x``
    |> (RAND_CONV(ONCE_REWRITE_CONV [GSYM PAIR] THENC
                  BINOP_CONV(ONCE_REWRITE_CONV[GSYM PAIR])) THENC
        REWR_CONV from_livesets_def)
  in
    compile_oracle |> SYM
    |> CONV_RULE(RAND_CONV(RATOR_CONV(REWR_CONV(GSYM ETA_AX))))
    |> CONV_RULE(RAND_CONV(REWR_CONV(GSYM LET_THM)))
    |> REWRITE_RULE[from_livesets_unpaired,from_word_def,from_stack_def]
    |> Q.GENL[`c`,`p`]
  end
(* -- *)

fun cbv_compile_to_lab_x64 data_prog_x64_def to_data_thm =
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

    val (_,[conf_tm,prog_tm]) =
      to_data_thm |> concl |> lhs |> strip_comb

    val to_livesets_thm =
      ``to_livesets ^conf_tm ^prog_tm``
      |> (REWR_CONV to_livesets_def THENC
          RAND_CONV (REWR_CONV to_data_thm) THENC
          REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
          eval)

    val oracles =
      to_livesets_thm
      |> rconc |> pairSyntax.dest_pair |> #1
      |> time_with_size term_size "external oracle" (reg_allocComputeLib.get_oracle 3)

    val wc = ``<|reg_alg:=3;col_oracle:= ^(oracles)|>``

    val to_livesets_thm1 =
      to_livesets_invariant
        |> Q.GENL[`c`,`p`,`wc`]
        |> ISPEC conf_tm
        |> Thm.Specialize prog_tm
        |> Thm.Specialize wc
        |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV to_livesets_thm)))

    val c = to_livesets_thm1 |> concl |> lhs |> rator |> rand
    val to_lab_thm =
      compile_oracle_to_lab |> ISPEC c |> Thm.Specialize prog_tm
      |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV to_livesets_thm1)))
    val () = computeLib.scrub_const cs (prim_mk_const{Thy="backend",Name="from_lab"})

    val to_lab_thm1 =
      to_lab_thm |> CONV_RULE(RAND_CONV eval)

    val lab_prog_def = mk_abbrev"lab_prog" (to_lab_thm1 |> rconc |> rand);

    val to_lab_thm2 =
      to_lab_thm1 |>
      CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM lab_prog_def))))
  in to_lab_thm2 end

fun cbv_to_bytes
      add_encode_compset backend_config_def names_def write_cake_S
      stack_to_lab_thm lab_prog_def heap_mb stack_mb filename =
  let
    val cs = compilation_compset()
    val () =
      computeLib.extend_compset [
        computeLib.Extenders [ add_encode_compset ],
        computeLib.Defs [ backend_config_def, names_def, lab_prog_def]
      ] cs
    val eval = computeLib.CBV_CONV cs;

    val bootstrap_thm =
      stack_to_lab_thm
      |> CONV_RULE(RAND_CONV(eval))

    val (bytes_tm,ffi_names_tm) = extract_bytes_ffis bootstrap_thm

    val () = time (
      write_cake_S stack_mb heap_mb
        (extract_ffi_names ffi_names_tm) bytes_tm ) filename
  in
    bootstrap_thm
  end

val cbv_to_bytes_arm8 =
  cbv_to_bytes
    arm8_targetLib.add_arm8_encode_compset
    arm8_backend_config_def arm8_names_def
    arm8_exportLib.write_cake_S

val cbv_to_bytes_arm6 =
  cbv_to_bytes
    arm6_targetLib.add_arm6_encode_compset
    arm6_backend_config_def arm6_names_def
    arm6_exportLib.write_cake_S

val cbv_to_bytes_mips =
  cbv_to_bytes
    mips_targetLib.add_mips_encode_compset
    mips_backend_config_def mips_names_def
    mips_exportLib.write_cake_S

val cbv_to_bytes_riscv =
  cbv_to_bytes
    riscv_targetLib.add_riscv_encode_compset
    riscv_backend_config_def riscv_names_def
    riscv_exportLib.write_cake_S

val cbv_to_bytes_x64 =
  cbv_to_bytes
    x64_targetLib.add_x64_encode_compset
    x64_backend_config_def x64_names_def
    x64_exportLib.write_cake_S

val intermediate_prog_prefix = ref ""

fun compile backend_config_def cbv_to_bytes heap_size stack_size name prog_def =
  let
    val cs = compilation_compset()
    val conf_def = backend_config_def
    val data_prog_name = (!intermediate_prog_prefix) ^ "data_prog"
    val to_data_thm = compile_to_data cs conf_def prog_def data_prog_name
    val data_prog_def = definition(mk_abbrev_name data_prog_name)
    val lab_prog_name = (!intermediate_prog_prefix) ^ "lab_prog"
    val stack_to_lab_thm = compile_to_lab data_prog_def to_data_thm lab_prog_name
    val lab_prog_def = definition(mk_abbrev_name lab_prog_name)
    val result = cbv_to_bytes stack_to_lab_thm lab_prog_def heap_size stack_size (name^".S")
    val bytes_name = (!intermediate_prog_prefix) ^ "bytes"
    val bytes_def = mk_abbrev bytes_name (result |> extract_bytes_ffis |> #1)
  in result |> PURE_REWRITE_RULE[GSYM bytes_def] end
  (*
val extract_oracle = find_term listSyntax.is_list o lhs o concl
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
val to_x64_bytes = to_bytes 3 ``x64_backend_config``
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
  *)

val compile_arm6 = compile arm6_backend_config_def cbv_to_bytes_arm6
val compile_arm8 = compile arm8_backend_config_def cbv_to_bytes_arm8
val compile_mips = compile mips_backend_config_def cbv_to_bytes_mips
val compile_riscv = compile riscv_backend_config_def cbv_to_bytes_riscv
val compile_x64 = compile x64_backend_config_def cbv_to_bytes_x64

end

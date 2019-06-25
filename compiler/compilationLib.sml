(*
  Library for in-logic compilation of CakeML abstract syntax producing machine
  code (for a variety of targets) using the CakeML compiler backend.
*)
structure compilationLib = struct

open preamble backendTheory
     arm7_compileLib export_arm7Theory
     arm8_compileLib export_arm8Theory
     mips_compileLib export_mipsTheory
     riscv_compileLib export_riscvTheory
     ag32_compileLib export_ag32Theory
     x64_compileLib export_x64Theory

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

    val to_flat_thm0 = timez "to_flat" eval ``to_flat ^conf_tm ^prog_tm``;
    val (c,p) = to_flat_thm0 |> rconc |> dest_pair
    val flat_conf_def = zDefine`flat_conf = ^c`;
    val flat_prog_def = zDefine`flat_prog = ^p`;
    val to_flat_thm =
      to_flat_thm0 |> CONV_RULE(RAND_CONV(
        FORK_CONV(REWR_CONV(SYM flat_conf_def),
                  REWR_CONV(SYM flat_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [flat_prog_def]] cs;

    val flat_conf_source_conf =
      ``flat_conf.source_conf``
      |> (RAND_CONV(REWR_CONV flat_conf_def) THENC eval)

    val flat_conf_clos_conf =
      ``flat_conf.clos_conf``
      |> (RAND_CONV(REWR_CONV flat_conf_def) THENC eval)

    val flat_conf_bvl_conf =
      ``flat_conf.bvl_conf``
      |> (RAND_CONV(REWR_CONV flat_conf_def) THENC eval)

    val to_pat_thm0 =
      ``to_pat ^conf_tm ^prog_tm``
      |> (REWR_CONV to_pat_def THENC
          RAND_CONV (REWR_CONV to_flat_thm) THENC
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
          PATH_CONV"rlr"(REWR_CONV flat_conf_clos_conf))
      |> timez "to_bvl" (CONV_RULE(RAND_CONV eval))
    val (c,p) = to_bvl_thm0 |> rconc |> dest_pair
    val bvl_conf_def = zDefine`bvl_conf = ^c`;
    val bvl_prog_def = zDefine`bvl_prog = ^p`;
    val to_bvl_thm =
      to_bvl_thm0 |> CONV_RULE(RAND_CONV(
        FORK_CONV(REWR_CONV(SYM bvl_conf_def),
                  REWR_CONV(SYM bvl_prog_def))));
    val () = computeLib.extend_compset [computeLib.Defs [bvl_prog_def]] cs;

    val bvl_conf_clos_conf_start =
      ``bvl_conf.clos_conf.start``
      |> (RAND_CONV(RAND_CONV(REWR_CONV bvl_conf_def)) THENC eval)

    val bvl_conf_bvl_conf =
      ``bvl_conf.bvl_conf``
      |> (RAND_CONV(REWR_CONV bvl_conf_def) THENC eval
          THENC REWR_CONV flat_conf_bvl_conf)

    val to_bvi_thm0 =
      ``to_bvi ^conf_tm ^prog_tm``
      |> (REWR_CONV to_bvi_def THENC
          RAND_CONV (REWR_CONV to_bvl_thm) THENC
          REWR_CONV LET_THM THENC
          PAIRED_BETA_CONV THENC
          PATH_CONV"rllr"(REWR_CONV bvl_conf_clos_conf_start) THENC
          PATH_CONV"rlr"(REWR_CONV bvl_conf_bvl_conf))

    val to_bvi_thm1 = to_bvi_thm0 |> CONV_RULE(RAND_CONV(
      timez "to_bvi" eval))

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
      ["flat_prog","pat_prog","clos_prog","bvl_prog","bvi_prog"]
  in to_data_thm end

fun compile_to_lab data_prog_def to_data_thm lab_prog_name =
  let
    val cs = compilation_compset()
    val () =
      computeLib.extend_compset [
        computeLib.Extenders [
          arm7_targetLib.add_arm7_encode_compset,
          arm8_targetLib.add_arm8_encode_compset,
          mips_targetLib.add_mips_encode_compset,
          riscv_targetLib.add_riscv_encode_compset,
          ag32_targetLib.add_ag32_encode_compset,
          x64_targetLib.add_x64_encode_compset],
        computeLib.Defs [
          arm7_backend_config_def, arm7_names_def,
          arm8_backend_config_def, arm8_names_def,
          mips_backend_config_def, mips_names_def,
          riscv_backend_config_def, riscv_names_def,
          ag32_backend_config_def, ag32_names_def,
          x64_backend_config_def, x64_names_def,
          data_prog_def
          ]
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
          REWR_CONV_BETA LET_THM THENC
          REWR_CONV LET_THM THENC BETA_CONV THENC
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
      |> time_with_size term_size "external oracle" (reg_allocComputeLib.get_oracle reg_alloc.Irc)

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
      |> CONV_RULE ((RATOR_CONV eval) THENC BETA_CONV)
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
        MAP3 (λa (b1,b2,b3,b4) (c1,c2,c3). f (SOME a, ((b1,b2,b3,b4), (c1,c2,c3)))) oracle_list l1 l2)`,
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
           REWR_CONV LET_THM THENC BETA_CONV THENC
           REWR_CONV LET_THM THENC BETA_CONV THENC
           RAND_CONV(
             RAND_CONV(REWR_CONV ZIP_GENLIST_lemma) THENC
             REWR_CONV MAP_GENLIST THENC
             RATOR_CONV(RAND_CONV(
               REWR_CONV o_DEF THENC
               ABS_CONV(RAND_CONV BETA_CONV))) THENC
             REWR_CONV GENLIST_EL_ZIP_lemma THENC
             PATH_CONV"lllrarararaararaa" (
               PAIRED_BETA_CONV THENC
               PATH_CONV"llr"(
                 REWR_CONV word_allocTheory.oracle_colour_ok_def THENC
                 REWR_CONV_BETA(CONJUNCT2 option_case_def))))))

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

      val prog_comp_tm =
        stack_allocTheory.prog_comp_def
        |> SPEC_ALL |> concl |> lhs |> strip_comb |> #1

      fun eval_fn i n p =
        let val tm = mk_icomb(prog_comp_tm,p)
        in eval tm end

      val stack_prog_els =
        stack_prog_def |> rconc |> listSyntax.dest_list |> #1

      val ths = time_with_size thms_size "stack_alloc (par)"
                  (parl eval_fn) stack_prog_els;

      val stack_to_lab_thm0 =
        from_word_thm'
        |> (CONV_RULE(RAND_CONV(
             REWR_CONV from_stack_def THENC
             RAND_CONV (RATOR_CONV eval) THENC
             REWR_CONV_BETA LET_THM THENC
             RAND_CONV (
               REWR_CONV stack_to_labTheory.compile_def THENC
               RAND_CONV (
                 REWR_CONV stack_allocTheory.compile_def THENC
                 FORK_CONV(eval,
                   RAND_CONV(REWR_CONV stack_prog_def) THENC
                   map_ths_conv ths) THENC
                 listLib.APPEND_CONV)))))

      val stack_alloc_prog_def =
        mk_abbrev"stack_alloc_prog"(stack_to_lab_thm0 |> rconc |> rand |> rand)
      val temp_defs = (mk_abbrev_name"stack_alloc_prog") :: temp_defs

      val stack_to_lab_thm1 =
        stack_to_lab_thm0
        |> CONV_RULE(RAND_CONV(
             RAND_CONV (
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

val extract_ffi_names_tm =
  optionSyntax.dest_some o assoc "ffi_names" o  #2 o TypeBase.dest_record
val extract_ffi_names =
  map stringSyntax.fromHOLstring o fst o listSyntax.dest_list o
  extract_ffi_names_tm

type compilation_result = {
  code : term, data : term, config : term };

fun extract_compilation_result th =
  let val ls = th |> rconc |> optionSyntax.dest_some |> pairSyntax.strip_pair
  in { code = el 1 ls, data = el 2 ls, config = el 3 ls } end

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

val export_defs = [
   exportTheory.word_to_string_def
  ,exportTheory.all_bytes_def
  ,exportTheory.byte_to_string_def
  ,exportTheory.words_line_def
  ,exportTheory.newl_strlit_def
  ,exportTheory.comma_cat_def
  ,exportTheory.comm_strlit_def
  ,exportTheory.data_section_def
  ,exportTheory.preamble_def
  ,exportTheory.space_line_def];

val arm7_export_defs = [
  export_arm7Theory.arm7_export_def,
  export_arm7Theory.ffi_asm_def];

val arm8_export_defs = [
  export_arm8Theory.arm8_export_def,
  export_arm8Theory.ffi_asm_def];

val x64_export_defs = [
  export_x64Theory.x64_export_def,
  export_x64Theory.ffi_asm_def,
  export_x64Theory.windows_ffi_asm_def
  ];

val mips_export_defs = [
  export_mipsTheory.mips_export_def,
  export_mipsTheory.ffi_asm_def];

val riscv_export_defs = [
  export_riscvTheory.riscv_export_def,
  export_riscvTheory.ffi_asm_def];

val ag32_export_defs = [
  export_ag32Theory.ag32_export_def];

datatype 'a app_list = Nil | List of 'a list | Append of 'a app_list * 'a app_list
val is_Nil = same_const (prim_mk_const{Thy="misc",Name="Nil"})
val (List_tm,mk_List,dest_List,is_List) = HolKernel.syntax_fns1 "misc" "List"
val (Append_tm,mk_Append,dest_Append,is_Append) = HolKernel.syntax_fns2 "misc" "Append"
val (SmartAppend_tm,mk_SmartAppend,dest_SmartAppend,is_SmartAppend) = HolKernel.syntax_fns2 "misc" "SmartAppend"
val (split16_tm,mk_split16,dest_split16,is_split16) = HolKernel.syntax_fns2 "export" "split16"

fun format_byte s = String.concat("0x"::(if String.size s < 2 then ["0",s] else [s]))

fun byte_to_string i = i |> Int.fmt StringCvt.HEX |> format_byte
fun word_to_string i = i |> Int.fmt StringCvt.DEC

fun split16_to_app_list f [] = Nil
  | split16_to_app_list f xs =
    let val (xs1,xs2) = Lib.split_after 16 xs handle HOL_ERR _ => (xs,[]) in
      Append (f xs1, split16_to_app_list f xs2)
    end

fun comma_cat f x =
  case x of [] => ["\n"] | [x] => [f x, "\n"] | (x::xs) =>
    (f x)::","::(comma_cat f xs)

fun words_line word_directive to_string ls =
  List (word_directive :: comma_cat to_string ls)

val mlstring_to_string = stringSyntax.fromHOLstring o mlstringSyntax.dest_strlit

(*
fun split16_def_to_app_list term_to_app_list eval f def =
  let
    val (ls,ty) = listSyntax.dest_list(rconc def)
    fun apply_f ls =
      let
        val tm = listSyntax.mk_list(ls,ty)
      in term_to_app_list(rconc(eval(mk_comb(f,tm)))) end
  in split16_to_app_list apply_f ls end
*)

fun split16_ml_to_app_list (prefix,to_string) def =
  let
    val (ls,ty) = listSyntax.dest_list(rconc def)
    val ints = map wordsSyntax.uint_of_word ls
  in split16_to_app_list (words_line prefix to_string) ints end

fun term_to_app_list word_directive eval code_def data_def =
  let
    fun ttal tm =
      if is_Nil tm then Nil
      else if is_split16 tm then
        let
          val (f,x) = dest_split16 tm
        in if same_const x (lhs(concl code_def))
           (*
           then split16_def_to_app_list ttal eval f code_def
           else split16_def_to_app_list ttal eval f data_def
           *)
           then split16_ml_to_app_list ("\t.byte ",byte_to_string) code_def
           else split16_ml_to_app_list ("\t."^word_directive^" ",word_to_string) data_def
        end
      else if is_List tm then
        dest_List tm |> listSyntax.dest_list |> #1
        |> map mlstring_to_string
        |> List
      else
        let
          val (t1,t2) =
            dest_Append tm handle HOL_ERR _ =>
            dest_SmartAppend tm
        in Append (ttal t1, ttal t2) end
  in ttal end

fun print_app_list out Nil = ()
  | print_app_list out (List ls) =
    List.app (curry TextIO.output out) ls
  | print_app_list out (Append (l1,l2)) =
    (print_app_list out l1; print_app_list out l2)

(*
val (split16_nil,split16_cons) = exportTheory.split16_def |> CONJ_PAIR
val split16_tm = split16_nil |> SPEC_ALL |> concl |> lhs |> strip_comb |> #1
fun split16_conv tm =
  tm |> (
  REWR_CONV split16_nil ORELSEC (
  REWR_CONV split16_cons THENC
  RAND_CONV listLib.FIRSTN_CONV THENC
  REWR_CONV_BETA LET_THM THENC
  RAND_CONV listLib.BUTFIRSTN_CONV THENC
  REWR_CONV_BETA LET_THM THENC
  RAND_CONV split16_conv ) )
*)

fun eval_export word_directive target_export_defs heap_size stack_size code_def data_def ffi_names_tm out =
  let
    val cs = wordsLib.words_compset()
    val eval = computeLib.CBV_CONV cs;
    val () = computeLib.extend_compset [
      computeLib.Extenders [basicComputeLib.add_basic_compset] ] cs;
    val () = computeLib.scrub_const cs (prim_mk_const{Thy="misc",Name="SmartAppend"})
    val () = computeLib.extend_compset [
      computeLib.Extenders [basisComputeLib.add_basis_compset],
      computeLib.Defs export_defs,
      computeLib.Defs target_export_defs ] cs;
    val exporter_tm = target_export_defs |> hd |> SPEC_ALL |> concl |> lhs |> strip_comb |> #1
    val eval_export_tm =
      list_mk_comb(exporter_tm,
        [ffi_names_tm,
         numSyntax.term_of_int heap_size,
         numSyntax.term_of_int stack_size,
         lhs(concl code_def),
         lhs(concl data_def)])
    val app_list = eval eval_export_tm |> rconc
  in print_app_list out (term_to_app_list word_directive eval code_def data_def app_list) end

fun cbv_to_bytes
      word_directive
      add_encode_compset backend_config_def names_def target_export_defs
      stack_to_lab_thm lab_prog_def heap_size stack_size
      code_name data_name config_name filename =
  let
    val cs = compilation_compset()
    val () =
      computeLib.extend_compset [
        computeLib.Extenders [ add_encode_compset ],
        computeLib.Defs [ backend_config_def, names_def, lab_prog_def]
      ] cs
    val eval = computeLib.CBV_CONV cs;

    val bootstrap_thm =
      timez "lab_to_target" (CONV_RULE(RAND_CONV(eval))) stack_to_lab_thm

    val result = extract_compilation_result bootstrap_thm
    val code_def = mk_abbrev code_name (#code result)
    val data_def = mk_abbrev data_name (#data result)
    val config_def = mk_abbrev config_name (#config result)
    val result_thm = PURE_REWRITE_RULE[GSYM code_def, GSYM data_def, GSYM config_def] bootstrap_thm

    val ffi_names_tm = extract_ffi_names_tm (#config result)

    val out = TextIO.openOut filename

    val () = Lib.say(pad_to 30 (" export: "))
    val () = time (
      eval_export word_directive target_export_defs heap_size stack_size code_def data_def ffi_names_tm) out

    val () = TextIO.closeOut out

  in
    result_thm
  end

val cbv_to_bytes_arm8 =
  cbv_to_bytes
    "quad"
    arm8_targetLib.add_arm8_encode_compset
    arm8_backend_config_def arm8_names_def
    arm8_export_defs

val cbv_to_bytes_arm7 =
  cbv_to_bytes
    "long"
    arm7_targetLib.add_arm7_encode_compset
    arm7_backend_config_def arm7_names_def
    arm7_export_defs

val cbv_to_bytes_mips =
  cbv_to_bytes
    "quad"
    mips_targetLib.add_mips_encode_compset
    mips_backend_config_def mips_names_def
    mips_export_defs

val cbv_to_bytes_riscv =
  cbv_to_bytes
    "quad"
    riscv_targetLib.add_riscv_encode_compset
    riscv_backend_config_def riscv_names_def
    riscv_export_defs

val cbv_to_bytes_ag32 =
  cbv_to_bytes
    "quad"
    ag32_targetLib.add_ag32_encode_compset
    ag32_backend_config_def ag32_names_def
    ag32_export_defs

val cbv_to_bytes_x64 =
  cbv_to_bytes
    "quad"
    x64_targetLib.add_x64_encode_compset
    x64_backend_config_def x64_names_def
    x64_export_defs

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
    val code_name = (!intermediate_prog_prefix) ^ "code"
    val data_name = (!intermediate_prog_prefix) ^ "data"
    val config_name = (!intermediate_prog_prefix) ^ "config"
    val result_thm =
      cbv_to_bytes stack_to_lab_thm lab_prog_def heap_size stack_size code_name data_name config_name (name^".S")
  in result_thm end

val compile_arm7 = compile arm7_backend_config_def cbv_to_bytes_arm7
val compile_arm8 = compile arm8_backend_config_def cbv_to_bytes_arm8
val compile_mips = compile mips_backend_config_def cbv_to_bytes_mips
val compile_riscv = compile riscv_backend_config_def cbv_to_bytes_riscv
val compile_ag32 = compile ag32_backend_config_def cbv_to_bytes_ag32
val compile_x64 = compile x64_backend_config_def cbv_to_bytes_x64

end

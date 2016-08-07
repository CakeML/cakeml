open preamble
     backendTheory
     to_dataBootstrapTheory
     x64_configTheory
     x64_targetTheory
     asmLib

val _ = new_theory "x64Bootstrap";

val _ = Globals.max_print_depth := 10;

val rconc = rhs o concl;

val to_data_thm0 =
  MATCH_MP backendTheory.to_data_change_config to_data_thm
  |> Q.GEN`c2` |> Q.ISPEC`x64_compiler_config`

val same_config = prove(to_data_thm0 |> concl |> rator |> rand,
  REWRITE_TAC[init_conf_def,x64_compiler_config_def]
  \\ EVAL_TAC
  \\ rw[FLOOKUP_EXT,FUN_EQ_THM,FLOOKUP_UPDATE,FLOOKUP_FUNION]
  \\ EVAL_TAC
  \\ rpt (IF_CASES_TAC \\ rveq \\ EVAL_TAC))

val to_data_thm1 =
  MATCH_MP to_data_thm0 same_config

val cs = wordsLib.words_compset()
val () =
  computeLib.extend_compset [
    computeLib.Extenders [
      basicComputeLib.add_basic_compset,
      compilerComputeLib.add_compiler_compset,
      asmLib.add_asm_compset ],
    computeLib.Defs [
      x64_compiler_config_def,
      x64_config_def,
      data_prog_def]
  ] cs
val eval = computeLib.CBV_CONV cs;

val to_livesets_thm0 =
  ``to_livesets x64_compiler_config init_prog``
  |> (REWR_CONV to_livesets_def THENC
      RAND_CONV (REWR_CONV to_data_thm1) THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC BETA_CONV THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC
      PATH_CONV "rlrraraalralrarllr" eval THENC
      PATH_CONV"rlrraraalralralralralrar"
        (RATOR_CONV(RATOR_CONV(RAND_CONV eval)) THENC
         REWR_CONV(CONJUNCT1 bool_case_thm)))

(*
val tm1 =
  to_livesets_thm0 |> rconc
  |> rand |> rator |> rand
  |> rand |> dest_abs |> #2
  |> rand |> dest_abs |> #2
  |> dest_abs |> #2
  |> rator |> rand |> dest_abs |> #2
  |> rator |> rand |> dest_abs |> #2
  (*
  |> rand |> rator |> rator |> rand
  *)
  |> rator |> rand |> dest_abs |> #2
  |> rator |> rand |> dest_abs |> #2
  |> rator |> rand |> dest_abs |> #2
  |> rand
  |> rator |> rator |> rand
*)

(* about 5 minutes *)

Lib.say "eval data_to_word: ";
val tm0 = to_livesets_thm0 |> rconc |> rand |> rand
val thm0 = time eval tm0;

(*
val word_prog0_def = Define`
  word_prog0 = ^(thm0 |> rconc)`;

val thm1 = thm0 |> CONV_RULE(RAND_CONV(REWR_CONV(SYM word_prog0_def)))
*)

(* could do it all at once?

Lib.say "eval to_livesets1: "

val to_livesets_thm1 =
  to_livesets_thm0
  |> CONV_RULE (RAND_CONV (
       RAND_CONV(RAND_CONV(REWR_CONV thm0) THENC
                 time eval)))
*)

val tm1 = to_livesets_thm0 |> rconc |> rand

val (args,body) = tm1 |> rator |> rand |> dest_pabs
val word_to_word_fn_def = zDefine`word_to_word_fn ^args = ^body`;
val word_to_word_fn_eq =
  word_to_word_fn_def
  |> SPEC_ALL
  |> PairRules.PABS args
  |> CONV_RULE(LAND_CONV PairRules.PETA_CONV)
val word_to_word_fn = word_to_word_fn_eq|>concl|>lhs

val word_prog = thm0 |> rconc |> listSyntax.dest_list |> #1

val num_progs = length word_prog

local
  open Thread

  fun chunks_of n ls =
    let
      val (ch,rst) = split_after n ls
    in
      if null rst then [ch]
      else ch::(chunks_of n rst)
    end handle HOL_ERR _ => [ls]

in
  fun parMAP str_fn chunk_size eval_fn ls =
    let
      val chs = chunks_of chunk_size ls

      fun do_eval n [] acc = acc
        | do_eval n (p::ps) acc =
          let
            val () = Lib.say(str_fn n)
            val th = eval_fn p
          in do_eval (n-1) ps (th::acc) end

      val mutex = Mutex.mutex()
      val cvar = ConditionVar.conditionVar()
      val threads_left = ref (length chs)

      fun do_chunk ch n r () =
        let
          val () = r := do_eval n ch []
          val () = Mutex.lock mutex
          val () = threads_left := !threads_left-1
          val () = Mutex.unlock mutex
          val () = ConditionVar.signal cvar
        in () end

      fun foldthis (ch,(n,refs)) =
        let
          val r = ref []
          val _ = Thread.fork (do_chunk ch n r, [])
        in (n-chunk_size,r::refs) end

      val true = Mutex.trylock mutex

      val (_,refs) = List.foldl foldthis (num_progs,[]) chs

      fun wait () =
        if !threads_left = 0 then Mutex.unlock mutex
        else (ConditionVar.wait(cvar,mutex); wait())

      val () = wait ()

      val ths = List.concat (List.map (op!) refs)

      fun mk_conv() =
        let
          val next_thm = ref ths
          fun el_conv _ =
            case !next_thm of th :: rest =>
              let val () = next_thm := rest in th end
        in
          listLib.MAP_CONV el_conv
        end
    in
      mk_conv
    end
end

val chunk_size = 400
fun str_fn n = String.concat["eval word_to_word (",Int.toString n,"remain): "]
fun eval_fn p =
  mk_comb(word_to_word_fn,p)
  |> (RATOR_CONV(REWR_CONV word_to_word_fn_eq) THENC
      time eval)

val map_conv = parMAP str_fn chunk_size eval_fn word_prog ()

val thm1 =
  tm1
  |> (RATOR_CONV(RAND_CONV(REWR_CONV(SYM word_to_word_fn_eq))) THENC
      RAND_CONV(REWR_CONV thm0) THENC map_conv)

val word_prog0_def = zDefine`
  word_prog0 = ^(thm1 |> rconc)`;

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
val clash_fn_eq =
  clash_fn_def
  |> SPEC_ALL
  |> PairRules.PABS args
  |> CONV_RULE(LAND_CONV PairRules.PETA_CONV)
val clash_fn = clash_fn_eq|>concl|>lhs

val word_prog0 = thm1 |> rconc |> listSyntax.dest_list |> #1

fun str_fn n = String.concat["eval clash (",Int.toString n," remain): "]
fun eval_fn p =
  mk_comb(clash_fn,p)
  |> (RATOR_CONV(REWR_CONV clash_fn_eq) THENC
      time eval)

val map_conv = parMAP str_fn chunk_size eval_fn word_prog0 ()

val thm2 =
  tm2
  |> (RATOR_CONV(RAND_CONV(REWR_CONV(SYM clash_fn_eq))) THENC
      RAND_CONV(REWR_CONV word_prog0_def) THENC map_conv)

val to_livesets_thm =
  to_livesets_thm1
  |> CONV_RULE (RAND_CONV (
       RAND_CONV(REWR_CONV thm2) THENC
       BETA_CONV THENC
       PATH_CONV"lrlr"eval))

val oracles =
  to_livesets_thm
  |> rconc |> pairSyntax.dest_pair |> #1
  |> time reg_allocComputeLib.get_oracle

val x64_oracle_def = zDefine`
  x64_oracle = ^oracles`;

val wc =
  ``x64_compiler_config.word_to_word_conf
    with col_oracle := x64_oracle``

(*
val to_livesets_invariant' = Q.prove(
  `to_livesets c p =
   let (rcm,c1,p) = to_livesets (c with word_to_word_conf := wc) p in
     (rcm,c1 with word_to_word_conf := c.word_to_word_conf,p)`,
  qmatch_goalsub_abbrev_tac`LET _ (to_livesets cc p)`
  \\ qspecl_then[`cc`,`c.word_to_word_conf`]mp_tac(Q.GENL[`wc`,`c`]to_livesets_invariant)
  \\ simp[Abbr`cc`]
  \\ disch_then(SUBST1_TAC o SYM)
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[config_component_equality]);
*)

val args = to_livesets_thm |> concl |> lhs |> strip_comb |> #2

val word_prog1_def = zDefine`
  word_prog1 = ^(thm2 |> rconc)`;

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

(* TODO: move *)
val ZIP_GENLIST1 = Q.store_thm("ZIP_GENLIST1",
  `∀l f n. LENGTH l = n ⇒ ZIP (GENLIST f n,l) = GENLIST (λx. (f x, EL x l)) n`,
  Induct \\ rw[] \\ rw[GENLIST_CONS,o_DEF]);
(* -- *)

val ZIP_GENLIST_lemma =
  MATCH_MP LENGTH_ZIP
    (TRANS LENGTH_word_prog1 (SYM LENGTH_word_prog0))
  |> CONJUNCT1
  |> C TRANS LENGTH_word_prog1
  |> MATCH_MP ZIP_GENLIST1
  |> ISPEC (lhs(concl(x64_oracle_def)))

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
         ALL_CONV (* rewrite the EL_ZIP *)) THENC
       REWR_CONV LET_THM THENC BETA_CONV THENC
       REWR_CONV LET_THM THENC BETA_CONV))

val _ = export_theory();

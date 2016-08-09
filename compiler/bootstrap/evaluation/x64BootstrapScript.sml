open preamble
     backendTheory
     to_dataBootstrapTheory
     x64_configTheory
     x64_targetTheory
     x64_targetLib
     asmLib

val _ = new_theory "x64Bootstrap";

(* TODO: move *)
val ZIP_GENLIST1 = Q.store_thm("ZIP_GENLIST1",
  `∀l f n. LENGTH l = n ⇒ ZIP (GENLIST f n,l) = GENLIST (λx. (f x, EL x l)) n`,
  Induct \\ rw[] \\ rw[GENLIST_CONS,o_DEF]);

val MAP2i_def = Define`
  (MAP2i f [] [] = []) /\
  (MAP2i f (h1::t1) (h2::t2) = f 0 h1 h2::MAP2i (f o SUC) t1 t2)`;
val _ = export_rewrites["MAP2i_def"];

val MAP2i_ind = theorem"MAP2i_ind";

val LENGTH_MAP2i = Q.store_thm("LENGTH_MAP2i[simp]",
  `∀f l1 l2. LENGTH l1 = LENGTH l2 ⇒ LENGTH (MAP2i f l1 l2) = LENGTH l2`,
  ho_match_mp_tac MAP2i_ind \\ rw[]);

val EL_MAP2i = Q.store_thm("EL_MAP2i",
  `∀f l1 l2 n. n < LENGTH l1 ∧ n < LENGTH l2 ⇒
    EL n (MAP2i f l1 l2) = f n (EL n l1) (EL n l2)`,
  ho_match_mp_tac MAP2i_ind \\ rw[]
  \\ Cases_on`n` \\ fs[]);

val MAP3_def = Define`
  (MAP3 f [] [] [] = []) /\
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)`;
val _ = export_rewrites["MAP3_def"];

val MAP3_ind = theorem"MAP3_ind";

val LENGTH_MAP3 = Q.store_thm("LENGTH_MAP3[simp]",
  `∀f l1 l2 l3. LENGTH l1 = LENGTH l3 /\ LENGTH l2 = LENGTH l3 ⇒ LENGTH (MAP3 f l1 l2 l3) = LENGTH l3`,
  ho_match_mp_tac MAP3_ind \\ rw[]);

val EL_MAP3 = Q.store_thm("EL_MAP3",
  `∀f l1 l2 l3 n. n < LENGTH l1 ∧ n < LENGTH l2 ∧ n < LENGTH l3 ⇒
    EL n (MAP3 f l1 l2 l3) = f (EL n l1) (EL n l2) (EL n l3)`,
  ho_match_mp_tac MAP3_ind \\ rw[]
  \\ Cases_on`n` \\ fs[]);

fun itlist3 f L1 L2 L3 base_value =
  let
    fun itl ([], [], []) = base_value
      | itl (a :: rst1, b :: rst2, c :: rst3) = f a b c (itl (rst1, rst2, rst3))
      | itl _ = raise mk_HOL_ERR "Lib" "itlist3" "lists of different length"
    in
      itl (L1, L2, L3)
    end

fun zip3 ([],[],[]) = []
  | zip3 ((h1::t1),(h2::t2),(h3::t3)) = ((h1,h2,h3)::zip3(t1,t2,t3))

val (map3_tm,mk_map3,dest_map3,is_map3) = syntax_fns4 "x64Bootstrap" "MAP3"

val (m3n,m3c) = CONJ_PAIR MAP3_def
val m3c = CONV_RULE(RESORT_FORALL_CONV(sort_vars["f","h1","h2","h3","t1","t2","t3"])) m3c
fun MAP3_CONV conv tm =
  let
    val (fnn,l1,l2,l3) = dest_map3 tm
    val (els1,_) = listSyntax.dest_list l1
    val (els2,_) = listSyntax.dest_list l2
    val (els3,_) = listSyntax.dest_list l3
    val nth = ISPEC fnn m3n
    val cth = ISPEC fnn m3c
    val cns = rator(rator(rand(snd(strip_forall(concl cth)))))
    fun APcons t1 t2 = MK_COMB(AP_TERM cns t2,t1)
    fun itfn e1 e2 e3 th =
      let
        val ts = tl(#2(strip_comb(rand(rator(concl th)))))
        val es = [e1,e2,e3]
        val th1 = SPECL ts (SPECL es cth)
      in
        TRANS th1 (APcons th (conv (list_mk_comb(fnn,es))))
      end
  in
    itlist3 itfn els1 els2 els3 nth
  end

val filter_skip_MAP = Q.store_thm("filter_skip_MAP",
  `∀ls. filter_skip ls = MAP (λx. case x of Section n xs => Section n (FILTER not_skip xs)) ls`,
  Induct \\ simp[lab_filterTheory.filter_skip_def]
  \\ Cases \\ simp[lab_filterTheory.filter_skip_def]);

(*
val find_ffi_index_def = Define`
  find_ffi_index x =
  ^(lab_to_targetTheory.find_ffi_index_limit_def
    |> CONJUNCTS |> el 3 |> SPEC_ALL
    |> concl |> rhs |> rand)`;
*)

(* -- *)

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

val () = Lib.say "eval data_to_word: ";
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
  fun parlist num_threads chunk_size eval_fn ls =
    let
      val num_items = List.length ls
      val chs = chunks_of chunk_size ls
      val num_chunks = List.length chs

      fun eval_chunk i n [] acc = acc
        | eval_chunk i n (x::xs) acc =
          eval_chunk i (n+1) xs (eval_fn i n x::acc)

      val mutex = Mutex.mutex()
      val refs = List.tabulate(num_chunks,(fn _ => ref NONE))
      val threads_left = ref num_threads
      val threads_left_mutex = Mutex.mutex()
      val cvar = ConditionVar.conditionVar()

      fun find_work i [] [] =
            let
              val () = Mutex.lock threads_left_mutex
              val () = threads_left := !threads_left-1
              val () = Mutex.unlock threads_left_mutex
            in ConditionVar.signal cvar end
        | find_work i (r::rs) (c::cs) =
            case (Mutex.lock mutex; !r) of
              SOME _ => (Mutex.unlock mutex; find_work (i+1) rs cs)
            | NONE =>
              let
                val () = r := SOME []
                val () = Mutex.unlock mutex
                val vs = eval_chunk i 0 c []
                val () = r := SOME vs
              in
                find_work (i+1) rs cs
              end

      fun fork_this () = find_work 0 refs chs

      val true = Mutex.trylock threads_left_mutex

      val () = for_se 1 num_threads
        (fn _ => ignore (Thread.fork (fork_this, [Thread.EnableBroadcastInterrupt true])))

      fun wait () =
        if !threads_left = 0 then Mutex.unlock threads_left_mutex
        else (ConditionVar.wait(cvar,threads_left_mutex); wait())

      val () = wait()
    in
      List.concat (List.map (Option.valOf o op!) (List.rev refs))
    end
end

fun map_ths_conv ths =
  let
    val next_thm = ref ths
    fun el_conv _ =
      case !next_thm of th :: rest =>
        let val () = next_thm := rest in th end
  in
    listLib.MAP_CONV el_conv
  end

val chunk_size = 50
val num_threads = 8
fun say_str s i n =
  Lib.say(String.concat["eval ",s,": chunk ",Int.toString i,": el ",Int.toString n,": "])
fun eval_fn i n p =
  let
    val () = say_str "word_to_word" i n
    val tm = mk_comb(word_to_word_fn,p)
    val conv = RATOR_CONV(REWR_CONV word_to_word_fn_eq) THENC time eval
  in
    conv tm
  end

val ths = parlist num_threads chunk_size eval_fn word_prog

val thm1 =
  tm1
  |> (RATOR_CONV(RAND_CONV(REWR_CONV(SYM word_to_word_fn_eq))) THENC
      RAND_CONV(REWR_CONV thm0) THENC map_ths_conv ths)

fun mk_def s tm = new_definition(s,mk_eq(mk_var(s,type_of tm),tm))

val word_prog0_def = mk_def "word_prog0" (thm1 |> rconc)

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

fun eval_fn i n p =
  let
    val () = say_str "clash" i n
    val tm = mk_comb(clash_fn,p)
    val conv = RATOR_CONV(REWR_CONV clash_fn_eq) THENC time eval
  in
    conv tm
  end

val ths = parlist num_threads chunk_size eval_fn word_prog0

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
  |> time reg_allocComputeLib.get_oracle

val x64_oracle_def = mk_def"x64_oracle" oracles;

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

val word_prog1_def = mk_def"word_prog1"(thm2 |> rconc);

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

(*
val GENLIST_EL_ZIP_lemma = Q.prove(
  `LENGTH l1 = n ∧ LENGTH l2 = n ⇒
   GENLIST (λx. f (y x, EL x (ZIP (l1,l2)))) n =
   GENLIST (λx. f (y x, (EL x l1, EL x l2))) n`,
  rw[GENLIST_FUN_EQ,EL_ZIP])
  |> C MATCH_MP (CONJ LENGTH_word_prog1 LENGTH_word_prog0)
*)

val x64_oracle_list_def = mk_def"x64_oracle_list" (x64_oracle_def |> rconc |> rand);

val x64_oracle_thm = Q.prove(
  `n < LENGTH x64_oracle_list ⇒
   x64_oracle n = SOME (EL n x64_oracle_list)`,
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
  `LENGTH l1 = n ∧ LENGTH l2 = n ∧ LENGTH x64_oracle_list = n ⇒
   GENLIST (λx. f (x64_oracle x, EL x (ZIP (l1,l2)))) n =
   MAP3 (λa (b1,b2) (c1,c2,c3). f (SOME a, ((b1,b2), (c1,c2,c3)))) x64_oracle_list l1 l2`,
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
         PATH_CONV"lllraraararaa" (
           PAIRED_BETA_CONV THENC
           PATH_CONV"llr"(
             REWR_CONV word_allocTheory.oracle_colour_ok_def THENC
             REWR_CONV(CONJUNCT2 option_case_def) THENC
             BETA_CONV))) THENC
       REWR_CONV LET_THM THENC BETA_CONV THENC
       REWR_CONV LET_THM THENC BETA_CONV))

val tm3 = compile_thm0 |> rconc |> rand

val check_fn = tm3 |> funpow 3 rator |> rand

fun eval_fn i n (a,b,c) =
  let
    val () = say_str "chunk" i n
    val tm = list_mk_comb(check_fn,[a,b,c])
  in
    time eval tm
  end

val x64_oracle_list_els =
  x64_oracle_list_def |> rconc |> listSyntax.dest_list |> #1
val word_prog1_els =
   word_prog1_def |> rconc |> listSyntax.dest_list |> #1
val word_prog0_els =
   word_prog0_def |> rconc |> listSyntax.dest_list |> #1

val lss = zip3
  (x64_oracle_list_els, word_prog1_els, word_prog0_els)

(*
val sum = foldr (op +) 0
fun avg ls = sum ls div num_progs
avg (map term_size x64_oracle_list_els)
avg (map term_size word_prog1_els)
avg (map term_size word_prog0_els)
avg (map (term_size o rconc) map3els)

fun avg ls = sum ls div (length ls)
avg (map term_size encoded_prog_els)
*)

val map3els = parlist num_threads chunk_size eval_fn lss

val check_fn_def = mk_def"check_fn"check_fn;

fun make_abbrevs str n [] acc = acc
  | make_abbrevs str n (t::ts) acc =
    make_abbrevs str (n-1) ts
      (mk_def (str^(Int.toString n)) t :: acc)

val word_prog1_defs = make_abbrevs "word_prog1_el_" num_progs word_prog1_els []

fun intro_abbrev [] tm = raise UNCHANGED
  | intro_abbrev (ab::abbs) tm =
      FORK_CONV(REWR_CONV(SYM ab),intro_abbrev abbs) tm

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
  fun str n =
    String.concat[Int.toString n,if n mod 10 = 0 then "\n" else " "]
  fun el_conv _ =
    case !next_thm of th :: rest =>
      let
        val () = next_thm := rest
        val () = Lib.say(str (!remain))
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
         time map3_conv)))

val word_prog2_def = mk_def"word_prog2" (compile_thm1 |> rconc |> rand);

val compile_thm1' = compile_thm1
  |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM word_prog2_def))))

val () = computeLib.extend_compset[computeLib.Defs[word_prog2_def]] cs;

(* about 15 minutes - cannot parallelise easily due to bitmaps accumulator *)
val () = Lib.say "eval word_to_stack: "
val from_word_thm =
  compile_thm1'
  |> CONV_RULE(RAND_CONV(
       REWR_CONV from_word_def THENC
       REWR_CONV LET_THM THENC
       RAND_CONV(time eval) THENC
       PAIRED_BETA_CONV THENC
       REWR_CONV LET_THM THENC
       BETA_CONV))

val stack_prog_def = mk_def"stack_prog" (from_word_thm |> rconc |> rand);

val from_word_thm' = from_word_thm
  |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM stack_prog_def))))

val () = computeLib.extend_compset[computeLib.Defs[stack_prog_def]] cs;

val bare_cs = wordsLib.words_compset()
val () =
  computeLib.extend_compset[computeLib.Extenders[compilerComputeLib.add_compiler_compset]] bare_cs
val bare_eval = computeLib.CBV_CONV bare_cs

val stack_to_lab_thm0 =
  from_word_thm'
  |> CONV_RULE(RAND_CONV(
       REWR_CONV from_stack_def THENC
       RAND_CONV bare_eval THENC
       REWR_CONV LET_THM THENC BETA_CONV THENC
       RAND_CONV(RATOR_CONV(RAND_CONV eval)) THENC
       RAND_CONV(funpow 2 RATOR_CONV(RAND_CONV bare_eval)) THENC
       RAND_CONV(funpow 3 RATOR_CONV(RAND_CONV bare_eval)) THENC
       RAND_CONV(funpow 4 RATOR_CONV(RAND_CONV bare_eval)) THENC
       REWR_CONV LET_THM THENC BETA_CONV))

val tm4 = stack_to_lab_thm0 |> rconc |> rand

val prog_comp_tm =
  stack_allocTheory.prog_comp_def
  |> SPEC_ALL |> concl |> lhs |> strip_comb |> #1
  |> inst[alpha |-> fcpSyntax.mk_int_numeric_type 64]

fun eval_fn i n p =
  let
    val () = say_str "stack_alloc" i n
    val tm = mk_comb(prog_comp_tm,p)
  in
    time eval tm
  end

val stack_prog_els =
  stack_prog_def |> rconc |> listSyntax.dest_list |> #1

val ths = parlist num_threads chunk_size eval_fn stack_prog_els

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
  mk_def"stack_alloc_prog" (stack_alloc_thm |> rconc |> rand);

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
  (RAND_CONV(
    RATOR_CONV(RAND_CONV eval) THENC
    funpow 3 RATOR_CONV(RAND_CONV bare_eval) THENC
    funpow 4 RATOR_CONV(RAND_CONV eval) THENC
    REWR_CONV stack_removeTheory.compile_def THENC
    LAND_CONV eval))

val tm6 = stack_remove_thm0 |> rconc |> rand |> rand

val prog_comp_n_tm = tm6 |> rator |> rand

fun eval_fn i n p =
  let
    val () = say_str "stack_remove" i n
    val tm = mk_comb(prog_comp_n_tm,p)
  in
    time eval tm
  end

val stack_alloc_prog_els =
  stack_alloc_prog_def |> rconc |> listSyntax.dest_list |> #1

val ths = parlist num_threads chunk_size eval_fn stack_alloc_prog_els

val stack_remove_thm =
  stack_remove_thm0
  |> CONV_RULE(RAND_CONV(
     RAND_CONV(
       RAND_CONV (
         RAND_CONV(REWR_CONV stack_alloc_prog_def) THENC
         map_ths_conv ths) THENC
       listLib.APPEND_CONV)))

val stack_remove_prog_def =
  mk_def"stack_remove_prog" (stack_remove_thm |> rconc |> rand);

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
  let
    val () = say_str "stack_names" i n
    val tm = mk_comb(prog_comp_nm_tm,p)
  in
    time eval tm
  end

val stack_remove_prog_els =
  stack_remove_prog_def |> rconc |> listSyntax.dest_list |> #1

val ths = parlist num_threads chunk_size eval_fn stack_remove_prog_els

val stack_names_thm0 =
  tm7
  |> (RAND_CONV(REWR_CONV stack_remove_prog_def) THENC
      map_ths_conv ths)

val stack_names_prog_def =
  mk_def"stack_names_prog" (stack_names_thm0 |> rconc);

val stack_names_thm = stack_names_thm0
  |> CONV_RULE(RAND_CONV(REWR_CONV(SYM stack_names_prog_def)))

val stack_to_lab_thm3 =
  stack_to_lab_thm2
  |> CONV_RULE(RAND_CONV(RAND_CONV(
       RAND_CONV(REWR_CONV stack_names_thm))))

val tm8 = stack_to_lab_thm3 |> rconc |> rand

val prog_to_section_tm = tm8 |> rator |> rand

fun eval_fn i n p =
  let
    val () = say_str "stack_to_lab" i n
    val tm = mk_comb(prog_to_section_tm,p)
  in
    time eval tm
  end

val stack_names_prog_els =
  stack_names_prog_def |> rconc |> listSyntax.dest_list |> #1

val ths = parlist num_threads chunk_size eval_fn stack_names_prog_els

val stack_to_lab_thm =
  stack_to_lab_thm3
  |> CONV_RULE(RAND_CONV(RAND_CONV(
       RAND_CONV(REWR_CONV stack_names_prog_def) THENC
       map_ths_conv ths)))

val lab_prog_def = mk_def"lab_prog" (stack_to_lab_thm |> rconc |> rand);

val lab_to_target_thm0 =
  stack_to_lab_thm
  |> CONV_RULE(RAND_CONV(
       RAND_CONV(REWR_CONV(SYM lab_prog_def)) THENC
       REWR_CONV from_lab_def THENC
       RATOR_CONV(RAND_CONV bare_eval)))

val tm9 = lab_to_target_thm0 |> rconc

val lab_prog_els =
  lab_prog_def |> rconc |> listSyntax.dest_list |> #1

val filter_skip_lab_prog =
  ISPEC(lhs(concl(lab_prog_def)))filter_skip_MAP

val filter_skip_fn =
  filter_skip_lab_prog |> rconc |> rator |> rand

fun eval_fn i n p =
  let
    val () = say_str "filter_skip" i n
    val tm = mk_comb(filter_skip_fn,p)
  in time eval tm end

val ths = parlist num_threads chunk_size eval_fn lab_prog_els

val filter_skip_thm =
  tm9 |> (
    REWR_CONV lab_to_targetTheory.compile_def THENC
    RAND_CONV(
      REWR_CONV filter_skip_lab_prog THENC
      RAND_CONV(REWR_CONV lab_prog_def) THENC
      map_ths_conv ths))

val skip_prog_def = mk_def"skip_prog" (filter_skip_thm |> rconc |> rand);

val filter_skip_thm' = filter_skip_thm
  |> CONV_RULE(RAND_CONV(RAND_CONV(REWR_CONV(SYM skip_prog_def))))

(* about 3 mins, could parallelise? *)
val ffi_limit_thm =
  ``find_ffi_index_limit skip_prog``
  |> (RAND_CONV(REWR_CONV skip_prog_def) THENC time eval)

val lab_to_target_thm1 =
  lab_to_target_thm0
  |> CONV_RULE (RAND_CONV(
     REWR_CONV filter_skip_thm' THENC
     REWR_CONV lab_to_targetTheory.compile_lab_def THENC
     RAND_CONV(REWR_CONV ffi_limit_thm) THENC
     REWR_CONV LET_THM THENC BETA_CONV))

val tm10 = lab_to_target_thm1 |> rconc |> rator |> rator |> rand

val () = computeLib.extend_compset[computeLib.Extenders[x64_targetLib.add_x64_encode_compset]] cs;

val remove_labels_thm0 =
  tm10 |>
  (REWR_CONV lab_to_targetTheory.remove_labels_def THENC
   RAND_CONV(
     REWR_CONV lab_to_targetTheory.enc_sec_list_def THENC
     RAND_CONV eval THENC
     REWR_CONV LET_THM THENC BETA_CONV THENC
     PATH_CONV"lrlr"eval) THENC
   PATH_CONV"lllr"eval THENC
   PATH_CONV"lr"eval)

val tm11 = remove_labels_thm0 |> rconc |> rand

val enc_sec_tm = tm11 |> rator |> rand

val skip_prog_els = skip_prog_def |> rconc |> listSyntax.dest_list |> #1

fun eval_fn i n p =
  let
    val () = say_str "enc_sec" i n
    val tm = mk_comb(enc_sec_tm,p)
  in time eval tm end

(* slow, >30 mins *)

val ths = parlist num_threads chunk_size eval_fn skip_prog_els

val remove_labels_thm1 =
  remove_labels_thm0
  |> CONV_RULE(RAND_CONV(
       RAND_CONV(
         RAND_CONV(REWR_CONV skip_prog_def) THENC
         map_ths_conv ths)))

val encoded_prog_def = mk_def"encoded_prog" (remove_labels_thm1 |> rconc |> rand);

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

val () = Lib.say "eval: compute_labels_alt: "

(* very slow!
  might be because x64_enc isn't evaluating properly?
  or just because encoded_prog_def contains huge terms...
val compute_labels_thm =
  tm12 |> (
    RAND_CONV(REWR_CONV encoded_prog_def) THENC
    time eval)
*)

val encoded_prog_els =
  encoded_prog_def |> rconc |> listSyntax.dest_list |> #1

val num_enc = length encoded_prog_els
val encoded_prog_defs = make_abbrevs "encoded_prog_el" num_enc encoded_prog_els []

val encoded_prog_thm =
  encoded_prog_def |> CONV_RULE(RAND_CONV(intro_abbrev (List.rev encoded_prog_defs)))

(* TODO: evaluate sec_lengths in parallel *)

(* TODO: evaluate compute_labels_alt with custom conv to unfold encoded_prog_els one-by-one *)

val (cln,clc) = CONJ_PAIR lab_to_targetTheory.compute_labels_alt_def

(*
val compute_labels_thm =
  tm12 |> (
    RAND_CONV(
      REWR_CONV encoded_prog_thm THENC
      RATOR_CONV(RAND_CONV(REWR_CONV(el 1800 encoded_prog_defs))))
    THENC
    REWR_CONV clc)
*)

(*
test encoder compset:
encoded_prog_def |> rconc |> listSyntax.dest_list |> #1 |> el 2
|> rand |> rator |> rand |> rator |> rand |> x64_compileLib.eval
*)

val _ = export_theory();

open preamble
     backendTheory
     to_dataBootstrapTheory
     x64_configTheory
     x64_targetTheory
     x64_targetLib
     asmLib

val _ = new_theory "x64Bootstrap";

(* TODO: move? *)

val Section_num_def = Define`
  Section_num (Section k _) = k`;
val Section_lines_def = Define`
  Section_lines (Section _ lines) = lines`;
val _ = export_rewrites["Section_num_def","Section_lines_def"];

val _ = hide"pos"

val compute_labels_alt_Section = Q.store_thm("compute_labels_alt_Section",
  `compute_labels_alt pos (sec::rest) =
   (let new_pos = sec_length (Section_lines sec) 0 in
    let labs = compute_labels_alt (pos + new_pos) rest in
    lab_insert (Section_num sec) 0 pos (section_labels pos (Section_lines sec) labs))`,
  Cases_on`sec` \\ rw[lab_to_targetTheory.compute_labels_alt_def]);

val pad_code_MAP = Q.store_thm("pad_code_MAP",
  `pad_code nop = MAP (λx. Section (Section_num x) (pad_section nop 0 (Section_lines x) []))`,
  simp[FUN_EQ_THM] \\ Induct
  \\ simp[lab_to_targetTheory.pad_code_def]
  \\ Cases \\ simp[lab_to_targetTheory.pad_code_def]);

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

fun mk_def_name s = String.concat[s,"_def"];
fun mk_def s tm = new_definition(mk_def_name s,mk_eq(mk_var(s,type_of tm),tm))

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
  ISPEC(lhs(concl(lab_prog_def)))lab_filterTheory.filter_skip_MAP

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

val encoded_prog_els =
  encoded_prog_def |> rconc |> listSyntax.dest_list |> #1

val num_enc = length encoded_prog_els
val encoded_prog_defs = make_abbrevs "encoded_prog_el" num_enc encoded_prog_els []

val encoded_prog_thm =
  encoded_prog_def |> CONV_RULE(RAND_CONV(intro_abbrev (List.rev encoded_prog_defs)))

val spec64 = INST_TYPE[alpha |-> fcpSyntax.mk_int_numeric_type 64]

val clc = compute_labels_alt_Section |> spec64

val cln = CONJUNCT1 lab_to_targetTheory.compute_labels_alt_def |> spec64

val (sec_length_tm,args) =
  clc |> SPEC_ALL |> rconc |> rand |> strip_comb

val Section_lines_tm = args |> hd |> dest_comb |> #1

val targs = tl args

fun eval_fn i n th =
  let
    val () = say_str "sec_length" i n
    val (enc_tm,enc_prog) = dest_eq (concl th)
    val tm = list_mk_comb(sec_length_tm,mk_comb(Section_lines_tm,enc_tm)::targs)
    val conv =
      RATOR_CONV(RAND_CONV(
        RAND_CONV(REWR_CONV th) THENC
        REWR_CONV Section_lines_def)) THENC
      time eval
  in
    conv tm
  end

val sec_lengths = parlist num_threads chunk_size eval_fn encoded_prog_defs

val () = PolyML.fullGC();

(*
val () = PolyML.SaveState.saveState"heap12"

val () = PolyML.SaveState.loadState"heap12"
*)

(*
val tm = tm12 |> RAND_CONV(REWR_CONV encoded_prog_thm) |> rconc

val (sth::sths) = sec_lengths
val (dth::dths) = List.rev encoded_prog_defs
*)

fun eval_fn n tm =
  let
    val () = Lib.say(String.concat["compute_labels ",Int.toString n,": "])
  in time eval tm end

fun compute_labels_alt_conv _ [] [] tm = REWR_CONV cln tm
  | compute_labels_alt_conv n (dth::dths) (sth::sths) tm =
    tm |>
    (REWR_CONV clc THENC
     REWR_CONV LET_THM THENC
     RAND_CONV (REWR_CONV sth) THENC
     BETA_CONV THENC
     RAND_CONV(RATOR_CONV(RAND_CONV numLib.REDUCE_CONV)) THENC
     PATH_CONV"lra"(
       PATH_CONV"lllr"(
         RAND_CONV(REWR_CONV dth) THENC
         REWR_CONV Section_num_def) THENC
       PATH_CONV"rlr"(
         RAND_CONV(REWR_CONV dth) THENC
         REWR_CONV Section_lines_def)) THENC
     REWR_CONV LET_THM THENC
     RAND_CONV (compute_labels_alt_conv (n+1) dths sths) THENC
     BETA_CONV THENC eval_fn n)

val compute_labels_thm =
  tm12 |> (
    RAND_CONV(REWR_CONV encoded_prog_thm) THENC
    compute_labels_alt_conv 0 (List.rev encoded_prog_defs) sec_lengths)

val computed_labs_def = mk_def"computed_labs"(compute_labels_thm |> rconc)
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

val (esn,esc) = lab_to_targetTheory.enc_secs_again_def |> spec64 |> CONJ_PAIR

(*
val tm = tm13 |> RAND_CONV(REWR_CONV encoded_prog_thm) |> rconc
val (dth::dths) = List.rev encoded_prog_defs
val n = 0
*)

fun eval_fn n tm =
  let
    val () = Lib.say(String.concat["enc_secs_again ",Int.toString n,": "])
  in time eval tm end

val T_AND = AND_CLAUSES |> SPEC_ALL |> CONJUNCT1

fun enc_secs_again_conv n [] tm = REWR_CONV esn tm
  | enc_secs_again_conv n (dth::dths) tm =
    let
      val th1 = tm |>
       (RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV dth))) THENC
        REWR_CONV esc THENC
        RAND_CONV(
          PATH_CONV"llllr"(REWR_CONV computed_labs_def) THENC
          eval_fn n))
      val def = mk_def("enc_again_"^Int.toString n)
                  (th1 |> rconc |> rand |> rator |> rand)
      val rec_conv = enc_secs_again_conv (n+1) dths
    in
      th1 |> CONV_RULE(RAND_CONV(
        RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM def)))) THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
        RAND_CONV(
          RAND_CONV (
            RATOR_CONV(RAND_CONV(REWR_CONV def)) THENC
            eval) THENC
          numLib.REDUCE_CONV) THENC
        REWR_CONV LET_THM THENC BETA_CONV THENC
        PATH_CONV"lrraar"(REWR_CONV T_AND) THENC
        RAND_CONV rec_conv THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV))
    end

val enc_secs_again_thm =
  tm13 |> (
    RAND_CONV(REWR_CONV encoded_prog_thm) THENC
    enc_secs_again_conv 0 (List.rev encoded_prog_defs))


val COND_T = COND_CLAUSES |> SPEC_ALL |> CONJUNCT1

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
  for 0 (num_enc-1) (fn i => definition(mk_def_name("enc_again_"^(Int.toString i))))

val (uln,ulc) = lab_to_targetTheory.upd_lab_len_def |> spec64 |> CONJ_PAIR

(*
val tm = tm14
val (dth::_) = enc_again_defs
val n = 0
*)

fun eval_fn n tm =
  let
    val () = Lib.say(String.concat["upd_lab_len ",Int.toString n,": "])
  in time eval tm end

fun upd_lab_len_conv _ [] tm = REWR_CONV uln tm
  | upd_lab_len_conv n (dth::dths) tm =
    let
      val th1 =
        tm |> (
          REWR_CONV ulc THENC
          RAND_CONV(
            RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
            eval_fn n))
      val def = mk_def ("upd_lab_"^(Int.toString n)) (rand(rconc th1))
    in
      th1 |> CONV_RULE(RAND_CONV(
        RAND_CONV(REWR_CONV(SYM def)) THENC
        REWR_CONV LET_THM THENC BETA_CONV THENC
        RAND_CONV(
          RAND_CONV(
            RATOR_CONV(RAND_CONV(REWR_CONV def)) THENC
            eval) THENC
          numLib.REDUCE_CONV) THENC
        REWR_CONV LET_THM THENC BETA_CONV THENC
        REWR_CONV LET_THM THENC
        RAND_CONV(upd_lab_len_conv (n+1) dths) THENC
        BETA_CONV))
    end

val upd_lab_len_thm =
  tm14 |> upd_lab_len_conv 0 enc_again_defs

val lab_to_target_thm5 =
  lab_to_target_thm4
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         RAND_CONV(REWR_CONV upd_lab_len_thm) THENC
         BETA_CONV)))

val tm15 =
  lab_to_target_thm5 |> rconc |> funpow 2 rator |> funpow 2 rand

val upd_lab_defs =
  for 0 (num_enc-1) (fn i => definition(mk_def_name("upd_lab_"^(Int.toString i))))

fun eval_fn i n dth =
  let
    val () = say_str "sec_length2" i n
    val ltm = dth |> concl |> lhs
    val tm = list_mk_comb(sec_length_tm,ltm::targs)
  in (RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
      time eval) tm end

val sec_lengths2 = parlist num_threads chunk_size eval_fn upd_lab_defs

(* TODO:
  the previous compute_labels_alt thing could be this instead, if encoded_progs
  were defined differently (define the lines rather than the whole Sections *)

val (cln,clc) =
  lab_to_targetTheory.compute_labels_alt_def |> spec64 |> CONJ_PAIR

fun eval_fn str n tm =
  let
    val () = Lib.say(String.concat[str," ",Int.toString n,": "])
  in time eval tm end

fun compute_labels_alt_conv _ _ [] [] tm = REWR_CONV cln tm
  | compute_labels_alt_conv str n (dth::dths) (sth::sths) tm =
    tm |>
    (REWR_CONV clc THENC
     REWR_CONV LET_THM THENC
     RAND_CONV (REWR_CONV sth) THENC
     BETA_CONV THENC
     RAND_CONV(RATOR_CONV(RAND_CONV numLib.REDUCE_CONV)) THENC
     PATH_CONV"lrarlr"(REWR_CONV dth) THENC
     REWR_CONV LET_THM THENC
     RAND_CONV (compute_labels_alt_conv str (n+1) dths sths) THENC
     BETA_CONV THENC eval_fn str n)

(*
val tm = tm15
val (dth::_) = upd_lab_defs
val (sth::_) = List.rev sec_lengths2
*)

val compute_labels_thm2 =
  tm15 |> compute_labels_alt_conv "compute_labels2" 0 upd_lab_defs (List.rev sec_lengths2)

val computed_labs2_def = mk_def"computed_labs2"(compute_labels_thm2 |> rconc)
val compute_labels_thm2' =
  compute_labels_thm2 |>
  CONV_RULE(RAND_CONV(REWR_CONV(SYM computed_labs2_def)))

val lab_to_target_thm6 =
  lab_to_target_thm5
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr" (
         RAND_CONV (REWR_CONV compute_labels_thm2') THENC
         REWR_CONV LET_THM THENC BETA_CONV)))

(* similar to compute_labels_alt_conv, could be reused if encoded_progs were
   abbreviated differently *)

fun eval_fn n tm =
  let
    val () = Lib.say(String.concat["enc_secs_again2 ",Int.toString n,": "])
  in time eval tm end

fun enc_secs_again_conv n [] tm = REWR_CONV esn tm
  | enc_secs_again_conv n (dth::dths) tm =
    let
      val th1 = tm |>
       (REWR_CONV esc THENC
        RAND_CONV(
          PATH_CONV"llllr"(REWR_CONV computed_labs2_def) THENC
          PATH_CONV"lr"(REWR_CONV dth) THENC
          eval_fn n))
      val def = mk_def("enc_again2_"^Int.toString n)
                  (th1 |> rconc |> rand |> rator |> rand)
      val rec_conv = enc_secs_again_conv (n+1) dths
    in
      th1 |> CONV_RULE(RAND_CONV(
        RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(SYM def)))) THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
        RAND_CONV(
          RAND_CONV (
            RATOR_CONV(RAND_CONV(REWR_CONV def)) THENC
            eval) THENC
          numLib.REDUCE_CONV) THENC
        REWR_CONV LET_THM THENC BETA_CONV THENC
        PATH_CONV"lrraar"(REWR_CONV T_AND) THENC
        RAND_CONV rec_conv THENC
        REWR_CONV LET_THM THENC PAIRED_BETA_CONV))
    end

val tm16 =
  lab_to_target_thm6 |> rconc |> funpow 2 rator |> funpow 2 rand

val enc_secs_again_thm2 =
  tm16 |> enc_secs_again_conv 0 upd_lab_defs

val lab_to_target_thm7 =
  lab_to_target_thm6 |> CONV_RULE(RAND_CONV(
    PATH_CONV"llr"(
      RAND_CONV(REWR_CONV enc_secs_again_thm2) THENC
      REWR_CONV LET_THM THENC PAIRED_BETA_CONV THENC
      REWR_CONV LET_THM THENC
      RAND_CONV(RATOR_CONV(REWR_CONV pad_code_MAP)))))

val tm17 =
  lab_to_target_thm7 |> rconc |> funpow 2 rator |> funpow 2 rand

val () = PolyML.fullGC();

(*
val () = PolyML.SaveState.saveState"heap17"

val () = PolyML.SaveState.loadState"heap17"
*)

val pad_section_tm =
  tm17 |> rator |> rand

val enc_again2_defs =
  for 0 (num_enc-1) (fn i => definition(mk_def_name("enc_again2_"^(Int.toString i))))

(*
val (dth::_) = enc_again2_defs
val p = tm17 |> rand |> rator |> rand
*)

fun eval_fn i n (dth, p) =
  let
    val () = say_str "pad_section" i n
    val tm = mk_comb(pad_section_tm,p)
    val conv =
      BETA_CONV THENC
      RATOR_CONV(RAND_CONV(REWR_CONV Section_num_def)) THENC
      RAND_CONV(
        RATOR_CONV(RAND_CONV(
          REWR_CONV Section_lines_def THENC
          REWR_CONV dth)) THENC
        time eval)
  in conv tm end

val enc_again2_els =
  tm17 |> rand |> listSyntax.dest_list |> #1

val pad_code_thms =
  parlist num_threads chunk_size eval_fn
    (zip enc_again2_defs enc_again2_els)

val pad_code_defs =
  make_abbrevs "pad_code_" num_enc (pad_code_thms |> map (rand o rconc)) []

val pad_code_thms' =
    map2 (CONV_RULE o RAND_CONV o RAND_CONV o REWR_CONV o SYM)
      (List.rev pad_code_defs) pad_code_thms

val pad_code_thm =
  tm17 |> (map_ths_conv pad_code_thms')

val padded_code_def = mk_def"padded_code"(rconc pad_code_thm)

val pad_code_thm' =
  pad_code_thm |> CONV_RULE(RAND_CONV(REWR_CONV(SYM padded_code_def)))

val lab_to_target_thm8 =
  lab_to_target_thm7
  |> CONV_RULE(RAND_CONV(
       PATH_CONV"llr"(
         RAND_CONV(REWR_CONV pad_code_thm') THENC
         BETA_CONV THENC
         REWR_CONV LET_THM THENC BETA_CONV THENC
         RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV T_AND))))))

val tm18 =
  lab_to_target_thm8 |> rconc
  |> funpow 2 rator |> rand
  |> funpow 2 rator |> rand

fun eval_fn i n dth =
  let
    val () = say_str "sec_length3" i n
    val ltm = dth |> concl |> lhs
    val tm = list_mk_comb(sec_length_tm,ltm::targs)
  in (RATOR_CONV(RAND_CONV(REWR_CONV dth)) THENC
      time eval) tm end

val sec_lengths3 = parlist num_threads chunk_size eval_fn pad_code_defs

val compute_labels_thm3 =
  tm18 |> rand |> lhs |> RAND_CONV (REWR_CONV padded_code_def) |> rconc
  |> compute_labels_alt_conv "compute_labels3" 0 pad_code_defs (List.rev sec_lengths3)

val compute_labels_thm3' =
  compute_labels_thm3
  |> CONV_RULE(RATOR_CONV(RAND_CONV(RAND_CONV(REWR_CONV(SYM padded_code_def)))))

val labs_eq =
  tm18 |> rand
  |> (LAND_CONV(REWR_CONV compute_labels_thm3') THENC
      RAND_CONV(REWR_CONV computed_labs2_def) THENC
      eval)

val (aen,aec) = lab_to_targetTheory.all_enc_ok_def |> spec64 |> CONJ_PAIR
val (aesn,aesc) = aec |> CONJ_PAIR

(*
val tm =
  tm18 |> rator |> rand
  |> (RAND_CONV(REWR_CONV padded_code_def))
  |> rconc
val (dth::_) = pad_code_defs
*)

fun eval_fn str n m tm =
  let
    val () = Lib.say(String.concat[str," ",Int.toString n,".",Int.toString m,": "])
  in time eval tm end

fun all_enc_ok_conv _ _ [] tm = REWR_CONV aen tm
  | all_enc_ok_conv n m (SOME dth::dths) tm =
      tm |>
      (RAND_CONV(
         RATOR_CONV(RAND_CONV(RAND_CONV(REWR_CONV dth))) ) THENC
       aesc_conv n m dths)
  | all_enc_ok_conv n m (NONE::dths) tm =
      tm |> (
        (REWR_CONV aesn THENC
         LAND_CONV(numLib.REDUCE_CONV) THENC
         REWR_CONV T_AND THENC
         all_enc_ok_conv (n+1) 0 dths)
        ORELSEC aesc_conv n m dths)
and aesc_conv n m dths =
       (REWR_CONV aesc THENC
         RATOR_CONV(RAND_CONV(
           PATH_CONV"llr"(REWR_CONV computed_labs2_def) THENC
           eval_fn "line_ok" n m)) THENC
         REWR_CONV T_AND THENC
         PATH_CONV"lr"(
           RAND_CONV(eval_fn "line_length" n m) THENC
           numLib.REDUCE_CONV) THENC
         all_enc_ok_conv n (m+1) (NONE::dths))

(* extremely slow: lots of lines to check

val encs_ok =
  tm18 |> rator |> rand
  |> (RAND_CONV(REWR_CONV padded_code_def) THENC
      all_enc_ok_conv 0 0 (map SOME pad_code_defs))
*)

(*
this is not true so doesn't work

val padded_code_els =
  padded_code_def |> rconc |> listSyntax.dest_list |> #1
val upd_lab_els =
  compute_labels_thm2'
  |> concl |> lhs |> rand |> listSyntax.dest_list |> #1

(*
val t1 = el 1 upd_lab_els
val t2 = el 1 padded_code_els
val dth = el 1 upd_lab_defs
*)

fun eval_fn i n (t1,dth,t2) =
  let
    val () = say_str "pad_eq" i n
    val tm = mk_eq(t1,t2)
    val conv =
      RATOR_CONV(RAND_CONV(RAND_CONV(REWR_CONV dth))) THENC
      time eval
  in conv tm |> EQT_ELIM end

compute_labels_thm2'
upd_lab_defs
*)


val _ = export_theory();

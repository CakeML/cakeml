open HolKernel Parse boolLib bossLib; 
open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory listLib;
open reg_allocTheory word_procTheory sortingTheory ml_translatorTheory
open sptreeTheory state_transformerTheory
open astPP
open lcsymtacs arithmeticTheory numeralTheory pred_setTheory
open miscLib BasicProvers

val _ = new_theory "reg_alloc_translate";

val _ = translate_into_module "reg_alloc";

val _ = std_preludeLib.std_prelude ();

val _ = add_preferred_thy "reg_alloc";
val _ = add_preferred_thy "word_proc";

val _ = enable_astPP();

val _ = set_trace "Goalstack.print_goal_at_top" 0; (*/"*)

val NOT_NIL_AND_LEMMA = prove(
  ``(b <> [] /\ x) = if b = [] then F else x``,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "reg_alloc" name handle HOL_ERR _ =>
            def_from_thy "word_proc" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> RW [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(*sptree*)
val _ = Parse.reveal"lrnext"

val DIV2_BIT2 = store_thm("DIV2_BIT2",
  ``DIV2 (BIT2 x) = SUC x``,
  metis_tac[numeral_div2,NUMERAL_DEF])

val bit_zero = prove(
``BIT1 n ≠ 0 ∧ BIT2 n ≠ 0``,
  simp[Once BIT1,Once BIT2] >>
  simp[Once BIT2])

val DIV2_PRE = store_thm("DIV2_PRE",
  ``∀n. DIV2 (PRE n) = if ODD n then DIV2 n else PRE (DIV2 n)``,
  ho_match_mp_tac bit_induction >>
  simp[numeral_evenodd] >>
  conj_tac >- ( simp[ALT_ZERO] ) >>
  simp[numeral_pre] >>
  simp[DIV2_BIT1,DIV2_BIT2] >>
  ho_match_mp_tac bit_induction >>
  simp[numeral_evenodd,numeral_pre,DIV2_BIT1,DIV2_BIT2,numeral_suc] >>
  conj_tac >- ( simp[ALT_ZERO] ) >>
  rpt strip_tac >>
  metis_tac[SUC_PRE,bit_zero,NOT_ZERO_LT_ZERO])

val lrnext_alt = prove(
  ``∀n. lrnext n =
        if n = 0 then 1
        else 2 * lrnext (DIV2 (PRE n))``,
  ho_match_mp_tac bit_induction >>
  conj_tac >- simp[lrnext_thm,ALT_ZERO] >>
  simp[lrnext_thm,bit_zero] >>
  conj_tac >> Cases >> simp[lrnext_thm] >>
  simp[DIV2_PRE,numeral_evenodd,DIV2_BIT1,lrnext_thm,DIV2_BIT2])

val lrnext_ind = store_thm("lrnext_ind",
``∀P.
  (∀n:num. (n ≠ 0 ⇒ P ((n-1) DIV 2)) ⇒ P n) ⇒ ∀v. P v``,
  ntac 2 strip_tac>>
  completeInduct_on`v`>>
  fs[]>>
  last_assum(qspec_then `v` assume_tac)>>
  Cases_on`v`>>fs[]>>
  `(n DIV 2) < SUC n` by
    (Cases_on`n`>>fs[]>>
    Q.SPECL_THEN [`SUC n'`,`2`] assume_tac arithmeticTheory.DIV_LESS>>
    DECIDE_TAC)>>
  metis_tac[])

val _ = lrnext_alt |> REWRITE_RULE[PRE_SUB1,DIV2_def] |> curry save_thm"lrnext_alt" |> translate

val option_filter_alt = prove(``
  (option_filter ([]:'a option list) = []) ∧ 
  ∀x:'a option xs.
  (option_filter (x::xs) = 
    case x of NONE => option_filter xs | SOME y => y :: (option_filter xs))``,
  rw[option_filter_def]>>Cases_on`x`>>fs[])

val def = option_filter_alt |> REWRITE_RULE[] |> curry save_thm"option_filter_alt"  
val _ = translate def

val _ = translate briggs_ok_def

fun fsm ls = fs (ls@[BIND_DEF,UNIT_DEF,IGNORE_BIND_DEF,FOREACH_def]);

val rpt_do_step_alt = prove(``
  rpt_do_step = \s. ((),WHILE (FST o has_work) (SND o do_step) s)``,
  fs[FUN_EQ_THM,rpt_do_step_def]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  fs[Once whileTheory.WHILE]>>
  Q.ISPECL_THEN [`has_work`,`do_step`] assume_tac MWHILE_DEF>>
  pop_assum (SUBST1_TAC)>>
  fsm[has_work_def,get_clock_def]>>
  IF_CASES_TAC>>fsm[]>>
  Cases_on`do_step s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  Q.ISPECL_THEN [`s`,`s.graph`,`r`] mp_tac do_step_graph_lemma>>
  (*Need to use a different lemma without undir_graph assumption*)
  discharge_hyps>- cheat>>
  (*Prove that the clock decreases*) 
  fsm[]>>ntac 2 strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])
  
val _ = translate rpt_do_step_alt

val rpt_do_step2_alt = prove(``
  rpt_do_step2 = \s. ((),WHILE (FST o has_work) (SND o do_step2) s)``,
  fs[FUN_EQ_THM,rpt_do_step2_def]>>
  completeInduct_on`s.clock`>>
  rw[]>>
  fs[Once whileTheory.WHILE]>>
  Q.ISPECL_THEN [`has_work`,`do_step2`] assume_tac MWHILE_DEF>>
  pop_assum (SUBST1_TAC)>>
  fsm[has_work_def,get_clock_def]>>
  IF_CASES_TAC>>fsm[]>>
  Cases_on`do_step2 s`>>
  first_x_assum(qspec_then`r.clock` mp_tac)>>
  discharge_hyps>- cheat>>
  (*Prove that the clock decreases*) 
  fsm[]>>strip_tac>>
  simp[Once whileTheory.WHILE,SimpRHS])

val _ = translate rpt_do_step2_alt
val _ = translate aux_move_pref_def

val option_CASE_thm = prove(
  ``option_CASE x f g = case x of NONE => f | SOME y => g y``,
  CONV_TAC (DEPTH_CONV ETA_CONV) THEN SIMP_TAC std_ss []);

(*Should provide a weakening*)
val aux_move_pref_side_def = prove(``
  ∀a b c d e.
  (d ≠ [] ) ⇒ aux_move_pref_side a b c d e``,
  rw[fetch"-""aux_move_pref_side_def"])

(*  (d ≠ []) ⇒ aux_move_pref_side a b c d e``,
  rw[fetch"-""aux_move_pref_side_def",EQ_IMP_THM]) |> update_precondition
  fs[option_CASE_thm]>>
  Cases_on`
  FULL_CASE_TAC>>fs[]>>
  Cases_on`d`>>fs[]
  first_match_col_def
*)

(*Use the clock trick*)
val rpt_do_step_side_def = prove(``
  ∀s. rpt_do_step_side s ⇔ T``,cheat)|>update_precondition

(*Use the clock trick*)
val rpt_do_step2_side_def = prove(``
  ∀s. rpt_do_step2_side s ⇔ T``,cheat) |> update_precondition

val _ = translate init_ra_state_def

val init_ra_state_side_def = prove(``
  ∀a b c. init_ra_state_side a b c ⇔ T``,
  fs[fetch "-" "init_ra_state_side_def"]>>rw[]>>
  fs[MEM_FILTER,MEM_MAP]>>Cases_on`y`>>
  fs[MEM_toAList]) |> update_precondition

val full_coalesce_aux_side_def = prove(``
  ∀ls G.
  (∀pxy. MEM pxy ls ⇒let (p:num,x,y) = pxy in
    x ∈ domain G ∧ y ∈ domain G) ⇒ 
  full_coalesce_aux_side G ls``,
  Induct>>
  simp[Once (fetch"-""full_coalesce_aux_side_def")]>>
  rw[]>-
    cheat (*because we strictly extend the domain*)
  >>
  first_x_assum(qspec_then`x4,x2,x1` assume_tac)>>fs[]>>
  fs[domain_lookup])

val _ = translate full_coalesce_def
val irc_alloc_def =  Define`
  irc_alloc (alg:num) G k moves =
  let s = init_ra_state G k moves in
  let ((),s) = rpt_do_step s in
  let coalesced = s.coalesced in 
  let pref = aux_move_pref coalesced (resort_moves(moves_to_sp moves LN)) in
  let (col,ls) = alloc_coloring s.graph k pref s.stack in
  let (G,spills,coalesce_map) = full_coalesce s.graph moves ls in 
  let s = sec_ra_state G k spills coalesce_map in
  let ((),s) = rpt_do_step2 s in
  let col = spill_coloring G k coalesce_map s.stack col in
  let col = spill_coloring G k LN ls col in
    col`

val _ = translate irc_alloc_def


val _ = export_theory();

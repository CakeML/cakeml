open HolKernel Parse boolLib bossLib; 
open listTheory arithmeticTheory ml_translatorLib mini_preludeTheory listLib;
open reg_allocTheory word_procTheory sortingTheory ml_translatorTheory
open sptreeTheory state_transformerTheory
open astPP
open lcsymtacs arithmeticTheory numeralTheory pred_setTheory

val _ = new_theory "reg_alloc_translate";

val _ = translate_into_module "reg_alloc";

val _ = std_preludeLib.std_prelude ();

val _ = add_preferred_thy "reg_alloc";
val _ = add_preferred_thy "word_proc";

val _ = enable_astPP();

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

val _ = translate option_filter_def

(*??? Doesn't seem provable*)
val option_filter_side_def = prove(
  ``∀v. option_filter_side v = T``,cheat)|>update_precondition

(*Fails*)
val _ = translate briggs_ok_def

(*These are all similar copies of briggs_ok*)
(*Fails*)
val test_def = Define`
  test (G:sp_graph) (k:num) degs (x,y) =
  case lookup x G of NONE => F
  | SOME x_edges => 
  case lookup y G of NONE => F
  | SOME y_edges => 
  let edges = union x_edges y_edges in
  let odegs = MAP (λx,y. lookup x degs) (toAList edges) in
  let degs = option_filter odegs in 
    k=5`
val _ = translate test_def;

(*Works*)
val test2_def = Define`
  test2 (G:sp_graph) (k:num) degs (x,y) =
  case lookup x G of NONE => F
  | SOME x_edges => 
  case lookup y G of NONE => F
  | SOME y_edges => 
  let edges = union x_edges y_edges in
  let odegs = MAP (λx,y. lookup x degs) (toAList edges) in
    k=5`
val _ = translate test2_def;

(*Works*)
val test3_def = Define`
  test3 (G:sp_graph) (k:num) degs (x,y) =
  case lookup x G of NONE => F
  | SOME x_edges => 
  case lookup y G of NONE => F
  | SOME y_edges => 
  let edges = union x_edges y_edges in
  let odegs = MAP (λx,y. lookup x degs) (toAList edges) in
  let degs = option_filter odegs in
    T` 
val _ = translate test3_def;

(*Fails*)
val _ = translate MWHILE_DEF

(*
val _ = translate init_ra_state_def

val _ = translate do_step_def


val _ = translate rpt_do_step_def
val _ = translate reg_alloc_def
*)

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = export_theory();

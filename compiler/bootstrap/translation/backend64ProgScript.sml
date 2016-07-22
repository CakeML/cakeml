open HolKernel Parse boolLib bossLib;
open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open std_preludeTheory;

val _ = new_theory "backend64Prog"
val _ = translation_extends "std_prelude";

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE
fun list_dest f tm =
  let val (x,y) = f tm in list_dest f x @ list_dest f y end
  handle HOL_ERR _ => [tm];
val dest_fun_type = dom_rng
val mk_fun_type = curry op -->;
fun list_mk_fun_type [ty] = ty
  | list_mk_fun_type (ty1::tys) =
      mk_fun_type ty1 (list_mk_fun_type tys)
  | list_mk_fun_type _ = fail()

val _ = register_type ``:lexer_fun$symbol``;

(* translator setup *)

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

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
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o INST_TYPE[alpha|->``:64``] o SPEC_ALL

(*TODO: Translating them all in 1 shot doesn't work... *)
val _ = translate (conv64_RHS backendTheory.to_mod_def)
val _ = translate (conv64_RHS backendTheory.to_con_def)
val _ = translate (conv64_RHS backendTheory.to_dec_def)
val _ = translate (conv64_RHS backendTheory.to_exh_def)
val _ = translate (exh_to_patTheory.pure_op_op_eqn)
val _ = translate (conv64_RHS backendTheory.to_pat_def)
val _ = translate (conv64_RHS backendTheory.to_clos_def)

(*TODO: slow proof *)
val compile_4_side = prove(``
  ∀x. compile_4_side x ⇔ T``,
  recInduct pat_to_closTheory.compile_ind>>
  rw[]>>
  simp[Once (fetch "-" "compile_4_side_def")]>>
  Cases_on`es`>>fs[])|>update_precondition;

val to_clos_side = prove(``
  ∀a b. to_clos_side a b ⇔ T``,
  simp[(fetch "-" "to_clos_side_def")]>>
  metis_tac[compile_4_side]) |> update_precondition

(* MTI *)
val _ = translate(clos_mtiTheory.intro_multi_def)

val intro_multi_side = prove(``
  ∀a. intro_multi_side a ⇔ T``,
  ho_match_mp_tac clos_mtiTheory.intro_multi_ind>>
  `∀z. intro_multi [z] ≠ []` by
    (CCONTR_TAC>>fs[]>>
    Q.SPEC_THEN `z` mp_tac clos_mtiTheory.intro_multi_sing >>fs[])>>
  rw[]>>
  simp[Once (fetch "-" "intro_multi_side_def")]>>
  metis_tac[])|>update_precondition

(* number
TODO: make this not have to be explicitly translated, probably by renaming it to renumber_code_locs_list_def
*)
val _ = translate (clos_numberTheory.renumber_code_locs_def)

val renumber_code_locs_list_side = prove(``
  (∀a b. renumber_code_locs_list_side a b ⇔ T) ∧
  (∀a b. renumber_code_locs_side a b ⇔ T)``,
  ho_match_mp_tac clos_numberTheory.renumber_code_locs_ind>>rw[]>>
  simp[Once (fetch"-" "renumber_code_locs_list_side_def")]>>
  metis_tac[clos_numberTheory.renumber_code_locs_length,LENGTH_MAP,SND]) |> update_precondition

(* known *)
val _ = translate clos_knownTheory.merge_alt

val num_abs_intro = prove(``
  ∀x. Num x = if 0 ≤ x then Num (ABS x) else Num x``,
  rw[]>>intLib.COOPER_TAC);

val _ = translate (clos_knownTheory.known_op_def |> ONCE_REWRITE_RULE [num_abs_intro] |> SIMP_RULE std_ss []);

val _ = translate (clos_knownTheory.known_def)

val known_op_side = prove(``
  ∀a b c. known_op_side a b c ⇔ T``,
  simp[Once (fetch"-" "known_op_side_def")]>>rw[]>>
  intLib.COOPER_TAC)

val known_side = prove(``
  ∀a b c. known_side a b c ⇔ T``,
  ho_match_mp_tac clos_knownTheory.known_ind>>
  `∀z a b c. known [z] a b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_knownTheory.known_sing_EQ_E>>
    fs[])>>
  rw[]>>simp[Once (fetch"-" "known_side_def")]>>
  metis_tac[FST,PAIR,known_op_side]) |> update_precondition

(* call *)

val _ = translate (clos_callTheory.calls_def)

val free_side = prove(``
  ∀a. free_side a ⇔ T``,
  ho_match_mp_tac clos_freeTheory.free_ind>>rw[]>>
  simp[Once (fetch "-" "free_side_def")]>>rw[]>>
  CCONTR_TAC>>fs[]>>
  imp_res_tac clos_freeTheory.free_SING>>fs[]>>
  metis_tac[]) |> update_precondition

val calls_side = prove(``
  ∀a b. calls_side a b ⇔ T``,
  ho_match_mp_tac clos_callTheory.calls_ind>>
  (*Move from calls proof*)
  `∀a b c. calls [a] b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_callTheory.calls_sing>>fs[])>>
  rw[]>> simp[Once (fetch"-" "calls_side_def"),Once (fetch "-" "closed_side_def"),free_side]>>
  TRY(metis_tac[])>>
  ntac 2 strip_tac>>
  simp[LAMBDA_PROD]>> rw[fetch "-" "closed_side_def",free_side]
  >-
    metis_tac[LIST_REL_LENGTH,LAMBDA_PROD]
  >>
    simp[GSYM LAMBDA_PROD]>>rw[]
    >- (imp_res_tac clos_callTheory.calls_length>>fs[])
    >> metis_tac[LIST_REL_LENGTH,LAMBDA_PROD]) |> update_precondition

(* remove *)
val _ = save_thm ("remove_ind",clos_removeTheory.remove_alt_ind)

val _ = translate (clos_removeTheory.remove_alt)

val remove_side = prove(``
  ∀x. remove_side x ⇔ T``,
  recInduct clos_removeTheory.remove_alt_ind>>
  rw[]>>
  simp[Once (fetch "-" "remove_side_def")]>>
  rw[]>>
  imp_res_tac clos_removeTheory.remove_SING>>fs[]>>
  TRY(first_x_assum match_mp_tac>>fs[]>>metis_tac[])>>
  CCONTR_TAC>>fs[]>>
  imp_res_tac clos_removeTheory.remove_SING>>fs[])|>update_precondition

(* shift *)
val _ = translate (clos_annotateTheory.shift_def)

val shift_side = prove(``
  ∀a b c d. shift_side a b c d ⇔ T``,
  ho_match_mp_tac clos_annotateTheory.shift_ind>>
  `∀a b c d. shift [a] b c d ≠ []` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_annotateTheory.shift_SING>>
    fs[])>>
  rw[]>>
  simp[Once (fetch "-" "shift_side_def")]>>
  rw[]>> metis_tac[]) |> update_precondition

val _ = translate (conv64_RHS backendTheory.to_bvl_def)

val jumplist_side = prove(``
  ∀a b. jumplist_side a b ⇔ T``,
  completeInduct_on`LENGTH (b:bvl$exp list)`>>
  rw[Once (fetch "-" "jumplist_side_def")]
  >-
    (Cases_on`b`>>fs[])
  >>
  fs[PULL_FORALL]>>
  first_assum match_mp_tac>>
  fs[]
  >-
    (Cases_on`x1`>>fs[ADD_DIV_RWT,ADD1])
  >>
    `SUC x1 DIV 2 < SUC x1` by
      fs[]>>
    simp[]);

val recc_lets_side = prove(``
  ∀a b c d.
  c = LENGTH b ⇒
  recc_lets_side a b c d``,
  ho_match_mp_tac clos_to_bvlTheory.recc_Lets_ind>>
  rw[]>>
  simp[Once (fetch"-" "recc_lets_side_def")]>>
  Cases_on`b`>>fs[])

val compile_exps_4_side = prove(``
  ∀a b. compile_exps_4_side a b``,
  ho_match_mp_tac clos_to_bvlTheory.compile_exps_ind>>
  `∀a b c. compile_exps [a] b ≠ ([],c)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_to_bvlTheory.compile_exps_SING>>
    fs[])>>
  rw[]>>
  simp[Once (fetch "-" "compile_exps_4_side_def")]>>
  TRY (metis_tac[])>>
  rw[]
  >-
    (fs[fetch"-" "build_recc_lets_side_def"]>>
    match_mp_tac recc_lets_side>>
    simp[LENGTH_TL])
  >>
  first_x_assum(qspecl_then[`x1`,`x43`,`x41`] assume_tac)>>
  CCONTR_TAC>>fs[])

val compile_prog_3_side = prove(``
  ∀x. compile_prog_3_side x ⇔ T``,
  ho_match_mp_tac clos_to_bvlTheory.compile_prog_ind>>rw[]>>
  simp[Once (fetch "-" "compile_prog_3_side_def"),compile_exps_4_side])

val to_bvl_side= prove(``
  ∀a b. to_bvl_side a b ⇔ T``,
  rw[Once (fetch "-" "to_bvl_side_def"),
  Once (fetch "-" "compile_5_1_side_def"),
  Once (fetch "-" "compile_6_side_def"),
  Once (fetch "-" "compile_7_side_def"),
  Once (fetch "-" "compile_8_side_def"),
  Once (fetch "-" "compile_9_side_def")]
  >-
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_callTheory.calls_sing>>
    fs[])
  >-
    (EVAL_TAC>>simp[jumplist_side])
  >-
    simp[compile_prog_3_side]
  >-
    (EVAL_TAC>>
    CCONTR_TAC >> fs[]>>
    Cases_on`free [v1]`>>
    imp_res_tac clos_freeTheory.free_SING>>fs[]>>
    imp_res_tac clos_annotateTheory.shift_SING>>fs[])
  >-
    (qpat_abbrev_tac`ls = v6'::A`>>
    Cases_on`remove ls`>>fs[Abbr`ls`]>>
    imp_res_tac clos_removeTheory.remove_LENGTH>>
    simp[])
  >-
    (CCONTR_TAC>>fs[]>>
    imp_res_tac clos_knownTheory.known_sing_EQ_E>>
    fs[])
  >>
    `∃z. compile v6.clos_conf.do_mti [v5] = [z]` by
      (Cases_on`v6.clos_conf.do_mti`>>fs[clos_mtiTheory.compile_def]>>
      metis_tac[clos_mtiTheory.intro_multi_sing])>>
    ntac 2 (pop_assum mp_tac)>>
    specl_args_of_then ``renumber_code_locs_list`` (clos_numberTheory.renumber_code_locs_length|>CONJUNCT1) assume_tac>>
    rw[]>>fs[]>>
    Cases_on`v10`>>fs[]) |> update_precondition

val _ = translate (bvl_handleTheory.LetLet_def |> SIMP_RULE std_ss [MAPi_enumerate_MAP])

val _ = translate (conv64_RHS backendTheory.to_bvi_def)

val _ = translate (bvi_to_dataTheory.op_requires_names_eqn)
val _ = translate (COUNT_LIST_compute)
val _ = translate (bvi_to_dataTheory.compile_exp_def)

val _ = translate (conv64_RHS backendTheory.to_data_def)

(* TODO: more preconditions, possibly do them earlier to avoid a mess *)

(*
Some data-to-word preliminaries
val _ = translate (data_to_wordTheory.adjust_set_def)

val _ = translate (conv64_RHS word_2comp_def)
val _ = translate (conv64_RHS data_to_wordTheory.GiveUp_def)
(* val _ = translate (conv64_RHS data_to_wordTheory.make_header_def) *)
val _ = translate (conv64_RHS word_extract_def|>INST_TYPE[beta|->``:64``])

val _ = translate (conv64_RHS word_slice_def)
val def = (conv64_RHS data_to_wordTheory.tag_mask_def)
*)

val _ = export_theory();

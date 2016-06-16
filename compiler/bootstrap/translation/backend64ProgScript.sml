open HolKernel Parse boolLib bossLib;
open preamble;
open terminationTheory inferProgTheory
open ml_translatorLib ml_translatorTheory;

val _ = new_theory "backend64Prog"

val _ = translation_extends "inferProg";

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

(*
TODO: make this not have to be explicitly translated, probably by renaming it to renumber_code_locs_list_def
*)
val _ = translate (clos_numberTheory.renumber_code_locs_def)
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

val _ = translate (conv64_RHS backendTheory.to_bvl_def)
(* TODO: bunch of preconditions for to_bvl ones... *)

(* TODO: See above *)
val _ = translate (bvl_constTheory.compile_exps_def)
val _ = translate (conv64_RHS backendTheory.to_bvi_def)
val _ = translate (bvi_to_bvpTheory.op_requires_names_eqn)

val _ = translate (COUNT_LIST_compute)
val _ = translate (bvi_to_bvpTheory.compile_exp_def)

val _ = translate (conv64_RHS backendTheory.to_bvp_def)

(* TODO: more preconditions, possibly do them earlier to avoid a mess *)

(*
Some bvp-to-word preliminaries
val _ = translate (bvp_to_wordTheory.adjust_set_def)

val _ = translate (conv64_RHS word_2comp_def)
val _ = translate (conv64_RHS bvp_to_wordTheory.GiveUp_def)
(* val _ = translate (conv64_RHS bvp_to_wordTheory.make_header_def) *)
val _ = translate (conv64_RHS word_extract_def|>INST_TYPE[beta|->``:64``])

val _ = translate (conv64_RHS word_slice_def)
val def = (conv64_RHS bvp_to_wordTheory.tag_mask_def)
*)

val _ = export_theory();

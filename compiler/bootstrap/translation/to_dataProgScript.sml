(*
  Translate the backend phase from BVI to dataLang.
*)

open preamble ml_translatorLib ml_translatorTheory to_bviProgTheory
local open backendTheory in end

val _ = new_theory "to_dataProg"
val _ = translation_extends "to_bviProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_dataProg");
val _ = ml_translatorLib.use_string_type true;

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

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

val _ = add_preferred_thy "-";
val _ = add_preferred_thy "termination";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy "termination" name handle HOL_ERR _ =>
            def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

(* ------------------------------------------------------------------------- *)
(* bvi_to_data                                                               *)
(* ------------------------------------------------------------------------- *)

val r = translate bvi_to_dataTheory.op_requires_names_pmatch;
val r = translate COUNT_LIST_compute;

(* TODO:
 *   - For some reason, the following def on sptrees fails to translate in a
 *     standalone manner (when the rest of this file's translation isn't
 *     loaded). Needs investigation.
 *)
val r = translate list_to_num_set_def;

val r = translate bvi_to_dataTheory.compile_def;

val bvi_to_data_compile_side = Q.prove(`
  ∀a b c d e. bvi_to_data_compile_side a b c d e ⇔ T`,
  ho_match_mp_tac bvi_to_dataTheory.compile_ind>>
  `∀a b c d e f g. bvi_to_data$compile a b c d [e] ≠ (f,[],g)` by
    (CCONTR_TAC>>fs[]>>
    imp_res_tac bvi_to_dataTheory.compile_SING_IMP>>
    fs[])>>
  rw[]>>
  simp[Once (fetch "-" "bvi_to_data_compile_side_def")]>>
  fs[FALSE_def]>>
  metis_tac[]) |> update_precondition;

(* TODO:
 *   - pmatch for bvl_space is broken
 *)
val r = translate data_spaceTheory.space_def;

val r = translate bvi_to_dataTheory.compile_prog_def;

(* ------------------------------------------------------------------------- *)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
val _ = export_theory ();

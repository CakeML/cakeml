(*
  Translate backend phases up to and including flatLang.
*)
open preamble ml_translatorLib ml_translatorTheory decProgTheory

local open source_to_flatTheory in end;

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "to_flatProg";
val _ = translation_extends "decProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_flatProg");

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

(* use CakeML's string type for HOL's char list *)
val _ = ml_translatorLib.use_string_type true;

(* ------------------------------------------------------------------------- *)
(* source_to_flat                                                            *)
(* ------------------------------------------------------------------------- *)

(* TODO:
 *   - This is a discrepancy between HOL's standard libraries and mllist.
 *     Probably the compiler should be using the mllist versions?
 *)
val res = translate EL;
val list_el_side = Q.prove(
  `!n xs. list_el_side n xs = (n < LENGTH xs)`,
  Induct THEN Cases_on `xs` THEN ONCE_REWRITE_TAC [fetch "-" "list_el_side_def"]
  THEN FULL_SIMP_TAC (srw_ss()) [CONTAINER_def])
  |> update_precondition;

(* -- *)

val res = translate listTheory.REV_DEF;
val res = translate listTheory.TAKE_def;
val res = translate listTheory.DROP_def;

val res = translate sumTheory.ISL;
val res = translate sumTheory.ISR;

val res = translate source_to_flatTheory.alloc_tags1_def;
val res = translate (DefnBase.one_line_ify NONE namespaceTheory.nsMap_def);
val res = translate source_to_flatTheory.alloc_tags_def;
val res = translate source_to_flatTheory.alloc_env_ref_def;
val res = translate source_to_flatTheory.glob_alloc_def;

val res = translate source_to_flatTheory.compile_decs_def;
val res = translate source_to_flatTheory.compile_prog_def;

val _ = (length (hyp res) = 0)
        orelse failwith "Unproved side condition: source_to_flat_compile_prog";
(* ------------------------------------------------------------------------- *)
(* source_to_source                                                          *)
(* ------------------------------------------------------------------------- *)

val res = translate source_to_sourceTheory.compile_def;

val _ = (length (hyp res) = 0)
        orelse failwith "Unproved side condition: source_to_source_compile";

(* ------------------------------------------------------------------------- *)
(* flat_elim                                                                 *)
(* ------------------------------------------------------------------------- *)

val res = translate sptreeTheory.subspt_eq;
val res = translate flat_elimTheory.remove_flat_prog_def;

(* ------------------------------------------------------------------------- *)
(* flat_pattern                                                              *)
(* ------------------------------------------------------------------------- *)

val _ = translate pattern_compTheory.is_True_def
val _ = translate pattern_compTheory.is_Any_def
val _ = translate pattern_compTheory.take_until_Any_def
val _ = translate pattern_compTheory.comp_def

val res = translate flat_patternTheory.enc_num_to_name_def;

val enc_side = Q.prove(
  `!n s. flat_pattern_enc_num_to_name_side n s = T`,
  gen_tac
  \\ measureInduct_on `I n`
  \\ simp [fetch "-" "flat_pattern_enc_num_to_name_side_def"]
  ) |> update_precondition;

val res = translate flat_patternTheory.dec_name_to_num_def;

val dec_side = Q.prove(
  `!s. flat_pattern_dec_name_to_num_side s = T`,
  simp [fetch "-" "flat_pattern_dec_name_to_num_side_def"]
  ) |> update_precondition;

val res = translate rich_listTheory.COUNT_LIST_compute;

val res = translate flat_patternTheory.compile_dec_def;

(* ------------------------------------------------------------------------- *)
(* source_to_flat                                                            *)
(* ------------------------------------------------------------------------- *)

val res = translate source_to_flatTheory.compile_flat_def;

val res = translate source_to_flatTheory.compile_def;

val res = translate source_to_flatTheory.inc_compile_def;

(* ------------------------------------------------------------------------- *)

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
val _ = export_theory ();

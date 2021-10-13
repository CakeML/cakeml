(*
  Translate the compiler's state decoder.
*)
open preamble
     num_list_enc_decTheory num_tree_enc_decTheory backend_enc_decTheory
     to_dataProgTheory ml_translatorLib ml_translatorTheory

val _ = new_theory "decodeProg"

val _ = translation_extends "to_dataProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "decodeProg");

(* translator setup *)

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

Theorem NOT_NIL_AND_LEMMA:
   (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

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
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

(* --- *)

val res = translate dec_next_def;
val res = translate chars_to_nums_def;

val res = translate const_dec_def;
val res = translate unit_dec_def;
val res = translate num_dec_def;
val res = translate num_list_enc_decTheory.list_dec'_def;
val res = translate list_dec_def;
val res = translate bool_dec_def;
val res = translate int_dec_def;
val _ = next_ml_names := ["word8_dec"];
val res = translate (word_dec_def |> INST_TYPE [alpha|->“:8”]);
val _ = next_ml_names := ["word64_dec"];
val res = translate (word_dec_def |> INST_TYPE [alpha|->“:64”]);
val res = translate char_dec_def;
val res = translate num_list_enc_decTheory.mlstring_dec_def;
val res = translate prod_dec_def;
val res = translate option_dec_def;
val res = translate sum_dec_def;
val res = translate spt_dec'_def;
val res = translate spt_dec''_def;
val res = translate spt_dec_def;
val res = translate namespace_dec'_def;
val res = translate namespace_dec_def;

(* --- *)

val res = translate num_tree_dec'_def;
val res = translate num_tree_dec_def;
val res = translate nth_def;
val res = translate int_dec'_def;
val res = translate bool_dec'_def;
val res = translate chr_dec'_def;
val res = translate list_dec'_def;
val res = translate pair_dec'_def;
val res = translate option_dec'_def;

(* --- *)



val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();

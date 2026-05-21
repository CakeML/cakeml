(*
  Translate the compiler's state decoder.
*)
Theory decodeProg[no_sig_docs]
Ancestors
  num_list_enc_dec num_tree_enc_dec backend_enc_dec explorerProg
  ml_translator
Libs
  preamble basisFunctionsLib ml_translatorLib cfLib

open preamble basisFunctionsLib
     num_list_enc_decTheory num_tree_enc_decTheory backend_enc_decTheory
     explorerProgTheory ml_translatorLib ml_translatorTheory cfLib;

val _ = translation_extends "explorerProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "decodeProg");
val _ = ml_translatorLib.use_sub_check true;

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

val _ = register_type “:lab_to_target$shmem_info_num”
val _ = register_type “:lab_to_target$config”

val _ = register_type “:backend$config”

Theorem IsTypeRep_BACKEND_CONFIG_v:
  IsTypeRep BACKEND_CONFIG_v BACKEND_CONFIG_TYPE
Proof
  irule_at Any (fetch_v_fun “:backend$config” |> snd |> hd) \\ fs []
  \\ irule_at Any (fetch_v_fun “:bvl_to_bvi$config” |> snd |> hd) \\ fs []
  \\ irule_at Any (fetch_v_fun “:clos_to_bvl$config” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a num_map” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a # 'b” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a option” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a list” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a num_map” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a # 'b” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:clos_known$config” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a list” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:closLang$exp” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:bvl$exp” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:closLang$op” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a list” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a num_map” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:clos_known$val_approx” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:closLang$exp” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:closLang$op” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:closLang$block_op” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:'a list” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:unit” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:num” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:closLang$const_part” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:closLang$const” |> snd |> hd) \\ fs []
  \\ rpt $ irule_at Any (fetch_v_fun “:word64” |> snd |> hd) \\ fs []
  \\ irule (fetch_v_fun “:lab_to_target$config” |> snd |> hd) \\ fs []
  \\ irule (fetch_v_fun “:'a list” |> snd |> hd) \\ fs []
  \\ irule (fetch_v_fun “:lab_to_target$shmem_info_num” |> snd |> hd) \\ fs []
  \\ irule (fetch_v_fun “:word8” |> snd |> hd) \\ fs []
QED

Theorem EqualityType_BACKEND_CONFIG_TYPE =
  EqualityType_rule [] “:backend$config”;

Theorem INJ_BACKEND_CONFIG_v[simp]:
  INJ BACKEND_CONFIG_v UNIV UNIV
Proof
  irule ml_translatorTheory.IsTypeRep_EqualityType_INJ
  \\ irule_at Any IsTypeRep_BACKEND_CONFIG_v
  \\ fs [EqualityType_BACKEND_CONFIG_TYPE]
QED

(* --- *)

val res = translate dec_next_def;
val res = translate chars_to_nums_def;
val res = translate num_list_enc_decTheory.mlstring_dec_def;
val res = translate mlstring_dec'_def;

Theorem list_dec'_eq_MAP:
  ∀f t. list_dec' f t = MAP f (list_dec' I t)
Proof
  Cases_on ‘t’ \\ fs [list_dec'_def]
QED

val res = translate num_list_enc_decTheory.list_dec'_def;
val res = translate (closLang_const_dec'_def |> DefnBase.one_line_ify NONE
                     |> ONCE_REWRITE_RULE [list_dec'_eq_MAP]);

val res = translate closLang_const_dec_def;
val res = translate unit_dec_def;
val res = translate num_dec_def;
val res = translate list_dec_def;
val res = translate bool_dec_def;
val res = translate int_dec_def;
val _ = next_ml_names := ["word8_dec"];
val res = translate (word_dec_def |> INST_TYPE [alpha|->“:8”]);
val _ = next_ml_names := ["word64_dec"];
val res = translate (word_dec_def |> INST_TYPE [alpha|->“:64”]);
val res = translate char_dec_def;
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

val res = translate (backend_common_tra_dec'_def |> DefnBase.one_line_ify NONE);
val res = translate safe_chr_list_def;
val res = translate list_chr_dec'_def;
val res = translate string_dec_def;
val res = translate source_to_flat_next_indices_dec_def;
val res = translate flat_pattern_config_dec_def;
val res = translate namespace_dec'_def;
val res = translate namespace_dec_def;
val res = translate (source_to_flat_var_name_dec'_def |> REWRITE_RULE [string_dec'_intro]);
val res = translate source_to_flat_var_name_dec_def;
val res = translate source_to_flat_environment_dec_def;
val res = translate source_to_flat_environment_store_dec_def;
val res = translate source_to_flat_config_dec_def;

val res = translate data_to_word_config_dec_def;
val res = translate word_to_word_config_dec_def;
val res = translate (word_to_stack_config_dec_def |> INST_TYPE [alpha|->“:64”]);
val res = translate stack_to_lab_config_dec_def;

val res = translate presLang_tap_config_dec'_def;
val res = translate presLang_tap_config_dec_def;

val res = translate (closLang_op_dec'_def |> DefnBase.one_line_ify NONE);

val def = bvl_exp_dec'_def |> DefnBase.one_line_ify NONE
          |> ONCE_REWRITE_RULE [list_dec'_eq_MAP]
val res = translate def;

val res = translate bvl_to_bvi_config_dec_def;

Theorem pair_dec'_eq:
  pair_dec' d1 d2 = λt. (d1 (nth 0 (list_dec' I t)), d2 (nth 1 (list_dec' I t)))
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
  \\ Cases \\ fs [pair_dec'_def,list_dec'_def]
QED

val def = closLang_exp_dec'_def |> DefnBase.one_line_ify NONE
          |> ONCE_REWRITE_RULE [list_dec'_eq_MAP]
          |> ONCE_REWRITE_RULE [pair_dec'_eq]
          |> CONV_RULE (DEPTH_CONV BETA_CONV)
val res = translate_no_ind def;

Theorem closlang_exp_dec'_ind[local]:
  closlang_exp_dec'_ind
Proof
  rewrite_tac [fetch "-" "closlang_exp_dec'_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum irule
  \\ rewrite_tac [num_tree_11]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt var_eq_tac
  \\ gen_tac \\ disch_then (assume_tac o SYM)
  \\ rename1 ‘SUC x6’
  \\ Cases_on ‘x6 = 0’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ ‘n ≠ 1 ∧ n ≠ 0’ by decide_tac
  \\ Cases_on ‘x6 = 1’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ ‘n ≠ 2’ by decide_tac
  \\ Cases_on ‘n = 3’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 4’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 5’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 6’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 7’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 8’ \\ asm_rewrite_tac [] THEN1 (gvs [ADD1])
  \\ Cases_on ‘n = 9’ \\ asm_rewrite_tac []
  \\ rpt var_eq_tac \\ gvs [ADD1]
QED

val _ = closlang_exp_dec'_ind |> update_precondition;

val def = clos_known_val_approx_dec'_def |> DefnBase.one_line_ify NONE
          |> ONCE_REWRITE_RULE [list_dec'_eq_MAP]
val res = translate def;

val def = clos_to_bvl_config_dec_def
val res = translate def;

val def = lab_to_target_config_dec_def
          |> REWRITE_RULE [GSYM string_dec_thm]
val res = translate def;
val res = translate backend_config_dec_def;

val res = translate decode_backend_config_def;


val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

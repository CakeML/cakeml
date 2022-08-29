(*
  Translate the pan_to_target part of the 64-bit compiler.
*)

open preamble;
open ml_translatorLib ml_translatorTheory;
open to_target64ProgTheory std_preludeTheory;
local open backendTheory in end

val _ = new_theory "from_pancake64Prog"

val _ = translation_extends "to_target64Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_pancake64Prog");
val _ = ml_translatorLib.use_string_type true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val matches = ref ([]: term list);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:64``,beta|->``:64``] else []

  val def = def |> RW (!extra_preprocessing)
                |> INST_TYPE insts
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

open panLangTheory;

val _ = register_type “:64 panLang$exp”;

val _ = register_type “:64 panLang$prog”;

val _ = translate $ spec64 exp_ids_def;

open crepLangTheory;

val _ = register_type “:64 crepLang$exp”;

val _ = register_type “:64 crepLang$prog”;

val _ = translate $ spec64 var_cexp_def;

val _ = translate $ spec64 acc_vars_def;

val _ = translate $ spec64 nested_decs_def;

val _ = translate $ spec64 nested_seq_def;

val lem = Q.prove(‘dimindex(:64) = 64’, EVAL_TAC);

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 stores_def;

val _ = translate $ spec64 store_globals_def;

val _ = translate $ spec64 load_globals_def;

val _ = translate $ spec64 assign_ret_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec64 load_shape_def;

open pan_simpTheory;

val _ = translate $ spec64 SmartSeq_def;

val _ = translate $ spec64 seq_assoc_def;

val _ = translate $ spec64 seq_call_ret_def;

val _ = translate $ conv64 ret_to_tail_def;

val _ = translate $ conv64 compile_def;

val _ = translate $ INST_TYPE[gamma|->“:64”] compile_prog_def;

open loopLangTheory;

val _ = register_type “:64 loopLang$exp”;

val _ = register_type “:64 loopLang$prog”;

val _ = translate $ spec64 acc_vars_def;

val _ = translate $ spec64 nested_seq_def;

open loop_removeTheory;

val _ = translate $ INST_TYPE[alpha|->“:64”, beta|->“:64 loopLang$prog”, gamma|->“:one$one”] store_cont_def;

val _ = translate $ spec64 comp_no_loop_def;

val _ = translate $ spec64 comp_with_loop_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 comp_prog_def;

open loop_to_wordTheory;

val _ = translate $ spec64 comp_exp_def;

val _ = translate $ spec64 find_reg_imm_def;

(* ^comp_exp, ^find_reg_imm *)
val _ = translate $ spec64 comp_def;

(* ^loopLang$acc_vars, ^comp *)
val _ = translate $ spec64 comp_func_def;

(* ^comp_func *)
val _ = translate $ spec64 compile_prog_def;

(* ^loop_remove$comp_prog, ^compile_prog *)
val _ = translate $ spec64 compile_def;

open pan_to_crepTheory;

val _ = translate $ spec64 ret_hdl_def;

val _ = translate $ INST_TYPE[alpha|->“:num”] ret_var_def;

val _ = translate $ INST_TYPE[alpha|->“:64 crepLang$exp”] cexp_heads_def;

val _ = translate $ spec64 comp_field_def;

val _ = translate $ spec64 exp_hdl_def;

val _ = register_type “:64 context”;

val _ = translate $ INST_TYPE[alpha|->“:64”, beta|->“:64”] compile_exp_def;

val _ = translate $ spec64 compile_def;

val _ = translate $ spec64 mk_ctxt_def;

(* compile, ^mk_ctxt *)
val _ = translate $ spec64 comp_func_def;

val _ = translate $ make_funcs_def;

(* ^panLang$exp_ids *)
val _ = translate $ get_eids_def;

(* comp_func, ^make_funcs, ^get_eids *)
val _ = translate $ spec64 compile_prog_def;

open loop_liveTheory;

(* aux-function: fixedpoint *)
val _ = translate $ spec64 shrink_def;

val _ = translate $ spec64 mark_all_def;

(* ^mark_all, shrink *)
val _ = translate $ spec64 comp_def;

(* comp, loop_call$comp *)
val _ = translate $ spec64 optimise_def;

open crep_to_loopTheory;

val _ = translate $ spec64 prog_if_def;

(* ^prog_if *)
val _ = translate $ spec64 compile_exp_def;

(* ^compile_exp, ^loopLang$nested_seq *)
val _ = translate $ spec64 compile_def;

(* ^compile *)
val _ = translate $ spec64 comp_func_def;

val _ = translate $ make_funcs_def;

(* ^comp_func, ^make_funcs, loop_live$optimise *)
val _ = translate $ spec64 compile_prog_def;

open pan_to_wordTheory;

(*
   ^pan_simp$compile_prog, pan_to_crep$compile_prog, crep_to_loop$compile_prog,
   ^loop_to_word$compile
*)
val _ = translate $ spec64 compile_prog_def;

open word_to_wordTheory;

(*
    word_simp$compile_exp, wordLang$max_var, word_inst$inst_select,
    word_all$remove_dead, word_inst$three_to_two_reg, word_alloc$word_alloc
*)
val _ = translate $ spec64 compile_single_def;

(* compile_single, word_remove$remove_must_terminate *)
val _ = translate $ spec64 full_compile_single_def;

(* full_compile_single *)
val _ = translate $ spec64 compile_def;

open backendTheory;

(* attach_bitmaps, lab_to_target$compile *)
val _ = translate $ INST_TYPE[alpha|->“:64 word list”, beta|->“:64”] from_lab_def;

(* stack_to_lab$compile, from_lab *)
val _ = translate $ spec64 $ INST_TYPE[beta|->“:64 word list”] from_stack_def;

(* word_to_stack$compile from_stack *)
val _ = translate $ spec64 from_word_def;

open pan_to_targetTheory;

(* pan_to_word$compile_prog, word_to_word$compile, backend$from_word *)
val _ = translate $ spec64 compile_prog_def;

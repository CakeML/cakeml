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

val EqualityType_prog = EqualityType_rule [] “:64 panLang$prog”;

open crepLangTheory;

val _ = register_type “:64 crepLang$exp”;

val _ = register_type “:64 crepLang$prog”;

open pan_simpTheory;

val _ = translate $ spec64 SmartSeq_def;

val _ = translate $ spec64 seq_assoc_def;

val _ = translate $ spec64 seq_call_ret_def;

val _ = translate $ conv64 ret_to_tail_def;

val _ = translate $ conv64 compile_def;

val _ = translate $ INST_TYPE[gamma|->“:64”] compile_prog_def;

open loop_removeTheory;

val _ = register_type “:64 loopLang$exp”;

val _ = register_type “:64 loopLang$prog”;

val EqualityType_prog = EqualityType_rule [] “:64 loopLang$prog”;

val _ = translate $ INST_TYPE[alpha|->“:64”, beta|->“:64 loopLang$prog”, gamma|->“:one$one”] store_cont_def;

val _ = translate $ spec64 comp_no_loop_def;

val _ = translate $ spec64 comp_with_loop_def;

val _ = translate $ spec64 comp_def;

val _ = translate $ spec64 comp_prog_def;

open loop_to_wordTheory;

val _ = translate $ spec64 compile_prog_def;

val _ = translate $ spec64 compile_def;

open pan_to_wordTheory;

val _ = translate $ spec64 compile_prog_def;

open pan_to_targetTheory;

val _ = translate $ spec64 compile_prog_def;

(*
  Translate the pan_to_target part of the 32-bit compiler.
*)

open preamble;
open ml_translatorLib ml_translatorTheory;
open to_target32ProgTheory std_preludeTheory;
local open backendTheory in end

val _ = new_theory "from_pancake32Prog"

val _ = translation_extends "to_target32Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_pancake32Prog");
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

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:32``,beta|->``:32``] else []

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

val spec32 = INST_TYPE[alpha|->``:32``]

val conv32 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec32 o SPEC_ALL

val conv32_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec32 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``,``foo:'a stackLang$prog``, “foo:'a pan_to_crep$context”]

open panLangTheory;

val _ = register_type “:32 panLang$exp”;

val _ = register_type “:32 panLang$prog”;

val _ = translate $ spec32 exp_ids_def;

open crepLangTheory;

val _ = register_type “:32 crepLang$exp”;

val _ = register_type “:32 crepLang$prog”;

val _ = translate $ spec32 var_cexp_def;

val _ = translate $ spec32 acc_vars_def;

val _ = translate $ spec32 nested_decs_def;

val _ = translate $ spec32 nested_seq_def;

val lem = Q.prove(‘dimindex(:32) = 32’, EVAL_TAC);

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec32 stores_def;

val _ = translate $ spec32 store_globals_def;

val _ = translate $ spec32 load_globals_def;

val _ = translate $ spec32 assign_ret_def;

val _ = translate $ SIMP_RULE std_ss [byteTheory.bytes_in_word_def,lem] $ spec32 load_shape_def;

open pan_simpTheory;

val _ = translate $ spec32 SmartSeq_def;

val _ = translate $ spec32 seq_assoc_def;

val _ = translate $ spec32 seq_call_ret_def;

val _ = translate $ conv32 ret_to_tail_def;

val _ = translate $ conv32 compile_def;

val _ = translate $ INST_TYPE[gamma|->“:32”] compile_prog_def;

open loopLangTheory;

val _ = register_type “:32 loopLang$exp”;

val _ = register_type “:32 loopLang$prog”;

val _ = translate $ spec32 acc_vars_def;

val _ = translate $ spec32 nested_seq_def;

open loop_removeTheory;

val _ = translate $ INST_TYPE[alpha|->“:32”, beta|->“:32 loopLang$prog”, gamma|->“:one$one”] store_cont_def;

val _ = translate $ spec32 comp_no_loop_def;

val _ = translate $ spec32 comp_with_loop_def;

val _ = translate $ spec32 comp_def;

val _ = translate $ spec32 comp_prog_def;

open loop_to_wordTheory;

val _ = translate $ spec32 comp_exp_def;

val _ = translate $ spec32 find_reg_imm_def;

val _ = translate $ spec32 comp_def;

val _ = translate $ spec32 comp_func_def;

val _ = translate $ spec32 compile_prog_def;

val _ = translate $ spec32 compile_def;

open pan_to_crepTheory;

val _ = translate $ spec32 ret_hdl_def;

val _ = translate $ INST_TYPE[alpha|->“:num”] ret_var_def;

val _ = translate $ INST_TYPE[alpha|->“:32 crepLang$exp”] cexp_heads_def;

val _ = translate $ spec32 comp_field_def;

val _ = translate $ spec32 exp_hdl_def;

val _ = translate $ INST_TYPE[alpha|->“:32”,
                              beta|->“:32”] compile_exp_def;

val res = translate_no_ind $ spec32 compile_def;

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ FULL_SIMP_TAC bool_ss[panLangTheory.prog_11, panLangTheory.prog_distinct]
  \\ rveq
  \\ metis_tac [])
|> update_precondition;

val _ = translate $ spec32 mk_ctxt_def;

val _ = translate $ spec32 comp_func_def;

val _ = translate $ make_funcs_def;

val _ = translate $ INST_TYPE[alpha|->“:32”,
                              beta|->“:mlstring”,
                              gamma|->“:(mlstring # shape) list”,
                              delta|->“:32”] get_eids_def;

val _ = translate $ spec32 compile_prog_def;

open loop_callTheory;

val _ = translate $ spec32 comp_def;

val loop_call_comp_side = Q.prove(
  ‘∀spt prog. (loop_call_comp_side spt prog) ⇔ T’,
  ho_match_mp_tac comp_ind
  \\ rw[]
  \\ simp[Once (fetch "-" "loop_call_comp_side_def")]
  \\ TRY (metis_tac []))
  |> update_precondition;

open loop_liveTheory;

val _ = translate $ spec32 vars_of_exp_def;

val res = translate $ spec32 shrink_def;

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ TRY (last_x_assum match_mp_tac
          \\ rpt strip_tac
          \\ fs [FORALL_PROD] \\ NO_TAC)
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD])
  |> update_precondition;

val _ = translate $ spec32 mark_all_def;

val _ = translate $ spec32 comp_def;

val _ = translate $ spec32 optimise_def;

open crep_to_loopTheory;

val _ = translate $ spec32 prog_if_def;

val _ = translate $ spec32 compile_exp_def;

val _ = translate $ spec32 compile_def;

val _ = translate $ spec32 comp_func_def;

val _ = translate $ make_funcs_def;

val _ = translate $ spec32 compile_prog_def;

open pan_to_wordTheory;

val _ = translate $ spec32 compile_prog_def;

open word_to_wordTheory;

val _ = translate $ spec32 compile_single_def;

val _ = translate $ spec32 full_compile_single_def;

val _ = translate $ spec32 compile_def;

open backendTheory;

val _ = translate $ INST_TYPE[alpha|->“:word8 list”,
                              beta|->“:word32 list”,
                              gamma|->“:32”,
                              delta|->“:32”] attach_bitmaps_def;

val _ = translate $ INST_TYPE[alpha|->“:32 word list”,
                              beta|->“:32”] from_lab_def;

val _ = translate $ SIMP_RULE std_ss [dimword_def,lem,backend_commonTheory.word_shift_def]
                  $ SIMP_RULE std_ss [data_to_wordTheory.max_heap_limit_def]
                  $ INST_TYPE[alpha|->“:32”,
                              beta|->“:32 word list”] from_stack_def;

val _ = translate $ spec32 from_word_def;

open pan_to_targetTheory;

val _ = translate $ spec32 compile_prog_def;

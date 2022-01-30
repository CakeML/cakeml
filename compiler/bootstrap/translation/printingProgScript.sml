(*
  Translate the pretty printing functions for the REPL
*)

open preamble ml_translatorLib ml_translatorTheory
     sexp_parserProgTheory std_preludeTheory printTweaksTheory

val _ = set_grammar_ancestry ["infer","misc"];

val _ = new_theory "printingProg"

val _ = translation_extends "sexp_parserProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "printingProg");

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

  val def = def |> RW (!extra_preprocessing)
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

val _ = ml_translatorLib.use_string_type true;

val r = translate typeDecToPPTheory.con_x_i_pat_def;
val r = translate addTypePPTheory.add_pp_decs_def;

Triviality OPT_MAP_I:
  ∀g ls. OPT_MMAP I (MAP g ls) = OPT_MMAP g ls
Proof
  Induct_on ‘ls’ \\ fs [listTheory.OPT_MMAP_def]
QED

val r = translate
  (addPrintValsTheory.inf_t_to_ast_t_def
   |> SIMP_RULE std_ss [Once (GSYM OPT_MAP_I)]);

val r = translate addPrintValsTheory.print_of_val_def;

val r = translate (DefnBase.one_line_ify NONE addPrintValsTheory.nsContents_def);

val r = translate
  (printTweaksTheory.add_print_features_def
   |> SIMP_RULE (srw_ss()) [inferTheory.init_infer_state_def]);

val lemma1 = prove(“printtweaks_add_print_features_side x y = T”,
  rw [fetch "-" "printtweaks_add_print_features_side_def"]
  \\ irule (inferProgTheory.infer_d_side_thm |> CONJUNCT2) \\ fs []
  \\ irule (inferPropsTheory.infer_d_wfs |> CONJUNCT2) \\ fs []
  \\ first_x_assum $ irule_at Any \\ fs [])
  |> update_precondition;

val r = translate printTweaksTheory.add_print_then_read_def;

val lemma2 = prove(“printtweaks_add_print_then_read_side x y = T”,
  rw [fetch "-" "printtweaks_add_print_then_read_side_def"]
  \\ PairCases_on ‘x’
  \\ fs [printTweaksTheory.add_print_features_def,AllCaseEqs()]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs [printTweaksTheory.add_print_features_def,AllCaseEqs()]
  \\ imp_res_tac (inferPropsTheory.infer_d_wfs |> CONJUNCT2) \\ fs []
  \\ irule (inferProgTheory.infer_d_side_thm |> CONJUNCT2) \\ fs [])
  |> update_precondition;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();

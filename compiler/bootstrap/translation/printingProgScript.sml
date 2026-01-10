(*
  Translate the pretty printing functions for the REPL
*)
Theory printingProg[no_sig_docs]
Ancestors
  infer[qualified] misc[qualified] ml_translator basis_defProg
  std_prelude printTweaks
Libs
  preamble ml_translatorLib

open preamble ml_translatorLib ml_translatorTheory
     basis_defProgTheory std_preludeTheory printTweaksTheory;

val _ = translation_extends "basis_defProg";
val _ = ml_translatorLib.use_sub_check true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "printingProg");

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

Theorem NOT_NIL_AND_LEMMA[local]:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

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

val r = translate typeDecToPPTheory.con_x_i_pat_def;
val r = translate addTypePPTheory.add_pp_decs_def;

Theorem OPT_MAP_I[local]:
  ∀g ls. OPT_MMAP I (MAP g ls) = OPT_MMAP g ls
Proof
  Induct_on ‘ls’ \\ fs [listTheory.OPT_MMAP_def]
QED

val r = translate
  (addPrintValsTheory.inf_t_to_ast_t_mono_def
   |> SIMP_RULE std_ss [Once (GSYM OPT_MAP_I)]);

val r = translate addPrintValsTheory.print_of_val_opts_def;

val r = translate (DefnBase.one_line_ify NONE addPrintValsTheory.nsContents_def);

val r = translate
  (printTweaksTheory.add_print_features_def
   |> SIMP_RULE (srw_ss()) [inferTheory.init_infer_state_def]);

(* handle many preconditions to do with inference st invariants t_wfs *)

Theorem t_wfs_inv[local] = print_features_infer_st_invs
  |> Q.GEN `P` |> Q.ISPEC `\st. t_wfs st.subst`
  |> SIMP_RULE (std_ss ++ SATISFY_ss) [inferPropsTheory.infer_d_wfs]

val lemma1 = Q.prove(`t_wfs ((SND st).subst) ==>
    printtweaks_add_err_message_side x y st`,
  rw [fetch "-" "printtweaks_add_err_message_side_def"]
  \\ fs [inferProgTheory.infer_d_side_thm])
  |> update_precondition;

val lemma2 = Q.prove(`!xs d_st. t_wfs ((SND (SND d_st)).subst) ==>
    printtweaks_add_print_from_opts_side nm xs d_st`,
  Induct
  \\ simp [Once (fetch "-" "printtweaks_add_print_from_opts_side_def")]
  \\ simp [FORALL_PROD, lemma1]
  \\ rw []
  \\ simp [inferProgTheory.infer_d_side_thm]
  \\ imp_res_tac t_wfs_inv
  \\ fs [])
  |> update_precondition;

val lemma3 = Q.prove(`!xs d_st. t_wfs ((SND (SND d_st)).subst) ==>
    printtweaks_add_prints_from_opts_side xs d_st`,
  Induct
  \\ simp [Once (fetch "-" "printtweaks_add_prints_from_opts_side_def")]
  \\ simp [FORALL_PROD, lemma2]
  \\ rw []
  \\ first_x_assum irule
  \\ qmatch_goalsub_abbrev_tac `SND (SND tup)`
  \\ PairCases_on `tup`
  \\ gvs [markerTheory.Abbrev_def, Q.ISPEC `(_, _)` EQ_SYM_EQ]
  \\ imp_res_tac t_wfs_inv
  \\ fs [])
  |> update_precondition;

val lemma4 = Q.prove(`printtweaks_add_print_features_side x y = T`,
  rw [fetch "-" "printtweaks_add_print_features_side_def"]
  \\ TRY (irule (inferProgTheory.infer_d_side_thm |> CONJUNCT2)) \\ fs []
  \\ TRY (irule lemma3) \\ fs []
  \\ TRY (irule lemma1) \\ fs []
  \\ TRY (drule_then irule (inferPropsTheory.infer_d_wfs |> CONJUNCT2)) \\ fs [])
  |> update_precondition;

val r = translate printTweaksTheory.add_print_then_read_def;

val lemma5 = prove(“printtweaks_add_print_then_read_side x y = T”,
  rw [fetch "-" "printtweaks_add_print_then_read_side_def"]
  \\ TRY (irule (inferProgTheory.infer_d_side_thm |> CONJUNCT2)) \\ fs []
  \\ imp_res_tac t_wfs_inv
  \\ fs [])
  |> update_precondition;



val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

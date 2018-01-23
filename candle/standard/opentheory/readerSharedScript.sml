(* ------------------------------------------------------------------------- *)
(* Shared OpenTheory reader translations                                     *)
(* ------------------------------------------------------------------------- *)

open preamble basis
     ml_monadBaseTheory ml_monad_translatorLib cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory
     readerProofTheory prettyTheory

val _ = new_theory "readerShared"
val _ = m_translation_extends "ml_hol_kernelProg"

(* --- Translate prettyTheory ---------------------------------------------- *)

val r = translate newline_def
val r = translate breakdist_def
val r = translate REPLICATE
val r = translate blanks_def
val r = translate printing_def
val r = translate pr_def
val r = translate tlength_def
val r = translate mk_blo_def
val r = translate mk_str_def
val r = translate mk_brk_def
val r = translate typ_def
val r = translate pp_margin_def
val r = translate ty_to_string_def
val r = translate fix_name_def
val r = translate paren_def
val r = translate term_def
val r = translate tm_to_string_def
val r = translate hyps_def
val r = translate thm_def
val r = translate thm_to_string_def

(* --- Translate readerTheory ---------------------------------------------- *)

val r = translate init_state_def
val r = translate mk_BN_def
val r = translate mk_BS_def
val r = translate insert_def
val r = translate delete_def
val r = translate lookup_def
val r = translate push_def
val r = translate insert_dict_def
val r = translate delete_dict_def
val r = translate first_def
val r = translate stringTheory.isDigit_def

val _ = (use_mem_intro := true)
val tymatch_ind = save_thm("tymatch_ind",REWRITE_RULE[GSYM rev_assocd_thm]holSyntaxExtraTheory.tymatch_ind)
val _ = add_preferred_thy"-";
val r = translate (REWRITE_RULE[GSYM rev_assocd_thm]holSyntaxExtraTheory.tymatch_def)
val _ = (use_mem_intro := false)
val r = translate OPTION_MAP_DEF
val r = translate holSyntaxExtraTheory.match_type_def

val r = m_translate find_axiom_def
val r = m_translate getNum_def
val r = m_translate getName_def
val r = m_translate getList_def
val r = m_translate getTypeOp_def
val r = m_translate getType_def
val r = m_translate getConst_def
val r = m_translate getVar_def
val r = m_translate getTerm_def
val r = m_translate getThm_def
val r = m_translate pop_def
val r = m_translate peek_def
val r = m_translate getPair_def
val r = m_translate getNvs_def
val r = m_translate getCns_def
val r = m_translate getTys_def
val r = m_translate getTms_def
val r = m_translate BETA_CONV_def

(* stack and dictionary dumping *)
val r = translate pad_def
val r = translate obj_t_def
val r = translate stack_t_def
val r = translate pair_t_def
val r = translate sptreeTheory.lrnext_def
val r = translate foldi_def
val r = translate toAList_def
val r = translate dict_t_def
val r = translate reader_state_t_def
val r = translate state_to_string_def

val r = translate i2s_def (* why is it not named s2i? *)
val r = m_translate readLine_def

val readline_side = Q.store_thm("readline_side",
  `!st1 l s. readline_side st1 l s <=> T`,
  rw [fetch "-" "readline_side_def"] \\ intLib.COOPER_TAC)
  |> update_precondition;

val r = translate fix_fun_typ_def
val r = translate current_line_def
val r = translate lines_read_def
val r = translate next_line_def
val r = translate line_Fail_def

val r = translate ind_name_def
val r = translate ind_ty_def
val r = translate select_name_def
val r = translate select_tm_def
val r = translate select_const_def
val r = translate mk_reader_ctxt_def
val r = m_translate set_reader_ctxt_def

val r = translate msg_success_def
val r = translate msg_usage_def
val r = translate msg_bad_name_def
val r = translate str_prefix_def;
val r = translate invalid_line_def;

val _ = Q.prove(
  `∀x. invalid_line_side x ⇔ T`,
  EVAL_TAC \\ rw[]) |> update_precondition;

val _ = export_theory ();


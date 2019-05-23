(*
  There are two 'frontends' to the OpenTheory reader. This theory contains
  translations of the functions which are used by both versions so that we
  do not translate more than once.
*)
open preamble basis
     ml_monadBaseTheory ml_monad_translator_interfaceLib
     cfMonadTheory cfMonadLib
     holKernelTheory holKernelProofTheory ml_hol_kernelProgTheory readerTheory
     readerProofTheory reader_initTheory prettyTheory

val _ = new_theory "reader_commonProg"
val _ = m_translation_extends "ml_hol_kernelProg"

val _ = use_full_type_names := true;

(* ------------------------------------------------------------------------- *)
(* Translate prettyTheory                                                    *)
(* ------------------------------------------------------------------------- *)

(* printer functions *)

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
val r = translate pp_margin_def

(* type printer *)

val r = translate pp_tyop_def
val r = translate pp_type_def

(* term printer *)

val r = translate fixity_of_def
val r = translate name_of_def
val r = translate is_binop_PMATCH
val r = translate is_binder_PMATCH
val r = translate is_cond_PMATCH
val r = translate is_neg_PMATCH
val r = translate collect_vars_PMATCH
val r = translate dest_binary_PMATCH
val r = translate dest_binder_PMATCH
val r = translate pp_paren_blk_def
val r = translate pp_seq_def
val r = translate interleave_def
val r = translate pp_term_def

Theorem pp_term_side = Q.prove(`
  !x y. pp_term_side x y <=> T`,
  recInduct pp_term_ind \\ rw []
  \\ rw [Once (fetch "-" "pp_term_side_def")]
  \\ TRY strip_tac \\ rw []
  \\ fs [is_binop_def, is_binder_def, is_cond_def])
  |> update_precondition;

(* theorem printer *)

val r = translate pp_thm_def

val r = translate term2str_def
val r = translate thm2str_def

(* ------------------------------------------------------------------------- *)
(* Translate readerTheory                                                    *)
(* ------------------------------------------------------------------------- *)

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

(* TODO This could be done in the Kernel module *)

val _ = (use_mem_intro := true)
val tymatch_ind = save_thm ("tymatch_ind",
  REWRITE_RULE [GSYM rev_assocd_thm] holSyntaxExtraTheory.tymatch_ind)
val _ = add_preferred_thy"-";
val r = holSyntaxExtraTheory.tymatch_def
        |> REWRITE_RULE [GSYM rev_assocd_thm]
        |> translate
val _ = (use_mem_intro := false)
val r = translate OPTION_MAP_DEF
val r = translate holSyntaxExtraTheory.match_type_def

val r = m_translate find_axiom_def
val r = m_translate getNum_PMATCH
val r = m_translate getName_PMATCH
val r = m_translate getList_PMATCH
val r = m_translate getTypeOp_PMATCH
val r = m_translate getType_PMATCH
val r = m_translate getConst_PMATCH
val r = m_translate getVar_PMATCH
val r = m_translate getTerm_PMATCH
val r = m_translate getThm_PMATCH
val r = m_translate pop_def
val r = m_translate peek_def
val r = m_translate getPair_PMATCH
val r = m_translate getNvs_def
val r = m_translate getCns_def
val r = m_translate getTys_def
val r = m_translate getTms_def
val r = m_translate BETA_CONV_def

(* stack and dictionary dumping *)
val r = translate commas_def
val r = translate listof_def
val r = translate obj_t_def
val r = translate sptreeTheory.lrnext_def
val r = translate foldi_def
val r = translate toAList_def
val r = translate obj_to_string_def
val r = translate state_to_string_def

val r = translate s2i_def
val r = m_translate readLine_def

Theorem readline_side = Q.prove(`
  !st1 l s. readline_side st1 l s <=> T`,
  rw [fetch "-" "readline_side_def"] \\ intLib.COOPER_TAC)
  |> update_precondition;

val readline_spec = save_thm ("readline_spec",
  mk_app_of_ArrowP (theorem "readline_v_thm"));

val r = translate unescape_PMATCH
val r = translate unescape_ml_def
val r = translate fix_fun_typ_def
val r = translate current_line_def
val r = translate lines_read_def
val r = translate next_line_def
val r = translate line_Fail_def

(* ------------------------------------------------------------------------- *)
(* Translate reader_initTheory                                               *)
(* ------------------------------------------------------------------------- *)

val r = m_translate mk_true_def
val r = m_translate mk_univ_def
val r = m_translate mk_forall_def
val r = m_translate mk_eta_ax_def
val r = translate select_const_def
val r = m_translate mk_conj_const_def
val r = m_translate mk_conj_def
val r = m_translate mk_imp_const_def
val r = m_translate mk_imp_def
val r = m_translate mk_select_ax_def
val r = m_translate mk_ex_def
val r = m_translate mk_exists_def
val r = m_translate mk_surj_def
val r = m_translate mk_inj_def
val r = m_translate mk_false_def
val r = m_translate mk_neg_const_def
val r = m_translate mk_neg_def
val r = m_translate mk_infinity_ax_def
val r = translate select_sym_def
val r = translate ind_type_def
val r = m_translate init_reader_def

val init_reader_spec = save_thm ("init_reader_spec",
  mk_app_of_ArrowP (theorem "init_reader_v_thm"));

val r = translate pp_namepair_def
val r = translate pp_update_def
val r = translate upd2str_def

val r = translate msg_success_def
val r = translate msg_usage_def
val r = translate msg_bad_name_def
val r = translate msg_axioms_def
val r = translate str_prefix_def
val r = translate invalid_line_def

val _ = Q.prove (
  `∀x. invalid_line_side x ⇔ T`,
  EVAL_TAC \\ rw [])
  |> update_precondition;

(* ------------------------------------------------------------------------- *)
(* Things needed by whole_prog_spec                                          *)
(* ------------------------------------------------------------------------- *)

Theorem HOL_STORE_init_precond:
   HOL_STORE init_refs
   {Mem (1+(LENGTH(delta_refs++empty_refs++ratio_refs++stdin_refs++stdout_refs
                             ++stderr_refs++init_type_constants_refs)))
        (Refv init_type_constants_v);
    Mem (2+(LENGTH(delta_refs++empty_refs++ratio_refs++stdin_refs++stdout_refs
                             ++stderr_refs++init_type_constants_refs
                             ++init_term_constants_refs)))
        (Refv init_term_constants_v);
    Mem (3+(LENGTH(delta_refs++empty_refs++ratio_refs++stdin_refs++stdout_refs
                             ++stderr_refs++init_type_constants_refs
                             ++init_term_constants_refs++init_axioms_refs)))
        (Refv init_axioms_v);
    Mem (4+(LENGTH(delta_refs++empty_refs++ratio_refs++stdin_refs++stdout_refs
                             ++stderr_refs++init_type_constants_refs
                             ++init_term_constants_refs++init_axioms_refs
                             ++init_context_refs)))
        (Refv init_context_v)}
Proof
  qmatch_goalsub_abbrev_tac`1 + l1`
  \\ qmatch_goalsub_abbrev_tac`2 + l2`
  \\ qmatch_goalsub_abbrev_tac`3 + l3`
  \\ qmatch_goalsub_abbrev_tac`4 + l4`
  \\ rw[HOL_STORE_def,ml_monad_translatorBaseTheory.REF_REL_def,init_refs_def]
  \\ rw[STAR_def,SEP_EXISTS_THM]
  \\ qmatch_goalsub_abbrev_tac`Mem (l1+1) v1`
  \\ qmatch_goalsub_abbrev_tac`Mem (l2+2) v2`
  \\ qmatch_goalsub_abbrev_tac`Mem (l3+3) v3`
  \\ qmatch_goalsub_abbrev_tac`Mem (l4+4) v4`
  \\ qexists_tac`{Mem(l1+1)v1;Mem(l2+2)v2;Mem(l3+3)v3}`
  \\ qexists_tac`{Mem(l4+4)v4}`
  \\ `l1+1 < l2+2` by simp[Abbr`l1`,Abbr`l2`]
  \\ `l2+2 < l3+3` by simp[Abbr`l2`,Abbr`l3`]
  \\ `l3+3 < l4+4` by simp[Abbr`l3`,Abbr`l4`]
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,the_context_def,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_context_v`
    \\ simp[init_context_v_thm]
    \\ unabbrev_all_tac
    \\ SPLIT_TAC )
  \\ qexists_tac`{Mem(l1+1)v1;Mem(l2+2)v2}`
  \\ qexists_tac`{Mem(l3+3)v3}`
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,the_axioms_def,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_axioms_v`
    \\ simp[init_axioms_v_thm]
    \\ unabbrev_all_tac
    \\ SPLIT_TAC )
  \\ qexists_tac`{Mem(l1+1)v1}`
  \\ qexists_tac`{Mem(l2+2)v2}`
  \\ conj_tac >- SPLIT_TAC
  \\ reverse conj_tac
  >- (
    rw[REF_def,SEP_EXISTS_THM,the_term_constants_def,cond_STAR,
       ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
    \\ rw[cond_def]
    \\ qexists_tac`init_term_constants_v`
    \\ simp[init_term_constants_v_thm]
    \\ unabbrev_all_tac
    \\ SPLIT_TAC ) \\
  rw[REF_def,SEP_EXISTS_THM,the_type_constants_def,cond_STAR,
     ml_monad_translatorBaseTheory.CELL_HPROP_SAT_EQ,ADD1]
  \\ rw[cond_def]
  \\ qexists_tac`init_type_constants_v`
  \\ simp[init_type_constants_v_thm]
  \\ unabbrev_all_tac
  \\ SPLIT_TAC
QED

(* ------------------------------------------------------------------------- *)
(* Generate app theorem for 'context'.                                       *)
(* Should really be in ml_hol_kernelProgTheory.                              *)
(* ------------------------------------------------------------------------- *)

val context_spec = save_thm ("context_spec",
  mk_app_of_ArrowP (fetch "ml_hol_kernelProg" "context_v_thm"));

val _ = export_theory ();

(*
  There are two 'frontends' to the OpenTheory reader. This theory contains
  translations of the functions which are used by both versions so that we
  do not translate more than once.
*)
Theory reader_commonProg
Ancestors
  ml_monadBase cfMonad holKernel holKernelProof
  ml_hol_kernel_funsProg ml_hol_kernelProg reader readerProof
  reader_init pretty
Libs
  preamble basis ml_monad_translator_interfaceLib cfMonadLib

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

val _ = m_translation_extends "ml_hol_kernelProg"

val _ = use_full_type_names := true;

(* ------------------------------------------------------------------------- *)
(* Translate prettyTheory                                                    *)
(* ------------------------------------------------------------------------- *)

(* printer functions *)

val r = translate newline_def;
val r = translate breakdist_def;
val r = translate REPLICATE;
val r = translate (blanks_def |> REWRITE_RULE [GSYM sub_check_def]);
val r = translate SmartAppend_def;
val r = translate (print_list_def |> REWRITE_RULE [GSYM sub_check_def]);

Triviality print_list_ind:
  print_list_ind
Proof
  once_rewrite_tac [fetch "-" "print_list_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD,sub_check_def]
QED

val _ = print_list_ind |> update_precondition;

val r = translate pr_def;
val r = translate tlength_def;
val r = translate mk_blo_def;
val r = translate mk_str_def;
val r = translate mk_brk_def;
val r = translate pp_margin_def;

(* type printer *)

val r = translate pp_tyop_aux_def;
val r = translate pp_with_sep_def;
val r = translate pp_type_def;

(* term printer *)

val r = translate fixity_of_def;
val r = translate name_of_def;
val r = translate is_binop_PMATCH;
val r = translate is_binder_PMATCH;
val r = translate is_cond_PMATCH;
val r = translate is_neg_PMATCH;
val r = translate collect_vars_PMATCH;
val r = translate dest_binary_PMATCH;
val r = translate dest_binder_PMATCH;
val r = translate pp_paren_blk_def;
val r = translate pp_seq_def;
val r = translate interleave_def;
val r = translate pp_term_def;

Theorem pp_term_side[local]:
  ∀x y. pp_term_side x y
Proof
  recInduct pp_term_ind \\ rw []
  \\ rw [Once (fetch "-" "pp_term_side_def")]
  \\ TRY strip_tac \\ rw []
  \\ fs [is_binop_def, is_binder_def, is_cond_def]
QED

val _ = update_precondition pp_term_side;

(* theorem printer *)

val r = translate pp_thm_def;

val r = translate term2str_applist_def;
val r = translate thm2str_applist_def;

(* ------------------------------------------------------------------------- *)
(* Translate readerTheory                                                    *)
(* ------------------------------------------------------------------------- *)

val r = translate init_state_def;
val r = translate mk_BN_def;
val r = translate mk_BS_def;
val r = translate insert_def;
val r = translate delete_def;
val r = translate lookup_def;
val r = translate push_def;
val r = translate insert_dict_def;
val r = translate delete_dict_def;
val r = translate first_def;
val r = translate stringTheory.isDigit_def;

(* TODO This could be done in the Kernel module *)

val _ = (use_mem_intro := true);
val _ = translate rev_assocd_def
Theorem tymatch_ind =
  REWRITE_RULE [GSYM rev_assocd_thm] holSyntaxExtraTheory.tymatch_ind
val _ = add_preferred_thy"-";
val r = holSyntaxExtraTheory.tymatch_def
        |> REWRITE_RULE [GSYM rev_assocd_thm]
        |> translate;
val _ = (use_mem_intro := false);
val r = translate OPTION_MAP_DEF;
val r = translate FOLDL;
val r = translate holSyntaxExtraTheory.match_type_def;

val r = m_translate find_axiom_def;
val r = m_translate getNum_PMATCH;
val r = m_translate getName_PMATCH;
val r = m_translate getList_PMATCH;
val r = m_translate getTypeOp_PMATCH;
val r = m_translate getType_PMATCH;
val r = m_translate getConst_PMATCH;
val r = m_translate getVar_PMATCH;
val r = m_translate getTerm_PMATCH;
val r = m_translate getThm_PMATCH;
val r = m_translate pop_def;
val r = m_translate peek_def;
val r = m_translate getPair_PMATCH;
val r = m_translate getNvs_def;
val r = m_translate getCns_def;
val r = m_translate getTys_def;
val r = m_translate getTms_def;
val r = m_translate BETA_CONV_def;

(* stack and dictionary dumping *)
val r = translate commas_def;
val r = translate listof_def;
val r = translate obj_t_def;
val r = translate sptreeTheory.lrnext_def;
val r = translate foldi_def;
val r = translate toAList_def;
val r = translate obj2str_applist_def;
val r = translate st2str_applist_def;

val r = m_translate holKernelTheory.map_def;
val r = m_translate readLine_def;

Theorem readline_side[local]:
  ∀st1 l s. readline_side st1 l s
Proof
  rw [fetch "-" "readline_side_def"]
  \\ intLib.COOPER_TAC
QED

val _ = update_precondition readline_side;

Theorem readline_spec = mk_app_of_ArrowP (theorem "readline_v_thm");

val r = translate unescape_PMATCH;
val r = translate unescape_ml_def;
val r = translate fix_fun_typ_def;
val r = translate current_line_def;
val r = translate lines_read_def;
val r = translate next_line_def;
val r = translate line_Fail_def;
val r = translate strh_aux_def;

val r = translate strh_def;
val r = translate (s2c_def |> REWRITE_RULE [GSYM sub_check_def]);

Theorem s2c_side[local]:
  ∀s. s2c_side s
Proof
  namedCases ["x"]
  \\ rw [fetch "-" "s2c_side_def"]
  \\ Cases_on ‘x’ \\ fs [sub_check_def]
QED
val _ = update_precondition s2c_side;

val r = translate (str_prefix_def |> REWRITE_RULE [GSYM sub_check_def]);

val r = translate tokenize_def;

val r = m_translate readLines_def;

Theorem readLines_spec = mk_app_of_ArrowP (theorem "readlines_v_thm");

(* ------------------------------------------------------------------------- *)
(* Translate reader_initTheory                                               *)
(* ------------------------------------------------------------------------- *)

val r = m_translate mk_true_def;
val r = m_translate mk_univ_def;
val r = m_translate mk_forall_def;
val r = m_translate mk_eta_ax_def;
val r = translate select_const_def;
val r = m_translate mk_conj_const_def;
val r = m_translate mk_conj_def;
val r = m_translate mk_imp_const_def;
val r = m_translate mk_imp_def;
val r = m_translate mk_select_ax_def;
val r = m_translate mk_ex_def;
val r = m_translate mk_exists_def;
val r = m_translate mk_surj_def;
val r = m_translate mk_inj_def;
val r = m_translate mk_false_def;
val r = m_translate mk_neg_const_def;
val r = m_translate mk_neg_def;
val r = m_translate mk_infinity_ax_def;
val r = translate select_sym_def;
val r = translate ind_type_def;
val r = m_translate init_reader_def;

Theorem init_reader_spec = mk_app_of_ArrowP (theorem "init_reader_v_thm");

val r = translate pp_namepair_def;
val r = translate pp_update_def;
val r = translate upd2str_applist_def;

val r = translate msg_success_def;
val r = translate msg_usage_def;
val r = translate msg_bad_name_def;

(* ------------------------------------------------------------------------- *)
(* Things needed by whole_prog_spec                                          *)
(* ------------------------------------------------------------------------- *)

val st = get_state (get_ml_prog_state ())
val refs = EVAL ``(^st).refs`` |> concl |> rhs |> listSyntax.strip_append;
val t = `` init_type_constants_v``;
fun prior_length t = let
    val refv_t = mk_Refv t
    val n = index (can (find_term (term_eq refv_t))) refs
    val xs = List.take (refs, n)
    val ns = mapfilter (length o fst o listSyntax.dest_list) xs
    val ys = filter (not o can (listSyntax.dest_list)) xs
      |> listSyntax.list_mk_append
  in numSyntax.mk_plus (numSyntax.term_of_int (sum ns), listSyntax.mk_length ys) end

Theorem HOL_STORE_init_precond:
   HOL_STORE init_refs
   {Mem (^(prior_length ``init_type_constants_v``))
        (Refv init_type_constants_v);
    Mem (^(prior_length ``init_term_constants_v``))
        (Refv init_term_constants_v);
    Mem (^(prior_length ``init_axioms_v``))
        (Refv init_axioms_v);
    Mem (^(prior_length ``init_context_v``))
        (Refv init_context_v)}
Proof
  qmatch_goalsub_abbrev_tac`2 + l1`
  \\ qmatch_goalsub_abbrev_tac`3 + l2`
  \\ qmatch_goalsub_abbrev_tac`4 + l3`
  \\ qmatch_goalsub_abbrev_tac`5 + l4`
  \\ rw[HOL_STORE_def,ml_monad_translatorBaseTheory.REF_REL_def,init_refs_def]
  \\ rw[STAR_def,SEP_EXISTS_THM]
  \\ qmatch_goalsub_abbrev_tac`Mem (l1+2) v1`
  \\ qmatch_goalsub_abbrev_tac`Mem (l2+3) v2`
  \\ qmatch_goalsub_abbrev_tac`Mem (l3+4) v3`
  \\ qmatch_goalsub_abbrev_tac`Mem (l4+5) v4`
  \\ qexists_tac`{Mem(l1+2)v1;Mem(l2+3)v2;Mem(l3+4)v3}`
  \\ qexists_tac`{Mem(l4+5)v4}`
  \\ `l1+2 < l2+3` by simp[Abbr`l1`,Abbr`l2`]
  \\ `l2+3 < l3+4` by simp[Abbr`l2`,Abbr`l3`]
  \\ `l3+4 < l4+5` by simp[Abbr`l3`,Abbr`l4`]
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
  \\ qexists_tac`{Mem(l1+2)v1;Mem(l2+3)v2}`
  \\ qexists_tac`{Mem(l3+4)v3}`
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
  \\ qexists_tac`{Mem(l1+2)v1}`
  \\ qexists_tac`{Mem(l2+3)v2}`
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

Theorem context_spec =
  mk_app_of_ArrowP (fetch "ml_hol_kernelProg" "context_v_thm");


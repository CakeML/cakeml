(*
  Prove perms theorems for kernel functions
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory sptreeTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory
     candle_kernel_valsTheory candle_kernelProgTheory;
open permsTheory ml_hol_kernel_funsProgTheory ml_progLib ast_extrasTheory;

val _ = new_theory "candle_kernel_perms";

val _ = set_grammar_ancestry ["candle_kernel_vals", "perms", "misc"];

val eval_nsLookup_tac =
  rewrite_tac [ml_progTheory.nsLookup_merge_env]
  \\ CONV_TAC(DEPTH_CONV ml_progLib.nsLookup_conv)

(* Functions translated with 'translate' should be proved for any ps *)

Theorem perms_ok_word8_fromint_v[simp]:
  perms_ok ps word8_fromint_v
Proof
  rw[perms_ok_def, Word8ProgTheory.word8_fromint_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_fst_v[simp]:
  perms_ok ps fst_v
Proof
  rw[perms_ok_def, std_preludeTheory.fst_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_snd_v[simp]:
  perms_ok ps snd_v
Proof
  rw[perms_ok_def, std_preludeTheory.snd_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_exists_v[simp]:
  perms_ok ps ListProg$exists_v
Proof
  rw[perms_ok_def, ListProgTheory.exists_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_length_aux_v[simp]:
  perms_ok ps ListProg$length_aux_v
Proof
  rw[perms_ok_def, ListProgTheory.length_aux_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_length_v[simp]:
  perms_ok ps ListProg$length_v
Proof
  rw[perms_ok_def, ListProgTheory.length_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ EVAL_TAC \\ rw[]
QED

Theorem perms_ok_map_1_v[simp]:
  perms_ok ps ListProg$map_1_v
Proof
  rw[perms_ok_def, ListProgTheory.map_1_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_member_v[simp]:
  perms_ok ps ListProg$member_v
Proof
  rw[perms_ok_def, ListProgTheory.member_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_filter_v[simp]:
  perms_ok ps ListProg$filter_v
Proof
  rw[perms_ok_def, ListProgTheory.filter_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_every_v[simp]:
  perms_ok ps ListProg$every_v
Proof
  rw[perms_ok_def, ListProgTheory.every_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_qsort_part_v[simp]:
  perms_ok ps ListProg$qsort_part_v
Proof
  rw[perms_ok_def, ListProgTheory.qsort_part_v_def, astTheory.pat_bindings_def,
     perms_ok_env_def]
QED

Theorem perms_ok_qsort_acc_v[simp]:
  perms_ok ps ListProg$qsort_acc_v
Proof
  rw[perms_ok_def, ListProgTheory.qsort_acc_v_def, astTheory.pat_bindings_def,perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_qsort_v[simp]:
  perms_ok ps ListProg$qsort_v
Proof
  rw[perms_ok_def, ListProgTheory.qsort_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_strcat_v[simp]:
  perms_ok ps strcat_v
Proof
  rw[perms_ok_def, StringProgTheory.strcat_v_def, perms_ok_env_def]
QED

Theorem perms_ok_string_lt_v[simp]:
  perms_ok ps string_lt_v
Proof
  rw[perms_ok_def, string_lt_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_string_le_v[simp]:
  perms_ok ps string_le_v
Proof
  rw[perms_ok_def, string_le_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_mmap_1_v[simp]:
  perms_ok ps ml_hol_kernel_funsProg$map_1_v
Proof
  rw[perms_ok_def, map_1_v_def, perms_ok_env_def, astTheory.pat_bindings_def]
QED

Theorem perms_ok_check_tm_v[simp]:
  perms_ok ps check_tm_v
Proof
  rw[perms_ok_def, check_tm_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_check_tm_tm_v[simp]:
  perms_ok ps check_tm_tm_v
Proof
  rw[perms_ok_def, check_tm_tm_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_check_ty_ty_v[simp]:
  perms_ok ps check_ty_ty_v
Proof
  rw[perms_ok_def, check_ty_ty_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_vfree_in_v[simp]:
  perms_ok ps vfree_in_v
Proof
  rw[perms_ok_def, vfree_in_v_def, astTheory.pat_bindings_def,perms_ok_env_def]
QED

Theorem perms_ok_call_vfree_in_v[simp]:
  perms_ok ps call_vfree_in_v
Proof
  rw[perms_ok_def, call_vfree_in_v_def, astTheory.pat_bindings_def,perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_variant_v[simp]:
  perms_ok ps variant_v
Proof
  rw[perms_ok_def, variant_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_call_variant_v[simp]:
  ∀ps. perms_ok ps call_variant_v
Proof
  rw[perms_ok_def, call_variant_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_concl_v[simp]:
  ∀ps. perms_ok ps concl_v
Proof
  rw[perms_ok_def, concl_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_assoc_v[simp]:
  perms_ok ps assoc_v
Proof
  rw[perms_ok_def, assoc_v_def, perms_ok_env_def, astTheory.pat_bindings_def]
QED

Theorem perms_ok_alphavars_v[simp]:
  perms_ok ps alphavars_v
Proof
  rw[perms_ok_def, alphavars_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_raconv_v[simp]:
  perms_ok ps raconv_v
Proof
  rw[perms_ok_def, raconv_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_aconv_v[simp]:
  perms_ok ps aconv_v
Proof
  rw[perms_ok_def, aconv_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_try_v[simp]:
  perms_ok ps try_v
Proof
  rw[perms_ok_def, try_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_o_1_v[simp]:
  perms_ok ps o_1_v
Proof
  rw[perms_ok_def, std_preludeTheory.o_1_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_dest_vartype_v[simp]:
  perms_ok ps dest_vartype_v
Proof
  rw[perms_ok_def, dest_vartype_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_dest_type_v[simp]:
  perms_ok ps dest_type_v
Proof
  rw[perms_ok_def, dest_type_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_is_type_v[simp]:
  perms_ok ps is_type_v
Proof
  rw[perms_ok_def, is_type_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_is_vartype_v[simp]:
  perms_ok ps is_vartype_v
Proof
  rw[perms_ok_def, is_vartype_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_check_ty_v[simp]:
  perms_ok ps check_ty_v
Proof
  rw[perms_ok_def, check_ty_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_rev_assocd_v[simp]:
  perms_ok ps rev_assocd_v
Proof
  rw[perms_ok_def, rev_assocd_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_type_subst_v[simp]:
  perms_ok ps type_subst_v
Proof
  rw[perms_ok_def, type_subst_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_call_type_subst_v[simp]:
  perms_ok ps call_type_subst_v
Proof
  rw[perms_ok_def, call_type_subst_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_itlist_v[simp]:
  perms_ok ps itlist_v
Proof
  rw[perms_ok_def, itlist_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_insert_1_v[simp]:
  perms_ok ps insert_1_v
Proof
  rw[perms_ok_def, insert_1_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_union_1_v[simp]:
  perms_ok ps union_1_v
Proof
  rw[perms_ok_def, union_1_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_subtract_v[simp]:
  perms_ok ps subtract_v
Proof
  rw[perms_ok_def, subtract_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_forall_v[simp]:
  perms_ok ps forall_v
Proof
  rw[perms_ok_def, forall_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_tyvars_v[simp]:
  ∀ps. perms_ok ps tyvars_v
Proof
  rw[perms_ok_def, tyvars_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_call_tyvars_v[simp]:
  ∀ps. perms_ok ps call_tyvars_v
Proof
  rw[perms_ok_def, call_tyvars_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_frees_v[simp]:
  perms_ok ps frees_v
Proof
  rw[perms_ok_def, frees_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_call_frees_v[simp]:
  perms_ok ps call_frees_v
Proof
  rw[perms_ok_def, call_frees_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_freesl_v[simp]:
  perms_ok ps freesl_v
Proof
  rw[perms_ok_def, freesl_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ CONV_TAC(DEPTH_CONV ml_progLib.nsLookup_conv)
  \\ rw[]
QED

Theorem perms_ok_freesin_v[simp]:
  perms_ok ps freesin_v
Proof
  rw[perms_ok_def, freesin_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_call_freesin_v[simp]:
  perms_ok ps call_freesin_v
Proof
  rw[perms_ok_def, call_freesin_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_type_vars_in_term_v[simp]:
  perms_ok ps type_vars_in_term_v
Proof
  rw[perms_ok_def, type_vars_in_term_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_call_type_vars_in_term_v[simp]:
  perms_ok ps call_type_vars_in_term_v
Proof
  rw[perms_ok_def, call_type_vars_in_term_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_dest_var_v[simp]:
  perms_ok ps dest_var_v
Proof
  rw[perms_ok_def, dest_var_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_dest_const_v[simp]:
  perms_ok ps dest_const_v
Proof
  rw[perms_ok_def, dest_const_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_dest_comb_v[simp]:
  perms_ok ps dest_comb_v
Proof
  rw[perms_ok_def, dest_comb_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_dest_abs_v[simp]:
  perms_ok ps dest_abs_v
Proof
  rw[perms_ok_def, dest_abs_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_dest_thm_v[simp]:
  perms_ok ps dest_thm_v
Proof
  rw[perms_ok_def, dest_thm_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_hyp_v[simp]:
  perms_ok ps hyp_v
Proof
  rw[perms_ok_def, hyp_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_rand_v[simp]:
  perms_ok ps rand_v
Proof
  rw[perms_ok_def, rand_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_rator_v[simp]:
  perms_ok ps rator_v
Proof
  rw[perms_ok_def, rator_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_dest_eq_v[simp]:
  perms_ok ps dest_eq_v
Proof
  rw[perms_ok_def, dest_eq_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_is_var_v[simp]:
  perms_ok ps is_var_v
Proof
  rw[perms_ok_def, is_var_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_is_const_v[simp]:
  perms_ok ps is_const_v
Proof
  rw[perms_ok_def, is_const_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_is_comb_v[simp]:
  perms_ok ps is_comb_v
Proof
  rw[perms_ok_def, is_comb_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_is_abs_v[simp]:
  perms_ok ps is_abs_v
Proof
  rw[perms_ok_def, is_abs_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_vsubst_aux_v[simp]:
  perms_ok ps vsubst_aux_v
Proof
  rw[perms_ok_def, vsubst_aux_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_inst_aux_v[simp]:
  perms_ok ps inst_aux_v
Proof
  rw[perms_ok_def, inst_aux_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_inst_v[simp]:
  perms_ok ps inst_v
Proof
  rw[perms_ok_def, inst_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_mk_vartype_v[simp]:
  perms_ok ps mk_vartype_v
Proof
  rw[perms_ok_def, mk_vartype_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_mk_var_v[simp]:
  perms_ok ps mk_var_v
Proof
  rw[perms_ok_def, mk_var_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_mk_abs_v[simp]:
  perms_ok ps mk_abs_v
Proof
  rw[perms_ok_def, mk_abs_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_compare_aux_v[simp]:
  perms_ok ps compare_aux_v
Proof
  rw[perms_ok_def, StringProgTheory.compare_aux_v_def, perms_ok_env_def]
QED

Theorem perms_ok_compare_1_v[simp]:
  perms_ok ps StringProg$compare_1_v
Proof
  rw[perms_ok_def, StringProgTheory.compare_1_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ EVAL_TAC \\ rw[]
QED

Theorem perms_ok_type_cmp_v[simp]:
  perms_ok ps type_cmp_v
Proof
  rw[perms_ok_def, type_cmp_v_def, astTheory.pat_bindings_def, perms_ok_env_def] \\ fs[] \\ rw[]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_term_cmp_v[simp]:
  perms_ok ps term_cmp_v
Proof
  rw[perms_ok_def, term_cmp_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_ordav_v[simp]:
  perms_ok ps ordav_v
Proof
  rw[perms_ok_def, ordav_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_codomain_v[simp]:
  perms_ok ps codomain_v
Proof
  rw[perms_ok_def, codomain_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_typeof_v[simp]:
  perms_ok ps typeof_v
Proof
  rw[perms_ok_def, typeof_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_orda_v[simp]:
  perms_ok ps orda_v
Proof
  rw[perms_ok_def, orda_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_term_union_v[simp]:
  perms_ok ps term_union_v
Proof
  rw[perms_ok_def, term_union_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_image_v[simp]:
  perms_ok ps image_v
Proof
  rw[perms_ok_def, image_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_eq_mp_v[simp]:
  perms_ok ps eq_mp_v
Proof
  rw[perms_ok_def, eq_mp_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_inst_type_v[simp]:
  perms_ok ps inst_type_v
Proof
  rw[perms_ok_def, inst_type_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_term_remove_v[simp]:
  perms_ok ps term_remove_v
Proof
  rw[perms_ok_def, term_remove_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_can_v[simp]:
  perms_ok ps can_v
Proof
  rw[perms_ok_def, can_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
QED

Theorem perms_ok_subset_v[simp]:
  perms_ok ps subset_v
Proof
  rw[perms_ok_def, subset_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_dropwhile_v[simp]:
  perms_ok ps dropwhile_v
Proof
  rw[perms_ok_def, dropwhile_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_flatten_v[simp]:
  perms_ok ps flatten_v
Proof
  rw[perms_ok_def, flatten_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_get_size_v[simp]:
  perms_ok ps get_size_v
Proof
  rw[perms_ok_def, get_size_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_get_next_size_v[simp]:
  perms_ok ps get_next_size_v
Proof
  rw[perms_ok_def, get_next_size_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_remove_all_v[simp]:
  perms_ok ps remove_all_v
Proof
  rw[perms_ok_def, remove_all_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_smart_remove_v[simp]:
  perms_ok ps smart_remove_v
Proof
  rw[perms_ok_def, smart_remove_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_annotate_v[simp]:
  perms_ok ps annotate_v
Proof
  rw[perms_ok_def, annotate_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_exp_1_v[simp]:
  perms_ok ps exp_1_v
Proof
  rw[perms_ok_def, std_preludeTheory.exp_1_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
  \\ rw[perms_ok_def, std_preludeTheory.exp_aux_v_def,
        astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_name_v[simp]:
  perms_ok ps name_v
Proof
  rw[perms_ok_def, name_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_name2str_v[simp]:
  perms_ok ps name2str_v
Proof
  rw[perms_ok_def, name2str_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
  \\ rw[perms_ok_def, ascii_name_v_def, astTheory.pat_bindings_def, perms_ok_env_def,
        ListProgTheory.hd_v_def,num2str_v_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
  \\ rw[ListProgTheory.hd_v_def,perms_ok_def,
        num2ascii_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_dest_quote_v[simp]:
  perms_ok ps dest_quote_v
Proof
  rw[perms_ok_def, dest_quote_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_dest_list_v[simp]:
  perms_ok ps dest_list_v
Proof
  rw[perms_ok_def, dest_list_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_newlines_v[simp]:
  perms_ok ps newlines_v
Proof
  rw[perms_ok_def, newlines_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_v2pretty_v[simp]:
  perms_ok ps v2pretty_v
Proof
  rw[perms_ok_def, v2pretty_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_v2str_v[simp]:
  perms_ok ps v2str_v
Proof
  rw[perms_ok_def, v2str_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_is_comment_v[simp]:
  perms_ok ps is_comment_v
Proof
  rw[perms_ok_def, is_comment_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_vs2str_v[simp]:
  perms_ok ps vs2str_v
Proof
  rw[perms_ok_def, vs2str_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_list_v[simp]:
  perms_ok ps list_v
Proof
  rw[perms_ok_def, list_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_nil_list_v[simp]:
  perms_ok ps nil_list_v
Proof
  rw[perms_ok_def, nil_list_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_null_v[simp]:
  perms_ok ps ListProg$null_v
Proof
  rw[perms_ok_def, ListProgTheory.null_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_str_to_v_v[simp]:
  perms_ok ps str_to_v_v
Proof
  rw[perms_ok_def, str_to_v_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_ty_to_v_v[simp]:
  perms_ok ps ty_to_v_v
Proof
  rw[perms_ok_def, ty_to_v_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_term_to_v_v[simp]:
  perms_ok ps term_to_v_v
Proof
  rw[perms_ok_def, term_to_v_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_thm_to_v_v[simp]:
  perms_ok ps thm_to_v_v
Proof
  rw[perms_ok_def, thm_to_v_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_update_to_v_v[simp]:
  perms_ok ps update_to_v_v
Proof
  rw[perms_ok_def, update_to_v_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

Theorem perms_ok_thm_to_string_v[simp]:
  perms_ok ps thm_to_string_v
Proof
  rw[perms_ok_def, thm_to_string_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw [] \\ fs []
QED

(* Functions translated with 'm_translate' should be proved for kernel_perms *)

Theorem perms_ok_the_type_constants[simp]:
  perms_ok kernel_perms the_type_constants
Proof
  rw[perms_ok_def, the_type_constants_def]
  \\ rw[kernel_perms_def, kernel_locs_def, the_type_constants_def]
QED

Theorem perms_ok_the_term_constants[simp]:
  perms_ok kernel_perms the_term_constants
Proof
  rw[perms_ok_def, the_term_constants_def]
  \\ rw[kernel_perms_def, kernel_locs_def, the_term_constants_def]
QED

Theorem perms_ok_the_axioms[simp]:
  perms_ok kernel_perms the_axioms
Proof
  rw[perms_ok_def, the_axioms_def]
  \\ rw[kernel_perms_def, kernel_locs_def, the_axioms_def]
QED

Theorem perms_ok_constants_v[simp]:
  perms_ok kernel_perms constants_v
Proof
  rw[perms_ok_def, constants_v_def, astTheory.pat_bindings_def]
  \\ rw[perms_ok_env_def] \\ pop_assum mp_tac
  \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_types_v[simp]:
  perms_ok kernel_perms types_v
Proof
  rw[perms_ok_def, types_v_def, astTheory.pat_bindings_def]
  \\ rw[perms_ok_env_def] \\ pop_assum mp_tac
  \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_axioms_v[simp]:
  perms_ok kernel_perms axioms_v
Proof
  rw[perms_ok_def, axioms_v_def, astTheory.pat_bindings_def]
  \\ rw[perms_ok_env_def] \\ pop_assum mp_tac
  \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_get_type_arity_v[simp]:
  perms_ok kernel_perms get_type_arity_v
Proof
  rw[perms_ok_def, get_type_arity_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac
  \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_mk_type_v[simp]:
  perms_ok kernel_perms mk_type_v
Proof
  rw[perms_ok_def, mk_type_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_mk_fun_ty_v[simp]:
  perms_ok kernel_perms mk_fun_ty_v
Proof
  rw[perms_ok_def, mk_fun_ty_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_type_of_v[simp]:
  perms_ok kernel_perms type_of_v
Proof
  rw[perms_ok_def, type_of_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_call_type_of_v[simp]:
  perms_ok kernel_perms call_type_of_v
Proof
  rw[perms_ok_def, call_type_of_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_get_const_type_v[simp]:
  perms_ok kernel_perms get_const_type_v
Proof
  rw[perms_ok_def, get_const_type_v_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_mk_const_v[simp]:
  perms_ok kernel_perms mk_const_v
Proof
  rw[perms_ok_def, mk_const_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_mk_comb_v[simp]:
  perms_ok kernel_perms mk_comb_v
Proof
  rw[perms_ok_def, mk_comb_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_mk_eq_v[simp]:
  perms_ok kernel_perms mk_eq_v
Proof
  rw[perms_ok_def, mk_eq_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_mk_comb_1_v[simp]:
  perms_ok kernel_perms mk_comb_1_v
Proof
  rw[perms_ok_def, mk_comb_1_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_refl_v[simp]:
  perms_ok kernel_perms refl_v
Proof
  rw[perms_ok_def, refl_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw[]
QED

Theorem perms_ok_assume_v[simp]:
  perms_ok kernel_perms assume_v
Proof
  rw[perms_ok_def, assume_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac \\ rw[]
QED

Theorem perms_ok_deduct_antisym_rule_v[simp]:
  perms_ok kernel_perms deduct_antisym_rule_v
Proof
  rw[perms_ok_def, deduct_antisym_rule_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_vsubst_v[simp]:
  perms_ok kernel_perms vsubst_v
Proof
  rw[perms_ok_def, vsubst_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_inst_1_v[simp]:
  perms_ok kernel_perms inst_1_v
Proof
  rw[perms_ok_def, inst_1_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_beta_v[simp]:
  perms_ok kernel_perms beta_v
Proof
  rw[perms_ok_def, beta_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_trans_v[simp]:
  perms_ok kernel_perms trans_v
Proof
  rw[perms_ok_def, trans_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_abs_v[simp]:
  perms_ok kernel_perms abs_v
Proof
  rw[perms_ok_def, abs_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_check_for_dups_v[simp]:
  perms_ok ps check_for_dups_v
Proof
  rw[perms_ok_def, check_for_dups_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_add_constants_v[simp]:
 perms_ok kernel_perms add_constants_v
Proof
  rw[perms_ok_def, add_constants_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ TRY(pop_assum mp_tac \\ eval_nsLookup_tac)
  \\ rw[] \\ rw[kernel_perms_def]
QED

Theorem perms_ok_the_context[simp]:
  perms_ok kernel_perms the_context
Proof
  rw[the_context_def, perms_ok_def, kernel_perms_def, kernel_locs_def]
QED

Theorem perms_ok_add_def_v[simp]:
  perms_ok kernel_perms add_def_v
Proof
  rw[perms_ok_def, add_def_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ TRY(pop_assum mp_tac \\ CONV_TAC(DEPTH_CONV nsLookup_conv))
  \\ rw[] \\ rw[kernel_perms_def]
QED

Theorem perms_ok_new_constant_v[simp]:
 perms_ok kernel_perms new_constant_v
Proof
  rw[perms_ok_def, new_constant_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_add_type_v[simp]:
  perms_ok kernel_perms add_type_v
Proof
  rw[perms_ok_def, add_type_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ TRY(pop_assum mp_tac \\ eval_nsLookup_tac)
  \\ rw[] \\ rw[kernel_perms_def]
QED

Theorem perms_ok_new_type_v[simp]:
  perms_ok kernel_perms new_type_v
Proof
  rw[perms_ok_def, new_type_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_call_new_type_v[simp]:
  perms_ok kernel_perms call_new_type_v
Proof
  rw[perms_ok_def, call_new_type_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_new_axiom_v[simp]:
 perms_ok kernel_perms new_axiom_v
Proof
  rw[perms_ok_def, new_axiom_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ TRY(pop_assum mp_tac \\ eval_nsLookup_tac)
  \\ rw[] \\ rw[kernel_perms_def]
QED

Theorem perms_ok_new_specification_v[simp]:
 perms_ok kernel_perms new_specification_v
Proof
  rw[perms_ok_def, new_specification_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

Theorem perms_ok_new_basic_definition_v[simp]:
 perms_ok kernel_perms new_basic_definition_v
Proof
  rw[perms_ok_def, new_basic_definition_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[] \\ rw[kernel_perms_def]
QED

Theorem perms_ok_new_basic_type_definition_v[simp]:
 perms_ok kernel_perms new_basic_type_definition_v
Proof
  rw[perms_ok_def, new_basic_type_definition_v_def, astTheory.pat_bindings_def, perms_ok_env_def]
  \\ pop_assum mp_tac \\ eval_nsLookup_tac
  \\ rw[]
QED

(*
Theorem perms_ok_member_v:
  perms_ok ps member_v
Proof
  rw [member_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
QED

Theorem perms_ok_list_union_v:
  perms_ok ps list_union_v
Proof
  rw [list_union_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "member"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_member_v]
QED

Theorem perms_ok_conj_v:
  perms_ok ps conj_v
Proof
  rw [conj_v_def, perms_ok_def, perms_ok_exp_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "list_union"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_list_union_v]
QED

Theorem perms_ok_disj1_v:
  perms_ok ps disj1_v
Proof
  rw [disj1_v_def, perms_ok_def, perms_ok_exp_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs []
        \\ CCONTR_TAC \\ gs [])
  \\ gs [perms_ok_env_def]
QED
*)

Triviality evaluate_kernel_perms_lemma:
  ∀ps.
    evaluate s env [exp] = (s',res) ∧
    perms_ok_exp ps exp ∧ perms_ok_env ps (freevars exp) env ∧ perms_ok_state ps s ∧
    DoFFI ∉ ps ∧ RefAlloc ∉ ps ∧ W8Alloc ∉ ps ⇒
    LENGTH s'.refs = LENGTH s.refs ∧
    s'.ffi = s.ffi ∧
    s'.eval_state = s.eval_state
Proof
  metis_tac [evaluate_perms_ok_exp]
QED

Theorem evaluate_kernel_perms =
  evaluate_kernel_perms_lemma
  |> Q.SPEC ‘kernel_perms’
  |> SIMP_RULE (srw_ss()) [kernel_perms_def]
  |> REWRITE_RULE [GSYM kernel_perms_def];

Theorem evaluate_empty_perms =
  evaluate_kernel_perms_lemma
  |> Q.SPEC ‘{}’
  |> SIMP_RULE (srw_ss()) [];

val _ = export_theory ();

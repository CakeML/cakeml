(*
  cv_compute version of addPrintVals_cv.
*)
Theory addPrintVals_cv
Ancestors
  cv_std infer_cv typeDecToPP_cv addPrintVals
Libs
  cv_transLib

val res = cv_auto_trans nsContents_def;
val res = cv_auto_trans empty_type_names_def;
val res = cv_auto_trans add_type_name_def;
val res = cv_auto_trans t_info_id_def;
val res = cv_auto_trans update_type_names_def;
val res = cv_auto_trans strip_tapp_fun_def;

val res = cv_auto_trans_pre "" tn_current_def;

Theorem tn_current_pre[cv_pre]:
  ∀ienv id nm. tn_current_pre ienv id nm
Proof
  simp [res]
QED

val res = cv_auto_trans add_to_namespace_def;
val res = cv_auto_trans mk_namespace_def;
val res = cv_auto_trans FIND_SND_def;
val res = cv_auto_trans tn_setup_fixes_def;
val res = cv_auto_trans init_type_names_def;
val res = cv_auto_trans FIND_tn_current_def;
val res = cv_auto_trans get_tn_ok_def;
val res = cv_auto_trans inf_t_to_ast_t_mono_def;

val res = cv_auto_trans_pre "" type_con_name_def;

Theorem type_con_name_pre[cv_pre]:
  ∀tn ti. type_con_name_pre tn ti
Proof
  simp [res]
QED

val res = cv_trans_pre "" inf_type_to_string_def;

Theorem inf_type_to_string_pre[cv_pre]:
  (∀tn v. inf_type_to_string_pre tn v) ∧
  (∀tn v. inf_type_to_string_list_pre tn v)
Proof
  ho_match_mp_tac inf_type_to_string_ind
  \\ rpt strip_tac \\ simp [Once res]
  \\ rpt strip_tac \\ gvs []
QED

val res = cv_trans inf_t_to_s_def;
val res = cv_auto_trans print_of_val_opts_def;
val res = cv_auto_trans val_prints_def;

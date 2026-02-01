(*
  cv_compute version of typeDecToPP.
*)
Theory typeDecToPP_cv
Ancestors
  cv_std infer_cv typeDecToPP
Libs
  cv_transLib

val res = cv_trans pppre_def;
val res = cv_trans pp_prefix_def;
val res = cv_trans mk_list_exp_def;
val res = cv_auto_trans con_x_i_pat_def;
val res = cv_auto_trans x_i_list_f_apps_def;
val res = cv_trans mod_pp_def;
val res = cv_trans id_to_str_def;

val res = cv_auto_trans_pre "" pp_of_ast_t_def;

Theorem pp_of_ast_t_pre[cv_pre]:
  (∀v fixes. pp_of_ast_t_pre fixes v) ∧
  (∀v fixes. pp_of_ast_ts_pre fixes v)
Proof
  ho_match_mp_tac astTheory.ast_t_induction
  \\ rpt strip_tac \\ simp [Once res]
QED

val res = cv_auto_trans mk_pps_for_type_def;
val res = cv_auto_trans mk_pp_type_def;
val res = cv_trans pps_for_dec_def;
val res = cv_trans add_pp_decs_def;

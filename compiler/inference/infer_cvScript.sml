(*
  Translating inferTheory to cv equations for use with cv_eval
*)
open preamble miscTheory;
open cv_transLib;
open astTheory namespaceTheory inferTheory unify_cvTheory;

val _ = new_theory "infer_cv";

val expand = let
  val th1 = SRULE [FUN_EQ_THM] st_ex_bind_def
  val th2 = SRULE [FUN_EQ_THM] st_ex_return_def
  val th3 = SRULE [FUN_EQ_THM,COND_RATOR,th2] guard_def
  in SRULE [th1,th2,th3,FUN_EQ_THM] end

val _ = cv_auto_trans $ expand failwith_def;
val _ = cv_auto_trans $ expand read_def;
val _ = cv_auto_trans $ expand write_def;

val _ = cv_trans $ init_infer_state_def;
val _ = cv_trans $ expand init_state_def;

val _ = cv_trans $ expand mlstringTheory.implode_def;
val _ = cv_auto_trans mlstringTheory.concat_def;
val _ = cv_auto_trans lookup_st_ex_def;

val _ = cv_auto_trans $ expand fresh_uvar_def;
val pre = n_fresh_uvar_def |> SRULE [fresh_uvar_def,COND_RATOR,FUN_EQ_THM] |> expand |> cv_trans_pre;

Theorem n_fresh_uvar_pre[cv_pre,local]:
  ∀a0 a1. n_fresh_uvar_pre a0 a1
Proof
  Induct \\ simp [Once pre]
QED

val _ = cv_auto_trans $ expand n_fresh_id_def;

val _ = cv_auto_trans $ expand get_next_uvar_def;
val apply_subst_pre = cv_auto_trans_pre
                      (expand apply_subst_def |> SRULE [read_def]);

Definition map_t_walkstar_def:
  map_t_walkstar s [] = [] ∧
  map_t_walkstar s (t::ts) = t_walkstar s t :: map_t_walkstar s ts
End

Triviality map_t_walkstar_thm:
  MAP (t_walkstar s) ts = map_t_walkstar s ts
Proof
 Induct_on ‘ts’ \\ gvs [map_t_walkstar_def]
QED

val map_t_walkstar_pre = cv_trans_pre map_t_walkstar_def;

val apply_subst_list_pre = cv_trans_pre
  (apply_subst_list_def |> expand |> SRULE [read_def,map_t_walkstar_thm]);

Definition add_parens_list_def:
  add_parens_list n [] = [] ∧
  add_parens_list n (x::xs) = add_parens n x :: add_parens_list n xs
End

Theorem add_parens_list:
  MAP (add_parens n) xs = add_parens_list n xs
Proof
  Induct_on ‘xs’ \\ gvs [add_parens_list_def]
QED

val _ = cv_trans infer_tTheory.add_parens_def;
val _ = cv_trans add_parens_list_def;

val res = cv_trans_pre infer_tTheory.get_tyname_def;

Theorem get_tyname_pre[cv_pre]:
  ∀a0 a1. get_tyname_pre a0 a1
Proof
  ho_match_mp_tac infer_tTheory.get_tyname_ind
  \\ rw [] \\ simp [Once res]
QED

val toChar_pre = cv_trans_pre mlintTheory.toChar_def
val num_to_chars_pre = cv_auto_trans_pre mlintTheory.num_to_chars_def;

Theorem num_to_chars_pre[cv_pre,local]:
  ∀a0 a1 a2 a3. num_to_chars_pre a0 a1 a2 a3
Proof
  ho_match_mp_tac mlintTheory.num_to_chars_ind \\ rw []
  \\ rw [] \\ simp [Once num_to_chars_pre]
  \\ once_rewrite_tac [toChar_pre] \\ gvs [] \\ rw []
  \\ ‘k MOD 10 < 10’ by gvs [] \\ simp []
QED

Triviality Num_ABS:
  Num (ABS i) = Num i
Proof
  Cases_on ‘i’ \\ gvs []
QED

val _ = cv_trans (mlintTheory.toString_def |> SRULE [Num_ABS]);
val _ = cv_trans mlintTheory.num_to_str_def;

val _ = cv_auto_trans infer_tTheory.type_ident_to_string_def;

val res = cv_trans_pre infer_tTheory.ty_var_name_def;

Theorem ty_var_name_pre[cv_pre,local]:
  ∀a0. ty_var_name_pre a0
Proof
  gvs [res]
QED

val res = expand infer_tTheory.inf_type_to_string_rec_def
            |> SRULE [add_parens_list]
            |> cv_auto_trans;

val res = infer_tTheory.inf_type_to_string_def |> cv_trans;

val add_constraint_pre = add_constraint_def |> expand |> cv_auto_trans_pre;
val add_constraints_pre = add_constraints_def |> expand |> cv_auto_trans_pre;

val _ = cv_trans generalise_def;
val _ = cv_trans infer_type_subst_def;

val infer_deBruijn_subst_pre = cv_trans_pre infer_deBruijn_subst_def;

Theorem infer_deBruijn_subst_pre[cv_pre,local]:
  (∀a1 a0. infer_deBruijn_subst_pre a0 a1) ∧
  (∀a3 a2. infer_deBruijn_subst_list_pre a2 a3)
Proof
  ho_match_mp_tac infer_tTheory.infer_t_induction \\ rw []
  \\ simp [Once infer_deBruijn_subst_pre]
QED

val _ = cv_trans word_tc_def
val _ = cv_trans op_to_string_def
val _ = cv_trans op_simple_constraints_def
val _ = cv_trans op_n_args_msg_def
val _ = cv_auto_trans extend_dec_ienv_def
val _ = cv_auto_trans lift_ienv_def
val _ = cv_trans find_dup_def

Definition type_subst_alist_def:
  type_subst_alist s (Tvar_db n) = Tvar_db n ∧
  type_subst_alist s (Tvar tv) =
    (case ALOOKUP s tv of NONE => Tvar tv | SOME t => t) ∧
  type_subst_alist s (Tapp ts tn) = Tapp (type_subst_alist_list s ts) tn ∧
  type_subst_alist_list s [] = [] ∧
  type_subst_alist_list s (t::ts) =
    type_subst_alist s t :: type_subst_alist_list s ts
End

Theorem type_subst_alist_to_fmap:
  (∀t xs. type_subst (alist_to_fmap xs) t = type_subst_alist xs t) ∧
  (∀t xs. MAP (type_subst (alist_to_fmap xs)) t = type_subst_alist_list xs t)
Proof
  ho_match_mp_tac typeSystemTheory.t_induction
  \\ gvs [typeSystemTheory.type_subst_def,type_subst_alist_def,SF ETA_ss]
QED

val _ = cv_trans type_subst_alist_def;
val _ = cv_trans typeSystemTheory.Tfn_def;
val _ = cv_trans typeSystemTheory.Ttup_def;

val type_name_check_sub_pre = cv_trans_pre
  (type_name_check_sub_def
     |> SRULE [type_subst_alist_to_fmap,FUN_EQ_THM])

Theorem type_name_check_sub_pre[local,cv_pre]:
  (∀t a0 a1 a2 (a4:'a). type_name_check_sub_pre a0 a1 a2 t a4) ∧
  (∀t a5 a6 a7 (a9:'a). type_name_check_sub_list_pre a5 a6 a7 t a9)
Proof
  ho_match_mp_tac ast_t_induction \\ rw []
  \\ simp [Once type_name_check_sub_pre]
QED

val res = cv_trans_pre check_ctor_types_expand

Theorem check_ctor_types_pre[local,cv_pre]:
  ∀a0 a1 a2 a3 a4. check_ctor_types_pre a0 a1 a2 a3 a4
Proof
  Induct_on ‘a3’ \\ rw [] \\ simp [Once res]
QED

val res = check_ctors_expand
val res = check_type_definition_expand |> SRULE [GSYM MAP_MAP_o]
val res = infer_p_expand (* has MAP *)
val res = constrain_op_expand
val res = infer_e_expand (* has MAP, MAP2 *)
val res = infer_d_expand (* has MAP, MAP2 *)
val res = infertype_prog_def

val _ = export_theory ();

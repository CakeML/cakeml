(*
  Translating inferTheory to cv equations for use with cv_eval
*)
open preamble miscTheory;
open cv_transLib;
open astTheory namespaceTheory inferTheory inferPropsTheory unify_cvTheory;

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
val pre = n_fresh_uvar_def |> SRULE [fresh_uvar_def,COND_RATOR,FUN_EQ_THM]
                           |> expand |> cv_trans_pre;

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

Theorem add_constraint_pre_eq:
  add_constraint_pre l t1 t2 s = t_wfs s.subst
Proof
  gvs [add_constraint_pre]
  \\ Cases_on ‘t_wfs s.subst’ \\ gvs []
QED

Theorem add_constraints_pre_eq:
  ∀ts1 ts2 l s.
    add_constraints_pre l ts1 ts2 s = (t_wfs s.subst ∨ ts1 = [] ∨ ts2 = [])
Proof
  Induct \\ rw [] \\ simp [Once add_constraints_pre]
  \\ Cases_on ‘ts2’ \\ gvs [add_constraint_pre_eq]
  \\ Cases_on ‘t_wfs s.subst’ \\ gvs []
  \\ gvs [add_constraint_def,AllCaseEqs()]
  \\ rw [] \\ gvs []
  \\ drule_all unifyTheory.t_unify_wfs \\ gvs []
QED

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

val type_name_check_sub_pre = cv_auto_trans_pre
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

val res = cv_trans_pre check_ctors_expand

Theorem check_ctors_pre[local,cv_pre]:
  ∀a0 a1 a2 a3. check_ctors_pre a0 a1 a2 a3
Proof
  Induct_on ‘a2’ \\ rw [] \\ simp [Once res]
QED

val res = cv_trans (check_type_definition_expand |> SRULE [GSYM MAP_MAP_o])

Definition map_infer_type_subst_def:
  map_infer_type_subst s [] = [] ∧
  map_infer_type_subst s (x::xs) =
  infer_type_subst s x :: map_infer_type_subst s xs
End

Triviality map_infer_type_subst_eq:
  map_infer_type_subst s xs = MAP (infer_type_subst s) xs
Proof
  Induct_on ‘xs’ \\ gvs [map_infer_type_subst_def]
QED

val _ = cv_trans map_infer_type_subst_def;

val infer_p_pre = cv_trans_pre
                  (infer_p_expand |> SRULE [GSYM map_infer_type_subst_eq]);

val constrain_op_pre = cv_trans_pre constrain_op_expand;

Definition map1_def:
  map1 [] = [] ∧
  map1 ((n,t)::xs) = (n,0n,t) :: map1 xs
End

Triviality map1_eq:
  map1 xs = MAP (λ(n,t). (n,0n,t)) xs
Proof
  Induct_on ‘xs’ \\ gvs [map1_def,FORALL_PROD]
QED

val _ = cv_trans map1_def

Definition map2_def:
  map2 ((f,x,e)::xs) (uvar::ys) = (f,0n,uvar) :: map2 xs ys ∧
  map2 _ _ = []
End

Triviality map2_eq:
  ∀xs ys. map2 xs ys = MAP2 (λ(f,x,e) uvar. (f,0n,uvar)) xs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [map2_def,FORALL_PROD]
QED

val _ = cv_trans map2_def;
val _ = cv_trans nsBind_def;
val _ = cv_trans nsOptBind_def;

val infer_e_pre = cv_trans_pre_rec
          (infer_e_expand |> SRULE [GSYM map_infer_type_subst_eq,
                                    GSYM map1_eq, GSYM map2_eq,
                                    namespaceTheory.alist_to_ns_def])
 (WF_REL_TAC ‘measure $ λx. case x of
                            | INL (_,_,e,_) => cv_sum_depth e
                            | INR (INL (_,_,es,_)) => cv_sum_depth es
                            | INR (INR (INL (_,_,pes,_,_,_))) => cv_sum_depth pes
                            | INR (INR (INR (_,_,funs,_))) => cv_sum_depth funs’
  \\ rpt conj_tac \\ cv_termination_tac);

Definition exp_is_value_def:
  exp_is_value (Lit _) = T ∧
  exp_is_value (Con _ es) = exp_is_value_list es ∧
  exp_is_value (Var _) = T ∧
  exp_is_value (Fun _ _) = T ∧
  exp_is_value (Tannot e v5) = exp_is_value e ∧
  exp_is_value (Lannot e v6) = exp_is_value e ∧
  exp_is_value _ = F ∧
  exp_is_value_list [] = T ∧
  exp_is_value_list (x::xs) = (exp_is_value x ∧ exp_is_value_list xs)
Termination
  WF_REL_TAC ‘measure $ λx. case x of INL e => exp_size e
                                    | INR es => list_size exp_size es’
End

val _ = cv_trans exp_is_value_def

Theorem exp_is_value_eq:
  (∀e. is_value e = exp_is_value e) ∧
  (∀es. EVERY is_value es = exp_is_value_list es)
Proof
  ho_match_mp_tac exp_is_value_ind \\ rw []
  \\ simp [typeSystemTheory.is_value_def,exp_is_value_def,SF ETA_ss]
QED

val _ = cv_trans alist_to_ns_def;

Definition infer_d_map_1_def:
  infer_d_map_1 y [] = [] ∧
  infer_d_map_1 y (t::ts) = (y,t) :: infer_d_map_1 y ts
End

val _ = cv_trans infer_d_map_1_def

Theorem infer_d_map_1_eq:
  MAP (λt. (y,t)) ts = infer_d_map_1 y ts
Proof
  Induct_on ‘ts’ \\ gvs [infer_d_map_1_def]
QED

Definition MAP_Tvar_def:
  MAP_Tvar [] = [] ∧
  MAP_Tvar (e::es) = Tvar e :: MAP_Tvar es
End

val _ = cv_trans MAP_Tvar_def

Theorem MAP_Tvar_eq:
  MAP Tvar ts = MAP_Tvar ts
Proof
  Induct_on ‘ts’ \\ gvs [MAP_Tvar_def]
QED

Definition infer_d_map_2_def:
  infer_d_map_2 ((tvs,tn,ctors)::xs) (i::ys) =
    (tn,tvs,Tapp (MAP_Tvar tvs) i) :: infer_d_map_2 xs ys ∧
  infer_d_map_2  _ _ = []
End

val _ = cv_trans infer_d_map_2_def

Theorem infer_d_map_2_eq:
  ∀xs ys.
    MAP2 (λ(tvs,tn,ctors) i. (tn,tvs,Tapp (MAP_Tvar tvs) i)) xs ys =
    infer_d_map_2 xs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [infer_d_map_2_def,FORALL_PROD]
QED

Definition infer_d_map_3_def:
  infer_d_map_3 y ((f,x,e)::xs) (t::ys) = (f,y,t) :: infer_d_map_3 y xs ys ∧
  infer_d_map_3 y  _ _ = []
End

val _ = cv_trans infer_d_map_3_def

Theorem infer_d_map_3_eq:
  ∀xs ys.
    MAP2 (λ(f,x,e) t. (f,y,t)) xs ys = infer_d_map_3 y xs ys
Proof
  Induct \\ Cases_on ‘ys’ \\ gvs [infer_d_map_3_def,FORALL_PROD]
QED

Definition type_name_subst_1_def:
  type_name_subst_1 tenvT (Atvar tv) = Tvar tv ∧
  type_name_subst_1 tenvT (Attup ts) =
    Ttup (type_name_subst_list_1 tenvT ts) ∧
  type_name_subst_1 tenvT (Atfun t1 t2) =
    Tfn (type_name_subst_1 tenvT t1) (type_name_subst_1 tenvT t2) ∧
  type_name_subst_1 tenvT (Atapp ts tc) =
    (let args = type_name_subst_list_1 tenvT ts in
       case nsLookup tenvT tc of
       | NONE => Ttup args
       | SOME (tvs,t) => type_subst_alist (ZIP (tvs,args)) t) ∧
  type_name_subst_list_1 tenvT [] = [] ∧
  type_name_subst_list_1 tenvT (t::ts) =
    type_name_subst_1 tenvT t ::
    type_name_subst_list_1 tenvT ts
End

val _ = cv_auto_trans type_name_subst_1_def;

Theorem type_name_subst_1_eq:
  (∀t. type_name_subst tenvT t = type_name_subst_1 tenvT t) ∧
  (∀ts. MAP (type_name_subst tenvT) ts = type_name_subst_list_1 tenvT ts)
Proof
  ho_match_mp_tac ast_t_induction \\ rw []
  \\ gvs [type_name_subst_1_def,GSYM type_subst_alist_to_fmap,
          typeSystemTheory.type_name_subst_def] \\ gvs [SF ETA_ss]
QED

Definition MAP_type_name_subst_def:
  MAP_type_name_subst tenvT [] = [] ∧
  MAP_type_name_subst tenvT (x::xs) =
  type_name_subst_1 tenvT x :: MAP_type_name_subst tenvT xs
End

val _ = cv_trans MAP_type_name_subst_def;

Theorem MAP_type_name_subst_eq:
  MAP (type_name_subst tenvT) ts = MAP_type_name_subst tenvT ts
Proof
  Induct_on ‘ts’ \\ gvs [MAP_type_name_subst_def,GSYM type_name_subst_1_eq]
QED

Definition MAP_MAP_type_name_subst_def:
  MAP_MAP_type_name_subst id tenvT tvs [] = [] ∧
  MAP_MAP_type_name_subst id tenvT tvs ((cn,ts)::xs) =
    (cn,tvs,MAP_type_name_subst tenvT ts,id) ::
    MAP_MAP_type_name_subst id tenvT tvs xs
End

val _ = cv_trans MAP_MAP_type_name_subst_def

Theorem MAP_MAP_type_name_subst_eq:
  MAP (λ(cn,ts). (cn,tvs,MAP_type_name_subst tenvT ts,id)) xs =
  MAP_MAP_type_name_subst id tenvT tvs xs
Proof
  Induct_on ‘xs’ \\ gvs [FORALL_PROD,MAP_MAP_type_name_subst_def]
QED

val res = cv_trans_pre (typeSystemTheory.build_ctor_tenv_def
 |> SRULE [namespaceTheory.alist_to_ns_def, namespaceTheory.nsEmpty_def,
           MAP_type_name_subst_eq,MAP_MAP_type_name_subst_eq]);

Theorem build_ctor_tenv_pre[cv_pre,local]:
  ∀a0 a1 a2. build_ctor_tenv_pre a0 a1 a2
Proof
  Induct_on ‘a1’ \\ gvs [] \\ rw [] \\ simp [Once res]
QED

val _ = cv_trans namespaceTheory.nsSing_def;

val infer_d_pre = cv_trans_pre
  (infer_d_expand
     |> SRULE [exp_is_value_eq,infer_d_map_1_eq,nsEmpty_def,
               extend_dec_ienv_def,
               infer_d_map_2_eq, infer_d_map_3_eq,init_state_def,
               GSYM map1_eq, GSYM map2_eq, MAP_Tvar_eq]);

Definition call_infer_def:
  call_infer ienv prog start_id =
  infer_ds ienv prog
    <|next_uvar := 0; subst := FEMPTY; next_id := start_id|>
End

val infertype_prog_eq =
  infertype_prog_def |> SRULE [init_infer_state_def, GSYM call_infer_def];

val infertype_prog_inc_eq =
  infertype_prog_inc_def |> SRULE [init_infer_state_def, GSYM call_infer_def];

val call_infer_pre = cv_auto_trans_pre call_infer_def;

Theorem type_name_check_sub_success:
  type_name_check_sub l ienv.inf_t xs a s = (Success r,s1) ⇒
  ∃f. type_name_check_subst l f ienv.inf_t xs a s = (Success r,s1)
Proof
  gvs [to_type_name_check_sub]
QED

Theorem IMP_infer_p_pre:
  (∀d l ienv s. t_wfs s.subst ⇒ infer_p_pre l ienv d s) ∧
  (∀ds l ienv s. t_wfs s.subst ⇒ infer_ps_pre l ienv ds s)
Proof
  Induct \\ rw [] \\ simp [Once infer_p_pre]
  \\ gvs [add_constraints_pre_eq] \\ rw []
  \\ gvs [lookup_st_ex_def,AllCaseEqs()]
  \\ imp_res_tac infer_p_wfs
  \\ gvs [n_fresh_uvar_success]
  \\ gvs [add_constraint_pre_eq] \\ rw []
  \\ gvs [to_type_name_check_sub]
  \\ imp_res_tac type_name_check_sub_success
  \\ gvs [type_name_check_subst_success]
QED

Theorem IMP_map_t_walkstar_pre:
  ∀xs s. t_wfs s ⇒ map_t_walkstar_pre s xs
Proof
  Induct \\ rw [] \\ simp [Once map_t_walkstar_pre]
QED

Theorem IMP_apply_subst_list_pre:
  t_wfs s.subst ⇒ apply_subst_list_pre xs s
Proof
  gvs [apply_subst_list_pre,IMP_map_t_walkstar_pre]
QED

Theorem add_constraint_wfs:
  add_constraint l x y s = (r,s1) ∧ t_wfs s.subst ⇒ t_wfs s1.subst
Proof
  Cases_on ‘r’ \\ gvs [] \\ gvs [add_constraint_success] \\ rw []
  >- (drule_all unifyTheory.t_unify_wfs \\ gvs [])
  \\ gvs [add_constraint_def,AllCaseEqs()]
QED

Theorem add_constraints_wfs:
  ∀x y l s. add_constraints l x y s = (r,s1) ∧ t_wfs s.subst ⇒ t_wfs s1.subst
Proof
  Induct \\ Cases_on ‘y’
  \\ gvs [add_constraints_def,st_ex_return_def,failwith_def,st_ex_bind_def]
  \\ rw [] \\ gvs [AllCaseEqs()]
  \\ drule_all add_constraint_wfs \\ rw []
  \\ res_tac \\ gvs []
QED

Theorem IMP_constrain_op_pre:
  t_wfs s.subst ⇒ constrain_op_pre l op ts s
Proof
  simp [constrain_op_pre] \\ rpt strip_tac \\ gvs []
  \\ gvs [add_constraint_pre_eq, add_constraints_pre_eq,fresh_uvar_def]
  \\ rpt (dxrule add_constraint_wfs \\ rpt strip_tac) \\ gvs []
QED

Theorem IMP_infer_e_pre:
  (∀l ienv e s. t_wfs s.subst ⇒ infer_e_pre l ienv e s) ∧
  (∀l ienv es s. t_wfs s.subst ⇒ infer_es_pre l ienv es s) ∧
  (∀l ienv pes t1 t2 s. t_wfs s.subst ⇒ infer_pes_pre l ienv pes t1 t2 s) ∧
  (∀l ienv funs s. t_wfs s.subst ⇒ infer_funs_pre l ienv funs s)
Proof
  ho_match_mp_tac infer_e_ind \\ rpt strip_tac
  \\ simp [Once infer_e_pre]
  \\ gvs [lookup_st_ex_def,AllCaseEqs()]
  \\ gvs [add_constraint_pre_eq,add_constraints_pre_eq] \\ rw []
  \\ gvs [] \\ imp_res_tac infer_e_wfs \\ gvs []
  \\ gvs [n_fresh_uvar_success,get_next_uvar_def,fresh_uvar_def]
  \\ rpt (dxrule add_constraint_wfs \\ rpt strip_tac)
  \\ rpt (dxrule add_constraints_wfs \\ rpt strip_tac) \\ gvs []
  \\ rpt (CASE_TAC \\ gvs (TypeBase.updates_of “:inf_env” @
                        TypeBase.updates_of “:loc_err_info”))
  \\ imp_res_tac type_name_check_sub_success \\ gvs []
  \\ gvs [type_name_check_subst_success,IMP_infer_p_pre]
  \\ imp_res_tac infer_p_wfs
  \\ gvs [GSYM map1_eq,alist_to_ns_def]
  \\ irule IMP_constrain_op_pre \\ gvs []
QED

Theorem IMP_infer_d_pre:
  (∀d ienv s. t_wfs s.subst ⇒ infer_d_pre ienv d s) ∧
  (∀ds ienv s. t_wfs s.subst ⇒ infer_ds_pre ienv ds s)
Proof
  Induct \\ rpt strip_tac
  >~ [‘Dtype’] >- (once_rewrite_tac [infer_d_pre] \\ gvs [])
  >~ [‘Dtabbrev’] >- (once_rewrite_tac [infer_d_pre] \\ gvs [])
  >~ [‘Dexn’] >- (once_rewrite_tac [infer_d_pre] \\ gvs [])
  >~ [‘Dmod’] >- (once_rewrite_tac [infer_d_pre] \\ gvs [])
  >~ [‘Denv’] >- (once_rewrite_tac [infer_d_pre] \\ gvs [])
  >~ [‘infer_ds_pre ienv [] s’] >- (once_rewrite_tac [infer_d_pre] \\ gvs [])
  >~ [‘infer_ds_pre ienv _ s’] >-
   (once_rewrite_tac [infer_d_pre] \\ gvs [] \\ rw []
    \\ imp_res_tac infer_d_wfs
    \\ first_x_assum irule \\ gvs [])
  >~ [‘Dlocal’] >-
   (once_rewrite_tac [infer_d_pre] \\ gvs [] \\ rw []
    \\ imp_res_tac infer_d_wfs
    \\ first_x_assum irule \\ gvs [])
  >~ [‘Dlet’] >-
   (once_rewrite_tac [infer_d_pre] \\ gvs [] \\ rw []
    \\ gvs [get_next_uvar_def]
    \\ imp_res_tac infer_e_wfs \\ gvs []
    >- (irule $ cj 1 IMP_infer_e_pre \\ gvs [init_infer_state_def])
    >- (irule $ cj 1 IMP_infer_p_pre \\ gvs [init_infer_state_def])
    \\ imp_res_tac infer_p_wfs \\ gvs [add_constraint_pre_eq]
    \\ irule IMP_apply_subst_list_pre \\ gvs []
    \\ drule_all add_constraint_wfs \\ gvs [])
  >~ [‘Dletrec’] >-
   (once_rewrite_tac [infer_d_pre] \\ gvs [] \\ rw []
    >- (irule $ cj 4 IMP_infer_e_pre \\ gvs [init_infer_state_def]
        \\ gvs [n_fresh_uvar_success,get_next_uvar_def])
    \\ gvs [add_constraints_pre_eq]
    \\ imp_res_tac infer_e_wfs \\ gvs []
    \\ gvs [n_fresh_uvar_success,get_next_uvar_def]
    \\ imp_res_tac add_constraints_wfs
    \\ irule IMP_apply_subst_list_pre \\ gvs [])
QED

Theorem call_infer_pre_thm[cv_pre,local]:
  ∀a0 a1 a2. call_infer_pre a0 a1 a2
Proof
  rw [call_infer_pre]
  \\ irule $ cj 2 IMP_infer_d_pre
  \\ gvs [unifyTheory.t_wfs_def]
QED

val _ = cv_auto_trans (infertype_prog_eq |> SRULE [extend_dec_ienv_def]);
val _ = cv_auto_trans (infertype_prog_inc_eq |> SRULE [extend_dec_ienv_def]);

(* main results stored as: cv_infertype_prog_thm
                           cv_infertype_prog_inc_thm *)

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = export_theory ();

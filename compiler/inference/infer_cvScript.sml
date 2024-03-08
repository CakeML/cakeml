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

fun rename_bound_vars_rule prefix th = let
  val i = ref 0
  fun next_name () = (i:= !i+1; prefix ^ int_to_string (!i))
  fun next_var v = mk_var(next_name (), type_of v)
  fun next_alpha_conv tm = let
    val (v,_) = dest_abs tm
    val _ = not (String.isPrefix prefix (fst (dest_var v))) orelse fail()
    in ALPHA_CONV (next_var v) tm end handle HOL_ERR _ => NO_CONV tm
  in CONV_RULE (DEPTH_CONV next_alpha_conv) th end;

val res = cv_trans_pre_rec
          (infer_e_expand |> SRULE [GSYM map_infer_type_subst_eq,
                                    GSYM map1_eq, GSYM map2_eq,
                                    namespaceTheory.alist_to_ns_def]
                                    |> rename_bound_vars_rule "var")
          cheat;

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

val _ = cv_trans type_name_subst_1_def;

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
  call_infer ienv prog =
  infer_ds ienv prog
     <|next_uvar := 0; subst := FEMPTY; next_id := start_type_id|>
End

val call_infer_pre =
  cv_trans_pre (call_infer_def |> SRULE [EVAL “start_type_id”]);

Theorem call_infer_pre[cv_pre,local]:
  ∀a0 a1. call_infer_pre a0 a1
Proof
  cheat
QED

val _ = cv_trans (infertype_prog_def
  |> SRULE [init_infer_state_def,GSYM call_infer_def,extend_dec_ienv_def]);

(* main result stored as: cv_infertype_prog_thm *)

val _ = export_theory ();

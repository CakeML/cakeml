(*
  Translate non-target-specific backend functions to cv equations.
*)
Theory backend_cv
Libs
  preamble cv_transLib
Ancestors
  mllist mergesort cv_std backend backend_passes to_data_cv export unify_cv
  infer_cv basis_cv

val _ = cv_memLib.use_long_names := true;

Definition collect_conses_def:
  (collect_conses p (Raise e) = collect_conses p e) ∧
  (collect_conses p (Handle e pes) =
     collect_conses_list2 (collect_conses p e) pes) ∧
  (collect_conses p (Mat e pes) =
     collect_conses_list2 (collect_conses p e) pes) ∧
  (collect_conses p (ast$Lit l) = p) ∧
  (collect_conses p (Con cn es) =
     case cn of
     | NONE => collect_conses_list p es
     | SOME c =>
         let x = (c,LENGTH es) in
           collect_conses_list (if MEM x p then p else x::p) es) ∧
  (collect_conses p (Var v) = p) ∧
  (collect_conses p (Fun x e) = collect_conses p e) ∧
  (collect_conses p (App op es) = collect_conses_list p es) ∧
  (collect_conses p (Log lop e1 e2) =
     collect_conses (collect_conses p e2) e1) ∧
  (collect_conses p (If e1 e2 e3) =
     collect_conses (collect_conses (collect_conses p e3) e2) e1) ∧
  (collect_conses p (Let x e1 e2) =
     collect_conses (collect_conses p e2) e1) ∧
  (collect_conses p (Tannot e a) = collect_conses p e) ∧
  (collect_conses p (Lannot e a) = collect_conses p e) ∧
  (collect_conses p (Letrec funs e) =
     collect_conses_list3 (collect_conses p e) funs) ∧
  (collect_conses_list p [] = p) ∧
  (collect_conses_list p (e::es) =
     collect_conses_list (collect_conses p e) es) ∧
  (collect_conses_list2 p [] = p) ∧
  (collect_conses_list2 p ((v,e)::es) =
     collect_conses_list2 (collect_conses p e) es) ∧
  (collect_conses_list3 p [] = p) ∧
  (collect_conses_list3 p ((v,x,e)::es) =
     collect_conses_list3 (collect_conses p e) es)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                | INL (p,e) => exp_size e
                | INR (INL (p,e)) => list_size exp_size e
                | INR (INR (INL (p,e))) => list_size (exp_size o SND) e
                | INR (INR (INR (p,e))) => list_size (exp_size o SND o SND) e’
  \\ gvs []
  \\ rw[list_size_pair_size_MAP_FST_SND]
End

val pre = cv_trans_pre "" $ measure_args [1,1,1,1] collect_conses_def;

Theorem collect_conses_pre[cv_pre]:
  (∀p v. collect_conses_pre p v) ∧
  (∀p v. collect_conses_list_pre p v) ∧
  (∀p v. collect_conses_list2_pre p v) ∧
  (∀p v. collect_conses_list3_pre p v)
Proof
  ho_match_mp_tac collect_conses_ind \\ rpt strip_tac
  \\ once_rewrite_tac [pre] \\ simp []
QED

Definition do_con_checks_def:
  do_con_checks cenv [] = T ∧
  do_con_checks cenv ((c,n)::rest) =
    case nsLookup cenv c of
    | NONE => F
    | SOME (l,_) => l = n ∧ do_con_checks cenv rest
End

val pre = cv_trans_pre "" do_con_checks_def;
Theorem do_con_checks_pre[cv_pre]:
  ∀cenv v. do_con_checks_pre cenv v
Proof
  Induct_on ‘v’ \\ simp [Once pre]
QED

Triviality collect_conses_acc_lemma:
  (∀(p:((string, string) id # num) list) v q p.
     collect_conses p v = q ⇒
     set p ∪ set (collect_conses [] v) = set q) ∧
  (∀(p:((string, string) id # num) list) v q p.
     collect_conses_list p v = q ⇒
     set p ∪ set (collect_conses_list [] v) = set q) ∧
  (∀(p:((string, string) id # num) list) v q p.
     collect_conses_list2 p v = q ⇒
     set p ∪ set (collect_conses_list2 [] v) = set q) ∧
  (∀(p:((string, string) id # num) list) v q p.
     collect_conses_list3 p v = q ⇒
     set p ∪ set (collect_conses_list3 [] v) = set q)
Proof
  ho_match_mp_tac collect_conses_ind \\ rpt strip_tac
  \\ gvs [collect_conses_def]
  \\ rpt $ pop_assum $ mp_tac o SRULE [Once EQ_SYM_EQ]
  \\ rpt strip_tac
  >~ [‘NONE = _’] >-
   (CASE_TAC \\ gvs []
    \\ gvs [collect_conses_def] \\ rw []
    \\ rpt $ pop_assum $ mp_tac o SRULE [Once EQ_SYM_EQ]
    \\ rpt strip_tac
    \\ once_asm_rewrite_tac []
    \\ simp_tac (srw_ss()) [AC UNION_ASSOC UNION_COMM,EXTENSION]
    \\  metis_tac [])
  \\ once_asm_rewrite_tac []
  \\ once_asm_rewrite_tac []
  \\ once_asm_rewrite_tac []
  \\ simp_tac (srw_ss()) [AC UNION_ASSOC UNION_COMM]
QED

Triviality collect_conses_acc =
  collect_conses_acc_lemma |> SRULE [] |> GSYM;

Theorem do_con_checks_set:
  ∀xs. do_con_checks cenv xs =
       ∀c n. MEM (c,n) xs ⇒ ∃y. nsLookup cenv c = SOME (n,y)
Proof
  Induct \\ gvs [FORALL_PROD,do_con_checks_def,SF DNF_ss]
  \\ rw [] \\ Cases_on ‘nsLookup cenv p_1’ \\ gvs []
  \\ PairCases_on ‘x’ \\ gvs []
QED

Theorem do_con_checks_collect_conses_thm:
  (∀(p:((string, string) id # num) list) v.
     do_con_checks env_c (collect_conses [] v) =
     every_exp (one_con_check env_c) v) ∧
  (∀(p:((string, string) id # num) list) v.
     do_con_checks env_c (collect_conses_list [] v) =
     EVERY (every_exp (one_con_check env_c)) v) ∧
  (∀(p:((string, string) id # num) list) v.
     do_con_checks env_c (collect_conses_list2 [] v) =
     EVERY (λ(x,e). every_exp (one_con_check env_c) e) v) ∧
  (∀(p:((string, string) id # num) list) v.
     do_con_checks env_c (collect_conses_list3 [] v) =
     EVERY (λ(x,y,e). every_exp (one_con_check env_c) e) v)
Proof
  ho_match_mp_tac collect_conses_ind \\ rpt strip_tac
  >~ [‘Con’] >-
   (Cases_on ‘cn’ \\ gvs []
    \\ simp [collect_conses_def,do_con_checks_def,SF ETA_ss,
             semanticPrimitivesTheory.do_con_check_def]
    \\ rpt $ pop_assum mp_tac
    \\ once_rewrite_tac [do_con_checks_set]
    \\ once_rewrite_tac [collect_conses_acc]
    \\ gvs [SF DNF_ss]
    \\ Cases_on ‘nsLookup env_c x’ \\ gvs []
    \\ Cases_on ‘x'’ \\ gvs [] \\ rw [] \\ eq_tac \\ rw [])
  \\ simp [collect_conses_def]
  \\ rpt $ pop_assum mp_tac
  \\ once_rewrite_tac [do_con_checks_set]
  \\ once_rewrite_tac [collect_conses_acc]
  \\ once_rewrite_tac [collect_conses_acc]
  \\ gvs [SF DNF_ss] \\ gvs [SF ETA_ss]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem to_do_con_checks_list3:
  EVERY (λ(f,n,e). every_exp (one_con_check env_c) e) funs =
  do_con_checks env_c (collect_conses_list3 [] funs)
Proof
  gvs [do_con_checks_collect_conses_thm]
QED

Theorem to_do_con_checks:
  every_exp (one_con_check env_c) e =
  do_con_checks env_c (collect_conses [] e)
Proof
  gvs [do_con_checks_collect_conses_thm]
QED

val _ = cv_auto_trans semanticPrimitivesTheory.build_tdefs_def;

val pre = cv_trans_pre "" (evaluate_decTheory.check_cons_dec_list_def
                          |> REWRITE_RULE [to_do_con_checks_list3]
                          |> REWRITE_RULE [to_do_con_checks]);

Theorem evaluate_dec_check_cons_dec_list_pre[cv_pre]:
  (∀env_c v. evaluate_dec_check_cons_dec_list_pre env_c v) ∧
  (∀env_c v. evaluate_dec_check_cons_dec_pre env_c v)
Proof
  ho_match_mp_tac evaluate_decTheory.check_cons_dec_list_ind
  \\ rpt strip_tac \\ simp [Once pre]
QED

val _ = cv_trans (ml_progTheory.prog_syntax_ok_def
                    |> SRULE [ml_progTheory.init_env_def]);

val _ = cv_trans lab_to_targetTheory.lab_inst_def;
val _ = cv_auto_trans lab_to_targetTheory.get_ffi_index_def;
val _ = cv_auto_trans lab_to_targetTheory.find_pos_def;
val _ = cv_auto_trans lab_to_targetTheory.get_label_def;
val _ = cv_trans lab_to_targetTheory.pad_bytes_def;
val _ = cv_auto_trans lab_filterTheory.filter_skip_def;
val _ = cv_auto_trans lab_to_targetTheory.prog_to_bytes_def;
val _ = cv_auto_trans lab_to_targetTheory.zero_labs_acc_exist_def;
val _ = cv_auto_trans lab_to_targetTheory.find_ffi_names_def;
val _ = TypeBase.accessors_of “:lab_to_target$inc_config” |> map cv_trans;
val _ = TypeBase.accessors_of “:environment” |> map cv_trans;
val _ = cv_trans (lab_to_targetTheory.get_memop_info_def
                    |> INST_TYPE [alpha|->“:8”]);

val _ = cv_trans num_list_enc_decTheory.append_rev_def;

Triviality make_cv_term_provable:
  (if n < 30 then x else y) = (if n = 0n then x else if 30 ≤ n then y else x)
Proof
  rw [] \\ gvs []
QED

val pre = cv_trans_pre "" $
  SRULE [make_cv_term_provable] num_list_enc_decTheory.num_to_chars_def;

Theorem num_list_enc_dec_num_to_chars_pre[cv_pre,local]:
  ∀n. num_list_enc_dec_num_to_chars_pre n
Proof
  completeInduct_on ‘n’ \\ simp [Once pre] \\ rw []
  \\ ‘n MOD 30 < 30’ by gs [] \\ decide_tac
QED

val _ = cv_trans num_list_enc_decTheory.rev_nums_to_chars_def;

Triviality spt_enc_def[cv_inline] = num_list_enc_decTheory.spt_enc_def;

val _ = cv_auto_trans backend_enc_decTheory.data_to_word_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.word_to_word_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.word_to_stack_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.stack_to_lab_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.lab_to_target_inc_config_enc_def;
val _ = cv_auto_trans backend_enc_decTheory.presLang_tap_config_enc_def;

(* environment encoding *)

val tms = backend_enc_decTheory.source_to_flat_environment_enc_def
            |> concl |> find_terms (can (match_term “namespace_enc _”)) |> map rand;
val tm1 = el 1 tms;
val tm2 = el 2 tms;

fun spec_namespace_enc' tm1 suffix = let
  val name = "namespace_enc'" ^ suffix
  val name_list = "namespace_enc'" ^ suffix ^ "_list"
  val r = “namespace_enc' ^tm1”
  val r_list = “namespace_enc'_list ^tm1”
  val v = mk_var(name,type_of r)
  val v_list = mk_var(name_list,type_of r_list)
  val tm = num_list_enc_decTheory.namespace_enc'_def
    |> CONJUNCTS |> map (ISPEC tm1 o Q.GEN ‘e’ o SPEC_ALL) |> LIST_CONJ |> SRULE [LET_THM]
    |> concl |> subst [r |-> v, r_list |-> v_list]
  val tac =  WF_REL_TAC ‘measure (λx. case x of
                         | INL x => namespace_size (K 0) (K 0) (K 0) x
                         | INR x => list_size (namespace_size (K 0) (K 0) (K 0)) x)’
  val def = Define [ANTIQUOTE tm]
  val _ = cv_auto_trans def
  val cs = def |> CONJUNCTS |> map (fst o strip_comb o lhs o concl o SPEC_ALL)
  val c = hd cs
  val c_list = last cs
  val goal = mk_conj(mk_eq(r,c),mk_eq(r_list,c_list))
  val res = prove(goal,
                  simp [FUN_EQ_THM]
                  \\ ho_match_mp_tac (fetch "-" (name ^ "_ind"))
                  \\ simp [def,num_list_enc_decTheory.namespace_enc'_def])
  in res end

val res1 = spec_namespace_enc' tm1 "_1";
val res2 = spec_namespace_enc' tm2 "_2";

val _ = cv_trans num_list_enc_decTheory.namespace_depth_def;

val _ = cv_trans (backend_enc_decTheory.source_to_flat_environment_enc_def
                    |> SRULE [res1,res2,num_list_enc_decTheory.namespace_enc_def,
                              num_list_enc_decTheory.prod_enc_def]);

val _ = cv_auto_trans backend_enc_decTheory.source_to_flat_config_enc_def;

(* closLang const encoding *)

val const_exp = backend_enc_decTheory.closLang_const_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val const_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘closLang_const_enc'’);

val name = "const_enc_aux"
val c = “closLang_const_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP closLang_const_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)

Definition const_enc_aux_def:
  ^(LIST_CONJ (CONJUNCTS const_exp @ const_exps |> map SPEC_ALL)
           |> concl |> subst [c|->r,c_list|->r_list])
End

val _ = cv_auto_trans const_enc_aux_def;

Theorem const_enc_aux_thm[cv_inline,local]:
  closLang_const_enc' = const_enc_aux ∧
  MAP closLang_const_enc' = const_enc_aux_list
Proof
  gvs [FUN_EQ_THM] \\ Induct
  \\ gvs [const_enc_aux_def,backend_enc_decTheory.closLang_const_enc'_def,
          num_tree_enc_decTheory.list_enc'_def,SF ETA_ss]
QED

(* bvl_exp encoding *)

val bvl_exp = backend_enc_decTheory.bvl_exp_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val bvl_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘bvl_exp_enc'’);

val name = "bvl_exp_enc_aux"
val c = “bvl_exp_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP bvl_exp_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)

Definition bvl_exp_enc_aux_def:
  ^(LIST_CONJ (CONJUNCTS bvl_exp @ bvl_exps |> map SPEC_ALL)
           |> concl |> subst [c|->r,c_list|->r_list])
End

val _ = cv_auto_trans bvl_exp_enc_aux_def;

Theorem bvl_exp_enc_aux_thm[cv_inline,local]:
  bvl_exp_enc' = bvl_exp_enc_aux ∧
  MAP bvl_exp_enc' = bvl_exp_enc_aux_list
Proof
  gvs [FUN_EQ_THM] \\ Induct
  \\ gvs [bvl_exp_enc_aux_def,backend_enc_decTheory.bvl_exp_enc'_def,
          num_tree_enc_decTheory.list_enc'_def,SF ETA_ss]
QED

val _ = cv_auto_trans backend_enc_decTheory.bvl_to_bvi_config_enc_def;

(* closLang_exp encoding *)

val closLang_exp = backend_enc_decTheory.closLang_exp_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val closLang_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘closLang_exp_enc'’);
val closLang_exps1 = MAP |> CONJUNCTS |> map (Q.ISPEC ‘pair_enc' num_enc' closLang_exp_enc'’);

val name = "closLang_exp_enc_aux"
val c = “closLang_exp_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP closLang_exp_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)
val c_list1 = “MAP $ pair_enc' num_enc' closLang_exp_enc'”
val r_list1 = mk_var(name ^ "_list1",type_of c_list1)

Definition closLang_exp_enc_aux_def:
  ^(CONJUNCTS closLang_exp @ closLang_exps @ closLang_exps1
    |> map (SPEC_ALL o SIMP_RULE bool_ss [FORALL_PROD,
              num_tree_enc_decTheory.pair_enc'_def]) |> LIST_CONJ
    |> concl |> subst [c|->r,c_list|->r_list,c_list1|->r_list1])
End

val pre = cv_auto_trans_pre "" closLang_exp_enc_aux_def;

Theorem closLang_exp_enc_aux_pre[cv_pre,local]:
  (∀v. closLang_exp_enc_aux_pre v) ∧
  (∀v. closLang_exp_enc_aux_list_pre v) ∧
  (∀v. closLang_exp_enc_aux_list1_pre v)
Proof
  ho_match_mp_tac closLang_exp_enc_aux_ind \\ rw [] \\ simp [Once pre]
QED

Theorem closLang_exp_enc_aux_thm[cv_inline,local]:
  closLang_exp_enc' = closLang_exp_enc_aux ∧
  MAP closLang_exp_enc' = closLang_exp_enc_aux_list ∧
  MAP (pair_enc' num_enc' closLang_exp_enc') = closLang_exp_enc_aux_list1
Proof
  gvs [FUN_EQ_THM] \\ ho_match_mp_tac closLang_exp_enc_aux_ind
  \\ gvs [closLang_exp_enc_aux_def,SF ETA_ss,
          backend_enc_decTheory.closLang_exp_enc'_def,
          num_tree_enc_decTheory.pair_enc'_def,
          num_tree_enc_decTheory.list_enc'_def]
QED

(* closLang val_approx encoding *)

val val_approx_exp = backend_enc_decTheory.clos_known_val_approx_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val val_approx_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘clos_known_val_approx_enc'’);

val name = "val_approx_enc_aux"
val c = “clos_known_val_approx_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP clos_known_val_approx_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)

Definition val_approx_enc_aux_def:
  ^(LIST_CONJ (CONJUNCTS val_approx_exp @ val_approx_exps |> map SPEC_ALL)
           |> concl |> subst [c|->r,c_list|->r_list])
End

val _ = cv_auto_trans val_approx_enc_aux_def;

Theorem val_approx_enc_aux_thm[cv_inline,local]:
  clos_known_val_approx_enc' = val_approx_enc_aux ∧
  MAP clos_known_val_approx_enc' = val_approx_enc_aux_list
Proof
  gvs [FUN_EQ_THM] \\ Induct
  \\ gvs [val_approx_enc_aux_def,backend_enc_decTheory.clos_known_val_approx_enc'_def,
          num_tree_enc_decTheory.list_enc'_def,SF ETA_ss]
QED

val _ = cv_auto_trans backend_enc_decTheory.clos_to_bvl_config_enc_def;

val _ = cv_auto_trans backend_enc_decTheory.backend_inc_config_enc_def;
val _ = cv_trans backend_enc_decTheory.encode_backend_config_def;
val _ = cv_auto_trans backend_asmTheory.attach_bitmaps_def;

(* ------------------------------------------------------------------------ *)

val _ = cv_trans stack_to_labTheory.negate_def;
val _ = cv_trans stack_to_labTheory.is_gen_gc_def;
val _ = stack_namesTheory.dest_find_name_def |> cv_trans;
val _ = stack_removeTheory.store_list_def |> cv_trans;
val _ = cv_auto_trans stack_removeTheory.store_pos_def;
val _ = stack_removeTheory.store_length_def |> CONV_RULE (RAND_CONV EVAL) |> cv_trans;
val _ = stack_removeTheory.stub_names_def |> cv_trans;
val _ = cv_trans data_to_wordTheory.shift_length_def;
val _ = cv_trans data_to_wordTheory.small_shift_length_def;
val _ = word_to_stackTheory.insert_bitmap_def |> cv_trans;
val _ = word_to_stackTheory.stack_arg_count_def |> cv_trans;

Definition split_at_pki_def:
  split_at_pki p k [] i acc = k (REVERSE acc) [] ∧
  split_at_pki p k (h::t) i acc =
    if p i h then k (REVERSE acc) (h::t) else
      split_at_pki p k t (i+1:num) (h::acc)
End

Theorem split_at_pki_thm[cv_inline]:
  splitAtPki p k xs = split_at_pki p k (xs:'a list) 0 []
Proof
  qsuff_tac ‘∀(xs:'a list) p k i acc.
               split_at_pki p k xs i acc =
               splitAtPki (λn. p (n + i)) (λx y. k (REVERSE acc ++ x) y) xs’
  >- gvs [SF ETA_ss]
  \\ Induct \\ gvs [split_at_pki_def,listTheory.splitAtPki_def] \\ rw []
  \\ rewrite_tac [GSYM APPEND_ASSOC,APPEND]
  \\ gvs [o_DEF,ADD1]
QED

val _ = cv_auto_trans parmoveTheory.fstep_def;
val _ = cv_trans parmoveTheory.pmov_def;
val _ = cv_auto_trans parmoveTheory.parmove_def;

Definition map_pair_def:
  map_pair f g [] = [] ∧
  map_pair f g ((x,y)::xs) = (f x, g y) :: map_pair f g xs
End

Theorem map_pair_thm[cv_inline]:
  MAP (f ## g) = map_pair f g
Proof
  gvs [FUN_EQ_THM]
  \\ Induct \\ gvs [map_pair_def,FORALL_PROD]
QED

Definition max_var_exp_list_def:
  max_var_exp_list ls = list_max (MAP (λx. max_var_exp x) ls)
End

Triviality max_var_exp_list_thm:
  max_var_exp_list ([]:'a wordLang$exp list) = 0 ∧
  ∀e es:'a wordLang$exp list.
    max_var_exp_list (e::es) = MAX (max_var_exp e) (max_var_exp_list es)
Proof
  gvs [max_var_exp_list_def,list_max_def,MAX_DEF] \\ rw []
QED

Theorem max_var_exp_eq =
  CONJ wordLangTheory.max_var_exp_def max_var_exp_list_thm |> CONJUNCTS
  |> LIST_CONJ |> REWRITE_RULE [GSYM max_var_exp_list_def];

val _ = cv_auto_trans word_allocTheory.every_even_colour_def;
val _ = cv_auto_trans word_allocTheory.total_colour_def;
val _ = cv_trans word_allocTheory.numset_list_insert_def;

Definition check_partial_col'_def:
  check_partial_col' f xs t ft = check_partial_col (total_colour f) xs t ft
End

Definition check_col'_def:
  check_col' f t = check_col (total_colour f) t
End

Definition check_clash_tree'_def:
  check_clash_tree' f x live flive = check_clash_tree (total_colour f) x live flive
End

Definition apply_nummap_key'_def:
  apply_nummap_key' f = apply_nummap_key (total_colour f)
End

Definition apply_colour_imm'_def:
  apply_colour_imm' f = apply_colour_imm (total_colour f)
End

Definition apply_colour_exp'_def:
  apply_colour_exp' f = apply_colour_exp (total_colour f)
End

Definition apply_colour_exp'_list_def:
  apply_colour_exp'_list f = MAP (λx. apply_colour_exp' f x)
End

Definition apply_colour_inst'_def:
  apply_colour_inst' f = apply_colour_inst (total_colour f)
End

Definition apply_colour'_def:
  apply_colour' f = apply_colour (total_colour f)
End

val defs = [GSYM check_partial_col'_def,
            GSYM check_col'_def,
            GSYM check_clash_tree'_def,
            GSYM apply_nummap_key'_def,
            GSYM apply_colour_imm'_def,
            GSYM apply_colour_exp'_def,
            GSYM apply_colour_exp'_list_def,
            GSYM apply_colour_exp'_list_def |> SRULE [SF ETA_ss],
            GSYM apply_colour_inst'_def,
            GSYM apply_colour'_def]

val tm = “total_colour colour”
val f = mk_var("f",type_of tm)
fun set_f th = th |> CONJUNCTS
                  |> map (INST [f|->tm] o SPEC_ALL)
                  |> LIST_CONJ |> REWRITE_RULE defs

Theorem check_partial_col'_eq = reg_allocTheory.check_partial_col_def |> set_f
Theorem check_col'_eq = reg_allocTheory.check_col_def |> set_f
Theorem check_clash_tree'_eq = reg_allocTheory.check_clash_tree_def |> set_f
Theorem apply_colour'_eq = word_allocTheory.apply_colour_def |> set_f
Theorem apply_colour_inst'_eq = word_allocTheory.apply_colour_inst_def |> set_f
Theorem apply_colour_imm'_eq = word_allocTheory.apply_colour_imm_def |> set_f
Theorem apply_colour_nummap_key'_eq = word_allocTheory.apply_nummap_key_def |> set_f
Theorem apply_colour_exp'_eq =
  (CONJUNCTS word_allocTheory.apply_colour_exp_def @
   map (Q.ISPEC ‘apply_colour_exp' f’) (CONJUNCTS MAP))
  |> LIST_CONJ |> set_f

val new_P = “λn. m ≤ n:num”
val P = mk_var("P",type_of new_P)

Definition every_stack_var'_def:
  every_stack_var' m = every_stack_var ^new_P
End

Definition every_name'_def:
  every_name' m = every_name ^new_P
End

val P_defs = [GSYM every_stack_var'_def, GSYM every_name'_def]

fun set_P th = th |> CONJUNCTS
                  |> map (INST [P|->new_P] o SPEC_ALL)
                  |> LIST_CONJ |> PURE_REWRITE_RULE P_defs

Theorem every_stack_var'_eq = wordLangTheory.every_stack_var_def |> set_P;
Theorem every_name'_eq = wordLangTheory.every_name_def |> set_P;

Theorem oracle_colour_ok_eq = word_allocTheory.oracle_colour_ok_def
                                |> SRULE [Once LET_THM,GREATER_EQ]
                                |> REWRITE_RULE (defs @ P_defs);

val _ = every_name'_eq |> cv_auto_trans;

val _ = check_col'_eq |> cv_auto_trans;

val pre = check_partial_col'_eq |> cv_trans_pre "";
Theorem check_partial_col'_pre[cv_pre]:
  ∀colour v t ft. check_partial_col'_pre colour v t ft
Proof
  Induct_on ‘v’ \\ rw [] \\ simp [Once pre]
QED

val pre = check_clash_tree'_eq |> cv_auto_trans_pre "";
Theorem check_clash_tree'_pre[cv_pre]:
  ∀colour v live flive. check_clash_tree'_pre colour v live flive
Proof
  Induct_on ‘v’ \\ rw [] \\ simp [Once pre]
QED

val _ = cv_auto_trans apply_colour_nummap_key'_eq;

Definition get_reads_exp_list_def:
  get_reads_exp_list xs = FLAT (MAP (λa. get_reads_exp a) xs)
End

Triviality get_reads_exp_list_thm:
  get_reads_exp_list ([]:'a wordLang$exp list) = [] ∧
  ∀x xs:'a wordLang$exp list.
    get_reads_exp_list (x::xs) = get_reads_exp x ++ get_reads_exp_list xs
Proof
  gvs [get_reads_exp_list_def]
QED

Theorem get_reads_exp_eq =
  CONJUNCTS (SRULE [GSYM get_reads_exp_list_def] word_allocTheory.get_reads_exp_def)
  @ CONJUNCTS get_reads_exp_list_thm |> LIST_CONJ;


Definition get_live_exps_def:
  get_live_exps ls = big_union (MAP (λa. get_live_exp a) ls)
End

Triviality get_live_exps_thm:
  get_live_exps ([]:'a wordLang$exp list) = LN ∧
  get_live_exps (x::xs:'a wordLang$exp list) = union (get_live_exp x) (get_live_exps xs)
Proof
  gvs [get_live_exps_def,word_allocTheory.big_union_def]
QED

Triviality get_live_exp_eq =
  CONJUNCTS word_allocTheory.get_live_exp_def
  @ CONJUNCTS get_live_exps_thm |> map GEN_ALL
  |> LIST_CONJ |> SRULE [GSYM get_live_exps_def];

val pre = cv_trans_pre "" get_live_exp_eq

Theorem word_alloc_get_live_exp_pre[cv_pre]:
  (∀v:'a wordLang$exp. word_alloc_get_live_exp_pre v) ∧
  (∀v:'a wordLang$exp list. get_live_exps_pre v)
Proof
  ho_match_mp_tac wordLangTheory.exp_induction \\ rw [] \\ simp [Once pre]
QED

val _ = cv_trans word_instTheory.is_Lookup_CurrHeap_def;
val _ = cv_trans word_instTheory.pull_ops_def;

Definition pull_exp_list_def:
  pull_exp_list ls = MAP (λa. pull_exp a) ls
End

Triviality pull_exp_list_thm:
  pull_exp_list ([]:'a wordLang$exp list) = [] ∧
  ∀x xs:'a wordLang$exp list.
    pull_exp_list (x::xs) = pull_exp x :: pull_exp_list xs
Proof
  gvs [pull_exp_list_def]
QED

Theorem pull_exp_eq =
  CONJUNCTS (CONJ word_instTheory.pull_exp_def pull_exp_list_thm) |> LIST_CONJ
  |> REWRITE_RULE [GSYM pull_exp_list_def]

Definition flatten_exp_list_def:
  flatten_exp_list ls = MAP (λa. flatten_exp a) ls
End

Triviality flatten_exp_list_thm:
  flatten_exp_list ([]:'a wordLang$exp list) = [] ∧
  ∀x xs:'a wordLang$exp list.
    flatten_exp_list (x::xs) = flatten_exp x :: flatten_exp_list xs
Proof
  gvs [flatten_exp_list_def]
QED

Theorem flatten_exp_eq =
  CONJUNCTS (CONJ word_instTheory.flatten_exp_def flatten_exp_list_thm) |> LIST_CONJ
  |> REWRITE_RULE [GSYM flatten_exp_list_def]

val _ = word_cseTheory.empty_data_def |> CONV_RULE (RAND_CONV EVAL) |> cv_trans;
val _ = cv_auto_trans word_cseTheory.is_seen_def;
val _ = cv_auto_trans word_cseTheory.canonicalMoveRegs3_def;

Definition lookup_listCmp_def:
  lookup_listCmp = lookup listCmp
End

val _ = cv_trans (word_cseTheory.listCmp_def |> SRULE [GREATER_DEF]);

val lookup_listCmp_eq =
  balanced_mapTheory.lookup_def |> CONJUNCTS |> map (ISPEC “listCmp”) |> LIST_CONJ
    |> REWRITE_RULE [GSYM lookup_listCmp_def];

val pre = cv_trans_pre "" lookup_listCmp_eq;
Theorem lookup_listCmp_pre[cv_pre]:
  ∀k v. lookup_listCmp_pre k v
Proof
  Induct_on ‘v’ \\ gvs [] \\ simp [Once pre]
QED

Definition insert_listCmp_def:
  insert_listCmp = insert listCmp
End

val insert_listCmp_eq =
  balanced_mapTheory.insert_def |> CONJUNCTS |> map (ISPEC “listCmp”) |> LIST_CONJ
    |> REWRITE_RULE [GSYM insert_listCmp_def,balanced_mapTheory.singleton_def];

val fix = REWRITE_RULE [balanced_mapTheory.ratio_def,
                        balanced_mapTheory.delta_def,
                        GREATER_DEF]

val _ = balanced_mapTheory.size_def |> cv_trans;
val _ = balanced_mapTheory.balanceR_def |> oneline |> fix |> cv_trans;
val _ = balanced_mapTheory.balanceL_def |> oneline |> fix |> cv_trans;

val pre = insert_listCmp_eq |> cv_trans_pre "";
Theorem insert_listCmp_pre[cv_pre]:
  ∀k v t. insert_listCmp_pre k v t
Proof
  Induct_on ‘t’ \\ simp [Once pre]
QED

val _ = word_cseTheory.arithOpToNum_def |> cv_trans;
val _ = word_cseTheory.shiftToNum_def |> cv_trans;
val _ = word_cseTheory.fpToNumList_def |> cv_trans;
val _ = cv_trans word_cseTheory.firstRegOfArith_def;
val _ = cv_trans word_cseTheory.canonicalRegs'_def;
val _ = cv_trans word_cseTheory.canonicalImmReg'_def;
val _ = cv_trans word_cseTheory.canonicalImmReg_def;
val _ = cv_trans word_cseTheory.canonicalArith_def;
val _ = cv_trans word_cseTheory.are_reads_seen_def;
val _ = cv_trans word_cseTheory.is_complex_def;
val _ = cv_trans word_cseTheory.is_store_def;
val _ = cv_trans word_cseTheory.canonicalExp_def;
val _ = cv_trans word_cseTheory.OpCurrHeapToNumList_def;

val _ = word_allocTheory.next_var_rename_def |> cv_trans;
val _ = word_allocTheory.list_next_var_rename_def |> cv_trans;
val _ = word_allocTheory.even_list_def |> cv_auto_trans;
val _ = word_allocTheory.option_lookup_def |> cv_trans;

Definition ssa_cc_trans_exp_list_def:
  ssa_cc_trans_exp_list t =  MAP (λa. ssa_cc_trans_exp t a)
End

Triviality list_thm:
  (∀t. ssa_cc_trans_exp_list t ([]:'a wordLang$exp list) = []) ∧
  ∀x (xs:'a wordLang$exp list) t.
    ssa_cc_trans_exp_list t (x::xs) = ssa_cc_trans_exp t x :: ssa_cc_trans_exp_list t xs
Proof
  gvs [ssa_cc_trans_exp_list_def]
QED

Theorem ssa_cc_trans_exp_eq =
  CONJUNCTS (CONJ word_allocTheory.ssa_cc_trans_exp_def list_thm) |> LIST_CONJ
  |> SRULE [GSYM ssa_cc_trans_exp_list_def];

Definition const_fp_exp_list_def:
  const_fp_exp_list ls cs = MAP (λa. const_fp_exp a cs) ls
End

Triviality list_thm:
  (∀cs. const_fp_exp_list ([]:'a wordLang$exp list) cs = []) ∧
  ∀x (xs:'a wordLang$exp list) cs.
    const_fp_exp_list (x::xs) cs = const_fp_exp x cs :: const_fp_exp_list xs cs
Proof
  gvs [const_fp_exp_list_def]
QED

Theorem const_fp_exp_eq =
  CONJUNCTS (CONJ word_simpTheory.const_fp_exp_def list_thm) |> LIST_CONJ
  |> SRULE [GSYM const_fp_exp_list_def];

val _ = word_simpTheory.dest_If_def |> cv_trans;
val _ = word_simpTheory.dest_If_Eq_Imm_def |> cv_trans;
val _ = word_simpTheory.dest_Seq_def |> cv_trans;
val _ = word_simpTheory.dest_Seq_Assign_Const_def |> cv_trans;
val _ = word_simpTheory.const_fp_move_cs_def |> cv_trans;

val pre = cv_trans_pre "" word_simpTheory.push_out_if_aux_def;

Theorem word_simp_push_out_if_aux_pre[cv_pre]:
  ∀p. word_simp_push_out_if_aux_pre p
Proof
  ho_match_mp_tac word_simpTheory.push_out_if_aux_ind>>
  rw[]>>simp[Once pre]
QED
val _ = word_simpTheory.push_out_if_def |> cv_trans;

val _ = cv_trans word_to_wordTheory.next_n_oracle_def;

Definition adjust_vars_def:
  adjust_vars [] = [] ∧
  adjust_vars (x::xs) = adjust_var x :: adjust_vars xs
End

Theorem to_adjust_vars:
  MAP adjust_var = adjust_vars
Proof
  gvs [FUN_EQ_THM] \\ Induct \\ gvs [adjust_vars_def]
QED

val _ = cv_trans data_to_wordTheory.adjust_var_def;
val _ = cv_trans adjust_vars_def;
val _ = cv_auto_trans data_to_wordTheory.adjust_set_def;
val _ = cv_trans data_to_wordTheory.get_names_def;
val _ = cv_trans data_to_wordTheory.lookup_word_op_def;
val _ = cv_trans data_to_wordTheory.fp_cmp_inst_def;
val _ = cv_trans data_to_wordTheory.fp_top_inst_def;
val _ = cv_trans data_to_wordTheory.fp_bop_inst_def;
val _ = cv_trans data_to_wordTheory.fp_uop_inst_def;
val _ = bitTheory.SLICE_def |> SRULE [bitTheory.MOD_2EXP_def] |> cv_trans;

Definition get_words_def:
  get_words [] = [] ∧
  get_words ((_,Word w) :: ws) = w :: get_words ws ∧
  get_words (_ :: ws) = 0w :: get_words ws
End

Theorem to_get_words:
  MAP (get_Word ∘ SND) ws = get_words ws
Proof
  Induct_on ‘ws’ \\ gvs [get_words_def,FORALL_PROD]
  \\ gen_tac \\ Cases \\ gvs [get_words_def]
QED

Definition map_compile_part_def:
  map_compile_part c [] = [] ∧
  map_compile_part c (p::ps) = data_to_word$compile_part c p :: map_compile_part c ps
End

Theorem to_map_compile_part:
  ∀ps. MAP (compile_part c) ps = map_compile_part c ps
Proof
  Induct \\ gvs [map_compile_part_def]
QED

val _ = word_allocTheory.get_coalescecost_def |> cv_trans;
val _ = word_allocTheory.get_spillcost_def |> cv_trans;
val _ = word_allocTheory.canonize_moves_aux_def |> cv_trans;
val _ = word_allocTheory.heu_max_all_def |> cv_auto_trans;
val _ = word_allocTheory.heu_merge_call_def |> cv_trans;

val tm = word_allocTheory.canonize_moves_def
           |> concl |> find_term (can (match_term “sort _”)) |> rand;

Definition sort_canonize_def:
  sort_canonize ls =
    sort ^tm ls
End

Definition merge_tail_canonize_def:
  merge_tail_canonize b ls accl accr =
    merge_tail b ^tm ls accl accr
End

val merge_tail_eq = merge_tail_def
            |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
            |> Q.GEN ‘R’ |> ISPEC tm |> SRULE [GSYM merge_tail_canonize_def]
            |> GEN_ALL |> SRULE [FORALL_PROD] |> SPEC_ALL

val pre = cv_trans_pre "" merge_tail_eq;

Theorem merge_tail_canonize_pre[cv_pre]:
  ∀negate v0 v acc. merge_tail_canonize_pre negate v0 v acc
Proof
  Induct_on`v` \\ rw[]
  >- simp[Once pre]
  \\ qid_spec_tac`acc`
  \\ Induct_on`v0` \\ rw[]
  >- simp[Once pre]
  \\ simp[Once pre]
  \\ rw[]
  \\ metis_tac[]
QED

Definition mergesortN_tail_canonize_def:
  mergesortN_tail_canonize b n ls =
    mergesortN_tail b ^tm n ls
End

val mergesortN_tail_eq = mergesortN_tail_def
            |> CONJUNCTS |> map SPEC_ALL |> LIST_CONJ
            |> Q.GEN ‘R’ |> ISPEC tm |> SRULE [GSYM mergesortN_tail_canonize_def, GSYM merge_tail_canonize_def]
            |> GEN_ALL |> SRULE [FORALL_PROD] |> SPEC_ALL;

Triviality c2b_b2c:
  cv$c2b (b2c b) = b
Proof
  fs[cvTheory.b2c_if,cvTheory.c2b_def]
  \\ rw[]
QED

val _ = cv_trans DIV2_def;

val pre = cv_auto_trans_pre_rec "" mergesortN_tail_eq
  (WF_REL_TAC ‘measure (cv_size o FST o SND)’ \\ rw []
   \\ rename1`_ < cv_size cvv`
   \\ Cases_on`cvv`
   \\ simp[GSYM (fetch "-" "cv_arithmetic_DIV2_thm")]
   \\ rw[DIV2_def]
   \\ cv_termination_tac
   \\ fs[c2b_b2c]
   \\ intLib.ARITH_TAC);

Theorem mergesortN_tail_canonize_pre[cv_pre]:
  ∀negate n l. mergesortN_tail_canonize_pre negate n l
Proof
  completeInduct_on`n`>>
  rw[Once pre,DIV2_def]>>
  first_x_assum irule>>
  intLib.ARITH_TAC
QED

val pre = cv_auto_trans (sort_canonize_def |> SRULE [sort_def,mergesort_tail_def,GSYM mergesortN_tail_canonize_def]);

val res = word_allocTheory.canonize_moves_def |> SRULE[GSYM sort_canonize_def] |> cv_auto_trans

val _ = cv_trans backendTheory.inc_set_oracle_def;

val _ = cv_trans (exportTheory.escape_sym_char_def |> SRULE [GREATER_EQ]);
val _ = cv_auto_trans exportTheory.emit_symbol_def;
val _ = cv_auto_trans exportTheory.emit_symbols_def;
val _ = cv_auto_trans (exportTheory.data_section_def |> SRULE [GSYM mlstringTheory.implode_def]);
val _ = cv_trans (exportTheory.data_buffer_def |> SRULE []);
val _ = cv_trans (exportTheory.code_buffer_def |> SRULE []);

Triviality eq_toChar:
  ∀n. n < 16 ⇒ EL n "0123456789ABCDEF" = toChar n
Proof
  Cases \\ gvs [] \\ EVAL_TAC
  \\ ntac 10 (Cases_on ‘n'’ \\ gvs [] \\ Cases_on ‘n’ \\ gvs [])
QED

Theorem byte_to_string_eq_toChar_toChar:
  byte_to_string b =
    strlit (STRING #"0" (STRING #"x" (STRING (toChar (w2n b DIV 16))
                                     (STRING (toChar (w2n b MOD 16)) []))))
Proof
  simp [exportTheory.byte_to_string_def]
  \\ DEP_REWRITE_TAC [eq_toChar]
  \\ gvs [DIV_LT_X]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ gvs []
QED

val pre = cv_trans_pre "" byte_to_string_eq_toChar_toChar;
Theorem export_byte_to_string_pre[cv_pre]:
  ∀b. export_byte_to_string_pre b
Proof
  simp [pre] \\ gen_tac
  \\ rpt $ irule_at Any basis_cvTheory.IMP_toChar_pre \\ gvs []
  \\ gvs [DIV_LT_X]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ gvs []
QED

val _ = cv_trans exportTheory.preamble_def

Definition chunks16_def:
  chunks16 f xs =
    case xs of
      [] => Nil
    | (x0::x1::x2::x3::x4::x5::x6::x7::
       x8::x9::x10::x11::x12::x13::x14::x15::ys) =>
         SmartAppend
           (f [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15])
           (chunks16 f ys)
    | other => f other
End

Theorem split16_eq_chunks16:
  ∀f xs. split16 f xs = chunks16 f xs
Proof
  rpt gen_tac
  \\ completeInduct_on ‘LENGTH xs’
  \\ rw [] \\ gvs [PULL_FORALL]
  \\ simp [Once chunks16_def]
  \\ every_case_tac \\ gvs []
  \\ simp [Once split16_def]
  \\ simp [Once chunks16_def,SmartAppend_Nil]
QED

Definition comma_cat_byte_to_string_def:
  comma_cat_byte_to_string x =
   case x of
     [] => [newl_strlit]
   | [x] => [byte_to_string x; newl_strlit]
   | (x::xs) => byte_to_string x::comm_strlit::comma_cat_byte_to_string xs
End

Definition comma_cat_word_to_string_def:
  comma_cat_word_to_string x =
   case x of
     [] => [newl_strlit]
   | [x] => [word_to_string x; newl_strlit]
   | (x::xs) => word_to_string x::comm_strlit::comma_cat_word_to_string xs
End

val _ = cv_trans word_to_string_def;
val _ = cv_trans newl_strlit_def;
val _ = cv_trans comm_strlit_def;
val _ = cv_trans comma_cat_byte_to_string_def;
val _ = cv_trans comma_cat_word_to_string_def;

Theorem to_comma_cat_byte_to_string:
  ∀xs. comma_cat byte_to_string xs =
       comma_cat_byte_to_string xs
Proof
  ho_match_mp_tac comma_cat_byte_to_string_ind
  \\ rw []
  \\ simp [Once comma_cat_def, Once comma_cat_byte_to_string_def]
  \\ Cases_on ‘xs’ \\ gvs []
  \\ Cases_on ‘t’ \\ gvs []
QED

Theorem to_comma_cat_word_to_string:
  ∀xs. comma_cat word_to_string xs =
       comma_cat_word_to_string xs
Proof
  ho_match_mp_tac comma_cat_word_to_string_ind
  \\ rw []
  \\ simp [Once comma_cat_def, Once comma_cat_word_to_string_def]
  \\ Cases_on ‘xs’ \\ gvs []
  \\ Cases_on ‘t’ \\ gvs []
QED

Definition words_line_byte_def:
  words_line_byte word_directive ls =
    List (word_directive :: comma_cat_byte_to_string ls)
End

Definition words_line_word_def:
  words_line_word word_directive ls =
    List (word_directive :: comma_cat_word_to_string ls)
End

val _ = cv_trans words_line_byte_def;
val _ = cv_trans words_line_word_def;

Theorem to_words_line_byte:
  words_line wd byte_to_string = words_line_byte wd
Proof
  gvs [FUN_EQ_THM,words_line_byte_def,
       to_comma_cat_byte_to_string,words_line_def]
QED

Theorem to_words_line_word:
  words_line wd word_to_string = words_line_word wd
Proof
  gvs [FUN_EQ_THM,words_line_word_def,
       to_comma_cat_word_to_string,words_line_def]
QED

val _ = cv_trans word_unreachTheory.dest_Seq_Move_def;
val _ = cv_auto_trans word_unreachTheory.merge_moves_def;
val _ = cv_trans word_unreachTheory.SimpSeq_def;
val _ = cv_trans word_unreachTheory.Seq_assoc_right_def;
val _ = cv_trans word_unreachTheory.remove_unreach_def;

val pre = cv_auto_trans_pre "" word_copyTheory.copy_prop_prog_def;

Theorem word_copy_copy_prop_prog_pre[cv_pre]:
  ∀v cs. word_copy_copy_prop_prog_pre v cs
Proof
  ho_match_mp_tac word_copyTheory.copy_prop_prog_ind >>
  rw[]>>
  simp[Once pre]
QED

val _ = cv_trans word_copyTheory.copy_prop_def;

val _ = cv_auto_trans backend_passesTheory.any_prog_pp_def;

val _ = Feedback.set_trace "TheoryPP.include_docs" 0;

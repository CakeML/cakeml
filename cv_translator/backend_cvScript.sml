(*
  Translate non-target-specific backend functions to cv equations.
*)
open preamble cv_transLib cv_stdTheory;
open backendTheory;

val _ = new_theory "backend_cv";

val _ = cv_trans sptreeTheory.fromAList_def;

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

val _ = cv_trans num_list_enc_decTheory.append_rev_def;

Triviality make_cv_term_provable:
  (if n < 30 then x else y) = (if n = 0n then x else if 30 ≤ n then y else x)
Proof
  rw [] \\ gvs []
QED

val pre = cv_trans_pre $
  SRULE [make_cv_term_provable] num_list_enc_decTheory.num_to_chars_def;

Theorem num_to_chars_pre[cv_pre,local]:
  ∀n. num_to_chars_pre n
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
val _ = cv_auto_trans backend_enc_decTheory.tap_config_enc_def;

(* environment encoding *)

val tms = backend_enc_decTheory.environment_enc_def
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
                         | INR x => namespace1_size (K 0) (K 0) (K 0) x)’
  val def = tDefine name [ANTIQUOTE tm] tac
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

val _ = cv_trans (backend_enc_decTheory.environment_enc_def
                    |> SRULE [res1,res2,num_list_enc_decTheory.namespace_enc_def,
                              num_list_enc_decTheory.prod_enc_def]);

val _ = cv_auto_trans backend_enc_decTheory.source_to_flat_config_enc_def;

(* closLang const encoding *)

val const_exp = backend_enc_decTheory.const_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val const_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘const_enc'’);

val name = "const_enc_aux"
val c = “const_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP const_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)

Definition const_enc_aux_def:
  ^(LIST_CONJ (CONJUNCTS const_exp @ const_exps |> map SPEC_ALL)
           |> concl |> subst [c|->r,c_list|->r_list])
End

val _ = cv_auto_trans const_enc_aux_def;

Theorem const_enc_aux_thm[cv_inline,local]:
  const_enc' = const_enc_aux ∧
  MAP const_enc' = const_enc_aux_list
Proof
  gvs [FUN_EQ_THM] \\ Induct
  \\ gvs [const_enc_aux_def,backend_enc_decTheory.const_enc'_def,
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
Termination
  WF_REL_TAC ‘measure $ λx. case x of
              | INL x => closLang$exp_size x
              | INR (INL xs) => list_size closLang$exp_size xs
              | INR (INR ys) => list_size (pair_size (λx.x) closLang$exp_size) ys’
  \\ gvs [closLangTheory.exp_size_eq]
End

val pre = cv_auto_trans_pre closLang_exp_enc_aux_def;

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

val val_approx_exp = backend_enc_decTheory.val_approx_enc'_def
                |> SRULE [SF ETA_ss, num_tree_enc_decTheory.list_enc'_def];
val val_approx_exps = MAP |> CONJUNCTS |> map (Q.ISPEC ‘val_approx_enc'’);

val name = "val_approx_enc_aux"
val c = “val_approx_enc'”
val r = mk_var(name,type_of c)
val c_list = “MAP val_approx_enc'”
val r_list = mk_var(name ^ "_list",type_of c_list)

Definition val_approx_enc_aux_def:
  ^(LIST_CONJ (CONJUNCTS val_approx_exp @ val_approx_exps |> map SPEC_ALL)
           |> concl |> subst [c|->r,c_list|->r_list])
End

val _ = cv_auto_trans val_approx_enc_aux_def;

Theorem val_approx_enc_aux_thm[cv_inline,local]:
  val_approx_enc' = val_approx_enc_aux ∧
  MAP val_approx_enc' = val_approx_enc_aux_list
Proof
  gvs [FUN_EQ_THM] \\ Induct
  \\ gvs [val_approx_enc_aux_def,backend_enc_decTheory.val_approx_enc'_def,
          num_tree_enc_decTheory.list_enc'_def,SF ETA_ss]
QED

val _ = cv_auto_trans backend_enc_decTheory.clos_to_bvl_config_enc_def;

val _ = cv_auto_trans backend_enc_decTheory.inc_config_enc_def;
val _ = cv_trans backend_enc_decTheory.encode_backend_config_def;
val _ = cv_auto_trans backend_asmTheory.attach_bitmaps_def;

(* ------------------------------------------------------------------------ *)

val _ = cv_trans miscTheory.append_aux_def;
val _ = cv_trans miscTheory.append_def;
val _ = cv_trans miscTheory.tlookup_def;
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

Definition max_var_word_exp_def:
  max_var_word_exp (wordLang$Var n) = n ∧
  max_var_word_exp (Load e) = max_var_word_exp e ∧
  max_var_word_exp (Shift _ e _) = max_var_word_exp e ∧
  max_var_word_exp (Op _ xs) = max_var_word_exp_list xs ∧
  max_var_word_exp _ = 0 ∧
  max_var_word_exp_list [] = 0 ∧
  max_var_word_exp_list (e::es) = MAX (max_var_word_exp e) (max_var_word_exp_list es)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
              | INL e => exp_size (K 0) e
              | INR es => list_size (exp_size (K 0)) es’
End

Theorem max_var_word_exp_thm[cv_inline]:
  (∀e:'a exp. max_var_exp e = max_var_word_exp e) ∧
  (∀es:'a exp list. list_max (MAP max_var_exp es) = max_var_word_exp_list es)
Proof
  ho_match_mp_tac max_var_word_exp_ind
  \\ rw [] \\ gvs [wordLangTheory.max_var_exp_def,max_var_word_exp_def,SF ETA_ss]
  \\ gvs [list_max_def] \\ rw [] \\ gvs [MAX_DEF]
QED

val _ = export_theory();

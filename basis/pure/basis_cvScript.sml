(*
  Translation of basis types and functions for use with cv_compute.
*)
Theory basis_cv[no_sig_docs]
Ancestors
  mlsexp cv_std
Libs
  preamble cv_transLib

val _ = cv_memLib.use_long_names := true;

Theorem list_mem[local,cv_inline] = listTheory.MEM;

val _ = cv_trans sptreeTheory.fromAList_def;
val _ = cv_trans miscTheory.SmartAppend_def;
val _ = cv_trans miscTheory.append_aux_def;
val _ = cv_trans miscTheory.append_def;
val _ = cv_trans miscTheory.tlookup_def;
val _ = cv_trans mlstringTheory.implode_def;
val _ = cv_trans mlstringTheory.explode_thm;
val _ = cv_trans mlstringTheory.strcat_thm;
val _ = cv_trans mlstringTheory.str_def;
val _ = cv_auto_trans mlstringTheory.concat_def;
val _ = cv_trans rich_listTheory.MAX_LIST_def;
val _ = cv_trans (miscTheory.max3_def |> PURE_REWRITE_RULE [GREATER_DEF]);

val toChar_pre = cv_trans_pre "mlint_toChar_pre" mlintTheory.toChar_def
val num_to_chars_pre = cv_auto_trans_pre "mlint_num_to_chars_pre" mlintTheory.num_to_chars_def;

Theorem IMP_toChar_pre:
  n < 16 ⇒ mlint_toChar_pre n
Proof
  gvs [toChar_pre]
QED

Theorem num_to_chars_pre[cv_pre,local]:
  ∀a0 a1 a2 a3. mlint_num_to_chars_pre a0 a1 a2 a3
Proof
  ho_match_mp_tac mlintTheory.num_to_chars_ind \\ rw []
  \\ rw [] \\ simp [Once num_to_chars_pre]
  \\ once_rewrite_tac [toChar_pre] \\ gvs [] \\ rw []
  \\ ‘k MOD 10 < 10’ by gvs [] \\ simp []
QED

Theorem Num_ABS[local]:
  Num (ABS i) = Num i
Proof
  Cases_on ‘i’ \\ gvs []
QED

val _ = cv_trans (mlintTheory.toString_def |> SRULE [Num_ABS]);
val _ = cv_trans mlintTheory.num_to_str_def;

val _ = cv_auto_trans (mlsexpTheory.smart_remove_def |> SRULE [GSYM GREATER_DEF]);
val _ = cv_auto_trans mlsexpTheory.v2pretty_def;
val _ = cv_auto_trans mlsexpTheory.str_tree_to_strs_def;

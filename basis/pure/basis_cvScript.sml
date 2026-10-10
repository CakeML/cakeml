(*
  Translation of basis types and functions for use with cv_compute.
*)
Theory basis_cv[no_sig_docs]
Ancestors
  mlsexp cv_std ast_cv
Libs
  preamble cv_transLib

val _ = cv_memLib.use_long_names := true;

Theorem list_mem[local,cv_inline] = listTheory.MEM;

val _ = cv_trans sptreeTheory.fromAList_def;
val _ = cv_trans miscTheory.SmartAppend_def;
val _ = cv_trans miscTheory.append_aux_def;
val _ = cv_trans miscTheory.append_def;
val _ = cv_trans miscTheory.tlookup_def;

val _ = cv_trans mlstringTheory.explode_thm;
val _ = cv_trans mlstringTheory.strcat_thm;
val _ = cv_trans mlstringTheory.chr_to_str_def;
val _ = cv_auto_trans mlstringTheory.concat_def;

val res = cv_trans_pre "strsub_pre" mlstringTheory.strsub_def;

Theorem strsub_pre[cv_pre]:
  ∀v n. strsub_pre v n ⇔ n < strlen v
Proof
  Cases \\ simp [Once res, mlstringTheory.strlen_def]
QED

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

(* mlsexp *********************************************************************)

val _ = cv_auto_trans (mlsexpTheory.smart_remove_def |> SRULE [GSYM GREATER_DEF]);
val _ = cv_auto_trans mlsexpTheory.v2pretty_def;
val _ = cv_auto_trans mlsexpTheory.str_tree_to_strs_def;

Definition str_every_is_safe_char_def:
  str_every_is_safe_char n s =
    if n = 0 then T else
      is_safe_char (strsub s (n-1)) ∧
      str_every_is_safe_char (n-1:num) s
End

Theorem str_every_is_safe_char_eq[local]:
  ∀n s. str_every is_safe_char n s ⇔ str_every_is_safe_char n s
Proof
  Induct
  >> once_rewrite_tac [str_every_is_safe_char_def, str_every_def]
  >> simp[]
QED

val str_every_is_safe_char_pre_def =
  cv_auto_trans_pre
    "str_every_is_safe_char_pre"
    str_every_is_safe_char_def

Theorem str_every_is_safe_char_pre[cv_pre,local]:
  ∀n s. str_every_is_safe_char_pre n s ⇔ n ≤ strlen s
Proof
  Induct >> simp [Once str_every_is_safe_char_pre_def]
QED

val r =
  cv_auto_trans
    (mlsexpTheory.make_str_safe_def |> REWRITE_RULE [str_every_is_safe_char_eq])

val r = cv_trans mlsexpTheory.sexp_to_app_list_def
val r = cv_auto_trans mlsexpTheory.sexp_to_string_def

(* ast_sexp *******************************************************************)

val r = cv_auto_trans ast_sexpTheory.from_ast_t_def
val r = cv_auto_trans ast_sexpTheory.from_pat_def

val from_exp_pre_def =
  cv_auto_trans_pre
    "from_exp_pre from_exps_pre from_pes_pre from_funs_pre"
    ast_sexpTheory.from_exp_def

Theorem from_exp_pre[cv_pre,local]:
  (∀v. from_exp_pre v) ∧
  (∀v. from_exps_pre v) ∧
  (∀v. from_pes_pre v) ∧
  (∀v. from_funs_pre v)
Proof
  ho_match_mp_tac ast_sexpTheory.from_exp_ind
  >> rw []
  >> simp [Once from_exp_pre_def]
QED

val r = cv_auto_trans ast_sexpTheory.from_dec_def
val r = cv_auto_trans ast_sexpTheory.from_dec_list_def

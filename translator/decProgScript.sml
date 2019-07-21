(*
  Translation of CakeML source AST
*)

open preamble astTheory semanticPrimitivesTheory;
open terminationTheory ml_translatorLib ml_translatorTheory ml_progLib;

val _ = new_theory "decProg";

val _ = use_string_type true;

val _ = register_type ``:'a list``;
val _ = register_type ``:'a option``;
val _ = register_type ``:lit``;
val _ = register_type ``:('a,'b) id``;
val _ = register_type ``:ast_t``;
val _ = register_type ``:pat``;
val _ = register_type ``:lop``;
val _ = register_type ``:opn``;
val _ = register_type ``:opb``;
val _ = register_type ``:opw``;
val _ = register_type ``:shift``;
val _ = register_type ``:word_size``;
val _ = register_type ``:fp_uop``;
val _ = register_type ``:fp_bop``;
val _ = register_type ``:fp_top``;
val _ = register_type ``:fp_cmp``;
val _ = register_type ``:op``;
val _ = register_type ``:locn``;
val _ = register_type ``:locs``;
val _ = register_type ``:exp``;
val _ = register_type ``:dec``;

fun my_fetch name = fetch "-" name |> SIMP_RULE (srw_ss())
  [HOL_STRING_TYPE_def, NUM_def, INT_def, STRING_TYPE_def,
   mlstringTheory.implode_def, WORD_def, HOL_STRING_TYPE_def,
   CHAR_def, STRING_TYPE_def, INT_def, mlstringTheory.implode_def];

val type_num_defs = LIST_CONJ
  [bool_type_num_def, list_type_num_def, option_type_num_def,
   lit_type_num_def, id_type_num_def, ast_t_type_num_def,
   pat_type_num_def, lop_type_num_def, opn_type_num_def,
   opb_type_num_def, opw_type_num_def, shift_type_num_def,
   word_size_type_num_def, fp_uop_type_num_def, fp_bop_type_num_def,
   fp_top_type_num_def, fp_cmp_type_num_def, op_type_num_def,
   locn_type_num_def, locs_type_num_def, exp_type_num_def,
   dec_type_num_def];

val OPTION_TYPE_def = my_fetch "OPTION_TYPE_def";
val AST_LIT_TYPE_def = my_fetch "AST_LIT_TYPE_def";
val NAMESPACE_ID_TYPE_def = my_fetch "NAMESPACE_ID_TYPE_def";
val AST_AST_T_TYPE_def = my_fetch "AST_AST_T_TYPE_def";
val AST_PAT_TYPE_def = my_fetch "AST_PAT_TYPE_def";
val AST_LOP_TYPE_def = my_fetch "AST_LOP_TYPE_def";
val AST_OPN_TYPE_def = my_fetch "AST_OPN_TYPE_def";
val AST_OPB_TYPE_def = my_fetch "AST_OPB_TYPE_def";
val AST_OPW_TYPE_def = my_fetch "AST_OPW_TYPE_def";
val AST_SHIFT_TYPE_def = my_fetch "AST_SHIFT_TYPE_def";
val AST_WORD_SIZE_TYPE_def = my_fetch "AST_WORD_SIZE_TYPE_def";
val FPSEM_FP_UOP_TYPE_def = my_fetch "FPSEM_FP_UOP_TYPE_def";
val FPSEM_FP_BOP_TYPE_def = my_fetch "FPSEM_FP_BOP_TYPE_def";
val FPSEM_FP_TOP_TYPE_def = my_fetch "FPSEM_FP_TOP_TYPE_def";
val FPSEM_FP_CMP_TYPE_def = my_fetch "FPSEM_FP_CMP_TYPE_def";
val AST_OP_TYPE_def = my_fetch "AST_OP_TYPE_def";
val LOCATION_LOCN_TYPE_def = my_fetch "LOCATION_LOCN_TYPE_def";
val LOCATION_LOCS_TYPE_def = my_fetch "LOCATION_LOCS_TYPE_def";
val AST_EXP_TYPE_def = my_fetch "AST_EXP_TYPE_def";
val AST_DEC_TYPE_def = my_fetch "AST_DEC_TYPE_def";

Theorem AST_LIT_TYPE_eq_enc:
  !l v. AST_LIT_TYPE l v <=> v = enc_lit l
Proof
  Cases \\ fs [AST_LIT_TYPE_def,enc_lit_def,type_num_defs]
QED

Theorem NAMESPACE_ID_TYPE_eq_enc:
  !l v. NAMESPACE_ID_TYPE HOL_STRING_TYPE HOL_STRING_TYPE l v <=> v = enc_id l
Proof
  Induct \\ fs [NAMESPACE_ID_TYPE_def,HOL_STRING_TYPE_def,type_num_defs,
                STRING_TYPE_def,mlstringTheory.implode_def,enc_id_def]
QED

Theorem AST_AST_T_TYPE_eq_enc:
  !l v. AST_AST_T_TYPE l v <=> v = enc_ast_t l
Proof
  recInduct enc_ast_t_ind \\ rw []
  \\ fs [AST_AST_T_TYPE_def,NAMESPACE_ID_TYPE_eq_enc,enc_ast_t_def,type_num_defs]
  \\ fs [HOL_STRING_TYPE_def,mlstringTheory.implode_def,STRING_TYPE_def]
  \\ qsuff_tac
       `!v. LIST_TYPE AST_AST_T_TYPE x v <=> v = enc_list (MAP (λa. enc_ast_t a) x)`
  \\ fs [] \\ Induct_on `x` \\ fs [LIST_TYPE_def,enc_list_def,type_num_defs]
QED

Theorem AST_PAT_TYPE_eq_enc:
  !l v. AST_PAT_TYPE l v <=> v = enc_pat l
Proof
  recInduct enc_pat_ind \\ rw []
  \\ fs [AST_PAT_TYPE_def,NAMESPACE_ID_TYPE_eq_enc,enc_pat_def,type_num_defs,
         AST_AST_T_TYPE_eq_enc]
  \\ fs [AST_LIT_TYPE_eq_enc,HOL_STRING_TYPE_def,mlstringTheory.implode_def,STRING_TYPE_def]
  \\ rename [`LIST_TYPE AST_PAT_TYPE xs`]
  \\ `!v. LIST_TYPE AST_PAT_TYPE xs v <=> v = enc_list (MAP (λa. enc_pat a) xs)` by
         (Induct_on `xs` \\ fs [LIST_TYPE_def,enc_list_def,type_num_defs]) \\ fs []
  \\ rename [`OPTION_MAP enc_id xo`]
  \\ Cases_on `xo`
  \\ fs [enc_option_def,OPTION_TYPE_def,PULL_EXISTS, NAMESPACE_ID_TYPE_eq_enc,
         enc_id_def,type_num_defs]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
QED

Theorem AST_LOP_TYPE_eq_enc:
  !l v. AST_LOP_TYPE l v <=> v = enc_lop l
Proof
  Induct \\ fs [AST_LOP_TYPE_def,enc_lop_def,type_num_defs]
QED

Theorem AST_OPN_TYPE_eq_enc:
  !l v. AST_OPN_TYPE l v <=> v = enc_opn l
Proof
  Induct \\ fs [AST_OPN_TYPE_def,enc_opn_def,type_num_defs]
QED

Theorem AST_OPB_TYPE_eq_enc:
  !l v. AST_OPB_TYPE l v <=> v = enc_opb l
Proof
  Induct \\ fs [AST_OPB_TYPE_def,enc_opb_def,type_num_defs]
QED

Theorem AST_OPW_TYPE_eq_enc:
  !l v. AST_OPW_TYPE l v <=> v = enc_opw l
Proof
  Induct \\ fs [AST_OPW_TYPE_def,enc_opw_def,type_num_defs]
QED

Theorem AST_SHIFT_TYPE_eq_enc:
  !l v. AST_SHIFT_TYPE l v <=> v = enc_shift l
Proof
  Induct \\ fs [AST_SHIFT_TYPE_def,enc_shift_def,type_num_defs]
QED

Theorem AST_WORD_SIZE_TYPE_eq_enc:
  !l v. AST_WORD_SIZE_TYPE l v <=> v = enc_word_size l
Proof
  Induct \\ fs [AST_WORD_SIZE_TYPE_def,enc_word_size_def,type_num_defs]
QED

Theorem FPSEM_FP_UOP_TYPE_eq_enc:
  !l v. FPSEM_FP_UOP_TYPE l v <=> v = enc_fp_uop l
Proof
  Induct \\ fs [FPSEM_FP_UOP_TYPE_def,enc_fp_uop_def,type_num_defs]
QED

Theorem FPSEM_FP_BOP_TYPE_eq_enc:
  !l v. FPSEM_FP_BOP_TYPE l v <=> v = enc_fp_bop l
Proof
  Induct \\ fs [FPSEM_FP_BOP_TYPE_def,enc_fp_bop_def,type_num_defs]
QED

Theorem FPSEM_FP_TOP_TYPE_eq_enc:
  !l v. FPSEM_FP_TOP_TYPE l v <=> v = enc_fp_top l
Proof
  Induct \\ fs [FPSEM_FP_TOP_TYPE_def,enc_fp_top_def,type_num_defs]
QED

Theorem FPSEM_FP_CMP_TYPE_eq_enc:
  !l v. FPSEM_FP_CMP_TYPE l v <=> v = enc_fp_cmp l
Proof
  Induct \\ fs [FPSEM_FP_CMP_TYPE_def,enc_fp_cmp_def,type_num_defs]
QED

Theorem AST_OP_TYPE_eq_enc:
  !l v. AST_OP_TYPE l v <=> v = enc_op l
Proof
  Induct \\ fs [AST_OP_TYPE_def,enc_op_def,type_num_defs,
    AST_OPB_TYPE_eq_enc, AST_OPN_TYPE_eq_enc, AST_OPW_TYPE_eq_enc,
    AST_SHIFT_TYPE_eq_enc, AST_WORD_SIZE_TYPE_eq_enc,
    FPSEM_FP_UOP_TYPE_eq_enc, FPSEM_FP_BOP_TYPE_eq_enc,
    FPSEM_FP_TOP_TYPE_eq_enc, FPSEM_FP_CMP_TYPE_eq_enc]
QED

Theorem LOCATION_LOCN_TYPE_eq_enc:
  !l v. LOCATION_LOCN_TYPE l v <=> v = enc_locn l
Proof
  Induct \\ fs [LOCATION_LOCN_TYPE_def,enc_locn_def,type_num_defs]
QED

Theorem LOCATION_LOCS_TYPE_eq_enc:
  !l v. LOCATION_LOCS_TYPE l v <=> v = enc_locs l
Proof
  Induct
  \\ fs [LOCATION_LOCS_TYPE_def,enc_locs_def,type_num_defs,LOCATION_LOCN_TYPE_eq_enc]
QED

Theorem AST_EXP_TYPE_eq_enc:
  !l v. AST_EXP_TYPE l v <=> v = enc_exp l
Proof
  recInduct enc_exp_ind \\ rpt conj_tac \\ rpt gen_tac
  \\ fs [AST_EXP_TYPE_def,enc_exp_def,AST_OP_TYPE_eq_enc,AST_LIT_TYPE_eq_enc,
         AST_AST_T_TYPE_eq_enc,AST_LOP_TYPE_eq_enc,LOCATION_LOCS_TYPE_eq_enc,
         NAMESPACE_ID_TYPE_eq_enc,type_num_defs]
  \\ rw []
  THEN1
   (rename [`LIST_TYPE _ xs`]
    \\ qsuff_tac `!v. LIST_TYPE
           (PAIR_TYPE HOL_STRING_TYPE
             (PAIR_TYPE HOL_STRING_TYPE AST_EXP_TYPE)) xs v <=>
         v = enc_list (MAP (λ(f,x,e).
                     enc_pair (Litv (StrLit f))
                       (enc_pair (Litv (StrLit x)) (enc_exp e))) xs)`
    THEN1 fs []
    \\ Induct_on `xs` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs]
    \\ rw [] \\ first_x_assum (fn th => mp_tac th \\ impl_tac)
    THEN1 metis_tac []
    \\ fs [PAIR_TYPE_def,enc_pair_def,HOL_STRING_TYPE_def,STRING_TYPE_def,
          mlstringTheory.implode_def,type_num_defs])
  THEN1
   (rename [`OPTION_MAP _ xo`] \\ Cases_on `xo`
    \\ fs [OPTION_TYPE_def,enc_option_def,HOL_STRING_TYPE_def,STRING_TYPE_def,
          mlstringTheory.implode_def,type_num_defs])
  THEN1
   (rename [`LIST_TYPE _ xs`]
    \\ qsuff_tac `!v. LIST_TYPE (PAIR_TYPE AST_PAT_TYPE AST_EXP_TYPE) xs v <=>
         v = enc_list (MAP (λ(p,e). enc_pair (enc_pat p) (enc_exp e)) xs)`
    THEN1 fs []
    \\ Induct_on `xs` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs]
    \\ rw [] \\ first_x_assum (fn th => mp_tac th \\ impl_tac)
    THEN1 metis_tac []
    \\ fs [PAIR_TYPE_def,enc_pair_def,HOL_STRING_TYPE_def,STRING_TYPE_def,
          mlstringTheory.implode_def,PULL_EXISTS,AST_PAT_TYPE_eq_enc,type_num_defs])
  THEN1
   (rename [`LIST_TYPE _ xs`]
    \\ qsuff_tac `!v. LIST_TYPE AST_EXP_TYPE xs v <=>
         v = enc_list (MAP (λa. enc_exp a) xs)`
    THEN1 fs []
    \\ Induct_on `xs`
    \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs] \\ rw [])
  THEN1
   (rename [`OPTION_TYPE _ x`]
    \\ Cases_on `x` \\ fs [OPTION_TYPE_def,enc_option_def,type_num_defs]
    \\ rename [`LIST_TYPE _ xs`]
    \\ `!v. LIST_TYPE AST_EXP_TYPE xs v <=>
            v = enc_list (MAP (λa. enc_exp a) xs)`
         by (Induct_on `xs`
             \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs] \\ rw [])
    \\ fs [NAMESPACE_ID_TYPE_eq_enc,enc_option_def,type_num_defs])
  THEN1
   (rename [`LIST_TYPE _ xs`]
    \\ qsuff_tac `!v. LIST_TYPE (PAIR_TYPE AST_PAT_TYPE AST_EXP_TYPE) xs v <=>
         v = enc_list (MAP (λ(p,e). enc_pair (enc_pat p) (enc_exp e)) xs)`
    THEN1 fs []
    \\ Induct_on `xs`
    \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs] \\ rw []
    \\ first_x_assum (fn th => mp_tac th \\ impl_tac)
    THEN1 metis_tac []
    \\ fs [PAIR_TYPE_def,enc_pair_def,HOL_STRING_TYPE_def,STRING_TYPE_def,
          mlstringTheory.implode_def,PULL_EXISTS,AST_PAT_TYPE_eq_enc,type_num_defs])
QED

Theorem AST_DEC_TYPE_eq_enc:
  !l v. AST_DEC_TYPE l v <=> v = enc_dec l
Proof
  recInduct enc_dec_ind \\ rpt conj_tac \\ rpt gen_tac
  \\ fs [AST_EXP_TYPE_eq_enc,AST_OP_TYPE_eq_enc,AST_LIT_TYPE_eq_enc,type_num_defs,
         AST_AST_T_TYPE_eq_enc,AST_LOP_TYPE_eq_enc,LOCATION_LOCS_TYPE_eq_enc,
         NAMESPACE_ID_TYPE_eq_enc,enc_dec_def,AST_DEC_TYPE_def,AST_PAT_TYPE_eq_enc]
  \\ rw []
  THEN1
   (rename [`LIST_TYPE _ xs _ /\ LIST_TYPE _ ys _`]
    \\ `!v. LIST_TYPE AST_DEC_TYPE xs v <=>
         v = enc_list (MAP (λa. enc_dec a) xs)` by
     (Induct_on `xs`
      \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs] \\ rw [])
    \\ `!v. LIST_TYPE AST_DEC_TYPE ys v <=>
         v = enc_list (MAP (λa. enc_dec a) ys)` by
     (Induct_on `ys`
      \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs] \\ rw [])
    \\ fs [])
  THEN1
   (rename [`LIST_TYPE _ xs`]
    \\ `!v. LIST_TYPE AST_DEC_TYPE xs v <=>
         v = enc_list (MAP (λa. enc_dec a) xs)` by
     (Induct_on `xs`
      \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs] \\ rw [])
    \\ fs [])
  THEN1
   (rename [`LIST_TYPE _ xs`]
    \\ `!v. LIST_TYPE AST_AST_T_TYPE xs v <=>
         v = enc_list (MAP enc_ast_t xs)` by
     (Induct_on `xs` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs]
      \\ rw [AST_AST_T_TYPE_eq_enc])
    \\ fs [])
  THEN1
   (rename [`LIST_TYPE _ xs`]
    \\ `!v. LIST_TYPE HOL_STRING_TYPE xs v <=>
         v = enc_list (MAP (λs. Litv (StrLit s)) xs)` by
     (Induct_on `xs` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD,type_num_defs]
      \\ rw [HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def])
    \\ fs [])
  THEN1
   (rename [`LIST_TYPE _ xs`]
    \\ qsuff_tac
     `!v. LIST_TYPE
           (PAIR_TYPE (LIST_TYPE HOL_STRING_TYPE)
              (PAIR_TYPE HOL_STRING_TYPE
                 (LIST_TYPE
                    (PAIR_TYPE HOL_STRING_TYPE (LIST_TYPE AST_AST_T_TYPE)))))
          xs v <=>
        v = enc_list
        (MAP
           (λ(vs,s,l).
                enc_pair (enc_list (MAP (λs. Litv (StrLit s)) vs))
                  (enc_pair (Litv (StrLit s))
                     (enc_list
                        (MAP
                           (λ(x,xs).
                                enc_pair (Litv (StrLit x))
                                  (enc_list (MAP enc_ast_t xs))) l)))) xs)` THEN1 fs []
    \\ Induct_on `xs` \\ fs [LIST_TYPE_def,enc_list_def,type_num_defs]
    \\ fs [FORALL_PROD,EXISTS_PROD,PAIR_TYPE_def,enc_pair_def,PULL_EXISTS,
           HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def,
           AST_EXP_TYPE_eq_enc]
     \\ `!l v. LIST_TYPE HOL_STRING_TYPE l v <=>
               v = enc_list (MAP (\s. Litv (StrLit s)) l)` by
           (Induct \\ fs [HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def,
             LIST_TYPE_def,enc_list_def,type_num_defs])
     \\ qsuff_tac
        `!l v. LIST_TYPE
                 (PAIR_TYPE HOL_STRING_TYPE (LIST_TYPE AST_AST_T_TYPE)) l v <=>
               v = enc_list (MAP (λ(x,xs).
                               Conv NONE
                                 [Litv (StrLit x);
                                  enc_list (MAP enc_ast_t xs)]) l)` THEN1 fs []
     \\ Induct \\ fs [HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def,
            FORALL_PROD,EXISTS_PROD,PAIR_TYPE_def,enc_pair_def,PULL_EXISTS,
            LIST_TYPE_def,enc_list_def,type_num_defs]
     \\ `!l v. LIST_TYPE AST_AST_T_TYPE l v <=>
               v = enc_list (MAP enc_ast_t l)` by
           (Induct \\ fs [LIST_TYPE_def,enc_list_def,AST_AST_T_TYPE_eq_enc,type_num_defs])
     \\ fs [])
  \\ rename [`LIST_TYPE _ xs`]
  \\ qsuff_tac
   `!v. LIST_TYPE
          (PAIR_TYPE HOL_STRING_TYPE (PAIR_TYPE HOL_STRING_TYPE AST_EXP_TYPE))
          xs v <=>
        v = enc_list (MAP (λ(f,x,e).
                enc_pair (Litv (StrLit f))
                  (enc_pair (Litv (StrLit x)) (enc_exp e))) xs)` THEN1 fs []
  \\ Induct_on `xs` \\ fs [LIST_TYPE_def,enc_list_def,type_num_defs]
  \\ fs [FORALL_PROD,EXISTS_PROD,PAIR_TYPE_def,enc_pair_def,PULL_EXISTS,
         HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def,
       AST_EXP_TYPE_eq_enc]
QED

Theorem AST_DEC_TYPE_eq_enc:
  !l v. LIST_TYPE AST_DEC_TYPE l v <=> v = decs_to_v l
Proof
  Induct
  \\ fs [LIST_TYPE_def,enc_list_def,decs_to_v_def,AST_DEC_TYPE_eq_enc,type_num_defs]
QED

Theorem AST_DEC_TYPE_eq_v_to_decs:
  !l v. LIST_TYPE AST_DEC_TYPE l v <=> v_to_decs v = SOME l
Proof
  simp [AST_DEC_TYPE_eq_enc,semanticPrimitivesPropsTheory.v_to_decs_eq_decs_to_v]
QED

val _ = (print_asts := true);
val _ = export_theory();

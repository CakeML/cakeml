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

Theorem enc_lit_11[simp]:
  !i j. enc_lit i = enc_lit j <=> i = j
Proof
  Cases_on `i` \\ Cases_on `j` \\ fs [enc_lit_def]
QED

Theorem dec_lit_enc_lit[simp]:
  dec_lit (enc_lit l) = SOME l
Proof
  fs [dec_lit_def]
QED

Theorem AST_LIT_TYPE_eq_enc:
  !l v. AST_LIT_TYPE l v <=> v = enc_lit l
Proof
  Cases \\ fs [AST_LIT_TYPE_def,enc_lit_def,lit_type_num_def]
QED

Definition enc_id_def:
  enc_id (Short s) =
    Conv (SOME (TypeStamp "Short" 4)) [Litv (StrLit s)] /\
  enc_id (Long s i) =
    Conv (SOME (TypeStamp "Long" 4)) [Litv (StrLit s); enc_id i]
End

Definition enc_list_def:
  enc_list [] =
    Conv (SOME (TypeStamp "[]" 1)) [] /\
  enc_list (x::xs) =
    Conv (SOME (TypeStamp "::" 1)) [x; enc_list xs]
End

Definition enc_option_def:
  enc_option NONE =
    Conv (SOME (TypeStamp "None" 2)) [] /\
  enc_option (SOME x) =
    Conv (SOME (TypeStamp "Some" 2)) [x]
End

Theorem MEM_ast_t_size:
  !xs a. MEM a xs ==> ast_t_size a < ast_t1_size xs
Proof
  Induct \\ fs [] \\ rw [] \\ fs [ast_t_size_def] \\ res_tac \\ fs []
QED

Definition enc_ast_t_def:
  enc_ast_t (Atapp x y) =
    Conv (SOME (TypeStamp "Atapp" 5))
      [enc_list (MAP enc_ast_t x); enc_id y] /\
  enc_ast_t (Attup x) =
    Conv (SOME (TypeStamp "Attup" 5))
      [enc_list (MAP enc_ast_t x)] /\
  enc_ast_t (Atfun x_3 x_2) =
    Conv (SOME (TypeStamp "Atfun" 5))
      [enc_ast_t x_3; enc_ast_t x_2] /\
  enc_ast_t (Atvar x_1) =
    Conv (SOME (TypeStamp "Atvar" 5)) [Litv (StrLit x_1)]
Termination
  WF_REL_TAC `measure ast_t_size`
  \\ rw [] \\ fs [ast_t_size_def]
  \\ imp_res_tac MEM_ast_t_size \\ fs []
End

Definition enc_pat_def:
  enc_pat (Ptannot x_7 x_6) =
    Conv (SOME (TypeStamp "Ptannot" 6))
      [enc_pat x_7; enc_ast_t x_6] /\
  enc_pat (Pref x_5) =
    Conv (SOME (TypeStamp "Pref" 6))
      [enc_pat x_5] /\
  enc_pat (Pcon x_4 x_3) =
    Conv (SOME (TypeStamp "Pcon" 6))
      [enc_option (OPTION_MAP enc_id x_4); enc_list (MAP enc_pat x_3)] /\
  enc_pat (Plit x_2) =
    Conv (SOME (TypeStamp "Plit" 6))
      [enc_lit x_2] /\
  enc_pat (Pvar x_1) =
    Conv (SOME (TypeStamp "Pvar" 6))
      [Litv (StrLit x_1)] /\
  enc_pat Pany =
    Conv (SOME (TypeStamp "Pany" 6)) []
Termination
  WF_REL_TAC `measure pat_size`
  \\ rw [] \\ fs [pat_size_def]
  \\ qsuff_tac `!a l. MEM a l ==> pat_size a < pat1_size l`
  THEN1 (rw[] \\ res_tac \\ fs [])
  \\ Induct_on `l` \\ fs [] \\ rw [] \\ fs [pat_size_def] \\ res_tac \\ fs []
End

Theorem enc_id_11[simp]:
  !i j. enc_id i = enc_id j <=> i = j
Proof
  Induct_on `i` \\ Cases_on `j` \\ fs [enc_id_def]
QED

Theorem NAMESPACE_ID_TYPE_eq_enc:
  !l v. NAMESPACE_ID_TYPE HOL_STRING_TYPE HOL_STRING_TYPE l v <=> v = enc_id l
Proof
  Induct \\ fs [NAMESPACE_ID_TYPE_def,HOL_STRING_TYPE_def,
                STRING_TYPE_def,mlstringTheory.implode_def,enc_id_def]
QED

Theorem enc_list_11[simp]:
  !i j. enc_list i = enc_list j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_list_def]
QED

Theorem enc_option_11[simp]:
  !i j. enc_option i = enc_option j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_option_def]
QED

Theorem enc_ast_t_11[simp]:
  !i j. enc_ast_t i = enc_ast_t j <=> i = j
Proof
  recInduct (theorem "enc_ast_t_ind") \\ rw []
  \\ Cases_on `j` \\ fs [enc_ast_t_def]
  THEN1
    (Cases_on `y = i` \\ fs [] \\ rveq
    \\ pop_assum mp_tac \\ qspec_tac (`l`,`l`)
    \\ Induct_on `x` \\ Cases_on `l` \\ fs [])
  \\ pop_assum mp_tac \\ qspec_tac (`l`,`l`)
  \\ Induct_on `x` \\ Cases_on `l` \\ fs []
QED

Theorem LIST_TYPE_eq_enc:
  !l v.
    (∀a. MEM a l ⇒ ∀v. P a v ⇔ v = f a) ==>
    (LIST_TYPE P l v <=> v = enc_list (MAP f l))
Proof
  Induct \\ fs [LIST_TYPE_def,enc_list_def]
QED

Theorem AST_AST_T_TYPE_eq_enc:
  !l v. AST_AST_T_TYPE l v <=> v = enc_ast_t l
Proof
  recInduct (theorem "enc_ast_t_ind") \\ rw []
  \\ fs [AST_AST_T_TYPE_def,NAMESPACE_ID_TYPE_eq_enc,enc_ast_t_def]
  \\ fs [HOL_STRING_TYPE_def,mlstringTheory.implode_def,STRING_TYPE_def]
  \\ drule LIST_TYPE_eq_enc
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
QED

Theorem AST_PAT_TYPE_eq_enc:
  !l v. AST_PAT_TYPE l v <=> v = enc_pat l
Proof
  recInduct (theorem "enc_pat_ind") \\ rw []
  \\ fs [AST_PAT_TYPE_def,NAMESPACE_ID_TYPE_eq_enc,enc_pat_def,
         AST_AST_T_TYPE_eq_enc]
  \\ fs [AST_LIT_TYPE_eq_enc,HOL_STRING_TYPE_def,mlstringTheory.implode_def,STRING_TYPE_def]
  \\ drule LIST_TYPE_eq_enc \\ fs []
  \\ Cases_on `x_4`
  \\ fs [enc_option_def,OPTION_TYPE_def,PULL_EXISTS, NAMESPACE_ID_TYPE_eq_enc,enc_id_def]
  \\ fs [] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs []
QED

Theorem enc_pat_11[simp]:
  !i j. enc_pat i = enc_pat j <=> i = j
Proof
  recInduct (theorem "enc_pat_ind") \\ rw []
  \\ Cases_on `j` \\ fs [enc_pat_def]
  \\ rename [`OPTION_MAP _ x = _ y`]
  \\ `OPTION_MAP enc_id x = OPTION_MAP enc_id y <=> x = y` by
       (Cases_on `x` \\ Cases_on `y` \\ fs [])
  \\ fs [] \\ Cases_on `x = y` \\ fs []
  \\ qspec_tac (`l`,`l`)
  \\ Induct_on `x_3` \\ rw [] \\ Cases_on `l` \\ fs []
QED

Definition enc_lop_def:
  enc_lop Or = Conv (SOME (TypeStamp "Or" 7)) [] /\
  enc_lop And = Conv (SOME (TypeStamp "And" 7)) []
End

Definition enc_opn_def:
  enc_opn Modulo = Conv (SOME (TypeStamp "Modulo" 8)) [] ∧
  enc_opn Divide = Conv (SOME (TypeStamp "Divide" 8)) [] ∧
  enc_opn Times = Conv (SOME (TypeStamp "Times" 8)) [] ∧
  enc_opn Minus = Conv (SOME (TypeStamp "Minus" 8)) [] ∧
  enc_opn Plus = Conv (SOME (TypeStamp "Plus" 8)) []
End

Definition enc_opb_def:
  enc_opb Geq = Conv (SOME (TypeStamp "Geq" 9)) [] ∧
  enc_opb Leq = Conv (SOME (TypeStamp "Leq" 9)) [] ∧
  enc_opb Gt = Conv (SOME (TypeStamp "Gt" 9)) [] ∧
  enc_opb Lt = Conv (SOME (TypeStamp "Lt" 9)) []
End

Definition enc_opw_def:
  enc_opw Sub = Conv (SOME (TypeStamp "Sub" 10)) [] ∧
  enc_opw Add = Conv (SOME (TypeStamp "Add" 10)) [] ∧
  enc_opw Xor = Conv (SOME (TypeStamp "Xor" 10)) [] ∧
  enc_opw Orw = Conv (SOME (TypeStamp "Orw" 10)) [] ∧
  enc_opw Andw = Conv (SOME (TypeStamp "Andw" 10)) []
End

Definition enc_shift_def:
  enc_shift Ror = Conv (SOME (TypeStamp "Ror" 11)) [] ∧
  enc_shift Asr = Conv (SOME (TypeStamp "Asr" 11)) [] ∧
  enc_shift Lsr = Conv (SOME (TypeStamp "Lsr" 11)) [] ∧
  enc_shift Lsl = Conv (SOME (TypeStamp "Lsl" 11)) []
End

Definition enc_word_size_def:
  enc_word_size W64 = Conv (SOME (TypeStamp "W64" 12)) [] ∧
  enc_word_size W8 = Conv (SOME (TypeStamp "W8" 12)) []
End

Definition enc_fp_uop_def:
  enc_fp_uop FP_Sqrt = Conv (SOME (TypeStamp "Fp_sqrt" 13)) [] ∧
  enc_fp_uop FP_Neg = Conv (SOME (TypeStamp "Fp_neg" 13)) [] ∧
  enc_fp_uop FP_Abs = Conv (SOME (TypeStamp "Fp_abs" 13)) []
End

Definition enc_fp_bop_def:
  enc_fp_bop FP_Div = Conv (SOME (TypeStamp "Fp_div" 14)) [] ∧
  enc_fp_bop FP_Mul = Conv (SOME (TypeStamp "Fp_mul" 14)) [] ∧
  enc_fp_bop FP_Sub = Conv (SOME (TypeStamp "Fp_sub" 14)) [] ∧
  enc_fp_bop FP_Add = Conv (SOME (TypeStamp "Fp_add" 14)) []
End

Definition enc_fp_top_def:
  enc_fp_top FP_Fma = Conv (SOME (TypeStamp "Fp_fma" 15)) []
End

Definition enc_fp_cmp_def:
  enc_fp_cmp FP_Equal = Conv (SOME (TypeStamp "Fp_equal" 16)) [] ∧
  enc_fp_cmp FP_GreaterEqual = Conv (SOME (TypeStamp "Fp_greaterequal" 16)) [] ∧
  enc_fp_cmp FP_Greater = Conv (SOME (TypeStamp "Fp_greater" 16)) [] ∧
  enc_fp_cmp FP_LessEqual = Conv (SOME (TypeStamp "Fp_lessequal" 16)) [] ∧
  enc_fp_cmp FP_Less = Conv (SOME (TypeStamp "Fp_less" 16)) []
End

Theorem enc_lop_11[simp]:
  !i j. enc_lop i = enc_lop j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_lop_def]
QED

Theorem enc_opn_11[simp]:
  !i j. enc_opn i = enc_opn j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_opn_def]
QED

Theorem enc_opb_11[simp]:
  !i j. enc_opb i = enc_opb j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_opb_def]
QED

Theorem enc_opw_11[simp]:
  !i j. enc_opw i = enc_opw j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_opw_def]
QED

Theorem enc_shift_11[simp]:
  !i j. enc_shift i = enc_shift j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_shift_def]
QED

Theorem enc_word_size_11[simp]:
  !i j. enc_word_size i = enc_word_size j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_word_size_def]
QED

Theorem enc_fp_uop_11[simp]:
  !i j. enc_fp_uop i = enc_fp_uop j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_fp_uop_def]
QED

Theorem enc_fp_bop_11[simp]:
  !i j. enc_fp_bop i = enc_fp_bop j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_fp_bop_def]
QED

Theorem enc_fp_top_11[simp]:
  !i j. enc_fp_top i = enc_fp_top j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_fp_cmp_def]
QED

Theorem enc_fp_cmp_11[simp]:
  !i j. enc_fp_cmp i = enc_fp_cmp j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_fp_cmp_def]
QED

Theorem AST_LOP_TYPE_eq_enc:
  !l v. AST_LOP_TYPE l v <=> v = enc_lop l
Proof
  Induct \\ fs [AST_LOP_TYPE_def,enc_lop_def]
QED

Theorem AST_OPN_TYPE_eq_enc:
  !l v. AST_OPN_TYPE l v <=> v = enc_opn l
Proof
  Induct \\ fs [AST_OPN_TYPE_def,enc_opn_def]
QED

Theorem AST_OPB_TYPE_eq_enc:
  !l v. AST_OPB_TYPE l v <=> v = enc_opb l
Proof
  Induct \\ fs [AST_OPB_TYPE_def,enc_opb_def]
QED

Theorem AST_OPW_TYPE_eq_enc:
  !l v. AST_OPW_TYPE l v <=> v = enc_opw l
Proof
  Induct \\ fs [AST_OPW_TYPE_def,enc_opw_def]
QED

Theorem AST_SHIFT_TYPE_eq_enc:
  !l v. AST_SHIFT_TYPE l v <=> v = enc_shift l
Proof
  Induct \\ fs [AST_SHIFT_TYPE_def,enc_shift_def]
QED

Theorem AST_WORD_SIZE_TYPE_eq_enc:
  !l v. AST_WORD_SIZE_TYPE l v <=> v = enc_word_size l
Proof
  Induct \\ fs [AST_WORD_SIZE_TYPE_def,enc_word_size_def]
QED

Theorem FPSEM_FP_UOP_TYPE_eq_enc:
  !l v. FPSEM_FP_UOP_TYPE l v <=> v = enc_fp_uop l
Proof
  Induct \\ fs [FPSEM_FP_UOP_TYPE_def,enc_fp_uop_def]
QED

Theorem FPSEM_FP_BOP_TYPE_eq_enc:
  !l v. FPSEM_FP_BOP_TYPE l v <=> v = enc_fp_bop l
Proof
  Induct \\ fs [FPSEM_FP_BOP_TYPE_def,enc_fp_bop_def]
QED

Theorem FPSEM_FP_TOP_TYPE_eq_enc:
  !l v. FPSEM_FP_TOP_TYPE l v <=> v = enc_fp_top l
Proof
  Induct \\ fs [FPSEM_FP_TOP_TYPE_def,enc_fp_top_def]
QED

Theorem FPSEM_FP_CMP_TYPE_eq_enc:
  !l v. FPSEM_FP_CMP_TYPE l v <=> v = enc_fp_cmp l
Proof
  Induct \\ fs [FPSEM_FP_CMP_TYPE_def,enc_fp_cmp_def]
QED

Definition enc_op_def:
  enc_op EnvLookup = Conv (SOME (TypeStamp "Envlookup" 17)) [] ∧
  enc_op Eval = Conv (SOME (TypeStamp "Eval" 17)) [] ∧
  enc_op (FFI x_15) = Conv (SOME (TypeStamp "Ffi" 17)) [Litv (StrLit x_15)] ∧
  enc_op ConfigGC = Conv (SOME (TypeStamp "Configgc" 17)) [] ∧
  enc_op ListAppend = Conv (SOME (TypeStamp "Listappend" 17)) [] ∧
  enc_op Aupdate = Conv (SOME (TypeStamp "Aupdate" 17)) [] ∧
  enc_op Alength = Conv (SOME (TypeStamp "Alength" 17)) [] ∧
  enc_op Asub = Conv (SOME (TypeStamp "Asub" 17)) [] ∧
  enc_op AallocEmpty = Conv (SOME (TypeStamp "Aallocempty" 17)) [] ∧
  enc_op Aalloc = Conv (SOME (TypeStamp "Aalloc" 17)) [] ∧
  enc_op Vlength = Conv (SOME (TypeStamp "Vlength" 17)) [] ∧
  enc_op Vsub = Conv (SOME (TypeStamp "Vsub" 17)) [] ∧
  enc_op VfromList = Conv (SOME (TypeStamp "Vfromlist" 17)) [] ∧
  enc_op Strcat = Conv (SOME (TypeStamp "Strcat" 17)) [] ∧
  enc_op Strlen = Conv (SOME (TypeStamp "Strlen" 17)) [] ∧
  enc_op Strsub = Conv (SOME (TypeStamp "Strsub" 17)) [] ∧
  enc_op Explode = Conv (SOME (TypeStamp "Explode" 17)) [] ∧
  enc_op Implode = Conv (SOME (TypeStamp "Implode" 17)) [] ∧
  enc_op (Chopb x_14) = Conv (SOME (TypeStamp "Chopb" 17)) [enc_opb x_14] ∧
  enc_op Chr = Conv (SOME (TypeStamp "Chr_1" 17)) [] ∧
  enc_op Ord = Conv (SOME (TypeStamp "Ord" 17)) [] ∧
  enc_op CopyAw8Aw8 = Conv (SOME (TypeStamp "Copyaw8aw8" 17)) [] ∧
  enc_op CopyAw8Str = Conv (SOME (TypeStamp "Copyaw8str" 17)) [] ∧
  enc_op CopyStrAw8 = Conv (SOME (TypeStamp "Copystraw8" 17)) [] ∧
  enc_op CopyStrStr = Conv (SOME (TypeStamp "Copystrstr" 17)) [] ∧
  enc_op (WordToInt x_13) = Conv (SOME (TypeStamp "Wordtoint" 17)) [enc_word_size x_13] ∧
  enc_op (WordFromInt x_12) = Conv (SOME (TypeStamp "Wordfromint" 17)) [enc_word_size x_12] ∧
  enc_op Aw8update = Conv (SOME (TypeStamp "Aw8update" 17)) [] ∧
  enc_op Aw8length = Conv (SOME (TypeStamp "Aw8length" 17)) [] ∧
  enc_op Aw8sub = Conv (SOME (TypeStamp "Aw8sub" 17)) [] ∧
  enc_op Aw8alloc = Conv (SOME (TypeStamp "Aw8alloc" 17)) [] ∧
  enc_op Opderef = Conv (SOME (TypeStamp "Opderef" 17)) [] ∧
  enc_op Opref = Conv (SOME (TypeStamp "Opref" 17)) [] ∧
  enc_op Opassign = Conv (SOME (TypeStamp "Opassign" 17)) [] ∧
  enc_op Opapp = Conv (SOME (TypeStamp "Opapp" 17)) [] ∧
  enc_op (FP_top x_11) = Conv (SOME (TypeStamp "Fp_top" 17)) [enc_fp_top x_11] ∧
  enc_op (FP_bop x_10) = Conv (SOME (TypeStamp "Fp_bop" 17)) [enc_fp_bop x_10] ∧
  enc_op (FP_uop x_9) = Conv (SOME (TypeStamp "Fp_uop" 17)) [enc_fp_uop x_9] ∧
  enc_op (FP_cmp x_8) = Conv (SOME (TypeStamp "Fp_cmp" 17)) [enc_fp_cmp x_8] ∧
  enc_op Equality = Conv (SOME (TypeStamp "Equality" 17)) [] ∧
  enc_op (Shift x_7 x_6 x_5) = Conv (SOME (TypeStamp "Shift" 17)) [enc_word_size x_7; enc_shift x_6; Litv (IntLit (&x_5))] ∧
  enc_op (Opw x_4 x_3) = Conv (SOME (TypeStamp "Opw" 17)) [enc_word_size x_4; enc_opw x_3] ∧
  enc_op (Opb x_2) = Conv (SOME (TypeStamp "Opb" 17)) [enc_opb x_2] ∧
  enc_op (Opn x_1) = Conv (SOME (TypeStamp "Opn" 17)) [enc_opn x_1]
End

Theorem enc_op_11[simp]:
  !i j. enc_op i = enc_op j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_op_def]
QED

Theorem AST_OP_TYPE_eq_enc:
  !l v. AST_OP_TYPE l v <=> v = enc_op l
Proof
  Induct \\ fs [AST_OP_TYPE_def,enc_op_def,
    AST_OPB_TYPE_eq_enc, AST_OPN_TYPE_eq_enc, AST_OPW_TYPE_eq_enc,
    AST_SHIFT_TYPE_eq_enc, AST_WORD_SIZE_TYPE_eq_enc,
    FPSEM_FP_UOP_TYPE_eq_enc, FPSEM_FP_BOP_TYPE_eq_enc,
    FPSEM_FP_TOP_TYPE_eq_enc, FPSEM_FP_CMP_TYPE_eq_enc]
QED

Definition enc_locn_def:
  enc_locn (locn x_3 x_2 x_1) =
    Conv (SOME (TypeStamp "Recordtypelocn" 18))
      [Litv (IntLit (&x_3)); Litv (IntLit (&x_2)); Litv (IntLit (&x_1))]
End

Theorem enc_locn_11[simp]:
  !i j. enc_locn i = enc_locn j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_locn_def]
QED

Theorem LOCATION_LOCN_TYPE_eq_enc:
  !l v. LOCATION_LOCN_TYPE l v <=> v = enc_locn l
Proof
  Induct \\ fs [LOCATION_LOCN_TYPE_def,enc_locn_def]
QED

Definition enc_locs_def:
  enc_locs (Locs x_2 x_1) =
    Conv (SOME (TypeStamp "Locs" 19)) [enc_locn x_2; enc_locn x_1]
End

Theorem enc_locs_11[simp]:
  !i j. enc_locs i = enc_locs j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [enc_locs_def]
QED

Theorem LOCATION_LOCS_TYPE_eq_enc:
  !l v. LOCATION_LOCS_TYPE l v <=> v = enc_locs l
Proof
  Induct \\ fs [LOCATION_LOCS_TYPE_def,enc_locs_def,LOCATION_LOCN_TYPE_eq_enc]
QED

Definition enc_pair_def:
  enc_pair v1 v2 = Conv NONE [v1; v2]
End

Definition enc_exp_def:
  enc_exp (Lannot x_28 x_27) =
    Conv (SOME (TypeStamp "Lannot" 20)) [enc_exp x_28; enc_locs x_27] ∧
  enc_exp (Tannot x_26 x_25) =
    Conv (SOME (TypeStamp "Tannot" 20)) [enc_exp x_26; enc_ast_t x_25] ∧
  enc_exp (Letrec x_24 x_23) =
    Conv (SOME (TypeStamp "Letrec" 20))
      [enc_list (MAP ( \ (f,x,e). enc_pair (Litv (StrLit f))
                               (enc_pair (Litv (StrLit x))
                                         (enc_exp e))) x_24);
       enc_exp x_23] ∧
  enc_exp (Let x_22 x_21 x_20) =
    Conv (SOME (TypeStamp "Let" 20))
      [enc_option (OPTION_MAP (\s. Litv (StrLit s)) x_22); enc_exp x_21; enc_exp x_20] ∧
  enc_exp (Mat x_19 x_18) =
    Conv (SOME (TypeStamp "Mat" 20))
      [enc_exp x_19; enc_list (MAP (\(p,e). enc_pair (enc_pat p) (enc_exp e)) x_18)] ∧
  enc_exp (If x_17 x_16 x_15) =
    Conv (SOME (TypeStamp "If" 20)) [enc_exp x_17; enc_exp x_16; enc_exp x_15] ∧
  enc_exp (Log x_14 x_13 x_12) =
    Conv (SOME (TypeStamp "Log" 20)) [enc_lop x_14; enc_exp x_13; enc_exp x_12] ∧
  enc_exp (App x_11 x_10) =
    Conv (SOME (TypeStamp "App" 20)) [enc_op x_11; enc_list (MAP enc_exp x_10)] ∧
  enc_exp (Fun x_9 x_8) =
    Conv (SOME (TypeStamp "Fun" 20)) [Litv (StrLit x_9); enc_exp x_8] ∧
  enc_exp (Var x_7) =
    Conv (SOME (TypeStamp "Var" 20)) [enc_id x_7] ∧
  enc_exp (Con x_6 x_5) =
    Conv (SOME (TypeStamp "Con" 20))
      [enc_option (OPTION_MAP enc_id x_6);
       enc_list (MAP enc_exp x_5)] ∧
  enc_exp (Lit x_4) =
    Conv (SOME (TypeStamp "Lit" 20)) [enc_lit x_4] ∧
  enc_exp (Handle x_3 x_2) =
    Conv (SOME (TypeStamp "Handle" 20))
      [enc_exp x_3; enc_list (MAP (\(p,e). enc_pair (enc_pat p) (enc_exp e)) x_2)] ∧
  enc_exp (Raise x_1) =
    Conv (SOME (TypeStamp "Raise" 20)) [enc_exp x_1]
Termination
  WF_REL_TAC `measure exp_size`
  \\ `!l f x e. MEM (f,x,e) l ==> exp_size e < exp1_size l` by
       (Induct \\ fs [exp_size_def] \\ rw [] \\ fs [exp_size_def] \\ res_tac \\ fs [])
  \\ `!l p e. MEM (p,e) l ==> exp_size e < exp3_size l` by
       (Induct \\ fs [exp_size_def] \\ rw [] \\ fs [exp_size_def] \\ res_tac \\ fs [])
  \\ `!l e. MEM e l ==> exp_size e < exp6_size l` by
       (Induct \\ fs [exp_size_def] \\ rw [] \\ fs [exp_size_def] \\ res_tac \\ fs [])
  \\ rw [] \\ fs [exp_size_def]
  \\ res_tac \\ fs []
End

Theorem enc_exp_11[simp]:
  !i j. enc_exp i = enc_exp j <=> i = j
Proof
  ho_match_mp_tac (theorem "enc_exp_ind")
  \\ rpt conj_tac \\ fs [PULL_FORALL]
  \\ Cases_on `j` \\ fs [enc_exp_def]
  \\ fs [FORALL_PROD] \\ rw []
  THEN1
   (Cases_on `i = e` \\ rw []
    \\ qid_spec_tac `l` \\ Induct_on `x_24`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l` \\ fs []
    \\ PairCases_on `h` \\ fs [enc_pair_def]
    \\ rw [] \\ eq_tac \\ rw [] \\ metis_tac [])
  THEN1
   (rename [`OPTION_MAP _ x = _ y`] \\ Cases_on `x` \\ Cases_on `y` \\ fs [])
  THEN1
   (Cases_on `i = e` \\ rw []
    \\ qid_spec_tac `l` \\ Induct_on `x_18`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l` \\ fs []
    \\ PairCases_on `h` \\ fs [enc_pair_def]
    \\ rw [] \\ eq_tac \\ rw [] \\ metis_tac [])
  THEN1
   (rename [`x44 = x55 /\ _`] \\ Cases_on `x44 = x55` \\ fs []
    \\ qid_spec_tac `l` \\ Induct_on `x_10`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l` \\ fs [])
  THEN1
   (rename [`OPTION_MAP _ x = _ y`]
    \\ `OPTION_MAP enc_id x = OPTION_MAP enc_id y <=> x = y` by
         (Cases_on `x` \\ Cases_on `y` \\ fs []) \\ fs []
    \\ Cases_on `x = y` \\ fs []
    \\ qid_spec_tac `l` \\ Induct_on `x_5`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l` \\ fs [])
  \\ Cases_on `i = e` \\ fs []
  \\ qid_spec_tac `l` \\ Induct_on `x_2`
  \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l` \\ fs []
  \\ PairCases_on `h` \\ fs [enc_pair_def] \\ metis_tac []
QED

Theorem AST_EXP_TYPE_eq_enc:
  !l v. AST_EXP_TYPE l v <=> v = enc_exp l
Proof
  recInduct (theorem "enc_exp_ind") \\ rpt conj_tac \\ rpt gen_tac
  \\ fs [AST_EXP_TYPE_def,enc_exp_def,AST_OP_TYPE_eq_enc,AST_LIT_TYPE_eq_enc,
         AST_AST_T_TYPE_eq_enc,AST_LOP_TYPE_eq_enc,LOCATION_LOCS_TYPE_eq_enc,
         NAMESPACE_ID_TYPE_eq_enc]
  \\ rw []
  THEN1
   (qsuff_tac `!v. LIST_TYPE
           (PAIR_TYPE HOL_STRING_TYPE
             (PAIR_TYPE HOL_STRING_TYPE AST_EXP_TYPE)) x_24 v <=>
         v = enc_list (MAP (λ(f,x,e).
                     enc_pair (Litv (StrLit f))
                       (enc_pair (Litv (StrLit x)) (enc_exp e))) x_24)`
    THEN1 fs []
    \\ Induct_on `x_24` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD] \\ rw []
    \\ first_x_assum (fn th => mp_tac th \\ impl_tac)
    THEN1 metis_tac []
    \\ fs [PAIR_TYPE_def,enc_pair_def,HOL_STRING_TYPE_def,STRING_TYPE_def,
          mlstringTheory.implode_def])
  THEN1
   (rename [`OPTION_MAP _ x99`] \\ Cases_on `x99`
    \\ fs [OPTION_TYPE_def,enc_option_def,HOL_STRING_TYPE_def,STRING_TYPE_def,
          mlstringTheory.implode_def])
  THEN1
   (qsuff_tac `!v. LIST_TYPE (PAIR_TYPE AST_PAT_TYPE AST_EXP_TYPE) x_18 v <=>
         v = enc_list (MAP (λ(p,e). enc_pair (enc_pat p) (enc_exp e)) x_18)`
    THEN1 fs []
    \\ Induct_on `x_18` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD] \\ rw []
    \\ first_x_assum (fn th => mp_tac th \\ impl_tac)
    THEN1 metis_tac []
    \\ fs [PAIR_TYPE_def,enc_pair_def,HOL_STRING_TYPE_def,STRING_TYPE_def,
          mlstringTheory.implode_def,PULL_EXISTS,AST_PAT_TYPE_eq_enc])
  THEN1
   (qsuff_tac `!v. LIST_TYPE AST_EXP_TYPE x_10 v <=>
         v = enc_list (MAP (λa. enc_exp a) x_10)`
    THEN1 fs []
    \\ Induct_on `x_10` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD] \\ rw [])
  THEN1
   (rename [`OPTION_TYPE _ x`] \\ Cases_on `x` \\ fs [OPTION_TYPE_def,enc_option_def]
    \\ `!v. LIST_TYPE AST_EXP_TYPE x_5 v <=>
            v = enc_list (MAP (λa. enc_exp a) x_5)`
         by (Induct_on `x_5` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD] \\ rw [])
    \\ fs [NAMESPACE_ID_TYPE_eq_enc,enc_option_def])

  THEN1
   (qsuff_tac `!v. LIST_TYPE (PAIR_TYPE AST_PAT_TYPE AST_EXP_TYPE) x_2 v <=>
         v = enc_list (MAP (λ(p,e). enc_pair (enc_pat p) (enc_exp e)) x_2)`
    THEN1 fs []
    \\ Induct_on `x_2` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD] \\ rw []
    \\ first_x_assum (fn th => mp_tac th \\ impl_tac)
    THEN1 metis_tac []
    \\ fs [PAIR_TYPE_def,enc_pair_def,HOL_STRING_TYPE_def,STRING_TYPE_def,
          mlstringTheory.implode_def,PULL_EXISTS,AST_PAT_TYPE_eq_enc])
QED

Definition enc_dec_def:
  enc_dec (Denv x_19) =
    Conv (SOME (TypeStamp "Denv" 21)) [Litv (StrLit x_19)] ∧
  enc_dec (Dlocal x_18 x_17) =
    Conv (SOME (TypeStamp "Dlocal" 21))
      [enc_list (MAP enc_dec x_18); enc_list (MAP enc_dec x_17)] ∧
  enc_dec (Dmod x_16 x_15) =
    Conv (SOME (TypeStamp "Dmod" 21))
      [Litv (StrLit x_16); enc_list (MAP enc_dec x_15)] ∧
  enc_dec (Dexn x_14 x_13 x_12) =
    Conv (SOME (TypeStamp "Dexn" 21))
      [enc_locs x_14; Litv (StrLit x_13); enc_list (MAP enc_ast_t x_12)] ∧
  enc_dec (Dtabbrev x_11 x_10 x_9 x_8) =
    Conv (SOME (TypeStamp "Dtabbrev" 21))
      [enc_locs x_11; enc_list (MAP (\s. Litv (StrLit s)) x_10);
       Litv (StrLit x_9); enc_ast_t x_8] ∧
  enc_dec (Dtype x_7 x_6) =
    Conv (SOME (TypeStamp "Dtype" 21))
      [enc_locs x_7;
       enc_list (MAP ( \ (vs,s,l).
                  enc_pair (enc_list (MAP (\s. Litv (StrLit s)) vs))
                    (enc_pair (Litv (StrLit s))
                       (enc_list (MAP ( \ (x,xs). enc_pair (Litv (StrLit x))
                          (enc_list (MAP enc_ast_t xs))) l)))) x_6)] ∧
  enc_dec (Dletrec x_5 x_4) =
    Conv (SOME (TypeStamp "Dletrec" 21))
      [enc_locs x_5;
       enc_list (MAP ( \ (f,x,e). enc_pair (Litv (StrLit f))
                               (enc_pair (Litv (StrLit x))
                                         (enc_exp e))) x_4)] ∧
  enc_dec (Dlet x_3 x_2 x_1) =
    Conv (SOME (TypeStamp "Dlet" 21))
      [enc_locs x_3; enc_pat x_2; enc_exp x_1]
Termination
  WF_REL_TAC `measure dec_size`
  \\ `!l e. MEM e l ==> dec_size e < dec1_size l` by
       (Induct \\ fs [dec_size_def] \\ rw [] \\ fs [dec_size_def] \\ res_tac \\ fs [])
  \\ rw [] \\ fs [dec_size_def]
  \\ res_tac \\ fs []
End

Theorem enc_dec_11[simp]:
  !i j. enc_dec i = enc_dec j <=> i = j
Proof
  ho_match_mp_tac (theorem "enc_dec_ind")
  \\ rpt conj_tac \\ fs [PULL_FORALL]
  \\ Cases_on `j` \\ fs [enc_dec_def]
  \\ fs [FORALL_PROD] \\ rw []
  THEN1
   (rename [`MAP _ l1 = MAP _ l2`]
    \\ `MAP (λa. enc_dec a) l1 = MAP (λa. enc_dec a) l2 <=> l1 = l2` by
      (qid_spec_tac `l2` \\ Induct_on `l1`
       \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l2` \\ fs [])
    \\ fs [] \\ Cases_on `l1 = l2` \\ fs []
    \\ rename [`MAP _ r1 = MAP _ r2`]
    \\ `MAP (λa. enc_dec a) r1 = MAP (λa. enc_dec a) r2 <=> r1 = r2` by
      (qid_spec_tac `r2` \\ Induct_on `r1`
       \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `r2` \\ fs []))
  THEN1
   (rename [`x = y /\ _`] \\ Cases_on `x = y` \\ fs [] \\ rveq
    \\ rename [`MAP _ l1 = MAP _ l2`]
    \\ qid_spec_tac `l2` \\ Induct_on `l1`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l2` \\ fs [])
  THEN1
   (rename [`x = y /\ _`] \\ Cases_on `x = y` \\ fs [] \\ rveq
    \\ rename [`x = y /\ _`] \\ Cases_on `x = y` \\ fs [] \\ rveq
    \\ rename [`MAP _ l1 = MAP _ l2`]
    \\ qid_spec_tac `l2` \\ Induct_on `l1`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l2` \\ fs [])
  THEN1
   (rename [`x = y /\ _`] \\ Cases_on `x = y` \\ fs [] \\ rveq
    \\ rename [`_ /\ x = y`] \\ Cases_on `x = y` \\ fs [] \\ rveq
    \\ rename [`_ /\ x = y`] \\ Cases_on `x = y` \\ fs [] \\ rveq
    \\ rename [`MAP _ l1 = MAP _ l2`]
    \\ qid_spec_tac `l2` \\ Induct_on `l1`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l2` \\ fs [])
  THEN1
   (rename [`x = y /\ _`] \\ Cases_on `x = y` \\ fs [] \\ rveq
    \\ rename [`MAP _ l1 = MAP _ l2`]
    \\ qid_spec_tac `l2` \\ Induct_on `l1`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l2` \\ fs []
    \\ PairCases_on `h` \\ fs [enc_pair_def]
    \\ rewrite_tac [GSYM CONJ_ASSOC]
    \\ rename [`_ /\ x1 = y1 /\ _ /\ l1 = z1`]
    \\ Cases_on `x1 = y1` \\ fs []
    \\ Cases_on `l1 = z1` \\ fs []
    \\ `MAP (λs. Litv (StrLit s)) p_1 = MAP (λs. Litv (StrLit s)) h0 <=> p_1 = h0` by
      (qid_spec_tac `h0` \\ Induct_on `p_1`
       \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `h0` \\ fs []) \\ fs []
    \\ Cases_on `p_1 = h0` \\ fs [] \\ rveq
    \\ rpt (pop_assum kall_tac)
    \\ qid_spec_tac `p_2` \\ Induct_on `h2`
    \\ rw [] \\ Cases_on `p_2` \\ fs []
    \\ rename [`_ x1 = _ x2 /\ _`] \\ PairCases_on `x1` \\ PairCases_on `x2`
    \\ fs []
    \\ qsuff_tac `MAP enc_ast_t x11 = MAP enc_ast_t x21 <=> x11 = x21` \\ fs []
    \\ qid_spec_tac `x11` \\ Induct_on `x21` \\ fs [] \\ Cases_on `x11` \\ fs [])
  THEN1
   (rename [`x = y /\ _`] \\ Cases_on `x = y` \\ fs [] \\ rveq
    \\ rename [`MAP _ l1 = MAP _ l2`]
    \\ qid_spec_tac `l2` \\ Induct_on `l1`
    \\ fs [FORALL_PROD] \\ rw [] \\ Cases_on `l2` \\ fs []
    \\ PairCases_on `h` \\ fs [enc_pair_def])
QED

Theorem AST_DEC_TYPE_eq_enc:
  !l v. AST_DEC_TYPE l v <=> v = enc_dec l
Proof
  recInduct (theorem "enc_dec_ind") \\ rpt conj_tac \\ rpt gen_tac
  \\ fs [AST_EXP_TYPE_eq_enc,AST_OP_TYPE_eq_enc,AST_LIT_TYPE_eq_enc,
         AST_AST_T_TYPE_eq_enc,AST_LOP_TYPE_eq_enc,LOCATION_LOCS_TYPE_eq_enc,
         NAMESPACE_ID_TYPE_eq_enc,enc_dec_def,AST_DEC_TYPE_def,AST_PAT_TYPE_eq_enc]
  \\ rw []
  THEN1
   (`!v. LIST_TYPE AST_DEC_TYPE x_17 v <=>
         v = enc_list (MAP (λa. enc_dec a) x_17)` by
     (Induct_on `x_17` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD] \\ rw [])
     \\ `!v. LIST_TYPE AST_DEC_TYPE x_18 v <=>
         v = enc_list (MAP (λa. enc_dec a) x_18)` by
     (Induct_on `x_18` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD] \\ rw [])
    \\ fs [])
  THEN1
   (`!v. LIST_TYPE AST_DEC_TYPE x_15 v <=>
         v = enc_list (MAP (λa. enc_dec a) x_15)` by
     (Induct_on `x_15` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD] \\ rw [])
    \\ fs [])
  THEN1
   (`!v. LIST_TYPE AST_AST_T_TYPE x_12 v <=>
         v = enc_list (MAP enc_ast_t x_12)` by
     (Induct_on `x_12` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD]
      \\ rw [AST_AST_T_TYPE_eq_enc])
    \\ fs [])
  THEN1
   (`!v. LIST_TYPE HOL_STRING_TYPE x_10 v <=>
         v = enc_list (MAP (λs. Litv (StrLit s)) x_10)` by
     (Induct_on `x_10` \\ fs [enc_list_def,LIST_TYPE_def,FORALL_PROD]
      \\ rw [HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def])
    \\ fs [])
  THEN1
   (qsuff_tac
     `!v. LIST_TYPE
           (PAIR_TYPE (LIST_TYPE HOL_STRING_TYPE)
              (PAIR_TYPE HOL_STRING_TYPE
                 (LIST_TYPE
                    (PAIR_TYPE HOL_STRING_TYPE (LIST_TYPE AST_AST_T_TYPE)))))
          x_6 v <=>
        v = enc_list
        (MAP
           (λ(vs,s,l).
                enc_pair (enc_list (MAP (λs. Litv (StrLit s)) vs))
                  (enc_pair (Litv (StrLit s))
                     (enc_list
                        (MAP
                           (λ(x,xs).
                                enc_pair (Litv (StrLit x))
                                  (enc_list (MAP enc_ast_t xs))) l)))) x_6)` THEN1 fs []
    \\ Induct_on `x_6` \\ fs [LIST_TYPE_def,enc_list_def]
    \\ fs [FORALL_PROD,EXISTS_PROD,PAIR_TYPE_def,enc_pair_def,PULL_EXISTS,
           HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def,
           AST_EXP_TYPE_eq_enc]
     \\ `!l v. LIST_TYPE HOL_STRING_TYPE l v <=>
               v = enc_list (MAP (\s. Litv (StrLit s)) l)` by
           (Induct \\ fs [HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def,
             LIST_TYPE_def,enc_list_def])
     \\ qsuff_tac
        `!l v. LIST_TYPE
                 (PAIR_TYPE HOL_STRING_TYPE (LIST_TYPE AST_AST_T_TYPE)) l v <=>
               v = enc_list (MAP (λ(x,xs).
                               Conv NONE
                                 [Litv (StrLit x);
                                  enc_list (MAP enc_ast_t xs)]) l)` THEN1 fs []
     \\ Induct \\ fs [HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def,
            FORALL_PROD,EXISTS_PROD,PAIR_TYPE_def,enc_pair_def,PULL_EXISTS,
            LIST_TYPE_def,enc_list_def]
     \\ `!l v. LIST_TYPE AST_AST_T_TYPE l v <=>
               v = enc_list (MAP enc_ast_t l)` by
           (Induct \\ fs [LIST_TYPE_def,enc_list_def,AST_AST_T_TYPE_eq_enc])
     \\ fs [])
  \\ qsuff_tac
   `!v. LIST_TYPE
          (PAIR_TYPE HOL_STRING_TYPE (PAIR_TYPE HOL_STRING_TYPE AST_EXP_TYPE))
          x_4 v <=>
        v = enc_list (MAP (λ(f,x,e).
                enc_pair (Litv (StrLit f))
                  (enc_pair (Litv (StrLit x)) (enc_exp e))) x_4)` THEN1 fs []
  \\ Induct_on `x_4` \\ fs [LIST_TYPE_def,enc_list_def]
  \\ fs [FORALL_PROD,EXISTS_PROD,PAIR_TYPE_def,enc_pair_def,PULL_EXISTS,
         HOL_STRING_TYPE_def,STRING_TYPE_def,mlstringTheory.implode_def,
       AST_EXP_TYPE_eq_enc]
QED

Definition decs_to_v_def:
  decs_to_v ds = enc_list (MAP enc_dec ds)
End

Theorem decs_to_v_11[simp]:
  !i j. decs_to_v i = decs_to_v j <=> i = j
Proof
  Induct \\ Cases_on `j` \\ fs [decs_to_v_def,enc_list_def]
QED

Theorem AST_DEC_TYPE_eq_enc:
  !l v. LIST_TYPE AST_DEC_TYPE l v <=> v = decs_to_v l
Proof
  Induct
  \\ fs [LIST_TYPE_def,enc_list_def,decs_to_v_def,AST_DEC_TYPE_eq_enc]
QED

Definition v_to_decs_def:
  v_to_decs v = some ds. v = decs_to_v ds
End

Theorem decs_to_v_v_to_decs:
  !ds. v_to_decs (decs_to_v ds) = SOME ds
Proof
  fs [v_to_decs_def]
QED

Theorem AST_DEC_TYPE_eq_v_to_decs:
  !l v. LIST_TYPE AST_DEC_TYPE l v <=> v_to_decs v = SOME l
Proof
  simp [AST_DEC_TYPE_eq_enc,v_to_decs_def]
  \\ fs [optionTheory.some_def] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

val _ = (print_asts := true);
val _ = export_theory();

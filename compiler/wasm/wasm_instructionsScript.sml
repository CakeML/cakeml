(*
  Ready-to-use Wasm instructions
*)

Theory wasm_instructions
Ancestors wasmLang

Definition I64_EQ_def:
  I64_EQ = Numeric (N_compare (Eq Int W64))
End
Definition I32_EQ_def:
  I32_EQ = Numeric (N_compare (Eq Int W32))
End

Definition I64_NE_def:
  I64_NE = Numeric (N_compare (Ne Int W64))
End
Definition I32_NE_def:
  I32_NE = Numeric (N_compare (Ne Int W32))
End

Definition I64_LT_U_def:
  I64_LT_U = Numeric (N_compare (Lt_ Unsigned W64))
End
Definition I32_LT_U_def:
  I32_LT_U = Numeric (N_compare (Lt_ Unsigned W32))
End

Definition I64_GT_U_def:
  I64_GT_U = Numeric (N_compare (Gt_ Unsigned W64))
End
Definition I32_GT_U_def:
  I32_GT_U = Numeric (N_compare (Gt_ Unsigned W32))
End

Definition I64_LE_U_def:
  I64_LE_U = Numeric (N_compare (Le_ Unsigned W64))
End
Definition I32_LE_U_def:
  I32_LE_U = Numeric (N_compare (Le_ Unsigned W32))
End

Definition I64_GE_U_def:
  I64_GE_U = Numeric (N_compare (Ge_ Unsigned W64))
End
Definition I32_GE_U_def:
  I32_GE_U = Numeric (N_compare (Ge_ Unsigned W32))
End

Definition I64_LT_S_def:
  I64_LT_S = Numeric (N_compare (Lt_ Signed W64))
End
Definition I32_LT_S_def:
  I32_LT_S = Numeric (N_compare (Lt_ Signed W32))
End

Definition I64_GT_S_def:
  I64_GT_S = Numeric (N_compare (Gt_ Signed W64))
End
Definition I32_GT_S_def:
  I32_GT_S = Numeric (N_compare (Gt_ Signed W32))
End

Definition I64_LE_S_def:
  I64_LE_S = Numeric (N_compare (Le_ Signed W64))
End
Definition I32_LE_S_def:
  I32_LE_S = Numeric (N_compare (Le_ Signed W32))
End

Definition I64_GE_S_def:
  I64_GE_S = Numeric (N_compare (Ge_ Signed W64))
End
Definition I32_GE_S_def:
  I32_GE_S = Numeric (N_compare (Ge_ Signed W32))
End

Definition I64_EQZ_def:
  I64_EQZ = Numeric (N_eqz W64)
End
Definition I32_EQZ_def:
  I32_EQZ = Numeric (N_eqz W32)
End

Definition I64_CONST_def:
  I64_CONST w = Numeric (N_const64 Int w)
End
Definition I32_CONST_def:
  I32_CONST w = Numeric (N_const32 Int w)
End

Definition I64_ADD_def:
  I64_ADD = Numeric (N_binary (Add Int W64))
End
Definition I32_ADD_def:
  I32_ADD = Numeric (N_binary (Add Int W32))
End

Definition I64_SUB_def:
  I64_SUB = Numeric (N_binary (Sub Int W64))
End
Definition I32_SUB_def:
  I32_SUB = Numeric (N_binary (Sub Int W32))
End

Definition I64_MUL_def:
  I64_MUL = Numeric (N_binary (Mul Int W64))
End
Definition I32_MUL_def:
  I32_MUL = Numeric (N_binary (Mul Int W32))
End

Definition I64_AND_def:
  I64_AND = Numeric (N_binary (And W64))
End
Definition I32_AND_def:
  I32_AND = Numeric (N_binary (And W32))
End

Definition I64_OR_def:
  I64_OR = Numeric (N_binary (Or W64))
End
Definition I32_OR_def:
  I32_OR = Numeric (N_binary (Or W32))
End

Definition I64_XOR_def:
  I64_XOR = Numeric (N_binary (Xor W64))
End
Definition I32_XOR_def:
  I32_XOR = Numeric (N_binary (Xor W32))
End

Definition I64_SHL_def:
  I64_SHL = Numeric (N_binary (Shl W64))
End
Definition I32_SHL_def:
  I32_SHL = Numeric (N_binary (Shl W32))
End

Definition I64_SHR_S_def:
  I64_SHR_S = Numeric (N_binary (Shr_ Signed W64))
End
Definition I32_SHR_S_def:
  I32_SHR_S = Numeric (N_binary (Shr_ Signed W32))
End

Definition I64_SHR_U_def:
  I64_SHR_U = Numeric (N_binary (Shr_ Unsigned W64))
End
Definition I32_SHR_U_def:
  I32_SHR_U = Numeric (N_binary (Shr_ Unsigned W32))
End

Definition I64_ROTR_def:
  I64_ROTR = Numeric (N_binary (Rotr W64))
End
Definition I32_ROTR_def:
  I32_ROTR = Numeric (N_binary (Rotr W32))
End

Definition I64_DIV_S_def:
  I64_DIV_S = Numeric (N_binary (Div_ Signed W64))
End
Definition I32_DIV_S_def:
  I32_DIV_S = Numeric (N_binary (Div_ Signed W32))
End

Definition I64_DIV_U_def:
  I64_DIV_U = Numeric (N_binary (Div_ Unsigned W64))
End
Definition I32_DIV_U_def:
  I32_DIV_U = Numeric (N_binary (Div_ Unsigned W32))
End

Definition I32_WRAP_I64_def:
  I32_WRAP_I64 = Numeric (N_convert WrapI64)
End

Definition GLOBAL_GET_def:
  GLOBAL_GET i = Variable (GlobalGet (n2w i))
End

Definition GLOBAL_SET_def:
  GLOBAL_SET i = Variable (GlobalSet (n2w i))
End

Definition LOCAL_GET_def:
  LOCAL_GET i = Variable (LocalGet (n2w i))
End

Definition LOCAL_SET_def:
  LOCAL_SET i = Variable (LocalSet (n2w i))
End

Definition LOCAL_TEE_def:
  LOCAL_TEE i = Variable (LocalTee (n2w i))
End

Definition RETURN_def:
  RETURN = wasmLang$Return
End

Definition CALL_def:
  CALL i = wasmLang$Call (n2w i)
End

Definition CALL_INDIRECT_def:
  CALL_INDIRECT ft = CallIndirect 0w ft
End

Definition RETURN_CALL_def:
  RETURN_CALL i = ReturnCall (n2w i)
End

Definition RETURN_CALL_INDIRECT_def:
  RETURN_CALL_INDIRECT ft = ReturnCallIndirect 0w ft
End

Definition SELECT_def:
  SELECT = Parametric Select
End

Definition I64_EXTEND32_U_def:
  I64_EXTEND32_U = Numeric (N_unary (ExtendI32_ Unsigned))
End

Definition I64_LOAD_def:
  I64_LOAD ofs = MemRead (Load Int W64 ofs 8w)
End

Definition I64_LOAD8_S_def:
  I64_LOAD8_S ofs = MemRead (LoadNarrow I8x16 Signed W64 ofs 1w)
End

Definition I64_LOAD8_U_def:
  I64_LOAD8_U ofs = MemRead (LoadNarrow I8x16 Unsigned W64 ofs 1w)
End

Definition I64_LOAD16_S_def:
  I64_LOAD16_S ofs = MemRead (LoadNarrow I16x8 Signed W64 ofs 2w)
End

Definition I64_LOAD16_U_def:
  I64_LOAD16_U ofs = MemRead (LoadNarrow I16x8 Unsigned W64 ofs 2w)
End

Definition I64_LOAD32_S_def:
  I64_LOAD32_S ofs = MemRead (LoadNarrow32 Signed ofs 4w)
End

Definition I64_LOAD32_U_def:
  I64_LOAD32_U ofs = MemRead (LoadNarrow32 Unsigned ofs 4w)
End

Definition I64_STORE_def:
  I64_STORE ofs = MemWrite (Store Int W64 ofs 8w)
End

Definition I64_STORE8_def:
  I64_STORE8 ofs = MemWrite (StoreNarrow I8x16 W64 ofs 1w)
End

Definition I64_STORE16_def:
  I64_STORE16 ofs = MemWrite (StoreNarrow I16x8 W64 ofs 2w)
End

Definition I64_STORE32_def:
  I64_STORE32 ofs = MemWrite (StoreNarrow32 ofs 4w)
End

Definition i32_def:
  i32 = Tnum Int W32
End

Definition i64_def:
  i64 = Tnum Int W64
End

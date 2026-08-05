(*
  Utility functions over tokens.
  TODO: perhaps should just appear in tokensTheory.
*)
Theory tokenUtils
Ancestors
  tokens grammar[qualified]
Libs
  preamble


Definition isInt_def[simp]:
  isInt (IntT i) = T ∧
  isInt _ = F
End

Definition isString_def[simp]:
  isString (StringT _) = T ∧
  isString _ = F
End

Definition isAlphaT_def[simp]:
  isAlphaT (AlphaT s) = T ∧
  isAlphaT _ = F
End

Definition isSymbolT_def[simp]:
  isSymbolT (SymbolT s) = T ∧
  isSymbolT _ = F
End

Definition isAlphaSym_def[simp]:
  isAlphaSym (AlphaT _) = T ∧
  isAlphaSym (SymbolT _) = T ∧
  isAlphaSym _ = F
End

Definition isTyvarT_def[simp]:
  isTyvarT (TyvarT _) = T ∧
  isTyvarT _ = F
End

Definition isWhitespaceT_def[simp]:
  (isWhitespaceT (WhitespaceT _) ⇔ T) ∧
  (isWhitespaceT _ ⇔ F)
End

Definition isCharT_def[simp]:
  (isCharT (CharT _) ⇔ T) ∧
  (isCharT _ ⇔ F)
End

Definition isWordT_def[simp]:
  (isWordT (WordT _) ⇔ T) ∧
  (isWordT _ ⇔ F)
End

Definition isLongidT_def[simp]:
  (isLongidT (LongidT _ _) ⇔ T) ∧
  (isLongidT _ ⇔ F)
End

Definition destLongidT_def[simp]:
  (destLongidT (LongidT str s) = SOME (str,s)) ∧
  (destLongidT _ = NONE)
End

Theorem destLongidT_EQ_SOME[simp]:
   destLongidT t = SOME strs ⇔ ∃str s. t = LongidT str s ∧ strs = (str, s)
Proof
  Cases_on `t` >> simp[] >> metis_tac[]
QED

Definition destTyvarPT_def[simp]:
  (destTyvarPT (Lf (TOK (TyvarT s),_)) = SOME s) ∧
  (destTyvarPT _ = NONE)
End

Definition destLf_def[simp]:
  (destLf (Lf (x,_)) = SOME x) ∧ (destLf _ = NONE)
End

Definition destTOK_def[simp]:
  (destTOK (TOK t) = SOME t) ∧ (destTOK _ = NONE)
End

Definition destAlphaT_def[simp]:
  (destAlphaT (AlphaT s) = SOME s) ∧ (destAlphaT _ = NONE)
End

Theorem destAlphaT_EQ_SOME[simp]:
   destAlphaT t = SOME s ⇔ t = AlphaT s
Proof
  Cases_on `t` >> simp[]
QED

Definition destSymbolT_def[simp]:
  (destSymbolT (SymbolT s) = SOME s) ∧
  (destSymbolT _ = NONE)
End

Theorem destSymbolT_EQ_SOME[simp]:
   destSymbolT t = SOME s ⇔ t = SymbolT s
Proof
  Cases_on `t` >> simp[]
QED

Definition destIntT_def[simp]:
  (destIntT (IntT i) = SOME i) ∧
  (destIntT _ = NONE)
End

Definition destCharT_def[simp]:
  (destCharT (CharT c) = SOME c) ∧
  (destCharT _ = NONE)
End

Definition destStringT_def[simp]:
  (destStringT (StringT s) = SOME s) ∧
  (destStringT _ = NONE)
End

Definition destWordT_def[simp]:
  (destWordT (WordT w) = SOME w) ∧
  (destWordT _ = NONE)
End

Definition destFFIT_def[simp]:
  (destFFIT (FFIT s) = SOME s) ∧
  (destFFIT _ = NONE)
End

Definition destREPLIDT_def[simp]:
  (destREPLIDT (REPLIDT s) = SOME s) ∧
  (destREPLIDT _ = NONE)
End


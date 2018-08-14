open preamble tokensTheory

val _ = new_theory "tokenUtils"
val _ = set_grammar_ancestry ["tokens", "grammar"]

(* ----------------------------------------------------------------------
    Utility functions over tokens; perhaps should just appear in
    TokensTheory
   ---------------------------------------------------------------------- *)

val isInt_def = Define`
  isInt (IntT i) = T ∧
  isInt _ = F
`;
val _ = export_rewrites ["isInt_def"]

val isString_def = Define`
  isString (StringT _) = T ∧
  isString _ = F
`;
val _ = export_rewrites ["isString_def"]

val isAlphaT_def = Define`
  isAlphaT (AlphaT s) = T ∧
  isAlphaT _ = F
`;
val _ = export_rewrites ["isAlphaT_def"]

val isSymbolT_def = Define`isSymbolT (SymbolT s) = T ∧ isSymbolT _ = F`
val _ = export_rewrites ["isSymbolT_def"]

val isAlphaSym_def = Define`
  isAlphaSym (AlphaT _) = T ∧
  isAlphaSym (SymbolT _) = T ∧
  isAlphaSym _ = F
`;
val _ = export_rewrites ["isAlphaSym_def"]

val isTyvarT_def = Define`isTyvarT (TyvarT _) = T ∧ isTyvarT _ = F`
val _ = export_rewrites ["isTyvarT_def"]

val isWhitespaceT_def = Define`
  (isWhitespaceT (WhitespaceT _) ⇔ T) ∧
  (isWhitespaceT _ ⇔ F)
`

val isCharT_def = Define`
  (isCharT (CharT _) ⇔ T) ∧
  (isCharT _ ⇔ F)
`;
val _ = export_rewrites ["isCharT_def"]

val isWordT_def = Define`
  (isWordT (WordT _) ⇔ T) ∧
  (isWordT _ ⇔ F)
`;
val _ = export_rewrites ["isWordT_def"]

val isLongidT_def = Define`
  (isLongidT (LongidT _ _ _) ⇔ T) ∧
  (isLongidT _ ⇔ F)
`
val _ = export_rewrites ["isLongidT_def"]

val destLongidT_def = Define`
  (destLongidT (LongidT str ms s) = SOME (str,ms,s)) ∧
  (destLongidT _ = NONE)
`
val _ = export_rewrites ["destLongidT_def"]

val destLongidT_EQ_SOME = Q.store_thm(
  "destLongidT_EQ_SOME[simp]",
  `destLongidT t = SOME strs ⇔
     ∃str ms s. t = LongidT str ms s ∧ strs = (str, ms, s)`,
  Cases_on `t` >> simp[] >> metis_tac[]);

val destTyvarPT_def = Define`
  (destTyvarPT (Lf (TOK (TyvarT s),_)) = SOME s) ∧
  (destTyvarPT _ = NONE)
`;
val _ = export_rewrites ["destTyvarPT_def"]

val destLf_def = Define`(destLf (Lf (x,_)) = SOME x) ∧ (destLf _ = NONE)`;
val _ = export_rewrites ["destLf_def"]

val destTOK_def = Define`(destTOK (TOK t) = SOME t) ∧ (destTOK _ = NONE)`;
val _ = export_rewrites ["destTOK_def"]

val destAlphaT_def = Define`
  (destAlphaT (AlphaT s) = SOME s) ∧ (destAlphaT _ = NONE)
`;
val _ = export_rewrites ["destAlphaT_def"]

val destAlphaT_EQ_SOME = Q.store_thm(
  "destAlphaT_EQ_SOME[simp]",
  `destAlphaT t = SOME s ⇔ t = AlphaT s`,
  Cases_on `t` >> simp[]);

val destSymbolT_def = Define`
  (destSymbolT (SymbolT s) = SOME s) ∧
  (destSymbolT _ = NONE)
`;
val _ = export_rewrites ["destSymbolT_def"]

val destSymbolT_EQ_SOME = Q.store_thm(
  "destSymbolT_EQ_SOME[simp]",
  `destSymbolT t = SOME s ⇔ t = SymbolT s`,
  Cases_on `t` >> simp[]);

val destIntT_def = Define`
  (destIntT (IntT i) = SOME i) ∧
  (destIntT _ = NONE)
`;
val _ = export_rewrites ["destIntT_def"]

val destCharT_def = Define`
  (destCharT (CharT c) = SOME c) ∧
  (destCharT _ = NONE)
`;
val _ = export_rewrites ["destCharT_def"]

val destStringT_def = Define`
  (destStringT (StringT s) = SOME s) ∧
  (destStringT _ = NONE)
`;
val _ = export_rewrites ["destStringT_def"]

val destWordT_def = Define`
  (destWordT (WordT w) = SOME w) ∧
  (destWordT _ = NONE)
`;
val _ = export_rewrites ["destWordT_def"]

val destFFIT_def = Define`
  (destFFIT (FFIT s) = SOME s) ∧
  (destFFIT _ = NONE)
`;
val _ = export_rewrites ["destFFIT_def"]

val _ = export_theory()

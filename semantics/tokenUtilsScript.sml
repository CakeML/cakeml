open HolKernel Parse boolLib bossLib

open TokensTheory

val _ = new_theory "tokenUtils"

(* ----------------------------------------------------------------------
    Utility functions over tokens; perhaps should just appear in
    TokensTheory
   ---------------------------------------------------------------------- *)

val isInt_def = Define`
  isInt (IntT i) = T ∧
  isInt _ = F
`;
val _ = export_rewrites ["isInt_def"]

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

val isLongidT_def = Define`
  (isLongidT (LongidT _ _) ⇔ T) ∧
  (isLongidT _ ⇔ F)
`
val _ = export_rewrites ["isLongidT_def"]

val destLongidT_def = Define`
  (destLongidT (LongidT str s) = SOME (str,s)) ∧
  (destLongidT _ = NONE)
`
val _ = export_rewrites ["destLongidT_def"]

val destTyvarPT_def = Define`
  (destTyvarPT (Lf (TOK (TyvarT s))) = SOME s) ∧
  (destTyvarPT _ = NONE)
`;
val _ = export_rewrites ["destTyvarPT_def"]

val destLf_def = Define`(destLf (Lf x) = SOME x) ∧ (destLf _ = NONE)`;
val _ = export_rewrites ["destLf_def"]

val destTOK_def = Define`(destTOK (TOK t) = SOME t) ∧ (destTOK _ = NONE)`;
val _ = export_rewrites ["destTOK_def"]

val destAlphaT_def = Define`
  (destAlphaT (AlphaT s) = SOME s) ∧ (destAlphaT _ = NONE)
`;
val _ = export_rewrites ["destAlphaT_def"]

val destSymbolT_def = Define`
  (destSymbolT (SymbolT s) = SOME s) ∧
  (destSymbolT _ = NONE)
`;
val _ = export_rewrites ["destSymbolT_def"]

val destIntT_def = Define`
  (destIntT (IntT i) = SOME i) ∧
  (destIntT _ = NONE)
`;
val _ = export_rewrites ["destIntT_def"]

val _ = export_theory()

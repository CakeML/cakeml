open HolKernel Parse boolLib bossLib

open TokensTheory

val _ = new_theory "mmlTokenUtils"

(* ----------------------------------------------------------------------
    Utility functions over tokens; perhaps should just appear in
    TokensTheory
   ---------------------------------------------------------------------- *)

val isInt_def = Define`
  isInt (IntT i) = T ∧
  isInt _ = F
`;

val isAlphaT_def = Define`
  isAlphaT (AlphaT s) = T ∧
  isAlphaT _ = F
`;

val isSymbolT_def = Define`isSymbolT (SymbolT s) = T ∧ isSymbolT _ = F`

val isAlphaSym_def = Define`
  isAlphaSym (AlphaT _) = T ∧
  isAlphaSym (SymbolT _) = T ∧
  isAlphaSym _ = F
`;

val isTyvarT_def = Define`isTyvarT (TyvarT _) = T ∧ isTyvarT _ = F`

val destTyvarPT_def = Define`
  (destTyvarPT (Lf (TOK (TyvarT s))) = SOME s) ∧
  (destTyvarPT _ = NONE)
`;

val destLf_def = Define`(destLf (Lf x) = SOME x) ∧ (destLf _ = NONE)`;

val destTOK_def = Define`(destTOK (TOK t) = SOME t) ∧ (destTOK _ = NONE)`;

val destAlphaT_def = Define`
  (destAlphaT (AlphaT s) = SOME s) ∧
  (destAlphaT _ = NONE)
`;

val destSymbolT_def = Define`
  (destSymbolT (SymbolT s) = SOME s) ∧
  (destSymbolT _ = NONE)
`;

val destIntT_def = Define`
  (destIntT (IntT i) = SOME i) ∧
  (destIntT _ = NONE)
`;

val _ = export_theory()

open preamble mlstringTheory mlintTheory

val _ = new_theory "mlnum";

val toString_def = Define`
  toString n = implode (toChars (n MOD maxSmall_DEC) (n DIV maxSmall_DEC) "")`;

val toString_thm = Q.store_thm("toString_thm",
  `toString n = implode (num_to_dec_string n)`,
  `0 < maxSmall_DEC` by EVAL_TAC
  \\ rw[toString_def,toChars_thm]
  \\ AP_TERM_TAC
  \\ qspec_then`maxSmall_DEC`mp_tac DIVISION
  \\ simp []);

val fromString_unsafe_def = Define`
  fromString_unsafe str = fromChars_unsafe (strlen str) str`;

val fromString_def = Define`
  fromString str = fromChars (strlen str) str`;

val fromString_unsafe_thm = Q.store_thm("fromString_unsafe_thm",
  `∀str. EVERY isDigit str ⇒
         fromString_unsafe (strlit str) = num_from_dec_string str`,
  rw [fromString_unsafe_def
     , fromChars_range_unsafe_eq
     , fromChars_range_unsafe_thm]);

val fromString_thm = Q.store_thm("fromString_thm",
  `∀str. EVERY isDigit str ⇒
         fromString (strlit str) = SOME (num_from_dec_string str)`,
  rw [fromString_def
     , fromChars_eq_unsafe
     , fromChars_range_unsafe_eq
     , fromChars_range_unsafe_thm]);

val _ = export_theory();

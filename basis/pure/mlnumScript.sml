(*
  Pure functions for the Num module.

  Num is like Int but when we can assume the integers are non-negative. num and
  int are distinct types in HOL even though they are represented by the same
  type (int) in CakeML.
*)
open preamble mlstringTheory mlintTheory

val _ = new_theory "mlnum";

val num_toString_def = Define`
  num_toString n = toChars (n MOD maxSmall_DEC) (n DIV maxSmall_DEC) ""
`;

val toString_def = Define`
  toString n = implode (num_toString n)
`;

Theorem num_toString_thm
  `num_toString n = num_to_dec_string n`
  (`0 < maxSmall_DEC` by EVAL_TAC
  \\ rw[toChars_thm,num_toString_def]
  \\ qspec_then`maxSmall_DEC`mp_tac DIVISION
  \\ simp []
);

Theorem toString_thm
  `toString n = implode (num_to_dec_string n)`
  (rw[toString_def,num_toString_thm]
);

val fromString_unsafe_def = Define`
  fromString_unsafe str = fromChars_unsafe (strlen str) str
`;

(* Replacement of num_from_dec_string *)
val hol_fromString_def = Define`
   hol_fromString s = fromString_unsafe (implode s)
`;

val fromString_def = Define`
  fromString str = fromChars (strlen str) str
`;

Theorem fromString_unsafe_thm
  `∀str. EVERY isDigit str ⇒
         fromString_unsafe (strlit str) = num_from_dec_string str`
  (rw [fromString_unsafe_def
     , fromChars_range_unsafe_eq
     , fromChars_range_unsafe_thm]
);

Theorem hol_fromString_thm
  `∀str. EVERY isDigit str ⇒
         hol_fromString str = num_from_dec_string str`
  (rw [hol_fromString_def,fromString_unsafe_thm,implode_def]
);

Theorem fromString_thm
  `∀str. EVERY isDigit str ⇒
         fromString (strlit str) = SOME (num_from_dec_string str)`
  (rw [fromString_def
     , fromChars_eq_unsafe
     , fromChars_range_unsafe_eq
     , fromChars_range_unsafe_thm]
);

Theorem fromString_IS_SOME_IFF
  `IS_SOME (mlnum$fromString s) ⇔ EVERY isDigit (explode s)`
  (reverse(rw[EQ_IMP_THM])
  >- (
    Cases_on`s` \\ fs[]
    \\ imp_res_tac fromString_thm
    \\ fs[])
  \\ fs[IS_SOME_EXISTS, fromString_def]
  \\ qspecl_then[`strlen s`,`s`]mp_tac fromChars_IS_SOME_IFF
  \\ simp[]
  \\ Cases_on`s` \\ fs[]);

(* this formulation avoids a comparsion using = for better performance *)
Theorem num_cmp_def `
  num_cmp i (j:num) = if i < j then LESS else
                      if j < i then GREATER else EQUAL`
  (fs [comparisonTheory.num_cmp_def] \\ rw []);

val _ = export_theory();

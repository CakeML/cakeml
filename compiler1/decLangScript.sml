open HolKernel Parse boolLib bossLib bigStepTheory;
val _ = new_theory "decLang"

(* Removes declarations. Follows conLang.
 *
 * The AST of decLang differs from conLang in that there is no declarations
 * level, the program is represented by an expressions.
 *)

 (*
val _ = type_abbrev("count_store_genv", ``:'a count_store_trace # ('a option) list``);
*)

val _ = export_theory()

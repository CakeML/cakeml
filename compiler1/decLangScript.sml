open HolKernel Parse boolLib bossLib;
val _ = new_theory "decLang"

(* Removes declarations. Follows conLang.
 *
 * The AST of decLang differs from conLang in that there is no declarations
 * level, the program is represented by an expressions.
 *)

val _ = export_theory()

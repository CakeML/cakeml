open HolKernel Parse boolLib bossLib conLangTheory;

val _ = new_theory "patLang"

(* Removes pattern-matching and variable names. Follows exhLang.
 *
 * The AST of patLang differs from exhLang in that it uses de Bruijn indices,
 * there are no Mat expressions, Handle expressions are simplified to catch and
 * bind any exception without matching on it, and there are new Tag_eq and El
 * expressions for checking the constructor of a compound value and retrieving
 * its arguments. 
 *)

val _ = Datatype`
  op =
   | Op (conLang$op)
   | Tag_eq num
   | El num`;

val _ = Datatype`
  exp =
   | Raise exp
   | Handle exp exp
   | Lit lit
   | Con num (exp list)
   | Var_local num
   | Var_global num
   | Fun exp
   | App op (exp list)
   | If exp exp exp
   | Let exp exp
   | Seq exp exp
   | Letrec (exp list) exp
   | Extend_global num`;

val _ = export_theory()

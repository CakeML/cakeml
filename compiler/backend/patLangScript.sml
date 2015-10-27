open preamble conLangTheory;

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
   | Tag_eq num num
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

val exp_size_def = definition"exp_size_def";

val exp1_size_APPEND = Q.store_thm("exp1_size_APPEND[simp]",
  `patLang$exp1_size (e ++ e2) = exp1_size e + exp1_size e2`,
  Induct_on`e`>>simp[exp_size_def])

val exp1_size_REVERSE = Q.store_thm("exp1_size_REVERSE[simp]",
  `patLang$exp1_size (REVERSE es) = exp1_size es`,
  Induct_on`es`>>simp[exp_size_def])

val _ = export_theory()

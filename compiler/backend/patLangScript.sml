open preamble flatLangTheory;

val _ = new_theory "patLang"
val _ = set_grammar_ancestry ["flatLang"]

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
   | Op (flatLang$op)
   | Run (* TODO: will eventually be inherited from earlier languages via Op *)
   | Tag_eq num num
   | El num`;

val _ = Datatype`
  exp =
   | Raise tra exp
   | Handle tra exp exp
   | Lit tra lit
   | Con tra num (exp list)
   | Var_local tra num
   | Fun tra exp
   | App tra op (exp list)
   | If tra exp exp exp
   | Let tra exp exp
   | Seq tra exp exp
   | Letrec tra (exp list) exp`;

(*TODO: Verify that the introduction of traces wont mess exp_sizes *)
val exp_size_def = definition"exp_size_def";

Theorem exp1_size_APPEND[simp]
  `patLang$exp1_size (e ++ e2) = exp1_size e + exp1_size e2`
  (Induct_on`e`>>simp[exp_size_def])

Theorem exp1_size_REVERSE[simp]
  `patLang$exp1_size (REVERSE es) = exp1_size es`
  (Induct_on`es`>>simp[exp_size_def])

val _ = export_theory()

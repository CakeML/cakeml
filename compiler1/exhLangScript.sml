open HolKernel Parse boolLib bossLib conLangTheory

val _ = new_theory "exhLang"

(* Adds a default case to non-exhaustive patterns. Follows decLang.
 *
 * The AST of exhLang differs from decLang by removing the type annotation from
 * constructors.
 *)

val _ = Datatype`
  pat =
   | Pvar varN
   | Plit lit
   | Pcon num (pat list)
   | Pref pat`;

val _ = Datatype`
  exp =
   | Raise exp
   | Handle exp ((pat # exp) list)
   | Lit lit
   | Con num (exp list)
   | Var_local varN
   | Var_global num
   | Fun varN exp
   | App op (exp list)
   | Mat exp ((pat # exp) list)
   | Let (varN option) exp exp
   | Letrec ((varN # varN # exp) list) exp
   | Extend_global num`;

val _ = export_theory()

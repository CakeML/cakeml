open preamble

open con_tagsTheory

val _ = numLib.prefer_num();

val _ = new_theory "conLang"

(* Removes named datatype constructors. Follows modLang.
 *
 * The AST of conLang differs from modLang by using numbered tags instead of
 * constructor name identifiers for all data constructor patterns and
 * expressions. Constructors explicitly mention the type they are constructing.
 * Also type and exception declarations are removed.
 *)

val _ = Datatype`
 op =
  | Op (ast$op)
  | Init_global_var num`;

val _ = Datatype`
 pat =
  | Pvar varN
  | Plit lit
  | Pcon ((num # tid_or_exn)option) (pat list)
  | Pref pat`;

val _ = Datatype`
 exp =
  | Raise exp
  | Handle exp ((pat # exp) list)
  | Lit lit
  | Con ((num # tid_or_exn)option) (exp list)
  | Var_local varN
  | Var_global num
  | Fun varN exp
  | App op (exp list)
  | Mat exp ((pat # exp) list)
  | Let (varN option) exp exp
  | Letrec ((varN # varN # exp) list) exp
  | Extend_global num`;

val exp_size_def = definition"exp_size_def";

val exp6_size_APPEND = Q.store_thm("exp6_size_APPEND[simp]",
  `conLang$exp6_size (e ++ e2) = exp6_size e + exp6_size e2`,
  Induct_on`e`>>simp[exp_size_def])

val exp6_size_REVERSE = Q.store_thm("exp6_size_REVERSE[simp]",
  `conLang$exp6_size (REVERSE es) = exp6_size es`,
  Induct_on`es`>>simp[exp_size_def])

val _ = Datatype`
 dec =
  | Dlet num exp
  | Dletrec ((varN # varN # exp) list)`;

val _ = Datatype`
 prompt =
    Prompt (dec list)`;

val _ = Define `
  (num_defs [] = 0)
  ∧
  (num_defs (Dlet n _::ds) = (n + num_defs ds))
  ∧
  (num_defs (Dletrec funs::ds) = (LENGTH funs + num_defs ds))`;

val _ = export_theory()

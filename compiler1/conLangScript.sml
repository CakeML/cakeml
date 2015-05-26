open HolKernel Parse boolLib bossLib;

val _ = numLib.prefer_num();

val _ = new_theory "conLang"

(* Removes named datatype constructors. Follows modLang.
 *
 * The AST of conLang differs from modLang by using numbered tags instead of
 * constructor name identifiers for all data constructor patterns and
 * expressions. Constructors explicitly mention the type they are constructing.
 * Also type and exception declarations are removed.
 *)

(* these must match what the prim_types_program generates *)

val _ = Define `bind_tag      = 0`;
val _ = Define `chr_tag       = 1`;
val _ = Define `div_tag       = 2`;
val _ = Define `eq_tag        = 3`;
val _ = Define `subscript_tag = 4`;

val _ = Define `true_tag  = 0`;
val _ = Define `false_tag = 1`;

val _ = Define `nil_tag   = 0`;
val _ = Define `cons_tag  = 0`;

val _ = Define `none_tag  = 0`;
val _ = Define `some_tag  = 0`;

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

(*
  The patLang intermediate language follows immediately after
  pattern-match compilation from flatLang. The patLang language
  differs from earlier languages in that it uses de Bruijn indices
  for variable names.
*)
open preamble flatLangTheory;

val _ = new_theory "patLang"
val _ = set_grammar_ancestry ["flatLang"]

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

Theorem exp1_size_APPEND[simp]:
   patLang$exp1_size (e ++ e2) = exp1_size e + exp1_size e2
Proof
  Induct_on`e`>>simp[exp_size_def]
QED

Theorem exp1_size_REVERSE[simp]:
   patLang$exp1_size (REVERSE es) = exp1_size es
Proof
  Induct_on`es`>>simp[exp_size_def]
QED

val _ = export_theory()

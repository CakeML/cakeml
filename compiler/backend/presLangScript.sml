open astTheory
(* PresLang intends to be a generalization of multiple languages. The purpose is
* * to do most of the JSON-work in a to_JSON in PresLang instead of having each language have it's own.
* * It is unclear how many languages we can include in PresLang, but the current
* * assumption is that at least all non-imperative languages will be included.
* * The imperative languages might get something similar to PresLang to represent
* * a generalization of them. *)

val _ = Datatype`
 exp = Raise tra exp
  | Handle tra exp ((pat # exp) list)
  | Lit tra lit
  | Con tra (((modN,conN) id) option) (exp list)
  | Var_local tra varN
  | Var_global tra num
  | Fun tra varN exp
  | App tra op (exp list)
  | If tra exp exp exp
  | Mat tra exp ((pat # exp) list)
  | Let tra (varN option) exp exp
  | Letrec tra ((varN # varN # exp) list) exp`;

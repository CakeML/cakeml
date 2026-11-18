(*
  Opt-in translation of pointer equality (Mptr_eq) for global-state monads.
  The user's state needs an oracle field of type num -> bool, described by
  an ORACLE_ACCESSORS theorem for its getter, setter and heap predicate.
  Results are EvalOM certificates (ArrowOM for the last curried argument).
  Limitations: pointer operands and if-guards must be variables, and returned
  expressions must not contain PtrEq.
*)
signature ml_monad_oracleLib =
sig
  include Abbrev

  (* Set the ORACLE_ACCESSORS theorem used by all translations below *)
  val start_oracle_translation : thm -> unit

  (* Translate Mptr_eq, st_ex_return, st_ex_bind and if on variables *)
  val translate_term : term -> thm

  (* Translate a non-recursive definition with variable arguments *)
  val translate_definition : thm -> thm

  (* As translate_definition, but also adds the declaration to the
     translator's program state *)
  val oracle_translate : thm -> thm
end

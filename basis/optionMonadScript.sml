open preamble optionTheory

val _ = new_theory"optionMonad"

val _ = monadsyntax.add_monadsyntax();
val _ = overload_on ("return", ``SOME``)
val _ = overload_on ("fail", ``NONE``)
val _ = overload_on ("SOME", ``SOME``)
val _ = overload_on ("NONE", ``NONE``)
val _ = overload_on ("++", ``OPTION_CHOICE``)
val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)

val OPTION_CHOICE_EQUALS_OPTION = Q.store_thm("OPTION_CHOICE_EQUALS_OPTION",
  `!x y z. x ++ y = SOME z <=> (x = SOME z \/ (x = NONE /\ y = SOME z))`,
  rw[] \\ cases_on `x` \\ cases_on `y` \\ fs[]);

val _ =  save_thm("option_eq_some",
    LIST_CONJ [
    OPTION_IGNORE_BIND_EQUALS_OPTION,
    OPTION_BIND_EQUALS_OPTION,
    OPTION_CHOICE_EQUALS_OPTION]);

val _ = export_theory();

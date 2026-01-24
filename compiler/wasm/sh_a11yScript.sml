(*
  DIXITQUE DEUS FIAT LUX ET FACTA EST LUX
*)
Theory sh_a11y
Ancestors arithmetic

Theorem normalize_relop = LIST_CONJ [GREATER_DEF, GREATER_EQ, NOT_LESS, NOT_LE, NOT_GREATER, prove(“∀a b. ¬(a:num>=b) <=> a<b”, simp_tac arith_ss[])];

Theorem NOT_IF:
  ∀b x y. (if ¬b then x else y) = if b then y else x
Proof rw[]
QED

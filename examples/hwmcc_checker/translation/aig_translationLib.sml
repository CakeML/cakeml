(*
  Helpers shared by the translation scripts.
*)
structure aig_translationLib =
struct

open preamble

fun demonadify thm =
  SRULE [oneline errorMonadTheory.bind_def, errorMonadTheory.guard_def, UNCURRY]
    thm;

end

(**
  A monad for results used by FloVer
**)
structure ResultsLib =
struct

open monadsyntax;
open ResultsTheory;

val res_monad = declare_monad ("Results",
    {bind = ``result_bind``,
     ignorebind = SOME ``result_ignore_bind``,
     unit = ``result_return``,
     fail = NONE, choice = NONE, guard = NONE});

val _ = monadsyntax.enable_monadsyntax();
val _ = List.app monadsyntax.enable_monad ["option", "Results"];

end

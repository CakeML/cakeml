(**
  A monad for results used by FloVer
**)
structure ResultsLib =
struct

open monadsyntax;
open ResultsTheory;

val res_monad = declare_monad ("Results",
    {bind = prim_mk_const{Thy="Results",Name="result_bind"},
     ignorebind = SOME (prim_mk_const{Thy="Results",Name="result_ignore_bind"}),
     unit = prim_mk_const{Thy="Results",Name="result_return"},
     fail = NONE, choice = NONE, guard = NONE});

val _ = monadsyntax.enable_monadsyntax();
val _ = List.app monadsyntax.enable_monad ["option", "Results"];

end

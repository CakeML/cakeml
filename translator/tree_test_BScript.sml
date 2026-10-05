(*
  Downstream theory that imports tree_test_A and checks that
  nsLookup_conv on an A-defined env goes through the tree path via
  try_lazy_load (ThmSet ancestry + saved theorems).
*)
Theory tree_test_B
Ancestors
  ast semanticPrimitives evaluate mlstring namespace ml_prog tree_test_A
Libs
  preamble ml_progLib

(* Force a lookup against A's env via the main nsLookup_conv; if the tree
   lazy-load works, this produces the concrete SOME value. *)
val check_thm =
  ml_progLib.nsLookup_conv ``nsLookup_Short A_env.v (strlit "foo")``

val () =
  if aconv (rhs (concl check_thm))
           ``SOME (Litv (IntLit 1))``
  then print "tree_test_B: lazy-load lookup OK\n"
  else raise Fail "tree_test_B: unexpected lookup result"

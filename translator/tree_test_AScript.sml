(*
  Upstream theory for the cross-theory tree-load test: defines an env via
  derive_nsLookup_tree and lets its tree Definitions + equiv/WF theorems
  persist through the ThmSet exporters.
*)
Theory tree_test_A
Ancestors
  ast semanticPrimitives evaluate mlstring namespace ml_prog
Libs
  preamble ml_progLib

Definition A_env_def:
  A_env = write (strlit "foo") (Litv (IntLit 1)) init_env
End

val () = ignore (ml_progLib.derive_nsLookup_tree A_env_def)

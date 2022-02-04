(*
  Combinatory Logic tutorial example
*)

Datatype:
  cl = K | S | # cl cl
End

set_fixity "#" (Infixl 1100);

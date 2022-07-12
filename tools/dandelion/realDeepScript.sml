(** A deep embedding of real-number arithmetic,
    needed to do automatic differentiation **)
open preambleDandelion;

val _ = new_theory "realDeep";

Datatype:
  rUop = Inv | Neg
End

Datatype:
  rBop = Add | Sub | Mul | Div
End

Datatype:
  deepReal =
    Cst int num
    | Var string
    | Uop rUop deepReal
    | Bop rBop deepReal deepReal
End

val _ = export_theory();

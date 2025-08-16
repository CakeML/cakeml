(*
  Pure functions for the Option module.
*)
Theory mloption
Ancestors
  ternaryComparisons
Libs
  preamble

Definition getOpt_def:
  (getOpt (SOME v) a = v) /\
  (getOpt NONE a = a)
End

Definition filter_def:
  filter f a = if f a then SOME(a) else NONE
End

Definition mapPartial_def:
  mapPartial f opt = OPTION_BIND opt f
End

Definition compose_def:
  compose f g a = case g a of
    (SOME v) => SOME(f v)
    | NONE => NONE
End

Definition composePartial_def:
  composePartial f g a = case g a of
    (SOME v) => f v
    | NONE => NONE
End

Definition compare_def:
  compare f x y =
    case x of
    | NONE => (case y of NONE => EQUAL | _ => LESS)
    | SOME vx => (case y of NONE => GREATER | SOME vy => f vx vy)
End

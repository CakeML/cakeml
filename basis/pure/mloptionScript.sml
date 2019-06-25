(*
  Pure functions for the Option module.
*)
open preamble

val _ = new_theory"mloption"

(*val _ = Datatype `option = *)

val getOpt_def = Define`
  (getOpt (SOME v) a = v) /\
  (getOpt NONE a = a)`;

val filter_def  = Define`
  filter f a = if f a then SOME(a) else NONE`;

val mapPartial_def = Define`
  mapPartial f opt = OPTION_BIND opt f`;

val compose_def = Define`
  compose f g a = case g a of
    (SOME v) => SOME(f v)
    | NONE => NONE`;

val composePartial_def = Define`
  composePartial f g a = case g a of
    (SOME v) => f v
    | NONE => NONE`;

val compare_def = Define `
  compare f x y =
    case x of
    | NONE => (case y of NONE => Equal | _ => Less)
    | SOME vx => (case y of NONE => Greater | SOME vy => f vx vy)`

val _ = export_theory()

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



val _ = export_theory()

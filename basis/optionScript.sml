open preamble 

val _ = new_theory"option"

(*val _ = Datatype `option = *)


val getOpt_def = Define`
  getOpt opt a = case opt of
    (SOME v) => v
    | NONE => a`;

val filter_def  = Define`
  filter f a = if f a then SOME(a) else NONE`;

val compose_def = Define`
  compose f g a = case g a of
    (SOME v) => SOME(f v)
    | NONE => NONE`;

val composePartial_def = Define`
  composePartial f g a = case g a of
    (SOME v) => f v
    | NONE => NONE`;



val _ = export_theory() 

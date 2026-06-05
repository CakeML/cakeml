(*
   Basic specification of a distributed RUP checker
*)
Theory distrup
Libs
  preamble
Ancestors
  cnf ccnf syntax_helper

(* The format has four proof steps. We let 'a be the ID type *)
Datatype:
  distrup =
  | Del (num list) (* Clauses to delete *)
  | Lrup num vcclause (num list)
  | Import num vcclause
  | ValidateUnsat
End

Definition check_distrup_def:
  check_distrup distrup fml =
  case distrup of
  | Del ls =>
      SOME (delete_ids fml ls)
  | Lrup n vc hints =>
    if is_rup fml vc hints
    then
      SOME (fml |+ (n,vc))
    else NONE
  | Import n vc =>
      SOME (fml |+ (n,vc))
  | ValidateUnsat =>
      if contains_emp fml
      then
        SOME fml
      else NONE
End


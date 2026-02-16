(*
   Basic specification of a distributed RUP checker
*)
Theory distrup
Libs
  preamble
Ancestors
  cnf ccnf syntax_helper

(* The format has three proof steps. *)
Datatype:
  distrup =
  | Del (num list) (* Clauses to delete *)
  | Lrup num vcclause (num list)
  | Import num vcclause
End

Definition check_distrup_def:
  check_distrup distrup fml =
  case distrup of
  | Del ls =>
    SOME (delete_ids fml ls)
  | Lrup n vc hints =>
    if is_rup fml vc hints
    then
      SOME (insert n vc fml)
    else NONE
  | Import n vc =>
      SOME (insert n vc fml)
End

(* TODO: soundness theorems *)

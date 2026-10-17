(*
  Helper functions for producing cnf output
*)
Theory toCnfHelper
Ancestors
  misc boolExpToCnf mlstring mlint
Libs
  preamble basis


(* ------------------------------ CNF to output ------------------------ *)

Definition literal_to_output_def:
  literal_to_output l =
  case l of
  | Pos x => List [num_to_str x; « »]
  | Neg y => List [«-»; num_to_str y; « »]
End

Definition clause_to_output_def:
  clause_to_output [] = List [] ∧
  clause_to_output (l::ls) =
    Append (literal_to_output l) (clause_to_output ls)
End

Definition cnf_to_output_def:
  cnf_to_output [] = List [] ∧
  cnf_to_output (c::cs) =
    Append (clause_to_output c)
      (Append (List [«0\n»]) (cnf_to_output cs))
End

Definition get_max_var_def:
  get_max_var [] = 0 ∧
  get_max_var (l::ls) = MAX (var_lit l) (get_max_var ls)
End

Definition get_max_var_and_clauses_def:
  get_max_var_and_clauses [] = (0:num, 0:num) ∧
  get_max_var_and_clauses (c::cs) =
    let (max_var, clauses) = get_max_var_and_clauses cs in
      (MAX (get_max_var c) max_var, clauses + 1)
End

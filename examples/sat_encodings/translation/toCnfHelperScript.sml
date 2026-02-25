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
  | INL x => List [num_to_str (x); (strlit " ")]
  | INR y => List [strlit "-"; num_to_str (y); (strlit " ")]
End

Definition clause_to_output_def:
  clause_to_output ClauseEmpty = List [] ∧
  clause_to_output (ClauseLit l) = literal_to_output l ∧
  clause_to_output (ClauseOr c1 c2) =
  Append (clause_to_output c1) (clause_to_output c2)
End

Definition cnf_to_output_def:
  cnf_to_output CnfEmpty = List [] ∧
  cnf_to_output (CnfClause c) =
  Append (clause_to_output c) (List [strlit "0\n"]) ∧
  cnf_to_output (CnfAnd cnf1 cnf2) =
  Append (cnf_to_output cnf1) (cnf_to_output cnf2)
End

Definition get_max_var_def:
  get_max_var ClauseEmpty = 0 ∧
  get_max_var (ClauseLit (INL x)) = x ∧
  get_max_var (ClauseLit (INR x)) = x ∧
  get_max_var (ClauseOr c1 c2) = MAX (get_max_var c1) (get_max_var c2)
End

Definition get_max_var_and_clauses_def:
  get_max_var_and_clauses CnfEmpty = (0:num, 0:num) ∧
  get_max_var_and_clauses (CnfClause c) = (get_max_var c, 1) ∧
  get_max_var_and_clauses (CnfAnd c1 c2) =
  let (max1, numC1) = get_max_var_and_clauses c1 in
    let (max2, numC2) = get_max_var_and_clauses c2 in
      (MAX max1 max2, numC1 + numC2)
End

(*
  Encode kakuro to cnf
*)
Theory kakuro
Ancestors
  misc ASCIInumbers set_sep quantifierExp orderEncodingBool
  numBoolExp numBoolExtended numBoolRange numberSudoku
  killerSudoku
Libs
  preamble


(* ----------------------------- Datatypes --------------------------- *)

Type clue = “:(num # num list)”;
Type clueList = “:clue list”


(* ----------------------------- Well formed --------------------------- *)

Definition clues_ok_def:
  clues_ok (clues:clueList) ⇔
  EVERY (λ l. l ≠ []) (MAP SND clues) ∧
  EVERY (λ l. ALL_DISTINCT l) (MAP SND clues)
End


(* ----------------------------- Evaluation --------------------------- *)

Definition eval_clue_def:
  eval_clue (w':numVarAssignment) [] = 0 ∧
  eval_clue w' (c::cs) = w' c + eval_clue w' cs
End

Definition eval_kakuro_def:
  eval_kakuro (w':numVarAssignment) (clues:clueList) ⇔
  EVERY (λ (v, l). eval_clue w' l = v) clues ∧
  EVERY ALL_DISTINCT (MAP (MAP w' o SND) clues)
End


(* ----------------------------- Encoding --------------------------- *)

Definition get_fresh_numVar_one_clue_def:
  get_fresh_numVar_one_clue [] = 0 ∧
  get_fresh_numVar_one_clue (c::cs) =
  MAX c (get_fresh_numVar_one_clue cs)
End

Definition get_fresh_numVar_clues_def:
  get_fresh_numVar_clues [] = 0 ∧
  get_fresh_numVar_clues ((v, l)::clues) =
  MAX
  (get_fresh_numVar_one_clue l + 1)
  (get_fresh_numVar_clues clues)
End

Definition kakuro_to_numBoolRanges_def:
  kakuro_to_numBoolRanges (clues:clueList) =
  RAnd
  (cages_to_numBoolRanges_inner (get_fresh_numVar_clues clues) clues)
  (ns_every_all_distinct (MAP SND clues))
End

Definition get_kakuro_variables_def:
  get_kakuro_variables (clues:clueList) =
  nub (FLAT (MAP SND clues))
End

Definition get_kakuro_rangeList_original_variables_def:
  get_kakuro_rangeList_original_variables (clues:clueList) =
  let variables = get_kakuro_variables clues in
    let ranges = GENLIST (λ _. (1:num, 9:num)) (LENGTH variables) in
      ZIP (variables, ranges)
End

Definition get_kakuro_rangeList_def:
  get_kakuro_rangeList (clues:clueList) =
  get_kakuro_rangeList_original_variables clues ++
  cages_to_rangeList (get_fresh_numVar_clues clues) clues
End

Definition kakuro_to_cnf_def:
  kakuro_to_cnf (clues:clueList) =
  numBoolRange_to_cnf
  (get_kakuro_rangeList clues)
  (kakuro_to_numBoolRanges clues)
End

Definition assignment_to_numVarAssignment_kakuro_def:
  assignment_to_numVarAssignment_kakuro (w:assignment) (clues:clueList) =
  assignment_to_numVarAssignment_numBoolRange
  w
  (get_kakuro_rangeList clues)
  (kakuro_to_numBoolRanges clues)
End

Definition numVarAssignment_to_assignment_kakuro_def:
  numVarAssignment_to_assignment_kakuro
  (w':numVarAssignment) (clues:clueList) =
  encode_assignment_numBoolRange
  (λ_. F)
  w'
  (get_kakuro_rangeList clues)
  (kakuro_to_numBoolRanges clues)
End



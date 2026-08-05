(*
  Encode killerSudoku to cnf
*)
Theory killerSudoku
Ancestors
  misc ASCIInumbers set_sep quantifierExp numBoolRange sudoku
  numberSudoku
Libs
  preamble


(* ------------------------ Types --------------------------- *)

Type pos = “:num”; (* 00, 01, 02, ..., 88.
                      First num is row, second is column *)

Type cage = “:(num # pos list)”;
Type cageList = “:cage list”;


(* -------------------- Help funktions ------------------------- *)

Definition get_all_positions_def:
  get_all_positions =
  FLAT (GENLIST (λ row. GENLIST (λ col. row * 10 + col) 9) 9)
End

Definition get_row_positions_def:
  get_row_positions =
  GENLIST (λ row. GENLIST (λ col. row * 10 + col) 9) 9
End

Definition get_col_positions_def:
  get_col_positions =
  GENLIST (λ col. GENLIST (λ row. row * 10 + col) 9) 9
End

Definition get_block_positions_def:
  get_block_positions =
  FLAT (GENLIST
        (λ i. GENLIST (λ j.
                         [(i * 3 + 0) * 10 + (j * 3 + 0);
                          (i * 3 + 0) * 10 + (j * 3 + 1);
                          (i * 3 + 0) * 10 + (j * 3 + 2);
                          (i * 3 + 1) * 10 + (j * 3 + 0);
                          (i * 3 + 1) * 10 + (j * 3 + 1);
                          (i * 3 + 1) * 10 + (j * 3 + 2);
                          (i * 3 + 2) * 10 + (j * 3 + 0);
                          (i * 3 + 2) * 10 + (j * 3 + 1);
                          (i * 3 + 2) * 10 + (j * 3 + 2)]) 3) 3)
End

Definition get_row_col_block_positions_def:
  get_row_col_block_positions =
  get_row_positions ++ get_col_positions ++ get_block_positions
End

(* -------------------- Well formed ------------------------- *)

Definition killerSudoku_ok_def:
  killerSudoku_ok (cages:cageList) ⇔
    EVERY (λ x. MEM x (FLAT (MAP SND cages))) get_all_positions ∧
    EVERY (λ x. MEM x get_all_positions) (FLAT (MAP SND cages)) ∧
    ALL_DISTINCT (FLAT (MAP SND cages)) ∧
    EVERY (λ (v, l). l ≠ []) cages
End


(* ---------------- Satisfiability ------------------------- *)

Definition eval_cage_def:
  eval_cage (w':cellAssignment) [] = 0 ∧
  eval_cage w' (c::cs) =
  w' c + eval_cage w' cs
End

Definition eval_cages_def:
  eval_cages (w':cellAssignment) (cages:cageList) =
  EVERY (λ (v, l). eval_cage w' l = v) cages
End

Definition eval_killerSudoku_def:
  eval_killerSudoku (w':cellAssignment) (cages:cageList) ⇔
    EVERY ALL_DISTINCT (MAP (MAP w') get_row_col_block_positions) ∧
    eval_cages w' cages
End


(* ------------------ Encoding ------------------------------- *)

Definition one_cage_to_numBoolRanges_def:
  one_cage_to_numBoolRanges (n:num) v [] = RFalse ∧
  one_cage_to_numBoolRanges n v [pos] = REqConst pos v ∧
  one_cage_to_numBoolRanges n v (pos1::pos2::l) =
  RAnd
  (RAdd pos1 pos2 n)
  (one_cage_to_numBoolRanges (n + 1) v (n::l))
Termination
  WF_REL_TAC ‘measure (λ (n, v, l). LENGTH l)’
  >> rw[]
End

Definition cages_to_numBoolRanges_inner_def:
  cages_to_numBoolRanges_inner (n:num) [] = RTrue ∧
  cages_to_numBoolRanges_inner n ((v, l)::cages) =
  RAnd
  (one_cage_to_numBoolRanges n v l)
  (cages_to_numBoolRanges_inner (n + LENGTH l - 1) cages)
End

Definition cages_to_numBoolRanges_def:
  cages_to_numBoolRanges (cages:cageList) =
  cages_to_numBoolRanges_inner 89 cages
End

Definition one_cage_to_rangeList_def:
  one_cage_to_rangeList n v l =
  ZIP (GENLIST (λ i. n + i) (LENGTH l - 1),
       GENLIST (λ_. ((1:num), v)) (LENGTH l - 1))
End

Definition cages_to_rangeList_def:
  cages_to_rangeList n [] = [] ∧
  cages_to_rangeList n ((v, l)::cages) =
  (one_cage_to_rangeList n v l) ++
  (cages_to_rangeList (n + LENGTH l - 1) cages)
End

Definition get_killerSudoku_rangeList_def:
  get_killerSudoku_rangeList (cages:cageList) =
  get_sudoku_rangeList ++
  cages_to_rangeList 89 cages
End

Definition killerSudoku_to_numBoolRanges_def:
  killerSudoku_to_numBoolRanges (cages:cageList) =
  RAnd
  (ns_every_all_distinct get_row_col_block_positions)
  (cages_to_numBoolRanges cages)
End

Definition killerSudoku_to_cnf_def:
  killerSudoku_to_cnf (cages:cageList) =
  numBoolRange_to_cnf
  (get_killerSudoku_rangeList cages)
  (killerSudoku_to_numBoolRanges cages)
End

Definition assignment_to_cellAssignment_killerSudoku_def:
  assignment_to_cellAssignment_killerSudoku (w:assignment) (cages:cageList) =
  assignment_to_numVarAssignment_numBoolRange
  w
  (get_killerSudoku_rangeList cages)
  (killerSudoku_to_numBoolRanges cages)
End



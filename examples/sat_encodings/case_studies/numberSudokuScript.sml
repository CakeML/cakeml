(*
  Encoding of sudoku to numBoolRange and to cnf
*)
Theory numberSudoku
Ancestors
  misc ASCIInumbers set_sep quantifierExp numBoolRange sudoku
Libs
  preamble


(* ------------------------ Types --------------------------- *)

Type value = “:num”; (* 0 means empty. Allowed values are 0-9 *)
Type pos = “:num”; (* 00, 01, 02, ..., 88.
                      First num is row, second is column *)

Type cell = “:value”
Type row = “:cell list”;
Type sudoku = “:row list”;

Type cellAssignment = “:pos -> value”;


(* -------------------- Well formed ------------------------- *)

Definition sudoku_ok_def:
  sudoku_ok (sudoku:sudoku) ⇔
    (LENGTH sudoku = 9) ∧
    EVERY (λ row. LENGTH row = 9) sudoku ∧
    (EVERY (λ n. 0 ≤ n ∧ n ≤ 9) (FLAT sudoku))
End

Definition assignment_ok_def:
  assignment_ok (w:cellAssignment) (sudoku:sudoku)  ⇔
    EVERY (EVERY (λ pos. 1 ≤ w pos ∧ w pos ≤ 9)) get_positions ∧
    EVERY (λ (c, v). if v = 0 then T else w c = v)
          (FLAT (get_sudoku_with_pos sudoku))
End


(* ---------------- Satisfiability ------------------------- *)

Definition fill_cell_def:
  fill_cell (w:cellAssignment) (pos, cell) =
  if cell = 0 then w pos else cell
End

Definition eval_sudoku_def:
  eval_sudoku (w:cellAssignment) (sudoku:sudoku) =
  let row_col_block_lists = create_row_col_block_lists sudoku in
    let filled_lists = MAP (MAP (fill_cell w)) row_col_block_lists in
      EVERY ALL_DISTINCT filled_lists
End

(* ------------------ Encoding ------------------------------- *)

Definition ns_filled_cells_to_numBoolRange_inner_def:
  ns_filled_cells_to_numBoolRange_inner [] = RTrue ∧
  ns_filled_cells_to_numBoolRange_inner (c::cs) =
  RAnd
  (REqConst (FST c) (SND c))
  (ns_filled_cells_to_numBoolRange_inner cs)
End

Definition ns_filled_cells_to_numBoolRange_def:
  ns_filled_cells_to_numBoolRange sudoku =
  let sudoku_with_pos = get_sudoku_with_pos sudoku in
    let filled_cells = FILTER (λ (pos, val). val ≠ 0)
                              (FLAT sudoku_with_pos) in
      ns_filled_cells_to_numBoolRange_inner filled_cells
End

Definition ns_not_member_def:
  ns_not_member c [] = RTrue ∧
  ns_not_member c (c'::cs) =
  RAnd
  (RNot (REq c c'))
  (ns_not_member c cs)
End

Definition ns_all_distinct_def:
  ns_all_distinct [] = RTrue ∧
  ns_all_distinct (c::cs) =
  RAnd
  (ns_not_member c cs)
  (ns_all_distinct cs)
End

Definition ns_every_all_distinct_def:
  ns_every_all_distinct [] = RTrue ∧
  ns_every_all_distinct (l::ls) =
  RAnd (ns_all_distinct l) (ns_every_all_distinct ls)
End

Definition ns_sudoku_rules_to_numBoolRange_def:
  ns_sudoku_rules_to_numBoolRange sudoku =
  let lists_with_pos = create_row_col_block_lists sudoku in
      let variable_lists = MAP (MAP (λ (pos, cell). pos)) lists_with_pos in
        ns_every_all_distinct variable_lists
End

Definition ns_sudoku_to_numBoolRange_def:
  ns_sudoku_to_numBoolRange sudoku =
  RAnd (ns_filled_cells_to_numBoolRange sudoku)
       (ns_sudoku_rules_to_numBoolRange sudoku)
End

Definition get_sudoku_rangeList_def:
  get_sudoku_rangeList =
  ZIP (FLAT get_positions, GENLIST (λ _. ((1:num), (9:num))) 81)
End

Definition numberSudoku_to_cnf_def:
  numberSudoku_to_cnf (sudoku:sudoku) =
  let e = ns_sudoku_to_numBoolRange sudoku in
    let l = get_sudoku_rangeList in
      numBoolRange_to_cnf l e
End

Definition cellAssignment_to_assignment_def:
  cellAssignment_to_assignment (w:cellAssignment) (sudoku:sudoku) =
  encode_assignment_numBoolRange
  (λ _. F)
  w
  get_sudoku_rangeList
  (ns_sudoku_to_numBoolRange sudoku)
End

Definition assignment_to_cellAssignment_def:
  assignment_to_cellAssignment (w:assignment) (sudoku:sudoku) =
  assignment_to_numVarAssignment_numBoolRange
  w get_sudoku_rangeList (ns_sudoku_to_numBoolRange sudoku)
End

Definition numberSudoku_to_assignment_def:
  numberSudoku_to_assignment (w:cellAssignment) (sudoku:sudoku) =
  numBoolRange_to_assignment
  (λ _. F) w get_sudoku_rangeList (ns_sudoku_to_numBoolRange sudoku)
End


(* ------------------ Theorems ------------------------------- *)

Theorem ns_all_pos_unique:
  ∀ sudoku.
    sudoku_ok sudoku ⇒
    ALL_DISTINCT (MAP FST (FLAT (get_sudoku_with_pos sudoku)))
Proof
  rw[get_sudoku_with_pos_def, get_positions_def, sudoku_ok_def]
  >> gvs[LENGTH_EQ_NUM_compute]
QED

Theorem ns_encode_filled_cells_lemma:
  ∀ l w.
    ALL_DISTINCT (MAP FST l) ∧
    EVERY (λ(c,v). v = 0 ∨ w c = v) l ⇒
    eval_numBoolRange
    (λ_. F)
    w
    (ns_filled_cells_to_numBoolRange_inner (FILTER (λ(pos,val). val ≠ 0) l))
Proof
  Induct
  >- rw[ns_filled_cells_to_numBoolRange_inner_def, eval_numBoolRange_def]
  >> Cases_on ‘h’
  >> rw[]
  >> rw[ns_filled_cells_to_numBoolRange_inner_def]
  >> rw[eval_numBoolRange_def]
QED

Theorem ns_encode_filled_cells_always_true:
  ∀ sudoku w.
    sudoku_ok sudoku ∧
    assignment_ok w sudoku ⇒
    eval_numBoolRange
    (λ _. F)
    w
    (ns_filled_cells_to_numBoolRange sudoku)
Proof
  rw[ns_filled_cells_to_numBoolRange_def]
  >> qspecl_then [‘sudoku’] assume_tac ns_all_pos_unique
  >> rgs[assignment_ok_def]
  >> rgs[ns_encode_filled_cells_lemma]
QED

Theorem fill_cell_equal:
  assignment_ok w sudoku ∧
  sudoku_ok sudoku ∧
  MEM (pos1, cell1) (FLAT (get_sudoku_with_pos sudoku)) ∧
  MEM (pos2, cell2) (FLAT (get_sudoku_with_pos sudoku)) ⇒
  (fill_cell w (pos1, cell1) ≠ fill_cell w (pos2, cell2) ⇔
     w pos1 ≠ w pos2)
Proof
  rw[fill_cell_def]
  >> (rgs[assignment_ok_def, EVERY_MEM, FORALL_PROD]
      >> metis_tac[])
QED

Theorem ns_not_member_lemma:
  ∀ l w w' sudoku pos cell.
    assignment_ok w sudoku ∧
    sudoku_ok sudoku ∧
    ALL_DISTINCT (MAP FST (FLAT (get_sudoku_with_pos sudoku))) ∧
    MEM (pos, cell) (FLAT (get_sudoku_with_pos sudoku)) ∧
    EVERY
    (λ(pos, cell). MEM (pos,cell) (FLAT (get_sudoku_with_pos sudoku))) l ⇒
    (¬MEM (fill_cell w (pos, cell) ) (MAP (fill_cell w) l) ⇔
       eval_numBoolRange
       (λ_. F)
       w
       (ns_not_member pos (MAP (λ(pos, cell). pos) l)))
Proof
  Induct
  >- rw[ns_not_member_def, eval_numBoolRange_def]
  >> Cases_on ‘h’
  >> rgs[ns_not_member_def, eval_numBoolRange_def]
  >> rw[]
  >> last_x_assum (qspecl_then [‘w’, ‘sudoku’, ‘pos’, ‘cell’] assume_tac)
  >> rgs[]
  >> metis_tac[fill_cell_equal]
QED

Theorem ns_every_all_distinct_in_list_lemma:
  ∀ l w w' sudoku.
    assignment_ok w sudoku ∧
    sudoku_ok sudoku ∧
    ALL_DISTINCT (MAP FST (FLAT (get_sudoku_with_pos sudoku))) ∧
    EVERY
    (λ(pos, cell). MEM (pos,cell) (FLAT (get_sudoku_with_pos sudoku))) l ⇒
    (ALL_DISTINCT (MAP (fill_cell w) l) ⇔
       eval_numBoolRange
       (λ_. F)
       w
       (ns_all_distinct (MAP (λ(pos, cell). pos) l)))
Proof
  Induct
  >- rw[ns_all_distinct_def, eval_numBoolRange_def]
  >> rw[]
  >> Cases_on ‘h’
  >> rw[]
  >> rw[ns_all_distinct_def]
  >> rw[eval_numBoolRange_def]
  >> rgs[]
  >> metis_tac[ns_not_member_lemma]
QED

Theorem ns_every_all_distinct_lemma:
  ∀ l w w' sudoku.
    assignment_ok w sudoku ∧
    sudoku_ok sudoku ∧
    EVERY
    (EVERY
     (λ(pos, cell). MEM (pos, cell) (FLAT (get_sudoku_with_pos sudoku)))) l ⇒
    (EVERY ALL_DISTINCT (MAP (MAP (fill_cell w)) l) ⇔
       eval_numBoolRange
       (λ_. F) w
       (ns_every_all_distinct (MAP (MAP (λ(pos, cell). pos)) l)))
Proof
  Induct
  >- rw[ns_every_all_distinct_def, eval_numBoolRange_def]
  >> rw[ns_every_all_distinct_def, eval_numBoolRange_def]
  >> qspecl_then [‘sudoku’] assume_tac ns_all_pos_unique >> rgs[]
  >> metis_tac[ns_every_all_distinct_in_list_lemma]
QED

Theorem ns_row_mem_sudoku:
  ∀(sudoku: sudoku).
    EVERY (λrow. LENGTH row = 9) sudoku ∧
    LENGTH sudoku = 9 ⇒
    (EVERY
     (EVERY
      (λ(pos,cell). MEM (pos,cell) (FLAT (get_sudoku_with_pos sudoku))))
     (get_sudoku_with_pos sudoku))
Proof
  rw[get_sudoku_with_pos_def, get_positions_def]
  >> qpat_x_assum ‘LENGTH _ = _’ mp_tac
  >> simp_tac std_ss [LENGTH_EQ_NUM_compute, PULL_EXISTS, ZIP]
  >> rpt strip_tac
  >> last_x_assum mp_tac
  >> asm_simp_tac std_ss [LENGTH_EQ_NUM_compute, PULL_EXISTS, ZIP, EVERY_DEF]
  >> rpt strip_tac
  >> rpt var_eq_tac
  >> rewrite_tac[MEM, MAP, ZIP, EVERY_DEF] >> rpt strip_tac >> EVAL_TAC
QED

Theorem ns_col_mem_sudoku:
  ∀ (sudoku: sudoku).
    EVERY (λrow. LENGTH row = 9) sudoku ∧
    LENGTH sudoku = 9 ⇒
    (EVERY
     (EVERY
      (λ(pos,cell). MEM (pos,cell) (FLAT (get_sudoku_with_pos sudoku))))
     (get_cols (get_sudoku_with_pos sudoku)))
Proof
  rw[get_sudoku_with_pos_def, get_positions_def]
  >> pop_assum mp_tac
  >> simp_tac std_ss [LENGTH_EQ_NUM_compute, PULL_EXISTS, ZIP]
  >> rpt strip_tac
  >> var_eq_tac
  >> pop_assum mp_tac
  >> asm_simp_tac std_ss [LENGTH_EQ_NUM_compute, PULL_EXISTS, ZIP, EVERY_DEF]
  >> rpt strip_tac
  >> rpt var_eq_tac
  >> rewrite_tac[get_cols_def]
  >> EVAL_TAC
QED

Theorem ns_block_mem_sudoku:
  ∀ (sudoku: sudoku).
    EVERY (λrow. LENGTH row = 9) sudoku ∧
    LENGTH sudoku = 9 ⇒
   (EVERY
    (EVERY
     (λ(pos,cell). MEM (pos,cell) (FLAT (get_sudoku_with_pos sudoku))))
    (get_blocks (get_sudoku_with_pos sudoku)))
Proof
  rw[get_sudoku_with_pos_def, get_positions_def]
  >> pop_assum mp_tac
  >> simp_tac std_ss [LENGTH_EQ_NUM_compute, PULL_EXISTS, ZIP]
  >> rpt strip_tac
  >> var_eq_tac
  >> pop_assum mp_tac
  >> simp_tac std_ss [LENGTH_EQ_NUM_compute, PULL_EXISTS, ZIP, EVERY_DEF, MAP]
  >> rpt strip_tac
  >> rpt var_eq_tac
  >> rewrite_tac[FLAT, APPEND, MEM]
  >> simp_tac std_ss []
  >> rewrite_tac[get_blocks_def, EVAL “GENLIST p 3”]
  >> EVAL_TAC
QED

Theorem ns_row_col_block_mem_sudoku:
  ∀ sudoku.
    sudoku_ok sudoku ⇒
    (EVERY (EVERY
           (λ(pos, cell). MEM (pos, cell)
                              (FLAT (get_sudoku_with_pos sudoku))))
          (create_row_col_block_lists sudoku))
Proof
  rw[create_row_col_block_lists_def, sudoku_ok_def]
  >- metis_tac[ns_row_mem_sudoku]
  >- metis_tac[ns_col_mem_sudoku]
  >> metis_tac[ns_block_mem_sudoku]
QED

Theorem ns_every_all_distinct_in_lists:
  ∀ w sudoku.
    sudoku_ok sudoku ∧
    assignment_ok w sudoku ⇒
    (EVERY ALL_DISTINCT
     (MAP (MAP (fill_cell w)) (create_row_col_block_lists sudoku)) ⇔
       eval_numBoolRange
       (λ _. F)
       w
       (ns_every_all_distinct (MAP (MAP (λ(pos, cell). pos))
                    (create_row_col_block_lists sudoku))))
Proof
  rw[]
  >> qspecl_then [‘sudoku’] assume_tac ns_row_col_block_mem_sudoku >> rgs[]
  >> metis_tac[ns_every_all_distinct_lemma]
QED

Theorem ns_sudoku_to_numBoolRange_preserves_sat:
  ∀ sudoku w.
    sudoku_ok sudoku ∧
    assignment_ok w sudoku ⇒
    (eval_sudoku w sudoku ⇔
       eval_numBoolRange
       (λ _. F)
       w
       (ns_sudoku_to_numBoolRange sudoku))
Proof
  rw[eval_sudoku_def]
  >> rw[ns_sudoku_to_numBoolRange_def]
  >> rw[eval_numBoolRange_def]
  >> rw[ns_sudoku_rules_to_numBoolRange_def]
  >> qspecl_then [‘sudoku’, ‘w’] assume_tac ns_encode_filled_cells_always_true
  >> rgs[]
  >> rw[ns_every_all_distinct_in_lists]
QED

(* --------------- numberSudoku_to_cnf ----------------------- *)

Theorem numberSudoku_to_rangeList_ok:
  rangeList_ok get_sudoku_rangeList
Proof
  rw[get_sudoku_rangeList_def, get_positions_def, rangeList_ok_def]
QED

Theorem ns_every_all_distinct_split:
  ∀ xs ys l.
    exp_rangeList_ok l (ns_every_all_distinct (xs ++ ys)) ⇔
    exp_rangeList_ok l (ns_every_all_distinct xs) ∧
    exp_rangeList_ok l (ns_every_all_distinct ys)
Proof
  Induct
  >- rgs[ns_every_all_distinct_def, exp_rangeList_ok_def]
  >> rw[]
  >> rw[ns_every_all_distinct_def]
  >> rw[exp_rangeList_ok_def]
  >> metis_tac[]
QED

Theorem get_positions_lemma:
  ∀ sudoku.
    sudoku_ok sudoku ⇒
    MAP (MAP (λ(pos,cell). pos)) (MAP ZIP (ZIP (get_positions,sudoku))) =
    get_positions
Proof
  rgs[sudoku_ok_def]
  >> rw[]
  >> rgs[LENGTH_EQ_NUM_compute]
  >> rgs[get_positions_def]
QED

Theorem get_sudoku_rangeList_lemma:
  MAP FST get_sudoku_rangeList = FLAT get_positions
Proof
  rw[get_sudoku_rangeList_def, get_positions_def]
QED

Definition get_col_positions_def:
  get_col_positions =
  GENLIST (λ col. GENLIST (λ row. row * 10 + col) 9) 9
End

Theorem get_col_positions_lemma:
  ∀ sudoku.
    sudoku_ok sudoku ⇒
    MAP (MAP (λ(pos,cell). pos)) (get_cols (get_sudoku_with_pos sudoku)) =
    get_col_positions
Proof
  rw[get_sudoku_with_pos_def, sudoku_ok_def]
  >> rgs[LENGTH_EQ_NUM_compute]
  >> rgs[get_positions_def]
  >> rpt (first_x_assum kall_tac)
  >> rewrite_tac[get_cols_def]
  >> rw[EVAL “GENLIST p 9”]
  >> rw[get_cell_def]
  >> rw[LLOOKUP_def]
  >> rw[get_col_positions_def]
QED

Definition get_block_positions_def:
  get_block_positions =
  FLAT (GENLIST
        (λ i. GENLIST
              (λ j. [(i * 3 + 0) * 10 + (j * 3 + 0);
                     (i * 3 + 1) * 10 + (j * 3 + 0);
                     (i * 3 + 2) * 10 + (j * 3 + 0);
                     (i * 3 + 0) * 10 + (j * 3 + 1);
                     (i * 3 + 1) * 10 + (j * 3 + 1);
                     (i * 3 + 2) * 10 + (j * 3 + 1);
                     (i * 3 + 0) * 10 + (j * 3 + 2);
                     (i * 3 + 1) * 10 + (j * 3 + 2);
                     (i * 3 + 2) * 10 + (j * 3 + 2)]) 3) 3)
End

Theorem get_block_positions_lemma:
  ∀ sudoku.
    sudoku_ok sudoku ⇒
    MAP (MAP (λ(pos,cell). pos)) (get_blocks (get_sudoku_with_pos sudoku)) =
    get_block_positions
Proof
  rw[sudoku_ok_def, get_sudoku_with_pos_def]
  >> rgs[LENGTH_EQ_NUM_compute]
  >> rgs[get_positions_def]
  >> rpt (first_x_assum kall_tac)
  >> rewrite_tac[get_blocks_def]
  >> rewrite_tac[get_cell_def]
  >> rw[LLOOKUP_def]
  >> rw[get_block_positions_def]
QED

Definition freeVars_def:
  freeVars RTrue = {} ∧
  freeVars RFalse = {} ∧
  freeVars (RBoolVar _) = {} ∧
  freeVars (RNot e) = freeVars e ∧
  freeVars (RAnd e1 e2) = freeVars e1 ∪ freeVars e2 ∧
  freeVars (ROr e1 e2) = freeVars e1 ∪ freeVars e2 ∧
  freeVars (RImpl e1 e2) = freeVars e1 ∪ freeVars e2 ∧
  freeVars (RIff e1 e2) = freeVars e1 ∪ freeVars e2 ∧
  freeVars (RAdd x y z) = {x; y; z} ∧
  freeVars (REq x y) = {x; y} ∧
  freeVars (RNeq x y) = {x; y} ∧
  freeVars (RLt x y) = {x; y} ∧
  freeVars (RLeq x y) = {x; y} ∧
  freeVars (RGt x y) = {x; y} ∧
  freeVars (RGeq x y) = {x; y} ∧
  freeVars (REqConst x n) = {x} ∧
  freeVars (RNeqConst x n) = {x} ∧
  freeVars (RLtConst x n) = {x} ∧
  freeVars (RLeqConst x n) = {x} ∧
  freeVars (RGtConst x n) = {x} ∧
  freeVars (RGeqConst x n) = {x} ∧
  freeVars (RConstEq n x) = {x} ∧
  freeVars (RConstNeq n x) = {x} ∧
  freeVars (RConstLt n x) = {x} ∧
  freeVars (RConstLeq n x) = {x} ∧
  freeVars (RConstGt n x) = {x} ∧
  freeVars (RConstGeq n x) = {x}
End

Theorem exp_rangeList_ok_freeVars:
  ∀ e l.
    exp_rangeList_ok l e ⇔
      ∀x. x ∈ freeVars e ⇒ MEM x (MAP FST l)
Proof
  Induct >> rw[exp_rangeList_ok_def, freeVars_def]
  >> metis_tac[]
QED

Theorem ns_filled_inner_freeVars:
  x ∈ freeVars (ns_filled_cells_to_numBoolRange_inner xs) ⇔
      MEM x (MAP FST xs)
Proof
  Induct_on‘xs’
  >> gvs[ns_filled_cells_to_numBoolRange_inner_def, freeVars_def]
QED

Theorem numberSudoku_to_exp_rangeList_ok:
  ∀ sudoku.
    sudoku_ok sudoku ⇒
    exp_rangeList_ok
    get_sudoku_rangeList
    (ns_sudoku_to_numBoolRange sudoku)
Proof
  rgs[ns_sudoku_to_numBoolRange_def]
  >> rw[exp_rangeList_ok_def]
  >- (rw[exp_rangeList_ok_freeVars, ns_filled_cells_to_numBoolRange_def]
      >> rgs[ns_filled_inner_freeVars]
      >> rgs[MEM_MAP, MEM_FILTER, EXISTS_PROD, MEM_FLAT]
      >> rgs[sudoku_ok_def]
      >> rgs[get_sudoku_with_pos_def, MEM_MAP]
      >> last_x_assum kall_tac
      >> rgs[LENGTH_EQ_NUM_compute]
      >> pop_assum mp_tac
      >> pop_assum mp_tac
      >> pop_assum mp_tac
      >> rgs[EVAL “get_positions”]
      >> rw[]
      >> (last_x_assum mp_tac
          >> EVAL_TAC
          >> rpt (strip_tac)
          >> rgs[]))
  >> rw[ns_sudoku_rules_to_numBoolRange_def]
  >> rw[create_row_col_block_lists_def]
  >> rw[ns_every_all_distinct_split]
  >- (rw[get_sudoku_with_pos_def]
      >> rw[get_positions_lemma] >> EVAL_TAC)
  >- (rw[get_col_positions_lemma]
      >> rw[get_col_positions_def] >> EVAL_TAC)
  >> rw[get_block_positions_lemma]
  >> rw[get_block_positions_def] >> EVAL_TAC
QED

Theorem numberSudoku_to_numVarAssignment_range_ok:
  ∀ sudoku w.
    sudoku_ok sudoku ∧
    assignment_ok w sudoku ⇒
    numVarAssignment_range_ok
    w
    get_sudoku_rangeList
Proof
  rgs[get_sudoku_rangeList_def]
  >> rgs[get_positions_def]
  >> rgs[numVarAssignment_range_ok_def]
  >> gvs[sudoku_ok_def]
  >> gvs[LENGTH_EQ_NUM_compute]
  >> gvs[APPLY_UPDATE_THM, get_value_def,
         assignment_ok_def, get_positions_def]
QED


Theorem numberSudoku_to_cnf_preserves_sat:
  ∀ sudoku w.
    sudoku_ok sudoku ∧
    assignment_ok w sudoku ⇒
    (eval_sudoku w sudoku ⇔
       eval_cnf
       (numberSudoku_to_assignment w sudoku)
       (numberSudoku_to_cnf sudoku))
Proof
  rw[]
  >> imp_res_tac ns_sudoku_to_numBoolRange_preserves_sat >> rgs[]
  >> rw[numberSudoku_to_cnf_def, numberSudoku_to_assignment_def]
  >> assume_tac numberSudoku_to_rangeList_ok
  >> imp_res_tac numberSudoku_to_exp_rangeList_ok
  >> imp_res_tac numberSudoku_to_numVarAssignment_range_ok
  >> metis_tac [numBoolRange_to_cnf_preserves_sat]
QED


(* ------------------ Encode assignment ------------------------------- *)

Theorem mem_sudoku_rangeList:
  ∀ p.
    MEM p (FLAT get_positions) ⇒
    MEM p (MAP FST get_sudoku_rangeList)
Proof
  rw[get_sudoku_rangeList_lemma]
QED


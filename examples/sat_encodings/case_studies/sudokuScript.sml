(*
  Encoding of sudoku to unordered sets
*)
Theory sudoku
Ancestors
  misc ASCIInumbers set_sep quantifierExp unorderedSets
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


(* ---------------- Help functions ------------------------- *)

Definition get_positions_def:
  get_positions = GENLIST (λ row. GENLIST (λ col. row * 10 + col) 9) 9
End

Definition get_sudoku_with_pos_def:
  get_sudoku_with_pos sudoku = MAP ZIP (ZIP (get_positions, sudoku))
End

Definition get_cell_def:
  get_cell i j (sudoku:(num # num) list list) =
  let row = case oEL i sudoku of
            | SOME row => row
            | NONE => [] in
    case oEL j row of
    | SOME cell => cell
    | NONE => (0, 0)
End

Definition get_cols_def:
  get_cols (sudoku:(num # num) list list) =
  GENLIST
  (λ col. GENLIST
        (λ row. get_cell row col sudoku) 9) 9
End


Definition get_blocks_def:
  get_blocks (sudoku: (num # num) list list) =
  FLAT (GENLIST
  (λi. GENLIST (λj. [(get_cell (i*3+0) (j*3+0) sudoku);
                     (get_cell (i*3+1) (j*3+0) sudoku);
                     (get_cell (i*3+2) (j*3+0) sudoku);
                     (get_cell (i*3+0) (j*3+1) sudoku);
                     (get_cell (i*3+1) (j*3+1) sudoku);
                     (get_cell (i*3+2) (j*3+1) sudoku);
                     (get_cell (i*3+0) (j*3+2) sudoku);
                     (get_cell (i*3+1) (j*3+2) sudoku);
                     (get_cell (i*3+2) (j*3+2) sudoku)] ) 3 ) 3)
End

Definition create_row_col_block_lists_def:
  create_row_col_block_lists (sudoku:sudoku) =
  let sudoku_with_pos = get_sudoku_with_pos sudoku in
  sudoku_with_pos ++ (get_cols sudoku_with_pos) ++ (get_blocks sudoku_with_pos)
End

(* -------------------- Well formed ------------------------- *)

Definition sudoku_ok_def:
  sudoku_ok (sudoku:sudoku) ⇔
    (LENGTH sudoku = 9) ∧
    EVERY (λ row. LENGTH row = 9) sudoku ∧
    (EVERY (λ n. 0 ≤ n ∧ n ≤ 9) (FLAT sudoku))
End

Definition assignment_ok_def:
  assignment_ok (w:cellAssignment)  ⇔
    EVERY (EVERY (λ pos. 1 ≤ w pos ∧ w pos ≤ 9)) get_positions
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

Definition filled_cells_to_equation_inner_def:
  filled_cells_to_equation_inner [] = EqTrue ∧
  filled_cells_to_equation_inner (c::cs) =
  EqAnd
  (EqVarCon (FST c, "sudokuSet") (num_to_dec_string (SND c)))
  (filled_cells_to_equation_inner cs)
End

Definition filled_cells_to_equation_def:
  filled_cells_to_equation sudoku =
  let sudoku_with_pos = get_sudoku_with_pos sudoku in
    let filled_cells = FILTER (λ (pos, val). val ≠ 0) (FLAT sudoku_with_pos) in
      filled_cells_to_equation_inner filled_cells
End

Definition not_member_def:
  not_member c [] = EqTrue ∧
  not_member c (c'::cs) =
  EqAnd
  (EqNot (EqVarVar c c'))
  (not_member c cs)
End

Definition all_distinct_def:
  all_distinct [] = EqTrue ∧
  all_distinct (c::cs) =
  EqAnd
  (not_member c cs)
  (all_distinct cs)
End

Definition every_all_distinct_def:
  every_all_distinct [] = EqTrue ∧
  every_all_distinct (l::ls) =
  EqAnd (all_distinct l) (every_all_distinct ls)
End

Definition sudoku_rules_to_equation_def:
  sudoku_rules_to_equation sudoku =
  let lists_with_pos = create_row_col_block_lists sudoku in
    let variable_lists =
        MAP (MAP (λ (pos, cell). (pos, "sudokuSet"))) lists_with_pos in
      every_all_distinct variable_lists
End

Definition sudoku_to_equation_def:
  sudoku_to_equation sudoku =
  EqAnd (filled_cells_to_equation sudoku) (sudoku_rules_to_equation sudoku)
End

Definition get_value_def:
  get_value (w:cellAssignment) (p:pos) (c:cell) ⇔
    if c = 0 then w p else c
End

Definition add_cellAssignment_def:
  add_cellAssignment (w:cellAssignment) (w':elementVarAssignment) [] =
  w' ∧
  add_cellAssignment w w' ((p, c)::ps) =
  let v = get_value w p c in
    let w'_new = (p =+ num_to_dec_string v)w' in
      add_cellAssignment w w'_new ps
End

Definition encode_cellAssignment_def:
  encode_cellAssignment (w:cellAssignment) (sudoku:sudoku) =
  let sudoku_with_pos = get_sudoku_with_pos sudoku in
      add_cellAssignment w (λ _.  "") (FLAT sudoku_with_pos)
End


(* ------------------ Theorems ------------------------------- *)

Theorem all_pos_unique:
  ∀ sudoku.
    sudoku_ok sudoku ⇒
    ALL_DISTINCT (MAP FST (FLAT (get_sudoku_with_pos sudoku)))
Proof
  rw[get_sudoku_with_pos_def, get_positions_def, sudoku_ok_def]
  >> gvs[LENGTH_EQ_NUM_compute]
QED

Theorem add_assignment_lemma:
  ∀ l pos w w' v.
    ¬MEM pos (MAP FST l) ∧
    ALL_DISTINCT (MAP FST l) ⇒
    (add_cellAssignment w w'⦇pos ↦ v⦈ l =
     (add_cellAssignment w w' l)⦇pos ↦ v⦈)
Proof
  Induct
  >- rw[add_cellAssignment_def]
  >> Cases_on ‘h’
  >> gs[add_cellAssignment_def, get_value_def, UPDATE_COMMUTES]
QED

Theorem add_unused_assignment_lemma:
  ∀ l pos w w' v.
    ¬MEM pos (MAP FST l) ∧
    ALL_DISTINCT (MAP FST l) ⇒
    (eval_equation
     (λ_. F)
     (add_cellAssignment w w'⦇pos ↦ v⦈ l)
     (filled_cells_to_equation_inner (FILTER (λ(pos,val). val ≠ 0) l)) ⇔
       eval_equation
       (λ_. F)
       (add_cellAssignment w w' l)
       (filled_cells_to_equation_inner (FILTER (λ(pos,val). val ≠ 0) l)))
Proof
  Induct
  >- rw[filled_cells_to_equation_inner_def, eval_equation_def]
  >> rw[]
  (* Cell not empty *)
  >- (Cases_on ‘h’
      >> rw[add_cellAssignment_def]
      >> gs[get_value_def, filled_cells_to_equation_inner_def,
            eval_equation_def]
      >> gs[UPDATE_COMMUTES, add_assignment_lemma, APPLY_UPDATE_THM]
      >> rw[])
  (* Cell empty *)
  >> Cases_on ‘h’
  >> rw[add_cellAssignment_def]
  >> gs[get_value_def]
QED

Theorem encode_filled_cells_lemma:
  ∀ l w.
    assignment_ok w ∧
    ALL_DISTINCT (MAP FST l) ⇒
    eval_equation
    (λ_. F)
    (add_cellAssignment w (λ_.  "") l)
    (filled_cells_to_equation_inner (FILTER (λ(pos,val). val ≠ 0) l))
Proof
  Induct
  >- rw[filled_cells_to_equation_inner_def, eval_equation_def]
  >> Cases_on ‘h’
  >> Cases_on ‘r = 0’
  >- (rw[]
      >> gs[add_cellAssignment_def, get_value_def]
      >> gs[add_unused_assignment_lemma])
  >> rw[filled_cells_to_equation_inner_def, add_cellAssignment_def]
  >> rw[eval_equation_def, add_unused_assignment_lemma]
  >> rw[add_assignment_lemma, APPLY_UPDATE_THM, get_value_def]
QED

Theorem encode_filled_cells_always_true:
  ∀ sudoku w.
    sudoku_ok sudoku ∧
    assignment_ok w ⇒
    eval_equation
    (λ _. F)
    (encode_cellAssignment w sudoku)
    (filled_cells_to_equation sudoku)
Proof
  rw[filled_cells_to_equation_def]
  >> rw[encode_cellAssignment_def]
  >> qspecl_then [‘sudoku’] assume_tac all_pos_unique
  >> gs[sudoku_ok_def]
  >> gs[encode_filled_cells_lemma]
QED

Theorem value_equal_lemma:
  ∀ l pos1 pos2 cell1 cell2 w w'.
    ¬MEM pos1 (MAP FST l) ∧
    ALL_DISTINCT (MAP FST l) ∧
    MEM (pos2, cell2) l ∧
    pos1 ≠ pos2 ⇒
    (fill_cell w (pos1, cell1) = fill_cell w (pos2, cell2) ⇔
       num_to_dec_string (get_value w pos1 cell1) =
       add_cellAssignment w w' l pos2)
Proof
  Induct >> rw[]
  >- (gs[add_cellAssignment_def, add_assignment_lemma, APPLY_UPDATE_THM]
      >> rw[get_value_def, fill_cell_def])
  >> Cases_on ‘h’
  >> rw[add_cellAssignment_def]
QED

Theorem value_equal:
  ∀ l pos1 pos2 cell1 cell2 w w'.
    ALL_DISTINCT (MAP FST l) ∧
    MEM (pos1, cell1) l ∧
    MEM (pos2, cell2) l ∧
    (pos1 = pos2 ⇒ cell1 = cell2) ⇒
    (fill_cell w (pos1, cell1) = fill_cell w (pos2, cell2) ⇔
       add_cellAssignment w w' l pos1 =
                          add_cellAssignment w w' l pos2)
Proof
  Induct >> rw[]
  >- (gs[add_cellAssignment_def, add_assignment_lemma, APPLY_UPDATE_THM]
      >> rw[]
      >> metis_tac[value_equal_lemma])
  >- (gs[add_cellAssignment_def, add_assignment_lemma, APPLY_UPDATE_THM]
      >> rw[]
      >> metis_tac[value_equal_lemma])
  >> Cases_on ‘h’
  >> gs[add_cellAssignment_def]
QED

Theorem mem_lemma:
  ∀ l pos cell.
    MEM (pos, cell) l ⇒
    MEM pos (MAP FST l)
Proof
  Induct
  >> rw[]
  >- gs[]
  >> metis_tac[]
QED

Theorem not_different_cells_for_same_pos:
  ∀ l pos1 pos2 cell1 cell2.
    ALL_DISTINCT (MAP FST l) ∧
    MEM (pos1, cell1) l ∧
    MEM (pos2, cell2) l ⇒
    (pos1 = pos2 ⇒ cell1 = cell2)
Proof
  Induct
  >- rw[]
  >> rw[]
  >> gs[]
  >> metis_tac[mem_lemma]
QED

Theorem not_member_lemma:
  ∀ l w w' sudoku pos cell.
    assignment_ok w ∧
    sudoku_ok sudoku ∧
    ALL_DISTINCT (MAP FST (FLAT (get_sudoku_with_pos sudoku))) ∧
    MEM (pos, cell) (FLAT (get_sudoku_with_pos sudoku)) ∧
    EVERY
    (λ(pos, cell). MEM (pos,cell) (FLAT (get_sudoku_with_pos sudoku))) l ⇒
    (¬MEM (fill_cell w (pos, cell) ) (MAP (fill_cell w) l) ⇔
       eval_equation
       (λ_. F)
       (add_cellAssignment w w' (FLAT (get_sudoku_with_pos sudoku)))
       (not_member
        (pos, "sudokuSet")
        (MAP (λ(pos, cell). (pos, "sudokuSet")) l)))
Proof
  Induct
  >- rw[not_member_def, eval_equation_def]
  >> Cases_on ‘h’
  >> gs[not_member_def, eval_equation_def]
  >> rw[]
  >> metis_tac[not_different_cells_for_same_pos, value_equal]
QED

Theorem every_all_distinct_in_list_lemma:
  ∀ l w w' sudoku.
    assignment_ok w ∧
    sudoku_ok sudoku ∧
    ALL_DISTINCT (MAP FST (FLAT (get_sudoku_with_pos sudoku))) ∧
    EVERY
    (λ(pos, cell). MEM (pos,cell) (FLAT (get_sudoku_with_pos sudoku))) l ⇒
    (ALL_DISTINCT (MAP (fill_cell w) l) ⇔
       eval_equation
       (λ_. F)
       (add_cellAssignment w w' (FLAT (get_sudoku_with_pos sudoku)))
       (all_distinct (MAP (λ(pos, cell). (pos, "sudokuSet")) l)))
Proof
  Induct
  >- rw[all_distinct_def, eval_equation_def]
  >> rw[]
  >> Cases_on ‘h’
  >> rw[]
  >> rw[all_distinct_def]
  >> rw[eval_equation_def]
  >> gs[]
  >> metis_tac[not_member_lemma]
QED

Theorem every_all_distinct_lemma:
  ∀ l w w' sudoku.
    assignment_ok w ∧
    sudoku_ok sudoku ∧
    EVERY
    (EVERY
     (λ(pos, cell). MEM (pos, cell) (FLAT (get_sudoku_with_pos sudoku)))) l ⇒
    (EVERY ALL_DISTINCT (MAP (MAP (fill_cell w)) l) ⇔
       eval_equation
       (λ_. F)
       (add_cellAssignment w w' (FLAT (get_sudoku_with_pos sudoku)))
       (every_all_distinct (MAP (MAP (λ(pos, cell). (pos, "sudokuSet"))) l)))
Proof
  Induct
  >- rw[every_all_distinct_def, eval_equation_def]
  >> rw[every_all_distinct_def, eval_equation_def]
  >> qspecl_then [‘sudoku’] assume_tac all_pos_unique >> gs[]
  >> metis_tac[every_all_distinct_in_list_lemma]
QED


Theorem row_mem_sudoku:
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


Theorem col_mem_sudoku:
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


Theorem block_mem_sudoku:
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


Theorem row_col_block_mem_sudoku:
  ∀ sudoku.
    sudoku_ok sudoku ⇒
    (EVERY (EVERY
            (λ(pos, cell). MEM (pos, cell)
                               (FLAT (get_sudoku_with_pos sudoku))))
     (create_row_col_block_lists sudoku))
Proof
  rw[create_row_col_block_lists_def, sudoku_ok_def]
  >- metis_tac[row_mem_sudoku]
  >- metis_tac[col_mem_sudoku]
  >> metis_tac[block_mem_sudoku]
QED

Theorem every_all_distinct_in_lists:
  ∀ w sudoku.
    sudoku_ok sudoku ∧
    assignment_ok w ⇒
    (EVERY ALL_DISTINCT
     (MAP (MAP (fill_cell w)) (create_row_col_block_lists sudoku)) ⇔
       eval_equation
       (λ _. F)
       (encode_cellAssignment w sudoku)
       (every_all_distinct (MAP (MAP (λ(pos, cell). (pos, "sudokuSet")))
                            (create_row_col_block_lists sudoku))))
Proof
  rw[encode_cellAssignment_def]
  >> qspecl_then [‘sudoku’] assume_tac row_col_block_mem_sudoku >> gs[]
  >> rw[every_all_distinct_lemma]
QED

Theorem sudoku_to_equation_preserves_sat:
  ∀ sudoku w.
    sudoku_ok sudoku ∧
    assignment_ok w ⇒
    (eval_sudoku w sudoku ⇔
       eval_equation
       (λ _. F)
       (encode_cellAssignment w sudoku)
       (sudoku_to_equation sudoku))
Proof
  rw[eval_sudoku_def, sudoku_to_equation_def, eval_equation_def,
     encode_filled_cells_always_true, sudoku_rules_to_equation_def,
     every_all_distinct_in_lists]
QED



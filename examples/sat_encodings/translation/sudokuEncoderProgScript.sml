(*
  Encoding program for the sudoku puzzle
*)
Theory sudokuEncoderProg
Ancestors
  misc set_sep list cnf boolExpToCnf quantifierExp
  orderEncodingBool numBoolExp numBoolExtended numBoolRange
  unorderedSets sudoku numberSudoku
  (* for parsing: *) parsing source_values
  toCnfHelper sat_encodersProg
Libs
  preamble basis

val _ = translation_extends "sat_encodersProg";

val _ = show_assums := true;

(* numberSudoku *)
val res = translate ns_filled_cells_to_numBoolRange_inner_def;
val res = translate get_positions_def;
val res = translate get_sudoku_with_pos_def;
val res = translate ns_filled_cells_to_numBoolRange_def;
val res = translate ns_not_member_def;
val res = translate ns_all_distinct_def;
val res = translate ns_every_all_distinct_def;
val res = translate oEL_def;
val res = translate get_cell_def;
val res = translate get_cols_def;
val res = translate get_blocks_def;
val res = translate create_row_col_block_lists_def;
val res = translate ns_sudoku_rules_to_numBoolRange_def;
val res = translate ns_sudoku_to_numBoolRange_def;
val res = translate get_value_def;
val res = translate sudoku_ok_def;
val res = translate get_sudoku_rangeList_def;
val res = translate numberSudoku_to_cnf_def;
val res = translate assignment_to_cellAssignment_def;
val res = translate fill_cell_def;
val res = translate numberSudoku_to_cnf_def;

Definition from_v_to_num_def:
  from_v_to_num (Num n) = n ∧
  from_v_to_num (Pair _ _) = 10
End

Definition from_v_to_numberSudoku_def:
  from_v_to_numberSudoku sudoku =
  let list_of_lists = MAP v2list (v2list sudoku) in
    MAP (λ l. MAP from_v_to_num l) list_of_lists
End

Definition parse_to_numberSudoku_def:
  parse_to_numberSudoku s =
  from_v_to_numberSudoku (from_str s)
End

Definition encode_to_output_def:
  encode_to_output v_exp =
  let sudoku = from_v_to_numberSudoku v_exp in
    case sudoku_ok sudoku of
    | F => (List [strlit "Invalid rangeList input"])
    | T =>
        let cnf_exp = numberSudoku_to_cnf sudoku in
          let (max_var, clauses) = get_max_var_and_clauses cnf_exp in
            Append
            (List [strlit "p cnf "; num_to_str max_var; strlit " "; num_to_str clauses; strlit "\n"])
            (cnf_to_output cnf_exp)
End

Definition sat_to_assignment_inner_def:
  sat_to_assignment_inner w [] = w ∧
  sat_to_assignment_inner w (l::ls) =
  case l of
  | (Pair _ _) => sat_to_assignment_inner w ls
  | (Num n) => sat_to_assignment_inner w⦇n ↦ T⦈ ls
End

Definition sat_to_assignment_def:
  sat_to_assignment ls = sat_to_assignment_inner (λ_. F) ls
End

Definition row_to_output_def:
  row_to_output [] = List [] ∧
  row_to_output [c] = List [num_to_str c] ∧
  row_to_output (c::cells) =
  Append (List [num_to_str c; (strlit " ")]) (row_to_output cells)
End

Definition sudoku_to_output_inner_def:
  sudoku_to_output_inner [] = List [] ∧
  sudoku_to_output_inner [row] = row_to_output row ∧
  sudoku_to_output_inner (row::rows) =
  Append (row_to_output row) (Append (List [strlit "\n"]) (sudoku_to_output_inner rows))
End

Definition sudoku_to_output_def:
  sudoku_to_output sudoku =
  Append (List [strlit "("]) (Append (sudoku_to_output_inner sudoku) (List [strlit ")"]))
End

Definition solve_to_output_def:
  solve_to_output v_exp sat =
  let sudoku = from_v_to_numberSudoku v_exp in
    let w = sat_to_assignment (v2list sat) in
      let w' = assignment_to_cellAssignment w sudoku in
        let sudoku_with_pos = get_sudoku_with_pos sudoku in
          let solved_sudoku = MAP (λ row. MAP (fill_cell w') row) sudoku_with_pos in
            sudoku_to_output solved_sudoku
End

Definition main_function_def:
  main_function (s:mlstring) =
  let v_exp = from_str (explode s) in
    case v_exp of
    | (Pair _ (Pair (Pair (Num 7561588) _) _)) =>
        solve_to_output (head v_exp) (tail (head (tail v_exp)))
    | _ => encode_to_output v_exp
End

val res = translate from_v_to_num_def;
val res = translate from_v_to_numberSudoku_def;
val res = translate parse_to_numberSudoku_def;
val res = translate literal_to_output_def;
val res = translate clause_to_output_def;
val res = translate cnf_to_output_def;
val res = translate get_max_var_def;
val res = translate get_max_var_and_clauses_def;

val res = translate encode_to_output_def;
val res = translate sat_to_assignment_inner_def;
val res = translate sat_to_assignment_def;
val res = translate row_to_output_def;
val res = translate sudoku_to_output_inner_def;
val res = translate sudoku_to_output_def;
val res = translate solve_to_output_def;
val res = translate main_function_def;

val _ = type_of “main_function” = “:mlstring -> mlstring app_list”
        orelse failwith "The main_function has the wrong type.";

val main = process_topdecs
  `print_app_list (main_function (TextIO.inputAll TextIO.stdIn));`;

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand

Definition sudoku_encoder_prog_def:
  sudoku_encoder_prog = ^prog
End

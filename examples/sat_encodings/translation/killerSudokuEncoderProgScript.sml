(*
  Encoding program for the killer sudoku puzzle
*)
Theory killerSudokuEncoderProg
Ancestors
  misc set_sep list cnf boolExpToCnf quantifierExp
  orderEncodingBool numBoolExp numBoolExtended numBoolRange
  unorderedSets sudoku numberSudoku killerSudoku
  (* for parsing: *) parsing source_values
  toCnfHelper sat_encodersProg
Libs
  preamble basis

val _ = translation_extends "sat_encodersProg";

val _ = show_assums := true;

(* killerSudoku *)
val res = translate get_positions_def;
val res = translate get_sudoku_rangeList_def;
val res = translate ns_not_member_def;
val res = translate ns_all_distinct_def;
val res = translate ns_every_all_distinct_def;
val res = translate get_row_positions_def;
val res = translate get_col_positions_def;
val res = translate get_block_positions_def;
val res = translate get_row_col_block_positions_def;
val res = translate one_cage_to_numBoolRanges_def;
val res = translate cages_to_numBoolRanges_inner_def;
val res = translate cages_to_numBoolRanges_def;
val res = translate killerSudoku_to_numBoolRanges_def;
val res = translate one_cage_to_rangeList_def;
val res = translate cages_to_rangeList_def;
val res = translate get_killerSudoku_rangeList_def;
val res = translate killerSudoku_to_cnf_def;
val res = translate get_all_positions_def;
val res = translate (REWRITE_RULE [MEMBER_INTRO] killerSudoku_ok_def);
val res = translate assignment_to_cellAssignment_killerSudoku_def;

(* ----------------- v to cageList ----------------------- *)

Definition from_v_to_num_def:
  from_v_to_num (Num n) = n ∧
  from_v_to_num (Pair _ _) = 10
End

Definition v2cage_def:
  v2cage v_exp =
  let value = from_v_to_num (head v_exp) in
    let l = MAP from_v_to_num (v2list (head (tail v_exp))) in
      (value, l)
End

Definition v2cageList_def:
  v2cageList v_exp =
  let v_list = v2list v_exp in
    MAP v2cage v_list
End

(* ------------------- Encode to output --------------------- *)

Definition encode_to_output_def:
  encode_to_output v_exp =
  let cages = v2cageList v_exp in
    case killerSudoku_ok cages of
    | F => (List [strlit "Invalid input"])
    | T =>
        let cnf_exp = killerSudoku_to_cnf cages in
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
  row_to_output (c::cells) =
  Append (List [num_to_str c; (strlit " ")]) (row_to_output cells)
End

Definition sudoku_to_output_def:
  sudoku_to_output [] = List [] ∧
  sudoku_to_output (row::rows) =
  Append (row_to_output row) (Append (List [strlit "\n"]) (sudoku_to_output rows))
End

Definition solve_to_output_def:
  solve_to_output v_exp sat =
  let cages = v2cageList v_exp in
    let w = sat_to_assignment (v2list sat) in
      let w' = assignment_to_cellAssignment_killerSudoku w cages in
        let pos = get_positions in
          let solved_sudoku = MAP (λ row. MAP w' row) pos in
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

val res = translate literal_to_output_def;
val res = translate clause_to_output_def;
val res = translate cnf_to_output_def;
val res = translate get_max_var_def;
val res = translate get_max_var_and_clauses_def;

val res = translate from_v_to_num_def;
val res = translate v2cage_def;
val res = translate v2cageList_def;
val res = translate encode_to_output_def;
val res = translate sat_to_assignment_inner_def;
val res = translate sat_to_assignment_def;
val res = translate row_to_output_def;
val res = translate sudoku_to_output_def;
val res = translate solve_to_output_def;
val res = translate main_function_def;

val _ = type_of “main_function” = “:mlstring -> mlstring app_list”
        orelse failwith "The main_function has the wrong type.";

val main = process_topdecs
  `print_app_list (main_function (TextIO.inputAll (TextIO.openStdIn ())));`;

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand

Definition killerSudoku_encoder_prog_def:
  killerSudoku_encoder_prog = ^prog
End

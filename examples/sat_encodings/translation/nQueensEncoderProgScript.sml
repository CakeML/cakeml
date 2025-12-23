(*
  Encoding program for the n-queens problem
*)
Theory nQueensEncoderProg
Ancestors
  misc set_sep list cnf boolExpToCnf quantifierExp
  orderEncodingBool nqueens
  (* for parsing: *) parsing source_values
  toCnfHelper sat_encodersProg
Libs
  preamble basis


val _ = translation_extends "sat_encodersProg";

val _ = show_assums := true;

val res = translate every_at_most_one_def;
val res = translate get_rows_def;
val res = translate get_cols_def;
val res = translate (REWRITE_RULE [MEMBER_INTRO] nub_def);
val res = translate oEL_def;
val res = translate get_element_def;
val res = translate get_lr_diagonals_def;
val res = translate get_rl_diagonals_def;
val res = translate get_diagonals_def;
val res = translate every_at_least_one_def;
val res = translate nqueens_to_pseudoBool_def;
val res = translate nqueens_to_cnf_def

Definition from_v_to_num_def:
  from_v_to_num (Num n) = n ∧
  from_v_to_num (Pair _ _) = 0
End

Definition encode_to_output_def:
  encode_to_output v_exp =
  let n = from_v_to_num v_exp in
    let cnf_exp = nqueens_to_cnf n in
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

Definition bool_to_output_def:
  bool_to_output T = strlit "X" ∧
  bool_to_output F = strlit "O"
End

Definition row_to_output_def:
  row_to_output [] = List [] ∧
  row_to_output (c::cells) =
  Append (List [bool_to_output c; (strlit " ")]) (row_to_output cells)
End

Definition problem_to_output_def:
  problem_to_output [] = List [] ∧
  problem_to_output (row::rows) =
  Append (row_to_output row) (Append (List [strlit "\n"]) (problem_to_output rows))
End

Definition get_solved_rows_def:
  get_solved_rows (w:assignment) (n:num) =
  MAP (λ row. MAP w row) (get_rows n)
End

Definition solve_to_output_def:
  solve_to_output v_exp sat =
  let n = from_v_to_num v_exp in
    let w = sat_to_assignment (v2list sat) in
      let solved_rows = get_solved_rows w n in
        problem_to_output solved_rows
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
val res = translate literal_to_output_def;
val res = translate clause_to_output_def;
val res = translate cnf_to_output_def;
val res = translate get_max_var_def;
val res = translate get_max_var_and_clauses_def;
val res = translate encode_to_output_def;
val res = translate sat_to_assignment_inner_def;
val res = translate sat_to_assignment_def;
val res = translate bool_to_output_def;
val res = translate row_to_output_def;
val res = translate problem_to_output_def;
val res = translate get_solved_rows_def;
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

Definition nQueens_encoder_prog_def:
  nQueens_encoder_prog = ^prog
End

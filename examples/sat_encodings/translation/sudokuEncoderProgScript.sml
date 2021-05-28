(*
  Encoding program for the sudoku puzzle
*)

open preamble basis miscTheory set_sepTheory listTheory;
open boolExpToCnfTheory quantifierExpTheory orderEncodingBoolTheory;
open numBoolExpTheory numBoolExtendedTheory numBoolRangeTheory;
open unorderedSetsTheory sudokuTheory numberSudokuTheory;
open (* for parsing: *) parsingTheory source_valuesTheory;
open tseytinTheory;
open toCnfHelperTheory;

val _ = new_theory "sudokuEncoderProg";

val _ = translation_extends "basisProg";

show_assums := true;


(* boolExpToCnf *)
val res = translate distr_def;
val res = translate nnf_to_cnf_def;
val res = translate negate_literal_def;
val res = translate noImp_to_nnf_def;
val res = translate boolExp_to_noImp_def;
val res = translate boolExp_to_cnf_def;

(* quantifierExp *)
val res = translate bool_to_quant_def;
val res = translate quant_size';
val res = translate pseudoBool_size';
val res = translate replace_name_quant_def;
val res = translate quant_to_boolExp_def;
val res = translate none_of_list_to_quant_def;
val res = translate most_one_to_quant_def;
val res = translate pseudoBool_to_quant_def;
val res = translate pseudoBool_to_cnf_def;

(* orderEncodingBool *)
val res = translate orderBool_size';
val res = translate encode_orderAxiom_def;
val res = translate orderBool_to_pseudoBool_def;
val res = translate orderBool_to_cnf_def;

(* numBoolExp *)
val res = translate (REWRITE_RULE [MEMBER_INTRO] add_numVar_to_list_def);
val res = translate (REWRITE_RULE [MEMBER_INTRO] nub_def);
val res = translate create_numVarList_inner_def;
val res = translate create_numVarList_def;
val res = translate get_fresh_boolVar_def;
val res = translate create_numVarMap_inner_def;
val res = translate create_numVarMap_def;

val res = translate vMap_to_orderBool_def;
val res = translate encode_combinations_def;
val res = translate encode_add_def;
val res = translate encode_leq_def;
val res = translate EL;

val el_side_def =
fetch "-" "el_side_def";

Theorem el_side:
  ∀ n l.
    n < LENGTH l ⇒
    el_side n l
Proof
  gs[Once el_side_def]
  >> Induct
  >- (rw[]
      >> Cases_on ‘l = []’ >> gs[])
  >> rw[]
  >> rw[Once el_side_def]
  >- (Cases_on ‘l’ >> gs[]
      >> Cases_on ‘t’ >> gs[])
  >> first_x_assum (qspecl_then [‘TL l’] assume_tac)
  >> first_x_assum irule
  >> gs[ADD1]
  >> Cases_on ‘l’ >> gs[]
QED

val res = translate encode_eqConst_def; (* side *)

val encode_eqconst_side_def =
fetch "-" "encode_eqconst_side_def";

Theorem encode_eqconst_side:
  ∀ n bvs.
    encode_eqconst_side n bvs
Proof
  gs[Once encode_eqconst_side_def]
  >> rw[]
  >- gs[]
  >- (irule el_side
      >> gs[])
  >> irule el_side
  >> gs[]
QED

val _ = update_precondition encode_eqconst_side;

val res = translate encode_leqConst_def; (* side *)

val encode_leqconst_side_def =
fetch "-" "encode_leqconst_side_def";

Theorem encode_leqconst_side:
  ∀ n bvs.
    encode_leqconst_side n bvs
Proof
  rw[Once encode_leqconst_side_def]
  >> irule el_side
  >> gs[]
QED

val _ = update_precondition encode_leqconst_side;

val res = translate numBoolExp_to_orderBool_def;
val res = translate encode_axioms_def;
val res = translate numBool_to_orderBool_def;
val res = translate numBool_to_cnf_def;
val res = translate invert_numVarMap_def;
val res = translate encode_assignment_def;
val res = translate minimal_encode_assignment_def;
val res = translate find_value_def;
val res = translate assignment_to_numVarAssignment_def;
val res = translate minimal_assignment_to_numVarAssignment_def;

(* numBoolExtended *)
val res = translate create_numVarList_numBoolExtended_inner_def;
val res = translate create_numVarList_numBoolExtended_def;
val res = translate numBoolExtended_to_numBoolExp_def;
val res = translate numBoolExtended_to_cnf_def;
val res = translate encode_assignment_numBoolExtended_def;
val res = translate assignment_to_numVarAssignment_numBoolExtended_def;

(* numBoolRange *)
val res = translate equation_to_numBoolExtended_def;
val res = translate ranges_to_numBoolExtended_def;
val res = translate numBoolRange_to_numBoolExtended_def;
val res = translate get_highest_max_def;
val res = translate rangeList_to_numVarList_def;
val res = translate numBoolRange_to_cnf_def;
val res = translate encode_assignment_numBoolRange_def;
val res = translate assignment_to_numVarAssignment_numBoolRange_def;

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

(* Tseytin *)
val res = translate boolExp_to_constFree_def;
val res = translate get_fresh_name_constFree_def;
val res = translate bind_def;
val res = translate constFree_to_cnf_inner_def;
val res = translate replace_not_def;
val res = translate replace_or_def;
val res = translate replace_and_def;
val res = translate replace_impl_def;
val res = translate replace_iff_def;
val res = translate rhs_to_cnf_def;
val res = translate map_to_cnf_def;
val res = translate append_aux_def;
val res = translate append_def;
val res = translate constFree_to_cnf_def;
val res = translate t_boolExp_to_cnf_def;
val res = translate t_pseudoBool_to_cnf_def;
val res = translate t_orderBool_to_cnf_def;
val res = translate t_numBool_to_cnf_def;
val res = translate t_numBoolExtended_to_cnf_def;
val res = translate t_numBoolRange_to_cnf_def;
val res = translate t_numberSudoku_to_cnf_def;



Definition from_str_def:
  from_str s = head (parse (lexer s) (Num 0) [])
End

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
        let cnf_exp = t_numberSudoku_to_cnf sudoku in
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

val res = translate name_def;
val res = translate head_def;
val res = translate tail_def;
val res = translate isNum_def;
val res = translate v2list_def;
val res = translate from_v_to_num_def;
val res = translate list_def;
val res = translate quote_def;
val res = translate parse_def;
val res = translate end_line_def;
val res = translate read_num_def;
val res = translate (REWRITE_RULE [MEMBER_INTRO] lex_def);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ gvs[MEMBER_def])
  |> update_precondition;

val res = translate lexer_def;
val res = translate from_str_def;

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

val _ = export_theory();

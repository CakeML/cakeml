(*
  Encoding program for the graph coloring problem
*)

open preamble basis miscTheory set_sepTheory listTheory;
open boolExpToCnfTheory quantifierExpTheory orderEncodingBoolTheory;
open numBoolExpTheory numBoolExtendedTheory numBoolRangeTheory;
open unorderedSetsTheory tseytinTheory graphColoringTheory;
open (* for parsing: *) parsingTheory source_valuesTheory;
open toCnfHelperTheory;

val _ = new_theory "graphColoringEncoderProg";

val _ = translation_extends "basisProg";

show_assums := true;

(* quantifierExp *)
val res = translate bool_to_quant_def;
val res = translate quant_size';
val res = translate pseudoBool_size';
val res = translate replace_name_quant_def;
val res = translate quant_to_boolExp_def;
val res = translate none_of_list_to_quant_def;
val res = translate most_one_to_quant_def;
val res = translate pseudoBool_to_quant_def;

(* orderEncodingBool *)
val res = translate orderBool_size';
val res = translate encode_orderAxiom_def;
val res = translate orderBool_to_pseudoBool_def;

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
val res = translate encode_assignment_numBoolExtended_def;
val res = translate assignment_to_numVarAssignment_numBoolExtended_def;

(* numBoolRange *)
val res = translate equation_to_numBoolExtended_def;
val res = translate ranges_to_numBoolExtended_def;
val res = translate numBoolRange_to_numBoolExtended_def;
val res = translate get_highest_max_def;
val res = translate rangeList_to_numVarList_def;
val res = translate encode_assignment_numBoolRange_def;
val res = translate assignment_to_numVarAssignment_numBoolRange_def;

(* unorderedSet *)
val res = translate get_varList_inner_def;
val res = translate get_varList_def;
val res = translate indexedListsTheory.findi_def;
val res = translate encode_constant_def;
val res = translate equation_to_numBoolRange_def;
val res = translate get_setName_def;
val res = translate elementVarAssignment_to_numVarAssignment_inner_def;
val res = translate elementVarAssignment_to_numVarAssignment_def;
val res = translate get_max_def;
val res = translate equation_to_rangeList_inner_def;
val res = translate equation_to_rangeList_def;
val res = translate encode_assignment_unorderedSet_def;
val res = translate oEL_def;
val res = translate numVarAssignment_to_elementVarAssignment_inner_def;
val res = translate numVarAssignment_to_elementVarAssignment_def;
val res = translate assignment_to_elementVarAssignment_def;

(* Tseytin *)
val res = translate boolExp_to_constFree_def;
val res = translate get_fresh_name_constFree_def;
val res = translate bind_def;
val res = translate constFree_to_cnf_inner_def;
val res = translate negate_literal_def;
val res = translate replace_not_def;
val res = translate replace_and_def;
val res = translate replace_or_def;
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
val res = translate t_equation_to_cnf_def;

(* Graph coloring *)
val res = translate vertex_to_equation_def;
val res = translate graphColoring_to_equation_def;
val res = translate colorList_to_setList_def;
val res = translate t_graphColoring_to_cnf_def;
val res = translate assignment_to_vertexColorAssignment_def;
val res = translate graph_ok_def;


(* ------------------------- v to colorList --------------------------- *)

Definition from_str_def:
  from_str s = head (parse (lexer s) (Num 0) [])
End

Definition v2color_def:
  v2color v =
  if v = Name "red" then "red"
  else if v = Name "blue" then "blue"
  else if v = Name "green" then "green"
  else ""
End

Definition v2colorList_def:
  v2colorList v = MAP v2color (v2list v)
End

EVAL “from_str "(red blue)"”;
EVAL “v2colorList (from_str "(red blue)")”;


(* -------------------------- v to graph ------------------------------- *)

Definition v2num_def:
  v2num (Num n) = (n:num) ∧
  v2num (Pair _ _) = 0
End

Definition v2vertex_def:
  v2vertex v = (v2num (head v), MAP v2num (v2list (head (tail v))))
End

Definition v2graph_def:
  v2graph v = MAP v2vertex (v2list v)
End

(* ------------------- Main functions --------------------- *)

Definition encode_to_output_def:
  encode_to_output v =
  let colors = v2colorList (head v) in
    let graph = v2graph (head (tail v)) in
      case graph_ok graph of
      | F => (List [strlit "Invalid input"])
      | T =>
          let cnf = t_graphColoring_to_cnf colors graph in
            let (max_var, clauses) = get_max_var_and_clauses cnf in
              Append
              (List [strlit "p cnf ";
                     num_to_str max_var; strlit " ";
                     num_to_str clauses; strlit "\n"])
              (cnf_to_output cnf)
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

Definition neighbours_to_output_inner_def:
  neighbours_to_output_inner [] = List [] ∧
  neighbours_to_output_inner (n::[]) = List [num_to_str n] ∧
  neighbours_to_output_inner (n::neighbours) =
  Append (List [num_to_str n; strlit ", "]) (neighbours_to_output_inner neighbours)
End

Definition neighbours_to_output_def:
  neighbours_to_output neighbours =
  Append (Append
          (List [strlit "["])
          (neighbours_to_output_inner neighbours))
         (List [strlit "]"])
End

Definition vertex_to_output_def:
  vertex_to_output w' vertex neighbours =
  Append (Append
          (List [strlit "["; num_to_str vertex; strlit ", "])
          (neighbours_to_output neighbours))
         (List [strlit ", "; implode (w' vertex); strlit "]"])
End

Definition graph_to_output_inner_def:
  graph_to_output_inner w' [] = List [] ∧
  graph_to_output_inner w' ((vertex, neighbours)::[]) =
  vertex_to_output w' vertex neighbours ∧
  graph_to_output_inner w' ((vertex, neighbours)::graph) =
  Append (Append
          (vertex_to_output w' vertex neighbours)
          (List [strlit ",\n"]))
         (graph_to_output_inner w' graph)
End

Definition graph_to_output_def:
  graph_to_output w' graph =
  Append (Append
          (List [strlit "["])
          (graph_to_output_inner w' graph))
         (List [strlit "]"])
End

Definition solve_to_output_def:
  solve_to_output v sat =
  let colors = v2colorList (head v) in
    let graph = v2graph (head (tail v)) in
      let w = sat_to_assignment (v2list sat) in
        let w' = assignment_to_vertexColorAssognment w colors graph in
          graph_to_output w' graph
End

Definition main_function_def:
  main_function (s:mlstring) =
  let v = from_str (explode s) in
    case v of
    | (Pair _ (Pair (Pair (Num 7561588) _) _)) =>
        solve_to_output (head v) (tail (head (tail v)))
    | _ => encode_to_output v
End

val res = translate name_def;
val res = translate head_def;
val res = translate tail_def;
val res = translate v2num_def;
val res = translate isNum_def;
val res = translate v2list_def;
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
val res = translate literal_to_output_def;
val res = translate clause_to_output_def;
val res = translate cnf_to_output_def;
val res = translate get_max_var_def;
val res = translate get_max_var_and_clauses_def;

val res = translate v2color_def;
val res = translate v2colorList_def;
val res = translate v2vertex_def;
val res = translate v2graph_def;
val res = translate encode_to_output_def;
val res = translate sat_to_assignment_inner_def;
val res = translate sat_to_assignment_def;
val res = translate neighbours_to_output_inner_def;
val res = translate neighbours_to_output_def;
val res = translate vertex_to_output_def;
val res = translate graph_to_output_inner_def;
val res = translate graph_to_output_def;
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

Definition graphColoring_encoder_prog_def:
  graphColoring_encoder_prog = ^prog
End

val _ = export_theory();

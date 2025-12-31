(*
  Encoding program for the graph coloring problem
*)
Theory graphColoringEncoderProg
Ancestors
  misc set_sep list cnf boolExpToCnf quantifierExp
  orderEncodingBool numBoolExp numBoolExtended numBoolRange
  unorderedSets graphColoring
  (* for parsing: *) parsing source_values
  toCnfHelper sat_encodersProg
Libs
  preamble basis

val _ = translation_extends "sat_encodersProg";

val _ = show_assums := true;

(* Graph coloring *)
val res = translate vertex_to_equation_def;
val res = translate graphColoring_to_equation_def;
val res = translate colorList_to_setList_def;
val res = translate graphColoring_to_cnf_def;
val res = translate assignment_to_vertexColorAssignment_def;
val res = translate graph_ok_def;


(* ------------------------- v to colorList --------------------------- *)

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
          let cnf = graphColoring_to_cnf colors graph in
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

val res = translate literal_to_output_def;
val res = translate clause_to_output_def;
val res = translate cnf_to_output_def;
val res = translate get_max_var_def;
val res = translate get_max_var_and_clauses_def;

val res = translate v2color_def;
val res = translate v2colorList_def;
val res = translate v2num_def;
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

Definition graphColoring_encoder_prog_def:
  graphColoring_encoder_prog = ^prog
End

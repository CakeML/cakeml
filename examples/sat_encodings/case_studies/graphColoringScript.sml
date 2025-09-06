(*
  Encoding of graph coloring problem
*)
Theory graphColoring
Ancestors
  misc unorderedSets
Libs
  preamble


(* --------------------- Types ---------------------- *)

Type vertex = “:num”;
Type graph = “:(vertex # (vertex list)) list”;
Type color = “:string”;
Type colorList = “:color list”;
Type vertexColorAssignment = “:vertex -> color”;


(* -------------------- Well-formed ------------------- *)

Definition graph_ok_def:
  graph_ok graph =
  ALL_DISTINCT (MAP FST graph)
End


(* ----------------- Evaluation ---------------------- *)

Definition eval_vertex_def:
  eval_vertex (w':vertexColorAssignment) ((vertex:vertex), []) = T ∧
  eval_vertex w' (vertex, ((neighbour:vertex)::neighbours)) =
  ((w' vertex ≠ w' neighbour) ∧
  eval_vertex w' (vertex, neighbours))
End

Definition eval_graphColoring_def:
  eval_graphColoring (w': vertexColorAssignment) [] = T ∧
  eval_graphColoring  w' ((vertexInfo::restOfGraph):graph) =
  (eval_vertex w' vertexInfo ∧
   eval_graphColoring w' restOfGraph)
End


(* ----------------- Encoding ----------------------- *)

Definition vertex_to_equation_def:
  vertex_to_equation (vertex:vertex, []) = EqTrue ∧
  vertex_to_equation (vertex, (neighbour::neighbours)) =
  EqAnd
  (EqNot (EqVarVar (vertex, "colors") (neighbour, "colors")))
  (vertex_to_equation (vertex, neighbours))
End

Definition graphColoring_to_equation_def:
  graphColoring_to_equation [] = EqTrue ∧
  graphColoring_to_equation (vertexInfo::graph) =
  EqAnd (vertex_to_equation vertexInfo) (graphColoring_to_equation graph)
End

Definition colorList_to_setList_def:
  colorList_to_setList (colors:colorList) =
  [("colors", colors)]
End

Definition graphColoring_to_cnf_def:
  graphColoring_to_cnf (colors:colorList) graph =
  equation_to_cnf
  (colorList_to_setList colors)
  (graphColoring_to_equation graph)
End

Definition assignment_to_vertexColorAssignment_def:
  assignment_to_vertexColorAssognment w (colors:colorList) graph =
  assignment_to_elementVarAssignment
  w (colorList_to_setList colors) (graphColoring_to_equation graph)
End



(*
  Encoding of Hamiltonian path problem
*)
Theory hamiltonianpath
Ancestors
  misc boolExpToCnf quantifierExp cnf
Libs
  preamble


(* ---------------- Types ------------------- *)

Type graph = “:((num list) list)”


(* ----------------- Evaluation -------------- *)

Definition eval_vertex_def:
  eval_vertex (w:assignment) [] = F ∧
  eval_vertex w (edges:num list) =
  let nr_traversed_edges = sum_bools (MAP w edges) in
      (nr_traversed_edges ≤ 2 ∧ 1 ≤ nr_traversed_edges)
End

Definition eval_hamiltonian_graph_def:
  eval_hamiltonian_graph (w:assignment) (graph:graph) =
  EVERY (λ vertex_edge_list. eval_vertex w vertex_edge_list) graph
End


(* --------------- Encoding ----------------- *)

Definition edge_list_to_pseudoBool_list_def:
  edge_list_to_pseudoBool_list edgeList =
  MAP (λ edge.  PLit (INL edge)) edgeList
End

Definition vertex_to_pseudoBool_def:
  vertex_to_pseudoBool [] = PFalse ∧
  vertex_to_pseudoBool [(edge: num)] = PTrue ∧
  vertex_to_pseudoBool ((edge::vertex_edge_list):num list) =
  PAnd (PImpl (PLit (INL edge))
        (PMostOne (MAP (λ y. PLit (INL y)) vertex_edge_list)))
       (vertex_to_pseudoBool vertex_edge_list)
End

Definition hamiltonian_to_pseudoBool_inner_def:
  hamiltonian_to_pseudoBool_inner [] = PTrue ∧
  hamiltonian_to_pseudoBool_inner (x::xs) =
  PAnd x (hamiltonian_to_pseudoBool_inner xs)
End

Definition hamiltonian_to_pseudoBool_def:
  hamiltonian_to_pseudoBool (graph:graph) =
  hamiltonian_to_pseudoBool_inner
  (MAP (λ vertex_edge_list.
          (PAnd (vertex_to_pseudoBool vertex_edge_list)
           (PLeastOne (MAP (λ y. PLit (INL y))
                       vertex_edge_list)))) graph)
End


(* ------------------ Theorems ------------------------ *)

Theorem sum_bools_least_one:
  ∀ h h' w.
  1 ≤ sum_bools (w h'::MAP w h) ⇔
    sum_bools
    (w h'::MAP (eval_pseudoBool w)
     (MAP (λy. PLit (INL y)) h)) ≥ 1
Proof
  Induct
  >> rw[sum_bools_def]
  >> gvs[eval_pseudoBool_def, eval_literal_def]
  >> Cases_on‘w h''’ >> gvs[sum_bools_def]
QED

Theorem sum_bools_map:
  ∀ h w.
    sum_bools
    (MAP (λa. eval_pseudoBool w a)
     (MAP (λy. PLit (INL y)) h)) =
    sum_bools (MAP w h)
Proof
  Induct
  >> gvs[sum_bools_def, eval_pseudoBool_def, eval_literal_def]
  >> rw[]
  >> Cases_on‘w h'’ >> gvs[sum_bools_def]
QED

Theorem sum_bools_vertex:
  ∀ h h' w.
    sum_bools (w h'::MAP w h) ≤ 2 ⇔
      eval_pseudoBool w (vertex_to_pseudoBool (h'::h))
Proof
  Induct
  >> rw[sum_bools_def, vertex_to_pseudoBool_def,
        eval_pseudoBool_def, eval_literal_def]
  >- (Cases_on ‘w h'’ >> gvs[sum_bools_def])
  >> last_x_assum (qspecl_then [‘h'’, ‘w’] assume_tac)
  >> Cases_on‘w h''’
  >> Cases_on‘w h'’
  >> gvs[sum_bools_map, sum_bools_def, vertex_to_pseudoBool_def]
  >> Cases_on‘sum_bools (MAP w h) = 0’ >> gvs[]
  >> Cases_on‘sum_bools (MAP w h) = 1’ >> gvs[]
QED

Theorem hamiltonian_to_pseudoBool_preserves_sat:
  ∀ graph w.
    eval_hamiltonian_graph w graph ⇔
      eval_pseudoBool w (hamiltonian_to_pseudoBool graph)
Proof
  Induct
  >> gvs[eval_hamiltonian_graph_def, hamiltonian_to_pseudoBool_def,
         hamiltonian_to_pseudoBool_inner_def,
         eval_pseudoBool_def, eval_vertex_def]
  >> rw[]
  >> last_x_assum (qspecl_then [‘w’] assume_tac)
  >> Cases_on ‘eval_pseudoBool
               w (hamiltonian_to_pseudoBool_inner
                  (MAP
                   (λ vertex_edge_list.
                      PAnd (vertex_to_pseudoBool vertex_edge_list)
                           (PLeastOne (MAP (λy. PLit (INL y))
                                       vertex_edge_list)))
                   graph))’ >> gvs[]
  >> Induct_on‘h’ >> gvs[eval_vertex_def, vertex_to_pseudoBool_def,
                         eval_pseudoBool_def, sum_bools_def, eval_literal_def]
  >> metis_tac[sum_bools_vertex, sum_bools_least_one]
QED


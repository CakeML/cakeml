(*
  Basic graph notions
*)
open preamble;

val _ = new_theory "graph_basic";

(* Graph: (V : num , E : (num list) num_map)
  V number of vertices
  E edge list representation *)

Type graph = ``:num # (num list) num_map``;

(* Edge from a -> b in edge list representation e *)
Definition is_edge_def:
  is_edge e a b ⇔
  case lookup a e of SOME ns => MEM b ns | _ => F
End

Theorem is_edge_thm:
  is_edge e a b ⇔
  ∃ns. lookup a e = SOME ns ∧ MEM b ns
Proof
  rw[is_edge_def]>>every_case_tac>>fs[]
QED

(* A "good" graph is undirected and only mentions edges < v *)
Definition good_graph_def:
  good_graph ((v,e):graph) ⇔
  ∀a ns.
    lookup a e = SOME ns ⇒ a < v ∧
    ∀b. is_edge e a b ⇒ is_edge e b a
End

Definition neighbours_def:
  neighbours e v =
  case lookup v e of NONE => [] | SOME ns => ns
End

Theorem MEM_neighbours:
  MEM b (neighbours ep a) ⇔
  is_edge ep a b
Proof
  rw[neighbours_def,is_edge_thm]>>
  every_case_tac>>fs[]
QED

Definition not_neighbours_def:
  not_neighbours (v,e) a =
  let n = neighbours e a in
  FILTER (λu. ¬ MEM u n) (COUNT_LIST v)
End

Theorem MEM_not_neighbours:
  MEM b (not_neighbours (vp,ep) a) ⇔
  b < vp ∧
  ¬is_edge ep a b
Proof
  rw[not_neighbours_def,MEM_FILTER,is_edge_thm,neighbours_def]>>
  every_case_tac>>fs[MEM_COUNT_LIST]>>
  metis_tac[]
QED

val _ = export_theory();

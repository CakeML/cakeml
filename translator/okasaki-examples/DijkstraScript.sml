(*
  Example of using bootstrapped skew binomial queues to implement Djikstra's
  algorithm.
*)

open preamble;
open SkewBinomialHeapTheory;

val _ = new_theory "Djikstra";

Datatype `vertex = Vertex 'a (('a # num) list)`;

EVAL ``Vertex #"a" [(#"b", 1); (#"c", 4)]``;

val _ = type_abbrev("graph", ``:'a vertex list``);

(*
  A small library for graphs
*)

(* Add an edge from s to d with weight w in graph g *)
val add_edge_def = Define `
  (add_edge [] s d w = [(s, [d, w])]) /\
  (add_edge ((l,ns)::vs) s d w =
     if l = s
     then (l, ((d, w)::ns))::vs
     else (l, ns)::(add_edge vs s d w))
`;

(* Add several edges to a graph *)
val add_edges_def = Define `
  (add_edges g [] = g) /\
  (add_edges g ((s,d,w)::es) = add_edges (add_edge g s d w) es)
`;

(* Get a graph from a list of edges (triples source, destination and weight) *)
val graph_from_edges_def = Define `
  graph_from_edges es = add_edges [] es
`;

(* Get the adjacent vertices for a vertex *)
val get_adjacents_def = Define `
  get_adjacents l ((Vertex l' ns)::vs) =
    if l = l'
    then ns
    else get_adjacents l vs
`;

(*
  A small library for elements associated with a priority. This priority is
  either a numeral, or a special value Infinity which is greater than all
  numerals.
*)
Datatype `infiNum = Inf | Num num`;

(* Addition over infiNums *)
val add_inf_def = Define `
  (add_inf Inf _ = Inf) /\
  (add_inf _ Inf = Inf) /\
  (add_inf (Num x) (Num y) = Num (x+y))
`;

(* Order on infiNums *)
val geq_inf_def = Define `
  (geq_inf _ Inf = F) /\
  (geq_inf Inf _ = T) /\
  (geq_inf (Num x) (Num y) = (x >= y))
`;

Datatype `elemPrio = ElemPrio 'a infiNum`;

(* Order on prioritized elements *)
val geq_def = Define `
  (geq (ElemPrio _ Inf) (ElemPrio _ Inf) = T) /\
  (geq (ElemPrio _ Inf) (ElemPrio _ (Num _)) = T) /\
  (geq (ElemPrio _ (Num _)) (ElemPrio _ Inf) = F) /\
  (geq (ElemPrio _ (Num x)) (ElemPrio _ (Num y)) = (x >= y))
`;

Theorem geq_total_preorder:
  TotalPreOrder geq
Proof
  rw[TotalPreOrder_def, PreOrder, reflexive_def, total_def, transitive_def]
  >- (Cases_on `x` \\
      Cases_on `i` \\
      rw[geq_def])
  >- (Cases_on `x` \\
      Cases_on `y` \\
      Cases_on `z` \\
      Cases_on `i` \\
      Cases_on `i'` \\
      Cases_on `i''` \\
      fs[geq_def])
  >- (Cases_on `x` \\
      Cases_on `y` \\
      Cases_on `i` \\
      Cases_on `i'` \\
      rw[geq_def])
QED;

(* Implementation of Djikstra using priority queues *)

(* Initial distance between the source and the other vertices *)
val initial_distances_def = Define `
  (initial_distances s [] = []) /\
  (initial_distances s ((Vertex l _)::vs) =
    (l, (if s = l then (Num 0) else Inf))::(initial_distances s vs))
`;

(* get the distance to the source of a vertice with a given label *)
val get_distance_def = Define `
  (get_distance [] _ = NONE) /\
  (get_distance ((vLabel, vDist)::dists) label =
    if vLabel = label
    then SOME vDist
    else get_distance dists label)
`;

(*
update_distances will take the current distances, the distance to a node and
a list of adjacent nodes and will return a list of updated nodes and the new
distances.
*)
val update_distances_def = Define `
  (update_distances dists weight [] = ([], dists)) /\
  (update_distances dists weight ((adj, distAdj)::adjs) =
    let new_dist = add_inf weight (Num distAdj)
    and old_dist = THE (get_distance dists adj)
    and dist_without_adj = FILTER (\ (l,_). l <> adj) dists in
    let (updated_rest, updated_dists_rest) =
          (update_distances dist_without_adj weight adjs)
    in
      if geq_inf old_dist new_dist
      then ((ElemPrio adj new_dist)::updated_rest, (adj, new_dist)::updated_dists_rest)
      else (updated_rest, (adj, old_dist)::updated_dists_rest))
`;

(*
 Djikstra's algorithm itself
*)
val dijkstra_step_defn = Hol_defn "dijkstra_step" `
  dijkstra_step g dists queue =
    if b_is_empty queue
    then dists
    else
      (case (THE (b_find_min queue)) of
       (ElemPrio (label_min:'a) (dist_min: infiNum)) =>
       let queue = THE (b_delete_min geq queue) in
       let adj_vertices = get_adjacents label_min g in
       let (updated_vertices, new_distances) =
         update_distances dists dist_min adj_vertices in
       dijkstra_step g new_distances
                     (b_insert_list geq updated_vertices queue))
`;

(* Termination of dijkstra step *)
Defn.tgoal dijkstra_step_defn;

val (dijkstra_step_def, dijkstra_step_ind) =
  Defn.tprove (dijkstra_step_defn,
	       cheat)
;

val dijkstra_def = Define `
  dijkstra source graph =
    dijkstra_step graph (initial_distances source graph)
                  (b_insert geq (ElemPrio source (Num 0)) Bsbempty)
`;

open ml_translatorTheory ml_translatorLib;

val _ = translation_extends "SkewBinomialHeap";

val _ = translate geq_def;
val _ = translate geq_inf_def;
val _ = translate get_adjacents_def;
val _ = translate add_inf_def;
val _ = translate get_distance_def;
val _ = translate update_distances_def;
val _ = translate dijkstra_step_def;
val _ = translate dijkstra_def;

(*
  Example of using bootstrapped skew binomial queues to implement Djikstra's
  algorithm.
*)
open preamble SkewBinomialHeapTheory sptreeTheory comparisonTheory;
(* open balanced_mapTheory;
   open mlmapTheory;
   open MapProgTheory; *)

val _ = new_theory "Djikstra";

Datatype `vertex = Vertex 'a (('a # num) list)`;

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
val ep_geq_def = Define `
  (ep_geq (ElemPrio _ Inf) (ElemPrio _ Inf) = T) /\
  (ep_geq (ElemPrio _ Inf) (ElemPrio _ (Num _)) = T) /\
  (ep_geq (ElemPrio _ (Num _)) (ElemPrio _ Inf) = F) /\
  (ep_geq (ElemPrio _ (Num x)) (ElemPrio _ (Num y)) = (x >= y))
`;
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
      then ((ElemPrio adj new_dist)::updated_rest,
	    (adj, new_dist)::updated_dists_rest)
      else (updated_rest, (adj, old_dist)::updated_dists_rest))
`;

val fromNodeList_def = Define `
  (fromNodeList [] = LN) /\
  (fromNodeList (v::vs) = insert v () (fromNodeList vs))
`;

(* set containing all the nodes of the graph *)
val spt_nodes_def = Define `
  (spt_nodes [] = LN) /\
  (spt_nodes ((Vertex l adjs)::vs) =
    sptree$insert l () (sptree$union
      (spt_nodes vs)
      (fromNodeList (MAP FST adjs))))
`;

(*
 Djikstra's algorithm itself
*)
val dijkstra_step_defn = Hol_defn "dijkstra_step" `
  dijkstra_step cmp (g:num vertex list) dists queue decided =
    if (subspt decided (spt_nodes g)) /\
       (is_b_heap_ordered cmp queue) /\
       (TotalPreOrder cmp)
    then
    if b_is_empty queue
    then dists
    else
      (case (THE (b_find_min queue)) of
       (ElemPrio (label_min:num) (dist_min: infiNum)) =>
       let queue = THE (b_delete_min cmp queue) in
       let current_distance = THE (get_distance dists label_min) in
       if ~(IS_SOME (sptree$lookup label_min decided )) /\
          IS_SOME (sptree$lookup label_min (spt_nodes g))
       then
         let adj_vertices = get_adjacents label_min g in
         let (updated_vertices, new_distances) =
	      update_distances dists dist_min adj_vertices in
	   dijkstra_step cmp
                         g
                         new_distances
                         (b_insert_list cmp updated_vertices queue)
                         (sptree$insert label_min () decided)
       else
         dijkstra_step cmp g dists queue decided)
    else ARB
`;

(*
Termination of dijkstra step
*)

(* Defn.tgoal dijkstra_step_defn; *)
val (dijkstra_step_def, dijkstra_step_ind) =
  Defn.tprove (dijkstra_step_defn,
    WF_REL_TAC `inv_image ($< LEX $<) (\(cmp,graph,dists,queue,decided).
     ( ((size (spt_nodes graph)) - (size decided)),
      bsize queue))` \\ rw[]
    >- (DISJ1_TAC \\ CONJ_TAC
        >- (fs[sptreeTheory.size_insert] \\
            Cases_on `label_min IN (domain decided)` \\ fs[] \\
            imp_res_tac lookup_NONE_domain)
	>- (imp_res_tac subspt_domain \\
            `size (spt_nodes g) = CARD (domain (spt_nodes g))` by
            metis_tac[size_domain] \\
            `size decided = CARD (domain decided)` by
            metis_tac[size_domain] \\
            `FINITE (domain (spt_nodes g))` by metis_tac[FINITE_domain] \\
            sg `(domain decided) PSUBSET (domain (spt_nodes g))`
            >- (fs[IS_SOME_DEF] \\
                `label_min NOTIN (domain decided)` by
		metis_tac[lookup_NONE_domain] \\
                `?x. lookup label_min (spt_nodes g) = SOME x` by
                metis_tac[IS_SOME_EXISTS] \\
	        metis_tac[PSUBSET_MEMBER, domain_lookup])
	    >- (imp_res_tac CARD_PSUBSET \\
                fs[]))) \\
    (Cases_on `queue`
     >- fs[b_is_empty_def]
     >- (imp_res_tac b_delete_size \\ fs[]))
);

val dijkstra_def = Define `
  dijkstra source graph =
    dijkstra_step ep_geq
                  graph
                  (initial_distances source graph)
                  (b_insert ep_geq (ElemPrio source (Num 0)) Bsbempty)
                  LN
`;

open ml_translatorTheory ml_translatorLib;

val _ = translation_extends "SkewBinomialHeap";

val _ = translate ep_geq_def;
val _ = translate geq_inf_def;
val _ = translate get_adjacents_def;
val _ = translate add_inf_def;
val _ = translate get_distance_def;
val _ = translate update_distances_def;
val _ = translate dijkstra_step_def;
val _ = translate dijkstra_def;

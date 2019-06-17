(*
  Example of using bootstrapped skew binomial queues to implement Djikstra's
  algorithm.
*)

open preamble;
open SkewBinomialHeapTheory;
open balanced_mapTheory;
open mlmapTheory;
open MapProgTheory;
open comparisonTheory;

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
      then ((ElemPrio adj new_dist)::updated_rest,
	    (adj, new_dist)::updated_dists_rest)
      else (updated_rest, (adj, old_dist)::updated_dists_rest))
`;

(*
 Djikstra's algorithm itself
*)
val dijkstra_step_defn = Hol_defn "dijkstra_step" `
  dijkstra_step g dists queue decided =
    if b_is_empty queue
    then dists
    else
      (case (THE (b_find_min queue)) of
       (ElemPrio (label_min:'a) (dist_min: infiNum)) =>
       let queue = THE (b_delete_min geq queue) in
       let current_distance = THE (get_distance dists label_min) in
       if (IS_SOME (lookup decided label_min)) then
         let adj_vertices = get_adjacents label_min g in
         let (updated_vertices, new_distances) =
	      update_distances dists dist_min adj_vertices in
	   dijkstra_step g
                         new_distances
                         (b_insert_list geq updated_vertices queue)
                         (insert decided label_min T)
       else
         dijkstra_step g dists queue decided)
`;

(*
Termination of dijkstra step
*)

(* size of a map *)
(* val map_size_def = Define ` *)
(*   (map_size s = foldrWithKey (\_ _ x. x+1) (0:num) s) *)
(* `; *)

(* Take one key from the map (not specified which one)*)
val one_key_def = Define `
  (one_key Tip = NONE) /\
  (one_key (Bin _ k v _ _) = SOME k)
`;

val map_diff_defn = Hol_defn "map_diff" `
  (map_diff cmp s1 s2 =
    if (good_cmp cmp) /\ (invariant cmp s1) /\ (invariant cmp s2)
    then
      (if (balanced_map$null s2) \/ (balanced_map$null s1)
       then s1
       else (let k = THE (one_key s1) in
         if (IS_SOME (balanced_map$lookup cmp k s2))
         then map_diff cmp (balanced_map$delete cmp k s1) s2
         else balanced_map$insert cmp k T
              (map_diff cmp (balanced_map$delete cmp k s1) s2)))
    else ARB)
`;

val map_size_def = Define `
  (map_size (Map cmp t) = structure_size t)
`;

Theorem almost_balancedL_aux:
  !cmp n k v n' k' v' b1 b2.
    (good_cmp cmp) /\
    (invariant cmp (Bin n k v Tip (Bin n' k' v' b1 b2))) /\
    almost_balancedL (size (Bin n k v Tip (Bin n' k' v' b1 b2)))
                     (size Tip) ==>
    (b1 = Tip) /\ (b2 = Tip)
Proof
  rpt gen_tac \\
  Cases_on `b1`
  >- (Cases_on `b2`
      >- rw[]
      >- (rw[almost_balancedL_def] \\
	  (DISJ2_TAC \\ DISJ1_TAC \\
           disch_tac \\
           fs[invariant_def, structure_size_def, size_def, balanced_def])))
  >- (Cases_on `b2` \\
      (rw[almost_balancedL_def] \\
	  (DISJ2_TAC \\ DISJ1_TAC \\
           disch_tac \\
           fs[invariant_def, structure_size_def, size_def, balanced_def])))
QED;

Theorem almost_balancedR_aux:
  !cmp n k v n' k' v' b1 b2.
    (good_cmp cmp) /\
    (invariant cmp (Bin n k v (Bin n' k' v' b1 b2) Tip)) /\
    almost_balancedR (size Tip)
                     (size (Bin n k v (Bin n' k' v' b1 b2) Tip)) ==>
    (b1 = Tip) /\ (b2 = Tip)
Proof
  rpt gen_tac \\
  Cases_on `b1`
  >- (Cases_on `b2`
      >- rw[]
      >- (rw[almost_balancedR_def] \\
          DISJ2_TAC \\ DISJ1_TAC \\
          disch_tac \\
          fs[invariant_def, structure_size_def, size_def, balanced_def]))
  >- (Cases_on `b2` \\
      (rw[almost_balancedL_def] \\
	  (DISJ2_TAC \\ DISJ1_TAC \\
           disch_tac \\
           fs[invariant_def, structure_size_def, size_def, balanced_def])))
QED;

Theorem size_bin_lower_bound:
  !cmp n k v b1 b2. (good_cmp cmp) /\
                    (invariant cmp (Bin n k v b1 b2)) ==>
                    size (Bin n k v b1 b2) >= 1
Proof
  rw[size_def, invariant_def]
QED;

Theorem structure_size_thm:
  !cmp t. invariant cmp t ==> size t = structure_size t
Proof
  Cases_on `t` \\
  rw[invariant_def, size_def, structure_size_def]
QED;

Theorem balanceL_size:
  !cmp k v l r. good_cmp cmp /\
                invariant cmp l /\
                invariant cmp r /\
                almost_balancedL (size l) (size r) ==>
                structure_size (balanceL k v l r) =
                1 + structure_size l + structure_size r
Proof
  Cases_on `l`
  >- (Cases_on `r`
      >- rw[balanceL_def, structure_size_def]
      >- rw[balanceL_def, structure_size_def])
  >- (Cases_on `r`
      >- (Cases_on `b`
          >- (Cases_on `b0`
              >- rw[balanceL_def, structure_size_def]
              >- (rw[balanceL_def, structure_size_def] \\
                 (* We prove that b and b0 must be Tip because l and r
                    are almost balancedL *)
                 imp_res_tac almost_balancedL_aux \\
		 rfs[structure_size_def]))
          >- (Cases_on `b0`
              >- rw[balanceL_def, structure_size_def]
              >- rw[balanceL_def, structure_size_def]))
      >- (rw[balanceL_def, almost_balancedL_def]
	  >- (imp_res_tac size_bin_lower_bound \\
              decide_tac)
          >- (fs[balanced_def] \\
              imp_res_tac size_bin_lower_bound
              >- decide_tac
	      >- fs[size_def])
	  >- (imp_res_tac size_bin_lower_bound \\
              decide_tac)
	  >- (fs[balanced_def] \\
              imp_res_tac size_bin_lower_bound
              >- decide_tac
              >- fs[size_def, delta_def, structure_size_def])
          >- (imp_res_tac size_bin_lower_bound \\
              decide_tac)
          >- (imp_res_tac size_bin_lower_bound \\
              decide_tac)
	  >- (fs[size_def,delta_def] \\
              Cases_on `b`
              >- (rw[structure_size_def] \\
                  fs[invariant_def, structure_size_def, balanced_def,
		     size_def] \\
		  imp_res_tac structure_size_thm \\
                  fs[])
	      >- (rw[structure_size_def] \\
                  Cases_on `b0`
                  >- (rw[structure_size_def] \\
		      fs[invariant_def, structure_size_def, balanced_def,
			 size_def])
                  >- rw[structure_size_def]))
          >- fs[size_def, delta_def]
          >- (fs[size_def, delta_def] \\
              Cases_on `b`
              >- (rw[structure_size_def] \\
                  fs[invariant_def, structure_size_def, balanced_def,
		     size_def] \\
		  imp_res_tac structure_size_thm \\
                  fs[])
              >- (rw[structure_size_def] \\
                  Cases_on `b0`
                  >- (rw[structure_size_def] \\
                      fs[invariant_def, structure_size_def, balanced_def,
			 size_def])
                  >- rw[structure_size_def]))
          >- fs[size_def, delta_def]))
QED;

Theorem balanceR_size:
  !cmp k v l r. good_cmp cmp /\
                invariant cmp l /\
                invariant cmp r /\
                almost_balancedR (size l) (size r) ==>
                structure_size (balanceR k v l r) =
                1 + structure_size l + structure_size r
Proof
  Cases_on `l`
  >- (Cases_on `r`
      >- rw[balanceR_def, structure_size_def]
      >- (Cases_on `b`
          >- (Cases_on `b0`
              >- rw[balanceR_def, structure_size_def]
	      >- rw[balanceR_def, structure_size_def])
          >- (Cases_on `b0`
              >- (rw[balanceR_def, structure_size_def] \\
                  imp_res_tac almost_balancedR_aux \\
		  rfs[structure_size_def])
              >- rw[balanceR_def, structure_size_def])))
  >- (Cases_on `r`
      >- rw[balanceR_def, structure_size_def]
      >- (rw[balanceR_def, almost_balancedR_def]
          >- (imp_res_tac size_bin_lower_bound \\
              decide_tac)
	  >- (fs[balanced_def] \\
              imp_res_tac size_bin_lower_bound
              >- decide_tac
	      >- fs[size_def])
	  >- (imp_res_tac size_bin_lower_bound \\
              decide_tac)
	  >- (fs[balanced_def] \\
              imp_res_tac size_bin_lower_bound
              >- decide_tac
              >- fs[size_def, delta_def, structure_size_def])
          >- (imp_res_tac size_bin_lower_bound \\
              decide_tac)
          >- (imp_res_tac size_bin_lower_bound \\
              decide_tac)
	  >- (fs[size_def,delta_def] \\
              Cases_on `b'`
              >- (rw[structure_size_def] \\
                  fs[invariant_def, structure_size_def, balanced_def,
		     size_def] \\
		  imp_res_tac structure_size_thm \\
                  fs[])
	      >- (rw[structure_size_def] \\
                  Cases_on `b0'`
                  >- (rw[structure_size_def] \\
		      fs[invariant_def, structure_size_def, balanced_def,
			 size_def])
                  >- rw[structure_size_def]))
          >- fs[size_def, delta_def]
          >- (fs[size_def, delta_def] \\
              Cases_on `b'`
              >- (rw[structure_size_def] \\
                  fs[invariant_def, structure_size_def, balanced_def,
		     size_def] \\
		  imp_res_tac structure_size_thm \\
                  fs[])
              >- (rw[structure_size_def] \\
                  Cases_on `b0'`
                  >- (rw[structure_size_def] \\
                      fs[invariant_def, structure_size_def, balanced_def,
			 size_def])
                  >- rw[structure_size_def]))
          >- fs[size_def, delta_def]))
QED;

Theorem balanced_is_almostBalancedL:
  !b1 b2. balanced (size b1) (size b2) ==> almost_balancedL (size b1) (size b2)
Proof
  rw[balanced_def, almost_balancedL_def, delta_def, size_def]
  >- (DISJ2_TAC \\ decide_tac)
  >- (DISJ2_TAC \\
      Cases_on `(size b1) < 1`
      >- fs[]
      >- fs[MIN_DEF])
  >- (DISJ1_TAC \\
      Cases_on `(size b1) < (size b2)` \\
      fs[MIN_DEF])
QED;

Theorem balanced_is_almostBalancedR:
  !b1 b2. balanced (size b1) (size b2) ==> almost_balancedR (size b1) (size b2)
Proof
  rw[balanced_def, almost_balancedR_def, delta_def, size_def]
  >- (DISJ2_TAC \\ decide_tac)
  >- (DISJ2_TAC \\
      Cases_on `(size b1) < 1`
      >- fs[]
      >- fs[MIN_DEF])
  >- (DISJ1_TAC \\
      Cases_on `(size b1) < (size b2)` \\
      fs[MIN_DEF])
QED;


Theorem balanced_sym:
  !b1 b2. balanced (size b1) (size b2) ==> balanced (size b2) (size b1)
Proof
  rw[balanced_def]
  >- (DISJ1_TAC \\ decide_tac)
  >- (DISJ2_TAC \\
      Cases_on `(size b2) < (size b1)` \\
      fs[MIN_DEF, delta_def])
QED;

Theorem deleteFindMax_size:
  !f km m b l. (good_cmp f) /\
               ~(balanced_map$null b) /\
               (invariant f b) /\
               (deleteFindMax b = ((km,m), l)) ==>
               structure_size b = (structure_size l) + 1
Proof
  ntac 3 strip_tac \\
  recInduct deleteFindMax_ind \\
  rpt strip_tac
  >- fs[deleteFindMax_def, structure_size_def]
  >- (fs[deleteFindMax_def] \\
      `~null (Bin v5 v6 v7 v8 v9)` by rw[balanced_mapTheory.null_def] \\
      `invariant f (Bin v5 v6 v7 v8 v9)` by fs[invariant_def] \\
      Cases_on `deleteFindMax (Bin v5 v6 v7 v8 v9)` \\
      Cases_on `q` \\
      fs[] \\
      rw[structure_size_def] \\
      sg `almost_balancedL (size l) (size r)`
      >- (`invariant f (Bin v5 v6 v7 v8 v9)` by fs[invariant_def] \\
          `structure_size (Bin v5 v6 v7 v8 v9) = size (Bin v5 v6 v7 v8 v9)`
          by (imp_res_tac (GSYM structure_size_thm)) \\
	  `invariant f r` by (imp_res_tac deleteFindMax) \\
	  `structure_size r = size r`
          by (imp_res_tac (GSYM structure_size_thm)) \\
	  fs[size_def] \\
	  fs[almost_balancedL_def] \\
          rw[balanced_def, delta_def]
	  >- (DISJ1_TAC \\ rw[])
	  >- (fs[invariant_def, balanced_def, size_def, structure_size_def,
		 delta_def] \\
              Cases_on `(size l) < (size r + 1)` \\
              fs[MIN_DEF])
          >- (fs[invariant_def, balanced_def, size_def] \\
              Cases_on `(size l) < 1` \\
              rw[] \\
	      fs[MIN_DEF, delta_def])
          >- (fs[invariant_def, balanced_def, size_def, structure_size_def,
		 delta_def] \\
              Cases_on `(size l) < 2` \\
              rw[] \\
              fs[MIN_DEF])
	  >- (fs[invariant_def, balanced_def, size_def, structure_size_def,
		delta_def] \\
              Cases_on `(size l) < (size r + 1)` \\
              fs[MIN_DEF, delta_def]))
      >- (`invariant f l` by fs[invariant_def] \\
          `invariant f r` by (imp_res_tac deleteFindMax) \\
	  sg `structure_size (balanceL k x l r) =
              1 + structure_size l + structure_size r`
          >- (imp_res_tac balanceL_size \\
	     first_x_assum (qspecl_then [`x`, `k`] assume_tac) \\
             rw[])
	  >- rw[]))
  >- fs[balanced_mapTheory.null_def]
QED;

Theorem deleteFindMin_size:
  !f km m b l. (good_cmp f) /\
               ~(balanced_map$null b) /\
               (invariant f b) /\
               (deleteFindMin b = ((km,m), l)) ==>
               structure_size b = (structure_size l) + 1
Proof
  ntac 3 strip_tac \\
  recInduct deleteFindMin_ind \\
  rpt strip_tac
  >- fs[deleteFindMin_def, structure_size_def]
  >- (fs[deleteFindMin_def] \\
      `~null (Bin v5 v6 v7 v8 v9)` by rw[balanced_mapTheory.null_def] \\
      `invariant f (Bin v5 v6 v7 v8 v9)` by fs[invariant_def] \\
      Cases_on `deleteFindMin (Bin v5 v6 v7 v8 v9)` \\
      Cases_on `q` \\
      fs[] \\
      rw[structure_size_def] \\
      sg `almost_balancedR (size r') (size r)`
      >- (`invariant f (Bin v5 v6 v7 v8 v9)` by fs[invariant_def] \\
          `structure_size (Bin v5 v6 v7 v8 v9) = size (Bin v5 v6 v7 v8 v9)`
          by (imp_res_tac (GSYM structure_size_thm)) \\
	  `invariant f r'` by (imp_res_tac deleteFindMin) \\
	  `structure_size r' = size r'`
          by (imp_res_tac (GSYM structure_size_thm)) \\
	  fs[size_def] \\
	  fs[almost_balancedR_def] \\
          rw[balanced_def, delta_def]
	  >- (DISJ1_TAC \\ rw[])
	  >- (fs[invariant_def, balanced_def, size_def, structure_size_def,
		 delta_def] \\
              Cases_on `(size r') < (size r + 1)` \\
              fs[MIN_DEF])
          >- (fs[invariant_def, balanced_def, size_def] \\
              Cases_on `(size r') < 1` \\
              rw[] \\
	      fs[MIN_DEF, delta_def])
          >- (fs[invariant_def, balanced_def, size_def, structure_size_def,
		 delta_def] \\
              Cases_on `(size r') < 2` \\
              rw[] \\
              fs[MIN_DEF])
	  >- (fs[invariant_def, balanced_def, size_def, structure_size_def,
		delta_def] \\
              Cases_on `(size r') < (size r + 1)` \\
              fs[MIN_DEF, delta_def]))
      >- (`invariant f r` by fs[invariant_def] \\
          `invariant f r'` by (imp_res_tac deleteFindMin) \\
	  sg `structure_size (balanceR k x r' r) =
              1 + structure_size r' + structure_size r`
          >- (imp_res_tac balanceR_size \\
	     first_x_assum (qspecl_then [`x`, `k`] assume_tac) \\
             rw[])
	  >- rw[]))
  >- fs[balanced_mapTheory.null_def]
QED;

Theorem glue_size:
  !f n k v b1 b2.
    (good_cmp f) /\
    (invariant f (Bin n k v b1 b2)) ==>
    structure_size (glue b1 b2) = structure_size b1 + structure_size b2
Proof
  Cases_on `b1`
  >- rw[glue_def,structure_size_def]
  >- (Cases_on `b2`
      >- rw[glue_def,structure_size_def]
      >- (rw[glue_def]
	  >- (Cases_on `deleteFindMax (Bin n k v b b0)` \\
              Cases_on `q` \\
              rw[] \\
              `invariant f (Bin n k v b b0)` by fs[invariant_def] \\
	      `~(null (Bin n k v b b0))` by rw[balanced_mapTheory.null_def] \\
              imp_res_tac deleteFindMax_size \\
              rpt (WEAKEN_TAC is_forall) \\
              `invariant f r` by (imp_res_tac deleteFindMax) \\
              sg `almost_balancedR (size r) (size (Bin n' k' v' b' b0'))`
              >- (rw[size_def] \\
                  `invariant f (Bin n k v b b0)` by fs[invariant_def] \\
		  `structure_size (Bin n k v b b0) = n`
                  by (imp_res_tac (GSYM structure_size_thm) \\ rw[size_def]) \\
		  `structure_size r = size r`
                  by (imp_res_tac (GSYM structure_size_thm)) \\
                  fs[size_def] \\
		  fs[almost_balancedR_def, invariant_def, balanced_def,
		     delta_def, structure_size_def, size_def] \\
                  rw[] \\
		  (Cases_on `(size r) <
                             (structure_size b' + (structure_size b0' + 1))`
                   >- fs[]
		   >- fs[MIN_DEF]))
	      >- (`invariant f (Bin n' k' v' b' b0')` by fs[invariant_def] \\
                  sg `structure_size (balanceR q' r' r (Bin n' k' v' b' b0')) =
                  1+(structure_size r)+(structure_size (Bin n' k' v' b' b0'))`
                  >- (imp_res_tac balanceR_size \\
                      first_x_assum (qspecl_then [`r'`, `q'`] assume_tac) \\
                      rw[])
		  >- rw[]))
	  >- (Cases_on `deleteFindMin (Bin n' k' v' b' b0')` \\
              Cases_on `q` \\
              rw[] \\
              `invariant f (Bin n' k' v' b' b0')` by fs[invariant_def] \\
	      `~(null (Bin n' k' v' b' b0'))` by rw[balanced_mapTheory.null_def] \\
              imp_res_tac deleteFindMin_size \\
              rpt (WEAKEN_TAC is_forall) \\
              `invariant f r` by (imp_res_tac deleteFindMin) \\
              sg `almost_balancedL (size (Bin n k v b b0)) (size r)`
              >- (rw[size_def] \\
                  `invariant f (Bin n k v b b0)` by fs[invariant_def] \\
		  `structure_size (Bin n k v b b0) = n`
                  by (imp_res_tac (GSYM structure_size_thm) \\ rw[size_def]) \\
		  `structure_size r = size r`
                  by (imp_res_tac (GSYM structure_size_thm)) \\
                  fs[size_def] \\
		  fs[almost_balancedL_def, invariant_def, balanced_def,
		     delta_def, structure_size_def, size_def] \\
                  rw[] \\
		  Cases_on `(structure_size b + (structure_size b0 + 1)) <
                            (size r + 1)` \\
                  fs[MIN_DEF])
	      >- (`invariant f (Bin n k v b b0)` by fs[invariant_def] \\
                  sg `structure_size (balanceL q' r' (Bin n k v b b0) r) =
                  1+(structure_size r)+(structure_size (Bin n k v b b0))`
                  >- (imp_res_tac balanceL_size \\
                      first_x_assum (qspecl_then [`r'`, `q'`] assume_tac) \\
                      rw[])
		  >- rw[]))))
QED;

Theorem delete_one_smaller:
  !s. (good_cmp f) /\
      (invariant f b) /\
      ~(balanced_map$null b) ==>
      balanced_map$structure_size (balanced_map$delete f (THE (one_key b)) b) <
      balanced_map$structure_size b
Proof
  strip_tac \\
  rw[structure_size_def] \\
  Cases_on `b`
  >- fs[null_def, balanced_mapTheory.null_def]
  >- (rw[one_key_def, THE_DEF, delete_def,
	 balanced_mapTheory.delete_def] \\
      sg `f k k = Equal`
      >- (imp_res_tac good_cmp_thm \\
          rpt (first_x_assum (qspecl_then [`k`] assume_tac)) \\
          rw[])
      >- (rw[structure_size_def] \\
          `invariant f b'` by fs[invariant_def] \\
          `invariant f b0` by fs[invariant_def] \\
          imp_res_tac glue_size \\
	  rw[]))
QED;

val (map_diff_def, map_diff_ind) =
  Defn.tprove (map_diff_defn,
    wf_rel_tac `measure (\(cmp,s1,_). structure_size s1)` \\
    CONJ_TAC \\
    rpt strip_tac \\
    imp_res_tac delete_one_smaller \\ rw[])
;

(* map containing all the the nodes of the graph *)
val map_nodes_def = Define `
  (map_nodes [] = (empty num_cmp)) /\
  (map_nodes ((Vertex l adjs)::vs) =
    insert (union
            (map_nodes vs)
            (mlmap$fromList num_cmp (MAP (\ (l,d).(l,T)) adjs)))
            l T)
`;

(* EVAL ``map_nodes  *)
(*   [(Vertex (1:num) [(2:num, 4); (3, 5)]); (Vertex 2 [(1, 4)])] *)
(* ``; *)



(* Defn.tgoal dijkstra_step_defn; *)
val (dijkstra_step_def, dijkstra_step_ind) =
  Defn.tprove (dijkstra_step_defn,
               cheat)
;




val dijkstra_def = Define `
  dijkstra source graph =
    dijkstra_step graph
                  (initial_distances source graph)
                  (b_insert geq (ElemPrio source (Num 0)) Bsbempty)
                  (empty num_cmp)
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

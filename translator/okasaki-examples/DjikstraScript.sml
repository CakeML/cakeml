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
  get_adjacents l ((l', ns)::vs) =
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

val add_inf_def = Define `
  (add_inf Inf _ = Inf) /\
  (add_inf _ Inf = Inf) /\
  (add_inf (Num x) (Num y) = Num (x+y))
`;

Datatype `elemPrio = ElemPrio 'a infiNum`;

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

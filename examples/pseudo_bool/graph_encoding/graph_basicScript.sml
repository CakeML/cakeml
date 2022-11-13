(*
  Basic graph notions
*)
open preamble mlintTheory;

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

(* Parser for LAD *)
Definition blanks_def:
  blanks (c:char) ⇔ c = #" " ∨ c = #"\n" ∨ c = #"\t" ∨ c = #"\r"
End

Definition tokenize_def:
  tokenize (s:mlstring) =
  case mlint$fromNatString s of
    NONE => INL s
  | SOME i => INR i
End

Definition toks_def:
  toks s = MAP tokenize (tokens blanks s)
End

Definition parse_num_list_def:
  (parse_num_list v [] acc = SOME (REVERSE acc)) ∧
  (parse_num_list v (x::xs) acc =
    case x of
      INR (n:num) => parse_num_list v xs (n::acc)
    | INL _ => NONE)
End

(* A parser for LAD format *)
Definition parse_edges_def:
  (parse_edges v i [] acc = SOME acc) ∧
  (parse_edges v i (l::ls) acc =
    case parse_num_list v l [] of
      SOME (d::xs) =>
        if LENGTH xs = d then parse_edges v (i+1) ls (insert i xs acc) else NONE
    | _ => NONE)
End

Definition check_good_edges_inner_def:
  check_good_edges_inner u v es =
  case lookup u es of NONE => F
      | SOME edges => MEM v edges
End

(* Undirectedness and u < bound *)
Definition check_good_edges_def:
  check_good_edges bound v ls es =
    EVERY (λu.
      check_good_edges_inner u v es) ls
End

Definition check_good_graph_def:
  check_good_graph (nv,edgelist) ⇔
  let ls = toAList edgelist in
  EVERY (λ(v,e). v < nv ∧ check_good_edges nv v e edgelist) ls
End

Theorem check_good_graph:
  check_good_graph (v,e) ⇒
  good_graph (v,e)
Proof
  rw[good_graph_def,check_good_graph_def,is_edge_def]>>
  fs[GSYM MEM_toAList,EVERY_MEM]>>
  first_x_assum drule>>
  fs[check_good_edges_def,check_good_edges_inner_def]>>
  rw[]>>
  fs[EVERY_MEM]
QED

Definition parse_lad_toks_def:
  parse_lad_toks ls =
  case ls of
    [INR h]::rest =>
      (case parse_edges h 0 rest LN of NONE => NONE
      | SOME e => SOME (h,e))
  | _ => NONE
End

val ladraw = ``[
  strlit"5";
  strlit"3 1 3 4";
  strlit"3 0 3 4";
  strlit"1 3";
  strlit"3 0 1 2";
  strlit"2 0 1";
]``;

val pattern = rconc (EVAL``check_good_graph (THE (parse_lad_toks (MAP toks ^(ladraw))))``)

(* Odd cases with self-edges *)

val ladraw = ``[
  strlit"2";
  strlit"2 0 1";
  strlit"2 1 0";
]``;

val pattern = rconc (EVAL``check_good_graph (THE (parse_lad_toks (MAP toks ^(ladraw))))``)

val _ = export_theory();

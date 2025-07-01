(*
  Basic graph notions
*)
open preamble mlintTheory;

val _ = new_theory "graph_basic";

(* Graph: (V : num , E : (num_set) num_map)
  V number of vertices
  E edge list representation *)

Type edges = ``:num_set num_map``;
Type graph = ``:num # edges``;

(* Edge from a -> b in edge list representation e *)
Definition is_edge_def:
  is_edge (e:edges) (a:num) (b:num) ⇔
  case lookup a e of
    SOME ns => lookup b ns = SOME ()
  | _ => F
End

Theorem is_edge_thm:
  is_edge e a b ⇔
  ∃ns.
    lookup a e = SOME ns ∧
    lookup b ns = SOME ()
Proof
  rw[is_edge_def]>>every_case_tac>>fs[]
QED

(* A "good" graph is undirected and only mentions edges < v *)
Definition good_graph_def:
  good_graph ((v,e):graph) ⇔
  domain e ⊆ count v ∧
  ∀a b. is_edge e a b ⇒ is_edge e b a
End

Theorem good_graph_eq:
  good_graph (v,e) ⇔
  ∀a ns.
    (sptree$lookup a e = SOME ns ⇒
      a < v ∧
      (∀b. is_edge e a b ⇒ is_edge e b a))
Proof
  rw[good_graph_def,EQ_IMP_THM,SUBSET_DEF,domain_lookup]>>
  fs[is_edge_thm]
QED

Definition neighbours_sp_def:
  neighbours_sp e v =
  case lookup v e of
    NONE => LN
  | SOME ns => ns
End

Theorem lookup_neighbours_sp:
  lookup b (neighbours_sp e a) = SOME () ⇔
  is_edge e a b
Proof
  rw[neighbours_sp_def,is_edge_thm]>>
  every_case_tac>>
  fs[]
QED

(* Neighbors as a sorted list *)
Definition neighbours_def:
  neighbours (e:edges) (v:num) =
  MAP FST (toSortedAList (neighbours_sp e v))
End

Theorem MEM_neighbours:
  MEM b (neighbours ep a) ⇔
  is_edge ep a b
Proof
  fs[MEM_toSortedAList,MEM_MAP,EXISTS_PROD,neighbours_def,lookup_neighbours_sp]
QED

Definition not_neighbours_def:
  not_neighbours (v,e) a =
  let n = neighbours_sp e a in
  FILTER (λu. lookup u n ≠ SOME ()) (COUNT_LIST v)
End

Theorem MEM_not_neighbours:
  MEM b (not_neighbours (vp,ep) a) ⇔
  b < vp ∧
  ¬is_edge ep a b
Proof
  rw[not_neighbours_def,MEM_FILTER,lookup_neighbours_sp,MEM_COUNT_LIST]>>
  metis_tac[]
QED

Definition insert_dir_edge_def:
  insert_dir_edge e u v =
  let ns = neighbours_sp e u in
  let nsv = insert v () ns in
  insert u nsv e
End

Definition insert_edge_def:
  insert_edge e u v =
  insert_dir_edge
    (insert_dir_edge e u v) v u
End

Theorem is_edge_insert_dir_edge:
  is_edge (insert_dir_edge e u v) x y ⇔
  is_edge e x y ∨
  x = u ∧ y = v
Proof
  rw[insert_dir_edge_def,is_edge_thm]>>
  every_case_tac>>
  rw[lookup_insert]>>
  rw[]>>
  fs[lookup_neighbours_sp,is_edge_thm]
QED

Theorem is_edge_insert_edge:
  is_edge (insert_edge e u v) x y ⇔
  is_edge e x y ∨
  x = u ∧ y = v ∨
  x = v ∧ y = u
Proof
  rw[is_edge_insert_dir_edge,insert_edge_def]>>
  metis_tac[]
QED

Theorem domain_insert_dir_edge:
  domain (insert_dir_edge e x y) = domain e ∪ {x}
Proof
  rw[insert_dir_edge_def]>>
  every_case_tac>>rw[]>>
  metis_tac[INSERT_SING_UNION,UNION_COMM]
QED

Theorem domain_insert_edge:
  domain (insert_edge e x y) = domain e ∪ {x;y}
Proof
  rw[insert_edge_def,domain_insert_dir_edge]>>
  simp[EXTENSION]>>
  metis_tac[]
QED

Theorem good_graph_insert_edge:
  good_graph (v,e) ∧
  x < v ∧ y < v ⇒
  good_graph (v,insert_edge e x y)
Proof
  rw[good_graph_def]
  >-
    simp[domain_insert_edge]
  >-
    fs[is_edge_insert_edge]
QED

(* Parsers *)

(* Everything recognized as a "blank" *)
Definition blanks_def:
  blanks (c:char) ⇔ c = #" " ∨ c = #"\n" ∨ c = #"\t" ∨ c = #"\r"
End

Definition tokenize_num_def:
  tokenize_num (s:mlstring) =
  case mlint$fromNatString s of
    NONE => INL s
  | SOME i => INR i
End

Definition toks_num_def:
  toks_num s = MAP tokenize_num (tokens blanks s)
End

(* Parser for LAD
  Assumptions:
  - The file must provide both (undirected) edges
*)
Definition parse_lad_num_list_def:
  (parse_lad_num_list v [] acc = SOME (REVERSE acc)) ∧
  (parse_lad_num_list v (x::xs) acc =
    case x of
      INR (n:num) => parse_lad_num_list v xs (n::acc)
    | INL _ => NONE)
End

Definition parse_lad_edges_def:
  (parse_lad_edges v i [] acc = SOME acc) ∧
  (parse_lad_edges v i (l::ls) acc =
    case parse_lad_num_list v l [] of
      SOME (d::xs) =>
        if LENGTH xs = d then
          parse_lad_edges v (i+1) ls (insert i (list_to_num_set xs) acc)
        else NONE
    | _ => NONE)
End

Definition parse_lad_toks_def:
  parse_lad_toks ls =
  case ls of
    [INR h]::rest =>
      (case parse_lad_edges h 0 rest LN of NONE => NONE
      | SOME e => SOME (h,e))
  | _ => NONE
End

Definition parse_lad_def:
  parse_lad lines = parse_lad_toks (MAP toks_num lines)
End

(* Parser for DIMACS
  Assumptions:
  - The file may provide edges in only one direction
    (they are automatically made into undirected edges)
*)
Definition nocomment_line_def:
  (nocomment_line (INL c::cs) = (c ≠ strlit "c")) ∧
  (nocomment_line _ = T)
End

Definition parse_dimacs_header_def:
  (parse_dimacs_header [INL p; INL lab; INR v; INR e] =
    if p = strlit"p" ∧
       (lab = strlit "col" ∨ lab = strlit"edge")
    then SOME (v:num,e:num)
    else NONE) ∧
  parse_dimacs_header _ = NONE
End

(* To keep the internal representation with LAD,
  we use 0-indexing *)
Definition parse_dimacs_edge_def:
  parse_dimacs_edge v ls =
    case ls of [INL e; INR (x:num); INR (y:num)] =>
      if e = strlit"e" ∧ x > 0 ∧ x ≤ v ∧ y > 0 ∧ y ≤ v
      then
        SOME (x - 1, y - 1)
      else NONE
    | _ => NONE
End

Definition parse_dimacs_edges_def:
  (parse_dimacs_edges v [] acc = SOME acc) ∧
  (parse_dimacs_edges v (l::ls) acc =
    case parse_dimacs_edge v l of
      SOME (x,y) =>
        parse_dimacs_edges v ls (insert_edge acc x y)
    | _ => NONE)
End

Definition parse_dimacs_toks_def:
  parse_dimacs_toks lines =
  case FILTER nocomment_line lines of
    [] => NONE
  | (h::xs) =>
    (case parse_dimacs_header h of NONE => NONE
    | SOME (v,e) =>
      (case parse_dimacs_edges v xs LN of
        NONE => NONE
      | SOME es => SOME (v,es)))
End

Definition parse_dimacs_def:
  parse_dimacs lines = parse_dimacs_toks (MAP toks_num lines)
End

Theorem parse_dimacs_edges_good_graph:
  ∀lines acc es.
  good_graph (v,acc) ∧
  parse_dimacs_edges v lines acc = SOME es ⇒
  good_graph (v,es)
Proof
  Induct>>rw[parse_dimacs_edges_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum match_mp_tac>>
  first_x_assum (irule_at Any)>>
  match_mp_tac good_graph_insert_edge>>
  fs[parse_dimacs_edge_def,AllCaseEqs()]
QED

Theorem parse_dimacs_good_graph:
  parse_dimacs lines = SOME g ⇒
  good_graph g
Proof
  rw[parse_dimacs_def,parse_dimacs_toks_def]>>
  gvs[AllCaseEqs()]>>
  match_mp_tac parse_dimacs_edges_good_graph>>
  first_x_assum (irule_at Any)>>
  fs[good_graph_def,is_edge_def]
QED

(* Undirectedness and u < bound *)
Definition check_good_edges_def:
  check_good_edges bound v ls es =
    EVERY (λ(u,_).
      is_edge es u v) (toAList ls)
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
  rw[good_graph_eq,check_good_graph_def,is_edge_def]>>
  fs[GSYM MEM_toAList,EVERY_MEM]>>
  fs[MEM_toAList,FORALL_PROD]>>
  first_x_assum drule>>
  fs[check_good_edges_def]>>
  rw[]>>
  fs[EVERY_MEM,MEM_toAList,FORALL_PROD]>>
  first_x_assum drule>>simp[is_edge_thm]>>
  rw[]>>
  simp[]
QED

Theorem check_good_graph_iff:
  good_graph g ⇔
  check_good_graph g
Proof
  Cases_on`g`>>
  simp[EQ_IMP_THM,check_good_graph]>>
  rw[good_graph_eq,check_good_graph_def,is_edge_def]>>
  fs[GSYM MEM_toAList,EVERY_MEM,FORALL_PROD]>>
  fs[MEM_toAList]>>rw[]>>
  first_x_assum drule>>
  fs[check_good_edges_def]>>
  rw[]>>
  fs[EVERY_MEM,FORALL_PROD,MEM_toAList]>>rw[]>>
  first_x_assum drule>>fs[is_edge_thm]>>
  every_case_tac>>fs[]
QED

(* This is just FOLD over naturals *)
Definition FOLDN_def:
  (FOLDN f 0 l = l) ∧
  (FOLDN f (SUC n) l = FOLDN f n (f n l))
End

Theorem FOLDN_APPEND:
  ∀xs.
  FOLDN (λu. $++ (f u)) n xs ++ y =
  FOLDN (λu. $++ (f u)) n (xs ++ y)
Proof
  Induct_on`n`>>simp[FOLDN_def]
QED

Theorem FOLDN_APPEND_op:
  $++ (FOLDN (λu. $++ (f u)) n xs) =
  λy. FOLDN (λu. $++ (f u)) n (xs ++ y)
Proof
  simp[FUN_EQ_THM,FOLDN_APPEND]
QED

Theorem FLAT_GENLIST_APPEND_FOLDN:
  ∀y.
  FLAT (GENLIST f n) ++ y =
  FOLDN (λu. $++ (f u)) n y
Proof
  Induct_on`n`>>rw[FOLDN_def,GENLIST,SNOC_APPEND]>>
  simp[FOLDN_APPEND]
QED

Theorem FLAT_GENLIST_FOLDN:
  FLAT (GENLIST f n) =
  FOLDN (λu. $++ (f u)) n []
Proof
  simp[GSYM FLAT_GENLIST_APPEND_FOLDN]
QED

Theorem APPEND_OP_DEF:
  $++ = λx y. x ++ y
Proof
  metis_tac[ETA_AX]
QED

Theorem MAP_if:
  MAP f (if p then a else b) = if p then MAP f a else MAP f b
Proof
  rw[]
QED

Theorem if_APPEND:
  (if p then a else b) ++ c = if p then a ++ c else b ++ c
Proof
  rw[]
QED

val ladraw = ``[
  strlit"5";
  strlit"3 1 3 4";
  strlit"3 0 3 4";
  strlit"1 3";
  strlit"3 0 1 2";
  strlit"2 0 1";
]``;

val pattern = rconc (EVAL``check_good_graph (THE (parse_lad ^ladraw))``)

(* Odd cases with self-edges *)

val ladraw = ``[
  strlit"2";
  strlit"2 0 1";
  strlit"2 1 0";
]``;

val pattern = rconc (EVAL``check_good_graph (THE (parse_lad ^ladraw))``)

(* DIMACS *)

val dimraw = ``[
strlit"c edge density";
strlit"c min degree";
strlit"p col 125 6963";
strlit"e 2 1";
strlit"e 3 1";
strlit"e 4 1";
strlit"e 5 1";
strlit"e 5 2";
strlit"e 5 3";
]``;

val pattern = rconc (EVAL``(THE (parse_dimacs ^dimraw))``)

val _ = export_theory();

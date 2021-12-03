(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble pb_constraintTheory mlstringTheory mlintTheory;

val _ = new_theory "pb_check";

val _ = numLib.prefer_num();

(* pbp = pseudo-boolean proof format
  Below, nums represent ConstraintIds, which are 1-indexed (although 0s internally work fine)
*)

(* A constraint to be added by a cutting planes proof *)
Datatype:
  constr =
  | Id num              (* Constraints can refer to earlier IDs *)
  | Add constr constr   (* Add two constraints *)
  | Mul constr num      (* Multiply by a constant factor *)
  | Div constr num      (* Divide by a constant factor *)
  | Sat constr          (* Saturation *)
  | Lit lit             (* Literal axiom lit ≥ 0 *)
  | Weak constr var     (* Addition of literal axioms until "var" disappears *)
End

Datatype:
  pbpstep =
  | Contradiction num (* Id representing a contradiction *)
  | Delete (num list) (* Ids to to delete *)
  | Polish constr     (* Adds a constraint, written in reverse polish notation *)
  (* TODO below
  | RUP constr --> u [constraint]
  | SR constr --> red [constraint] [mapping] [unit prop hints] [clauseID -> pbpstep list]
  | ... *)
End

(*
  The type of PB formulas represented as a finite map
  num -> pbc
*)
Type pbf = ``:npbc spt``;
Type pbp = ``:pbpstep list``;

(* Computes the LHS term of the slack of a constraint under
  a partial assignment p (list of literals) *)
Definition lslack_def:
  lslack (PBC ls num) p =
  SUM (MAP FST (FILTER (λ(a,b). ¬MEM (negate b) p) ls))
End

Definition check_contradiction_def:
  check_contradiction (PBC ls num) =
  let l = lslack (PBC ls num) [] in
    l < num
End

Definition check_polish_def:
  (check_polish fml (Id n) = lookup n fml) ∧
  (check_polish fml (Add c1 c2) =
    OPTION_MAP2 add (check_polish fml c1) (check_polish fml c2)) ∧
  (check_polish fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_polish fml c)) ∧
  (check_polish fml (Div c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. divide c k) (check_polish fml c)
    else NONE) ∧
  (check_polish fml (Sat c) =
    OPTION_MAP saturate (check_polish fml c)) ∧
  (check_polish fml (Lit l) = SOME (PBC [(1,l)] 0)) ∧
  (check_polish fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_polish fml c))
End

(* The result is either:
  Unsat -> unsatisfiability proved
  Fail -> proof step failed (more errors can be added in imperative part)
  Cont (pbf,num) -> continue with pbf and next ID (input formula is sat equiv to the pbv)
*)
Datatype:
  pbpres = Unsat | Fail | Cont pbf num
End

Definition check_pbpstep_def:
  check_pbpstep (step:pbpstep) (fml:pbf) (id:num) =
  case step of
    Contradiction n =>
      (case lookup n fml of
        NONE => Fail
      | SOME c =>
      if check_contradiction c then Unsat else Fail)
  | Delete ls =>
      Cont (FOLDL (λa b. delete b a) fml ls) id
  | Polish constr =>
    case check_polish fml constr of
      NONE => Fail
    | SOME c => Cont (insert id c fml) (id+1)
End

Definition check_pbpsteps_def:
  (check_pbpsteps [] fml id = Cont fml id) ∧
  (check_pbpsteps (step::steps) fml id =
    case check_pbpstep step fml id of
      Cont fml' id' => check_pbpsteps steps fml' id'
    | res => res)
End

(* Copied from satSem: this is the set of pseudoboolean constraints *)
Theorem check_polish_correct:
  ∀n c w.
  check_polish fml n = SOME c ∧ satisfies w (range fml) ⇒
  satisfies_npbc w c
Proof
  Induct_on`n`>>rw[check_polish_def]
  >- (
    (*Id case*)
    fs[satisfies_def,range_def]>>metis_tac[])
  >- (
    (* add case *)
    match_mp_tac add_thm>>
    metis_tac[])
 >- (
    (* multiply case *)
    match_mp_tac multiply_thm>>
    metis_tac[])
  >- (
    (* divide case *)
    match_mp_tac divide_thm>>
    metis_tac[])
  >- (
    (* saturate case *)
    match_mp_tac saturate_thm>>
    metis_tac[])
  >- (
    (* literal case *)
    EVAL_TAC)
  >- (
    (* weaken case *)
    match_mp_tac weaken_thm>>
    metis_tac[])
QED

Theorem check_polish_compact:
  ∀n c.
  (∀c. c ∈ range fml ⇒ compact c) ∧
  check_polish fml n = SOME c ⇒
  compact c
Proof
  Induct_on`n`>>rw[check_polish_def]
  >- (
    (*Id case*)
    fs[range_def]>>metis_tac[])
  >- (
    (* add case *)
    metis_tac[compact_add])
 >- (
    (* multiply case *)
    metis_tac[compact_multiply])
  >- (
    metis_tac[compact_divide])
  >- (
    metis_tac[compact_saturate])
  >- (
    (* literal case *)
    EVAL_TAC)
  >- (
    (* weaken case *)
    metis_tac[compact_weaken])
QED

Theorem check_contradiction_unsat:
  check_contradiction c ⇒
  ¬satisfies_npbc w c
Proof
  Cases_on`c`>>
  rw[check_contradiction_def,satisfies_npbc_def,lslack_def]>>
  qmatch_asmsub_abbrev_tac`MAP FST lss`>>
  `lss = l` by
    fs[Abbr`lss`,FILTER_EQ_ID,EVERY_MEM,FORALL_PROD]>>
  rw[]>>
  `SUM (MAP (eval_term w) l) ≤ SUM (MAP FST l)` by
      (match_mp_tac SUM_MAP_same_LE>>
      fs[EVERY_MEM,FORALL_PROD]>>
      rw[]>>
      rename1`eval_lit w r`>>
      assume_tac eval_lit_bool>>
      fs[])>>
  fs[]
QED

Theorem range_FOLDL_delete:
  ∀ls v.
  range (FOLDL (λa b. delete b a) v ls) ⊆ range v
Proof
  Induct>>rw[]>>
  first_x_assum (qspec_then`delete h v` mp_tac)>>rw[]>>
  match_mp_tac SUBSET_TRANS>>
  asm_exists_tac>>simp[]>>
  simp[range_delete]
QED

Theorem satisfiable_subset:
  satisfiable t ∧ s ⊆ t ⇒
  satisfiable s
Proof
  rw[satisfiable_def,SUBSET_DEF,satisfies_def]>>
  metis_tac[]
QED

Theorem check_pbpstep_Cont:
  check_pbpstep step fml id = Cont fml' id' ⇒
  satisfiable (range fml) ⇒ satisfiable (range fml')
Proof
  Cases_on`step`>>fs[check_pbpstep_def]>>
  every_case_tac
  >- (
    (* constraint deletion *)
    rw[]>>
    drule satisfiable_subset>>
    disch_then match_mp_tac>>
    fs[range_FOLDL_delete])
  >> (
    (* check_polish *)
    rw[]>>
    drule check_polish_correct>>
    fs[satisfiable_def,satisfies_def]>>
    rw[]>>qexists_tac`w`>>
    rw[]>>
    drule range_insert_2 >> fs[]>>
    metis_tac[])
QED

Theorem check_pbpstep_Unsat:
  check_pbpstep step fml id = Unsat ⇒
  ¬ satisfiable (range fml)
Proof
  Cases_on`step`>>fs[check_pbpstep_def]>>
  every_case_tac>>
  (* check_contradiction *)
  rw[satisfiable_def,range_def,satisfies_def]>>
  drule check_contradiction_unsat>>
  metis_tac[]
QED

Theorem check_pbpsteps_correct:
  ∀steps fml id.
  case check_pbpsteps steps fml id of
    Cont fml' id' =>
      satisfiable (range fml) ⇒ satisfiable (range fml')
  | Unsat =>
      ¬ satisfiable (range fml)
  | Fail => T
Proof
  Induct>>rw[check_pbpsteps_def]>>
  every_case_tac>>fs[]
  >- (
    drule check_pbpstep_Unsat>>fs[])>>
  (* two subgoals *)
  first_x_assum(qspecl_then [`s`,`n`] assume_tac)>>rfs[]>>
  metis_tac[check_pbpstep_Cont]
QED

Theorem check_pbpstep_compact:
  (∀c. c ∈ range fml ⇒ compact c) ∧
  check_pbpstep step fml id = Cont fml' id' ⇒
  (∀c. c ∈ range fml' ⇒ compact c)
Proof
  Cases_on`step`>>fs[check_pbpstep_def]>>
  every_case_tac>>rw[]
  >-
    metis_tac[range_FOLDL_delete,SUBSET_DEF] >>
  drule range_insert_2>>rw[]>>
  metis_tac[check_polish_compact]
QED

(* Parsing an OPB file
  For now, use the standard format where variables are named x1,...,xn
*)

(* todo: copied from lpr_parsing *)
(* Everything recognized as a "blank" *)
Definition blanks_def:
  blanks (c:char) ⇔ c = #" " ∨ c = #"\n" ∨ c = #"\t" ∨ c = #"\r"
End

Definition tokenize_def:
  tokenize (s:mlstring) =
  case mlint$fromString s of
    NONE => INL s
  | SOME i => INR i
End

Definition toks_def:
  toks s = MAP tokenize (tokens blanks s)
End

(* OPB parser
  Parses a literal xi, ~xi
  Note: for now, only handle default "xi" var names
*)

Definition parse_lit_def:
  parse_lit s =
  if strlen s ≥ 2 ∧ strsub s 0 = #"~" /\ strsub s 1 = #"x" then
    OPTION_MAP Neg (mlint$fromNatString (substring s 2 (strlen s - 2)))
  else if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    OPTION_MAP Pos (mlint$fromNatString (substring s 1 (strlen s - 1)))
  else NONE
End

(*
  EVAL ``parse_lit (strlit "x1")``
  EVAL ``parse_lit (strlit "~x1234")``
*)

(* Parse the LHS of a constraint and returns the remainder the line *)
Definition parse_constraint_LHS_def:
  (parse_constraint_LHS (INR n::INL v::rest) acc =
    case parse_lit v of NONE => (INR n::INL v::rest,REVERSE acc)
    | SOME lit => parse_constraint_LHS rest ((n,lit)::acc)) ∧
  (parse_constraint_LHS ls acc = (ls,REVERSE acc))
End

Definition term_le_def:
  term_le (_,l1) (_,l2) = (get_var l1 < get_var l2)
End

Definition term_eq_def:
  term_eq (_,l1) (_,l2) = (get_var l1 = get_var l2)
End

(* same as add_terms but not normalizing *)
Definition add_terms_denorm_def:
  add_terms_denorm (c1,Pos n) (c2,Pos _) = ((c1+c2:int,Pos n), 0) ∧
  add_terms_denorm (c1,Pos n) (c2,Neg _) = ((c1-c2,Pos n), c2) ∧
  add_terms_denorm (c1,Neg n) (c2,Neg _) = ((c1+c2,Neg n),0) ∧
  add_terms_denorm (c1,Neg n) (c2,Pos _) = ((c1-c2,Neg n),c2)
End

Definition merge_adjacent_def:
  (merge_adjacent (x::y::xs) acc n =
  if term_eq x y then
    let (trm,carry) = add_terms_denorm x y in
    merge_adjacent xs (trm::acc) (n-carry)
  else
    merge_adjacent (y::xs) (x::acc) n) ∧
  (merge_adjacent ls acc n = (REVERSE (ls++acc),n))
End

Definition normalize_def:
  (normalize [] acc n = (REVERSE acc,n)) ∧
  (normalize ((c,l)::xs) acc n =
    if (c:int) = 0 then normalize xs acc n
    else if c < 0 then (* *)
      normalize xs ((Num(-c),negate l)::acc) (n - c)
    else
      normalize xs ((Num c,l)::acc) n)
End

(* Given an inequality _ >= _, produces a normalized PBC *)
Definition normalize_PBC_def:
  normalize_PBC lhs deg =
  (* Sort literals by underlying vars then merge adjacent terms with equal vars *)
  let (lhs',deg') = merge_adjacent (QSORT term_le lhs) [] deg in
  let (lhs'',deg'') = normalize lhs' [] deg' in
  if deg'' < 0 then PBC lhs'' 0
  else PBC lhs'' (Num deg'')
End

(* strip ; from a number *)
Definition strip_terminator_def:
  strip_terminator s =
  if strlen s ≥ 1 ∧ strsub s (strlen s - 1) = #";"
  then mlint$fromString (substring s 0 (strlen s - 1))
  else NONE
End

Definition parse_constraint_def:
  parse_constraint line =
  case parse_constraint_LHS line [] of (rest,lhs) =>
  let cmpdeg =
    (case rest of
      [INL cmp; INR deg; INL term] =>
        if term ≠ str #";" then NONE else SOME(cmp,deg)
    | [INL cmp; INL degterm] =>
      (case strip_terminator degterm of NONE => NONE
      | SOME deg => SOME(cmp,deg))
    | _ => NONE) in
  case cmpdeg of NONE => NONE
  | SOME (cmp, deg) =>
    if cmp = implode ">=" then
      SOME [normalize_PBC lhs deg]
    else if cmp = implode "=" then
      (* which one first ? *)
      SOME [normalize_PBC (MAP (λ(c:int,l). (-c,l)) lhs) (-deg); normalize_PBC lhs deg]
    else NONE
End

Definition parse_constraints_def:
  (parse_constraints [] acc = SOME (REVERSE acc)) ∧
  (parse_constraints (s::ss) acc =
    case parse_constraint s of
      NONE => NONE
    | SOME pbc => parse_constraints ss (pbc++acc))
End

Definition nocomment_line_def:
  (nocomment_line (INL c::cs) = (c ≠ strlit "*")) ∧
  (nocomment_line _ = T)
End

(* Parse the tokenized pbf file *)
Definition parse_pbf_toks_def:
  parse_pbf_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  (* TODO: parse the header line ? *)
  parse_constraints nocomments []
End

(* Parse a list of strings in pbf format *)
Definition parse_pbf_def:
  parse_pbf strs = parse_pbf_toks (MAP toks strs)
End

(* build an sptree for the PBF from an initial ID *)
Definition build_fml_def:
  (build_fml (id:num) [] acc = (acc,id)) ∧
  (build_fml id (s::ss) acc =
    build_fml (id+1) ss (insert id s acc))
End

(* The stack is formed from constraints, where factors and variables are
  also encoded using Id *)
Definition parse_polish_def:
  (parse_polish (x::xs) stack =
  case x of INR n =>
    parse_polish xs (Id n :: stack)
  | INL s =>
  if s = str #"+" then
    (case stack of
      a::b::rest => parse_polish xs (Add b a::rest)
    | _ => NONE)
  else if s = str #"*" then
    (case stack of
      Id a::b::rest => parse_polish xs (Mul b a::rest)
    | _ => NONE)
  else if s = str #"d" then
    (case stack of
      Id a::b::rest => parse_polish xs (Div b a::rest)
    | _ => NONE)
  else if s = str #"s" then
    (case stack of
      a::rest => parse_polish xs (Sat a::rest)
    | _ => NONE)
  else if s = str #"w" then
    (case stack of
      Lit (Pos v)::a::rest => parse_polish xs (Weak a v::rest)
    | _ => NONE)
  else
    case parse_lit s of SOME l => parse_polish xs (Lit l::stack)
    | NONE => NONE) ∧
  (parse_polish [] [c] = SOME c) ∧
  (parse_polish [] _ = NONE)
End

Definition strip_numbers_def:
  (strip_numbers [] acc = SOME (REVERSE acc)) ∧
  (strip_numbers (x::xs) acc =
  case x of INR n =>
    strip_numbers xs (n::acc)
  | INL _ => NONE)
End

Definition parse_pbpstep_def:
  (parse_pbpstep (first::rest) =
  if first = INL (strlit "c") then
    case rest of
      [INR id] => SOME (Contradiction id)
    | _ => NONE
  else if first = INL (strlit "d") then
    OPTION_MAP Delete (strip_numbers rest [])
  else if first = INL (strlit "p") then
    OPTION_MAP Polish (parse_polish rest [])
  else NONE) ∧
  (parse_pbpstep _ = NONE)
End

Definition parse_pbpsteps_def:
  (parse_pbpsteps [] acc = SOME (REVERSE acc)) ∧
  (parse_pbpsteps (s::ss) acc =
    case parse_pbpstep s of
      NONE => NONE
    | SOME pbpstep => parse_pbpsteps ss (pbpstep::acc))
End

Definition parse_pbp_toks_def:
  parse_pbp_toks tokss =
  let nocomments = FILTER nocomment_line tokss in
  (* TODO: parse the header line ? *)
  parse_pbpsteps nocomments []
End

(* Exactly the same as tokenize, but parses to nums instead of ints *)
Definition tokenize_num_def:
  tokenize_num (s:mlstring) =
  case mlint$fromNatString s of
    NONE => INL s
  | SOME i => INR i
End

Definition toks_num_def:
  toks_num s = MAP tokenize_num (tokens blanks s)
End

(* Parse a list of strings in pbf format *)
Definition parse_pbp_def:
  parse_pbp strs = parse_pbp_toks (MAP toks_num strs)
End

val pbfraw = ``[
  strlit "* #variable= 4 #constraint= 7";
  strlit "2 ~x1 1 ~x3 >= 1;";
  strlit "1 ~x3 1 ~x5 >= 1 ;";
  strlit "1 ~x1 1 ~x5 >= 1;";
  strlit "1 ~x2 1 ~x4 1 ~x6 >= 2 ;";
  strlit "* test comment 1234567";
  strlit "+1 x1 +1 x2 >= 1 ;";
  strlit "+1 x3 +1 x4 >= 1 ;";
  strlit "+1 x5 +1 x6 >= 1 ;";
]``;

val pbf = rconc (EVAL ``THE (parse_pbf ^(pbfraw))``);

val pbpraw = ``[
  strlit"* comment";
  strlit"p 1 s";
  strlit"* comment 2";
  strlit"p 8 2 + 3 +";
  strlit"p 9 2 d";
  strlit"p 10 4 + 5 + 6 + 7 +";
  strlit"c 11";
]``;

val pbp = rconc (EVAL ``THE (parse_pbp ^(pbpraw))``);

val check = rconc (EVAL``((UNCURRY (check_pbpsteps ^(pbp))) (build_fml 1 ^(pbf) LN))``);

val _ = export_theory ();

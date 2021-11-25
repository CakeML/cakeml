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
  | RUP constr
  | ... *)
End

(*
  The type of PB formulas represented as a finite map
  num -> pb_constraint
*)
Type pbf = ``:pb_constraint spt``;
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
(* TODO: probably move *)
Definition values_def:
  values s = {v | ∃n. lookup n s = SOME v}
End

Theorem check_polish_correct:
  ∀n c w.
  check_polish fml n = SOME c ∧ satisfies w (values fml) ⇒
  eval_pbc w c
Proof
  Induct_on`n`>>rw[check_polish_def]
  >- (
    (*Id case*)
    fs[satisfies_def,values_def]>>metis_tac[])
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
  (∀c. c ∈ values fml ⇒ compact c) ∧
  check_polish fml n = SOME c ⇒
  compact c
Proof
  Induct_on`n`>>rw[check_polish_def]
  >- (
    (*Id case*)
    fs[values_def]>>metis_tac[])
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
  ¬eval_pbc w c
Proof
  Cases_on`c`>>
  rw[check_contradiction_def,eval_pbc_def,lslack_def]>>
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

(* TODO: copied *)
Theorem values_delete:
  values (delete h v) ⊆ values v
Proof
  simp[values_def,lookup_delete,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem values_insert:
  C ∈ values (insert n l fml) ⇒ C ∈ values fml ∨ C = l
Proof
  fs[values_def,lookup_insert]>>
  rw[]>>
  every_case_tac>>fs[]>>
  metis_tac[]
QED

Theorem values_insert2:
  values (insert n l fml) ⊆ l INSERT values fml
Proof
  rw[SUBSET_DEF]>>
  metis_tac[values_insert]
QED

Theorem values_FOLDL_delete:
  ∀ls v.
  values (FOLDL (λa b. delete b a) v ls) ⊆ values v
Proof
  Induct>>rw[]>>
  first_x_assum (qspec_then`delete h v` mp_tac)>>rw[]>>
  match_mp_tac SUBSET_TRANS>>
  asm_exists_tac>>simp[]>>
  simp[values_delete]
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
  satisfiable (values fml) ⇒ satisfiable (values fml')
Proof
  Cases_on`step`>>fs[check_pbpstep_def]>>
  every_case_tac
  >- (
    (* constraint deletion *)
    rw[]>>
    drule satisfiable_subset>>
    disch_then match_mp_tac>>
    fs[values_FOLDL_delete])
  >> (
    (* check_polish *)
    rw[]>>
    drule check_polish_correct>>
    fs[satisfiable_def,satisfies_def]>>
    rw[]>>qexists_tac`w`>>
    rw[]>>
    drule values_insert >> fs[]>>
    metis_tac[])
QED

Theorem check_pbpstep_Unsat:
  check_pbpstep step fml id = Unsat ⇒
  ¬ satisfiable (values fml)
Proof
  Cases_on`step`>>fs[check_pbpstep_def]>>
  every_case_tac>>
  (* check_contradiction *)
  rw[satisfiable_def,values_def,satisfies_def]>>
  drule check_contradiction_unsat>>
  metis_tac[]
QED

Theorem check_pbpsteps_correct:
  ∀steps fml id.
  case check_pbpsteps steps fml id of
    Cont fml' id' =>
      satisfiable (values fml) ⇒ satisfiable (values fml')
  | Unsat =>
      ¬ satisfiable (values fml)
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
  (∀c. c ∈ values fml ⇒ compact c) ∧
  check_pbpstep step fml id = Cont fml' id' ⇒
  (∀c. c ∈ values fml' ⇒ compact c)
Proof
  Cases_on`step`>>fs[check_pbpstep_def]>>
  every_case_tac>>rw[]
  >-
    metis_tac[values_FOLDL_delete,SUBSET_DEF] >>
  drule values_insert>>rw[]>>
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

(* OPB parser *)

Definition parse_lit_def:
  parse_lit s =
  if strlen s ≥ 2 ∧ strsub s 0 = #"~" /\ strsub s 1 = #"x" then
    OPTION_MAP Neg (mlint$fromNatString (substring s 2 (strlen s - 1)))
  else if strlen s ≥ 1 ∧ strsub s 0 = #"x" then
    OPTION_MAP Pos (mlint$fromNatString (substring s 1 (strlen s - 1)))
  else NONE
End

(* Parsing the LHS of a constraint and returns the rest *)
Definition parse_constraint_LHS_def:
  (parse_constraint_LHS (INR n::INL v::rest) acc =
    (*  Note: for now, we only handle names of the form "xi" *)
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
      normalize xs ((Num(-c),negate l)::acc) (n + c)
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

Definition parse_constraint_def:
  parse_constraint line =
  case parse_constraint_LHS line [] of (rest,lhs) =>
  case rest of
    [INL cmp; INR deg; INL term] =>
      if term ≠ str #";" then NONE
      else if cmp = implode ">=" then
        SOME [normalize_PBC lhs deg]
      else NONE
  | _ => NONE
End

(* EVAL``parse_constraint (toks (strlit "10 x1 +2 x2 -12 x1 >= 1 ;"))`` *)

val _ = export_theory ();

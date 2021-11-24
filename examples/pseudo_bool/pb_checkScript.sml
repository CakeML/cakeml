(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble pb_constraintTheory;

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
  a partial assignment p (list of literals)
Definition lslack_def:
  lslack (PBC ls num) p =
  SUM (MAP FST (FILTER (λ(a,b). ¬MEM (negate b) p) ls))
End

Definition check_contradiction_def:
  check_contradiction (PBC ls num) = ¬
  let l = lslack (PBC ls num) [] in
    l < num
End *)

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
    (* divide case TODO: must be changed to ensure compactness(?) *)
    cheat)
  >- (
    (* saturate case TODO: must be changed to ensure compactness *)
    cheat)
  >- (
    (* literal case *)
    EVAL_TAC)
  >- (
    (* weaken case *)
    cheat)
QED

Theorem check_contradiction_unsat:
  check_contradiction c ⇒
  ¬eval_pbc w c
Proof
  Cases_on`c`>>rw[check_contradiction_def,eval_pbc_def,lslack_def]>>
  CCONTR_TAC>>fs[]>>
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

(* TODO: write a parser *)

val _ = export_theory ();

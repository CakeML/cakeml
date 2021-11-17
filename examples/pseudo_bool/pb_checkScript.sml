(*
  Pseudo-boolean constraints proof format and checker
*)
open preamble pb_constraintTheory;

val _ = new_theory "pb_check";

val _ = numLib.prefer_num();

(* pbp = pseudo-boolean proof format
  Below, nums represent ConstraintIds, which are 1-indexed (although 0s internally work fine)
*)
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

(* Copied from satSem: this is the set of pseudoboolean constraints *)
(* TODO: probably move *)
Definition values_def:
  values s = {v | ∃n. lookup n s = SOME v}
End

(* TODO: every constraint is satisfied, maybe rename eval_pbc to satisfies_pbc *)
Definition satisfies_def:
  satisfies w pbf ⇔
  ∀c. c ∈ values pbf ⇒ eval_pbc w c
End

Theorem check_polish_correct:
  ∀n c w.
  check_polish fml n = SOME c ∧ satisfies w fml ⇒
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

val _ = export_theory ();

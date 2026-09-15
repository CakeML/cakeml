(*
  Formalization of And-Inverter Graphs
*)
Theory aig
Ancestors
  misc mlstring
Libs
  preamble

val _ = numLib.prefer_num()

(* TODO Make aigScript over tuples again *)
(* TODO Turn all lits_hold over singleton set to eval/xeval *)

(* TODO Replace sg and derivatives by have *)
(* TODO Replace qsuff_tac with suff *)
(* TODO Replay by with have ‘...’ >- ...*)

(* TODO Remove this once misc theory stops defining steps *)
val _ = Parse.remove_ovl_mapping "steps" {Name = "steps", Thy = "misc"}

(* And-Inverter Graphs ********************************************************)

(* Things that appear in base positions.
   Ff corresponds to the constant false. *)
Datatype:
  bvar = Ff | Input 'i | Latch 'l
End

Datatype:
  var = Gate 'a | Base (('i,'l) bvar)
End

Type istate = “:'i -> bool”
Type lstate = “:'l -> bool”
Type steps[pp] = “:num -> 'i istate # 'l lstate”

Definition eval_bvar_def[simp]:
  (eval_bvar (is: 'i istate, ls: 'l lstate) Ff = F) ∧
  (eval_bvar (is,ls) (Input i) = is i) ∧
  (eval_bvar (is,ls) (Latch l) = ls l)
End

Theorem eval_bvar_Ff[simp]:
  eval_bvar isls Ff = F
Proof
  Cases_on ‘isls’ >> simp [eval_bvar_def]
QED

Type lit[pp] = “:('a,'i,'l) var # bool”
Overload TT = “(Base Ff, T)”
Overload FF = “(Base Ff, F)”

Type and[pp] = “:'a # (('a,'i,'l) lit list)”
Type aig[pp] = “:('a,'i,'l) and list”

(* Note that we can conjunction over a list of literals as opposed to a pair.
   If needed, we can apply a reduction at the end, allowing for simpler
   definitions for operations such as equivalence.  *)
Definition eval_lit_def:
  (eval_lit (ss : 'i istate # 'l lstate) aig ((v,b):('a,'i,'l) lit) =
    case v of
    | Base bv => b ⇎ eval_bvar ss bv
    | Gate n => b ⇎ eval_gate ss aig n) ∧
  (eval_gate ss ([]:('a,'i,'l) aig) n = F) ∧
  (eval_gate ss (h::tl) n =
   let (n', ins) = h in
     if n' = n then EVERY (eval_lit ss tl) ins
     else eval_gate ss tl n)
End

(*
EVAL``eval_lit (is,ls) aig TT``
EVAL``eval_lit (is,ls) aig FF``
*)

Theorem eval_gate_nil[simp]:
  ¬eval_gate ss [] n
Proof
  simp [eval_lit_def]
QED

(** AIGs with access to two states ********************************************)

Definition state_pair_def:
  state_pair (is₁,ls₁) (is₂,ls₂) =
    ((λi. sum_CASE i is₁ is₂), (λl. sum_CASE l ls₁ ls₂))
End

Theorem state_pair_surj:
  ∀s. ∃s₁ s₂. s = state_pair s₁ s₂
Proof
  namedCases ["is ls"]
  >> qexistsl_tac [‘(is ∘ INL, ls ∘ INL)’, ‘(is ∘ INR, ls ∘ INR)’]
  >> simp [state_pair_def, FUN_EQ_THM]
  >> conj_tac >> Cases >> simp []
QED

Theorem FORALL_STATE_PAIR:
  (∀s. P s) ⇔ (∀s₁ s₂. P (state_pair s₁ s₂))
Proof
  metis_tac [state_pair_surj]
QED

(* Circuits *******************************************************************)

Definition lits_hold_def:
  lits_hold ss (aig: ('a, 'i, 'l) aig) (lits: ('a,'i,'l) lit set) ⇔
    ∀lit. lit ∈ lits ⇒ eval_lit ss aig lit
End

Definition is_reset_def:
  is_reset ss (aig: ('a, 'i, 'l) aig)
    (reset: 'l -> ('a,'i,'l) lit option) (latches: 'l set) =
  ∀l lit.
    l ∈ latches ∧ reset l = SOME lit ⇒
    eval_lit ss aig (Base (Latch l), F) =
    eval_lit ss aig lit
End

Definition is_next_def:
  is_next ss₀ (aig: ('a, 'i, 'l) aig)
    (next: 'l -> ('a,'i,'l) lit) (latches: 'l set) ls₁ =
  ∀l. l ∈ latches ⇒ eval_lit ss₀ aig (next l) = ls₁ l
End

Definition is_trace_def:
  is_trace (aig: ('a, 'i, 'l) aig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (steps: ('i, 'l) steps) (n: num)
  ⇔
    is_reset (steps 0) aig reset latches ∧
    lits_hold (steps 0) aig cnstrs ∧
    (∀i. i < n ⇒
       is_next (steps i) aig next latches (SND (steps (i + 1))) ∧
       lits_hold (steps (i + 1)) aig cnstrs)
End

(** Safety ********************************************************************)

Definition is_unsafe_def:
  is_unsafe (aig: ('a, 'i, 'l) aig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set) (safes: ('a,'i,'l) lit set)
  =
  ∃(steps: ('i, 'l) steps) (n: num).
    is_trace aig reset next cnstrs latches steps n ∧
    ¬lits_hold (steps n) aig safes
End

Definition is_safe_def:
  is_safe (aig: ('a, 'i, 'l) aig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (safes: ('a,'i,'l) lit set) ⇔
  ¬is_unsafe aig reset next cnstrs latches safes
End

(** Liveness ******************************************************************)

Definition is_inf_trace_def:
  is_inf_trace (aig: ('a, 'i, 'l) aig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (steps: ('i, 'l) steps)
  ⇔
    is_reset (steps 0) aig reset latches ∧
    lits_hold (steps 0) aig cnstrs ∧
    (∀i.
       is_next (steps i) aig next latches (SND (steps (i + 1))) ∧
       lits_hold (steps (i + 1)) aig cnstrs)
End

Theorem is_inf_trace_eq:
  is_inf_trace aig reset next cnstrs latches steps ⇔
  ∀n. is_trace aig reset next cnstrs latches steps n
Proof
  eq_tac>>
  rw[is_inf_trace_def,is_trace_def]>>
  first_x_assum(qspec_then`i+1` mp_tac)>>
  rw[]
QED

Definition is_live_def:
  is_live (aig: ('a, 'i, 'l) aig) (reset: 'l -> ('a,'i,'l) lit option)
    (next: 'l -> ('a,'i,'l) lit) (cnstrs: ('a,'i,'l) lit set)
    (qaig: ('b, 'i + 'i, 'l + 'l) aig)
    (live: ('b, 'i + 'i, 'l + 'l) lit set set) (latches: 'l set) =
  ∀steps.
    is_inf_trace aig reset next cnstrs latches steps ⇒
    ∀prop. prop ∈ live ⇒
      ∃k signal.
        signal ∈ prop ∧
        (∀i. k ≤ i ⇒
             eval_lit (state_pair (steps i) (steps (i + 1))) qaig signal)
End

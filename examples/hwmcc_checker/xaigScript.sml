(*
  An eXtended AIG format for internal use
*)
Theory xaig
Ancestors
  aig
Libs
  preamble

(* eXtended And-Inverter Graphs ***********************************************)
(* The only part of AIGs we extend are the types of gates; the notion of state,
   variables and literals stays the same. *)

Datatype:
  gty =
    (* Multi-input And gates out = \And_i in_i *)
    And (('a,'i,'l) lit list)
    (* Two-input XOR gates out = in_1 XOR in_2 *)
  | Xor (('a,'i,'l) lit) (('a,'i,'l) lit)
    (* Three-input if-then-else gates
      out = if in_1 then in_2 else in_3 *)
  | Ite (('a,'i,'l) lit) (('a,'i,'l) lit) (('a,'i,'l) lit)
    (* Multi-input Or gates out = ⋁ᵢ inᵢ *)
  | Or (('a,'i,'l) lit list)
End

Definition get_lits_def[simp]:
  get_lits (And xs) = xs ∧
  get_lits (Xor x₀ x₁) = [x₀; x₁] ∧
  get_lits (Ite cnd thn els) = [cnd; thn; els] ∧
  get_lits (Or xs) = xs
End

Type gate[pp] = “:('a # ('a,'i,'l) gty)”
Type xaig[pp] = “:('a,'i,'l) gate list”

(* Analogous to eval_lit for aig *)

Definition xeval_lit_def:
  (xeval_lit (ss : 'i istate # 'l lstate) xaig
    ((v,b):('a,'i,'l) lit) =
    case v of
    | Base bv => b ⇎ eval_bvar ss bv
    | Gate n => b ⇎ xeval_gate ss xaig n) ∧
  (xeval_gate ss ([]:('a,'i,'l) xaig) n = F) ∧
  (xeval_gate ss (h::tl) n =
   let (n', gt) = h in
     if n' = n then
       xeval_gty ss tl gt
     else xeval_gate ss tl n) ∧
  (xeval_gty ss tl gt =
      (case gt of
        And ins => EVERY (xeval_lit ss tl) ins
      | Xor in1 in2 =>
        xeval_lit ss tl in1 ⇎ xeval_lit ss tl in2
      | Ite in1 inT inF =>
        if xeval_lit ss tl in1
        then xeval_lit ss tl inT
        else xeval_lit ss tl inF
      | Or ins => EXISTS (xeval_lit ss tl) ins))
End

Theorem xeval_gate_nil[simp]:
  ¬xeval_gate ss [] n
Proof
  simp [xeval_lit_def]
QED

Theorem xeval_lit_not:
   xeval_lit ss xaig (not x) ⇔ ¬xeval_lit ss xaig x
Proof
  Cases_on ‘x’
  >> simp [not_def, xeval_lit_def]
  >> TOP_CASE_TAC >> metis_tac []
QED

(* Equivalence to AIG *********************************************************)

Definition aig_xaig_rel_def:
  aig_xaig_rel aig xaig ⇔
  (∀ss n. eval_gate ss aig n ⇔ xeval_gate ss xaig n) ∧
  (∀ss lit. eval_lit ss aig lit ⇔ xeval_lit ss xaig lit)
End

(* Lifting to two states ******************************************************)

Definition gty_map_base_def:
  gty_map_base f g (And xs) =
    And (MAP (lit_map_base f g) xs) ∧
  gty_map_base f g (Xor x₀ x₁) =
    Xor (lit_map_base f g x₀) (lit_map_base f g x₁) ∧
  gty_map_base f g (Ite cnd thn els) =
    Ite (lit_map_base f g cnd) (lit_map_base f g thn) (lit_map_base f g els) ∧
  gty_map_base f g (Or xs) =
    Or (MAP (lit_map_base f g) xs)
End

Definition gate_map_base_def:
  gate_map_base f g (n, gty) = (n, gty_map_base f g gty)
End

Definition xaig_map_base_def:
  xaig_map_base f g (xaig: ('a, 'i, 'l) xaig) =
    MAP (gate_map_base f g) xaig
End

Definition qxleft_def:
  qxleft (xaig: ('a, 'i, 'l) xaig) = xaig_map_base INL INL xaig
End

Theorem qxleft_cons[local]:
  qxleft (g::xaig) = gate_map_base INL INL g::qxleft xaig
Proof
  simp [qxleft_def, xaig_map_base_def]
QED

Theorem xeval_gate_pair_qxleft:
  ∀xaig.
    (∀n.
       xeval_gate (state_pair s₁ s₂) (qxleft xaig) n ⇔
       xeval_gate s₁ xaig n) ∧
    (∀lit.
       xeval_lit (state_pair s₁ s₂) (qxleft xaig) (lit_map_base INL INL lit) ⇔
       xeval_lit s₁ xaig lit)
Proof
  Induct >> rw []
  >- simp [qxleft_def, xaig_map_base_def]
  >- (
    simp [qxleft_def, xaig_map_base_def]
    >> Cases_on ‘lit’
    >> rename1 ‘lit_map_base _ _ (v, _)’ >> Cases_on ‘v’
    >> simp [lit_map_base_def, var_map_base_def, xeval_lit_def]
    >> rename1 ‘bvar_map _ _ b’ >> Cases_on ‘b’
    >> simp [bvar_map_def, xeval_lit_def]
    >> Cases_on ‘s₁’ >> Cases_on ‘s₂’ >> simp [state_pair_def, eval_bvar_def]
  )
  >- (
    simp [xeval_lit_def, qxleft_cons]
    >> rw [] >> rpt (pairarg_tac >> gvs [])
    >> gvs [gate_map_base_def]
    >> IF_CASES_TAC >> gvs []
    >> rename1 ‘gty_map_base _ _ gt'’ >> Cases_on ‘gt'’
    >> simp [gty_map_base_def, EVERY_MAP, EXISTS_MAP]
  )
  >> Cases_on ‘lit’
  >> rename1 ‘lit_map_base _ _ (v, _)’ >> Cases_on ‘v’
  >> simp [lit_map_base_def, var_map_base_def, xeval_lit_def]
  >> qmatch_goalsub_abbrev_tac ‘(r ⇔ X) ⇔ (r ⇔ Y)’
  >> qsuff_tac ‘X ⇔ Y’ >- simp []
  >> simp [Abbr ‘X’, Abbr ‘Y’]
  >- (
    simp [qxleft_cons, xeval_lit_def]
    >> rpt (pairarg_tac >> gvs [])
    >> IF_CASES_TAC >> gvs []
    >> gvs [gate_map_base_def]
    >> rename1 ‘gty_map_base _ _ gt'’ >> Cases_on ‘gt'’
    >> simp [gty_map_base_def, EVERY_MAP, EXISTS_MAP])
  >> rename1 ‘bvar_map _ _ b’ >> Cases_on ‘b’
  >> simp [bvar_map_def, xeval_lit_def]
  >> Cases_on ‘s₁’ >> Cases_on ‘s₂’ >> simp [state_pair_def, eval_bvar_def]
QED

Theorem aig_xaig_rel_qleft:
  ∀maig mxaig.
    aig_xaig_rel (qleft maig) (qxleft mxaig) ⇔ aig_xaig_rel maig mxaig
Proof
  simp [aig_xaig_rel_def, FORALL_STATE_PAIR]
  >> rw [] >> eq_tac >> rw []
  >- metis_tac [eval_gate_pair_qleft, xeval_gate_pair_qxleft]
  >- metis_tac [eval_gate_pair_qleft, xeval_gate_pair_qxleft]
  >- metis_tac [eval_gate_pair_qleft, xeval_gate_pair_qxleft]
  >> Cases_on ‘lit’
  >> simp [eval_lit_def, xeval_lit_def]
  >> TOP_CASE_TAC >> simp []
  >> metis_tac [eval_gate_pair_qleft, xeval_gate_pair_qxleft]
QED

(* Circuits *******************************************************************)

Definition xlits_hold_def:
  xlits_hold ss (xaig: ('a, 'i, 'l) xaig) (lits: ('a,'i,'l) lit set) ⇔
    ∀lit. lit ∈ lits ⇒ xeval_lit ss xaig lit
End

Definition xis_reset_def:
  xis_reset ss (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (latches: 'l set) =
  ∀l lit.
    l ∈ latches ∧ reset l = SOME lit ⇒
    xeval_lit ss xaig (Base (Latch l), F) =
    xeval_lit ss xaig lit
End

Definition xis_next_def:
  xis_next ss₀ (xaig: ('a, 'i, 'l) xaig)
    (next: 'l -> ('a,'i,'l) lit) (latches: 'l set) ls₁ =
  ∀l. l ∈ latches ⇒ xeval_lit ss₀ xaig (next l) = ls₁ l
End

Definition xis_trace_def:
  xis_trace (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (steps: ('i, 'l) steps) (n: num)
  ⇔
    xis_reset (steps 0) xaig reset latches ∧
    xlits_hold (steps 0) xaig cnstrs ∧
    (∀i. i < n ⇒
       xis_next (steps i) xaig next latches (SND (steps (i + 1))) ∧
       xlits_hold (steps (i + 1)) xaig cnstrs)
End

(** Safety ********************************************************************)

Definition xis_unsafe_def:
  xis_unsafe (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set) (safes: ('a,'i,'l) lit set)
  =
  ∃(steps: ('i, 'l) steps) (n: num).
    xis_trace xaig reset next cnstrs latches steps n ∧
    ¬xlits_hold (steps n) xaig safes
End

Definition xis_safe_def:
  xis_safe (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (safes: ('a,'i,'l) lit set) ⇔
  ¬xis_unsafe xaig reset next cnstrs latches safes
End

Theorem xis_safe_is_safe:
  aig_xaig_rel maig mxaig ⇒
  (xis_safe mxaig mreset mnext mcnstrs mlatches msafes ⇔
   is_safe maig mreset mnext mcnstrs mlatches msafes)
Proof
  rw [aig_xaig_rel_def]
  >> simp [xis_safe_def, is_safe_def,
           xis_unsafe_def, is_unsafe_def, xis_trace_def,
           is_trace_def, xlits_hold_def, lits_hold_def,
           xis_reset_def, is_reset_def,
           xis_next_def, is_next_def]
QED

(** Liveness ******************************************************************)

Definition xis_inf_trace_def:
  xis_inf_trace (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (steps: ('i, 'l) steps)
  ⇔
    xis_reset (steps 0) xaig reset latches ∧
    xlits_hold (steps 0) xaig cnstrs ∧
    (∀i.
       xis_next (steps i) xaig next latches (SND (steps (i + 1))) ∧
       xlits_hold (steps (i + 1)) xaig cnstrs)
End

Theorem xis_inf_trace_eq:
  xis_inf_trace xaig reset next cnstrs latches steps ⇔
  ∀n. xis_trace xaig reset next cnstrs latches steps n
Proof
  eq_tac>>
  rw[xis_inf_trace_def,xis_trace_def]>>
  first_x_assum(qspec_then`i+1` mp_tac)>>
  rw[]
QED

Definition xis_live_def:
  xis_live (xaig: ('a, 'i, 'l) xaig) (reset: 'l -> ('a,'i,'l) lit option)
    (next: 'l -> ('a,'i,'l) lit) (cnstrs: ('a,'i,'l) lit set)
    (qxaig: ('b, 'i + 'i, 'l + 'l) xaig)
    (live: ('b, 'i + 'i, 'l + 'l) lit set set) (latches: 'l set) =
  ∀steps.
    xis_inf_trace xaig reset next cnstrs latches steps ⇒
    ∀prop. prop ∈ live ⇒
      ∃k signal.
        signal ∈ prop ∧
        (∀i. k ≤ i ⇒
             xeval_lit (state_pair (steps i) (steps (i + 1))) qxaig signal)
End

Theorem xis_live_is_live:
  aig_xaig_rel maig mxaig ⇒
  (xis_live
     mxaig mreset mnext (set mcnstrs) (qxleft mxaig)
     (IMAGE set (set (qleft_live mlive))) (set mlatches)
   ⇔
   is_live
     maig mreset mnext (set mcnstrs) (qleft maig)
     (IMAGE set (set (qleft_live mlive))) (set mlatches))
Proof
  strip_tac
  >> drule_then assume_tac $
       INST_TYPE [“:δ” |-> “:β”, “:ε” |-> “:γ”] $ iffRL aig_xaig_rel_qleft
  >> gvs [aig_xaig_rel_def]
  >> simp [xis_live_def, is_live_def, xis_inf_trace_def, is_inf_trace_def,
           xis_reset_def, is_reset_def, xlits_hold_def, lits_hold_def,
           xis_next_def, is_next_def]
QED

(* Converting from AIG to xAIG ************************************************)

(* Naive *)
Definition aig_to_xaig_def:
  (aig_to_xaig ([]:('a,'i,'l) aig) = []) ∧
  (aig_to_xaig ((n,ins)::tl) =
    (n,And ins)::aig_to_xaig tl)
End

(* Sanity check *)
Theorem aig_to_xaig_sound:
  ∀aig xaig lit gs.
  aig_to_xaig aig = xaig ⇒
  (eval_lit ss aig lit =
  xeval_lit ss xaig lit) ∧
  (eval_gate ss aig gs =
  xeval_gate ss xaig gs)
Proof
  Induct>>rw[aig_to_xaig_def]
  >-
    (Cases_on`lit`>>simp[eval_lit_def,xeval_lit_def])
  >- (
    Cases_on`h`>>
    Cases_on`lit`>>
    simp[eval_lit_def,xeval_lit_def,aig_to_xaig_def]>>
    every_case_tac>>rw[]
    >- (
      cong_tac NONE>>
      simp[FUN_EQ_THM])>>
    metis_tac[])>>
  Cases_on`h`>>
  rw[eval_lit_def,aig_to_xaig_def,xeval_lit_def]>>
  cong_tac NONE>>
  simp[FUN_EQ_THM]
QED

Theorem aig_xaig_rel_aig_to_xaig:
  ∀aig. aig_xaig_rel aig (aig_to_xaig aig)
Proof
  simp [aig_xaig_rel_def, aig_to_xaig_sound]
QED

(*
  Formalization of circuits over eXtended And-Inverter Graphs.
*)
Theory xaig_circ
Ancestors
  aig xaig
Libs
  preamble

(* TODO Remove this once misc theory stops defining steps *)
val _ = Parse.remove_ovl_mapping "steps" {Name = "steps", Thy = "misc"}

(** Various set definitions/theorems ******************************************)

Definition IMAGE_PARTIAL_DEF:
  IMAGE_PARTIAL f xs = {y | ∃x. x ∈ xs ∧ f x = SOME y}
End

Theorem IMAGE_PARTIAL_EMPTY[simp]:
  IMAGE_PARTIAL f ∅ = ∅
Proof
  simp [IMAGE_PARTIAL_DEF]
QED

Theorem IMAGE_PARTIAL_INSERT:
  IMAGE_PARTIAL f (x INSERT s) =
  case f x of
  | NONE => IMAGE_PARTIAL f s
  | SOME y => y INSERT IMAGE_PARTIAL f s
Proof
  simp [IMAGE_PARTIAL_DEF, INSERT_DEF]
  >> CASE_TAC
  >> rw [EXTENSION]
  >> metis_tac [NOT_NONE_SOME, SOME_11]
QED

Definition pair_set_def:
  pair_set xs = IMAGE INL xs ∪ IMAGE INR xs
End

Theorem SUBSET_pair_set:
  IMAGE OUTL x ⊆ y ∧
  IMAGE OUTR x ⊆ y
  ⇒
  x ⊆ pair_set y
Proof
  rw[pair_set_def,SUBSET_DEF,PULL_EXISTS]>>
  first_x_assum drule_all>>
  first_x_assum drule_all>>
  rename1`xx ∈ _`>>
  Cases_on`xx`>>rw[]
QED

(*
Theorem xeval_lit_flip:
  xeval_lit ss xaig (v,¬b) ⇔ ¬xeval_lit ss xaig (v,b)
Proof
  once_rewrite_tac [xeval_lit_def] >> CASE_TAC >> metis_tac []
QED

Theorem xeval_lit_not:
  xeval_lit ss xaig (not x) ⇔ ¬xeval_lit ss xaig x
Proof
  Cases_on ‘x’ >> simp [not_def, xeval_lit_flip]
QED
*)

(** Safety ********************************************************************)

Definition lits_hold_def:
  lits_hold ss (xaig: ('a, 'i, 'l) xaig) (lits: ('a,'i,'l) lit set) ⇔
    ∀lit. lit ∈ lits ⇒ xeval_lit ss xaig lit
End

Definition is_reset_def:
  is_reset ss (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (latches: 'l set) =
  ∀l lit.
    l ∈ latches ∧ reset l = SOME lit ⇒
    xeval_lit ss xaig (Base (Latch l), F) =
    xeval_lit ss xaig lit
End

Definition is_next_def:
  is_next ss₀ (xaig: ('a, 'i, 'l) xaig)
    (next: 'l -> ('a,'i,'l) lit) (latches: 'l set) ls₁ =
  ∀l. l ∈ latches ⇒ xeval_lit ss₀ xaig (next l) = ls₁ l
End

Type steps[pp] = “:num -> 'i istate # 'l lstate”

Definition is_trace_def:
  is_trace (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (steps: ('i, 'l) steps) (n: num)
  ⇔
    is_reset (steps 0) xaig reset latches ∧
    lits_hold (steps 0) xaig cnstrs ∧
    (∀i. i < n ⇒
       is_next (steps i) xaig next latches (SND (steps (i + 1))) ∧
       lits_hold (steps (i + 1)) xaig cnstrs)
End

Definition is_unsafe_def:
  is_unsafe (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set) (safes: ('a,'i,'l) lit set)
  =
  ∃(steps: ('i, 'l) steps) (n: num).
    is_trace xaig reset next cnstrs latches steps n ∧
    ¬lits_hold (steps n) xaig safes
End

Definition is_safe_def:
  is_safe (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (safes: ('a,'i,'l) lit set) ⇔
  ¬is_unsafe xaig reset next cnstrs latches safes
End

(** Liveness ******************************************************************)

Definition is_inf_trace_def:
  is_inf_trace (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (steps: ('i, 'l) steps)
  ⇔
    is_reset (steps 0) xaig reset latches ∧
    lits_hold (steps 0) xaig cnstrs ∧
    (∀i.
       is_next (steps i) xaig next latches (SND (steps (i + 1))) ∧
       lits_hold (steps (i + 1)) xaig cnstrs)
End

Theorem is_inf_trace_eq:
  is_inf_trace xaig reset next cnstrs latches steps ⇔
  ∀n. is_trace xaig reset next cnstrs latches steps n
Proof
  eq_tac>>
  rw[is_inf_trace_def,is_trace_def]>>
  first_x_assum(qspec_then`i+1` mp_tac)>>
  rw[]
QED

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

Definition is_live_def:
  is_live (xaig: ('a, 'i, 'l) xaig) (reset: 'l -> ('a,'i,'l) lit option)
    (next: 'l -> ('a,'i,'l) lit) (cnstrs: ('a,'i,'l) lit set)
    (qxaig: ('b, 'i + 'i, 'l + 'l) xaig)
    (live: ('b, 'i + 'i, 'l + 'l) lit set set) (latches: 'l set) =
  ∀steps.
    is_inf_trace xaig reset next cnstrs latches steps ⇒
    ∀prop. prop ∈ live ⇒
      ∃k signal.
        signal ∈ prop ∧
        (∀i. k ≤ i ⇒
             lits_hold (state_pair (steps i) (steps (i + 1))) qxaig {signal})
End

(* XAIG Dependencies ***********************************************************)

(* While state and input are defined over the entirety of (potentially infinite)
   domains, an XAIG can only depend on a finite subset of these domains, as
   we have a finite amount of gates.
   We formalize this notion in dep_xaig. *)

Definition agree_on_def:
  agree_on (inputs: 'i set) (latches: 'l set) (is', ls') (is, ls) ⇔
    (∀i. i ∈ inputs  ⇒ is' i = is i) ∧
    (∀l. l ∈ latches ⇒ ls' l = ls l)
End

Definition matching_transition_def:
  matching_transition inputs latches steps i j ⇔
    i < j ∧
    agree_on inputs latches (steps j) (steps i) ∧
    agree_on inputs latches (steps (j + 1)) (steps (i + 1))
End

(* Used Inputs ****************************************************************)

Definition bvar_inputs_def:
  (bvar_inputs (Input i) = [i]) ∧
  (bvar_inputs _         = [])
End

Definition var_inputs_def:
  (var_inputs (Base bv) = bvar_inputs bv) ∧
  (var_inputs (Gate _)  = [])
End

Definition lit_inputs_def:
  lit_inputs (v, b) = var_inputs v
End

Definition gty_inputs_def:
  gty_inputs (And xs) = FLAT (MAP lit_inputs xs) ∧
  gty_inputs (Xor x₀ x₁) =
    lit_inputs x₀ ++ lit_inputs x₁ ∧
  gty_inputs (Ite cnd thn els) =
    lit_inputs cnd ++ lit_inputs thn ++ lit_inputs els ∧
  gty_inputs (Or xs) = FLAT (MAP lit_inputs xs)
End

Definition gate_inputs_def:
  gate_inputs (_, gate : ('a,'i,'l) gty) = gty_inputs gate
End

Definition xaig_inputs_def:
  xaig_inputs (xaig: ('a,'i,'l) xaig) = FLAT (MAP gate_inputs xaig)
End

(* Used Latches ****************************************************************)

Definition bvar_latches_def:
  (bvar_latches (Latch l) = [l]) ∧
  (bvar_latches _         = [])
End

Definition var_latches_def:
  (var_latches (Base bv) = bvar_latches bv) ∧
  (var_latches (Gate _)  = [])
End

Definition lit_latches_def:
  lit_latches (v, b) = var_latches v
End

Definition gty_latches_def:
  gty_latches (And xs) = FLAT (MAP lit_latches xs) ∧
  gty_latches (Xor x₀ x₁) =
    lit_latches x₀ ++ lit_latches x₁ ∧
  gty_latches (Ite cnd thn els) =
    lit_latches cnd ++ lit_latches thn ++ lit_latches els ∧
  gty_latches (Or xs) = FLAT (MAP lit_latches xs)
End

Definition gate_latches_def:
  gate_latches (_, gate : ('a,'i,'l) gty) = gty_latches gate
End

Definition xaig_latches_def:
  xaig_latches (xaig: ('a,'i,'l) xaig) = FLAT (MAP gate_latches xaig)
End

(* Syntactic Dependencies *****************************************************)

Definition dep_xaig_def:
  dep_xaig inputs latches xaig =
  ∀n ss' ss.
    agree_on inputs latches ss' ss ⇒
    (xeval_gate ss' xaig n ⇔ xeval_gate ss xaig n)
End

Definition dep_bvar_def[simp]:
  (dep_bvar inputs latches Ff        ⇔ T) ∧
  (dep_bvar inputs latches (Input i) ⇔ i ∈ inputs) ∧
  (dep_bvar inputs latches (Latch l) ⇔ l ∈ latches)
End

Definition dep_var_def[simp]:
  (dep_var inputs latches (Gate _)  = T) ∧
  (dep_var inputs latches (Base bv) = dep_bvar inputs latches bv)
End

Definition dep_lit_def[simp]:
  dep_lit inputs latches (v, b) = dep_var inputs latches v
End

Definition dep_lits_def:
  dep_lits inputs latches (lits: ('a,'i,'l) lit set) ⇔
    ∀lit. lit ∈ lits ⇒ dep_lit inputs latches lit
End

Theorem dep_lits_INSERT:
  dep_lits inputs latches (x INSERT xs) ⇔
    dep_lits inputs latches {x} ∧ dep_lits inputs latches xs
Proof
  simp [dep_lits_def] >> metis_tac []
QED

Definition dep_latch_lit_def:
  dep_latch_lit inputs latches (latch_lit: 'l -> ('a,'i,'l) lit) latch_args ⇔
    ∀l. l ∈ latch_args ⇒ dep_lit inputs latches (latch_lit l)
End

Definition dep_reset_def:
  dep_reset inputs latches (reset: 'l -> ('a,'i,'l) lit option) latch_args ⇔
    ∀lat lit.
      lat ∈ latch_args ∧ reset lat = SOME lit ⇒
      dep_lit inputs latches lit
End

Definition dep_reset_lt_def:
  dep_reset_lt lt xaig reset latches ⇔
    ∀lat lit is ls' ls.
      lat ∈ latches ∧ reset lat = SOME lit ∧
      (∀l. l ∈ { l' | lt l' lat } ⇒ (ls' l ⇔ ls l)) ⇒
      (xeval_lit (is,ls') xaig lit ⇔ xeval_lit (is,ls) xaig lit)
End

Definition is_stratified_def:
  is_stratified lt xaig reset latches ⇔
  irreflexive lt ∧
  transitive lt ∧
  dep_reset_lt lt xaig reset latches
End

Definition patch_def:
  (patch xaig reset is (ls: 'l lstate) ([]: 'l list) = ls) ∧
  (patch xaig reset is ls (latch::rest) =
   patch xaig reset is
     (λl.
        if l = latch then
          (case reset l of
           | NONE => ls l
           | SOME lit => xeval_lit (is, ls) xaig lit)
        else ls l) rest)
End

Theorem not_mem_patch_eq:
  ∀xs ls. ¬MEM l xs ⇒ (patch xaig reset is ls xs) l = ls l
Proof
  Induct >> rw [patch_def]
QED

Theorem is_reset_insert_NONE:
  reset l = NONE ⇒
  (is_reset ss xaig reset (l INSERT ls) ⇔
     is_reset ss xaig reset ls)
Proof
  rw [is_reset_def] >> eq_tac >> rw [] >> gvs []
QED

Theorem is_reset_insert_SOME:
  reset l = SOME lit ⇒
  (is_reset ss xaig reset (l INSERT latches) ⇔
     is_reset ss xaig reset latches ∧
     (xeval_lit ss xaig (Base (Latch l),F) ⇔ xeval_lit ss xaig lit))
Proof
  rw [is_reset_def] >> eq_tac >> rw [] >> gvs []
QED

Theorem is_reset_union:
  is_reset ss xaig reset (xs ∪ ys) ⇔
    is_reset ss xaig reset xs ∧ is_reset ss xaig reset ys
Proof
  rw [is_reset_def] >> metis_tac []
QED

Definition no_inversions_def:
  (no_inversions R [] ⇔ T) ∧
  (no_inversions R (x::rest) ⇔
      (∀y. MEM y rest ⇒ ¬R y x) ∧ no_inversions R rest)
End

Theorem subset_is_reset_patch:
  ∀xs ls.
    dep_reset_lt lt xaig reset latches ∧ set xs ⊆ latches ∧
    no_inversions lt xs ∧ ALL_DISTINCT xs ∧ irreflexive lt
    ⇒
    is_reset (is, patch xaig reset is ls xs) xaig reset (set xs)
Proof
  Induct >> rw [patch_def]
  >- simp [is_reset_def]
  >> rename1 ‘reset lat’
  >> namedCases_on ‘reset lat’ ["", "lit"] >> gvs []
  >-
   (simp [Req0 is_reset_insert_NONE]
    >> last_x_assum irule
    >> fs [no_inversions_def])
  >> drule_then assume_tac is_reset_insert_SOME
  >> simp []
  >> conj_tac
  >- (last_x_assum irule >> fs [no_inversions_def])
  >> simp [xeval_lit_def]
  >> rename1 ‘l::xs’
  >> drule_then assume_tac not_mem_patch_eq >> simp []
  >> fs [dep_reset_lt_def]
  >> qmatch_goalsub_abbrev_tac ‘_ ⇔ xeval_lit (is, ls') _ _’
  >> last_x_assum $ qspecl_then [‘l’, ‘lit’, ‘is’, ‘ls'’, ‘ls’] mp_tac
  >> sg ‘∀l'. lt l' l ⇒ (ls' l' ⇔ ls l')’
  >-
   (rw []
    >> Cases_on ‘l' = l’
    >- gvs [irreflexive_def]
    >> simp [Abbr ‘ls'’]
    >> sg ‘¬MEM l' xs’
    >- (CCONTR_TAC >> gvs [no_inversions_def])
    >> drule_then assume_tac not_mem_patch_eq >> simp [])
  >> simp []
QED

Theorem dep_xeval_lit_eq:
  ∀n ss' ss.
    dep_xaig inputs latches xaig ∧
    dep_lit inputs latches n ∧
    agree_on inputs latches ss' ss ⇒
    (xeval_lit ss' xaig n ⇔ xeval_lit ss xaig n)
Proof
  namedCases ["v b"]
  >> namedCases ["is' ls'"]
  >> namedCases ["is ls"]
  >> Cases_on ‘v’ >> rw [xeval_lit_def]
  >-
   (fs [dep_xaig_def]
    >> rename1 ‘xeval_gate _ _ a’
    >> last_x_assum drule >> simp [])
  >> rename1 ‘eval_bvar _ b₁’
  >> Cases_on ‘b₁’
  >> fs [eval_bvar_def, agree_on_def]
QED

Theorem agree_on_union:
  agree_on (xs₀ ∪ xs₁) (ys₀ ∪ ys₁) ss' ss ⇔
  agree_on xs₀ ys₀ ss' ss ∧ agree_on xs₁ ys₁ ss' ss
Proof
  Cases_on ‘ss'’ >> Cases_on ‘ss’ >> simp [agree_on_def]
  >> metis_tac []
QED

Theorem xaig_inputs_cons:
  xaig_inputs (h::xaig) = gate_inputs h ++ xaig_inputs xaig
Proof
  simp [xaig_inputs_def]
QED

Theorem xaig_latches_cons:
  xaig_latches (h::xaig) = gate_latches h ++ xaig_latches xaig
Proof
  simp [xaig_latches_def]
QED

Theorem agree_on_weaken:
  agree_on inputs latches ss' ss ∧
  inputs' ⊆ inputs ∧
  latches' ⊆ latches
  ⇒
  agree_on inputs' latches' ss' ss
Proof
  Cases_on ‘ss'’ >> Cases_on ‘ss’ >> rw [agree_on_def, SUBSET_DEF]
QED

Theorem dep_xaig_subset:
  dep_xaig xs ys xaig ∧ xs ⊆ xs' ∧ ys ⊆ ys'
  ⇒
  dep_xaig xs' ys' xaig
Proof
  rw [dep_xaig_def] >> metis_tac [agree_on_weaken]
QED

Theorem dep_lit_subset:
  dep_lit xs ys l ∧ xs ⊆ xs' ∧ ys ⊆ ys'
  ⇒
  dep_lit xs' ys' l
Proof
  namedCases_on ‘l’ ["b v"] >> simp [dep_lit_def]
  >> namedCases_on ‘b’ ["n", "bv"] >> simp [dep_var_def]
  >> Cases_on ‘bv’ >> simp [dep_bvar_def]
  >> metis_tac [SUBSET_DEF]
QED

Theorem dep_lit_gty:
  MEM lit (get_lits ls) ⇒
  dep_lit (set (gty_inputs ls)) (set (gty_latches ls)) lit
Proof
  namedCases_on ‘lit’ ["b v"] >> simp [dep_lit_def]
  >> namedCases_on ‘b’ ["n", "bv"] >> simp [dep_var_def]
  >> Cases_on ‘bv’ >> simp [dep_bvar_def]
  >> Cases_on ‘ls’
  >> rw [gty_inputs_def, gty_latches_def,
         MEM_FLAT, MEM_MAP, PULL_EXISTS]
  >> simp [lit_inputs_def, var_inputs_def, bvar_inputs_def,
           lit_latches_def, var_latches_def, bvar_latches_def]
  >> first_assum $ irule_at Any
  >> simp [lit_inputs_def, var_inputs_def, bvar_inputs_def,
           lit_latches_def, var_latches_def, bvar_latches_def]
QED

Theorem dep_xaig_inputs_latches:
  dep_xaig (set (xaig_inputs xaig)) (set (xaig_latches xaig)) xaig
Proof
  Induct_on ‘xaig’ >- simp [dep_xaig_def]
  >> rw [dep_xaig_def]
  >> fs [xaig_inputs_cons, xaig_latches_cons]
  >> rename1 ‘h::_’ >> namedCases_on ‘h’ ["n ls"]
  >> gvs [xeval_lit_def, gate_inputs_def, gate_latches_def]
  >> reverse IF_CASES_TAC >> gvs []
  >- (
    fs [dep_xaig_def]
    >> first_assum irule
    >> fs [agree_on_union]
  )
  >> have
       ‘∀lit. MEM lit (get_lits ls) ⇒
          (xeval_lit ss' xaig lit ⇔ xeval_lit ss xaig lit)’
  >- (
    rw []
    >> irule dep_xeval_lit_eq
    >> qpat_assum ‘agree_on _ _ _ _’ $ irule_at Any
    >> irule_at (Pos hd) dep_lit_subset
    >> irule_at (Pos hd) dep_lit_gty
    >> first_assum $ irule_at (Pos hd) >> simp []
    >> irule_at (Pos hd) dep_xaig_subset
    >> first_assum $ irule_at (Pos hd) >> simp []
  )
  >> TOP_CASE_TAC >> gvs []
  >> simp [EVERY_CONG, EXISTS_CONG]
QED

(* Extending a trace for the model to a trace for the witness *****************)

Theorem agree_on_sym:
  agree_on inputs latches ss ss' = agree_on inputs latches ss' ss
Proof
  Cases_on ‘ss’ >> Cases_on ‘ss'’ >> eq_tac >> rw [agree_on_def]
QED

Definition steps_agree_def:
  steps_agree n inputs latches (steps': ('i, 'l) steps) steps ⇔
    ∀i. i ≤ n ⇒ agree_on inputs latches (steps' i) (steps i)
End

Theorem is_next_subset:
  is_next ss xaig next latches  ls ∧ latches' ⊆ latches ⇒
  is_next ss xaig next latches' ls
Proof
  rw [is_next_def] >> metis_tac [SUBSET_DEF]
QED

Theorem is_next_dep_xaig:
  is_next ss₀ xaig next latches ls₁ ∧
  (∀l. l ∈ latches' ⇒ ls₁ l = ls₁' l) ∧
  agree_on inputs latches' ss₀ ss₀' ∧
  dep_xaig inputs latches' xaig ∧
  dep_latch_lit inputs latches' next latches ∧
  latches ⊆ latches'
  ⇒
  is_next ss₀' xaig next latches ls₁'
Proof
  rw [is_next_def, dep_latch_lit_def]
  >> fs[SUBSET_DEF]
  >> metis_tac [dep_xeval_lit_eq]
QED

Theorem lits_hold_dep_xaig:
  lits_hold ss xaig lits ∧
  dep_xaig inputs latches xaig ∧
  dep_lits inputs latches lits ∧
  agree_on inputs latches ss ss'
  ⇒
  lits_hold ss' xaig lits
Proof
  rw [lits_hold_def, dep_lits_def]
  >> metis_tac [dep_xeval_lit_eq]
QED

Theorem is_reset_dep_xaig:
  is_reset ss xaig reset latches ∧
  dep_xaig inputs latches xaig ∧
  dep_reset inputs latches reset latches ∧
  agree_on inputs latches ss ss'
  ⇒
  is_reset ss' xaig reset latches
Proof
  rw [is_reset_def, dep_reset_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> last_x_assum $ drule_then assume_tac
  >> gvs [xeval_lit_def]
  >> metis_tac [dep_xeval_lit_eq, agree_on_def]
QED

Theorem is_trace_dep_xaig:
  is_trace xaig reset next cnstrs latches steps n ∧
  dep_xaig inputs latches xaig ∧
  dep_lits inputs latches cnstrs ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  steps_agree n inputs latches steps' steps
  ⇒
  is_trace xaig reset next cnstrs latches steps' n
Proof
  rw [steps_agree_def, is_trace_def, agree_on_sym]
  >-
   (irule is_reset_dep_xaig >> simp []
    >> last_assum $ irule_at (Pos last)
    >> last_assum $ irule_at (Pos last)
    >> gvs [])
  >-
   (irule lits_hold_dep_xaig >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp [])
  >-
   (last_x_assum $ drule_then assume_tac
    >> irule is_next_dep_xaig >> fs []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> rename1 ‘SND (steps (i + 1))’
    >> Cases_on ‘steps (i + 1)’ >> Cases_on ‘steps' (i + 1)’ >> fs []
    >> first_x_assum $ qspec_then ‘i + 1’ mp_tac
    >> simp [agree_on_def])
  >> last_x_assum $ drule_then assume_tac
  >> irule lits_hold_dep_xaig >> fs []
  >> first_assum $ irule_at (Pos last) >> simp []
QED

Theorem is_inf_trace_dep_xaig:
  is_inf_trace xaig reset next cnstrs latches steps ∧
  dep_xaig inputs latches xaig ∧
  dep_lits inputs latches cnstrs ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  (∀n. steps_agree n inputs latches steps' steps)
  ⇒
  is_inf_trace xaig reset next cnstrs latches steps'
Proof
  rw [is_inf_trace_eq] >> metis_tac[is_trace_dep_xaig]
QED


Theorem is_trace_lits_hold_n:
  is_trace xaig reset next cnstrs latches steps n
  ⇒
  lits_hold (steps n) xaig cnstrs
Proof
  rw [is_trace_def] >> Cases_on ‘n’ >> fs [ADD1]
QED

Theorem is_trace_SUC:
  is_trace mxaig mreset mnext mcnstrs mlatches steps (SUC n)
  ⇔
  is_trace mxaig mreset mnext mcnstrs mlatches steps n ∧
  is_next (steps n) mxaig mnext mlatches (SND (steps (n + 1))) ∧
  lits_hold (steps (n + 1)) mxaig mcnstrs
Proof
  eq_tac >> rw [is_trace_def]
  >> rename1 ‘i < SUC n’ >> Cases_on ‘i < n’ >> gvs []
  >> ‘i = n’ by simp []
  >> simp []
QED

Theorem steps_agree_SUC:
  steps_agree (SUC n) inputs latches steps' steps ⇔
    steps_agree n inputs latches steps' steps ∧
    agree_on inputs latches (steps' (n + 1)) (steps (n + 1))
Proof
  eq_tac >> rw [steps_agree_def]
  >> rename1 ‘i ≤ SUC n’
  >> Cases_on ‘i ≤ n’
  >> Cases_on ‘steps' i’ >> Cases_on ‘steps i’
  >> Cases_on ‘steps' (n + 1)’ >> Cases_on ‘steps (n + 1)’
  >- (last_x_assum drule >> gvs [])
  >> ‘i = n + 1’ by simp []
  >> gvs []
QED

Theorem is_reset_dep_latch_lit:
  is_reset ss xaig reset latches ∧
  dep_xaig inputs latches xaig ∧
  dep_reset inputs latches reset latches ∧
  agree_on inputs latches ss ss'
  ⇒
  is_reset ss' xaig reset latches
Proof
  rw [is_reset_def, dep_reset_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> gvs[xeval_lit_def]
  >> metis_tac [dep_xeval_lit_eq, agree_on_def]
QED

Definition dep_qxaig_def:
  dep_qxaig inputs qxaig live latches ⇔
    dep_xaig (pair_set inputs) (pair_set latches) qxaig ∧
    dep_lits (pair_set inputs) (pair_set latches) (set (FLAT live))
End

Theorem is_safe_is_inf_trace_lits_hold:
  is_safe xaig reset next cnstrs latches safes ∧
  is_inf_trace xaig reset next cnstrs latches steps
  ⇒
  ∀n. lits_hold (steps n) xaig safes
Proof
  rw [is_safe_def, is_unsafe_def, is_inf_trace_eq]
  >> metis_tac []
QED

Theorem is_inf_trace_cnstrs_hold:
  is_inf_trace xaig reset next cnstrs latches steps
  ⇒
  ∀n. lits_hold (steps n) xaig cnstrs
Proof
  rw [is_inf_trace_def] >> Cases_on ‘n’ >> gvs [ADD1]
QED

Theorem is_inf_trace_is_next:
  is_inf_trace xaig reset next cnstrs latches steps
  ⇒
  ∀n. is_next (steps n) xaig next latches (SND (steps (n + 1)))
Proof
  rw [is_inf_trace_def]
QED

Theorem agree_on_pair:
  agree_on (pair_set inputs) (pair_set latches)
    (state_pair ss₀ ss₁) (state_pair ss₂ ss₃)
  ⇔
  (agree_on inputs latches ss₀ ss₂ ∧ agree_on inputs latches ss₁ ss₃)
Proof
  map_every PairCases_on [‘ss₀’, ‘ss₁’, ‘ss₂’, ‘ss₃’]
  >> rw [state_pair_def, agree_on_def, pair_set_def]
  >> metis_tac [sum_case_def]
QED

Theorem agree_on_refl[simp]:
  agree_on inputs latches ss ss
Proof
  Cases_on ‘ss’ >> simp [agree_on_def]
QED

(* TODO Wouldn't this be better called _subset? *)
Theorem dep_latch_lit_next:
  BIGUNION (IMAGE (set ∘ lit_latches ∘ next) latches) ⊆ latches' ∧
  BIGUNION (IMAGE (set ∘ lit_inputs ∘ next) latches) ⊆ inputs' ⇒
  dep_latch_lit inputs' latches' next latches
Proof
  rw[dep_latch_lit_def,SUBSET_DEF,PULL_EXISTS]>>
  first_x_assum (drule_at Any)>>
  first_x_assum (drule_at Any)>>
  Cases_on`next l`>>rw[lit_latches_def,lit_inputs_def]>>
  Cases_on`q`>>fs[var_latches_def,var_inputs_def]>>
  Cases_on`b`>>gvs[bvar_latches_def,bvar_inputs_def]
QED

Theorem dep_reset_subset:
  BIGUNION (IMAGE (set ∘ lit_latches) (IMAGE_PARTIAL reset latches)) ⊆ latches' ∧
  BIGUNION (IMAGE (set ∘ lit_inputs)  (IMAGE_PARTIAL reset latches)) ⊆ inputs' ⇒
  dep_reset inputs' latches' reset latches
Proof
  rw [dep_reset_def, IMAGE_PARTIAL_DEF, SUBSET_DEF, PULL_EXISTS]
  >> first_x_assum (drule_at Any)
  >> first_x_assum (drule_at Any)
  >> rename1 ‘dep_lit _ _ lit’
  >> namedCases_on ‘lit’ ["v b"]
  >> namedCases_on ‘v’ ["n", "b'"] >> simp [dep_lit_def, dep_var_def]
  >> Cases_on ‘b'’ >> simp [dep_bvar_def]
  >> simp [lit_inputs_def, var_inputs_def, bvar_inputs_def]
  >> simp [lit_latches_def, var_latches_def, bvar_latches_def]
QED

(* TODO Wouldn't this be better called _subset? *)
Theorem dep_lits_lits:
  BIGUNION (IMAGE (set ∘ lit_latches) lits) ⊆ latches' ∧
  BIGUNION (IMAGE (set ∘ lit_inputs) lits) ⊆ inputs' ⇒
  dep_lits inputs' latches' lits
Proof
  rw[dep_lits_def,SUBSET_DEF,PULL_EXISTS]>>
  first_x_assum (drule_at Any)>>
  first_x_assum (drule_at Any)>>
  Cases_on`lit`>>rw[lit_latches_def,lit_inputs_def]>>
  Cases_on`q`>>fs[var_latches_def,var_inputs_def]>>
  Cases_on`b`>>gvs[bvar_latches_def,bvar_inputs_def]
QED

Theorem is_inf_trace_steps_agree:
  (∀n.
     is_trace mxaig mreset mnext mcnstrs mlatches steps n ⇒
     is_trace wxaig wreset wnext wcnstrs wlatches steps' n ∧
     steps_agree n UNIV mlatches steps' steps)
  ⇒
    (is_inf_trace mxaig mreset mnext mcnstrs mlatches steps ⇒
     is_inf_trace wxaig wreset wnext wcnstrs wlatches steps' ∧
     (∀n. steps_agree n UNIV mlatches steps' steps))
Proof
  rw [is_inf_trace_eq]
QED

Definition restrict_ss_def:
  restrict_ss (inputs : 'i set) (latches : 'l set)
              ((is, ls) : 'i istate # 'l lstate) =
    ({i | i ∈ inputs ∧ is i}, {l | l ∈ latches ∧ ls l})
End

Theorem FST_restrict_ss_in_POW[simp]:
  FST (restrict_ss inputs latches ss) ∈ POW inputs
Proof
  Cases_on ‘ss’ >> rw [restrict_ss_def, IN_POW, SUBSET_DEF]
QED

Theorem SND_restrict_ss_in_POW[simp]:
  SND (restrict_ss inputs latches ss) ∈ POW latches
Proof
  Cases_on ‘ss’ >> rw [restrict_ss_def, IN_POW, SUBSET_DEF]
QED

Theorem agree_on_iff_restrict_ss_eq:
  agree_on inputs latches ss ss' ⇔
  restrict_ss inputs latches ss = restrict_ss inputs latches ss'
Proof
  map_every Cases_on [‘ss’, ‘ss'’]
  >> rw [agree_on_def, restrict_ss_def, EXTENSION]
  >> metis_tac []
QED

Theorem pigeonhole_recurrence:
  FINITE A ∧ (∀n. f n ∈ A) ⇒
  ∃k. ∀i. k < i ⇒ ∃j. i < j ∧ f j = f i
Proof
  strip_tac
  >> qabbrev_tac ‘nonRec = {i | ∀j. i < j ⇒ f j ≠ f i}’
  >> ‘INJ f nonRec A’ by (
       rw [INJ_DEF, Abbr ‘nonRec’]
       >> Cases_on ‘x = y’ >- simp []
       >> ‘x < y ∨ y < x’ by simp []
       >> metis_tac [])
  >> ‘FINITE nonRec’ by metis_tac [FINITE_INJ]
  >> qexists ‘MAX_SET nonRec’ >> rw []
  >> ‘i ∉ nonRec’ by (
       CCONTR_TAC >> fs []
       >> ‘i ≤ MAX_SET nonRec’ by metis_tac [in_max_set]
       >> gvs [])
  >> fs [Abbr ‘nonRec’] >> metis_tac []
QED

Theorem matching_transition_exists:
  ∀inputs latches steps.
    FINITE inputs ∧ FINITE latches ⇒
    ∃k. ∀i. k < i ⇒
      ∃j. matching_transition inputs latches (steps: ('i, 'l) steps) i j
Proof
  rw []
  >> qabbrev_tac ‘g = λi.
       (restrict_ss inputs latches (steps i),
        restrict_ss inputs latches (steps (i + 1)))’
  >> ‘∀n. g n ∈ (POW inputs × POW latches) × (POW inputs × POW latches)’
    by simp [Abbr ‘g’]
  >> ‘FINITE ((POW inputs × POW latches) × (POW inputs × POW latches))’
    by simp []
  >> drule_all pigeonhole_recurrence >> rw []
  >> qexists ‘k’ >> rw []
  >> first_x_assum drule >> rw []
  >> qexists ‘j’
  >> fs [matching_transition_def, Abbr ‘g’, agree_on_iff_restrict_ss_eq]
QED

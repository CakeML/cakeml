(*
  Formalization of HWMCC certificates
*)
Theory xaig_cert
Ancestors
  aig xaig
Libs
  preamble

(* TODO Add references to papers *)

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


(* xAIG Dependencies ***********************************************************)

(* While state and input are defined over the entirety of (potentially infinite)
   domains, an xAIG can only depend on a finite subset of these domains, as
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

Theorem xis_reset_insert_NONE:
  reset l = NONE ⇒
  (xis_reset ss xaig reset (l INSERT ls) ⇔
     xis_reset ss xaig reset ls)
Proof
  rw [xis_reset_def] >> eq_tac >> rw [] >> gvs []
QED

Theorem xis_reset_insert_SOME:
  reset l = SOME lit ⇒
  (xis_reset ss xaig reset (l INSERT latches) ⇔
     xis_reset ss xaig reset latches ∧
     (xeval_lit ss xaig (Base (Latch l),F) ⇔ xeval_lit ss xaig lit))
Proof
  rw [xis_reset_def] >> eq_tac >> rw [] >> gvs []
QED

Theorem xis_reset_union:
  xis_reset ss xaig reset (xs ∪ ys) ⇔
    xis_reset ss xaig reset xs ∧ xis_reset ss xaig reset ys
Proof
  rw [xis_reset_def] >> metis_tac []
QED

Definition no_inversions_def:
  (no_inversions R [] ⇔ T) ∧
  (no_inversions R (x::rest) ⇔
      (∀y. MEM y rest ⇒ ¬R y x) ∧ no_inversions R rest)
End

Theorem subset_xis_reset_patch:
  ∀xs ls.
    dep_reset_lt lt xaig reset latches ∧ set xs ⊆ latches ∧
    no_inversions lt xs ∧ ALL_DISTINCT xs ∧ irreflexive lt
    ⇒
    xis_reset (is, patch xaig reset is ls xs) xaig reset (set xs)
Proof
  Induct >> rw [patch_def]
  >- simp [xis_reset_def]
  >> rename1 ‘reset lat’
  >> namedCases_on ‘reset lat’ ["", "lit"] >> gvs []
  >-
   (simp [Req0 xis_reset_insert_NONE]
    >> last_x_assum irule
    >> fs [no_inversions_def])
  >> drule_then assume_tac xis_reset_insert_SOME
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

Theorem xis_next_subset:
  xis_next ss xaig next latches  ls ∧ latches' ⊆ latches ⇒
  xis_next ss xaig next latches' ls
Proof
  rw [xis_next_def] >> metis_tac [SUBSET_DEF]
QED

Theorem xis_next_dep_xaig:
  xis_next ss₀ xaig next latches ls₁ ∧
  (∀l. l ∈ latches' ⇒ ls₁ l = ls₁' l) ∧
  agree_on inputs latches' ss₀ ss₀' ∧
  dep_xaig inputs latches' xaig ∧
  dep_latch_lit inputs latches' next latches ∧
  latches ⊆ latches'
  ⇒
  xis_next ss₀' xaig next latches ls₁'
Proof
  rw [xis_next_def, dep_latch_lit_def]
  >> fs[SUBSET_DEF]
  >> metis_tac [dep_xeval_lit_eq]
QED

Theorem xlits_hold_dep_xaig:
  xlits_hold ss xaig lits ∧
  dep_xaig inputs latches xaig ∧
  dep_lits inputs latches lits ∧
  agree_on inputs latches ss ss'
  ⇒
  xlits_hold ss' xaig lits
Proof
  rw [xlits_hold_def, dep_lits_def]
  >> metis_tac [dep_xeval_lit_eq]
QED

Theorem xis_reset_dep_xaig:
  xis_reset ss xaig reset latches ∧
  dep_xaig inputs latches xaig ∧
  dep_reset inputs latches reset latches ∧
  agree_on inputs latches ss ss'
  ⇒
  xis_reset ss' xaig reset latches
Proof
  rw [xis_reset_def, dep_reset_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> last_x_assum $ drule_then assume_tac
  >> gvs [xeval_lit_def]
  >> metis_tac [dep_xeval_lit_eq, agree_on_def]
QED

Theorem xis_trace_dep_xaig:
  xis_trace xaig reset next cnstrs latches steps n ∧
  dep_xaig inputs latches xaig ∧
  dep_lits inputs latches cnstrs ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  steps_agree n inputs latches steps' steps
  ⇒
  xis_trace xaig reset next cnstrs latches steps' n
Proof
  rw [steps_agree_def, xis_trace_def, agree_on_sym]
  >-
   (irule xis_reset_dep_xaig >> simp []
    >> last_assum $ irule_at (Pos last)
    >> last_assum $ irule_at (Pos last)
    >> gvs [])
  >-
   (irule xlits_hold_dep_xaig >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp [])
  >-
   (last_x_assum $ drule_then assume_tac
    >> irule xis_next_dep_xaig >> fs []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> rename1 ‘SND (steps (i + 1))’
    >> Cases_on ‘steps (i + 1)’ >> Cases_on ‘steps' (i + 1)’ >> fs []
    >> first_x_assum $ qspec_then ‘i + 1’ mp_tac
    >> simp [agree_on_def])
  >> last_x_assum $ drule_then assume_tac
  >> irule xlits_hold_dep_xaig >> fs []
  >> first_assum $ irule_at (Pos last) >> simp []
QED

Theorem xis_inf_trace_dep_xaig:
  xis_inf_trace xaig reset next cnstrs latches steps ∧
  dep_xaig inputs latches xaig ∧
  dep_lits inputs latches cnstrs ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  (∀n. steps_agree n inputs latches steps' steps)
  ⇒
  xis_inf_trace xaig reset next cnstrs latches steps'
Proof
  rw [xis_inf_trace_eq] >> metis_tac[xis_trace_dep_xaig]
QED


Theorem xis_trace_xlits_hold_n:
  xis_trace xaig reset next cnstrs latches steps n
  ⇒
  xlits_hold (steps n) xaig cnstrs
Proof
  rw [xis_trace_def] >> Cases_on ‘n’ >> fs [ADD1]
QED

Theorem xis_trace_SUC:
  xis_trace mxaig mreset mnext mcnstrs mlatches steps (SUC n)
  ⇔
  xis_trace mxaig mreset mnext mcnstrs mlatches steps n ∧
  xis_next (steps n) mxaig mnext mlatches (SND (steps (n + 1))) ∧
  xlits_hold (steps (n + 1)) mxaig mcnstrs
Proof
  eq_tac >> rw [xis_trace_def]
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

Theorem xis_reset_dep_latch_lit:
  xis_reset ss xaig reset latches ∧
  dep_xaig inputs latches xaig ∧
  dep_reset inputs latches reset latches ∧
  agree_on inputs latches ss ss'
  ⇒
  xis_reset ss' xaig reset latches
Proof
  rw [xis_reset_def, dep_reset_def]
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

Theorem xis_safe_xis_inf_trace_xlits_hold:
  xis_safe xaig reset next cnstrs latches safes ∧
  xis_inf_trace xaig reset next cnstrs latches steps
  ⇒
  ∀n. xlits_hold (steps n) xaig safes
Proof
  rw [xis_safe_def, xis_unsafe_def, xis_inf_trace_eq]
  >> metis_tac []
QED

Theorem xis_inf_trace_cnstrs_hold:
  xis_inf_trace xaig reset next cnstrs latches steps
  ⇒
  ∀n. xlits_hold (steps n) xaig cnstrs
Proof
  rw [xis_inf_trace_def] >> Cases_on ‘n’ >> gvs [ADD1]
QED

Theorem xis_inf_trace_xis_next:
  xis_inf_trace xaig reset next cnstrs latches steps
  ⇒
  ∀n. xis_next (steps n) xaig next latches (SND (steps (n + 1)))
Proof
  rw [xis_inf_trace_def]
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

Theorem xis_inf_trace_steps_agree:
  (∀n.
     xis_trace mxaig mreset mnext mcnstrs mlatches steps n ⇒
     xis_trace wxaig wreset wnext wcnstrs wlatches steps' n ∧
     steps_agree n UNIV mlatches steps' steps)
  ⇒
    (xis_inf_trace mxaig mreset mnext mcnstrs mlatches steps ⇒
     xis_inf_trace wxaig wreset wnext wcnstrs wlatches steps' ∧
     (∀n. steps_agree n UNIV mlatches steps' steps))
Proof
  rw [xis_inf_trace_eq]
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

(* Soundness ******************************************************************)

Definition signal_imply_def:
  signal_imply ss xaig ss' xaig' signals signals' =
  LIST_REL (λq q'. xeval_lit ss xaig q ⇒  xeval_lit ss' xaig' q')
    signals signals'
End

Definition lives_imply_def:
  lives_imply ss₀ ss₁ wqxaig mqxaig wlive mlive =
  LIST_REL (λQ Q'. signal_imply ss₀ wqxaig ss₁ mqxaig Q Q') wlive mlive
End

Definition some_signal_holds_def:
  some_signal_holds ss xaig signals =
  EXISTS (λp.  xeval_lit ss xaig p) signals
End

Definition lives_hold_def:
  lives_hold ss xaig live = EVERY (some_signal_holds ss xaig) live
End

(* TODO Use records for circuit *)

(* NOTE We use R{L} and F{L} on the left-hand side of implications
   instead of R{K} and F{K}, allowing us to prove soundness a bit easier. *)

Definition reset_cond_def:
  reset_cond
    mxaig mreset mcnstrs mlatches
    wxaig wreset wcnstrs wlatches
  ⇔
  ∀ss.
    (xis_reset ss mxaig mreset mlatches ∧
     xlits_hold ss mxaig mcnstrs
     ⇒
     xis_reset ss wxaig wreset (mlatches ∩ wlatches) ∧
     xlits_hold ss wxaig wcnstrs)
End

Definition transition_cond_def:
  transition_cond
    mxaig mnext mcnstrs mlatches
    wxaig wnext wcnstrs wlatches
  ⇔
  ∀ss₀ ss₁.
    (xis_next ss₀ mxaig mnext mlatches (SND ss₁) ∧
     xlits_hold ss₀ mxaig mcnstrs ∧
     xlits_hold ss₁ mxaig mcnstrs ∧
     xlits_hold ss₀ wxaig wcnstrs)
    ⇒
    (xis_next ss₀ wxaig wnext (mlatches ∩ wlatches) (SND ss₁) ∧
     xlits_hold ss₁ wxaig wcnstrs)
End

Definition safety_cond_def:
  safety_cond
    mxaig msafes mcnstrs
    wxaig wsafes wcnstrs
  ⇔
  ∀ss.
    (xlits_hold ss mxaig mcnstrs ∧
     xlits_hold ss wxaig wcnstrs) ⇒
    xlits_hold ss wxaig wsafes ⇒
    xlits_hold ss mxaig msafes
End

Definition liveness_cond_def:
  liveness_cond
    mxaig mcnstrs mqxaig mlive
    wxaig wnext wsafes wcnstrs wqxaig wlive wlatches
  ⇔
    (* This LENGTH property is not strictly necessary but makes the proof a bit
       neater *)
    LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive ∧
    ∀ss₀ ss₁.
      (xlits_hold ss₀ mxaig mcnstrs ∧
       xlits_hold ss₀ wxaig wcnstrs ∧
       xlits_hold ss₀ wxaig wsafes ∧
       xlits_hold ss₁ mxaig mcnstrs ∧
       xlits_hold ss₁ wxaig wcnstrs ∧
       xlits_hold ss₁ wxaig wsafes ∧
       xis_next ss₀ wxaig wnext wlatches (SND ss₁))
      ⇒
      lives_imply (state_pair ss₀ ss₁) (state_pair ss₀ ss₁) wqxaig mqxaig
        wlive mlive
End

Definition simulates_def:
  simulates
    mxaig mreset mnext msafes mcnstrs mqxaig mlive mlatches
    wxaig wreset wnext wsafes wcnstrs wqxaig wlive wlatches
  ⇔
  reset_cond
    mxaig mreset mcnstrs mlatches
    wxaig wreset wcnstrs wlatches
  ∧
  transition_cond
    mxaig mnext mcnstrs mlatches
    wxaig wnext wcnstrs wlatches
  ∧
  safety_cond
    mxaig msafes mcnstrs
    wxaig wsafes wcnstrs
  ∧
  liveness_cond
    mxaig mcnstrs mqxaig mlive
    wxaig wnext wsafes wcnstrs wqxaig wlive wlatches
End

Definition base_cond_def:
  base_cond
    xaig reset safes cnstrs latches
  ⇔
    ∀ss.
      (xis_reset ss xaig reset latches ∧
       xlits_hold ss xaig cnstrs)
      ⇒
      xlits_hold ss xaig safes
End

Definition induction_cond_def:
  induction_cond
    xaig next safes cnstrs latches
  ⇔
    ∀ss₀ ss₁.
      (xlits_hold ss₀ xaig safes ∧
       xis_next ss₀ xaig next latches (SND ss₁) ∧
       xlits_hold ss₀ xaig cnstrs ∧
       xlits_hold ss₁ xaig cnstrs)
      ⇒
      xlits_hold ss₁ xaig safes
End

Definition is_inductive_def:
  is_inductive
    xaig reset next safes cnstrs latches
  ⇔
    base_cond xaig reset safes cnstrs latches ∧
    induction_cond xaig next safes cnstrs latches
End

Definition decrease_cond_def:
  decrease_cond
    xaig next safes cnstrs qxaig live latches
  ⇔
    ∀ss₀ ss₁.
      (xlits_hold ss₀ xaig cnstrs ∧
       xlits_hold ss₀ xaig safes ∧
       xlits_hold ss₁ xaig cnstrs ∧
       xlits_hold ss₁ xaig safes ∧
       xis_next ss₀ xaig next latches (SND ss₁))
       ⇒
       lives_hold (state_pair ss₁ ss₀) qxaig live
End

Definition closure_cond_def:
  closure_cond
    xaig next safes cnstrs qxaig live latches
  ⇔
    ∀ss₀ ss₁ ss₂.
      (xlits_hold ss₀ xaig cnstrs ∧
       xlits_hold ss₀ xaig safes ∧
       xlits_hold ss₁ xaig cnstrs ∧
       xlits_hold ss₁ xaig safes ∧
       xlits_hold ss₂ xaig cnstrs ∧
       xlits_hold ss₂ xaig safes ∧
       xis_next ss₀ xaig next latches (SND ss₁) ∧
       lives_hold (state_pair ss₀ ss₂) qxaig live)
      ⇒
      lives_hold (state_pair ss₁ ss₂) qxaig live
End

Definition stable_cond_def:
  stable_cond
    xaig next safes cnstrs qxaig live latches
  ⇔
    ∀ss₀ ss₁ ss₂.
      (xlits_hold ss₀ xaig cnstrs ∧
       xlits_hold ss₀ xaig safes ∧
       xlits_hold ss₁ xaig cnstrs ∧
       xlits_hold ss₁ xaig safes ∧
       xlits_hold ss₂ xaig cnstrs ∧
       xlits_hold ss₂ xaig safes ∧
       xis_next ss₀ xaig next latches (SND ss₁) ∧
       xis_next ss₁ xaig next latches (SND ss₂) ∧
       lives_hold (state_pair ss₀ ss₁) qxaig live ∧
       lives_hold (state_pair ss₁ ss₂) qxaig live)
       ⇒
       lives_imply (state_pair ss₀ ss₁) (state_pair ss₁ ss₂) qxaig qxaig
         live live
End

Definition is_ranked_def:
  is_ranked
    wxaig wnext wsafes wcnstrs wqxaig wlive wlatches
  ⇔
  decrease_cond
    wxaig wnext wsafes wcnstrs wqxaig wlive wlatches
  ∧
  closure_cond
    wxaig wnext wsafes wcnstrs wqxaig wlive wlatches
  ∧
  stable_cond
    wxaig wnext wsafes wcnstrs wqxaig wlive wlatches
End

Definition is_witness_def:
  is_witness
    mxaig mreset mnext msafes mcnstrs mqxaig mlive mlatches
    wxaig wreset wnext wsafes wcnstrs wqxaig wlive wlatches
  ⇔
  simulates
    mxaig mreset mnext msafes mcnstrs mqxaig mlive mlatches
    wxaig wreset wnext wsafes wcnstrs wqxaig wlive wlatches
  ∧
  is_inductive
    wxaig wreset wnext wsafes wcnstrs wlatches
  ∧
  is_ranked
    wxaig wnext wsafes wcnstrs wqxaig wlive wlatches
End

(* To show that we can find a state where the reset functions are all satisfied,
   we construct a topological order that we can pass to patch. *)

Definition is_minimal_def:
  is_minimal R s x ⇔ x ∈ s ∧ ∀y. y ∈ s ⇒ ¬R y x
End

Definition topo_sort_def:
  topo_sort R s =
  if FINITE s ∧ ∃x. is_minimal R s x then
    let m = @x. is_minimal R s x in
      m :: topo_sort R (s DELETE m)
  else []
Termination
  wf_rel_tac ‘measure (CARD ∘ SND)’ >> rw []
  >-
   (gvs [CARD_EQ_0, GSYM NOT_ZERO, is_minimal_def]
    >> metis_tac [MEMBER_NOT_EMPTY])
  >- metis_tac [is_minimal_def]
End

Theorem topo_sort_empty[local,simp]:
  topo_sort R ∅ = []
Proof
  simp [Once topo_sort_def, is_minimal_def]
QED

Theorem exists_is_minimal:
  irreflexive R ∧ transitive R ⇒
  FINITE s ∧ s ≠ ∅ ⇒ ∃x. is_minimal R s x
Proof
  strip_tac
  >> Induct_on ‘FINITE s’
  >> rw [is_minimal_def]
  >> Cases_on ‘s = ∅’
  >- fs [irreflexive_def]
  >> metis_tac [irreflexive_def, transitive_def]
QED

Theorem set_topo_sort_sub[local]:
  ∀R s. set (topo_sort R s) ⊆ s
Proof
  recInduct topo_sort_ind >> rw []
  >> simp [Once topo_sort_def]
  >> IF_CASES_TAC >> gvs []
  >> conj_tac
  >- metis_tac [is_minimal_def]
  >> irule SUBSET_TRANS
  >> metis_tac [DELETE_SUBSET]
QED

Theorem MEM_topo_sort[local]:
  ∀R s y. MEM y (topo_sort R s) ⇒ y ∈ s
Proof
  metis_tac [set_topo_sort_sub, SUBSET_DEF]
QED

Theorem set_topo_sort_eq[local]:
  ∀R s. irreflexive R ∧ transitive R ∧ FINITE s ⇒ set (topo_sort R s) = s
Proof
  recInduct topo_sort_ind >> rw []
  >> Cases_on ‘s = ∅’ >> gvs []
  >> simp [Once topo_sort_def]
  >> drule_all_then assume_tac exists_is_minimal >> simp []
  >> irule INSERT_DELETE
  >> metis_tac [is_minimal_def]
QED

Theorem ALL_DISTINCT_topo_sort[local]:
  ∀R s. ALL_DISTINCT (topo_sort R s)
Proof
  recInduct topo_sort_ind >> rw []
  >> simp [Once topo_sort_def]
  >> IF_CASES_TAC >> gvs []
  >> strip_tac
  >> drule MEM_topo_sort
  >> simp []
QED

Theorem no_inversions_topo_sort[local]:
  ∀R s. no_inversions R (topo_sort R s)
Proof
  recInduct topo_sort_ind >> rw []
  >> simp [Once topo_sort_def]
  >> IF_CASES_TAC >> gvs [no_inversions_def]
  >> rw []
  >> ‘is_minimal R s (@x. is_minimal R s x)’ by metis_tac [is_minimal_def]
  >> drule_then assume_tac MEM_topo_sort
  >> fs [is_minimal_def]
QED

(* Extends a trace for the model to a trace for the witness.
   This setup allows us to formulate the conclusion of
   extend_model_trace_to_witness as ∃steps'. ∀n. ... allowing us to use the lemma
   for both finite and infinite traces. *)
Definition mk_trace_def:
  (mk_trace lt mlatches wxaig wreset wnext wsafes wcnstrs wlatches steps 0 =
   let
     xs = topo_sort lt (wlatches DIFF (mlatches ∩ wlatches));
     (is, ls) = steps 0
   in
     (is, patch wxaig wreset is ls xs)) ∧
  (mk_trace lt mlatches wxaig wreset wnext wsafes wcnstrs wlatches steps (SUC n) =
   let
     prev = mk_trace lt mlatches wxaig wreset wnext wsafes wcnstrs wlatches steps n
   in
     @succ.
       xis_next prev wxaig wnext wlatches (SND succ) ∧
       xlits_hold succ wxaig wcnstrs ∧
       agree_on UNIV mlatches succ (steps (SUC n)))
End

Definition dep_model_def:
  dep_model
    xaig reset next safes cnstrs inputs latches ⇔
  dep_xaig inputs latches xaig ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  dep_lits inputs latches safes ∧
  dep_lits inputs latches cnstrs
End

Theorem agree_on_weaken_inputs[local]:
  agree_on inputs latches ss' ss ∧
  inputs' ⊆ inputs
  ⇒
  agree_on inputs' latches ss' ss
Proof
  metis_tac [SUBSET_DEF, agree_on_weaken]
QED

Theorem steps_agree_weaken_inputs[local]:
  steps_agree n inputs latches steps' steps ∧
  inputs' ⊆ inputs
  ⇒
  steps_agree n inputs' latches steps' steps
Proof
  metis_tac [steps_agree_def, agree_on_weaken_inputs]
QED

Theorem extend_model_trace_to_witness:
  dep_model mxaig mreset mnext msafes mcnstrs minputs mlatches ∧
  reset_cond
    mxaig mreset mcnstrs mlatches
    wxaig wreset wcnstrs wlatches ∧
  transition_cond
    mxaig mnext mcnstrs mlatches
    wxaig wnext wcnstrs wlatches ∧
  is_stratified lt wxaig wreset wlatches ∧
  FINITE wlatches
  ⇒
  ∃steps'. ∀n.
    xis_trace mxaig mreset mnext mcnstrs mlatches steps n ⇒
    xis_trace wxaig wreset wnext wcnstrs wlatches steps' n ∧
    steps_agree n UNIV mlatches steps' steps
Proof
  rw [dep_model_def, is_stratified_def]
  >> qexists ‘mk_trace lt mlatches wxaig wreset wnext wsafes wcnstrs wlatches steps’
  >> Induct_on ‘n’ >> strip_tac
  >-
   (fs [xis_trace_def, reset_cond_def, steps_agree_def]
    >> first_assum $ drule_all_then assume_tac
    >> namedCases_on ‘steps 0’ ["is ls"] >> fs []
    >> gvs [mk_trace_def]
    >> qmatch_goalsub_abbrev_tac ‘patch _ _ _ _ xs’
    >> sg ‘∀l. MEM l xs ⇔ l ∈ (wlatches DIFF mlatches ∩ wlatches)’
    >- (simp [Abbr ‘xs’, Req0 set_topo_sort_eq])
    >> qmatch_goalsub_abbrev_tac ‘xis_reset ss0’
    >> CONJ_TAC
      (* wlatches are in reset and wcnstrs
        are satisfied in patched state *)
    >- (
      first_x_assum (qspec_then ‘ss0’ mp_tac)
      >> impl_tac
      >- (
        CONJ_TAC
        >- (
          drule_then irule xis_reset_dep_latch_lit>>
          last_assum $ irule_at (Pos hd)>>
          simp[Abbr`ss0`, agree_on_def]>>
          rw[]>>
          irule (GSYM not_mem_patch_eq)>>
          simp[Abbr`xs`])
        >>
          drule_then irule xlits_hold_dep_xaig>>
          last_assum $ irule_at (Pos hd)>>
          simp[Abbr`ss0`, agree_on_def]>>
          rw[]>>
          irule (GSYM not_mem_patch_eq)>>
          simp[Abbr`xs`])
      >> rw[]
      >> sg ‘wlatches = (mlatches ∩ wlatches) ∪ (set xs)’
      >- (simp [Abbr ‘xs’, Req0 set_topo_sort_eq] >> SET_TAC [])
      >> pop_assum SUBST1_TAC
      >> simp [xis_reset_union,Abbr`ss0`]
      >> irule subset_xis_reset_patch
      >> first_assum $ irule_at (Pos last)
      >> simp [Abbr ‘xs’, Req0 set_topo_sort_eq, ALL_DISTINCT_topo_sort,
               no_inversions_topo_sort])
    >> simp [steps_agree_def, agree_on_def, Abbr`ss0`]
    >-
     (rw []
      >> rename1 ‘patch _ _ _ _ _ l’ >> ‘¬MEM l xs’ by simp [Abbr ‘xs’]
      >> simp [not_mem_patch_eq]))
  >> gvs [xis_trace_SUC, steps_agree_SUC]
  >> simp [GSYM ADD1, mk_trace_def]
  >> qmatch_goalsub_abbrev_tac ‘xis_next steps'n’
  >> SELECT_ELIM_TAC
  >> conj_tac
  >-
   (qabbrev_tac ‘step =
                 (FST (steps (n + 1)),
                  λl. if l ∈ mlatches then (SND (steps (n + 1))) l
                      else xeval_lit (steps'n) wxaig (wnext l))’
    >> qexists ‘step’
    >> ‘xis_next (steps'n) mxaig mnext mlatches (SND step)’ by
      (drule xis_next_dep_xaig
       >> disch_then irule
       >> qpat_x_assum ‘dep_xaig _ _ _’ $ irule_at Any
       >> gvs [steps_agree_def, agree_on_sym, Abbr ‘step’, Abbr‘steps'n’]
       >> irule agree_on_weaken_inputs
       >> first_assum $ irule_at (Pos last) >> simp [])
    >> ‘xlits_hold (steps'n) mxaig mcnstrs’ by
      (‘xlits_hold (steps n) mxaig mcnstrs’ by metis_tac [xis_trace_xlits_hold_n]
       >> drule xlits_hold_dep_xaig
       >> disch_then drule >> disch_then irule
       >> gvs [steps_agree_def, agree_on_sym, Abbr‘steps'n’]
       >> irule agree_on_weaken_inputs
       >> first_assum $ irule_at (Pos last) >> simp [])
    >> ‘xlits_hold step mxaig mcnstrs’ by
      (rev_drule xlits_hold_dep_xaig
       >> disch_then drule >> disch_then irule
       >> Cases_on ‘steps (n + 1)’
       >> gvs [agree_on_def, Abbr ‘step’])
    >> ‘xlits_hold (steps'n) wxaig wcnstrs’ by metis_tac [xis_trace_xlits_hold_n]
    (* Following the paper proof, we can now invoke the transition check
       and extend these two facts to the witness. *)
    >> fs [transition_cond_def]
    >> first_x_assum $ drule_all_then assume_tac >> fs []
    >> conj_tac
    >- (fs [xis_next_def] >> rw [] >> Cases_on ‘l ∈ mlatches’ >> gvs [Abbr ‘step’])
    >> gvs [ADD1]
    >> Cases_on ‘steps (n + 1)’
    >> fs [agree_on_def, Abbr ‘step’])
  >> rw []
QED

Theorem is_inductive_xlits_hold[local]:
  xis_trace xaig reset next cnstrs latches steps n ∧
  is_inductive
    xaig reset next safes cnstrs latches
  ⇒
  xlits_hold (steps n) xaig safes
Proof
  simp[is_inductive_def]>>
  Induct_on`n`>>rw[]
  >-
    gvs[base_cond_def,xis_trace_def]>>
  gvs[xis_trace_SUC] >>
  gvs[induction_cond_def,ADD1]>>
  first_x_assum irule>>
  rw[]>>
  first_x_assum (irule_at (Pos last))>>
  simp[]>>
  metis_tac[xis_trace_xlits_hold_n]
QED

Theorem inf_is_inductive_xlits_hold[local]:
  xis_inf_trace xaig reset next cnstrs latches steps ∧
  is_inductive
    xaig reset next safes cnstrs latches
  ⇒
  (∀n. xlits_hold (steps n) xaig safes)
Proof
  rw [xis_inf_trace_eq] >> metis_tac [is_inductive_xlits_hold]
QED

Theorem is_witness_xis_safe:
  is_witness
    mxaig mreset mnext msafes mcnstrs mqxaig mlive mlatches
    wxaig wreset wnext wsafes wcnstrs wqxaig wlive wlatches ∧
  dep_model
    mxaig mreset mnext msafes mcnstrs minputs mlatches ∧
  is_stratified lt wxaig wreset wlatches ∧
  FINITE wlatches
  ⇒
  xis_safe
    mxaig mreset mnext mcnstrs mlatches msafes
Proof
  rw [is_witness_def, xis_safe_def, simulates_def]
  >> CCONTR_TAC
  >> fs [xis_unsafe_def]
  >> pop_assum mp_tac >> simp[]
  >> rename1 ‘xlits_hold (steps _)’
  >> drule_all extend_model_trace_to_witness
  >> disch_then $ qspec_then ‘steps’ mp_tac >> rw []
  >> first_assum drule >> strip_tac
  >> drule_all is_inductive_xlits_hold
  >> strip_tac
  >> fs [dep_model_def]
  >> `xis_trace mxaig mreset mnext mcnstrs mlatches steps' n` by
    (irule xis_trace_dep_xaig >> fs []
     >> first_assum $ irule_at (Pos hd) >> simp []
     >> irule_at (Pos hd) steps_agree_weaken_inputs
     >> first_assum $ irule_at (Pos hd)
     >> simp [])
  >> drule_at_then Any irule xlits_hold_dep_xaig
  >> rename1`steps_agree n _ mlatches steps' steps`
  >> fs[steps_agree_def]
  >> qexists_tac`steps' n`
  >> conj_tac
  >-
   (gvs[safety_cond_def]
    >> first_x_assum irule
    >> gvs[]
    >> metis_tac[xis_trace_xlits_hold_n])
  >> irule agree_on_weaken_inputs
  >> first_assum $ irule_at (Pos last)
  >> simp []
QED

Theorem closure_cond_lives_hold[local]:
  ∀k.
    closure_cond
      xaig next safes cnstrs qxaig live latches ∧
    lives_hold (state_pair (steps i) (steps j)) qxaig live ∧
    (∀n. xlits_hold (steps n) xaig safes) ∧
    (∀n. xlits_hold (steps n) xaig cnstrs) ∧
    (∀n. xis_next (steps n) xaig next latches (SND (steps (n + 1))))
    ⇒
    lives_hold (state_pair (steps (i + k)) (steps j)) qxaig live
Proof
  Induct >> rw [] >> fs []
  >> fs [closure_cond_def]
  >> first_assum irule >> simp []
  >> qexists ‘steps (i + k)’ >> fs [ADD1]
  >> rewrite_tac [ADD_ASSOC] >> simp[ADD_ASSOC]
  >> first_x_assum $ qspec_then ‘i + k’ mp_tac >> simp []
QED

Theorem lives_hold_dep_xaig[local]:
  lives_hold ss xaig ns ∧
  dep_xaig inputs latches xaig ∧
  dep_lits inputs latches (set (FLAT ns)) ∧
  agree_on inputs latches ss ss'
  ⇒
  lives_hold ss' xaig ns
Proof
  rw [lives_hold_def, EVERY_MEM, dep_lits_def, some_signal_holds_def,
          EXISTS_MEM, MEM_FLAT, xlits_hold_def]
  >> metis_tac [dep_xeval_lit_eq]
QED

Theorem lives_hold_matching_transition[local]:
  lives_hold (state_pair (steps (i + 2)) (steps (i + 1))) qxaig live ∧
  matching_transition inputs latches steps i (i + 2) ∧
  dep_xaig (pair_set inputs) (pair_set latches) qxaig ∧
  dep_lits (pair_set inputs) (pair_set latches) (set (FLAT live))
  ⇒
  lives_hold (state_pair (steps i) (steps (i + 1))) qxaig live
Proof
  rw []
  >> irule lives_hold_dep_xaig
  >> qpat_x_assum ‘lives_hold _ _ _’ $ irule_at Any
  >> first_assum $ irule_at (Pos hd) >> simp []
  >> fs [agree_on_pair, matching_transition_def]
QED

Theorem matching_transition_live[local]:
  decrease_cond
    xaig next safes cnstrs qxaig live latches  ∧
  xis_inf_trace xaig reset next cnstrs latches steps ∧
  closure_cond
    xaig next safes cnstrs qxaig live latches ∧
  matching_transition inputs' latches' steps i j ∧
  set (xaig_inputs xaig) ⊆ inputs' ∧
  BIGUNION (IMAGE (set o lit_inputs o next) latches) ⊆ inputs' ∧
  set (xaig_inputs qxaig) ⊆ pair_set inputs' ∧
  BIGUNION (IMAGE (set o lit_inputs) (set (FLAT live))) ⊆ pair_set inputs' ∧
  latches ⊆ latches' ∧
  set (xaig_latches xaig) ⊆ latches' ∧
  BIGUNION (IMAGE (set o lit_latches o next) latches) ⊆ latches' ∧
  set (xaig_latches qxaig) ⊆ pair_set latches' ∧
  BIGUNION (IMAGE (set o lit_latches) (set (FLAT live))) ⊆ pair_set latches' ∧
  (∀n. xlits_hold (steps n) xaig safes)
  ⇒
  lives_hold (state_pair (steps i) (steps (i + 1))) qxaig live
Proof
  rw []
  >> drule_then assume_tac xis_inf_trace_cnstrs_hold
  >> Cases_on ‘j = i + 1’ >> gvs []
  >- (
    fs [matching_transition_def, decrease_cond_def]
    >> last_assum irule >> gvs [xis_inf_trace_def]
    >> last_x_assum $ qspec_then ‘i’ assume_tac
    >> irule xis_next_dep_xaig
    >> first_assum $ irule_at (Pos last)
    >> fs [agree_on_sym]
    >> first_assum $ irule_at (Pos (el 4)) >> simp []
    >> CONJ_TAC >-
      (Cases_on ‘steps i’ >> Cases_on ‘steps (i + 1)’
      >> fs [agree_on_def]
      >> metis_tac[])
    >> CONJ_TAC >- (
      irule dep_xaig_subset>>
      metis_tac[dep_xaig_inputs_latches])
    >>
      irule dep_latch_lit_next>>
      fs[])
  >> drule_then assume_tac xis_inf_trace_xis_next
  >> ‘lives_hold (state_pair (steps (i + 2)) (steps (i + 1))) qxaig live’ by
    (fs [decrease_cond_def]
     >> last_assum irule >> simp []
     >> first_x_assum $ qspec_then ‘i + 1’ mp_tac >> simp [])
  >> Cases_on ‘j = i + 2’ >> gvs []
  >- (
    irule lives_hold_matching_transition >> simp []
    >> qpat_x_assum ‘matching_transition _ _ _ _ _’ $ irule_at Any
    >> simp []
    >> conj_tac >- metis_tac [dep_lits_lits]
    >> irule dep_xaig_subset
    >> metis_tac [dep_xaig_inputs_latches]
  )
  >> drule_all closure_cond_lives_hold
  >> disch_then $ qspec_then ‘j - i - 2’ assume_tac
  >> gvs [matching_transition_def]
  >> irule lives_hold_dep_xaig
  >> pop_assum (irule_at Any)
  >> qexists_tac`pair_set latches'`
  >> qexists_tac`pair_set inputs'`
  >> simp [agree_on_pair]
  >> conj_tac >- metis_tac [dep_lits_lits]
  >> irule dep_xaig_subset
  >> metis_tac [dep_xaig_inputs_latches]
QED

Theorem stable_cond_xlits_hold[local]:
  stable_cond wxaig wnext wsafes wcnstrs wqxaig wlive wlatches ∧
  MEM q Q ∧ MEM Q wlive ∧
  xeval_lit (state_pair (steps j) (steps (j + 1))) wqxaig q ∧
  (∀n. xlits_hold (steps n) wxaig wcnstrs) ∧
  (∀n. xlits_hold (steps n) wxaig wsafes) ∧
  (∀n. xis_next (steps n) wxaig wnext wlatches (SND (steps (n + 1)))) ∧
  (∀i. j ≤ i ⇒
       lives_hold (state_pair (steps i) (steps (i + 1))) wqxaig wlive) ∧
  j ≤ i
  ⇒
  xeval_lit (state_pair (steps i) (steps (i + 1))) wqxaig q
Proof
  Induct_on ‘i - j’ >> rw [] >> fs []
  >- (‘i = j’ by simp [] >> simp [])
  >> last_x_assum $ qspecl_then [‘i - 1’, ‘j’] assume_tac
  >> gvs []
  >> gvs [stable_cond_def, MEM_EL]
  >> last_x_assum $ qspecl_then [‘steps (i - 1)’, ‘steps i’, ‘steps (i + 1)’] mp_tac
  >> simp []
  >> impl_tac >-
   (‘i - 1n + 1 = i’ by simp []
    >> ‘j ≤ i - 1’ by simp []
    >> metis_tac [])
  >> simp [lives_imply_def, signal_imply_def, LIST_REL_EL_EQN]
QED

Theorem xeval_lit_single_xlits_hold[local]:
  xeval_lit ss xaig lit ⇔ xlits_hold ss xaig {lit}
Proof
  simp [xlits_hold_def]
QED

Theorem is_witness_xis_live:
  is_witness
    mxaig mreset mnext msafes mcnstrs mqxaig mlive mlatches
    wxaig wreset wnext wsafes wcnstrs wqxaig wlive wlatches ∧
  dep_model
    mxaig mreset mnext msafes mcnstrs minput mlatches ∧
  (* TODO Does dep_qxaig really need the same minput?
     If not, the proof of encoding_xis_safe_and_live may become tidier *)
  dep_qxaig minput mqxaig mlive mlatches ∧
  is_stratified lt wxaig wreset wlatches ∧
  FINITE wlatches
  ⇒
  xis_live
    mxaig mreset mnext mcnstrs mqxaig (IMAGE set (set mlive)) mlatches
Proof
  rw []
  (* Get safety of model *)
  >> drule_all_then assume_tac is_witness_xis_safe
  (* Extend trace on model to trace on witness *)
  >> fs [is_witness_def, simulates_def]
  >> rw [xis_live_def]
  >> drule_all extend_model_trace_to_witness
  >> rename1 ‘xis_inf_trace _ _ _ _ _ steps’
  >> disch_then $ qspec_then ‘steps’ mp_tac >> strip_tac
  >> dxrule xis_inf_trace_steps_agree
  >> simp [] >> strip_tac
  (* Witness constraints and safety signals hold on extended trace *)
  >> ‘∀n. xlits_hold (steps' n) wxaig wsafes’ by
    metis_tac [inf_is_inductive_xlits_hold]
  >> ‘∀n. xlits_hold (steps' n) wxaig wcnstrs’ by
    metis_tac [xis_inf_trace_cnstrs_hold]
  (* Extended trace has valid steps for the witness *)
  >> ‘∀n. xis_next (steps' n) wxaig wnext wlatches (SND (steps' (n + 1)))’ by
     metis_tac [xis_inf_trace_xis_next]
  (* Extended trace is also a trace for the model *)
  >> ‘xis_inf_trace mxaig mreset mnext mcnstrs mlatches steps'’ by
    (irule xis_inf_trace_dep_xaig
     >> first_assum $ irule_at (Pos last)
     >> fs [dep_model_def]
     >> first_assum $ irule_at (Pos last)
     >> rw []
     >> irule steps_agree_weaken_inputs
     >> qexists ‘UNIV’ >> simp [])
  (* Model constraints holds on the witness *)
  >> ‘∀n. xlits_hold (steps' n) mxaig mcnstrs’ by
    metis_tac [xis_inf_trace_cnstrs_hold]
  >> qabbrev_tac`inputs' =
    set (xaig_inputs wxaig) ∪
    BIGUNION (IMAGE (set o lit_inputs o wnext) wlatches) ∪
    (IMAGE OUTL (set (xaig_inputs wqxaig)) ∪
    IMAGE OUTR (set (xaig_inputs wqxaig))) ∪
    (IMAGE OUTL (BIGUNION (IMAGE (set o lit_inputs) (set (FLAT wlive)))) ∪
    IMAGE OUTR (BIGUNION (IMAGE (set o lit_inputs) (set (FLAT wlive)))))`
  >> qabbrev_tac`latches' =
    wlatches ∪
    set (xaig_latches wxaig) ∪
    BIGUNION (IMAGE (set o lit_latches o wnext) wlatches) ∪
    (IMAGE OUTL (set (xaig_latches wqxaig)) ∪
    IMAGE OUTR (set (xaig_latches wqxaig))) ∪
    (IMAGE OUTL (BIGUNION (IMAGE (set o lit_latches) (set (FLAT wlive)))) ∪
    IMAGE OUTR (BIGUNION (IMAGE (set o lit_latches) (set (FLAT wlive)))))`
  (* Infinite trace on witness repeats from k onwards *)
  >> qspecl_then [‘inputs'’, ‘latches'’, ‘steps'’] mp_tac matching_transition_exists
  >> impl_tac >-
    (unabbrev_all_tac>>fs[is_stratified_def,PULL_EXISTS])
  >> strip_tac
  >> rename1 ‘k < _ ⇒ _’ >> qexists ‘k+1’ >> rw []
  >> rename1 ‘MEM prop mlive’
  (* Model is live if model is live on extended trace *)
  >> suff
       ‘∃signal.
          MEM signal prop ∧
            ∀i. k + 1 ≤ i ⇒
              xeval_lit (state_pair (steps' i) (steps' (i + 1))) mqxaig signal’
  >-
    (rw []
     >> qexists ‘signal’ >> rw []
     >> rewrite_tac [xeval_lit_single_xlits_hold]
     >> irule xlits_hold_dep_xaig
     >> fs [dep_qxaig_def]
     >> qpat_assum ‘dep_xaig _ _ _’ $ irule_at Any
     >> qexists ‘state_pair (steps' i) (steps' (i + 1))’
     >> simp []
     >> conj_tac
     >- (fs [dep_lits_def, MEM_FLAT] >> metis_tac [])
     >> conj_tac
     >- simp [xlits_hold_def]
     >> fs [steps_agree_def, agree_on_pair]
     >> irule_at (Pos hd) agree_on_weaken_inputs
     >> qexists ‘UNIV’ >> simp []
     >> first_assum $ irule_at (Pos hd)
     >> qexists ‘i’ >> simp []
     >> irule agree_on_weaken_inputs
     >> qexists ‘UNIV’ >> simp []
     >> first_assum $ irule_at (Pos hd)
     >> qexists ‘i+1’ >> simp [])
  >> gvs [MEM_EL, PULL_EXISTS]
  >> ‘LENGTH wlive = LENGTH mlive ∧
      ∀n. n < LENGTH wlive ⇒ LENGTH wlive❲n❳ = LENGTH mlive❲n❳’ by
    (fs [liveness_cond_def, LIST_REL_EL_EQN])
  >> suff
     ‘∃n'. n' < LENGTH wlive❲n❳ ∧
        ∀i. k + 1 ≤ i ⇒
          xeval_lit (state_pair (steps' i) (steps' (i + 1))) wqxaig wlive❲n❳❲n'❳’
  >- (
    rw []
    >> qexists ‘n'’
    >> gvs []
    >> rw []
    >> gvs [liveness_cond_def, lives_imply_def, signal_imply_def,
            LIST_REL_EL_EQN, PULL_FORALL])
  (* Witness is live *)
  >> fs [is_ranked_def]
  >> have
       ‘∀i. k + 1 ≤ i ⇒
            lives_hold (state_pair (steps' i) (steps' (i + 1))) wqxaig wlive’
  >-
    (rw []
     >> drule matching_transition_live >> simp []
     >> disch_then drule
     >> disch_then irule >> simp []
     >> qpat_x_assum ‘∀_. _ ⇒ ∃_. matching_transition _ _ _ _ _’ $
          qspec_then `i` mp_tac
     >> rw []
     >> pop_assum (irule_at Any)
     >> unabbrev_all_tac
     >> irule_at Any SUBSET_pair_set
     >> irule_at Any SUBSET_pair_set
     >> irule_at Any SUBSET_pair_set
     >> irule_at Any SUBSET_pair_set
     >> metis_tac[SUBSET_UNION,UNION_ASSOC,UNION_COMM])
  >> drule stable_cond_xlits_hold
  >> disch_then $ drule_at Any >> simp []
  >> gvs [lives_hold_def, EVERY_EL, PULL_FORALL]
  >> first_x_assum $ qspecl_then [‘k + 1’, ‘n’] mp_tac
  >> pure_rewrite_tac [some_signal_holds_def] >> rw [EXISTS_MEM, MEM_EL]
  >> simp [GSYM PULL_FORALL]
  >> first_assum $ irule_at (Pos hd)
  >> rw []
  >> first_assum irule
  >> simp [PULL_EXISTS]
  >> metis_tac []
QED

Theorem is_witness_xis_safe_and_live:
  is_witness
    mxaig mreset mnext msafes mcnstrs mqxaig mlive mlatches
    wxaig wreset wnext wsafes wcnstrs wqxaig wlive wlatches ∧
  dep_model
    mxaig mreset mnext msafes mcnstrs minput mlatches ∧
  (* TODO See is_witness_xis_live comment *)
  dep_qxaig minput mqxaig mlive mlatches ∧
  is_stratified lt wxaig wreset wlatches ∧
  FINITE wlatches
  ⇒
  xis_safe
    mxaig mreset mnext mcnstrs mlatches msafes
  ∧
  xis_live
    mxaig mreset mnext mcnstrs mqxaig (IMAGE set (set mlive)) mlatches
Proof
  strip_tac
  >> drule_all_then assume_tac is_witness_xis_safe
  >> drule_all_then assume_tac is_witness_xis_live
  >> simp []
QED

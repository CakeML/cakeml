(*
  Formalization of And-Inverter Graphs
*)
Theory aig
Ancestors
  misc mlstring
Libs
  preamble

val _ = numLib.prefer_num()

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

(** AIG ***********************************************************************)

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
Type and[pp] = “:'a # (('a,'i,'l) lit list)”
Type aig[pp] = “:('a,'i,'l) and list”

Overload TT = “(Base Ff, T)”
Overload FF = “(Base Ff, F)”

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

Theorem eval_gate_nil[simp]:
  ¬eval_gate ss [] n
Proof
  simp [eval_lit_def]
QED

Theorem eval_lit_flip:
  eval_lit ss aig (v,¬b) ⇔ ¬eval_lit ss aig (v,b)
Proof
  once_rewrite_tac [eval_lit_def] >> CASE_TAC >> metis_tac []
QED

Definition not_def:
  not ((v, b): ('a,'i,'l) lit) = (v, ¬b)
End

Theorem eval_lit_not:
  eval_lit ss aig (not x) ⇔ ¬eval_lit ss aig x
Proof
  Cases_on ‘x’ >> simp [not_def, eval_lit_flip]
QED

(*
EVAL``eval_lit (is,ls) aig TT``
EVAL``eval_lit (is,ls) aig FF``
*)

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
  ∀l. l ∈ latches ⇒
      eval_lit ss₀ aig (next l) = ls₁ l
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

Definition is_unsafe_def:
  is_unsafe (aig: ('a, 'i, 'l) aig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set) (safe: ('a,'i,'l) lit set)
  =
  ∃(steps: ('i, 'l) steps) (n: num).
    is_trace aig reset next cnstrs latches steps n ∧
    ¬lits_hold (steps n) aig safe
End

Definition is_safe_def:
  is_safe (aig: ('a, 'i, 'l) aig)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (safe: ('a,'i,'l) lit set) ⇔
  ¬is_unsafe aig reset next cnstrs latches safe
End

(* Liveness *******************************************************************)

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
    (live: ('b, 'i + 'i, 'l + 'l) lit list list) (latches: 'l set) =
  ∀steps.
    is_inf_trace aig reset next cnstrs latches steps ⇒
    ∀prop. MEM prop live ⇒
      ∃k signal.
        MEM signal prop ∧
        (∀i. k ≤ i ⇒
             lits_hold (state_pair (steps i) (steps (i + 1))) qaig {signal})
End

(* AIG Dependencies ***********************************************************)

(* While state and input are defined over the entirety of (potentially infinite)
   domains, an AIG can only depend on a finite subset of these domains, as
   we have a finite amount of gates.
   We formalize this notion in dep_aig. *)

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

Definition and_inputs_def:
  and_inputs ((_, lits): ('a,'i,'l) and) = FLAT (MAP lit_inputs lits)
End

Definition aig_inputs_def:
  aig_inputs (aig: ('a,'i,'l) aig) = FLAT (MAP and_inputs aig)
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

Definition and_latches_def:
  and_latches ((_, lits): ('a,'i,'l) and) = FLAT (MAP lit_latches lits)
End

Definition aig_latches_def:
  aig_latches (aig: ('a,'i,'l) aig) = FLAT (MAP and_latches aig)
End

(* Syntactic Dependencies *****************************************************)

Definition dep_aig_def:
  dep_aig inputs latches aig =
  ∀n ss' ss.
    agree_on inputs latches ss' ss
    ⇒
    eval_gate ss' aig n = eval_gate ss aig n
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

(* TODO Is there a better name for this? It feels like this is a component of
   stratification, but not the entirety (since stratified_full exists) *)
Definition is_stratified_def:
  is_stratified lt aig reset latches ⇔
    ∀lat lit is ls' ls.
      lat ∈ latches ∧ reset lat = SOME lit ∧
      (∀l. l ∈ { l' | lt l' lat } ⇒ (ls' l ⇔ ls l)) ⇒
      (eval_lit (is,ls') aig lit ⇔ eval_lit (is,ls) aig lit)
End

Definition patch_def:
  (patch aig reset is (ls: 'l lstate) ([]: 'l list) = ls) ∧
  (patch aig reset is ls (latch::rest) =
   patch aig reset is
     (λl.
        if l = latch then
          (case reset l of
           | NONE => ls l
           | SOME lit => eval_lit (is, ls) aig lit)
        else ls l) rest)
End

Theorem not_mem_patch_eq:
  ∀xs ls. ¬MEM l xs ⇒ (patch aig reset is ls xs) l = ls l
Proof
  Induct >> rw [patch_def]
QED

Theorem is_reset_insert_NONE:
  reset l = NONE ⇒
  (is_reset ss aig reset (l INSERT ls) ⇔
     is_reset ss aig reset ls)
Proof
  rw [is_reset_def] >> eq_tac >> rw [] >> gvs []
QED

Theorem is_reset_insert_SOME:
  reset l = SOME lit ⇒
  (is_reset ss aig reset (l INSERT latches) ⇔
     is_reset ss aig reset latches ∧
     (eval_lit ss aig (Base (Latch l),F) ⇔ eval_lit ss aig lit))
Proof
  rw [is_reset_def] >> eq_tac >> rw [] >> gvs []
QED

Theorem is_reset_union:
  is_reset ss aig reset (xs ∪ ys) ⇔
    is_reset ss aig reset xs ∧ is_reset ss aig reset ys
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
    is_stratified lt aig reset latches ∧ set xs ⊆ latches ∧
    no_inversions lt xs ∧ ALL_DISTINCT xs ∧ irreflexive lt
    ⇒
    is_reset (is, patch aig reset is ls xs) aig reset (set xs)
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
  >> simp [eval_lit_def]
  >> rename1 ‘l::xs’
  >> drule_then assume_tac not_mem_patch_eq >> simp []
  >> fs [is_stratified_def]
  >> qmatch_goalsub_abbrev_tac ‘_ ⇔ eval_lit (is, ls') _ _’
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

Theorem dep_eval_lit_eq:
  ∀n ss' ss.
    dep_aig inputs latches aig ∧
    dep_lit inputs latches n ∧
    agree_on inputs latches ss' ss ⇒
    (eval_lit ss' aig n ⇔ eval_lit ss aig n)
Proof
  namedCases ["v b"]
  >> namedCases ["is' ls'"]
  >> namedCases ["is ls"]
  >> Cases_on ‘v’ >> rw [eval_lit_def]
  >-
   (fs [dep_aig_def]
    >> rename1 ‘eval_gate _ _ a’
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

Theorem aig_inputs_cons:
  aig_inputs (h::aig) = and_inputs h ++ aig_inputs aig
Proof
  simp [aig_inputs_def]
QED

Theorem aig_latches_cons:
  aig_latches (h::aig) = and_latches h ++ aig_latches aig
Proof
  simp [aig_latches_def]
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

Theorem dep_aig_subset:
  dep_aig xs ys aig ∧ xs ⊆ xs' ∧ ys ⊆ ys'
  ⇒
  dep_aig xs' ys' aig
Proof
  rw [dep_aig_def] >> metis_tac [agree_on_weaken]
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

Theorem dep_lit_and:
  MEM lit lits ⇒
  dep_lit (set (and_inputs (n,lits))) (set (and_latches (n,lits))) lit
Proof
  namedCases_on ‘lit’ ["b v"] >> simp [dep_lit_def]
  >> namedCases_on ‘b’ ["n", "bv"] >> simp [dep_var_def]
  >> Cases_on ‘bv’ >> simp [dep_bvar_def]
  >> rw [and_latches_def, and_inputs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS]
  >> first_assum $ irule_at Any
  >> simp [lit_inputs_def, var_inputs_def, bvar_inputs_def, lit_latches_def,
           var_latches_def, bvar_latches_def]
QED

Theorem dep_aig_inputs_latches:
  dep_aig (set (aig_inputs aig)) (set (aig_latches aig)) aig
Proof
  Induct_on ‘aig’ >- simp [dep_aig_def]
  >> rw [dep_aig_def]
  >> fs [aig_inputs_cons, aig_latches_cons]
  >> rename1 ‘h::_’ >> namedCases_on ‘h’ ["n ls"]
  >> gvs [eval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >-
   (irule EVERY_CONG >> rw []
    >> irule dep_eval_lit_eq
    >> qpat_assum ‘agree_on _ _ _ _’ $ irule_at Any
    >> irule_at (Pos hd) dep_aig_subset
    >> first_assum $ irule_at (Pos hd)
    >> simp []
    >> irule_at (Pos hd) dep_lit_subset
    >> irule_at (Pos hd) dep_lit_and
    >> first_assum $ irule_at (Pos hd)
    >> qexists ‘n’ >> simp [])
  >> fs [dep_aig_def]
  >> first_assum irule
  >> fs [agree_on_union]
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
  is_next ss aig next latches  ls ∧ latches' ⊆ latches ⇒
  is_next ss aig next latches' ls
Proof
  rw [is_next_def] >> metis_tac [SUBSET_DEF]
QED

Theorem is_next_dep_aig:
  is_next ss₀ aig next latches ls₁ ∧
  (∀l. l ∈ latches' ⇒ ls₁ l = ls₁' l) ∧
  agree_on inputs latches' ss₀ ss₀' ∧
  dep_aig inputs latches' aig ∧
  dep_latch_lit inputs latches' next latches ∧
  latches ⊆ latches'
  ⇒
  is_next ss₀' aig next latches ls₁'
Proof
  rw [is_next_def, dep_latch_lit_def]
  >> fs[SUBSET_DEF]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem lits_hold_dep_aig:
  lits_hold ss aig lits ∧
  dep_aig inputs latches aig ∧
  dep_lits inputs latches lits ∧
  agree_on inputs latches ss ss'
  ⇒
  lits_hold ss' aig lits
Proof
  rw [lits_hold_def, dep_lits_def]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem is_reset_dep_aig:
  is_reset ss aig reset latches ∧
  dep_aig inputs latches aig ∧
  dep_reset inputs latches reset latches ∧
  agree_on inputs latches ss ss'
  ⇒
  is_reset ss' aig reset latches
Proof
  rw [is_reset_def, dep_reset_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> last_x_assum $ drule_then assume_tac
  >> gvs [eval_lit_def]
  >> metis_tac [dep_eval_lit_eq, agree_on_def]
QED

Theorem is_trace_dep_aig:
  is_trace aig reset next cnstrs latches steps n ∧
  dep_aig inputs latches aig ∧
  dep_lits inputs latches cnstrs ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  steps_agree n inputs latches steps' steps
  ⇒
  is_trace aig reset next cnstrs latches steps' n
Proof
  rw [steps_agree_def, is_trace_def, agree_on_sym]
  >-
   (irule is_reset_dep_aig >> simp []
    >> last_assum $ irule_at (Pos last)
    >> last_assum $ irule_at (Pos last)
    >> gvs [])
  >-
   (irule lits_hold_dep_aig >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp [])
  >-
   (last_x_assum $ drule_then assume_tac
    >> irule is_next_dep_aig >> fs []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> rename1 ‘SND (steps (i + 1))’
    >> Cases_on ‘steps (i + 1)’ >> Cases_on ‘steps' (i + 1)’ >> fs []
    >> first_x_assum $ qspec_then ‘i + 1’ mp_tac
    >> simp [agree_on_def])
  >> last_x_assum $ drule_then assume_tac
  >> irule lits_hold_dep_aig >> fs []
  >> first_assum $ irule_at (Pos last) >> simp []
QED

Theorem is_inf_trace_dep_aig:
  is_inf_trace aig reset next cnstrs latches steps ∧
  dep_aig inputs latches aig ∧
  dep_lits inputs latches cnstrs ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  (∀n. steps_agree n inputs latches steps' steps)
  ⇒
  is_inf_trace aig reset next cnstrs latches steps'
Proof
  rw [is_inf_trace_eq] >> metis_tac[is_trace_dep_aig]
QED


Theorem is_trace_lits_hold_n:
  is_trace aig reset next cnstrs latches steps n
  ⇒
  lits_hold (steps n) aig cnstrs
Proof
  rw [is_trace_def] >> Cases_on ‘n’ >> fs [ADD1]
QED

Theorem is_trace_SUC:
  is_trace maig mreset mnext mcnstrs mlatches steps (SUC n)
  ⇔
  is_trace maig mreset mnext mcnstrs mlatches steps n ∧
  is_next (steps n) maig mnext mlatches (SND (steps (n + 1))) ∧
  lits_hold (steps (n + 1)) maig mcnstrs
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
  is_reset ss aig reset latches ∧
  dep_aig inputs latches aig ∧
  dep_reset inputs latches reset latches ∧
  agree_on inputs latches ss ss'
  ⇒
  is_reset ss' aig reset latches
Proof
  rw [is_reset_def, dep_reset_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> gvs[eval_lit_def]
  >> metis_tac [dep_eval_lit_eq, agree_on_def]
QED

Definition dep_qaig_def:
  dep_qaig inputs qaig live latches ⇔
    dep_aig (pair_set inputs) (pair_set latches) qaig ∧
    dep_lits (pair_set inputs) (pair_set latches) (set (FLAT live))
End

Theorem is_safe_is_inf_trace_lits_hold:
  is_safe aig reset next cnstrs latches preds ∧
  is_inf_trace aig reset next cnstrs latches steps
  ⇒
  ∀n. lits_hold (steps n) aig preds
Proof
  rw [is_safe_def, is_unsafe_def, is_inf_trace_eq]
  >> metis_tac []
QED

Theorem is_inf_trace_cnstrs_hold:
  is_inf_trace aig reset next cnstrs latches steps
  ⇒
  ∀n. lits_hold (steps n) aig cnstrs
Proof
  rw [is_inf_trace_def] >> Cases_on ‘n’ >> gvs [ADD1]
QED

Theorem is_inf_trace_is_next:
  is_inf_trace aig reset next cnstrs latches steps
  ⇒
  ∀n. is_next (steps n) aig next latches (SND (steps (n + 1)))
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
     is_trace maig mreset mnext mcnstrs mlatches steps n ⇒
     is_trace waig wreset wnext wcnstrs wlatches steps' n ∧
     steps_agree n UNIV mlatches steps' steps)
  ⇒
    (is_inf_trace maig mreset mnext mcnstrs mlatches steps ⇒
     is_inf_trace waig wreset wnext wcnstrs wlatches steps' ∧
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

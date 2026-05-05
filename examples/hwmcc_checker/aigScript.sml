(*
  Formalization of And-Inverter Graphs
*)
Theory aig
Ancestors
  misc mlstring
Libs
  preamble

val _ = numLib.prefer_num();

(* Things that appear in base positions.
   Ff corresponds to the constant false. *)
Datatype:
  bvar = Ff | Input 'i | Latch 'l
End

Datatype:
  var = Name 'a | Base (('i,'l) bvar)
End

Type inputs = “:'i -> bool”
Type state = “:'l -> bool”
Type trace[pp] = “:num -> 'i inputs # 'l state”

Definition eval_bvar_def[simp]:
  (eval_bvar (is: 'i inputs, ls: 'l state) Ff = F) ∧
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
Type circuit[pp] = “:('a,'i,'l) and list”

Overload TT = “(Base Ff, T)”
Overload FF = “(Base Ff, F)”

(* Note that we can conjunction over a list of literals as opposed to a pair.
   If needed, we can apply a reduction at the end, allowing for simpler
   definitions for operations such as equivalence.  *)
Definition eval_circuit_def:
  (eval_lit (ss : 'i inputs # 'l state) circ ((v,b):('a,'i,'l) lit) =
    case v of
    | Base bv => b ⇎ eval_bvar ss bv
    | Name n => b ⇎ eval_circuit ss circ n) ∧
  (eval_circuit ss ([]:('a,'i,'l) circuit) n = F) ∧
  (eval_circuit ss (h::tl) n =
   let (n', ins) = h in
     if n' = n then EVERY (eval_lit ss tl) ins
     else eval_circuit ss tl n)
End

Theorem eval_circuit_nil[simp]:
  ¬eval_circuit ss [] n
Proof
  simp [eval_circuit_def]
QED

Theorem eval_lit_flip:
  eval_lit ss circ (v,¬b) ⇔ ¬eval_lit ss circ (v,b)
Proof
  once_rewrite_tac [eval_circuit_def] >> CASE_TAC >> metis_tac []
QED

(*
EVAL``eval_lit (is,ls) circ TT``
EVAL``eval_lit (is,ls) circ FF``
*)

Definition pair_state_def:
  pair_state (is₁,ls₁) (is₂,ls₂) =
    ((λi. sum_CASE i is₁ is₂), (λl. sum_CASE l ls₁ ls₂))
End

Definition preds_hold_def:
  preds_hold ss (circ: ('a, 'i, 'l) circuit)
    (ns: ('a,'i,'l) lit set) =
  (∀n. n ∈ ns ⇒ eval_lit ss circ n)
End

Definition is_reset_def:
  is_reset ss (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit) (ls: 'l set) =
  ∀l. l ∈ ls ⇒
      eval_lit ss circ (Base (Latch l), F) =
      eval_lit ss circ (reset l)
End

Definition is_next_def:
  is_next ss₀ (circ: ('a, 'i, 'l) circuit)
    (next: 'l -> ('a,'i,'l) lit) (latches: 'l set) ls₁ =
  ∀l. l ∈ latches ⇒
      eval_lit ss₀ circ (next l) = ls₁ l
End

Definition is_trace_def:
  is_trace (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (tr: ('i, 'l) trace) (n: num)
  ⇔
    (is_reset (tr 0) circ reset latches ∧
     preds_hold (tr 0) circ cnstrs) ∧
    ∀i. i < n ⇒
      is_next (tr i) circ next latches (SND (tr (i + 1))) ∧
      preds_hold (tr (i + 1)) circ cnstrs
End

(* TODO Why not inline is_unsafe into is_safe? *)
Definition is_unsafe_def:
  is_unsafe (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set) (safe: ('a,'i,'l) lit set)
  =
  ∃(tr: ('i, 'l) trace) (n: num).
    is_trace circ reset next cnstrs latches tr n ∧
    ¬preds_hold (tr n) circ safe
End

Definition is_safe_def:
  is_safe (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (safe: ('a,'i,'l) lit set) ⇔
  ¬is_unsafe circ reset next cnstrs latches safe
End

(* Soundness ******************************************************************)

(* NOTE We use R{L} and F{L} on the left-hand side of implications
   instead of R{K} and F{K}, allowing us to prove soundness a bit easier. *)

Definition is_witness_reset_def:
  is_witness_reset
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
  ∀ss.
    (is_reset ss mcirc mreset mlatches ∧
     preds_hold ss mcirc mcnstrs
     ⇒
     is_reset ss wcirc wreset (mlatches ∩ wlatches) ∧
     preds_hold ss wcirc wcnstrs)
End

Definition is_witness_transition_def:
  is_witness_transition
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
  ∀ss₀ ss₁.
    (is_next ss₀ mcirc mnext mlatches (SND ss₁) ∧
     preds_hold ss₀ mcirc mcnstrs ∧
     preds_hold ss₁ mcirc mcnstrs ∧
     preds_hold ss₀ wcirc wcnstrs)
    ⇒
    (is_next ss₀ wcirc wnext (mlatches ∩ wlatches) (SND ss₁) ∧
     preds_hold ss₁ wcirc wcnstrs)
End

Definition is_witness_property_def:
  is_witness_property
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
  ∀ss.
    (preds_hold ss mcirc mcnstrs ∧
     preds_hold ss wcirc wcnstrs) ⇒
    preds_hold ss wcirc wpreds ⇒
    preds_hold ss mcirc mpreds
End

Definition is_witness_base_def:
  is_witness_base
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
    ∀ss.
      (is_reset ss wcirc wreset wlatches ∧
       preds_hold ss wcirc wcnstrs)
      ⇒
      preds_hold ss wcirc wpreds
End

Definition is_witness_step_def:
  is_witness_step
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇔
    ∀ss₀ ss₁.
      (preds_hold ss₀ wcirc wpreds ∧
       is_next ss₀ wcirc wnext wlatches (SND ss₁) ∧
       preds_hold ss₀ wcirc wcnstrs ∧
       preds_hold ss₁ wcirc wcnstrs)
      ⇒
      preds_hold ss₁ wcirc wpreds
End

Definition is_witness_liveness_def:
  is_witness_liveness
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
    wcirc wreset wnext wpreds wcnstrs wlatches wqcirc wlive
  ⇔
    ∀ss₀ ss₁.
      (preds_hold ss₀ mcirc mcnstrs ∧
       preds_hold ss₀ wcirc wcnstrs ∧
       preds_hold ss₀ wcirc wpreds ∧
       preds_hold ss₁ mcirc mcnstrs ∧
       preds_hold ss₁ wcirc wcnstrs ∧
       preds_hold ss₁ wcirc wpreds ∧
       is_next ss₀ wcirc wnext wlatches (SND ss₁) ∧
       preds_hold (pair_state ss₀ ss₁) wqcirc wlive)
      ⇒
      preds_hold (pair_state ss₀ ss₁) mqcirc mlive
End

Definition is_witness_decrease_def:
  is_witness_decrease
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
  ⇔
    ∀ss₀ ss₁.
      (preds_hold ss₀ mcirc mcnstrs ∧
       preds_hold ss₀ mcirc mpreds ∧
       preds_hold ss₁ mcirc mcnstrs ∧
       preds_hold ss₁ mcirc mpreds ∧
       is_next ss₀ mcirc mnext mlatches (SND ss₁))
       ⇒
       preds_hold (pair_state ss₁ ss₀) mqcirc mlive
End

Definition is_witness_closure_def:
  is_witness_closure
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
  ⇔
    ∀ss₀ ss₁ ss₂.
      (preds_hold ss₀ mcirc mcnstrs ∧
       preds_hold ss₀ mcirc mpreds ∧
       preds_hold ss₁ mcirc mcnstrs ∧
       preds_hold ss₁ mcirc mpreds ∧
       preds_hold ss₂ mcirc mcnstrs ∧
       preds_hold ss₂ mcirc mpreds ∧
       is_next ss₀ mcirc mnext mlatches (SND ss₁) ∧
       preds_hold (pair_state ss₀ ss₂) mqcirc mlive)
      ⇒
      preds_hold (pair_state ss₁ ss₂) mqcirc mlive
End

Definition is_witness_def:
  is_witness
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
    wcirc wreset wnext wpreds wcnstrs wlatches wqcirc wlive
  ⇔
  is_witness_reset
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_transition
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_property
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_base
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_step
    wcirc wreset wnext wpreds wcnstrs wlatches
  ∧
  is_witness_liveness
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
    wcirc wreset wnext wpreds wcnstrs wlatches wqcirc wlive
  ∧
  is_witness_decrease
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
  ∧
  is_witness_closure
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
End

(* Latch Dependencies *********************************************************)

(* While state is defined over the entirety of the (potentially infinite) domain
   'l, a circuit only depends on a finite subset of 'l.
   We formalize this notion in dep_circuit. *)

Definition dep_circuit_def:
  dep_circuit latches circ =
  ∀n is ls ls'.
    (∀l. l ∈ latches ⇒ ls' l = ls l) ⇒
    eval_circuit (is, ls') circ n = eval_circuit (is, ls) circ n
End

Definition dep_bvar_def[simp]:
  (dep_bvar latches Ff        ⇔ T) ∧
  (dep_bvar latches (Input i) ⇔ T) ∧
  (dep_bvar latches (Latch l) ⇔ l ∈ latches)
End

Definition dep_var_def[simp]:
  (dep_var latches (Name _)  = T) ∧
  (dep_var latches (Base bv) = dep_bvar latches bv)
End

Definition dep_lit_def[simp]:
  dep_lit latches (v, b) = dep_var latches v
End

Definition dep_lits_def:
  dep_lits latches (lits: ('a,'i,'l) lit set) ⇔
    ∀lit. lit ∈ lits ⇒ dep_lit latches lit
End

Definition dep_latch_lit_def:
  dep_latch_lit latches (latch_lit: 'l -> ('a,'i,'l) lit) ⇔
    ∀l. l ∈ latches ⇒ dep_lit latches (latch_lit l)
End

(* TODO can dep_ family be merged with is_stratified? *)
Definition is_stratified_def:
  is_stratified lt circ reset latches ⇔
    ∀l is ls' ls.
      l ∈ latches ∧ (∀l. l ∈ { l' | lt l' l } ⇒ (ls' l ⇔ ls l)) ⇒
      eval_lit (is,ls') circ (reset l) ⇔ eval_lit (is,ls) circ (reset l)
End

Definition patch_def:
  (patch circ reset is (ls: 'l state) ([]: 'l list) = ls) ∧
  (patch circ reset is ls (latch::rest) =
   patch circ reset is
     (λl. if l = latch then eval_lit (is, ls) circ (reset l) else ls l)
     rest)
End

Theorem not_mem_patch_eq:
  ∀xs ls. ¬MEM l xs ⇒ (patch circ reset is ls xs) l = ls l
Proof
  Induct >> rw [patch_def]
QED

Theorem is_reset_insert:
  is_reset ss circ reset (l INSERT ls) ⇔
    is_reset ss circ reset ls ∧
    (eval_lit ss circ (Base (Latch l),F) ⇔ eval_lit ss circ (reset l))
Proof
  rw [is_reset_def] >> metis_tac []
QED

Theorem is_reset_union:
  is_reset ss circ reset (xs ∪ ys) ⇔
    is_reset ss circ reset xs ∧ is_reset ss circ reset ys
Proof
  rw [is_reset_def] >> metis_tac []
QED

(* TODO Is assuming irreflexive ok? How to express
   "latch is always in reset state"? *)
Theorem subset_is_reset_patch:
  ∀xs ls.
    is_stratified lt circ reset latches ∧ set xs ⊆ latches ∧
    SORTED lt xs ∧ irreflexive lt ∧ transitive lt
    ⇒
    is_reset (is, patch circ reset is ls xs) circ reset (set xs)
Proof
  Induct >> rw [patch_def]
  >- simp [is_reset_def]
  >> simp [is_reset_insert]
  >> conj_tac
  >- (last_x_assum irule >> drule SORTED_TL >> simp [])
  >> simp [eval_circuit_def]
  >> rename1 ‘l::xs’
  >> ‘¬MEM l xs’ by (drule_all SORTED_ALL_DISTINCT >> simp [])
  >> drule_then assume_tac not_mem_patch_eq >> simp []
  >> fs [is_stratified_def]
  >> qmatch_goalsub_abbrev_tac ‘_ ⇔ eval_lit (is, ls') _ _’
  >> last_x_assum $ qspecl_then [‘l’, ‘is’, ‘ls'’, ‘ls’] mp_tac
  >> fs [irreflexive_def]
QED

Theorem dep_eval_lit_eq:
  ∀n is ls ls'.
    dep_circuit latches circ ∧ dep_lit latches n ∧
    (∀l. l ∈ latches ⇒ (ls' l ⇔ ls l)) ⇒
    (eval_lit (is,ls') circ n ⇔ eval_lit (is,ls) circ n)
Proof
  namedCases ["v b"]
  >> Cases_on ‘v’ >> rw [eval_circuit_def]
  >-
   (fs [dep_circuit_def]
    >> rename1 ‘eval_circuit _ _ a’
    >> last_x_assum $ qspecl_then [‘a’, ‘is’, ‘ls’, ‘ls'’] mp_tac
    >> simp [])
  >> rename1 ‘eval_bvar _ b₁’
  >> Cases_on ‘b₁’
  >> fs [eval_bvar_def]
QED

(* Extending a trace for the model to a trace for the witness *****************)

Definition steps_agree_def:
  steps_agree (latches: 'l set) ((is', ls'): 'i inputs # 'l state) (is, ls) ⇔
  is' = is ∧ ∀l. l ∈ latches ⇒ ls' l = ls l
End

Theorem steps_agree_sym:
  steps_agree mlatches ss ss' = steps_agree mlatches ss' ss
Proof
  Cases_on ‘ss’ >> Cases_on ‘ss'’ >> eq_tac >> rw [steps_agree_def]
QED

(* tr' and tr agree on the first n inputs and states on latches *)
Definition traces_agree_def:
  traces_agree n latches (tr': ('i, 'l) trace) tr ⇔
    ∀i. i ≤ n ⇒ steps_agree latches (tr' i) (tr i)
End

Theorem is_next_subset:
  is_next ss circ next latches  ls ∧ latches' ⊆ latches ⇒
  is_next ss circ next latches' ls
Proof
  rw [is_next_def] >> metis_tac [SUBSET_DEF]
QED

Theorem is_next_dep_circuit:
  is_next ss₀ circ next latches ls₁ ∧
  (∀l. l ∈ latches ⇒ ls₁ l = ls₁' l) ∧
  steps_agree latches ss₀ ss₀' ∧
  dep_circuit latches circ ∧
  dep_latch_lit latches next
  ⇒
  is_next ss₀' circ next latches ls₁'
Proof
  rw [is_next_def, dep_latch_lit_def]
  >> namedCases_on ‘ss₀’ ["is ls₀"]
  >> namedCases_on ‘ss₀'’ ["is' ls₀'"]
  >> gvs [steps_agree_def]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem preds_hold_dep_circuit:
  preds_hold ss circ ns ∧
  dep_circuit latches circ ∧
  dep_lits latches ns ∧
  steps_agree latches ss ss'
  ⇒
  preds_hold ss' circ ns
Proof
  rw [preds_hold_def, dep_lits_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> gvs [steps_agree_def]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem is_reset_dep_circuit:
  is_reset ss circ reset latches ∧
  dep_circuit latches circ ∧
  dep_latch_lit latches reset ∧
  steps_agree latches ss ss'
  ⇒
  is_reset ss' circ reset latches
Proof
  rw [is_reset_def, dep_latch_lit_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> gvs [steps_agree_def]
  >> last_x_assum $ drule_then assume_tac
  >> gvs [eval_circuit_def]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem is_trace_dep_circuit:
  is_trace circ reset next cnstrs latches tr n ∧
  dep_circuit latches circ ∧
  dep_lits latches cnstrs ∧
  dep_latch_lit latches reset ∧
  dep_latch_lit latches next ∧
  traces_agree n latches tr' tr
  ⇒
  is_trace circ reset next cnstrs latches tr' n
Proof
  rw [traces_agree_def, is_trace_def, steps_agree_sym]
  >-
   (irule is_reset_dep_circuit >> simp []
    >> last_assum $ irule_at (Pos last) >> gvs [])
  >-
   (irule preds_hold_dep_circuit >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp [])
  >-
   (last_x_assum $ drule_then assume_tac
    >> irule is_next_dep_circuit >> fs []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> rename1 ‘SND (tr (i + 1))’
    >> Cases_on ‘tr (i + 1)’ >> Cases_on ‘tr' (i + 1)’ >> fs []
    >> first_x_assum $ qspec_then ‘i + 1’ mp_tac
    >> simp [steps_agree_def])
  >> last_x_assum $ drule_then assume_tac
  >> irule preds_hold_dep_circuit >> fs []
  >> first_assum $ irule_at (Pos last) >> simp []
QED

Theorem is_trace_preds_hold_n:
  is_trace circ reset next cnstrs latches tr n
  ⇒
  preds_hold (tr n) circ cnstrs
Proof
  rw [is_trace_def] >> Cases_on ‘n’ >> fs [ADD1]
QED

Theorem is_trace_SUC:
  is_trace mcirc mreset mnext mcnstrs mlatches tr (SUC n)
  ⇔
  is_trace mcirc mreset mnext mcnstrs mlatches tr n ∧
  is_next (tr n) mcirc mnext mlatches (SND (tr (n + 1))) ∧
  preds_hold (tr (n + 1)) mcirc mcnstrs
Proof
  eq_tac >> rw [is_trace_def]
  >> rename1 ‘i < SUC n’ >> Cases_on ‘i < n’ >> gvs []
  >> ‘i = n’ by simp []
  >> simp []
QED

Theorem traces_agree_SUC:
  traces_agree (SUC n) mlatches tr' tr ⇔
    traces_agree n mlatches tr' tr ∧
    steps_agree mlatches (tr' (n + 1)) (tr (n + 1))
Proof
  eq_tac >> rw [traces_agree_def]
  >> rename1 ‘i ≤ SUC n’
  >> Cases_on ‘i ≤ n’
  >> Cases_on ‘tr' i’ >> Cases_on ‘tr i’
  >> Cases_on ‘tr' (n + 1)’ >> Cases_on ‘tr (n + 1)’
  >- (last_x_assum drule >> gvs [])
  >> ‘i = n + 1’ by simp []
  >> gvs []
QED

Theorem set_QSORT[local,simp]:
  ∀R ls. set (QSORT R ls) = set ls
Proof
  metis_tac [QSORT_PERM, PERM_LIST_TO_SET]
QED

Theorem is_reset_dep_latch_lit:
  is_reset ss circ reset latches ∧
  dep_circuit latches circ ∧
  dep_latch_lit latches reset ∧
  steps_agree latches ss ss'
  ⇒
  is_reset ss' circ reset latches
Proof
  rw [is_reset_def, dep_latch_lit_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> gvs[eval_circuit_def, steps_agree_def]
  >> metis_tac [dep_eval_lit_eq, SND, PAIR]
QED

Theorem extend_model_trace_to_witness:
  is_trace mcirc mreset mnext mcnstrs mlatches tr n ∧
  (* model latches constraints *)
  dep_circuit mlatches mcirc ∧
  dep_latch_lit mlatches mreset ∧
  dep_latch_lit mlatches mnext ∧
  dep_lits mlatches mcnstrs ∧
  (* witness latches constraints *)
  FINITE wlatches ∧
  irreflexive lt ∧
  transitive lt ∧
  total lt ∧  (* for QSORT_SORTED *)
  is_stratified lt wcirc wreset wlatches ∧
  is_witness_reset
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches ∧
  is_witness_transition
    mcirc mreset mnext mpreds mcnstrs mlatches
    wcirc wreset wnext wpreds wcnstrs wlatches
  ⇒
  ∃tr'.
    is_trace wcirc wreset wnext wcnstrs wlatches tr' n ∧
    traces_agree n mlatches tr' tr
Proof
  Induct_on ‘n’ >> rw []
  >-
   (fs [is_trace_def, is_witness_reset_def]
    >> first_assum $ drule_all_then assume_tac
    >> namedCases_on ‘tr 0’ ["is ls"] >> fs []
    >> qabbrev_tac
         ‘xs = QSORT lt (SET_TO_LIST (wlatches DIFF (mlatches ∩ wlatches)))’
    >> qabbrev_tac `ss0 = (is, patch wcirc wreset is ls xs)`
    >> qexists ‘λ_. ss0’ >> simp []
    >> CONJ_TAC
      (* wlatches are in reset and wcnstrs
        are satisfied in patched state *)
    >- (
      first_x_assum (qspec_then ‘ss0’ mp_tac)
      >> impl_tac
      >- (
        CONJ_TAC
        >- (
          drule_then irule is_reset_dep_latch_lit>>
          simp[Abbr`ss0`, steps_agree_def]>>
          rw[]>>
          irule (GSYM not_mem_patch_eq)>>
          simp[Abbr`xs`])
        >>
          drule_then irule preds_hold_dep_circuit>>
          simp[Abbr`ss0`, steps_agree_def]>>
          first_x_assum $ irule_at Any>>
          rw[]>>
          irule (GSYM not_mem_patch_eq)>>
          simp[Abbr`xs`])
      >> rw[]
      >> ‘wlatches = (mlatches ∩ wlatches) ∪ (set xs)’ by
          (simp [Abbr ‘xs’, Req0 SET_TO_LIST_INV] >> SET_TAC [])
      >> pop_assum SUBST1_TAC
      >> simp [is_reset_union,Abbr`ss0`]
      >> irule subset_is_reset_patch
      >> first_assum $ irule_at (Pos last)  (* is_stratified *)
      >> simp [Abbr ‘xs’, Req0 SET_TO_LIST_INV, Req0 QSORT_SORTED])
    >> simp [traces_agree_def, steps_agree_def, Abbr`ss0`]
    >-
     (rw []
      >> rename1 ‘patch _ _ _ _ _ l’ >> ‘¬MEM l xs’ by simp [Abbr ‘xs’]
      >> simp [not_mem_patch_eq]))
  >> gvs [is_trace_SUC, traces_agree_SUC]
  >> qrefine ‘λn'. if n' ≤ n then tr' n' else step’
  >> ‘∃step.
        is_next (tr' n) wcirc wnext wlatches (SND step) ∧
        preds_hold step wcirc wcnstrs ∧
        steps_agree mlatches step (tr (n + 1))’
    suffices_by
    (rw [] >> qexists ‘step’ >> gvs [is_trace_def, traces_agree_def])
  >> qabbrev_tac ‘step = (FST (tr (n + 1)),
                          λl. if l ∈ mlatches then (SND (tr (n + 1))) l
                              else eval_lit (tr' n) wcirc (wnext l))’
  >> qexists ‘step’
  >> ‘is_next (tr' n) mcirc mnext mlatches (SND step)’ by
    (drule is_next_dep_circuit
     >> disch_then irule
     >> gvs [traces_agree_def, steps_agree_sym, Abbr ‘step’])
  >> ‘preds_hold (tr' n) mcirc mcnstrs’ by
    (‘preds_hold (tr n) mcirc mcnstrs’ by metis_tac [is_trace_preds_hold_n]
     >> drule preds_hold_dep_circuit
     >> disch_then drule >> disch_then irule
     >> gvs [traces_agree_def, steps_agree_sym])
  >> ‘preds_hold step mcirc mcnstrs’ by
    (rev_drule preds_hold_dep_circuit
     >> disch_then drule >> disch_then irule
     >> Cases_on ‘tr (n + 1)’
     >> gvs [steps_agree_def, Abbr ‘step’])
  >> ‘preds_hold (tr' n) wcirc wcnstrs’ by metis_tac [is_trace_preds_hold_n]
  (* Following the paper proof, we can now invoke the transition check and
     extend these two facts to the witness. *)
  >> fs [is_witness_transition_def]
  >> first_x_assum $ drule_all_then assume_tac >> fs []
  >> conj_tac
  >- (fs [is_next_def] >> rw [] >> Cases_on ‘l ∈ mlatches’ >> gvs [Abbr ‘step’])
  >> Cases_on ‘tr (n + 1)’
  >> fs [steps_agree_def, Abbr ‘step’]
QED

Theorem is_witness_base_step_safe:
  is_trace circ reset next cnstrs latches tr n ∧
  is_witness_base
    circ reset next preds cnstrs latches ∧
  is_witness_step
    circ reset next preds cnstrs latches
  ⇒
  preds_hold (tr n) circ preds
Proof
  Induct_on`n`>>rw[]
  >-
    gvs[is_witness_base_def,is_trace_def]>>
  gvs[is_trace_SUC] >>
  gvs[is_witness_step_def,ADD1]>>
  first_x_assum irule>>
  rw[]>>
  first_x_assum (irule_at (Pos last))>>
  simp[]>>
  metis_tac[is_trace_preds_hold_n]
QED

Definition dep_model_def:
  dep_model
    circ reset next preds cnstrs latches ⇔
  dep_circuit latches circ ∧
  dep_latch_lit latches reset ∧
  dep_latch_lit latches next ∧
  dep_lits latches preds ∧
  dep_lits latches cnstrs
End

Definition is_stratified_full_def:
  is_stratified_full lt circ reset latches ⇔
  FINITE latches ∧
  irreflexive lt ∧
  transitive lt ∧
  total lt ∧
  is_stratified lt circ reset latches
End

Theorem is_witness_is_safe:
  is_witness
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
    wcirc wreset wnext wpreds wcnstrs wlatches wqcirc wlive ∧
  dep_model
    mcirc mreset mnext mpreds mcnstrs mlatches ∧
  is_stratified_full lt wcirc wreset wlatches
  ⇒
  is_safe
    mcirc mreset mnext mcnstrs mlatches mpreds
Proof
  rw [is_witness_def, is_safe_def]
  >> CCONTR_TAC
  >> fs [is_unsafe_def, dep_model_def,is_stratified_full_def]
  >> pop_assum mp_tac >> simp[]
  >> drule_at_then (Pos last) drule extend_model_trace_to_witness
  >> rpt (disch_then $ drule_at Any)
  >> strip_tac
  >> drule_all is_witness_base_step_safe
  >> strip_tac
  >> `is_trace mcirc mreset mnext mcnstrs mlatches tr' n` by
    (irule is_trace_dep_circuit >> simp []
     >> first_assum $ irule_at (Pos hd) >> simp [])
  >> drule_at_then Any irule preds_hold_dep_circuit
  >> rename1`traces_agree n mlatches tr' tr`
  >> fs[traces_agree_def]
  >> qexists_tac`tr' n`
  >> gvs[is_witness_property_def]
  >> first_x_assum irule
  >> gvs[]
  >> metis_tac[is_trace_preds_hold_n]
QED

Theorem is_witness_is_live:
  is_witness
    mcirc mreset mnext mpreds mcnstrs mlatches mqcirc mlive
    wcirc wreset wnext wpreds wcnstrs wlatches wqcirc wlive ∧
  dep_model
    mcirc mreset mnext mpreds mcnstrs mlatches ∧
  is_stratified_full lt wcirc wreset wlatches
  ⇒
  is_live
    mcirc mreset mnext mcnstrs mlatches mqcirc mlive
Proof
  rw []
  >> drule_all is_witness_is_safe
  >> cheat
QED


(* Liveness *******************************************************************)

Definition is_inf_trace_def:
  is_inf_trace (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (tr: ('i, 'l) trace)
  ⇔
    (is_reset (tr 0) circ reset latches ∧
     preds_hold (tr 0) circ cnstrs) ∧
    ∀i.
      is_next (tr i) circ next latches (SND (tr (i + 1))) ∧
      preds_hold (tr (i + 1)) circ cnstrs
End

Theorem is_inf_trace_eq:
  is_inf_trace circ reset next cnstrs latches tr ⇔
  ∀n. is_trace circ reset next cnstrs latches tr n
Proof
  eq_tac>>
  rw[is_inf_trace_def,is_trace_def]>>
  first_x_assum(qspec_then`i+1` mp_tac)>>
  rw[]
QED

Definition is_live_def:
  is_live (circ: ('a, 'i, 'l) circuit) (reset: 'l -> ('a,'i,'l) lit)
    (next: 'l -> ('a,'i,'l) lit) (cnstrs: ('a,'i,'l) lit set)
    (latches: 'l set) (qcirc: ('b, 'i + 'i, 'l + 'l) circuit)
    (live: ('b, 'i + 'i, 'l + 'l) lit set) =
  ∀tr.
    is_inf_trace circ reset next cnstrs latches tr ⇒
    ∃k. ∀i. k ≤ i ⇒ preds_hold (pair_state (tr k) (tr (k + 1))) qcirc live
End


(* Implementation *************************************************************)

Definition is_transition_def:
  is_transition ss (circ: ('a, 'i, 'l + 'l) circuit)
    (next: 'l + 'l -> ('a, 'i, 'l + 'l) lit) (ls: 'l set) =
  ∀l. l ∈ ls ⇒
      (eval_lit ss circ (Base (Latch (INR l)), F) ⇔
       eval_lit ss circ (next (INL l)))
End

(* Extension types for names *)
Datatype:
  ext = Orig 'a | Ext mlstring
End

Type iext[pp] = “:'a ext + num”

Definition iname_def:
  iname (v,b) =
    case v of Name (INR n) => n
    | _ => 0
End

Theorem eval_lit_INR_neq:
  iname m ≠ n ⇒
  (eval_lit ss ((INR n, xs)::circ) m ⇔ eval_lit ss circ m)
Proof
  simp [oneline iname_def] >> every_case_tac >> rw [eval_circuit_def]
QED

Definition maxn_def:
  maxn (ls : ('a iext,'i,'l) lit list) =
    MAX_LIST (MAP iname ls) + 1
End

Definition not_def:
  not ((v, b): ('a,'i,'l) lit) = (v, ¬b)
End

Theorem iname_not[simp]:
  iname (not x) = iname x
Proof
  Cases_on ‘x’ >> simp [not_def, iname_def]
QED

Theorem eval_lit_not:
  eval_lit ss circ (not x) ⇔ ¬eval_lit ss circ x
Proof
  Cases_on ‘x’ >> simp [not_def, eval_lit_flip]
QED

Definition equiv_aux_def:
  (equiv_aux (n: num) [] = [(INR n, [])]: ('a iext,'i,'l) circuit) ∧
  (equiv_aux n (xy::xys) =
   let (x, y) = xy in [
    (INR n, [
        (Name (INR (n + 1)), T);
        (Name (INR (n + 2)), T);
        (Name (INR (n + 3)), F)
      ]);
    (INR (n + 1), [x; not y]);
    (INR (n + 2), [not x; y]);
   ] ++ equiv_aux (n + 3) xys)
End

Definition equiv_def:
  equiv (circ: ('a iext, 'i, 'l) circuit) name xys =
    let n = MAX (maxn (MAP FST xys)) (maxn (MAP SND xys)) in
      ((INL (Ext name), [(Name (INR n), F)])::equiv_aux n xys) ++ circ
End

Theorem eval_circuit_equiv_aux_INL[simp]:
  ∀xys n.
    eval_circuit ss (equiv_aux n xys ++ circ) (INL out) ⇔
    eval_circuit ss circ (INL out)
Proof
  Induct
  >> rw [equiv_aux_def, eval_circuit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_circuit_def]
QED

Theorem eval_lit_equiv_aux_neq:
  ∀xys n.
    iname m < n ⇒
    (eval_lit ss (equiv_aux n xys ++ circ) m ⇔
     eval_lit ss circ m)
Proof
  Induct >> rw [equiv_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_INR_neq]
QED

Theorem eval_circuit_equiv_aux_INR_eq:
  ∀xys n.
    EVERY (λ(x, y). iname x < n ∧ iname y < n) xys ⇒
    (eval_circuit ss (equiv_aux n xys ++ circ) (INR n) ⇔
    EVERY (λ(x,y). eval_lit ss circ x ⇔ eval_lit ss circ y) xys)
Proof
  Cases_on ‘ss’
  >> Induct
  >> rw [equiv_aux_def, eval_circuit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_circuit_def]
  >> DEP_REWRITE_TAC [eval_lit_INR_neq]
  >> conj_tac >- simp []
  >> DEP_REWRITE_TAC [eval_lit_equiv_aux_neq]
  >> conj_tac >- simp []
  >> first_x_assum $ qspec_then ‘n + 3’ mp_tac
  >> impl_tac
  >-
   (gvs [EVERY_MEM]
    >> rpt strip_tac
    >> first_x_assum drule >> simp []
    >> rpt (pairarg_tac >> gvs []))
  >> strip_tac >> simp []
  >> metis_tac [eval_lit_not]
QED

Theorem eval_circuit_equiv_INL:
  eval_circuit ss (equiv circ name xys) (INL n) =
  if n = Ext name then
    EVERY (λ(x,y). eval_lit ss circ x ⇔ eval_lit ss circ y) xys
  else eval_circuit ss circ (INL n)
Proof
  Cases_on ‘ss’ >> rw [eval_circuit_def, equiv_def]
  >> irule eval_circuit_equiv_aux_INR_eq
  >> rw [maxn_def, EVERY_MEM]
  >> rpt (pairarg_tac >> gvs [])
  >> ‘MEM (iname x) (MAP iname (MAP FST xys)) ∧
      MEM (iname y) (MAP iname (MAP SND xys))’
    by metis_tac[MEM_MAP, FST, SND]
  >> imp_res_tac MAX_LIST_PROPERTY >> simp []
QED

Definition encode_is_reset_def:
  encode_is_reset ss (circ: ('a iext, 'i, 'l) circuit) name
    (reset: 'l -> ('a iext,'i,'l) lit) (ls: 'l list) =
  equiv circ name (ZIP (MAP (λl. (Base (Latch l), F)) ls, MAP reset ls))
End

Theorem eval_circuit_encode_is_reset_INL:
  eval_circuit ss (encode_is_reset ss circ name reset ls) (INL n) =
  if n = Ext name then
    is_reset ss circ reset (set ls)
  else eval_circuit ss circ (INL n)
Proof
  Cases_on ‘ss’
  >> rw [eval_circuit_def, encode_is_reset_def, eval_circuit_equiv_INL]
  >> simp [is_reset_def]
  >> eq_tac >> rw []
  >-
   (gvs [EVERY_MEM]
    >> rename1 ‘MEM l _’
    >> first_x_assum $ qspec_then ‘((Base (Latch l), F), reset l)’ mp_tac
    >> impl_tac >- simp [ZIP_MAP, MEM_MAP, PULL_EXISTS]
    >> simp [])
  >> rw [EVERY_MEM, ZIP_MAP, MEM_MAP] >> simp []
QED

(* Pairing circuits ***********************************************************)

(* Combines two circuits into one, keeping them separate using the sum type. *)

Definition left_bvar_def:
  (left_bvar (Input i) = Input (INL i)) ∧
  (left_bvar (Latch l) = Latch (INL l)) ∧
  (left_bvar Ff        = Ff)
End

Definition left_var_def:
  (left_var (Name a)  = Name (INL a)) ∧
  (left_var (Base bv) = Base (left_bvar bv))
End

Definition left_lit_def:
  left_lit (v, b) = (left_var v, b)
End

Definition left_and_def:
  left_and (n, ins) = (INL n, MAP left_lit ins)
End

Definition right_bvar_def:
  (right_bvar (Input i) = Input (INR i)) ∧
  (right_bvar (Latch l) = Latch (INR l)) ∧
  (right_bvar Ff        = Ff)
End

Definition right_var_def:
  (right_var (Name a)  = Name (INR a)) ∧
  (right_var (Base bv) = Base (right_bvar bv))
End

Definition right_lit_def:
  right_lit (v, b) = (right_var v, b)
End

Definition right_and_def:
  right_and (n, ins) = (INR n, MAP right_lit ins)
End

Definition pair_circuits_def:
  pair_circuits (circ₁: ('a₁, 'i₁, 'l₁) circuit)
    (circ₂: ('a₂, 'i₂, 'l₂) circuit) =
  MAP left_and circ₁ ++ MAP right_and circ₂
End

Theorem pair_circuits_left_cons:
  pair_circuits (a::circ₁) circ₂ =
  left_and a::(pair_circuits circ₁ circ₂)
Proof
  simp [pair_circuits_def]
QED

Theorem pair_circuits_left_nil_right_cons:
  pair_circuits [] (a::circ₂) =
  right_and a::(pair_circuits [] circ₂)
Proof
  simp [pair_circuits_def]
QED

Theorem eval_circuit_pair_left_nil_INL[local]:
  ¬eval_circuit ss (pair_circuits [] circ) (INL n)
Proof
  Induct_on ‘circ’ >> rw []
  >> gvs [pair_circuits_def, eval_circuit_def]
  >> rename1 ‘right_and a’ >> Cases_on ‘a’
  >> simp [right_and_def]
QED

Theorem eval_circuit_pair_left_nil_INR[local]:
  (∀n.
     eval_circuit (pair_state ss₁ ss₂)
       (pair_circuits ([]: ('a, 'i, 'l) circuit) circ) (INR n) =
     eval_circuit ss₂ circ n) ∧
  (∀m.
     eval_lit (pair_state ss₁ ss₂)
       (pair_circuits ([]: ('a, 'i, 'l) circuit) circ) (right_lit m) =
     eval_lit ss₂ circ m)
Proof
  Induct_on ‘circ’ >> rw []
  >- simp [pair_circuits_def, eval_circuit_def]
  >-
   (Cases_on ‘m’ >> simp [pair_circuits_def, right_lit_def]
    >> rename1 ‘right_var x’ >> Cases_on ‘x’
    >> simp [right_var_def, eval_circuit_def]
    >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [pair_state_def]
    >> rename1 ‘right_bvar b’ >> Cases_on ‘b’
    >> simp [right_bvar_def, eval_bvar_def])
  >> simp [pair_circuits_left_nil_right_cons]
  >-
   (rename1 ‘right_and a’ >> Cases_on ‘a’
    >> simp [right_and_def, eval_circuit_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> rename1 ‘right_lit m’ >> Cases_on ‘m’
  >> simp [right_lit_def]
  >> rename1 ‘right_var x’ >> Cases_on ‘x’
  >> simp [right_var_def, eval_circuit_def]
  >-
   (rename1 ‘right_and y’ >> Cases_on ‘y’
    >> simp [right_and_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [pair_state_def]
  >> rename1 ‘right_bvar b’ >> Cases_on ‘b’
  >> simp [right_bvar_def, eval_bvar_def]
QED

Theorem eval_lit_pair_left_nil_left[local]:
  eval_lit (pair_state ss₁ ss₂) (pair_circuits [] circ₂) (left_lit n) =
  eval_lit ss₁ [] n
Proof
  Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [pair_state_def]
  >> Induct_on ‘circ₂’ >> gvs [pair_circuits_def]
  >> Cases_on ‘n’ >> gvs [left_lit_def]
  >-
   (rename1 ‘left_var v’ >> Cases_on ‘v’
    >> simp [left_var_def, eval_circuit_def]
    >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
    >> simp [left_bvar_def, eval_bvar_def])
  >> Cases >> simp [right_and_def]
  >> rename1 ‘left_var v’ >> Cases_on ‘v’
  >> gvs [left_var_def, eval_circuit_def]
  >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
  >> simp [left_bvar_def, eval_bvar_def]
QED

Theorem eval_pair_left[simp]:
  (∀n.
     eval_circuit (pair_state ss₁ ss₂) (pair_circuits circ₁ circ₂) (INL n) =
     eval_circuit ss₁ circ₁ n) ∧
  (∀m.
     eval_lit (pair_state ss₁ ss₂) (pair_circuits circ₁ circ₂) (left_lit m) =
     eval_lit ss₁ circ₁ m)
Proof
  Induct_on ‘circ₁’ >> rw [eval_circuit_def]
  >- simp [eval_circuit_pair_left_nil_INL]
  >- simp [eval_lit_pair_left_nil_left]
  >> simp [pair_circuits_left_cons]
  >-
   (simp [eval_circuit_def]
    >> rename1 ‘left_and a’ >> Cases_on ‘a’
    >> simp [left_and_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> rename1 ‘left_lit m’ >> Cases_on ‘m’
  >> simp [left_lit_def]
  >> rename1 ‘left_var v’ >> Cases_on ‘v’
  >> simp [eval_circuit_def, left_var_def]
  >-
   (rename1 ‘left_and b’ >> Cases_on ‘b’
    >> simp [eval_circuit_def, left_and_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> gvs [pair_state_def]
  >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
  >> simp [left_bvar_def, eval_bvar_def]
QED

Theorem eval_pair_right[simp]:
  (∀n.
    eval_circuit (pair_state ss₁ ss₂) (pair_circuits circ₁ circ₂) (INR n) =
    eval_circuit ss₂ circ₂ n) ∧
  (∀m.
    eval_lit (pair_state ss₁ ss₂) (pair_circuits circ₁ circ₂) (right_lit m) =
    eval_lit ss₂ circ₂ m)
Proof
  Induct_on ‘circ₁’ >> rw [eval_circuit_def]
  >- simp [eval_circuit_pair_left_nil_INR]
  >- simp [eval_circuit_pair_left_nil_INR]
  >> simp [pair_circuits_left_cons]
  >-
   (rename1 ‘left_and a’ >> Cases_on ‘a’
    >> simp [left_and_def, eval_circuit_def])
  >> rename1 ‘right_lit m’ >> Cases_on ‘m’
  >> simp [right_lit_def]
  >> rename1 ‘right_var x’ >> Cases_on ‘x’
  >> simp [eval_circuit_def, right_var_def]
  >-
   (rename1 ‘left_and g’ >> Cases_on ‘g’
    >> simp [left_and_def, eval_circuit_def])
  >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> gvs [pair_state_def]
  >> rename1 ‘right_bvar b’ >> Cases_on ‘b’
  >> simp [right_bvar_def, eval_bvar_def]
QED

(* Transition Function ********************************************************)

Definition encode_is_transition_def:
  encode_is_transition ss (circ: ('a iext, 'i, 'l + 'l) circuit) name
    (next: 'l + 'l -> ('a iext, 'i, 'l + 'l) lit) (ls: 'l list) =
  equiv circ name
    (ZIP (MAP (λl. (Base (Latch (INR l)), F)) ls, MAP (next ∘ INL) ls))
End

Theorem eval_circuit_encode_is_transition_INL:
  eval_circuit ss (encode_is_transition ss circ name next ls) (INL n) =
  if n = Ext name then
    is_transition ss circ next (set ls)
  else eval_circuit ss circ (INL n)
Proof
  Cases_on ‘ss’
  >> rw [eval_circuit_def, encode_is_transition_def, eval_circuit_equiv_INL]
  >> simp [is_transition_def]
  >> eq_tac >> rw []
  >-
   (gvs [EVERY_MEM]
    >> rename1 ‘MEM l _’
    >> first_x_assum $ qspec_then
         ‘((Base (Latch (INR l)), F), next (INL l))’ mp_tac
    >> impl_tac >- simp [ZIP_MAP, MEM_MAP, PULL_EXISTS]
    >> simp [])
  >> rw [EVERY_MEM, ZIP_MAP, MEM_MAP] >> simp []
QED

(* Lifting to iext ************************************************************)

Definition iext_var_def:
  (iext_var (Name (a: 'a))  = Name ((INL (Orig a)): 'a iext)) ∧
  (iext_var (Base bv) = Base bv)
End

Definition iext_lit_def:
  iext_lit (v, b) = (iext_var v, b)
End

Definition iext_and_def:
  iext_and ((n, ins): ('a, 'i, 'l) and) =
  (INL (Orig n), MAP iext_lit ins): ('a iext, 'i, 'l) and
End

Definition iext_circuit_def:
  iext_circuit circ = MAP iext_and circ
End

Theorem eval_circuit_iext_circuit[simp]:
  (∀n.
     eval_circuit ss (iext_circuit circ) (INL (Orig n)) =
     eval_circuit ss circ n) ∧
  ∀l. eval_lit ss (iext_circuit circ) (iext_lit l) = eval_lit ss circ l
Proof
  Induct_on ‘circ’ >> rw [iext_circuit_def, eval_circuit_def]
  >-
   (Cases_on ‘l’ >> simp [iext_lit_def]
    >> rename1 ‘iext_var v’ >> Cases_on ‘v’ >> simp [iext_var_def]
    >> simp [eval_circuit_def])
  >-
   (rename1 ‘iext_and a’ >> Cases_on ‘a’ >> simp [iext_and_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP])
  >> Cases_on ‘l’ >> simp [iext_lit_def]
  >> rename1 ‘iext_var v’ >> Cases_on ‘v’ >> simp [iext_var_def]
  >> simp [eval_circuit_def]
  >> rename1 ‘iext_and b’ >> Cases_on ‘b’ >> simp [iext_and_def]
  >> IF_CASES_TAC >> gvs [EVERY_MAP]
QED

(* Merging circuit ************************************************************)
(* Merging two circuits results in a new circuit where the inputs and latches
   are shared. *)

Definition left_name_var_def:
  (left_name_var (Name a)  = Name (INL a)) ∧
  (left_name_var (Base bv) = Base bv)
End

Definition left_name_lit_def:
  left_name_lit (v, b) = (left_name_var v, b)
End

Definition left_name_and_def:
  left_name_and (n, ins) = (INL n, MAP left_name_lit ins)
End

Definition right_name_var_def:
  (right_name_var (Name a)  = Name (INR a)) ∧
  (right_name_var (Base bv) = Base bv)
End

Definition right_name_lit_def:
  right_name_lit (v, b) = (right_name_var v, b)
End

Definition right_name_and_def:
  right_name_and (n, ins) = (INR n, MAP right_name_lit ins)
End

Definition merge_circuits_def:
  merge_circuits (circ₁: ('a₁, 'i, 'l) circuit) (circ₂: ('a₂, 'i, 'l) circuit) =
    (MAP left_name_and circ₁ ++ MAP right_name_and circ₂)
    :('a₁ + 'a₂, 'i, 'l) circuit
End

Theorem merge_circuits_left_cons:
  merge_circuits (a::circ₁) circ₂ =
  left_name_and a::(merge_circuits circ₁) circ₂
Proof
  simp [merge_circuits_def]
QED

Theorem merge_circuits_left_nil_right_cons:
  merge_circuits [] (a::circ) =
  right_name_and a::(merge_circuits [] circ)
Proof
  simp [merge_circuits_def]
QED

Theorem eval_circuit_merge_circuits_left_nil_INL[local]:
  ¬eval_circuit ss (merge_circuits [] circ) (INL n)
Proof
  Induct_on ‘circ’ >> rw [merge_circuits_def, eval_circuit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rename1 ‘right_name_and a’
  >> Cases_on ‘a’ >> gvs [right_name_and_def, merge_circuits_def]
QED

Theorem eval_lit_merge_circuits_left_nil_left[local]:
  eval_lit ss (merge_circuits [] circ) (left_name_lit m) ⇔
  eval_lit ss [] m
Proof
  Induct_on ‘circ’
  >> Cases_on ‘m’ >> fs [left_name_lit_def]
  >> rename1 ‘left_name_var x’ >> Cases_on ‘x’ >> fs [left_name_var_def]
  >> fs [merge_circuits_def, eval_circuit_def]
  >> Cases >> simp [right_name_and_def]
QED

Theorem eval_circuit_merge_circuits_left_nil_INR[local]:
  (∀n.
     eval_circuit ss (merge_circuits ([]: ('a, 'i, 'l) circuit) circ) (INR n) =
     eval_circuit ss circ n) ∧
  (∀m.
     eval_lit ss (merge_circuits ([]: ('a, 'i, 'l) circuit) circ) (right_name_lit m) =
     eval_lit ss circ m)
Proof
  Induct_on ‘circ’ >> rw []
  >- simp [merge_circuits_def]
  >-
   (simp [merge_circuits_def]
    >> Cases_on ‘m’ >> simp [right_name_lit_def]
    >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
    >> simp [eval_circuit_def])
  >> simp [merge_circuits_left_nil_right_cons]
  >-
   (simp [eval_circuit_def]
    >> rename1 ‘right_name_and h’ >> Cases_on ‘h’ >> simp [right_name_and_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP])
  >> Cases_on ‘m’ >> simp [right_name_lit_def]
  >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
  >> simp [eval_circuit_def]
  >> rename1 ‘right_name_and h’ >> Cases_on ‘h’ >> simp [right_name_and_def]
  >> IF_CASES_TAC >> gvs [EVERY_MAP]
QED

Theorem eval_circuit_merge_circuits_left:
  (∀n.
     eval_circuit ss (merge_circuits circ₁ circ₂) (INL n) =
     eval_circuit ss circ₁ n) ∧
  (∀m.
     eval_lit ss (merge_circuits circ₁ circ₂) (left_name_lit m) =
     eval_lit ss circ₁ m)
Proof
  Induct_on ‘circ₁’ >> rw []
  >- simp [eval_circuit_merge_circuits_left_nil_INL]
  >- simp [eval_lit_merge_circuits_left_nil_left]
  >> simp [merge_circuits_left_cons]
  >-
   (simp [eval_circuit_def]
    >> rename1 ‘left_name_and a’ >> Cases_on ‘a’ >> simp [left_name_and_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP])
  >> rename1 ‘left_name_lit m’ >> Cases_on ‘m’ >> simp [left_name_lit_def]
  >> rename1 ‘left_name_var v’ >> Cases_on ‘v’ >> simp [left_name_var_def]
  >> simp [eval_circuit_def]
  >> rename1 ‘left_name_and b’ >> Cases_on ‘b’ >> simp [left_name_and_def]
  >> IF_CASES_TAC >> gvs [EVERY_MAP]
QED

Theorem eval_circuit_merge_circuits_right:
  (∀n.
     eval_circuit ss (merge_circuits circ₁ circ₂) (INR n) =
     eval_circuit ss circ₂ n) ∧
  (∀m.
     eval_lit ss (merge_circuits circ₁ circ₂) (right_name_lit m) =
     eval_lit ss circ₂ m)
Proof
  Induct_on ‘circ₁’ >> rw []
  >- simp [eval_circuit_merge_circuits_left_nil_INR]
  >- simp [eval_circuit_merge_circuits_left_nil_INR]
  >> simp [merge_circuits_left_cons]
  >-
   (rename1 ‘left_name_and a’ >> Cases_on ‘a’ >> simp [left_name_and_def]
    >> simp [eval_circuit_def])
  >> Cases_on ‘m’ >> simp [right_name_lit_def]
  >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
  >> rename1 ‘left_name_and h’ >> Cases_on ‘h’ >> simp [left_name_and_def]
  >> simp [eval_circuit_def]
QED

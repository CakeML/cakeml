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

Definition not_def:
  not ((v, b): ('a,'i,'l) lit) = (v, ¬b)
End

Theorem eval_lit_not:
  eval_lit ss circ (not x) ⇔ ¬eval_lit ss circ x
Proof
  Cases_on ‘x’ >> simp [not_def, eval_lit_flip]
QED

(*
EVAL``eval_lit (is,ls) circ TT``
EVAL``eval_lit (is,ls) circ FF``
*)

Definition pair_state_def:
  pair_state (is₁,ls₁) (is₂,ls₂) =
    ((λi. sum_CASE i is₁ is₂), (λl. sum_CASE l ls₁ ls₂))
End

Theorem pair_state_surj:
  ∀s. ∃s₁ s₂. s = pair_state s₁ s₂
Proof
  namedCases ["is ls"]
  >> qexistsl_tac [‘(is ∘ INL, ls ∘ INL)’, ‘(is ∘ INR, ls ∘ INR)’]
  >> simp [pair_state_def, FUN_EQ_THM]
  >> conj_tac >> Cases >> simp []
QED

Theorem FORALL_PAIR_STATE:
  (∀s. P s) ⇔ (∀s₁ s₂. P (pair_state s₁ s₂))
Proof
  metis_tac [pair_state_surj]
QED

Definition preds_hold_def:
  preds_hold ss (circ: ('a, 'i, 'l) circuit)
    (ns: ('a,'i,'l) lit set) =
  (∀n. n ∈ ns ⇒ eval_lit ss circ n)
End

Definition is_reset_def:
  is_reset ss (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit option) (ls: 'l set) =
  ∀lat lit.
    lat ∈ ls ∧ reset lat = SOME lit ⇒
    eval_lit ss circ (Base (Latch lat), F) =
    eval_lit ss circ lit
End

Definition is_next_def:
  is_next ss₀ (circ: ('a, 'i, 'l) circuit)
    (next: 'l -> ('a,'i,'l) lit) (latches: 'l set) ls₁ =
  ∀l. l ∈ latches ⇒
      eval_lit ss₀ circ (next l) = ls₁ l
End

Definition is_trace_def:
  is_trace (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (tr: ('i, 'l) trace) (n: num)
  ⇔
    (is_reset (tr 0) circ reset latches ∧
     preds_hold (tr 0) circ cnstrs) ∧
    ∀i. i < n ⇒
      is_next (tr i) circ next latches (SND (tr (i + 1))) ∧
      preds_hold (tr (i + 1)) circ cnstrs
End

Definition is_unsafe_def:
  is_unsafe (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set) (safe: ('a,'i,'l) lit set)
  =
  ∃(tr: ('i, 'l) trace) (n: num).
    is_trace circ reset next cnstrs latches tr n ∧
    ¬preds_hold (tr n) circ safe
End

Definition is_safe_def:
  is_safe (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
    (cnstrs: ('a,'i,'l) lit set) (latches: 'l set)
    (safe: ('a,'i,'l) lit set) ⇔
  ¬is_unsafe circ reset next cnstrs latches safe
End

(* Liveness *******************************************************************)

Definition is_inf_trace_def:
  is_inf_trace (circ: ('a, 'i, 'l) circuit)
    (reset: 'l -> ('a,'i,'l) lit option) (next: 'l -> ('a,'i,'l) lit)
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
  is_live (circ: ('a, 'i, 'l) circuit) (reset: 'l -> ('a,'i,'l) lit option)
    (next: 'l -> ('a,'i,'l) lit) (cnstrs: ('a,'i,'l) lit set)
    (qcirc: ('b, 'i + 'i, 'l + 'l) circuit)
    (live: ('b, 'i + 'i, 'l + 'l) lit list list) (latches: 'l set) =
  ∀tr.
    is_inf_trace circ reset next cnstrs latches tr ⇒
    ∀prop. MEM prop live ⇒
      ∃k signal.
        MEM signal prop ∧
        (∀i. k ≤ i ⇒
             preds_hold (pair_state (tr i) (tr (i + 1))) qcirc {signal})
End

(* Circuit Dependencies *******************************************************)

(* While state and input are defined over the entirety of (potentially infinite)
   domains, a circuit can only depend on a finite subset of these domains, as
   we have a finite amount of gates.
   We formalize this notion in dep_circuit. *)

Definition agree_on_def:
  agree_on (inputs: 'i set) (latches: 'l set) (is', ls') (is, ls) ⇔
    (∀i. i ∈ inputs  ⇒ is' i = is i) ∧
    (∀l. l ∈ latches ⇒ ls' l = ls l)
End

Definition matching_transition_def:
  matching_transition inputs latches tr i j ⇔
    i < j ∧
    agree_on inputs latches (tr j) (tr i) ∧
    agree_on inputs latches (tr (j + 1)) (tr (i + 1))
End

(* Used Inputs ****************************************************************)

Definition bvar_inputs_def:
  (bvar_inputs (Input i) = [i]) ∧
  (bvar_inputs _         = [])
End

Definition var_inputs_def:
  (var_inputs (Base bv) = bvar_inputs bv) ∧
  (var_inputs (Name _)  = [])
End

Definition lit_inputs_def:
  lit_inputs (v, b) = var_inputs v
End

Definition and_inputs_def:
  and_inputs ((_, lits): ('a,'i,'l) and) = FLAT (MAP lit_inputs lits)
End

Definition circuit_inputs_def:
  circuit_inputs (circ: ('a,'i,'l) circuit) = FLAT (MAP and_inputs circ)
End

(* Used Latches ****************************************************************)

Definition bvar_latches_def:
  (bvar_latches (Latch l) = [l]) ∧
  (bvar_latches _         = [])
End

Definition var_latches_def:
  (var_latches (Base bv) = bvar_latches bv) ∧
  (var_latches (Name _)  = [])
End

Definition lit_latches_def:
  lit_latches (v, b) = var_latches v
End

Definition and_latches_def:
  and_latches ((_, lits): ('a,'i,'l) and) = FLAT (MAP lit_latches lits)
End

Definition circuit_latches_def:
  circuit_latches (circ: ('a,'i,'l) circuit) = FLAT (MAP and_latches circ)
End

(* Syntactic Dependencies *****************************************************)

Definition dep_circuit_def:
  dep_circuit inputs latches circ =
  ∀n ss' ss.
    agree_on inputs latches ss' ss
    ⇒
    eval_circuit ss' circ n = eval_circuit ss circ n
End

Definition dep_bvar_def[simp]:
  (dep_bvar inputs latches Ff        ⇔ T) ∧
  (dep_bvar inputs latches (Input i) ⇔ i ∈ inputs) ∧
  (dep_bvar inputs latches (Latch l) ⇔ l ∈ latches)
End

Definition dep_var_def[simp]:
  (dep_var inputs latches (Name _)  = T) ∧
  (dep_var inputs latches (Base bv) = dep_bvar inputs latches bv)
End

Definition dep_lit_def[simp]:
  dep_lit inputs latches (v, b) = dep_var inputs latches v
End

Definition dep_lits_def:
  dep_lits inputs latches (lits: ('a,'i,'l) lit set) ⇔
    ∀lit. lit ∈ lits ⇒ dep_lit inputs latches lit
End

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

Definition is_stratified_def:
  is_stratified lt circ reset latches ⇔
    ∀lat lit is ls' ls.
      lat ∈ latches ∧ reset lat = SOME lit ∧
      (∀l. l ∈ { l' | lt l' l } ⇒ (ls' l ⇔ ls l)) ⇒
      eval_lit (is,ls') circ lit ⇔ eval_lit (is,ls) circ lit
End

Definition patch_def:
  (patch circ reset is (ls: 'l state) ([]: 'l list) = ls) ∧
  (patch circ reset is ls (latch::rest) =
   patch circ reset is
     (λl.
        if l = latch then
          (case reset l of
           | NONE => ls l
           | SOME lit => eval_lit (is, ls) circ lit)
        else ls l) rest)
End

Theorem not_mem_patch_eq:
  ∀xs ls. ¬MEM l xs ⇒ (patch circ reset is ls xs) l = ls l
Proof
  Induct >> rw [patch_def]
QED

Theorem is_reset_insert_NONE:
  reset l = NONE ⇒
  (is_reset ss circ reset (l INSERT ls) ⇔
     is_reset ss circ reset ls)
Proof
  rw [is_reset_def] >> eq_tac >> rw [] >> gvs []
QED

Theorem is_reset_insert_SOME:
  reset l = SOME lit ⇒
  (is_reset ss circ reset (l INSERT ls) ⇔
     is_reset ss circ reset ls ∧
     (eval_lit ss circ (Base (Latch l),F) ⇔ eval_lit ss circ lit))
Proof
  rw [is_reset_def] >> eq_tac >> rw [] >> gvs []
QED

Theorem is_reset_union:
  is_reset ss circ reset (xs ∪ ys) ⇔
    is_reset ss circ reset xs ∧ is_reset ss circ reset ys
Proof
  rw [is_reset_def] >> metis_tac []
QED

Theorem subset_is_reset_patch:
  ∀xs ls.
    is_stratified lt circ reset latches ∧ set xs ⊆ latches ∧
    SORTED lt xs ∧ irreflexive lt ∧ transitive lt
    ⇒
    is_reset (is, patch circ reset is ls xs) circ reset (set xs)
Proof
  Induct >> rw [patch_def]
  >- simp [is_reset_def]
  >> rename1 ‘reset lat’
  >> namedCases_on ‘reset lat’ ["", "lit"] >> gvs []
  >-
   (simp [Req0 is_reset_insert_NONE]
    >> last_x_assum irule
    >> drule SORTED_TL >> simp [])
  >> drule_then assume_tac is_reset_insert_SOME
  >> simp []
  >> conj_tac
  >- (last_x_assum irule >> drule SORTED_TL >> simp [])
  >> simp [eval_circuit_def]
  >> rename1 ‘l::xs’
  >> ‘¬MEM l xs’ by (drule_all SORTED_ALL_DISTINCT >> simp [])
  >> drule_then assume_tac not_mem_patch_eq >> simp []
  >> fs [is_stratified_def]
  >> qmatch_goalsub_abbrev_tac ‘_ ⇔ eval_lit (is, ls') _ _’
  >> last_x_assum $ qspecl_then [‘l’, ‘lit’, ‘is’, ‘ls'’, ‘ls’] mp_tac
  >> fs [irreflexive_def]
QED

Theorem dep_eval_lit_eq:
  ∀n ss' ss.
    dep_circuit inputs latches circ ∧
    dep_lit inputs latches n ∧
    agree_on inputs latches ss' ss ⇒
    (eval_lit ss' circ n ⇔ eval_lit ss circ n)
Proof
  namedCases ["v b"]
  >> namedCases ["is' ls'"]
  >> namedCases ["is ls"]
  >> Cases_on ‘v’ >> rw [eval_circuit_def]
  >-
   (fs [dep_circuit_def]
    >> rename1 ‘eval_circuit _ _ a’
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

Theorem circuit_inputs_cons:
  circuit_inputs (h::circ) = and_inputs h ++ circuit_inputs circ
Proof
  simp [circuit_inputs_def]
QED

Theorem circuit_latches_cons:
  circuit_latches (h::circ) = and_latches h ++ circuit_latches circ
Proof
  simp [circuit_latches_def]
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

Theorem dep_circuit_subset:
  dep_circuit xs ys circ ∧ xs ⊆ xs' ∧ ys ⊆ ys'
  ⇒
  dep_circuit xs' ys' circ
Proof
  rw [dep_circuit_def] >> metis_tac [agree_on_weaken]
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
  MEM l ls ⇒
  dep_lit (set (and_inputs (n,ls))) (set (and_latches (n,ls))) l
Proof
  namedCases_on ‘l’ ["b v"] >> simp [dep_lit_def]
  >> namedCases_on ‘b’ ["n", "bv"] >> simp [dep_var_def]
  >> Cases_on ‘bv’ >> simp [dep_bvar_def]
  >> rw [and_latches_def, and_inputs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS]
  >> first_assum $ irule_at Any
  >> simp [lit_inputs_def, var_inputs_def, bvar_inputs_def, lit_latches_def,
           var_latches_def, bvar_latches_def]
QED

Theorem dep_circuit_inputs_latches:
  dep_circuit (set (circuit_inputs circ)) (set (circuit_latches circ)) circ
Proof
  Induct_on ‘circ’ >- simp [dep_circuit_def]
  >> rw [dep_circuit_def]
  >> fs [circuit_inputs_cons, circuit_latches_cons]
  >> rename1 ‘h::_’ >> namedCases_on ‘h’ ["n ls"]
  >> gvs [eval_circuit_def]
  >> IF_CASES_TAC >> gvs []
  >-
   (irule EVERY_CONG >> rw []
    >> irule dep_eval_lit_eq
    >> qpat_assum ‘agree_on _ _ _ _’ $ irule_at Any
    >> irule_at (Pos hd) dep_circuit_subset
    >> first_assum $ irule_at (Pos hd)
    >> simp []
    >> irule_at (Pos hd) dep_lit_subset
    >> irule_at (Pos hd) dep_lit_and
    >> first_assum $ irule_at (Pos hd)
    >> qexists ‘n’ >> simp [])
  >> fs [dep_circuit_def]
  >> first_assum irule
  >> fs [agree_on_union]
QED

(* Extending a trace for the model to a trace for the witness *****************)

Theorem agree_on_sym:
  agree_on inputs latches ss ss' = agree_on inputs latches ss' ss
Proof
  Cases_on ‘ss’ >> Cases_on ‘ss'’ >> eq_tac >> rw [agree_on_def]
QED

Definition traces_agree_def:
  traces_agree n inputs latches (tr': ('i, 'l) trace) tr ⇔
    ∀i. i ≤ n ⇒ agree_on inputs latches (tr' i) (tr i)
End

Theorem is_next_subset:
  is_next ss circ next latches  ls ∧ latches' ⊆ latches ⇒
  is_next ss circ next latches' ls
Proof
  rw [is_next_def] >> metis_tac [SUBSET_DEF]
QED

Theorem is_next_dep_circuit:
  is_next ss₀ circ next latches ls₁ ∧
  (∀l. l ∈ latches' ⇒ ls₁ l = ls₁' l) ∧
  agree_on inputs latches' ss₀ ss₀' ∧
  dep_circuit inputs latches' circ ∧
  dep_latch_lit inputs latches' next latches ∧
  latches ⊆ latches'
  ⇒
  is_next ss₀' circ next latches ls₁'
Proof
  rw [is_next_def, dep_latch_lit_def]
  >> fs[SUBSET_DEF]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem preds_hold_dep_circuit:
  preds_hold ss circ ns ∧
  dep_circuit inputs latches circ ∧
  dep_lits inputs latches ns ∧
  agree_on inputs latches ss ss'
  ⇒
  preds_hold ss' circ ns
Proof
  rw [preds_hold_def, dep_lits_def]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem is_reset_dep_circuit:
  is_reset ss circ reset latches ∧
  dep_circuit inputs latches circ ∧
  dep_reset inputs latches reset latches ∧
  agree_on inputs latches ss ss'
  ⇒
  is_reset ss' circ reset latches
Proof
  rw [is_reset_def, dep_reset_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> last_x_assum $ drule_then assume_tac
  >> gvs [eval_circuit_def]
  >> metis_tac [dep_eval_lit_eq, agree_on_def]
QED

Theorem is_trace_dep_circuit:
  is_trace circ reset next cnstrs latches tr n ∧
  dep_circuit inputs latches circ ∧
  dep_lits inputs latches cnstrs ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  traces_agree n inputs latches tr' tr
  ⇒
  is_trace circ reset next cnstrs latches tr' n
Proof
  rw [traces_agree_def, is_trace_def, agree_on_sym]
  >-
   (irule is_reset_dep_circuit >> simp []
    >> last_assum $ irule_at (Pos last)
    >> last_assum $ irule_at (Pos last)
    >> gvs [])
  >-
   (irule preds_hold_dep_circuit >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp []
    >> first_assum $ irule_at (Pos hd) >> simp [])
  >-
   (last_x_assum $ drule_then assume_tac
    >> irule is_next_dep_circuit >> fs []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> first_assum $ irule_at (Pos last) >> simp []
    >> rename1 ‘SND (tr (i + 1))’
    >> Cases_on ‘tr (i + 1)’ >> Cases_on ‘tr' (i + 1)’ >> fs []
    >> first_x_assum $ qspec_then ‘i + 1’ mp_tac
    >> simp [agree_on_def])
  >> last_x_assum $ drule_then assume_tac
  >> irule preds_hold_dep_circuit >> fs []
  >> first_assum $ irule_at (Pos last) >> simp []
QED

Theorem is_inf_trace_dep_circuit:
  is_inf_trace circ reset next cnstrs latches tr ∧
  dep_circuit inputs latches circ ∧
  dep_lits inputs latches cnstrs ∧
  dep_reset inputs latches reset latches ∧
  dep_latch_lit inputs latches next latches ∧
  (∀n. traces_agree n inputs latches tr' tr)
  ⇒
  is_inf_trace circ reset next cnstrs latches tr'
Proof
  rw [is_inf_trace_eq] >> metis_tac[is_trace_dep_circuit]
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
  traces_agree (SUC n) inputs latches tr' tr ⇔
    traces_agree n inputs latches tr' tr ∧
    agree_on inputs latches (tr' (n + 1)) (tr (n + 1))
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

Theorem is_reset_dep_latch_lit:
  is_reset ss circ reset latches ∧
  dep_circuit inputs latches circ ∧
  dep_reset inputs latches reset latches ∧
  agree_on inputs latches ss ss'
  ⇒
  is_reset ss' circ reset latches
Proof
  rw [is_reset_def, dep_reset_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> namedCases_on ‘ss'’ ["is' ls'"]
  >> gvs[eval_circuit_def]
  >> metis_tac [dep_eval_lit_eq, agree_on_def]
QED

Definition pair_set_def:
  pair_set xs = IMAGE INL xs ∪ IMAGE INR xs
End

Definition dep_qcirc_def:
  dep_qcirc inputs qcirc live latches ⇔
    dep_circuit (pair_set inputs) (pair_set latches) qcirc ∧
    dep_lits (pair_set inputs) (pair_set latches) (set (FLAT live))
End

Theorem is_safe_is_inf_trace_preds_hold:
  is_safe circ reset next cnstrs latches preds ∧
  is_inf_trace circ reset next cnstrs latches tr
  ⇒
  ∀n. preds_hold (tr n) circ preds
Proof
  rw [is_safe_def, is_unsafe_def, is_inf_trace_eq]
  >> metis_tac []
QED

Theorem is_inf_trace_cnstrs_hold:
  is_inf_trace circ reset next cnstrs latches tr
  ⇒
  ∀n. preds_hold (tr n) circ cnstrs
Proof
  rw [is_inf_trace_def] >> Cases_on ‘n’ >> gvs [ADD1]
QED

Theorem is_inf_trace_is_next:
  is_inf_trace circ reset next cnstrs latches tr
  ⇒
  ∀n. is_next (tr n) circ next latches (SND (tr (n + 1)))
Proof
  rw [is_inf_trace_def]
QED

Theorem agree_on_pair:
  agree_on (pair_set inputs) (pair_set latches)
    (pair_state ss₀ ss₁) (pair_state ss₂ ss₃)
  ⇔
  (agree_on inputs latches ss₀ ss₂ ∧ agree_on inputs latches ss₁ ss₃)
Proof
  map_every PairCases_on [‘ss₀’, ‘ss₁’, ‘ss₂’, ‘ss₃’]
  >> rw [pair_state_def, agree_on_def, pair_set_def]
  >> metis_tac [sum_case_def]
QED

Theorem agree_on_refl[simp]:
  agree_on inputs latches ss ss
Proof
  Cases_on ‘ss’ >> simp [agree_on_def]
QED

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

Theorem is_inf_trace_traces_agree:
  (∀n.
     is_trace mcirc mreset mnext mcnstrs mlatches tr n ⇒
     is_trace wcirc wreset wnext wcnstrs wlatches tr' n ∧
     traces_agree n UNIV mlatches tr' tr)
  ⇒
    (is_inf_trace mcirc mreset mnext mcnstrs mlatches tr ⇒
     is_inf_trace wcirc wreset wnext wcnstrs wlatches tr' ∧
     (∀n. traces_agree n UNIV mlatches tr' tr))
Proof
  rw [is_inf_trace_eq]
QED

Definition restrict_ss_def:
  restrict_ss (inputs : 'i set) (latches : 'l set)
              ((is, ls) : 'i inputs # 'l state) =
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
  ∀inputs latches tr.
    FINITE inputs ∧ FINITE latches ⇒
    ∃k. ∀i. k < i ⇒
      ∃j. matching_transition inputs latches (tr: ('i, 'l) trace) i j
Proof
  rw []
  >> qabbrev_tac ‘g = λi.
       (restrict_ss inputs latches (tr i),
        restrict_ss inputs latches (tr (i + 1)))’
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

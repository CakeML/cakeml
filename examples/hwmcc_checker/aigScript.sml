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

Definition signal_imply_def:
  signal_imply ss circ ss' circ' signals signals' =
  LIST_REL (λq q'. preds_hold ss circ {q} ⇒ preds_hold ss' circ' {q'})
    signals signals'
End

Definition lives_imply_def:
  lives_imply ss₀ ss₁ wqcirc mqcirc wlive mlive =
  LIST_REL (λQ Q'. signal_imply ss₀ wqcirc ss₁ mqcirc Q Q') wlive mlive
End

Definition some_signal_holds_def:
  some_signal_holds ss circ signals =
  EXISTS (λp. preds_hold ss circ {p}) signals
End

Definition lives_hold_def:
  lives_hold ss circ live = EVERY (some_signal_holds ss circ) live
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

Theorem lives_hold_dep_circuit:
  lives_hold ss circ ns ∧
  dep_circuit inputs latches circ ∧
  dep_lits inputs latches (set (FLAT ns)) ∧
  agree_on inputs latches ss ss'
  ⇒
  lives_hold ss' circ ns
Proof
  rw [lives_hold_def, EVERY_MEM, dep_lits_def, some_signal_holds_def,
          EXISTS_MEM, MEM_FLAT, preds_hold_def]
  >> metis_tac [dep_eval_lit_eq]
QED

Theorem lives_hold_matching_transition:
  lives_hold (pair_state (tr (i + 2)) (tr (i + 1))) qcirc live ∧
  matching_transition inputs latches tr i (i + 2) ∧
  dep_circuit (pair_set inputs) (pair_set latches) qcirc ∧
  dep_lits (pair_set inputs) (pair_set latches) (set (FLAT live))
  ⇒
  lives_hold (pair_state (tr i) (tr (i + 1))) qcirc live
Proof
  rw []
  >> irule lives_hold_dep_circuit
  >> qpat_x_assum ‘lives_hold _ _ _’ $ irule_at Any
  >> first_assum $ irule_at (Pos hd) >> simp []
  >> fs [agree_on_pair, matching_transition_def]
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

Definition latch_reset_pairs_def:
  (latch_reset_pairs (reset: 'l -> ('a iext,'i,'l) lit option) ([]: 'l list) = []) ∧
  (latch_reset_pairs reset (l::ls) =
     case reset l of
     | NONE   => latch_reset_pairs reset ls
     | SOME r => ((Base (Latch l), F), r) :: latch_reset_pairs reset ls)
End

Definition encode_is_reset_def:
  encode_is_reset ss (circ: ('a iext, 'i, 'l) circuit) name reset ls =
  equiv circ name (latch_reset_pairs reset ls)
End

Theorem MEM_latch_reset_pairs_eq:
  MEM ((Base (Latch l),F),lit) (latch_reset_pairs reset ls)
  ⇔
  MEM l ls ∧ reset l = SOME lit
Proof
  Induct_on ‘ls’
  >> rw [latch_reset_pairs_def]
  >> TOP_CASE_TAC
  >> eq_tac >> rw [] >> gvs []
QED

Theorem exists_MEM_latch_reset_pairs:
  MEM ll (latch_reset_pairs reset ls) ⇒
  ∃lat lit. ll = ((Base (Latch lat), F), lit)
Proof
  Induct_on ‘ls’
  >> simp [latch_reset_pairs_def]
  >> gen_tac
  >> TOP_CASE_TAC
  >> rw [] >> gvs []
QED

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
    >> first_x_assum $ qspec_then ‘((Base (Latch l), F), lit)’ mp_tac
    >> impl_tac >- simp [MEM_latch_reset_pairs_eq]
    >> simp [])
  >> rw [EVERY_MEM]
  >> drule_then assume_tac exists_MEM_latch_reset_pairs
  >> gvs [MEM_latch_reset_pairs_eq]
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

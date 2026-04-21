(*
  Formalization of And-Inverter Graphs
*)
Theory aig
Ancestors
  misc mlstring
Libs
  preamble

val _ = numLib.prefer_num();

(* Things that appear in base positions *)
Datatype:
  bvar = Ff | Input 'i | Latch 'l
End

Datatype:
  var = Name 'a | Base (('i,'l) bvar)
End

Type inputs = “:'i -> bool”
Type state = “:'l -> bool”

Definition eval_bvar_def:
  (eval_bvar (is: 'i inputs, ls: 'l state) Ff = F) ∧
  (eval_bvar (is,ls) (Input i) = is i) ∧
  (eval_bvar (is,ls) (Latch l) = ls l)
End

Type lit[pp] = “:('a,'i,'l) var # bool”
Type and[pp] = “:'a # (('a,'i,'l) lit # ('a,'i,'l) lit)”
Type circuit[pp] = “:('a,'i,'l) and list”

Overload TT =``(Base Ff, T)``
Overload FF =``(Base Ff, F)``

Definition eval_circuit_def:
  (eval_lit (ss : 'i inputs # 'l state)
    circ ((v,b):('a,'i,'l) lit) =
    case v of
    | Base bv => b ⇎ eval_bvar ss bv
    | Name n => eval_circuit ss circ n) ∧
  (eval_circuit ss ([]:('a,'i,'l) circuit) n = F) ∧
  (eval_circuit ss (h::tl) n =
   let (n', (in₁, in₂)) = h in
     if n' = n then
       (eval_lit ss tl in₁) ∧
       (eval_lit ss tl in₂)
     else
       eval_circuit ss tl n)
End

(*
EVAL``eval_lit (is,ls) circ TT``
EVAL``eval_lit (is,ls) circ FF``
*)

Definition next_state_def:
  next_state ss (circ: ('a, 'i, 'l) circuit)
    (next: 'l -> ('a,'i,'l) lit) =
  eval_lit ss circ ∘ next
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
      eval_lit ss circ (reset l) =
      eval_lit ss circ (Base (Latch l), T)
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

Definition maxn_def:
  maxn (ls : ('a iext,'i,'l) lit list) =
    MAX_LIST (MAP iname ls) + 1
End

(* TODO conj_def *)
Definition conj_aux_def:
  (conj_aux (n: num) ([]: ('a iext,'i,'l) lit list) =
    [ (INR n, TT, TT) ]:('a iext,'i,'l) circuit) ∧
  (conj_aux (n: num) (x::xs) =
    (INR n, x, (Name (INR (n+1)),T))
      ::conj_aux (n + 1) xs )
End

Definition conj_def:
  conj (circ: ('a iext, 'i, 'l) circuit) name xs =
    let n = maxn xs in
    ((INL (Ext name), (Name (INR n), T), (Name (INR n), T))
      ::conj_aux n xs) ++ circ
End

Theorem eval_circuit_conj_aux_INL[simp]:
  ∀xs n.
    eval_circuit ss (conj_aux n xs ++ circ) (INL out) ⇔
    eval_circuit ss circ (INL out)
Proof
  Cases_on ‘ss’ >> Induct >> rw [conj_aux_def, eval_circuit_def]
QED

Theorem eval_circuit_conj_aux_INR:
  ∀xs n.
    m < n ⇒
    (eval_circuit ss (conj_aux n xs ++ circ) (INR m) ⇔
    eval_circuit ss circ (INR m))
Proof
  Cases_on ‘ss’
  >> Induct
  >> rw [conj_aux_def, eval_circuit_def, eval_bvar_def]
QED

Theorem eval_circuit_conj_aux_INR:
  ∀xs n.
    EVERY (λx. iname x < n) xs ⇒
    (eval_circuit ss (conj_aux n xs ++ circ) (INR n) ⇔
    EVERY (eval_lit ss circ) xs)
Proof
  Cases_on ‘ss’
  >> Induct
  >> rw [conj_aux_def, eval_circuit_def, eval_bvar_def]
  >> first_x_assum (qspec_then `n+1` mp_tac)
  >> impl_tac >-
    (drule_at_then Any irule EVERY_MONOTONIC>>rw[])
  >> rw[]
  >> fs[oneline iname_def]
  >> every_case_tac>>simp[eval_circuit_def]
  >> DEP_REWRITE_TAC[eval_circuit_conj_aux_INR]
  >> gvs[]
QED

Theorem eval_circuit_conj_INL:
  eval_circuit ss (conj circ name xs) (INL n) =
  if n = Ext name then
    EVERY (eval_lit ss circ) xs
  else eval_circuit ss circ (INL n)
Proof
  Cases_on ‘ss’ >>
  rw [eval_circuit_def, conj_def]>>
  irule eval_circuit_conj_aux_INR>>
  rw[maxn_def,EVERY_MEM]>>
  `MEM (iname x) (MAP iname xs)` by metis_tac[MEM_MAP]>>
  drule MAX_LIST_PROPERTY>>
  simp[]
QED

(* --- old --- *)

Datatype:
  gate = And ('a # bool) ('a # bool) | Latch 'l | Input 'i | Const bool
End

Type state = “:'l -> bool”
Type inputs = “:'i -> bool”
Type circuit[pp] = “:('a, ('a, 'l, 'i) gate) alist”
(* We will refer to the elements of the circuit as nodes. *)

Definition eval_circuit_def:
  (eval_circuit (s: 'l state, is: 'i inputs) ([]: ('a, 'l, 'i) circuit) (out: 'a) = F) ∧
  eval_circuit (s, is) ((a, g)::rest) out =
    if a = out then
     (case g of
      | Const b => b
      | Latch l => s l
      | Input i => is i
      | And (g₁, b₁) (g₂, b₂) =>
          (b₁ ⇔ eval_circuit (s, is) rest g₁) ∧
          (b₂ ⇔ eval_circuit (s, is) rest g₂))
    else eval_circuit (s, is) rest out
End

Definition next_state_def:
  next_state sis (circ: ('a, 'l, 'i) circuit) (next: 'l -> 'a) =
  eval_circuit sis circ ∘ next
End

Definition is_reset_def:
  is_reset (s, is) (circ: ('a, 'l, 'i) circuit) (reset: 'l -> 'a) =
  ∀l. eval_circuit (s, is) circ (reset l) = s l
End

Definition preds_hold_def:
  preds_hold sis (circ: ('a, 'l, 'i) circuit) (xs: 'a set) =
  ∀x. x ∈ xs ⇒ eval_circuit sis circ x
End

Definition is_trace_def:
  is_trace (circ: ('a, 'l, 'i) circuit) (reset: 'l -> 'a) (next: 'l -> 'a)
    (cnstr: 'a set) (tr: num -> 'l state # 'i inputs)
  ⇔
    (∃is. let (s, _) = tr 0 in is_reset (s, is) circ reset) ∧
    ∀i.
      let (s, _) = tr (i + 1) in
      next_state (tr i) circ next = s ∧
      preds_hold (tr i) circ cnstr
End

Definition is_safe_def:
  is_safe (circ: ('a, 'l, 'i) circuit) (reset: 'l -> 'a) (next: 'l -> 'a)
    (cnstr: 'a set) (safe: 'a set) ⇔
    ∀tr.
      is_trace circ reset next cnstr tr ⇒ ∀i. preds_hold (tr i) circ safe
End

(* Cs ∧ C′s ∧ P′s → Ps *)

(* Place and-gates into separate namespace - used when merging witness and
   model circuits. In particular, the circuits will share inputs and latches. *)
Definition leftify_gate_and_def:
  (leftify_gate_and (And (a₁, b₁) (a₂, b₂)) = And (INL a₁, b₁) (INL a₂, b₂)) ∧
  (leftify_gate_and (Latch l) = Latch l) ∧
  (leftify_gate_and (Input i) = Input i) ∧
  (leftify_gate_and (Const b) = Const b)
End

Definition rightify_gate_and_def:
  (rightify_gate_and (And (a₁, b₁) (a₂, b₂)) = And (INR a₁, b₁) (INR a₂, b₂)) ∧
  (rightify_gate_and (Latch l) = Latch l) ∧
  (rightify_gate_and (Input i) = Input i) ∧
  (rightify_gate_and (Const b) = Const b)
End

Definition leftify_node_and_def:
  leftify_node_and (a, g) = (INL a, leftify_gate_and g)
End

Definition rightify_node_and_def:
  rightify_node_and (a, g) = (INR a, rightify_gate_and g)
End

Definition rightify_and_def:
  rightify_and circ = MAP rightify_node_and circ
End

Definition leftify_and_def:
  leftify_and circ = MAP leftify_node_and circ
End

(* "Merges" two circuits by having them share inputs and latches.

   This function assumes that the latches and inputs of left are a superset
   of those of right. If we consider the left circuit to be the witness, it is
   probably possible to have a preprocessing step that adjusts the witness
   latches and inputs to look something like this:

   ┌──────┬────────────────────────────────────┬────────────┐
   │shared│model-only (dummy/unused in witness)│witness-only│
   └──────┴────────────────────────────────────┴────────────┘
   ▲
   start
 *)

Definition merge_circuits_def:
  merge_circuits
    (left: ('a₁, 'l₁, 'i₁) circuit) (right: ('a₂, 'l₁, 'i₁) circuit) =
  leftify_and left ++ rightify_and right
End

Theorem leftify_and_nil[simp]:
  leftify_and [] = []
Proof
  simp [leftify_and_def]
QED

Theorem rightify_and_nil[simp]:
  rightify_and [] = []
Proof
  simp [rightify_and_def]
QED

Theorem eval_circuit_nil:
  eval_circuit sis [] out = F
Proof
  Cases_on ‘sis’ >> simp [eval_circuit_def]
QED

Theorem eval_circuit_rightify_node_and_INL[local]:
  ∀circ. eval_circuit sis (MAP rightify_node_and circ) (INL out) = F
Proof
  Cases_on ‘sis’
  >> Induct >> rw []
  >- simp [eval_circuit_nil]
  >> rename1 ‘rightify_node_and h’
  >> Cases_on ‘h’ >> simp [rightify_node_and_def]
  >> simp [eval_circuit_def]
QED

Theorem eval_circuit_rightify_and_INL:
  eval_circuit sis (rightify_and circ) (INL out) = F
Proof
  simp [rightify_and_def, eval_circuit_rightify_node_and_INL]
QED

Theorem eval_circuit_leftify_node_and_INL[local]:
  ∀circ out.
    eval_circuit sis (MAP leftify_node_and circ) (INL out) =
    eval_circuit sis circ out
Proof
  Cases_on ‘sis’
  >> Induct >> rw []
  >- simp [eval_circuit_nil]
  >> rename1 ‘leftify_node_and h’
  >> namedCases_on ‘h’ ["a g"]
  >> simp [leftify_node_and_def]
  >> simp [eval_circuit_def]
  >> IF_CASES_TAC >> gvs []
  >> Cases_on ‘g’ >> gvs [leftify_gate_and_def]
  >> rename1 ‘And g₁ g₂’
  >> PairCases_on ‘g₁’ >> PairCases_on ‘g₂’
  >> gvs [leftify_gate_and_def]
QED

Theorem eval_circuit_leftify_and_INL:
  eval_circuit sis (leftify_and circ) (INL out) ⇔
  eval_circuit sis circ out
Proof
  simp [leftify_and_def, eval_circuit_leftify_node_and_INL]
QED

Theorem eval_circuit_leftify_and_rightify_and_INL:
  ∀circ₁ out.
    eval_circuit sis (leftify_and circ₁ ++ rightify_and circ₂) (INL out) ⇔
    eval_circuit sis (leftify_and circ₁) (INL out)
Proof
  Induct >> simp [eval_circuit_nil, eval_circuit_rightify_and_INL]
  >> namedCases ["a g"] >> gen_tac >> Cases_on ‘sis’
  >> gvs [leftify_and_def, leftify_node_and_def, eval_circuit_def]
  >> IF_CASES_TAC >> gvs []
  >> Cases_on ‘g’ >> gvs [leftify_gate_and_def]
  >> rename1 ‘And g₁ g₂’
  >> PairCases_on ‘g₁’ >> PairCases_on ‘g₂’
  >> gvs [leftify_gate_and_def]
QED

Theorem eval_circuit_merge_circuits_INL:
  eval_circuit sis (merge_circuits circ₁ circ₂) (INL out) =
  eval_circuit sis circ₁ out
Proof
  simp [merge_circuits_def, eval_circuit_leftify_and_rightify_and_INL,
        eval_circuit_leftify_and_INL]
QED

(* TODO change to mlstring *)
Datatype:
  ext = Orig 'a | Ext (char list)
End

Type iext[pp] = “:'a ext + num”

Definition conj_aux_def:
  (conj_aux (n: num) ([]: 'a ext list) = [(INR n, Const T)]) ∧
  (conj_aux n (x::xs) =
   (INR n, And (INL x, T) (INR (n + 1), T))::conj_aux (n + 1) xs)
End

Definition conj_def:
  conj (circ: ('a iext, 'i, 'l) circuit) name xs =
    ((INL (Ext name), And (INR 0, T) (INR 0, T))::conj_aux 0 xs) ++ circ
End

Theorem eval_circuit_conj_aux_INL[simp]:
  ∀xs n.
    eval_circuit sis (conj_aux n xs ++ circ) (INL out) ⇔
    eval_circuit sis circ (INL out)
Proof
  Cases_on ‘sis’ >> Induct >> rw [conj_aux_def, eval_circuit_def]
QED

Theorem eval_circuit_conj_aux_INR:
  ∀xs n.
    eval_circuit sis (conj_aux n xs ++ circ) (INR n) ⇔
    EVERY (eval_circuit sis circ ∘ INL) xs
Proof
  Cases_on ‘sis’
  >> Induct >> rw [conj_aux_def, eval_circuit_def]
QED

Theorem eval_circuit_conj_INL:
  eval_circuit sis (conj circ name xs) (INL out) =
  if out = Ext name then EVERY (eval_circuit sis circ ∘ INL) xs
  else eval_circuit sis circ (INL out)
Proof
  Cases_on ‘sis’ >> rw [eval_circuit_def, conj_def, eval_circuit_conj_aux_INR]
QED

Definition encode_preds_def:
  encode_preds (circ₀: ('a iext, 'i, 'l) circuit) rs rks cs ps =
  let
    circ₁ = conj circ₀ "R" (MAP Orig rs);
    circ₂ = conj circ₁ "RK" (MAP Orig rks);
    circ₃ = conj circ₂ "C" (MAP Orig cs);
  in
    conj circ₃ "P" (MAP Orig ps)
End

Theorem eval_circuit_encode_preds:
  eval_circuit sis (encode_preds circ rs rks cs ps) (INL (Ext "R")) =
  preds_hold sis circ (set (MAP (INL ∘ Orig) rs)) ∧
  eval_circuit sis (encode_preds circ rs rks cs ps) (INL (Ext "RK")) =
  preds_hold sis circ (set (MAP (INL ∘ Orig) rks)) ∧
  eval_circuit sis (encode_preds circ rs rks cs ps) (INL (Ext "C")) =
  preds_hold sis circ (set (MAP (INL ∘ Orig) cs)) ∧
  eval_circuit sis (encode_preds circ rs rks cs ps) (INL (Ext "P")) =
  preds_hold sis circ (set (MAP (INL ∘ Orig) ps))
Proof
  rw [encode_preds_def, eval_circuit_conj_INL, EVERY_MAP, preds_hold_def,
      EVERY_MEM, MEM_MAP]
  >> metis_tac []
QED

(**************************)


(* Place all gates into separate namespace - used when combining independent
   circuits, such as copies of the same circuit to represent different
   time steps. In particular, the circuits will have disjoint inputs and
   latches. *)
Definition leftify_gate_def:
  (leftify_gate (And (a₁, b₁) (a₂, b₂)) = And (INL a₁, b₁) (INL a₂, b₂)) ∧
  (leftify_gate (Latch l) = Latch (INL l)) ∧
  (leftify_gate (Input i) = Input (INL i)) ∧
  (leftify_gate (Const b) = Const b)
End

Definition rightify_gate_def:
  (rightify_gate (And (a₁, b₁) (a₂, b₂)) = And (INR a₁, b₁) (INR a₂, b₂)) ∧
  (rightify_gate (Latch l) = Latch (INR l)) ∧
  (rightify_gate (Input i) = Input (INR i)) ∧
  (rightify_gate (Const b) = Const b)
End

Definition leftify_node_def:
  leftify_node (a, g) = (INL a, leftify_gate g)
End

Definition rightify_node_def:
  rightify_node (a, g) = (INR a, rightify_gate g)
End

Definition rightify_def:
  rightify circ = MAP rightify_node circ
End

Definition leftify_def:
  leftify circ = MAP leftify_node circ
End


Theorem leftify_nil[simp]:
  leftify [] = []
Proof
  simp [leftify_def]
QED

Theorem rightify_nil[simp]:
  leftify [] = []
Proof
  simp [rightify_def]
QED

Theorem is_reset_nil:
  is_reset (s, is) [] reset ⇔ s = λx. F
Proof
  rw [is_reset_def, eval_circuit_nil] >> metis_tac []
QED

Theorem is_reset_rightify_and_INL:
  is_reset (s, is) (rightify_and circ) (λl. INL (reset l)) ⇔
  s = λx. F
Proof
  rw [is_reset_def, rightify_and_def, eval_circuit_rightify_and_INL]
  >> metis_tac []
QED

Theorem is_reset_merge_circuits_INL:
  ∀circ₁ sis circ₂ reset.
    is_reset sis (merge_circuits circ₁ circ₂) (λl. INL (reset l)) ⇔
    is_reset sis circ₁ reset
Proof
  Cases_on ‘sis’ >> simp [is_reset_def, eval_circuit_merge_circuits_INL]
QED

(* spo = strict partial order *)
Theorem stratification_reset_exists:
  is_stratified reset spo circ is ⇒ ∃s. is_reset sis circ reset
Proof
  cheat
QED

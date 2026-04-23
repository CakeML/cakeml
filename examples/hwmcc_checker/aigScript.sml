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
  (eval_lit (ss : 'i inputs # 'l state)
    circ ((v,b):('a,'i,'l) lit) =
    case v of
    | Base bv => b ⇎ eval_bvar ss bv
    | Name n => b ⇎ eval_circuit ss circ n) ∧
  (eval_circuit ss ([]:('a,'i,'l) circuit) n = F) ∧
  (eval_circuit ss (h::tl) n =
   let (n', ins) = h in
     if n' = n then EVERY (eval_lit ss tl) ins
     else eval_circuit ss tl n)
End

Theorem eval_lit_flip:
  eval_lit ss circ (v,¬b) ⇔ ¬eval_lit ss circ (v,b)
Proof
  once_rewrite_tac [eval_circuit_def] >> CASE_TAC >> metis_tac []
QED

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
      eval_lit ss circ (Base (Latch l), F) =
      eval_lit ss circ (reset l)
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

Definition pair_state_def:
  pair_state (is₁,ls₁) (is₂,ls₂) =
    ((λi. sum_CASE i is₁ is₂), (λl. sum_CASE l ls₁ ls₂))
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

Definition is_transition_def:
  is_transition ss (circ: ('a, 'i, 'l + 'l) circuit)
    (next: 'l + 'l -> ('a, 'i, 'l + 'l) lit) (ls: 'l set) =
  ∀l. l ∈ ls ⇒
      (eval_lit ss circ (Base (Latch (INR l)), F) ⇔
       next_state ss circ next (INL l))
End

Definition encode_is_transition_def:
  encode_is_transition ss (circ: ('a iext, 'i, 'l + 'l) circuit) name
    (next: 'l + 'l -> ('a iext, 'i, 'l + 'l) lit) (ls: 'l list) =
  equiv circ name
    (ZIP (MAP (λl. (Base (Latch (INR l)), F)) ls, MAP (next ∘ INL) ls))
End

Theorem eval_circuit_encode_is_reset_INL:
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
    >> simp [next_state_def])
  >> rw [EVERY_MEM, ZIP_MAP, MEM_MAP] >> simp [next_state_def]
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

(*
  Encodes the certificate conditions as an AIG.
*)
Theory aig_cert_encode
Ancestors
  aig aig_cert
Libs
  preamble

(* todo check which theorems/simps are actually used *)
(* todo check whether it is possible to reduce the amount of
   definitions/theorems *)

Theorem eval_lit_base:
  eval_lit ss circ (Base (Latch l), b) ⇔ (b ⇎ SND ss l)
Proof
  Cases_on ‘ss’ >> simp [eval_circuit_def]
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

Theorem eval_circuit_merge_circuits_left[simp]:
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

Theorem eval_circuit_merge_circuits_right[simp]:
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

(* Liveness circuits (qcirc) **************************************************)

(* Liveness circuits (qcirc) have access to two different states.
   For model circuits this is not needed; inputs and outputs (not gates) are
   lifted to INL.
   In contrast, witness circuits need to make use of this. For this, the
   intervention function maps literals to latches in the other state.
   Thus, we go through the circuit and for each literal present as a key in the
   intervention map, we replace it by INR x, where x is the value in the
   intervention map.
   If the literal is not present, we lift inputs/outputs to INL. *)

Definition qleft_bvar_def:
  (qleft_bvar : ('i, 'l) bvar -> ('i + 'i, 'l + 'l) bvar
     (Input i) = Input (INL i)) ∧
  (qleft_bvar (Latch l) = Latch (INL l)) ∧
  (qleft_bvar Ff        = Ff)
End

Definition qleft_var_def:
  (qleft_var (Name a)  = Name a) ∧
  (qleft_var (Base bv) = Base (qleft_bvar bv))
End

Definition qleft_lit_def:
  qleft_lit (v, b) = (qleft_var v, b)
End

Definition qleft_and_def:
  qleft_and (n, ins) = (n, MAP qleft_lit ins)
End

Definition qleft_live_def:
  qleft_live (live: ('a, 'i, 'l) lit list list) = MAP (MAP qleft_lit) live
End

Definition qleft_def:
  qleft (circ: ('a, 'i, 'l) circuit) = MAP qleft_and circ
End

Definition qinterv_lit_def:
  qinterv_lit (interv: ('a, 'i, 'l) lit -> 'l option) lit =
  case interv lit of
  | NONE => qleft_lit lit
  | SOME l =>
    let (v, b) = lit in (Base (Latch (INR l)), b)
End

Definition qinterv_and_def:
  qinterv_and interv ((n, ins): ('a, 'i, 'l) and) =
    (n, MAP (qinterv_lit interv) ins)
End

Definition qinterv_live_def:
  qinterv_live interv (live: ('a, 'i, 'l) lit list list) =
    MAP (MAP (qinterv_lit interv)) live
End

Definition qinterv_def:
  qinterv interv (circ: ('a, 'i, 'l) circuit) = MAP (qinterv_and interv) circ
End

(* Extending a circuit ********************************************************)

(* Named extensions *)
Datatype:
  ext = Orig 'a | Ext mlstring
End

(* Numbered extensions; used for "anonymous" intermediates *)
Datatype:
  iext = Named ('a ext) | Anon num
End

(* Lifting to iext *)

Definition iext_var_def:
  (iext_var (Name a) = Name (Named (Orig a))) ∧
  (iext_var (Base bv) = Base bv)
End

Definition iext_lit_def:
  iext_lit (v, b) = (iext_var v, b)
End

Definition iext_and_def:
  iext_and ((n, ins): ('a, 'i, 'l) and) =
  (Named (Orig n), MAP iext_lit ins)
End

Definition iext_circuit_def:
  iext_circuit circ = MAP iext_and circ
End

Theorem eval_lit_Named_Ext_iext_lit[simp]:
  eval_lit ss ((Named (Ext name),lits)::circ) (iext_lit x) ⇔
   eval_lit ss circ (iext_lit x)
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [iext_lit_def, iext_var_def, eval_circuit_def]
QED

Theorem eval_lit_Anon_iext_lit[simp]:
  eval_lit ss ((Anon n,lits)::circ) (iext_lit x) ⇔
   eval_lit ss circ (iext_lit x)
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [iext_lit_def, iext_var_def, eval_circuit_def]
QED

Theorem eval_circuit_iext_circuit[simp]:
  (∀n.
     eval_circuit ss (iext_circuit circ) (Named (Orig n)) =
     eval_circuit ss circ n) ∧
  (∀l. eval_lit ss (iext_circuit circ) (iext_lit l) = eval_lit ss circ l) ∧
  (∀l. eval_lit ss (iext_circuit circ) (Base bv, b) = eval_lit ss circ (Base bv, b))
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

Definition iname_def:
  iname (v,b) =
    case v of Name (Anon n) => n
    | _ => 0
End

Theorem iname_not[simp]:
  iname (not x) = iname x
Proof
  Cases_on ‘x’ >> simp [not_def, iname_def]
QED

Theorem iname_iext_lit[simp]:
  iname (iext_lit x) = 0
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [iext_lit_def, iext_var_def, iname_def]
QED

Theorem eval_lit_Anon_neq:
  iname m ≠ n ⇒
  (eval_lit ss ((Anon n, xs)::circ) m ⇔ eval_lit ss circ m)
Proof
  simp [oneline iname_def] >> every_case_tac >> rw [eval_circuit_def]
QED

(* Getting the next available number to use as intermediate *)
Definition maxn_def:
  maxn (ls : ('a iext,'i,'l) lit list) =
    MAX_LIST (MAP iname ls) + 1
End

Theorem MEM_neq_iname_maxn:
  MEM z xs ∨ MEM z ys ⇒ iname z ≠ MAX (maxn xs) (maxn ys)
Proof
  disch_tac
  >> ‘MEM (iname z) (MAP iname xs) ∨ MEM (iname z) (MAP iname ys)’ by
    metis_tac [MEM_MAP]
  >> imp_res_tac MAX_LIST_PROPERTY
  >> simp [maxn_def, MAX_DEF]
QED

(* Encoding implication *******************************************************)

(* b ⇔ negated implication *)
Definition encode_imply_def:
  encode_imply (circ: ('a iext, 'i, 'l) circuit) name b lhss rhss =
  let n = MAX (maxn lhss) (maxn rhss) in
    (* b = F: (lhss ⇒ rhss) ⇔ (¬lhss ∨ rhss) ⇔ ¬(lhss ∧ ¬rhss) *)
    (Named (Ext name), [(Name (Anon (n+2)), ¬b)])
    ::(Anon (n+2), [(Name (Anon n), F); (Name (Anon (n+1)), T)]) (* lhss ∧ ¬rhss *)
    ::(Anon (n+1), rhss)::(Anon n, lhss)::circ
End

Theorem eval_circuit_encode_imply:
  eval_circuit ss (encode_imply circ name b lhss rhss) (Named n) =
  if n = Ext name then
    (b ⇎ ((EVERY (eval_lit ss circ) lhss) ⇒ (EVERY (eval_lit ss circ) rhss)))
  else eval_circuit ss circ (Named n)
Proof
  eq_tac
  >> rw [encode_imply_def, eval_circuit_def, EVERY_MEM, EXISTS_MEM]
  >> gvs []
  >- metis_tac [MEM_neq_iname_maxn, eval_lit_Anon_neq]
  >> Cases_on ‘∃e. MEM e lhss ∧ ¬eval_lit ss circ e’ >> fs []
  >- metis_tac []
  >> qpat_x_assum ‘∀e. ¬MEM e lhss ∨ _’ $
       assume_tac o PURE_REWRITE_RULE [GSYM IMP_DISJ_THM]
  >> metis_tac [MEM_neq_iname_maxn, eval_lit_Anon_neq]
QED

(* Encoding point-wise equivalence ********************************************)

Definition encode_equiv_aux_def:
  (encode_equiv_aux (n: num) [] = [(Anon n, [])]: ('a iext,'i,'l) circuit) ∧
  (encode_equiv_aux n (xy::xys) =
   let (x, y) = xy in [
    (Anon n, [
        (Name (Anon (n + 1)), T);
        (Name (Anon (n + 2)), T);
        (Name (Anon (n + 3)), F)
      ]);
    (Anon (n + 1), [x; not y]);
    (Anon (n + 2), [not x; y]);
   ] ++ encode_equiv_aux (n + 3) xys)
End

Definition encode_equiv_def:
  encode_equiv (circ: ('a iext, 'i, 'l) circuit) name xys =
    let n = MAX (maxn (MAP FST xys)) (maxn (MAP SND xys)) in
      ((Named (Ext name), [(Name (Anon n), F)])::encode_equiv_aux n xys) ++ circ
End

Theorem eval_circuit_encode_equiv_aux_Named[local,simp]:
  ∀xys n.
    eval_circuit ss (encode_equiv_aux n xys ++ circ) (Named out) ⇔
    eval_circuit ss circ (Named out)
Proof
  Induct
  >> rw [encode_equiv_aux_def, eval_circuit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_circuit_def]
QED

Theorem eval_lit_encode_equiv_aux_neq:
  ∀xys n.
    iname m < n ⇒
    (eval_lit ss (encode_equiv_aux n xys ++ circ) m ⇔
     eval_lit ss circ m)
Proof
  Induct >> rw [encode_equiv_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_Anon_neq]
QED

Theorem eval_circuit_encode_equiv_aux_Anon_eq:
  ∀xys n.
    EVERY (λ(x, y). iname x < n ∧ iname y < n) xys ⇒
    (eval_circuit ss (encode_equiv_aux n xys ++ circ) (Anon n) ⇔
    EVERY (λ(x,y). eval_lit ss circ x ⇔ eval_lit ss circ y) xys)
Proof
  Cases_on ‘ss’
  >> Induct
  >> rw [encode_equiv_aux_def, eval_circuit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_circuit_def]
  >> DEP_REWRITE_TAC [eval_lit_Anon_neq]
  >> conj_tac >- simp []
  >> DEP_REWRITE_TAC [eval_lit_encode_equiv_aux_neq]
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

Theorem eval_circuit_encode_equiv_Named:
  eval_circuit ss (encode_equiv circ name xys) (Named n) =
  if n = Ext name then
    EVERY (λ(x,y). eval_lit ss circ x ⇔ eval_lit ss circ y) xys
  else eval_circuit ss circ (Named n)
Proof
  Cases_on ‘ss’ >> rw [eval_circuit_def, encode_equiv_def]
  >> irule eval_circuit_encode_equiv_aux_Anon_eq
  >> rw [maxn_def, EVERY_MEM]
  >> rpt (pairarg_tac >> gvs [])
  >> ‘MEM (iname x) (MAP iname (MAP FST xys)) ∧
      MEM (iname y) (MAP iname (MAP SND xys))’
    by metis_tac[MEM_MAP, FST, SND]
  >> imp_res_tac MAX_LIST_PROPERTY >> simp []
QED

Theorem eval_lit_encode_equiv_Named:
  eval_lit ss (encode_equiv circ name xys) (Name (Named n), b) =
  if n = Ext name then
    b ⇎ EVERY (λ(x,y). eval_lit ss circ x ⇔ eval_lit ss circ y) xys
  else eval_lit ss circ (Name (Named n), b)
Proof
  simp [eval_circuit_def, eval_circuit_encode_equiv_Named]
  >> IF_CASES_TAC >> gvs []
QED

Theorem eval_lit_encode_equiv_iext_lit[simp]:
  eval_lit ss (encode_equiv circ name xys) (iext_lit n) =
  eval_lit ss circ (iext_lit n)
Proof
  namedCases_on ‘n’ ["v b"] >> Cases_on ‘v’
  >> simp [iext_lit_def, iext_var_def, encode_equiv_def, eval_circuit_def]
QED

(* Encoding is_reset **********************************************************)

Definition latch_reset_pairs_def:
  (latch_reset_pairs (reset: 'l -> ('a iext,'i,'l) lit option) ([]: 'l list) = []) ∧
  (latch_reset_pairs reset (l::ls) =
     case reset l of
     | NONE   => latch_reset_pairs reset ls
     | SOME r => ((Base (Latch l), F), r) :: latch_reset_pairs reset ls)
End

Definition encode_is_reset_def:
  encode_is_reset (circ: ('a iext, 'i, 'l) circuit) name reset ls =
  encode_equiv circ name (latch_reset_pairs reset ls)
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

Theorem eval_circuit_encode_is_reset_Named:
  eval_circuit ss (encode_is_reset circ name reset ls) (Named n) =
  if n = Ext name then
    is_reset ss circ reset (set ls)
  else eval_circuit ss circ (Named n)
Proof
  Cases_on ‘ss’
  >> rw [eval_circuit_def, encode_is_reset_def, eval_circuit_encode_equiv_Named]
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

Theorem eval_lit_encode_is_reset_Named:
  eval_lit ss (encode_is_reset circ name reset ls) (Name (Named n),F) =
  if n = Ext name then
    is_reset ss circ reset (set ls)
  else eval_lit ss circ (Name (Named n),F)
Proof
  simp [eval_circuit_def, eval_circuit_encode_is_reset_Named]
QED

(* Encoding preds_hold ********************************************************)

Definition encode_preds_hold_def:
  encode_preds_hold
    (circ: ('a iext, 'i, 'l) circuit) name (lits: ('a iext,'i,'l) lit list) =
  (Named (Ext name), lits)::circ
End

Theorem eval_lit_encode_preds_hold_Named:
  eval_lit ss (encode_preds_hold circ name lits) (n,F) =
  if n = Name (Named (Ext name)) then
    preds_hold ss circ (set lits)
  else eval_lit ss circ (n,F)
Proof
  simp [encode_preds_hold_def, eval_circuit_def, preds_hold_def, EVERY_MEM]
  >> IF_CASES_TAC >> gvs []
  >> TOP_CASE_TAC >> gvs []
QED

Theorem eval_lit_encode_preds_hold_iext_lit[simp]:
  eval_lit ss (encode_preds_hold circ name lits) (iext_lit lit) =
  eval_lit ss circ (iext_lit lit)
Proof
  simp [encode_preds_hold_def]
QED

Theorem eval_circuit_encode_preds_hold_Named:
  eval_circuit ss (encode_preds_hold circ name lits) (Named n) =
  if n = Ext name then
    preds_hold ss circ (set lits)
  else eval_circuit ss circ (Named n)
Proof
  simp [encode_preds_hold_def, eval_circuit_def, preds_hold_def, EVERY_MEM]
  >> IF_CASES_TAC >> simp []
QED

Definition left_reset_def:
  left_reset mreset =
  λl. OPTION_MAP left_name_lit (mreset l)
End

Definition right_reset_def:
  right_reset mreset =
  λl. OPTION_MAP right_name_lit (mreset l)
End

Definition iext_reset_def:
  iext_reset reset = λl. OPTION_MAP iext_lit (reset l)
End

Definition ileft_reset_def:
  ileft_reset = iext_reset ∘ left_reset
End

Definition iright_reset_def:
  iright_reset = iext_reset ∘ right_reset
End

Definition ileft_name_lits_def:
  ileft_name_lits = MAP (iext_lit ∘ left_name_lit)
End

Definition iright_name_lits_def:
  iright_name_lits = MAP (iext_lit ∘ right_name_lit)
End

Definition imerge_circuits_def:
  imerge_circuits circ₀ circ₁ = iext_circuit (merge_circuits circ₀ circ₁)
End

Theorem eval_lit_imerge_circuit_iext_lit[simp]:
  eval_lit ss (imerge_circuits circ₀ circ₁) (iext_lit lit) ⇔
    eval_lit ss (merge_circuits circ₀ circ₁) lit
Proof
  simp [imerge_circuits_def]
QED

(* Encoding is_next ***********************************************************)

Definition encode_is_next_def:
  encode_is_next
    (circ: (('a + 'b) iext, 'i + 'j, 'l + 'l) circuit)
    (name: mlstring)
    (next: ('l -> ('a,'i,'l) lit))
    (latches: 'l list)
  =
  encode_equiv circ name
    (MAP (λl. (iext_lit (left_lit (next l)),
               iext_lit (right_lit (Base (Latch l), F)))) latches)
End

(* Encoding lives_imply *******************************************************)

(* If the liveness properties are "well-formed", that is, we assume that
   corresponding liveness properties in the model and the witness have the
   same number of signals, lives_imply is the same as signal_imply on the
   flattened liveness properties (i.e., all signals at once). *)

Theorem LIST_REL_LENGTH_FLAT[local]:
  ∀xss yss.
    LIST_REL (λxs ys. LENGTH xs = LENGTH ys) xss yss ⇒
      LENGTH (FLAT xss) = LENGTH (FLAT yss)
Proof
  Induct >> Cases_on ‘yss’
  >> rpt strip_tac >> gvs []
  >> first_x_assum drule >> simp []
QED

Theorem LIST_REL_FLAT[local]:
  ∀xss yss.
    LIST_REL (LIST_REL R) xss yss ⇔
      LIST_REL R (FLAT xss) (FLAT yss) ∧
      LIST_REL (λxs ys. LENGTH xs = LENGTH ys) xss yss
Proof
  Induct >> Cases_on ‘yss’ >> rw []
  >> rename1 ‘LIST_REL _ (_ ++ FLAT xss) (_ ++ FLAT yss)’
  >> eq_tac >> rw []
  >- (rev_drule $ iffLR LIST_REL_APPEND >> disch_then drule >> gvs [])
  >- imp_res_tac LIST_REL_LENGTH
  >> drule $ iffRL LIST_REL_APPEND
  >> drule LIST_REL_LENGTH_FLAT >> simp []
QED

Theorem lives_imply_signal_imply_FLAT:
  ∀wlive mlive.
    lives_imply ss₀ ss₁ wqcirc mqcirc wlive mlive =
    (signal_imply ss₀ wqcirc ss₁ mqcirc (FLAT wlive) (FLAT mlive) ∧
     LIST_REL (λQ Q'. LENGTH Q = LENGTH Q') wlive mlive)
Proof
  simp [lives_imply_def, signal_imply_def]
  >> qmatch_goalsub_abbrev_tac ‘LIST_REL (λQ Q'. LIST_REL R Q Q')’
  >> ‘(λQ Q'. LIST_REL R Q Q') = LIST_REL R’ by simp [FUN_EQ_THM]
  >> simp [LIST_REL_FLAT]
QED

Definition encode_signal_imply_aux_def:
  (encode_signal_imply_aux
     (circ: ('a iext, 'i, 'l) circuit)
     (signal::rest : ('a iext, 'i, 'l) lit list)
     (signal'::rest': ('a iext, 'i, 'l) lit list)
     (next: num)
   : (('a iext, 'i, 'l) circuit # num list)
   =
   let
     (circ, outs) = encode_signal_imply_aux circ rest rest' (next + 2);
     circ =
       (Anon (next + 1), [(Name (Anon next), T)])
       ::(Anon next, [signal; not signal'])
       ::circ;
     outs = (next + 1)::outs;
   in
     (circ, outs)) ∧
  (encode_signal_imply_aux circ _ _ _ = (circ, []))
End

(* Implements pointwise implication. *)
Definition encode_signal_imply_def:
  encode_signal_imply
    (circ: ('a iext, 'i, 'l) circuit)
    (name: mlstring)
    (signals : ('a iext, 'i, 'l) lit list)
    (signals': ('a iext, 'i, 'l) lit list)
  : (('a iext, 'i, 'l) circuit)
  =
  let
    (* 1n instead of 0n, since 0n is iname's default value for non-anonymous
       literals*)
    (circ, outs) = encode_signal_imply_aux circ signals signals' 1n;
  in
    ((Named (Ext name), MAP (λn. Name (Anon n), F) outs)::circ)
End

Theorem encode_signal_imply_eval_circuit_Named[local]:
  ∀circ signals signals' next circ' outs'.
    encode_signal_imply_aux circ signals signals' next = (circ',outs') ⇒
    (eval_circuit ss circ' (Named n) ⇔ eval_circuit ss circ (Named n))
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_circuit_def]
QED

Theorem encode_signal_imply_aux_eval_lit_iname_lt[local]:
  ∀circ signals signals' next circ' outs.
    encode_signal_imply_aux circ signals signals' next = (circ', outs) ∧
    iname x < next
    ⇒
    (eval_lit ss circ' x ⇔ eval_lit ss circ x)
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_Anon_neq]
QED

Theorem encode_signal_imply_aux_LENGTH[local]:
  ∀circ signals signals' next circ' outs'.
    encode_signal_imply_aux circ signals signals' next = (circ',outs')
    ⇒
    LENGTH outs' = MIN (LENGTH signals) (LENGTH signals')
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def, MIN_DEF]
  >> rpt (pairarg_tac >> gvs [])
QED

Theorem encode_signal_imply_aux_EVERY_leq_outs[local]:
  ∀circ signals signals' next circ' outs.
    encode_signal_imply_aux circ signals signals' next = (circ',outs) ⇒
    EVERY (λout. next ≤ out) outs
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> fs [EVERY_MEM]
  >> rpt strip_tac
  >> last_x_assum drule >> simp []
QED

Theorem encode_signal_imply_aux_eval_lit[local]:
  ∀circ signals signals' next circ' outs'.
    encode_signal_imply_aux circ signals signals' next = (circ',outs') ∧
    EVERY (λx. iname x < next) signals ∧
    EVERY (λx. iname x < next) signals' ∧
    LENGTH signals' = LENGTH signals ⇒
    ∀n. n < LENGTH signals ⇒
        (eval_lit ss circ' (Name (Anon outs'❲n❳),F) ⇔
           preds_hold ss circ {signals❲n❳} ⇒
           preds_hold ss circ {signals'❲n❳})
Proof
  recInduct encode_signal_imply_aux_ind >> rw []
  >> Cases_on ‘n’ >> gvs [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> fs [preds_hold_def]
  >-
   (simp [eval_circuit_def, eval_lit_not]
    >> rename1 ‘eval_lit _ _ signal ⇒ eval_lit _ _ signal'’
    >> ‘iname signal < next + 2 ∧ iname signal' < next + 2’ by simp []
    >> drule_all encode_signal_imply_aux_eval_lit_iname_lt
    >> rev_drule_all encode_signal_imply_aux_eval_lit_iname_lt
    >> simp []
    >> metis_tac [])
  >> rename1 ‘Anon outs❲n❳’
  >> ‘outs❲n❳ ≠ next ∧ outs❲n❳ ≠ next + 1’ by
    (drule_then assume_tac encode_signal_imply_aux_LENGTH
     >> drule_then assume_tac encode_signal_imply_aux_EVERY_leq_outs
     >> gvs [EVERY_EL]
     >> first_x_assum drule >> simp [])
  >> DEP_REWRITE_TAC [eval_lit_Anon_neq]
  >> conj_tac
  >-
   (simp [iname_def]
    >> gvs [EVERY_EL]
    >> first_x_assum drule >> simp []
    >> first_x_assum drule >> simp [])
  >> last_assum irule >> simp []
  (* EVERY (λx. iname x < next + 2) _ *)
  >> fs [EVERY_MEM] >> rw [] >> res_tac >> simp []
QED

Theorem eval_circuit_encode_signal_imply:
  LENGTH signals' = LENGTH signals ∧
  EVERY (λx. iname x = 0) signals  ∧
  EVERY (λx. iname x = 0) signals'
  ⇒
  (eval_circuit ss (encode_signal_imply circ name signals signals') (Named n) =
   if n = Ext name then
     signal_imply ss circ ss circ signals signals'
   else eval_circuit ss circ (Named n))
Proof
  strip_tac
  >> simp [encode_signal_imply_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_circuit_def]
  >> reverse IF_CASES_TAC >> gvs []
  >- (drule encode_signal_imply_eval_circuit_Named >> simp [])
  >> simp [signal_imply_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP]
  >> drule_then assume_tac encode_signal_imply_aux_LENGTH >> gvs [MIN_DEF]
  >> drule encode_signal_imply_aux_eval_lit
  >> simp []
QED

Theorem eval_lit_encode_signal_imply_Name:
  LENGTH signals' = LENGTH signals ∧
  EVERY (λx. iname x = 0) signals  ∧
  EVERY (λx. iname x = 0) signals'
  ⇒
  (eval_lit ss (encode_signal_imply circ name signals signals')
     (Name (Named n), b) ⇔
   if n = Ext name then
     (b ⇎ signal_imply ss circ ss circ signals signals')
   else eval_lit ss circ (Name (Named n), b))
Proof
  strip_tac >> simp [eval_circuit_def]
  >> drule_all eval_circuit_encode_signal_imply
  >> rw []
QED

(* Encoding lives_hold ********************************************************)

Definition lives_hold_def:
  lives_hold
    (circ: ('a iext, 'i, 'l) circuit)
    (name: mlstring)
    (live: ('a, 'i, 'l) lit list list)
  : ('a iext, 'i, 'l) circuit
  =
  let ns = GENLIST Anon (LENGTH live) in
    (Named (Ext name), MAP (λn. (Name n, T)) ns)
    :: ZIP (ns, MAP (MAP (iext_lit ∘ not)) live)
    ++ circ
End

(* Encoding certificate conditions ********************************************)

Definition encode_is_witness_reset_def:
  encode_is_witness_reset
    (mcirc: ('a, 'i, 'l) circuit)
    (mreset: 'l -> ('a, 'i, 'l) lit option)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlatches: 'l list)
    (wcirc: ('b, 'i, 'l) circuit)
    (wreset: 'l -> ('b, 'i, 'l) lit option)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wlatches: 'l list)
  =
  let
    circ = imerge_circuits mcirc wcirc;
    circ = encode_is_reset circ «mreset» (ileft_reset mreset) mlatches;
    circ = encode_preds_hold circ «mcnstrs» (ileft_name_lits mcnstrs);
    klatches = list_inter mlatches wlatches;
    circ = encode_is_reset circ «wreset» (iright_reset wreset) klatches;
    circ = encode_preds_hold circ «wcnstrs» (iright_name_lits wcnstrs);
    lhss =
      [(Name (Named (Ext «mreset»)), F);
       (Name (Named (Ext «mcnstrs»)), F)];
    rhss =
      [(Name (Named (Ext «wreset»)), F);
       (Name (Named (Ext «wcnstrs»)), F)];
  in
    encode_imply circ «reset» T lhss rhss
End

Definition encode_is_witness_transition_def:
  encode_is_witness_transition
    (mcirc: ('a, 'i, 'l) circuit)
    (mnext: 'l -> ('a, 'i, 'l) lit)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlatches: 'l list)
    (wcirc: ('b, 'i, 'l) circuit)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wlatches: 'l list)
  =
  let
    circ  = imerge_circuits mcirc wcirc;
    circ = encode_preds_hold circ «mcnstrs» (ileft_name_lits mcnstrs);
    circ = encode_preds_hold circ «wcnstrs» (iright_name_lits wcnstrs);
    circ  = iext_circuit (pair_circuits circ circ);
    circ  = encode_is_next circ «mnext» (iext_lit ∘ left_name_lit ∘ mnext) mlatches;
    klatches = list_inter mlatches wlatches;
    circ  = encode_is_next circ «wnext» (iext_lit ∘ right_name_lit ∘ wnext) klatches;
    lhss  =
      [(Name (Named (Ext «mnext»)), F);
       iext_lit (left_lit (Name (Named (Ext «mcnstrs»)), F));
       iext_lit (right_lit (Name (Named (Ext «mcnstrs»)), F));
       iext_lit (left_lit (Name (Named (Ext «wcnstrs»)), F));
      ];
    rhss  =
      [(Name (Named (Ext «wnext»)), F);
       iext_lit (right_lit (Name (Named (Ext «wcnstrs»)), F))];
  in
    encode_imply circ «transition» T lhss rhss
End

Definition encode_is_witness_property_def:
  encode_is_witness_property
    (mcirc: ('a, 'i, 'l) circuit)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mpreds: ('a, 'i, 'l) lit list)
    (wcirc: ('b, 'i, 'l) circuit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wpreds: ('b, 'i, 'l) lit list)
  =
  let
    circ = imerge_circuits mcirc wcirc;
    circ = encode_preds_hold circ «mcnstrs» (ileft_name_lits mcnstrs);
    circ = encode_preds_hold circ «mpreds» (ileft_name_lits mpreds);
    circ = encode_preds_hold circ «wcnstrs» (iright_name_lits wcnstrs);
    circ = encode_preds_hold circ «wpreds» (iright_name_lits wpreds);
    lhss =
      [(Name (Named (Ext «mcnstrs»)),F);
       (Name (Named (Ext «wcnstrs»)),F);
       (Name (Named (Ext «wpreds»)),F)];
    rhss = [(Name (Named (Ext «mpreds»)), F);]
  in
    encode_imply circ «property» T lhss rhss
End

Definition encode_is_witness_base_def:
  encode_is_witness_base
    (wcirc: ('a, 'i, 'l) circuit)
    (wreset: 'l -> ('a, 'i, 'l) lit option)
    (wcnstrs: ('a, 'i, 'l) lit list)
    (wpreds: ('a, 'i, 'l) lit list)
    (wlatches: 'l list)
  ⇔
    let
      circ = iext_circuit wcirc;
      circ = encode_is_reset circ «wreset» (iext_reset wreset) wlatches;
      circ = encode_preds_hold circ «wcnstrs» (MAP iext_lit wcnstrs);
      circ = encode_preds_hold circ «wpreds» (MAP iext_lit wpreds);
      lhss =
        [(Name (Named (Ext «wreset»)),F);
         (Name (Named (Ext «wcnstrs»)),F)];
      rhss = [(Name (Named (Ext «wpreds»)), F)]
  in
    encode_imply circ «base» T lhss rhss
End

Definition encode_is_witness_step_def:
  encode_is_witness_step
    (wcirc: ('a, 'i, 'l) circuit)
    (wnext: 'l -> ('a, 'i, 'l) lit)
    (wcnstrs: ('a, 'i, 'l) lit list)
    (wpreds: ('a, 'i, 'l) lit list)
    (wlatches: 'l list)
  ⇔
    let
      circ = iext_circuit wcirc;
      circ = encode_preds_hold circ «wcnstrs» (MAP iext_lit wcnstrs);
      circ = encode_preds_hold circ «wpreds» (MAP iext_lit wpreds);
      circ = iext_circuit (pair_circuits circ circ);
      circ = encode_is_next circ «wnext» (iext_lit ∘ wnext) wlatches;
      lhss =
        [iext_lit (left_lit (Name (Named (Ext «wpreds»)), F));
         (Name (Named (Ext «wnext»)), F);
         iext_lit (right_lit (Name (Named (Ext «wcnstrs»)), F));
         iext_lit (left_lit (Name (Named (Ext «wcnstrs»)), F))];
      rhss = [iext_lit (right_lit (Name (Named (Ext «wpreds»)), F))]
    in
      encode_imply circ «step» T lhss rhss
End

Definition encode_is_witness_liveness_def:
  encode_is_witness_liveness
    (mcirc: ('a, 'i, 'l) circuit)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlive: ('a, 'i, 'l) lit list list)
    (wcirc: ('b, 'i, 'l) circuit)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wpreds: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) lit -> 'l option)
  =
  let
    msignals  = ileft_name_lits (FLAT (qleft_live mlive));
    wsignals  = iright_name_lits (FLAT (qinterv_live interv wlive));
    mqcirc = qleft mcirc;
    wqcirc = qinterv interv wcirc;
    qcirc = imerge_circuits mqcirc wqcirc;
    qcirc = encode_signal_imply qcirc «lives_imply» wsignals msignals;
    circ = imerge_circuits mcirc wcirc;
    circ = encode_preds_hold circ «mcnstrs» (ileft_name_lits mcnstrs);
    circ = encode_preds_hold circ «wcnstrs» (iright_name_lits wcnstrs);
    circ = encode_preds_hold circ «wpreds» (iright_name_lits wpreds);
    circ = iext_circuit (pair_circuits circ circ);
    circ =
      encode_is_next circ «wnext» (iext_lit ∘ right_name_lit ∘ wnext) wlatches;
    circ = imerge_circuits circ qcirc;
    lhss = [
      iext_lit
        (left_name_lit (iext_lit (left_lit (Name (Named (Ext «mcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (left_lit (Name (Named (Ext «wcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (left_lit (Name (Named (Ext «wpreds»)), F))));
      iext_lit
        (left_name_lit (iext_lit (right_lit (Name (Named (Ext «mcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (right_lit (Name (Named (Ext «wcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (right_lit (Name (Named (Ext «wpreds»)), F))));
      iext_lit
        (left_name_lit ((Name (Named (Ext «wnext»)), F)));
    ];
    rhss = [iext_lit (right_name_lit (Name (Named (Ext «lives_imply»)), F))]
  in
    encode_imply circ «liveness» F lhss rhss
End

(* Proving correctness of the encodings ***************************************)

(* A bunch of trivial helper lemmas, which keep the proof state readable
   when an encoding function uses many other encoding functions. *)

Theorem is_reset_iext[local,simp]:
  is_reset ss (iext_circuit circ) (iext_reset reset) latches ⇔
    is_reset ss circ reset latches
Proof
  simp [is_reset_def, iext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_ileft[local,simp]:
  is_reset ss (imerge_circuits lcirc rcirc) (ileft_reset lreset) latches ⇔
    is_reset ss lcirc lreset latches
Proof
  simp [is_reset_def, imerge_circuits_def, ileft_reset_def, left_reset_def,
        eval_circuit_def, iext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_iright[local,simp]:
  is_reset ss (imerge_circuits lcirc rcirc) (iright_reset rreset) latches ⇔
    is_reset ss rcirc rreset latches
Proof
  simp [is_reset_def, imerge_circuits_def, iright_reset_def, right_reset_def,
        eval_circuit_def, iext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_encode_preds_hold_iright[local,simp]:
  is_reset ss
    (encode_preds_hold circ name lits) (iright_reset reset) latches ⇔
  is_reset ss circ (iright_reset reset) latches
Proof
  simp [is_reset_def, encode_preds_hold_def, iright_reset_def, right_reset_def,
        eval_circuit_def, iext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_encode_is_reset_iright[local,simp]:
  is_reset ss (encode_is_reset circ name reset' latches')
    (iright_reset reset) latches ⇔
  is_reset ss circ (iright_reset reset) latches
Proof
  simp [is_reset_def, encode_is_reset_def, iright_reset_def, eval_circuit_def,
        iext_reset_def, PULL_EXISTS]
QED

Theorem preds_hold_iext[local,simp]:
  preds_hold ss (iext_circuit circ) (set (MAP iext_lit preds)) ⇔
    preds_hold ss circ (set preds)
Proof
  simp [preds_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_ileft[local,simp]:
  preds_hold ss (imerge_circuits lcirc rcirc) (set (ileft_name_lits preds)) ⇔
    preds_hold ss lcirc (set preds)
Proof
  simp [preds_hold_def, ileft_name_lits_def, imerge_circuits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_iright[local,simp]:
  preds_hold ss (imerge_circuits lcirc rcirc) (set (iright_name_lits preds)) ⇔
    preds_hold ss rcirc (set preds)
Proof
  simp [preds_hold_def, iright_name_lits_def, imerge_circuits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_encode_is_reset_ileft[local,simp]:
  preds_hold ss
    (encode_is_reset circ name reset latches) (set (ileft_name_lits preds)) ⇔
  preds_hold ss circ (set (ileft_name_lits preds))
Proof
  simp [preds_hold_def, encode_is_reset_def, ileft_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_encode_is_reset_iright[local,simp]:
  preds_hold ss
    (encode_is_reset circ name reset latches) (set (iright_name_lits preds)) ⇔
  preds_hold ss circ (set (iright_name_lits preds))
Proof
  simp [preds_hold_def, encode_is_reset_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_encode_is_reset_iext[local,simp]:
  preds_hold ss
    (encode_is_reset circ name reset latches) (set (MAP iext_lit preds)) ⇔
  preds_hold ss circ (set (MAP iext_lit preds))
Proof
  simp [preds_hold_def, encode_is_reset_def, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_encode_preds_hold_iright[local,simp]:
  preds_hold ss (encode_preds_hold circ name preds') (set (iright_name_lits preds)) ⇔
    preds_hold ss circ (set (iright_name_lits preds))
Proof
  simp [preds_hold_def, encode_preds_hold_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_encode_preds_hold_iext_lit[local,simp]:
  preds_hold ss (encode_preds_hold circ name preds') (set (MAP iext_lit preds)) ⇔
    preds_hold ss circ (set (MAP iext_lit preds))
Proof
  simp [preds_hold_def, encode_preds_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_encode_preds_hold_iright[local,simp]:
  preds_hold ss (encode_preds_hold circ name preds') (set (iright_name_lits preds)) ⇔
    preds_hold ss circ (set (iright_name_lits preds))
Proof
  simp [preds_hold_def, encode_preds_hold_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem preds_hold_encode_preds_hold_ileft[local,simp]:
  preds_hold ss (encode_preds_hold circ name preds') (set (ileft_name_lits preds)) ⇔
    preds_hold ss circ (set (ileft_name_lits preds))
Proof
  simp [preds_hold_def, encode_preds_hold_def, ileft_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem signal_imply_iright_ileft[local,simp]:
  signal_imply ss₀ (imerge_circuits circ₁ circ₂)
    ss₁ (imerge_circuits circ₃ circ₄) (iright_name_lits signals')
    (ileft_name_lits signals)
  ⇔
  signal_imply ss₀ circ₂ ss₁ circ₃ signals' signals
Proof
  simp [signal_imply_def, ileft_name_lits_def, iright_name_lits_def,
        preds_hold_def, LIST_REL_MAP]
QED

(* Main encoder theorems ******************************************************)

Theorem eval_circuit_encode_is_witness_reset:
  (¬∃ss.
     (eval_circuit ss
       (encode_is_witness_reset
          mcirc mreset mcnstrs mlatches
          wcirc wreset wcnstrs wlatches)
       (Named (Ext «reset»)))) =
  is_witness_reset
    mcirc mreset mnext mpreds (set mcnstrs) (set mlatches)
    wcirc wreset wnext wpreds (set wcnstrs) (set wlatches)
Proof
  simp [
      is_witness_reset_def, encode_is_witness_reset_def,
      eval_circuit_encode_imply,
      eval_lit_encode_preds_hold_Named,
      eval_lit_encode_is_reset_Named,
      list_inter_set
    ]
  >> metis_tac []
QED

Theorem eval_circuit_encode_is_witness_transition:
  (¬∃ss.
     (eval_circuit ss
       (encode_is_witness_transition
          mcirc mnext mcnstrs mlatches
          wcirc wnext wcnstrs wlatches)
       (Named (Ext «transition»)))) ⇔
  is_witness_transition
    mcirc mreset mnext mpreds (set mcnstrs) (set mlatches)
    wcirc wreset wnext wpreds (set wcnstrs) (set wlatches)
Proof
  simp [
      encode_is_witness_transition_def,
      eval_circuit_encode_imply,
      encode_is_next_def,
      eval_lit_encode_equiv_Named,
      eval_lit_encode_preds_hold_Named,
      FORALL_PAIR_STATE,
      is_witness_transition_def, list_inter_set, is_next_def, eval_lit_base,
      EVERY_MEM, MEM_MAP, PULL_EXISTS, PULL_FORALL
    ]
  (* metis_tac is quite finicky here... *)
  >> eq_tac >> rw []
  >-
   (rename1 ‘eval_lit ss₀ _ _ ⇔ _ ss₁ l’
    >> first_x_assum $ qspecl_then [‘ss₀’, ‘ss₁’, ‘l’] assume_tac
    >> metis_tac [])
  >-
   (rename1 ‘eval_lit ss₀ _ _ ⇔ _ ss₁ _’
    >> first_x_assum $ qspecl_then [‘ss₀’, ‘ss₁’, ‘ARB’] assume_tac
    >> metis_tac [])
  >> rename1 ‘eval_lit ss₀ _ _ ⇔ _ ss₁ l’
  (* metis_tac is *especially* finicky here... *)
  >> CCONTR_TAC
  >> first_x_assum $ qspecl_then [‘ss₀’, ‘ss₁’, ‘l’] mp_tac
  >> gvs []
  >> metis_tac []
QED

Theorem eval_circuit_encode_is_witness_property:
  (¬∃ss.
     (eval_circuit ss
       (encode_is_witness_property
          mcirc mcnstrs mpreds
          wcirc wcnstrs wpreds)
       (Named (Ext «property»)))) =
  is_witness_property
    mcirc mreset mnext (set mpreds) (set mcnstrs) mlatches
    wcirc wreset wnext (set wpreds) (set wcnstrs) wlatches
Proof
  simp [
      encode_is_witness_property_def,
      eval_circuit_encode_imply,
      eval_lit_encode_preds_hold_Named,
      is_witness_property_def
    ]
  >> metis_tac []
QED

Theorem eval_circuit_encode_is_witness_base:
  (¬∃ss.
     (eval_circuit ss
       (encode_is_witness_base
          wcirc wreset wcnstrs wpreds wlatches)
       (Named (Ext «base»)))) =
  is_witness_base
    wcirc wreset wnext (set wpreds) (set wcnstrs) (set wlatches)
Proof
  simp [
      encode_is_witness_base_def,
      eval_circuit_encode_imply,
      eval_lit_encode_preds_hold_Named,
      eval_lit_encode_is_reset_Named,
      is_witness_base_def
    ]
  >> metis_tac []
QED

Theorem eval_circuit_encode_is_witness_step:
  (¬∃ss.
     (eval_circuit ss
       (encode_is_witness_step
          wcirc wnext wcnstrs wpreds wlatches)
       (Named (Ext «step»)))) =
  is_witness_step wcirc wreset wnext (set wpreds) (set wcnstrs) (set wlatches)
Proof
  simp [
      encode_is_witness_step_def,
      eval_circuit_encode_imply,
      eval_lit_encode_preds_hold_Named,
      eval_lit_encode_equiv_Named,
      encode_is_next_def,
      eval_lit_base,
      is_witness_step_def, is_next_def,
      FORALL_PAIR_STATE,
      EVERY_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> metis_tac []
QED

Theorem eval_circuit_encode_is_witness_liveness:
  LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive
  ⇒
  (∀ss.
     (eval_circuit ss
       (encode_is_witness_liveness
          mcirc mcnstrs mlive
          wcirc wnext wcnstrs wpreds wlive wlatches interv)
       (Named (Ext «liveness»)))) =
  is_witness_liveness
    mcirc mreset mnext (set mpreds) (set mcnstrs)
    (qleft mcirc) (qleft_live mlive) (set mlatches)
    wcirc wreset wnext (set wpreds) (set wcnstrs)
    (qinterv interv wcirc) (qinterv_live interv wlive) (set wlatches)
Proof
  strip_tac
  >> simp [
      encode_is_witness_liveness_def,
      eval_circuit_encode_imply,
      encode_is_next_def, is_next_def,
      is_witness_liveness_def, lives_imply_signal_imply_FLAT,
      eval_lit_encode_preds_hold_Named,
      eval_lit_encode_equiv_Named,
      eval_lit_base,
      FORALL_PAIR_STATE,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> qabbrev_tac ‘mlive' = qleft_live mlive’
  >> qabbrev_tac ‘wlive' = qinterv_live interv wlive’
  >> sg ‘LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive' wlive'’
  >-
   (fs [Abbr ‘mlive'’, Abbr ‘wlive'’, LIST_REL_EL_EQN, qinterv_live_def,
        qleft_live_def, EL_MAP])
  >> qmatch_goalsub_abbrev_tac ‘encode_signal_imply _ _ signals signals'’
  >> sg ‘LENGTH signals' = LENGTH signals’
  >-
   (simp [Abbr ‘signals'’, Abbr ‘signals’, iright_name_lits_def,
          ileft_name_lits_def]
    >> drule LIST_REL_LENGTH_FLAT >> simp [])
  >> sg ‘EVERY (λx. iname x = 0) signals ∧ EVERY (λx. iname x = 0) signals'’
  >-
   (unabbrev_all_tac
    >> simp [EVERY_MEM, ileft_name_lits_def, iright_name_lits_def,
             GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS])
  >> drule_all_then assume_tac eval_lit_encode_signal_imply_Name
  >> simp [is_witness_liveness_def, lives_imply_signal_imply_FLAT]
  >> sg ‘LIST_REL (λws ms. LENGTH ws = LENGTH ms) wlive' mlive'’
  >-
   (irule LIST_REL_sym
    >> qpat_x_assum ‘LIST_REL _ mlive' wlive'’ $ irule_at Any
    >> simp [])
  >> simp [Abbr ‘signals’, Abbr ‘signals'’]
  >> metis_tac []
QED

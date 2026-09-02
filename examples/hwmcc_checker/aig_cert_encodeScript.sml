(*
  Encodes the certificate conditions as an AIG.
*)
Theory aig_cert_encode
Ancestors
  aig aig_cert
  (* TODO maybe should move; is for stratification *)
  topological_sort
Libs
  preamble

(* todo check which theorems/simps are actually used *)
(* todo check whether it is possible to reduce the amount of
   definitions/theorems *)

Theorem eval_lit_base:
  eval_lit ss aig (Base (Latch l), b) ⇔ (b ⇎ SND ss l)
Proof
  Cases_on ‘ss’ >> simp [eval_lit_def]
QED

(* Merging AIGs ***************************************************************)
(* Merging two AIGs results in a new AIG where the inputs and latches
   are shared. *)

Definition left_name_var_def:
  (left_name_var (Gate a)  = Gate (INL a)) ∧
  (left_name_var (Base bv) = Base bv)
End

Definition left_name_lit_def:
  left_name_lit (v, b) = (left_name_var v, b)
End

Definition left_name_and_def:
  left_name_and (n, ins) = (INL n, MAP left_name_lit ins)
End

Definition right_name_var_def:
  (right_name_var (Gate a)  = Gate (INR a)) ∧
  (right_name_var (Base bv) = Base bv)
End

Definition right_name_lit_def:
  right_name_lit (v, b) = (right_name_var v, b)
End

Definition right_name_and_def:
  right_name_and (n, ins) = (INR n, MAP right_name_lit ins)
End

Definition merge_aigs_def:
  merge_aigs (aig₁: ('a₁, 'i, 'l) aig) (aig₂: ('a₂, 'i, 'l) aig) =
    (MAP left_name_and aig₁ ++ MAP right_name_and aig₂)
    :('a₁ + 'a₂, 'i, 'l) aig
End

Theorem merge_aigs_left_cons:
  merge_aigs (a::aig₁) aig₂ =
  left_name_and a::(merge_aigs aig₁) aig₂
Proof
  simp [merge_aigs_def]
QED

Theorem merge_aigs_left_nil_right_cons:
  merge_aigs [] (a::aig) =
  right_name_and a::(merge_aigs [] aig)
Proof
  simp [merge_aigs_def]
QED

Theorem eval_gate_merge_aigs_left_nil_INL[local]:
  ¬eval_gate ss (merge_aigs [] aig) (INL n)
Proof
  Induct_on ‘aig’ >> rw [merge_aigs_def, eval_lit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rename1 ‘right_name_and a’
  >> Cases_on ‘a’ >> gvs [right_name_and_def, merge_aigs_def]
QED

Theorem eval_lit_merge_aigs_left_nil_left[local]:
  eval_lit ss (merge_aigs [] aig) (left_name_lit m) ⇔
  eval_lit ss [] m
Proof
  Induct_on ‘aig’
  >> Cases_on ‘m’ >> fs [left_name_lit_def]
  >> rename1 ‘left_name_var x’ >> Cases_on ‘x’ >> fs [left_name_var_def]
  >> fs [merge_aigs_def, eval_lit_def]
  >> Cases >> simp [right_name_and_def]
QED

Theorem eval_gate_merge_aigs_left_nil_INR[local]:
  (∀n.
     eval_gate ss (merge_aigs ([]: ('a, 'i, 'l) aig) aig) (INR n) =
     eval_gate ss aig n) ∧
  (∀m.
     eval_lit ss (merge_aigs ([]: ('a, 'i, 'l) aig) aig) (right_name_lit m) =
     eval_lit ss aig m)
Proof
  Induct_on ‘aig’ >> rw []
  >- simp [merge_aigs_def]
  >-
   (simp [merge_aigs_def]
    >> Cases_on ‘m’ >> simp [right_name_lit_def]
    >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
    >> simp [eval_lit_def])
  >> simp [merge_aigs_left_nil_right_cons]
  >-
   (simp [eval_lit_def]
    >> rename1 ‘right_name_and h’ >> Cases_on ‘h’ >> simp [right_name_and_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP])
  >> Cases_on ‘m’ >> simp [right_name_lit_def]
  >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
  >> simp [eval_lit_def]
  >> rename1 ‘right_name_and h’ >> Cases_on ‘h’ >> simp [right_name_and_def]
  >> IF_CASES_TAC >> gvs [EVERY_MAP]
QED

Theorem eval_gate_merge_aigs_left[simp]:
  (∀n.
     eval_gate ss (merge_aigs aig₁ aig₂) (INL n) =
     eval_gate ss aig₁ n) ∧
  (∀m.
     eval_lit ss (merge_aigs aig₁ aig₂) (left_name_lit m) =
     eval_lit ss aig₁ m)
Proof
  Induct_on ‘aig₁’ >> rw []
  >- simp [eval_gate_merge_aigs_left_nil_INL]
  >- simp [eval_lit_merge_aigs_left_nil_left]
  >> simp [merge_aigs_left_cons]
  >-
   (simp [eval_lit_def]
    >> rename1 ‘left_name_and a’ >> Cases_on ‘a’ >> simp [left_name_and_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP])
  >> rename1 ‘left_name_lit m’ >> Cases_on ‘m’ >> simp [left_name_lit_def]
  >> rename1 ‘left_name_var v’ >> Cases_on ‘v’ >> simp [left_name_var_def]
  >> simp [eval_lit_def]
  >> rename1 ‘left_name_and b’ >> Cases_on ‘b’ >> simp [left_name_and_def]
  >> IF_CASES_TAC >> gvs [EVERY_MAP]
QED

Theorem eval_gate_merge_aigs_right[simp]:
  (∀n.
     eval_gate ss (merge_aigs aig₁ aig₂) (INR n) =
     eval_gate ss aig₂ n) ∧
  (∀m.
     eval_lit ss (merge_aigs aig₁ aig₂) (right_name_lit m) =
     eval_lit ss aig₂ m)
Proof
  Induct_on ‘aig₁’ >> rw []
  >- simp [eval_gate_merge_aigs_left_nil_INR]
  >- simp [eval_gate_merge_aigs_left_nil_INR]
  >> simp [merge_aigs_left_cons]
  >-
   (rename1 ‘left_name_and a’ >> Cases_on ‘a’ >> simp [left_name_and_def]
    >> simp [eval_lit_def])
  >> Cases_on ‘m’ >> simp [right_name_lit_def]
  >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
  >> rename1 ‘left_name_and h’ >> Cases_on ‘h’ >> simp [left_name_and_def]
  >> simp [eval_lit_def]
QED

(* Pairing AIGs ***************************************************************)

(* Combines two AIGs into one, keeping them separate using the sum type. *)

Definition left_bvar_def:
  (left_bvar (Input i) = Input (INL i)) ∧
  (left_bvar (Latch l) = Latch (INL l)) ∧
  (left_bvar Ff        = Ff)
End

Definition left_var_def:
  (left_var (Gate a)  = Gate (INL a)) ∧
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
  (right_var (Gate a)  = Gate (INR a)) ∧
  (right_var (Base bv) = Base (right_bvar bv))
End

Definition right_lit_def:
  right_lit (v, b) = (right_var v, b)
End

Definition right_and_def:
  right_and (n, ins) = (INR n, MAP right_lit ins)
End

Definition pair_aigs_def:
  pair_aigs (aig₁: ('a₁, 'i₁, 'l₁) aig)
    (aig₂: ('a₂, 'i₂, 'l₂) aig) =
  MAP left_and aig₁ ++ MAP right_and aig₂
End

Theorem pair_aigs_left_cons:
  pair_aigs (a::aig₁) aig₂ =
  left_and a::(pair_aigs aig₁ aig₂)
Proof
  simp [pair_aigs_def]
QED

Theorem pair_aigs_left_nil_right_cons:
  pair_aigs [] (a::aig₂) =
  right_and a::(pair_aigs [] aig₂)
Proof
  simp [pair_aigs_def]
QED

Theorem eval_gate_pair_left_nil_INL[local]:
  ¬eval_gate ss (pair_aigs [] aig) (INL n)
Proof
  Induct_on ‘aig’ >> rw []
  >> gvs [pair_aigs_def, eval_lit_def]
  >> rename1 ‘right_and a’ >> Cases_on ‘a’
  >> simp [right_and_def]
QED

Theorem eval_gate_pair_left_nil_INR[local]:
  (∀n.
     eval_gate (state_pair ss₁ ss₂)
       (pair_aigs ([]: ('a, 'i, 'l) aig) aig) (INR n) =
     eval_gate ss₂ aig n) ∧
  (∀m.
     eval_lit (state_pair ss₁ ss₂)
       (pair_aigs ([]: ('a, 'i, 'l) aig) aig) (right_lit m) =
     eval_lit ss₂ aig m)
Proof
  Induct_on ‘aig’ >> rw []
  >- simp [pair_aigs_def, eval_lit_def]
  >-
   (Cases_on ‘m’ >> simp [pair_aigs_def, right_lit_def]
    >> rename1 ‘right_var x’ >> Cases_on ‘x’
    >> simp [right_var_def, eval_lit_def]
    >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [state_pair_def]
    >> rename1 ‘right_bvar b’ >> Cases_on ‘b’
    >> simp [right_bvar_def, eval_bvar_def])
  >> simp [pair_aigs_left_nil_right_cons]
  >-
   (rename1 ‘right_and a’ >> Cases_on ‘a’
    >> simp [right_and_def, eval_lit_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> rename1 ‘right_lit m’ >> Cases_on ‘m’
  >> simp [right_lit_def]
  >> rename1 ‘right_var x’ >> Cases_on ‘x’
  >> simp [right_var_def, eval_lit_def]
  >-
   (rename1 ‘right_and y’ >> Cases_on ‘y’
    >> simp [right_and_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [state_pair_def]
  >> rename1 ‘right_bvar b’ >> Cases_on ‘b’
  >> simp [right_bvar_def, eval_bvar_def]
QED

Theorem eval_lit_pair_left_nil_left[local]:
  eval_lit (state_pair ss₁ ss₂) (pair_aigs [] aig₂) (left_lit n) =
  eval_lit ss₁ [] n
Proof
  Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [state_pair_def]
  >> Induct_on ‘aig₂’ >> gvs [pair_aigs_def]
  >> Cases_on ‘n’ >> gvs [left_lit_def]
  >-
   (rename1 ‘left_var v’ >> Cases_on ‘v’
    >> simp [left_var_def, eval_lit_def]
    >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
    >> simp [left_bvar_def, eval_bvar_def])
  >> Cases >> simp [right_and_def]
  >> rename1 ‘left_var v’ >> Cases_on ‘v’
  >> gvs [left_var_def, eval_lit_def]
  >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
  >> simp [left_bvar_def, eval_bvar_def]
QED

Theorem eval_pair_left[simp]:
  (∀n.
     eval_gate (state_pair ss₁ ss₂) (pair_aigs aig₁ aig₂) (INL n) =
     eval_gate ss₁ aig₁ n) ∧
  (∀m.
     eval_lit (state_pair ss₁ ss₂) (pair_aigs aig₁ aig₂) (left_lit m) =
     eval_lit ss₁ aig₁ m)
Proof
  Induct_on ‘aig₁’ >> rw [eval_lit_def]
  >- simp [eval_gate_pair_left_nil_INL]
  >- simp [eval_lit_pair_left_nil_left]
  >> simp [pair_aigs_left_cons]
  >-
   (simp [eval_lit_def]
    >> rename1 ‘left_and a’ >> Cases_on ‘a’
    >> simp [left_and_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> rename1 ‘left_lit m’ >> Cases_on ‘m’
  >> simp [left_lit_def]
  >> rename1 ‘left_var v’ >> Cases_on ‘v’
  >> simp [eval_lit_def, left_var_def]
  >-
   (rename1 ‘left_and b’ >> Cases_on ‘b’
    >> simp [eval_lit_def, left_and_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> gvs [state_pair_def]
  >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
  >> simp [left_bvar_def, eval_bvar_def]
QED

Theorem eval_pair_right[simp]:
  (∀n.
    eval_gate (state_pair ss₁ ss₂) (pair_aigs aig₁ aig₂) (INR n) =
    eval_gate ss₂ aig₂ n) ∧
  (∀m.
    eval_lit (state_pair ss₁ ss₂) (pair_aigs aig₁ aig₂) (right_lit m) =
    eval_lit ss₂ aig₂ m)
Proof
  Induct_on ‘aig₁’ >> rw [eval_lit_def]
  >- simp [eval_gate_pair_left_nil_INR]
  >- simp [eval_gate_pair_left_nil_INR]
  >> simp [pair_aigs_left_cons]
  >-
   (rename1 ‘left_and a’ >> Cases_on ‘a’
    >> simp [left_and_def, eval_lit_def])
  >> rename1 ‘right_lit m’ >> Cases_on ‘m’
  >> simp [right_lit_def]
  >> rename1 ‘right_var x’ >> Cases_on ‘x’
  >> simp [eval_lit_def, right_var_def]
  >-
   (rename1 ‘left_and g’ >> Cases_on ‘g’
    >> simp [left_and_def, eval_lit_def])
  >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> gvs [state_pair_def]
  >> rename1 ‘right_bvar b’ >> Cases_on ‘b’
  >> simp [right_bvar_def, eval_bvar_def]
QED

(* Liveness AIGs (qaig) *******************************************************)

(* Liveness AIGs (qaig) have access to two different states.
   For model AIGs this is not needed; inputs and outputs (not gates) are
   lifted to INL.
   In contrast, witness AIGs need to make use of this. For this, the
   intervention function maps literals to latches in the other state.
   Thus, we go through the AIG and for each literal present as a key in the
   intervention map, we replace it by g x, where x is the value in the
   intervention map.
   If the literal is not present, we lift inputs/outputs to f.
   In the simplest case, f = INL and g = INR. To encode the decreases property,
   these are flipped, and in the presence of three states (as in consistent),
   we need to nest the constructors. *)

(* f/g indicate the namespace inputs/latches should be mapped to.
   Usually f = g, e.g., f = g = INL. *)
Definition bvar_map_def:
  (bvar_map (f: 'i0 -> 'i1) _               (Input i) = Input (f i)) ∧
  (bvar_map  _              (g: 'l0 -> 'l1) (Latch l) = Latch (g l)) ∧
  (bvar_map  _              _               Ff        = Ff)
End

Definition var_map_base_def:
  (var_map_base _ _ (Gate a)  = Gate a) ∧
  (var_map_base f g (Base bv) = Base (bvar_map f g bv))
End

Definition lit_map_base_def:
  lit_map_base f g (v, b) = (var_map_base f g v, b)
End

Definition and_map_base_def:
  and_map_base f g (n, ins) = (n, MAP (lit_map_base f g) ins)
End

Definition aig_map_base_def:
  aig_map_base f g (aig: ('a, 'i, 'l) aig) =
    MAP (and_map_base f g) aig
End

Definition live_map_base_def:
  live_map_base f g (live: ('a, 'i, 'l) lit list list) =
    MAP (MAP (lit_map_base f g)) live
End

(** Intervention **************************************************************)

(* f/g indicate the namespace the first copy of input/latches should be mapped
   to. h indicates the second copy of latches intervened literals should be
   mapped to. *)
Definition qinterv_lit_def:
  qinterv_lit f g h (interv: ('a, 'i, 'l) var -> ('l # bool) option) lit =
  let (v, b) = lit in
    case interv v of
    | NONE => lit_map_base f g lit
    | SOME (l, b') =>
      (* if the intervened literal and the key in interv have different
         polarity, make sure result has negative polarity *)
        (Base (Latch (h l)), b ≠ b')
End

Definition qinterv_and_def:
  qinterv_and f g h interv ((n, ins): ('a, 'i, 'l) and) =
    (n, MAP (qinterv_lit f g h interv) ins)
End

Definition qinterv_live_def:
  qinterv_live f g h interv (live: ('a, 'i, 'l) lit list list) =
    MAP (MAP (qinterv_lit f g h interv)) live
End

Definition qinterv_def:
  qinterv f g h interv (aig: ('a, 'i, 'l) aig) =
    MAP (qinterv_and f g h interv) aig
End

(** Specialized versions of the functions above. ******************************)

Definition qleft_def:
  qleft (aig: ('a, 'i, 'l) aig) = aig_map_base INL INL aig
End

Theorem qleft_cons:
  qleft (g::aig) = and_map_base INL INL g::qleft aig
Proof
  simp [qleft_def, aig_map_base_def]
QED

Theorem eval_gate_pair_qleft:
  ∀aig.
    (∀n.
       eval_gate (state_pair s₁ s₂) (qleft aig) n ⇔
       eval_gate s₁ aig n) ∧
    (∀lit.
       eval_lit (state_pair s₁ s₂) (qleft aig) (lit_map_base INL INL lit) ⇔
       eval_lit s₁ aig lit)
Proof
  Induct >> rw []
  >- simp [qleft_def, aig_map_base_def]
  >- (
    simp [qleft_def, aig_map_base_def]
    >> Cases_on ‘lit’
    >> rename1 ‘lit_map_base _ _ (v, _)’ >> Cases_on ‘v’
    >> simp [lit_map_base_def, var_map_base_def, eval_lit_def]
    >> rename1 ‘bvar_map _ _ b’ >> Cases_on ‘b’
    >> simp [bvar_map_def, eval_lit_def]
    >> Cases_on ‘s₁’ >> Cases_on ‘s₂’ >> simp [state_pair_def, eval_bvar_def]
  )
  >- (
    simp [eval_lit_def, qleft_cons]
    >> rw [] >> rpt (pairarg_tac >> gvs [])
    >> gvs [and_map_base_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MAP]
  )
  >> Cases_on ‘lit’
  >> rename1 ‘lit_map_base _ _ (v, _)’ >> Cases_on ‘v’
  >> simp [lit_map_base_def, var_map_base_def, eval_lit_def]
  >> qmatch_goalsub_abbrev_tac ‘(r ⇔ X) ⇔ (r ⇔ Y)’
  >> qsuff_tac ‘X ⇔ Y’ >- simp []
  >> simp [Abbr ‘X’, Abbr ‘Y’]
  >- (
    simp [qleft_cons, eval_lit_def]
    >> rpt (pairarg_tac >> gvs [])
    >> gvs [and_map_base_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [EVERY_MAP])
  >> rename1 ‘bvar_map _ _ b’ >> Cases_on ‘b’
  >> simp [bvar_map_def, eval_lit_def]
  >> Cases_on ‘s₁’ >> Cases_on ‘s₂’ >> simp [state_pair_def, eval_bvar_def]
QED

Theorem dep_aig_pair_qleft:
  dep_aig (pair_set minput) (pair_set (set mlatches)) (qleft maig) =
  dep_aig minput (set mlatches) maig
Proof
  simp [dep_aig_def, FORALL_STATE_PAIR, agree_on_pair,
        eval_gate_pair_qleft]
  >> metis_tac []
QED

Definition qleft_live_def:
  qleft_live (live: ('a, 'i, 'l) lit list list) = live_map_base INL INL live
End

Definition qinterv_live_l_r_def:
  qinterv_live_l_r interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live INL INL INR interv live
End

Definition qinterv_live_r_l_def:
  qinterv_live_r_l interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live INR INR INL interv live
End

Definition qinterv_live_ll_r_def:
  qinterv_live_ll_r interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live (INL ∘ INL) (INL ∘ INL) INR interv live
End

Definition qinterv_live_ll_lr_def:
  qinterv_live_ll_lr interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live (INL ∘ INL) (INL ∘ INL) (INL ∘ INR) interv live
End

Definition qinterv_live_lr_r_def:
  qinterv_live_lr_r interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live (INL ∘ INR) (INL ∘ INR) INR interv live
End

Definition qinterv_l_r_def:
  qinterv_l_r interv (aig: ('a, 'i, 'l) aig) =
    qinterv INL INL INR interv aig
End

Definition qinterv_r_l_def:
  qinterv_r_l interv (aig: ('a, 'i, 'l) aig) =
    qinterv INR INR INL interv aig
End

Definition qinterv_ll_r_def:
  qinterv_ll_r interv (aig: ('a, 'i, 'l) aig) =
    qinterv (INL ∘ INL) (INL ∘ INL) INR interv aig
End

Definition qinterv_ll_lr_def:
  qinterv_ll_lr interv (aig: ('a, 'i, 'l) aig) =
    qinterv (INL ∘ INL) (INL ∘ INL) (INL ∘ INR) interv aig
End

Definition qinterv_lr_r_def:
  qinterv_lr_r interv (aig: ('a, 'i, 'l) aig) =
    qinterv (INL ∘ INR) (INL ∘ INR) INR interv aig
End

(* Extending an AIG ***********************************************************)

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
  (iext_var (Gate a) = Gate (Named (Orig a))) ∧
  (iext_var (Base bv) = Base bv)
End

Definition iext_lit_def:
  iext_lit (v, b) = (iext_var v, b)
End

Definition iext_and_def:
  iext_and ((n, ins): ('a, 'i, 'l) and) =
  (Named (Orig n), MAP iext_lit ins)
End

Definition iext_aig_def:
  iext_aig aig = MAP iext_and aig
End

Theorem eval_lit_Named_Ext_iext_lit[simp]:
  eval_lit ss ((Named (Ext name),lits)::aig) (iext_lit x) ⇔
   eval_lit ss aig (iext_lit x)
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [iext_lit_def, iext_var_def, eval_lit_def]
QED

Theorem eval_lit_Anon_iext_lit[simp]:
  eval_lit ss ((Anon n,lits)::aig) (iext_lit x) ⇔
   eval_lit ss aig (iext_lit x)
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [iext_lit_def, iext_var_def, eval_lit_def]
QED

Theorem eval_gate_iext_aig[simp]:
  (∀n.
     eval_gate ss (iext_aig aig) (Named (Orig n)) =
     eval_gate ss aig n) ∧
  (∀l. eval_lit ss (iext_aig aig) (iext_lit l) = eval_lit ss aig l) ∧
  (∀l. eval_lit ss (iext_aig aig) (Base bv, b) = eval_lit ss aig (Base bv, b))
Proof
  Induct_on ‘aig’ >> rw [iext_aig_def, eval_lit_def]
  >-
   (Cases_on ‘l’ >> simp [iext_lit_def]
    >> rename1 ‘iext_var v’ >> Cases_on ‘v’ >> simp [iext_var_def]
    >> simp [eval_lit_def])
  >-
   (rename1 ‘iext_and a’ >> Cases_on ‘a’ >> simp [iext_and_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP])
  >> Cases_on ‘l’ >> simp [iext_lit_def]
  >> rename1 ‘iext_var v’ >> Cases_on ‘v’ >> simp [iext_var_def]
  >> simp [eval_lit_def]
  >> rename1 ‘iext_and b’ >> Cases_on ‘b’ >> simp [iext_and_def]
  >> IF_CASES_TAC >> gvs [EVERY_MAP]
QED

Definition iname_def:
  iname (v,b) =
    case v of Gate (Anon n) => n
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
  (eval_lit ss ((Anon n, xs)::aig) m ⇔ eval_lit ss aig m)
Proof
  simp [oneline iname_def] >> every_case_tac >> rw [eval_lit_def]
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
  encode_imply (aig: ('a iext, 'i, 'l) aig) name b lhss rhss =
  let n = MAX (maxn lhss) (maxn rhss) in
    (* b = F: (lhss ⇒ rhss) ⇔ (¬lhss ∨ rhss) ⇔ ¬(lhss ∧ ¬rhss) *)
    (Named (Ext name), [(Gate (Anon (n+2)), ¬b)])
    ::(Anon (n+2), [(Gate (Anon n), F); (Gate (Anon (n+1)), T)]) (* lhss ∧ ¬rhss *)
    ::(Anon (n+1), rhss)::(Anon n, lhss)::aig
End

Theorem eval_gate_encode_imply:
  eval_gate ss (encode_imply aig name b lhss rhss) (Named n) =
  if n = Ext name then
    (b ⇎ ((EVERY (eval_lit ss aig) lhss) ⇒ (EVERY (eval_lit ss aig) rhss)))
  else eval_gate ss aig (Named n)
Proof
  eq_tac
  >> rw [encode_imply_def, eval_lit_def, EVERY_MEM, EXISTS_MEM]
  >> gvs []
  >- metis_tac [MEM_neq_iname_maxn, eval_lit_Anon_neq]
  >> Cases_on ‘∃e. MEM e lhss ∧ ¬eval_lit ss aig e’ >> fs []
  >- metis_tac []
  >> qpat_x_assum ‘∀e. ¬MEM e lhss ∨ _’ $
       assume_tac o PURE_REWRITE_RULE [GSYM IMP_DISJ_THM]
  >> metis_tac [MEM_neq_iname_maxn, eval_lit_Anon_neq]
QED

(* Encoding point-wise equivalence ********************************************)

Definition encode_equiv_aux_def:
  (encode_equiv_aux (n: num) [] = [(Anon n, [])]: ('a iext,'i,'l) aig) ∧
  (encode_equiv_aux n (xy::xys) =
   let (x, y) = xy in [
    (Anon n, [
        (Gate (Anon (n + 1)), T);
        (Gate (Anon (n + 2)), T);
        (Gate (Anon (n + 3)), F)
      ]);
    (Anon (n + 1), [x; not y]);
    (Anon (n + 2), [not x; y]);
   ] ++ encode_equiv_aux (n + 3) xys)
End

Definition encode_equiv_def:
  encode_equiv (aig: ('a iext, 'i, 'l) aig) name xys =
    let n = MAX (maxn (MAP FST xys)) (maxn (MAP SND xys)) in
      ((Named (Ext name), [(Gate (Anon n), F)])::encode_equiv_aux n xys) ++ aig
End

Theorem eval_gate_encode_equiv_aux_Named[local,simp]:
  ∀xys n.
    eval_gate ss (encode_equiv_aux n xys ++ aig) (Named out) ⇔
    eval_gate ss aig (Named out)
Proof
  Induct
  >> rw [encode_equiv_aux_def, eval_lit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_def]
QED

Theorem eval_lit_encode_equiv_aux_neq:
  ∀xys n.
    iname m < n ⇒
    (eval_lit ss (encode_equiv_aux n xys ++ aig) m ⇔
     eval_lit ss aig m)
Proof
  Induct >> rw [encode_equiv_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_Anon_neq]
QED

Theorem eval_gate_encode_equiv_aux_Anon_eq:
  ∀xys n.
    EVERY (λ(x, y). iname x < n ∧ iname y < n) xys ⇒
    (eval_gate ss (encode_equiv_aux n xys ++ aig) (Anon n) ⇔
    EVERY (λ(x,y). eval_lit ss aig x ⇔ eval_lit ss aig y) xys)
Proof
  Cases_on ‘ss’
  >> Induct
  >> rw [encode_equiv_aux_def, eval_lit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_def]
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

Theorem eval_gate_encode_equiv_Named:
  eval_gate ss (encode_equiv aig name xys) (Named n) =
  if n = Ext name then
    EVERY (λ(x,y). eval_lit ss aig x ⇔ eval_lit ss aig y) xys
  else eval_gate ss aig (Named n)
Proof
  Cases_on ‘ss’ >> rw [eval_lit_def, encode_equiv_def]
  >> irule eval_gate_encode_equiv_aux_Anon_eq
  >> rw [maxn_def, EVERY_MEM]
  >> rpt (pairarg_tac >> gvs [])
  >> ‘MEM (iname x) (MAP iname (MAP FST xys)) ∧
      MEM (iname y) (MAP iname (MAP SND xys))’
    by metis_tac[MEM_MAP, FST, SND]
  >> imp_res_tac MAX_LIST_PROPERTY >> simp []
QED

Theorem eval_lit_encode_equiv_Named:
  eval_lit ss (encode_equiv aig name xys) (Gate (Named n), b) =
  if n = Ext name then
    b ⇎ EVERY (λ(x,y). eval_lit ss aig x ⇔ eval_lit ss aig y) xys
  else eval_lit ss aig (Gate (Named n), b)
Proof
  simp [eval_lit_def, eval_gate_encode_equiv_Named]
  >> IF_CASES_TAC >> gvs []
QED

Theorem eval_lit_encode_equiv_iext_lit[simp]:
  eval_lit ss (encode_equiv aig name xys) (iext_lit n) =
  eval_lit ss aig (iext_lit n)
Proof
  namedCases_on ‘n’ ["v b"] >> Cases_on ‘v’
  >> simp [iext_lit_def, iext_var_def, encode_equiv_def, eval_lit_def]
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
  encode_is_reset (aig: ('a iext, 'i, 'l) aig) name reset ls =
  encode_equiv aig name (latch_reset_pairs reset ls)
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

Theorem eval_gate_encode_is_reset_Named:
  eval_gate ss (encode_is_reset aig name reset ls) (Named n) =
  if n = Ext name then
    is_reset ss aig reset (set ls)
  else eval_gate ss aig (Named n)
Proof
  Cases_on ‘ss’
  >> rw [eval_lit_def, encode_is_reset_def, eval_gate_encode_equiv_Named]
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
  eval_lit ss (encode_is_reset aig name reset ls) (Gate (Named n),F) =
  if n = Ext name then
    is_reset ss aig reset (set ls)
  else eval_lit ss aig (Gate (Named n),F)
Proof
  simp [eval_lit_def, eval_gate_encode_is_reset_Named]
QED

(* Encoding lits_hold *********************************************************)

Definition encode_lits_hold_def:
  encode_lits_hold
    (aig: ('a iext, 'i, 'l) aig) name (lits: ('a iext,'i,'l) lit list) =
  (Named (Ext name), lits)::aig
End

Theorem eval_lit_encode_lits_hold_Named:
  eval_lit ss (encode_lits_hold aig name lits) (n,F) =
  if n = Gate (Named (Ext name)) then
    lits_hold ss aig (set lits)
  else eval_lit ss aig (n,F)
Proof
  simp [encode_lits_hold_def, eval_lit_def, lits_hold_def, EVERY_MEM]
  >> IF_CASES_TAC >> gvs []
  >> TOP_CASE_TAC >> gvs []
QED

Theorem eval_lit_encode_lits_hold_iext_lit[simp]:
  eval_lit ss (encode_lits_hold aig name lits) (iext_lit lit) =
  eval_lit ss aig (iext_lit lit)
Proof
  simp [encode_lits_hold_def]
QED

Theorem eval_gate_encode_lits_hold_Named:
  eval_gate ss (encode_lits_hold aig name lits) (Named n) =
  if n = Ext name then
    lits_hold ss aig (set lits)
  else eval_gate ss aig (Named n)
Proof
  simp [encode_lits_hold_def, eval_lit_def, lits_hold_def, EVERY_MEM]
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

Definition imerge_aigs_def:
  imerge_aigs aig₀ aig₁ = iext_aig (merge_aigs aig₀ aig₁)
End

Theorem eval_lit_imerge_aig_iext_lit[simp]:
  eval_lit ss (imerge_aigs aig₀ aig₁) (iext_lit lit) ⇔
    eval_lit ss (merge_aigs aig₀ aig₁) lit
Proof
  simp [imerge_aigs_def]
QED

(* Encoding is_next ***********************************************************)

(* cur/next are usually INL/INR, but for consistent we need more flexibility. *)
Definition encode_is_next_with_def:
  encode_is_next_with aig name cur nxt next latches =
    encode_equiv aig name
      (MAP (λl. (cur (next l), nxt (Base (Latch l), F))) latches)
End

Definition encode_is_next_def:
  encode_is_next
    (aig: (('a + 'b) iext, 'i + 'j, 'l + 'l) aig)
    (name: mlstring)
    (next: ('l -> ('a,'i,'l) lit))
    (latches: 'l list)
  =
  encode_is_next_with aig name (iext_lit ∘ left_lit) (iext_lit ∘ right_lit)
    next latches
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
    lives_imply ss₀ ss₁ wqaig mqaig wlive mlive =
    (signal_imply ss₀ wqaig ss₁ mqaig (FLAT wlive) (FLAT mlive) ∧
     LIST_REL (λQ Q'. LENGTH Q = LENGTH Q') wlive mlive)
Proof
  simp [lives_imply_def, signal_imply_def]
  >> qmatch_goalsub_abbrev_tac ‘LIST_REL (λQ Q'. LIST_REL R Q Q')’
  >> ‘(λQ Q'. LIST_REL R Q Q') = LIST_REL R’ by simp [FUN_EQ_THM]
  >> simp [LIST_REL_FLAT]
QED

Definition encode_signal_imply_aux_def:
  (encode_signal_imply_aux
     (aig: ('a iext, 'i, 'l) aig)
     (signal::rest : ('a iext, 'i, 'l) lit list)
     (signal'::rest': ('a iext, 'i, 'l) lit list)
     (next: num)
   : (('a iext, 'i, 'l) aig # num list)
   =
   let
     (aig, outs) = encode_signal_imply_aux aig rest rest' (next + 2);
     aig =
       (Anon (next + 1), [(Gate (Anon next), T)])
       ::(Anon next, [signal; not signal'])
       ::aig;
     outs = (next + 1)::outs;
   in
     (aig, outs)) ∧
  (encode_signal_imply_aux aig _ _ _ = (aig, []))
End

(* Implements pointwise implication. *)
Definition encode_signal_imply_def:
  encode_signal_imply
    (aig: ('a iext, 'i, 'l) aig)
    (name: mlstring)
    (signals : ('a iext, 'i, 'l) lit list)
    (signals': ('a iext, 'i, 'l) lit list)
  : (('a iext, 'i, 'l) aig)
  =
  let
    (* 1n instead of 0n, since 0n is iname's default value for non-anonymous
       literals*)
    (aig, outs) = encode_signal_imply_aux aig signals signals' 1n;
  in
    ((Named (Ext name), MAP (λn. Gate (Anon n), F) outs)::aig)
End

Theorem encode_signal_imply_eval_gate_Named[local]:
  ∀aig signals signals' next aig' outs'.
    encode_signal_imply_aux aig signals signals' next = (aig',outs') ⇒
    (eval_gate ss aig' (Named n) ⇔ eval_gate ss aig (Named n))
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_def]
QED

Theorem encode_signal_imply_aux_eval_lit_iname_lt[local]:
  ∀aig signals signals' next aig' outs.
    encode_signal_imply_aux aig signals signals' next = (aig', outs) ∧
    iname x < next
    ⇒
    (eval_lit ss aig' x ⇔ eval_lit ss aig x)
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_Anon_neq]
QED

Theorem encode_signal_imply_aux_LENGTH[local]:
  ∀aig signals signals' next aig' outs'.
    encode_signal_imply_aux aig signals signals' next = (aig',outs')
    ⇒
    LENGTH outs' = MIN (LENGTH signals) (LENGTH signals')
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def, MIN_DEF]
  >> rpt (pairarg_tac >> gvs [])
QED

Theorem encode_signal_imply_aux_EVERY_leq_outs[local]:
  ∀aig signals signals' next aig' outs.
    encode_signal_imply_aux aig signals signals' next = (aig',outs) ⇒
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
  ∀aig signals signals' next aig' outs'.
    encode_signal_imply_aux aig signals signals' next = (aig',outs') ∧
    EVERY (λx. iname x < next) signals ∧
    EVERY (λx. iname x < next) signals' ∧
    LENGTH signals' = LENGTH signals ⇒
    ∀n. n < LENGTH signals ⇒
        (eval_lit ss aig' (Gate (Anon outs'❲n❳),F) ⇔
           lits_hold ss aig {signals❲n❳} ⇒
           lits_hold ss aig {signals'❲n❳})
Proof
  recInduct encode_signal_imply_aux_ind >> rw []
  >> Cases_on ‘n’ >> gvs [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> fs [lits_hold_def]
  >-
   (simp [eval_lit_def, eval_lit_not]
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

Theorem eval_gate_encode_signal_imply:
  LENGTH signals' = LENGTH signals ∧
  EVERY (λx. iname x = 0) signals  ∧
  EVERY (λx. iname x = 0) signals'
  ⇒
  (eval_gate ss (encode_signal_imply aig name signals signals') (Named n) =
   if n = Ext name then
     signal_imply ss aig ss aig signals signals'
   else eval_gate ss aig (Named n))
Proof
  strip_tac
  >> simp [encode_signal_imply_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_def]
  >> reverse IF_CASES_TAC >> gvs []
  >- (drule encode_signal_imply_eval_gate_Named >> simp [])
  >> simp [signal_imply_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP]
  >> drule_then assume_tac encode_signal_imply_aux_LENGTH >> gvs [MIN_DEF]
  >> drule encode_signal_imply_aux_eval_lit
  >> simp []
QED

Theorem eval_lit_encode_signal_imply_Gate:
  ∀signals' signals ss aig name n b.
    LENGTH signals' = LENGTH signals ∧
    EVERY (λx. iname x = 0) signals  ∧
    EVERY (λx. iname x = 0) signals'
    ⇒
    (eval_lit ss (encode_signal_imply aig name signals signals')
       (Gate (Named n), b) ⇔
     if n = Ext name then
       (b ⇎ signal_imply ss aig ss aig signals signals')
     else eval_lit ss aig (Gate (Named n), b))
Proof
  rpt strip_tac >> simp [eval_lit_def]
  >> drule_all eval_gate_encode_signal_imply
  >> rw []
QED

(* Encoding lives_hold ********************************************************)

(* Computes the disjunction of each list.
   MAPi and GENLIST were annoying to deal with here, so a separate function
   it is. *)
Definition encode_lives_hold_aux_def:
  (encode_lives_hold_aux
     (aig: ('a iext, 'i, 'l) aig)
     (signals::rest : ('a iext, 'i, 'l) lit list list)
     (next: num)
   : (('a iext, 'i, 'l) aig # num list)
   =
   let
     (aig', outs) = encode_lives_hold_aux aig rest (next + 1);
     aig  = (Anon next, MAP not signals)::aig';
     outs = next::outs
   in
     (aig, outs)) ∧
  (encode_lives_hold_aux aig _ _ = (aig, []))
End

Definition encode_lives_hold_def:
  encode_lives_hold
    (aig: ('a iext, 'i, 'l) aig)
    (name: mlstring)
    (live: ('a iext, 'i, 'l) lit list list)
  : ('a iext, 'i, 'l) aig
  =
  let
    (aig, outs) = encode_lives_hold_aux aig live 1;
  in
    (Named (Ext name),MAP (λn. (Gate (Anon n),T)) outs)::aig
End

Theorem eval_gate_encode_lives_hold_aux_Named[local]:
  ∀live aig next aig' outs.
    (encode_lives_hold_aux aig live next = (aig', outs)
    ⇒
    (eval_gate ss aig' (Named n) ⇔ eval_gate ss aig (Named n)))
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> last_x_assum drule
  >> simp [eval_lit_def]
QED

Theorem encode_lives_hold_aux_LENGTH[local]:
  ∀live aig next aig' outs.
    encode_lives_hold_aux aig live next = (aig',outs) ⇒
    LENGTH outs = LENGTH live
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> first_assum drule
  >> simp []
QED

Theorem encode_lives_hold_aux_EVERY_leq_outs[local]:
  ∀live aig next aig' outs.
     encode_lives_hold_aux aig live next = (aig',outs) ⇒
     EVERY (λout. next ≤ out) outs
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> fs [EVERY_MEM]
  >> last_x_assum drule
  >> rpt strip_tac
  >> last_x_assum drule >> simp []
QED

Theorem encode_lives_hold_aux_EXISTS_eq[local]:
  ∀live aig next aig' outs.
    encode_lives_hold_aux aig live next = (aig',outs) ∧
    EVERY (λx. iname x < next) xs
    ⇒
    (EXISTS (λx. eval_lit ss aig' x) xs ⇔ EXISTS (λx. eval_lit ss aig x) xs)
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> fs [EXISTS_MEM, EVERY_MEM]
  >> last_x_assum drule
  >> impl_tac >- (rpt strip_tac >> res_tac >> simp [])
  >> strip_tac
  >> eq_tac >> rw []
  >> metis_tac [prim_recTheory.LESS_NOT_EQ, eval_lit_Anon_neq]
QED

Theorem encode_lives_hold_aux_eval_lit[local]:
  ∀live aig next aig' outs.
    encode_lives_hold_aux aig live next = (aig',outs) ∧
    EVERY (EVERY (λx. iname x < next)) live
    ⇒
    ∀n. n < LENGTH live ⇒
       ((eval_lit ss aig' (MAP (λn. (Gate (Anon n),T)) outs)❲n❳) ⇔
        EXISTS (λp. lits_hold ss aig {p}) live❲n❳)
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> Cases_on ‘n’ >> gvs []
  >-
   (simp [eval_lit_def, lits_hold_def]
    >> simp [EXISTS_MAP, eval_lit_not]
    >> drule encode_lives_hold_aux_EXISTS_eq
    >> rename1 ‘EXISTS _ xs’
    >> disch_then $ qspec_then ‘xs’ mp_tac
    >> impl_tac >- (fs [EVERY_MEM] >> rpt strip_tac >> res_tac >> simp [])
    >> simp [])
  >> last_x_assum drule
  >> rename1 ‘EXISTS _ live❲n❳’
  >> disch_then $ qspec_then ‘n’ mp_tac
  >> impl_tac >- (fs [EVERY_MEM] >> rpt strip_tac >> res_tac >> simp [])
  >> strip_tac
  >> drule_then assume_tac encode_lives_hold_aux_LENGTH
  >> gvs [Req0 EL_MAP]
  >> drule encode_lives_hold_aux_EVERY_leq_outs
  >> simp [EVERY_EL]
  >> disch_then $ drule_then assume_tac
  >> DEP_REWRITE_TAC [eval_lit_Anon_neq]
  >> simp [iname_def]
QED

Theorem eval_gate_encode_lives_hold:
  EVERY (EVERY (λx. iname x = 0)) live
  ⇒
  eval_gate ss (encode_lives_hold aig name live) (Named n) =
  if n = Ext name then
    lives_hold ss aig live
  else eval_gate ss aig (Named n)
Proof
  strip_tac
  >> simp [encode_lives_hold_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [eval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >-
   (simp [lives_hold_def, some_signal_holds_def, EVERY_EL]
    >> drule_then assume_tac encode_lives_hold_aux_LENGTH
    >> rewrite_tac [EXISTS_NOT_EVERY]
    >> drule_then assume_tac encode_lives_hold_aux_eval_lit
    >> simp [o_DEF])
  >> drule eval_gate_encode_lives_hold_aux_Named
  >> simp []
QED

Theorem eval_lit_encode_lives_hold_Named:
  EVERY (EVERY (λx. iname x = 0)) live
  ⇒
  eval_lit ss (encode_lives_hold aig name live) (Gate (Named n), b) =
  if n = Ext name then
    (b ⇎ lives_hold ss aig live)
  else eval_lit ss aig (Gate (Named n), b)
Proof
  strip_tac >> simp [eval_lit_def]
  >> drule_all eval_gate_encode_lives_hold
  >> rw []
QED

(* Encoding certificate conditions ********************************************)

Definition encode_is_witness_reset_def:
  encode_is_witness_reset
    (maig: ('a, 'i, 'l) aig)
    (mreset: 'l -> ('a, 'i, 'l) lit option)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlatches: 'l list)
    (waig: ('b, 'i, 'l) aig)
    (wreset: 'l -> ('b, 'i, 'l) lit option)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wlatches: 'l list)
    (klatches: 'l list)  (* mlatches ∩ wlatches *)
  =
  let
    aig  = imerge_aigs maig waig;
    aig  = encode_is_reset aig «mreset» (ileft_reset mreset) mlatches;
    aig  = encode_lits_hold aig «mcnstrs» (ileft_name_lits mcnstrs);
    aig  = encode_is_reset aig «wreset» (iright_reset wreset) klatches;
    aig  = encode_lits_hold aig «wcnstrs» (iright_name_lits wcnstrs);
    lhss =
      [(Gate (Named (Ext «mreset»)), F);
       (Gate (Named (Ext «mcnstrs»)), F)];
    rhss =
      [(Gate (Named (Ext «wreset»)), F);
       (Gate (Named (Ext «wcnstrs»)), F)];
  in
    encode_imply aig «reset» T lhss rhss
End

Definition encode_is_witness_transition_def:
  encode_is_witness_transition
    (maig: ('a, 'i, 'l) aig)
    (mnext: 'l -> ('a, 'i, 'l) lit)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlatches: 'l list)
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wlatches: 'l list)
    (klatches: 'l list)  (* mlatches ∩ wlatches *)
  =
  let
    aig  = imerge_aigs maig waig;
    aig  = encode_lits_hold aig «mcnstrs» (ileft_name_lits mcnstrs);
    aig  = encode_lits_hold aig «wcnstrs» (iright_name_lits wcnstrs);
    aig  = iext_aig (pair_aigs aig aig);
    aig  = encode_is_next aig «mnext» (iext_lit ∘ left_name_lit ∘ mnext) mlatches;
    aig  = encode_is_next aig «wnext» (iext_lit ∘ right_name_lit ∘ wnext) klatches;
    lhss =
      [(Gate (Named (Ext «mnext»)), F);
       iext_lit (left_lit (Gate (Named (Ext «mcnstrs»)), F));
       iext_lit (right_lit (Gate (Named (Ext «mcnstrs»)), F));
       iext_lit (left_lit (Gate (Named (Ext «wcnstrs»)), F));
      ];
    rhss =
      [(Gate (Named (Ext «wnext»)), F);
       iext_lit (right_lit (Gate (Named (Ext «wcnstrs»)), F))];
  in
    encode_imply aig «transition» T lhss rhss
End

Definition encode_is_witness_property_def:
  encode_is_witness_property
    (maig: ('a, 'i, 'l) aig)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mpreds: ('a, 'i, 'l) lit list)
    (waig: ('b, 'i, 'l) aig)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wpreds: ('b, 'i, 'l) lit list)
  =
  let
    aig  = imerge_aigs maig waig;
    aig  = encode_lits_hold aig «mcnstrs» (ileft_name_lits mcnstrs);
    aig  = encode_lits_hold aig «mpreds» (ileft_name_lits mpreds);
    aig  = encode_lits_hold aig «wcnstrs» (iright_name_lits wcnstrs);
    aig  = encode_lits_hold aig «wpreds» (iright_name_lits wpreds);
    lhss =
      [(Gate (Named (Ext «mcnstrs»)),F);
       (Gate (Named (Ext «wcnstrs»)),F);
       (Gate (Named (Ext «wpreds»)),F)];
    rhss = [(Gate (Named (Ext «mpreds»)), F);]
  in
    encode_imply aig «property» T lhss rhss
End

Definition encode_is_witness_base_def:
  encode_is_witness_base
    (waig: ('a, 'i, 'l) aig)
    (wreset: 'l -> ('a, 'i, 'l) lit option)
    (wcnstrs: ('a, 'i, 'l) lit list)
    (wpreds: ('a, 'i, 'l) lit list)
    (wlatches: 'l list)
  ⇔
    let
      aig  = iext_aig waig;
      aig  = encode_is_reset aig «wreset» (iext_reset wreset) wlatches;
      aig  = encode_lits_hold aig «wcnstrs» (MAP iext_lit wcnstrs);
      aig  = encode_lits_hold aig «wpreds» (MAP iext_lit wpreds);
      lhss =
        [(Gate (Named (Ext «wreset»)),F);
         (Gate (Named (Ext «wcnstrs»)),F)];
      rhss = [(Gate (Named (Ext «wpreds»)), F)]
  in
    encode_imply aig «base» T lhss rhss
End

Definition encode_is_witness_step_def:
  encode_is_witness_step
    (waig: ('a, 'i, 'l) aig)
    (wnext: 'l -> ('a, 'i, 'l) lit)
    (wcnstrs: ('a, 'i, 'l) lit list)
    (wpreds: ('a, 'i, 'l) lit list)
    (wlatches: 'l list)
  ⇔
    let
      aig  = iext_aig waig;
      aig  = encode_lits_hold aig «wcnstrs» (MAP iext_lit wcnstrs);
      aig  = encode_lits_hold aig «wpreds» (MAP iext_lit wpreds);
      aig  = iext_aig (pair_aigs aig aig);
      aig  = encode_is_next aig «wnext» (iext_lit ∘ wnext) wlatches;
      lhss =
        [iext_lit (left_lit (Gate (Named (Ext «wpreds»)), F));
         (Gate (Named (Ext «wnext»)), F);
         iext_lit (right_lit (Gate (Named (Ext «wcnstrs»)), F));
         iext_lit (left_lit (Gate (Named (Ext «wcnstrs»)), F))];
      rhss = [iext_lit (right_lit (Gate (Named (Ext «wpreds»)), F))]
    in
      encode_imply aig «step» T lhss rhss
End

Definition encode_is_witness_liveness_def:
  encode_is_witness_liveness
    (maig: ('a, 'i, 'l) aig)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlive: ('a, 'i, 'l) lit list list)
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wpreds: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    msignals  = ileft_name_lits (FLAT (qleft_live mlive));
    wsignals  = iright_name_lits (FLAT (qinterv_live_l_r interv wlive));
    mqaig = qleft maig;
    wqaig = qinterv_l_r interv waig;
    qaig = imerge_aigs mqaig wqaig;
    qaig = encode_signal_imply qaig «lives_imply» wsignals msignals;
    aig = imerge_aigs maig waig;
    aig = encode_lits_hold aig «mcnstrs» (ileft_name_lits mcnstrs);
    aig = encode_lits_hold aig «wcnstrs» (iright_name_lits wcnstrs);
    aig = encode_lits_hold aig «wpreds» (iright_name_lits wpreds);
    aig = iext_aig (pair_aigs aig aig);
    aig =
      encode_is_next aig «wnext» (iext_lit ∘ right_name_lit ∘ wnext) wlatches;
    aig  = imerge_aigs aig qaig;
    lhss = [
      iext_lit
        (left_name_lit (iext_lit (left_lit (Gate (Named (Ext «mcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (left_lit (Gate (Named (Ext «wcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (left_lit (Gate (Named (Ext «wpreds»)), F))));
      iext_lit
        (left_name_lit (iext_lit (right_lit (Gate (Named (Ext «mcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (right_lit (Gate (Named (Ext «wcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (right_lit (Gate (Named (Ext «wpreds»)), F))));
      iext_lit
        (left_name_lit ((Gate (Named (Ext «wnext»)), F)));
    ];
    rhss = [iext_lit (right_name_lit (Gate (Named (Ext «lives_imply»)), F))]
  in
    encode_imply aig «liveness» T lhss rhss
End

Definition encode_is_witness_decrease_def:
  encode_is_witness_decrease
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wpreds: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    wqaig = qinterv_r_l interv waig;
    qaig = iext_aig wqaig;
    wlive = MAP (MAP iext_lit) (qinterv_live_r_l interv wlive);
    qaig = encode_lives_hold qaig «lives_hold» wlive;
    aig = iext_aig waig;
    aig = encode_lits_hold aig «wcnstrs» (MAP iext_lit wcnstrs);
    aig = encode_lits_hold aig «wpreds» (MAP iext_lit wpreds);
    aig = iext_aig (pair_aigs aig aig);
    aig = encode_is_next aig «wnext» (iext_lit ∘ wnext) wlatches;
    aig = imerge_aigs aig qaig;
    lhss = [
      iext_lit
        (left_name_lit (iext_lit (left_lit (Gate (Named (Ext «wcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (left_lit (Gate (Named (Ext «wpreds»)), F))));
      iext_lit
        (left_name_lit (iext_lit (right_lit (Gate (Named (Ext «wcnstrs»)), F))));
      iext_lit
        (left_name_lit (iext_lit (right_lit (Gate (Named (Ext «wpreds»)), F))));
      iext_lit
        (left_name_lit ((Gate (Named (Ext «wnext»)), F)));
    ];
    rhss = [iext_lit (right_name_lit (Gate (Named (Ext «lives_hold»)), F))]
  in
    encode_imply aig «decrease» T lhss rhss
End

Definition encode_is_witness_closure_def:
  encode_is_witness_closure
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wpreds: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    wqaig₀ = qinterv_ll_r interv waig;
    qaig₀ = iext_aig wqaig₀;
    wlive₀ = MAP (MAP iext_lit) (qinterv_live_ll_r interv wlive);
    qaig₀ = encode_lives_hold qaig₀ «lives_hold02» wlive₀;
    wqaig₁ = qinterv_lr_r interv waig;
    qaig₁ = iext_aig wqaig₁;
    wlive₁ = MAP (MAP iext_lit) (qinterv_live_lr_r interv wlive);
    qaig₁ = encode_lives_hold qaig₁ «lives_hold12» wlive₁;
    aig₀ = iext_aig waig;
    aig₀ = encode_lits_hold aig₀ «wcnstrs» (MAP iext_lit wcnstrs);
    aig₀ = encode_lits_hold aig₀ «wpreds» (MAP iext_lit wpreds);
    aig = iext_aig (pair_aigs aig₀ aig₀);
    aig = encode_is_next aig «wnext» (iext_lit ∘ wnext) wlatches;
    aig = iext_aig (pair_aigs aig aig₀);
    aig = imerge_aigs aig qaig₀;
    aig = imerge_aigs aig qaig₁;
    lhss = [
      iext_lit (left_name_lit (iext_lit (left_name_lit
        (iext_lit (left_lit (iext_lit (left_lit
          (Gate (Named (Ext «wcnstrs»)), F))))))));
      iext_lit (left_name_lit (iext_lit (left_name_lit
        (iext_lit (left_lit (iext_lit (left_lit
          (Gate (Named (Ext «wpreds»)), F))))))));
      iext_lit (left_name_lit (iext_lit (left_name_lit
        (iext_lit (left_lit (iext_lit (right_lit
          (Gate (Named (Ext «wcnstrs»)), F))))))));
      iext_lit (left_name_lit (iext_lit (left_name_lit
        (iext_lit (left_lit (iext_lit (right_lit
          (Gate (Named (Ext «wpreds»)), F))))))));
      iext_lit (left_name_lit (iext_lit (left_name_lit
        (iext_lit (right_lit (Gate (Named (Ext «wcnstrs»)), F))))));
      iext_lit (left_name_lit (iext_lit (left_name_lit
        (iext_lit (right_lit (Gate (Named (Ext «wpreds»)), F))))));
      iext_lit (left_name_lit (iext_lit (left_name_lit
        (iext_lit (left_lit (Gate (Named (Ext «wnext»)), F))))));
      iext_lit (left_name_lit (iext_lit (right_name_lit
        (Gate (Named (Ext «lives_hold02»)), F))))
    ];
    rhss = [iext_lit (right_name_lit (Gate (Named (Ext «lives_hold12»)), F))]
  in
    encode_imply aig «closure» T lhss rhss
End

Definition encode_is_witness_consistent_def:
  encode_is_witness_consistent
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wpreds: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    wlive₀ = MAP ileft_name_lits (qinterv_live_ll_lr interv wlive);
    wlive₁ = MAP iright_name_lits (qinterv_live_lr_r interv wlive);
    qaig₀ = qinterv_ll_lr interv waig;
    qaig₁ = qinterv_lr_r interv waig;
    qaig  = imerge_aigs qaig₀ qaig₁;
    qaig = encode_signal_imply qaig «lives_imply» (FLAT wlive₀) (FLAT wlive₁) ;
    qaig = encode_lives_hold qaig «lives_hold01» wlive₀;
    qaig = encode_lives_hold qaig «lives_hold12» wlive₁;
    aig₀ = iext_aig waig;
    aig₀ = encode_lits_hold aig₀ «wcnstrs» (MAP iext_lit wcnstrs);
    aig₀ = encode_lits_hold aig₀ «wpreds» (MAP iext_lit wpreds);
    aig = iext_aig (pair_aigs aig₀ aig₀);
    aig = encode_is_next aig «wnext» (iext_lit ∘ wnext) wlatches;
    aig = iext_aig (pair_aigs aig aig₀);
    aig = encode_is_next_with aig «wnext»
             (iext_lit ∘ left_lit ∘ iext_lit ∘ right_lit) (iext_lit ∘ right_lit)
             (iext_lit ∘ wnext) wlatches;
    aig  = imerge_aigs aig qaig;
    lhss = [
      iext_lit (left_name_lit (iext_lit (left_lit
        (iext_lit (left_lit (Gate (Named (Ext «wcnstrs»)), F))))));
      iext_lit (left_name_lit (iext_lit (left_lit
        (iext_lit (left_lit (Gate (Named (Ext «wpreds»)), F))))));
      iext_lit (left_name_lit (iext_lit (left_lit
        (iext_lit (right_lit (Gate (Named (Ext «wcnstrs»)), F))))));
      iext_lit (left_name_lit (iext_lit (left_lit
        (iext_lit (right_lit (Gate (Named (Ext «wpreds»)), F))))));
      iext_lit (left_name_lit (iext_lit (right_lit
        (Gate (Named (Ext «wcnstrs»)), F))));
      iext_lit (left_name_lit (iext_lit (right_lit
        (Gate (Named (Ext «wpreds»)), F))));
      iext_lit (left_name_lit (iext_lit (left_lit
        (Gate (Named (Ext «wnext»)), F))));
      iext_lit (left_name_lit (Gate (Named (Ext «wnext»)), F));
      iext_lit (right_name_lit (Gate (Named (Ext «lives_hold01»)), F));
      iext_lit (right_name_lit (Gate (Named (Ext «lives_hold12»)), F))
      ];
    rhss = [iext_lit (right_name_lit (Gate (Named (Ext «lives_imply»)), F))];
  in
    encode_imply aig «consistent» T lhss rhss
End

(* Proving correctness of the encodings ***************************************)

(* A bunch of trivial helper lemmas, which keep the proof state readable
   when an encoding function uses many other encoding functions. *)

Theorem is_reset_iext[local,simp]:
  is_reset ss (iext_aig aig) (iext_reset reset) latches ⇔
    is_reset ss aig reset latches
Proof
  simp [is_reset_def, iext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_ileft[local,simp]:
  is_reset ss (imerge_aigs laig raig) (ileft_reset lreset) latches ⇔
    is_reset ss laig lreset latches
Proof
  simp [is_reset_def, imerge_aigs_def, ileft_reset_def, left_reset_def,
        eval_lit_def, iext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_iright[local,simp]:
  is_reset ss (imerge_aigs laig raig) (iright_reset rreset) latches ⇔
    is_reset ss raig rreset latches
Proof
  simp [is_reset_def, imerge_aigs_def, iright_reset_def, right_reset_def,
        eval_lit_def, iext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_encode_lits_hold_iright[local,simp]:
  is_reset ss
    (encode_lits_hold aig name lits) (iright_reset reset) latches ⇔
  is_reset ss aig (iright_reset reset) latches
Proof
  simp [is_reset_def, encode_lits_hold_def, iright_reset_def, right_reset_def,
        eval_lit_def, iext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_encode_is_reset_iright[local,simp]:
  is_reset ss (encode_is_reset aig name reset' latches')
    (iright_reset reset) latches ⇔
  is_reset ss aig (iright_reset reset) latches
Proof
  simp [is_reset_def, encode_is_reset_def, iright_reset_def, eval_lit_def,
        iext_reset_def, PULL_EXISTS]
QED

Theorem lits_hold_iext[local,simp]:
  lits_hold ss (iext_aig aig) (set (MAP iext_lit preds)) ⇔
    lits_hold ss aig (set preds)
Proof
  simp [lits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_ileft[local,simp]:
  lits_hold ss (imerge_aigs laig raig) (set (ileft_name_lits preds)) ⇔
    lits_hold ss laig (set preds)
Proof
  simp [lits_hold_def, ileft_name_lits_def, imerge_aigs_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_iright[local,simp]:
  lits_hold ss (imerge_aigs laig raig) (set (iright_name_lits preds)) ⇔
    lits_hold ss raig (set preds)
Proof
  simp [lits_hold_def, iright_name_lits_def, imerge_aigs_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_encode_is_reset_ileft[local,simp]:
  lits_hold ss
    (encode_is_reset aig name reset latches) (set (ileft_name_lits preds)) ⇔
  lits_hold ss aig (set (ileft_name_lits preds))
Proof
  simp [lits_hold_def, encode_is_reset_def, ileft_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_encode_is_reset_iright[local,simp]:
  lits_hold ss
    (encode_is_reset aig name reset latches) (set (iright_name_lits preds)) ⇔
  lits_hold ss aig (set (iright_name_lits preds))
Proof
  simp [lits_hold_def, encode_is_reset_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_encode_is_reset_iext[local,simp]:
  lits_hold ss
    (encode_is_reset aig name reset latches) (set (MAP iext_lit preds)) ⇔
  lits_hold ss aig (set (MAP iext_lit preds))
Proof
  simp [lits_hold_def, encode_is_reset_def, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_encode_lits_hold_iright[local,simp]:
  lits_hold ss (encode_lits_hold aig name preds') (set (iright_name_lits preds)) ⇔
    lits_hold ss aig (set (iright_name_lits preds))
Proof
  simp [lits_hold_def, encode_lits_hold_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_encode_lits_hold_iext_lit[local,simp]:
  lits_hold ss (encode_lits_hold aig name preds') (set (MAP iext_lit preds)) ⇔
    lits_hold ss aig (set (MAP iext_lit preds))
Proof
  simp [lits_hold_def, encode_lits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_encode_lits_hold_iright[local,simp]:
  lits_hold ss (encode_lits_hold aig name preds') (set (iright_name_lits preds)) ⇔
    lits_hold ss aig (set (iright_name_lits preds))
Proof
  simp [lits_hold_def, encode_lits_hold_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem lits_hold_encode_lits_hold_ileft[local,simp]:
  lits_hold ss (encode_lits_hold aig name preds') (set (ileft_name_lits preds)) ⇔
    lits_hold ss aig (set (ileft_name_lits preds))
Proof
  simp [lits_hold_def, encode_lits_hold_def, ileft_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem signal_imply_iright_ileft[local,simp]:
  signal_imply ss₀ (imerge_aigs aig₁ aig₂)
    ss₁ (imerge_aigs aig₃ aig₄) (iright_name_lits signals')
    (ileft_name_lits signals)
  ⇔
  signal_imply ss₀ aig₂ ss₁ aig₃ signals' signals
Proof
  simp [signal_imply_def, ileft_name_lits_def, iright_name_lits_def,
        lits_hold_def, LIST_REL_MAP]
QED

Theorem signal_imply_ileft_iright[local,simp]:
  signal_imply ss₀ (imerge_aigs aig₁ aig₂)
    ss₁ (imerge_aigs aig₃ aig₄) (ileft_name_lits signals')
    (iright_name_lits signals)
  ⇔
  signal_imply ss₀ aig₁ ss₁ aig₄ signals' signals
Proof
  simp [signal_imply_def, ileft_name_lits_def, iright_name_lits_def,
        lits_hold_def, LIST_REL_MAP]
QED

Theorem lives_hold_iext_aig[local,simp]:
  lives_hold ss (iext_aig aig) (MAP (MAP iext_lit) lives)
  ⇔
  lives_hold ss aig lives
Proof
  simp [lives_hold_def, some_signal_holds_def, lits_hold_def,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem encode_lives_hold_aux_eval_lit_iext[local]:
  ∀live aig next aig' outs.
    encode_lives_hold_aux aig live next = (aig',outs)
    ⇒
    (eval_lit ss aig' (iext_lit lit) ⇔ eval_lit ss aig (iext_lit lit))
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> last_x_assum drule >> simp []
QED

Theorem encode_signal_imply_aux_eval_lit_iext[local]:
  ∀aig signals signals' next aig' outs.
    encode_signal_imply_aux aig signals signals' next = (aig',outs)
    ⇒
    (eval_lit ss aig' (iext_lit lit) ⇔ eval_lit ss aig (iext_lit lit))
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
QED

Theorem lives_hold_encode_lives_hold_iright[local,simp]:
  lives_hold ss (encode_lives_hold aig name live) (MAP iright_name_lits live')
  ⇔
  lives_hold ss aig (MAP iright_name_lits live')
Proof
  simp [encode_lives_hold_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [lives_hold_def, some_signal_holds_def,
           lits_hold_def, iright_name_lits_def,
           EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
  >> drule encode_lives_hold_aux_eval_lit_iext >> simp []
QED

Theorem lives_hold_encode_signal_imply_ileft[local,simp]:
  lives_hold ss (encode_signal_imply aig name signals signals')
    (MAP ileft_name_lits live')
  ⇔
  lives_hold ss aig (MAP ileft_name_lits live')
Proof
  simp [encode_signal_imply_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [lives_hold_def, some_signal_holds_def,
           lits_hold_def, ileft_name_lits_def,
           EVERY_MEM, MEM_MAP, EXISTS_MEM, PULL_EXISTS]
  >> drule encode_signal_imply_aux_eval_lit_iext
  >> simp []
QED

Theorem lives_hold_encode_signal_imply_iright[local,simp]:
  lives_hold ss (encode_signal_imply aig name signals signals')
    (MAP iright_name_lits live')
  ⇔
  lives_hold ss aig (MAP iright_name_lits live')
Proof
  simp [encode_signal_imply_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [lives_hold_def, some_signal_holds_def,
           lits_hold_def, iright_name_lits_def,
           EVERY_MEM, MEM_MAP, EXISTS_MEM, PULL_EXISTS]
  >> drule encode_signal_imply_aux_eval_lit_iext
  >> simp []
QED

Theorem lives_hold_imerge_aigs_ileft[local,simp]:
  lives_hold ss (imerge_aigs aig₀ aig₁) (MAP ileft_name_lits live)
  ⇔
  lives_hold ss aig₀ live
Proof
  simp [lives_hold_def, some_signal_holds_def,
        ileft_name_lits_def, lits_hold_def,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_imerge_aigs_iright[local,simp]:
  lives_hold ss (imerge_aigs aig₀ aig₁) (MAP iright_name_lits live)
  ⇔
  lives_hold ss aig₁ live
Proof
  simp [lives_hold_def, some_signal_holds_def,
        iright_name_lits_def, lits_hold_def,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem qinterv_r_l_cons[local]:
  qinterv_r_l interv (a::aig) =
    (qinterv_and INR INR INL interv a)::(qinterv_r_l interv aig)
Proof
  simp [qinterv_r_l_def, qinterv_def]
QED

Theorem qinterv_ll_r_cons[local]:
  qinterv_ll_r interv (a::aig) =
    (qinterv_and (INL ∘ INL) (INL ∘ INL) INR interv a)
    ::(qinterv_ll_r interv aig)
Proof
  simp [qinterv_ll_r_def, qinterv_def]
QED

Theorem qinterv_lr_r_cons[local]:
  qinterv_lr_r interv (a::aig) =
    (qinterv_and (INL ∘ INR) (INL ∘ INR) INR interv a)
    ::(qinterv_lr_r interv aig)
Proof
  simp [qinterv_lr_r_def, qinterv_def]
QED

Theorem qinterv_ll_lr_cons[local]:
  qinterv_ll_lr interv (a::aig) =
    (qinterv_and (INL ∘ INL) (INL ∘ INL) (INL ∘ INR) interv a)
    ::(qinterv_ll_lr interv aig)
Proof
  simp [qinterv_ll_lr_def, qinterv_def]
QED

Theorem qinterv_l_r_cons[local]:
  qinterv_l_r interv (a::aig) =
    (qinterv_and INL INL INR interv a)::(qinterv_l_r interv aig)
Proof
  simp [qinterv_l_r_def, qinterv_def]
QED

Theorem eval_lit_qinterv_r_l_eq[local]:
  (∀lit.
     eval_lit (state_pair s₀ s₁) (qinterv_r_l interv aig)
       (qinterv_lit INR INR INL interv lit)
     ⇔
     eval_lit (state_pair s₁ s₀) (qinterv_l_r interv aig)
       (qinterv_lit INL INL INR interv lit)) ∧
  (∀a.
     eval_gate (state_pair s₀ s₁) (qinterv_r_l interv aig) a ⇔
     eval_gate (state_pair s₁ s₀) (qinterv_l_r interv aig) a)
Proof
  Induct_on ‘aig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’
  >-
   (simp [qinterv_r_l_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def, state_pair_def]
    >> rpt CASE_TAC
    >> simp [eval_lit_def]
    >> rename1 ‘bvar_map _ _ base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def])
  >- simp [qinterv_r_l_def, qinterv_l_r_def, qinterv_def]
  >-
   (simp [qinterv_r_l_cons, qinterv_l_r_cons]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def]
    >-
     (reverse CASE_TAC
      >- (CASE_TAC >> simp [eval_lit_def, state_pair_def])
      >> simp [eval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_and_def, AllCaseEqs()]
      >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [eval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [eval_lit_def])
  >> rename1 ‘qinterv_r_l _ (h::_)’
  >> Cases_on ‘h’
  >> simp [qinterv_r_l_cons, qinterv_l_r_cons]
  >> simp [qinterv_and_def, eval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem eval_lit_qinterv_ll_r_eq[local]:
  (∀lit.
     eval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_ll_r interv aig)
       (qinterv_lit (INL ∘ INL) (INL ∘ INL) INR interv lit)
     ⇔
     eval_lit (state_pair s₀ s₂) (qinterv_l_r interv aig)
       (qinterv_lit INL INL INR interv lit)) ∧
  (∀a.
     eval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_ll_r interv aig) a ⇔
     eval_gate (state_pair s₀ s₂) (qinterv_l_r interv aig) a)
Proof
  Induct_on ‘aig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_ll_r_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def, state_pair_def]
    >> rpt CASE_TAC
    >> simp [eval_lit_def]
    >> rename1 ‘bvar_map _ _ base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def])
  >- simp [qinterv_ll_r_def, qinterv_l_r_def, qinterv_def]
  >-
   (simp [qinterv_ll_r_cons, qinterv_l_r_cons]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def]
    >-
     (reverse CASE_TAC
      >- (CASE_TAC >> simp [eval_lit_def, state_pair_def])
      >> simp [eval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_and_def, AllCaseEqs()]
      >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [eval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [eval_lit_def])
  >> rename1 ‘qinterv_ll_r _ (h::_)’
  >> Cases_on ‘h’
  >> simp [qinterv_ll_r_cons, qinterv_l_r_cons]
  >> simp [qinterv_and_def, eval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem eval_lit_qinterv_lr_r_eq[local]:
  (∀lit.
     eval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_lr_r interv aig)
       (qinterv_lit (INL ∘ INR) (INL ∘ INR) INR interv lit)
     ⇔
     eval_lit (state_pair s₁ s₂) (qinterv_l_r interv aig)
       (qinterv_lit INL INL INR interv lit)) ∧
  (∀a.
     eval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_lr_r interv aig) a ⇔
     eval_gate (state_pair s₁ s₂) (qinterv_l_r interv aig) a)
Proof
  Induct_on ‘aig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_lr_r_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def, state_pair_def]
    >> rpt CASE_TAC
    >> simp [eval_lit_def]
    >> rename1 ‘bvar_map _ _ base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def])
  >- simp [qinterv_lr_r_def, qinterv_l_r_def, qinterv_def]
  >-
   (simp [qinterv_lr_r_cons, qinterv_l_r_cons]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def]
    >-
     (reverse CASE_TAC
      >- (CASE_TAC >> simp [eval_lit_def, state_pair_def])
      >> simp [eval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_and_def, AllCaseEqs()]
      >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [eval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [eval_lit_def])
  >> rename1 ‘qinterv_lr_r _ (h::_)’
  >> Cases_on ‘h’
  >> simp [qinterv_lr_r_cons, qinterv_l_r_cons]
  >> simp [qinterv_and_def, eval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem eval_lit_qinterv_ll_lr_eq[local]:
  (∀lit.
     eval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_ll_lr interv aig)
       (qinterv_lit (INL ∘ INL) (INL ∘ INL) (INL ∘ INR) interv lit)
     ⇔
     eval_lit (state_pair s₀ s₁) (qinterv_l_r interv aig)
       (qinterv_lit INL INL INR interv lit)) ∧
  (∀a.
     eval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_ll_lr interv aig) a ⇔
     eval_gate (state_pair s₀ s₁) (qinterv_l_r interv aig) a)
Proof
  Induct_on ‘aig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_ll_lr_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def, state_pair_def]
    >> rpt CASE_TAC
    >> simp [eval_lit_def]
    >> rename1 ‘bvar_map _ _ base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def])
  >- simp [qinterv_ll_lr_def, qinterv_l_r_def, qinterv_def]
  >-
   (simp [qinterv_ll_lr_cons, qinterv_l_r_cons]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def]
    >-
     (reverse CASE_TAC
      >- (CASE_TAC >> simp [eval_lit_def, state_pair_def])
      >> simp [eval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_and_def, AllCaseEqs()]
      >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [eval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [eval_lit_def])
  >> rename1 ‘qinterv_ll_lr _ (h::_)’
  >> Cases_on ‘h’
  >> simp [qinterv_ll_lr_cons, qinterv_l_r_cons]
  >> simp [qinterv_and_def, eval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_r_l_eq[local]:
  lives_hold (state_pair s₀ s₁)
    (qinterv_r_l interv waig) (qinterv_live_r_l interv wlive)
  ⇔
  lives_hold (state_pair s₁ s₀)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive)
Proof
  simp [lives_hold_def, some_signal_holds_def,
        qinterv_live_r_l_def,
        qinterv_live_l_r_def,
        qinterv_live_def,
        lits_hold_def,
        eval_lit_qinterv_r_l_eq,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_ll_r_eq[local]:
  lives_hold (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_ll_r interv waig) (qinterv_live_ll_r interv wlive)
  ⇔
  lives_hold (state_pair s₀ s₂)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive)
Proof
  simp [lives_hold_def, some_signal_holds_def,
        qinterv_live_ll_r_def,
        qinterv_live_l_r_def,
        qinterv_live_def,
        lits_hold_def,
        eval_lit_qinterv_ll_r_eq,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_ll_lr_eq[local]:
  lives_hold (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_ll_lr interv waig) (qinterv_live_ll_lr interv wlive)
  ⇔
  lives_hold (state_pair s₀ s₁)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive)
Proof
  simp [lives_hold_def, some_signal_holds_def,
        qinterv_live_ll_lr_def, qinterv_live_l_r_def, qinterv_live_def,
        lits_hold_def, eval_lit_qinterv_ll_lr_eq,
        EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_lr_r_eq[local]:
  lives_hold (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_lr_r interv waig) (qinterv_live_lr_r interv wlive)
  ⇔
  lives_hold (state_pair s₁ s₂)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive)
Proof
  simp [lives_hold_def, some_signal_holds_def,
        qinterv_live_lr_r_def,
        qinterv_live_l_r_def,
        qinterv_live_def,
        lits_hold_def,
        eval_lit_qinterv_lr_r_eq,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem FLAT_qinterv_live_flip[local]:
  FLAT (qinterv_live_lr_r interv wlive) =
    MAP (qinterv_lit (INL ∘ INR) (INL ∘ INR) INR interv) (FLAT wlive)
  ∧
  FLAT (qinterv_live_l_r interv wlive) =
    MAP (qinterv_lit INL INL INR interv) (FLAT wlive)
  ∧
  FLAT (qinterv_live_ll_lr interv wlive) =
    MAP (qinterv_lit (INL ∘ INL) (INL ∘ INL) (INL ∘ INR) interv) (FLAT wlive)
Proof
  simp [qinterv_live_lr_r_def, qinterv_live_def, qinterv_live_l_r_def,
        qinterv_live_ll_lr_def,
        GSYM MAP_FLAT]
QED

Theorem signal_imply_right_lr_r_eq[local]:
  signal_imply ss aig
    (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_lr_r interv waig)
    signals
    (FLAT (qinterv_live_lr_r interv wlive))
  ⇔
  signal_imply ss aig (state_pair s₁ s₂) (qinterv_l_r interv waig)
    signals (FLAT (qinterv_live_l_r interv wlive))
Proof
  simp [signal_imply_def, FLAT_qinterv_live_flip, LIST_REL_EL_EQN]
  >> eq_tac >> rw []
  >> gvs [Req0 EL_MAP, lits_hold_def, eval_lit_qinterv_lr_r_eq]
QED

Theorem signal_imply_left_ll_lr_eq[local]:
  signal_imply
    (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_ll_lr interv waig)
    ss aig
    (FLAT (qinterv_live_ll_lr interv wlive))
    signals
  ⇔
  signal_imply (state_pair s₀ s₁) (qinterv_l_r interv waig) ss aig
    (FLAT (qinterv_live_l_r interv wlive)) signals
Proof
  simp [signal_imply_def, FLAT_qinterv_live_flip, LIST_REL_EL_EQN]
  >> eq_tac >> rw []
  >> gvs [Req0 EL_MAP, lits_hold_def, eval_lit_qinterv_ll_lr_eq]
QED

Theorem FLAT_MAP_name_lits_flip[local]:
  FLAT (MAP ileft_name_lits xs) = ileft_name_lits (FLAT xs) ∧
  FLAT (MAP iright_name_lits xs) = iright_name_lits (FLAT xs)
Proof
  simp [ileft_name_lits_def, iright_name_lits_def, GSYM MAP_FLAT]
QED

(* Main encoder theorems ******************************************************)

Definition reset_encoding_is_unsat_def:
  reset_encoding_is_unsat
    maig mreset mcnstrs mlatches
    waig wreset wcnstrs wlatches klatches
  ⇔
  (¬∃ss.
    (eval_gate ss
       (encode_is_witness_reset
          maig mreset mcnstrs mlatches
          waig wreset wcnstrs wlatches klatches)
       (Named (Ext «reset»))))
End

Theorem eval_gate_encode_is_witness_reset:
  (set klatches) = (set mlatches) ∩ (set wlatches)
  ⇒
  (reset_encoding_is_unsat
    maig mreset mcnstrs mlatches
    waig wreset wcnstrs wlatches klatches
   =
   is_witness_reset
     maig mreset (set mcnstrs) (set mlatches)
     waig wreset (set wcnstrs) (set wlatches))
Proof
  simp [
      reset_encoding_is_unsat_def,
      is_witness_reset_def, encode_is_witness_reset_def,
      eval_gate_encode_imply,
      eval_lit_encode_lits_hold_Named,
      eval_lit_encode_is_reset_Named
    ]
  >> metis_tac []
QED

Definition transition_encoding_is_unsat_def:
  transition_encoding_is_unsat
    maig mnext mcnstrs mlatches
    waig wnext wcnstrs wlatches klatches
  ⇔
  (¬∃ss.
     (eval_gate ss
       (encode_is_witness_transition
          maig mnext mcnstrs mlatches
          waig wnext wcnstrs wlatches klatches)
       (Named (Ext «transition»))))
End

Theorem eval_gate_encode_is_witness_transition:
  (set klatches) = (set mlatches) ∩ (set wlatches)
  ⇒
  (transition_encoding_is_unsat
    maig mnext mcnstrs mlatches
    waig wnext wcnstrs wlatches klatches ⇔
  is_witness_transition
    maig mnext (set mcnstrs) (set mlatches)
    waig wnext (set wcnstrs) (set wlatches))
Proof
  strip_tac
  >> simp [
      transition_encoding_is_unsat_def,
      encode_is_witness_transition_def,
      eval_gate_encode_imply,
      encode_is_next_def, encode_is_next_with_def,
      eval_lit_encode_equiv_Named,
      eval_lit_encode_lits_hold_Named,
      FORALL_STATE_PAIR,
      is_witness_transition_def, is_next_def, eval_lit_base,
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

Definition property_encoding_is_unsat_def:
  property_encoding_is_unsat
    maig mcnstrs mpreds
    waig wcnstrs wpreds
  ⇔
  (¬∃ss.
     (eval_gate ss
       (encode_is_witness_property
          maig mcnstrs mpreds
          waig wcnstrs wpreds)
       (Named (Ext «property»))))
End

Theorem eval_gate_encode_is_witness_property:
  property_encoding_is_unsat
    maig mcnstrs mpreds
    waig wcnstrs wpreds
  =
  is_witness_property
    maig (set mpreds) (set mcnstrs)
    waig (set wpreds) (set wcnstrs)
Proof
  simp [
      property_encoding_is_unsat_def,
      encode_is_witness_property_def,
      eval_gate_encode_imply,
      eval_lit_encode_lits_hold_Named,
      is_witness_property_def
    ]
  >> metis_tac []
QED

Definition base_encoding_is_unsat_def:
  base_encoding_is_unsat
    waig wreset wcnstrs wpreds wlatches
  ⇔
  (¬∃ss.
     (eval_gate ss
       (encode_is_witness_base
          waig wreset wcnstrs wpreds wlatches)
       (Named (Ext «base»))))
End

Theorem eval_gate_encode_is_witness_base:
  base_encoding_is_unsat
    waig wreset wcnstrs wpreds wlatches
  =
  is_witness_base
    waig wreset (set wpreds) (set wcnstrs) (set wlatches)
Proof
  simp [
      base_encoding_is_unsat_def,
      encode_is_witness_base_def,
      eval_gate_encode_imply,
      eval_lit_encode_lits_hold_Named,
      eval_lit_encode_is_reset_Named,
      is_witness_base_def
    ]
  >> metis_tac []
QED

Definition step_encoding_is_unsat_def:
  step_encoding_is_unsat
    waig wnext wcnstrs wpreds wlatches
  ⇔
  (¬∃ss.
     (eval_gate ss
       (encode_is_witness_step
          waig wnext wcnstrs wpreds wlatches)
       (Named (Ext «step»))))
End

Theorem eval_gate_encode_is_witness_step:
  step_encoding_is_unsat
    waig wnext wcnstrs wpreds wlatches
   =
  is_witness_step waig wnext (set wpreds) (set wcnstrs) (set wlatches)
Proof
  simp [
      step_encoding_is_unsat_def,
      encode_is_witness_step_def,
      eval_gate_encode_imply,
      eval_lit_encode_lits_hold_Named,
      eval_lit_encode_equiv_Named,
      encode_is_next_def, encode_is_next_with_def,
      eval_lit_base,
      is_witness_step_def, is_next_def,
      FORALL_STATE_PAIR,
      EVERY_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> metis_tac []
QED

Definition liveness_encoding_is_unsat_def:
  liveness_encoding_is_unsat
    maig mcnstrs mlive
    waig wnext wcnstrs wpreds wlive wlatches interv
  ⇔
  (¬∃ss.
     (eval_gate ss
       (encode_is_witness_liveness
          maig mcnstrs mlive
          waig wnext wcnstrs wpreds wlive wlatches interv)
       (Named (Ext «liveness»))))
End

Theorem eval_gate_encode_is_witness_liveness:
  LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive
  ⇒
  liveness_encoding_is_unsat
    maig mcnstrs mlive
    waig wnext wcnstrs wpreds wlive wlatches interv
  =
  is_witness_liveness
    maig (set mcnstrs) (qleft maig) (qleft_live mlive)
    waig wreset wnext (set wpreds) (set wcnstrs)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof
  strip_tac
  >> qmatch_goalsub_abbrev_tac
       ‘is_witness_liveness _ _ _ mlive' _ _ _ _ _ _ wlive' _’
  >> simp [
      liveness_encoding_is_unsat_def,
      encode_is_witness_liveness_def,
      eval_gate_encode_imply,
      encode_is_next_def, encode_is_next_with_def, is_next_def,
      is_witness_liveness_def, lives_imply_signal_imply_FLAT,
      eval_lit_encode_lits_hold_Named,
      eval_lit_encode_equiv_Named,
      eval_lit_base,
      FORALL_STATE_PAIR,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> sg ‘LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive' wlive'’
  >-
   (fs [Abbr ‘mlive'’, Abbr ‘wlive'’, LIST_REL_EL_EQN,
        qinterv_live_l_r_def, live_map_base_def,
        qinterv_live_def, qleft_live_def, EL_MAP])
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
  >> drule_all_then assume_tac eval_lit_encode_signal_imply_Gate
  >> simp [is_witness_liveness_def, lives_imply_signal_imply_FLAT]
  >> sg ‘LIST_REL (λws ms. LENGTH ws = LENGTH ms) wlive' mlive'’
  >-
   (irule LIST_REL_sym
    >> qpat_x_assum ‘LIST_REL _ mlive' wlive'’ $ irule_at Any
    >> simp [])
  >> simp [Abbr ‘signals’, Abbr ‘signals'’]
  >> metis_tac []
QED

Definition decrease_encoding_is_unsat_def:
  decrease_encoding_is_unsat
    waig wnext wcnstrs wpreds wlive wlatches interv
  ⇔
  (¬∃ss.
     (eval_gate ss
       (encode_is_witness_decrease
          waig wnext wcnstrs wpreds wlive wlatches interv)
       (Named (Ext «decrease»))))
End

Theorem eval_gate_encode_is_witness_decrease:
  decrease_encoding_is_unsat
    waig wnext wcnstrs wpreds wlive wlatches interv
  =
  is_witness_decrease
    waig wnext (set wpreds) (set wcnstrs)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof
  simp [
      decrease_encoding_is_unsat_def,
      encode_is_witness_decrease_def,
      eval_gate_encode_imply,
      eval_lit_encode_lits_hold_Named,
      eval_lit_encode_equiv_Named,
      encode_is_next_def, encode_is_next_with_def,
      eval_lit_base,
      is_witness_decrease_def,
      is_next_def,
      FORALL_STATE_PAIR,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> qmatch_goalsub_abbrev_tac ‘encode_lives_hold _ _ wlive'’
  >> sg ‘EVERY (EVERY (λx. iname x = 0)) wlive'’
  >- (simp [Abbr ‘wlive'’, qinterv_live_r_l_def, qinterv_live_def, MEM_MAP,
            EVERY_MAP])
  >> simp [Req0 eval_lit_encode_lives_hold_Named]
  >> simp [Abbr ‘wlive'’]
  >> simp [lives_hold_r_l_eq]
  >> metis_tac []
QED

Definition closure_encoding_is_unsat_def:
  closure_encoding_is_unsat
    waig wnext wcnstrs wpreds wlive wlatches interv
  ⇔
  (¬∃ss.
     (eval_gate ss
       (encode_is_witness_closure
          waig wnext wcnstrs wpreds wlive wlatches interv)
       (Named (Ext «closure»))))
End

Theorem eval_gate_encode_is_witness_closure:
  closure_encoding_is_unsat
    waig wnext wcnstrs wpreds wlive wlatches interv
   =
  is_witness_closure
    waig wnext (set wpreds) (set wcnstrs)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof
  simp [
      closure_encoding_is_unsat_def,
      encode_is_witness_closure_def,
      eval_gate_encode_imply,
      eval_lit_encode_lits_hold_Named,
      eval_lit_encode_equiv_Named,
      encode_is_next_def, encode_is_next_with_def,
      eval_lit_base,
      is_witness_closure_def, is_next_def,
      FORALL_STATE_PAIR,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> qmatch_goalsub_abbrev_tac ‘encode_lives_hold _ «lives_hold02» wlive₀’
  >> qmatch_goalsub_abbrev_tac ‘encode_lives_hold _ «lives_hold12» wlive₁’
  >> sg ‘EVERY (EVERY (λx. iname x = 0)) wlive₀ ∧
         EVERY (EVERY (λx. iname x = 0)) wlive₁’
  >-
   (simp [Abbr ‘wlive₀’, Abbr ‘wlive₁’, MEM_MAP, EVERY_MAP,
          qinterv_live_ll_r_def, qinterv_live_lr_r_def, qinterv_live_def])
  >> simp [Req0 eval_lit_encode_lives_hold_Named]
  >> simp [Abbr ‘wlive₀’, Abbr ‘wlive₁’]
  >> simp [lives_hold_ll_r_eq, lives_hold_lr_r_eq]
  >> metis_tac []
QED

Definition consistent_encoding_is_unsat_def:
  consistent_encoding_is_unsat
    waig wnext wcnstrs wpreds wlive wlatches interv
  ⇔
  (¬∃ss.
     (eval_gate ss
       (encode_is_witness_consistent
          waig wnext wcnstrs wpreds wlive wlatches interv)
       (Named (Ext «consistent»))))
End

Theorem eval_gate_encode_is_witness_consistent:
  consistent_encoding_is_unsat
    waig wnext wcnstrs wpreds wlive wlatches interv
   =
  is_witness_consistent
    waig wnext (set wpreds) (set wcnstrs)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof
  simp [
      consistent_encoding_is_unsat_def,
      encode_is_witness_consistent_def,
      eval_gate_encode_imply,
      encode_is_next_with_def,
      encode_is_next_def,
      eval_lit_encode_equiv_Named,
      eval_lit_encode_lits_hold_Named,
      eval_lit_base, is_next_def,
      is_witness_consistent_def,
      FORALL_STATE_PAIR,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> qmatch_goalsub_abbrev_tac
     ‘encode_signal_imply _ _ (FLAT wlive₀) (FLAT wlive₁)’
  >> sg ‘LIST_REL (λws ws'. LENGTH ws = LENGTH ws') wlive₀ wlive₁’
  >-
   (unabbrev_all_tac
    >> simp [LIST_REL_EL_EQN, qinterv_live_ll_lr_def, qinterv_live_lr_r_def,
             qinterv_live_def, ileft_name_lits_def, iright_name_lits_def,
             EL_MAP])
  >> sg ‘EVERY (EVERY (λx. iname x = 0)) wlive₀ ∧
         EVERY (EVERY (λx. iname x = 0)) wlive₁’
  >-
   (simp [Abbr ‘wlive₀’, Abbr ‘wlive₁’, EVERY_MEM, MEM_MAP, PULL_EXISTS,
          ileft_name_lits_def, iright_name_lits_def])
  >> qmatch_goalsub_abbrev_tac ‘encode_signal_imply _ _ signals' signals’
  >> sg ‘LENGTH signals' = LENGTH signals’
  >-
   (simp [Abbr ‘signals'’, Abbr ‘signals’, iright_name_lits_def,
          ileft_name_lits_def]
    >> drule LIST_REL_LENGTH_FLAT >> simp [])
  >> sg ‘EVERY (λx. iname x = 0) signals ∧ EVERY (λx. iname x = 0) signals'’
  >-
   (unabbrev_all_tac
    >> simp [EVERY_MEM, MEM_FLAT, MEM_MAP, ileft_name_lits_def,
             iright_name_lits_def, PULL_EXISTS])
  >> simp [Req0 eval_lit_encode_lives_hold_Named]
  >> simp [Req0 eval_lit_encode_signal_imply_Gate]
  >> unabbrev_all_tac
  >> simp [lives_hold_lr_r_eq, lives_imply_signal_imply_FLAT]
  >> qmatch_goalsub_abbrev_tac ‘LIST_REL _ xs _’
  >> sg ‘LIST_REL (λQ Q'. LENGTH Q = LENGTH Q') xs xs’
  >- simp [LIST_REL_EL_EQN]
  >> simp [FLAT_MAP_name_lits_flip, signal_imply_right_lr_r_eq,
           lives_hold_ll_lr_eq, signal_imply_left_ll_lr_eq]
  >> simp [IMP_DISJ_THM]
QED

(** Stratification ************************************************************)

(* Given an AIG and a name, finds the first match, returning its
   input literals and the rest of the AIG. *)
(* To motivate this function, consider the simple AIG
   [(Gate 0, [(Gate 0, F)])]
   Repeatedly applying ALOOKUP to find the dependencies of Gate 0 would lead to
   a loop. In contrast, by using the rest returned by aig_lookup, the second
   invocation of aig_lookup would return NONE, breaking the loop. *)
Definition aig_lookup_def:
  (aig_lookup (h::tl) n =
   let (n', ins) = h in
     if n' = n then SOME (ins,  tl) else aig_lookup tl n) ∧
  aig_lookup [] n = NONE
End

Theorem aig_lookup_LENGTH_lt[local]:
  ∀aig n. aig_lookup aig n = SOME (ins, rest) ⇒ LENGTH rest < LENGTH aig
Proof
  Induct >> rw [aig_lookup_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rename1 ‘if n' = n then _ else _’
  >> Cases_on ‘n' = n’ >> gvs []
  >> last_x_assum drule >> simp []
QED

(* Computes the latches a literal depends on. *)
Definition latch_deps_def:
  (latch_deps (aig: ('a, 'i, 'l) aig) lit =
   let (v, _) = lit in
     case v of
     | Base (Latch l) => [l]
     | Gate a =>
         (case aig_lookup aig a of
          | NONE => []
          | SOME (lits, rest) =>
            FLAT (MAP (latch_deps rest) lits))
     | _ => [])
Termination
  wf_rel_tac ‘measure (LENGTH o FST)’ >> rw []
  >> drule aig_lookup_LENGTH_lt >> simp []
End

Theorem latch_deps_cons_name_neq[local]:
  n' ≠ n ⇒
  latch_deps ((n',ins)::aig) (Gate n,b) = latch_deps aig (Gate n,b)
Proof
  simp [Once latch_deps_def, SimpLHS]
  >> simp [Once latch_deps_def, SimpRHS]
  >> simp [aig_lookup_def]
QED

Theorem MEM_latch_deps_name_eq:
  MEM x ins ∧ MEM l (latch_deps aig x) ⇒
  MEM l (latch_deps ((n,ins)::aig) (Gate n,b))
Proof
  strip_tac
  >> simp [Once latch_deps_def, aig_lookup_def]
  >> simp [MEM_FLAT, MEM_MAP, PULL_EXISTS]
  >> qpat_assum ‘MEM _ (latch_deps _ _)’ $ irule_at Any
  >> simp []
QED

Theorem latch_deps_eval_eq:
  (∀lit.
     (∀l. MEM l (latch_deps aig lit) ⇒ (ls' l ⇔ ls l)) ⇒
     (eval_lit (is,ls') aig lit ⇔ eval_lit (is,ls) aig lit)) ∧
  (∀lit n b.
    (∀l. MEM l (latch_deps aig lit) ⇒ (ls' l ⇔ ls l)) ∧
    lit = (Gate n, b) ⇒
    (eval_gate (is,ls') aig n ⇔ eval_gate (is,ls) aig n))
Proof
  Induct_on ‘aig’ >> rw []
  >~ [‘eval_lit _ [] _ ⇔ _’] >- suspend "eval_lit_nil"
  >~ [‘eval_lit _ (_::_) _ ⇔ _’] >- suspend "eval_lit_cons"
  >~ [‘eval_gate _ (_::_) _ ⇔ _’] >- suspend "eval_gate_cons"
QED

Resume latch_deps_eval_eq[eval_lit_nil]:
  namedCases_on ‘lit’ ["v b"]
  >> reverse $ namedCases_on ‘v’ ["n", "b'"]
  >> simp [eval_lit_def]
  >> Cases_on ‘b'’
  >> fs [eval_lit_def, Once latch_deps_def]
QED

Resume latch_deps_eval_eq[eval_lit_cons]:
  namedCases_on ‘lit’ ["v b"]
  >> reverse $ namedCases_on ‘v’ ["n", "b'"]
  >- (
    Cases_on ‘b'’
    >> simp [eval_lit_def]
    >> fs [eval_lit_def, Once latch_deps_def]
  )
  >> simp [eval_lit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> IF_CASES_TAC >> gvs []
  >- (
    qsuff_tac
      ‘EVERY (λa. eval_lit (is,ls') aig a) ins ⇔
         EVERY (λa. eval_lit (is,ls) aig a) ins’
    >- simp []
    >> irule EVERY_CONG >> rw []
    >> first_x_assum irule >> rw []
    >> first_x_assum irule
    >> drule_all MEM_latch_deps_name_eq >> simp []
  )
  >> qsuff_tac ‘eval_gate (is,ls') aig n ⇔ eval_gate (is,ls) aig n’
  >- simp []
  >> drule_then assume_tac $
       INST_TYPE [“:γ” |-> “:β”, “:β” |-> “:γ”] latch_deps_cons_name_neq
  >> fs []
  >> qpat_x_assum ‘∀_ _. _ ⇒ (eval_gate _ _ _ ⇔ _)’ drule
  >> simp []
QED

Resume latch_deps_eval_eq[eval_gate_cons]:
  simp [eval_lit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> IF_CASES_TAC >> gvs []
  >- (
    irule EVERY_CONG >> rw []
    >> first_x_assum irule >> rw []
    >> first_x_assum irule
    >> drule_all MEM_latch_deps_name_eq >> simp []
  )
  >> first_x_assum irule
  >> qexists ‘b’ >> rw []
  >> first_x_assum irule
  >> drule_then assume_tac $
       INST_TYPE [“:γ” |-> “:β”, “:β” |-> “:γ”] latch_deps_cons_name_neq
  >> simp []
QED

Finalise latch_deps_eval_eq[local]

Theorem latch_deps_eval_lit_eq[local] = cj 1 latch_deps_eval_eq
Theorem latch_deps_eval_gate_eq[local] =
  cj 2 latch_deps_eval_eq
    |> SIMP_RULE (pure_ss ++ UNWIND_ss) []  (* unwinds _ = (_, _)  *)


(* Returns the tuple (latch, latch dependencies), if latch has a defined reset
   function. The tuple can be interpreted as a set of edges from a latch to
   each of the dependencies of its reset function. *)
Definition reset_edges_def:
  reset_edges
    (aig: ('a, 'i, 'l) aig) (reset: 'l -> ('a, 'i, 'l) lit option) latch
  =
  case reset latch of
  | NONE => NONE
  | SOME lit => SOME (latch, latch_deps aig lit)
End

(* Generates the dependency graph for the dependency graph of latches' reset
   functions.
   If this graph is acyclic, we know there exists an order that satisfies
   is_stratified. *)
Definition reset_graph_def:
  reset_graph
    (aig: ('a, 'i, 'l) aig) (reset: 'l -> ('a, 'i, 'l) lit option) latches
  =
  (* TODO Remove list$ once mllist's duplicate mapPartial has been removed *)
  list$mapPartial (reset_edges aig reset) latches
End

(* Constructs the witness for is_stratified from the dependency graph of
   latches' reset functions.
   If the graph is acyclic, the order is irreflexive and thus the reset
   functions are stratified. *)
Definition reset_order_def:
  reset_order
    (aig: ('a, 'i, 'l) aig) (reset: 'l -> ('a, 'i, 'l) lit option) latches
  =
  (* ᵀ gives us R x y ⇔ "x is a dependency of y", as opposed to
     "x depends on y". We use the weak variant of TC_depends_on, since we do not
     want to force all dependencies to also be present as keys; the reset
     function of latch x may depend on some latch y, but y may not have a reset
     function. *)
  (TC_depends_on_weak (reset_graph aig reset latches))ᵀ
End

Theorem transitive_reset_order[local]:
  transitive (reset_order aig reset latches)
Proof
  simp [reset_order_def, TC_depends_on_weak_def]
QED

Theorem irreflexive_reset_order[local]:
  ALL_DISTINCT (MAP FST (reset_graph aig reset latches)) ∧
  ¬has_cycle (reset_graph aig reset latches)
  ⇒
  irreflexive (reset_order aig reset latches)
Proof
  strip_tac
  >> drule_all has_cycle_correct2
  >> simp [irreflexive_def, reset_order_def]
QED

Theorem ALOOKUP_reset_graph_SOME[local]:
  ∀latches.
    MEM lat latches ∧ reset lat = SOME lit ⇒
    ALOOKUP (reset_graph aig reset latches) lat = SOME (latch_deps aig lit)
Proof
  Induct >> rw [reset_graph_def]
  >- simp [mapPartial_def, reset_edges_def]
  >> simp [reset_edges_def]
  >> CASE_TAC >> fs [reset_graph_def]
  >> IF_CASES_TAC >> fs []
QED

Theorem latch_deps_reset_order[local]:
  MEM lat latches ∧
  reset lat = SOME lit ∧
  MEM l (latch_deps aig lit)
  ⇒
  reset_order aig reset latches l lat
Proof
  rw [reset_order_def, TC_depends_on_weak_def]
  >> irule TC_SUBSET >> simp []
  >> irule_at Any ALOOKUP_reset_graph_SOME
  >> qexists ‘lit’ >> simp []
QED

Theorem dep_reset_lt_reset_order[local]:
  dep_reset_lt (reset_order aig reset latches) aig reset (set latches)
Proof
  rw [dep_reset_lt_def]
  >> irule latch_deps_eval_lit_eq
  >> rpt strip_tac
  >> first_x_assum irule
  >> drule_all latch_deps_reset_order
  >> simp []
QED

Definition stratified_cond_def:
  stratified_cond aig reset latches =
  let g = reset_graph aig reset latches in
    ALL_DISTINCT (MAP FST g) ∧ ¬has_cycle g
End

Theorem stratified_cond_is_stratified:
  stratified_cond aig reset latches
  ⇒
  ∃lt. is_stratified lt aig reset (set latches)
Proof
  rw [stratified_cond_def]
  >> qexists ‘reset_order aig reset latches’
  >> simp [is_stratified_def, transitive_reset_order,
           irreflexive_reset_order, dep_reset_lt_reset_order]
QED

(** Top-level theorems ********************************************************)

Definition encodings_unsat_def:
  encodings_unsat
    maig mreset mnext mpreds mcnstrs mlive mlatches
    waig wreset wnext wpreds wcnstrs wlive wlatches
    interv klatches
  ⇔
    (reset_encoding_is_unsat
       maig mreset mcnstrs mlatches
       waig wreset wcnstrs wlatches klatches) ∧
    (transition_encoding_is_unsat
       maig mnext mcnstrs mlatches
       waig wnext wcnstrs wlatches klatches) ∧
    (property_encoding_is_unsat
       maig mcnstrs mpreds
       waig wcnstrs wpreds) ∧
    (base_encoding_is_unsat
       waig wreset wcnstrs wpreds wlatches) ∧
    (step_encoding_is_unsat
       waig wnext wcnstrs wpreds wlatches) ∧
    (liveness_encoding_is_unsat
       maig mcnstrs mlive
       waig wnext wcnstrs wpreds wlive wlatches interv) ∧
    (decrease_encoding_is_unsat
       waig wnext wcnstrs wpreds wlive wlatches interv) ∧
    (closure_encoding_is_unsat
       waig wnext wcnstrs wpreds wlive wlatches interv) ∧
    (consistent_encoding_is_unsat
       waig wnext wcnstrs wpreds wlive wlatches interv)
End

(** dep_model *****************************************************************)

(* dep_aig *)

Definition dep_cond_def:
  dep_cond aig reset next preds cnstrs live latches ⇔
    set (aig_latches aig) ⊆ set latches ∧
    BIGUNION (IMAGE (set ∘ lit_latches ∘ next) (set latches)) ⊆ set latches ∧
    BIGUNION (IMAGE (set ∘ lit_latches) (set preds)) ⊆ set latches ∧
    BIGUNION (IMAGE (set ∘ lit_latches) (set cnstrs)) ⊆ set latches ∧
    BIGUNION
      (IMAGE (set ∘ lit_latches) (IMAGE_PARTIAL reset (set latches))) ⊆
      set latches ∧
    BIGUNION (IMAGE (set ∘ lit_latches) (set (FLAT live))) ⊆ set latches
End

Theorem dep_lits_pair_map_lit_map_base_inl:
  ∀live.
    dep_lits (pair_set inputs) (pair_set latches)
     (set ((MAP (lit_map_base INL INL)) live))
    ⇔
    dep_lits inputs latches (set live)
Proof
  Induct
  >- simp [dep_lits_def]
  >> rw []
  >> once_rewrite_tac [dep_lits_INSERT]
  >> simp []
  >> rename1 ‘lit_map_base INL INL h’
  >> qsuff_tac
     ‘dep_lits (pair_set inputs) (pair_set latches) {lit_map_base INL INL h} ⇔
        dep_lits inputs latches {h}’
  >- simp []
  >> namedCases_on ‘h’ ["v b"]
  >> Cases_on ‘v’
  >- simp [lit_map_base_def, var_map_base_def, dep_lits_def]
  >> rename1 ‘Base b'’
  >> Cases_on ‘b'’
  >> simp [lit_map_base_def, var_map_base_def, dep_lits_def, bvar_map_def,
           pair_set_def]
QED

Theorem dep_lits_pair_qleft_live:
  dep_lits (pair_set inputs) (pair_set latches) (set (FLAT (qleft_live mlive)))
  ⇔
  dep_lits inputs latches (set (FLAT mlive))
Proof
  simp [qleft_live_def, live_map_base_def, GSYM MAP_FLAT]
  >> simp [dep_lits_pair_map_lit_map_base_inl]
QED

Theorem encoding_is_safe_and_live:
  LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive ∧
  set klatches = set mlatches ∩ set wlatches ∧
  stratified_cond waig wreset wlatches ∧
  dep_cond maig mreset mnext mpreds mcnstrs mlive mlatches ∧
  encodings_unsat
    maig mreset mnext mpreds mcnstrs mlive mlatches
    waig wreset wnext wpreds wcnstrs wlive wlatches
    interv klatches
  ⇒
  is_safe
    maig mreset mnext (set mcnstrs) (set mlatches) (set mpreds) ∧
  is_live
    maig mreset mnext (set mcnstrs) (qleft maig) (qleft_live mlive)
    (set mlatches)
Proof
  strip_tac
  >> sg
       ‘is_witness
          maig mreset mnext (set mpreds) (set mcnstrs)
          (qleft maig) (qleft_live mlive) (set mlatches)
          waig wreset wnext (set wpreds) (set wcnstrs)
          (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive)
          (set wlatches)’
  >- (
    rewrite_tac [is_witness_def]
    >> MAP_EVERY (irule_at Any o iffLR) [
         eval_gate_encode_is_witness_reset,
         eval_gate_encode_is_witness_transition,
         eval_gate_encode_is_witness_property,
         eval_gate_encode_is_witness_base,
         eval_gate_encode_is_witness_step,
         eval_gate_encode_is_witness_liveness,
         eval_gate_encode_is_witness_decrease,
         eval_gate_encode_is_witness_closure,
         eval_gate_encode_is_witness_consistent,
       ]
    >> qexistsl [‘klatches’, ‘klatches’]
    >> fs [encodings_unsat_def]
  )
  >> sg
     ‘∃minput.
        dep_model maig mreset mnext (set mpreds) (set mcnstrs) minput
          (set mlatches) ∧
        dep_qaig minput (qleft maig) (qleft_live mlive) (set mlatches)’
  >- (
    qabbrev_tac
      ‘minput =
         set (aig_inputs maig) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs ∘ mnext) (set mlatches)) ∪
         BIGUNION
           (IMAGE (set ∘ lit_inputs) (IMAGE_PARTIAL mreset (set mlatches))) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs) (set mpreds)) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs) (set mcnstrs)) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs) (set (FLAT mlive)))’
    >> qexists ‘minput’
    >> rewrite_tac [dep_model_def, dep_qaig_def, GSYM CONJ_ASSOC]
    >> simp [dep_aig_pair_qleft, dep_lits_pair_qleft_live]
    >> fs [dep_cond_def]
    >> sg ‘dep_aig minput (set mlatches) maig’
    >- (
      irule dep_aig_subset
      >> irule_at Any dep_aig_inputs_latches
      >> simp [SUBSET_DEF, Abbr ‘minput’]
    )
    >> sg ‘dep_reset minput (set mlatches) mreset (set mlatches)’
    >- (irule dep_reset_subset >> simp [SUBSET_DEF, Abbr ‘minput’])
    >> sg ‘dep_latch_lit minput (set mlatches) mnext (set mlatches)’
    >- (irule dep_latch_lit_next >> simp [SUBSET_DEF, Abbr ‘minput’])
    >> simp []
    (* only conjuncts of dep_lits ... should remain *)
    >> rpt conj_tac
    >> irule dep_lits_lits
    >> simp [SUBSET_DEF, Abbr ‘minput’]
  )
  >> drule_all stratified_cond_is_stratified >> strip_tac
  >> drule_all_then assume_tac is_witness_is_safe
  >> drule_all_then assume_tac is_witness_is_live
  >> simp []
QED

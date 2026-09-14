(*
  Encodes the certificate conditions as an AIG.
*)
Theory xaig_cert_encode
Ancestors
  aig aig_cert xaig
  (* TODO maybe should move; is for stratification *)
  topological_sort
Libs
  preamble

(* todo check which theorems/simps are actually used *)
(* todo check whether it is possible to reduce the amount of
   definitions/theorems *)
(* todo can we clean up/reduce duplication (e.g. mapping over datatypes) *)

(* todo once this version works, we could simplify aig to be over two inputs *)

(* todo are the wrappers like iright_name_lits really useful,
   or could things be simplified by removing them *)

(* todo left_name -> left_merge; left_lit -> left_pair? *)

(* todo instead of aig -> xaig in each condition, we should make a new predicate
     that says the xaig is equivalent to original aig; can probably
     delete the aig_to_xaig specific thms from the proofs in that case *)

(* todo the names are inconsistent;
   - aig/xaig
   - x-prefix (e.g. we have encode_is_reset instead of encode_xis_reset)
   - xeval_gate_encode_base_cond <- those theorems dont mention eval_gate directly anymore
 *)

(* xaig extensions ************************************************************)

(* todo move to xaigScript.sml *)

Definition dep_xaig_def:
  dep_xaig inputs latches aig =
  ∀n ss' ss.
    agree_on inputs latches ss' ss
    ⇒
    xeval_gate ss' aig n = xeval_gate ss aig n
End

Theorem xeval_aig_to_xaig[local]:
  (xeval_lit ss (aig_to_xaig aig) lit ⇔ eval_lit ss aig lit) ∧
  (xeval_gate ss (aig_to_xaig aig) gs ⇔ eval_gate ss aig gs)
Proof
  simp [aig_to_xaig_sound]
QED

Theorem xeval_gate_nil[simp]:
  ¬xeval_gate ss [] n
Proof
  simp [xeval_lit_def]
QED

Definition xis_reset_def:
  xis_reset ss (xaig: ('a, 'i, 'l) xaig)
    (reset: 'l -> ('a,'i,'l) lit option) (latches: 'l set) =
  ∀l lit.
    l ∈ latches ∧ reset l = SOME lit ⇒
    xeval_lit ss xaig (Base (Latch l), F) =
    xeval_lit ss xaig lit
End

Theorem xis_reset_eq:
  xis_reset ss (aig_to_xaig aig) reset latches ⇔
  is_reset ss aig reset latches
Proof
  simp [xis_reset_def, is_reset_def, xeval_aig_to_xaig]
QED

Definition xlits_hold_def:
  xlits_hold ss (xaig: ('a, 'i, 'l) xaig) (lits: ('a,'i,'l) lit set) ⇔
    ∀lit. lit ∈ lits ⇒ xeval_lit ss xaig lit
End

Theorem xlits_hold_eq:
  xlits_hold ss (aig_to_xaig aig) lits ⇔ lits_hold ss aig lits
Proof
  simp [xlits_hold_def, lits_hold_def, xeval_aig_to_xaig]
QED

Definition xsignal_imply_def:
  xsignal_imply ss aig ss' aig' signals signals' =
    LIST_REL (λq q'. xlits_hold ss aig {q} ⇒ xlits_hold ss' aig' {q'})
      signals signals'
End

(* General ********************************************************************)

Theorem eval_lit_latch:
  eval_lit ss aig (Base (Latch l), b) ⇔ (b ⇎ SND ss l)
Proof
  Cases_on ‘ss’ >> simp [eval_lit_def]
QED

Theorem xeval_lit_latch:
  xeval_lit ss aig (Base (Latch l), b) ⇔ (b ⇎ SND ss l)
Proof
  Cases_on ‘ss’ >> simp [xeval_lit_def]
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

Definition left_name_gty_def:
  left_name_gty (And xs) = And (MAP left_name_lit xs) ∧
  left_name_gty (Xor x₀ x₁) = Xor (left_name_lit x₀) (left_name_lit x₁) ∧
  left_name_gty (Ite cnd thn els) =
    Ite (left_name_lit cnd) (left_name_lit thn) (left_name_lit els) ∧
  left_name_gty (Or xs) = Or (MAP left_name_lit xs)
End

Definition left_name_gate_def:
  left_name_gate (n, ins) = (INL n, left_name_gty ins)
End

Definition right_name_var_def:
  (right_name_var (Gate a)  = Gate (INR a)) ∧
  (right_name_var (Base bv) = Base bv)
End

Definition right_name_lit_def:
  right_name_lit (v, b) = (right_name_var v, b)
End

Definition right_name_gty_def:
  right_name_gty (And xs) = And (MAP right_name_lit xs) ∧
  right_name_gty (Xor x₀ x₁) = Xor (right_name_lit x₀) (right_name_lit x₁) ∧
  right_name_gty (Ite cnd thn els) =
    Ite (right_name_lit cnd) (right_name_lit thn) (right_name_lit els) ∧
  right_name_gty (Or xs) = Or (MAP right_name_lit xs)
End

Definition right_name_gate_def:
  right_name_gate (n, ins) = (INR n, right_name_gty ins)
End

Definition merge_aigs_def:
  merge_aigs (xaig₁: ('a1, 'i, 'l) xaig) (xaig₂: ('a2, 'i, 'l) xaig) =
    (MAP left_name_gate xaig₁ ++ MAP right_name_gate xaig₂)
    :('a1 + 'a2, 'i, 'l) xaig
End

Theorem merge_aigs_left_cons:
  merge_aigs (a::aig₁) aig₂ =
  left_name_gate a::(merge_aigs aig₁) aig₂
Proof
  simp [merge_aigs_def]
QED

Theorem merge_aigs_left_nil_right_cons:
  merge_aigs [] (a::aig) =
  right_name_gate a::(merge_aigs [] aig)
Proof
  simp [merge_aigs_def]
QED

Theorem xeval_gate_merge_aigs_left_nil_INL[local]:
  ¬xeval_gate ss (merge_aigs [] aig) (INL n)
Proof
  Induct_on ‘aig’ >> rw [merge_aigs_def, xeval_lit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rename1 ‘right_name_gate a’
  >> Cases_on ‘a’ >> gvs [right_name_gate_def, merge_aigs_def]
QED

Theorem xeval_lit_merge_aigs_left_nil_left[local]:
  xeval_lit ss (merge_aigs [] aig) (left_name_lit m) ⇔
  xeval_lit ss [] m
Proof
  Induct_on ‘aig’
  >> Cases_on ‘m’ >> fs [left_name_lit_def]
  >> rename1 ‘left_name_var x’ >> Cases_on ‘x’ >> fs [left_name_var_def]
  >> fs [merge_aigs_def, xeval_lit_def]
  >> Cases >> simp [right_name_gate_def]
QED

Theorem xeval_gate_merge_aigs_left_nil_INR[local]:
  (∀n.
     xeval_gate ss (merge_aigs ([]: ('a, 'i, 'l) xaig) aig) (INR n) =
     xeval_gate ss aig n) ∧
  (∀m.
     xeval_lit ss (merge_aigs ([]: ('a, 'i, 'l) xaig) aig) (right_name_lit m) =
     xeval_lit ss aig m)
Proof
  Induct_on ‘aig’ >> rw []
  >- simp [merge_aigs_def]
  >-
   (simp [merge_aigs_def]
    >> Cases_on ‘m’ >> simp [right_name_lit_def]
    >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
    >> simp [xeval_lit_def])
  >> simp [merge_aigs_left_nil_right_cons]
  >-
   (simp [xeval_lit_def]
    >> rename1 ‘right_name_gate h’ >> Cases_on ‘h’ >> simp [right_name_gate_def]
    >> IF_CASES_TAC >> gvs []
    >> rename1 ‘right_name_gty r’ >> Cases_on ‘r’ >> simp [right_name_gty_def]
    >> gvs [EVERY_MAP, EXISTS_MAP])
  >> Cases_on ‘m’ >> simp [right_name_lit_def]
  >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
  >> simp [xeval_lit_def]
  >> rename1 ‘right_name_gate h’ >> Cases_on ‘h’ >> simp [right_name_gate_def]
  >> IF_CASES_TAC >> gvs []
  >> rename1 ‘right_name_gty r'’ >> Cases_on ‘r'’ >> simp [right_name_gty_def]
  >> gvs [EVERY_MAP, EXISTS_MAP]
QED

Theorem xeval_gate_merge_aigs_left[simp]:
  (∀n.
     xeval_gate ss (merge_aigs aig₁ aig₂) (INL n) =
     xeval_gate ss aig₁ n) ∧
  (∀m.
     xeval_lit ss (merge_aigs aig₁ aig₂) (left_name_lit m) =
     xeval_lit ss aig₁ m)
Proof
  Induct_on ‘aig₁’ >> rw []
  >- simp [xeval_gate_merge_aigs_left_nil_INL]
  >- simp [xeval_lit_merge_aigs_left_nil_left]
  >> simp [merge_aigs_left_cons]
  >-
   (simp [xeval_lit_def]
    >> rename1 ‘left_name_gate a’ >> Cases_on ‘a’ >> simp [left_name_gate_def]
    >> IF_CASES_TAC >> gvs []
    >> rename1 ‘left_name_gty r’ >> Cases_on ‘r’ >> simp [left_name_gty_def]
    >> gvs [EVERY_MAP, EXISTS_MAP])
  >> rename1 ‘left_name_lit m’ >> Cases_on ‘m’ >> simp [left_name_lit_def]
  >> rename1 ‘left_name_var v’ >> Cases_on ‘v’ >> simp [left_name_var_def]
  >> simp [xeval_lit_def]
  >> rename1 ‘left_name_gate b’ >> Cases_on ‘b’ >> simp [left_name_gate_def]
  >> IF_CASES_TAC >> gvs []
  >> rename1 ‘left_name_gty r'’ >> Cases_on ‘r'’ >> simp [left_name_gty_def]
  >> gvs [EVERY_MAP, EXISTS_MAP]
QED

Theorem xeval_gate_merge_aigs_right[simp]:
  (∀n.
     xeval_gate ss (merge_aigs aig₁ aig₂) (INR n) =
     xeval_gate ss aig₂ n) ∧
  (∀m.
     xeval_lit ss (merge_aigs aig₁ aig₂) (right_name_lit m) =
     xeval_lit ss aig₂ m)
Proof
  Induct_on ‘aig₁’ >> rw []
  >- simp [xeval_gate_merge_aigs_left_nil_INR]
  >- simp [xeval_gate_merge_aigs_left_nil_INR]
  >> simp [merge_aigs_left_cons]
  >-
   (rename1 ‘left_name_gate a’ >> Cases_on ‘a’ >> simp [left_name_gate_def]
    >> simp [xeval_lit_def])
  >> Cases_on ‘m’ >> simp [right_name_lit_def]
  >> rename1 ‘right_name_var v’ >> Cases_on ‘v’ >> simp [right_name_var_def]
  >> rename1 ‘left_name_gate h’ >> Cases_on ‘h’ >> simp [left_name_gate_def]
  >> simp [xeval_lit_def]
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

Definition left_gty_def:
  left_gty (And xs) = And (MAP left_lit xs) ∧
  left_gty (Xor x₀ x₁) = Xor (left_lit x₀) (left_lit x₁) ∧
  left_gty (Ite cnd thn els) =
    Ite (left_lit cnd) (left_lit thn) (left_lit els) ∧
  left_gty (Or xs) = Or (MAP left_lit xs)
End

Definition left_gate_def:
  left_gate (n, ins) = (INL n, left_gty ins)
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

Definition right_gty_def:
  right_gty (And xs) = And (MAP right_lit xs) ∧
  right_gty (Xor x₀ x₁) = Xor (right_lit x₀) (right_lit x₁) ∧
  right_gty (Ite cnd thn els) =
    Ite (right_lit cnd) (right_lit thn) (right_lit els) ∧
  right_gty (Or xs) = Or (MAP right_lit xs)
End

Definition right_gate_def:
  right_gate (n, ins) = (INR n, right_gty ins)
End

Definition pair_aigs_def:
  pair_aigs (xaig₁: ('a1, 'i1, 'l1) xaig)
    (xaig₂: ('a2, 'i2, 'l2) xaig) =
  MAP left_gate xaig₁ ++ MAP right_gate xaig₂
End

Theorem pair_aigs_left_cons:
  pair_aigs (a::aig₁) aig₂ =
  left_gate a::(pair_aigs aig₁ aig₂)
Proof
  simp [pair_aigs_def]
QED

Theorem pair_aigs_left_nil_right_cons:
  pair_aigs [] (a::aig₂) =
  right_gate a::(pair_aigs [] aig₂)
Proof
  simp [pair_aigs_def]
QED

Theorem xeval_gate_pair_left_nil_INL[local]:
  ¬xeval_gate ss (pair_aigs [] aig) (INL n)
Proof
  Induct_on ‘aig’ >> rw []
  >> gvs [pair_aigs_def, xeval_lit_def]
  >> rename1 ‘right_gate a’ >> Cases_on ‘a’
  >> simp [right_gate_def]
QED

Theorem xeval_gate_pair_left_nil_INR[local]:
  (∀n.
     xeval_gate (state_pair ss₁ ss₂)
       (pair_aigs ([]: ('a, 'i, 'l) xaig) aig) (INR n) =
     xeval_gate ss₂ aig n) ∧
  (∀m.
     xeval_lit (state_pair ss₁ ss₂)
       (pair_aigs ([]: ('a, 'i, 'l) xaig) aig) (right_lit m) =
     xeval_lit ss₂ aig m)
Proof
  Induct_on ‘aig’ >> rw []
  >- simp [pair_aigs_def, xeval_lit_def]
  >-
   (Cases_on ‘m’ >> simp [pair_aigs_def, right_lit_def]
    >> rename1 ‘right_var x’ >> Cases_on ‘x’
    >> simp [right_var_def, xeval_lit_def]
    >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [state_pair_def]
    >> rename1 ‘right_bvar b’ >> Cases_on ‘b’
    >> simp [right_bvar_def, eval_bvar_def])
  >> simp [pair_aigs_left_nil_right_cons]
  >-
   (rename1 ‘right_gate a’ >> Cases_on ‘a’
    >> simp [right_gate_def, xeval_lit_def]
    >> IF_CASES_TAC >> gvs []
    >> rename1 ‘right_gty r’ >> Cases_on ‘r’
    >> gvs [right_gty_def, EVERY_MAP, EXISTS_MAP])
  >> rename1 ‘right_lit m’ >> Cases_on ‘m’
  >> simp [right_lit_def]
  >> rename1 ‘right_var x’ >> Cases_on ‘x’
  >> simp [right_var_def, xeval_lit_def]
  >-
   (rename1 ‘right_gate y’ >> Cases_on ‘y’
    >> simp [right_gate_def]
    >> IF_CASES_TAC >> gvs []
    >> rename1 ‘right_gty r'’ >> Cases_on ‘r'’
    >> gvs [right_gty_def, EVERY_MAP, EXISTS_MAP])
  >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [state_pair_def]
  >> rename1 ‘right_bvar b’ >> Cases_on ‘b’
  >> simp [right_bvar_def, eval_bvar_def]
QED

Theorem xeval_lit_pair_left_nil_left[local]:
  xeval_lit (state_pair ss₁ ss₂) (pair_aigs [] aig₂) (left_lit n) =
  xeval_lit ss₁ [] n
Proof
  Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [state_pair_def]
  >> Induct_on ‘aig₂’ >> gvs [pair_aigs_def]
  >> Cases_on ‘n’ >> gvs [left_lit_def]
  >-
   (rename1 ‘left_var v’ >> Cases_on ‘v’
    >> simp [left_var_def, xeval_lit_def]
    >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
    >> simp [left_bvar_def, eval_bvar_def])
  >> Cases >> simp [right_gate_def]
  >> rename1 ‘left_var v’ >> Cases_on ‘v’
  >> gvs [left_var_def, xeval_lit_def]
  >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
  >> simp [left_bvar_def, eval_bvar_def]
QED

Theorem xeval_pair_left[simp]:
  (∀n.
     xeval_gate (state_pair ss₁ ss₂) (pair_aigs aig₁ aig₂) (INL n) =
     xeval_gate ss₁ aig₁ n) ∧
  (∀m.
     xeval_lit (state_pair ss₁ ss₂) (pair_aigs aig₁ aig₂) (left_lit m) =
     xeval_lit ss₁ aig₁ m)
Proof
  Induct_on ‘aig₁’ >> rw [xeval_lit_def]
  >- simp [xeval_gate_pair_left_nil_INL]
  >- simp [xeval_lit_pair_left_nil_left]
  >> simp [pair_aigs_left_cons]
  >-
   (simp [xeval_lit_def]
    >> rename1 ‘left_gate a’ >> Cases_on ‘a’
    >> simp [left_gate_def]
    >> IF_CASES_TAC >> gvs []
    >> rename1 ‘left_gty r’ >> Cases_on ‘r’
    >> gvs [left_gty_def, EVERY_MAP, EXISTS_MAP]
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> rename1 ‘left_lit m’ >> Cases_on ‘m’
  >> simp [left_lit_def]
  >> rename1 ‘left_var v’ >> Cases_on ‘v’
  >> simp [xeval_lit_def, left_var_def]
  >-
   (rename1 ‘left_gate b’ >> Cases_on ‘b’
    >> simp [xeval_lit_def, left_gate_def]
    >> IF_CASES_TAC >> gvs []
    >> rename1 ‘left_gty r'’ >> Cases_on ‘r'’
    >> gvs [left_gty_def, EVERY_MAP, EXISTS_MAP]
    >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
  >> Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> gvs [state_pair_def]
  >> rename1 ‘left_bvar b’ >> Cases_on ‘b’
  >> simp [left_bvar_def, eval_bvar_def]
QED

Theorem xeval_pair_right[simp]:
  (∀n.
    xeval_gate (state_pair ss₁ ss₂) (pair_aigs aig₁ aig₂) (INR n) =
    xeval_gate ss₂ aig₂ n) ∧
  (∀m.
    xeval_lit (state_pair ss₁ ss₂) (pair_aigs aig₁ aig₂) (right_lit m) =
    xeval_lit ss₂ aig₂ m)
Proof
  Induct_on ‘aig₁’ >> rw [xeval_lit_def]
  >- simp [xeval_gate_pair_left_nil_INR]
  >- simp [xeval_gate_pair_left_nil_INR]
  >> simp [pair_aigs_left_cons]
  >-
   (rename1 ‘left_gate a’ >> Cases_on ‘a’
    >> simp [left_gate_def, xeval_lit_def])
  >> rename1 ‘right_lit m’ >> Cases_on ‘m’
  >> simp [right_lit_def]
  >> rename1 ‘right_var x’ >> Cases_on ‘x’
  >> simp [xeval_lit_def, right_var_def]
  >-
   (rename1 ‘left_gate g’ >> Cases_on ‘g’
    >> simp [left_gate_def, xeval_lit_def])
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
   these are flipped, and in the presence of three states (as in stable),
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

Definition gty_map_base_def:
  gty_map_base f g (And xs) =
    And (MAP (lit_map_base f g) xs) ∧
  gty_map_base f g (Xor x₀ x₁) =
    Xor (lit_map_base f g x₀) (lit_map_base f g x₁) ∧
  gty_map_base f g (Ite cnd thn els) =
    Ite (lit_map_base f g cnd) (lit_map_base f g thn) (lit_map_base f g els) ∧
  gty_map_base f g (Or xs) =
    Or (MAP (lit_map_base f g) xs)
End

Definition gate_map_base_def:
  gate_map_base f g (n, gty) = (n, gty_map_base f g gty)
End

Definition aig_map_base_def:
  aig_map_base f g (aig: ('a, 'i, 'l) aig) =
    MAP (and_map_base f g) aig
End

Definition xaig_map_base_def:
  xaig_map_base f g (aig: ('a, 'i, 'l) xaig) =
    MAP (gate_map_base f g) aig
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

Definition xqinterv_gty_def:
  xqinterv_gty f g h interv (And xs) =
    And (MAP (qinterv_lit f g h interv) xs) ∧
  xqinterv_gty f g h interv (Xor x₀ x₁) =
    Xor (qinterv_lit f g h interv x₀) (qinterv_lit f g h interv x₁) ∧
  xqinterv_gty f g h interv (Ite cnd thn els) =
    Ite
      (qinterv_lit f g h interv cnd)
      (qinterv_lit f g h interv thn)
      (qinterv_lit f g h interv els) ∧
  xqinterv_gty f g h interv (Or xs) =
    Or (MAP (qinterv_lit f g h interv) xs)
End

Definition xqinterv_gate_def:
  xqinterv_gate f g h interv ((n, gty): ('a, 'i, 'l) gate) =
    (n, xqinterv_gty f g h interv gty)
End

Definition qinterv_live_def:
  qinterv_live f g h interv (live: ('a, 'i, 'l) lit list list) =
    MAP (MAP (qinterv_lit f g h interv)) live
End

Definition xqinterv_def:
  xqinterv f g h interv (xaig: ('a, 'i, 'l) xaig) =
    MAP (xqinterv_gate f g h interv) xaig
End

Definition qinterv_def:
  qinterv f g h interv (aig: ('a, 'i, 'l) aig) =
    MAP (qinterv_and f g h interv) aig
End

(** Specialized versions of the functions above. ******************************)

Definition xqleft_def:
  xqleft (xaig: ('a, 'i, 'l) xaig) = xaig_map_base INL INL xaig
End

Theorem xqleft_cons:
  xqleft (g::aig) = gate_map_base INL INL g::xqleft aig
Proof
  simp [xqleft_def, xaig_map_base_def]
QED

Theorem xeval_gate_pair_xqleft:
  ∀xaig.
    (∀n.
       xeval_gate (state_pair s₁ s₂) (xqleft xaig) n ⇔
       xeval_gate s₁ xaig n) ∧
    (∀lit.
       xeval_lit (state_pair s₁ s₂) (xqleft xaig) (lit_map_base INL INL lit) ⇔
       xeval_lit s₁ xaig lit)
Proof
  Induct >> rw []
  >- simp [xqleft_def, xaig_map_base_def]
  >- (
    simp [xqleft_def, xaig_map_base_def]
    >> Cases_on ‘lit’
    >> rename1 ‘lit_map_base _ _ (v, _)’ >> Cases_on ‘v’
    >> simp [lit_map_base_def, var_map_base_def, xeval_lit_def]
    >> rename1 ‘bvar_map _ _ b’ >> Cases_on ‘b’
    >> simp [bvar_map_def, xeval_lit_def]
    >> Cases_on ‘s₁’ >> Cases_on ‘s₂’ >> simp [state_pair_def, eval_bvar_def]
  )
  >- (
    simp [xeval_lit_def, xqleft_cons]
    >> rw [] >> rpt (pairarg_tac >> gvs [])
    >> gvs [gate_map_base_def]
    >> IF_CASES_TAC >> gvs []
    >> rename1 ‘gty_map_base _ _ gt'’ >> Cases_on ‘gt'’
    >> simp [gty_map_base_def, EVERY_MAP, EXISTS_MAP]
  )
  >> Cases_on ‘lit’
  >> rename1 ‘lit_map_base _ _ (v, _)’ >> Cases_on ‘v’
  >> simp [lit_map_base_def, var_map_base_def, xeval_lit_def]
  >> qmatch_goalsub_abbrev_tac ‘(r ⇔ X) ⇔ (r ⇔ Y)’
  >> qsuff_tac ‘X ⇔ Y’ >- simp []
  >> simp [Abbr ‘X’, Abbr ‘Y’]
  >- (
    simp [xqleft_cons, xeval_lit_def]
    >> rpt (pairarg_tac >> gvs [])
    >> IF_CASES_TAC >> gvs []
    >> gvs [gate_map_base_def]
    >> rename1 ‘gty_map_base _ _ gt'’ >> Cases_on ‘gt'’
    >> simp [gty_map_base_def, EVERY_MAP, EXISTS_MAP])
  >> rename1 ‘bvar_map _ _ b’ >> Cases_on ‘b’
  >> simp [bvar_map_def, xeval_lit_def]
  >> Cases_on ‘s₁’ >> Cases_on ‘s₂’ >> simp [state_pair_def, eval_bvar_def]
QED

Theorem dep_xaig_pair_xqleft:
  dep_xaig (pair_set minput) (pair_set (set mlatches)) (xqleft mxaig) =
  dep_xaig minput (set mlatches) mxaig
Proof
  simp [dep_xaig_def, FORALL_STATE_PAIR, agree_on_pair,
        xeval_gate_pair_xqleft]
  >> metis_tac []
QED

Definition xqleft_live_def:
  xqleft_live (live: ('a, 'i, 'l) lit list list) = live_map_base INL INL live
End

Definition qleft_def:
  qleft (aig: ('a, 'i, 'l) aig) = aig_map_base INL INL aig
End

Definition qleft_live_def:
  qleft_live (live: ('a, 'i, 'l) lit list list) = live_map_base INL INL live
End

Definition qinterv_l_r_def:
  qinterv_l_r interv (aig: ('a, 'i, 'l) aig) =
    qinterv INL INL INR interv aig
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

Definition xqinterv_l_r_def:
  xqinterv_l_r interv (xaig: ('a, 'i, 'l) xaig) =
    xqinterv INL INL INR interv xaig
End

Definition xqinterv_r_l_def:
  xqinterv_r_l interv (xaig: ('a, 'i, 'l) xaig) =
    xqinterv INR INR INL interv xaig
End

Definition xqinterv_ll_r_def:
  xqinterv_ll_r interv (xaig: ('a, 'i, 'l) xaig) =
    xqinterv (INL ∘ INL) (INL ∘ INL) INR interv xaig
End

Definition xqinterv_ll_lr_def:
  xqinterv_ll_lr interv (xaig: ('a, 'i, 'l) xaig) =
    xqinterv (INL ∘ INL) (INL ∘ INL) (INL ∘ INR) interv xaig
End

Definition xqinterv_lr_r_def:
  xqinterv_lr_r interv (xaig: ('a, 'i, 'l) xaig) =
    xqinterv (INL ∘ INR) (INL ∘ INR) INR interv xaig
End

(* Extending an xAIG **********************************************************)

Datatype:
  ext = Orig 'a | Ext mlstring | Anon num
End

(* Lifting to gate names to ext *)

Definition ext_var_def:
  (ext_var (Gate a) = Gate (Orig a)) ∧
  (ext_var (Base bv) = Base bv)
End

Definition ext_lit_def:
  ext_lit (v, b) = (ext_var v, b)
End

Definition ext_gty_def:
  ext_gty (And xs) = And (MAP ext_lit xs) ∧
  ext_gty (Xor x₀ x₁) = Xor (ext_lit x₀) (ext_lit x₁) ∧
  ext_gty (Ite cnd thn els) = Ite (ext_lit cnd) (ext_lit thn) (ext_lit els) ∧
  ext_gty (Or xs) = Or (MAP ext_lit xs)
End

Definition ext_gate_def:
  ext_gate ((n, gty): (('a,'i,'l) gate)) = (Orig n, ext_gty gty)
End

Definition ext_xaig_def:
  ext_xaig (xaig: ('a, 'i, 'l) xaig) = MAP ext_gate xaig
End

Theorem xeval_lit_Ext_ext_lit[simp]:
  xeval_lit ss ((Ext name,lits)::aig) (ext_lit x) ⇔
  xeval_lit ss aig (ext_lit x)
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [ext_lit_def, ext_var_def, xeval_lit_def]
QED

Theorem xeval_lit_Anon_ext_lit[simp]:
  xeval_lit ss ((Anon n,lits)::aig) (ext_lit x) ⇔
  xeval_lit ss aig (ext_lit x)
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [ext_lit_def, ext_var_def, xeval_lit_def]
QED

Theorem xeval_gate_ext_aig[simp]:
  (∀n. xeval_gate ss (ext_xaig aig) (Orig n) = xeval_gate ss aig n) ∧
  (∀l. xeval_lit  ss (ext_xaig aig) (ext_lit l) = xeval_lit ss aig l) ∧
  (∀l. xeval_lit  ss (ext_xaig aig) (Base bv, b) = xeval_lit ss aig (Base bv, b))
Proof
  Induct_on ‘aig’ >> rw [ext_xaig_def, xeval_lit_def]
  >-
   (Cases_on ‘l’ >> simp [ext_lit_def]
    >> rename1 ‘ext_var v’ >> Cases_on ‘v’ >> simp [ext_var_def]
    >> simp [xeval_lit_def])
  >-
   (rename1 ‘ext_gate a’ >> Cases_on ‘a’ >> simp [ext_gate_def]
    >> IF_CASES_TAC >> simp []
    >> rename1 ‘ext_gty g’ >> Cases_on ‘g’ >> simp [ext_gty_def]
    >> gvs [EVERY_MAP, EXISTS_MAP]
    )
  >> Cases_on ‘l’ >> simp [ext_lit_def]
  >> rename1 ‘ext_var v’ >> Cases_on ‘v’ >> simp [ext_var_def]
  >> simp [xeval_lit_def]
  >> rename1 ‘ext_gate b’ >> Cases_on ‘b’ >> simp [ext_gate_def]
  >> rename1 ‘ext_gty g’ >> Cases_on ‘g’ >> simp [ext_gty_def]
  >> IF_CASES_TAC >> gvs [EVERY_MAP, EXISTS_MAP]
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

Theorem iname_ext_lit[simp]:
  iname (ext_lit x) = 0
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [ext_lit_def, ext_var_def, iname_def]
QED

Theorem xeval_lit_Anon_neq:
  iname m ≠ n ⇒
  (xeval_lit ss ((Anon n, xs)::aig) m ⇔ xeval_lit ss aig m)
Proof
  simp [oneline iname_def] >> every_case_tac >> rw [xeval_lit_def]
QED

(* Getting the next available number to use as intermediate *)
Definition maxn_def:
  maxn (ls : ('a ext,'i,'l) lit list) =
    MAX_LIST (MAP iname ls) + 1
End

Theorem maxn_cons_leq:
  maxn (x::xs) ≤ n ⇔ iname x < n ∧ maxn xs ≤  n
Proof
  simp [maxn_def, MAX_DEF]
QED

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
  encode_imply (aig: ('a ext, 'i, 'l) xaig) name b lhss rhss =
  let n = MAX (maxn lhss) (maxn rhss) in
    (Ext name, And [(Gate (Anon (n+2)), b)])
    ::(Anon (n + 2), Ite (Gate (Anon (n+1)), F) (Gate (Anon n), F) TT)
    ::(Anon (n + 1), And lhss)::(Anon n, And rhss)::aig
End

Theorem xeval_gate_encode_imply:
  xeval_gate ss (encode_imply aig name b lhss rhss) (Ext n) =
  if n = name then
    (b ⇎ ((EVERY (xeval_lit ss aig) lhss) ⇒ (EVERY (xeval_lit ss aig) rhss)))
  else xeval_gate ss aig (Ext n)
Proof
  eq_tac
  >> rw [encode_imply_def, xeval_lit_def, EVERY_MEM]
  >> metis_tac [MEM_neq_iname_maxn, xeval_lit_Anon_neq]
QED

(* Encoding point-wise equality ***********************************************)

Definition xori_def:
  xori n i (x, y) : ('a ext, 'i, 'l) gate = (Anon (i + n), Xor x y)
End

Theorem xori_suc:
  xori n ∘ SUC = xori (n + 1)
Proof
  simp [FUN_EQ_THM] >> rpt Cases >> gvs [xori_def]
QED

Theorem iname_xeval_lit_xori:
  ∀xys n.
    iname x < n ⇒
    (xeval_lit ss (MAPi (xori n) xys ++ xaig) x ⇔ xeval_lit ss xaig x)
Proof
  Induct >> rw []
  >> rename1 ‘xori _ _ g’ >> Cases_on ‘g’
  >> simp [xori_def, xori_suc, xeval_lit_Anon_neq]
QED

Theorem xeval_gate_xori_anon:
  ∀xys n i.
    i < LENGTH xys ∧
    MAX (maxn (MAP FST xys)) (maxn (MAP SND xys)) ≤ n
    ⇒
    (xeval_gate ss (MAPi (xori n) xys ++ xaig) (Anon (i + n)) ⇔
     (xeval_lit ss xaig (FST xys❲i❳) ⇎ xeval_lit ss xaig (SND xys❲i❳)))
Proof
  Induct >> rw []
  >> rename1 ‘xori _ _ g’ >> Cases_on ‘g’ >> simp [xori_def]
  >> Cases_on ‘i’
  >> gvs [xeval_lit_def, xori_suc, maxn_cons_leq]
  >- gvs [Req0 iname_xeval_lit_xori]
  >> rename1 ‘Anon (n + SUC i)’
  >> first_x_assum $ qspecl_then [‘n + 1’, ‘i’] mp_tac
  >> simp [ADD1]
QED

Theorem xeval_gate_xori_ext:
  ∀xys n.
    xeval_gate ss (MAPi (xori n) xys ++ xaig) (Ext name) ⇔
    xeval_gate ss xaig (Ext name)
Proof
  Induct >> rw []
  >> rename1 ‘xori _ _ g’ >> Cases_on ‘g’
  >> simp [xori_def, xori_suc, xeval_lit_def]
QED

Theorem xeval_gate_xori_orig:
  ∀xys n.
    xeval_gate ss (MAPi (xori n) xys ++ xaig) (Orig a) ⇔
    xeval_gate ss xaig (Orig a)
Proof
  Induct >> rw []
  >> rename1 ‘xori _ _ g’ >> Cases_on ‘g’
  >> simp [xori_def, xori_suc, xeval_lit_def]
QED

Definition encode_pointwise_equal_def:
  encode_pointwise_equal (xaig: ('a ext, 'i, 'l) xaig) name xys =
  let
    n = MAX (maxn (MAP FST xys)) (maxn (MAP SND xys));
    xor_gates = MAPi (xori n) xys;
    xnor_lits = And (GENLIST (λi. (Gate (Anon (i + n)), T)) (LENGTH xys));
  in
    (Ext name, xnor_lits)::xor_gates ++ xaig
End

Theorem xeval_gate_encode_pointwise_equal_ext:
  xeval_gate ss (encode_pointwise_equal xaig name xys) (Ext n) =
  if n = name then
    EVERY (λ(x,y). xeval_lit ss xaig x ⇔ xeval_lit ss xaig y) xys
  else xeval_gate ss xaig (Ext n)
Proof
  rw [xeval_lit_def, encode_pointwise_equal_def]
  >- (
    eq_tac
    >> rw [EVERY_EL]
    >> rpt strip_tac
    >> first_x_assum $ drule_then assume_tac
    >> pairarg_tac >> gvs []
    >> gvs [xeval_lit_def, Req0 xeval_gate_xori_anon]
  )
  >> simp [xeval_gate_xori_ext]
QED

Theorem xeval_lit_encode_pointwise_equal_ext:
  xeval_lit ss (encode_pointwise_equal xaig name xys) (Gate (Ext n), b) =
  if n = name then
    b ⇎ EVERY (λ(x,y). xeval_lit ss xaig x ⇔ xeval_lit ss xaig y) xys
  else xeval_lit ss xaig (Gate (Ext n), b)
Proof
  simp [xeval_lit_def, xeval_gate_encode_pointwise_equal_ext]
  >> IF_CASES_TAC >> gvs []
QED

Theorem xeval_lit_encode_pointwise_equal_ext_lit:
  xeval_lit ss (encode_pointwise_equal xaig name xys) (ext_lit n) =
  xeval_lit ss xaig (ext_lit n)
Proof
  namedCases_on ‘n’ ["v b"] >> Cases_on ‘v’
  >> simp [ext_lit_def, ext_var_def, encode_pointwise_equal_def, xeval_lit_def,
           xeval_gate_xori_orig]
QED

(* Encoding point-wise implication ********************************************)

Definition impi_def:
  impi n i (x, y) : ('a ext, 'i, 'l) gate = (Anon (i + n), Ite x y TT)
End

Theorem impi_suc:
  impi n ∘ SUC = impi (n + 1)
Proof
  simp [FUN_EQ_THM] >> rpt Cases >> gvs [impi_def]
QED

Theorem iname_xeval_lit_impi:
  ∀xys n.
    iname x < n ⇒
    (xeval_lit ss (MAPi (impi n) xys ++ xaig) x ⇔ xeval_lit ss xaig x)
Proof
  Induct >> rw []
  >> rename1 ‘impi _ _ g’ >> Cases_on ‘g’
  >> simp [impi_def, impi_suc, xeval_lit_Anon_neq]
QED

Theorem xeval_gate_impi_anon:
  ∀xys n i.
    i < LENGTH xys ∧
    MAX (maxn (MAP FST xys)) (maxn (MAP SND xys)) ≤ n
    ⇒
    (xeval_gate ss (MAPi (impi n) xys ++ xaig) (Anon (i + n)) ⇔
     (xeval_lit ss xaig (FST xys❲i❳) ⇒ xeval_lit ss xaig (SND xys❲i❳)))
Proof
  Induct >> rw []
  >> rename1 ‘impi _ _ g’ >> Cases_on ‘g’ >> simp [impi_def]
  >> Cases_on ‘i’
  >> gvs [xeval_lit_def, impi_suc, maxn_cons_leq]
  >- gvs [Req0 iname_xeval_lit_impi]
  >> rename1 ‘Anon (n + SUC i)’
  >> first_x_assum $ qspecl_then [‘n + 1’, ‘i’] mp_tac
  >> simp [ADD1]
QED

Theorem xeval_gate_impi_ext:
  ∀xys n.
    xeval_gate ss (MAPi (impi n) xys ++ xaig) (Ext name) ⇔
    xeval_gate ss xaig (Ext name)
Proof
  Induct >> rw []
  >> rename1 ‘impi _ _ g’ >> Cases_on ‘g’
  >> simp [impi_def, impi_suc, xeval_lit_def]
QED

Theorem xeval_gate_impi_orig:
  ∀xys n.
    xeval_gate ss (MAPi (impi n) xys ++ xaig) (Orig a) ⇔
    xeval_gate ss xaig (Orig a)
Proof
  Induct >> rw []
  >> rename1 ‘impi _ _ g’ >> Cases_on ‘g’
  >> simp [impi_def, impi_suc, xeval_lit_def]
QED

Definition encode_pointwise_imply_def:
  encode_pointwise_imply (xaig: ('a ext, 'i, 'l) xaig) name xys =
  let
    n = MAX (maxn (MAP FST xys)) (maxn (MAP SND xys));
    imp_gates = MAPi (impi n) xys;
    gty = And (GENLIST (λi. (Gate (Anon (i + n)), F)) (LENGTH xys));
  in
    (Ext name, gty)::imp_gates ++ xaig
End

Theorem xeval_gate_encode_pointwise_imply_ext:
  xeval_gate ss (encode_pointwise_imply xaig name xys) (Ext n) =
  if n = name then
    EVERY (λ(x,y). xeval_lit ss xaig x ⇒ xeval_lit ss xaig y) xys
  else xeval_gate ss xaig (Ext n)
Proof
  rw [xeval_lit_def, encode_pointwise_imply_def]
  >- (
    eq_tac
    >> rw [EVERY_EL]
    >> rpt strip_tac
    >> first_x_assum $ drule_then assume_tac
    >> pairarg_tac >> gvs []
    >> gvs [xeval_lit_def, Req0 xeval_gate_impi_anon]
  )
  >> simp [xeval_gate_impi_ext]
QED

Theorem xeval_lit_encode_pointwise_imply_ext:
  xeval_lit ss (encode_pointwise_imply xaig name xys) (Gate (Ext n), b) =
  if n = name then
    b ⇎ EVERY (λ(x,y). xeval_lit ss xaig x ⇒ xeval_lit ss xaig y) xys
  else xeval_lit ss xaig (Gate (Ext n), b)
Proof
  simp [xeval_lit_def, xeval_gate_encode_pointwise_imply_ext]
  >> IF_CASES_TAC >> gvs []
QED

Theorem xeval_lit_encode_pointwise_imply_ext_lit:
  xeval_lit ss (encode_pointwise_imply xaig name xys) (ext_lit n) =
  xeval_lit ss xaig (ext_lit n)
Proof
  namedCases_on ‘n’ ["v b"] >> Cases_on ‘v’
  >> simp [ext_lit_def, ext_var_def, encode_pointwise_imply_def, xeval_lit_def,
           xeval_gate_impi_orig]
QED

(* Encoding is_reset **********************************************************)

Definition latch_reset_pairs_def:
  (latch_reset_pairs (reset: 'l -> ('a ext,'i,'l) lit option) ([]: 'l list) = []) ∧
  (latch_reset_pairs reset (l::ls) =
     case reset l of
     | NONE   => latch_reset_pairs reset ls
     | SOME r => ((Base (Latch l), F), r) :: latch_reset_pairs reset ls)
End

Definition encode_is_reset_def:
  encode_is_reset (xaig: ('a ext, 'i, 'l) xaig) name reset ls =
  encode_pointwise_equal xaig name (latch_reset_pairs reset ls)
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

Theorem xeval_gate_encode_is_reset_ext:
  xeval_gate ss (encode_is_reset xaig name reset ls) (Ext n) =
  if n = name then
    xis_reset ss xaig reset (set ls)
  else xeval_gate ss xaig (Ext n)
Proof
  Cases_on ‘ss’
  >> rw [xeval_lit_def, encode_is_reset_def, xeval_gate_encode_pointwise_equal_ext]
  >> simp [xis_reset_def]
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

Theorem xeval_lit_encode_is_reset_ext:
  xeval_lit ss (encode_is_reset xaig name reset ls) (Gate (Ext n),F) =
  if n = name then
    xis_reset ss xaig reset (set ls)
  else xeval_lit ss xaig (Gate (Ext n),F)
Proof
  simp [xeval_lit_def, xeval_gate_encode_is_reset_ext]
QED

(* Encoding lits_hold *********************************************************)

Definition encode_lits_hold_def:
  encode_lits_hold
    (xaig: ('a ext, 'i, 'l) xaig) name (lits: ('a ext,'i,'l) lit list) =
  (Ext name, And lits)::xaig
End

Theorem xeval_lit_encode_lits_hold_ext:
  xeval_lit ss (encode_lits_hold xaig name lits) (n,F) =
  if n = Gate (Ext name) then
    xlits_hold ss xaig (set lits)
  else xeval_lit ss xaig (n,F)
Proof
  simp [encode_lits_hold_def, xeval_lit_def, xlits_hold_def, EVERY_MEM]
  >> IF_CASES_TAC >> gvs []
  >> TOP_CASE_TAC >> gvs []
QED

Theorem xeval_lit_encode_lits_hold_ext_lit:
  xeval_lit ss (encode_lits_hold xaig name lits) (ext_lit lit) =
  xeval_lit ss xaig (ext_lit lit)
Proof
  simp [encode_lits_hold_def]
QED

Theorem xeval_gate_encode_lits_hold_ext:
  xeval_gate ss (encode_lits_hold xaig name lits) (Ext n) =
  if n = name then
    xlits_hold ss xaig (set lits)
  else xeval_gate ss xaig (Ext n)
Proof
  simp [encode_lits_hold_def, xeval_lit_def, xlits_hold_def, EVERY_MEM]
  >> IF_CASES_TAC >> simp []
QED

Definition ext_reset_def:
  ext_reset reset = λl. OPTION_MAP ext_lit (reset l)
End

Definition left_reset_def:
  left_reset mreset =
  λl. OPTION_MAP left_name_lit (mreset l)
End

Definition right_reset_def:
  right_reset mreset =
  λl. OPTION_MAP right_name_lit (mreset l)
End

(* Encoding is_next ***********************************************************)

(* cur = "path" to literals in the current state; nxt = "path" to next state *)
Definition encode_is_next_def:
  encode_is_next aig name cur nxt next latches =
    encode_pointwise_equal aig name
      (MAP (λl. (cur (next l), nxt (Base (Latch l), F))) latches)
End

(* Encoding lives_imply *******************************************************)

(* If the liveness properties are "well-formed", that is, we assume that
   corresponding liveness properties in the model and the witness have the
   same number of signals, lives_imply is the same as pointwise implication
   all signals at once. *)

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

Definition encode_signal_imply_def:
  encode_signal_imply xaig name xs ys =
    encode_pointwise_imply xaig name (ZIP (xs, ys))
End

Theorem xeval_lit_encode_signal_imply_ext:
  LENGTH signals' = LENGTH signals ⇒
  xeval_lit ss (encode_signal_imply xaig name signals signals') (Gate (Ext n), b) =
  if n = name then
    (b ⇎ xsignal_imply ss xaig ss xaig signals signals')
  else xeval_lit ss xaig (Gate (Ext n), b)
Proof
  strip_tac
  >> simp [encode_signal_imply_def, xeval_lit_encode_pointwise_imply_ext,
           xsignal_imply_def, xlits_hold_def, LIST_REL_EVERY]
QED

Theorem xeval_lit_encode_signal_imply_ext_lit:
  xeval_lit ss (encode_signal_imply xaig name signals signals') (ext_lit n) =
  xeval_lit ss xaig (ext_lit n)
Proof
  simp [encode_signal_imply_def, xeval_lit_encode_pointwise_imply_ext_lit]
QED

(*
(* Encoding lives_hold ********************************************************)

(* Computes the disjunction of each list.
   MAPi and GENLIST were annoying to deal with here, so a separate function
   it is. *)
Definition encode_lives_hold_aux_def:
  (encode_lives_hold_aux
     (aig: ('a ext, 'i, 'l) aig)
     (signals::rest : ('a ext, 'i, 'l) lit list list)
     (next: num)
   : (('a ext, 'i, 'l) aig # num list)
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
    (aig: ('a ext, 'i, 'l) aig)
    (name: mlstring)
    (live: ('a ext, 'i, 'l) lit list list)
  : ('a ext, 'i, 'l) aig
  =
  let
    (aig, outs) = encode_lives_hold_aux aig live 1;
  in
    (Named (Ext name),MAP (λn. (Gate (Anon n),T)) outs)::aig
End

Theorem xeval_gate_encode_lives_hold_aux_Named[local]:
  ∀live aig next aig' outs.
    (encode_lives_hold_aux aig live next = (aig', outs)
    ⇒
    (xeval_gate ss aig' (Named n) ⇔ xeval_gate ss aig (Named n)))
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> last_x_assum drule
  >> simp [xeval_lit_def]
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
    (EXISTS (λx. xeval_lit ss aig' x) xs ⇔ EXISTS (λx. xeval_lit ss aig x) xs)
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> fs [EXISTS_MEM, EVERY_MEM]
  >> last_x_assum drule
  >> impl_tac >- (rpt strip_tac >> res_tac >> simp [])
  >> strip_tac
  >> eq_tac >> rw []
  >> metis_tac [prim_recTheory.LESS_NOT_EQ, xeval_lit_Anon_neq]
QED

Theorem encode_lives_hold_aux_xeval_lit[local]:
  ∀live aig next aig' outs.
    encode_lives_hold_aux aig live next = (aig',outs) ∧
    EVERY (EVERY (λx. iname x < next)) live
    ⇒
    ∀n. n < LENGTH live ⇒
       ((xeval_lit ss aig' (MAP (λn. (Gate (Anon n),T)) outs)❲n❳) ⇔
        EXISTS (λp. lits_hold ss aig {p}) live❲n❳)
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> Cases_on ‘n’ >> gvs []
  >-
   (simp [xeval_lit_def, lits_hold_def]
    >> simp [EXISTS_MAP, xeval_lit_not]
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
  >> DEP_REWRITE_TAC [xeval_lit_Anon_neq]
  >> simp [iname_def]
QED

Theorem xeval_gate_encode_lives_hold:
  EVERY (EVERY (λx. iname x = 0)) live
  ⇒
  xeval_gate ss (encode_lives_hold aig name live) (Named n) =
  if n = Ext name then
    lives_hold ss aig live
  else xeval_gate ss aig (Named n)
Proof
  strip_tac
  >> simp [encode_lives_hold_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [xeval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >-
   (simp [lives_hold_def, some_signal_holds_def, EVERY_EL]
    >> drule_then assume_tac encode_lives_hold_aux_LENGTH
    >> rewrite_tac [EXISTS_NOT_EVERY]
    >> drule_then assume_tac encode_lives_hold_aux_xeval_lit
    >> simp [o_DEF])
  >> drule xeval_gate_encode_lives_hold_aux_Named
  >> simp []
QED

Theorem xeval_lit_encode_lives_hold_Named:
  EVERY (EVERY (λx. iname x = 0)) live
  ⇒
  xeval_lit ss (encode_lives_hold aig name live) (Gate (Named n), b) =
  if n = Ext name then
    (b ⇎ lives_hold ss aig live)
  else xeval_lit ss aig (Gate (Named n), b)
Proof
  strip_tac >> simp [xeval_lit_def]
  >> drule_all xeval_gate_encode_lives_hold
  >> rw []
QED
*)
(* Encoding certificate conditions ********************************************)

(* todo use optimized aig_to_xaig when available *)

Definition encode_reset_cond_def:
  encode_reset_cond
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
    xaig  = ext_xaig (merge_aigs (aig_to_xaig maig) (aig_to_xaig waig));
    xaig  = encode_is_reset xaig «mreset» (ext_reset (left_reset mreset)) mlatches;
    xaig  = encode_lits_hold xaig «mcnstrs» (MAP (ext_lit ∘ left_name_lit) mcnstrs);
    xaig  = encode_is_reset xaig «wreset» (ext_reset (right_reset wreset)) klatches;
    xaig  = encode_lits_hold xaig «wcnstrs» (MAP (ext_lit ∘ right_name_lit) wcnstrs);
    lhss =
      [(Gate (Ext «mreset»), F);
       (Gate (Ext «mcnstrs»), F)];
    rhss =
      [(Gate (Ext «wreset»), F);
       (Gate (Ext «wcnstrs»), F)];
  in
    encode_imply xaig «reset» T lhss rhss
End

Definition encode_transition_cond_def:
  encode_transition_cond
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
    aig  = merge_aigs (aig_to_xaig maig) (aig_to_xaig waig);
    aig  = ext_xaig (pair_aigs aig aig);
    aig  = encode_lits_hold aig «mcnstrs0»
             (MAP (ext_lit ∘ left_lit ∘ left_name_lit) mcnstrs);
    aig  = encode_lits_hold aig «wcnstrs0»
             (MAP (ext_lit ∘ left_lit ∘ right_name_lit) wcnstrs);
    aig  = encode_lits_hold aig «mcnstrs1»
             (MAP (ext_lit ∘ right_lit ∘ left_name_lit) mcnstrs);
    aig  = encode_lits_hold aig «wcnstrs1»
             (MAP (ext_lit ∘ right_lit ∘ right_name_lit) wcnstrs);
    aig  = encode_is_next aig «mnext»
            (ext_lit ∘ left_lit ∘ left_name_lit)
            (ext_lit ∘ right_lit)
            mnext mlatches;
    aig  = encode_is_next aig «wnext»
            (ext_lit ∘ left_lit ∘ right_name_lit)
            (ext_lit ∘ right_lit)
            wnext klatches;
    lhss =
      [(Gate (Ext «mnext»), F);
       (Gate (Ext «mcnstrs0»), F);
       (Gate (Ext «mcnstrs1»), F);
       (Gate (Ext «wcnstrs0»), F)];
    rhss =
      [(Gate (Ext «wnext»), F);
       (Gate (Ext «wcnstrs1»), F)];
  in
    encode_imply aig «transition» T lhss rhss
End

Definition encode_safety_cond_def:
  encode_safety_cond
    (maig: ('a, 'i, 'l) aig)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (msafes: ('a, 'i, 'l) lit list)
    (waig: ('b, 'i, 'l) aig)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
  =
  let
    aig  = ext_xaig (merge_aigs (aig_to_xaig maig) (aig_to_xaig waig));
    aig  = encode_lits_hold aig «mcnstrs» (MAP (ext_lit ∘ left_name_lit) mcnstrs);
    aig  = encode_lits_hold aig «msafes» (MAP (ext_lit ∘ left_name_lit) msafes);
    aig  = encode_lits_hold aig «wcnstrs» (MAP (ext_lit ∘ right_name_lit) wcnstrs);
    aig  = encode_lits_hold aig «wsafes» (MAP (ext_lit ∘ right_name_lit) wsafes);
    lhss =
      [(Gate (Ext «mcnstrs»),F);
       (Gate (Ext «wcnstrs»),F);
       (Gate (Ext «wsafes»),F)];
    rhss = [(Gate (Ext «msafes»), F);]
  in
    encode_imply aig «safety» T lhss rhss
End


Definition encode_base_cond_def:
  encode_base_cond
    (waig: ('a, 'i, 'l) aig)
    (wreset: 'l -> ('a, 'i, 'l) lit option)
    (wcnstrs: ('a, 'i, 'l) lit list)
    (wsafes: ('a, 'i, 'l) lit list)
    (wlatches: 'l list)
  ⇔
    let
      xaig  = ext_xaig (aig_to_xaig waig);
      xaig  = encode_is_reset xaig «wreset» (ext_reset wreset) wlatches;
      xaig  = encode_lits_hold xaig «wcnstrs» (MAP ext_lit wcnstrs);
      xaig  = encode_lits_hold xaig «wsafes» (MAP ext_lit wsafes);
      lhss =
        [(Gate (Ext «wreset»),F);
         (Gate (Ext «wcnstrs»),F)];
      rhss = [(Gate (Ext «wsafes»), F)]
  in
    encode_imply xaig «base» T lhss rhss
End

Definition encode_induction_cond_def:
  encode_induction_cond
    (waig: ('a, 'i, 'l) aig)
    (wnext: 'l -> ('a, 'i, 'l) lit)
    (wcnstrs: ('a, 'i, 'l) lit list)
    (wsafes: ('a, 'i, 'l) lit list)
    (wlatches: 'l list)
  =
    let
      xwaig = aig_to_xaig waig;
      aig  = ext_xaig (pair_aigs xwaig xwaig);
      aig  = encode_lits_hold aig «wcnstrs0»
               (MAP (ext_lit ∘ left_lit) wcnstrs);
      aig  = encode_lits_hold aig «wsafes0»
               (MAP (ext_lit ∘ left_lit) wsafes);
      aig  = encode_lits_hold aig «wcnstrs1»
               (MAP (ext_lit ∘ right_lit) wcnstrs);
      aig  = encode_lits_hold aig «wsafes1»
               (MAP (ext_lit ∘ right_lit) wsafes);
      aig  = encode_is_next aig «wnext»
               (ext_lit ∘ left_lit) (ext_lit ∘ right_lit)
               wnext wlatches;
      lhss =
        [(Gate (Ext «wsafes0»), F);
         (Gate (Ext «wnext»), F);
         (Gate (Ext «wcnstrs1»), F);
         (Gate (Ext «wcnstrs0»), F)];
      rhss = [(Gate (Ext «wsafes1»), F)]
    in
      encode_imply aig «induction» T lhss rhss
End

Definition encode_liveness_cond_def:
  encode_liveness_cond
    (maig: ('a, 'i, 'l) aig)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlive: ('a, 'i, 'l) lit list list)
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    maig = aig_to_xaig maig;
    waig = aig_to_xaig waig;
    mqaig = xqleft maig;
    wqaig = xqinterv_l_r interv waig;
    qaig  = merge_aigs mqaig wqaig;
    aig   = merge_aigs maig waig;
    aig   = pair_aigs aig aig;
    aig   = ext_xaig (merge_aigs aig qaig);
    wsignals = MAP (ext_lit ∘ right_name_lit ∘ right_name_lit)
                     (FLAT (qinterv_live_l_r interv wlive));
    msignals = MAP (ext_lit ∘ right_name_lit ∘ left_name_lit)
                     (FLAT (xqleft_live mlive));
    aig   = encode_signal_imply aig «lives_imply» wsignals msignals;
    aig   = encode_lits_hold aig «mcnstrs0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_name_lit) mcnstrs);
    aig   = encode_lits_hold aig «wcnstrs0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_name_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_name_lit) wsafes);
    aig   = encode_lits_hold aig «mcnstrs1»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit ∘ left_name_lit) mcnstrs);
    aig   = encode_lits_hold aig «wcnstrs1»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit ∘ right_name_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes1»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit ∘ right_name_lit) wsafes);
    aig =
      encode_is_next aig «wnext»
        (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_name_lit)
        (ext_lit ∘ left_name_lit ∘ right_lit)
        wnext wlatches;
    lhss = [
        (Gate (Ext «mcnstrs0»), F);
        (Gate (Ext «wcnstrs0»), F);
        (Gate (Ext «wsafes0»), F);
        (Gate (Ext «mcnstrs1»), F);
        (Gate (Ext «wcnstrs1»), F);
        (Gate (Ext «wsafes1»), F);
        (Gate (Ext «wnext»), F)
    ];
    rhss = [(Gate (Ext «lives_imply»), F)]
  in
    encode_imply aig «liveness» T lhss rhss
End

(*
Definition encode_decrease_cond_def:
  encode_decrease_cond
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    qaig  = qinterv_r_l interv waig;
    aig   = pair_aigs waig waig;
    aig   = imerge_aigs aig qaig;
    aig   = encode_lits_hold aig «wcnstrs0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit) wsafes);
    aig   = encode_lits_hold aig «wcnstrs1»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes1»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wsafes);
    aig   = encode_is_next_with aig «wnext»
              (ext_lit ∘ left_name_lit ∘ left_lit)
              (ext_lit ∘ left_name_lit ∘ right_lit)
              wnext wlatches;
    live  = MAP iright_name_lits (qinterv_live_r_l interv wlive);
    aig   = encode_lives_hold aig «lives_hold» live;
    lhss = [
      (Gate (Named (Ext «wcnstrs0»)), F);
      (Gate (Named (Ext «wsafes0»)), F);
      (Gate (Named (Ext «wcnstrs1»)), F);
      (Gate (Named (Ext «wsafes1»)), F);
      (Gate (Named (Ext «wnext»)), F);
    ];
    rhss = [(Gate (Named (Ext «lives_hold»)), F)]
  in
    encode_imply aig «decrease» T lhss rhss
End

Definition encode_closure_cond_def:
  encode_closure_cond
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    (* states: s = ll, t = lr, u = r *)
    qaig₀ = qinterv_ll_r interv waig;
    qaig₁ = qinterv_lr_r interv waig;
    qaig  = merge_aigs qaig₀ qaig₁;
    aig   = pair_aigs (pair_aigs waig waig) waig;
    aig   = imerge_aigs aig qaig;
    aig   = encode_lits_hold aig «wcnstrs0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit) wsafes);
    aig   = encode_lits_hold aig «wcnstrs1»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes1»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit) wsafes);
    aig   = encode_lits_hold aig «wcnstrs2»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes2»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wsafes);
    aig   = encode_is_next_with aig «wnext»
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit)
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit)
              wnext wlatches;
    live₀ = MAP (MAP (ext_lit ∘ right_name_lit ∘ left_name_lit))
              (qinterv_live_ll_r interv wlive);
    live₁ = MAP (MAP (ext_lit ∘ right_name_lit ∘ right_name_lit))
              (qinterv_live_lr_r interv wlive);
    aig = encode_lives_hold aig «lives_hold02» live₀;
    aig = encode_lives_hold aig «lives_hold12» live₁;
    lhss = [
      (Gate (Named (Ext «wcnstrs»)), F);
      (Gate (Named (Ext «wsafes»)), F);
      (Gate (Named (Ext «wcnstrs»)), F);
      (Gate (Named (Ext «wsafes»)), F);
      (Gate (Named (Ext «wcnstrs»)), F);
      (Gate (Named (Ext «wsafes»)), F);
      (Gate (Named (Ext «wnext»)), F);
      (Gate (Named (Ext «lives_hold02»)), F);
    ];
    rhss = [(Gate (Named (Ext «lives_hold12»)), F)]
  in
    encode_imply aig «closure» T lhss rhss
End

Definition encode_stable_cond_def:
  encode_stable_cond
    (waig: ('b, 'i, 'l) aig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    (* states: s = ll, t = lr, u = r *)
    qaig₀ = qinterv_ll_lr interv waig;
    qaig₁ = qinterv_lr_r interv waig;
    qaig  = merge_aigs qaig₀ qaig₁;
    aig   = pair_aigs (pair_aigs waig waig) waig;
    aig   = imerge_aigs aig qaig;
    aig   = encode_lits_hold aig «wcnstrs0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes0»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit) wsafes);
    aig   = encode_lits_hold aig «wcnstrs1»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes1»
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit) wsafes);
    aig   = encode_lits_hold aig «wcnstrs2»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wcnstrs);
    aig   = encode_lits_hold aig «wsafes2»
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wsafes);
    aig   = encode_is_next_with aig «wnext0»
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit)
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit)
              wnext wlatches;
    aig   = encode_is_next_with aig «wnext1»
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit)
              (ext_lit ∘ left_name_lit ∘ right_lit)
              wnext wlatches;
    live₀ = MAP (MAP (ext_lit ∘ right_name_lit ∘ left_name_lit))
              (qinterv_live_ll_lr interv wlive);
    live₁ = MAP (MAP (ext_lit ∘ right_name_lit ∘ right_name_lit))
              (qinterv_live_lr_r interv wlive);
    aig = encode_lives_hold aig «lives_hold01» live₀;
    aig = encode_lives_hold aig «lives_hold12» live₁;
    aig = encode_signal_imply aig «lives_imply» (FLAT live₀) (FLAT live₁) ;
    lhss = [
        (Gate (Named (Ext «wcnstrs0»)), F);
        (Gate (Named (Ext «wsafes0»)), F);
        (Gate (Named (Ext «wcnstrs1»)), F);
        (Gate (Named (Ext «wsafes1»)), F);
        (Gate (Named (Ext «wcnstrs2»)), F);
        (Gate (Named (Ext «wsafes2»)), F);
        (Gate (Named (Ext «wnext0»)), F);
        (Gate (Named (Ext «wnext1»)), F);
        (Gate (Named (Ext «lives_hold01»)), F);
        (Gate (Named (Ext «lives_hold12»)), F)
      ];
    rhss = [(Gate (Named (Ext «lives_imply»)), F)];
  in
    encode_imply aig «stable» T lhss rhss
End

(* Proving correctness of the encodings ***************************************)

(* A bunch of trivial helper lemmas, which keep the proof state readable
   when an encoding function uses many other encoding functions. *)

Theorem is_reset_encode_lits_hold_iright[local,simp]:
  is_reset ss
    (encode_lits_hold aig name lits) (iright_reset reset) latches ⇔
  is_reset ss aig (iright_reset reset) latches
Proof
  simp [is_reset_def, encode_lits_hold_def, iright_reset_def, right_reset_def,
        xeval_lit_def, ext_reset_def, PULL_EXISTS]
QED

Theorem is_reset_encode_is_reset_iright[local,simp]:
  is_reset ss (encode_is_reset aig name reset' latches')
    (iright_reset reset) latches ⇔
  is_reset ss aig (iright_reset reset) latches
Proof
  simp [is_reset_def, encode_is_reset_def, iright_reset_def, xeval_lit_def,
        ext_reset_def, PULL_EXISTS]
QED

Theorem lits_hold_ext[local,simp]:
  lits_hold ss (ext_aig aig) (set (MAP ext_lit preds)) ⇔
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

Theorem lits_hold_encode_is_reset_ext[local,simp]:
  lits_hold ss
    (encode_is_reset aig name reset latches) (set (MAP ext_lit preds)) ⇔
  lits_hold ss aig (set (MAP ext_lit preds))
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
*)

(*** xlits_hold ***************************************************************)

Theorem xlits_hold_ext_aig_ext_lit[local,simp]:
  xlits_hold ss (ext_xaig xaig) (set (MAP ext_lit preds)) ⇔
    xlits_hold ss xaig (set preds)
Proof
  simp [xlits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_merge_left[local,simp]:
  xlits_hold ss (merge_aigs laig raig) (set (MAP left_name_lit preds)) ⇔
    xlits_hold ss laig (set preds)
Proof
  simp [xlits_hold_def, left_name_lit_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_merge_right[local,simp]:
  xlits_hold ss (merge_aigs laig raig) (set (MAP right_name_lit preds)) ⇔
    xlits_hold ss raig (set preds)
Proof
  simp [xlits_hold_def, right_name_lit_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_pair_left[local,simp]:
  xlits_hold (state_pair s₁ s₂) (pair_aigs laig raig)
    (set (MAP left_lit preds)) ⇔
  xlits_hold s₁ laig (set preds)
Proof
  simp [xlits_hold_def, left_lit_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_pair_right[local,simp]:
  xlits_hold (state_pair s₁ s₂) (pair_aigs laig raig)
    (set (MAP right_lit preds)) ⇔
  xlits_hold s₂ raig (set preds)
Proof
  simp [xlits_hold_def, right_lit_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_lits_hold_ext_lit[local,simp]:
  xlits_hold ss (encode_lits_hold xaig name preds')
    (set (MAP ext_lit preds)) ⇔
  xlits_hold ss xaig (set (MAP ext_lit preds))
Proof
  simp [xlits_hold_def, encode_lits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_is_reset_ext_lit[local,simp]:
  xlits_hold ss (encode_is_reset xaig name reset ls)
    (set (MAP ext_lit preds)) ⇔
  xlits_hold ss xaig (set (MAP ext_lit preds))
Proof
  simp [xlits_hold_def, encode_is_reset_def, encode_pointwise_equal_def,
        MEM_MAP, PULL_EXISTS]
  >> qmatch_goalsub_abbrev_tac ‘xori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_xori]
QED

Theorem xlits_hold_encode_pointwise_imply_ext_lit[local,simp]:
  xlits_hold ss (encode_pointwise_imply xaig name xys)
    (set (MAP ext_lit preds)) ⇔
  xlits_hold ss xaig (set (MAP ext_lit preds))
Proof
  simp [xlits_hold_def, encode_pointwise_imply_def,
        MEM_MAP, PULL_EXISTS]
  >> qmatch_goalsub_abbrev_tac ‘impi n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_impi]
QED

Theorem xlits_hold_encode_signal_imply_ext_lit[local,simp]:
  xlits_hold ss (encode_signal_imply xaig name xs ys)
    (set (MAP ext_lit preds)) ⇔
  xlits_hold ss xaig (set (MAP ext_lit preds))
Proof
  simp [encode_signal_imply_def]
QED

(*** xis_reset ****************************************************************)

Theorem xis_reset_ext[local,simp]:
  xis_reset ss (ext_xaig xaig) (ext_reset reset) latches ⇔
    xis_reset ss xaig reset latches
Proof
  simp [xis_reset_def, ext_reset_def, PULL_EXISTS]
QED

Theorem xis_reset_left[local,simp]:
  xis_reset ss (merge_aigs laig raig) (left_reset lreset) latches ⇔
    xis_reset ss laig lreset latches
Proof
  simp [xis_reset_def, left_reset_def, xeval_lit_def, PULL_EXISTS]
QED

Theorem xis_reset_right[local,simp]:
  xis_reset ss (merge_aigs laig raig) (right_reset rreset) latches ⇔
    xis_reset ss raig rreset latches
Proof
  simp [xis_reset_def, right_reset_def, xeval_lit_def, PULL_EXISTS]
QED

Theorem xis_reset_encode_lits_hold[local,simp]:
  xis_reset ss (encode_lits_hold xaig name lits) (ext_reset reset) ls ⇔
    xis_reset ss xaig (ext_reset reset) ls
Proof
  simp [xis_reset_def, encode_lits_hold_def, xeval_lit_def, ext_reset_def,
        PULL_EXISTS]
QED

Theorem xis_reset_encode_is_reset_ext[local,simp]:
  xis_reset ss (encode_is_reset xaig name reset' ls') (ext_reset reset) ls ⇔
    xis_reset ss xaig (ext_reset reset) ls
Proof
  simp [xis_reset_def, encode_is_reset_def, encode_pointwise_equal_def, xeval_lit_def,
        ext_reset_def, PULL_EXISTS]
  >> qmatch_goalsub_abbrev_tac ‘xori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_xori]
QED

(*** xsignal_imply ************************************************************)

Theorem xsignal_imply_ext_lit[local,simp]:
  (xsignal_imply ss (ext_xaig xaig) ss' xaig' (MAP ext_lit signals) signals' ⇔
     xsignal_imply ss xaig ss' xaig' signals signals') ∧
  (xsignal_imply ss xaig ss' (ext_xaig xaig') signals (MAP ext_lit signals') ⇔
    xsignal_imply ss xaig ss' xaig' signals signals')
Proof
  simp [xsignal_imply_def, LIST_REL_MAP, xlits_hold_def]
QED

Theorem xsignal_imply_merge_right[local,simp]:
  (xsignal_imply ss (merge_aigs laig raig) ss' xaig'
    (MAP right_name_lit signals) signals' ⇔
   xsignal_imply ss raig ss' xaig' signals signals') ∧
  (xsignal_imply ss xaig ss' (merge_aigs laig' raig')
     signals (MAP right_name_lit signals') ⇔
   xsignal_imply ss xaig ss' raig' signals signals')
Proof
  simp [xsignal_imply_def, LIST_REL_MAP, xlits_hold_def]
QED

Theorem xsignal_imply_merge_left[local,simp]:
  (xsignal_imply ss (merge_aigs laig raig) ss' xaig'
    (MAP left_name_lit signals) signals' ⇔
   xsignal_imply ss laig ss' xaig' signals signals') ∧
  (xsignal_imply ss xaig ss' (merge_aigs laig' raig')
     signals (MAP left_name_lit signals') ⇔
   xsignal_imply ss xaig ss' laig' signals signals')
Proof
  simp [xsignal_imply_def, LIST_REL_MAP, xlits_hold_def]
QED

(*
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

Theorem lives_hold_ext_aig[local,simp]:
  lives_hold ss (ext_aig aig) (MAP (MAP ext_lit) lives)
  ⇔
  lives_hold ss aig lives
Proof
  simp [lives_hold_def, some_signal_holds_def, lits_hold_def,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem encode_lives_hold_aux_xeval_lit_ext[local]:
  ∀live aig next aig' outs.
    encode_lives_hold_aux aig live next = (aig',outs)
    ⇒
    (xeval_lit ss aig' (ext_lit lit) ⇔ xeval_lit ss aig (ext_lit lit))
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> last_x_assum drule >> simp []
QED

Theorem encode_signal_imply_aux_xeval_lit_ext[local]:
  ∀aig signals signals' next aig' outs.
    encode_signal_imply_aux aig signals signals' next = (aig',outs)
    ⇒
    (xeval_lit ss aig' (ext_lit lit) ⇔ xeval_lit ss aig (ext_lit lit))
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
  >> drule encode_lives_hold_aux_xeval_lit_ext >> simp []
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
  >> drule encode_signal_imply_aux_xeval_lit_ext
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
  >> drule encode_signal_imply_aux_xeval_lit_ext
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

Theorem xeval_lit_qinterv_r_l_eq[local]:
  (∀lit.
     xeval_lit (state_pair s₀ s₁) (qinterv_r_l interv aig)
       (qinterv_lit INR INR INL interv lit)
     ⇔
     xeval_lit (state_pair s₁ s₀) (qinterv_l_r interv aig)
       (qinterv_lit INL INL INR interv lit)) ∧
  (∀a.
     xeval_gate (state_pair s₀ s₁) (qinterv_r_l interv aig) a ⇔
     xeval_gate (state_pair s₁ s₀) (qinterv_l_r interv aig) a)
Proof
  Induct_on ‘aig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’
  >-
   (simp [qinterv_r_l_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def, state_pair_def]
    >> rpt CASE_TAC
    >> simp [xeval_lit_def]
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
      >- (CASE_TAC >> simp [xeval_lit_def, state_pair_def])
      >> simp [xeval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_and_def, AllCaseEqs()]
      >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [xeval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [xeval_lit_def])
  >> rename1 ‘qinterv_r_l _ (h::_)’
  >> Cases_on ‘h’
  >> simp [qinterv_r_l_cons, qinterv_l_r_cons]
  >> simp [qinterv_and_def, xeval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem xeval_lit_qinterv_ll_r_eq[local]:
  (∀lit.
     xeval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_ll_r interv aig)
       (qinterv_lit (INL ∘ INL) (INL ∘ INL) INR interv lit)
     ⇔
     xeval_lit (state_pair s₀ s₂) (qinterv_l_r interv aig)
       (qinterv_lit INL INL INR interv lit)) ∧
  (∀a.
     xeval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_ll_r interv aig) a ⇔
     xeval_gate (state_pair s₀ s₂) (qinterv_l_r interv aig) a)
Proof
  Induct_on ‘aig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_ll_r_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def, state_pair_def]
    >> rpt CASE_TAC
    >> simp [xeval_lit_def]
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
      >- (CASE_TAC >> simp [xeval_lit_def, state_pair_def])
      >> simp [xeval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_and_def, AllCaseEqs()]
      >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [xeval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [xeval_lit_def])
  >> rename1 ‘qinterv_ll_r _ (h::_)’
  >> Cases_on ‘h’
  >> simp [qinterv_ll_r_cons, qinterv_l_r_cons]
  >> simp [qinterv_and_def, xeval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem xeval_lit_qinterv_lr_r_eq[local]:
  (∀lit.
     xeval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_lr_r interv aig)
       (qinterv_lit (INL ∘ INR) (INL ∘ INR) INR interv lit)
     ⇔
     xeval_lit (state_pair s₁ s₂) (qinterv_l_r interv aig)
       (qinterv_lit INL INL INR interv lit)) ∧
  (∀a.
     xeval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_lr_r interv aig) a ⇔
     xeval_gate (state_pair s₁ s₂) (qinterv_l_r interv aig) a)
Proof
  Induct_on ‘aig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_lr_r_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def, state_pair_def]
    >> rpt CASE_TAC
    >> simp [xeval_lit_def]
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
      >- (CASE_TAC >> simp [xeval_lit_def, state_pair_def])
      >> simp [xeval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_and_def, AllCaseEqs()]
      >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [xeval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [xeval_lit_def])
  >> rename1 ‘qinterv_lr_r _ (h::_)’
  >> Cases_on ‘h’
  >> simp [qinterv_lr_r_cons, qinterv_l_r_cons]
  >> simp [qinterv_and_def, xeval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem xeval_lit_qinterv_ll_lr_eq[local]:
  (∀lit.
     xeval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_ll_lr interv aig)
       (qinterv_lit (INL ∘ INL) (INL ∘ INL) (INL ∘ INR) interv lit)
     ⇔
     xeval_lit (state_pair s₀ s₁) (qinterv_l_r interv aig)
       (qinterv_lit INL INL INR interv lit)) ∧
  (∀a.
     xeval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_ll_lr interv aig) a ⇔
     xeval_gate (state_pair s₀ s₁) (qinterv_l_r interv aig) a)
Proof
  Induct_on ‘aig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_ll_lr_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, var_map_base_def, state_pair_def]
    >> rpt CASE_TAC
    >> simp [xeval_lit_def]
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
      >- (CASE_TAC >> simp [xeval_lit_def, state_pair_def])
      >> simp [xeval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_and_def, AllCaseEqs()]
      >> simp [EVERY_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [xeval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [xeval_lit_def])
  >> rename1 ‘qinterv_ll_lr _ (h::_)’
  >> Cases_on ‘h’
  >> simp [qinterv_ll_lr_cons, qinterv_l_r_cons]
  >> simp [qinterv_and_def, xeval_lit_def]
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
        xeval_lit_qinterv_r_l_eq,
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
        xeval_lit_qinterv_ll_r_eq,
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
        lits_hold_def, xeval_lit_qinterv_ll_lr_eq,
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
        xeval_lit_qinterv_lr_r_eq,
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
  >> gvs [Req0 EL_MAP, lits_hold_def, xeval_lit_qinterv_lr_r_eq]
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
  >> gvs [Req0 EL_MAP, lits_hold_def, xeval_lit_qinterv_ll_lr_eq]
QED

Theorem FLAT_MAP_name_lits_flip[local]:
  FLAT (MAP ileft_name_lits xs) = ileft_name_lits (FLAT xs) ∧
  FLAT (MAP iright_name_lits xs) = iright_name_lits (FLAT xs)
Proof
  simp [ileft_name_lits_def, iright_name_lits_def, GSYM MAP_FLAT]
QED

(* Main encoder theorems ******************************************************)
*)

Definition reset_encoding_is_unsat_def:
  reset_encoding_is_unsat
    maig mreset mcnstrs mlatches
    waig wreset wcnstrs wlatches klatches
  ⇔
  (¬∃ss.
    (xeval_gate ss
       (encode_reset_cond
          maig mreset mcnstrs mlatches
          waig wreset wcnstrs wlatches klatches)
       ((Ext «reset»))))
End

Theorem xeval_gate_encode_reset_cond:
  (set klatches) = (set mlatches) ∩ (set wlatches)
  ⇒
  (reset_encoding_is_unsat
    maig mreset mcnstrs mlatches
    waig wreset wcnstrs wlatches klatches
   =
   reset_cond
     maig mreset (set mcnstrs) (set mlatches)
     waig wreset (set wcnstrs) (set wlatches))
Proof
  simp [
      reset_encoding_is_unsat_def,
      encode_reset_cond_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_lits_hold_ext,
      xeval_lit_encode_is_reset_ext,
      xis_reset_eq, xlits_hold_eq,
      reset_cond_def,
      GSYM MAP_MAP_o
    ]
  >> metis_tac []
QED

Definition transition_encoding_is_unsat_def:
  transition_encoding_is_unsat
    maig mnext mcnstrs mlatches
    waig wnext wcnstrs wlatches klatches
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_transition_cond
          maig mnext mcnstrs mlatches
          waig wnext wcnstrs wlatches klatches)
       (Ext «transition»)))
End

Theorem xeval_gate_encode_transition_cond:
  (set klatches) = (set mlatches) ∩ (set wlatches)
  ⇒
  (transition_encoding_is_unsat
    maig mnext mcnstrs mlatches
    waig wnext wcnstrs wlatches klatches ⇔
  transition_cond
    maig mnext (set mcnstrs) (set mlatches)
    waig wnext (set wcnstrs) (set wlatches))
Proof
  strip_tac
  >> simp [
      transition_encoding_is_unsat_def,
      encode_transition_cond_def,
      encode_is_next_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_lit_encode_pointwise_equal_ext_lit,
      xeval_lit_encode_lits_hold_ext,
      xeval_lit_encode_lits_hold_ext_lit,
      FORALL_STATE_PAIR,
      xeval_aig_to_xaig, xlits_hold_eq, xeval_lit_latch,
      transition_cond_def, is_next_def,
      GSYM MAP_MAP_o,
      EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS, PULL_FORALL
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

Definition safety_encoding_is_unsat_def:
  safety_encoding_is_unsat
    maig mcnstrs msafes
    waig wcnstrs wsafes
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_safety_cond
          maig mcnstrs msafes
          waig wcnstrs wsafes)
       (Ext «safety»)))
End

Theorem xeval_gate_encode_safety_cond:
  safety_encoding_is_unsat
    maig mcnstrs msafes
    waig wcnstrs wsafes
  =
  safety_cond
    maig (set msafes) (set mcnstrs)
    waig (set wsafes) (set wcnstrs)
Proof
  simp [
      safety_encoding_is_unsat_def,
      encode_safety_cond_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_lits_hold_ext,
      xeval_lit_encode_lits_hold_ext_lit,
      xlits_hold_eq,
      safety_cond_def,
      GSYM MAP_MAP_o
    ]
  >> metis_tac []
QED

Definition base_encoding_is_unsat_def:
  base_encoding_is_unsat
    waig wreset wcnstrs wsafes wlatches
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_base_cond
          waig wreset wcnstrs wsafes wlatches)
       (Ext «base»)))
End

Theorem xeval_gate_encode_base_cond:
  base_encoding_is_unsat
    waig wreset wcnstrs wsafes wlatches
  =
  base_cond
    waig wreset (set wsafes) (set wcnstrs) (set wlatches)
Proof
  simp [
      base_encoding_is_unsat_def,
      encode_base_cond_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_lits_hold_ext,
      xeval_lit_encode_is_reset_ext,
      xis_reset_eq, xlits_hold_eq,
      base_cond_def
    ]
  >> metis_tac []
QED

Definition induction_encoding_is_unsat_def:
  induction_encoding_is_unsat
    waig wnext wcnstrs wsafes wlatches
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_induction_cond
          waig wnext wcnstrs wsafes wlatches)
       (Ext «induction»)))
End

Theorem xeval_gate_encode_induction_cond:
  induction_encoding_is_unsat
    waig wnext wcnstrs wsafes wlatches
   =
  induction_cond waig wnext (set wsafes) (set wcnstrs) (set wlatches)
Proof
  simp [
      induction_encoding_is_unsat_def,
      encode_induction_cond_def,
      encode_is_next_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_lit_encode_lits_hold_ext,
      xeval_lit_encode_lits_hold_ext_lit,
      xlits_hold_eq, xeval_aig_to_xaig, eval_lit_latch,
      GSYM MAP_MAP_o,
      FORALL_STATE_PAIR,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS,
      induction_cond_def, is_next_def
    ]
  >> metis_tac []
QED

Definition liveness_encoding_is_unsat_def:
  liveness_encoding_is_unsat
    maig mcnstrs mlive
    waig wnext wcnstrs wsafes wlive wlatches interv
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_liveness_cond
          maig mcnstrs mlive
          waig wnext wcnstrs wsafes wlive wlatches interv)
       (Ext «liveness»)))
End

(*
Theorem xeval_gate_encode_liveness_cond:
  LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive
  ⇒
  liveness_encoding_is_unsat
    maig mcnstrs mlive
    waig wnext wcnstrs wsafes wlive wlatches interv
  =
  liveness_cond
    maig (set mcnstrs) (qleft maig) (qleft_live mlive)
    waig wnext (set wsafes) (set wcnstrs)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof
  strip_tac
  >> qmatch_goalsub_abbrev_tac
       ‘liveness_cond _ _ _ _ _ _ _ _ _ wlive' _’
  >> simp [
      liveness_encoding_is_unsat_def,
      encode_liveness_cond_def,
      xeval_gate_encode_imply,
      encode_is_next_def, is_next_def,
      xeval_lit_encode_lits_hold_ext,
      xeval_lit_encode_lits_hold_ext_lit,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_lit_encode_signal_imply_ext_lit,
      FORALL_STATE_PAIR,
      xlits_hold_eq, xeval_aig_to_xaig, xeval_lit_latch,
      GSYM MAP_MAP_o,
      EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> qmatch_goalsub_abbrev_tac ‘MAP left_name_lit (FLAT mlive')’
  >> have ‘LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive' wlive'’
  >- (
    fs [Abbr ‘mlive'’, Abbr ‘wlive'’, LIST_REL_EL_EQN,
        qinterv_live_l_r_def, qinterv_live_def, xqleft_live_def,
        live_map_base_def, EL_MAP]
  )
  >> have ‘LENGTH (FLAT mlive') = LENGTH (FLAT wlive')’
  >- (drule LIST_REL_LENGTH_FLAT >> simp [])
  >> simp [Req0 xeval_lit_encode_signal_imply_ext]


  >> simp [Abbr ‘mlive'’, Abbr ‘wlive'’, liveness_cond_def,
           lives_imply_signal_imply_FLAT]

  >> simp [MEM_ZIP, PULL_FORALL, PULL_eEXISTS]

  >> simp [ZIP_MAP, MEM_MAP, PULL_FORALL, PULL_EXISTS]

  >> simp [
      liveness_encoding_is_unsat_def,
      encode_liveness_cond_def,
      xeval_gate_encode_imply,
      encode_is_next_def, encode_is_next_with_def, is_next_def,
      liveness_cond_def, lives_imply_signal_imply_FLAT,
      xeval_lit_encode_lits_hold_Named,
      xeval_lit_encode_pointwise_equal_Named,
      xeval_lit_base,
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
  >> drule_all_then assume_tac xeval_lit_encode_signal_imply_Gate
  >> simp [liveness_cond_def, lives_imply_signal_imply_FLAT]
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
    waig wnext wcnstrs wsafes wlive wlatches interv
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_decrease_cond
          waig wnext wcnstrs wsafes wlive wlatches interv)
       (Named (Ext «decrease»))))
End

Theorem xeval_gate_encode_decrease_cond:
  decrease_encoding_is_unsat
    waig wnext wcnstrs wsafes wlive wlatches interv
  =
  decrease_cond
    waig wnext (set wsafes) (set wcnstrs)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof
  simp [
      decrease_encoding_is_unsat_def,
      encode_decrease_cond_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_lits_hold_Named,
      xeval_lit_encode_pointwise_equal_Named,
      encode_is_next_def, encode_is_next_with_def,
      xeval_lit_base,
      decrease_cond_def,
      is_next_def,
      FORALL_STATE_PAIR,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS
    ]
  >> qmatch_goalsub_abbrev_tac ‘encode_lives_hold _ _ wlive'’
  >> sg ‘EVERY (EVERY (λx. iname x = 0)) wlive'’
  >- (simp [Abbr ‘wlive'’, qinterv_live_r_l_def, qinterv_live_def, MEM_MAP,
            EVERY_MAP])
  >> simp [Req0 xeval_lit_encode_lives_hold_Named]
  >> simp [Abbr ‘wlive'’]
  >> simp [lives_hold_r_l_eq]
  >> metis_tac []
QED

Definition closure_encoding_is_unsat_def:
  closure_encoding_is_unsat
    waig wnext wcnstrs wsafes wlive wlatches interv
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_closure_cond
          waig wnext wcnstrs wsafes wlive wlatches interv)
       (Named (Ext «closure»))))
End

Theorem xeval_gate_encode_closure_cond:
  closure_encoding_is_unsat
    waig wnext wcnstrs wsafes wlive wlatches interv
   =
  closure_cond
    waig wnext (set wsafes) (set wcnstrs)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof
  simp [
      closure_encoding_is_unsat_def,
      encode_closure_cond_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_lits_hold_Named,
      xeval_lit_encode_pointwise_equal_Named,
      encode_is_next_def, encode_is_next_with_def,
      xeval_lit_base,
      closure_cond_def, is_next_def,
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
  >> simp [Req0 xeval_lit_encode_lives_hold_Named]
  >> simp [Abbr ‘wlive₀’, Abbr ‘wlive₁’]
  >> simp [lives_hold_ll_r_eq, lives_hold_lr_r_eq]
  >> metis_tac []
QED

Definition stable_encoding_is_unsat_def:
  stable_encoding_is_unsat
    waig wnext wcnstrs wsafes wlive wlatches interv
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_stable_cond
          waig wnext wcnstrs wsafes wlive wlatches interv)
       (Named (Ext «stable»))))
End

Theorem xeval_gate_encode_stable_cond:
  stable_encoding_is_unsat
    waig wnext wcnstrs wsafes wlive wlatches interv
   =
  stable_cond
    waig wnext (set wsafes) (set wcnstrs)
    (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof
  simp [
      stable_encoding_is_unsat_def,
      encode_stable_cond_def,
      xeval_gate_encode_imply,
      encode_is_next_with_def,
      encode_is_next_def,
      xeval_lit_encode_pointwise_equal_Named,
      xeval_lit_encode_lits_hold_Named,
      xeval_lit_base, is_next_def,
      stable_cond_def,
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
  >> simp [Req0 xeval_lit_encode_lives_hold_Named]
  >> simp [Req0 xeval_lit_encode_signal_imply_Gate]
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

Theorem latch_deps_xeval_eq:
  (∀lit.
     (∀l. MEM l (latch_deps aig lit) ⇒ (ls' l ⇔ ls l)) ⇒
     (xeval_lit (is,ls') aig lit ⇔ xeval_lit (is,ls) aig lit)) ∧
  (∀lit n b.
    (∀l. MEM l (latch_deps aig lit) ⇒ (ls' l ⇔ ls l)) ∧
    lit = (Gate n, b) ⇒
    (xeval_gate (is,ls') aig n ⇔ xeval_gate (is,ls) aig n))
Proof
  Induct_on ‘aig’ >> rw []
  >~ [‘xeval_lit _ [] _ ⇔ _’] >- suspend "xeval_lit_nil"
  >~ [‘xeval_lit _ (_::_) _ ⇔ _’] >- suspend "xeval_lit_cons"
  >~ [‘xeval_gate _ (_::_) _ ⇔ _’] >- suspend "xeval_gate_cons"
QED

Resume latch_deps_xeval_eq[xeval_lit_nil]:
  namedCases_on ‘lit’ ["v b"]
  >> reverse $ namedCases_on ‘v’ ["n", "b'"]
  >> simp [xeval_lit_def]
  >> Cases_on ‘b'’
  >> fs [xeval_lit_def, Once latch_deps_def]
QED

Resume latch_deps_xeval_eq[xeval_lit_cons]:
  namedCases_on ‘lit’ ["v b"]
  >> reverse $ namedCases_on ‘v’ ["n", "b'"]
  >- (
    Cases_on ‘b'’
    >> simp [xeval_lit_def]
    >> fs [xeval_lit_def, Once latch_deps_def]
  )
  >> simp [xeval_lit_def]
  >> rpt (pairarg_tac >> gvs [])
  >> IF_CASES_TAC >> gvs []
  >- (
    qsuff_tac
      ‘EVERY (λa. xeval_lit (is,ls') aig a) ins ⇔
         EVERY (λa. xeval_lit (is,ls) aig a) ins’
    >- simp []
    >> irule EVERY_CONG >> rw []
    >> first_x_assum irule >> rw []
    >> first_x_assum irule
    >> drule_all MEM_latch_deps_name_eq >> simp []
  )
  >> qsuff_tac ‘xeval_gate (is,ls') aig n ⇔ xeval_gate (is,ls) aig n’
  >- simp []
  >> drule_then assume_tac $
       INST_TYPE [“:γ” |-> “:β”, “:β” |-> “:γ”] latch_deps_cons_name_neq
  >> fs []
  >> qpat_x_assum ‘∀_ _. _ ⇒ (xeval_gate _ _ _ ⇔ _)’ drule
  >> simp []
QED

Resume latch_deps_xeval_eq[xeval_gate_cons]:
  simp [xeval_lit_def]
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

Finalise latch_deps_xeval_eq[local]

Theorem latch_deps_xeval_lit_eq[local] = cj 1 latch_deps_xeval_eq
Theorem latch_deps_xeval_gate_eq[local] =
  cj 2 latch_deps_xeval_eq
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
  >> irule latch_deps_xeval_lit_eq
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
    maig mreset mnext msafes mcnstrs mlive mlatches
    waig wreset wnext wsafes wcnstrs wlive wlatches
    interv klatches
  ⇔
    (reset_encoding_is_unsat
       maig mreset mcnstrs mlatches
       waig wreset wcnstrs wlatches klatches) ∧
    (transition_encoding_is_unsat
       maig mnext mcnstrs mlatches
       waig wnext wcnstrs wlatches klatches) ∧
    (safety_encoding_is_unsat
       maig mcnstrs msafes
       waig wcnstrs wsafes) ∧
    (base_encoding_is_unsat
       waig wreset wcnstrs wsafes wlatches) ∧
    (induction_encoding_is_unsat
       waig wnext wcnstrs wsafes wlatches) ∧
    (liveness_encoding_is_unsat
       maig mcnstrs mlive
       waig wnext wcnstrs wsafes wlive wlatches interv) ∧
    (decrease_encoding_is_unsat
       waig wnext wcnstrs wsafes wlive wlatches interv) ∧
    (closure_encoding_is_unsat
       waig wnext wcnstrs wsafes wlive wlatches interv) ∧
    (stable_encoding_is_unsat
       waig wnext wcnstrs wsafes wlive wlatches interv)
End

(** dep_model *****************************************************************)

(* dep_aig *)

Definition dep_cond_def:
  dep_cond aig reset next safes cnstrs live latches ⇔
    set (aig_latches aig) ⊆ set latches ∧
    BIGUNION (IMAGE (set ∘ lit_latches ∘ next) (set latches)) ⊆ set latches ∧
    BIGUNION (IMAGE (set ∘ lit_latches) (set safes)) ⊆ set latches ∧
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
  dep_cond maig mreset mnext msafes mcnstrs mlive mlatches ∧
  encodings_unsat
    maig mreset mnext msafes mcnstrs mlive mlatches
    waig wreset wnext wsafes wcnstrs wlive wlatches
    interv klatches
  ⇒
  is_safe
    maig mreset mnext (set mcnstrs) (set mlatches) (set msafes) ∧
  is_live
    maig mreset mnext (set mcnstrs) (qleft maig)
    (IMAGE set (set (qleft_live mlive))) (set mlatches)
Proof
  strip_tac
  >> sg
       ‘is_witness
          maig mreset mnext (set msafes) (set mcnstrs)
          (qleft maig) (qleft_live mlive) (set mlatches)
          waig wreset wnext (set wsafes) (set wcnstrs)
          (qinterv_l_r interv waig) (qinterv_live_l_r interv wlive)
          (set wlatches)’
  >- (
    rewrite_tac [is_witness_def, simulates_def, is_inductive_def, is_ranked_def]
    >> MAP_EVERY (irule_at Any o iffLR) [
         xeval_gate_encode_reset_cond,
         xeval_gate_encode_transition_cond,
         xeval_gate_encode_safety_cond,
         xeval_gate_encode_base_cond,
         xeval_gate_encode_induction_cond,
         xeval_gate_encode_liveness_cond,
         xeval_gate_encode_decrease_cond,
         xeval_gate_encode_closure_cond,
         xeval_gate_encode_stable_cond,
       ]
    >> qexistsl [‘klatches’, ‘klatches’]
    >> fs [encodings_unsat_def]
  )
  >> sg
     ‘∃minput.
        dep_model maig mreset mnext (set msafes) (set mcnstrs) minput
          (set mlatches) ∧
        dep_qaig minput (qleft maig) (qleft_live mlive) (set mlatches)’
  >- (
    qabbrev_tac
      ‘minput =
         set (aig_inputs maig) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs ∘ mnext) (set mlatches)) ∪
         BIGUNION
           (IMAGE (set ∘ lit_inputs) (IMAGE_PARTIAL mreset (set mlatches))) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs) (set msafes)) ∪
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
  >> sg ‘FINITE (set wlatches)’ >- simp []
  >> drule_all stratified_cond_is_stratified >> strip_tac
  >> drule_all_then assume_tac is_witness_is_safe_and_livee
  >> simp []
QED
*)

(*
  Encodes the certificate conditions as an extended AIG.
*)
Theory xaig_cert_encode
Ancestors
  aig xaig xaig_cert
  (* TODO maybe should move; is for stratification *)
  topological_sort
Libs
  preamble

(* todo clean out commented out parts *)

(* todo check which theorems/simps are actually used *)
(* todo check whether it is possible to reduce the amount of
   definitions/theorems *)
(* todo can we clean up/reduce duplication (e.g. mapping over datatypes),
   simpler theorems/proofs *)

(* todo once this version works, we could simplify aig to be over two inputs *)

(* todo are the wrappers like iright_name_lits really useful,
   or could things be simplified by removing them *)

(* todo left_name -> left_merge; left_lit -> left_pair? *)

(* todo instead of xaig -> xaig in each condition, we should make a new predicate
     that says the xaig is equivalent to original xaig; can probably
     delete the xaig_to_xaig specific thms from the proofs in that case *)

(* todo the names are inconsistent;
   - xaig/xaig
   - x-prefix (e.g. we have encode_xis_reset instead of encode_xxis_reset)
   - xeval_gate_encode_base_cond <- those theorems dont mention eval_gate directly anymore
 *)

(* TODO upstream *)
(*
Theorem MAPi_MAP:
  ∀l f g. MAPi f (MAP g l) = MAPi (λi a. f i (g a)) l
Proof
  Induct >> rw []
  >> have ‘(λi a. f (SUC i) (g a)) = ((λi a. f i (g a)) ∘ SUC)’
  >- simp [FUN_EQ_THM]
  >> simp []
QED
*)

Theorem xeval_lit_latch:
  xeval_lit ss xaig (Base (Latch l), b) ⇔ (b ⇎ SND ss l)
Proof
  Cases_on ‘ss’ >> simp [xeval_lit_def]
QED

(* Merging xAIGs ***************************************************************)
(* Merging two xAIGs results in a new xAIG where the inputs and latches
   are shared. *)

Definition left_name_lit_def:
  left_name_lit = lit_map I I INL
End

Definition right_name_lit_def:
  right_name_lit = lit_map I I INR
End

Definition merge_xaigs_def:
  merge_xaigs (xaig₁: ('a1, 'i, 'l) xaig) (xaig₂: ('a2, 'i, 'l) xaig) =
    (xaig_map I I INL xaig₁ ++ xaig_map I I INR xaig₂)
    :('a1 + 'a2, 'i, 'l) xaig
End

Theorem xeval_gate_merge_xaigs_left_nil_INL[local]:
  ¬xeval_gate ss (merge_xaigs [] xaig) (INL n)
Proof
  Induct_on ‘xaig’
  >> gvs [merge_xaigs_def, xaig_map_def]
  >> Cases >> simp [gate_map_def, xeval_lit_def]
QED

Theorem xeval_lit_merge_xaigs_left_nil_left[local]:
  xeval_lit ss (merge_xaigs [] xaig) (left_name_lit m) ⇔
  xeval_lit ss [] m
Proof
  Induct_on ‘xaig’
  >> gvs [merge_xaigs_def, xaig_map_def,
          oneline left_name_lit_def, oneline lit_map_def,
          oneline var_map_def, oneline bvar_map_def]
  >> every_case_tac
  >> gvs [xeval_lit_def]
  >> Cases >> simp [gate_map_def, xeval_lit_def]
QED

Theorem xeval_gate_merge_xaigs_left_nil_INR[local]:
  (∀n.
     xeval_gate ss (merge_xaigs ([]: ('a, 'i, 'l) xaig) xaig) (INR n) =
     xeval_gate ss xaig n) ∧
  (∀m.
     xeval_lit ss (merge_xaigs ([]: ('a, 'i, 'l) xaig) xaig) (right_name_lit m) =
     xeval_lit ss xaig m)
Proof
  simp [merge_xaigs_def, right_name_lit_def]
  >> namedCases_on ‘ss’ ["is ls"]
  >> mp_tac $
       INST_TYPE [“:α” |-> “:ι”, “:β” |-> “:ι”, “:γ” |-> “:μ”,
                  “:δ” |-> “:μ”, “:ε” |-> “:β”, “:ζ” |-> “:α + β”] xaig_map_eq
  >> disch_then $
       qspecl_then
         [‘xaig’, ‘I’, ‘I’, ‘INR’, ‘is’, ‘is’, ‘ls’, ‘ls’]
         mp_tac
  >> impl_tac
  >> simp [INJ_I, INJ_INR]
QED

Theorem xeval_gate_merge_xaigs_left[simp]:
  (∀n.
     xeval_gate ss (merge_xaigs xaig₁ xaig₂) (INL n) =
     xeval_gate ss xaig₁ n) ∧
  (∀m.
     xeval_lit ss (merge_xaigs xaig₁ xaig₂) (left_name_lit m) =
     xeval_lit ss xaig₁ m)
Proof
  Induct_on ‘xaig₁’ >> rw []
  >- simp [xeval_gate_merge_xaigs_left_nil_INL]
  >- simp [xeval_lit_merge_xaigs_left_nil_left]
  >> gvs [merge_xaigs_def, xaig_map_cons, left_name_lit_def, xeval_lit_def]
  >- (
    simp [oneline gate_map_def] >> CASE_TAC >> simp []
    >> IF_CASES_TAC >> gvs []
    >> simp [oneline gty_map_def] >> CASE_TAC >> simp []
    >> simp [EVERY_MAP, EXISTS_MAP]
  )
  >> simp [oneline lit_map_def, oneline var_map_def, oneline bvar_map_def]
  >> every_case_tac >> simp [xeval_lit_def]
  >> simp [oneline gate_map_def] >> CASE_TAC >> simp []
  >> IF_CASES_TAC >> gvs []
  >> simp [oneline gty_map_def] >> CASE_TAC >> simp []
  >> simp [EVERY_MAP, EXISTS_MAP]
QED

Theorem xeval_gate_merge_xaigs_right[simp]:
  (∀n.
     xeval_gate ss (merge_xaigs xaig₁ xaig₂) (INR n) =
     xeval_gate ss xaig₂ n) ∧
  (∀m.
     xeval_lit ss (merge_xaigs xaig₁ xaig₂) (right_name_lit m) =
     xeval_lit ss xaig₂ m)
Proof
  Induct_on ‘xaig₁’ >> rw []
  >- simp [xeval_gate_merge_xaigs_left_nil_INR]
  >- simp [xeval_gate_merge_xaigs_left_nil_INR]
  >> gvs [merge_xaigs_def, xaig_map_cons, left_name_lit_def, xeval_lit_def]
  >- (simp [oneline gate_map_def] >> CASE_TAC >> simp [])
  >> simp [right_name_lit_def, oneline lit_map_def, oneline var_map_def,
           oneline bvar_map_def]
  >> every_case_tac >> simp [xeval_lit_def]
  >> simp [oneline gate_map_def] >> CASE_TAC >> simp []
QED

(* Pairing xAIGs ***************************************************************)

(* Combines two xAIGs into one, keeping them separate using the sum type. *)

Definition left_lit_def:
  left_lit = lit_map INL INL INL
End

Definition right_lit_def:
  right_lit = lit_map INR INR INR
End

Definition pair_xaigs_def:
  pair_xaigs (xaig₁: ('a1, 'i1, 'l1) xaig) (xaig₂: ('a2, 'i2, 'l2) xaig) =
    xaig_map INL INL INL xaig₁ ++ xaig_map INR INR INR xaig₂
End

Theorem xeval_gate_pair_left_nil_INL[local]:
  ¬xeval_gate ss (pair_xaigs [] xaig) (INL n)
Proof
  Induct_on ‘xaig’ >> rw []
  >> gvs [pair_xaigs_def, xeval_lit_def, xaig_map_cons]
  >> simp [oneline gate_map_def] >> CASE_TAC >> simp []
QED

Theorem xeval_gate_pair_left_nil_INR[local]:
  (∀n.
     xeval_gate (state_pair ss₁ ss₂)
       (pair_xaigs ([]: ('a, 'i, 'l) xaig) xaig) (INR n) =
     xeval_gate ss₂ xaig n) ∧
  (∀m.
     xeval_lit (state_pair ss₁ ss₂)
       (pair_xaigs ([]: ('a, 'i, 'l) xaig) xaig) (right_lit m) =
     xeval_lit ss₂ xaig m)
Proof
  Induct_on ‘xaig’ >> rw []
  >> gvs [pair_xaigs_def, right_lit_def, xaig_map_cons]
  >- (
    simp [pair_xaigs_def, right_lit_def]
    >> simp [oneline lit_map_def, oneline var_map_def, oneline bvar_map_def,
             oneline state_pair_def]
    >> every_case_tac
    >> simp [xeval_lit_def]
  )
  >- (
    simp [xeval_lit_def, oneline gate_map_def]
    >> CASE_TAC >> simp [xeval_lit_def]
    >> IF_CASES_TAC >> gvs []
    >> simp [oneline gty_map_def] >> CASE_TAC
    >> simp [EVERY_MAP, EXISTS_MAP]
  )
  >> simp [oneline lit_map_def, oneline var_map_def, oneline bvar_map_def]
  >> every_case_tac
  >- (
    simp [oneline gate_map_def, oneline gty_map_def]
    >> every_case_tac >> simp [xeval_lit_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP, EXISTS_MAP]
  )
  >> simp [oneline state_pair_def]
  >> every_case_tac
  >> simp [xeval_lit_def]
QED

Theorem xeval_lit_pair_left_nil_left[local]:
  xeval_lit (state_pair ss₁ ss₂) (pair_xaigs [] xaig₂) (left_lit n) =
  xeval_lit ss₁ [] n
Proof
  Cases_on ‘ss₁’ >> Cases_on ‘ss₂’ >> simp [state_pair_def]
  >> Induct_on ‘xaig₂’
  >> gvs [pair_xaigs_def, left_lit_def, oneline lit_map_def, oneline var_map_def,
          oneline bvar_map_def, xaig_map_cons]
  >> every_case_tac
  >> gvs [xeval_lit_def]
  >> strip_tac
  >> simp [oneline gate_map_def, oneline gty_map_def]
  >> every_case_tac >> simp [xeval_lit_def]
QED

Theorem xeval_pair_left[simp]:
  (∀n.
     xeval_gate (state_pair ss₁ ss₂) (pair_xaigs xaig₁ xaig₂) (INL n) =
     xeval_gate ss₁ xaig₁ n) ∧
  (∀m.
     xeval_lit (state_pair ss₁ ss₂) (pair_xaigs xaig₁ xaig₂) (left_lit m) =
     xeval_lit ss₁ xaig₁ m)
Proof
  Induct_on ‘xaig₁’ >> rw [xeval_lit_def]
  >- simp [xeval_gate_pair_left_nil_INL]
  >- simp [xeval_lit_pair_left_nil_left]
  >> gvs [pair_xaigs_def, xaig_map_cons, left_lit_def]
  >- (
    simp [oneline gate_map_def, oneline gty_map_def]
    >> every_case_tac >> simp [xeval_lit_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP, EXISTS_MAP]
  )
  >> simp [oneline lit_map_def, oneline var_map_def, oneline bvar_map_def]
  >> every_case_tac
  >- (
    simp [xeval_lit_def]
    >> simp [oneline gate_map_def, oneline gty_map_def]
    >> every_case_tac >> simp [xeval_lit_def]
    >> IF_CASES_TAC >> gvs [EVERY_MAP, EXISTS_MAP]
  )
  >> simp [oneline state_pair_def]
  >> every_case_tac
  >> simp [xeval_lit_def]
QED

Theorem xeval_pair_right[simp]:
  (∀n.
    xeval_gate (state_pair ss₁ ss₂) (pair_xaigs xaig₁ xaig₂) (INR n) =
    xeval_gate ss₂ xaig₂ n) ∧
  (∀m.
    xeval_lit (state_pair ss₁ ss₂) (pair_xaigs xaig₁ xaig₂) (right_lit m) =
    xeval_lit ss₂ xaig₂ m)
Proof
  Induct_on ‘xaig₁’ >> rw [xeval_lit_def]
  >- simp [xeval_gate_pair_left_nil_INR]
  >- simp [xeval_gate_pair_left_nil_INR]
  >> gvs [pair_xaigs_def, xaig_map_cons, right_lit_def]
  >- (
    simp [oneline gate_map_def, oneline gty_map_def]
    >> every_case_tac >> simp [xeval_lit_def]
  )
  >> simp [oneline gate_map_def, oneline lit_map_def,
           oneline var_map_def, oneline bvar_map_def]
  >> every_case_tac >> simp [xeval_lit_def]
  >> simp [oneline state_pair_def]
  >> every_case_tac
  >> simp [xeval_lit_def]
QED

(** Intervention **************************************************************)

(* Liveness xAIGs (qxaig) have access to two different states.
   Model xAIGs do not need this, thus inputs and outputs (not gates) can be
   simply lifted to INL.
   In contrast, witness xAIGs need to make use of this. For this, the
   intervention function maps literals to latches in the other state.
   Thus, we go through the xAIG and for each literal present as a key in the
   intervention map, we replace it by g x, where x is the value in the
   intervention map.
   If the literal is not present, we lift inputs/outputs to f.
   In the simplest case, f = INL and g = INR. To encode the decreases property,
   these are flipped, and in the presence of three states (as in stable),
   we need to nest the constructors. *)

(* f/g indicate the namespace the first copy of input/latches should be mapped
   to. h indicates the second copy of latches intervened literals should be
   mapped to. *)
Definition qinterv_lit_def:
  qinterv_lit f g h i (interv: ('a, 'i, 'l) var -> ('l # bool) option) lit =
  let (v, b) = lit in
    case interv v of
    | NONE => lit_map f g h lit
    | SOME (l, b') =>
      (* if the intervened literal and the key in interv have different
         polarity, make sure result has negative polarity *)
        (Base (Latch (i l)), b ≠ b')
End

Definition qinterv_gty_def:
  qinterv_gty f g h i interv (And xs) =
    And (MAP (qinterv_lit f g h i interv) xs) ∧
  qinterv_gty f g h i interv (Xor x₀ x₁) =
    Xor (qinterv_lit f g h i interv x₀) (qinterv_lit f g h i interv x₁) ∧
  qinterv_gty f g h i interv (Ite cnd thn els) =
    Ite
      (qinterv_lit f g h i interv cnd)
      (qinterv_lit f g h i interv thn)
      (qinterv_lit f g h i interv els) ∧
  qinterv_gty f g h i interv (Or xs) =
    Or (MAP (qinterv_lit f g h i interv) xs)
End

Definition qinterv_gate_def:
  qinterv_gate f g h i interv ((n, gty): ('a, 'i, 'l) gate) =
    (h n, qinterv_gty f g h i interv gty)
End

Definition qinterv_live_def:
  qinterv_live f g h i interv (live: ('a, 'i, 'l) lit list list) =
    MAP (MAP (qinterv_lit f g h i interv)) live
End

Definition qinterv_def:
  qinterv f g h i interv (xaig: ('a, 'i, 'l) xaig) =
    MAP (qinterv_gate f g h i interv) xaig
End

(** Specialized versions of the functions above. ******************************)

Theorem dep_xaig_pair_qxleft:
  dep_xaig (pair_set minput) (pair_set (set mlatches)) (qxleft mxaig) =
  dep_xaig minput (set mlatches) mxaig
Proof
  simp [dep_xaig_def, FORALL_STATE_PAIR, agree_on_pair,
        xeval_gate_pair_qxleft]
  >> metis_tac []
QED

Definition qinterv_l_r_def:
  qinterv_l_r interv (xaig: ('a, 'i, 'l) xaig) =
    qinterv INL INL I INR interv xaig
End

Definition qinterv_live_l_r_def:
  qinterv_live_l_r interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live INL INL I INR interv live
End

Definition qinterv_live_r_l_def:
  qinterv_live_r_l interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live INR INR I INL interv live
End

Definition qinterv_live_ll_r_def:
  qinterv_live_ll_r interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live (INL ∘ INL) (INL ∘ INL) I INR interv live
End

Definition qinterv_live_ll_lr_def:
  qinterv_live_ll_lr interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live (INL ∘ INL) (INL ∘ INL) I (INL ∘ INR) interv live
End

Definition qinterv_live_lr_r_def:
  qinterv_live_lr_r interv (live: ('a, 'i, 'l) lit list list) =
    qinterv_live (INL ∘ INR) (INL ∘ INR) I INR interv live
End

Definition qinterv_r_l_def:
  qinterv_r_l interv (xaig: ('a, 'i, 'l) xaig) =
    qinterv INR INR I INL interv xaig
End

Definition qinterv_ll_r_def:
  qinterv_ll_r interv (xaig: ('a, 'i, 'l) xaig) =
    qinterv (INL ∘ INL) (INL ∘ INL) I INR interv xaig
End

Definition qinterv_ll_lr_def:
  qinterv_ll_lr interv (xaig: ('a, 'i, 'l) xaig) =
    qinterv (INL ∘ INL) (INL ∘ INL) I (INL ∘ INR) interv xaig
End

Definition qinterv_lr_r_def:
  qinterv_lr_r interv (xaig: ('a, 'i, 'l) xaig) =
    qinterv (INL ∘ INR) (INL ∘ INR) I INR interv xaig
End

(* Extending an xaig **********************************************************)

(* Names of extensions. *)
Datatype:
  ext_name =
    Mreset | Mcnstrs0 | Mcnstrs1 | Msafes | Mnext
  | Wreset | Wcnstrs0 | Wcnstrs1 | Wcnstrs2 | Wsafes0 | Wsafes1 | Wsafes2
  | Wnext0 | Wnext1
  | Lives_imply | Lives_hold10 | Lives_hold01 | Lives_hold12 | Lives_hold02
  | Reset | Transition | Safety | Base | Induction | Liveness | Decrease
  | Closure | Stable
End

val ext_name_count =
  TypeBase.constructors_of “:ext_name” |> length |> numSyntax.term_of_int

val ext_name2num_11 = theorem "ext_name2num_11"
val ext_name2num_thm = theorem "ext_name2num_thm"

Datatype:
  ext = Orig 'a | Ext ext_name | Anon num
End

(* Lifting to gate names to ext *)

Definition ext_lit_def:
  ext_lit = lit_map I I Orig
End

Definition ext_xaig_def:
  ext_xaig (xaig: ('a, 'i, 'l) xaig) = MAP (gate_map I I Orig) xaig
End

Theorem xeval_lit_Ext_ext_lit[simp]:
  xeval_lit ss ((Ext name,lits)::xaig) (ext_lit x) ⇔
  xeval_lit ss xaig (ext_lit x)
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [ext_lit_def, lit_map_def, var_map_def, xeval_lit_def]
QED

Theorem xeval_lit_Anon_ext_lit[simp]:
  xeval_lit ss ((Anon n,lits)::xaig) (ext_lit x) ⇔
  xeval_lit ss xaig (ext_lit x)
Proof
  namedCases_on ‘x’ ["v b"]
  >> Cases_on ‘v’
  >> simp [ext_lit_def, lit_map_def, var_map_def, xeval_lit_def]
QED

Theorem xeval_gate_ext_xaig[simp]:
  (∀n. xeval_gate ss (ext_xaig xaig) (Orig n) = xeval_gate ss xaig n) ∧
  (∀l. xeval_lit  ss (ext_xaig xaig) (ext_lit l) = xeval_lit ss xaig l) ∧
  (∀l. xeval_lit  ss (ext_xaig xaig) (Base bv, b) = xeval_lit ss xaig (Base bv, b))
Proof
  Induct_on ‘xaig’ >> rw [ext_xaig_def, xeval_lit_def, ext_lit_def]
  >-
   (Cases_on ‘l’
    >> simp [lit_map_def, oneline var_map_def, oneline bvar_map_def]
    >> every_case_tac >> gvs []
    >> simp [xeval_lit_def])
  >- (
    simp [oneline gate_map_def]
    >> CASE_TAC >> simp []
    >> IF_CASES_TAC >> simp []
    >> simp [oneline gty_map_def]
    >> CASE_TAC >> gvs [EVERY_MAP, EXISTS_MAP]
  )
  >> Cases_on ‘l’
  >> simp [lit_map_def, oneline var_map_def, oneline bvar_map_def]
  >> every_case_tac >> gvs []
  >> simp [xeval_lit_def]
  >> simp [oneline gate_map_def]
  >> CASE_TAC >> simp []
  >> IF_CASES_TAC >> simp []
  >> simp [oneline gty_map_def]
  >> CASE_TAC >> gvs [EVERY_MAP, EXISTS_MAP]
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
  >> simp [ext_lit_def, lit_map_def, var_map_def, iname_def]
QED

Theorem xeval_lit_Anon_neq:
  iname m ≠ n ⇒
  (xeval_lit ss ((Anon n, xs)::xaig) m ⇔ xeval_lit ss xaig m)
Proof
  simp [oneline iname_def] >> every_case_tac >> rw [xeval_lit_def]
QED

(* Getting the next available number to use as intermediate *)
Definition maxn_def:
  maxn (ls : ('a ext,'i,'l) lit list) =
    MAX_LIST (MAP iname ls) + 1
End

Theorem maxn_cons_leq:
  maxn (x::xs) ≤ n ⇔ iname x < n ∧ maxn xs ≤ n
Proof
  simp [maxn_def, MAX_DEF]
QED

Theorem maxn_every_iname:
  maxn xs ≤ n ⇒ EVERY (λx. iname x < n) xs
Proof
  Induct_on ‘xs’ >- simp [maxn_def]
  >> rw [maxn_cons_leq]
QED

Theorem maxn_append_leq:
  maxn (xs ++ ys) ≤ n ⇔ maxn xs ≤ n ∧ maxn ys ≤ n
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
  encode_imply name b lhss rhss =
  let n = MAX (maxn lhss) (maxn rhss) in [
    (Ext name, And [(Gate (Anon (n+2)), b)]);
    (* We use Or over ITE; otherwise, ITE forces the condition into both
       polarities and we lose PG's savings. *)
    (Anon (n + 2), Or [(Gate (Anon (n+1)), T); (Gate (Anon n), F)]);
    (Anon (n + 1), And lhss);
    (Anon n, And rhss)
    ]
End

Theorem xeval_gate_encode_imply:
  xeval_gate ss (encode_imply name b lhss rhss ++ xaig) (Ext n) =
  if n = name then
    (b ⇎ ((EVERY (xeval_lit ss xaig) lhss) ⇒ (EVERY (xeval_lit ss xaig) rhss)))
  else xeval_gate ss xaig (Ext n)
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
  encode_pointwise_equal name xys =
  let
    n = MAX (maxn (MAP FST xys)) (maxn (MAP SND xys));
    xor_gates = MAPi (xori n) xys;
    xnor_lits = And (GENLIST (λi. (Gate (Anon (i + n)), T)) (LENGTH xys));
  in
    (Ext name, xnor_lits)::xor_gates
End

Theorem xeval_gate_encode_pointwise_equal_ext:
  xeval_gate ss (encode_pointwise_equal name xys ++ xaig) (Ext n) =
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
  xeval_lit ss (encode_pointwise_equal name xys ++ xaig) (Gate (Ext n), b) =
  if n = name then
    b ⇎ EVERY (λ(x,y). xeval_lit ss xaig x ⇔ xeval_lit ss xaig y) xys
  else xeval_lit ss xaig (Gate (Ext n), b)
Proof
  simp [xeval_lit_def, xeval_gate_encode_pointwise_equal_ext]
  >> IF_CASES_TAC >> gvs []
QED

Theorem xeval_lit_encode_pointwise_equal_ext_lit:
  xeval_lit ss (encode_pointwise_equal name xys ++ xaig) (ext_lit n) =
  xeval_lit ss xaig (ext_lit n)
Proof
  namedCases_on ‘n’ ["v b"] >> Cases_on ‘v’
  >> simp [ext_lit_def, lit_map_def, var_map_def, encode_pointwise_equal_def, xeval_lit_def,
           xeval_gate_xori_orig]
QED

(* Encoding point-wise implication ********************************************)

Definition impi_def:
  impi n i (x, y) : ('a ext, 'i, 'l) gate = (Anon (i + n), Or [not x; y])
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
  >- gvs [Req0 iname_xeval_lit_impi, IMP_DISJ_THM, xeval_lit_not]
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
  encode_pointwise_imply name xys =
  let
    n = MAX (maxn (MAP FST xys)) (maxn (MAP SND xys));
    imp_gates = MAPi (impi n) xys;
    gty = And (GENLIST (λi. (Gate (Anon (i + n)), F)) (LENGTH xys));
  in
    (Ext name, gty)::imp_gates
End

Theorem xeval_gate_encode_pointwise_imply_ext:
  xeval_gate ss (encode_pointwise_imply name xys ++ xaig) (Ext n) =
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
  xeval_lit ss (encode_pointwise_imply name xys ++ xaig) (Gate (Ext n), b) =
  if n = name then
    b ⇎ EVERY (λ(x,y). xeval_lit ss xaig x ⇒ xeval_lit ss xaig y) xys
  else xeval_lit ss xaig (Gate (Ext n), b)
Proof
  simp [xeval_lit_def, xeval_gate_encode_pointwise_imply_ext]
  >> IF_CASES_TAC >> gvs []
QED

Theorem xeval_lit_encode_pointwise_imply_ext_lit:
  xeval_lit ss (encode_pointwise_imply name xys ++ xaig) (ext_lit n) =
  xeval_lit ss xaig (ext_lit n)
Proof
  namedCases_on ‘n’ ["v b"] >> Cases_on ‘v’
  >> simp [ext_lit_def, lit_map_def, var_map_def, encode_pointwise_imply_def, xeval_lit_def,
           xeval_gate_impi_orig]
QED

(* Encoding xis_reset **********************************************************)

Definition latch_reset_pairs_def:
  (latch_reset_pairs (reset: 'l -> ('a ext,'i,'l) lit option) ([]: 'l list) = []) ∧
  (latch_reset_pairs reset (l::ls) =
     case reset l of
     | NONE   => latch_reset_pairs reset ls
     | SOME r => ((Base (Latch l), F), r) :: latch_reset_pairs reset ls)
End

Definition encode_xis_reset_def:
  encode_xis_reset name reset ls =
  encode_pointwise_equal name (latch_reset_pairs reset ls)
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

Theorem xeval_gate_encode_xis_reset_ext:
  xeval_gate ss (encode_xis_reset name reset ls ++ xaig) (Ext n) =
  if n = name then
    xis_reset ss xaig reset (set ls)
  else xeval_gate ss xaig (Ext n)
Proof
  Cases_on ‘ss’
  >> rw [xeval_lit_def, encode_xis_reset_def, xeval_gate_encode_pointwise_equal_ext]
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

Theorem xeval_lit_encode_xis_reset_ext:
  xeval_lit ss (encode_xis_reset name reset ls ++ xaig) (Gate (Ext n),F) =
  if n = name then
    xis_reset ss xaig reset (set ls)
  else xeval_lit ss xaig (Gate (Ext n),F)
Proof
  simp [xeval_lit_def, xeval_gate_encode_xis_reset_ext]
QED

(* Encoding xlits_hold *********************************************************)

Definition encode_xlits_hold_def:
  encode_xlits_hold name (lits: ('a ext,'i,'l) lit list) = [(Ext name, And lits)]
End

Theorem xeval_lit_encode_xlits_hold_ext:
  xeval_lit ss (encode_xlits_hold name lits ++ xaig) (n,F) =
  if n = Gate (Ext name) then
    xlits_hold ss xaig (set lits)
  else xeval_lit ss xaig (n,F)
Proof
  simp [encode_xlits_hold_def, xeval_lit_def, xlits_hold_def, EVERY_MEM]
  >> IF_CASES_TAC >> gvs []
  >> TOP_CASE_TAC >> gvs []
QED

Theorem xeval_lit_encode_xlits_hold_ext_lit:
  xeval_lit ss (encode_xlits_hold name lits ++ xaig) (ext_lit lit) =
  xeval_lit ss xaig (ext_lit lit)
Proof
  simp [encode_xlits_hold_def]
QED

Theorem xeval_gate_encode_xlits_hold_ext:
  xeval_gate ss (encode_xlits_hold name lits ++ xaig) (Ext n) =
  if n = name then
    xlits_hold ss xaig (set lits)
  else xeval_gate ss xaig (Ext n)
Proof
  simp [encode_xlits_hold_def, xeval_lit_def, xlits_hold_def, EVERY_MEM]
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

(* Encoding xis_next ***********************************************************)

(* cur = "path" to literals in the current state; nxt = "path" to next state *)
Definition encode_xis_next_def:
  encode_xis_next name cur nxt next latches =
    encode_pointwise_equal name
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
    lives_imply ss₀ ss₁ wqxaig mqxaig wlive mlive =
    (signal_imply ss₀ wqxaig ss₁ mqxaig (FLAT wlive) (FLAT mlive) ∧
     LIST_REL (λQ Q'. LENGTH Q = LENGTH Q') mlive wlive)
Proof
  simp [lives_imply_def, signal_imply_def]
  >> qmatch_goalsub_abbrev_tac ‘LIST_REL (λQ Q'. LIST_REL R Q Q')’
  >> ‘(λQ Q'. LIST_REL R Q Q') = LIST_REL R’ by simp [FUN_EQ_THM]
  >> simp [LIST_REL_FLAT]
  >> simp [LIST_REL_EL_EQN]  (* must be separate from LIST_REL_FLAT *)
  >> metis_tac []
QED

Definition encode_signal_imply_def:
  encode_signal_imply name xs ys =
    encode_pointwise_imply name (ZIP (xs, ys))
End

Theorem xeval_lit_encode_signal_imply_ext:
  LENGTH signals' = LENGTH signals ⇒
  xeval_lit ss (encode_signal_imply name signals signals' ++ xaig)
    (Gate (Ext n), b) =
  if n = name then
    (b ⇎ signal_imply ss xaig ss xaig signals signals')
  else xeval_lit ss xaig (Gate (Ext n), b)
Proof
  strip_tac
  >> simp [encode_signal_imply_def, xeval_lit_encode_pointwise_imply_ext,
           signal_imply_def, xlits_hold_def, LIST_REL_EVERY]
QED

Theorem xeval_lit_encode_signal_imply_ext_lit:
  xeval_lit ss (encode_signal_imply name signals signals' ++ xaig) (ext_lit n) =
  xeval_lit ss xaig (ext_lit n)
Proof
  simp [encode_signal_imply_def, xeval_lit_encode_pointwise_imply_ext_lit]
QED

(* Encoding lives_hold ********************************************************)

Definition ori_def:
  ori n i xs : ('a ext, 'i, 'l) gate = (Anon (i + n), Or xs)
End

Theorem ori_suc:
  ori n ∘ SUC = ori (n + 1)
Proof
  simp [FUN_EQ_THM] >> rpt Cases >> gvs [ori_def]
QED

Theorem iname_xeval_lit_ori:
  ∀xys n.
    iname x < n ⇒
    (xeval_lit ss (MAPi (ori n) xys ++ xaig) x ⇔ xeval_lit ss xaig x)
Proof
  Induct >> rw []
  >> rename1 ‘ori _ _ g’ >> Cases_on ‘g’
  >> simp [ori_def, ori_suc, xeval_lit_Anon_neq]
QED

Theorem xeval_gate_ori_anon:
  ∀xss n i.
    i < LENGTH xss ∧
    maxn (FLAT xss) ≤ n
    ⇒
    (xeval_gate ss (MAPi (ori n) xss ++ xaig) (Anon (i + n)) ⇔
       EXISTS (xeval_lit ss xaig) xss❲i❳)
Proof
  Induct >> rw [ori_def, ori_suc]
  >> Cases_on ‘i’ >> simp [xeval_lit_def]
  >- (
    irule EXISTS_CONG >> rw []
    >> irule iname_xeval_lit_ori
    >> rename1 ‘MEM x _’
    >> suff ‘iname x < n’ >- simp []
    >> imp_res_tac maxn_every_iname
    >> gvs [EVERY_MEM]
  )
  >> rename1 ‘Anon (n + SUC i)’
  >> first_x_assum $ qspecl_then [‘n + 1’, ‘i’] mp_tac
  >> impl_tac >- fs [maxn_append_leq]
  >> simp [ADD1]
QED

Theorem xeval_gate_ori_ext:
  ∀xys n.
    xeval_gate ss (MAPi (ori n) xys ++ xaig) (Ext name) ⇔
    xeval_gate ss xaig (Ext name)
Proof
  Induct >> rw []
  >> rename1 ‘ori _ _ g’ >> Cases_on ‘g’
  >> simp [ori_def, ori_suc, xeval_lit_def]
QED

Theorem xeval_gate_ori_orig:
  ∀xys n.
    xeval_gate ss (MAPi (ori n) xys ++ xaig) (Orig a) ⇔
    xeval_gate ss xaig (Orig a)
Proof
  Induct >> rw []
  >> rename1 ‘ori _ _ g’ >> Cases_on ‘g’
  >> simp [ori_def, ori_suc, xeval_lit_def]
QED

Definition encode_lives_hold_def:
  encode_lives_hold name xss =
  let
    n = maxn (FLAT xss);
    ori_gates = MAPi (ori n) xss;
    gty = And (GENLIST (λi. (Gate (Anon (i + n)), F)) (LENGTH xss));
  in
    (Ext name, gty)::ori_gates
End

Theorem xeval_gate_encode_lives_hold_ext:
  xeval_gate ss (encode_lives_hold name live ++ xaig) (Ext n) =
  if n = name then lives_hold ss xaig live
  else xeval_gate ss xaig (Ext n)
Proof
  rw [xeval_lit_def, encode_lives_hold_def]
  >- (
    eq_tac
    >> simp [lives_hold_def]
    >> rw [EVERY_EL]
    >> fs [some_signal_holds_def, xlits_hold_def]
    >> first_x_assum $ drule_then assume_tac
    >> gvs [xeval_lit_def, Req0 xeval_gate_ori_anon]
    >> gvs [EXISTS_MEM] >> metis_tac []
  )
  >> simp [xeval_gate_ori_ext]
QED

Theorem xeval_lit_encode_lives_hold_ext:
  xeval_lit ss (encode_lives_hold name live ++ xaig) (Gate (Ext n), b) =
  if n = name then
    b ⇎ lives_hold ss xaig live
  else xeval_lit ss xaig (Gate (Ext n), b)
Proof
  simp [xeval_lit_def, xeval_gate_encode_lives_hold_ext]
  >> IF_CASES_TAC >> gvs []
QED

Theorem xeval_lit_encode_lives_hold_ext_lit:
  xeval_lit ss (encode_lives_hold name xys ++ xaig) (ext_lit n) =
  xeval_lit ss xaig (ext_lit n)
Proof
  namedCases_on ‘n’ ["v b"] >> Cases_on ‘v’
  >> simp [ext_lit_def, lit_map_def, var_map_def, encode_lives_hold_def, xeval_lit_def,
           xeval_gate_ori_orig]
QED


(* Encoding certificate conditions ********************************************)

Definition encode_reset_cond_def:
  encode_reset_cond
    (mxaig: ('a, 'i, 'l) xaig)
    (mreset: 'l -> ('a, 'i, 'l) lit option)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlatches: 'l list)
    (wxaig: ('b, 'i, 'l) xaig)
    (wreset: 'l -> ('b, 'i, 'l) lit option)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wlatches: 'l list)
    (klatches: 'l list)  (* mlatches ∩ wlatches *)
  =
  let
    xaig = ext_xaig (merge_xaigs mxaig wxaig);
    mr   = encode_xis_reset Mreset (ext_reset (left_reset mreset)) mlatches;
    mc0  = encode_xlits_hold Mcnstrs0 (MAP (ext_lit ∘ left_name_lit) mcnstrs);
    wr   = encode_xis_reset Wreset (ext_reset (right_reset wreset)) klatches;
    wc0  = encode_xlits_hold Wcnstrs0 (MAP (ext_lit ∘ right_name_lit) wcnstrs);
    lhss =
      [(Gate (Ext Mreset), F);
       (Gate (Ext Mcnstrs0), F)];
    rhss =
      [(Gate (Ext Wreset), F);
       (Gate (Ext Wcnstrs0), F)];
  in
    FLAT [encode_imply Reset T lhss rhss; wc0; wr; mc0; mr; xaig]
End

Definition encode_transition_cond_def:
  encode_transition_cond
    (mxaig: ('a, 'i, 'l) xaig)
    (mnext: 'l -> ('a, 'i, 'l) lit)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlatches: 'l list)
    (wxaig: ('b, 'i, 'l) xaig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wlatches: 'l list)
    (klatches: 'l list)  (* mlatches ∩ wlatches *)
  =
  let
    xaig = merge_xaigs mxaig wxaig;
    xaig = ext_xaig (pair_xaigs xaig xaig);
    mc0  = encode_xlits_hold Mcnstrs0
            (MAP (ext_lit ∘ left_lit ∘ left_name_lit) mcnstrs);
    wc0  = encode_xlits_hold Wcnstrs0
            (MAP (ext_lit ∘ left_lit ∘ right_name_lit) wcnstrs);
    mc1  = encode_xlits_hold Mcnstrs1
            (MAP (ext_lit ∘ right_lit ∘ left_name_lit) mcnstrs);
    wc1  = encode_xlits_hold Wcnstrs1
            (MAP (ext_lit ∘ right_lit ∘ right_name_lit) wcnstrs);
    mn   = encode_xis_next Mnext
            (ext_lit ∘ left_lit ∘ left_name_lit)
            (ext_lit ∘ right_lit)
            mnext mlatches;
    wn0  = encode_xis_next Wnext0
            (ext_lit ∘ left_lit ∘ right_name_lit)
            (ext_lit ∘ right_lit)
            wnext klatches;
    lhss =
      [(Gate (Ext Mnext), F);
       (Gate (Ext Mcnstrs0), F);
       (Gate (Ext Mcnstrs1), F);
       (Gate (Ext Wcnstrs0), F)];
    rhss =
      [(Gate (Ext Wnext0), F);
       (Gate (Ext Wcnstrs1), F)];
  in
    FLAT [encode_imply Transition T lhss rhss;
          wn0; mn; wc1; mc1; wc0; mc0; xaig]
End

Definition encode_safety_cond_def:
  encode_safety_cond
    (mxaig: ('a, 'i, 'l) xaig)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (msafes: ('a, 'i, 'l) lit list)
    (wxaig: ('b, 'i, 'l) xaig)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
  =
  let
    xaig = ext_xaig (merge_xaigs mxaig wxaig);
    mc0  = encode_xlits_hold Mcnstrs0 (MAP (ext_lit ∘ left_name_lit) mcnstrs);
    ms   = encode_xlits_hold Msafes (MAP (ext_lit ∘ left_name_lit) msafes);
    wc0  = encode_xlits_hold Wcnstrs0 (MAP (ext_lit ∘ right_name_lit) wcnstrs);
    ws0  = encode_xlits_hold Wsafes0 (MAP (ext_lit ∘ right_name_lit) wsafes);
    lhss =
      [(Gate (Ext Mcnstrs0),F);
       (Gate (Ext Wcnstrs0),F);
       (Gate (Ext Wsafes0),F)];
    rhss = [(Gate (Ext Msafes), F);]
  in
    FLAT [encode_imply Safety T lhss rhss; ws0; wc0; ms; mc0; xaig]
End


Definition encode_base_cond_def:
  encode_base_cond
    (wxaig: ('a, 'i, 'l) xaig)
    (wreset: 'l -> ('a, 'i, 'l) lit option)
    (wcnstrs: ('a, 'i, 'l) lit list)
    (wsafes: ('a, 'i, 'l) lit list)
    (wlatches: 'l list)
  ⇔
    let
      xaig = ext_xaig wxaig;
      wr   = encode_xis_reset Wreset (ext_reset wreset) wlatches;
      wc0  = encode_xlits_hold Wcnstrs0 (MAP ext_lit wcnstrs);
      ws0  = encode_xlits_hold Wsafes0 (MAP ext_lit wsafes);
      lhss =
        [(Gate (Ext Wreset),F);
         (Gate (Ext Wcnstrs0),F)];
      rhss = [(Gate (Ext Wsafes0), F)]
  in
    FLAT [encode_imply Base T lhss rhss; ws0; wc0; wr; xaig]
End

Definition encode_induction_cond_def:
  encode_induction_cond
    (wxaig: ('a, 'i, 'l) xaig)
    (wnext: 'l -> ('a, 'i, 'l) lit)
    (wcnstrs: ('a, 'i, 'l) lit list)
    (wsafes: ('a, 'i, 'l) lit list)
    (wlatches: 'l list)
  =
    let
      xaig = ext_xaig (pair_xaigs wxaig wxaig);
      wc0  = encode_xlits_hold Wcnstrs0
              (MAP (ext_lit ∘ left_lit) wcnstrs);
      ws0  = encode_xlits_hold Wsafes0
              (MAP (ext_lit ∘ left_lit) wsafes);
      wc1  = encode_xlits_hold Wcnstrs1
              (MAP (ext_lit ∘ right_lit) wcnstrs);
      ws1  = encode_xlits_hold Wsafes1
              (MAP (ext_lit ∘ right_lit) wsafes);
      wn0  = encode_xis_next Wnext0
              (ext_lit ∘ left_lit) (ext_lit ∘ right_lit)
              wnext wlatches;
      lhss =
        [(Gate (Ext Wsafes0), F);
         (Gate (Ext Wnext0), F);
         (Gate (Ext Wcnstrs1), F);
         (Gate (Ext Wcnstrs0), F)];
      rhss = [(Gate (Ext Wsafes1), F)]
    in
      FLAT [encode_imply Induction T lhss rhss; wn0; ws1; wc1; ws0; wc0; xaig]
End

Definition encode_liveness_cond_def:
  encode_liveness_cond
    (mxaig: ('a, 'i, 'l) xaig)
    (mcnstrs: ('a, 'i, 'l) lit list)
    (mlive: ('a, 'i, 'l) lit list list)
    (wxaig: ('b, 'i, 'l) xaig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    mqxaig = qxleft mxaig;
    wqxaig = qinterv_l_r interv wxaig;
    qxaig  = merge_xaigs mqxaig wqxaig;
    xaig   = merge_xaigs mxaig wxaig;
    xaig   = pair_xaigs xaig xaig;
    xaig   = ext_xaig (merge_xaigs xaig qxaig);
    wsignals = MAP (ext_lit ∘ right_name_lit ∘ right_name_lit)
                     (FLAT (qinterv_live_l_r interv wlive));
    msignals = MAP (ext_lit ∘ right_name_lit ∘ left_name_lit)
                     (FLAT (qleft_live mlive));
    li     = encode_signal_imply Lives_imply wsignals msignals;
    mc0    = encode_xlits_hold Mcnstrs0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_name_lit) mcnstrs);
    wc0    = encode_xlits_hold Wcnstrs0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_name_lit) wcnstrs);
    ws0    = encode_xlits_hold Wsafes0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_name_lit) wsafes);
    mc1    = encode_xlits_hold Mcnstrs1
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit ∘ left_name_lit) mcnstrs);
    wc1    = encode_xlits_hold Wcnstrs1
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit ∘ right_name_lit) wcnstrs);
    ws1    = encode_xlits_hold Wsafes1
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit ∘ right_name_lit) wsafes);
    wn0    =
      encode_xis_next Wnext0
        (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_name_lit)
        (ext_lit ∘ left_name_lit ∘ right_lit)
        wnext wlatches;
    lhss = [
        (Gate (Ext Mcnstrs0), F);
        (Gate (Ext Wcnstrs0), F);
        (Gate (Ext Wsafes0), F);
        (Gate (Ext Mcnstrs1), F);
        (Gate (Ext Wcnstrs1), F);
        (Gate (Ext Wsafes1), F);
        (Gate (Ext Wnext0), F)
    ];
    rhss = [(Gate (Ext Lives_imply), F)]
  in
    FLAT [encode_imply Liveness T lhss rhss;
          wn0; ws1; wc1; mc1; ws0; wc0; mc0; li; xaig]
End

Definition encode_decrease_cond_def:
  encode_decrease_cond
    (wxaig: ('b, 'i, 'l) xaig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    qxaig  = qinterv_r_l interv wxaig;
    xaig   = pair_xaigs wxaig wxaig;
    xaig   = ext_xaig (merge_xaigs xaig qxaig);
    wc0    = encode_xlits_hold Wcnstrs0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit) wcnstrs);
    ws0    = encode_xlits_hold Wsafes0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit) wsafes);
    wc1    = encode_xlits_hold Wcnstrs1
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wcnstrs);
    ws1    = encode_xlits_hold Wsafes1
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wsafes);
    wn0    = encode_xis_next Wnext0
              (ext_lit ∘ left_name_lit ∘ left_lit)
              (ext_lit ∘ left_name_lit ∘ right_lit)
              wnext wlatches;
    live  = MAP (MAP (ext_lit ∘ right_name_lit))
              (qinterv_live_r_l interv wlive);
    lh10  = encode_lives_hold Lives_hold10 live;
    lhss = [
      (Gate (Ext Wcnstrs0), F);
      (Gate (Ext Wsafes0), F);
      (Gate (Ext Wcnstrs1), F);
      (Gate (Ext Wsafes1), F);
      (Gate (Ext Wnext0), F);
    ];
    rhss = [(Gate (Ext Lives_hold10), F)]
  in
    FLAT [encode_imply Decrease T lhss rhss;
          lh10; wn0; ws1; wc1; ws0; wc0; xaig]
End

Definition encode_closure_cond_def:
  encode_closure_cond
    (wxaig: ('b, 'i, 'l) xaig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    (* states: s = ll, t = lr, u = r *)
    qxaig₀ = qinterv_ll_r interv wxaig;
    qxaig₁ = qinterv_lr_r interv wxaig;
    qxaig  = merge_xaigs qxaig₀ qxaig₁;
    xaig   = pair_xaigs (pair_xaigs wxaig wxaig) wxaig;
    xaig   = ext_xaig (merge_xaigs xaig qxaig);
    wc0    = encode_xlits_hold Wcnstrs0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit) wcnstrs);
    ws0    = encode_xlits_hold Wsafes0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit) wsafes);
    wc1    = encode_xlits_hold Wcnstrs1
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit) wcnstrs);
    ws1    = encode_xlits_hold Wsafes1
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit) wsafes);
    wc2    = encode_xlits_hold Wcnstrs2
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wcnstrs);
    ws2    = encode_xlits_hold Wsafes2
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wsafes);
    wn0    = encode_xis_next Wnext0
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit)
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit)
              wnext wlatches;
    live₀ = MAP (MAP (ext_lit ∘ right_name_lit ∘ left_name_lit))
              (qinterv_live_ll_r interv wlive);
    live₁ = MAP (MAP (ext_lit ∘ right_name_lit ∘ right_name_lit))
              (qinterv_live_lr_r interv wlive);
    lh02 = encode_lives_hold Lives_hold02 live₀;
    lh12 = encode_lives_hold Lives_hold12 live₁;
    lhss = [
      (Gate (Ext Wcnstrs0), F);
      (Gate (Ext Wsafes0), F);
      (Gate (Ext Wcnstrs1), F);
      (Gate (Ext Wsafes1), F);
      (Gate (Ext Wcnstrs2), F);
      (Gate (Ext Wsafes2), F);
      (Gate (Ext Wnext0), F);
      (Gate (Ext Lives_hold02), F);
    ];
    rhss = [(Gate (Ext Lives_hold12), F)]
  in
    FLAT [encode_imply Closure T lhss rhss;
          lh12; lh02; wn0; ws2; wc2; ws1; wc1; ws0; wc0; xaig]
End

Definition encode_stable_cond_def:
  encode_stable_cond
    (wxaig: ('b, 'i, 'l) xaig)
    (wnext: 'l -> ('b, 'i, 'l) lit)
    (wcnstrs: ('b, 'i, 'l) lit list)
    (wsafes: ('b, 'i, 'l) lit list)
    (wlive: ('b, 'i, 'l) lit list list)
    (wlatches: 'l list)
    (interv: ('b, 'i, 'l) var -> ('l # bool) option)
  =
  let
    (* states: s = ll, t = lr, u = r *)
    qxaig₀ = qinterv_ll_lr interv wxaig;
    qxaig₁ = qinterv_lr_r interv wxaig;
    qxaig  = merge_xaigs qxaig₀ qxaig₁;
    xaig   = pair_xaigs (pair_xaigs wxaig wxaig) wxaig;
    xaig   = ext_xaig (merge_xaigs xaig qxaig);
    wc0    = encode_xlits_hold Wcnstrs0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit) wcnstrs);
    ws0    = encode_xlits_hold Wsafes0
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit) wsafes);
    wc1    = encode_xlits_hold Wcnstrs1
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit) wcnstrs);
    ws1    = encode_xlits_hold Wsafes1
              (MAP (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit) wsafes);
    wc2    = encode_xlits_hold Wcnstrs2
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wcnstrs);
    ws2    = encode_xlits_hold Wsafes2
              (MAP (ext_lit ∘ left_name_lit ∘ right_lit) wsafes);
    wn0    = encode_xis_next Wnext0
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ left_lit)
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit)
              wnext wlatches;
    wn1    = encode_xis_next Wnext1
              (ext_lit ∘ left_name_lit ∘ left_lit ∘ right_lit)
              (ext_lit ∘ left_name_lit ∘ right_lit)
              wnext wlatches;
    live₀ = MAP (MAP (ext_lit ∘ right_name_lit ∘ left_name_lit))
              (qinterv_live_ll_lr interv wlive);
    live₁ = MAP (MAP (ext_lit ∘ right_name_lit ∘ right_name_lit))
              (qinterv_live_lr_r interv wlive);
    lh01 = encode_lives_hold Lives_hold01 live₀;
    lh12 = encode_lives_hold Lives_hold12 live₁;
    li   = encode_signal_imply Lives_imply (FLAT live₀) (FLAT live₁) ;
    lhss = [
        (Gate (Ext Wcnstrs0), F);
        (Gate (Ext Wsafes0), F);
        (Gate (Ext Wcnstrs1), F);
        (Gate (Ext Wsafes1), F);
        (Gate (Ext Wcnstrs2), F);
        (Gate (Ext Wsafes2), F);
        (Gate (Ext Wnext0), F);
        (Gate (Ext Wnext1), F);
        (Gate (Ext Lives_hold01), F);
        (Gate (Ext Lives_hold12), F)
      ];
    rhss = [(Gate (Ext Lives_imply), F)];
  in
    FLAT [encode_imply Stable T lhss rhss;
          li; lh12; lh01; wn1; wn0; ws2; wc2; ws1; wc1; ws0; wc0; xaig]
End

(* Proving correctness of the encodings ***************************************)

(* A bunch of trivial helper lemmas, which keep the proof state readable
   when an encoding function uses many other encoding functions. *)
(*
Theorem xis_reset_encode_xlits_hold_iright[local,simp]:
  xis_reset ss
    (encode_xlits_hold xaig name lits) (iright_reset reset) latches ⇔
  xis_reset ss xaig (iright_reset reset) latches
Proof
  simp [xis_reset_def, encode_xlits_hold_def, iright_reset_def, right_reset_def,
        xeval_lit_def, ext_reset_def, PULL_EXISTS]
QED

Theorem xis_reset_encode_xis_reset_iright[local,simp]:
  xis_reset ss (encode_xis_reset xaig name reset' latches')
    (iright_reset reset) latches ⇔
  xis_reset ss xaig (iright_reset reset) latches
Proof
  simp [xis_reset_def, encode_xis_reset_def, iright_reset_def, xeval_lit_def,
        ext_reset_def, PULL_EXISTS]
QED

Theorem xlits_hold_ext[local,simp]:
  xlits_hold ss (ext_xaig xaig) (set (MAP ext_lit preds)) ⇔
    xlits_hold ss xaig (set preds)
Proof
  simp [xlits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_ileft[local,simp]:
  xlits_hold ss (imerge_xaigs lxaig rxaig) (set (ileft_name_lits preds)) ⇔
    xlits_hold ss lxaig (set preds)
Proof
  simp [xlits_hold_def, ileft_name_lits_def, imerge_xaigs_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_iright[local,simp]:
  xlits_hold ss (imerge_xaigs lxaig rxaig) (set (iright_name_lits preds)) ⇔
    xlits_hold ss rxaig (set preds)
Proof
  simp [xlits_hold_def, iright_name_lits_def, imerge_xaigs_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_xis_reset_ileft[local,simp]:
  xlits_hold ss
    (encode_xis_reset xaig name reset latches) (set (ileft_name_lits preds)) ⇔
  xlits_hold ss xaig (set (ileft_name_lits preds))
Proof
  simp [xlits_hold_def, encode_xis_reset_def, ileft_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_xis_reset_iright[local,simp]:
  xlits_hold ss
    (encode_xis_reset xaig name reset latches) (set (iright_name_lits preds)) ⇔
  xlits_hold ss xaig (set (iright_name_lits preds))
Proof
  simp [xlits_hold_def, encode_xis_reset_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_xis_reset_ext[local,simp]:
  xlits_hold ss
    (encode_xis_reset xaig name reset latches) (set (MAP ext_lit preds)) ⇔
  xlits_hold ss xaig (set (MAP ext_lit preds))
Proof
  simp [xlits_hold_def, encode_xis_reset_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_xlits_hold_iright[local,simp]:
  xlits_hold ss (encode_xlits_hold xaig name preds') (set (iright_name_lits preds)) ⇔
    xlits_hold ss xaig (set (iright_name_lits preds))
Proof
  simp [xlits_hold_def, encode_xlits_hold_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED
*)

(*** xlits_hold ***************************************************************)

Theorem xlits_hold_ext_xaig_ext_lit[local,simp]:
  xlits_hold ss (ext_xaig xaig) (set (MAP ext_lit preds)) ⇔
    xlits_hold ss xaig (set preds)
Proof
  simp [xlits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_merge_left[local,simp]:
  xlits_hold ss (merge_xaigs lxaig rxaig) (set (MAP left_name_lit preds)) ⇔
    xlits_hold ss lxaig (set preds)
Proof
  simp [xlits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_merge_right[local,simp]:
  xlits_hold ss (merge_xaigs lxaig rxaig) (set (MAP right_name_lit preds)) ⇔
    xlits_hold ss rxaig (set preds)
Proof
  simp [xlits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_pair_left[local,simp]:
  xlits_hold (state_pair s₁ s₂) (pair_xaigs lxaig rxaig)
    (set (MAP left_lit preds)) ⇔
  xlits_hold s₁ lxaig (set preds)
Proof
  simp [xlits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_pair_right[local,simp]:
  xlits_hold (state_pair s₁ s₂) (pair_xaigs lxaig rxaig)
    (set (MAP right_lit preds)) ⇔
  xlits_hold s₂ rxaig (set preds)
Proof
  simp [xlits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_xlits_hold_ext_lit[local,simp]:
  xlits_hold ss (encode_xlits_hold name preds' ++ xaig)
    (set (MAP ext_lit preds)) ⇔
  xlits_hold ss xaig (set (MAP ext_lit preds))
Proof
  simp [xlits_hold_def, encode_xlits_hold_def, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_xis_reset_ext_lit[local,simp]:
  xlits_hold ss (encode_xis_reset name reset ls ++ xaig)
    (set (MAP ext_lit preds)) ⇔
  xlits_hold ss xaig (set (MAP ext_lit preds))
Proof
  simp [xlits_hold_def, encode_xis_reset_def, encode_pointwise_equal_def,
        MEM_MAP, PULL_EXISTS]
  >> qmatch_goalsub_abbrev_tac ‘xori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_xori]
QED

Theorem xlits_hold_encode_pointwise_imply_ext_lit[local,simp]:
  xlits_hold ss (encode_pointwise_imply name xys ++ xaig)
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
  xlits_hold ss (encode_signal_imply name xs ys ++ xaig)
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
  xis_reset ss (merge_xaigs lxaig rxaig) (left_reset lreset) latches ⇔
    xis_reset ss lxaig lreset latches
Proof
  simp [xis_reset_def, left_reset_def, xeval_lit_def, PULL_EXISTS]
QED

Theorem xis_reset_right[local,simp]:
  xis_reset ss (merge_xaigs lxaig rxaig) (right_reset rreset) latches ⇔
    xis_reset ss rxaig rreset latches
Proof
  simp [xis_reset_def, right_reset_def, xeval_lit_def, PULL_EXISTS]
QED

Theorem xis_reset_encode_xlits_hold[local,simp]:
  xis_reset ss (encode_xlits_hold name lits ++ xaig) (ext_reset reset) ls ⇔
    xis_reset ss xaig (ext_reset reset) ls
Proof
  simp [xis_reset_def, encode_xlits_hold_def, xeval_lit_def, ext_reset_def,
        PULL_EXISTS]
QED

Theorem xis_reset_encode_xis_reset_ext[local,simp]:
  xis_reset ss (encode_xis_reset name reset' ls' ++ xaig) (ext_reset reset) ls ⇔
    xis_reset ss xaig (ext_reset reset) ls
Proof
  simp [xis_reset_def, encode_xis_reset_def, encode_pointwise_equal_def, xeval_lit_def,
        ext_reset_def, PULL_EXISTS]
  >> qmatch_goalsub_abbrev_tac ‘xori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_xori]
QED

(*** signal_imply *************************************************************)

Theorem signal_imply_ext_lit[local,simp]:
  (signal_imply ss (ext_xaig xaig) ss' xaig' (MAP ext_lit signals) signals' ⇔
     signal_imply ss xaig ss' xaig' signals signals') ∧
  (signal_imply ss xaig ss' (ext_xaig xaig') signals (MAP ext_lit signals') ⇔
    signal_imply ss xaig ss' xaig' signals signals')
Proof
  simp [signal_imply_def, LIST_REL_MAP, xlits_hold_def]
QED

Theorem signal_imply_merge_right[local,simp]:
  (signal_imply ss (merge_xaigs lxaig rxaig) ss' xaig'
    (MAP right_name_lit signals) signals' ⇔
   signal_imply ss rxaig ss' xaig' signals signals') ∧
  (signal_imply ss xaig ss' (merge_xaigs lxaig' rxaig')
     signals (MAP right_name_lit signals') ⇔
   signal_imply ss xaig ss' rxaig' signals signals')
Proof
  simp [signal_imply_def, LIST_REL_MAP, xlits_hold_def]
QED

Theorem signal_imply_merge_left[local,simp]:
  (signal_imply ss (merge_xaigs lxaig rxaig) ss' xaig'
    (MAP left_name_lit signals) signals' ⇔
   signal_imply ss lxaig ss' xaig' signals signals') ∧
  (signal_imply ss xaig ss' (merge_xaigs lxaig' rxaig')
     signals (MAP left_name_lit signals') ⇔
   signal_imply ss xaig ss' lxaig' signals signals')
Proof
  simp [signal_imply_def, LIST_REL_MAP, xlits_hold_def]
QED

Theorem signal_imply_encode_lives_hold_l[local,simp]:
  (signal_imply ss (encode_lives_hold name xss ++ xaig) ss' xaig'
     (MAP ext_lit signals) signals'
   ⇔ signal_imply ss xaig ss' xaig' (MAP ext_lit signals) signals')
Proof
  simp [signal_imply_def, encode_lives_hold_def]
  >> qmatch_goalsub_abbrev_tac ‘ori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> irule LIST_REL_cong
  >> rw [MEM_MAP, PULL_EXISTS]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_ori]
  >> metis_tac []
QED

Theorem signal_imply_encode_lives_hold_r[local,simp]:
  (signal_imply ss xaig ss' (encode_lives_hold name xss ++ xaig')
     signals (MAP ext_lit signals')
   ⇔ signal_imply ss xaig ss' xaig' signals (MAP ext_lit signals'))
Proof
  simp [signal_imply_def, encode_lives_hold_def]
  >> qmatch_goalsub_abbrev_tac ‘ori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> irule LIST_REL_cong
  >> rw [MEM_MAP, PULL_EXISTS]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_ori]
  >> metis_tac []
QED

Theorem signal_imply_encode_pointwise_equal_l[local,simp]:
  (signal_imply ss (encode_pointwise_equal name xys ++ xaig) ss' xaig'
     (MAP ext_lit signals) signals'
  ⇔ signal_imply ss xaig ss' xaig' (MAP ext_lit signals) signals')
Proof
  simp [signal_imply_def, encode_pointwise_equal_def]
  >> qmatch_goalsub_abbrev_tac ‘xori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> irule LIST_REL_cong
  >> rw [MEM_MAP, PULL_EXISTS]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_xori]
  >> metis_tac []
QED

Theorem signal_imply_encode_pointwise_equal_r[local,simp]:
  (signal_imply ss xaig ss' (encode_pointwise_equal name xss ++ xaig')
     signals (MAP ext_lit signals')
   ⇔ signal_imply ss xaig ss' xaig' signals (MAP ext_lit signals'))
Proof
  simp [signal_imply_def, encode_pointwise_equal_def]
  >> qmatch_goalsub_abbrev_tac ‘xori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> irule LIST_REL_cong
  >> rw [MEM_MAP, PULL_EXISTS]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_xori]
  >> metis_tac []
QED

Theorem signal_imply_encode_xlits_hold_l[local,simp]:
  (signal_imply ss (encode_xlits_hold name xys ++ xaig) ss' xaig'
     (MAP ext_lit signals) signals'
  ⇔ signal_imply ss xaig ss' xaig' (MAP ext_lit signals) signals')
Proof
  simp [signal_imply_def, encode_xlits_hold_def, LIST_REL_MAP]
QED

Theorem signal_imply_encode_xlits_hold_r[local,simp]:
  (signal_imply ss xaig ss' (encode_xlits_hold name xss ++ xaig')
     signals (MAP ext_lit signals')
   ⇔ signal_imply ss xaig ss' xaig' signals (MAP ext_lit signals'))
Proof
  simp [signal_imply_def, encode_xlits_hold_def, LIST_REL_MAP]
QED

(*** some_signal_holds ********************************************************)

Theorem some_signal_holds_encode_lives_hold_ext_lit[local,simp]:
  some_signal_holds ss (encode_lives_hold name live ++ xaig) (MAP (ext_lit ∘ f) lit)
  ⇔
  some_signal_holds ss xaig (MAP (ext_lit ∘ f) lit)
Proof
  simp [some_signal_holds_def, EXISTS_MEM, MEM_MAP, PULL_EXISTS,
        encode_lives_hold_def]
  >> qmatch_goalsub_abbrev_tac ‘ori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_ori]
  >> metis_tac []
QED

Theorem some_signal_holds_encode_pointwise_equal_ext_lit[local,simp]:
  some_signal_holds ss (encode_pointwise_equal name live ++ xaig)
    (MAP (ext_lit ∘ f) lit)
  ⇔
  some_signal_holds ss xaig (MAP (ext_lit ∘ f) lit)
Proof
  simp [some_signal_holds_def, EXISTS_MEM, MEM_MAP, PULL_EXISTS,
        encode_pointwise_equal_def]
  >> qmatch_goalsub_abbrev_tac ‘xori n’
  >> have ‘∀y. iname (ext_lit y) < n’
  >- simp [Abbr ‘n’, iname_def, maxn_def]
  >> eq_tac >> rw []
  >> gvs [iname_xeval_lit_xori]
  >> metis_tac []
QED

Theorem some_signal_holds_encode_xlits_hold_ext_lit[local,simp]:
  some_signal_holds ss (encode_xlits_hold name live ++ xaig) (MAP (ext_lit ∘ f) lit)
  ⇔
  some_signal_holds ss xaig (MAP (ext_lit ∘ f) lit)
Proof
  simp [some_signal_holds_def, EXISTS_MEM, MEM_MAP, PULL_EXISTS,
        encode_xlits_hold_def]
QED

Theorem some_signal_holds_encode_xlits_hold_ext_lit[local,simp]:
  some_signal_holds ss (ext_xaig xaig) (MAP (ext_lit ∘ f) lit)
  ⇔
  some_signal_holds ss xaig (MAP f lit)
Proof
  simp [some_signal_holds_def, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem some_signal_holds_merge_right[local,simp]:
  some_signal_holds ss (merge_xaigs laig raig) (MAP (right_name_lit ∘ f) lits)
  ⇔
  some_signal_holds ss raig (MAP f lits)
Proof
  simp [some_signal_holds_def, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem some_signal_holds_merge_right_only[local,simp]:
  some_signal_holds ss (merge_xaigs laig raig) (MAP right_name_lit lits)
  ⇔
  some_signal_holds ss raig lits
Proof
  have ‘lits = MAP I lits’ >- simp []
  >> pop_assum SUBST1_TAC
  >> rewrite_tac [MAP_MAP_o, some_signal_holds_merge_right]
QED

Theorem some_signal_holds_merge_left[local,simp]:
  some_signal_holds ss (merge_xaigs laig raig) (MAP (left_name_lit ∘ f) lits)
  ⇔
  some_signal_holds ss laig (MAP f lits)
Proof
  simp [some_signal_holds_def, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem some_signal_holds_merge_left_only[local,simp]:
  some_signal_holds ss (merge_xaigs laig raig) (MAP left_name_lit lits)
  ⇔
  some_signal_holds ss laig lits
Proof
  have ‘lits = MAP I lits’ >- simp []
  >> pop_assum SUBST1_TAC
  >> rewrite_tac [MAP_MAP_o, some_signal_holds_merge_left]
QED

(*** lives_hold ***************************************************************)

Theorem lives_hold_encode_lives_hold_ext_lit[local,simp]:
  lives_hold ss (encode_lives_hold name live ++ xaig) (MAP (MAP (ext_lit ∘ f)) live')
  ⇔
  lives_hold ss xaig (MAP (MAP (ext_lit ∘ f)) live')
Proof
  fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, lives_hold_def]
QED

Theorem lives_hold_encode_pointwise_equal_ext_lit[local,simp]:
  lives_hold ss (encode_pointwise_equal name live ++ xaig)
    (MAP (MAP (ext_lit ∘ f)) live')
  ⇔
  lives_hold ss xaig (MAP (MAP (ext_lit ∘ f)) live')
Proof
  fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, lives_hold_def]
QED

Theorem lives_hold_encode_xlits_hold_ext_lit[local,simp]:
  lives_hold ss (encode_xlits_hold name live ++ xaig) (MAP (MAP (ext_lit ∘ f)) live')
  ⇔
  lives_hold ss xaig (MAP (MAP (ext_lit ∘ f)) live')
Proof
  fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, lives_hold_def]
QED

Theorem lives_hold_ext_lit[local,simp]:
  lives_hold ss (ext_xaig xaig) (MAP (MAP (ext_lit ∘ f)) live')
  ⇔
  lives_hold ss xaig (MAP (MAP f) live')
Proof
  fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, lives_hold_def]
QED

Theorem lives_hold_merge_right[local,simp]:
  lives_hold ss (merge_xaigs laig raig) (MAP (MAP (right_name_lit ∘ f)) live')
  ⇔
  lives_hold ss raig (MAP (MAP f) live')
Proof
  fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, lives_hold_def]
QED

Theorem lives_hold_merge_right_only[local,simp]:
  lives_hold ss (merge_xaigs laig raig) (MAP (MAP right_name_lit) live')
  ⇔
  lives_hold ss raig live'
Proof
  fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, lives_hold_def]
QED

Theorem lives_hold_merge_left[local,simp]:
  lives_hold ss (merge_xaigs laig raig) (MAP (MAP (left_name_lit ∘ f)) live')
  ⇔
  lives_hold ss laig (MAP (MAP f) live')
Proof
  fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, lives_hold_def]
QED

Theorem lives_hold_merge_left_only[local,simp]:
  lives_hold ss (merge_xaigs laig raig) (MAP (MAP left_name_lit) live')
  ⇔
  lives_hold ss laig live'
Proof
  fs [EVERY_MEM, MEM_MAP, PULL_EXISTS, lives_hold_def]
QED

(*** qinterv ******************************************************************)

Theorem qinterv_r_l_cons[local]:
  qinterv_r_l interv (a::xaig) =
    (qinterv_gate INR INR I INL interv a)::(qinterv_r_l interv xaig)
Proof
  simp [qinterv_r_l_def, qinterv_def]
QED

Theorem qinterv_ll_r_cons[local]:
  qinterv_ll_r interv (a::xaig) =
    (qinterv_gate (INL ∘ INL) (INL ∘ INL) I INR interv a)
    ::(qinterv_ll_r interv xaig)
Proof
  simp [qinterv_ll_r_def, qinterv_def]
QED

Theorem qinterv_lr_r_cons[local]:
  qinterv_lr_r interv (a::xaig) =
    (qinterv_gate (INL ∘ INR) (INL ∘ INR) I INR interv a)
    ::(qinterv_lr_r interv xaig)
Proof
  simp [qinterv_lr_r_def, qinterv_def]
QED

Theorem qinterv_ll_lr_cons[local]:
  qinterv_ll_lr interv (a::xaig) =
    (qinterv_gate (INL ∘ INL) (INL ∘ INL) I (INL ∘ INR) interv a)
    ::(qinterv_ll_lr interv xaig)
Proof
  simp [qinterv_ll_lr_def, qinterv_def]
QED

Theorem qinterv_l_r_cons[local]:
  qinterv_l_r interv (a::xaig) =
    (qinterv_gate INL INL I INR interv a)::(qinterv_l_r interv xaig)
Proof
  simp [qinterv_l_r_def, qinterv_def]
QED

Theorem xeval_lit_qinterv_r_l_eq[local]:
  (∀lit.
     xeval_lit (state_pair s₀ s₁) (qinterv_r_l interv xaig)
       (qinterv_lit INR INR I INL interv lit)
     ⇔
     xeval_lit (state_pair s₁ s₀) (qinterv_l_r interv xaig)
       (qinterv_lit INL INL I INR interv lit)) ∧
  (∀a.
     xeval_gate (state_pair s₀ s₁) (qinterv_r_l interv xaig) a ⇔
     xeval_gate (state_pair s₁ s₀) (qinterv_l_r interv xaig) a)
Proof
  Induct_on ‘xaig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’
  >-
   (simp [qinterv_r_l_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, lit_map_def, var_map_def,
             state_pair_def]
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
    >> simp [qinterv_lit_def, lit_map_base_def, lit_map_def, var_map_def]
    >-
     (reverse CASE_TAC
      >- (CASE_TAC >> simp [xeval_lit_def, state_pair_def])
      >> simp [xeval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_gate_def, oneline qinterv_gty_def, AllCaseEqs()]
      >> simp [EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [xeval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [xeval_lit_def])
  >> rename1 ‘qinterv_r_l _ (h::_)’
  >> PairCases_on ‘h’
  >> simp [qinterv_r_l_cons, qinterv_l_r_cons]
  >> simp [qinterv_gate_def]
  >> Cases_on ‘h1’
  >> simp [qinterv_gty_def, xeval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem xeval_lit_qinterv_ll_r_eq[local]:
  (∀lit.
     xeval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_ll_r interv xaig)
       (qinterv_lit (INL ∘ INL) (INL ∘ INL) I INR interv lit)
     ⇔
     xeval_lit (state_pair s₀ s₂) (qinterv_l_r interv xaig)
       (qinterv_lit INL INL I INR interv lit)) ∧
  (∀a.
     xeval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_ll_r interv xaig) a ⇔
     xeval_gate (state_pair s₀ s₂) (qinterv_l_r interv xaig) a)
Proof
  Induct_on ‘xaig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_ll_r_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, lit_map_def, var_map_def,
             state_pair_def]
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
    >> simp [qinterv_lit_def, lit_map_base_def, lit_map_def, var_map_def]
    >-
     (reverse CASE_TAC
      >- (CASE_TAC >> simp [xeval_lit_def, state_pair_def])
      >> simp [xeval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_gate_def, oneline qinterv_gty_def, AllCaseEqs()]
      >> simp [EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [xeval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [xeval_lit_def])
  >> rename1 ‘qinterv_ll_r _ (h::_)’
  >> PairCases_on ‘h’
  >> simp [qinterv_ll_r_cons, qinterv_l_r_cons]
  >> simp [qinterv_gate_def]
  >> Cases_on ‘h1’
  >> simp [qinterv_gty_def, xeval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem xeval_lit_qinterv_lr_r_eq[local]:
  (∀lit.
     xeval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_lr_r interv xaig)
       (qinterv_lit (INL ∘ INR) (INL ∘ INR) I INR interv lit)
     ⇔
     xeval_lit (state_pair s₁ s₂) (qinterv_l_r interv xaig)
       (qinterv_lit INL INL I INR interv lit)) ∧
  (∀a.
     xeval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_lr_r interv xaig) a ⇔
     xeval_gate (state_pair s₁ s₂) (qinterv_l_r interv xaig) a)
Proof
  Induct_on ‘xaig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_lr_r_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, lit_map_def, var_map_def,
             state_pair_def]
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
    >> simp [qinterv_lit_def, lit_map_base_def, lit_map_def, var_map_def]
    >-
     (reverse CASE_TAC
      >- (CASE_TAC >> simp [xeval_lit_def, state_pair_def])
      >> simp [xeval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_gate_def, oneline qinterv_gty_def, AllCaseEqs()]
      >> simp [EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [xeval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [xeval_lit_def])
  >> rename1 ‘qinterv_lr_r _ (h::_)’
  >> PairCases_on ‘h’
  >> simp [qinterv_lr_r_cons, qinterv_l_r_cons]
  >> simp [qinterv_gate_def]
  >> Cases_on ‘h1’
  >> simp [qinterv_gty_def, xeval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem xeval_lit_qinterv_ll_lr_eq[local]:
  (∀lit.
     xeval_lit (state_pair (state_pair s₀ s₁) s₂) (qinterv_ll_lr interv xaig)
       (qinterv_lit (INL ∘ INL) (INL ∘ INL) I (INL ∘ INR) interv lit)
     ⇔
     xeval_lit (state_pair s₀ s₁) (qinterv_l_r interv xaig)
       (qinterv_lit INL INL I INR interv lit)) ∧
  (∀a.
     xeval_gate (state_pair (state_pair s₀ s₁) s₂)
       (qinterv_ll_lr interv xaig) a ⇔
     xeval_gate (state_pair s₀ s₁) (qinterv_l_r interv xaig) a)
Proof
  Induct_on ‘xaig’ >> rw []
  >> PairCases_on ‘s₀’ >> PairCases_on ‘s₁’ >> PairCases_on ‘s₂’
  >-
   (simp [qinterv_ll_lr_def, qinterv_l_r_def, qinterv_def]
    >> namedCases_on ‘lit’ ["v b"]
    >> Cases_on ‘v’
    >> simp [qinterv_lit_def, lit_map_base_def, lit_map_def, var_map_def, state_pair_def]
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
    >> simp [qinterv_lit_def, lit_map_base_def, lit_map_def, var_map_def]
    >-
     (reverse CASE_TAC
      >- (CASE_TAC >> simp [xeval_lit_def, state_pair_def])
      >> simp [xeval_lit_def]
      >> rpt (pairarg_tac >> gvs [])
      >> IF_CASES_TAC >> gvs []
      >> IF_CASES_TAC >> gvs []
      >> gvs [oneline qinterv_gate_def, oneline qinterv_gty_def, AllCaseEqs()]
      >> simp [EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS])
    >> rename1 ‘Base base’
    >> Cases_on ‘base’
    >> simp [bvar_map_def]
    >> CASE_TAC >> gvs [xeval_lit_def]
    >> gvs [state_pair_def]
    >> CASE_TAC >> gvs [xeval_lit_def])
  >> rename1 ‘qinterv_ll_lr _ (h::_)’
  >> PairCases_on ‘h’
  >> simp [qinterv_ll_lr_cons, qinterv_l_r_cons]
  >> simp [qinterv_gate_def]
  >> Cases_on ‘h1’
  >> simp [qinterv_gty_def, xeval_lit_def]
  >> IF_CASES_TAC >> gvs []
  >> simp [EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_r_l_eq[local]:
  lives_hold (state_pair s₀ s₁)
    (qinterv_r_l interv wxaig) (qinterv_live_r_l interv wlive)
  ⇔
  lives_hold (state_pair s₁ s₀)
    (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive)
Proof
  simp [lives_hold_def, some_signal_holds_def,
        qinterv_live_r_l_def,
        qinterv_live_l_r_def,
        qinterv_live_def,
        xlits_hold_def,
        xeval_lit_qinterv_r_l_eq,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_ll_r_eq[local]:
  lives_hold (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_ll_r interv wxaig) (qinterv_live_ll_r interv wlive)
  ⇔
  lives_hold (state_pair s₀ s₂)
    (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive)
Proof
  simp [lives_hold_def, some_signal_holds_def,
        qinterv_live_ll_r_def,
        qinterv_live_l_r_def,
        qinterv_live_def,
        xlits_hold_def,
        xeval_lit_qinterv_ll_r_eq,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_ll_lr_eq[local]:
  lives_hold (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_ll_lr interv wxaig) (qinterv_live_ll_lr interv wlive)
  ⇔
  lives_hold (state_pair s₀ s₁)
    (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive)
Proof
  simp [lives_hold_def, some_signal_holds_def,
        qinterv_live_ll_lr_def, qinterv_live_l_r_def, qinterv_live_def,
        xlits_hold_def, xeval_lit_qinterv_ll_lr_eq,
        EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_lr_r_eq[local]:
  lives_hold (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_lr_r interv wxaig) (qinterv_live_lr_r interv wlive)
  ⇔
  lives_hold (state_pair s₁ s₂)
    (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive)
Proof
  simp [lives_hold_def, some_signal_holds_def,
        qinterv_live_lr_r_def,
        qinterv_live_l_r_def,
        qinterv_live_def,
        xlits_hold_def,
        xeval_lit_qinterv_lr_r_eq,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem FLAT_qinterv_live_flip[local]:
  FLAT (qinterv_live_lr_r interv wlive) =
    MAP (qinterv_lit (INL ∘ INR) (INL ∘ INR) I INR interv) (FLAT wlive)
  ∧
  FLAT (qinterv_live_l_r interv wlive) =
    MAP (qinterv_lit INL INL I INR interv) (FLAT wlive)
  ∧
  FLAT (qinterv_live_ll_lr interv wlive) =
    MAP (qinterv_lit (INL ∘ INL) (INL ∘ INL) I (INL ∘ INR) interv) (FLAT wlive)
Proof
  simp [qinterv_live_lr_r_def, qinterv_live_def, qinterv_live_l_r_def,
        qinterv_live_ll_lr_def,
        GSYM MAP_FLAT]
QED

Theorem signal_imply_right_lr_r_eq[local]:
  signal_imply ss xaig
    (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_lr_r interv wxaig)
    signals
    (FLAT (qinterv_live_lr_r interv wlive))
  ⇔
  signal_imply ss xaig (state_pair s₁ s₂) (qinterv_l_r interv wxaig)
    signals (FLAT (qinterv_live_l_r interv wlive))
Proof
  simp [signal_imply_def, FLAT_qinterv_live_flip, LIST_REL_EL_EQN]
  >> eq_tac >> rw []
  >> gvs [Req0 EL_MAP, xlits_hold_def, xeval_lit_qinterv_lr_r_eq]
QED

Theorem signal_imply_left_ll_lr_eq[local]:
  signal_imply
    (state_pair (state_pair s₀ s₁) s₂)
    (qinterv_ll_lr interv wxaig)
    ss xaig
    (FLAT (qinterv_live_ll_lr interv wlive))
    signals
  ⇔
  signal_imply (state_pair s₀ s₁) (qinterv_l_r interv wxaig) ss xaig
    (FLAT (qinterv_live_l_r interv wlive)) signals
Proof
  simp [signal_imply_def, FLAT_qinterv_live_flip, LIST_REL_EL_EQN]
  >> eq_tac >> rw []
  >> gvs [Req0 EL_MAP, xlits_hold_def, xeval_lit_qinterv_ll_lr_eq]
QED

(*
Theorem xlits_hold_encode_xlits_hold_iright[local,simp]:
  xlits_hold ss (encode_xlits_hold xaig name preds') (set (iright_name_lits preds)) ⇔
    xlits_hold ss xaig (set (iright_name_lits preds))
Proof
  simp [xlits_hold_def, encode_xlits_hold_def, iright_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem xlits_hold_encode_xlits_hold_ileft[local,simp]:
  xlits_hold ss (encode_xlits_hold xaig name preds') (set (ileft_name_lits preds)) ⇔
    xlits_hold ss xaig (set (ileft_name_lits preds))
Proof
  simp [xlits_hold_def, encode_xlits_hold_def, ileft_name_lits_def,
        GSYM MAP_MAP_o, MEM_MAP, PULL_EXISTS]
QED

Theorem signal_imply_iright_ileft[local,simp]:
  signal_imply ss₀ (imerge_xaigs xaig₁ xaig₂)
    ss₁ (imerge_xaigs xaig₃ xaig₄) (iright_name_lits signals')
    (ileft_name_lits signals)
  ⇔
  signal_imply ss₀ xaig₂ ss₁ xaig₃ signals' signals
Proof
  simp [signal_imply_def, ileft_name_lits_def, iright_name_lits_def,
        xlits_hold_def, LIST_REL_MAP]
QED

Theorem signal_imply_ileft_iright[local,simp]:
  signal_imply ss₀ (imerge_xaigs xaig₁ xaig₂)
    ss₁ (imerge_xaigs xaig₃ xaig₄) (ileft_name_lits signals')
    (iright_name_lits signals)
  ⇔
  signal_imply ss₀ xaig₁ ss₁ xaig₄ signals' signals
Proof
  simp [signal_imply_def, ileft_name_lits_def, iright_name_lits_def,
        xlits_hold_def, LIST_REL_MAP]
QED

Theorem lives_hold_ext_xaig[local,simp]:
  lives_hold ss (ext_xaig xaig) (MAP (MAP ext_lit) lives)
  ⇔
  lives_hold ss xaig lives
Proof
  simp [lives_hold_def, some_signal_holds_def, xlits_hold_def,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem encode_lives_hold_aux_xeval_lit_ext[local]:
  ∀live xaig next xaig' outs.
    encode_lives_hold_aux xaig live next = (xaig',outs)
    ⇒
    (xeval_lit ss xaig' (ext_lit lit) ⇔ xeval_lit ss xaig (ext_lit lit))
Proof
  Induct >> rw [encode_lives_hold_aux_def]
  >> rpt (pairarg_tac >> gvs [])
  >> last_x_assum drule >> simp []
QED

Theorem encode_signal_imply_aux_xeval_lit_ext[local]:
  ∀xaig signals signals' next xaig' outs.
    encode_signal_imply_aux xaig signals signals' next = (xaig',outs)
    ⇒
    (xeval_lit ss xaig' (ext_lit lit) ⇔ xeval_lit ss xaig (ext_lit lit))
Proof
  recInduct encode_signal_imply_aux_ind
  >> rw [encode_signal_imply_aux_def]
  >> rpt (pairarg_tac >> gvs [])
QED

Theorem lives_hold_encode_lives_hold_iright[local,simp]:
  lives_hold ss (encode_lives_hold xaig name live) (MAP iright_name_lits live')
  ⇔
  lives_hold ss xaig (MAP iright_name_lits live')
Proof
  simp [encode_lives_hold_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [lives_hold_def, some_signal_holds_def,
           xlits_hold_def, iright_name_lits_def,
           EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS]
  >> drule encode_lives_hold_aux_xeval_lit_ext >> simp []
QED

Theorem lives_hold_encode_signal_imply_ileft[local,simp]:
  lives_hold ss (encode_signal_imply xaig name signals signals')
    (MAP ileft_name_lits live')
  ⇔
  lives_hold ss xaig (MAP ileft_name_lits live')
Proof
  simp [encode_signal_imply_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [lives_hold_def, some_signal_holds_def,
           xlits_hold_def, ileft_name_lits_def,
           EVERY_MEM, MEM_MAP, EXISTS_MEM, PULL_EXISTS]
  >> drule encode_signal_imply_aux_xeval_lit_ext
  >> simp []
QED

Theorem lives_hold_encode_signal_imply_iright[local,simp]:
  lives_hold ss (encode_signal_imply xaig name signals signals')
    (MAP iright_name_lits live')
  ⇔
  lives_hold ss xaig (MAP iright_name_lits live')
Proof
  simp [encode_signal_imply_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [lives_hold_def, some_signal_holds_def,
           xlits_hold_def, iright_name_lits_def,
           EVERY_MEM, MEM_MAP, EXISTS_MEM, PULL_EXISTS]
  >> drule encode_signal_imply_aux_xeval_lit_ext
  >> simp []
QED

Theorem lives_hold_imerge_xaigs_ileft[local,simp]:
  lives_hold ss (imerge_xaigs xaig₀ xaig₁) (MAP ileft_name_lits live)
  ⇔
  lives_hold ss xaig₀ live
Proof
  simp [lives_hold_def, some_signal_holds_def,
        ileft_name_lits_def, xlits_hold_def,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

Theorem lives_hold_imerge_xaigs_iright[local,simp]:
  lives_hold ss (imerge_xaigs xaig₀ xaig₁) (MAP iright_name_lits live)
  ⇔
  lives_hold ss xaig₁ live
Proof
  simp [lives_hold_def, some_signal_holds_def,
        iright_name_lits_def, xlits_hold_def,
        EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS]
QED

(* Main encoder theorems ******************************************************)
*)

Definition reset_encoding_is_unsat_def:
  reset_encoding_is_unsat
    mxaig mreset mcnstrs mlatches
    wxaig wreset wcnstrs wlatches klatches
  ⇔
  (¬∃ss.
    (xeval_gate ss
       (encode_reset_cond
          mxaig mreset mcnstrs mlatches
          wxaig wreset wcnstrs wlatches klatches)
       ((Ext Reset))))
End

Theorem xeval_gate_encode_reset_cond:
  (set klatches) = (set mlatches) ∩ (set wlatches)
  ⇒
  (reset_encoding_is_unsat
    mxaig mreset mcnstrs mlatches
    wxaig wreset wcnstrs wlatches klatches
   =
   reset_cond
     mxaig mreset (set mcnstrs) (set mlatches)
     wxaig wreset (set wcnstrs) (set wlatches))
Proof[exclude_simps = APPEND_ASSOC]
  simp [
      reset_encoding_is_unsat_def,
      encode_reset_cond_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xis_reset_ext,
      reset_cond_def,
      GSYM MAP_MAP_o,
      GSYM APPEND_ASSOC
    ]
  >> metis_tac []
QED

Definition transition_encoding_is_unsat_def:
  transition_encoding_is_unsat
    mxaig mnext mcnstrs mlatches
    wxaig wnext wcnstrs wlatches klatches
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_transition_cond
          mxaig mnext mcnstrs mlatches
          wxaig wnext wcnstrs wlatches klatches)
       (Ext Transition)))
End

Theorem xeval_gate_encode_transition_cond:
  (set klatches) = (set mlatches) ∩ (set wlatches)
  ⇒
  (transition_encoding_is_unsat
    mxaig mnext mcnstrs mlatches
    wxaig wnext wcnstrs wlatches klatches ⇔
  transition_cond
    mxaig mnext (set mcnstrs) (set mlatches)
    wxaig wnext (set wcnstrs) (set wlatches))
Proof[exclude_simps = APPEND_ASSOC]
  strip_tac
  >> simp [
      transition_encoding_is_unsat_def,
      encode_transition_cond_def,
      encode_xis_next_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_lit_encode_pointwise_equal_ext_lit,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xlits_hold_ext_lit,
      FORALL_STATE_PAIR,
      xeval_lit_latch,
      transition_cond_def, xis_next_def,
      GSYM MAP_MAP_o,
      EXISTS_MEM, EVERY_MEM, MEM_MAP, PULL_EXISTS, PULL_FORALL,
      GSYM APPEND_ASSOC
    ]
  (* metis_tac is quite finicky here... *)
  >> eq_tac >> rw []
  >-
   (rename1 ‘xeval_lit ss₀ _ _ ⇔ _ ss₁ l’
    >> first_x_assum $ qspecl_then [‘ss₀’, ‘ss₁’, ‘l’] assume_tac
    >> metis_tac [])
  >-
   (rename1 ‘xeval_lit ss₀ _ _ ⇔ _ ss₁ _’
    >> first_x_assum $ qspecl_then [‘ss₀’, ‘ss₁’, ‘ARB’] assume_tac
    >> metis_tac [])
  >> rename1 ‘xeval_lit ss₀ _ _ ⇔ _ ss₁ l’
  (* metis_tac is *especially* finicky here... *)
  >> CCONTR_TAC
  >> first_x_assum $ qspecl_then [‘ss₀’, ‘ss₁’, ‘l’] mp_tac
  >> gvs []
  >> metis_tac []
QED

Definition safety_encoding_is_unsat_def:
  safety_encoding_is_unsat
    mxaig mcnstrs msafes
    wxaig wcnstrs wsafes
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_safety_cond
          mxaig mcnstrs msafes
          wxaig wcnstrs wsafes)
       (Ext Safety)))
End

Theorem xeval_gate_encode_safety_cond:
  safety_encoding_is_unsat
    mxaig mcnstrs msafes
    wxaig wcnstrs wsafes
  =
  safety_cond
    mxaig (set msafes) (set mcnstrs)
    wxaig (set wsafes) (set wcnstrs)
Proof[exclude_simps = APPEND_ASSOC]
  simp [
      safety_encoding_is_unsat_def,
      encode_safety_cond_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xlits_hold_ext_lit,
      safety_cond_def,
      GSYM MAP_MAP_o, GSYM APPEND_ASSOC
    ]
  >> metis_tac []
QED

Definition base_encoding_is_unsat_def:
  base_encoding_is_unsat
    wxaig wreset wcnstrs wsafes wlatches
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_base_cond
          wxaig wreset wcnstrs wsafes wlatches)
       (Ext Base)))
End

Theorem xeval_gate_encode_base_cond:
  base_encoding_is_unsat
    wxaig wreset wcnstrs wsafes wlatches
  =
  base_cond
    wxaig wreset (set wsafes) (set wcnstrs) (set wlatches)
Proof[exclude_simps = APPEND_ASSOC]
  simp [
      base_encoding_is_unsat_def,
      encode_base_cond_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xis_reset_ext,
      base_cond_def, GSYM APPEND_ASSOC
    ]
  >> metis_tac []
QED

Definition induction_encoding_is_unsat_def:
  induction_encoding_is_unsat
    wxaig wnext wcnstrs wsafes wlatches
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_induction_cond
          wxaig wnext wcnstrs wsafes wlatches)
       (Ext Induction)))
End

Theorem xeval_gate_encode_induction_cond:
  induction_encoding_is_unsat
    wxaig wnext wcnstrs wsafes wlatches
   =
  induction_cond wxaig wnext (set wsafes) (set wcnstrs) (set wlatches)
Proof[exclude_simps = APPEND_ASSOC]
  simp [
      induction_encoding_is_unsat_def,
      encode_induction_cond_def,
      encode_xis_next_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xlits_hold_ext_lit,
      xeval_lit_latch,
      GSYM MAP_MAP_o,
      FORALL_STATE_PAIR,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS,
      induction_cond_def, xis_next_def,
      GSYM APPEND_ASSOC
    ]
  >> metis_tac []
QED

Definition liveness_encoding_is_unsat_def:
  liveness_encoding_is_unsat
    mxaig mcnstrs mlive
    wxaig wnext wcnstrs wsafes wlive wlatches interv
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_liveness_cond
          mxaig mcnstrs mlive
          wxaig wnext wcnstrs wsafes wlive wlatches interv)
       (Ext Liveness)))
End

Theorem xeval_gate_encode_liveness_cond:
  LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive
  ⇒
  liveness_encoding_is_unsat
    mxaig mcnstrs mlive
    wxaig wnext wcnstrs wsafes wlive wlatches interv
  =
  liveness_cond
    mxaig (set mcnstrs) (qxleft mxaig) (qleft_live mlive)
    wxaig wnext (set wsafes) (set wcnstrs)
    (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof[exclude_simps = APPEND_ASSOC]
  strip_tac
  >> qmatch_goalsub_abbrev_tac
       ‘liveness_cond _ _ _ _ _ _ _ _ _ wlive' _’
  >> simp [
      liveness_encoding_is_unsat_def,
      encode_liveness_cond_def,
      xeval_gate_encode_imply,
      encode_xis_next_def, xis_next_def,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xlits_hold_ext_lit,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_lit_encode_signal_imply_ext_lit,
      FORALL_STATE_PAIR, xeval_lit_latch,
      GSYM MAP_MAP_o,
      EVERY_MEM, EXISTS_MEM, MEM_MAP, PULL_EXISTS,
      GSYM APPEND_ASSOC
    ]
  >> qmatch_goalsub_abbrev_tac ‘MAP left_name_lit (FLAT mlive')’
  >> have ‘LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive' wlive'’
  >- (
    fs [Abbr ‘mlive'’, Abbr ‘wlive'’, LIST_REL_EL_EQN,
        qinterv_live_l_r_def, qinterv_live_def, qleft_live_def,
        live_map_base_def, EL_MAP]
  )
  >> have ‘LENGTH (FLAT mlive') = LENGTH (FLAT wlive')’
  >- (drule LIST_REL_LENGTH_FLAT >> simp [])
  >> simp [Req0 xeval_lit_encode_signal_imply_ext]
  >> simp [Abbr ‘mlive'’, Abbr ‘wlive'’, liveness_cond_def, xis_next_def,
           lives_imply_signal_imply_FLAT]
  >> metis_tac []
QED

Definition decrease_encoding_is_unsat_def:
  decrease_encoding_is_unsat
    wxaig wnext wcnstrs wsafes wlive wlatches interv
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_decrease_cond
          wxaig wnext wcnstrs wsafes wlive wlatches interv)
       (Ext Decrease)))
End

Theorem xeval_gate_encode_decrease_cond:
  decrease_encoding_is_unsat
    wxaig wnext wcnstrs wsafes wlive wlatches interv
  =
  decrease_cond
    wxaig wnext (set wsafes) (set wcnstrs)
    (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof[exclude_simps = APPEND_ASSOC]
  simp [
      decrease_encoding_is_unsat_def,
      encode_decrease_cond_def,
      encode_xis_next_def,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_gate_encode_imply,
      xeval_lit_encode_lives_hold_ext,
      xeval_lit_encode_lives_hold_ext_lit,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xlits_hold_ext_lit,
      xeval_lit_latch,
      FORALL_STATE_PAIR,
      GSYM MAP_MAP_o,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS,
      xis_next_def, decrease_cond_def, lives_hold_r_l_eq,
      GSYM APPEND_ASSOC
    ]
  >> metis_tac []
QED

Definition closure_encoding_is_unsat_def:
  closure_encoding_is_unsat
    wxaig wnext wcnstrs wsafes wlive wlatches interv
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_closure_cond
          wxaig wnext wcnstrs wsafes wlive wlatches interv)
       (Ext Closure)))
End

Theorem xeval_gate_encode_closure_cond:
  closure_encoding_is_unsat
    wxaig wnext wcnstrs wsafes wlive wlatches interv
   =
  closure_cond
    wxaig wnext (set wsafes) (set wcnstrs)
    (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof[exclude_simps = APPEND_ASSOC]
  simp [
      closure_encoding_is_unsat_def,
      encode_closure_cond_def,
      encode_xis_next_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_lives_hold_ext,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xlits_hold_ext_lit,
      xeval_lit_latch,
      FORALL_STATE_PAIR,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS,
      GSYM MAP_MAP_o,
      closure_cond_def, xis_next_def,
      lives_hold_ll_r_eq, lives_hold_lr_r_eq,
      GSYM APPEND_ASSOC
    ]
  >> metis_tac []
QED

Definition stable_encoding_is_unsat_def:
  stable_encoding_is_unsat
    wxaig wnext wcnstrs wsafes wlive wlatches interv
  ⇔
  (¬∃ss.
     (xeval_gate ss
       (encode_stable_cond
          wxaig wnext wcnstrs wsafes wlive wlatches interv)
       (Ext Stable)))
End

Theorem xeval_gate_encode_stable_cond:
  stable_encoding_is_unsat
    wxaig wnext wcnstrs wsafes wlive wlatches interv
   =
  stable_cond
    wxaig wnext (set wsafes) (set wcnstrs)
    (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive) (set wlatches)
Proof[exclude_simps = APPEND_ASSOC]
  simp [stable_encoding_is_unsat_def, encode_stable_cond_def]
  >> qmatch_goalsub_abbrev_tac ‘encode_signal_imply _ signals' signals’
  >> have ‘LENGTH signals' = LENGTH signals’
  >- (
    simp [Abbr ‘signals'’, Abbr ‘signals’]
    >> irule LIST_REL_LENGTH_FLAT
    >> simp [LIST_REL_EL_EQN, EL_MAP,
             qinterv_live_ll_lr_def, qinterv_live_lr_r_def, qinterv_live_def]
  )
  >> simp [
      stable_encoding_is_unsat_def,
      encode_stable_cond_def,
      encode_xis_next_def,
      xeval_gate_encode_imply,
      xeval_lit_encode_pointwise_equal_ext,
      xeval_lit_encode_pointwise_equal_ext_lit,
      Req0 xeval_lit_encode_signal_imply_ext,
      xeval_lit_encode_signal_imply_ext_lit,
      xeval_lit_encode_lives_hold_ext,
      xeval_lit_encode_lives_hold_ext_lit,
      xeval_lit_encode_xlits_hold_ext,
      xeval_lit_encode_xlits_hold_ext_lit,
      FORALL_STATE_PAIR,
      GSYM MAP_MAP_o, GSYM APPEND_ASSOC,
      EXISTS_MEM, MEM_MAP, PULL_EXISTS
  ]
  >> simp [Abbr ‘signals’, Abbr ‘signals'’, GSYM MAP_FLAT, GSYM MAP_MAP_o]
  >> simp [lives_hold_lr_r_eq, lives_hold_ll_lr_eq]
  >> simp [signal_imply_right_lr_r_eq, signal_imply_left_ll_lr_eq]
  >> simp [stable_cond_def, lives_imply_signal_imply_FLAT, xis_next_def,
           xeval_lit_latch]
  >> qmatch_goalsub_abbrev_tac ‘LIST_REL _ xs _’
  >> have ‘LIST_REL (λQ Q'. LENGTH Q = LENGTH Q') xs xs’
  >- simp [LIST_REL_EL_EQN]
  >> simp [IMP_DISJ_THM]
QED

(** Stratification ************************************************************)

(* Given an xAIG and a name, finds the first match, returning its
   input literals and the rest of the xAIG. *)
(* To motivate this function, consider the simple xAIG
   [(Gate 0, [(Gate 0, F)])]
   Repeatedly applying ALOOKUP to find the dependencies of Gate 0 would lead to
   a loop. In contrast, by using the rest returned by xaig_lookup, the second
   invocation of xaig_lookup would return NONE, breaking the loop. *)
Definition xaig_lookup_def:
  (xaig_lookup (h::tl) n =
   let (n', gty) = h in
     if n' = n then SOME (get_lits gty,  tl) else xaig_lookup tl n) ∧
  xaig_lookup [] n = NONE
End

Theorem xaig_lookup_LENGTH_lt[local]:
  ∀xaig n. xaig_lookup xaig n = SOME (ins, rest) ⇒ LENGTH rest < LENGTH xaig
Proof
  Induct >> rw [xaig_lookup_def]
  >> rpt (pairarg_tac >> gvs [])
  >> rename1 ‘if n' = n then _ else _’
  >> Cases_on ‘n' = n’ >> gvs []
  >> last_x_assum drule >> simp []
QED

(* Computes the latches a literal depends on. *)
Definition latch_deps_def:
  (latch_deps (xaig: ('a, 'i, 'l) xaig) lit =
   let (v, _) = lit in
     case v of
     | Base (Latch l) => [l]
     | Gate a =>
       (case xaig_lookup xaig a of
        | NONE => []
        | SOME (lits, rest) =>
            FLAT (MAP (latch_deps rest) lits))
     | _ => [])
Termination
  wf_rel_tac ‘measure (LENGTH o FST)’ >> rw []
  >> drule xaig_lookup_LENGTH_lt >> simp []
End

Theorem latch_deps_cons_name_neq[local]:
  n' ≠ n ⇒
  latch_deps ((n',ins)::xaig) (Gate n,b) = latch_deps xaig (Gate n,b)
Proof
  simp [Once latch_deps_def, SimpLHS]
  >> simp [Once latch_deps_def, SimpRHS]
  >> simp [xaig_lookup_def]
QED

Theorem MEM_latch_deps_name_eq:
  MEM a (get_lits gt) ∧ MEM l (latch_deps xaig a) ⇒
  MEM l (latch_deps ((n,gt)::xaig) (Gate n,b))
Proof
  strip_tac
  >> simp [Once latch_deps_def, xaig_lookup_def]
  >> simp [MEM_FLAT, MEM_MAP, PULL_EXISTS]
  >> qpat_assum ‘MEM _ (latch_deps _ _)’ $ irule_at Any
  >> simp []
QED

Theorem latch_deps_xeval_eq:
  (∀lit.
     (∀l. MEM l (latch_deps xaig lit) ⇒ (ls' l ⇔ ls l)) ⇒
     (xeval_lit (is,ls') xaig lit ⇔ xeval_lit (is,ls) xaig lit)) ∧
  (∀lit n b.
    (∀l. MEM l (latch_deps xaig lit) ⇒ (ls' l ⇔ ls l)) ∧
    lit = (Gate n, b) ⇒
    (xeval_gate (is,ls') xaig n ⇔ xeval_gate (is,ls) xaig n))
Proof
  Induct_on ‘xaig’ >> rw []
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
    rename1 ‘latch_deps ((_,gt)::_)’
    >> suff
         ‘EVERY (λa. xeval_lit (is,ls') xaig a ⇔ xeval_lit (is,ls) xaig a)
            (get_lits gt)’
    >- (TOP_CASE_TAC >> gvs [EVERY_MEM, EXISTS_MEM] >> metis_tac [])
    >> rw [EVERY_MEM]
    >> first_x_assum irule >> rw []
    >> drule_all MEM_latch_deps_name_eq >> simp []
  )
  >> qsuff_tac ‘xeval_gate (is,ls') xaig n ⇔ xeval_gate (is,ls) xaig n’
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
    rename1 ‘latch_deps ((_,gt)::_)’
    >> suff
         ‘EVERY (λa. xeval_lit (is,ls') xaig a ⇔ xeval_lit (is,ls) xaig a)
            (get_lits gt)’
    >- (TOP_CASE_TAC >> gvs [EVERY_MEM, EXISTS_MEM] >> metis_tac [])
    >> rw [EVERY_MEM]
    >> first_x_assum irule >> rw []
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
    (xaig: ('a, 'i, 'l) xaig) (reset: 'l -> ('a, 'i, 'l) lit option) latch
  =
  case reset latch of
  | NONE => NONE
  | SOME lit => SOME (latch, latch_deps xaig lit)
End

(* Generates the dependency graph for the dependency graph of latches' reset
   functions.
   If this graph is acyclic, we know there exists an order that satisfies
   is_stratified. *)
Definition reset_graph_def:
  reset_graph
    (xaig: ('a, 'i, 'l) xaig) (reset: 'l -> ('a, 'i, 'l) lit option) latches
  =
  (* TODO Remove list$ once mllist's duplicate mapPartial has been removed *)
  list$mapPartial (reset_edges xaig reset) latches
End

(* Constructs the witness for is_stratified from the dependency graph of
   latches' reset functions.
   If the graph is acyclic, the order is irreflexive and thus the reset
   functions are stratified. *)
Definition reset_order_def:
  reset_order
    (xaig: ('a, 'i, 'l) xaig) (reset: 'l -> ('a, 'i, 'l) lit option) latches
  =
  (* ᵀ gives us R x y ⇔ "x is a dependency of y", as opposed to
     "x depends on y". We use the weak variant of TC_depends_on, since we do not
     want to force all dependencies to also be present as keys; the reset
     function of latch x may depend on some latch y, but y may not have a reset
     function. *)
  (TC_depends_on_weak (reset_graph xaig reset latches))ᵀ
End

Theorem transitive_reset_order[local]:
  transitive (reset_order xaig reset latches)
Proof
  simp [reset_order_def, TC_depends_on_weak_def]
QED

Theorem irreflexive_reset_order[local]:
  ALL_DISTINCT (MAP FST (reset_graph xaig reset latches)) ∧
  ¬has_cycle (reset_graph xaig reset latches)
  ⇒
  irreflexive (reset_order xaig reset latches)
Proof
  strip_tac
  >> drule_all has_cycle_correct2
  >> simp [irreflexive_def, reset_order_def]
QED

Theorem ALOOKUP_reset_graph_SOME[local]:
  ∀latches.
    MEM lat latches ∧ reset lat = SOME lit ⇒
    ALOOKUP (reset_graph xaig reset latches) lat = SOME (latch_deps xaig lit)
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
  MEM l (latch_deps xaig lit)
  ⇒
  reset_order xaig reset latches l lat
Proof
  rw [reset_order_def, TC_depends_on_weak_def]
  >> irule TC_SUBSET >> simp []
  >> irule_at Any ALOOKUP_reset_graph_SOME
  >> qexists ‘lit’ >> simp []
QED

Theorem dep_reset_lt_reset_order[local]:
  dep_reset_lt (reset_order xaig reset latches) xaig reset (set latches)
Proof
  rw [dep_reset_lt_def]
  >> irule latch_deps_xeval_lit_eq
  >> rpt strip_tac
  >> first_x_assum irule
  >> drule_all latch_deps_reset_order
  >> simp []
QED

Definition stratified_cond_def:
  stratified_cond xaig reset latches =
  let g = reset_graph xaig reset latches in
    ALL_DISTINCT (MAP FST g) ∧ ¬has_cycle g
End

Theorem stratified_cond_is_stratified:
  stratified_cond xaig reset latches
  ⇒
  ∃lt. is_stratified lt xaig reset (set latches)
Proof
  rw [stratified_cond_def]
  >> qexists ‘reset_order xaig reset latches’
  >> simp [is_stratified_def, transitive_reset_order,
           irreflexive_reset_order, dep_reset_lt_reset_order]
QED

(** Top-level theorems ********************************************************)

Definition encodings_unsat_def:
  encodings_unsat
    mxaig mreset mnext msafes mcnstrs mlive mlatches
    wxaig wreset wnext wsafes wcnstrs wlive wlatches
    interv klatches
  ⇔
    (reset_encoding_is_unsat
       mxaig mreset mcnstrs mlatches
       wxaig wreset wcnstrs wlatches klatches) ∧
    (transition_encoding_is_unsat
       mxaig mnext mcnstrs mlatches
       wxaig wnext wcnstrs wlatches klatches) ∧
    (safety_encoding_is_unsat
       mxaig mcnstrs msafes
       wxaig wcnstrs wsafes) ∧
    (base_encoding_is_unsat
       wxaig wreset wcnstrs wsafes wlatches) ∧
    (induction_encoding_is_unsat
       wxaig wnext wcnstrs wsafes wlatches) ∧
    (liveness_encoding_is_unsat
       mxaig mcnstrs mlive
       wxaig wnext wcnstrs wsafes wlive wlatches interv) ∧
    (decrease_encoding_is_unsat
       wxaig wnext wcnstrs wsafes wlive wlatches interv) ∧
    (closure_encoding_is_unsat
       wxaig wnext wcnstrs wsafes wlive wlatches interv) ∧
    (stable_encoding_is_unsat
       wxaig wnext wcnstrs wsafes wlive wlatches interv)
End

(** dep_model *****************************************************************)

(* dep_xaig *)

Definition dep_cond_def:
  dep_cond xaig reset next safes cnstrs live latches ⇔
    set (xaig_latches xaig) ⊆ set latches ∧
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
  >- simp [lit_map_base_def, lit_map_def, var_map_def, dep_lits_def]
  >> rename1 ‘Base b'’
  >> Cases_on ‘b'’
  >> simp [lit_map_base_def, lit_map_def, var_map_def, dep_lits_def,
           bvar_map_def, pair_set_def]
QED

Theorem dep_lits_pair_qleft_live:
  dep_lits (pair_set inputs) (pair_set latches) (set (FLAT (qleft_live mlive)))
  ⇔
  dep_lits inputs latches (set (FLAT mlive))
Proof
  simp [qleft_live_def, live_map_base_def, GSYM MAP_FLAT]
  >> simp [dep_lits_pair_map_lit_map_base_inl]
QED

Theorem encoding_xis_safe_and_live:
  LIST_REL (λms ws. LENGTH ms = LENGTH ws) mlive wlive ∧
  set klatches = set mlatches ∩ set wlatches ∧
  stratified_cond wxaig wreset wlatches ∧
  dep_cond mxaig mreset mnext msafes mcnstrs mlive mlatches ∧
  encodings_unsat
    mxaig mreset mnext msafes mcnstrs mlive mlatches
    wxaig wreset wnext wsafes wcnstrs wlive wlatches
    interv klatches
  ⇒
  xis_safe
    mxaig mreset mnext (set mcnstrs) (set mlatches) (set msafes) ∧
  xis_live
    mxaig mreset mnext (set mcnstrs) (qxleft mxaig)
    (IMAGE set (set (qleft_live mlive))) (set mlatches)
Proof
  strip_tac
  >> sg
       ‘is_witness
          mxaig mreset mnext (set msafes) (set mcnstrs)
          (qxleft mxaig) (qleft_live mlive) (set mlatches)
          wxaig wreset wnext (set wsafes) (set wcnstrs)
          (qinterv_l_r interv wxaig) (qinterv_live_l_r interv wlive)
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
        dep_model mxaig mreset mnext (set msafes) (set mcnstrs) minput
          (set mlatches) ∧
        dep_qxaig minput (qxleft mxaig) (qleft_live mlive) (set mlatches)’
  >- (
    qabbrev_tac
      ‘minput =
         set (xaig_inputs mxaig) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs ∘ mnext) (set mlatches)) ∪
         BIGUNION
           (IMAGE (set ∘ lit_inputs) (IMAGE_PARTIAL mreset (set mlatches))) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs) (set msafes)) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs) (set mcnstrs)) ∪
         BIGUNION (IMAGE (set ∘ lit_inputs) (set (FLAT mlive)))’
    >> qexists ‘minput’
    >> rewrite_tac [dep_model_def, dep_qxaig_def, GSYM CONJ_ASSOC]
    >> simp [dep_xaig_pair_qxleft, dep_lits_pair_qleft_live]
    >> fs [dep_cond_def]
    >> sg ‘dep_xaig minput (set mlatches) mxaig’
    >- (
      irule dep_xaig_subset
      >> irule_at Any dep_xaig_inputs_latches
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
  >> drule_all_then assume_tac is_witness_xis_safe_and_live
  >> simp []
QED

(** Mapping names to nums *****************************************************)

(* We use nested datatypes as names, which make proofs easier (since they encode
   namespaces neatly), but seems to incur some cost in the form of comparisons
   when renaming to packed nums (packed = every number between up to some n
   is used).
   Thus, we apply an injective function that maps to (unpacked) nums once,
   in the hopes of comparisons becoming cheaper. *)

Theorem exists_xeval_gate_xaig_map:
  INJ f 𝕌(:α) 𝕌(:β) ∧ INJ g 𝕌(:γ) 𝕌(:δ) ∧ INJ h 𝕌(:ε) 𝕌(:ζ)
  ⇒
  ((∃ss. xeval_gate ss (xaig_map f g h xaig) (h n)) ⇔
   (∃ss. xeval_gate ss xaig n))
Proof
  strip_tac >> eq_tac >> rw []
  >> namedCases_on ‘ss’ ["is ls"]
  >- (
    qexists ‘(is ∘ f, ls ∘ g)’
    >> irule $ iffLR $ cj 2 xaig_map_eq
    >> simp [o_DEF]
    >> metis_tac []
  )
  >> qexists ‘(is ∘ LINV f 𝕌(:α), ls ∘ LINV g 𝕌(:γ))’
  >> irule $ iffRL $ cj 2 xaig_map_eq
  >> imp_res_tac LINV_DEF >> simp []
  >> metis_tac []
QED

Definition sum2num_def:
  sum2num f _ (INL x) = 2 * (f x) ∧
  sum2num _ g (INR x) = 2 * (g x) + 1
End

Theorem sum2num_11:
  (∀x' x. f x' = f x ⇔ x' = x) ∧
  (∀x' x. g x' = g x ⇔ x' = x)
  ⇒
  (sum2num f g x' = sum2num f g x ⇔ x' = x)
Proof
  strip_tac
  >> simp [oneline sum2num_def]
  >> every_case_tac >> simp []
  >> ntac 2 $ pop_assum kall_tac
  >> intLib.COOPER_TAC
QED

(* (num + num) -> num *)
Definition nsn2num_def:
  nsn2num = sum2num I I
End

Theorem nsn2num_11:
  (nsn2num n' = nsn2num n ⇔ n' = n)
Proof
  simp [nsn2num_def, sum2num_11]
QED

Theorem INJ_nsn2num:
  INJ nsn2num 𝕌(:num + num) 𝕌(:num)
Proof
  simp [INJ_IFF, nsn2num_11]
QED

(* (num + num) + (num + num) -> num *)
Definition nsn_s_nsn2num_def:
  nsn_s_nsn2num = sum2num nsn2num nsn2num
End

Theorem nsn_s_nsn2num_11:
  (nsn_s_nsn2num n' = nsn_s_nsn2num n ⇔ n' = n)
Proof
  simp [nsn_s_nsn2num_def, sum2num_11, nsn2num_11]
QED

(* (num + num) + num -> num *)
Definition nsn_s_n2num_def:
  nsn_s_n2num = sum2num nsn2num I
End

Theorem nsn_s_n2num_11:
  (nsn_s_n2num n' = nsn_s_n2num n ⇔ n' = n)
Proof
  simp [nsn_s_n2num_def, sum2num_11, nsn2num_11]
QED

Theorem INJ_nsn_s_n2num:
  INJ nsn_s_n2num 𝕌(:(num + num) + num) 𝕌(:num)
Proof
  simp [INJ_IFF, nsn_s_n2num_11]
QED

(* ((num + num) + (num + num)) + (num + num) -> num *)
Definition nsn_s_nsn_s_nsn2num_def:
  nsn_s_nsn_s_nsn2num = sum2num nsn_s_nsn2num nsn2num
End

Theorem nsn_s_nsn_s_nsn2num_11:
  (nsn_s_nsn_s_nsn2num n' = nsn_s_nsn_s_nsn2num n ⇔ n' = n)
Proof
  simp [nsn_s_nsn_s_nsn2num_def, sum2num_11, nsn_s_nsn2num_11, nsn2num_11]
QED

(* ((num + num) + num) + (num + num) -> num *)
Definition nsn_s_n_s_nsn2num_def:
  nsn_s_n_s_nsn2num = sum2num nsn_s_n2num nsn2num
End

Theorem nsn_s_n_s_nsn2num_11:
  (nsn_s_n_s_nsn2num n' = nsn_s_n_s_nsn2num n ⇔ n' = n)
Proof
  simp [nsn_s_n_s_nsn2num_def, sum2num_11, nsn_s_n2num_11, nsn2num_11]
QED

Definition ext2num_def:
  ext2num f (Orig orig) =
    ^ext_name_count + 2 * (f orig) ∧
  ext2num _ (Ext  e) =
    ext_name2num e ∧
  ext2num _ (Anon a) =
    ^ext_name_count + 2 * a + 1
End

Theorem ext2num_11:
  (∀x' x. f x' = f x ⇔ x' = x)
  ⇒
  (ext2num f n' = ext2num f n ⇔ n' = n)
Proof
  strip_tac
  >> simp [oneline ext2num_def]
  >> every_case_tac
  >> simp [ext_name2num_11]
  >> simp [oneline ext_name2num_thm]
  >> every_case_tac >> simp []
  >> pop_assum kall_tac
  >> intLib.COOPER_TAC
QED

(* (num + num) ext -> num *)
Definition nsn_e2num_def:
  nsn_e2num = ext2num nsn2num
End

Theorem nsn_e2num_11:
  (nsn_e2num n' = nsn_e2num n) ⇔ n' = n
Proof
  simp [nsn_e2num_def, ext2num_11, nsn2num_11]
QED

Theorem INJ_nsn_e2num:
  INJ nsn_e2num 𝕌(:(num + num) ext) 𝕌(:num)
Proof
  simp [INJ_IFF, nsn_e2num_11]
QED

(* ((num + num) + (num + num)) ext -> num *)
Definition nsn_s_nsn_e2num_def:
  nsn_s_nsn_e2num = ext2num nsn_s_nsn2num
End

Theorem nsn_s_nsn_e2num_11:
  (nsn_s_nsn_e2num n' = nsn_s_nsn_e2num n) ⇔ n' = n
Proof
  simp [nsn_s_nsn_e2num_def, ext2num_11, nsn_s_nsn2num_11]
QED

Theorem INJ_nsn_s_nsn_e2num:
  INJ nsn_s_nsn_e2num 𝕌(:((num + num) + num + num) ext) 𝕌(:num)
Proof
  simp [INJ_IFF, nsn_s_nsn_e2num_11]
QED

(* num ext -> num *)
Definition n_e2num_def:
  n_e2num = ext2num I
End

Theorem n_e2num_11:
  (n_e2num n' = n_e2num n) ⇔ n' = n
Proof
  simp [n_e2num_def, ext2num_11]
QED

Theorem INJ_n_e2num:
  INJ n_e2num 𝕌(:num ext) 𝕌(:num)
Proof
  simp [INJ_IFF, n_e2num_11]
QED

(* (((num + num) + (num + num)) + (num + num)) ext -> num *)
Definition nsn_s_nsn_s_nsn_e2num_def:
  nsn_s_nsn_s_nsn_e2num = ext2num nsn_s_nsn_s_nsn2num
End

Theorem nsn_s_nsn_s_nsn_e2num_11:
  (nsn_s_nsn_s_nsn_e2num n' = nsn_s_nsn_s_nsn_e2num n) ⇔ n' = n
Proof
  simp [nsn_s_nsn_s_nsn_e2num_def, ext2num_11, nsn_s_nsn_s_nsn2num_11]
QED

Theorem INJ_nsn_s_nsn_s_nsn_e2num:
  INJ nsn_s_nsn_s_nsn_e2num
    𝕌(:(((num + num) + num + num) + num + num) ext) 𝕌(:num)
Proof
  simp [INJ_IFF, nsn_s_nsn_s_nsn_e2num_11]
QED

(* ((num + num) + num) ext -> num *)
Definition nsn_s_n_e2num_def:
  nsn_s_n_e2num = ext2num nsn_s_n2num
End

Theorem nsn_s_n_e2num_11:
  (nsn_s_n_e2num n' = nsn_s_n_e2num n) ⇔ n' = n
Proof
  simp [nsn_s_n_e2num_def, ext2num_11, nsn_s_n2num_11]
QED

Theorem INJ_nsn_s_n_e2num:
  INJ nsn_s_n_e2num 𝕌(:((num + num) + num) ext) 𝕌(:num)
Proof
  simp [INJ_IFF, nsn_s_n_e2num_11]
QED

(* (((num + num) + num) + (num + num)) ext -> num *)
Definition nsn_s_n_s_nsn_e2num_def:
  nsn_s_n_s_nsn_e2num = ext2num nsn_s_n_s_nsn2num
End

Theorem nsn_s_n_s_nsn_e2num_11:
  (nsn_s_n_s_nsn_e2num n' = nsn_s_n_s_nsn_e2num n) ⇔ n' = n
Proof
  simp [nsn_s_n_s_nsn_e2num_def, ext2num_11, nsn_s_n_s_nsn2num_11]
QED

Theorem INJ_nsn_s_n_s_nsn_e2num:
  INJ nsn_s_n_s_nsn_e2num
    𝕌(:(((num + num) + num) + num + num) ext) 𝕌(:num)
Proof
  simp [INJ_IFF, nsn_s_n_s_nsn_e2num_11]
QED

(** Fusing encoding + mapping names to nums ***********************************)

(** Intervention **************************************************************)

Theorem lit_map_o_qinterv_lit:
  lit_map f g h ∘ qinterv_lit f' g' h' i interv =
  qinterv_lit (f ∘ f') (g ∘ g') (h ∘ h') (g ∘ i) interv
Proof
  simp [FUN_EQ_THM, qinterv_lit_def]
  >> Cases >> simp []
  >> CASE_TAC >> simp [GSYM lit_map_o]
  >> CASE_TAC >> simp [lit_map_def, var_map_def, bvar_map_def]
QED

Theorem gty_map_o_qinterv_gty:
  gty_map f g h ∘ qinterv_gty f' g' h' i interv =
  qinterv_gty (f ∘ f') (g ∘ g') (h ∘ h') (g ∘ i) interv
Proof
  simp [FUN_EQ_THM]
  >> Cases >> simp [qinterv_gty_def, gty_map_def]
  >> simp [MAP_MAP_o, GSYM lit_map_o_qinterv_lit]
QED

Theorem gate_map_o_qinterv_gate:
  gate_map f g h ∘ qinterv_gate f' g' h' i interv =
  qinterv_gate (f ∘ f') (g ∘ g') (h ∘ h') (g ∘ i) interv
Proof
  simp [FUN_EQ_THM]
  >> Cases >> simp [qinterv_gate_def, gate_map_def]
  >> simp [GSYM gty_map_o_qinterv_gty]
QED

(*** xaig_map *****************************************************************)

(* Theorem xaig_map_cons: *)
(*   xaig_map f g h (x::xs) = gate_map f g h x :: xaig_map f g h xs *)
(* Proof *)
(*   simp [xaig_map_def] *)
(* QED *)

Theorem xaig_map_append:
  xaig_map f g h (xs ++ ys) = xaig_map f g h xs ++ xaig_map f g h ys
Proof
  simp [xaig_map_def]
QED

(*** encode_ ******************************************************************)

(* Definition mapi_xori_num_aux_def: *)
(*   mapi_xori_num_aux i []      = [] ∧ *)
(*   mapi_xori_num_aux i (x::xs) = (i, Xor (FST x) (SND x))::mapi_xori_num_aux (i + 2) xs *)
(* End *)

(* Definition mapi_xori_num_def: *)
(*   mapi_xori_num n xys = mapi_xori_num_aux (2 * n + 29) xys *)
(* End *)

(* Theorem mapi_xori_num_aux_thm: *)
(*   ∀xys i. *)
(*     mapi_xori_num_aux i xys = MAPi (λj (x,y). (2 * j + i, Xor x y)) xys *)
(* Proof *)
(*   Induct >> rw [mapi_xori_num_aux_def] *)
(*   >> rpt (pairarg_tac >> gvs []) *)
(*   >> simp [o_DEF, ADD1, LEFT_ADD_DISTRIB] *)
(* QED *)

(* Definition and_genlist_num_aux_def: *)
(*   and_genlist_num_aux b i 0       = [] ∧ *)
(*   and_genlist_num_aux b i (SUC c) = *)
(*     (Gate i, b)::and_genlist_num_aux b (i + 2) c *)
(* End *)

(* Definition and_genlist_num_def: *)
(*   and_genlist_num b n cnt = *)
(*     And (and_genlist_num_aux b (2 * n + 29) cnt) *)
(* End *)

(* Theorem and_genlist_num_aux_thm: *)
(*   ∀cnt i. and_genlist_num_aux b i cnt = GENLIST (λj. (Gate (2 * j + i), b)) cnt *)
(* Proof *)
(*   Induct *)
(*   >> rw [and_genlist_num_aux_def, GENLIST_CONS, o_DEF, ADD1, LEFT_ADD_DISTRIB] *)
(* QED *)

(* Definition encode_pointwise_equal_num_def: *)
(*   encode_pointwise_equal_num (xaig: (num, num, num) xaig) (name: num) xys n = *)
(*   let *)
(*     xor_gates = mapi_xori_num n xys; *)
(*     xnor_lits = and_genlist_num T n (LENGTH xys); *)
(*   in *)
(*     (name, xnor_lits)::xor_gates ++ xaig *)
(* End *)

(* Theorem encode_pointwise_equal_to_num: *)
(*   xaig_map f g (ext2num h) (encode_pointwise_equal xaig name xys) = *)
(*   encode_pointwise_equal_num (xaig_map f g (ext2num h) xaig) *)
(*     (ext_name2num name) *)
(*     (MAP *)
(*        (λx. *)
(*           (lit_map f g (ext2num h) (FST x), *)
(*            lit_map f g (ext2num h) (SND x))) xys) *)
(*     (MAX (maxn (MAP FST xys)) (maxn (MAP SND xys))) *)
(* Proof *)
(*   simp [encode_pointwise_equal_def, encode_pointwise_equal_num_def, *)
(*         xaig_map_def, gate_map_def, gty_map_def, ext2num_def, *)
(*         and_genlist_num_def, and_genlist_num_aux_thm, *)
(*         MAP_GENLIST, o_DEF, lit_map_def, var_map_def, ext2num_def, *)
(*         mapi_xori_num_def, mapi_xori_num_aux_thm, LEFT_ADD_DISTRIB, *)
(*         MAPi_MAP] *)
(*   >> irule MAPi_CONG >> rw [] *)
(*   >> simp [oneline xori_def] >> CASE_TAC *)
(*   >> simp [gate_map_def, gty_map_def, ext2num_def] *)
(* QED *)

(*** lit_map ******************************************************************)

(*** 2num *********************************************************************)

Theorem sum2num_sum:
  (sum2num f g ∘ INL = λx. 2 * f x) ∧
  (sum2num f g ∘ INR = λx. 2 * g x + 1)
Proof
  simp [FUN_EQ_THM, sum2num_def]
QED

Theorem sum2num_sum_sum:
  (sum2num (sum2num f g) x ∘ INL ∘ INL =
     λx. 4 * f x) ∧
  (sum2num (sum2num f g) x ∘ INL ∘ INR =
     λx. 4 * g x + 2) ∧
  (sum2num x (sum2num f' g') ∘ INR ∘ INL =
     λx. 4 * f' x + 1) ∧
  (sum2num x (sum2num f' g') ∘ INR ∘ INR =
     λx. 4 * g' x + 3)
Proof
  simp [FUN_EQ_THM, sum2num_def]
QED

Theorem ext2num_Orig:
  ext2num f ∘ Orig = λx. 2 * f x + 28
Proof
  simp [FUN_EQ_THM, ext2num_def,]
QED

Theorem ext2num_sum2num_Orig_sum:
  (ext2num (sum2num f g) ∘ Orig ∘ INL = λx. 4 * f x + 28) ∧
  (ext2num (sum2num f g) ∘ Orig ∘ INR = λx. 4 * g x + 30)
Proof
  simp [FUN_EQ_THM, ext2num_def, sum2num_def]
QED

Theorem ext2num_sum2num_Orig_sum_sum:
  (ext2num (sum2num (sum2num f g) x) ∘ Orig ∘ INL ∘ INL =
     λx. 8 * f x + 28) ∧
  (ext2num (sum2num (sum2num f g) x) ∘ Orig ∘ INL ∘ INR =
     λx. 8 * g x + 32) ∧
  (ext2num (sum2num x (sum2num f' g')) ∘ Orig ∘ INR ∘ INL =
     λx. 8 * f' x + 30) ∧
  (ext2num (sum2num x (sum2num f' g')) ∘ Orig ∘ INR ∘ INR =
     λx. 8 * g' x + 34)
Proof
  simp [FUN_EQ_THM, ext2num_def, sum2num_def]
QED

Theorem ext2num_sum2num_Orig_sum_sum_sum:
  (ext2num (sum2num (sum2num (sum2num f g) x) y) ∘ Orig ∘ INL ∘ INL ∘ INL =
     λx. 16 * f x + 28) ∧
  (ext2num (sum2num (sum2num (sum2num f g) x) y) ∘ Orig ∘ INL ∘ INL ∘ INR =
     λx. 16 * g x + 36) ∧
  (ext2num (sum2num (sum2num x (sum2num f₁ g₁)) y) ∘ Orig ∘ INL ∘ INR ∘ INL =
     λx. 16 * f₁ x + 32) ∧
  (ext2num (sum2num (sum2num x (sum2num f₁ g₁)) y) ∘ Orig ∘ INL ∘ INR ∘ INR =
     λx. 16 * g₁ x + 40)
Proof
  simp [FUN_EQ_THM, ext2num_def, sum2num_def]
QED

fun step ss ths = CONV_RULE (RHS_CONV (SIMP_CONV ss ths))

val ext_case_def = definition "ext_case_def"

val unfold_cond =
  let
    val thms =
      [encode_reset_cond_def, xaig_map_def, FLAT, APPEND_NIL]
    val cnv = SIMP_CONV (pure_ss ++ LET_ss)
  in fn th => cnv (th::thms) end

val collapse_circuits =
  step std_ss
    [ext_xaig_def, merge_xaigs_def, pair_xaigs_def,
     xaig_map_def, MAP_APPEND, MAP_MAP_o, gate_map_o, qxleft_def,
     qinterv_def, qinterv_l_r_def, qinterv_r_l_def, qinterv_ll_r_def,
     qinterv_ll_lr_def, qinterv_lr_r_def,
     lit_map_base_def, live_map_base_def,
     gate_map_o_qinterv_gate, lit_map_o_qinterv_lit, lit_map_o,
     MAP_MAP_o, GSYM MAP_FLAT, GSYM MAP_o]

val encode_imply_to_num =
  step (std_ss ++ LET_ss)
    [encode_imply_def, MAP, MAX_DEF, MAX_LIST_def,
     maxn_def, iname_def, ext_case_def, var_case_def,
     gate_map_def, gty_map_def, lit_map_def, var_map_def]

val encode_xlits_hold_to_num =
  step arith_ss
    [encode_xlits_hold_def, MAP, gate_map_def, gty_map_def, ext2num_def,
     MAP_MAP_o, ext_lit_def, lit_map_o,
     left_lit_def, right_lit_def,
     right_name_lit_def, left_name_lit_def]

val simp2num =
  step std_ss
    [nsn_e2num_def, nsn2num_def, ext2num_def, ext_name2num_thm,
     nsn_s_nsn_s_nsn_e2num_def, nsn_s_nsn_s_nsn2num_def,
     nsn_s_nsn_e2num_def, nsn_s_nsn2num_def, n_e2num_def,
     nsn_s_n_e2num_def, nsn_s_n2num_def, nsn_s_n_s_nsn_e2num_def,
     sum2num_sum, ext2num_sum2num_Orig_sum, ext2num_sum2num_Orig_sum_sum,
     ext2num_sum2num_Orig_sum_sum_sum, nsn_s_n_s_nsn2num_def,
     ext2num_Orig, sum2num_sum_sum]

val reassoc = step pure_ss [GSYM APPEND_ASSOC]

val encode_reset_cond_num =
  “xaig_map (I: num -> num) (I: num -> num) nsn_e2num
      (encode_reset_cond mxaig mreset mcnstrs mlatches wxaig wreset wcnstrs
         wlatches klatches)”
  |> unfold_cond encode_reset_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

val encode_transition_cond_num =
  “xaig_map nsn2num nsn2num nsn_s_nsn_e2num
     (encode_transition_cond
        mxaig mnext mcnstrs mlatches
        wxaig wnext wcnstrs wlatches klatches)”
  |> unfold_cond encode_transition_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

val encode_safety_cond_num =
  “xaig_map I I nsn_e2num
     (encode_safety_cond mxaig mcnstrs msafes wxaig wcnstrs wsafes)”
  |> unfold_cond encode_safety_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

val encode_base_cond_num =
  “xaig_map I I n_e2num
     (encode_base_cond wxaig wreset wcnstrs wsafes wlatches)”
  |> unfold_cond encode_base_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

val encode_induction_cond_num =
  “xaig_map nsn2num nsn2num nsn_e2num
     (encode_induction_cond wxaig wreset wcnstrs wsafes wlatches)”
  |> unfold_cond encode_induction_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

val encode_liveness_cond_num =
  “xaig_map nsn2num nsn2num nsn_s_nsn_s_nsn_e2num
     (encode_liveness_cond
        mxaig mcnstrs mlive
        wxaig wnext wcnstrs wsafes wlive wlatches interv)”
  |> unfold_cond encode_liveness_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

val encode_decrease_cond_num =
  “xaig_map nsn2num nsn2num nsn_s_n_e2num
     (encode_decrease_cond
        wxaig wnext wcnstrs wsafes wlive wlatches interv)”
  |> unfold_cond encode_decrease_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

val encode_closure_cond_num =
  “xaig_map nsn_s_n2num nsn_s_n2num nsn_s_n_s_nsn_e2num
     (encode_closure_cond
        wxaig wnext wcnstrs wsafes wlive wlatches interv)”
  |> unfold_cond encode_closure_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

val encode_stable_cond_num =
  “xaig_map nsn_s_n2num nsn_s_n2num nsn_s_n_s_nsn_e2num
     (encode_stable_cond
        wxaig wnext wcnstrs wsafes wlive wlatches interv)”
  |> unfold_cond encode_stable_cond_def
  |> collapse_circuits
  |> encode_imply_to_num
  |> encode_xlits_hold_to_num
  |> simp2num
  |> reassoc

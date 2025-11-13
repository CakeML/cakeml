(*
  This is an example of applying the translator to the Red-Black
  Set algorithm from Chris Okasaki's book.
*)
Theory RedBlackSet
Ancestors
  okasaki_misc pred_set ListProg
Libs
  preamble pred_setSimps ml_translatorLib

val _ = translation_extends "ListProg";

(* Okasaki page 28 *)

Datatype:
  color = Red | Black
End

Datatype:
  tree = Empty | Tree color tree 'a tree
End

val tree_distinct = fetch "-" "tree_distinct"
val tree_nchotomy = fetch "-" "tree_nchotomy"

Definition tree_to_set_def:
(tree_to_set Empty = {}) ∧
(tree_to_set (Tree _ t1 x t2)  = {x} ∪ tree_to_set t1 ∪ tree_to_set t2)
End

(* The tree is a binary search tree *)
Definition is_bst_def:
(is_bst lt Empty <=> T) ∧
(is_bst lt (Tree _ t1 x t2) <=>
  is_bst lt t1 ∧
  is_bst lt t2 ∧
  (!y. y ∈ tree_to_set t1 ⇒ lt y x) ∧
  (!y. y ∈ tree_to_set t2 ⇒ lt x y))
End

Definition not_red_def:
(not_red (Tree Red t1 x t2) = F) ∧
(not_red _ = T)
End

Definition red_black_invariant1_def:
(red_black_invariant1 Empty <=> T) ∧
(red_black_invariant1 (Tree Black t1 x t2) <=>
  red_black_invariant1 t1 ∧ red_black_invariant1 t2) ∧
(red_black_invariant1 (Tree Red t1 x t2) <=>
  red_black_invariant1 t1 ∧ red_black_invariant1 t2 ∧
  not_red t1 ∧ not_red t2)
End

(* Count the number of black nodes along every path to the root.
 * Return NONE, if this number isn't the same along every path. *)
Definition red_black_invariant2_def:
(red_black_invariant2 Empty = SOME 0) ∧
(red_black_invariant2 (Tree c t1 x t2) =
  case red_black_invariant2 t1 of
     | NONE => NONE
     | SOME n =>
         case red_black_invariant2 t2 of
            | NONE => NONE
            | SOME n' =>
                if n = n' then
                  if c = Black then
                    SOME (n + 1)
                  else
                    SOME n
                else
                  NONE)
End

Definition empty_def:
empty = Empty
End
val r = translate empty_def;

Definition member_def:
(member lt x Empty = F) ∧
(member lt x (Tree _ a y b) =
  if lt x y then
    member lt x a
  else if lt y x then
    member lt x b
  else
    T)
End
val r = translate member_def;

Definition balance_def:
(balance Black (Tree Red (Tree Red a x b) y c) z d =
  Tree Red (Tree Black a x b) y (Tree Black c z d)) ∧

(balance Black (Tree Red a x (Tree Red b y c)) z d =
  Tree Red (Tree Black a x b) y (Tree Black c z d)) ∧

(balance Black a x (Tree Red (Tree Red b y c) z d) =
  Tree Red (Tree Black a x b) y (Tree Black c z d)) ∧

(balance Black a x (Tree Red b y (Tree Red c z d)) =
  Tree Red (Tree Black a x b) y (Tree Black c z d)) ∧

(balance col a x b = Tree col a x b)
End

val balance_ind = fetch "-" "balance_ind"

(* HOL expands the above balance into over 50 cases, so this alternate
 * definition works better for the current translator. *)
Definition balance_left_left_def:
  balance_left_left a z d =
    case a of
    | (Tree Red (Tree Red a x b) y c) =>
         SOME (Tree Red (Tree Black a x b) y (Tree Black c z d))
    | _ => NONE
End
val r = translate balance_left_left_def;

Definition balance_left_right_def:
  balance_left_right a z d =
    case a of
    | (Tree Red a x (Tree Red b y c)) =>
         SOME (Tree Red (Tree Black a x b) y (Tree Black c z d))
    | _ => NONE
End
val r = translate balance_left_right_def;

Definition balance_right_left_def:
  balance_right_left a x b =
    case b of
    | (Tree Red (Tree Red b y c) z d) =>
         SOME (Tree Red (Tree Black a x b) y (Tree Black c z d))
    | _ => NONE
End
val r = translate balance_right_left_def;

Definition balance_right_right_def:
  balance_right_right a x b =
    case b of
    | (Tree Red b y (Tree Red c z d)) =>
         SOME (Tree Red (Tree Black a x b) y (Tree Black c z d))
    | _ => NONE
End
val r = translate balance_right_right_def;

Definition balance'_def:
balance' c a x b =
  if c = Black then
    case balance_left_left a x b of
       | SOME t => t
       | NONE =>
           case balance_left_right a x b of
              | SOME t => t
              | NONE =>
                  case balance_right_left a x b of
                     | SOME t => t
                     | NONE =>
                         case balance_right_right a x b of
                            | SOME t => t
                            | NONE => Tree c a x b
  else
    Tree c a x b
End
val r = translate balance'_def;

Definition ins_def:
(ins lt x Empty = Tree Red Empty x Empty) ∧
(ins lt x (Tree col a y b) =
  if lt x y then
    balance' col (ins lt x a) y b
  else if lt y x then
    balance' col a y (ins lt x b)
  else
    Tree col a y b)
End
val r = translate ins_def;

Definition insert_def:
insert lt x s =
  case ins lt x s of
     | Tree _ a y b => Tree Black a y b
End
val r = translate insert_def;


(* Proof of functional correctness *)

Theorem balance'_correct[local]:
  !c a x b. balance' c a x b = balance c a x b
Proof
  recInduct balance_ind >>
rw [balance'_def, balance_def, balance_left_left_def, balance_left_right_def,
    balance_right_left_def, balance_right_right_def] >>
REPEAT (BasicProvers.FULL_CASE_TAC)
QED

Theorem balance'_tree[local]:
  !c t1 x t2. ∃c' t1' x' t2'. (balance' c t1 x t2 = Tree c' t1' x' t2')
Proof
  recInduct balance_ind >>
rw [balance'_def, balance_left_left_def, balance_left_right_def,
    balance_right_left_def, balance_right_right_def] >>
REPEAT BasicProvers.FULL_CASE_TAC
QED

Theorem balance'_set[local]:
  !c t1 x t2. tree_to_set (balance' c t1 x t2) = tree_to_set (Tree c t1 x t2)
Proof
  recInduct balance_ind >>
srw_tac [PRED_SET_AC_ss]
        [balance'_def, balance_left_left_def, balance_left_right_def,
         balance_right_left_def, balance_right_right_def,
         tree_to_set_def] >>
REPEAT BasicProvers.FULL_CASE_TAC >>
srw_tac [PRED_SET_AC_ss] [tree_to_set_def]
QED

Theorem balance'_bst[local]:
  !c t1 x t2.
  transitive lt ∧ is_bst lt (Tree c t1 x t2)
  ⇒
  is_bst lt (balance' c t1 x t2)
Proof
  recInduct balance_ind >>
rw [transitive_def, balance'_def,  balance_left_left_def,
    balance_left_right_def, balance_right_left_def,
    balance_right_right_def, is_bst_def, tree_to_set_def] >>
fs [transitive_def, balance'_def,  balance_left_left_def,
    balance_left_right_def, balance_right_left_def,
    balance_right_right_def, is_bst_def, tree_to_set_def] >>
REPEAT BasicProvers.FULL_CASE_TAC >>
fs [transitive_def, balance'_def,  balance_left_left_def,
    balance_left_right_def, balance_right_left_def,
    balance_right_right_def, is_bst_def, tree_to_set_def] >>
metis_tac []
QED

Theorem ins_tree[local]:
  !lt x t. ?c t1 y t2. (ins lt x t = Tree c t1 y t2)
Proof
  cases_on `t` >>
rw [ins_def] >>
metis_tac [balance'_tree]
QED

Theorem ins_set[local]:
  ∀lt x t.
  StrongLinearOrder lt
  ⇒
  (tree_to_set (ins lt x t) = {x} ∪ tree_to_set t)
Proof
  induct_on `t` >>
rw [tree_to_set_def, ins_def, balance'_set] >>
fs [] >>
srw_tac [PRED_SET_AC_ss] [] >>
`x = a` by (fs [StrongLinearOrder, StrongOrder, irreflexive_def,
                transitive_def, trichotomous] >>
            metis_tac []) >>
rw []
QED

Theorem ins_bst[local]:
  !lt x t. StrongLinearOrder lt ∧ is_bst lt t ⇒ is_bst lt (ins lt x t)
Proof
  induct_on `t` >>
rw [is_bst_def, ins_def, tree_to_set_def] >>
match_mp_tac balance'_bst >>
rw [is_bst_def] >>
imp_res_tac ins_set >>
fs [StrongLinearOrder, StrongOrder]
QED

Theorem insert_set:
 ∀lt x t.
  StrongLinearOrder lt
  ⇒
  (tree_to_set (insert lt x t) = {x} ∪ tree_to_set t)
Proof
rw [insert_def] >>
`?c t1 y t2. ins lt x t = Tree c t1 y t2` by metis_tac [ins_tree] >>
rw [tree_to_set_def] >>
`tree_to_set (ins lt x t) = tree_to_set (Tree c t1 y t2)`
         by metis_tac [] >>
fs [] >>
imp_res_tac ins_set >>
fs [tree_to_set_def]
QED

Theorem insert_bst:
 !lt x t.
  StrongLinearOrder lt ∧ is_bst lt t
  ⇒
  is_bst lt (insert lt x t)
Proof
rw [insert_def] >>
`?c t1 y t2. ins lt x t = Tree c t1 y t2` by metis_tac [ins_tree] >>
rw [] >>
`is_bst lt (Tree c t1 y t2)` by metis_tac [ins_bst] >>
fs [is_bst_def]
QED

Theorem member_correct:
 !lt t x.
  StrongLinearOrder lt ∧
  is_bst lt t
  ⇒
  (member lt x t <=> x ∈ tree_to_set t)
Proof
strip_tac >> induct_on `t` >>
rw [member_def, is_bst_def, tree_to_set_def] >>
fs [StrongLinearOrder, StrongOrder, irreflexive_def, transitive_def,
    trichotomous] >>
metis_tac []
QED


(* Prove the two red-black invariants that no red node has a red child,
 * and that the number of black nodes is the same on each path from
 * the root to the leaves. *)

Theorem case_opt_lem[local]:
  !x f z.
  ((case x of NONE => NONE | SOME y => f y) = SOME z) =
  (?y. (x = SOME y) ∧ (f y = SOME z))
Proof
  cases_on `x` >>
rw []
QED

Theorem balance_inv2_black[local]:
  !c t1 a t2 n.
  (red_black_invariant2 t1 = SOME n) ∧
  (red_black_invariant2 t2 = SOME n) ∧
  (c = Black)
  ⇒
  (red_black_invariant2 (balance c t1 a t2) = SOME (n+1))
Proof
  recInduct balance_ind >>
rw [balance_def, red_black_invariant2_def, case_opt_lem] >>
metis_tac []
QED

Theorem ins_inv2[local]:
  !leq x t n.
  (red_black_invariant2 t = SOME n)
  ⇒
  (red_black_invariant2 (ins leq x t) = SOME n)
Proof
  induct_on `t` >>
rw [red_black_invariant2_def, ins_def, case_opt_lem] >>
every_case_tac >>
cases_on `c` >>
fs [] >>
rw [] >|
[metis_tac [balance_inv2_black, balance'_correct],
 rw [balance'_def, red_black_invariant2_def, case_opt_lem],
 metis_tac [balance_inv2_black, balance'_correct],
 rw [balance'_def, red_black_invariant2_def, case_opt_lem]]
QED

Theorem insert_invariant2:
 !leq x t n.
  (red_black_invariant2 t = SOME n)
  ⇒
  (red_black_invariant2 (insert leq x t) = SOME n) ∨
  (red_black_invariant2 (insert leq x t) = SOME (n + 1))
Proof
rw [insert_def] >>
cases_on `ins leq x t` >>
rw [] >-
metis_tac [ins_tree, tree_distinct] >>
`red_black_invariant2 (ins leq x t) = SOME n` by metis_tac [ins_inv2] >>
POP_ASSUM MP_TAC >>
rw [red_black_invariant2_def, case_opt_lem] >>
cases_on `n = n''` >>
cases_on `c` >>
fs []
QED

(* Invariant one hold everywhere except for the root node,
 * where it may or may not. *)
Definition rbinv1_root_def:
(rbinv1_root Empty <=> T) ∧
(rbinv1_root (Tree c t1 x t2) <=>
  red_black_invariant1 t1 ∧ red_black_invariant1 t2)
End

Theorem balance_inv1_black[local]:
  !c t1 a t2 n.
  red_black_invariant1 t1 ∧ rbinv1_root t2 ∧ (c = Black)
  ⇒
  red_black_invariant1 (balance c t1 a t2) ∧
  red_black_invariant1 (balance c t2 a t1)
Proof
  recInduct balance_ind >>
rw [balance_def, red_black_invariant1_def, rbinv1_root_def, not_red_def]
QED

Theorem inv1_lemma[local]:
  !t. red_black_invariant1 t ⇒ rbinv1_root t
Proof
  cases_on `t` >>
rw [red_black_invariant1_def, rbinv1_root_def] >>
cases_on `c` >>
fs [red_black_invariant1_def]
QED

Theorem ins_inv1[local]:
  !leq x t.
  red_black_invariant1 t
  ⇒
  (not_red t ⇒ red_black_invariant1 (ins leq x t)) ∧
  (¬not_red t ⇒ rbinv1_root (ins leq x t))
Proof
  induct_on `t` >>
rw [red_black_invariant1_def, rbinv1_root_def, ins_def, not_red_def] >>
cases_on `c` >>
fs [red_black_invariant1_def, not_red_def] >|
[metis_tac [balance_inv1_black, balance'_correct, inv1_lemma],
 rw [balance'_def, rbinv1_root_def],
 metis_tac [balance_inv1_black, balance'_correct, inv1_lemma],
 rw [balance'_def, rbinv1_root_def]]
QED

Theorem insert_invariant1:
 !leq x t. red_black_invariant1 t ⇒ red_black_invariant1 (insert leq x t)
Proof
rw [insert_def] >>
cases_on `ins leq x t` >>
rw [] >-
metis_tac [ins_tree, tree_distinct] >>
`not_red t ⇒ red_black_invariant1 (ins leq x t)` by metis_tac [ins_inv1] >>
`¬not_red t ⇒ rbinv1_root (ins leq x t)` by metis_tac [ins_inv1] >>
POP_ASSUM MP_TAC >>
POP_ASSUM MP_TAC >>
cases_on `not_red t` >>
rw [] >>
cases_on `c` >>
fs [red_black_invariant1_def, rbinv1_root_def]
QED


(* Simplify the side conditions on the generated certificate theorems,
 * based on the verification. *)

val insert_side_def = fetch "-" "insert_side_def"

Theorem insert_side[local]:
  ∀leq x t. insert_side leq x t
Proof
  rw [insert_side_def] >>
`?c t1 y t2. ins leq x t = Tree c t1 y t2` by metis_tac [ins_tree] >>
rw []
QED


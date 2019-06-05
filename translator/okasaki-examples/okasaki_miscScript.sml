(*
  Lemmas used in Okasaki examples.
*)
open preamble
open relationTheory bagLib bagTheory;

val fs = full_simp_tac (srw_ss ())
val rw = srw_tac []

val _ = new_theory "okasaki_misc"

Theorem WeakLinearOrder_neg:
 !leq x y. WeakLinearOrder leq ⇒ (~leq x y <=> leq y x ∧ x ≠ y)
Proof
metis_tac [WeakLinearOrder, WeakOrder, trichotomous, reflexive_def,
           antisymmetric_def]
QED

Theorem BAG_EVERY_DIFF:
 !P b1 b2. BAG_EVERY P b1 ⇒ BAG_EVERY P (BAG_DIFF b1 b2)
Proof
rw [BAG_EVERY] >>
metis_tac [BAG_IN_DIFF_E]
QED

Theorem BAG_EVERY_EL:
 !P x. BAG_EVERY P (EL_BAG x) = P x
Proof
rw [BAG_EVERY, EL_BAG]
QED

Theorem BAG_INN_BAG_DIFF:
 !x m b1 b2.
  BAG_INN x m (BAG_DIFF b1 b2) =
  ∃n1 n2. (m = n1 - n2) ∧
          BAG_INN x n1 b1 ∧ BAG_INN x n2 b2 ∧ ~BAG_INN x (n2 + 1) b2
Proof
rw [BAG_INN, BAG_DIFF] >>
EQ_TAC >>
rw [] >|
[qexists_tac `b2 x + m` >>
     qexists_tac `b2 x` >>
     decide_tac,
 qexists_tac `0` >>
     qexists_tac `b2 x` >>
     decide_tac,
 decide_tac]
QED

Theorem BAG_DIFF_INSERT2:
 !x b. BAG_DIFF (BAG_INSERT x b) (EL_BAG x) = b
Proof
rw [BAG_DIFF, BAG_INSERT, EL_BAG, FUN_EQ_THM, EMPTY_BAG] >>
cases_on `x' = x` >>
rw []
QED

val list_to_bag_def = Define `
(list_to_bag [] = {||}) ∧
(list_to_bag (h::t) = BAG_INSERT h (list_to_bag t))`;

Theorem list_to_bag_filter:
 ∀P l. list_to_bag (FILTER P l) = BAG_FILTER P (list_to_bag l)
Proof
Induct_on `l` >>
rw [list_to_bag_def]
QED

Theorem list_to_bag_append:
 ∀l1 l2. list_to_bag (l1 ++ l2) = BAG_UNION (list_to_bag l1) (list_to_bag l2)
Proof
Induct_on `l1` >>
srw_tac [BAG_ss] [list_to_bag_def, BAG_INSERT_UNION]
QED

val list_to_bag_to_perm = Q.prove (
`!l1 l2. PERM l1 l2 ⇒ (list_to_bag l1 = list_to_bag l2)`,
HO_MATCH_MP_TAC PERM_IND >>
srw_tac [BAG_ss] [list_to_bag_def, BAG_INSERT_UNION]);

val perm_to_list_to_bag_lem = Q.prove (
`!l1 l2 x.
  (list_to_bag (FILTER ($= x) l1) = list_to_bag (FILTER ($= x) l2))
  ⇒
  (FILTER ($= x) l1 = FILTER ($= x) l2)`,
induct_on `l1` >>
rw [] >>
induct_on `l2` >>
rw [] >>
fs [list_to_bag_def]);

val perm_to_list_to_bag = Q.prove (
`!l1 l2. (list_to_bag l1 = list_to_bag l2) ⇒ PERM l1 l2`,
rw [PERM_DEF] >>
metis_tac [perm_to_list_to_bag_lem, list_to_bag_filter]);

Theorem list_to_bag_perm:
 !l1 l2. (list_to_bag l1 = list_to_bag l2) = PERM l1 l2
Proof
metis_tac [perm_to_list_to_bag, list_to_bag_to_perm]
QED

val sorted_reverse_lem = Q.prove (
`!R l. transitive R ∧ SORTED R l ⇒ SORTED (\x y. R y x) (REVERSE l)`,
induct_on `l` >>
rw [SORTED_DEF] >>
match_mp_tac SORTED_APPEND >>
rw [SORTED_DEF] >-
(fs [transitive_def] >>
     metis_tac []) >>
metis_tac [SORTED_EQ]);

Theorem sorted_reverse:
 !R l. transitive R ⇒ (SORTED R (REVERSE l) = SORTED (\x y. R y x) l)
Proof
rw [] >>
EQ_TAC >>
rw [] >>
imp_res_tac sorted_reverse_lem >>
fs [transitive_def] >>
`(\x y. R x y) = R` by metis_tac [] >>
fs [] >>
metis_tac []
QED

val _ = export_theory ();

open preamble
open okasaki_miscTheory bagLib bagTheory sortingTheory ml_translatorLib mini_preludeTheory;
val _ = numLib.prefer_num()

val _ = new_theory "BottomUpMergeSort"

val _ = translation_extends "mini_prelude";

(* Okasaki page 77 *)

(* Note, we're following Chargueraud and just cutting out the laziness since it
 * shouldn't affect functional correctness *)

val _ = type_abbrev ("sortable", ``:num # 'a list list``);

val sortable_inv_def = tDefine "sortable_inv" `
(sortable_inv leq (n,[]) m = (n = 0)) ∧
(sortable_inv leq (n,xs::xss) m =
  if (n = 0) then
    F
  else if n MOD 2 = 0 then
    sortable_inv leq (n DIV 2,xs::xss) (m * 2)
  else
    (LENGTH xs = m) ∧
    SORTED leq xs ∧
    sortable_inv leq (n DIV 2, xss) (m * 2))`
(wf_rel_tac `measure (\(x,(y,z),s). y)` >>
 rw [] >>
 Cases_on `n = 0` >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val sortable_inv_ind = fetch "-" "sortable_inv_ind"

val sortable_to_bag_def = Define `
(sortable_to_bag (size,[]) = {||}) ∧
(sortable_to_bag (size,seg::segs) =
  BAG_UNION (list_to_bag seg) (sortable_to_bag (size-LENGTH seg,segs)))`;

val mrg_def = mlDefine `
(mrg leq [] ys = ys) ∧
(mrg leq xs [] = xs) ∧
(mrg leq (x::xs) (y::ys) =
  if leq x y then
    x :: mrg leq xs (y::ys)
  else
    y :: mrg leq (x::xs) ys)`;

val mrg_ind = fetch "-" "mrg_ind"

val empty_def = mlDefine `
empty = (0, [])`;

val sptree_size = Parse.hide"size"

val add_seg_def = tDefine "add_seg" `
add_seg leq seg segs size =
  if size MOD 2 = 0 then
    seg::segs
  else
    add_seg leq (mrg leq seg (HD segs)) (TL segs) (size DIV 2)`
(wf_rel_tac `measure (\(x,y,z,s). s)` >>
 rw [] >>
 Cases_on `size = 0` >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val add_seg_ind = fetch "-" "add_seg_ind"

val _ = translate add_seg_def;

val add_def = mlDefine `
add leq x (size,segs) = (size+1, add_seg leq [x] segs size)`;

val mrg_all_def = mlDefine `
(mrg_all leq xs [] = xs) ∧
(mrg_all leq xs (seg::segs) = mrg_all leq (mrg leq xs seg) segs)`;

val sort_def = mlDefine `
sort leq (size, segs) = mrg_all leq [] segs`;



(* Functional correctness, and the structural invariant on the size of the lists
 * in the sortable collection.  That is, the nth list has length equal to 2^m,
 * where m is the position of the nth 1 bit in the size of the collection, from
 * least-to-most significant. E.g., if the size is 9, there should be 2 lists,
 * the first of length 1, and the second of length 8.*)

val sortable_inv_sorted = Q.prove (
`!leq size segs m. sortable_inv leq (size,segs) m ⇒ EVERY (SORTED leq) segs`,
recInduct sortable_inv_ind >>
rw [] >>
POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once sortable_inv_def]) >>
fs [] >>
every_case_tac >>
fs []);

val mrg_sorted = Q.prove (
`!leq xs ys.
  WeakLinearOrder leq ∧ SORTED leq xs ∧ SORTED leq ys
  ⇒
  SORTED leq (mrg leq xs ys)`,
recInduct mrg_ind >>
rw [SORTED_DEF,mrg_def] >|
[cases_on `xs`, cases_on `ys`] >>
fs [SORTED_DEF, mrg_def] >>
every_case_tac >>
fs [SORTED_DEF] >>
metis_tac [WeakLinearOrder_neg]);

val mrg_perm = Q.prove (
`!leq xs ys. PERM (mrg leq xs ys) (xs++ys)`,
recInduct mrg_ind >>
rw [mrg_def] >>
metis_tac [PERM_FUN_APPEND, PERM_CONS_IFF, CONS_PERM, PERM_SWAP_AT_FRONT,
           PERM_TRANS, PERM_REFL]);

val mrg_length = Q.prove (
`!leq xs ys. LENGTH (mrg leq xs ys) = LENGTH xs + LENGTH ys`,
recInduct mrg_ind >>
srw_tac [ARITH_ss] [mrg_def]);

val mrg_bag = Q.prove (
`!leq xs ys.
  list_to_bag (mrg leq xs ys) = BAG_UNION (list_to_bag xs) (list_to_bag ys)`,
recInduct mrg_ind >>
srw_tac [BAG_ss] [list_to_bag_def, mrg_def, BAG_INSERT_UNION]);

val add_seg_sub_inv = Q.prove (
`!leq size segs n seg.
  WeakLinearOrder leq ∧
  (n ≠ 0) ∧
  sortable_inv leq (size,segs) n ∧
  SORTED leq seg ∧
  (LENGTH seg = n)
  ⇒
  sortable_inv leq (size+1, add_seg leq seg segs size) n`,
recInduct sortable_inv_ind >>
rw [] >|
[fs [Once sortable_inv_def] >>
     rw [Once add_seg_def] >>
     rw [Once sortable_inv_def] >>
     rw [Once sortable_inv_def],
 `n ≠ 0` by fs [Once sortable_inv_def] >>
     cases_on `n MOD 2 = 0` >>
     fs [] >>
     fs [Once sortable_inv_def] >>
     rw [Once add_seg_def] >>
     rw [Once sortable_inv_def] >|
     [fs [arithmeticTheory.MOD_2] >>
          every_case_tac >>
          fs [arithmeticTheory.EVEN_ADD],
      `0 < 2:num` by rw [] >>
          `(n+1) DIV 2 = n DIV 2 + 1 DIV 2`
                     by metis_tac [arithmeticTheory.ADD_DIV_RWT] >>
          fs [],
      `LENGTH seg + LENGTH xs = LENGTH seg * 2`
                    by decide_tac >>
          `sortable_inv leq (n DIV 2 +  1,
                             add_seg leq (mrg leq seg xs) xss (n DIV 2))
                        (LENGTH seg * 2)`
                    by metis_tac [mrg_sorted, mrg_length] >>
          cases_on `add_seg leq (mrg leq seg xs) xss (n DIV 2)` >>
          fs [] >-
          fs [Once sortable_inv_def] >>
          rw [Once sortable_inv_def] >>
          fs [arithmeticTheory.MOD_2] >>
          every_case_tac >>
          fs [arithmeticTheory.EVEN_ADD] >>
          metis_tac [intLib.ARITH_PROVE
                     ``!n:num. ~EVEN n ⇒ (n DIV 2 + 1 = (n + 1) DIV 2)``]]]);

val add_seg_bag = Q.prove (
`!leq size segs n seg SIZE.
  sortable_inv leq (size,segs) n
  ⇒
  (sortable_to_bag (SIZE, add_seg leq seg segs size) =
   BAG_UNION (list_to_bag seg) (sortable_to_bag (SIZE-LENGTH seg,segs)))`,
recInduct sortable_inv_ind >>
rw [] >|
[fs [Once sortable_inv_def] >>
     rw [Once add_seg_def, sortable_to_bag_def],
 POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once sortable_inv_def]) >>
     cases_on `n MOD 2 = 0` >>
     fs [] >>
     srw_tac [BAG_AC_ss]
             [Once add_seg_def, sortable_to_bag_def, mrg_bag, mrg_length,
              arithmeticTheory.SUB_PLUS]]);

val add_bag = Q.store_thm ("add_bag",
`!leq x size segs.
  sortable_inv leq (size,segs) 1
  ⇒
  (sortable_to_bag (add leq x (size, segs)) =
   BAG_INSERT x (sortable_to_bag (size, segs)))`,
rw [add_def] >>
ASSUME_TAC (Q.SPECL [`leq`, `size`, `segs`, `1`, `[x]`] add_seg_bag) >>
fs [list_to_bag_def, BAG_INSERT_UNION]);

val add_correct = Q.store_thm ("add_correct",
`!leq x size segs.
  WeakLinearOrder leq ∧ sortable_inv leq (size,segs) 1
  ⇒
  sortable_inv leq (add leq x (size,segs)) 1`,
rw [add_def] >>
match_mp_tac add_seg_sub_inv >>
rw [SORTED_DEF]);

val mrg_all_sorted = Q.prove (
`!leq xs segs.
  WeakLinearOrder leq ∧
  EVERY (SORTED leq) segs ∧ SORTED leq xs
  ⇒
  SORTED leq (mrg_all leq xs segs)`,
induct_on `segs` >>
rw [mrg_all_def] >>
metis_tac [mrg_sorted]);

val mrg_all_perm = Q.prove (
`!leq xs segs. PERM (mrg_all leq xs segs) (xs++FLAT segs)`,
induct_on `segs` >>
rw [mrg_all_def] >>
metis_tac [mrg_perm, PERM_CONG, PERM_REFL, PERM_TRANS]);

val sort_sorted = Q.store_thm ("sort_sorted",
`!leq size segs.
  WeakLinearOrder leq ∧ sortable_inv leq (size,segs) 1
  ⇒
  SORTED leq (sort leq (size,segs))`,
rw [sort_def] >>
metis_tac [sortable_inv_sorted, SORTED_DEF, mrg_all_sorted]);

val sortable_to_bag_lem = Q.prove (
`!size segs. sortable_to_bag (size,segs) = list_to_bag (FLAT segs)`,
induct_on `segs` >>
rw [sortable_to_bag_def, list_to_bag_def, list_to_bag_append]);

val sort_bag = Q.store_thm ("sort_bag",
`!leq x size segs.
  list_to_bag (sort leq (size,segs)) = sortable_to_bag (size,segs)`,
rw [sort_def, sortable_to_bag_lem, list_to_bag_perm] >>
metis_tac [mrg_all_perm, APPEND]);


(* Simplify the side conditions on the generated certificate theorems, based on
 * the verification invariant. *)

val add_seg_side_cases = fetch "-" "add_seg_side_def"

val add_seg_side = Q.prove (
`!leq size segs n seg.
  sortable_inv leq (size,segs) n ⇒ add_seg_side leq seg segs size`,
recInduct sortable_inv_ind >>
rw [] >>
ONCE_REWRITE_TAC [Once add_seg_side_cases] >>
rw [] >>
fs [sortable_inv_def] >>
ONCE_REWRITE_TAC [Once add_seg_side_cases] >>
rw []);

val add_side = Q.prove (
`!leq x size segs n.
  sortable_inv leq (size,segs) n ⇒ add_side leq x (size,segs)`,
rw [fetch "-" "add_side_def"] >>
metis_tac [add_seg_side]);

val _ = export_theory();

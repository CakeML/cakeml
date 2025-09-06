(*
  This is an example of applying the translator to the Bottom Up Merge
  Sort algorithm from Chris Okasaki's book.
*)
Theory BottomUpMergeSort
Ancestors
  okasaki_misc bag sorting ListProg
Libs
  preamble bagLib ml_translatorLib

val _ = numLib.temp_prefer_num()

val _ = translation_extends "ListProg";

(* Okasaki page 77 *)

(* Note, we're following Chargueraud and just cutting out the laziness since it
 * shouldn't affect functional correctness *)

Type sortable = ``:num # 'a list list``

Definition sortable_inv_def:
(sortable_inv leq (n,[]) m = (n = 0)) ∧
(sortable_inv leq (n,xs::xss) m =
  if (n = 0) then
    F
  else if n MOD 2 = 0 then
    sortable_inv leq (n DIV 2,xs::xss) (m * 2)
  else
    (LENGTH xs = m) ∧
    SORTED leq xs ∧
    sortable_inv leq (n DIV 2, xss) (m * 2))
Termination
  wf_rel_tac `measure (\(x,(y,z),s). y)` >>
 rw [] >>
 Cases_on `n = 0` >>
 full_simp_tac (srw_ss()++ARITH_ss) []
End

val sortable_inv_ind = fetch "-" "sortable_inv_ind"

Definition sortable_to_bag_def:
(sortable_to_bag (size,[]) = {||}) ∧
(sortable_to_bag (size,seg::segs) =
  BAG_UNION (list_to_bag seg) (sortable_to_bag (size-LENGTH seg,segs)))
End

Definition mrg_def:
(mrg leq [] ys = ys) ∧
(mrg leq xs [] = xs) ∧
(mrg leq (x::xs) (y::ys) =
  if leq x y then
    x :: mrg leq xs (y::ys)
  else
    y :: mrg leq (x::xs) ys)
End
val r = translate mrg_def;

val mrg_ind = fetch "-" "mrg_ind"

Definition empty_def:
empty = (0, [])
End
val r = translate empty_def;

val sptree_size = Parse.hide"size"
val _ = Parse.hide"seg"

Definition add_seg_def:
add_seg leq seg segs size =
  if size MOD 2 = 0 then
    seg::segs
  else
    add_seg leq (mrg leq seg (HD segs)) (TL segs) (size DIV 2)
Termination
  wf_rel_tac `measure (\(x,y,z,s). s)` >>
 rw [] >>
 Cases_on `size = 0` >>
 full_simp_tac (srw_ss()++ARITH_ss) []
End

val add_seg_ind = fetch "-" "add_seg_ind"

val _ = translate add_seg_def;

Definition add_def:
add leq x (size,segs) = (size+1, add_seg leq [x] segs size)
End
val r = translate add_def;

Definition mrg_all_def:
(mrg_all leq xs [] = xs) ∧
(mrg_all leq xs (seg::segs) = mrg_all leq (mrg leq xs seg) segs)
End
val r = translate mrg_all_def;

Definition sort_def:
sort leq (size, segs) = mrg_all leq [] segs
End
val r = translate sort_def;



(* Functional correctness, and the structural invariant on the size of the lists
 * in the sortable collection.  That is, the nth list has length equal to 2^m,
 * where m is the position of the nth 1 bit in the size of the collection, from
 * least-to-most significant. E.g., if the size is 9, there should be 2 lists,
 * the first of length 1, and the second of length 8.*)

Triviality sortable_inv_sorted:
  !leq size segs m. sortable_inv leq (size,segs) m ⇒ EVERY (SORTED leq) segs
Proof
  recInduct sortable_inv_ind >>
rw [] >>
POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once sortable_inv_def]) >>
fs [] >>
every_case_tac >>
fs []
QED

Triviality mrg_sorted:
  !leq xs ys.
  WeakLinearOrder leq ∧ SORTED leq xs ∧ SORTED leq ys
  ⇒
  SORTED leq (mrg leq xs ys)
Proof
  recInduct mrg_ind >>
rw [SORTED_DEF,mrg_def] >|
[cases_on `xs`, cases_on `ys`] >>
fs [SORTED_DEF, mrg_def] >>
every_case_tac >>
fs [SORTED_DEF] >>
metis_tac [WeakLinearOrder_neg]
QED

Triviality mrg_perm:
  !leq xs ys. PERM (mrg leq xs ys) (xs++ys)
Proof
  recInduct mrg_ind >>
rw [mrg_def] >>
metis_tac [PERM_FUN_APPEND, PERM_CONS_IFF, CONS_PERM, PERM_SWAP_AT_FRONT,
           PERM_TRANS, PERM_REFL]
QED

Triviality mrg_length:
  !leq xs ys. LENGTH (mrg leq xs ys) = LENGTH xs + LENGTH ys
Proof
  recInduct mrg_ind >>
srw_tac [ARITH_ss] [mrg_def]
QED

Triviality mrg_bag:
  !leq xs ys.
  list_to_bag (mrg leq xs ys) = BAG_UNION (list_to_bag xs) (list_to_bag ys)
Proof
  recInduct mrg_ind >>
srw_tac [BAG_ss] [list_to_bag_def, mrg_def, BAG_INSERT_UNION]
QED

Triviality add_seg_sub_inv:
  !leq size segs n seg.
  WeakLinearOrder leq ∧
  (n ≠ 0) ∧
  sortable_inv leq (size,segs) n ∧
  SORTED leq seg ∧
  (LENGTH seg = n)
  ⇒
  sortable_inv leq (size+1, add_seg leq seg segs size) n
Proof
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
      `LENGTH seg + LENGTH xs = 2 * LENGTH seg`
                    by decide_tac >>
          `sortable_inv leq (n DIV 2 +  1,
                             add_seg leq (mrg leq seg xs) xss (n DIV 2))
                        (2 * LENGTH seg)`
                    by metis_tac [mrg_sorted, mrg_length] >>
          cases_on `add_seg leq (mrg leq seg xs) xss (n DIV 2)` >>
          fs [] >-
          fs [Once sortable_inv_def] >>
          rw [Once sortable_inv_def] >>
          fs [arithmeticTheory.MOD_2] >>
          every_case_tac >>
          fs [arithmeticTheory.EVEN_ADD] >>
          metis_tac [intLib.ARITH_PROVE
                     ``!n:num. ~EVEN n ⇒ (n DIV 2 + 1 = (n + 1) DIV 2)``]]]
QED

Triviality add_seg_bag:
  !leq size segs n seg SIZE.
  sortable_inv leq (size,segs) n
  ⇒
  (sortable_to_bag (SIZE, add_seg leq seg segs size) =
   BAG_UNION (list_to_bag seg) (sortable_to_bag (SIZE-LENGTH seg,segs)))
Proof
  recInduct sortable_inv_ind >>
rw [] >|
[fs [Once sortable_inv_def] >>
     rw [Once add_seg_def, sortable_to_bag_def],
 POP_ASSUM (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once sortable_inv_def]) >>
     cases_on `n MOD 2 = 0` >>
     fs [] >>
     srw_tac [BAG_AC_ss]
             [Once add_seg_def, sortable_to_bag_def, mrg_bag, mrg_length,
              arithmeticTheory.SUB_PLUS]]
QED

Theorem add_bag:
 !leq x size segs.
  sortable_inv leq (size,segs) 1
  ⇒
  (sortable_to_bag (add leq x (size, segs)) =
   BAG_INSERT x (sortable_to_bag (size, segs)))
Proof
rw [add_def] >>
ASSUME_TAC (Q.SPECL [`leq`, `size`, `segs`, `1`, `[x]`] add_seg_bag) >>
fs [list_to_bag_def, BAG_INSERT_UNION]
QED

Theorem add_correct:
 !leq x size segs.
  WeakLinearOrder leq ∧ sortable_inv leq (size,segs) 1
  ⇒
  sortable_inv leq (add leq x (size,segs)) 1
Proof
rw [add_def] >>
match_mp_tac add_seg_sub_inv >>
rw [SORTED_DEF]
QED

Triviality mrg_all_sorted:
  !leq xs segs.
  WeakLinearOrder leq ∧
  EVERY (SORTED leq) segs ∧ SORTED leq xs
  ⇒
  SORTED leq (mrg_all leq xs segs)
Proof
  induct_on `segs` >>
rw [mrg_all_def] >>
metis_tac [mrg_sorted]
QED

Triviality mrg_all_perm:
  !leq xs segs. PERM (mrg_all leq xs segs) (xs++FLAT segs)
Proof
  induct_on `segs` >>
rw [mrg_all_def] >>
metis_tac [mrg_perm, PERM_CONG, PERM_REFL, PERM_TRANS]
QED

Theorem sort_sorted:
 !leq size segs.
  WeakLinearOrder leq ∧ sortable_inv leq (size,segs) 1
  ⇒
  SORTED leq (sort leq (size,segs))
Proof
rw [sort_def] >>
metis_tac [sortable_inv_sorted, SORTED_DEF, mrg_all_sorted]
QED

Triviality sortable_to_bag_lem:
  !size segs. sortable_to_bag (size,segs) = list_to_bag (FLAT segs)
Proof
  induct_on `segs` >>
rw [sortable_to_bag_def, list_to_bag_def, list_to_bag_append]
QED

Theorem sort_bag:
 !leq x size segs.
  list_to_bag (sort leq (size,segs)) = sortable_to_bag (size,segs)
Proof
rw [sort_def, sortable_to_bag_lem, list_to_bag_perm] >>
metis_tac [mrg_all_perm, APPEND]
QED


(* Simplify the side conditions on the generated certificate theorems, based on
 * the verification invariant. *)

val add_seg_side_cases = fetch "-" "add_seg_side_def"

Triviality add_seg_side:
  !leq size segs n seg.
  sortable_inv leq (size,segs) n ⇒ add_seg_side leq seg segs size
Proof
  recInduct sortable_inv_ind >>
rw [] >>
ONCE_REWRITE_TAC [Once add_seg_side_cases] >>
rw [] >>
fs [sortable_inv_def] >>
ONCE_REWRITE_TAC [Once add_seg_side_cases] >>
rw []
QED

Triviality add_side:
  !leq x size segs n.
  sortable_inv leq (size,segs) n ⇒ add_side leq x (size,segs)
Proof
  rw [fetch "-" "add_side_def"] >>
metis_tac [add_seg_side]
QED


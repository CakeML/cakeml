(*
  This is a simple example of applying the translator to functions over
  finite maps. Finite maps are compiled to CakeML's balanced-tree Map
  module by registering a total order for each key type with
  MapProgLib.add_fmap_for_cmp.
*)
Theory example_fmapProg
Ancestors
  ml_translator MapProg misc comparison mlstring
Libs
  preamble ml_translatorLib ml_progLib MapProgLib

val _ = translation_extends "MapProg";

(*----------------------------------------------------------------------*
   Orderings for the key types. Each one is a monomorphic constant that
   is translated, together with a TotOrd theorem for it; the pair is
   what add_fmap_for_cmp consumes.
 *----------------------------------------------------------------------*)

(* :num and :mlstring are already translated in IntProg and StringProg,
   and both come with a TotOrd theorem, so there is nothing to do. *)

(* :num + mlstring *)

Definition num_str_cmp_def:
  num_str_cmp = sum_cmp num_cmp mlstring$compare
End

Theorem num_str_cmp_eq[local] =
  num_str_cmp_def |> SRULE [sum_cmp_def, FUN_EQ_THM];

val _ = translate num_str_cmp_eq;

Theorem TotOrd_num_str_cmp:
  TotOrd num_str_cmp
Proof
  rewrite_tac [num_str_cmp_def]
  \\ irule TotOrd_sum
  \\ simp [TotOrd_num_cmp, mlstringTheory.TotOrd_compare]
QED

(* :num # mlstring *)

Definition num_str_pair_cmp_def:
  num_str_pair_cmp = pair_cmp num_cmp mlstring$compare
End

Theorem num_str_pair_cmp_eq[local] =
  num_str_pair_cmp_def |> SRULE [comparisonTheory.pair_cmp_def, FUN_EQ_THM];

val _ = translate num_str_pair_cmp_eq;

Theorem TotOrd_num_str_pair_cmp:
  TotOrd num_str_pair_cmp
Proof
  rewrite_tac [num_str_pair_cmp_def]
  \\ irule TotOrd_pair_cmp
  \\ simp [TotOrd_num_cmp, mlstringTheory.TotOrd_compare]
QED

(* :mlstring list *)

val _ = translate ternaryComparisonsTheory.list_compare_def;

Definition str_list_cmp_def:
  str_list_cmp = list_cmp mlstring$compare
End

Theorem str_list_cmp_eq[local] =
  str_list_cmp_def |> SRULE [FUN_EQ_THM];

val _ = translate str_list_cmp_eq;

Theorem TotOrd_str_list_cmp:
  TotOrd str_list_cmp
Proof
  rewrite_tac [str_list_cmp_def]
  \\ irule comparisonTheory.TotOrd_list_cmp
  \\ simp [mlstringTheory.TotOrd_compare]
QED

(* a user-defined key type *)

Datatype:
  ekey = KName mlstring | KIdx num | KBoth mlstring num
End

Definition ekey_cmp_def:
  ekey_cmp k1 k2 =
    case k1 of
    | KName s1 =>
        (case k2 of
         | KName s2 => mlstring$compare s1 s2
         | KIdx _ => LESS
         | KBoth _ _ => LESS)
    | KIdx n1 =>
        (case k2 of
         | KName _ => GREATER
         | KIdx n2 => num_cmp n1 n2
         | KBoth _ _ => LESS)
    | KBoth s1 n1 =>
        (case k2 of
         | KName _ => GREATER
         | KIdx _ => GREATER
         | KBoth s2 n2 =>
             (case mlstring$compare s1 s2 of
              | LESS => LESS
              | EQUAL => num_cmp n1 n2
              | GREATER => GREATER))
End

val _ = translate ekey_cmp_def;

Theorem ekey_forall[local]:
  (∀x. P x) ⇔ (∀s. P (KName s)) ∧ (∀n. P (KIdx n)) ∧ (∀s n. P (KBoth s n))
Proof
  eq_tac \\ rw [] \\ simp [] \\ Cases_on ‘x’ \\ fs []
QED

Theorem TotOrd_ekey_cmp:
  TotOrd ekey_cmp
Proof
  mp_tac mlstringTheory.TotOrd_compare
  \\ mp_tac TotOrd_num_cmp
  \\ fs [totoTheory.TotOrd, ekey_cmp_def, AllCaseEqs(), ekey_forall]
  \\ simp [SF DNF_ss, PULL_EXISTS] \\ rw [] \\ res_tac
  \\ metis_tac []
QED

(* :(ekey # num) list, i.e. the pair, list and user-datatype cases nested *)

Definition ekey_num_cmp_def:
  ekey_num_cmp = pair_cmp ekey_cmp num_cmp
End

Theorem ekey_num_cmp_eq[local] =
  ekey_num_cmp_def |> SRULE [comparisonTheory.pair_cmp_def, FUN_EQ_THM];

val _ = translate ekey_num_cmp_eq;

Theorem TotOrd_ekey_num_cmp[local]:
  TotOrd ekey_num_cmp
Proof
  rewrite_tac [ekey_num_cmp_def]
  \\ irule TotOrd_pair_cmp
  \\ simp [TotOrd_ekey_cmp, TotOrd_num_cmp]
QED

Definition ekey_num_list_cmp_def:
  ekey_num_list_cmp = list_cmp ekey_num_cmp
End

Theorem ekey_num_list_cmp_eq[local] =
  ekey_num_list_cmp_def |> SRULE [FUN_EQ_THM];

val _ = translate ekey_num_list_cmp_eq;

Theorem TotOrd_ekey_num_list_cmp:
  TotOrd ekey_num_list_cmp
Proof
  rewrite_tac [ekey_num_list_cmp_def]
  \\ irule comparisonTheory.TotOrd_list_cmp
  \\ simp [TotOrd_ekey_num_cmp]
QED

(*----------------------------------------------------------------------*
   Register finite maps at each of the key types above
 *----------------------------------------------------------------------*)

val _ = add_fmap_for_cmp TotOrd_num_cmp;
val _ = add_fmap_for_cmp mlstringTheory.TotOrd_compare;
val _ = add_fmap_for_cmp TotOrd_num_str_cmp;
val _ = add_fmap_for_cmp TotOrd_num_str_pair_cmp;
val _ = add_fmap_for_cmp TotOrd_str_list_cmp;
val _ = add_fmap_for_cmp TotOrd_ekey_cmp;
val _ = add_fmap_for_cmp TotOrd_ekey_num_list_cmp;

(*----------------------------------------------------------------------*
   Functions over finite maps. Note that fmap_update must be used
   instead of FUPDATE in definitions that go through translation.
 *----------------------------------------------------------------------*)

(* FEMPTY and fmap_update, at the user-defined key type *)

Definition build_ekey_map_def:
  build_ekey_map [] = (FEMPTY : ekey |-> num) ∧
  build_ekey_map ((k,v)::rest) = fmap_update (build_ekey_map rest) k v
End

val _ = translate build_ekey_map_def;

(* FLOOKUP, at :num + mlstring *)

Definition lookup_default_def:
  lookup_default (m : (num + mlstring) |-> num) k d =
    case FLOOKUP m k of
    | NONE => d
    | SOME v => v
End

val _ = translate lookup_default_def;

(* DOMSUB, at :mlstring list *)

Definition delete_keys_def:
  delete_keys (m : mlstring list |-> num) [] = m ∧
  delete_keys m (k::ks) = delete_keys (m \\ k) ks
End

val _ = translate delete_keys_def;

(* FUNION, at :(ekey # num) list *)

Definition merge_maps_def:
  merge_maps (m1 : (ekey # num) list |-> mlstring) m2 = FUNION m1 m2
End

val _ = translate merge_maps_def;

(* a finite map whose values are themselves finite maps *)

Definition insert_inner_def:
  insert_inner (m : mlstring |-> (num |-> mlstring)) outer k v =
    case FLOOKUP m outer of
    | NONE => fmap_update m outer (fmap_update FEMPTY k v)
    | SOME inner => fmap_update m outer (fmap_update inner k v)
End

val _ = translate insert_inner_def;

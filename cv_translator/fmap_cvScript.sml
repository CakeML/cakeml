(*
  Set up cv translation of fmaps
*)
open preamble cv_transLib cv_stdTheory finite_mapTheory listTheory;
open alistTheory stringTheory;

val _ = new_theory "fmap_cv";

(* -- string as domain -- *)

Definition from_str_fmap_def:
  from_str_fmap (f_a:'a -> cv) (m:string |-> 'a) =
    from_list (from_pair (from_list from_char) f_a)
      (MAP (λk. (k, m ' k)) (QSORT string_le (SET_TO_LIST (FDOM m))))
End

Definition to_str_fmap_def:
  to_str_fmap (t_a:cv -> 'a) (v:cv) =
    FEMPTY |++ (to_list (to_pair (to_list to_char) t_a) v)
End

Theorem from_to_str_fmap[cv_from_to]:
  from_to f_a t_a ⇒
  from_to (from_str_fmap (f_a:'a -> cv)) (to_str_fmap (t_a:cv -> 'a))
Proof
  cheat
QED

(* lookup *)

Theorem FLOOKUP_cv_rep[cv_rep]:
  from_option (f_a:'a -> cv) (FLOOKUP m k) =
  cv_ALOOKUP (from_str_fmap f_a m) (from_list from_char k)
Proof
  cheat
QED

(* update *)

val _ = cv_trans char_lt_def;
val _ = cv_trans string_lt_def;

Definition str_insert_def:
  str_insert [] k v = [(k,v)] ∧
  str_insert ((a,b)::rest) k v =
    if string_lt a k then (a,b)::str_insert rest k v else
    if k = a then (k,v)::rest else (k,v)::(a,b)::rest
End

val _ = cv_trans str_insert_def;
val str_insert_cv_thm = fetch "-" "cv_str_insert_thm";

Theorem FUPDATE_cv_rep[cv_rep]:
  from_str_fmap f_a (m |+ (k,v:'a)) =
  cv_str_insert (from_str_fmap f_a m) (from_list from_char k) (f_a v)
Proof
  cheat
QED

(* test *)

Definition test_def:
  test m = (FLOOKUP m "hi", m |+ ("ho",5:num))
End

val _ = cv_trans test_def;
val res = fetch "-" "cv_test_thm";

val _ = export_theory();

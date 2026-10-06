load "ml_progTheory";
open HolKernel boolLib bossLib Parse simpLib ml_progTheory;

(* Test: does simp with our lemmas eliminate combine_entries? *)
val e1 = ``(empty_entry with sv := SOME v1) with sc := SOME c1``;
val e2 = ``(empty_entry with mv := SOME m2) with mc := SOME n2``;

val target = ``combine_entries ^e1 ^e2``;
val _ = print "\ntarget: "; val _ = print_term target; val _ = print "\n";

val simp_rules =
  [combine_entries_sv_fupd, combine_entries_sc_fupd,
   combine_entries_mv_fupd, combine_entries_mc_fupd,
   combine_entries_empty_left, combine_entries_empty_right];

val result = QCONV (SIMP_CONV (srw_ss()) simp_rules) target
             handle UNCHANGED => REFL target;
val _ = print "after simp: "; val _ = print_term (rhs (concl result)); val _ = print "\n";

(* Overlapping field case *)
val e1' = ``empty_entry with sv := SOME v1``;
val e2' = ``empty_entry with sv := SOME v2``;
val target' = ``combine_entries ^e1' ^e2'``;
val _ = print "\noverlapping target: "; val _ = print_term target'; val _ = print "\n";

val result' = QCONV (SIMP_CONV (srw_ss()) simp_rules) target'
              handle UNCHANGED => REFL target';
val _ = print "after simp: "; val _ = print_term (rhs (concl result')); val _ = print "\n";

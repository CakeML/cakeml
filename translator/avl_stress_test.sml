(* AVL balancing stress test for insert_leaf_into. *)

load "ml_progLib";
open ml_progLib ml_progTheory HolKernel boolLib bossLib Parse;

val _ = print "\n=== AVL sorted-insert stress test ===\n";

val _ = ignore (derive_nsLookup_tree (Define `s0 = write (strlit "k00") (Litv (IntLit 0)) init_env`));
val _ = ignore (derive_nsLookup_tree (Define `s1 = write (strlit "k01") (Litv (IntLit 1)) s0`));
val _ = ignore (derive_nsLookup_tree (Define `s2 = write (strlit "k02") (Litv (IntLit 2)) s1`));
val _ = ignore (derive_nsLookup_tree (Define `s3 = write (strlit "k03") (Litv (IntLit 3)) s2`));
val _ = ignore (derive_nsLookup_tree (Define `s4 = write (strlit "k04") (Litv (IntLit 4)) s3`));
val _ = ignore (derive_nsLookup_tree (Define `s5 = write (strlit "k05") (Litv (IntLit 5)) s4`));
val _ = ignore (derive_nsLookup_tree (Define `s6 = write (strlit "k06") (Litv (IntLit 6)) s5`));
val _ = ignore (derive_nsLookup_tree (Define `s7 = write (strlit "k07") (Litv (IntLit 7)) s6`));
val _ = ignore (derive_nsLookup_tree (Define `s8 = write (strlit "k08") (Litv (IntLit 8)) s7`));
val _ = ignore (derive_nsLookup_tree (Define `s9 = write (strlit "k09") (Litv (IntLit 9)) s8`));

val t00 = nsLookup_conv ``nsLookup_Short s9.v (strlit "k00")``;
val t04 = nsLookup_conv ``nsLookup_Short s9.v (strlit "k04")``;
val t05 = nsLookup_conv ``nsLookup_Short s9.v (strlit "k05")``;
val t09 = nsLookup_conv ``nsLookup_Short s9.v (strlit "k09")``;

fun check nm th expected =
  if aconv (rhs (concl th)) expected
  then print ("  " ^ nm ^ " OK\n")
  else (print_term (rhs (concl th)); print "\n";
        raise Fail ("bad lookup for " ^ nm));

val _ = print "\n-- lookups --\n";
val _ = check "k00" t00 ``SOME (Litv (IntLit 0))``;
val _ = check "k04" t04 ``SOME (Litv (IntLit 4))``;
val _ = check "k05" t05 ``SOME (Litv (IntLit 5))``;
val _ = check "k09" t09 ``SOME (Litv (IntLit 9))``;

val _ = print "\n=== AVL stress test PASSED ===\n";

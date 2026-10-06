(* Test coalescing merge: both envs derived from init_env, with fresh key
   on each side.  Without legacy, the tree path should handle this. *)
load "ml_progLib";
open ml_progLib ml_progTheory HolKernel boolLib bossLib Parse;

val _ = print "\n=== coalescing merge test ===\n";

val _ = ignore (derive_nsLookup_tree (Define `ct_a = write_cons (strlit "AAA") (1n, TypeStamp (strlit "AAA") 99n) init_env`));
val _ = ignore (derive_nsLookup_tree (Define `ct_b = write_cons (strlit "ZZZ") (0n, ExnStamp 88n) init_env`));

val _ = print "Registered ct_a and ct_b (both based on init_env).\n";

val merge_def = Define `ct_merged = merge_env ct_a ct_b`;
val _ = ignore (derive_nsLookup_tree merge_def);

val _ = print "Coalesced merge succeeded!\n";

(* Verify lookups *)
val t_aaa = nsLookup_conv ``nsLookup_Short ct_merged.c (strlit "AAA")``;
val t_zzz = nsLookup_conv ``nsLookup_Short ct_merged.c (strlit "ZZZ")``;
val t_init = nsLookup_conv ``nsLookup_Short ct_merged.c (strlit "Bind")``;

fun check nm th expected =
  if aconv (rhs (concl th)) expected
  then print ("  " ^ nm ^ " OK\n")
  else (print_term (rhs (concl th)); print "\n";
        raise Fail ("bad lookup for " ^ nm));

val _ = check "AAA" t_aaa ``SOME (1n, TypeStamp (strlit "AAA") 99n)``;
val _ = check "ZZZ" t_zzz ``SOME (0n, ExnStamp 88n)``;
val _ = check "Bind (shared from init_env)" t_init ``SOME (0n, ExnStamp 0n)``;

val _ = if env_tree_has ``ct_merged``
        then print "env_tree_has ct_merged: true\n"
        else raise Fail "env_tree_has ct_merged: false";

val _ = print "\n=== coalescing merge test PASSED ===\n";

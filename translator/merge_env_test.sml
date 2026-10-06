(* Test: derive_nsLookup_tree handles `env = merge_env a b` with disjoint
   key ranges by building EnvBranch tree_a tree_b and registering. *)

load "ml_progLib";
open ml_progLib ml_progTheory HolKernel boolLib bossLib Parse;

val _ = print "\n=== merge_env push-down test ===\n";

(* Two empty-based envs with disjoint key ranges: "aaa..." on the left,
   "zzz..." on the right. *)
val _ = ignore (derive_nsLookup_tree (Define `m_left = write (strlit "aaa") (Litv (IntLit 10)) empty_env`));
val _ = ignore (derive_nsLookup_tree (Define `m_right = write (strlit "zzz") (Litv (IntLit 99)) empty_env`));

val _ = print "Registered m_left (aaa) and m_right (zzz).\n";

(* Merge them — ranges disjoint, so the disjoint-gap check succeeds. *)
val _ = ignore (derive_nsLookup_tree (Define `m_merged = merge_env m_left m_right`));

val _ = print "Registered m_merged = merge_env m_left m_right.\n";

(* Verify lookup works on both keys via the merged tree. *)
val t_aaa = nsLookup_conv ``nsLookup_Short m_merged.v (strlit "aaa")``;
val t_zzz = nsLookup_conv ``nsLookup_Short m_merged.v (strlit "zzz")``;

fun check nm th expected =
  if aconv (rhs (concl th)) expected
  then print ("  " ^ nm ^ " OK\n")
  else (print_term (rhs (concl th)); print "\n";
        raise Fail ("bad lookup for " ^ nm));

val _ = check "aaa" t_aaa ``SOME (Litv (IntLit 10))``;
val _ = check "zzz" t_zzz ``SOME (Litv (IntLit 99))``;

(* Verify env_tree_has m_merged = true *)
val _ = if env_tree_has ``m_merged``
        then print "  env_tree_has m_merged: true (eagerly cached) OK\n"
        else raise Fail "env_tree_has m_merged: false — not cached";

val _ = print "\n=== merge_env push-down test PASSED ===\n";

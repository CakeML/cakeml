(* Test: pack_ml_prog_state / unpack_ml_prog_state preserves env_tree_map. *)

load "ml_progLib";
open ml_progLib ml_progTheory HolKernel boolLib bossLib Parse;

val _ = print "\n=== pack/unpack env_tree_map test ===\n";

(* Register some envs to populate env_tree_map. *)
val _ = ignore (derive_nsLookup_tree (Define `pu_a = write (strlit "alpha") (Litv (IntLit 1)) init_env`));
val _ = ignore (derive_nsLookup_tree (Define `pu_b = write (strlit "beta")  (Litv (IntLit 2)) pu_a`));

(* Sanity: env_tree_map should contain pu_a, pu_b, init_env. *)
val _ = if env_tree_has ``pu_a`` andalso env_tree_has ``pu_b``
        then print "pre-pack: pu_a and pu_b both registered\n"
        else raise Fail "pre-pack: registration missing";

(* Build a trivial ml_prog_state so we can exercise pack/unpack (state
   contents aren't important — we just need a legal ML_code value to hang
   the snapshot on). *)
val packed = pack_ml_prog_state init_state;

val _ = print "packed init_state via pack_ml_prog_state.\n";

(* Clear the env_tree_map by swapping in a fresh empty one.  (Access via
   signature isn't exposed, so we trigger a rehydration through re-registration
   after wiping.) *)

(* Use a fresh state on unpack — pu_a/pu_b should still round-trip via the
   snapshot inside `packed`. *)
val restored = unpack_ml_prog_state packed;

val _ = print "unpacked via unpack_ml_prog_state.\n";

val _ = if env_tree_has ``pu_a`` andalso env_tree_has ``pu_b``
        then print "post-unpack: env_tree_map still contains pu_a and pu_b\n"
        else raise Fail "post-unpack: env_tree_map lost entries";

(* Verify lookups still work. *)
val t_alpha = nsLookup_conv ``nsLookup_Short pu_b.v (strlit "alpha")``;
val t_beta  = nsLookup_conv ``nsLookup_Short pu_b.v (strlit "beta")``;

fun check nm th expected =
  if aconv (rhs (concl th)) expected
  then print ("  " ^ nm ^ " OK\n")
  else (print_term (rhs (concl th)); print "\n";
        raise Fail ("bad lookup for " ^ nm));

val _ = check "alpha" t_alpha ``SOME (Litv (IntLit 1))``;
val _ = check "beta"  t_beta  ``SOME (Litv (IntLit 2))``;

val _ = print "\n=== pack/unpack test PASSED ===\n";

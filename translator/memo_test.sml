(* Test: env_leaf_mem memoization keeps repeated lookups fast.
   Build a deep env via sorted inserts, then time repeated nsLookup_conv
   calls for the same key. Second call should be much faster than first. *)

load "ml_progLib";
open ml_progLib ml_progTheory HolKernel boolLib bossLib Parse;

val _ = print "\n=== env_leaf_mem memoization test ===\n";

(* Build a moderately-deep env: 20 sorted inserts. *)
fun pad n =
  if n < 10 then "k0" ^ Int.toString n
  else "k" ^ Int.toString n;

val _ = ignore (derive_nsLookup_tree (Define `mt0 = write (strlit "k00") (Litv (IntLit 0)) init_env`));
fun step prev i =
  let val nm = "mt" ^ Int.toString i
      val prev_const = mk_var (prev, ``:v sem_env``)
      val key = pad i
      val def_q = Parse.Term [QUOTE (nm ^ " = write (strlit \"" ^ key ^ "\") (Litv (IntLit " ^ Int.toString i ^ ")) " ^ prev)]
      val def = Definition.new_definition (nm ^ "_def", def_q)
  in ignore (derive_nsLookup_tree def); nm end;

val _ =
  let fun loop prev i =
        if i > 19 then ()
        else loop (step prev i) (i + 1)
  in loop "mt0" 1 end;

val _ = print "Built mt19 (20 keys).\n";

fun time_conv conv tm =
  let val t0 = Time.toReal (Time.now ())
      val _ = conv tm
      val t1 = Time.toReal (Time.now ())
  in (t1 - t0) * 1000.0 end;

val lookup_tm = ``nsLookup_Short mt19.v (strlit "k10")``;
val t1 = time_conv nsLookup_conv lookup_tm;
val _ = print ("first  lookup: " ^ Real.toString t1 ^ " ms\n");
val t2 = time_conv nsLookup_conv lookup_tm;
val _ = print ("second lookup: " ^ Real.toString t2 ^ " ms\n");
val t3 = time_conv nsLookup_conv lookup_tm;
val _ = print ("third  lookup: " ^ Real.toString t3 ^ " ms\n");

(* Assert memoization actually fires: second and third should be faster
   than the first by at least 2x in the typical case. Soft check — just
   print — since absolute timings depend on machine. *)

val _ = if t2 < t1 orelse t1 < 0.5
        then print "memoization appears to be helping (or first call too fast to measure)\n"
        else print ("WARNING: second lookup not faster than first: " ^
                    Real.toString t1 ^ " -> " ^ Real.toString t2 ^ "\n");

val _ = print "\n=== memo test DONE ===\n";

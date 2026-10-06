(*
  Standalone test for rebalance_join_with: builds simple env_node trees
  from leaves and exercises both NORMAL and ROTATE paths.
*)
Theory avl_join_test
Ancestors
  ml_prog
Libs
  preamble ml_progLib

val () = print "\n=== avl_join_test ===\n";

val a = ml_progLib.mk_leaf "a01";
val b = ml_progLib.mk_leaf "a02";
val c = ml_progLib.mk_leaf "a03";
val d = ml_progLib.mk_leaf "a04";
val e = ml_progLib.mk_leaf "a05";

(* Pairwise join *)
val (ab, _) = ml_progLib.rebalance_join_test a b;
val () = print ("ab depth = " ^ Int.toString (ml_progLib.depth_of ab) ^ "\n");

val (bc, _) = ml_progLib.rebalance_join_test b c;
val () = print ("bc depth = " ^ Int.toString (ml_progLib.depth_of bc) ^ "\n");

(* Right-heavy: a join (b,c). depth(a)=1, depth(bc)=2. Looping case *)
val (a_bc, _) = ml_progLib.rebalance_join_test a bc;
val () = print ("a_bc depth = " ^ Int.toString (ml_progLib.depth_of a_bc) ^ "\n");
val () = print ("a_bc tree = " ^ Parse.term_to_string (ml_progLib.tree_tm_of a_bc) ^ "\n");

(* The looping shape: (a, (b,c)) join d. *)
val () = print "\n=== Looping case test ===\n";
val (result, _) = ml_progLib.rebalance_join_test a_bc d;
val () = print ("(a, (b,c)) join d : depth = " ^ Int.toString (ml_progLib.depth_of result) ^ "\n");
val () = print ("tree = " ^ Parse.term_to_string (ml_progLib.tree_tm_of result) ^ "\n");

(* Build a deeper right-heavy tree to test multi-level rotation. *)
val () = print "\n=== Deep right-heavy ===\n";
val (cd, _) = ml_progLib.rebalance_join_test c d;
val (b_cd, _) = ml_progLib.rebalance_join_test b cd;
val () = print ("b_cd depth = " ^ Int.toString (ml_progLib.depth_of b_cd) ^ "\n");
val (a_b_cd, _) = ml_progLib.rebalance_join_test a b_cd;
val () = print ("a_b_cd depth = " ^ Int.toString (ml_progLib.depth_of a_b_cd) ^ "\n");
val (deep_result, _) = ml_progLib.rebalance_join_test a_b_cd e;
val () = print ("(a, (b, (c, d))) join e : depth = " ^ Int.toString (ml_progLib.depth_of deep_result) ^ "\n");
val () = print ("tree = " ^ Parse.term_to_string (ml_progLib.tree_tm_of deep_result) ^ "\n");

(* The hypothesized failing case:
   A right-heavy at depth 4, A.right right-heavy at depth 3.
   A.r = Branch(x, Branch(y, z))  (right-heavy, depth 3)
   A.l = Branch(p, q)              (depth 2)
   A   = Branch(A.l, A.r)          (right-heavy depth 4)
   B   = Branch(w, v)              (depth 2)
   diff(A, B) = 2, A right-heavy, A.r right-heavy. *)
val () = print "\n=== A right-heavy + A.r right-heavy ===\n";
val p = ml_progLib.mk_leaf "b01";
val q = ml_progLib.mk_leaf "b02";
val x = ml_progLib.mk_leaf "b03";
val y = ml_progLib.mk_leaf "b04";
val z = ml_progLib.mk_leaf "b05";
val w = ml_progLib.mk_leaf "b06";
val v = ml_progLib.mk_leaf "b07";

val (yz, _) = ml_progLib.rebalance_join_test y z;       (* depth 2 *)
val (x_yz, _) = ml_progLib.rebalance_join_test x yz;    (* depth 3, right-heavy *)
val () = print ("x_yz depth = " ^ Int.toString (ml_progLib.depth_of x_yz) ^ "\n");
val () = print ("x_yz tree = " ^ Parse.term_to_string (ml_progLib.tree_tm_of x_yz) ^ "\n");

val (pq, _) = ml_progLib.rebalance_join_test p q;       (* depth 2 *)
val (big_a, _) = ml_progLib.rebalance_join_test pq x_yz; (* depth 4, right-heavy *)
val () = print ("big_a depth = " ^ Int.toString (ml_progLib.depth_of big_a) ^ "\n");
val () = print ("big_a tree = " ^ Parse.term_to_string (ml_progLib.tree_tm_of big_a) ^ "\n");

val (wv, _) = ml_progLib.rebalance_join_test w v;       (* depth 2 *)

(* The test: join (depth 4 right-heavy where A.r is right-heavy) with depth 2 *)
val (final, _) = ml_progLib.rebalance_join_test big_a wv;
val () = print ("FINAL depth = " ^ Int.toString (ml_progLib.depth_of final) ^ "\n");
val () = print ("FINAL tree = " ^ Parse.term_to_string (ml_progLib.tree_tm_of final) ^ "\n");

val () = print "\nDONE\n";

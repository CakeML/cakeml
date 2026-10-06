load "ml_progTheory";
open HolKernel boolLib bossLib Parse;

val cons_tm = prim_mk_const {Name = "recordtype.env_entry", Thy = "ml_prog"};
val _ = print "cons_tm = "; val _ = print_term cons_tm;
val _ = print "\ntype = "; val _ = print_type (type_of cons_tm); val _ = print "\n";

val r1 = list_mk_comb (cons_tm,
  [``SOME (Litv (IntLit 0))``,
   ``NONE : (num # stamp) option``,
   ``NONE : (mlstring, mlstring, v) namespace option``,
   ``NONE : (mlstring, mlstring, (num # stamp)) namespace option``]);

val r2 = ``<| sv := SOME (Litv (IntLit 0)); sc := NONE;
              mv := NONE; mc := NONE |> : env_entry``;

val _ = print "\nr1 (via list_mk_comb): "; val _ = print_term r1;
val _ = print "\nr2 (via <|..|>):       "; val _ = print_term r2;
val _ = print ("\naconv: " ^ Bool.toString (aconv r1 r2) ^ "\n\n");

(* Show the head constants *)
val _ = print ("r1 head: " ^ (fst (dest_const (fst (strip_comb r1)))
                              handle _ => "(non-const)") ^ "\n");
val _ = print ("r2 head: " ^ (fst (dest_const (fst (strip_comb r2)))
                              handle _ => "(non-const)") ^ "\n");

(* Show with types *)
val _ = Feedback.set_trace "types" 1;
val _ = print "\nr1 with types: "; val _ = print_term r1; val _ = print "\n";
val _ = print "r2 with types: "; val _ = print_term r2; val _ = print "\n";

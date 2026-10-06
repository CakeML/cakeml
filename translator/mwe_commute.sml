(* Minimum repro for the MATCH_MP issue with tree_lookup_commute_cps. *)
load "ml_progTheory";
open HolKernel boolLib bossLib Parse ml_progTheory;

(* Make up some concrete variables. *)
val L_tm = mk_var ("L", mk_type ("env_tree", []));
val R_tm = mk_var ("R", mk_type ("env_tree", []));
val leaf_tm = mk_var ("lf", mk_type ("env_tree", []));

val mlstring_ty = mk_type ("mlstring", []);
val kl = mk_var ("kL", mlstring_ty);
val kr1 = mk_var ("kR1", mlstring_ty);
val kr2 = mk_var ("kR2", mlstring_ty);
val klf = mk_var ("klf", mlstring_ty);

(* Assume hypotheses *)
val Tdef = ASSUME ``T_tt = EnvBranch ^L_tm ^R_tm``;
val wf_R = ASSUME ``env_wf ^R_tm ^kr1 ^kr2``;
val wf_leaf = ASSUME ``env_wf ^leaf_tm ^klf ^klf``;
val disj_thm = ASSUME ``mlstring_lt ^kr2 ^klf \/ mlstring_lt ^klf ^kr1``;

val refl_tT = REFL ``EnvBranch T_tt ^leaf_tm``;
val refl_tLinner' = REFL ``EnvBranch ^L_tm ^leaf_tm``;
val refl_tT' = REFL ``EnvBranch (EnvBranch ^L_tm ^leaf_tm) ^R_tm``;

val hyps = LIST_CONJ [Tdef, refl_tT, refl_tLinner', refl_tT', wf_R, wf_leaf, disj_thm];
val _ = print "hyps:\n"; val _ = print_thm hyps; val _ = print "\n";

val r = MATCH_MP tree_lookup_commute_cps hyps
        handle e => (print ("FAILED: " ^ General.exnMessage e ^ "\n"); TRUTH);
val _ = print_thm r;

load "ml_progLib";
load "ml_translatorLib";
open ml_progLib ml_progTheory HolKernel boolLib bossLib Parse;

val tm = ``lookup_cons (Short (strlit "Some"))
             (merge_env empty_env
                (merge_env empty_env init_env)) = NONE``;

val step1 = REWRITE_CONV [ml_progTheory.lookup_cons_def] tm;
val _ = print "\nafter lookup_cons_def:\n"; val _ = print_term (rhs (concl step1)); val _ = print "\n";

val step2 = CONV_RULE (RAND_CONV (TOP_DEPTH_CONV nsLookup_conv)) step1
            handle e => (print ("step2 error: " ^ General.exnMessage e ^ "\n"); step1);
val _ = print "\nafter TOP_DEPTH_CONV nsLookup_conv:\n"; val _ = print_term (rhs (concl step2)); val _ = print "\n";

val step3 = CONV_RULE (RAND_CONV EVAL) step2;
val _ = print "\nafter EVAL:\n"; val _ = print_term (rhs (concl step3)); val _ = print "\n";

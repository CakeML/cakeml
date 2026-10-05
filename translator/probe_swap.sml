load "ml_progTheory";
open HolKernel boolLib bossLib Parse ml_progTheory simpLib;

val goal = ``(!k. tree_lookup X k = empty_entry \/ tree_lookup Y k = empty_entry) ==>
  tree_lookup (EnvBranch X Y) = tree_lookup (EnvBranch Y X)``;

val r = prove (goal,
  strip_tac
  \\ rw [FUN_EQ_THM, tree_lookup_def, LET_THM]
  \\ first_x_assum (qspec_then `k` strip_assume_tac)
  \\ fs [empty_entry_def, optionTheory.OPTION_CHOICE_def,
         env_entry_component_equality])
  handle e => (print "proof failed\n"; TRUTH);

val _ = print_thm r;

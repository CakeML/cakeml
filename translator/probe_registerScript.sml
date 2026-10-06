Theory probe_register
Libs
  ml_progLib ml_translatorLib

val _ = print "\n=== probe init_env registration with no ancestor ===\n";
val _ = ignore (ml_progLib.derive_nsLookup_tree
                  (Define `pr_a = write (strlit "a") (Litv (IntLit 0)) init_env`));
val _ = print "pr_a registered\n";

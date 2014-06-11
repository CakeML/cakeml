open HolKernel Parse boolLib bossLib; val _ = new_theory "std_prelude";

open listTheory pairTheory ml_translatorLib ml_translatorTheory;

val _ = std_preludeLib.std_prelude ();

val _ = (print_asts := true);

val _ = export_theory();

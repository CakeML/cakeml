open HolKernel Parse boolLib bossLib; val _ = new_theory "mini_prelude";

open listTheory pairTheory ml_translatorLib ml_translatorTheory;

val _ = mini_preludeLib.mini_prelude ();

val _ = (print_asts := true);

val _ = export_theory();

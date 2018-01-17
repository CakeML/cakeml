
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_balanced_bst";

open comparisonTheory balanced_mapTheory;

open ml_translatorLib;

val _ = register_type ``:('k,'v) balanced_map``;

val _ = translate lookup_def;
val _ = translate singleton_def;
val _ = translate ratio_def;
val _ = translate size_def;
val _ = translate delta_def;
val _ = translate balanceL_def;
val _ = translate balanceR_def;
val _ = translate insert_def;
val _ = translate num_cmp_def;

val _ = export_theory();



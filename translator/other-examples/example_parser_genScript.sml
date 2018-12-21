(*
  This is a simple example of applying the translator to a
  parser generator.
*)
open HolKernel Parse boolLib bossLib; val _ = new_theory "example_parser_gen";

open slr_parser_genTheory optionTheory;
open ml_translatorTheory ml_translatorLib ListProgTheory;

val _ = translation_extends "ListProg";

val res = translate push_def;
val res = translate pop_def;
val res = translate take1_def;
val res = translate take_def;
val res = translate isNonTmnlSym_def;
val res = translate sym2Str_def;
val res = translate ruleRhs_def;
val res = translate ruleLhs_def;
val res = translate ptree2Sym_def;
val res = translate THE_DEF;
val res = translate buildTree_def;
val res = translate addRule_def;
val res = translate stackSyms_def;
val res = translate findItemInRules_def;
val res = translate itemEqRuleList_def;
val res = translate getState_def;
val res = translate stackSyms_def;
val res = translate exitCond_def;
val res = translate init_def;
val res = translate doReduce_def;
val res = translate parse_def;
val res = translate (parser_def |> SIMP_RULE std_ss [mwhile_def]);

val _ = export_theory();

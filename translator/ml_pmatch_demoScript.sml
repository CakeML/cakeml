open HolKernel Parse boolLib bossLib;
open deepMatchesLib ml_translatorLib;

val _ = new_theory "ml_pmatch_demo";

val foo_def = Define `
  foo f x k = case f x of ([t]::[y]::ys) => t + y + (3:num) + k | _ => 5`

val c = (PMATCH_INTRO_CONV THENC PMATCH_SIMP_CONV)

val def = CONV_RULE (TOP_DEPTH_CONV c) foo_def

val res = translate def;

val _ = export_theory();

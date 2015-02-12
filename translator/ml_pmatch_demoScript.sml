open HolKernel Parse boolLib bossLib;
open deepMatchesLib ml_translatorLib;

val _ = new_theory "ml_pmatch_demo";

(* basic example *)

val foo_def = Define `
  foo f x k = case f x of ([t]::[y]::ys) => t + y + (3:num) + k | _ => 5`

val c = (PMATCH_INTRO_CONV THENC PMATCH_SIMP_CONV)

val def = CONV_RULE (TOP_DEPTH_CONV c) foo_def

val res = translate def;

(* red-black tree example *)

val _ = Datatype `
  color = Red | Black`;

val _ = Datatype `
  tree = Empty | Tree color tree 'a tree`;

(* causes the normal case-of syntax to be parsed as PMATCH *)
val _ = set_trace "parse deep cases" 1;

val balance_black_def = Define `
  balance_black a n b =
    case (a,b) of
    | (Tree Red (Tree Red a x b) y c,d) =>
      Tree Red (Tree Black a x b) y (Tree Black c n d)
    | (Tree Red a x (Tree Red b y c),d) =>
      Tree Red (Tree Black a x b) y (Tree Black c n d)
    | (a,Tree Red (Tree Red b y c) z d) =>
      Tree Red (Tree Black a n b) y (Tree Black c z d)
    | (a,Tree Red b y (Tree Red c z d)) =>
      Tree Red (Tree Black a n b) y (Tree Black c z d)
    | other => Tree Black a n b`

val _ = set_trace "parse deep cases" 0;

val res = translate balance_black_def;

val _ = export_theory();

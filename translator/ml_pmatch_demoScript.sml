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
  tree = Empty
       | Red tree 'a tree
       | Black tree 'a tree`;

(* causes the normal case-of syntax to be parsed as PMATCH *)
val _ = set_trace "parse deep cases" 1;

val balance_black_def = Define `
  balance_black a n b =
    case (a,b) of
    | (Red (Red a x b) y c,d) => Red (Black a x b) y (Black c n d)
    | (Red a x (Red b y c),d) => Red (Black a x b) y (Black c n d)
    | (a,Red (Red b y c) z d) => Red (Black a n b) y (Black c z d)
    | (a,Red b y (Red c z d)) => Red (Black a n b) y (Black c z d)
    | other => Black a n b`

val _ = set_trace "parse deep cases" 0;

val res = translate balance_black_def;

val _ = export_theory();

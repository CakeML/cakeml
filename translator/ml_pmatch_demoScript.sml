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

val balance_black_def = Define `
  balance_black a n b =
    PMATCH (a,b)
      [PMATCH_ROW
         (\(a,x,b,y,c,d). (Tree Red (Tree Red a x b) y c,d))
         (\(a,x,b,y,c,d). T)
         (\(a,x,b,y,c,d). Tree Red (Tree Black a x b) y (Tree Black c n d));
       PMATCH_ROW
         (\(a,x,b,y,c,d). ((Tree Red a x (Tree Red b y c)),d))
         (\(a,x,b,y,c,d). T)
         (\(a,x,b,y,c,d). Tree Red (Tree Black a x b) y (Tree Black c n d));
       PMATCH_ROW
         (\(a,b,y,c,z,d). (a,(Tree Red (Tree Red b y c) z d)))
         (\(a,b,y,c,z,d). T)
         (\(a,b,y,c,z,d). Tree Red (Tree Black a n b) y (Tree Black c z d));
       PMATCH_ROW
         (\(a,b,y,c,z,d). (a,(Tree Red b y (Tree Red c z d))))
         (\(a,b,y,c,z,d). T)
         (\(a,b,y,c,z,d). Tree Red (Tree Black a n b) y (Tree Black c z d));
       PMATCH_ROW
         (\(a,b). (a,b))
         (\(a,b). T)
         (\(a,b). Tree Black a n b)]`

val res = translate balance_black_def;

val _ = export_theory();

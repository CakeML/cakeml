(*
  Renamnts of Lem dependency
*)
open HolKernel Parse boolLib bossLib;
open alistTheory llistTheory sptreeTheory wordsTheory integer_wordTheory;

val _ = numLib.temp_prefer_num();

val _ = new_theory "lib"

 val _ = Define `
 ((the:'a -> 'a option -> 'a) _ (SOME x)=  x) /\ ((the:'a -> 'a option -> 'a) x NONE=  x)`;

val _ = Define `
 ((fapply:'a -> 'b ->('b,'a)fmap -> 'a) d x f=  ((case FLOOKUP f x of SOME d => d | NONE => d )))`;


 val lunion_defn = Defn.Hol_multi_defns `

((lunion:'a list -> 'a list -> 'a list) [] s=  s)
/\
((lunion:'a list -> 'a list -> 'a list) (x::xs) s=
   (if MEM x s
  then lunion xs s
  else x::(lunion xs s)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) lunion_defn;

val _ = type_abbrev((* ( 'a, 'b) *) "alist" , ``: ('a # 'b) list``);

val _ = Define `
 ((opt_bind:'a option -> 'b ->('a#'b)list ->('a#'b)list) n v e=
   ((case n of
      NONE => e
    | SOME n' => (n',v)::e
  )))`;

 val _ = Define `

((lshift:num ->(num)list ->(num)list) (n : num) ls=
   (MAP (\ v .  v - n) (FILTER (\ v .  n <= v) ls)))`;

val _ = export_theory()

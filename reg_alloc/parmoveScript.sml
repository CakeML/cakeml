open HolKernel Parse boolLib bossLib;

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open sptreeTheory lcsymtacs miscTheory;

val _ = new_theory "parmove";


(* This is a formalisation of a JAR'08 paper by Rideau, Serpette, Leroy:
     Tilting at windmills with Coq: formal verification of a compilation
     algorithm for parallel moves
   http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf *)

val windmill_def = Define `
  windmill (moves:('a # 'a) list) = ALL_DISTINCT (MAP SND moves)`;

(* ... *)

(* The top-level parallel move compiler *)

val parmove_def = Define `
  parmove (xs:('a # 'a) list) (temp:'a) = xs (* TODO *)`

val _ = export_theory();

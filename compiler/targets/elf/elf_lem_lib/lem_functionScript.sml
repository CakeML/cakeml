(*Generated by Lem from function.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_boolTheory lem_basic_classesTheory;

val _ = numLib.prefer_num();



val _ = new_theory "lem_function"

(******************************************************************************)
(* A library for common operations on functions                               *)
(******************************************************************************)

(*open import Bool Basic_classes*)

(*open import {coq} `Program.Basics`*)

(* ----------------------- *)
(* identity function       *)
(* ----------------------- *)

(*val id : forall 'a. 'a -> 'a*)
(*let id x=  x*)


(* ----------------------- *)
(* constant function       *)
(* ----------------------- *)

(*val const : forall 'a 'b. 'a -> 'b -> 'a*)


(* ----------------------- *)
(* function composition    *)
(* ----------------------- *)

(*val comb : forall 'a 'b 'c. ('b -> 'c) -> ('a -> 'b) -> ('a -> 'c)*)
(*let comb f g=  (fun x -> f (g x))*)


(* ----------------------- *)
(* function application    *)
(* ----------------------- *)

(*val $ [apply] : forall 'a 'b. ('a -> 'b) -> ('a -> 'b)*)
(*let $ f=  (fun x -> f x)*)

(* ----------------------- *)
(* flipping argument order *)
(* ----------------------- *)

(*val flip : forall 'a 'b 'c. ('a -> 'b -> 'c) -> ('b -> 'a -> 'c)*)
(*let flip f=  (fun x y -> f y x)*)


(* currying / uncurrying *)

(*val curry : forall 'a 'b 'c. (('a * 'b) -> 'c) -> 'a -> 'b -> 'c*)
val _ = Define `
 (curry f=  (\ a b .  f (a, b)))`;


(*val uncurry : forall 'a 'b 'c. ('a -> 'b -> 'c) -> ('a * 'b -> 'c)*)
val _ = Define `
 (uncurry f (a,b)=  (f a b))`;

val _ = export_theory()


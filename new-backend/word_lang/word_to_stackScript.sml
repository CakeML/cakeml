open HolKernel Parse boolLib bossLib;
val _ = new_theory "word_to_stack";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory sptreeTheory lcsymtacs miscTheory asmTheory word_langTheory;
open stackLangTheory;

val _ = ParseExtras.tight_equality ();

val list_union_def = Define `
  (list_union [] l = l) /\
  (list_union (x::xs) l = list_union xs (union x l))`

(* TODO: stack index needs to be adjusted, currently counts from top
         of stack, should count from base of stack frame. *)

val wReg1_def = Define `
  wReg1 r k = if r < k then ([],r,insert r () LN) else ([(k,r-k)],k:num,LN)`

val wReg2_def = Define `
  wReg2 r k = if r < k then ([],r,insert r () LN) else ([(k+1,r-k)],k+1:num,LN)`

val wRegImm2_def = Define `
  (wRegImm2 (Reg r) k = let (x,n,l) = wReg2 r k in (x,Reg n,l)) /\
  (wRegImm2 (Imm i) k = ([],Imm i,LN))`

val wAttach_def = Define `
  (wAttach [] x = x) /\
  (wAttach ((r,i)::ps) x = Seq (StackLoad r i) (wAttach ps x))`

val wMove_def = Define `
  wMove xs l k = (Skip:'a stack_prog,l)`; (* TODO *)

val wInst_def = Define `
  wInst i l k = (Skip:'a stack_prog,l)`; (* TODO *)

val wImpossible_def = Define `
  wImpossible = Skip`

val wComp_def = Define `
  (wComp (Skip:'a word_prog) l k = (Skip:'a stack_prog,l)) /\
  (wComp (Move _ xs) l k = wMove xs l k) /\
  (wComp (Inst i) l k = wInst i l k) /\
  (wComp (Return v1 v2) l k = (Return v1 v2,insert v1 () (insert v2 () LN))) /\
  (wComp (Raise v) l k = (Raise v,insert v () LN)) /\
  (wComp (Tick) l k = (Tick,l)) /\
  (wComp (Seq p1 p2) l k =
     let (q2,l2) = wComp p2 l k in
     let (q1,l1) = wComp p1 l2 k in
       (Seq q1 q2,l1)) /\
  (wComp (If cmp r ri p1 p2) l k =
     let (q1,l1) = wComp p1 l k in
     let (q2,l2) = wComp p2 l k in
     let (x1,r',l3) = wReg1 r k in
     let (x2,ri',l4) = wRegImm2 ri k in
       (wAttach (x1++x2) (If cmp r' ri' q1 q2),
        list_union [l1;l2;l3] l4)) /\
  (wComp (Set name exp) l k =
     case exp of
     | Var n => let (x1,r',l) = wReg1 n k in
                  (wAttach x1 (Set name r'),l)
     | _ => (wImpossible,l)) /\
  (wComp (Get n name) l k = (Skip,l)) /\ (* TODO *)
  (wComp (Call x1 x2 x3 x4) l k = (Skip,l)) /\ (* TODO *)
  (wComp (Alloc size live) l k = (Skip,l)) /\ (* TODO *)
  (wComp _ l k = (wImpossible,l))`

val _ = export_theory();

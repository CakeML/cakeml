open HolKernel Parse boolLib bossLib;
val _ = new_theory "word_to_stack";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory sptreeTheory lcsymtacs miscTheory asmTheory wordLangTheory;
open stackLangTheory;

val _ = ParseExtras.tight_equality ();

val list_union_def = Define `
  (list_union [] l = l) /\
  (list_union (x::xs) l = list_union xs (union x l))`

(* Here k = number of regsiters
    and f = size of stack frame
    and kf = (k,f) *)

val wReg1_def = Define `
  wReg1 r (k,f) = if r < k then ([],r,insert r () LN)
                           else ([(k,f+k-r)],k:num,LN)`

val wReg2_def = Define `
  wReg2 r (k,f) = if r < k then ([],r,insert r () LN)
                           else ([(k+1,f+k-r)],k+1:num,LN)`

val wRegWrite1_def = Define `
  wRegWrite1 r (k,f) = if r < k then ([],r)
                       else ([(f+k-r,k)],k:num)`

val wRegImm2_def = Define `
  (wRegImm2 (Reg r) kf = let (x,n,l) = wReg2 r kf in (x,Reg n,l)) /\
  (wRegImm2 (Imm i) kf = ([],Imm i,LN))`

val wRegWrite1_def = Define `
  wRegWrite1 g r (k,f) =
    if r < k then g r
    else Seq (g k) (StackStore k (f+k-r))`

val wStackLoad_def = Define `
  (wStackLoad [] x = x) /\
  (wStackLoad ((r,i)::ps) x = Seq (StackLoad r i) (wStackLoad ps x))`

val wStackStore_def = Define `
  (wStackStore [] x = x) /\
  (wStackStore ((r,i)::ps) x = Seq (wStackStore ps x) (StackStore r i))`

val wMove_def = Define `
  wMove xs l kf = (Skip:'a stackLang$prog,l)`; (* TODO *)

val wInst_def = Define `
  wInst i l kf = (Skip:'a stackLang$prog,l)`; (* TODO *)

val wImpossible_def = Define `
  wImpossible = Skip:'a stackLang$prog`

val bits_to_word_def = Define `
  (bits_to_word [] = 0w) /\
  (bits_to_word (T::xs) = (bits_to_word xs << 1 || 1w)) /\
  (bits_to_word (F::xs) = (bits_to_word xs << 1))`;

val word_list_def = tDefine "word_list" `
  word_list (xs:bool list) d =
    if LENGTH xs < d \/ (d = 0) then [bits_to_word xs]
    else bits_to_word (TAKE d xs ++ [T]) :: word_list (DROP d xs) d`
 (WF_REL_TAC `measure (LENGTH o FST)`
  \\ fs [LENGTH_DROP] \\ DECIDE_TAC)

val write_bitmap_def = Define `
  (write_bitmap live k f):'a word list =
    let names = MAP (\(r,y). f+k-r) (toAList live) in
      word_list (GENLIST (\x. MEM x names) f) (dimindex(:'a) - 1)`

val wLiveAux_def = tDefine "wLiveAux" `
  wLiveAux (xs:'a word list) r index =
    case xs of
    | [] => Skip
    | [x] => Seq (Inst (Const r x)) (StackStore r index)
    | _ => Seq (wLiveAux [HD xs] r index)
               (wLiveAux (TL xs) r (index+1))`
 (WF_REL_TAC `measure (LENGTH o FST)` \\ fs [] \\ decide_tac);

val wLive_def = Define `
  wLive live (k,f) = wLiveAux (write_bitmap live k f) k 0`;

val wComp_def = Define `
  (wComp (Skip:'a wordLang$prog) l kf = (Skip:'a stackLang$prog,l)) /\
  (wComp (Move _ xs) l kf = wMove xs l kf) /\
  (wComp (Inst i) l kf = wInst i l kf) /\
  (wComp (Return v1 v2) l kf = (Return v1 v2,insert v1 () (insert v2 () LN))) /\
  (wComp (Raise v) l kf = (Raise v,insert v () LN)) /\ (* TODO *)
  (wComp (Tick) l kf = (Tick,l)) /\
  (wComp (Seq p1 p2) l kf =
     let (q2,l2) = wComp p2 l kf in
     let (q1,l1) = wComp p1 l2 kf in
       (Seq q1 q2,l1)) /\
  (wComp (If cmp r ri p1 p2) l kf =
     let (q1,l1) = wComp p1 l kf in
     let (q2,l2) = wComp p2 l kf in
     let (x1,r',l3) = wReg1 r kf in
     let (x2,ri',l4) = wRegImm2 ri kf in
       (wStackLoad (x1++x2) (If cmp r' ri' q1 q2),
        list_union [l1;l2;l3] l4)) /\
  (wComp (Set name exp) l kf =
     case exp of
     | Var n => let (x1,r',l) = wReg1 n kf in
                  (wStackLoad x1 (Set name r'),l)
     | _ => (wImpossible,l)) /\
  (wComp (Get n name) l kf =
     (wRegWrite1 (\r. Get r name) n kf, delete n l)) /\
  (wComp (Call x1 x2 x3 x4) l kf = (Skip,l)) /\ (* TODO *)
  (wComp (Alloc size live) l kf =
     (Seq (wLive live kf) (Alloc size),live)) /\
  (wComp _ l kf = (wImpossible,l))`

val _ = export_theory();

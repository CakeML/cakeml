open HolKernel Parse boolLib bossLib;
val _ = new_theory "word_to_stack";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory sptreeTheory lcsymtacs miscTheory asmTheory wordLangTheory;
open stackLangTheory;

val _ = ParseExtras.tight_equality ();

(* TODO: move *)

val list_union_def = Define `
  (list_union [] l = l) /\
  (list_union (x::xs) l = list_union xs (union x l))`

val MAX_LIST_def = Define `
  (MAX_LIST [] = 0) /\
  (MAX_LIST (n::ns) = MAX n (MAX_LIST ns))`

(* -- *)

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

val comp_def = Define `
  (comp (Skip:'a wordLang$prog) l kf = (Skip:'a stackLang$prog,l)) /\
  (comp (Move _ xs) l kf = wMove xs l kf) /\
  (comp (Inst i) l kf = wInst i l kf) /\
  (comp (Return v1 v2) l kf = (Return v1 v2,insert v1 () (insert v2 () LN))) /\
  (comp (Raise v) l kf = (Raise v,insert v () LN)) /\ (* TODO *)
  (comp (Tick) l kf = (Tick,l)) /\
  (comp (Seq p1 p2) l kf =
     let (q2,l2) = comp p2 l kf in
     let (q1,l1) = comp p1 l2 kf in
       (Seq q1 q2,l1)) /\
  (comp (If cmp r ri p1 p2) l kf =
     let (q1,l1) = comp p1 l kf in
     let (q2,l2) = comp p2 l kf in
     let (x1,r',l3) = wReg1 r kf in
     let (x2,ri',l4) = wRegImm2 ri kf in
       (wStackLoad (x1++x2) (If cmp r' ri' q1 q2),
        list_union [l1;l2;l3] l4)) /\
  (comp (Set name exp) l kf =
     case exp of
     | Var n => let (x1,r',l) = wReg1 n kf in
                  (wStackLoad x1 (Set name r'),l)
     | _ => (wImpossible,l)) /\
  (comp (Get n name) l kf =
     (wRegWrite1 (\r. Get r name) n kf, delete n l)) /\
  (comp (Call x1 x2 x3 x4) l kf = (Skip,l)) /\ (* TODO *)
  (comp (Alloc size live) l kf =
     (Seq (wLive live kf) (Alloc size),live)) /\
  (comp _ l kf = (wImpossible,l))`

val inst_vars_def = Define `
  (inst_vars Skip = []) /\
  (inst_vars (Const n _) = [n]) /\
  (inst_vars (Arith (Binop _ n1 n2 (Imm _))) = [n1;n2]) /\
  (inst_vars (Arith (Binop _ n1 n2 (Reg n3))) = [n1;n2;n3]) /\
  (inst_vars (Arith (Shift _ n1 n2 _)) = [n1;n2]) /\
  (inst_vars (Mem _ n1 (Addr n2 _)) = [n1;n2])`

val max_var_def = Define `
  (max_var (Skip:'a wordLang$prog) = 0) /\
  (max_var (Move _ xs) = MAX_LIST (MAP (\(x,y). MAX x y) xs)) /\
  (max_var (Inst i) = MAX_LIST (inst_vars i)) /\
  (max_var (Return v1 v2) = MAX v1 v2) /\
  (max_var (Raise v) = v) /\
  (max_var (Seq p1 p2) = MAX (max_var p1) (max_var p2)) /\
  (max_var (If cmp r ri p1 p2) =
     MAX (case ri of Reg n => n | _ => 0)
       (MAX r (MAX (max_var p1) (max_var p2)))) /\
  (max_var (Set name exp) = case exp of Var n => n | _ => 0) /\
  (max_var (Get n name) = n) /\
  (max_var (Call ret x2 args handler) =
     MAX (MAX_LIST args)
         (MAX (case ret of SOME (x,_) => x | _ => 0)
              (case handler of SOME (x,_) => x | _ => 0))) /\
  (max_var _ = 0)`

val compile_def = Define `
  compile (prog:'a wordLang$prog) arg_count reg_count =
    let stack_arg_count = arg_count - reg_count in
    let stack_var_count = MAX (max_var prog DIV 2 - reg_count) stack_arg_count in
      if stack_var_count = 0 then
        FST (comp prog LN (reg_count,0))
      else
        let bitmap_size = stack_var_count DIV (dimindex (:'a) - 1) + 1 in
        let f = stack_var_count + bitmap_size in
          Seq (StackAlloc (f - stack_arg_count))
              (FST (comp prog LN (reg_count,f)))`

val _ = export_theory();

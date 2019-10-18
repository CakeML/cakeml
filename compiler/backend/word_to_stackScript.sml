(*
  This compiler phase maps wordLang programs into stackLang
  programs. The most complicated part is the handling of spilled
  variables in conjunction with function calls. This compiler phase
  also introduces the so called bitmaps that the garbage collector
  uses to known which variables it should treat as roots in a given
  stack frame.
*)
open preamble asmTheory wordLangTheory stackLangTheory parmoveTheory
     word_allocTheory

val _ = new_theory "word_to_stack";

val _ = Datatype `config = <| bitmaps : 'a word list |>`;

(* -- *)

(* Here k = number of regsiters
    and f = size of stack frame
    and f' = number of slots in stack frame (= f - bitmap_size)
    and kf = (k,f,f') *)

val wReg1_def = Define `
  wReg1 r (k,f,f':num) =
    let r = r DIV 2 in
      if r < k then ([],r) else ([(k,f-1 - (r - k))],k:num)`

val wReg2_def = Define `
  wReg2 r (k,f,f':num) =
    let r = r DIV 2 in
      if r < k then ([],r) else ([(k+1,f-1 - (r - k))],k+1:num)`

val wRegImm2_def = Define `
  (wRegImm2 (Reg r) kf = let (x,n) = wReg2 r kf in (x,Reg n)) /\
  (wRegImm2 (Imm i) kf = ([],Imm i))`

val wRegWrite1_def = Define `
  wRegWrite1 g r (k,f,f':num) =
    let r = r DIV 2 in
      if r < k then g r else Seq (g k) (StackStore k (f-1 - (r - k)))`

val wRegWrite2_def = Define `
  wRegWrite2 g r (k,f,f':num) =
    let r = r DIV 2 in
      if r < k then g r else Seq (g (k+1)) (StackStore (k+1) (f-1 - (r - k)))`

val wStackLoad_def = Define `
  (wStackLoad [] x = x) /\
  (wStackLoad ((r,i)::ps) x = Seq (StackLoad r i) (wStackLoad ps x))`

val wStackStore_def = Define `
  (wStackStore [] x = x) /\
  (wStackStore ((r,i)::ps) x = Seq (wStackStore ps x) (StackStore r i))`

val wMoveSingle_def = Define `
  wMoveSingle (x,y) (k,f,f':num) =
    case (x,y) of
    | (INL r1, INL r2) => Inst (Arith (Binop Or r1 r2 (Reg r2)))
    | (INL r1, INR r2) => StackLoad r1 (f-1 - (r2 - k))
    | (INR r1, INL r2) => StackStore r2 (f-1 - (r1 - k))
    | (INR r1, INR r2) => Seq (StackLoad k (f-1 - (r2 - k)))
                              (StackStore k (f-1 - (r1 - k)))`

val wMoveAux_def = Define `
  (wMoveAux [] kf = Skip) /\
  (wMoveAux [xy] kf = wMoveSingle xy kf) /\
  (wMoveAux (xy::xys) kf = Seq (wMoveSingle xy kf) (wMoveAux xys kf))`

val format_var_def = Define `
  (format_var k NONE = INL (k+1)) /\
  (format_var k (SOME x) = if x < k:num then INL x else INR x)`;

val wMove_def = Define `
  wMove xs (k,f:num,f':num) =
    wMoveAux (MAP (format_var k ## format_var k) (parmove (MAP (DIV2 ## DIV2) xs))) (k,f,f')`;

val wInst_def = Define `
  (wInst ((Const n c):'a inst) kf =
    wRegWrite1 (\n. Inst (Const n c)) n kf) /\
  (wInst (Arith (Binop bop n1 n2 (Imm imm))) kf =
    let (l,n2) = wReg1 n2 kf in
    wStackLoad l
      (wRegWrite1 (\n1. Inst (Arith (Binop bop n1 n2 (Imm imm)))) n1 kf)) /\
  (wInst (Arith (Binop bop n1 n2 (Reg n3))) kf =
    let (l,n2) = wReg1 n2 kf in
    let (l',n3) = wReg2 n3 kf in
    wStackLoad (l++l')
      (wRegWrite1 (\n1. Inst (Arith (Binop bop n1 n2 (Reg n3)))) n1 kf)) /\
  (wInst (Arith (Shift sh n1 n2 a)) kf =
    let (l,n2) = wReg1 n2 kf in
    wStackLoad l
      (wRegWrite1 (\n1. Inst (Arith (Shift sh n1 n2 a))) n1 kf)) /\
  (wInst (Arith (Div n1 n2 n3)) kf =
    let (l,n2) = wReg1 n2 kf in
    let (l',n3) = wReg2 n3 kf in
    wStackLoad (l++l')
      (wRegWrite1 (\n1. Inst (Arith (Div n1 n2 n3))) n1 kf)) ∧
  (wInst (Arith (AddCarry n1 n2 n3 n4)) kf =
    let (l,n2) = wReg1 n2 kf in
    let (l',n3) = wReg2 n3 kf in
    wStackLoad (l++l')
      (wRegWrite1 (\n1. Inst (Arith (AddCarry n1 n2 n3 n4))) n1 kf)) /\
  (wInst (Arith (AddOverflow n1 n2 n3 n4)) kf =
    let (l,n2) = wReg1 n2 kf in
    let (l',n3) = wReg2 n3 kf in
    wStackLoad (l++l')
      (wRegWrite1 (\n1. Inst (Arith (AddOverflow n1 n2 n3 n4))) n1 kf)) /\
  (wInst (Arith (SubOverflow n1 n2 n3 n4)) kf =
    let (l,n2) = wReg1 n2 kf in
    let (l',n3) = wReg2 n3 kf in
    wStackLoad (l++l')
      (wRegWrite1 (\n1. Inst (Arith (SubOverflow n1 n2 n3 n4))) n1 kf)) /\
  (wInst (Arith (LongMul n1 n2 n3 n4)) kf =
    (*n1 = 2, n2 = 0, n3 = 0, n4 = 1 no spills necessary*)
      (Inst (Arith (LongMul 3 0 0 2)))) /\
  (wInst (Arith (LongDiv n1 n2 n3 n4 n5)) kf =
    (*n1 = 0, n2 = 2, n3 = 2, n4 = 0 no spills necessary*)
    let (l,n5) = wReg1 n5 kf in
    wStackLoad l
      (Inst (Arith (LongDiv 0 3 3 0 n5)))) /\
  (wInst (Mem Load n1 (Addr n2 offset)) kf =
    let (l,n2) = wReg1 n2 kf in
    wStackLoad l
      (wRegWrite1 (\n1. Inst (Mem Load n1 (Addr n2 offset))) n1 kf)) /\
  (wInst (Mem Store n1 (Addr n2 offset)) kf =
    let (l1,n2) = wReg1 n2 kf in
    let (l2,n1) = wReg2 n1 kf in
      wStackLoad (l1 ++ l2)
        (Inst (Mem Store n1 (Addr n2 offset)))) /\
  (wInst (Mem Load8 n1 (Addr n2 offset)) kf =
    let (l,n2) = wReg1 n2 kf in
    wStackLoad l
      (wRegWrite1 (\n1. Inst (Mem Load8 n1 (Addr n2 offset))) n1 kf)) /\
  (wInst (Mem Store8 n1 (Addr n2 offset)) kf =
    let (l1,n2) = wReg1 n2 kf in
    let (l2,n1) = wReg2 n1 kf in
      wStackLoad (l1 ++ l2)
        (Inst (Mem Store8 n1 (Addr n2 offset)))) /\
  (wInst (FP (FPLess r f1 f2)) kf =
    wRegWrite1 (\r. Inst (FP (FPLess r f1 f2))) r kf) /\
  (wInst (FP (FPLessEqual r f1 f2)) kf =
    wRegWrite1 (\r. Inst (FP (FPLessEqual r f1 f2))) r kf) /\
  (wInst (FP (FPEqual r f1 f2)) kf =
    wRegWrite1 (\r. Inst (FP (FPEqual r f1 f2))) r kf) /\
  (wInst (FP (FPMovToReg r1 r2 d)) kf =
    if dimindex(:'a) = 64 then
      wRegWrite1 (λr1. Inst (FP (FPMovToReg r1 0 d))) r1 kf
    else
      wRegWrite2 (λr2. wRegWrite1 (λr1. Inst(FP (FPMovToReg r1 r2 d))) r1 kf) r2 kf) /\
  (wInst (FP (FPMovFromReg d r1 r2)) kf =
    let (l,n1) = wReg1 r1 kf in
    let (l',n2) =
      if dimindex(:'a) = 64 then ([],0)
      else wReg2 r2 kf in
    wStackLoad (l++l')
      (Inst (FP (FPMovFromReg d n1 n2)))) /\
  (wInst (FP f) kf = Inst (FP f)) /\ (*pass through the ones that don't use int registers *)
  (wInst _ kf = Inst Skip)`

val bits_to_word_def = Define `
  (bits_to_word [] = 0w) /\
  (bits_to_word (T::xs) = (bits_to_word xs << 1 || 1w)) /\
  (bits_to_word (F::xs) = (bits_to_word xs << 1))`;

val word_list_def = tDefine "word_list" `
  word_list (xs:bool list) d =
    if LENGTH xs <= d \/ (d = 0) then [bits_to_word xs]
    else bits_to_word (TAKE d xs ++ [T]) :: word_list (DROP d xs) d`
 (WF_REL_TAC `measure (LENGTH o FST)`
  \\ fs [LENGTH_DROP] \\ DECIDE_TAC)

val write_bitmap_def = Define `
  (write_bitmap live k f'):'a word list =
    let names = MAP (\(r,y). (f' -1) - (r DIV 2 - k)) (toAList live) in
      word_list (GENLIST (\x. MEM x names) f' ++ [T]) (dimindex(:'a) - 1)`

val insert_bitmap_def = Define `
  (insert_bitmap ws [] = (ws,0n)) /\
  (insert_bitmap ws (x::xs) =
     if isPREFIX ws (x::xs) then (x::xs,0)
     else let (ys,n) = insert_bitmap ws xs in (x::ys,n+1))`

val wLive_def = Define `
  wLive (live:num_set) (bitmaps:'a word list) (k,f:num,f':num) =
    if f = 0 then (Skip,bitmaps)
    else
      let (new_bitmaps,i) = insert_bitmap (write_bitmap live k f') bitmaps in
        (Seq (Inst (Const k (n2w (i+1)))) (StackStore k 0):'a stackLang$prog,new_bitmaps)`

val SeqStackFree_def = Define `
  SeqStackFree n p = if n = 0 then p else Seq (StackFree n) p`

val call_dest_def = Define `
  (call_dest (SOME pos) args kf = (Skip, INL pos)) /\
  (call_dest NONE args kf =
     if LENGTH args = 0
       then (Skip, INL raise_stub_location) (* this case can never occur, raise_stub_location is convenient *)
       else
       let (x1,r) = wReg2 (LAST args) kf in
         (wStackLoad x1 Skip, INR r))`

val stack_arg_count_def = Define `
  stack_arg_count dest arg_count k =
    case dest of
    | INL _ => (arg_count - k:num)
    | INR _ => ((arg_count - 1) - k:num)`

val stack_free_def = Define `
  stack_free dest arg_count (k,f,f':num) =
    f - stack_arg_count dest arg_count k`

val stack_move_def = Define `
  (stack_move 0 start offset i p = p) /\
  (stack_move (SUC n) start offset i p =
     Seq (stack_move n (start+1) offset i p)
         (Seq (StackLoad i (start+offset)) (StackStore i start)))`

val StackArgs_def = Define `
  StackArgs dest arg_count (k,f,f':num) =
    let n = stack_arg_count dest arg_count k in
      stack_move n 0 f k (StackAlloc n)`

val StackHandlerArgs_def = Define `
  StackHandlerArgs dest arg_count (k,f,f':num) =
    StackArgs dest arg_count (k,f+3,f'+3)`;

val PushHandler_def = Define `
  PushHandler l1 l2 (k,f,f') =
    Seq (StackAlloc 3)
   (Seq (Inst (Const k 1w))
   (Seq (StackStore k 0)
   (Seq (LocValue k l1 l2)
   (Seq (StackStore k 1)
   (Seq (Get k Handler)
   (Seq (StackStore k 2)
   (Seq (StackGetSize k)
        (Set Handler k))))))))`

val PopHandler_def = Define`
  PopHandler (k,f,f') prog =
   Seq (StackLoad k 2)
  (Seq (Set Handler k)
  (Seq (StackFree 3)
  prog))`

val comp_def = Define `
  (comp (Skip:'a wordLang$prog) bs kf = (Skip:'a stackLang$prog,bs)) /\
  (comp (Move _ xs) bs kf = (wMove xs kf,bs)) /\
  (comp (Inst i) bs kf = (wInst i kf,bs)) /\
  (comp (Return v1 v2) bs kf =
     let (xs,x) = wReg1 v1 kf in
       (wStackLoad xs (SeqStackFree (FST (SND kf)) (Return x 1)),bs)) /\
  (comp (Raise v) bs kf = (Call NONE (INL raise_stub_location) NONE,bs)) /\
  (comp (Tick) bs kf = (Tick,bs)) /\
  (comp (MustTerminate p1) gs kf = comp p1 gs kf) /\
  (comp (Seq p1 p2) bs kf =
     let (q1,bs) = comp p1 bs kf in
     let (q2,bs) = comp p2 bs kf in
       (Seq q1 q2,bs)) /\
  (comp (If cmp r ri p1 p2) bs kf =
     let (x1,r') = wReg1 r kf in
     let (x2,ri') = wRegImm2 ri kf in
     let (q1,bs) = comp p1 bs kf in
     let (q2,bs) = comp p2 bs kf in
       (wStackLoad (x1++x2) (If cmp r' ri' q1 q2),bs)) /\
  (comp (Set name exp) bs kf =
    if name = BitmapBase then (Skip,bs) (*Impossible*)
    else
     case exp of
     | Var n => let (x1,r') = wReg1 n kf in (wStackLoad x1 (Set name r'),bs)
     | _ => (Skip,bs) (* impossible *)) /\
  (comp (Get n name) bs kf =
     (wRegWrite1 (\r. Get r name) n kf,bs)) /\
  (comp (Call ret dest args handler) bs kf =
     let (q0,dest) = call_dest dest args kf in
     case ret of
     | NONE => (Seq q0 (SeqStackFree (stack_free dest (LENGTH args) kf)
                 (Call NONE dest NONE)),bs)
     | SOME (ret_var, live, ret_code, l1, l2) =>
         let (q1,bs) = wLive live bs kf in
         let (q2,bs) = comp ret_code bs kf in
           case handler of
           | NONE => (Seq q0
                     (Seq q1
                     (Seq (StackArgs dest (LENGTH args + 1) kf)
                          (Call (SOME (q2,0,l1,l2)) dest NONE))),
                      bs)
           | SOME (handle_var, handle_code, h1, h2) =>
               let (q3,bs) = comp handle_code bs kf in
                (Seq q0
                (Seq q1
                (Seq (PushHandler h1 h2 kf)
                (Seq (StackHandlerArgs dest (LENGTH args + 1) kf)
                     (Call (SOME (PopHandler kf q2,0,l1,l2)) dest (SOME (q3,h1,h2)))))),
                 bs)) /\
  (comp (Alloc r live) bs kf =
     let (q1,bs) = wLive live bs kf in
       (Seq q1 (Alloc 1),bs)) /\
  (comp (LocValue r l1) bs kf = (wRegWrite1 (λr. LocValue r l1 0) r kf,bs)) /\
  (comp (Install r1 r2 r3 r4 live) bs kf =
    let (l3,r3) = wReg1 r3 kf in
    let (l4,r4) = wReg2 r4 kf in
      (wStackLoad (l3++l4) (Install (r1 DIV 2) (r2 DIV 2) r3 r4 0),bs)) /\
  (comp (CodeBufferWrite r1 r2) bs kf =
    let (l1,r1) = wReg1 r1 kf in
    let (l2,r2) = wReg2 r2 kf in
      (wStackLoad (l1++l2) (CodeBufferWrite r1 r2),bs)) /\
  (comp (DataBufferWrite r1 r2) bs kf =
    let (l1,r1) = wReg1 r1 kf in
    let (l2,r2) = wReg2 r2 kf in
      (wStackLoad (l1++l2) (DataBufferWrite r1 r2),bs)) /\
  (comp (FFI i r1 r2 r3 r4 live) bs kf = (FFI i (r1 DIV 2) (r2 DIV 2)
                                                (r3 DIV 2) (r4 DIV 2) 0,bs)) /\
  (comp _ bs kf = (Skip,bs) (* impossible *))`

val raise_stub_def = Define `
  raise_stub k =
     Seq (Get k Handler)
    (Seq (StackSetSize k)
    (Seq (StackLoad k 2) (* next handler *)
    (Seq (Set Handler k)
    (Seq (StackLoad k 1) (* handler pc *)
    (Seq (StackFree 3)
         (Raise k))))))`;

(*stack args are in wordLang vars 0,2,4,...,2*(k-1), 2*k , ...*)
(*2*k and above are "stack" variables*)
(*We always allocate enough space for the maximum stack var*)
val compile_prog_def = Define `
  compile_prog (prog:'a wordLang$prog) arg_count reg_count bitmaps =
    let stack_arg_count = arg_count - reg_count in
    let stack_var_count = MAX ((max_var prog DIV 2 + 1)- reg_count) stack_arg_count in
    let f = if stack_var_count = 0 then 0 else stack_var_count + 1 in
    let (q1,bitmaps) = comp prog bitmaps (reg_count,f,stack_var_count) in
      (Seq (StackAlloc (f - stack_arg_count)) q1, f, bitmaps)`

val compile_word_to_stack_def = Define `
  (compile_word_to_stack k [] bitmaps = ([],[],bitmaps)) /\
  (compile_word_to_stack k ((i,n,p)::progs) bitmaps =
     let (prog,f,bitmaps) = compile_prog p n k bitmaps in
     let (progs,fs,bitmaps) = compile_word_to_stack k progs bitmaps in
       ((i,prog)::progs,f::fs,bitmaps))`

val compile_def = Define `
  compile asm_conf progs =
    let k = asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs) in
    let (progs,fs,bitmaps) = compile_word_to_stack k progs [4w] in
      (<| bitmaps := bitmaps |>, 0::fs, (raise_stub_location,raise_stub k) :: progs)`

val _ = export_theory();

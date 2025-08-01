(*
  This compiler phase maps wordLang programs into stackLang
  programs. The most complicated part is the handling of spilled
  variables in conjunction with function calls. This compiler phase
  also introduces the so called bitmaps that the garbage collector
  uses to known which variables it should treat as roots in a given
  stack frame.
*)
open preamble asmTheory wordLangTheory stackLangTheory parmoveTheory
     word_allocTheory mlstringTheory

val _ = new_theory "word_to_stack";

(* bitmaps_length stores the current length of the bitmaps *)
Datatype:
  config = <| bitmaps_length: num ;
                              stack_frame_size : num spt |>
End

(* -- *)

(* Here k = number of registers
    and f = size of stack frame
    and f' = number of slots in stack frame (= f - bitmap_size)
    and kf = (k,f,f') *)

Definition wReg1_def:
  wReg1 r (k,f,f':num) =
    let r = r DIV 2 in
      if r < k then ([],r) else ([(k,f-1 - (r - k))],k:num)
End

Definition wReg2_def:
  wReg2 r (k,f,f':num) =
    let r = r DIV 2 in
      if r < k then ([],r) else ([(k+1,f-1 - (r - k))],k+1:num)
End

Definition wRegWrite1_def:
  wRegWrite1 g r (k,f,f':num) =
    let r = r DIV 2 in
      if r < k then g r else Seq (g k) (StackStore k (f-1 - (r - k)))
End

Definition wRegWrite2_def:
  wRegWrite2 g r (k,f,f':num) =
    let r = r DIV 2 in
      if r < k then g r else Seq (g (k+1)) (StackStore (k+1) (f-1 - (r - k)))
End

Definition wStackLoad_def:
  (wStackLoad [] x = x) /\
  (wStackLoad ((r,i)::ps) x = Seq (StackLoad r i) (wStackLoad ps x))
End

Definition wStackStore_def:
  (wStackStore [] x = x) /\
  (wStackStore ((r,i)::ps) x = Seq (wStackStore ps x) (StackStore r i))
End

Definition wMoveSingle_def:
  wMoveSingle (x,y) (k,f,f':num) =
    case (x,y) of
    | (INL r1, INL r2) => Inst (Arith (Binop Or r1 r2 (Reg r2)))
    | (INL r1, INR r2) => StackLoad r1 (f-1 - (r2 - k))
    | (INR r1, INL r2) => StackStore r2 (f-1 - (r1 - k))
    | (INR r1, INR r2) => Seq (StackLoad k (f-1 - (r2 - k)))
                              (StackStore k (f-1 - (r1 - k)))
End

Definition wMoveAux_def:
  (wMoveAux [] kf = Skip) /\
  (wMoveAux [xy] kf = wMoveSingle xy kf) /\
  (wMoveAux (xy::xys) kf = Seq (wMoveSingle xy kf) (wMoveAux xys kf))
End

Definition format_var_def:
  (format_var k NONE = INL (k+1)) /\
  (format_var k (SOME x) = if x < k:num then INL x else INR x)
End

Definition wMove_def:
  wMove xs (k,f:num,f':num) =
    wMoveAux (MAP (format_var k ## format_var k) (parmove (MAP (DIV2 ## DIV2) xs))) (k,f,f')
End

Definition wInst_def:
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
  (wInst (Mem Load32 n1 (Addr n2 offset)) kf =
    let (l,n2) = wReg1 n2 kf in
    wStackLoad l
      (wRegWrite1 (\n1. Inst (Mem Load32 n1 (Addr n2 offset))) n1 kf)) /\
  (wInst (Mem Store32 n1 (Addr n2 offset)) kf =
    let (l1,n2) = wReg1 n2 kf in
    let (l2,n1) = wReg2 n1 kf in
      wStackLoad (l1 ++ l2)
        (Inst (Mem Store32 n1 (Addr n2 offset)))) /\
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
  (wInst _ kf = Inst Skip)
End

Definition wShareInst_def:
  (wShareInst Load v (Addr ad offset) kf =
    let (l,n2) = wReg1 ad kf in
    wStackLoad l
      (wRegWrite1 (\r. ShMemOp Load r (Addr n2 offset)) v kf)) /\
  (wShareInst Load8 v (Addr ad offset) kf =
    let (l,n2) = wReg1 ad kf in
    wStackLoad l
      (wRegWrite1 (\r. ShMemOp Load8 r (Addr n2 offset)) v kf)) /\
  (wShareInst Load32 v (Addr ad offset) kf =
    let (l,n2) = wReg1 ad kf in
    wStackLoad l
      (wRegWrite1 (\r. ShMemOp Load32 r (Addr n2 offset)) v kf)) /\
  (wShareInst Store v (Addr ad offset) kf =
    let (l1,n2) = wReg1 ad kf in
    let (l2,n1) = wReg2 v kf in
    wStackLoad (l1 ++ l2)
      (ShMemOp Store n1 (Addr n2 offset))) /\
  (wShareInst Store8 v (Addr ad offset) kf =
    let (l1,n2) = wReg1 ad kf in
    let (l2,n1) = wReg2 v kf in
    wStackLoad (l1 ++ l2)
      (ShMemOp Store8 n1 (Addr n2 offset))) /\
  (wShareInst Store32 v (Addr ad offset) kf =
    let (l1,n2) = wReg1 ad kf in
    let (l2,n1) = wReg2 v kf in
    wStackLoad (l1 ++ l2)
      (ShMemOp Store32 n1 (Addr n2 offset)))
End

Definition bits_to_word_def:
  (bits_to_word [] = 0w) /\
  (bits_to_word (T::xs) = (bits_to_word xs << 1 || 1w)) /\
  (bits_to_word (F::xs) = (bits_to_word xs << 1))
End

Definition word_list_def:
  word_list (xs:bool list) d =
    if LENGTH xs <= d \/ (d = 0) then [bits_to_word xs]
    else bits_to_word (TAKE d xs ++ [T]) :: word_list (DROP d xs) d
Termination
  WF_REL_TAC `measure (LENGTH o FST)`
  \\ fs [LENGTH_DROP] \\ DECIDE_TAC
End

Definition write_bitmap_def:
  (write_bitmap live k f'):'a word list =
    let names = MAP (\(r,y). (f' -1) - (r DIV 2 - k)) (toAList live) in
      word_list (GENLIST (\x. MEM x names) f' ++ [T]) (dimindex(:'a) - 1)
End

Definition insert_bitmap_def:
  insert_bitmap ws (data,data_len) =
    let l = LENGTH ws in
      ((Append data (List ws), data_len + l), data_len)
End

Definition wLive_def:
  wLive (live:cutsets) (bitmaps:'a word app_list # num) (k,f:num,f':num) =
    if f = 0 then (Skip,bitmaps)
    else
      let (new_bitmaps,i) = insert_bitmap (write_bitmap (SND live) k f') bitmaps in
        (Seq (Inst (Const k (n2w (i+1)))) (StackStore k 0):'a stackLang$prog,new_bitmaps)
End

Definition SeqStackFree_def:
  SeqStackFree n p = if n = 0 then p else Seq (StackFree n) p
End

Definition call_dest_def:
  (call_dest (SOME pos) args kf = (Skip, INL pos)) /\
  (call_dest NONE args kf =
     if LENGTH args = 0
       then (Skip, INL raise_stub_location) (* this case can never occur, raise_stub_location is convenient *)
       else
       let (x1,r) = wReg2 (LAST args) kf in
         (wStackLoad x1 Skip, INR r))
End

Definition stack_arg_count_def:
  stack_arg_count dest arg_count k =
    case dest of
    | INL _ => (arg_count - k:num)
    | INR _ => ((arg_count - 1) - k:num)
End

Definition stack_free_def:
  stack_free dest arg_count (k,f,f':num) =
    f - stack_arg_count dest arg_count k
End

Definition stack_move_def:
  (stack_move 0 start offset i p = p) /\
  (stack_move (SUC n) start offset i p =
     Seq (stack_move n (start+1) offset i p)
         (Seq (StackLoad i (start+offset)) (StackStore i start)))
End

Definition StackArgs_def:
  StackArgs dest arg_count (k,f,f':num) =
    let n = stack_arg_count dest arg_count k in
      stack_move n 0 f k (StackAlloc n)
End

Definition StackHandlerArgs_def:
  StackHandlerArgs dest arg_count (k,f,f':num) =
    StackArgs dest arg_count (k,f+3,f'+3)
End

Definition PushHandler_def:
  PushHandler l1 l2 (k,f,f') =
    Seq (StackAlloc 3)
   (Seq (Inst (Const k 1w))
   (Seq (StackStore k 0)
   (Seq (LocValue k l1 l2)
   (Seq (StackStore k 1)
   (Seq (Get k Handler)
   (Seq (StackStore k 2)
   (Seq (StackGetSize k)
        (Set Handler k))))))))
End

Definition PopHandler_def:
  PopHandler (k,f,f') prog =
   Seq (StackLoad k 2)
  (Seq (Set Handler k)
  (Seq (StackFree 3)
  prog))
End

Definition chunk_to_bits_def:
  chunk_to_bits ([]:(bool # α word) list) = 1w:'a word ∧
  chunk_to_bits ((b,w)::ws) =
    let res = (chunk_to_bits ws) << 1 in
      if b then res + 1w else res
End

Definition chunk_to_bitmap_def:
  chunk_to_bitmap ws = chunk_to_bits ws :: MAP SND ws
End

Definition const_words_to_bitmap_def:
  const_words_to_bitmap (ws:(bool # α word) list) (ws_len:num) =
    if ws_len < (dimindex (:'a) - 1) ∨ (dimindex (:'a) - 1) = 0
    then chunk_to_bitmap ws
    else
      let h = TAKE (dimindex (:'a) - 1) ws in
      let t = DROP (dimindex (:'a) - 1) ws in
        chunk_to_bitmap h ++ const_words_to_bitmap t (ws_len - (dimindex (:'a) - 1))
End

(* Store a large constant in the second temporary *)

(*
0                f-1 0    ...   g-1
| ----------(---)|   |----------|----stack---|
            ^
      values returned on stack
*)

(* Stack slots used in multi-arg return *)
Definition num_stack_ret_def:
  num_stack_ret k vs =
  LENGTH vs + 1 - k
End

(* Number of slots to free by callee *)
Definition skip_free_def:
  skip_free (k,f,f') vs =
    f - num_stack_ret k vs
End

(* Caller copying from the previous stack frame into its own *)
Definition copy_ret_aux_def:
  (copy_ret_aux k f n =
    if n = 0 then Skip
    else
      let n' = n-1 in
      list_Seq
      [
        StackLoad k n';
        StackStore k (n'+f);
        copy_ret_aux k f n'
      ]
  )
End

Definition copy_ret_def:
  copy_ret is_handle (k,f,f') vs kont =
  let n = num_stack_ret k vs in
  if n = 0 then kont
  else Seq
      (copy_ret_aux k (if is_handle then f+3 else f) n)
      (SeqStackFree n kont)
End

(* Return should be 2,4,6,...,2k,2k+1,... *)
Definition comp_def:
  (comp conf (Skip:'a wordLang$prog) bs kf = (Skip:'a stackLang$prog,bs)) /\
  (comp conf (Move _ xs) bs kf = (wMove xs kf,bs)) /\
  (comp conf (Inst i) bs kf = (wInst i kf,bs)) /\
  (comp conf (Return v1 vs) bs kf =
     let (xs,x) = wReg1 v1 kf in
       (wStackLoad xs (SeqStackFree (skip_free kf vs) (Return x)),bs)) /\
  (comp conf (Raise v) bs kf = (Call NONE (INL raise_stub_location) NONE,bs)) /\
  (comp conf (OpCurrHeap b dst src) bs kf =
     let (xs,src_r) = wReg1 src kf in
       (wStackLoad xs (wRegWrite1 (\dst_r. OpCurrHeap b dst_r src_r) dst kf),bs)) /\
  (comp conf (Tick) bs kf = (Tick,bs)) /\
  (comp conf (MustTerminate p1) gs kf = comp conf p1 gs kf) /\
  (comp conf (Seq p1 p2) bs kf =
     let (q1,bs) = comp conf p1 bs kf in
     let (q2,bs) = comp conf p2 bs kf in
       (Seq q1 q2,bs)) /\
  (comp conf (If cmp r ri p1 p2) bs kf =
     let (x1,r') = wReg1 r kf in
     let (q1,bs) = comp conf p1 bs kf in
     let (q2,bs) = comp conf p2 bs kf in
     case ri of
       Reg r =>
         let (x2,n) = wReg2 r kf in
          (wStackLoad (x1++x2) (If cmp r' (Reg n) q1 q2),bs)
     | Imm i =>
        if conf.valid_imm (INR cmp) i then
          (wStackLoad x1 (If cmp r' (Imm i) q1 q2),bs)
        else
          let r = FST kf + 1 in
          (Seq
            (const_inst r i)
            (wStackLoad x1 (If cmp r' (Reg r) q1 q2)),bs)) /\
  (comp conf (Set name exp) bs kf =
    if name = BitmapBase then (Skip,bs) (*Impossible*)
    else
     case exp of
     | Var n => let (x1,r') = wReg1 n kf in (wStackLoad x1 (Set name r'),bs)
     | _ => (Skip,bs) (* impossible *)) /\
  (comp conf (Get n name) bs kf =
     (wRegWrite1 (\r. Get r name) n kf,bs)) /\
  (comp conf (Call ret dest args handler) bs kf =
     let (q0,dest) = call_dest dest args kf in
     case ret of
     | NONE => (Seq q0 (SeqStackFree (stack_free dest (LENGTH args) kf)
                 (Call NONE dest NONE)),bs)
     | SOME (vs, live, ret_code, l1, l2) =>
         let (q1,bs) = wLive live bs kf in
         let (q2,bs) = comp conf ret_code bs kf in
           case handler of
           | NONE =>
             let q3 = copy_ret F kf vs q2 in
               (Seq q0
                 (Seq q1
                   (Seq (StackArgs dest (LENGTH args + 1) kf)
                     (Call (SOME (q3,0,l1,l2)) dest NONE))),
                bs)
           | SOME (handle_var, handle_code, h1, h2) =>
             let q3 = copy_ret T kf vs (PopHandler kf q2) in
             let (q4,bs) = comp conf handle_code bs kf in
               (Seq q0
                  (Seq q1
                    (Seq (PushHandler h1 h2 kf)
                      (Seq (StackHandlerArgs dest (LENGTH args + 1) kf)
                        (Call (SOME (q3,0,l1,l2)) dest (SOME (q4,h1,h2)))))),
                bs)) /\
  (comp conf (Alloc r live) bs kf =
     let (q1,bs) = wLive live bs kf in
       (Seq q1 (Alloc 1),bs)) /\
  (comp conf (StoreConsts a b c d ws) bs kf =
     let (new_bs,i) = insert_bitmap (const_words_to_bitmap ws (LENGTH ws)) bs in
       (Seq (Inst (Const 1 (n2w i)))
            (StoreConsts (FST kf) (FST kf + 1) (SOME store_consts_stub_location)),new_bs)) /\
  (comp conf (LocValue r l1) bs kf = (wRegWrite1 (λr. LocValue r l1 0) r kf,bs)) /\
  (comp conf (Install r1 r2 r3 r4 live) bs kf =
    let (l3,r3) = wReg1 r3 kf in
    let (l4,r4) = wReg2 r4 kf in
      (wStackLoad (l3++l4) (Install (r1 DIV 2) (r2 DIV 2) r3 r4 0),bs)) /\
  (comp conf (CodeBufferWrite r1 r2) bs kf =
    let (l1,r1) = wReg1 r1 kf in
    let (l2,r2) = wReg2 r2 kf in
      (wStackLoad (l1++l2) (CodeBufferWrite r1 r2),bs)) /\
  (comp conf (DataBufferWrite r1 r2) bs kf =
    let (l1,r1) = wReg1 r1 kf in
    let (l2,r2) = wReg2 r2 kf in
      (wStackLoad (l1++l2) (DataBufferWrite r1 r2),bs)) /\
  (comp conf (FFI i r1 r2 r3 r4 live) bs kf = (FFI i (r1 DIV 2) (r2 DIV 2)
                                                (r3 DIV 2) (r4 DIV 2) 0,bs)) /\
  (comp conf (ShareInst op v exp) bs kf =
   (case exp_to_addr exp of
      NONE => (Skip, bs)
    | SOME addr => wShareInst op v addr kf,bs)) /\
  (comp conf _ bs kf = (Skip,bs) (* impossible *))
End

Definition raise_stub_def:
  raise_stub k =
     Seq (Get k Handler)
    (Seq (StackSetSize k)
    (Seq (StackLoad k 2) (* next handler *)
    (Seq (Set Handler k)
    (Seq (StackLoad k 1) (* handler pc *)
    (Seq (StackFree 3)
         (Raise k))))))
End

Definition store_consts_stub_def:
  store_consts_stub k =
    Seq (StoreConsts k (k+1) NONE) (Return 0)
End

(*stack args are in wordLang vars 0,2,4,...,2*(k-1), 2*k , ...*)
(*2*k and above are "stack" variables*)
(*We always allocate enough space for the maximum stack var*)
Definition compile_prog_def:
  compile_prog asm_conf (prog:'a wordLang$prog) arg_count reg_count bitmaps =
    let stack_arg_count = arg_count - reg_count in
    let stack_var_count = MAX ((max_var prog DIV 2 + 1)- reg_count) stack_arg_count in
    let f = if stack_var_count = 0 then 0 else stack_var_count + 1 in
    let (q1,bitmaps) = comp asm_conf prog bitmaps (reg_count,f,stack_var_count) in
      (Seq (StackAlloc (f - stack_arg_count)) q1, f, bitmaps)
End

Definition compile_word_to_stack_def:
  (compile_word_to_stack asm_conf k [] bitmaps = ([],[],bitmaps)) /\
  (compile_word_to_stack asm_conf k ((i,n,p)::progs) bitmaps =
     let (prog,f,bitmaps) = compile_prog asm_conf p n k bitmaps in
     let (progs,fs,bitmaps) = compile_word_to_stack asm_conf k progs bitmaps in
       ((i,prog)::progs,f::fs,bitmaps))
End

Definition compile_def:
  compile asm_conf progs =
    let k = asm_conf.reg_count - (5+LENGTH asm_conf.avoid_regs) in
    let (progs,fs,bitmaps) = compile_word_to_stack asm_conf k progs (List [4w], 1) in
    let sfs = fromAList (MAP (λ((i,_),n). (i,n)) (ZIP (progs,fs))) in
      (append (FST bitmaps),
       <| bitmaps_length := SND bitmaps;
          stack_frame_size := sfs |>, 0::fs,
       (raise_stub_location,raise_stub k) ::
       (store_consts_stub_location,store_consts_stub k) :: progs)
End

Definition stub_names_def:
  stub_names () = [
    (raise_stub_location,        mlstring$strlit "_Raise");
    (store_consts_stub_location, mlstring$strlit "_StoreConsts")]
End

val _ = export_theory();

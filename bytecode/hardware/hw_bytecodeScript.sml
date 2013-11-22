
open HolKernel Parse boolLib bossLib;
open arithmeticTheory wordsTheory wordsLib listTheory;

val _ = new_theory "hw_bytecode";

(* -------------------------------------------------------------------------- *
    Definition of hardware bytecode
 * -------------------------------------------------------------------------- *)

val UPDATE_NTH_def = Define `
  (UPDATE_NTH n x [] = []) /\
  (UPDATE_NTH 0 x (y::ys) = x::ys) /\
  (UPDATE_NTH (SUC n) x (y::ys) = y :: UPDATE_NTH n x ys)`;

val _ = Hol_datatype `
  hw_instruction =
    hwPop                     (* pop top of stack *)
  | hwPop1                    (* pop element below top of stack *)
  | hwPushImm of 6 word       (* push immediate *)
  | hwShiftAddImm of 6 word   (* top := top << 6 + imm *)
  | hwShiftRight              (* top := top >>> 6 (no sign extend) *)
  | hwLowerEqual of 6 word    (* check if lower 6 bits are equal to imm *)
  | hwStackLoad               (* load value from inside stack *)
  | hwStackStore              (* store top of stack into stack *)
  | hwHeapAlloc               (* extend heap *)
  | hwHeapStore               (* store into heap *)
  | hwHeapLoad                (* load from Cons cell *)
  | hwHeapAddress             (* ptr to new location *)
  | hwAdd                     (* 32-bit word + *)
  | hwSub                     (* 32-bit word - *)
  | hwLess                    (* 32-bit word < *)
  | hwEqual                   (* 32-bit word = *)
  | hwSwap                    (* swaps top two stack elements *)
  | hwJump                    (* jump/return to pointer on stack *)
  | hwJumpIfNotZero           (* conditional jump *)
  | hwCall                    (* proc call *)
  | hwRead                    (* read NV memory / UART regs *)
  | hwWrite                   (* write NV memory / UART regs *)
  | hwCompareExchange         (* atomic compare-and-exchange *)
  | hwAbort                   (* stops execution *)
  | hwFail                    (* cause an error *)`

val _ = Hol_datatype `hw_state =
  <| pc         : word32;
     stack      : word32 list;
     heap       : word32 list;
     memory     : word32 list;
     error      : bool |>`; (* sticky error bit *)


val overflow_def = Define `
  overflow b s = (s with error := (s.error \/ b))`

val inc_pc_def = Define `
  inc_pc s = overflow (2**32 <= w2n s.pc + 1) (s with pc := s.pc + 1w)`;

val arg_def = Define `
  arg s = (HD s.stack, s with stack := TL s.stack)`;

val push_def = Define `
  push x s = s with stack := x :: s.stack`;

val stack_load_def = Define `
  stack_load n s = EL (w2n n) s.stack`;

val stack_store_def = Define `
  stack_store n x s = s with stack := UPDATE_NTH (w2n n) x s.stack`;

val heap_load_def = Define `
  heap_load n s = EL (w2n n) s.heap`;

val heap_store_def = Define `
  heap_store n x s = s with heap := UPDATE_NTH (w2n n) x s.heap`;

val heap_alloc_def = Define `
  heap_alloc x s = let s' = s with heap := s.heap ++ [x] in
                     overflow (2**26 <= LENGTH s'.heap) s'`;

val heap_address_def = Define `
  heap_address s = n2w (LENGTH s.heap):word32`;

val memory_load_def = Define `
  memory_load n s = EL (w2n n) s.memory`;

val memory_store_def = Define `
  memory_store n x s = s with memory := UPDATE_NTH (w2n n) x s.memory`;

val hw_step_def = Define `
  hw_step instr s =
    let s = inc_pc s in
      case instr of
          hwPop => SND (arg s)
        | hwPop1 =>
            let (x2,s) = arg s in
            let (x1,s) = arg s in
              push x2 s
        | hwPushImm imm => push (w2w imm) s
        | hwShiftAddImm imm =>
            let (i,s) = arg s in
              push (i << 6 + w2w imm) s
        | hwLowerEqual imm =>
            let (i,s) = arg s in
              push (if w2w i = imm then 1w else 0w) s
        | hwShiftRight =>
            let (i,s) = arg s in
              push (i >>> 6) s
        | hwStackLoad =>
            let (n,s) = arg s in
              push n (push (stack_load n s) s)
        | hwStackStore =>
            let (n,s) = arg s in
            let (x,s) = arg s in
              push n (stack_store n x s)
        | hwHeapAlloc =>
            let (x,s) = arg s in
              heap_alloc x s
        | hwHeapStore =>
            let (n,s) = arg s in
            let (x,s) = arg s in
              push n (heap_store n x s)
        | hwHeapLoad =>
            let (n,s) = arg s in
              push (heap_load n s) s
        | hwHeapAddress =>
            push (heap_address s) s
        | hwAdd =>
            let (x2,s) = arg s in
            let (x1,s) = arg s in
              push (x1 + x2) (overflow (2**32 <= w2n x1 + w2n x2) s)
        | hwSub =>
            let (x2,s) = arg s in
            let (x1,s) = arg s in
              push (x1 - x2) (overflow (w2n x1 < w2n x2) s)
        | hwLess =>
            let (x2,s) = arg s in
            let (x1,s) = arg s in
              push (if x1 <+ x2 then 1w else 0w) s
        | hwEqual =>
            let (x2,s) = arg s in
            let (x1,s) = arg s in
              push (if x1 = x2 then 1w else 0w) s
        | hwSwap =>
            let (x2,s) = arg s in
            let (x1,s) = arg s in
              push x1 (push x2 s)
        | hwJump =>
            let (a,s) = arg s in
              s with pc := a
        | hwJumpIfNotZero =>
            let (a,s) = arg s in
            let (x,s) = arg s in
              if x = 0w then s else s with pc := a
        | hwCall =>
            let (a,s) = arg s in
            let (x,s) = arg s in
              push x (push (s.pc) (s with pc := a))
        | hwRead =>
            let (a,s) = arg s in
              push (memory_load a s) s
        | hwWrite =>
            let (x,s) = arg s in
            let (a,s) = arg s in
              memory_store a x s
        | hwCompareExchange =>
            let (z,s) = arg s in
            let (x,s) = arg s in
            let (a,s) = arg s in
            let y = memory_load a s in
            let s = push y s in
              if x = y then memory_store a z s else s
        | hwAbort => overflow T s
        | hwFail => overflow T s`;

val hw_step_rel_def = Define `
  hw_step_rel code s t =
    w2n s.pc < LENGTH code /\ (t = hw_step (EL (w2n s.pc) code) s)`;

val hw_decode_def = Define `
  hw_decode b =
    if b ' 6 /\ ~(b ' 7) then hwPushImm (w2w b) else
    if b ' 6 /\ b ' 7 then hwShiftAddImm (w2w b) else
    if ~(b ' 6) /\ b ' 7 then hwLowerEqual (w2w b) else
    (* --- *)
    if b = 0w then hwAbort else
    if b = 1w then hwPop else
    if b = 2w then hwStackLoad else
    if b = 3w then hwStackStore else
    if b = 4w then hwPop1 else
    (* --- *)
    if b = 8w then hwEqual else
    if b = 9w then hwLess else
    if b = 10w then hwAdd else
    if b = 11w then hwSub else
    if b = 12w then hwSwap else
    if b = 13w then hwShiftRight else
    (* --- *)
    if b = 16w then hwJump else
    if b = 17w then hwJumpIfNotZero else
    if b = 18w then hwCall else
    (* --- *)
    if b = 32w then hwHeapLoad else
    if b = 33w then hwHeapStore else
    if b = 38w then hwHeapAlloc else
    if b = 34w then hwHeapAddress else
    if b = 35w then hwRead else
    if b = 36w then hwWrite else
    if b = 37w then hwCompareExchange else
    if b = 39w then hwFail else hwAbort`

val hw_encode_def = Define `
  hw_encode instr =
    case instr of
      hwPushImm imm =>     1w * 64w || w2w imm
    | hwShiftAddImm imm => 3w * 64w || w2w imm
    | hwLowerEqual imm =>  2w * 64w || w2w imm
    (* --- *)
    | hwPop => (1w:word8)
    | hwPop1 => 4w
    | hwStackLoad => 2w
    | hwStackStore => 3w
    (* --- *)
    | hwEqual => 8w
    | hwLess => 9w
    | hwAdd => 10w
    | hwSub => 11w
    | hwSwap => 12w
    | hwShiftRight => 13w
    (* --- *)
    | hwJump => 16w
    | hwJumpIfNotZero => 17w
    | hwCall => 18w
    (* --- *)
    | hwHeapLoad => 32w
    | hwHeapStore => 33w
    | hwHeapAlloc => 38w
    | hwHeapAddress => 34w
    | hwRead => 35w
    | hwWrite => 36w
    | hwCompareExchange => 37w
    | hwFail => 39w
    | hwAbort => 40w`;

val hw_decode_encode = store_thm("hw_decode_encode",
  ``!x. hw_decode (hw_encode x) = x``,
  Cases THEN EVAL_TAC
  THEN `((64w:word8) || w2w (c:6 word)) ' 6 /\ ~(64w:word8 || w2w (c:6 word)) ' 7 /\
        ((192w:word8) || w2w (c:6 word)) ' 6 /\ (192w:word8 || w2w (c:6 word)) ' 7 /\
        ~((128w:word8) || w2w (c:6 word)) ' 6 /\ (128w:word8 || w2w (c:6 word)) ' 7 /\
        (w2w ((64w:word8) || w2w c) = c:6 word) /\
        (w2w ((128w:word8) || w2w c) = c:6 word) /\
        (w2w ((192w:word8) || w2w c) = c:6 word)` by blastLib.BBLAST_TAC
  THEN FULL_SIMP_TAC std_ss []);

val _ = export_theory();

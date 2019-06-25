(*
  The formal semantics of stackLang
*)

open preamble stackLangTheory
local open wordSemTheory labSemTheory in end

val _ = new_theory"stackSem";

val _ = set_grammar_ancestry
  ["stackLang",
   "wordSem" (* for word_loc *)
  ];

val _ = Datatype `
  result = Result ('w word_loc)
         | Exception ('w word_loc)
         | Halt ('w word_loc)
         | TimeOut
         | FinalFFI final_event
         | Error `

val bit_length_def = Define `
  bit_length w = if w = 0w then (0:num) else bit_length (w >>> 1) + 1`;

val filter_bitmap_def = Define `
  (filter_bitmap [] rs = SOME ([],rs)) /\
  (filter_bitmap (F::bs) (r::rs) = filter_bitmap bs rs) /\
  (filter_bitmap (T::bs) (r::rs) =
     case filter_bitmap bs rs of
     | NONE => NONE
     | SOME (ts,rs') => SOME (r::ts,rs')) /\
  (filter_bitmap _ _ = NONE)`

val map_bitmap_def = Define `
  (map_bitmap [] ts rs = SOME ([],ts,rs)) /\
  (map_bitmap (F::bs) ts (r::rs) =
     case map_bitmap bs ts rs of
     | NONE => NONE
     | SOME (xs,ys,zs) => SOME (r::xs,ys,zs)) /\
  (map_bitmap (T::bs) (t::ts) (r::rs) =
     case map_bitmap bs ts rs of
     | NONE => NONE
     | SOME (xs,ys,zs) => SOME (t::xs,ys,zs)) /\
  (map_bitmap _ _ _ = NONE)`

Theorem filter_bitmap_LENGTH:
   !bs xs x y. (filter_bitmap bs xs = SOME (x,y)) ==> LENGTH y <= LENGTH xs
Proof
  Induct \\ fs [filter_bitmap_def] \\ Cases_on `xs` \\ TRY (Cases_on `h`)
  \\ fs [filter_bitmap_def] \\ Cases \\ fs [filter_bitmap_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ res_tac \\ decide_tac
QED

Theorem map_bitmap_LENGTH:
   !t1 t2 t3 x y z. (map_bitmap t1 t2 t3 = SOME (x,y,z)) ==>
                   LENGTH y ≤ LENGTH t2 ∧
                   LENGTH z <= LENGTH t3
Proof
  Induct \\ fs [map_bitmap_def] \\ Cases_on `t2` \\ Cases_on `t3`
  \\ TRY (Cases_on `h`)
  \\ fs [map_bitmap_def] \\ Cases \\ fs [map_bitmap_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ res_tac \\ fs[] \\ decide_tac
QED

val read_bitmap_def = Define `
  (read_bitmap [] = NONE) /\
  (read_bitmap ((w:'a word)::ws) =
     if word_msb w then (* there is a continuation *)
       case read_bitmap ws of
       | NONE => NONE
       | SOME bs => SOME (GENLIST (\i. w ' i) (dimindex (:'a) - 1) ++ bs)
     else (* this is the last bitmap word *)
       SOME (GENLIST (\i. w ' i) (bit_length w - 1)))`

val _ = Datatype.big_record_size := 25;

val _ = Datatype `
  state =
    <| regs    : num |-> 'a word_loc
     ; fp_regs : num |-> word64
     ; store   : store_name |-> 'a word_loc
     ; stack   : ('a word_loc) list
     ; stack_space : num
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     ; bitmaps : 'a word list
     ; compile : 'c -> (num # 'a stackLang$prog) list -> (word8 list # 'c) option
     ; compile_oracle : num -> 'c # (num # 'a stackLang$prog) list # 'a word list
     ; code_buffer : ('a,8) buffer
     ; data_buffer : ('a,'a) buffer
     ; gc_fun  : 'a gc_fun_type
     ; use_stack : bool
     ; use_store : bool
     ; use_alloc : bool
     ; clock   : num
     ; code    : ('a stackLang$prog) num_map
     ; ffi     : 'ffi ffi_state
     ; ffi_save_regs : num set
     ; be      : bool (* is big-endian *) |> `

val mem_store_def = Define `
  mem_store (addr:'a word) (w:'a word_loc) (s:('a,'c,'ffi) stackSem$state) =
    if addr IN s.mdomain then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE`

val mem_load_def = Define `
  mem_load (addr:'a word) (s:('a,'c,'ffi) stackSem$state) =
    if addr IN s.mdomain then
      SOME (s.memory addr)
    else NONE`

val dec_clock_def = Define `
  dec_clock (s:('a,'c,'ffi) stackSem$state) = s with clock := s.clock - 1`;

val word_exp_def = tDefine "word_exp" `
  (word_exp s (Const w) = SOME w) /\
  (word_exp s (Var v) =
     case FLOOKUP s.regs v of
     | SOME (Word w) => SOME w
     | _ => NONE) /\
  (word_exp s (Lookup name) =
     case FLOOKUP s.store name of
     | SOME (Word w) => SOME w
     | _ => NONE) /\
  (word_exp s (Load addr) =
     case word_exp s addr of
     | SOME w => (case mem_load w s of
                  | SOME (Word w) => SOME w
                  | _ => NONE)
     | _ => NONE) /\
  (word_exp s (Op op wexps) =
     let ws = MAP (word_exp s) wexps in
       if EVERY IS_SOME ws then word_op op (MAP THE ws) else NONE) /\
  (word_exp s (Shift sh wexp n) =
     case word_exp s wexp of
     | NONE => NONE
     | SOME w => word_sh sh w n)`
  (WF_REL_TAC `measure (exp_size ARB o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC wordLangTheory.MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ DECIDE_TAC)

val get_var_def = Define `
  get_var v (s:('a,'c,'ffi) stackSem$state) = FLOOKUP s.regs v`;

val get_vars_def = Define `
  (get_vars [] s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val get_fp_var_def = Define`
  get_fp_var v (s:('a,'c,'ffi) stackSem$state) = FLOOKUP s.fp_regs v`

val set_var_def = Define `
  set_var v x (s:('a,'c,'ffi) stackSem$state) =
    (s with regs := (s.regs |+ (v,x)))`;

val set_fp_var_def = Define `
  set_fp_var v x (s:('a,'c,'ffi) stackSem$state) =
    (s with fp_regs := (s.fp_regs |+ (v,x)))`;

val set_store_def = Define `
  set_store v x (s:('a,'c,'ffi) stackSem$state) = (s with store := s.store |+ (v,x))`;

val empty_env_def = Define `
  empty_env (s:('a,'c,'ffi) stackSem$state) = s with <| regs := FEMPTY ; stack := [] |>`;

val full_read_bitmap_def = Define `
  (full_read_bitmap bitmaps (Word w) =
     if w = 0w then NONE
     else read_bitmap (DROP (w2n (w - 1w)) bitmaps)) /\
  (full_read_bitmap bitmaps _ = NONE)`

val enc_stack_def = tDefine "enc_stack" `
  (enc_stack bitmaps [] = NONE) /\
  (enc_stack bitmaps (w::ws) =
     if w = Word 0w then (if ws = [] then SOME [] else NONE) else
       case full_read_bitmap bitmaps w of
       | NONE => NONE
       | SOME bs =>
          case filter_bitmap bs ws of
          | NONE => NONE
          | SOME (ts,ws') =>
              case enc_stack bitmaps ws' of
              | NONE => NONE
              | SOME rs => SOME (ts ++ rs))`
 (WF_REL_TAC `measure (LENGTH o SND)` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC filter_bitmap_LENGTH
  \\ fs [] \\ decide_tac)

val dec_stack_def = tDefine "dec_stack" `
  (dec_stack bitmaps _ [] = NONE) ∧
  (dec_stack bitmaps ts (w::ws) =
    if w = Word 0w then (if ts = [] ∧ ws = [] then SOME [Word 0w] else NONE) else
     case full_read_bitmap bitmaps w of
     | NONE => NONE
     | SOME bs =>
        case map_bitmap bs ts ws of
        | NONE => NONE
        | SOME (hd,ts',ws') =>
           case dec_stack bitmaps ts' ws' of
           | NONE => NONE
           | SOME rest => SOME ([w] ++ hd ++ rest))`
  (WF_REL_TAC `measure (LENGTH o SND o SND)` \\ rw []
   \\ IMP_RES_TAC map_bitmap_LENGTH
   \\ fs [LENGTH_NIL] \\ rw []
   \\ fs [map_bitmap_def] \\ rw [] \\ decide_tac)

val gc_def = Define `
  gc s =
    if LENGTH s.stack < s.stack_space then NONE else
      let unused = TAKE s.stack_space s.stack in
      let stack = DROP s.stack_space s.stack in
        case enc_stack s.bitmaps (DROP s.stack_space s.stack) of
        | NONE => NONE
        | SOME wl_list =>
          case s.gc_fun (wl_list, s.memory, s.mdomain, s.store) of
          | NONE => NONE
          | SOME (wl,m,st) =>
           (case dec_stack s.bitmaps wl stack of
            | NONE => NONE
            | SOME stack =>
                SOME (s with <| stack := unused ++ stack
                              ; store := st
                              ; regs := FEMPTY
                              ; memory := m |>))`

val has_space_def = Define `
  has_space wl store =
    case (wl, FLOOKUP store NextFree, FLOOKUP store TriggerGC) of
    | (Word w, SOME (Word n), SOME (Word l)) => SOME (w2n w <= w2n (l - n))
    | _ => NONE`

val alloc_def = Define `
  alloc (w:'a word) (s:('a,'c,'ffi) stackSem$state) =
    (* perform garbage collection *)
      case gc (set_store AllocSize (Word w) s) of
      | NONE => (SOME Error,s)
      | SOME s =>
         (* read how much space should be allocated *)
         (case FLOOKUP s.store AllocSize of
          | NONE => (SOME Error, s)
          | SOME w =>
           (* check how much space there is *)
           (case has_space w s.store of
            | NONE => (SOME Error, s)
            | SOME T => (* success there is that much space *)
                        (NONE,s)
            | SOME F => (* fail, GC didn't free up enough space *)
                        (SOME (Halt (Word (1w:'a word))),empty_env s)))`

val assign_def = Define `
  assign reg exp s =
    case word_exp s exp of
     | NONE => NONE
     | SOME w => SOME (set_var reg (Word w) s)`;

val inst_def = Define `
  inst i (s:('a,'c,'ffi) stackSem$state) =
    case i of
    | Skip => SOME s
    | Const reg w => assign reg (Const w) s
    | Arith (Binop bop r1 r2 ri) =>
        if bop = Or /\ ri = Reg r2 then
          case FLOOKUP s.regs r2 of
          | NONE => NONE
          | SOME w => SOME (set_var r1 w s)
        else
          assign r1
            (Op bop [Var r2; case ri of Reg r3 => Var r3
                                      | Imm w => Const w]) s
    | Arith (Shift sh r1 r2 n) =>
        assign r1
          (Shift sh (Var r2) n) s
    | Arith (Div r1 r2 r3) =>
       (let vs = get_vars[r3;r2] s in
       case vs of
       SOME [Word q;Word w2] =>
         if q ≠ 0w then
           SOME (set_var r1 (Word (w2 / q)) s)
         else NONE
      | _ => NONE)
    | Arith (AddCarry r1 r2 r3 r4) =>
        (let vs = get_vars [r2;r3;r4] s in
        case vs of
        SOME [Word l;Word r;Word c] =>
          let res = w2n l + w2n r + if c = (0w:'a word) then 0 else 1 in
            SOME (set_var r4 (Word (if dimword(:'a) ≤ res then (1w:'a word) else 0w))
                 (set_var r1 (Word (n2w res)) s))

        | _ => NONE)
    | Arith (AddOverflow r1 r2 r3 r4) =>
        (let vs = get_vars [r2;r3] s in
        case vs of
        SOME [Word w2;Word w3] =>
          SOME (set_var r4 (Word (if w2i (w2 + w3) ≠ w2i w2 + w2i w3 then 1w else 0w))
                 (set_var r1 (Word (w2 + w3)) s))
        | _ => NONE)
    | Arith (SubOverflow r1 r2 r3 r4) =>
        (let vs = get_vars [r2;r3] s in
        case vs of
        SOME [Word w2;Word w3] =>
          SOME (set_var r4 (Word (if w2i (w2 - w3) ≠ w2i w2 - w2i w3 then 1w else 0w))
                 (set_var r1 (Word (w2 - w3)) s))
        | _ => NONE)
    | Arith (LongMul r1 r2 r3 r4) =>
        (let vs = get_vars [r3;r4] s in
        case vs of
        SOME [Word w3;Word w4] =>
         let r = w2n w3 * w2n w4 in
           SOME (set_var r2 (Word (n2w r)) (set_var r1 (Word (n2w (r DIV dimword(:'a)))) s))
        | _ => NONE)
    | Arith (LongDiv r1 r2 r3 r4 r5) =>
       (let vs = get_vars [r3;r4;r5] s in
       case vs of
       SOME [Word w3;Word w4;Word w5] =>
         let n = w2n w3 * dimword (:'a) + w2n w4 in
         let d = w2n w5 in
         let q = n DIV d in
         if (d ≠ 0 ∧ q < dimword(:'a)) then
           SOME (set_var r1 (Word (n2w q)) (set_var r2 (Word (n2w (n MOD d))) s))
         else NONE
      | _ => NONE)
    | Mem Load r (Addr a w) =>
       (case word_exp s (Op Add [Var a; Const w]) of
        | NONE => NONE
        | SOME w =>
            case mem_load w s of
            | NONE => NONE
            | SOME w => SOME (set_var r w s))
    | Mem Load8 r (Addr a w) =>
       (case word_exp s (Op Add [Var a; Const w]) of
        | SOME w =>
           (case mem_load_byte_aux s.memory s.mdomain s.be w of
            | NONE => NONE
            | SOME w => SOME (set_var r (Word (w2w w)) s))
        | _ => NONE)
    | Mem Store r (Addr a w) =>
       (case (word_exp s (Op Add [Var a; Const w]), get_var r s) of
        | (SOME a, SOME w) =>
            (case mem_store a w s of
             | SOME s1 => SOME s1
             | NONE => NONE)
        | _ => NONE)
    | Mem Store8 r (Addr a w) =>
       (case (word_exp s (Op Add [Var a; Const w]), get_var r s) of
        | (SOME a, SOME (Word w)) =>
            (case mem_store_byte_aux s.memory s.mdomain s.be a (w2w w) of
             | SOME new_m => SOME (s with memory := new_m)
             | NONE => NONE)
        | _ => NONE)
    | FP (FPLess r d1 d2) =>
      (case (get_fp_var d1 s,get_fp_var d2 s) of
      | (SOME f1 ,SOME f2) =>
        SOME (set_var r
          (Word (if fp64_lessThan f1 f2
                 then 1w
                 else 0w)) s)
      | _ => NONE)
    | FP (FPLessEqual r d1 d2) =>
      (case (get_fp_var d1 s,get_fp_var d2 s) of
      | (SOME f1, SOME f2) =>
        SOME (set_var r
          (Word (if fp64_lessEqual f1 f2
                 then 1w
                 else 0w)) s)
      | _ => NONE)
    | FP (FPEqual r d1 d2) =>
      (case (get_fp_var d1 s,get_fp_var d2 s) of
      | (SOME f1, SOME f2) =>
        SOME (set_var r
          (Word (if fp64_equal f1 f2
                 then 1w
                 else 0w)) s)
      | _ => NONE)
    | FP (FPMov d1 d2) =>
      (case get_fp_var d2 s of
      | SOME f =>
        SOME (set_fp_var d1 f s)
      | _ => NONE)
    | FP (FPAbs d1 d2) =>
      (case get_fp_var d2 s of
      | SOME f =>
        SOME (set_fp_var d1 (fp64_abs f) s)
      | _ => NONE)
    | FP (FPNeg d1 d2) =>
      (case get_fp_var d2 s of
      | SOME f =>
        SOME (set_fp_var d1 (fp64_negate f) s)
      | _ => NONE)
    | FP (FPSqrt d1 d2) =>
      (case get_fp_var d2 s of
      | SOME f =>
        SOME (set_fp_var d1 (fp64_sqrt roundTiesToEven f) s)
      | _ => NONE)
    | FP (FPAdd d1 d2 d3) =>
      (case (get_fp_var d2 s,get_fp_var d3 s) of
      | (SOME f1,SOME f2) =>
        SOME (set_fp_var d1 (fp64_add roundTiesToEven f1 f2) s)
      | _ => NONE)
    | FP (FPSub d1 d2 d3) =>
      (case (get_fp_var d2 s,get_fp_var d3 s) of
      | (SOME f1,SOME f2) =>
        SOME (set_fp_var d1 (fp64_sub roundTiesToEven f1 f2) s)
      | _ => NONE)
    | FP (FPMul d1 d2 d3) =>
      (case (get_fp_var d2 s,get_fp_var d3 s) of
      | (SOME f1,SOME f2) =>
        SOME (set_fp_var d1 (fp64_mul roundTiesToEven f1 f2) s)
      | _ => NONE)
    | FP (FPDiv d1 d2 d3) =>
      (case (get_fp_var d2 s,get_fp_var d3 s) of
      | (SOME f1,SOME f2) =>
        SOME (set_fp_var d1 (fp64_div roundTiesToEven f1 f2) s)
      | _ => NONE)
    | FP (FPFma d1 d2 d3) =>
      (case (get_fp_var d1 s, get_fp_var d2 s, get_fp_var d3 s) of
      | (SOME f1, SOME f2, SOME f3) =>
        SOME (set_fp_var d1 (fpSem$fpfma f1 f2 f3) s)
      | _ => NONE)
    | FP (FPMovToReg r1 r2 d) =>
      (case get_fp_var d s of
      | SOME v =>
        if dimindex(:'a) = 64 then
          SOME (set_var r1 (Word (w2w v)) s)
        else
          SOME (set_var r2 (Word ((63 >< 32) v)) (set_var r1 (Word ((31 >< 0) v)) s))
      | _ => NONE)
    | FP (FPMovFromReg d r1 r2) =>
      (if dimindex(:'a) = 64 then
        case get_var r1 s of
          SOME (Word w1) => SOME (set_fp_var d (w2w w1) s)
        | _ => NONE
      else
        case (get_var r1 s,get_var r2 s) of
          (SOME (Word w1),SOME (Word w2)) => SOME (set_fp_var d (w2 @@ w1) s)
        | _ => NONE)
    | FP (FPToInt d1 d2) =>
      (case get_fp_var d2 s of
        NONE => NONE
      | SOME f =>
      case fp64_to_int roundTiesToEven f of
        NONE => NONE
      | SOME i =>
        let w = i2w i : word32 in
        if w2i w = i then
          (if dimindex(:'a) = 64 then
             SOME (set_fp_var d1 (w2w w) s)
           else
           case get_fp_var (d1 DIV 2) s of
             NONE => NONE
           | SOME f =>
             let (h, l) = if ODD d1 then (63, 32) else (31, 0) in
                  SOME (set_fp_var (d1 DIV 2) (bit_field_insert h l w f) s))
        else
          NONE)
    | FP (FPFromInt d1 d2) =>
      if dimindex(:'a) = 64 then
        case get_fp_var d2 s of
        | SOME f =>
          let i =  w2i ((31 >< 0) f : word32) in
            SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
        | NONE => NONE
      else
        case get_fp_var (d2 DIV 2) s of
        | SOME v =>
          let i =  w2i (if ODD d2 then (63 >< 32) v else (31 >< 0) v : 'a word) in
            SOME (set_fp_var d1 (int_to_fp64 roundTiesToEven i) s)
        | NONE => NONE
    | _ => NONE`

val get_var_imm_def = Define`
  (get_var_imm ((Reg n):'a reg_imm) s = get_var n s) /\
  (get_var_imm (Imm w) s = SOME(Word w))`

val find_code_def = Define `
  (find_code (INL p) regs code = sptree$lookup p code) /\
  (find_code (INR r) regs code =
     case FLOOKUP regs r of
       SOME (Loc loc 0) => lookup loc code
     | other => NONE)`

val fix_clock_def = Define `
  fix_clock s (res,s1) = (res,s1 with clock := MIN s.clock s1.clock)`

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (res,s1) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val STOP_def = Define `STOP x = x`;

val get_labels_def = Define `
  (get_labels (Seq p1 p2) = get_labels p1 UNION get_labels p2) /\
  (get_labels (If _ _ _ p1 p2) = get_labels p1 UNION get_labels p2) /\
  (get_labels (Call ret _ handler) =
     (case ret of
      | NONE => {}
      | SOME (r,_,l1,l2) => (l1,l2) INSERT get_labels r UNION
          (case handler of
           | NONE => {}
           | SOME (r,l1,l2) => (l1,l2) INSERT get_labels r))) /\
  (get_labels (Halt _) = {}) /\
  (get_labels _ = {})`

val loc_check_def = Define `
  loc_check code (l1,l2) <=>
    (l2 = 0 /\ l1 ∈ domain code) \/
    ?n e. lookup n code = SOME e /\ (l1,l2) IN get_labels e`;

val evaluate_def = tDefine "evaluate" `
  (evaluate (Skip:'a stackLang$prog,s) = (NONE,s:('a,'c,'ffi) stackSem$state)) /\
  (evaluate (Halt v,s) =
     case get_var v s of
     | SOME w => (SOME (Halt w), empty_env s)
     | NONE => (SOME Error, s)) /\
  (evaluate (Alloc n,s) =
     if ~s.use_alloc then (SOME Error,s) else
     case get_var n s of
     | SOME (Word w) => alloc w s
     | _ => (SOME Error,s)) /\
  (evaluate (Inst i,s) =
     case inst i s of
     | SOME s1 => (NONE, s1)
     | NONE => (SOME Error, s)) /\
  (evaluate (Get v name,s) =
     if ¬s.use_store then (SOME Error,s) else
     case FLOOKUP s.store name of
     | SOME x => (NONE, set_var v x s)
     | NONE => (SOME Error, s)) /\
  (evaluate (Set name v,s) =
     if ¬s.use_store then (SOME Error,s) else
     case get_var v s of
     | SOME w => (NONE, set_store name w s)
     | NONE => (SOME Error, s)) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,empty_env s)
                    else (NONE,dec_clock s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (Return n m,s) =
     case (get_var n s ,get_var m s) of
     | (SOME (Loc l1 l2),SOME _) => (SOME (Result (Loc l1 l2)),s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise n,s) =
     case get_var n s of
     | SOME (Loc l1 l2) => (SOME (Exception (Loc l1 l2)),s)
     | _ => (SOME Error,s)) /\
  (evaluate (If cmp r1 ri c1 c2,s) =
    (case (get_var r1 s,get_var_imm ri s)of
    | SOME x,SOME y =>
     (case labSem$word_cmp cmp x y of
      | SOME T => evaluate (c1,s)
      | SOME F => evaluate (c2,s)
      | NONE => (SOME Error,s))
    | _ => (SOME Error,s))) /\
  (evaluate (While cmp r1 ri c1,s) =
    (case (get_var r1 s,get_var_imm ri s)of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y
      then let (res,s1) = fix_clock s (evaluate (c1,s)) in
             if res <> NONE then (res,s1) else
             if s1.clock = 0 then (SOME TimeOut,empty_env s1) else
               evaluate (STOP (While cmp r1 ri c1),dec_clock s1)
      else (NONE,s)
    | _ => (SOME Error,s))) /\
  (evaluate (JumpLower r1 r2 dest,s) =
    case (get_var r1 s, get_var r2 s) of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp Lower x y then
       (case find_code (INL dest) s.regs s.code of
        | NONE => (SOME Error,s)
        | SOME prog =>
           if s.clock = 0 then (SOME TimeOut,empty_env s) else
             (case evaluate (prog,dec_clock s) of
              | (NONE,s) => (SOME Error,s)
              | (SOME res,s) => (SOME res,s)))
      else (NONE,s)
    | _ => (SOME Error,s)) /\
  (evaluate (Call ret dest handler,s) =
     case ret of
     (* tail call *)
     | NONE =>
       (case find_code dest s.regs s.code of
        | NONE => (SOME Error,s)
        | SOME prog =>
           if handler <> NONE then (SOME Error,s) else
           if s.clock = 0 then (SOME TimeOut,empty_env s) else
             (case fix_clock (dec_clock s) (evaluate (prog,dec_clock s)) of
              | (NONE,s) => (SOME Error,s)
              | (SOME res,s) => (SOME res,s)))
     (* returning call, returns into var n *)
     | SOME (ret_handler,link_reg,l1,l2) =>
       (case find_code dest (s.regs \\ link_reg) s.code of
        | NONE => (SOME Error,s)
        | SOME prog =>
           if s.clock = 0 then (SOME TimeOut,empty_env s) else
             (case fix_clock (dec_clock (set_var link_reg (Loc l1 l2) s))
             (evaluate (prog, dec_clock (set_var link_reg (Loc l1 l2) s))) of
              | (SOME (Result x),s2) =>
                  if x <> Loc l1 l2 then (SOME Error,s2)
                  else evaluate(ret_handler,s2)
              | (SOME (Exception x),s2) =>
                  (case handler of (* if handler is present, then handle exc *)
                   | NONE => (SOME (Exception x),s2)
                   | SOME (h,l1,l2) =>
                      if x <> Loc l1 l2 then (SOME Error,s2) else
                        evaluate (h,s2))
              | (NONE,s) => (SOME Error,s)
              | res => res))) /\
  (evaluate (Install ptr len dptr dlen ret,s) =
    case (get_var ptr s, get_var len s, get_var dptr s, get_var dlen s) of
    | SOME (Word w1), SOME (Word w2), SOME (Word w3), SOME (Word w4) =>
        let (cfg,progs,bm) = s.compile_oracle 0 in
       (case (buffer_flush s.code_buffer w1 w2,
              if s.use_stack then buffer_flush s.data_buffer w3 w4
              else SOME (bm, s.data_buffer)) of
         SOME (bytes, cb), SOME (data, db) =>
        let new_oracle = shift_seq 1 s.compile_oracle in
        (case s.compile cfg progs, progs of
          | SOME (bytes',cfg'), (k,prog)::_ =>
            if bytes = bytes' ∧ data = bm ∧ FST(new_oracle 0) = cfg' then
            let s' =
                s with <|
                  bitmaps := s.bitmaps ++ bm
                ; code_buffer := cb
                ; data_buffer := db
                ; code := union s.code (fromAList progs)
                (* This order is convenient because it means all of s.code's entries are preserved *)
                (* TODO: this might need to be a new field, cc_save_regs *)
                ; regs := (DRESTRICT s.regs s.ffi_save_regs) |+ (ptr,Loc k 0)
                ; compile_oracle := new_oracle
                |> in
              (NONE,s')
            else (SOME Error,s)
          | _ => (SOME Error,s))
        | _ => (SOME Error,s))
      | _ => (SOME Error,s)) /\
  (evaluate (CodeBufferWrite r1 r2,s) =
    (case (get_var r1 s,get_var r2 s) of
        | (SOME (Word w1), SOME (Word w2)) =>
          (case buffer_write s.code_buffer w1 (w2w w2) of
          | SOME new_cb =>
            (NONE,s with code_buffer:=new_cb)
          | _ => (SOME Error,s))
        | _ => (SOME Error,s))) /\
  (evaluate (DataBufferWrite r1 r2,s) =
    if ~s.use_stack then (SOME Error,s) else
    (case (get_var r1 s,get_var r2 s) of
        | (SOME (Word w1), SOME (Word w2)) =>
          (case buffer_write s.data_buffer w1 w2 of
          | SOME new_db =>
            (NONE,s with data_buffer:=new_db)
          | _ => (SOME Error,s))
        | _ => (SOME Error,s))) /\
  (evaluate (FFI ffi_index ptr len ptr2 len2 ret,s) =
    case (get_var len s, get_var ptr s,get_var len2 s, get_var ptr2 s) of
    | SOME (Word w),SOME (Word w2),SOME (Word w3),SOME (Word w4) =>
         (case (read_bytearray w2 (w2n w) (mem_load_byte_aux s.memory s.mdomain s.be),
                read_bytearray w4 (w2n w3) (mem_load_byte_aux s.memory s.mdomain s.be)) of
          | SOME bytes,SOME bytes2 =>
             (case call_FFI s.ffi ffi_index bytes bytes2 of
              | FFI_final outcome => (SOME (FinalFFI outcome),s)
              | FFI_return new_ffi new_bytes =>
                  let new_m = write_bytearray w4 new_bytes s.memory s.mdomain s.be in
                    (NONE, s with <| memory := new_m ;
                                     regs := DRESTRICT s.regs s.ffi_save_regs;
                                     ffi := new_ffi |>))
          | _ => (SOME Error,s))
    | res => (SOME Error,s)) /\
  (evaluate (LocValue r l1 l2,s) =
     if loc_check s.code (l1,l2) then
       (NONE,set_var r (Loc l1 l2) s)
     else (SOME Error,s)) /\
  (evaluate (StackAlloc n,s) =
     if ~s.use_stack then (SOME Error,s) else
     if s.stack_space < n then (SOME (Halt (Word 2w)),empty_env s) else
       (NONE, s with stack_space := s.stack_space - n)) /\
  (evaluate (StackFree n,s) =
     if ~s.use_stack then (SOME Error,s) else
     if LENGTH s.stack < s.stack_space + n then (SOME Error,empty_env s) else
       (NONE, s with stack_space := s.stack_space + n)) /\
  (evaluate (StackLoad r n,s) =
     if ~s.use_stack then (SOME Error,s) else
     if s.stack_space + n < LENGTH s.stack
       then (NONE, set_var r (EL (s.stack_space + n) s.stack) s)
     else (SOME Error,empty_env s)) /\
  (evaluate (StackLoadAny r rn,s) =
     if ~s.use_stack then (SOME Error,s) else
       case get_var rn s of
       | SOME (Word (w:'a word)) =>
         let i = s.stack_space + w2n (w >>> word_shift (:'a)) in
           if i < LENGTH s.stack /\
              ((w >>> word_shift (:'a)) << word_shift (:'a) = w)
           then (NONE, set_var r (EL i s.stack) s)
           else (SOME Error,empty_env s)
       | _ => (SOME Error,empty_env s)) /\
  (evaluate (StackStore r n,s) =
     if ~s.use_stack then (SOME Error,s) else
     if LENGTH s.stack ≤ s.stack_space + n then (SOME Error,empty_env s) else
       case get_var r s of
       | NONE => (SOME Error,empty_env s)
       | SOME v => (NONE, s with stack := LUPDATE v (s.stack_space + n) s.stack)) /\
  (evaluate (StackStoreAny r rn,s) =
     if ~s.use_stack then (SOME Error,s) else
       case (get_var r s, get_var rn s) of
       | (SOME v, SOME (Word (w:'a word))) =>
         let i = s.stack_space + w2n (w >>> word_shift (:'a)) in
           if i < LENGTH s.stack /\
              ((w >>> word_shift (:'a)) << word_shift (:'a) = w)
           then (NONE, s with stack := LUPDATE v i s.stack)
           else (SOME Error,empty_env s)
       | _ => (SOME Error,empty_env s)) /\
  (evaluate (StackGetSize r,s) =
     if ~s.use_stack then (SOME Error,s) else
     (NONE, set_var r (Word (n2w s.stack_space)) s)) /\
  (evaluate (StackSetSize r,s) =
     if ~s.use_stack then (SOME Error,s) else
     case get_var r s of
     | SOME (Word (w:'a word)) =>
         if LENGTH s.stack ≤ w2n w then (SOME Error,empty_env s)
         else (NONE, set_var r (Word (w << word_shift (:'a)))
                       (s with stack_space := w2n w))
     | _ => (SOME Error,s)) /\
  (evaluate (BitmapLoad r v,s) =
     if ~s.use_stack \/ r = v then (SOME Error,s) else
     case get_var v s of
     | SOME (Word w) =>
         if LENGTH s.bitmaps <= w2n w then (SOME Error,s)
         else (NONE, set_var r (Word (EL (w2n w) s.bitmaps)) s)
     | _ => (SOME Error,s))`
  (WF_REL_TAC `(inv_image (measure I LEX measure (prog_size (K 0)))
                             (\(xs,(s:('a,'c,'ffi) stackSem$state)). (s.clock,xs)))`
   \\ rpt strip_tac
   \\ fs[empty_env_def,dec_clock_def,set_var_def,STOP_def]
   \\ imp_res_tac fix_clock_IMP \\ fs []
   \\ imp_res_tac (GSYM fix_clock_IMP) \\ fs [] \\ decide_tac)

val evaluate_ind = theorem"evaluate_ind";

(* We prove that the clock never increases. *)

Theorem gc_clock:
   !s1 s2. (gc s1 = SOME s2) ==> s2.clock <= s1.clock
Proof
  fs [gc_def,LET_DEF] \\ SRW_TAC [] []
  \\ every_case_tac >> fs[]
  \\ SRW_TAC [] [] \\ fs []
QED

Theorem alloc_clock:
   !xs s1 vs s2. (alloc x s1 = (vs,s2)) ==> s2.clock <= s1.clock
Proof
  SIMP_TAC std_ss [alloc_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ SRW_TAC [] [] \\ fs []
  \\ Q.ABBREV_TAC `s3 = set_store AllocSize (Word x) s1`
  \\ `s3.clock=s1.clock` by (Q.UNABBREV_TAC`s3`>>fs[set_store_def])
  \\ IMP_RES_TAC gc_clock \\ fs []
  \\ UNABBREV_ALL_TAC \\ fs []
  \\ Cases_on `x'` \\ fs [] \\ SRW_TAC [] []
  \\ EVAL_TAC \\ decide_tac
QED

val inst_clock = Q.prove(
  `inst i s = SOME s2 ==> s2.clock <= s.clock`,
  Cases_on `i` \\ fs [inst_def,assign_def] \\ every_case_tac
  \\ SRW_TAC [] [set_var_def] \\ fs []
  \\ fs [mem_store_def] \\ SRW_TAC [] []\\
  EVAL_TAC \\ fs[]);

Theorem evaluate_clock:
   !xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock
Proof
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss [STOP_def]
  \\ TRY BasicProvers.TOP_CASE_TAC \\ fs []
  \\ rpt (every_case_tac \\ fs []
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [empty_env_def]
    \\ IMP_RES_TAC inst_clock
    \\ IMP_RES_TAC alloc_clock
    \\ fs [set_var_def,set_store_def,dec_clock_def,LET_THM]
    \\ rpt (pairarg_tac \\ fs [])
    \\ every_case_tac \\ fs []
    \\ imp_res_tac fix_clock_IMP \\ fs []
    \\ imp_res_tac LESS_EQ_TRANS \\ fs [] \\ rfs []
    \\ TRY decide_tac)
QED

Theorem fix_clock_evaluate:
   fix_clock s (evaluate (xs,s)) = evaluate (xs,s)
Proof
  Cases_on `evaluate (xs,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,GSYM NOT_LESS,theorem "state_component_equality"]
QED

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

(* observational semantics *)

val semantics_def = Define `
  semantics start s =
  let prog = Call NONE (INL start) NONE in
  if ∃k. let res = FST (evaluate (prog, s with clock := k)) in
           res <> SOME TimeOut /\ res <> SOME (Result (Loc 1 0)) /\
           (!w. res <> SOME (Halt (Word w))) /\ !f. res <> SOME (FinalFFI f)
  then Fail
  else
    case some res.
      ∃k t r outcome.
        evaluate (prog, s with clock := k) = (SOME r,t) ∧
        (case r of
         | FinalFFI e => outcome = FFI_outcome e
         | Halt w => outcome = if w = Word 0w then Success
                               else Resource_limit_hit
         | Result _ => outcome = Success
         | _ => F) ∧
        res = Terminate outcome t.ffi.io_events
      of
    | SOME res => res
    | NONE =>
      Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))`;

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();

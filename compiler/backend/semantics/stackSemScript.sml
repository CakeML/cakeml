open preamble stackLangTheory wordSemTheory labSemTheory;

val _ = new_theory"stackSem";

(* TODO: move *)

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

val filter_bitmap_LENGTH = prove(
  ``!bs xs x y. (filter_bitmap bs xs = SOME (x,y)) ==> LENGTH y <= LENGTH xs``,
  Induct \\ fs [filter_bitmap_def] \\ Cases_on `xs` \\ TRY (Cases_on `h`)
  \\ fs [filter_bitmap_def] \\ Cases \\ fs [filter_bitmap_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ res_tac \\ decide_tac);

val map_bitmap_LENGTH = prove(
  ``!t1 t2 t3 x y z. (map_bitmap t1 t2 t3 = SOME (x,y,z)) ==>
                   LENGTH y ≤ LENGTH t2 ∧
                   LENGTH z <= LENGTH t3``,
  Induct \\ fs [map_bitmap_def] \\ Cases_on `t2` \\ Cases_on `t3`
  \\ TRY (Cases_on `h`)
  \\ fs [map_bitmap_def] \\ Cases \\ fs [map_bitmap_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ res_tac \\ fs[] \\ decide_tac);

(* -- *)

val _ = Datatype `
  result = Result ('w word_loc)
         | Exception ('w word_loc)
         | Halt ('w word_loc)
         | TimeOut
         | Error `

val read_bitmap_def = Define `
  (read_bitmap [] = NONE) /\
  (read_bitmap ((w:'a word)::ws) =
     if word_msb w then (* there is a continuation *)
       case read_bitmap ws of
       | NONE => NONE
       | SOME bs => SOME (GENLIST (\i. w ' i) (dimindex (:'a) - 1) ++ bs)
     else (* this is the last bitmap word *)
       SOME (GENLIST (\i. w ' i) (bit_length w - 1)))`

val _ = Datatype `
  state =
    <| regs    : num |-> 'a word_loc
     ; store   : store_name |-> 'a word_loc
     ; stack   : ('a word_loc) list
     ; stack_space : num
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     ; bitmaps : 'a word list
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
  mem_store (addr:'a word) (w:'a word_loc) (s:('a,'ffi) stackSem$state) =
    if addr IN s.mdomain then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE`

val mem_load_def = Define `
  mem_load (addr:'a word) (s:('a,'ffi) stackSem$state) =
    if addr IN s.mdomain then
      SOME (s.memory addr)
    else NONE`

val dec_clock_def = Define `
  dec_clock (s:('a,'ffi) stackSem$state) = s with clock := s.clock - 1`;

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
  (word_exp s (Shift sh wexp nexp) =
     case word_exp s wexp of
     | NONE => NONE
     | SOME w => word_sh sh w (num_exp nexp))`
  (WF_REL_TAC `measure (exp_size ARB o SND)`
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC wordLangTheory.MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ DECIDE_TAC)

val get_var_def = Define `
  get_var v (s:('a,'ffi) stackSem$state) = FLOOKUP s.regs v`;

val get_vars_def = Define `
  (get_vars [] s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val set_var_def = Define `
  set_var v x (s:('a,'ffi) stackSem$state) =
    (s with regs := (s.regs |+ (v,x)))`;

val set_store_def = Define `
  set_store v x (s:('a,'ffi) stackSem$state) = (s with store := s.store |+ (v,x))`;

val check_clock_def = Define `
  check_clock (s1:('a,'ffi) stackSem$state) (s2:('a,'ffi) stackSem$state) =
    if s1.clock <= s2.clock then s1 else s1 with clock := s2.clock`;

val check_clock_thm = prove(
  ``(check_clock s1 s2).clock <= s2.clock /\
    (s1.clock <= s2.clock ==> (check_clock s1 s2 = s1))``,
  SRW_TAC [] [check_clock_def])

val check_clock_alt = prove(
  ``(s1.clock <= (dec_clock s2).clock ==> (check_clock s1 s2 = s1))``,
  SRW_TAC [] [check_clock_def,dec_clock_def] \\ `F` by DECIDE_TAC)

val check_clock_lemma = prove(
  ``b ==> ((check_clock s1 s).clock < s.clock \/
          ((check_clock s1 s).clock = s.clock) /\ b)``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val empty_env_def = Define `
  empty_env (s:('a,'ffi) stackSem$state) = s with <| regs := FEMPTY ; stack := [] |>`;

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
    case (wl, FLOOKUP store NextFree, FLOOKUP store EndOfHeap) of
    | (Word w, SOME (Word n), SOME (Word l)) => SOME (w2n w <= w2n (l - n))
    | _ => NONE`

val alloc_def = Define `
  alloc (w:'a word) (s:('a,'ffi) stackSem$state) =
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
                        (SOME (Halt (Word 1w)),empty_env s)))`

val assign_def = Define `
  assign reg exp s =
    case word_exp s exp of
     | NONE => NONE
     | SOME w => SOME (set_var reg (Word w) s)`;

val inst_def = Define `
  inst i (s:('a,'ffi) stackSem$state) =
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
          (Shift sh (Var r2) (Nat n)) s
    | Mem Load r (Addr a w) =>
       (case word_exp s (Op Add [Var a; Const w]) of
        | NONE => NONE
        | SOME w =>
            case mem_load w s of
            | NONE => NONE
            | SOME w => SOME (set_var r w s))
    | Mem Store r (Addr a w) =>
       (case (word_exp s (Op Add [Var a; Const w]), get_var r s) of
        | (SOME a, SOME w) =>
            (case mem_store a w s of
             | SOME s1 => SOME s1
             | NONE => NONE)
        | _ => NONE)
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

val fix_clock_IMP = prove(
  ``fix_clock s x = (res,s1) ==> s1.clock <= s.clock``,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val STOP_def = Define `STOP x = x`;

val evaluate_def = tDefine "evaluate" `
  (evaluate (Skip:'a stackLang$prog,s) = (NONE,s:('a,'ffi) stackSem$state)) /\
  (evaluate (Halt v,s) =
     case get_var v s of
     | SOME w => (SOME (Halt w), s)
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
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y then evaluate (c1,s)
                          else evaluate (c2,s)
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
  (evaluate (FFI ffi_index ptr len ret,s) =
    case (get_var ptr s, get_var len s) of
    | SOME (Word w),SOME (Word w2) =>
         (case read_bytearray w2 (w2n w) s.memory s.mdomain s.be of
          | SOME bytes =>
              let (new_ffi,new_bytes) = call_FFI s.ffi ffi_index bytes in
              let new_m = write_bytearray w2 new_bytes s.memory s.mdomain s.be in
                (NONE, s with <| memory := new_m ;
                                 regs := DRESTRICT s.regs s.ffi_save_regs;
                                 ffi := new_ffi |>)
          | _ => (SOME Error,s))
    | res => (SOME Error,s)) /\
  (evaluate (LocValue r l1 l2,s) =
     (NONE,set_var r (Loc l1 l2) s)) /\
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
                             (\(xs,(s:('a,'ffi) stackSem$state)). (s.clock,xs)))`
   \\ rpt strip_tac
   \\ fs[empty_env_def,dec_clock_def,set_var_def,STOP_def]
   \\ imp_res_tac fix_clock_IMP \\ fs []
   \\ imp_res_tac (GSYM fix_clock_IMP) \\ fs [] \\ decide_tac)

val evaluate_ind = theorem"evaluate_ind";

(* We prove that the clock never increases. *)

val gc_clock = store_thm("gc_clock",
  ``!s1 s2. (gc s1 = SOME s2) ==> s2.clock <= s1.clock``,
  fs [gc_def,LET_DEF] \\ SRW_TAC [] []
  \\ every_case_tac >> fs[]
  \\ SRW_TAC [] [] \\ fs []);

val alloc_clock = store_thm("alloc_clock",
  ``!xs s1 vs s2. (alloc x s1 = (vs,s2)) ==> s2.clock <= s1.clock``,
  SIMP_TAC std_ss [alloc_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ SRW_TAC [] [] \\ fs []
  \\ Q.ABBREV_TAC `s3 = set_store AllocSize (Word x) s1`
  \\ `s3.clock=s1.clock` by Q.UNABBREV_TAC`s3`>>fs[set_store_def]
  \\ IMP_RES_TAC gc_clock \\ fs []
  \\ UNABBREV_ALL_TAC \\ fs []
  \\ Cases_on `x'` \\ fs [] \\ SRW_TAC [] []
  \\ EVAL_TAC \\ decide_tac);

val inst_clock = prove(
  ``inst i s = SOME s2 ==> s2.clock <= s.clock``,
  Cases_on `i` \\ fs [inst_def,assign_def] \\ every_case_tac
  \\ SRW_TAC [] [set_var_def] \\ fs []
  \\ fs [mem_store_def] \\ SRW_TAC [] []);

val evaluate_clock = store_thm("evaluate_clock",
  ``!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss [cut_state_opt_def,STOP_def]
  \\ TRY BasicProvers.TOP_CASE_TAC \\ fs []
  \\ rpt (every_case_tac \\ fs []
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def,empty_env_def]
    \\ IMP_RES_TAC inst_clock
    \\ IMP_RES_TAC alloc_clock
    \\ fs [set_var_def,set_store_def,dec_clock_def,LET_THM]
    \\ rpt (split_pair_tac \\ fs [])
    \\ every_case_tac \\ fs []
    \\ imp_res_tac fix_clock_IMP \\ fs []
    \\ imp_res_tac LESS_EQ_TRANS \\ fs [] \\ rfs []
    \\ TRY decide_tac));

val fix_clock_evaluate = store_thm("fix_clock_evaluate",
  ``fix_clock s (evaluate (xs,s)) = evaluate (xs,s)``,
  Cases_on `evaluate (xs,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,GSYM NOT_LESS,theorem "state_component_equality"]);

val evaluate_def = save_thm("evaluate_def",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

(* observational semantics *)

val semantics_def = Define `
  semantics start s =
  let prog = Call NONE (INL start) NONE in
  if ∃k. let res = FST (evaluate (prog, s with clock := k)) in
           res <> SOME TimeOut /\ res <> SOME (Result (Loc 1 0)) /\
           !w. res <> SOME (Halt (Word w))
  then Fail
  else
    case some res.
      ∃k t r outcome.
        evaluate (prog, s with clock := k) = (SOME r,t) ∧
        (case (t.ffi.final_event,r) of
         | (SOME e,_) => outcome = FFI_outcome e
         | (_,Halt w) => outcome = if w = Word 0w then Success
                                   else Resource_limit_hit
         | (_,Result _) => outcome = Success
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

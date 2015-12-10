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
  (map_bitmap [] [] rs = SOME ([],rs)) /\
  (map_bitmap (F::bs) ts (r::rs) =
     case map_bitmap bs ts rs of
     | NONE => NONE
     | SOME (xs,ys) => SOME (r::xs,ys)) /\
  (map_bitmap (T::bs) (t::ts) (r::rs) =
     case map_bitmap bs ts rs of
     | NONE => NONE
     | SOME (ts,rs') => SOME (t::ts,rs')) /\
  (map_bitmap _ _ _ = NONE)`

val filter_bitmap_LENGTH = prove(
  ``!bs xs x y. (filter_bitmap bs xs = SOME (x,y)) ==> LENGTH y <= LENGTH xs``,
  Induct \\ fs [filter_bitmap_def] \\ Cases_on `xs` \\ TRY (Cases_on `h`)
  \\ fs [filter_bitmap_def] \\ Cases \\ fs [filter_bitmap_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ res_tac \\ decide_tac);

val map_bitmap_LENGTH = prove(
  ``!t1 t2 t3 x y. (map_bitmap t1 t2 t3 = SOME (x,y)) ==>
                   LENGTH y <= LENGTH t3``,
  Induct \\ fs [map_bitmap_def] \\ Cases_on `t2` \\ Cases_on `t3`
  \\ TRY (Cases_on `h`)
  \\ fs [map_bitmap_def] \\ Cases \\ fs [map_bitmap_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ res_tac \\ decide_tac);

(* -- *)

val _ = Datatype `
  result = Result ('w word_loc) ('w word_loc)
         | Exception ('w word_loc) ('w word_loc)
         | Halt ('w word_loc)
         | TimeOut
         | Error `

val read_bitmap_def = Define `
  (read_bitmap (Word (w:'a word)::ws) =
     if word_msb w then (* there is a continuation *)
       case read_bitmap ws of
       | NONE => NONE
       | SOME (bs,w',rest) =>
           SOME (GENLIST (\i. w ' i) (dimindex (:'a) - 1) ++ bs,Word w::w',rest)
     else (* this is the last bitmap word *)
       SOME (GENLIST (\i. w ' i) (bit_length w - 1),[Word w],ws)) /\
  (read_bitmap _ = NONE)`

val read_bitmap_LENGTH = store_thm("read_bitmap_LENGTH",
  ``!xs x w y. (read_bitmap xs = SOME (x,w,y)) ==> LENGTH y < LENGTH xs``,
  Induct \\ fs [read_bitmap_def] \\ Cases_on `h`
  \\ fs [read_bitmap_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ decide_tac);

val _ = Datatype `
  state =
    <| regs    : num |-> 'a word_loc
     ; store   : store_name |-> 'a word_loc
     ; stack   : ('a word_loc) list
     ; stack_space : num
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
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

val enc_stack_def = tDefine "enc_stack" `
  (enc_stack ws =
     if ws = [] then NONE else
     if ws = [Word 0w] then SOME [] else
       case read_bitmap ws of
       | NONE => NONE
       | SOME (bs,_,rs) =>
          case filter_bitmap bs rs of
          | NONE => NONE
          | SOME (ts,ws') =>
              case enc_stack ws' of
              | NONE => NONE
              | SOME rs => SOME (ts ++ rs))`
 (WF_REL_TAC `measure LENGTH` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC read_bitmap_LENGTH
  \\ IMP_RES_TAC filter_bitmap_LENGTH
  \\ fs [] \\ decide_tac)

val dec_stack_def = tDefine "dec_stack" `
  (dec_stack [] [] = SOME []) /\
  (dec_stack ts ws =
     case read_bitmap ws of
     | NONE => NONE
     | SOME (bs,w1,ws') =>
        if LENGTH ts < LENGTH bs then NONE else
        case map_bitmap bs (TAKE (LENGTH bs) ts) ws' of
        | NONE => NONE
        | SOME (ws1,ws2) =>
           case dec_stack (DROP (LENGTH bs) ts) ws2 of
           | NONE => NONE
           | SOME ws3 => SOME (w1 ++ ws1 ++ ws3))`
  (WF_REL_TAC `measure (LENGTH o SND)` \\ rw []
   \\ IMP_RES_TAC read_bitmap_LENGTH
   \\ IMP_RES_TAC map_bitmap_LENGTH
   \\ fs [LENGTH_NIL] \\ rw []
   \\ fs [map_bitmap_def] \\ rw [] \\ decide_tac)

val gc_def = Define `
  gc s =
    if LENGTH s.stack < s.stack_space then NONE else
      let unused = TAKE s.stack_space s.stack in
      let stack = DROP s.stack_space s.stack in
        case enc_stack (DROP s.stack_space s.stack) of
        | NONE => NONE
        | SOME wl_list =>
          case s.gc_fun (wl_list, s.memory, s.mdomain, s.store) of
          | NONE => NONE
          | SOME (wl,m,st) =>
           (case dec_stack wl stack of
            | NONE => NONE
            | SOME stack =>
                SOME (s with <| stack := unused ++ stack
                              ; store := st
                              ; regs := FEMPTY
                              ; memory := m |>))`

val has_space_def = Define `
  has_space wl (s:('a,'ffi) stackSem$state) =
    case (wl, FLOOKUP s.store NextFree, FLOOKUP s.store EndOfHeap) of
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
           (case has_space w s of
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
        assign r1
          (Op bop [Var r2; case ri of Reg r3 => Var r3
                                    | Imm w => Const w]) s
    | Arith (Shift sh r1 r2 n) =>
        assign r1
          (Shift sh (Var r2) (Nat n)) s
    | Mem Load r (Addr a w) =>
        assign r (Load (Op Add [Var a; Const w])) s
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
     let (res,s1) = evaluate (c1,s) in
       if res = NONE then evaluate (c2,check_clock s1 s) else (res,s1)) /\
  (evaluate (Return n m,s) =
     case (get_var n s ,get_var m s) of
     | (SOME x,SOME y) => (SOME (Result x y),s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME w => (SOME (Exception w w),s)) /\
  (evaluate (If cmp r1 ri c1 c2,s) =
    (case (get_var r1 s,get_var_imm ri s)of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y then evaluate (c1,s)
                          else evaluate (c2,s)
    | _ => (SOME Error,s))) /\
  (evaluate (JumpLess r1 r2 dest,s) =
    case (get_var r1 s, get_var r2 s) of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp Less x y then
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
     case find_code dest s.regs s.code of
     | NONE => (SOME Error,s)
     | SOME prog =>
     case ret of
     (* tail call *)
     | NONE =>
        if handler <> NONE then (SOME Error,s) else
        if s.clock = 0 then (SOME TimeOut,empty_env s) else
          (case evaluate (prog,dec_clock s) of
           | (NONE,s) => (SOME Error,s)
           | (SOME res,s) => (SOME res,s))
     (* returning call, returns into var n *)
     | SOME (ret_handler,link_reg,l1,l2) =>
        if s.clock = 0 then (SOME TimeOut,empty_env s) else
          (case evaluate (prog, dec_clock s) of
           | (SOME (Result x y),s2) =>
               if x <> Loc l1 l2 then (SOME Error,s2) else
                 (case evaluate(ret_handler,check_clock s2 s) of
                  | (NONE,s) => (NONE,s)
                  | (_,s) => (SOME Error,s))
           | (SOME (Exception x y),s2) =>
               (case handler of (* if handler is present, then handle exc *)
                | NONE => (SOME (Exception x y),s2)
                | SOME (h,l1,l2) =>
                   if x <> Loc l1 l2 then (SOME Error,s2) else
                     evaluate (h, check_clock s2 s))
           | (NONE,s) => (SOME Error,s)
           | res => res)) /\
  (evaluate (FFI ffi_index ptr len,s) =
    case (get_var ptr s, get_var len s) of
    | SOME (Word w),SOME (Word w2) =>
         (case read_bytearray w2 (w2n w) s.memory s.mdomain s.be of
          | SOME bytes =>
              let (new_ffi,new_bytes) = call_FFI s.ffi ffi_index bytes in
              let new_m = write_bytearray w2 new_bytes s.memory s.mdomain s.be in
                (NONE, s with <| memory := new_m ;
                                 regs := DRESTRICT s.regs s.ffi_save_regs |>)
          | _ => (SOME Error,s))
    | res => (SOME Error,s)) /\
  (evaluate (StackAlloc n,s) =
     if ~s.use_stack then (SOME Error,s) else
     if s.stack_space < n then (SOME (Halt (Word 1w)),empty_env s) else
       (NONE, s with stack_space := s.stack_space - n)) /\
  (evaluate (StackFree n,s) =
     if ~s.use_stack then (SOME Error,s) else
     if LENGTH s.stack < s.stack_space + n then (SOME Error,empty_env s) else
       (NONE, s with stack_space := s.stack_space + n)) /\
  (evaluate (StackLoad r n,s) =
     if ~s.use_stack then (SOME Error,s) else
     if LENGTH s.stack < s.stack_space + n then (SOME Error,empty_env s) else
       (NONE, set_var r (EL (s.stack_space + n) s.stack) s)) /\
  (evaluate (StackLoadAny r rn,s) =
     if ~s.use_stack then (SOME Error,s) else
       case get_var rn s of
       | SOME (Word w) =>
           if LENGTH s.stack < s.stack_space + w2n w then (SOME Error,empty_env s)
           else (NONE, set_var r (EL (s.stack_space + w2n w) s.stack) s)
       | _ => (SOME Error,empty_env s)) /\
  (evaluate (StackStore r n,s) =
     if ~s.use_stack then (SOME Error,s) else
     if LENGTH s.stack < s.stack_space + n then (SOME Error,empty_env s) else
       case get_var r s of
       | NONE => (SOME Error,empty_env s)
       | SOME v => (NONE, s with stack := LUPDATE v (s.stack_space + n) s.stack)) /\
  (evaluate (StackStoreAny r rn,s) =
     if ~s.use_stack then (SOME Error,s) else
       case (get_var r s, get_var rn s) of
       | (SOME v, SOME (Word w)) =>
           if LENGTH s.stack < s.stack_space + w2n w then (SOME Error,empty_env s)
           else (NONE, s with stack := LUPDATE v (s.stack_space + w2n w) s.stack)
       | _ => (SOME Error,empty_env s)) /\
  (evaluate (StackGetSize r,s) =
     (NONE, set_var r (Word (n2w s.stack_space)) s)) /\
  (evaluate (StackSetSize r,s) =
     case get_var r s of
     | SOME (Word w) =>
         if LENGTH s.stack < w2n w then (SOME Error,empty_env s)
         else (NONE, s with stack_space := w2n w)
     | _ => (SOME Error,s))`
  (WF_REL_TAC `(inv_image (measure I LEX measure (prog_size (K 0)))
                             (\(xs,(s:('a,'ffi) stackSem$state)). (s.clock,xs)))`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
   \\ fs[empty_env_def,dec_clock_def] \\ DECIDE_TAC)

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
  \\ FULL_SIMP_TAC std_ss [cut_state_opt_def] \\ every_case_tac
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def,empty_env_def]
  \\ IMP_RES_TAC inst_clock
  \\ IMP_RES_TAC alloc_clock
  \\ fs [set_var_def,set_store_def,dec_clock_def,jump_exc_def]
  \\ Cases_on `evaluate (c1,s)` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ simp[] \\ every_case_tac \\ fs[] \\ rw[]
  \\ IMP_RES_TAC check_clock_IMP
  \\ res_tac \\ fs [] \\ TRY decide_tac
  \\ Cases_on `call_FFI s.ffi ffi_index x` \\ rw [] \\ fs [] \\ rw []);

val evaluate_check_clock = prove(
  ``!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [evaluate_clock,check_clock_thm]);

(* Finally, we remove check_clock from the induction and definition theorems. *)

val clean_term = term_rewrite
     [``check_clock s1 s2 = s1:('a,'ffi) stackSem$state``,
      ``(s.clock < k \/ b2) <=> (s:('a,'ffi) stackSem$state).clock < k:num``]

val set_var_check_clock = prove(
  ``set_var v x (check_clock s1 s2) = check_clock (set_var v x s1) s2``,
  SIMP_TAC std_ss [set_var_def,check_clock_def] \\ SRW_TAC [] []);

val evaluate_ind = curry save_thm "evaluate_ind" let
  val raw_ind = evaluate_ind
  val goal = raw_ind |> concl |> clean_term
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ reverse (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (FIRST_X_ASSUM MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC evaluate_clock \\ SRW_TAC [] []
           \\ RES_TAC \\ IMP_RES_TAC check_clock_alt \\ fs [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC evaluate_clock
    \\ IMP_RES_TAC (GSYM evaluate_clock)
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_thm,GSYM set_var_check_clock])
  in ind end;

val evaluate_def = curry save_thm "evaluate_def" let
  val goal = evaluate_def |> concl |> clean_term
  (* set_goal([],goal) *)
  val def = prove(goal,
    REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [Once evaluate_def] \\ fs []
    \\ Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ IMP_RES_TAC evaluate_check_clock \\ fs []
    \\ Cases_on `find_code dest s.regs s.code` \\ fs []
    \\ Cases_on `evaluate (x,dec_clock s)` \\ fs []
    \\ `check_clock r' s = r'` by ALL_TAC \\ fs []
    \\ IMP_RES_TAC evaluate_check_clock
    \\ fs [check_clock_def,dec_clock_def] \\ SRW_TAC [] []
    \\ fs [theorem "state_component_equality"]
    \\ Cases_on `r'.clock <= s.clock - 1` \\ fs []
    \\ DECIDE_TAC)
  in def end;

(* observational semantics *)

val semantics_def = Define `
  semantics start s =
  let prog = Call NONE (INL start) NONE in
  if ∃k. let res = FST (evaluate (prog, s with clock := k)) in
           res <> SOME TimeOut /\ !w. res <> SOME (Halt w)
  then Fail
  else
    case some res.
      ∃k t r outcome.
        evaluate (prog, s with clock := k) = (SOME r,t) ∧
        (case (t.ffi.final_event,r) of
         | (SOME e,_) => outcome = FFI_outcome e
         | (_,Halt w) => outcome = if w = Word 0w then Success
                                   else Resource_limit_hit
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

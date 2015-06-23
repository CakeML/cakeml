open HolKernel Parse boolLib bossLib;
val _ = new_theory "stackLang";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory sptreeTheory lcsymtacs miscTheory asmTheory word_langTheory;

infix \\ val op \\ = op THEN;

val _ = ParseExtras.tight_equality ();

(* word lang = structured program with words, stack and memory *)

(* --- Syntax of word lang --- *)

val _ = Datatype `
  stack_prog = Skip
             | Inst ('a inst)
             | Get num store_name
             | Set store_name num
             | Call ((stack_prog # num # num) option)
                    (* return var, return-handler code, labels l1,l2*)
                    (num + num) (* target of call *)
                    ((stack_prog # num # num) option)
                    (* handler: exception-handler code, labels l1,l2*)
             | Seq stack_prog stack_prog
             | If cmp num ('a reg_imm) stack_prog stack_prog
             | Alloc num
             | Raise num
             | Return num num
             | Tick
             (* new for this language below *)
             | StackAlloc num
             | StackStore num num
             | StackLoad num num
             | StackFree num `;

(* --- Semantics of word lang --- *)

val _ = Datatype `
  stack_state =
    <| regs  : ('a word_loc) num_map
     ; store   : store_name |-> 'a word_loc
     ; stack   : ('a word_loc) list
     ; stack_shadow : ('a word_loc) list
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     ; permute : num -> num -> num (* sequence of bijective mappings *)
     ; gc_fun  : 'a gc_fun_type
     ; handler : num (*position of current handle frame on stack*)
     ; clock   : num
     ; code    : ('a stack_prog) num_map
     ; output  : string |> `

val mem_store_def = Define `
  mem_store (addr:'a word) (w:'a word_loc) (s:'a stack_state) =
    if addr IN s.mdomain then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE`

val mem_load_def = Define `
  mem_load (addr:'a word) (s:'a stack_state) =
    if addr IN s.mdomain then
      SOME (s.memory addr)
    else NONE`

val word_op_def = Define `
  word_op op (ws:('a word) list) =
    case (op,ws) of
    | (And,ws) => SOME (FOLDR word_and (~0w) ws)
    | (Add,ws) => SOME (FOLDR word_add 0w ws)
    | (Or,ws) => SOME (FOLDR word_or 0w ws)
    | (Xor,ws) => SOME (FOLDR word_xor 0w ws)
    | (Sub,[w1;w2]) => SOME (w1 - w2)
    | _ => NONE`;

val word_sh_def = Define `
  word_sh sh (w:'a word) n =
    if n <> 0 /\ n < dimindex (:'a) then NONE else
      case sh of
      | Lsl => SOME (w << n)
      | Lsr => SOME (w >>> n)
      | Asr => SOME (w >> n)`;

val MEM_IMP_word_exp_size = store_thm("MEM_IMP_word_exp_size",
  ``!xs a. MEM a xs ==> (word_exp_size l a < word_exp1_size l xs)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [word_exp_size_def]
  \\ RES_TAC \\ DECIDE_TAC);

val word_exp_def = tDefine "word_exp" `
  (word_exp s (Const w) = SOME w) /\
  (word_exp s (Var v) =
     case lookup v s.regs of
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
 (WF_REL_TAC `measure (word_exp_size ARB o SND)`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_word_exp_size
  \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
  \\ DECIDE_TAC)

val dec_clock_def = Define `
  dec_clock (s:'a stack_state) = s with clock := s.clock - 1`;

val isResult_def = Define `
  (isResult (Result a b) = T) /\ (isResult _ = F)`;

val isException_def = Define `
  (isException (Exception a b) = T) /\ (isException _ = F)`;

val get_var_def = Define `
  get_var v (s:'a stack_state) = sptree$lookup v s.regs`;

val get_vars_def = Define `
  (get_vars [] s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val list_insert_def = Define `
  (list_insert [] xs t = t) /\
  (list_insert vs [] t = t) /\
  (list_insert (v::vs) (x::xs) t = insert v x (list_insert vs xs t))`

val set_var_def = Define `
  set_var v x (s:'a stack_state) =
    (s with regs := (insert v x s.regs))`;

val set_vars_def = Define `
  set_vars vs xs (s:'a stack_state) =
    (s with regs := (list_insert vs xs s.regs))`;

val set_store_def = Define `
  set_store v x (s:'a stack_state) = (s with store := s.store |+ (v,x))`;

val check_clock_def = Define `
  check_clock (s1:'a stack_state) (s2:'a stack_state) =
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

val fromList2_def = Define `
  fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN) l)`

val EVEN_fromList2_lemma = prove(
  ``!l n t.
      EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
      !x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (n,t) l)) ==> EVEN x``,
  Induct \\ fs [FOLDL] \\ REPEAT STRIP_TAC \\ fs [PULL_FORALL]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`insert n h t`,`x`])
  \\ fs [] \\ SRW_TAC [] [] \\ POP_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ fs [] \\ fs [EVEN_EXISTS]
  \\ Q.EXISTS_TAC `SUC m` \\ DECIDE_TAC);

val EVEN_fromList2 = store_thm("EVEN_fromList2",
  ``!l n. n IN domain (fromList2 l) ==> EVEN n``,
  ASSUME_TAC (EVEN_fromList2_lemma
    |> Q.SPECL [`l`,`0`,`LN`]
    |> SIMP_RULE (srw_ss()) [GSYM fromList2_def]
    |> GEN_ALL) \\ fs []);

val empty_env_def = Define `
  empty_env (s:'a stack_state) = s with <| regs := LN ; stack := [] |>`;

val jump_exc_def = Define `
  jump_exc s =
    if s.handler < LENGTH s.stack then
      case LAST_N (s.handler+1) s.stack of
      | Word _ :: Loc l1 l2 :: Word w :: xs =>
          SOME (s with <| handler := w2n w ; stack := xs |>,l1,l2)
      | _ => NONE
    else NONE`;

val bit_length_def = Define `
  bit_length w = if w = 0w then 0 else bit_length (w >>> 1) + 1`;

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

val read_bitmap_LENGTH = prove(
  ``!xs x w y. (read_bitmap xs = SOME (x,w,y)) ==> LENGTH y < LENGTH xs``,
  Induct \\ fs [read_bitmap_def] \\ Cases_on `h`
  \\ fs [read_bitmap_def]
  \\ REPEAT STRIP_TAC \\ RES_TAC \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ SRW_TAC [] []
  \\ decide_tac);

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

val enc_stack_def = tDefine "enc_stack" `
  (enc_stack [] = SOME []) /\
  (enc_stack ws =
     case read_bitmap ws of
     | NONE => NONE
     | SOME (bs,_,rs) =>
        case filter_bitmap bs rs of
        | NONE => NONE
        | SOME (ts,ws') =>
            case enc_stack ws' of
            | NONE => NONE
            | SOME rs => SOME (ts :: rs))`
 (WF_REL_TAC `measure LENGTH` \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC read_bitmap_LENGTH
  \\ IMP_RES_TAC filter_bitmap_LENGTH
  \\ fs [] \\ decide_tac)

val dec_stack_def = Define `
  (dec_stack [] [] = SOME []) /\
  (dec_stack (ts::xs) ws =
     case read_bitmap ws of
     | NONE => NONE
     | SOME (bs,w1,ws') =>
        case map_bitmap bs ts ws' of
        | NONE => NONE
        | SOME (ws1,ws2) =>
           case dec_stack xs ws2 of
           | NONE => NONE
           | SOME ws3 => SOME (w1 ++ ws1 ++ ws3))`

val sGC_def = Define `  (* wGC runs the garbage collector algorithm *)
  sGC s =
    case enc_stack s.stack of
    | NONE => NONE
    | SOME wl_list =>
      case s.gc_fun (wl_list, s.memory, s.mdomain, s.store) of
      | NONE => NONE
      | SOME (wl,m,st) =>
       (case dec_stack wl s.stack of
        | NONE => NONE
        | SOME stack =>
            SOME (s with <| stack := stack
                          ; store := st
                          ; memory := m |>))`

val has_space_def = Define `
  has_space wl (s:'a stack_state) =
    case (wl, FLOOKUP s.store NextFree, FLOOKUP s.store LastFree) of
    | (Word w, SOME (Word n), SOME (Word l)) => SOME (w2n w <= w2n (l - n))
    | _ => NONE`

val sAlloc_def = Define `
  sAlloc (w:'a word) (s:'a stack_state) =
    (* perform garbage collection *)
      case sGC (set_store AllocSize (Word w) s) of
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
                        (SOME NotEnoughSpace,empty_env s)))`

val word_assign_def = Define `
  word_assign reg exp s =
    case word_exp s exp of
     | NONE => NONE
     | SOME w => SOME (set_var reg (Word w) s)`;

val wInst_def = Define `
  wInst i (s:'a stack_state) =
    case i of
    | Skip => SOME s
    | Const reg w => word_assign reg (Const w) s
    | Arith (Binop bop r1 r2 ri) =>
        word_assign r1
          (Op bop [Var r2; case ri of Reg r3 => Var r3
                                    | Imm w => Const w]) s
    | Arith (Shift sh r1 r2 n) =>
        word_assign r1
          (Shift sh (Var r2) (Nat n)) s
    | Mem Load r (Addr a w) =>
        word_assign r (Load (Op Add [Var a; Const w])) s
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
     case lookup r regs of
       SOME (Loc loc 0) => lookup loc code
     | other => NONE)`

val sEval_def = tDefine "sEval" `
  (sEval (Skip:'a stack_prog,s) = (NONE,s:'a stack_state)) /\
  (sEval (Alloc n,s) =
     case get_var n s of
     | SOME (Word w) => sAlloc w s
     | _ => (SOME Error,s)) /\
  (sEval (Inst i,s) =
     case wInst i s of
     | SOME s1 => (NONE, s1)
     | NONE => (SOME Error, s)) /\
  (sEval (Get v name,s) =
     case FLOOKUP s.store name of
     | SOME x => (NONE, set_var v x s)
     | NONE => (SOME Error, s)) /\
  (sEval (Set name v,s) =
     case get_var v s of
     | SOME w => (NONE, set_store name w s)
     | NONE => (SOME Error, s)) /\
  (sEval (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,empty_env s)
                    else (NONE,dec_clock s)) /\
  (sEval (Seq c1 c2,s) =
     let (res,s1) = sEval (c1,s) in
       if res = NONE then sEval (c2,check_clock s1 s) else (res,s1)) /\
  (sEval (Return n m,s) =
     case (get_var n s ,get_var m s) of
     | (SOME x,SOME y) => (SOME (Result x y),empty_env s)
     | _ => (SOME Error,s)) /\
  (sEval (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME w =>
       (case jump_exc s of
        | NONE => (SOME Error,s)
        | SOME (s,l1,l2) => (SOME (Exception (Loc l1 l2) w)),s)) /\
  (sEval (If cmp r1 ri c1 c2,s) =
    (case (get_var r1 s,get_var_imm ri s)of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y then sEval (c1,s)
                          else sEval (c2,s)
    | _ => (SOME Error,s))) /\
  (sEval (Call ret dest handler,s) =
     case find_code dest s.regs s.code of
     | NONE => (SOME Error,s)
     | SOME prog =>
     case ret of
     (* tail call *)
     | NONE =>
        if handler <> NONE then (SOME Error,s) else
        if s.clock = 0 then (SOME TimeOut,empty_env s) else
          (case sEval (prog,dec_clock s) of
           | (NONE,s) => (SOME Error,s)
           | (SOME res,s) => (SOME res,s))
     (* returning call, returns into var n *)
     | SOME (ret_handler,l1,l2) =>
        if s.clock = 0 then (SOME TimeOut,empty_env s) else
          (case sEval (prog, dec_clock s) of
           | (SOME (Result x y),s2) =>
               if x <> Loc l1 l2 then (SOME Error,s2) else
                 (case sEval(ret_handler,check_clock s2 s) of
                  | (NONE,s) => (NONE,s)
                  | (_,s) => (SOME Error,s))
           | (SOME (Exception x y),s2) =>
               (case handler of (* if handler is present, then handle exc *)
                | NONE => (SOME (Exception x y),s2)
                | SOME (h,l1,l2) =>
                   if x <> Loc l1 l2 then (SOME Error,s2) else
                     sEval (h, check_clock s2 s))
           | (NONE,s) => (SOME Error,s)
           | res => res)) /\
  (sEval (StackAlloc n,s) =
     if LENGTH s.stack_shadow < n then (SOME NotEnoughSpace,empty_env s) else
       (NONE, s with <| stack := TAKE n s.stack_shadow ++ s.stack ;
                        stack_shadow := DROP n s.stack_shadow |>)) /\
  (sEval (StackFree n,s) =
     if LENGTH s.stack < n then (SOME Error,empty_env s) else
       (NONE, s with <| stack := DROP n s.stack ;
                        stack_shadow := TAKE n s.stack ++ s.stack_shadow |>)) /\
  (sEval (StackLoad r n,s) =
     if LENGTH s.stack < n then (SOME Error,empty_env s) else
       (NONE, set_var r (EL n s.stack) s)) /\
  (sEval (StackStore r n,s) =
     if LENGTH s.stack < n then (SOME Error,empty_env s) else
       case get_var r s of
       | NONE => (SOME Error,empty_env s)
       | SOME v => (NONE, s with stack := LUPDATE v n s.stack))`
 (WF_REL_TAC `(inv_image (measure I LEX measure (stack_prog_size (K 0)))
                            (\(xs,(s:'a stack_state)). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ fs[empty_env_def,dec_clock_def] \\ DECIDE_TAC)


(* We prove that the clock never increases. *)

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val sGC_clock = store_thm("sGC_clock",
  ``!s1 s2. (sGC s1 = SOME s2) ==> s2.clock <= s1.clock``,
  fs [sGC_def,LET_DEF] \\ SRW_TAC [] []
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs [])
  \\ SRW_TAC [] [] \\ fs []);

val sAlloc_clock = store_thm("sAlloc_clock",
  ``!xs s1 vs s2. (sAlloc x s1 = (vs,s2)) ==> s2.clock <= s1.clock``,
  SIMP_TAC std_ss [sAlloc_def] \\ REPEAT STRIP_TAC
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ Q.ABBREV_TAC `s3 = set_store AllocSize (Word x) s1`
  \\ `s3.clock=s1.clock` by Q.UNABBREV_TAC`s3`>>fs[set_store_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ IMP_RES_TAC sGC_clock \\ fs []
  \\ UNABBREV_ALL_TAC \\ fs []
  \\ Cases_on `x'''` \\ fs [] \\ SRW_TAC [] []
  \\ EVAL_TAC \\ decide_tac);

val wInst_clock = prove(
  ``wInst i s = SOME s2 ==> s2.clock <= s.clock``,
  Cases_on `i` \\ fs [wInst_def,word_assign_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ SRW_TAC [] [set_var_def] \\ fs []
  \\ fs [mem_store_def] \\ SRW_TAC [] []);

val sEval_clock = store_thm("sEval_clock",
  ``!xs s1 vs s2. (sEval (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "sEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [sEval_def]
  \\ FULL_SIMP_TAC std_ss [cut_state_opt_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def,empty_env_def]
  \\ IMP_RES_TAC wInst_clock
  \\ IMP_RES_TAC sAlloc_clock
  \\ fs [set_var_def,set_store_def,dec_clock_def,jump_exc_def]
  \\ Cases_on `sEval (c1,s)` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ NTAC 5 ((BasicProvers.EVERY_CASE_TAC)
             \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC check_clock_IMP
  \\ RES_TAC \\ DECIDE_TAC);

val sEval_check_clock = prove(
  ``!xs s1 vs s2. (sEval (xs,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [sEval_clock,check_clock_thm]);

(* Finally, we remove check_clock from the induction and definition theorems. *)

fun sub f tm = f tm handle HOL_ERR _ =>
  let val (v,t) = dest_abs tm in mk_abs (v, sub f t) end
  handle HOL_ERR _ =>
  let val (t1,t2) = dest_comb tm in mk_comb (sub f t1, sub f t2) end
  handle HOL_ERR _ => tm

val remove_check_clock = sub (fn tm =>
  if can (match_term ``check_clock s1 (s2:'a stack_state)``) tm
  then tm |> rator |> rand else fail())

val remove_disj = sub (fn tm => if is_disj tm then tm |> rator |> rand else fail())

val set_var_check_clock = prove(
  ``set_var v x (check_clock s1 s2) = check_clock (set_var v x s1) s2``,
  SIMP_TAC std_ss [set_var_def,check_clock_def] \\ SRW_TAC [] []);

val sEval_ind = curry save_thm "sEval_ind" let
  val raw_ind = fetch "-" "sEval_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (FIRST_X_ASSUM MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC sEval_clock \\ SRW_TAC [] []
           \\ RES_TAC \\ IMP_RES_TAC check_clock_alt \\ fs [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC sEval_clock
    \\ IMP_RES_TAC (GSYM sEval_clock)
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_thm,GSYM set_var_check_clock])
  in ind end;

val sEval_def = curry save_thm "sEval_def" let
  val goal = sEval_def |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [Once sEval_def] \\ fs []
    \\ Cases_on `sEval (c1,s)` \\ fs [LET_DEF]
    \\ IMP_RES_TAC sEval_check_clock \\ fs []
    \\ Cases_on `find_code dest s.regs s.code` \\ fs []
    \\ Cases_on `sEval (x,dec_clock s)` \\ fs []
    \\ `check_clock r' s = r'` by ALL_TAC \\ fs []
    \\ IMP_RES_TAC sEval_check_clock
    \\ fs [check_clock_def,dec_clock_def] \\ SRW_TAC [] []
    \\ fs [theorem "stack_state_component_equality"]
    \\ Cases_on `r'.clock <= s.clock - 1` \\ fs []
    \\ DECIDE_TAC)
  in def end;

(* clean up *)

val _ = map delete_binding ["sEval_AUX_def", "sEval_primitive_def"];

val _ = export_theory();

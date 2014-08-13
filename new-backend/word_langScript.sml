open HolKernel Parse boolLib bossLib; val _ = new_theory "word_lang";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open wordsTheory sptreeTheory lcsymtacs bvpTheory;

infix \\ val op \\ = op THEN;

(* word lang = structured program with words, stack and memory *)

(* --- Syntax of word lang --- *)

val _ = Datatype `
  store_name =
    NextFree | LastFree | CurrHeap | OtherHeap | AllocSize`

val _ = Datatype `
  num_exp = Nat num
          | Add num_exp num_exp
          | Sub num_exp num_exp
          | Div2 num_exp
          | Exp2 num_exp
          | WordWidth ('a word)`

val _ = Datatype `
  word_op = AND | ADD | OR | SUB | MUL | XOR`

val _ = Datatype `
  word_sh = LSL | LSR | ASR`

val _ = Datatype `
  word_exp = Const ('a word)
           | Var num
           | Get store_name
           | Load word_exp
           | Op word_op (word_exp list)
           | Shift word_sh word_exp ('a num_exp)`

val _ = Datatype `
  word_prog = Skip
            | Move ((num # num) list)
            | Assign num ('a word_exp)
            | Set store_name ('a word_exp)
            | Store ('a word_exp) num
            | Call ((num # num_set) option) (* return var, cut-set *)
                               (num option) (* target of call *)
                                 (num list) (* arguments *)
                 ((num # word_prog) option) (* handler: varname, handler code *)
            | Seq word_prog word_prog
            | If word_prog num word_prog word_prog
            | Alloc num num_set
            | Raise num
            | Return num
            | Tick `;

(* --- Semantics of word lang --- *)

val _ = Datatype `
  word_loc = Word ('a word) | Loc num num `;

val _ = Datatype `
  word_st = StackFrame ((num # ('a word_loc)) list) (num option) `;

val _ = type_abbrev("gc_fun_type",
  ``: (('a word_loc list) list) # (('a word) -> ('a word_loc)) # ('a word) set #
      (store_name |-> 'a word_loc) ->
      ((('a word_loc list) list) # (('a word) -> ('a word_loc)) #
       (store_name |-> 'a word_loc)) option``);

val _ = Datatype `
  word_state =
    <| locals  : ('a word_loc) num_map
     ; store   : store_name |-> 'a word_loc
     ; stack   : ('a word_st) list
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     ; permute : num -> num -> num (* sequence of bijective mappings *)
     ; gc_fun  : 'a gc_fun_type
     ; handler : num
     ; clock   : num
     ; code    : (num # ('a word_prog) # num) num_map
     ; output  : string |> `

val _ = Datatype `
  word_result = Result 'a
              | Exception ('w word_loc)
              | TimeOut
              | NotEnoughSpace
              | Error `

val gc_bij_ok_def = Define `
  gc_bij_ok (seq':num->num->num) = !n. BIJ (seq' n) UNIV UNIV`;

val num_exp_def = Define `
  (num_exp (Nat n) = n) /\
  (num_exp (Add x y) = num_exp x + num_exp y) /\
  (num_exp (Sub x y) = num_exp x - num_exp y) /\
  (num_exp (Div2 x) = num_exp x DIV 2) /\
  (num_exp (Exp2 x) = 2 ** (num_exp x)) /\
  (num_exp (WordWidth (w:'a word)) = dimindex (:'a))`

val is_word_def = Define `
  (is_word (Word w) = T) /\
  (is_word _ = F)`

val get_word_def = Define `
  get_word (Word w) = w`

val mem_store_def = Define `
  mem_store (addr:'a word) (w:'a word_loc) (s:'a word_state) =
    if addr IN s.mdomain then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE`

val mem_load_def = Define `
  mem_load (addr:'a word) (s:'a word_state) =
    if addr IN s.mdomain then
      SOME (s.memory addr)
    else NONE`

val word_op_def = Define `
  word_op op (ws:('a word) list) =
    case (op,ws) of
    | (AND,ws) => SOME (FOLDR word_and (~0w) ws)
    | (ADD,ws) => SOME (FOLDR word_add 0w ws)
    | (OR,ws) => SOME (FOLDR word_or 0w ws)
    | (XOR,ws) => SOME (FOLDR word_xor 0w ws)
    | (SUB,[w1;w2]) => SOME (w1 - w2)
    | (MUL,[w1;w2]) => SOME (w1 * w2)
    | _ => NONE`;

val word_sh_def = Define `
  word_sh sh (w:'a word) n =
    if n <> 0 /\ n < dimindex (:'a) then NONE else
      case sh of
      | LSL => SOME (w << n)
      | LSR => SOME (w >>> n)
      | ASR => SOME (w >> n)`;

val MEM_IMP_word_exp_size = prove(
  ``!xs a. MEM a xs ==> (word_exp_size l a < word_exp1_size l xs)``,
  Induct \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [fetch "-" "word_exp_size_def"]
  \\ RES_TAC \\ DECIDE_TAC);

val word_exp_def = tDefine "word_exp" `
  (word_exp s (Const w) = SOME w) /\
  (word_exp s (Var v) =
     case lookup v s.locals of
     | SOME (Word w) => SOME w
     | _ => NONE) /\
  (word_exp s (Get name) =
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
  dec_clock (s:'a word_state) = s with clock := s.clock - 1`;

val isResult_def = Define `
  (isResult (Result r) = T) /\ (isResult _ = F)`;

val isException_def = Define `
  (isException (Exception r) = T) /\ (isException _ = F)`;

val get_var_def = Define `
  get_var v (s:'a word_state) = sptree$lookup v s.locals`;

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
  set_var v x (s:'a word_state) =
    (s with locals := (insert v x s.locals))`;

val set_vars_def = Define `
  set_vars vs xs (s:'a word_state) =
    (s with locals := (list_insert vs xs s.locals))`;

val set_store_def = Define `
  set_store v x (s:'a word_state) = (s with store := s.store |+ (v,x))`;

val check_clock_def = Define `
  check_clock (s1:'a word_state) (s2:'a word_state) =
    if s1.clock <= s2.clock then s1 else s1 with clock := s2.clock`;

val check_clock_thm = prove(
  ``(check_clock s1 s2).clock <= s2.clock /\
    (s1.clock <= s2.clock ==> (check_clock s1 s2 = s1))``,
  SRW_TAC [] [check_clock_def])

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

val call_env_def = Define `
  call_env args (s:'a word_state) =
    s with <| locals := fromList2 args |>`;

val env_to_list_def = Define `
  env_to_list env (bij_seq:num->num->num) =
    let renamer = bij_seq 0 in
    let permute = (\n. bij_seq (n + 1)) in
    let l = toAList env in
    let l = QSORT (\x y. renamer (FST x) <= renamer (FST y)) l in
      (l,permute)`

val push_env_def = Define `
  push_env env b s =
    let (l,permute) = env_to_list env s.permute in
    let handler = if b then SOME s.handler else NONE in
      s with <| stack := StackFrame l handler :: s.stack
              ; permute := permute
              ; handler := if b then LENGTH s.stack else s.handler |>`;

val fromAList_def = Define `
  (fromAList [] = LN) /\
  (fromAList ((x,y)::xs) = insert x y (fromAList xs))`;

val pop_env_def = Define `
  pop_env s =
    case s.stack of
    | (StackFrame e NONE::xs) =>
         SOME (s with <| locals := fromAList e ; stack := xs |>)
    | (StackFrame e (SOME n)::xs) =>
         SOME (s with <| locals := fromAList e ; stack := xs ; handler := n |>)
    | _ => NONE`;

val jump_exc_def = Define `
  jump_exc s =
    if s.handler < LENGTH s.stack then
      case LAST_N (s.handler+1) s.stack of
      | StackFrame e (SOME n) :: xs =>
          SOME (s with <| handler := n ; locals := fromAList e ; stack := xs |>)
      | _ => NONE
    else NONE`;

val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (inter env name_set)
    else NONE`

val cut_state_def = Define `
  cut_state names s =
    case cut_env names s.locals of
    | NONE => NONE
    | SOME env => SOME (s with locals := env)`;

val cut_state_opt_def = Define `
  cut_state_opt names s =
    case names of
    | NONE => SOME s
    | SOME names => cut_state names s`;

val pop_env_clock = prove(
  ``(pop_env s = SOME s1) ==> (s1.clock = s.clock)``,
  fs [pop_env_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
  \\ SRW_TAC [] [] \\ fs []);

val push_env_clock = prove(
  ``(push_env env b s).clock = s.clock``,
  Cases_on `b` \\ fs [push_env_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ fs []
  \\ SRW_TAC [] [] \\ fs []);

val find_code_def = Define `
  (find_code (SOME p) args code =
     case sptree$lookup p code of
     | NONE => NONE
     | SOME (_,exp,arity) => if LENGTH args = arity then SOME (args,exp)
                                                    else NONE) /\
  (find_code NONE args code =
     if args = [] then NONE else
       case LAST args of
       | Loc loc 0 =>
           (case lookup loc code of
            | NONE => NONE
            | SOME (_,exp,arity) => if LENGTH args = arity + 1
                                    then SOME (FRONT args,exp)
                                    else NONE)
       | other => NONE)`

val enc_stack_def = Define `
  (enc_stack [] = []) /\
  (enc_stack ((StackFrame l handler :: st)) =
     (MAP SND l) :: enc_stack st)`;

val dec_stack_def = Define `
  (dec_stack [] [] = SOME []) /\
  (dec_stack (ws::xs) ((StackFrame l handler :: st)) =
     if LENGTH ws <> LENGTH l then NONE else
       case dec_stack xs st of
       | NONE => NONE
       | SOME s => SOME (StackFrame (ZIP (MAP FST l,ws)) handler :: s))`

val wGC_def = Define `  (* wGC runs the garbage collector algorithm *)
  wGC s =
    let wl_list = enc_stack s.stack in
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
  has_space wl s =
    case (wl, FLOOKUP s.store NextFree, FLOOKUP s.store LastFree) of
    | (Word w, SOME (Word n), SOME (Word l)) => SOME (w2n w <= w2n (l - n))
    | _ => NONE`

val wAlloc_def = Define `
  wAlloc w names s =
    (* prune local names *)
    case cut_env names s.locals of
    | NONE => (SOME Error,s)
    | SOME env =>
     (* perform garbage collection *)
     (case wGC (push_env env F (set_store AllocSize (Word w) s)) of
      | NONE => (SOME Error,s)
      | SOME s1 =>
       (* restore local variables *)
       (case pop_env s of
        | NONE => (SOME Error, s)
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
                        (SOME NotEnoughSpace,s1)))))`

val wEval_def = tDefine "wEval" `
  (wEval (Skip:'a word_prog,s) = (NONE,s:'a word_state)) /\
  (wEval (Alloc n names,s) =
     case get_var n s of
     | SOME (Word w) => wAlloc w names s
     | _ => (SOME Error,s)) /\
  (wEval (Move moves,s) =
     if ALL_DISTINCT (MAP FST moves) then
       case get_vars (MAP SND moves) s of
       | NONE => (SOME Error,s)
       | SOME vs => (NONE, set_vars (MAP FST moves) vs s)
     else (SOME Error,s)) /\
  (wEval (Assign v exp,s) =
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var v (Word w) s)) /\
  (wEval (Set v exp,s) =
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_store v (Word w) s)) /\
  (wEval (Store exp v,s) =
     case (word_exp s exp, get_var v s) of
     | (SOME addr, SOME w) =>
         (case mem_store addr w s of
          | SOME s1 => (NONE, s1)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (wEval (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := [])
                    else (NONE,dec_clock s)) /\
  (wEval (Seq c1 c2,s) =
     let (res,s1) = wEval (c1,s) in
       if res = NONE then wEval (c2,check_clock s1 s) else (res,s1)) /\
  (wEval (Return n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME x => (SOME (Result x),call_env [] s)) /\
  (wEval (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME w =>
       (case jump_exc s of
        | NONE => (SOME Error,s)
        | SOME s => (SOME (Exception w),s))) /\
  (wEval (If g n c1 c2,s) =
     case wEval (g,s) of
     | (NONE,s1) =>
         (case get_var n s1 of
          | SOME (Word x) => if x = 0w
                             then wEval (c2,check_clock s1 s)
                             else wEval (c1,check_clock s1 s)
          | _ => (SOME Error,s1))
     | res => res) /\
  (wEval (Call ret dest args handler,s) =
     if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := []) else
       case get_vars args s of
       | NONE => (SOME Error,s)
       | SOME xs =>
         (case find_code dest xs s.code of
          | NONE => (SOME Error,s)
          | SOME (args1,prog) =>
            (case ret of
             | NONE (* tail call *) =>
               if handler = NONE then
                 (case wEval (prog, call_env args1 (dec_clock s)) of
                  | (NONE,s) => (SOME Error,s)
                  | (SOME res,s) => (SOME res,s))
               else (SOME Error,s)
             | SOME (n,names) (* returning call, returns into var n *) =>
               (case cut_env names s.locals of
                | NONE => (SOME Error,s)
                | SOME env =>
               (case wEval (prog, call_env args1
                       (push_env env (IS_SOME handler) (dec_clock s))) of
                | (SOME (Result x),s2) =>
                   (case pop_env s2 of
                    | NONE => (SOME Error,s2)
                    | SOME s1 =>
                        (if domain s1.locals = domain env
                         then (NONE, set_var n x s1)
                         else (SOME Error,s1)))
                | (SOME (Exception x),s2) =>
                   (case handler of (* if handler is present, then handle exc *)
                    | NONE => (SOME (Exception x),s2)
                    | SOME (n,h) =>
                        (if domain s2.locals = domain env
                         then wEval (h, set_var n x (check_clock s2 s))
                         else (SOME Error,s2)))
                | (NONE,s) => (SOME Error,s)
                | res => res)))))`
 (WF_REL_TAC `(inv_image (measure I LEX measure (word_prog_size (K 0)))
                            (\(xs,(s:'a word_state)). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
  \\ FULL_SIMP_TAC (srw_ss()) [push_env_clock]
  \\ IMP_RES_TAC pop_env_clock \\ fs [] \\ SRW_TAC [] []
  \\ Cases_on `s2.clock < s.clock` \\ fs [] \\ DECIDE_TAC)

(* We prove that the clock never increases. *)

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val wGC_clock = store_thm("wGC_clock",
  ``!s1 s2. (wGC s1 = SOME s2) ==> s2.clock <= s1.clock``,
  fs [wGC_def,LET_DEF] \\ SRW_TAC [] []
  \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs [])
  \\ SRW_TAC [] [] \\ fs []);

val wAlloc_clock = store_thm("wAlloc_clock",
  ``!xs s1 vs s2. (wAlloc x names s1 = (vs,s2)) ==> s2.clock <= s1.clock``,
  SIMP_TAC std_ss [wAlloc_def] \\ REPEAT STRIP_TAC
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] []
  \\ IMP_RES_TAC pop_env_clock \\ IMP_RES_TAC wGC_clock
  \\ fs [push_env_clock,set_store_def] \\ SRW_TAC [] []
  \\ Cases_on `env_to_list s1.locals s1.permute` \\ fs [LET_DEF]);

val pop_env_clock = prove(
  ``(pop_env s = SOME t) ==> (s.clock = t.clock)``,
  fs [pop_env_def] \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ SRW_TAC [] [] \\ fs []);

val wEval_clock = store_thm("wEval_clock",
  ``!xs s1 vs s2. (wEval (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "wEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [wEval_def]
  \\ FULL_SIMP_TAC std_ss [cut_state_opt_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def,call_env_def]
  \\ fs [call_env_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC wAlloc_clock
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def,set_var_def,
       add_space_def,jump_exc_def,get_var_def,push_env_clock,set_vars_def,
       call_env_def,cut_state_def,set_store_def,mem_store_def]
  \\ REV_FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ IMP_RES_TAC pop_env_clock
  \\ TRY DECIDE_TAC
  \\ SRW_TAC [] []
  \\ Cases_on `wEval (c1,s)` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ NTAC 5 (REPEAT (BasicProvers.FULL_CASE_TAC)
             \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC check_clock_IMP
  \\ RES_TAC \\ DECIDE_TAC);

val wEval_check_clock = prove(
  ``!xs s1 vs s2. (wEval (xs,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [wEval_clock,check_clock_thm]);

(* Finally, we remove check_clock from the induction and definition theorems. *)

fun sub f tm = f tm handle HOL_ERR _ =>
  let val (v,t) = dest_abs tm in mk_abs (v, sub f t) end
  handle HOL_ERR _ =>
  let val (t1,t2) = dest_comb tm in mk_comb (sub f t1, sub f t2) end
  handle HOL_ERR _ => tm

val remove_check_clock = sub (fn tm =>
  if can (match_term ``check_clock s1 (s2:'a word_state)``) tm
  then tm |> rator |> rand else fail())

val remove_disj = sub (fn tm => if is_disj tm then tm |> rator |> rand else fail())

val set_var_check_clock = prove(
  ``set_var v x (check_clock s1 s2) = check_clock (set_var v x s1) s2``,
  SIMP_TAC std_ss [set_var_def,check_clock_def] \\ SRW_TAC [] []);

val wEval_ind = save_thm("wEval_ind",let
  val raw_ind = fetch "-" "wEval_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (FIRST_X_ASSUM MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC wEval_clock \\ SRW_TAC [] []
           \\ `s2.clock <= s.clock` by
            (fs [call_env_def,dec_clock_def,push_env_clock]
             \\ IMP_RES_TAC pop_env_clock \\ DECIDE_TAC)
           \\ `s2 = check_clock s2 s` by fs [check_clock_def]
           \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
           \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC wEval_clock
    \\ IMP_RES_TAC (GSYM wEval_clock)
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_thm,GSYM set_var_check_clock])
  val lemma = EVAL ``bool_to_val F = bool_to_val T``
  in ind |> SIMP_RULE std_ss [lemma] end);

val wEval_def = save_thm("wEval_def",let
  val tm = fetch "-" "wEval_AUX_def"
           |> concl |> rand |> dest_abs |> snd |> rand |> rand
  val tm = ``^tm wEval (x,s)``
  val rhs = SIMP_CONV std_ss [EVAL ``pair_CASE (x,y) f``] tm |> concl |> rand
  val goal = ``!x s. wEval (x,s) = ^rhs`` |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    recInduct wEval_ind
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ TRY (SIMP_TAC std_ss [Once wEval_def] \\ NO_TAC)
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [Once wEval_def]
    \\ Cases_on `wEval (c1,s)`
    \\ Cases_on `wEval (p,s)`
    \\ Cases_on `wEval (g,s)`
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    \\ IMP_RES_TAC wEval_check_clock \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT BasicProvers.CASE_TAC
    \\ SRW_TAC [] [] \\ IMP_RES_TAC wEval_check_clock
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_def]
    \\ fs [call_env_def,dec_clock_def,push_env_clock]
    \\ SRW_TAC [] []
    \\ IMP_RES_TAC wEval_clock
    \\ fs [call_env_def,dec_clock_def,push_env_clock]
    \\ `F` by DECIDE_TAC)
  val new_def = wEval_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* clean up *)

val _ = map delete_binding ["wEval_AUX_def", "wEval_primitive_def"];

(*

  BVP --> word_lang compiler correctness thm:

    pEval (prog,s1) = (res,s2) ==>
    state_rel s1 t1 ==>
      wEval (pCompile prog,t1) = (res1,t2) /\
      state_rel s2 t2 /\ res_rel res res1

  word_lang --> word_lang compiler correctness thm:

    !wprog t1 t2 d1 res c.
      ?p n.
        state_rel p t1 d1 /\
        colouring_ok wprog c /\ res <> SOME Error /\
        wEval (wprog,t1) = (res,t2) ==>
        ?d2. wEval (apply_colour c wprog,d1) = (res,d2) /\
             state_rel (\i. p (i+n)) t2 d2

    where state_rel is roughly

    state_rel p t1 d1 =
      ?dp dl dc.
        (d1 = t1 with <| permute := dp; locals := dl; code := dc |>) /\
        t1.permute = p /\
        !k arity code.
          lookup k t1.code = SOME (arity,code)
          ?c. colouring_ok code c /\
              lookup k d1.code = SOME (arity,apply_colour c code)

  word_lang --> stack_lang compiler correctness thm:

    wEval (wprog,t1 with permute := K I) = (res,t2) ==>
    sEval (wCompile wprog,r1) = (res1,r2)

*)

val _ = export_theory();

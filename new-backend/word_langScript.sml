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
           | Op word_op (word_exp list)
           | Shift word_sh word_exp ('a num_exp)`

val _ = Datatype `
  word_prog = Skip
            | Move num num
            | Assign num ('a word_exp)
            | Set store_name ('a word_exp)
            | Store ('a word_exp) num
            | Call ((num # num_set) option) (num option) (num list)
            | Seq word_prog word_prog
            | If word_prog num word_prog word_prog
            | GC ('a word_exp) num_set
            | Raise num
            | Return num
            | Handle num_set word_prog num num num_set word_prog
            | Tick `;

(* --- Semantics of word lang --- *)

val _ = Datatype `
  word_loc = Word ('a word) | Loc num `;

val _ = Datatype `
  word_st = Env (('a word_loc) num_map) | Exc num `;

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
     ; gc_bij  : num -> num -> num (* sequence of bijective mappings *)
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
  gc_bij_ok (seq:num->num->num) = !n. BIJ (seq n) UNIV UNIV`;

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

val word_op_def = Define `
  word_op op (ws:('a word) list) =
    case (op,ws) of
    | (ADD,ws) => SOME (FOLDR word_add 0w ws)
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

val set_var_def = Define `
  set_var v x (s:'a word_state) = (s with locals := (insert v x s.locals))`;

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

val call_env_def = Define `
  call_env args (s:'a word_state) =
    s with <| locals := fromList args |>`;

val push_env_def = Define `
  push_env env (s:'a word_state) =
    s with <| stack := Env env :: s.stack |>`;

val pop_env_def = Define `
  pop_env (s:'a word_state) =
    case s.stack of
    | (Env e::xs) => SOME (s with <| locals := e ; stack := xs |>)
    | _ => NONE`;

val jump_exc_def = Define `
  jump_exc (s:'a word_state) =
    if s.handler < LENGTH s.stack then
      case LAST_N (s.handler + 1) s.stack of
      | Exc n :: Env e :: xs =>
          SOME (s with <| handler := n ; locals := e ; stack := xs |>)
      | _ => NONE
    else NONE`;

val pop_exc_def = Define `
  pop_exc (s:'a word_state) =
    case s.stack of
    | (Exc n :: Env e :: rest) =>
        SOME (s with <| stack := rest ; handler := n ; locals := e |>)
    | _ => NONE `;

val push_exc_def = Define `
  push_exc env1 env2 (s:'a word_state) =
    s with <| locals := env1
            ; stack := Exc s.handler :: Env env2 :: s.stack
            ; handler := LENGTH s.stack + 1 |> `;

val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (inter env name_set)
    else NONE`

val cut_state_def = Define `
  cut_state names (s:'a word_state) =
    case cut_env names s.locals of
    | NONE => NONE
    | SOME env => SOME (s with locals := env)`;

val cut_state_opt_def = Define `
  cut_state_opt names (s:'a word_state) =
    case names of
    | NONE => SOME s
    | SOME names => cut_state names s`;

val mem_store_def = Define `
  mem_store (addr:'a word) (w:'a word_loc) (s:'a word_state) =
    if addr IN s.mdomain then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE`

val find_code_def = Define `
  (find_code (SOME p) args code =
     case sptree$lookup p code of
     | NONE => NONE
     | SOME (_,exp,arity) => if LENGTH args = arity then SOME (args,exp)
                                                    else NONE) /\
  (find_code NONE args code =
     if args = [] then NONE else
       case LAST args of
       | Loc loc =>
           (case lookup loc code of
            | NONE => NONE
            | SOME (_,exp,arity) => if LENGTH args = arity + 1
                                    then SOME (FRONT args,exp)
                                    else NONE)
       | other => NONE)`

val inv_fun_def = Define `
  inv_fun f x = @y. f y = x`;

val enc_stack_def = Define `
  (enc_stack (bij:num->num->num) [] = []) /\
  (enc_stack bij ((Exc n :: st)) =
     [] :: enc_stack (\n. bij (n+1)) st) /\
  (enc_stack bij ((Env env :: st)) =
     let l = MAP (\(i,x). (bij 0 i,x)) (toAList env) in
     let l = QSORT (\(i,x) (j,y). j <= i) l in
       (MAP SND l) :: enc_stack (\n. bij (n+1)) st)`;

val dec_stack_def = Define `
  (dec_stack (bij:num->num->num) [] [] = SOME []) /\
  (dec_stack bij (ws::xs) ((Exc n :: st)) =
     case dec_stack (\n. bij (n+1)) xs st of
     | NONE => NONE
     | SOME s => SOME (Exc n :: s)) /\
  (dec_stack bij (ws::xs) ((Env env :: st)) =
     let l = MAP (\(i,x). (bij 0 i,x)) (toAList env) in
     let l = QSORT (\(i,x) (j,y). j <= i) l in
     let l = MAP FST l in
     let l1 = ZIP (l, ws) in
     let l2 = MAP (\(i,x). (inv_fun (bij 0) i,x)) l1 in
     let env = FOLDL (\f (k,v). insert k v f) LN l2 in
       if LENGTH l <> LENGTH ws then NONE else
         case dec_stack (\n. bij (n+1)) xs st of
         | NONE => NONE
         | SOME s => SOME (Env env :: s))`;

val wGC_def = Define `
  wGC s =
    let wl_list = enc_stack s.gc_bij s.stack in
      case s.gc_fun (wl_list, s.memory, s.mdomain, s.store) of
      | NONE => NONE
      | SOME (wl,m,st) =>
       (case dec_stack s.gc_bij wl s.stack of
        | NONE => NONE
        | SOME stack =>
            SOME (s with <| stack := stack
                          ; store := st
                          ; memory := m
                          ; gc_bij := (\n. s.gc_bij (n + LENGTH s.stack)) |>))`

val has_space_def = Define `
  has_space wl s =
    case (wl, FLOOKUP s.store NextFree, FLOOKUP s.store LastFree) of
    | (Word w, SOME (Word n), SOME (Word l)) => SOME (w2n w <= w2n (l - n))
    | _ => NONE`

val wAlloc_def = Define `
  wAlloc w names s =
    case cut_env names s.locals of
    | NONE => (SOME Error,s)
    | SOME env =>
     (case wGC (push_env env (set_store AllocSize (Word w) s)) of
      | NONE => (SOME Error,s)
      | SOME s1 =>
       (case FLOOKUP s.store AllocSize of
        | NONE => (SOME Error, s)
        | SOME w =>
         (case has_space w s of
          | NONE => (SOME Error, s)
          | SOME T => (NONE,s)
          | SOME F =>
           (case pop_env s1 of
            | NONE => (SOME Error,s1)
            | SOME s2 => (NONE,s2)))))`

val wEval_def = tDefine "wEval" `
  (wEval (Skip:'a word_prog,s) = (NONE,s:'a word_state)) /\
  (wEval (GC exp names,s) =
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w =>
      (case has_space (Word w) s of
       | NONE => (SOME Error, s)
       | SOME T => (NONE,s)
       | SOME F => wAlloc w names s)) /\
  (wEval (Move dest src,s) =
     case get_var src s of
     | NONE => (SOME Error,s)
     | SOME v => (NONE, set_var dest v s)) /\
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
  (wEval (Handle ns1 c1 v n ns2 c2,s) =
     case cut_env ns1 s.locals of
     | NONE => (SOME Error,s)
     | SOME env1 =>
        (case cut_env ns2 s.locals of
        | NONE => (SOME Error,s)
        | SOME env2 =>
           (case wEval (c1,push_exc env1 env2 s) of
           | (SOME (Exception v),s1) =>
                wEval (c2, check_clock (set_var n v s1) s)
           | (SOME (Result _),s1) => (SOME Error,s1)
           | (NONE,s1) =>
               (case (get_var v s1, pop_exc s1) of
                | (SOME x, SOME s2) => (NONE, set_var v x s2)
                | _ => (SOME Error,s1))
           | res => res))) /\
  (wEval (Call ret dest args,s) =
     if s.clock = 0 then (SOME TimeOut, call_env [] s with stack := []) else
       case get_vars args s of
       | NONE => (SOME Error,s)
       | SOME xs =>
         (case find_code dest xs s.code of
          | NONE => (SOME Error,s)
          | SOME (args1,prog) =>
            (case ret of
             | NONE (* tail call *) =>
               (case wEval (prog, call_env args1 (dec_clock s)) of
                | (NONE,s) => (SOME Error,s)
                | (SOME res,s) => (SOME res,s))
             | SOME (n,names) (* returning call, returns into var n *) =>
               (case cut_env names s.locals of
                | NONE => (SOME Error,s)
                | SOME env =>
               (case wEval (prog, call_env args1 (push_env env (dec_clock s))) of
                | (SOME (Result x),s) =>
                   (case pop_env s of
                    | NONE => (SOME Error,s)
                    | SOME s1 => (NONE, set_var n x s1))
                | (NONE,s1) => (SOME Error,s1)
                | res => res)))))`
 (WF_REL_TAC `(inv_image (measure I LEX measure (word_prog_size (K 0)))
                            (\(xs,(s:'a word_state)). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

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
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ IMP_RES_TAC wGC_clock
  \\ fs [push_env_def,set_store_def,pop_env_def] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ SRW_TAC [] [] \\ fs []
  \\ SRW_TAC [] []);

val wEval_clock = store_thm("wEval_clock",
  ``!xs s1 vs s2. (wEval (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "wEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [wEval_def]
  \\ FULL_SIMP_TAC std_ss [cut_state_opt_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC wAlloc_clock
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def,set_var_def,push_env_def,pop_env_def,
       add_space_def,jump_exc_def,get_var_def,pop_exc_def,push_exc_def,
       call_env_def,cut_state_def,set_store_def,mem_store_def]
  \\ TRY DECIDE_TAC
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
  if can (match_term ``check_clock s1 (s2:bvp_state)``) tm
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
           \\ IMP_RES_TAC wEval_clock)
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC wEval_clock
    \\ IMP_RES_TAC (GSYM wEval_clock)
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_thm,GSYM set_var_check_clock,
         push_exc_def])
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
    \\ Cases_on `q`
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM set_var_check_clock]
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_def,push_exc_def]
    \\ NTAC 3 BasicProvers.CASE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC wEval_check_clock \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q`
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM set_var_check_clock,GSYM check_clock_def]
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_def,push_exc_def])
  val new_def = wEval_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* clean up *)

val _ = map delete_binding ["wEval_AUX_def", "wEval_primitive_def"];

val _ = export_theory();

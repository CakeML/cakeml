open preamble wordLangTheory;

val _ = new_theory"wordSem";

val _ = Datatype `
  word_loc = Word ('a word) | Loc num num `;

val _ = Datatype `
  stack_frame = StackFrame ((num # ('a word_loc)) list) ((num # num # num)option) `;

val _ = type_abbrev("gc_fun_type",
  ``: (('a word_loc list) list) # (('a word) -> ('a word_loc)) # ('a word) set #
      (store_name |-> 'a word_loc) ->
      ((('a word_loc list) list) # (('a word) -> ('a word_loc)) #
       (store_name |-> 'a word_loc)) option``);

val gc_bij_ok_def = Define `
  gc_bij_ok (seq':num->num->num) = !n. BIJ (seq' n) UNIV UNIV`;

val _ = Datatype `
  state =
    <| locals  : ('a word_loc) num_map
     ; store   : store_name |-> 'a word_loc
     ; stack   : ('a stack_frame) list
     ; memory  : 'a word -> 'a word_loc
     ; mdomain : ('a word) set
     ; permute : num -> num -> num (* sequence of bijective mappings *)
     ; gc_fun  : 'a gc_fun_type
     ; handler : num (*position of current handle frame on stack*)
     ; clock   : num
     ; code    : (num # ('a wordLang$prog) # num) num_map
     ; io      : io_trace |> `

val state_component_equality = theorem"state_component_equality";

val _ = Datatype `
  result = Result ('w word_loc) ('w word_loc)
         | Exception ('w word_loc) ('w word_loc)
         | TimeOut
         | FFIError
         | NotEnoughSpace
         | Error `

val isResult_def = Define `
  (isResult (Result a b) = T) /\ (isResult _ = F)`;

val isException_def = Define `
  (isException (Exception a b) = T) /\ (isException _ = F)`;

val dec_clock_def = Define `
  dec_clock (s:'a wordSem$state) = s with clock := s.clock - 1`;

val check_clock_def = Define `
  check_clock (s1:'a wordSem$state) (s2:'a wordSem$state) =
    if s1.clock <= s2.clock then s1 else s1 with clock := s2.clock`;

val check_clock_thm = prove(
  ``(check_clock s1 s2).clock <= s2.clock /\
    (s1.clock <= s2.clock ==> (check_clock s1 s2 = s1))``,
  SRW_TAC [] [check_clock_def])

val check_clock_lemma = prove(
  ``b ==> ((check_clock s1 s).clock < s.clock \/
          ((check_clock s1 s).clock = s.clock) /\ b)``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

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
  mem_store (addr:'a word) (w:'a word_loc) (s:'a wordSem$state) =
    if addr IN s.mdomain then
      SOME (s with memory := (addr =+ w) s.memory)
    else NONE`

val mem_load_def = Define `
  mem_load (addr:'a word) (s:'a wordSem$state) =
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

val word_exp_def = tDefine "word_exp" `
  (word_exp s (Const w) = SOME w) /\
  (word_exp s (Var v) =
     case lookup v s.locals of
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
   \\ REPEAT STRIP_TAC \\ IMP_RES_TAC MEM_IMP_exp_size
   \\ TRY (FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `ARB`))
   \\ DECIDE_TAC)

val get_var_def = Define `
  get_var v (s:'a wordSem$state) = sptree$lookup v s.locals`;

val get_vars_def = Define `
  (get_vars [] s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val set_var_def = Define `
  set_var v x (s:'a wordSem$state) =
    (s with locals := (insert v x s.locals))`;

val set_vars_def = Define `
  set_vars vs xs (s:'a wordSem$state) =
    (s with locals := (alist_insert vs xs s.locals))`;

val set_store_def = Define `
  set_store v x (s:'a wordSem$state) = (s with store := s.store |+ (v,x))`;

val call_env_def = Define `
  call_env args (s:'a wordSem$state) =
    s with <| locals := fromList2 args |>`;

val list_rearrange_def = Define `
  list_rearrange mover xs =
    (* if the mover function is actually a permutation,
     i.e. it bijects (or injects) the keys 0...n-1 to 0...n-1
     use it *)
    if (BIJ mover (count (LENGTH xs)) (count (LENGTH xs))) then
      GENLIST (\i. EL (mover i) xs) (LENGTH xs)
    else (* if it isn't well-formed, just pretend it is I *)
      xs`

(* Compare on keys, if keys match (never), then compare on
   the word_loc vals. Treat Words as < Locs *)
val key_val_compare_def = Define `
  key_val_compare x y =
    let (a:num,b) = x in
    let (a':num,b') = y in
      (a > a') \/
      (a = a' /\
        case b of
          Word x => (case b' of Word y => x <= y | _ => T)
        | Loc a b => case b' of Loc a' b' => (a>a') \/ (a=a' /\ b>=b') | _ => F)`

(*
EVAL ``key_val_compare (1,Loc 3 4) (1,Loc 1 2)``
*)

val env_to_list_def = Define `
  env_to_list env (bij_seq:num->num->num) =
    let mover = bij_seq 0 in
    let permute = (\n. bij_seq (n + 1)) in
    let l = toAList env in
    let l = QSORT key_val_compare l in
    let l = list_rearrange mover l in
      (l,permute)`

val push_env_def = Define `
  (push_env env NONE s =
    let (l,permute) = env_to_list env s.permute in
      s with <| stack := StackFrame l NONE :: s.stack
              ; permute := permute|>) ∧
  (push_env env (SOME (w:num,h:'a wordLang$prog,l1,l2)) s =
    let (l,permute) = env_to_list env s.permute in
      let handler = SOME (s.handler,l1,l2) in
      s with <| stack := StackFrame l handler :: s.stack
              ; permute := permute
              ; handler := LENGTH s.stack|>)`;

val pop_env_def = Define `
  pop_env s =
    case s.stack of
    | (StackFrame e NONE::xs) =>
         SOME (s with <| locals := fromAList e ; stack := xs |>)
    | (StackFrame e (SOME (n,_,_))::xs) =>
         SOME (s with <| locals := fromAList e ; stack := xs ; handler := n |>)
    | _ => NONE`;

val push_env_clock = Q.prove(
  `(wordSem$push_env env b s).clock = s.clock`,
  Cases_on `b` \\ TRY(PairCases_on`x`) \\ fs [push_env_def]
  \\ every_case_tac \\ fs []
  \\ SRW_TAC [] [] \\ fs []);

val pop_env_clock = Q.prove(
  `(wordSem$pop_env s = SOME s1) ==> (s1.clock = s.clock)`,
  fs [pop_env_def]
  \\ every_case_tac \\ fs []
  \\ SRW_TAC [] [] \\ fs []);

val jump_exc_def = Define `
  jump_exc s =
    if s.handler < LENGTH s.stack then
      case LAST_N (s.handler+1) s.stack of
      | StackFrame e (SOME (n,l1,l2)) :: xs =>
          SOME (s with <| handler := n ; locals := fromAList e ; stack := xs |>,l1,l2)
      | _ => NONE
    else NONE`;

(* TODO: reuse this from bvpSem? *)
val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (inter env name_set)
    else NONE`
(* -- *)

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
       | SOME s => SOME (StackFrame (ZIP (MAP FST l,ws)) handler :: s)) /\
  (dec_stack _ _ = NONE)`

val gc_def = Define `  (* gc runs the garbage collector algorithm *)
  gc s =
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

val alloc_def = Define `
  alloc (w:'a word) names s =
    (* prune local names *)
    case cut_env names s.locals of
    | NONE => (SOME Error,s)
    | SOME env =>
     (* perform garbage collection *)
     (case gc (push_env env (NONE:(num # 'a wordLang$prog # num # num) option) (set_store AllocSize (Word w) s)) of
      | NONE => (SOME Error,s)
      | SOME s =>
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
                        (SOME NotEnoughSpace,call_env [] s with stack:= [])))))`

val assign_def = Define `
  assign reg exp s =
    case word_exp s exp of
     | NONE => NONE
     | SOME w => SOME (set_var reg (Word w) s)`;

val inst_def = Define `
  inst i s =
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
  (get_var_imm ((Reg n):'a reg_imm) s = get_var n s) ∧
  (get_var_imm (Imm w) s = SOME(Word w))`

val evaluate_def = tDefine "evaluate" `
  (evaluate (Skip:'a wordLang$prog,s) = (NONE,s:'a wordSem$state)) /\
  (evaluate (Alloc n names,s) =
     case get_var n s of
     | SOME (Word w) => alloc w names s
     | _ => (SOME Error,s)) /\
  (evaluate (Move pri moves,s) =
     if ALL_DISTINCT (MAP FST moves) then
       case get_vars (MAP SND moves) s of
       | NONE => (SOME Error,s)
       | SOME vs => (NONE, set_vars (MAP FST moves) vs s)
     else (SOME Error,s)) /\
  (evaluate (Inst i,s) =
     case inst i s of
     | SOME s1 => (NONE, s1)
     | NONE => (SOME Error, s)) /\
  (evaluate (Assign v exp,s) =
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_var v (Word w) s)) /\
  (evaluate (Get v name,s) =
     case FLOOKUP s.store name of
     | NONE => (SOME Error, s)
     | SOME x => (NONE, set_var v x s)) /\
  (evaluate (Set v exp,s) =
     case word_exp s exp of
     | NONE => (SOME Error, s)
     | SOME w => (NONE, set_store v (Word w) s)) /\
  (evaluate (Store exp v,s) =
     case (word_exp s exp, get_var v s) of
     | (SOME a, SOME w) =>
         (case mem_store a w s of
          | SOME s1 => (NONE, s1)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := [])
                    else (NONE,dec_clock s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = evaluate (c1,s) in
       if res = NONE then evaluate (c2,check_clock s1 s) else (res,s1)) /\
  (evaluate (Return n m,s) =
     case (get_var n s ,get_var m s) of
     | (SOME x,SOME y) => (SOME (Result x y),call_env [] s)
     | _ => (SOME Error,s)) /\
  (evaluate (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME w =>
       (case jump_exc s of
        | NONE => (SOME Error,s)
        | SOME (s,l1,l2) => (SOME (Exception (Loc l1 l2) w)),s)) /\
  (evaluate (If cmp r1 ri c1 c2,s) =
    (case (get_var r1 s,get_var_imm ri s)of
    | SOME (Word x),SOME (Word y) =>
      if word_cmp cmp x y then evaluate (c1,s)
                          else evaluate (c2,s)
    | _ => (SOME Error,s))) /\
  (evaluate (Call ret dest args handler,s) =
     case get_vars args s of
     | NONE => (SOME Error,s)
     | SOME xs =>
       (case find_code dest xs s.code of
	  | NONE => (SOME Error,s)
	  | SOME (args1,prog) =>
	    (case ret of
	     | NONE (* tail call *) =>
	       if handler = NONE then
           if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := []) else
           (case evaluate (prog, call_env args1 (dec_clock s)) of
            | (NONE,s) => (SOME Error,s)
            | (SOME res,s) => (SOME res,s))
               else (SOME Error,s)
	     | SOME (n,names,ret_handler,l1,l2) (* returning call, returns into var n *) =>
	       (case cut_env names s.locals of
		| NONE => (SOME Error,s)
		| SOME env =>
	       if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := []) else
	       (case evaluate (prog, call_env ((Loc l1 l2)::args1)
		       (push_env env handler (dec_clock s))) of
		| (SOME (Result x y),s2) =>
      if x ≠ Loc l1 l2 then (SOME Error,s2)
      else
		   (case pop_env s2 of
		    | NONE => (SOME Error,s2)
		    | SOME s1 =>
			(if domain s1.locals = domain env
			 then
			   (*Value restriction on the return handler (makes it easier to reason about)
			     Don't really need it to do fancy things.
           Keep y in register 2
           *)
			   case evaluate(ret_handler,set_var n y (check_clock s1 s)) of
			   | (NONE,s) => (NONE,s)
			   | (_,s) => (SOME Error,s)
			 else (SOME Error,s1)))
		| (SOME (Exception x y),s2) =>
		   (case handler of (* if handler is present, then handle exc *)
		    | NONE => (SOME (Exception x y),s2)
		    | SOME (n,h,l1,l2) =>
        if x ≠ Loc l1 l2 then (SOME Error,s2)
        else
          (if domain s2.locals = domain env
           then evaluate (h, set_var n y (check_clock s2 s))
           else (SOME Error,s2)))
        | (NONE,s) => (SOME Error,s)
		| res => res))))) `
  (WF_REL_TAC `(inv_image (measure I LEX measure (prog_size (K 0)))
                             (\(xs,(s:'a wordSem$state)). (s.clock,xs)))`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
   \\ TRY
     (fs[push_env_clock,call_env_def,dec_clock_def]\\DECIDE_TAC)
   \\ EVAL_TAC
    \\ Cases_on `s.clock <= s1.clock`
  \\ FULL_SIMP_TAC (srw_ss()) [push_env_clock]
   \\ IMP_RES_TAC pop_env_clock \\ fs [] \\ SRW_TAC [] []
   \\ Cases_on `s2.clock < s.clock` \\ fs [] \\ DECIDE_TAC)

val evaluate_ind = theorem"evaluate_ind";

(* We prove that the clock never increases. *)

val gc_clock = store_thm("gc_clock",
  ``!s1 s2. (gc s1 = SOME s2) ==> s2.clock <= s1.clock``,
  fs [gc_def,LET_DEF] \\ SRW_TAC [] []
  \\ every_case_tac >> fs[]
  \\ SRW_TAC [] [] \\ fs []);

val alloc_clock = store_thm("alloc_clock",
  ``!xs s1 vs s2. (alloc x names s1 = (vs,s2)) ==> s2.clock <= s1.clock``,
  SIMP_TAC std_ss [alloc_def] \\ REPEAT STRIP_TAC
  \\ every_case_tac \\ SRW_TAC [] [] \\ fs []
  \\ every_case_tac \\ SRW_TAC [] [] \\ fs []
  \\ Q.ABBREV_TAC `s3 = set_store AllocSize (Word x) s1`
  \\ `s3.clock=s1.clock` by Q.UNABBREV_TAC`s3`>>fs[set_store_def]
  \\ every_case_tac \\ SRW_TAC [] [] \\ fs []
  >- (IMP_RES_TAC gc_clock \\
     fs[push_env_def,LET_THM,env_to_list_def] \\
     unabbrev_all_tac>>fs[])
  \\ every_case_tac \\ SRW_TAC [] [] \\ fs []
  \\ POP_ASSUM MP_TAC \\ SRW_TAC [] []
  \\ IMP_RES_TAC pop_env_clock \\ IMP_RES_TAC gc_clock
  \\ fs [push_env_clock,set_store_def] \\ SRW_TAC [] []
  \\ Cases_on `env_to_list s1.locals s1.permute` \\ fs [LET_DEF]\\rfs[]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs[call_env_def,state_component_equality]);

val inst_clock = prove(
  ``inst i s = SOME s2 ==> s2.clock <= s.clock``,
  Cases_on `i` \\ fs [inst_def,assign_def]
  \\ every_case_tac
  \\ SRW_TAC [] [set_var_def] \\ fs []
  \\ fs [mem_store_def] \\ SRW_TAC [] []);

val evaluate_clock = Q.store_thm("evaluate_clock",
  `!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock`,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss [cut_state_opt_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def,call_env_def]
  \\ IMP_RES_TAC inst_clock
  \\ fs [call_env_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC alloc_clock
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def,set_var_def,
       jump_exc_def,get_var_def,push_env_clock,set_vars_def,
       call_env_def,cut_state_def,set_store_def,mem_store_def]
  \\ REV_FULL_SIMP_TAC std_ss [] \\ RES_TAC
  \\ IMP_RES_TAC pop_env_clock
  \\ TRY DECIDE_TAC
  \\ SRW_TAC [] []
  \\ Cases_on `evaluate (c1,s)` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ NTAC 5 ((BasicProvers.EVERY_CASE_TAC)
             \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC check_clock_IMP
  \\ RES_TAC \\ DECIDE_TAC);

val evaluate_check_clock = prove(
  ``!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [evaluate_clock,check_clock_thm]);

(* Finally, we remove check_clock from the induction and definition theorems. *)

fun sub f tm = f tm handle HOL_ERR _ =>
  let val (v,t) = dest_abs tm in mk_abs (v, sub f t) end
  handle HOL_ERR _ =>
  let val (t1,t2) = dest_comb tm in mk_comb (sub f t1, sub f t2) end
  handle HOL_ERR _ => tm

val remove_check_clock = sub (fn tm =>
  if can (match_term ``check_clock s1 (s2:'a wordSem$state)``) tm
  then tm |> rator |> rand else fail())

val remove_disj = sub (fn tm => if is_disj tm then tm |> rator |> rand else fail())

val set_var_check_clock = prove(
  ``set_var v x (check_clock s1 s2) = check_clock (set_var v x s1) s2``,
  SIMP_TAC std_ss [set_var_def,check_clock_def] \\ SRW_TAC [] []);

val evaluate_ind = save_thm("evaluate_ind",let
  val raw_ind = evaluate_ind
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (FIRST_X_ASSUM MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC evaluate_clock \\ SRW_TAC [] []
           \\ TRY (`s2.clock <= s.clock` by
            (fs [call_env_def,dec_clock_def,push_env_clock]
             \\ IMP_RES_TAC pop_env_clock \\ DECIDE_TAC)
           \\ `s2 = check_clock s2 s` by fs [check_clock_def])
           \\ TRY (`s1.clock <= s.clock` by
             (fs [call_env_def,dec_clock_def,push_env_clock]
             \\ IMP_RES_TAC pop_env_clock \\ DECIDE_TAC)
           \\ `s1 = check_clock s1 s` by fs[check_clock_def])
           \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
           \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC evaluate_clock
    \\ IMP_RES_TAC (GSYM evaluate_clock)
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_thm,GSYM set_var_check_clock])
  in ind |> SIMP_RULE std_ss [] end);

val evaluate_def = save_thm("evaluate_def",let
  val tm = definition"evaluate_AUX_def"
           |> concl |> rand |> dest_abs |> snd |> rand |> rand
  val tm = ``^tm evaluate (x,s)``
  val rhs = SIMP_CONV std_ss [EVAL ``pair_CASE (x,y) f``] tm |> concl |> rand
  val goal = ``!x s. evaluate (x,s) = ^rhs`` |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    recInduct evaluate_ind
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ TRY (SIMP_TAC std_ss [Once evaluate_def] \\ NO_TAC)
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [Once evaluate_def]
    \\ Cases_on `evaluate (c1,s)`
    \\ Cases_on `evaluate (p,s)`
    \\ Cases_on `evaluate (g,s)`
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    \\ IMP_RES_TAC evaluate_check_clock \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT BasicProvers.CASE_TAC
    \\ SRW_TAC [] [] \\ IMP_RES_TAC evaluate_check_clock
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_def]
    \\ fs [pop_env_def,call_env_def,dec_clock_def,push_env_clock]
    \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_clock
    \\ fs [call_env_def,dec_clock_def,push_env_clock]
    \\ `x''.clock <= s.clock` by
         (BasicProvers.EVERY_CASE_TAC>>fs[state_component_equality]>>
         `F` by DECIDE_TAC) \\ fs[]
    \\ TRY (`x''.clock = r'''''.clock` by
       (BasicProvers.EVERY_CASE_TAC>>fs[state_component_equality]))
    \\ TRY (`x''.clock = r''''''.clock` by
       (BasicProvers.EVERY_CASE_TAC>>fs[state_component_equality]))
    \\ `F` by DECIDE_TAC)
  val new_def = evaluate_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

(*

  BVP --> word_lang compiler correctness thm:

    pEval (prog,s1) = (res,s2) ==>
    state_rel s1 t1 ==>
      evaluate (pCompile prog,t1) = (res1,t2) /\
      state_rel s2 t2 /\ res_rel res res1

  word_lang --> word_lang compiler correctness thm:

    !wprog t1 t2 d1 res c.
      ?p n.
        state_rel p t1 d1 /\
        colouring_ok wprog c /\ res <> SOME Error /\
        evaluate (wprog,t1) = (res,t2) ==>
        ?d2. evaluate (apply_colour c wprog,d1) = (res,d2) /\
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

    evaluate (wprog,t1 with permute := K I) = (res,t2) ==>
    sEval (wCompile wprog,r1) = (res1,r2)

*)
val _ = export_theory();

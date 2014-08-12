open HolKernel Parse boolLib bossLib; val _ = new_theory "bvp";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory bvlTheory sptreeTheory lcsymtacs bviTheory;

infix \\ val op \\ = op THEN;

(* BVP = bytecode-value program *)

(* BVP is the next step from BVL: (1) BVP is an imperative version of
   BVL, i.e. operations update state; (2) there is a new state
   component (called space) and an explicit MakeSpace operation that
   increases space. Space is consumed by Ref and Cons. *)

(* The idea is that the MakeSpace calls can be moved around and lumped
   together. This optimisation reduces the number of calls to the
   allocator and, thus, simplifies to program.  The MakeSpace function
   can, unfortunately, not be moved across function calls or bignum
   operations, which can internally call the allocator. *)

(* The MakeSpace command has an optional variable name list. If this
   list is provided, i.e. SOME var_names, then only these variables
   can survive the execution of the MakeSpace command. The idea is
   that one generates MakeSpace X NONE when compiling into BVP. Then
   optimisations move around and combine MakeSpace commands. Then
   liveness analysis annotates each MakeSpace command with a SOME. The
   translation from BVP into more concete forms must implement a GC
   that only looks at the variables in the SOME annotations. *)


(* --- Syntax of BVP --- *)

val _ = Datatype `
  bvp_prog = Skip
           | Move num num
           | Call ((num # num_set) option) (* return var, cut-set *)
                              (num option) (* target of call *)
                                (num list) (* arguments *)
                 ((num # bvp_prog) option) (* handler: varname, handler code *)
           | Assign num bvl_op (num list) (num_set option)
           | Seq bvp_prog bvp_prog
           | If bvp_prog num bvp_prog bvp_prog
           | MakeSpace num num_set
           | Raise num
           | Return num
           | Tick `;

(* --- Semantics of BVP --- *)

val _ = Datatype `
  bvp_st = Env (bc_value num_map)
         | Exc (bc_value num_map) num`;

val _ = Datatype `
  bvp_state =
    <| globals : (bc_value option) list
     ; locals  : bc_value num_map
     ; stack   : bvp_st list
     ; handler : num
     ; refs    : num |-> ref_value
     ; clock   : num
     ; code    : (num # bvp_prog) num_map
     ; output  : string
     ; space   : num |> `

val bvp_to_bvi_def = Define `
  (bvp_to_bvi:bvp_state->bvi_state) s =
    <| globals := s.globals
     ; refs := s.refs
     ; clock := s.clock
     ; code := spt_set (K ARB) s.code
     ; output := s.output |>`;

val bvi_to_bvp_def = Define `
  (bvi_to_bvp:bvi_state->bvp_state->bvp_state) s t =
    t with <| globals := s.globals
            ; refs := s.refs
            ; clock := s.clock
            ; output := s.output |>`;

val consume_space_def = Define `
  consume_space k s =
    if s.space < k then NONE else SOME (s with space := s.space - k)`;

val op_space_reset_def = Define `
  (op_space_reset Add = T) /\
  (op_space_reset Sub = T) /\
  (op_space_reset _ = F)`;

val op_space_req_def = Define `
  (op_space_req (Cons k) = (k+1)) /\
  (op_space_req Ref = 2) /\
  (op_space_req x = 0)`;

val pEvalOpSpace_def = Define `
  pEvalOpSpace op s =
    if op_space_reset op then SOME (s with space := 0)
    else if op_space_req op = 0 then SOME s
         else consume_space (op_space_req op) s`;

val pEvalOp_def = Define `
  pEvalOp op vs (s:bvp_state) =
    case pEvalOpSpace op s of
    | NONE => NONE
    | SOME s1 => (case iEvalOp op vs (bvp_to_bvi s1) of
                  | NONE => NONE
                  | SOME (v,t) => SOME (v, bvi_to_bvp t s1))`

val dec_clock_def = Define `
  dec_clock (s:bvp_state) = s with clock := s.clock - 1`;

val isResult_def = Define `
  (isResult (Result r) = T) /\ (isResult _ = F)`;

val isException_def = Define `
  (isException (Exception r) = T) /\ (isException _ = F)`;

val add_space_def = Define `
  add_space s k = s with space := s.space + k`;

val get_var_def = Define `
  get_var v s = lookup v s.locals`;

val get_vars_def = Define `
  (get_vars [] s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val set_var_def = Define `
  set_var v x s = (s with locals := (insert v x s.locals))`;

val check_clock_def = Define `
  check_clock (s1:bvp_state) (s2:bvp_state) =
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
  call_env args s =
    s with <| locals := fromList args |>`;

val push_env_def = Define `
  (push_env env F s = s with <| stack := Env env :: s.stack |>) /\
  (push_env env T s = s with <| stack := Exc env s.handler :: s.stack
                              ; handler := LENGTH s.stack |>)`;

val pop_env_def = Define `
  pop_env s =
    case s.stack of
    | (Env e::xs) => SOME (s with <| locals := e ; stack := xs |>)
    | (Exc e n::xs) => SOME (s with <| locals := e; stack := xs ; handler := n |>)
    | _ => NONE`;

val LAST_N_def = Define `
  LAST_N n xs = REVERSE (TAKE n (REVERSE xs))`;

val jump_exc_def = Define `
  jump_exc s =
    if s.handler < LENGTH s.stack then
      case LAST_N (s.handler+1) s.stack of
      | Exc e n :: xs =>
          SOME (s with <| handler := n ; locals := e ; stack := xs |>)
      | _ => NONE
    else NONE`;

val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (mk_wf (inter env name_set))
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

val list_to_num_set_def = Define `
  (list_to_num_set [] = LN) /\
  (list_to_num_set (n::ns) = insert n () (list_to_num_set ns))`;

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

val pEval_def = tDefine "pEval" `
  (pEval (Skip,s) = (NONE,s:bvp_state)) /\
  (pEval (Move dest src,s) =
     case get_var src s of
     | NONE => (SOME Error,s)
     | SOME v => (NONE, set_var dest v s)) /\
  (pEval (Assign dest op args names_opt,s) =
     if op_space_reset op /\ IS_NONE names_opt then (SOME Error,s) else
     case cut_state_opt names_opt s of
     | NONE => (SOME Error,s)
     | SOME s =>
       (case get_vars args s of
        | NONE => (SOME Error,s)
        | SOME xs => (case pEvalOp op xs s of
                      | NONE => (SOME Error,s)
                      | SOME (v,s) =>
                        (NONE, set_var dest v s)))) /\
  (pEval (Tick,s) =
     if s.clock = 0 then (SOME TimeOut,call_env [] s with stack := [])
                    else (NONE,dec_clock s)) /\
  (pEval (MakeSpace k names,s) =
     case cut_env names s.locals of
     | NONE => (SOME Error,s)
     | SOME env => (NONE,add_space s k with locals := env)) /\
  (pEval (Raise n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME x =>
       (case jump_exc s of
        | NONE => (SOME Error,s)
        | SOME s => (SOME (Exception x),s))) /\
  (pEval (Return n,s) =
     case get_var n s of
     | NONE => (SOME Error,s)
     | SOME x => (SOME (Result x),call_env [] s)) /\
  (pEval (Seq c1 c2,s) =
     let (res,s1) = pEval (c1,s) in
       if res = NONE then pEval (c2,check_clock s1 s) else (res,s1)) /\
  (pEval (If g n c1 c2,s) =
     case pEval (g,s) of
     | (NONE,s1) =>
         (case get_var n s1 of
          | NONE => (SOME Error,s1)
          | SOME x => if x = bool_to_val T then pEval (c1,check_clock s1 s) else
                      if x = bool_to_val F then pEval (c2,check_clock s1 s) else
                        (SOME Error,s1))
     | res => res) /\
  (pEval (Call ret dest args handler,s) =
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
                 (case pEval (prog, call_env args1 (dec_clock s)) of
                  | (NONE,s) => (SOME Error,s)
                  | (SOME res,s) => (SOME res,s))
               else (SOME Error,s)
             | SOME (n,names) (* returning call, returns into var n *) =>
               (case cut_env names s.locals of
                | NONE => (SOME Error,s)
                | SOME env =>
               (case pEval (prog, call_env args1 (push_env env (IS_SOME handler) (dec_clock s))) of
                | (SOME (Result x),s2) =>
                   (case pop_env s2 of
                    | NONE => (SOME Error,s2)
                    | SOME s1 => (NONE, set_var n x s1))
                | (SOME (Exception x),s2) =>
                   (case handler of (* if handler is present, then handle exc *)
                    | NONE => (SOME (Exception x),s2)
                    | SOME (n,h) => pEval (h, set_var n x (check_clock s2 s)))
                | (NONE,s) => (SOME Error,s)
                | res => res)))))`
 (WF_REL_TAC `(inv_image (measure I LEX measure bvp_prog_size)
                            (\(xs,s). (s.clock,xs)))`
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

val pEvalOp_clock = store_thm("pEvalOp_clock",
  ``(pEvalOp op args s1 = SOME (res,s2)) ==> s2.clock <= s1.clock``,
  SIMP_TAC std_ss [pEvalOp_def,pEvalOpSpace_def,consume_space_def]
  \\ SRW_TAC [] [] \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
  \\ IMP_RES_TAC iEvalOp_const \\ fs []
  \\ fs [bvp_to_bvi_def,bvi_to_bvp_def] \\ SRW_TAC [] []);

val pEval_clock = store_thm("pEval_clock",
  ``!xs s1 vs s2. (pEval (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "pEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [pEval_def]
  \\ FULL_SIMP_TAC std_ss [cut_state_opt_def] \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC pEvalOp_clock
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def,set_var_def,push_env_def,pop_env_def,
       add_space_def,jump_exc_def,get_var_def,
       call_env_def,cut_state_def,push_env_clock]
  \\ TRY DECIDE_TAC
  \\ Cases_on `pEval (c1,s)` \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
  \\ NTAC 5 (REPEAT (BasicProvers.FULL_CASE_TAC)
             \\ FULL_SIMP_TAC (srw_ss()) [] \\ SRW_TAC [] [])
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ IMP_RES_TAC check_clock_IMP
  \\ RES_TAC \\ DECIDE_TAC);

val pEval_check_clock = prove(
  ``!xs s1 vs s2. (pEval (xs,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [pEval_clock,check_clock_thm]);

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

val pEval_ind = save_thm("pEval_ind",let
  val raw_ind = fetch "-" "pEval_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (FIRST_X_ASSUM MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC pEval_clock \\ SRW_TAC [] []
           \\ `s2.clock <= s.clock` by
            (fs [call_env_def,push_env_def,dec_clock_def]
             \\ IMP_RES_TAC pop_env_clock \\ DECIDE_TAC)
           \\ `s2 = check_clock s2 s` by fs [check_clock_def]
           \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
           \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC pEval_clock
    \\ IMP_RES_TAC (GSYM pEval_clock)
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_thm,GSYM set_var_check_clock])
  val lemma = EVAL ``bool_to_val F = bool_to_val T``
  in ind |> SIMP_RULE std_ss [lemma] end);

val pEval_def = save_thm("pEval_def",let
  val tm = fetch "-" "pEval_AUX_def"
           |> concl |> rand |> dest_abs |> snd |> rand |> rand
  val tm = ``^tm pEval (x,s)``
  val rhs = SIMP_CONV std_ss [EVAL ``pair_CASE (x,y) f``] tm |> concl |> rand
  val goal = ``!x s. pEval (x,s) = ^rhs`` |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    recInduct pEval_ind
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ TRY (SIMP_TAC std_ss [Once pEval_def] \\ NO_TAC)
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [Once pEval_def]
    \\ Cases_on `pEval (c1,s)`
    \\ Cases_on `pEval (p,s)`
    \\ Cases_on `pEval (g,s)`
    \\ FULL_SIMP_TAC (srw_ss()) [LET_DEF]
    \\ IMP_RES_TAC pEval_check_clock \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q`
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM set_var_check_clock]
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_def]
    \\ NTAC 3 BasicProvers.CASE_TAC
    \\ FULL_SIMP_TAC (srw_ss()) []
    \\ IMP_RES_TAC pEval_check_clock \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q`
    \\ FULL_SIMP_TAC (srw_ss()) [GSYM set_var_check_clock,GSYM check_clock_def]
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_def]
    \\ Cases_on `s.clock = 0` \\ fs []
    \\ REPEAT BasicProvers.CASE_TAC
    \\ IMP_RES_TAC pop_env_clock
    \\ IMP_RES_TAC pEval_clock \\ FULL_SIMP_TAC std_ss []
    \\ fs [call_env_def,push_env_def,dec_clock_def]
    \\ `F` by DECIDE_TAC)
  val new_def = pEval_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* clean up *)

val _ = map delete_binding ["pEval_AUX_def", "pEval_primitive_def"];

val _ = export_theory();

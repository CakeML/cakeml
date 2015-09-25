open preamble bvpTheory bvi_to_bvpTheory;
local open bvlSemTheory bvlPropsTheory bviSemTheory in end;

val _ = new_theory"bvpSem";

val _ = Datatype `
  stack = Env (bvlSem$v num_map)
        | Exc (bvlSem$v num_map) num`;

val _ = Datatype `
  state =
    <| locals  : bvlSem$v num_map
     ; stack   : stack list
     ; global  : bvlSem$v
     ; handler : num
     ; refs    : num |-> bvlSem$v ref
     ; clock   : num
     ; code    : (num # bvp$prog) num_map
     ; io      : io_trace
     ; space   : num |> `

val dec_clock_def = Define `
  dec_clock (s:bvpSem$state) = s with clock := s.clock - 1`;

val LESS_EQ_dec_clock = prove(
  ``r.clock <= (dec_clock s).clock ==> r.clock <= s.clock``,
  SRW_TAC [] [dec_clock_def] \\ DECIDE_TAC);

val bvp_to_bvi_def = Define `
  (bvp_to_bvi:bvpSem$state->bviSem$state) s =
    <| refs := s.refs
     ; clock := s.clock
     ; code := map (K ARB) s.code
     ; io := s.io |>`;

val bvi_to_bvp_def = Define `
  (bvi_to_bvp:bviSem$state->bvpSem$state->bvpSem$state) s t =
    t with <| refs := s.refs
            ; clock := s.clock
            ; io := s.io |>`;

val add_space_def = Define `
  add_space s k = s with space := s.space + k`;

val consume_space_def = Define `
  consume_space k s =
    if s.space < k then NONE else SOME (s with space := s.space - k)`;

val do_space_def = Define `
  do_space op s =
    if op_space_reset op then SOME (s with space := 0)
    else if op_space_req op = 0 then SOME s
         else consume_space (op_space_req op) s`;

val do_app_def = Define `
  do_app op vs (s:bvpSem$state) =
    case do_space op s of
    | NONE => Rerr(Rabort Rtype_error)
    | SOME s1 => (case bviSem$do_app op vs (bvp_to_bvi s1) of
                  | Rerr e => Rerr e
                  | Rval (v,t) => Rval (v, bvi_to_bvp t s1))`

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
  check_clock (s1:bvpSem$state) (s2:bvpSem$state) =
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

val evaluate_def = tDefine "evaluate" `
  (evaluate (Skip,s) = (NONE,s:bvpSem$state)) /\
  (evaluate (Move dest src,s) =
     case get_var src s of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME v => (NONE, set_var dest v s)) /\
  (evaluate (Assign dest op args names_opt,s) =
     if op_space_reset op /\ IS_NONE names_opt then (SOME (Rerr(Rabort Rtype_error)),s) else
     case cut_state_opt names_opt s of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME s =>
       (case get_vars args s of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME xs => (case do_app op xs s of
                      | Rerr e => (SOME (Rerr e),s)
                      | Rval (v,s) =>
                        (NONE, set_var dest v s)))) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME (Rerr(Rabort Rtimeout_error)),call_env [] s with stack := [])
                    else (NONE,dec_clock s)) /\
  (evaluate (MakeSpace k names,s) =
     case cut_env names s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME env => (NONE,add_space s k with locals := env)) /\
  (evaluate (Raise n,s) =
     case get_var n s of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x =>
       (case jump_exc s of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME s => (SOME (Rerr(Rraise x)),s))) /\
  (evaluate (Return n,s) =
     case get_var n s of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x => (SOME (Rval x),call_env [] s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = evaluate (c1,s) in
       if res = NONE then evaluate (c2,check_clock s1 s) else (res,s1)) /\
  (evaluate (If g n c1 c2,s) =
     case evaluate (g,s) of
     | (NONE,s1) =>
         (case get_var n s1 of
          | NONE => (SOME (Rerr(Rabort Rtype_error)),s1)
          | SOME x => if x = Boolv T then evaluate (c1,check_clock s1 s) else
                      if x = Boolv F then evaluate (c2,check_clock s1 s) else
                        (SOME (Rerr(Rabort Rtype_error)),s1))
     | res => res) /\
  (evaluate (Call ret dest args handler,s) =
     if s.clock = 0 then (SOME (Rerr(Rabort Rtimeout_error)),call_env [] s with stack := []) else
       case get_vars args s of
       | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
       | SOME xs =>
         (case find_code dest xs s.code of
          | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
          | SOME (args1,prog) =>
            (case ret of
             | NONE (* tail call *) =>
               if handler = NONE then
                 (case evaluate (prog, call_env args1 (dec_clock s)) of
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | (SOME res,s) => (SOME res,s))
               else (SOME (Rerr(Rabort Rtype_error)),s)
             | SOME (n,names) (* returning call, returns into var n *) =>
               (case cut_env names s.locals of
                | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
                | SOME env =>
               (case evaluate (prog, call_env args1 (push_env env (IS_SOME handler) (dec_clock s))) of
                | (SOME (Rval x),s2) =>
                   (case pop_env s2 of
                    | NONE => (SOME (Rerr(Rabort Rtype_error)),s2)
                    | SOME s1 => (NONE, set_var n x s1))
                | (SOME (Rerr(Rraise x)),s2) =>
                   (case handler of (* if handler is present, then handle exc *)
                    | NONE => (SOME (Rerr(Rraise x)),s2)
                    | SOME (n,h) => evaluate (h, set_var n x (check_clock s2 s)))
                | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                | res => res)))))`
  (WF_REL_TAC `(inv_image (measure I LEX measure prog_size)
                             (\(xs,s). (s.clock,xs)))`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
   \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
   \\ FULL_SIMP_TAC (srw_ss()) [push_env_clock]
   \\ IMP_RES_TAC pop_env_clock \\ fs [] \\ SRW_TAC [] []
   \\ Cases_on `s2.clock < s.clock` \\ fs [] \\ DECIDE_TAC)

val evaluate_ind = theorem"evaluate_ind";

(* We prove that the clock never increases. *)

val do_app_clock = store_thm("do_app_clock",
  ``(bvpSem$do_app op args s1 = Rval (res,s2)) ==> s2.clock <= s1.clock``,
  SIMP_TAC std_ss [do_app_def,do_space_def,consume_space_def]
  \\ SRW_TAC [] [] \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ fs [])
  \\ IMP_RES_TAC bviSemTheory.do_app_const \\ fs []
  \\ fs [bvp_to_bvi_def,bvi_to_bvp_def] \\ SRW_TAC [] []);

val evaluate_clock = store_thm("evaluate_clock",
  ``!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ simp[]
  \\ every_case_tac >> simp[] >> rw[]
  \\ fs[set_var_def,cut_state_opt_def,cut_state_def,call_env_def,dec_clock_def,
        add_space_def,jump_exc_def,push_env_clock]
  \\ every_case_tac >> simp[] >> rw[] >> simp[]
  \\ imp_res_tac pop_env_clock
  \\ imp_res_tac do_app_clock >> fs[] >> rfs[]
  \\ imp_res_tac check_clock_IMP >> fs[] >> simp[]
  \\ imp_res_tac check_clock_IMP >> fs[] >> simp[]
  \\ first_assum(split_applied_pair_tac o lhs o concl) >> fs[]
  \\ every_case_tac >> fs[]
  \\ imp_res_tac check_clock_IMP >> fs[] >> simp[]);

val evaluate_check_clock = prove(
  ``!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [evaluate_clock,check_clock_thm]);

(* Finally, we remove check_clock from the induction and definition theorems. *)

val clean_term = term_rewrite
                   [``check_clock s1 s2 = s1:bvpSem$state``,
                    ``(s.clock < k \/ b2) <=> (s:bvpSem$state).clock < k:num``]

val set_var_check_clock = prove(
  ``set_var v x (check_clock s1 s2) = check_clock (set_var v x s1) s2``,
  SIMP_TAC std_ss [set_var_def,check_clock_def] \\ SRW_TAC [] []);

val evaluate_ind = save_thm("evaluate_ind",let
  val raw_ind = evaluate_ind
  val goal = raw_ind |> concl |> clean_term
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ reverse (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (FIRST_X_ASSUM MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC evaluate_clock \\ SRW_TAC [] []
           \\ `s2.clock <= s.clock` by
            (fs [call_env_def,push_env_def,dec_clock_def]
             \\ IMP_RES_TAC pop_env_clock \\ DECIDE_TAC)
           \\ `s2 = check_clock s2 s` by fs [check_clock_def]
           \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
           \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC evaluate_clock
    \\ IMP_RES_TAC (GSYM evaluate_clock)
    \\ FULL_SIMP_TAC (srw_ss()) [check_clock_thm,GSYM set_var_check_clock])
  in ind |> SIMP_RULE std_ss [bvlPropsTheory.Boolv_11] end);

val evaluate_def = save_thm("evaluate_def",let
  val goal = evaluate_def |> concl |> clean_term
  (* set_goal([],goal) *)
  val def = prove(goal,
    REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [evaluate_def] \\ rfs []
    \\ SRW_TAC [] [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_check_clock
    \\ IMP_RES_TAC evaluate_clock
    \\ fs [check_clock_thm]
    \\ rfs [check_clock_thm]
    \\ fs [check_clock_thm]
    \\ fs [call_env_def,push_env_def]
    \\ IMP_RES_TAC LESS_EQ_dec_clock
    \\ fs [check_clock_thm])
  in def end);

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();

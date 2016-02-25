open preamble bviTheory;
local open bvlSemTheory in end;

val _ = new_theory"bviSem";

val _ = Datatype `
  state =
    <| refs    : num |-> bvlSem$v ref
     ; clock   : num
     ; global  : num option
     ; code    : (num # bvi$exp) num_map
     ; ffi     : 'ffi ffi_state |> `

val dec_clock_def = Define `
  dec_clock x s = s with clock := s.clock - x`;

val LESS_EQ_dec_clock = prove(
  ``r.clock <= (dec_clock x s).clock ==> r.clock <= s.clock``,
  SRW_TAC [] [dec_clock_def] \\ DECIDE_TAC);

val bvi_to_bvl_def = Define `
  (bvi_to_bvl:'ffi bviSem$state->'ffi bvlSem$state) s =
    <| refs := s.refs
     ; clock := s.clock
     ; code := map (K ARB) s.code
     ; ffi := s.ffi |>`;

val bvl_to_bvi_def = Define `
  (bvl_to_bvi:'ffi bvlSem$state->'ffi bviSem$state->'ffi bviSem$state) s t =
    t with <| refs := s.refs
            ; clock := s.clock
            ; ffi := s.ffi |>`;

val small_enough_int_def = Define `
  small_enough_int i <=> -268435457 <= i /\ i <= 268435457`;

val do_app_aux_def = Define `
  do_app_aux op (vs:bvlSem$v list) (s:'ffi bviSem$state) =
    case (op,vs) of
    | (Const i,xs) => if small_enough_int i then
                        SOME (SOME (Number i, s))
                      else NONE
    | (Label l,xs) => (case xs of
                       | [] => SOME (SOME (CodePtr (num_stubs + 2 * l), s))
                       | _ => NONE)
    | (GlobalsPtr,xs) =>
        (case xs of
         | [] => (case s.global of
                  | SOME p => SOME (SOME (RefPtr p, s))
                  | NONE => NONE)
         | _ => NONE)
    | (SetGlobalsPtr,xs) =>
        (case xs of
         | [RefPtr p] => SOME (SOME (Unit, s with global := SOME p))
         | _ => NONE)
    | (Global n, _) => NONE
    | (SetGlobal n, _) => NONE
    | (AllocGlobal, _) => NONE
    | _ => SOME NONE`

val do_app_def = Define `
  do_app op vs (s:'ffi bviSem$state) =
    case do_app_aux op vs s of
    | NONE => Rerr(Rabort Rtype_error)
    | SOME (SOME (v,t)) => Rval (v,t)
    | SOME NONE => (case bvlSem$do_app op vs (bvi_to_bvl s) of
                    | Rerr e => Rerr e
                    | Rval (v,t) => Rval (v, bvl_to_bvi t s))`

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

val check_clock_def = Define `
  check_clock (s1:'ffi bviSem$state) (s2:'ffi bviSem$state) =
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

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of bvi_exp expressions. *)

val evaluate_def = tDefine "evaluate" `
  (evaluate ([],env,s) = (Rval [],s)) /\
  (evaluate (x::y::xs,env,s) =
     case evaluate ([x],env,s) of
     | (Rval v1,s1) =>
         (case evaluate (y::xs,env,check_clock s1 s) of
          | (Rval vs,s2) => (Rval (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (evaluate ([Var n],env,s) =
     if n < LENGTH env then (Rval [EL n env],s) else (Rerr(Rabort Rtype_error),s)) /\
  (evaluate ([If x1 x2 x3],env,s) =
     case evaluate ([x1],env,s) of
     | (Rval vs,s1) =>
          if Boolv T = HD vs then evaluate([x2],env,check_clock s1 s) else
          if Boolv F = HD vs then evaluate([x3],env,check_clock s1 s) else
            (Rerr(Rabort Rtype_error),s1)
     | res => res) /\
  (evaluate ([Let xs x2],env,s) =
     case evaluate (xs,env,s) of
     | (Rval vs,s1) => evaluate ([x2],vs++env,check_clock s1 s)
     | res => res) /\
  (evaluate ([Raise x1],env,s) =
     case evaluate ([x1],env,s) of
     | (Rval vs,s) => (Rerr(Rraise (HD vs)),s)
     | res => res) /\
  (evaluate ([Op op xs],env,s) =
     case evaluate (xs,env,s) of
     | (Rval vs,s) => (case do_app op (REVERSE vs) s of
                          | Rerr e => (Rerr e,s)
                          | Rval (v,s) => (Rval [v],s))
     | res => res) /\
  (evaluate ([Tick x],env,s) =
     if s.clock = 0 then (Rerr(Rabort Rtimeout_error),s) else evaluate ([x],env,dec_clock 1 s)) /\
  (evaluate ([Call ticks dest xs handler],env,s1) =
     if IS_NONE dest /\ IS_SOME handler then (Rerr(Rabort Rtype_error),s1) else
     case evaluate (xs,env,s1) of
     | (Rval vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Rerr(Rabort Rtype_error),s)
          | SOME (args,exp) =>
              if (s.clock < ticks + 1) \/ (s1.clock < ticks + 1) then (Rerr(Rabort Rtimeout_error),s with clock := 0) else
                case evaluate ([exp],args,dec_clock (ticks+1) (check_clock s s1)) of
                | (Rerr(Rraise v),s) =>
                     (case handler of
                      | SOME x => evaluate ([x],v::env,check_clock s s1)
                      | NONE => (Rerr(Rraise v),s))
                | res => res)
     | res => res)`
  (WF_REL_TAC `(inv_image (measure I LEX measure exp2_size)
                             (\(xs,env,s). (s.clock,xs)))`
   \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
   \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
   \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
   \\ FULL_SIMP_TAC (srw_ss()) []
   \\ DECIDE_TAC);

val evaluate_ind = theorem"evaluate_ind";

(* We prove that the clock never increases. *)

val do_app_const = store_thm("do_app_const",
  ``(bviSem$do_app op args s1 = Rval (res,s2)) ==>
    (s2.clock = s1.clock) /\ (s2.code = s1.code)``,
  SIMP_TAC std_ss [do_app_def]
  \\ Cases_on `do_app_aux op args s1` \\ fs []
  \\ Cases_on `x` \\ fs [] THEN1
   (Cases_on `do_app op args (bvi_to_bvl s1)` \\ fs []
    \\ Cases_on `a` \\ fs []
    \\ IMP_RES_TAC bvlSemTheory.do_app_const
    \\ SRW_TAC [] [bvl_to_bvi_def,bvi_to_bvl_def]
    \\ SRW_TAC [] [bvl_to_bvi_def,bvi_to_bvl_def])
  \\ Cases_on `x'` \\ fs []
  \\ fs [do_app_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val evaluate_clock = store_thm("evaluate_clock",
  ``!xs env s1 vs s2.
      (bviSem$evaluate (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss [] \\ BasicProvers.EVERY_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC do_app_const
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ TRY DECIDE_TAC
  \\ REV_FULL_SIMP_TAC std_ss []
  \\ TRY (`check_clock r s1 = r` by SRW_TAC [] [check_clock_def]
          \\ fs [] \\ RES_TAC \\ DECIDE_TAC)
  \\ `check_clock r s1 = r` by SRW_TAC [] [check_clock_def]
  \\ fs [] \\ POP_ASSUM (K ALL_TAC)
  \\ SRW_TAC [] [] \\ RES_TAC
  \\ Q.PAT_ASSUM `!x.bbb` MP_TAC
  \\ `r''.clock <= s1.clock` by DECIDE_TAC
  \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
  \\ REPEAT STRIP_TAC
  \\ `r''.clock <= s1.clock` by DECIDE_TAC
  \\ `check_clock r'' s1 = r''` by SRW_TAC [] [check_clock_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ RES_TAC \\ DECIDE_TAC)

val evaluate_check_clock = prove(
  ``!xs env s1 vs s2.
      (evaluate (xs,env,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [evaluate_clock,check_clock_thm]);

(* Finally, we remove check_clock from the induction and definition theorems. *)

val clean_term = term_rewrite
                   [``check_clock s1 s2 = s1:'ffi bviSem$state``,
                    ``(s.clock < k \/ b2) <=> (s:'ffi bviSem$state).clock < k:num``]

val evaluate_ind = save_thm("evaluate_ind",let
  val raw_ind = evaluate_ind |> INST_TYPE[alpha|->``:'ffi``]
  val goal = raw_ind |> concl |> clean_term
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ reverse (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (first_x_assum match_mp_tac
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ fs []
           \\ SRW_TAC [] [] \\ IMP_RES_TAC evaluate_clock
           \\ IMP_RES_TAC evaluate_check_clock \\ fs []
           \\ fs [check_clock_def, dec_clock_def]
           \\ rfs []
           \\ TRY (`s'.clock ≤ s1.clock` by decide_tac)
           \\ fs []
           \\ first_x_assum match_mp_tac
           \\ decide_tac)
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC evaluate_clock
    \\ FULL_SIMP_TAC std_ss [check_clock_thm])
  in ind end);

val evaluate_def = save_thm("evaluate_def",let
  val goal = evaluate_def |> INST_TYPE[alpha|->``:'ffi``] |> concl |> clean_term
  (* set_goal([],goal) *)
  val def = prove(goal,
    REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [evaluate_def] \\ rfs []
    \\ IMP_RES_TAC evaluate_check_clock
    \\ IMP_RES_TAC evaluate_clock
    \\ IMP_RES_TAC LESS_EQ_TRANS
    \\ IMP_RES_TAC LESS_EQ_dec_clock
    \\ REPEAT (Q.PAT_ASSUM `!x. bbb` (K ALL_TAC))
    \\ IMP_RES_TAC do_app_const
    \\ SRW_TAC [] []
    \\ fs [check_clock_thm]
    \\ rfs [check_clock_thm]
    \\ fs [check_clock_thm, dec_clock_def]
    \\ IMP_RES_TAC LESS_EQ_TRANS
    \\ REPEAT (Q.PAT_ASSUM `!x. bbb` (K ALL_TAC))
    \\ fs [check_clock_thm]
    \\ imp_res_tac LESS_EQ_LESS_TRANS)
  in def end);

(* observational semantics *)

val initial_state_def = Define`
  initial_state ffi code k= <|
    clock := k;
    ffi := ffi;
    code := code;
    refs := FEMPTY;
    global := NONE |>`;

val semantics_def = Define`
  semantics init_ffi code start =
  let es = [bvi$Call 0 (SOME start) [] NONE] in
    if ∃k e. FST (evaluate (es,[],initial_state init_ffi code k)) = Rerr e ∧ e ≠ Rabort Rtimeout_error
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate (es,[],initial_state init_ffi code k) = (r,s) ∧
        (case (s.ffi.final_event,r) of
         | (SOME e,_) => outcome = FFI_outcome e
         | (_,Rval _) => outcome = Success
         | _ => F) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (SND (evaluate (es,[],initial_state init_ffi code k))).ffi.io_events) UNIV))`;

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory()

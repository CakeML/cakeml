open preamble bvlTheory closSemTheory clos_to_bvlTheory

val _ = new_theory"bvlSem"

(* --- Semantics of BVL --- *)

(* these parts are shared by bytecode and, if bytecode is to be supported, need
   to move to a common ancestor *)

val _ = Datatype `
  v =
    Number int          (* integer *)
  | Block num (v list)  (* cons block: tag and payload *)
  | CodePtr num         (* code pointer *)
  | RefPtr num          (* pointer to ref cell *)`;

val Boolv_def = Define`
  Boolv b = bvlSem$Block (bool_to_tag b) []`

val Unit_def = Define`
  Unit = bvlSem$Block (tuple_tag) []`

(* -- *)

val _ = Datatype `
  state =
    <| globals : (bvlSem$v option) list
     ; refs    : num |-> bvlSem$v ref
     ; clock   : num
     ; code    : (num # bvl$exp) num_map
     ; ffi     : 'ffi ffi_state |> `

val v_to_list_def = Define`
  (v_to_list (Block tag []) =
     if tag = nil_tag then SOME [] else NONE) ∧
  (v_to_list (Block tag [h;bt]) =
     if tag = cons_tag then
       (case v_to_list bt of
        | SOME t => SOME (h::t)
        | _ => NONE )
     else NONE) ∧
  (v_to_list _ = NONE)`

val _ = Parse.temp_overload_on("Error",``(Rerr(Rabort Rtype_error)):(bvlSem$v#'ffi bvlSem$state,bvlSem$v)result``)

(* same as closSem$do_app, except:
    - ToList is removed
    - Equal only compares integers
    - IsBlock is added
    - Label is added *)

val do_app_def = Define `
  do_app op vs (s:'ffi bvlSem$state) =
    case (op,vs) of
    | (Global n,[]) =>
        (case get_global n s.globals of
         | SOME (SOME v) => Rval (v,s)
         | _ => Error)
    | (SetGlobal n,[v]) =>
        (case get_global n s.globals of
         | SOME NONE => Rval (Unit,
             s with globals := (LUPDATE (SOME v) n s.globals))
         | _ => Error)
    | (AllocGlobal,[]) =>
        Rval (Unit, s with globals := s.globals ++ [NONE])
    | (Const i,[]) => Rval (Number i, s)
    | (Cons tag,xs) => Rval (Block tag xs, s)
    | (El,[Block tag xs;Number i]) =>
        if 0 ≤ i ∧ Num i < LENGTH xs then Rval (EL (Num i) xs, s) else Error
    | (LengthBlock,[Block tag xs]) =>
        Rval (Number (&LENGTH xs), s)
    | (Length,[RefPtr ptr]) =>
        (case FLOOKUP s.refs ptr of
          | SOME (ValueArray xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (LengthByte,[RefPtr ptr]) =>
        (case FLOOKUP s.refs ptr of
          | SOME (ByteArray xs) =>
              Rval (Number (&LENGTH xs), s)
          | _ => Error)
    | (RefByte,[Number i;Number b]) =>
         if 0 ≤ i ∧ 0 ≤ b ∧ b < 256 then
           let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
             Rval (RefPtr ptr, s with refs := s.refs |+
               (ptr,ByteArray (REPLICATE (Num i) (n2w (Num b)))))
         else Error
    | (RefArray,[Number i;v]) =>
        if 0 ≤ i then
          let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
            Rval (RefPtr ptr, s with refs := s.refs |+
              (ptr,ValueArray (REPLICATE (Num i) v)))
         else Error
    | (DerefByte,[RefPtr ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray ws) =>
            (if 0 ≤ i ∧ i < &LENGTH ws
             then Rval (Number (&(w2n (EL (Num i) ws))),s)
             else Error)
         | _ => Error)
    | (UpdateByte,[RefPtr ptr; Number i; Number b]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray bs) =>
            (if 0 ≤ i ∧ i < &LENGTH bs ∧ 0 ≤ b ∧ b < 256
             then
               Rval (Unit, s with refs := s.refs |+
                 (ptr, ByteArray (LUPDATE (n2w (Num b)) (Num i) bs)))
             else Error)
         | _ => Error)
    | (FromList n,[lv]) =>
        (case v_to_list lv of
         | SOME vs => Rval (Block n vs, s)
         | _ => Error)
    | (TagEq n,[Block tag xs]) =>
        Rval (Boolv (tag = n), s)
    | (TagLenEq n l,[Block tag xs]) =>
        Rval (Boolv (tag = n ∧ LENGTH xs = l),s)
    | (Equal,[Number n1;Number n2]) => Rval (Boolv (n1 = n2), s)
    | (Equal,[RefPtr r1;RefPtr r2]) => Rval (Boolv (r1 = r2), s)
    | (BlockCmp,[Block t1 vs1;Block t2 vs2]) =>
        Rval (Boolv (t1 = t2 ∧ LENGTH vs1 = LENGTH vs2), s)
    | (IsBlock,[Number i]) => Rval (Boolv F, s)
    | (IsBlock,[RefPtr ptr]) => Rval (Boolv F, s)
    | (IsBlock,[Block tag ys]) => Rval (Boolv T, s)
    | (Ref,xs) =>
        let ptr = (LEAST ptr. ~(ptr IN FDOM s.refs)) in
          Rval (RefPtr ptr, s with refs := s.refs |+ (ptr,ValueArray xs))
    | (Deref,[RefPtr ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then Rval (EL (Num i) xs, s)
             else Error)
         | _ => Error)
    | (Update,[RefPtr ptr; Number i; x]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then Rval (Unit, s with refs := s.refs |+
                              (ptr,ValueArray (LUPDATE x (Num i) xs)))
             else Error)
         | _ => Error)
    | (Label n,[]) =>
        if n IN domain s.code then Rval (CodePtr n, s) else Error
    | (Add,[Number n1; Number n2]) => Rval (Number (n1 + n2),s)
    | (Sub,[Number n1; Number n2]) => Rval (Number (n1 - n2),s)
    | (Mult,[Number n1; Number n2]) => Rval (Number (n1 * n2),s)
    | (Div,[Number n1; Number n2]) =>
         if n2 = 0 then Error else Rval (Number (n1 / n2),s)
    | (Mod,[Number n1; Number n2]) =>
         if n2 = 0 then Error else Rval (Number (n1 % n2),s)
    | (Less,[Number n1; Number n2]) =>
         Rval (Boolv (n1 < n2),s)
    | (LessEq,[Number n1; Number n2]) =>
         Rval (Boolv (n1 <= n2),s)
    | (Greater,[Number n1; Number n2]) =>
         Rval (Boolv (n1 > n2),s)
    | (GreaterEq,[Number n1; Number n2]) =>
         Rval (Boolv (n1 >= n2),s)
    | (FFI n, [RefPtr ptr]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray ws) =>
           (case call_FFI s.ffi n ws of
            | (ffi',ws') =>
                Rval (Unit,
                      s with <| refs := s.refs |+ (ptr,ByteArray ws')
                              ; ffi  := ffi'|>))
         | _ => Error)
    | _ => Error`;

val dec_clock_def = Define `
  dec_clock n s = s with clock := s.clock - n`;

(* Functions for looking up function definitions *)

val find_code_def = Define `
  (find_code (SOME p) args code =
     case lookup p code of
     | NONE => NONE
     | SOME (arity,exp) => if LENGTH args = arity then SOME (args,exp)
                                                  else NONE) /\
  (find_code NONE args code =
     if args = [] then NONE else
       case LAST args of
       | CodePtr loc =>
           (case sptree$lookup loc code of
            | NONE => NONE
            | SOME (arity,exp) => if LENGTH args = arity + 1
                                  then SOME (FRONT args,exp)
                                  else NONE)
       | other => NONE)`

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

(* Proving termination of the evaluator directly is tricky. We make
   our life simpler by forcing the clock to stay good using
   check_clock. At the bottom of this file, we remove all occurrences
   of check_clock. *)

val check_clock_def = Define `
  check_clock (s1:'ffi bvlSem$state) (s2:'ffi bvlSem$state) =
    if s1.clock <= s2.clock then s1 else s1 with clock := s2.clock`;

val check_clock_thm = prove(
  ``(check_clock s1 s2).clock <= s2.clock /\
    (s1.clock <= s2.clock ==> (check_clock s1 s2 = s1))``,
  SRW_TAC [] [check_clock_def])

val check_clock_lemma = prove(
  ``b ==> ((check_clock s1 s).clock < s.clock \/
          ((check_clock s1 s).clock = s.clock) /\ b)``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of exp expressions. *)

val evaluate_def = tDefine "evaluate" `
  (evaluate ([],env,s:'ffi bvlSem$state) = (Rval [],s)) /\
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
  (evaluate ([Handle x1 x2],env,s1) =
     case evaluate ([x1],env,s1) of
     | (Rerr(Rraise v),s) => evaluate ([x2],v::env,check_clock s s1)
     | res => res) /\
  (evaluate ([Op op xs],env,s) =
     case evaluate (xs,env,s) of
     | (Rval vs,s) => (case do_app op (REVERSE vs) s of
                          | Rerr err => (Rerr err,s)
                          | Rval (v,s) => (Rval [v],s))
     | res => res) /\
  (evaluate ([Tick x],env,s) =
     if s.clock = 0 then (Rerr(Rabort Rtimeout_error),s) else evaluate ([x],env,dec_clock 1 s)) /\
  (evaluate ([Call ticks dest xs],env,s1) =
     case evaluate (xs,env,s1) of
     | (Rval vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Rerr(Rabort Rtype_error),s)
          | SOME (args,exp) =>
              if (s.clock < ticks + 1) \/ (s1.clock < ticks + 1) then (Rerr(Rabort Rtimeout_error),s with clock := 0) else
                  evaluate ([exp],args,dec_clock (ticks + 1) (check_clock s s1)))
     | res => res)`
 (WF_REL_TAC `(inv_image (measure I LEX measure exp1_size)
                            (\(xs,env,s). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

(* We prove that the clock never increases. *)

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val do_app_const = store_thm("do_app_const",
  ``(do_app op args s1 = Rval (res,s2)) ==>
    (s2.clock = s1.clock) /\ (s2.code = s1.code)``,
  SIMP_TAC std_ss [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val evaluate_clock = store_thm("evaluate_clock",
  ``!xs env s1 vs s2.
      (evaluate (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "evaluate_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss [] \\ BasicProvers.EVERY_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC do_app_const
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ TRY DECIDE_TAC
  \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val evaluate_check_clock = prove(
  ``!xs env s1 vs s2.
      (evaluate (xs,env,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [evaluate_clock,check_clock_thm]);

(* Finally, we remove check_clock from the induction and definition theorems. *)

val clean_term = term_rewrite
                   [``check_clock s1 s2 = s1:'ffi bvlSem$state``,
                    ``(s.clock < k \/ b2) <=> (s:'ffi bvlSem$state).clock < k:num``]

val evaluate_ind = save_thm("evaluate_ind",let
  val raw_ind = fetch "-" "evaluate_ind"
  val goal = raw_ind |> concl |> clean_term
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ reverse (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (Q.PAT_ASSUM `!ticks dest xs env s1. bb ==> bbb` MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC evaluate_clock
           \\ `¬(s1.clock < ticks + 1)` by DECIDE_TAC
           \\ SRW_TAC [] []
           \\ FULL_SIMP_TAC (srw_ss()) []
           \\ IMP_RES_TAC evaluate_check_clock
           \\ FULL_SIMP_TAC std_ss [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC evaluate_clock
    \\ FULL_SIMP_TAC std_ss [check_clock_thm])
  in ind end);

val evaluate_def = save_thm("evaluate_def",let
  val goal = evaluate_def |> concl |> clean_term
  (* set_goal([],goal) *)
  val def = prove(goal,
    REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [evaluate_def] \\ rfs []
    \\ IMP_RES_TAC evaluate_check_clock
    \\ IMP_RES_TAC evaluate_clock
    \\ IMP_RES_TAC LESS_EQ_TRANS
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
  initial_state ffi code k = <|
    clock := k;
    ffi := ffi;
    code := code;
    globals := [];
    refs := FEMPTY
  |>`;

val semantics_def = Define`
  semantics init_ffi code start =
  let es = [Call 0 (SOME start) []] in
    if ∃k. FST (evaluate (es,[],initial_state init_ffi code k)) = Rerr (Rabort Rtype_error)
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate (es,[],initial_state init_ffi code k) = (r,s) ∧
        (case s.ffi.final_event of
         | NONE => (∀a. r ≠ Rerr (Rabort a)) ∧ outcome = Success
         | SOME e => outcome = FFI_outcome e) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (SND (evaluate (es,[],initial_state init_ffi code k))).ffi.io_events) UNIV))`;

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory()

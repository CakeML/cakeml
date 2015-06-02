open preamble bvlTheory closSemTheory

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

val closure_tag_def = Define`closure_tag = 0:num`
val partial_app_tag_def = Define`partial_app_tag = 1:num`
val clos_tag_shift_def = Define`clos_tag_shift = 2:num`

val do_eq_def = tDefine"do_eq"`
  (do_eq (CodePtr _) _ = Eq_type_error) ∧
  (do_eq _ (CodePtr _) = Eq_type_error) ∧
  (do_eq (Number n1) (Number n2) = (Eq_val (n1 = n2))) ∧
  (do_eq (Number _) _ = Eq_val F) ∧
  (do_eq _ (Number _) = Eq_val F) ∧
  (do_eq (RefPtr n1) (RefPtr n2) = (Eq_val (n1 = n2))) ∧
  (do_eq (RefPtr _) _ = Eq_val F) ∧
  (do_eq _ (RefPtr _) = Eq_val F) ∧
  (do_eq (Block t1 l1) (Block t2 l2) =
   if (t1 = closure_tag) ∨ (t2 = closure_tag) ∨ (t1 = partial_app_tag) ∨ (t2 = partial_app_tag)
   then Eq_closure
   else if (t1 = t2) ∧ (LENGTH l1 = LENGTH l2)
        then do_eq_list l1 l2
        else Eq_val F) ∧
  (do_eq_list [] [] = Eq_val T) ∧
  (do_eq_list (v1::vs1) (v2::vs2) =
   case do_eq v1 (v2:bvlSem$v) of
   | Eq_val T => do_eq_list vs1 vs2
   | Eq_val F => Eq_val F
   | bad => bad) ∧
  (do_eq_list _ _ = Eq_val F)`
  (WF_REL_TAC `measure (\x. case x of INL (v1,v2) => v_size v1 | INR (vs1,vs2) => v1_size vs1)`);

val bool_to_tag_def = Define`
  bool_to_tag b = ((if b then true_tag else false_tag) + pat_tag_shift + clos_tag_shift)`

val bool_to_tag_11 = store_thm("bool_to_tag_11[simp]",
  ``bool_to_tag b1 = bool_to_tag b2 ⇔ (b1 = b2)``,
  rw[bool_to_tag_def] >> EVAL_TAC >> simp[])

val Boolv_def = Define`
  Boolv b = bvlSem$Block (bool_to_tag b) []`

(* -- *)

val _ = Datatype `
  state =
    <| globals : (bvlSem$v option) list
     ; refs    : num |-> bvlSem$v ref
     ; clock   : num
     ; code    : (num # bvl$exp) num_map
     ; io      : io_trace |> `

val do_app_def = Define `
  do_app op vs (s:bvlSem$state) =
    case (op,vs) of
    | (Global n,[]) =>
        (case get_global n s.globals of
         | SOME (SOME v) => SOME (v,s)
         | _ => NONE)
    | (SetGlobal n,[v]) =>
        (case get_global n s.globals of
         | SOME NONE => SOME (Number 0,
             s with globals := (LUPDATE (SOME v) n s.globals))
         | _ => NONE)
    | (AllocGlobal,[]) =>
        SOME (Number 0, s with globals := s.globals ++ [NONE])
    | (Const i,[]) => SOME (bvlSem$Number i, s)
    | (Cons tag,xs) => SOME (Block tag xs, s)
    | (El,[Block tag xs;Number i]) =>
        if 0 ≤ i ∧ Num i < LENGTH xs then SOME (EL (Num i) xs, s) else NONE
    | (LengthBlock,[Block tag xs]) =>
        SOME (Number (&LENGTH xs), s)
    | (Length,[RefPtr ptr]) =>
        (case FLOOKUP s.refs ptr of
          | SOME (ValueArray xs) =>
              SOME (Number (&LENGTH xs), s)
          | _ => NONE)
    | (LengthByte,[RefPtr ptr]) =>
        (case FLOOKUP s.refs ptr of
          | SOME (ByteArray xs) =>
              SOME (Number (&LENGTH xs), s)
          | _ => NONE)
    | (RefByte,[Number b;Number i]) =>
         if 0 ≤ i ∧ 0 ≤ b ∧ b < 256 then
           let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
             SOME (RefPtr ptr, s with refs := s.refs |+
               (ptr,ByteArray (REPLICATE (Num i) (n2w (Num b)))))
         else NONE
    | (RefArray,[v;Number i]) =>
        if 0 ≤ i then
          let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
            SOME (RefPtr ptr, s with refs := s.refs |+
              (ptr,ValueArray (REPLICATE (Num i) v)))
         else NONE
    | (DerefByte,[RefPtr ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray ws) =>
            (if 0 ≤ i ∧ i < &LENGTH ws
             then SOME (Number (&(w2n (EL (Num i) ws))),s)
             else NONE)
         | _ => NONE)
    | (UpdateByte,[RefPtr ptr; Number i; Number b]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray bs) =>
            (if 0 ≤ i ∧ i < &LENGTH bs ∧ 0 ≤ b ∧ b < 256
             then
               (SOME (Number b, s with refs := s.refs |+
                 (ptr, ByteArray (LUPDATE (n2w (Num b)) (Num i) bs))))
             else NONE)
         | _ => NONE)
    | (TagEq n l,[Block tag xs]) =>
        SOME (Boolv (tag = n ∧ LENGTH xs = l),s)
    | (Equal,[x1;x2]) =>
        (case do_eq x1 x2 of
         | Eq_val b => SOME (Boolv b, s)
         | Eq_closure => SOME (Number 0, s)
         | _ => NONE)
    | (IsBlock,[Number i]) => SOME (Boolv F, s)
    | (IsBlock,[RefPtr ptr]) => SOME (Boolv F, s)
    | (IsBlock,[Block tag ys]) => SOME (Boolv T, s)
    | (Ref,xs) =>
        let ptr = (LEAST ptr. ~(ptr IN FDOM s.refs)) in
          SOME (RefPtr ptr, s with refs := s.refs |+ (ptr,ValueArray xs))
    | (Deref,[RefPtr ptr; Number i]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then SOME (EL (Num i) xs, s)
             else NONE)
         | _ => NONE)
    | (Update,[RefPtr ptr; Number i; x]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ValueArray xs) =>
            (if 0 <= i /\ i < & (LENGTH xs)
             then SOME (x, s with refs := s.refs |+
                    (ptr,ValueArray (LUPDATE x (Num i) xs)))
             else NONE)
         | _ => NONE)
    | (Label n,[]) =>
        if n IN domain s.code then SOME (CodePtr n, s) else NONE
    | (Add,[Number n1; Number n2]) => SOME (Number (n1 + n2),s)
    | (Sub,[Number n1; Number n2]) => SOME (Number (n1 - n2),s)
    | (Mult,[Number n1; Number n2]) => SOME (Number (n1 * n2),s)
    | (Div,[Number n1; Number n2]) =>
         if n2 = 0 then NONE else SOME (Number (n1 / n2),s)
    | (Mod,[Number n1; Number n2]) =>
         if n2 = 0 then NONE else SOME (Number (n1 % n2),s)
    | (Less,[Number n1; Number n2]) =>
         SOME (Boolv (n1 < n2),s)
    | (LessEq,[Number n1; Number n2]) =>
         SOME (Boolv (n1 <= n2),s)
    | (Greater,[Number n1; Number n2]) =>
         SOME (Boolv (n1 > n2),s)
    | (GreaterEq,[Number n1; Number n2]) =>
         SOME (Boolv (n1 >= n2),s)
    | _ => NONE`;

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
  check_clock s1 s2 =
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
  (evaluate ([],env,s:bvlSem$state) = (Rval [],s)) /\
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
                          | NONE => (Rerr(Rabort Rtype_error),s)
                          | SOME (v,s) => (Rval [v],s))
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
  ``(do_app op args s1 = SOME (res,s2)) ==>
    (s2.clock = s1.clock) /\ (s2.code = s1.code)``,
  SIMP_TAC std_ss [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val do_app_change_clock = store_thm("do_app_change_clock",
  ``(do_app op args s1 = SOME (res,s2)) ==>
    (do_app op args (s1 with clock := ck) = SOME (res,s2 with clock := ck))``,
  SIMP_TAC std_ss [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [] \\
  CCONTR_TAC >> fs [] >>
  rw [] >>
  fs [do_eq_def]);

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

fun sub f tm = f tm handle HOL_ERR _ =>
  let val (v,t) = dest_abs tm in mk_abs (v, sub f t) end
  handle HOL_ERR _ =>
  let val (t1,t2) = dest_comb tm in mk_comb (sub f t1, sub f t2) end
  handle HOL_ERR _ => tm

val remove_check_clock = sub (fn tm =>
  if can (match_term ``check_clock s1 s2``) tm
  then tm |> rator |> rand else fail())

val remove_disj = sub (fn tm => if is_disj tm then tm |> rator |> rand else fail())

val evaluate_ind = save_thm("evaluate_ind",let
  val raw_ind = fetch "-" "evaluate_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
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
  val tm = fetch "-" "evaluate_AUX_def"
           |> concl |> rand |> dest_abs |> snd |> rand |> rand
  val tm = ``^tm evaluate (xs,env,s)``
  val rhs = SIMP_CONV std_ss [EVAL ``pair_CASE (x,y) f``] tm |> concl |> rand
  val goal = ``!xs env s. evaluate (xs,env,s) = ^rhs`` |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    recInduct evaluate_ind
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ TRY (SIMP_TAC std_ss [Once evaluate_def] \\ NO_TAC)
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [Once evaluate_def]
    \\ Cases_on `evaluate (xs,env,s1)`
    \\ Cases_on `evaluate (xs,env,s)`
    \\ Cases_on `evaluate ([x],env,s)`
    \\ Cases_on `evaluate ([x1],env,s)`
    \\ Cases_on `evaluate ([x2],env,s)`
    \\ Cases_on `evaluate ([x1],env,s1)`
    \\ Cases_on `evaluate ([x2],env,s1)`
    \\ IMP_RES_TAC evaluate_check_clock
    \\ IMP_RES_TAC evaluate_clock
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``pair_CASE (x,y) f``]
    \\ Cases_on `r.clock < ticks + 1` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `s1.clock < ticks + 1` \\ FULL_SIMP_TAC std_ss [] >>
    `r.clock = s1.clock` by decide_tac >>
    fs [])
  val new_def = evaluate_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* lemmas *)

val evaluate_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case evaluate (xs,s,env) of (Rval res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC evaluate_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [evaluate_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("evaluate_LENGTH", evaluate_LENGTH);

val evaluate_IMP_LENGTH = store_thm("evaluate_IMP_LENGTH",
  ``(evaluate (xs,s,env) = (Rval res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL evaluate_LENGTH) \\ fs []);

val evaluate_CONS = store_thm("evaluate_CONS",
  ``evaluate (x::xs,env,s) =
      case evaluate ([x],env,s) of
      | (Rval v,s2) =>
         (case evaluate (xs,env,s2) of
          | (Rval vs,s1) => (Rval (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ fs [evaluate_def]
  \\ Cases_on `evaluate ([x],env,s)` \\ fs [evaluate_def]
  \\ Cases_on `q` \\ fs [evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val evaluate_SNOC = store_thm("evaluate_SNOC",
  ``!xs env s x.
      evaluate (SNOC x xs,env,s) =
      case evaluate (xs,env,s) of
      | (Rval vs,s2) =>
         (case evaluate ([x],env,s2) of
          | (Rval v,s1) => (Rval (vs ++ v),s1)
          | t => t)
      | t => t``,
  Induct THEN1
   (fs [SNOC_APPEND,evaluate_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `evaluate ([x],env,s)` \\ Cases_on `q` \\ fs [])
  \\ fs [SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate ([h],env,s)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `evaluate (xs,env,r)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `evaluate ([x],env,r')` \\ Cases_on `q` \\ fs [evaluate_def]
  \\ IMP_RES_TAC evaluate_IMP_LENGTH
  \\ Cases_on `a''` \\ fs [LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ fs []);

val evaluate_APPEND = store_thm("evaluate_APPEND",
  ``!xs env s ys.
      evaluate (xs ++ ys,env,s) =
      case evaluate (xs,env,s) of
        (Rval vs,s2) =>
          (case evaluate (ys,env,s2) of
             (Rval ws,s1) => (Rval (vs ++ ws),s1)
           | res => res)
      | res => res``,
  Induct \\ fs [APPEND,evaluate_def] \\ REPEAT STRIP_TAC
  THEN1 REPEAT BasicProvers.CASE_TAC
  \\ ONCE_REWRITE_TAC [evaluate_CONS]
  \\ REPEAT BasicProvers.CASE_TAC \\ fs []);

val state_component_equality=theorem"state_component_equality"

val evaluate_code = store_thm("evaluate_code",
  ``!xs env s1 vs s2.
      (evaluate (xs,env,s1) = (vs,s2)) ==> s2.code = s1.code``,
  recInduct evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [dec_clock_def]
  \\ Cases_on`q`  \\ FULL_SIMP_TAC (srw_ss())[]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ SRW_TAC[][]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ IMP_RES_TAC do_app_const \\ SRW_TAC[][]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ SRW_TAC[][dec_clock_def]);

val mk_tick_def = Define `
  mk_tick n e = FUNPOW Tick n e : bvl$exp`;

val evaluate_mk_tick = Q.store_thm ("evaluate_mk_tick",
`!exp env s n.
  evaluate ([mk_tick n exp], env, s) =
    if s.clock < n then
      (Rerr(Rabort Rtimeout_error), s with clock := 0)
    else
      evaluate ([exp], env, dec_clock n s)`,
 Induct_on `n` >>
 rw [mk_tick_def, evaluate_def, dec_clock_def, FUNPOW] >>
 fs [mk_tick_def, evaluate_def, dec_clock_def] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def, ADD1]
 >- (`s with clock := s.clock = s`
            by rw [state_component_equality] >>
     rw [])
 >- (`s.clock = n` by decide_tac >>
     fs []));

val inc_clock_def = Define `
inc_clock ck s = s with clock := s.clock + ck`;

val inc_clock_code = Q.store_thm ("inc_clock_code",
`!n (s:bvlSem$state). (inc_clock n s).code = s.code`,
 rw [inc_clock_def]);

val inc_clock_refs = Q.store_thm ("inc_clock_refs",
`!n (s:bvlSem$state). (inc_clock n s).refs = s.refs`,
 rw [inc_clock_def]);

val inc_clock0 = Q.store_thm ("inc_clock0",
`!n (s:bvlSem$state). inc_clock 0 s = s`,
 simp [inc_clock_def, state_component_equality]);

val _ = export_rewrites ["inc_clock_refs", "inc_clock_code", "inc_clock0"];

val dec_clock_code = Q.store_thm ("dec_clock_code",
`!n (s:bvlSem$state). (dec_clock n s).code = s.code`,
 rw [dec_clock_def]);

val dec_clock_refs = Q.store_thm ("dec_clock_refs",
`!n (s:bvlSem$state). (dec_clock n s).refs = s.refs`,
 rw [dec_clock_def]);

val dec_clock0 = Q.store_thm ("dec_clock0",
`!n (s:bvlSem$state). dec_clock 0 s = s`,
 simp [dec_clock_def, state_component_equality]);

val _ = export_rewrites ["dec_clock_refs", "dec_clock_code", "dec_clock0"];

val evaluate_add_clock = Q.store_thm ("evaluate_add_clock",
`!exps env s1 res s2.
  evaluate (exps,env,s1) = (res, s2) ∧
  res ≠ Rerr(Rabort Rtimeout_error)
  ⇒
  !ck. evaluate (exps,env,inc_clock ck s1) = (res, inc_clock ck s2)`,
 recInduct evaluate_ind >>
 rw [evaluate_def]
 >- (Cases_on `evaluate ([x], env,s)` >> fs [] >>
     Cases_on `q` >> fs [] >> rw [] >>
     Cases_on `evaluate (y::xs,env,r)` >> fs [] >>
     Cases_on `q` >> fs [] >> rw [] >> fs[])
 >- (Cases_on `evaluate ([x1],env,s)` >> fs [] >>
     Cases_on `q` >> fs [] >> rw[] >> fs[])
 >- (Cases_on `evaluate (xs,env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >> fs[])
 >- (Cases_on `evaluate (xs,env,s)` >> fs [] >>
     Cases_on `q` >> fs [] >> rw[] >> fs[] >>
     BasicProvers.EVERY_CASE_TAC >>
     fs [] >> rw [] >> fs[])
 >- (Cases_on `evaluate ([x1],env,s1)` >> fs [] >>
     Cases_on `q` >> fs [] >> rw [] >> fs[] >>
     Cases_on`e`>>fs[]>>rw[]>>fs[])
 >- (Cases_on `evaluate (xs,env,s)` >> fs [] >>
     Cases_on `q` >> fs [] >> rw[] >> fs[] >>
     rw [inc_clock_def] >>
     BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     imp_res_tac do_app_const >>
     imp_res_tac do_app_change_clock >>
     fs [] >>
     rw [] >>
     pop_assum (qspec_then `r.clock` mp_tac) >>
     rw [] >>
     `r with clock := r.clock = r` by rw [state_component_equality] >>
     fs [])
 >- (rw [] >>
     fs [inc_clock_def, dec_clock_def] >>
     rw [] >>
     `s.clock + ck - 1 = s.clock - 1 + ck` by (srw_tac [ARITH_ss] [ADD1]) >>
     metis_tac [])
 >- (Cases_on `evaluate (xs,env,s1)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     rw [] >>
     rfs [inc_clock_def, dec_clock_def] >>
     rw []
     >- decide_tac >>
     `r.clock + ck - (ticks + 1) = r.clock - (ticks + 1) + ck` by srw_tac [ARITH_ss] [ADD1] >>
     metis_tac []));

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory()

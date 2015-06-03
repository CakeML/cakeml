open preamble closLangTheory conLangTheory pat_to_closTheory

val _ = new_theory"closSem"

(* differs from store_v by removing the single value Refv *)
val _ = Datatype `
  ref = ValueArray ('a list)
      | ByteArray (word8 list)`

(* --- Semantics of ClosLang --- *)

val _ = Datatype `
  v =
    Number int
  | Block num (v list)
  | RefPtr num
  | Closure num (v list) (v list) num closLang$exp
  | Recclosure num (v list) (v list) ((num # closLang$exp) list) num`

val _ = Datatype `
  state =
    <| globals : (closSem$v option) list
     ; refs    : num |-> closSem$v ref
     ; io      : io_trace
     ; clock   : num
     ; code    : num |-> (num # closLang$exp)
     ; restrict_envs : bool |> `

(* helper functions *)

val get_global_def = Define `
  get_global n globals =
    if n < LENGTH globals then SOME (EL n globals) else NONE`

val Boolv_def = Define `
  (Boolv b = Block ((if b then true_tag else false_tag)+pat_tag_shift) [])`;

val do_eq_def = tDefine "do_eq" `
  (do_eq x y =
     case x of
     | Number i =>
         (case y of
          | Number j => Eq_val (i = j)
          | _ => Eq_val F)
     | Block t1 xs =>
         (case y of
          | Block t2 ys => if (t1 = t2) /\ (LENGTH xs = LENGTH ys) then
                             do_eq_list xs ys
                           else Eq_val F
          | Number _ => Eq_val F
          | RefPtr _ => Eq_val F
          | _ => Eq_closure)
     | RefPtr i =>
         (case y of
          | RefPtr j => Eq_val (i = j)
          | _ => Eq_val F)
     | _ =>
         (case y of
          | Number _ => Eq_val F
          | RefPtr _ => Eq_val F
          | _ => Eq_closure)) /\
  (do_eq_list [] [] = Eq_val T) /\
  (do_eq_list (x::xs) (y::ys) =
     case do_eq x y of
     | Eq_val T => do_eq_list xs ys
     | res => res) /\
  (do_eq_list _ _ = Eq_val F)`
 (WF_REL_TAC `measure (\x. case x of INL (v,_) => v_size v
                                   | INR (vs,_) => v1_size vs)`)

val v_to_list_def = Define`
  (v_to_list (Block tag []) =
     if tag = nil_tag+pat_tag_shift then SOME [] else NONE) ∧
  (v_to_list (Block tag [h;bt]) =
     if tag = cons_tag+pat_tag_shift then
       (case v_to_list bt of
        | SOME t => SOME (h::t)
        | _ => NONE )
     else NONE) ∧
  (v_to_list _ = NONE)`

val list_to_v_def = Define`
  (list_to_v [] = Block (nil_tag+pat_tag_shift) []) ∧
  (list_to_v (h::t) = Block (cons_tag+pat_tag_shift) [h;list_to_v t])`

val Unit_def = Define`
  Unit = Block (tuple_tag+pat_tag_shift) []`

val _ = Parse.temp_overload_on("Error",``(Rerr(Rabort Rtype_error)):(closSem$v#closSem$state,closSem$v)result``)

val do_app_def = Define `
  do_app (op:closLang$op) (vs:closSem$v list) (s:closSem$state) =
    case (op,vs) of
    | (Global n,[]:closSem$v list) =>
        (case get_global n s.globals of
         | SOME (SOME v) => (Rval (v,s))
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
    | (ToList,[Block tag xs]) =>
        Rval (list_to_v xs, s)
    | (TagEq n l,[Block tag xs]) =>
        Rval (Boolv (tag = n ∧ LENGTH xs = l),s)
    | (Equal,[x1;x2]) =>
        (case do_eq x1 x2 of
         | Eq_val b => Rval (Boolv b, s)
         | Eq_closure => Rval (Number 0, s)
         | _ => Error)
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
           (case call_FFI n ws s.io of
            | SOME (ws',t') =>
                Rval (Unit,
                      s with <| refs := s.refs |+ (ptr,ByteArray ws')
                              ; io   := t'|>)
            | _ => Rerr(Rabort Rffi_error))
         | _ => Error)
    | _ => Error`;

val dec_clock_def = Define `
  dec_clock n (s:closSem$state) = s with clock := s.clock - n`;

val find_code_def = Define `
  find_code p args code =
    case FLOOKUP code p of
    | NONE => NONE
    | SOME (arity,exp) => if LENGTH args = arity then SOME (args,exp)
                                                 else NONE`

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
   defined to evaluate a list of clos_exp expressions. *)

val lookup_vars_def = Define `
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)`

val check_loc_opt_def = Define `
  (check_loc NONE loc num_params num_args so_far ⇔ num_args ≤ max_app) /\
  (check_loc (SOME p) loc num_params num_args so_far ⇔ 
    (num_params = num_args) ∧ (so_far = 0:num) ∧ (p = loc))`;

val _ = Datatype `
  app_kind =
    | Partial_app closSem$v
    | Full_app closLang$exp (closSem$v list) (closSem$v list)`;

val dest_closure_def = Define `
  dest_closure loc_opt f args =
    case f of
    | Closure loc arg_env clo_env num_args exp =>
        if check_loc loc_opt loc num_args (LENGTH args) (LENGTH arg_env) ∧ LENGTH arg_env < num_args then
          if ¬(LENGTH args + LENGTH arg_env < num_args) then
            SOME (Full_app exp
                           (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE args))++
                            arg_env++clo_env)
                           (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
          else
            SOME (Partial_app (Closure loc (args++arg_env) clo_env num_args exp))
        else
          NONE
    | Recclosure loc arg_env clo_env fns i =>
        let (num_args,exp) = EL i fns in
          if LENGTH fns <= i \/
             ~(check_loc loc_opt (loc+i) num_args (LENGTH args) (LENGTH arg_env)) ∨
             ¬(LENGTH arg_env < num_args) then NONE else
            let rs = GENLIST (Recclosure loc [] clo_env fns) (LENGTH fns) in
              if ¬(LENGTH args + LENGTH arg_env < num_args) then
                SOME (Full_app exp
                               (REVERSE (TAKE (num_args - LENGTH arg_env) (REVERSE args))++
                                arg_env++rs++clo_env)
                               (REVERSE (DROP (num_args - LENGTH arg_env) (REVERSE args))))
              else
                SOME (Partial_app (Recclosure loc (args++arg_env) clo_env fns i))
    | _ => NONE`;

val dest_closure_length = Q.prove (
  `!loc_opt f args exp args1 args2 so_far.
    dest_closure loc_opt f args = SOME (Full_app exp args1 args2)
    ⇒
    LENGTH args2 < LENGTH args`,
  rw [dest_closure_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  rw [] >>
  TRY decide_tac >>
  Cases_on `EL n l1` >>
  fs [LET_THM] >>
  Cases_on `LENGTH args + LENGTH l < q` >>
  fs [] >>
  rw [] >>
  decide_tac);

val clos_env_def = Define `
  clos_env restrict names env =
    if restrict then lookup_vars names env else SOME env`

val build_recc_def = Define `
  build_recc restrict loc env names fns =
    case clos_env restrict names env of
    | SOME env1 => SOME (GENLIST (Recclosure loc [] env1 fns) (LENGTH fns))
    | NONE => NONE`

val evaluate_def = tDefine "evaluate" `
  (evaluate ([],env:closSem$v list,s:closSem$state) = (Rval [],s)) /\
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
          if Boolv T = HD vs then evaluate ([x2],env,check_clock s1 s) else
          if Boolv F = HD vs then evaluate ([x3],env,check_clock s1 s) else
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
  (evaluate ([Fn loc vs num_args exp],env,s) =
     if num_args ≤ max_app ∧ num_args ≠ 0 then
       case clos_env s.restrict_envs vs env of
       | NONE => (Rerr(Rabort Rtype_error),s)
       | SOME env' => (Rval [Closure loc [] env' num_args exp], s)
     else
       (Rerr(Rabort Rtype_error), s)) /\
  (evaluate ([Letrec loc names fns exp],env,s) =
     if EVERY (\(num_args,e). num_args ≤ max_app ∧ num_args ≠ 0) fns then
       case build_recc s.restrict_envs loc env names fns of
       | NONE => (Rerr(Rabort Rtype_error),s)
       | SOME rs => evaluate ([exp],rs ++ env,s)
     else
       (Rerr(Rabort Rtype_error), s)) /\
  (evaluate ([App loc_opt x1 args],env,s) =
     if LENGTH args > 0 then
       (case evaluate (args,env,s) of
        | (Rval y2,s1) =>
          (case evaluate ([x1],env,check_clock s1 s) of
           | (Rval y1,s2) => evaluate_app loc_opt (HD y1) y2 (check_clock s2 s)
           | res => res)
        | res => res)
     else
       (Rerr(Rabort Rtype_error), s)) /\
  (evaluate ([Tick x],env,s) =
     if s.clock = 0 then (Rerr(Rabort Rtimeout_error),s) else evaluate ([x],env,dec_clock 1 s)) /\
  (evaluate ([Call dest xs],env,s1) =
     case evaluate (xs,env,s1) of
     | (Rval vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Rerr(Rabort Rtype_error),s)
          | SOME (args,exp) =>
              if (s.clock = 0) \/ (s1.clock = 0) then (Rerr(Rabort Rtimeout_error),s) else
                  evaluate ([exp],args,dec_clock 1 (check_clock s s1)))
     | res => res) ∧
  (evaluate_app loc_opt f [] s = (Rval [f], s)) ∧
  (evaluate_app loc_opt f args s =
     case dest_closure loc_opt f args of
     | NONE => (Rerr(Rabort Rtype_error),s)
     | SOME (Partial_app v) =>
         if s.clock < LENGTH args
         then (Rerr(Rabort Rtimeout_error),s with clock := 0)
         else (Rval [v], dec_clock (LENGTH args) s)
     | SOME (Full_app exp env rest_args) =>
         if s.clock < (LENGTH args - LENGTH rest_args)
         then (Rerr(Rabort Rtimeout_error),s with clock := 0)
         else
           case evaluate ([exp],env,dec_clock (LENGTH args - LENGTH rest_args) s) of
           | (Rval [v], s1) =>
               evaluate_app loc_opt v rest_args (check_clock s1 s)
           | res => res)`
 (WF_REL_TAC `(inv_image (measure I LEX measure I LEX measure I)
               (\x. case x of INL (xs,env,s) => (s.clock,exp3_size xs,0)
                              | INR (l,f,args,s) => (s.clock,0,LENGTH args)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
  \\ Cases_on `s.clock <= s2.clock`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] []
  \\ TRY DECIDE_TAC >>
  imp_res_tac dest_closure_length >>
  full_simp_tac (srw_ss()++ARITH_ss) [])

(* We prove that the clock never increases. *)

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val do_app_const = store_thm("do_app_const",
  ``(do_app op args s1 = Rval (res,s2)) ==>
    (s2.clock = s1.clock) /\
    (s2.code = s1.code) /\
    (s2.restrict_envs = s1.restrict_envs)``,
  SIMP_TAC std_ss [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val evaluate_ind = theorem"evaluate_ind"

val evaluate_clock_help = prove (
  ``(!tup vs s2.
      (evaluate tup = (vs,s2)) ==> s2.clock <= (SND (SND tup)).clock) ∧
    (!loc_opt f args s1 vs s2.
      (evaluate_app loc_opt f args s1 = (vs,s2)) ==> s2.clock <= s1.clock)``,
  ho_match_mp_tac evaluate_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [evaluate_def]
  \\ FULL_SIMP_TAC std_ss [] \\ BasicProvers.EVERY_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC do_app_const
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ TRY DECIDE_TAC
  \\ POP_ASSUM MP_TAC
  \\ TRY (REPEAT (POP_ASSUM (K ALL_TAC))
          \\ SRW_TAC [] [check_clock_def] \\ DECIDE_TAC)
  \\ rfs [] \\ fs [] \\ rfs [check_clock_def]);

val evaluate_clock = store_thm("evaluate_clock",
``(!xs env s1 vs s2.
      (evaluate (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock)``,
 metis_tac [evaluate_clock_help, SND]);

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

val pat = ``check_clock s1 s2``
val remove_check_clock = sub (fn tm =>
  if can (match_term pat) tm
  then tm |> rator |> rand else fail())

val remove_disj = sub (fn tm => if is_disj tm then tm |> rator |> rand else fail())

val evaluate_ind = save_thm("evaluate_ind",let
  val raw_ind = evaluate_ind
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    NTAC 3 STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ Tactical.REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    \\ TRY
     (FIRST_X_ASSUM (MATCH_MP_TAC) \\ REPEAT STRIP_TAC \\ fs []
      \\ IMP_RES_TAC evaluate_clock
      \\ IMP_RES_TAC check_clock_thm \\ fs []
      \\ `s1.clock <= s.clock` by (fs [dec_clock_def] \\ DECIDE_TAC)
      \\ IMP_RES_TAC check_clock_thm \\ fs [])
    \\ TRY
     (FIRST_X_ASSUM (MATCH_MP_TAC)
      \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ fs []
      \\ IMP_RES_TAC evaluate_clock
      \\ IMP_RES_TAC check_clock_thm \\ fs []
      \\ FIRST_X_ASSUM (MATCH_MP_TAC)
      \\ DECIDE_TAC)
    \\ TRY
     (FIRST_X_ASSUM (MATCH_MP_TAC)
      \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ fs []
      \\ IMP_RES_TAC evaluate_clock \\ IMP_RES_TAC LESS_EQ_TRANS
      \\ IMP_RES_TAC check_clock_thm \\ fs []
      \\ FIRST_X_ASSUM (MATCH_MP_TAC)
      \\ DECIDE_TAC)
   \\ TRY
     (IMP_RES_TAC evaluate_clock
      \\ fs [dec_clock_def]
      \\ IMP_RES_TAC (DECIDE ``n <= m - k:num ==> n <= m``)
      \\ IMP_RES_TAC LESS_EQ_TRANS
      \\ IMP_RES_TAC check_clock_thm \\ fs []))
  in ind end);

val evaluate_def = save_thm("evaluate_def",let
  val goal = evaluate_def |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val thm = prove(goal,
    REPEAT STRIP_TAC
    \\ SIMP_TAC std_ss [Once evaluate_def]
    \\ BasicProvers.EVERY_CASE_TAC
    \\ IMP_RES_TAC evaluate_check_clock \\ fs []
    \\ SRW_TAC [] []
    \\ IMP_RES_TAC evaluate_clock
    \\ fs [check_clock_def,dec_clock_def]
    \\ TRY (`F` by DECIDE_TAC)
    \\ IMP_RES_TAC LESS_EQ_TRANS
    \\ fs [check_clock_def])
  in thm end);

val _ = export_theory()

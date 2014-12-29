open HolKernel Parse boolLib bossLib; val _ = new_theory "callLang";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs bvlTheory;

(* CallLang -- introduces the code table *)

(* --- Syntax of CallLang --- *)

(* CallLang uses De Bruijn indices so there is no need for a variable
   name in the let-expression. *)

val _ = Datatype `
  call_exp = Var num
           | If call_exp call_exp call_exp
           | Let (call_exp list) call_exp
           | Raise call_exp
           | Handle call_exp call_exp
           | Tick call_exp
           | Call num (call_exp list)
           | App call_exp call_exp
           | Fn call_exp
           | Letrec (call_exp list) call_exp
           | Op bvl_op (call_exp list) `

(* --- Semantics of CallLang --- *)

val _ = Datatype `
  call_val =
    Number int
  | Block num (call_val list)
  | RefPtr num
  | Closure (call_val list) call_exp
  | Recclosure (call_val list) (call_exp list) num`

val _ = Datatype `
  call_res = Result 'a
           | Exception call_val
           | TimeOut
           | Error `

val _ = Datatype `
  call_ref = ValueArray (call_val list)`

val _ = Datatype `
  call_state =
    <| globals : (call_val option) list
     ; refs    : num |-> call_ref
     ; clock   : num
     ; code    : num |-> (num # call_exp)
     ; output  : string |> `

(* helper functions *)

val get_global_def = Define `
  get_global n globals =
    if n < LENGTH globals then SOME (EL n globals) else NONE`

val bool_to_val_def = Define `
  (bool_to_val T = Block 1 []) /\
  (bool_to_val F = Block 0 [])`;

val call_equal_def = tDefine "call_equal" `
  (call_equal x (y:call_val) =
     case x of
     | Number i =>
         (case y of
          | Number j => Eq_val (i = j)
          | _ => Eq_type_error)
     | Block t1 xs =>
         (case y of
          | Block t2 ys => if (t1 = t2) /\ (LENGTH xs = LENGTH ys) then
                             call_equal_list xs ys
                           else Eq_val F
          | _ => Eq_type_error)
     | RefPtr i =>
         (case y of
          | RefPtr j => Eq_val (i = j)
          | _ => Eq_type_error)
     | _ =>
         (case y of
          | Number _ => Eq_type_error
          | Block _ _ => Eq_type_error
          | RefPtr _ => Eq_type_error
          | _ => Eq_closure)) /\
  (call_equal_list [] [] = Eq_val T) /\
  (call_equal_list (x::xs) (y::ys) =
     case call_equal x y of
     | Eq_val T => call_equal_list xs ys
     | res => res) /\
  (call_equal_list _ _ = Eq_val F)`
 (WF_REL_TAC `measure (\x. case x of INL (v,_) => call_val_size v
                                   | INR (vs,_) => call_val1_size vs)`)

val call_to_chars_def = Define `
  (call_to_chars [] ac = SOME (REVERSE ac)) /\
  (call_to_chars (((Number i):call_val)::vs) ac =
     if 0 <= i /\ i < 256 then
       call_to_chars vs (STRING (CHR (Num (ABS i))) ac)
     else NONE) /\
  (call_to_chars _ _ = NONE)`

val call_to_string_def = Define `
  (call_to_string (Number i) = SOME (int_to_string i)) /\
  (call_to_string (Block n vs) =
   (if n = 0 then SOME "false"
    else if n = 1 then SOME "true"
    else if n = 2 then SOME "()"
    else if n = 3 then SOME "<vector>"
    else if n = 4 then
      case call_to_chars vs "" of
        NONE => NONE
      | SOME cs => SOME (string_to_string (IMPLODE cs))
    else SOME "<constructor>")) /\
  (call_to_string ((RefPtr v0) : call_val) = SOME "<ref>") /\
  (call_to_string _ = SOME "<fn>")`;

val tEvalOp_def = Define `
  tEvalOp (op:bvl_op) (vs:call_val list) (s:call_state) =
    case (op,vs) of
    | (Global n,[]:call_val list) =>
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
    | (Const i,[]) => SOME (Number i, s)
    | (Cons tag,xs) => SOME (Block tag xs, s)
    | (El n,[Block tag xs]) =>
        if n < LENGTH xs then SOME (EL n xs, s) else NONE
    | (TagEq n,[Block tag xs]) =>
        SOME (bool_to_val (tag = n),s)
    | (Equal,[x1;x2]) =>
        (case call_equal x1 x2 of
         | Eq_val b => SOME (bool_to_val b, s)
         | Eq_closure => SOME (Number 0, s)
         | _ => NONE)
    | (IsBlock,[Number i]) => SOME (bool_to_val F, s)
    | (IsBlock,[RefPtr ptr]) => SOME (bool_to_val F, s)
    | (IsBlock,[Block tag ys]) => SOME (bool_to_val T, s)
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
    | (Add,[Number n1; Number n2]) => SOME (Number (n1 + n2),s)
    | (Sub,[Number n1; Number n2]) => SOME (Number (n1 - n2),s)
    | (Mult,[Number n1; Number n2]) => SOME (Number (n1 * n2),s)
    | (Div,[Number n1; Number n2]) =>
         if n2 = 0 then NONE else SOME (Number (n1 / n2),s)
    | (Mod,[Number n1; Number n2]) =>
         if n2 = 0 then NONE else SOME (Number (n1 % n2),s)
    | (Less,[Number n1; Number n2]) =>
         SOME (bool_to_val (n1 < n2),s)
    | (Print, [x]) =>
        (case call_to_string x of
         | SOME str => SOME (x, s with output := s.output ++ str)
         | NONE => NONE)
    | (PrintC c, []) =>
          SOME (Number 0, s with output := s.output ++ [c])
    | _ => NONE`

val dec_clock_def = Define `
  dec_clock (s:call_state) = s with clock := s.clock - 1`;

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
   defined to evaluate a list of call_exp expressions. *)

val dest_closure_def = Define `
  dest_closure f x =
    case f of
    | Closure env exp => SOME (exp,x::env)
    | Recclosure env fns i =>
        (if LENGTH fns <= i then NONE else
           let exp = EL i fns in
           let rs = GENLIST (Recclosure env fns) (LENGTH fns) in
             SOME (exp,x::rs++env))
    | _ => NONE`;

val build_recc_def = Define `
  build_recc env fns =
    GENLIST (Recclosure env fns) (LENGTH fns)`

val tEval_def = tDefine "tEval" `
  (tEval ([],env:call_val list,s:call_state) = (Result [],s)) /\
  (tEval (x::y::xs,env,s) =
     case tEval ([x],env,s) of
     | (Result v1,s1) =>
         (case tEval (y::xs,env,check_clock s1 s) of
          | (Result vs,s2) => (Result (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (tEval ([Var n],env,s) =
     if n < LENGTH env then (Result [EL n env],s) else (Error,s)) /\
  (tEval ([If x1 x2 x3],env,s) =
     case tEval ([x1],env,s) of
     | (Result vs,s1) =>
          if Block 1 [] = HD vs then tEval([x2],env,check_clock s1 s) else
          if Block 0 [] = HD vs then tEval([x3],env,check_clock s1 s) else
            (Error,s1)
     | res => res) /\
  (tEval ([Let xs x2],env,s) =
     case tEval (xs,env,s) of
     | (Result vs,s1) => tEval ([x2],vs++env,check_clock s1 s)
     | res => res) /\
  (tEval ([Raise x1],env,s) =
     case tEval ([x1],env,s) of
     | (Result vs,s) => (Exception (HD vs),s)
     | res => res) /\
  (tEval ([Handle x1 x2],env,s1) =
     case tEval ([x1],env,s1) of
     | (Exception v,s) => tEval ([x2],v::env,check_clock s s1)
     | res => res) /\
  (tEval ([Op op xs],env,s) =
     case tEval (xs,env,s) of
     | (Result vs,s) => (case tEvalOp op vs s of
                          | NONE => (Error,s)
                          | SOME (v,s) => (Result [v],s))
     | res => res) /\
  (tEval ([Fn exp],env,s) =
     (Result [Closure env exp], s)) /\
  (tEval ([Letrec fns exp],env,s) =
     tEval ([exp],build_recc env fns ++ env,s)) /\
  (tEval ([App x1 x2],env,s) =
     case tEval ([x1],env,s) of
     | (Result y1,s1) =>
         (case tEval ([x2],env,check_clock s1 s) of
          | (Result y2,s2) =>
             (case dest_closure (HD y1) (HD y2) of
              | NONE => (Error,s2)
              | SOME (exp,env1) =>
                  if (s2.clock = 0) \/ (s1.clock = 0) \/ (s.clock = 0)
                  then (TimeOut,s2)
                  else tEval ([exp],env1,dec_clock (check_clock s2 s)))
          | res => res)
     | res => res) /\
  (tEval ([Tick x],env,s) =
     if s.clock = 0 then (TimeOut,s) else tEval ([x],env,dec_clock s)) /\
  (tEval ([Call dest xs],env,s1) =
     case tEval (xs,env,s1) of
     | (Result vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Error,s)
          | SOME (args,exp) =>
              if (s.clock = 0) \/ (s1.clock = 0) then (TimeOut,s) else
                  tEval ([exp],args,dec_clock (check_clock s s1)))
     | res => res)`
 (WF_REL_TAC `(inv_image (measure I LEX measure call_exp1_size)
                            (\(xs,env,s). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
  \\ Cases_on `s.clock <= s2.clock`
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ DECIDE_TAC);

(* We prove that the clock never increases. *)

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val tEvalOp_const = store_thm("tEvalOp_const",
  ``(tEvalOp op args s1 = SOME (res,s2)) ==>
    (s2.clock = s1.clock) /\ (s2.code = s1.code)``,
  SIMP_TAC std_ss [tEvalOp_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val tEval_clock = store_thm("tEval_clock",
  ``!xs env s1 vs s2.
      (tEval (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "tEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [tEval_def]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC tEvalOp_const
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ TRY DECIDE_TAC
  \\ POP_ASSUM MP_TAC
  \\ TRY (REPEAT (POP_ASSUM (K ALL_TAC))
          \\ SRW_TAC [] [check_clock_def] \\ DECIDE_TAC)
  \\ rfs [] \\ fs [] \\ rfs [check_clock_def]
  \\ Cases_on `r'.clock <= s.clock` \\ fs [] \\ DECIDE_TAC);

val tEval_check_clock = prove(
  ``!xs env s1 vs s2.
      (tEval (xs,env,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [tEval_clock,check_clock_thm]);

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

val tEval_ind = save_thm("tEval_ind",let
  val raw_ind = fetch "-" "tEval_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (Q.PAT_ASSUM `!dest xs env s1. bb ==> bbb` MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC tEval_clock
           \\ `s1.clock <> 0` by DECIDE_TAC
           \\ SRW_TAC [] []
           \\ FULL_SIMP_TAC (srw_ss()) []
           \\ IMP_RES_TAC tEval_check_clock
           \\ FULL_SIMP_TAC std_ss [])
    \\ TRY (FIRST_X_ASSUM (MATCH_MP_TAC)
        \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
        \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
        \\ IMP_RES_TAC tEval_clock
        \\ FULL_SIMP_TAC std_ss [check_clock_thm] \\ NO_TAC)
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC tEval_clock
    \\ IMP_RES_TAC check_clock_thm
    \\ TRY (`s2.clock <= s.clock` by DECIDE_TAC)
    \\ IMP_RES_TAC check_clock_thm
    \\ fs [check_clock_thm]
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ DECIDE_TAC)
  in ind end);

val tEval_def = save_thm("tEval_def",let
  val tm = fetch "-" "tEval_AUX_def"
           |> concl |> rand |> dest_abs |> snd |> rand |> rand
  val tm = ``^tm tEval (xs,env,s)``
  val rhs = SIMP_CONV std_ss [EVAL ``pair_CASE (x,y) f``] tm |> concl |> rand
  val goal = ``!xs env s. tEval (xs,env,s) = ^rhs`` |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    recInduct tEval_ind
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ TRY (SIMP_TAC std_ss [Once tEval_def] \\ NO_TAC)
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [Once tEval_def]
    \\ Cases_on `tEval (xs,env,s1)`
    \\ Cases_on `tEval (xs,env,s)`
    \\ Cases_on `tEval ([x],env,s)`
    \\ Cases_on `tEval ([x1],env,s)`
    \\ Cases_on `tEval ([x2],env,s)`
    \\ Cases_on `tEval ([x1],env,s1)`
    \\ Cases_on `tEval ([x2],env,s1)`
    \\ IMP_RES_TAC tEval_check_clock
    \\ IMP_RES_TAC tEval_clock
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``pair_CASE (x,y) f``]
    \\ Cases_on `r.clock = 0` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `s1.clock = 0` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q'''` \\ fs []
    \\ Cases_on `tEval ([x2],env,r''')` \\ fs []
    \\ Cases_on `q'''` \\ fs []
    \\ IMP_RES_TAC tEval_check_clock
    \\ IMP_RES_TAC tEval_clock
    \\ IMP_RES_TAC check_clock_thm
    \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ rfs []
    \\ SRW_TAC [] []
    \\ fs [check_clock_def] \\ rfs []
    \\ SRW_TAC [] []
    \\ `F` by DECIDE_TAC)
  val new_def = tEval_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* lemmas *)

val tEval_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case tEval (xs,s,env) of (Result res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC tEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [tEval_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("tEval_LENGTH", tEval_LENGTH);

val tEval_IMP_LENGTH = store_thm("tEval_IMP_LENGTH",
  ``(tEval (xs,s,env) = (Result res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL tEval_LENGTH) \\ fs []);

val tEval_SING = store_thm("tEval_SING",
  ``(tEval ([x],s,env) = (Result r,s2)) ==> ?r1. r = [r1]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC tEval_IMP_LENGTH
  \\ Cases_on `r` \\ fs [] \\ Cases_on `t` \\ fs []);

val tEval_CONS = store_thm("tEval_CONS",
  ``tEval (x::xs,env,s) =
      case tEval ([x],env,s) of
      | (Result v,s2) =>
         (case tEval (xs,env,s2) of
          | (Result vs,s1) => (Result (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ fs [tEval_def]
  \\ Cases_on `tEval ([x],env,s)` \\ fs [tEval_def]
  \\ Cases_on `q` \\ fs [tEval_def]
  \\ IMP_RES_TAC tEval_IMP_LENGTH
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val tEval_SNOC = store_thm("tEval_SNOC",
  ``!xs env s x.
      tEval (SNOC x xs,env,s) =
      case tEval (xs,env,s) of
      | (Result vs,s2) =>
         (case tEval ([x],env,s2) of
          | (Result v,s1) => (Result (vs ++ v),s1)
          | t => t)
      | t => t``,
  Induct THEN1
   (fs [SNOC_APPEND,tEval_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `tEval ([x],env,s)` \\ Cases_on `q` \\ fs [])
  \\ fs [SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [tEval_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `tEval ([h],env,s)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `tEval (xs,env,r)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `tEval ([x],env,r')` \\ Cases_on `q` \\ fs [tEval_def]
  \\ IMP_RES_TAC tEval_IMP_LENGTH
  \\ Cases_on `a''` \\ fs [LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ fs []);

(* clean up *)

val _ = map delete_binding ["tEval_AUX_def", "tEval_primitive_def"];

val _ = export_theory();

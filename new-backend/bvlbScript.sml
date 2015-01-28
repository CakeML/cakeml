open HolKernel Parse boolLib bossLib;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory sptreeTheory lcsymtacs bvlTheory;

val _ = new_theory "bvlb";

infix \\ val op \\ = op THEN;

val _ = type_abbrev("num_map",``:'a spt``);
val _ = type_abbrev("num_set",``:unit spt``);

(* BVLB is an alternative semantics for BVL that does left-to-right evaluation
   for the arguments of primitive operators. It is only used as a stepping stone
   on the way to translation to Bytecode. The compiler from BVL via the new
   backend will not use BVLB. *)

val check_clock_thm = prove(
  ``(check_clock s1 s2).clock <= s2.clock /\
    (s1.clock <= s2.clock ==> (check_clock s1 s2 = s1))``,
  SRW_TAC [] [check_clock_def])

val check_clock_lemma = prove(
  ``b ==> ((check_clock s1 s).clock < s.clock \/
          ((check_clock s1 s).clock = s.clock) /\ b)``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val bbEval_def = tDefine "bbEval" `
  (bbEval ([],env,s:bvl_state) = (Result [],s)) /\
  (bbEval (x::y::xs,env,s) =
     case bbEval ([x],env,s) of
     | (Result v1,s1) =>
         (case bbEval (y::xs,env,check_clock s1 s) of
          | (Result vs,s2) => (Result (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (bbEval ([Var n],env,s) =
     if n < LENGTH env then (Result [EL n env],s) else (Error,s)) /\
  (bbEval ([If x1 x2 x3],env,s) =
     case bbEval ([x1],env,s) of
     | (Result vs,s1) =>
          if bool_to_val T = HD vs then bbEval([x2],env,check_clock s1 s) else
          if bool_to_val F = HD vs then bbEval([x3],env,check_clock s1 s) else
            (Error,s1)
     | res => res) /\
  (bbEval ([Let xs x2],env,s) =
     case bbEval (xs,env,s) of
     | (Result vs,s1) => bbEval ([x2],vs++env,check_clock s1 s)
     | res => res) /\
  (bbEval ([Raise x1],env,s) =
     case bbEval ([x1],env,s) of
     | (Result vs,s) => (Exception (HD vs),s)
     | res => res) /\
  (bbEval ([Handle x1 x2],env,s1) =
     case bbEval ([x1],env,s1) of
     | (Exception v,s) => bbEval ([x2],v::env,check_clock s s1)
     | res => res) /\
  (bbEval ([Op op xs],env,s) =
     case bbEval (xs,env,s) of
     | (Result vs,s) => (case bEvalOp op vs s of
                          | NONE => (Error,s)
                          | SOME (v,s) => (Result [v],s))
     | res => res) /\
  (bbEval ([Tick x],env,s) =
     if s.clock = 0 then (TimeOut,s) else bbEval ([x],env,dec_clock 1 s)) /\
  (bbEval ([Call ticks dest xs],env,s1) =
     case bbEval (xs,env,s1) of
     | (Result vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Error,s)
          | SOME (args,exp) =>
              if (s.clock < ticks + 1) \/ (s1.clock < ticks + 1) then (TimeOut,s with clock := 0) else
                  bbEval ([exp],args,dec_clock (ticks + 1) (check_clock s s1)))
     | res => res)`
 (WF_REL_TAC `(inv_image (measure I LEX measure bvl_exp1_size)
                            (\(xs,env,s). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val bbEval_clock = store_thm("bbEval_clock",
  ``!xs env s1 vs s2.
      (bbEval (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "bbEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [bbEval_def]
  \\ FULL_SIMP_TAC std_ss [] \\ BasicProvers.EVERY_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC bEvalOp_const
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ TRY DECIDE_TAC
  \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val bbEval_check_clock = prove(
  ``!xs env s1 vs s2.
      (bbEval (xs,env,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [bbEval_clock,check_clock_thm]);

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

val bbEval_ind = save_thm("bbEval_ind",let
  val raw_ind = fetch "-" "bbEval_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (Q.PAT_ASSUM `!ticks dest xs env s1. bb ==> bbb` MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC bbEval_clock
           \\ `¬(s1.clock < ticks + 1)` by DECIDE_TAC
           \\ SRW_TAC [] []
           \\ FULL_SIMP_TAC (srw_ss()) []
           \\ IMP_RES_TAC bbEval_check_clock
           \\ FULL_SIMP_TAC std_ss [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC bbEval_clock
    \\ FULL_SIMP_TAC std_ss [check_clock_thm])
  in ind end);

val bbEval_def = save_thm("bbEval_def",let
  val tm = fetch "-" "bbEval_AUX_def"
           |> concl |> rand |> dest_abs |> snd |> rand |> rand
  val tm = ``^tm bbEval (xs,env,s)``
  val rhs = SIMP_CONV std_ss [EVAL ``pair_CASE (x,y) f``] tm |> concl |> rand
  val goal = ``!xs env s. bbEval (xs,env,s) = ^rhs`` |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    recInduct bbEval_ind
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ TRY (SIMP_TAC std_ss [Once bbEval_def] \\ NO_TAC)
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [Once bbEval_def]
    \\ Cases_on `bbEval (xs,env,s1)`
    \\ Cases_on `bbEval (xs,env,s)`
    \\ Cases_on `bbEval ([x],env,s)`
    \\ Cases_on `bbEval ([x1],env,s)`
    \\ Cases_on `bbEval ([x2],env,s)`
    \\ Cases_on `bbEval ([x1],env,s1)`
    \\ Cases_on `bbEval ([x2],env,s1)`
    \\ IMP_RES_TAC bbEval_check_clock
    \\ IMP_RES_TAC bbEval_clock
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``pair_CASE (x,y) f``]
    \\ Cases_on `r.clock < ticks + 1` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `s1.clock < ticks + 1` \\ FULL_SIMP_TAC std_ss [] >>
    `r.clock = s1.clock` by decide_tac >>
    fs [])
  val new_def = bbEval_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* lemmas *)

val bbEval_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case bbEval (xs,s,env) of (Result res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC bbEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [bbEval_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("bbEval_LENGTH", bbEval_LENGTH);

val bbEval_IMP_LENGTH = store_thm("bbEval_IMP_LENGTH",
  ``(bbEval (xs,s,env) = (Result res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bbEval_LENGTH) \\ fs []);

val bbEval_CONS = store_thm("bbEval_CONS",
  ``bbEval (x::xs,env,s) =
      case bbEval ([x],env,s) of
      | (Result v,s2) =>
         (case bbEval (xs,env,s2) of
          | (Result vs,s1) => (Result (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ fs [bbEval_def]
  \\ Cases_on `bbEval ([x],env,s)` \\ fs [bbEval_def]
  \\ Cases_on `q` \\ fs [bbEval_def]
  \\ IMP_RES_TAC bbEval_IMP_LENGTH
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val bbEval_SNOC = store_thm("bbEval_SNOC",
  ``!xs env s x.
      bbEval (SNOC x xs,env,s) =
      case bbEval (xs,env,s) of
      | (Result vs,s2) =>
         (case bbEval ([x],env,s2) of
          | (Result v,s1) => (Result (vs ++ v),s1)
          | t => t)
      | t => t``,
  Induct THEN1
   (fs [SNOC_APPEND,bbEval_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `bbEval ([x],env,s)` \\ Cases_on `q` \\ fs [])
  \\ fs [SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [bbEval_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `bbEval ([h],env,s)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `bbEval (xs,env,r)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `bbEval ([x],env,r')` \\ Cases_on `q` \\ fs [bbEval_def]
  \\ IMP_RES_TAC bbEval_IMP_LENGTH
  \\ Cases_on `a''` \\ fs [LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ fs []);

val bbEval_APPEND = store_thm("bbEval_APPEND",
  ``!xs env s ys.
      bbEval (xs ++ ys,env,s) =
      case bbEval (xs,env,s) of
        (Result vs,s2) =>
          (case bbEval (ys,env,s2) of
             (Result ws,s1) => (Result (vs ++ ws),s1)
           | res => res)
      | res => res``,
  Induct \\ fs [APPEND,bbEval_def] \\ REPEAT STRIP_TAC
  THEN1 REPEAT BasicProvers.CASE_TAC
  \\ ONCE_REWRITE_TAC [bbEval_CONS]
  \\ REPEAT BasicProvers.CASE_TAC \\ fs []);

val bbEval_code = store_thm("bbEval_code",
  ``!xs env s1 vs s2.
      (bbEval (xs,env,s1) = (vs,s2)) ==> s2.code = s1.code``,
  recInduct bbEval_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [bbEval_def]
  \\ FULL_SIMP_TAC std_ss []
  \\ BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [dec_clock_def]
  \\ Cases_on`q`  \\ FULL_SIMP_TAC (srw_ss())[]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ SRW_TAC[][]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ IMP_RES_TAC bEvalOp_const \\ SRW_TAC[][]
  \\ POP_ASSUM MP_TAC
  \\ BasicProvers.CASE_TAC \\ FULL_SIMP_TAC (srw_ss())[]
  \\ SRW_TAC[][] \\ SRW_TAC[][dec_clock_def]);

val mk_tick_def = Define `
  mk_tick n e = FUNPOW Tick n e : bvl_exp`;

val bbEval_mk_tick = Q.store_thm ("bbEval_mk_tick",
`!exp env s n.
  bbEval ([mk_tick n exp], env, s) =
    if s.clock < n then
      (TimeOut, s with clock := 0)
    else
      bbEval ([exp], env, dec_clock n s)`,
 Induct_on `n` >>
 rw [mk_tick_def, bbEval_def, dec_clock_def, FUNPOW] >>
 fs [mk_tick_def, bbEval_def, dec_clock_def] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def, ADD1]
 >- (`s with clock := s.clock = s`
            by rw [bvl_state_explode] >>
     rw [])
 >- (`s.clock = n` by decide_tac >>
     fs []));

(* clean up *)

val _ = map delete_binding ["bbEval_AUX_def", "bbEval_primitive_def"];

val _ = export_theory();

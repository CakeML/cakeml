open HolKernel Parse boolLib bossLib; val _ = new_theory "closLang";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs bvlTheory;

(* ClosLang -- compilation from this lanugage removes closures, gets to BVL *)

(* --- Syntax of ClosLang --- *)

(* ClosLang uses De Bruijn indices so there is no need for a variable
   name in the let-expression. *)

val _ = Datatype `
  clos_exp = Var num
           | If clos_exp clos_exp clos_exp
           | Let (clos_exp list) clos_exp
           | Raise clos_exp
           | Handle clos_exp clos_exp
           | Tick clos_exp
           | Call num (clos_exp list)
           | App clos_exp clos_exp
           | Fn (num list) clos_exp
           (* TODO: add Letrec *)
           | Op bvl_op (clos_exp list) `

(* --- Semantics of ClosLang --- *)

val _ = Datatype `
  clos_val =
    Number int
  | Block num (clos_val list)
  | RefPtr num
  | Closure (clos_val list) clos_exp
  (* TODO: add Recclosure *)`

val _ = Datatype `
  clos_res = Result 'a
           | Exception clos_val
           | TimeOut
           | Error `

val _ = Datatype `
  clos_state =
    <| globals : (clos_val option) list
     ; refs    : num |-> clos_val (* TODO: refs are more complicated *)
     ; clock   : num
     ; code    : num |-> (num # clos_exp)
     ; output  : string |> `

(* helper functions *)

val cEvalOp_def = Define `
  cEvalOp op vs (s:clos_state) =
    case (op,vs) of
    | (Add,[Number n1; Number n2]) => SOME ((Number (n1 + n2)) :clos_val,s)
    | _ => NONE`;

val dec_clock_def = Define `
  dec_clock (s:clos_state) = s with clock := s.clock - 1`;

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

val dest_closure_def = Define `
  dest_closure f x =
    case f of
    | Closure env exp => SOME (exp,x::env)
    | _ => NONE`;

val cEval_def = tDefine "cEval" `
  (cEval ([],env:clos_val list,s:clos_state) = (Result [],s)) /\
  (cEval (x::y::xs,env,s) =
     case cEval ([x],env,s) of
     | (Result v1,s1) =>
         (case cEval (y::xs,env,check_clock s1 s) of
          | (Result vs,s2) => (Result (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (cEval ([Var n],env,s) =
     if n < LENGTH env then (Result [EL n env],s) else (Error,s)) /\
  (cEval ([If x1 x2 x3],env,s) =
     case cEval ([x1],env,s) of
     | (Result vs,s1) =>
          if Block 1 [] = HD vs then cEval([x2],env,check_clock s1 s) else
          if Block 0 [] = HD vs then cEval([x3],env,check_clock s1 s) else
            (Error,s1)
     | res => res) /\
  (cEval ([Let xs x2],env,s) =
     case cEval (xs,env,s) of
     | (Result vs,s1) => cEval ([x2],vs++env,check_clock s1 s)
     | res => res) /\
  (cEval ([Raise x1],env,s) =
     case cEval ([x1],env,s) of
     | (Result vs,s) => (Exception (HD vs),s)
     | res => res) /\
  (cEval ([Handle x1 x2],env,s1) =
     case cEval ([x1],env,s1) of
     | (Exception v,s) => cEval ([x2],v::env,check_clock s s1)
     | res => res) /\
  (cEval ([Op op xs],env,s) =
     case cEval (xs,env,s) of
     | (Result vs,s) => (case cEvalOp op vs s of
                          | NONE => (Error,s)
                          | SOME (v,s) => (Result [v],s))
     | res => res) /\
  (cEval ([Fn vs exp],env,s) =
     case lookup_vars vs env of
     | NONE => (Error,s)
     | SOME env' => (Result [Closure env' exp], s)) /\
  (cEval ([App x1 x2],env,s) =
     case cEval ([x1],env,s) of
     | (Result y1,s1) =>
         (case cEval ([x2],env,check_clock s1 s) of
          | (Result y2,s2) =>
             (case dest_closure (HD y1) (HD y2) of
              | NONE => (Error,s2)
              | SOME (exp,env1) =>
                  if (s2.clock = 0) \/ (s1.clock = 0) \/ (s.clock = 0)
                  then (TimeOut,s2)
                  else cEval ([exp],env1,dec_clock (check_clock s2 s)))
          | res => res)
     | res => res) /\
  (cEval ([Tick x],env,s) =
     if s.clock = 0 then (TimeOut,s) else cEval ([x],env,dec_clock s)) /\
  (cEval ([Call dest xs],env,s1) =
     case cEval (xs,env,s1) of
     | (Result vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Error,s)
          | SOME (args,exp) =>
              if (s.clock = 0) \/ (s1.clock = 0) then (TimeOut,s) else
                  cEval ([exp],args,dec_clock (check_clock s s1)))
     | res => res)`
 (WF_REL_TAC `(inv_image (measure I LEX measure clos_exp1_size)
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

val cEvalOp_const = store_thm("cEvalOp_const",
  ``(cEvalOp op args s1 = SOME (res,s2)) ==>
    (s2.clock = s1.clock) /\ (s2.code = s1.code)``,
  SIMP_TAC std_ss [cEvalOp_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val cEval_clock = store_thm("cEval_clock",
  ``!xs env s1 vs s2.
      (cEval (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "cEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [cEval_def]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC cEvalOp_const
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ TRY DECIDE_TAC
  \\ POP_ASSUM MP_TAC
  \\ TRY (REPEAT (POP_ASSUM (K ALL_TAC))
          \\ SRW_TAC [] [check_clock_def] \\ DECIDE_TAC)
  \\ rfs [] \\ fs [] \\ rfs [check_clock_def]
  \\ Cases_on `r'.clock <= s.clock` \\ fs [] \\ DECIDE_TAC);

val cEval_check_clock = prove(
  ``!xs env s1 vs s2.
      (cEval (xs,env,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [cEval_clock,check_clock_thm]);

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

val cEval_ind = save_thm("cEval_ind",let
  val raw_ind = fetch "-" "cEval_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (Q.PAT_ASSUM `!dest xs env s1. bb ==> bbb` MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC cEval_clock
           \\ `s1.clock <> 0` by DECIDE_TAC
           \\ SRW_TAC [] []
           \\ FULL_SIMP_TAC (srw_ss()) []
           \\ IMP_RES_TAC cEval_check_clock
           \\ FULL_SIMP_TAC std_ss [])
    \\ TRY (FIRST_X_ASSUM (MATCH_MP_TAC)
        \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
        \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
        \\ IMP_RES_TAC cEval_clock
        \\ FULL_SIMP_TAC std_ss [check_clock_thm] \\ NO_TAC)
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC cEval_clock
    \\ IMP_RES_TAC check_clock_thm
    \\ TRY (`s2.clock <= s.clock` by DECIDE_TAC)
    \\ IMP_RES_TAC check_clock_thm
    \\ fs [check_clock_thm]
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ DECIDE_TAC)
  in ind end);

val cEval_def = save_thm("cEval_def",let
  val tm = fetch "-" "cEval_AUX_def"
           |> concl |> rand |> dest_abs |> snd |> rand |> rand
  val tm = ``^tm cEval (xs,env,s)``
  val rhs = SIMP_CONV std_ss [EVAL ``pair_CASE (x,y) f``] tm |> concl |> rand
  val goal = ``!xs env s. cEval (xs,env,s) = ^rhs`` |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    recInduct cEval_ind
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ TRY (SIMP_TAC std_ss [Once cEval_def] \\ NO_TAC)
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [Once cEval_def]
    \\ Cases_on `cEval (xs,env,s1)`
    \\ Cases_on `cEval (xs,env,s)`
    \\ Cases_on `cEval ([x],env,s)`
    \\ Cases_on `cEval ([x1],env,s)`
    \\ Cases_on `cEval ([x2],env,s)`
    \\ Cases_on `cEval ([x1],env,s1)`
    \\ Cases_on `cEval ([x2],env,s1)`
    \\ IMP_RES_TAC cEval_check_clock
    \\ IMP_RES_TAC cEval_clock
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``pair_CASE (x,y) f``]
    \\ Cases_on `r.clock = 0` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `s1.clock = 0` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `q'''` \\ fs []
    \\ Cases_on `cEval ([x2],env,r''')` \\ fs []
    \\ Cases_on `q'''` \\ fs []
    \\ IMP_RES_TAC cEval_check_clock
    \\ IMP_RES_TAC cEval_clock
    \\ IMP_RES_TAC check_clock_thm
    \\ REPEAT BasicProvers.CASE_TAC \\ fs [] \\ rfs []
    \\ SRW_TAC [] []
    \\ fs [check_clock_def] \\ rfs []
    \\ SRW_TAC [] []
    \\ `F` by DECIDE_TAC)
  val new_def = cEval_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* lemmas *)

val cEval_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case cEval (xs,s,env) of (Result res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC cEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [cEval_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("cEval_LENGTH", cEval_LENGTH);

val cEval_IMP_LENGTH = store_thm("cEval_IMP_LENGTH",
  ``(cEval (xs,s,env) = (Result res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL cEval_LENGTH) \\ fs []);

val cEval_SING = store_thm("cEval_SING",
  ``(cEval ([x],s,env) = (Result r,s2)) ==> ?r1. r = [r1]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC cEval_IMP_LENGTH
  \\ Cases_on `r` \\ fs [] \\ Cases_on `t` \\ fs []);

val cEval_CONS = store_thm("cEval_CONS",
  ``cEval (x::xs,env,s) =
      case cEval ([x],env,s) of
      | (Result v,s2) =>
         (case cEval (xs,env,s2) of
          | (Result vs,s1) => (Result (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ fs [cEval_def]
  \\ Cases_on `cEval ([x],env,s)` \\ fs [cEval_def]
  \\ Cases_on `q` \\ fs [cEval_def]
  \\ IMP_RES_TAC cEval_IMP_LENGTH
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val cEval_SNOC = store_thm("cEval_SNOC",
  ``!xs env s x.
      cEval (SNOC x xs,env,s) =
      case cEval (xs,env,s) of
      | (Result vs,s2) =>
         (case cEval ([x],env,s2) of
          | (Result v,s1) => (Result (vs ++ v),s1)
          | t => t)
      | t => t``,
  Induct THEN1
   (fs [SNOC_APPEND,cEval_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `cEval ([x],env,s)` \\ Cases_on `q` \\ fs [])
  \\ fs [SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [cEval_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `cEval ([h],env,s)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `cEval (xs,env,r)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `cEval ([x],env,r')` \\ Cases_on `q` \\ fs [cEval_def]
  \\ IMP_RES_TAC cEval_IMP_LENGTH
  \\ Cases_on `a''` \\ fs [LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ fs []);

(* clean up *)

val _ = map delete_binding ["cEval_AUX_def", "cEval_primitive_def"];

val _ = export_theory();

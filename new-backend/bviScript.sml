open HolKernel Parse boolLib bossLib;

val _ = new_theory "bvi";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory sptreeTheory lcsymtacs bvlTheory;

infix \\ val op \\ = op THEN;

(* BVI = bytecode-value intermediate language *)

(* BVI is a stepping stone on the way from BVL to BVP. BVI is almost
   identical to BVL. The main differences are:

    - The Handle (exception) construct from BVL has been merged into
      the Call construct. The reason we want to do this is that we
      want each function in BVI (and the following intermediate
      languages) to only operate within one stack frame. The execution
      of the body of the Handle construct is to execute in a separate
      stack frame. To keep things simple and uniform, we merge all
      stack-frame creation into the Call construct. Note that BVL and
      BVI have no concept of stack frames. However, the next language,
      BVP, does have stack frames. BVI is a nice high-level language
      where the Handle construct can cleanly be eliminated.

    - Each creation of a number constant must only produce constants
      that will fit into a machine word. The previous language, BVL,
      allows any size of integer to be constructed immediately. In
      BVI, we compile creation of very large constants into creation
      of small constants, and plug these together using +, - and *.

    - BVI also doesn't have the 'globals' state component from BVL.
      BVI implements the globals using a (dynamically extended) wide
      reference. *)


(* --- Syntax of BVI --- *)

val _ = Datatype `
  bvi_exp = Var num
          | If bvi_exp bvi_exp bvi_exp
          | Let (bvi_exp list) bvi_exp
          | Raise bvi_exp
          | Tick bvi_exp
          | Call num (num option) (bvi_exp list) (bvi_exp option)
          | Op bvl_op (bvi_exp list) `

(* --- Semantics of BVI --- *)

val _ = Datatype `
  bvi_state =
    <| globals : (bc_value option) list
     ; refs    : num |-> ref_value
     ; clock   : num
     ; code    : (num # bvi_exp) num_map
     ; output  : string |> `

val spt_set_def = Define `
  (spt_set f LN = LN) /\
  (spt_set f (LS x) = LS (f x)) /\
  (spt_set f (BN t1 t2) = BN (spt_set f t1) (spt_set f t2)) /\
  (spt_set f (BS t1 x t2) = BS (spt_set f t1) (f x) (spt_set f t2))`;

val bvi_to_bvl_def = Define `
  (bvi_to_bvl:bvi_state->bvl_state) s =
    <| globals := s.globals
     ; refs := s.refs
     ; clock := s.clock
     ; code := spt_set (K ARB) s.code
     ; output := s.output |>`;

val bvl_to_bvi_def = Define `
  (bvl_to_bvi:bvl_state->bvi_state->bvi_state) s t =
    t with <| globals := s.globals
            ; refs := s.refs
            ; clock := s.clock
            ; output := s.output |>`;

val small_enough_int_def = Define `
  small_enough_int i <=> -1073741823 <= i /\ i <= 1073741823`;

val iEvalOpAux_def = Define `
  iEvalOpAux op (vs:bc_value list) (s:bvi_state) =
    case (op,vs) of
    | (Const i,xs) => if small_enough_int i then
                        SOME (SOME (Number i, s))
                      else NONE
    | (Label l,xs) => (case xs of
                       | [] => SOME (SOME (CodePtr (2 * l), s))
                       | _ => NONE)
    | _ => SOME NONE`

val iEvalOp_def = Define `
  iEvalOp op vs (s:bvi_state) =
    case iEvalOpAux op vs s of
    | NONE => NONE
    | SOME (SOME (v,t)) => SOME (v,t)
    | SOME NONE => (case bEvalOp op vs (bvi_to_bvl s) of
                    | NONE => NONE
                    | SOME (v,t) => SOME (v, bvl_to_bvi t s))`

val dec_clock_def = Define `
  dec_clock x s = s with clock := s.clock - x`;

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

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
   defined to evaluate a list of bvi_exp expressions. *)

val iEval_def = tDefine "iEval" `
  (iEval ([],env,s) = (Result [],s)) /\
  (iEval (x::y::xs,env,s) =
     case iEval ([x],env,s) of
     | (Result v1,s1) =>
         (case iEval (y::xs,env,check_clock s1 s) of
          | (Result vs,s2) => (Result (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (iEval ([Var n],env,s) =
     if n < LENGTH env then (Result [EL n env],s) else (Error,s)) /\
  (iEval ([If x1 x2 x3],env,s) =
     case iEval ([x1],env,s) of
     | (Result vs,s1) =>
          if bool_to_val T = HD vs then iEval([x2],env,check_clock s1 s) else
          if bool_to_val F = HD vs then iEval([x3],env,check_clock s1 s) else
            (Error,s1)
     | res => res) /\
  (iEval ([Let xs x2],env,s) =
     case iEval (xs,env,s) of
     | (Result vs,s1) => iEval ([x2],vs++env,check_clock s1 s)
     | res => res) /\
  (iEval ([Raise x1],env,s) =
     case iEval ([x1],env,s) of
     | (Result vs,s) => (Exception (HD vs),s)
     | res => res) /\
  (iEval ([Op op xs],env,s) =
     case iEval (xs,env,s) of
     | (Result vs,s) => (case iEvalOp op (REVERSE vs) s of
                          | NONE => (Error,s)
                          | SOME (v,s) => (Result [v],s))
     | res => res) /\
  (iEval ([Tick x],env,s) =
     if s.clock = 0 then (TimeOut,s) else iEval ([x],env,dec_clock 1 s)) /\
  (iEval ([Call ticks dest xs handler],env,s1) =
     if IS_NONE dest /\ IS_SOME handler then (Error,s1) else
     case iEval (xs,env,s1) of
     | (Result vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Error,s)
          | SOME (args,exp) =>
              if (s.clock < ticks + 1) \/ (s1.clock < ticks + 1) then (TimeOut,s with clock := 0) else
                case iEval ([exp],args,dec_clock (ticks+1) (check_clock s s1)) of
                | (Exception v,s) =>
                     (case handler of
                      | SOME x => iEval ([x],v::env,check_clock s s1)
                      | NONE => (Exception v,s))
                | res => res)
     | res => res)`
 (WF_REL_TAC `(inv_image (measure I LEX measure bvi_exp2_size)
                            (\(xs,env,s). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
  \\ FULL_SIMP_TAC (srw_ss()) [] 
  \\ DECIDE_TAC);

(* We prove that the clock never increases. *)

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val iEvalOp_const = store_thm("iEvalOp_const",
  ``(iEvalOp op args s1 = SOME (res,s2)) ==>
    (s2.clock = s1.clock) /\ (s2.code = s1.code)``,
  SIMP_TAC std_ss [iEvalOp_def]
  \\ Cases_on `iEvalOpAux op args s1` \\ fs []
  \\ Cases_on `x` \\ fs [] THEN1
   (Cases_on `bEvalOp op args (bvi_to_bvl s1)` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ IMP_RES_TAC bEvalOp_const
    \\ SRW_TAC [] [bvl_to_bvi_def,bvi_to_bvl_def]
    \\ SRW_TAC [] [bvl_to_bvi_def,bvi_to_bvl_def])
  \\ Cases_on `x'` \\ fs []
  \\ fs [iEvalOpAux_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val iEval_clock = store_thm("iEval_clock",
  ``!xs env s1 vs s2.
      (iEval (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "iEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [iEval_def]
  \\ FULL_SIMP_TAC std_ss [] \\ BasicProvers.EVERY_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC iEvalOp_const
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

val iEval_check_clock = prove(
  ``!xs env s1 vs s2.
      (iEval (xs,env,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [iEval_clock,check_clock_thm]);

(* Finally, we remove check_clock from the induction and definition theorems. *)

fun sub f tm = f tm handle HOL_ERR _ =>
  let val (v,t) = dest_abs tm in mk_abs (v, sub f t) end
  handle HOL_ERR _ =>
  let val (t1,t2) = dest_comb tm in mk_comb (sub f t1, sub f t2) end
  handle HOL_ERR _ => tm

val remove_check_clock = sub (fn tm =>
  if can (match_term ``check_clock s1 (s2:bvi_state)``) tm
  then tm |> rator |> rand else fail())

val remove_disj = sub (fn tm => if is_disj tm then tm |> rator |> rand else fail())

val iEval_ind = save_thm("iEval_ind",let
  val raw_ind = fetch "-" "iEval_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (first_x_assum match_mp_tac
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ fs []
           \\ SRW_TAC [] [] \\ IMP_RES_TAC iEval_clock
           \\ IMP_RES_TAC iEval_check_clock \\ fs []
           \\ fs [check_clock_def, dec_clock_def]
           \\ rfs []
           \\ TRY (`s'.clock ≤ s1.clock` by decide_tac)
           \\ fs []
           \\ first_x_assum match_mp_tac
           \\ decide_tac)
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC iEval_clock
    \\ FULL_SIMP_TAC std_ss [check_clock_thm])
  in ind end);

val LESS_EQ_dec_clock = prove(
  ``r.clock <= (dec_clock x s).clock ==> r.clock <= s.clock``,
  SRW_TAC [] [dec_clock_def] \\ DECIDE_TAC);

val iEval_def = save_thm("iEval_def",let
  val goal = iEval_def |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ BasicProvers.EVERY_CASE_TAC
    \\ fs [iEval_def] \\ rfs []
    \\ IMP_RES_TAC iEval_check_clock
    \\ IMP_RES_TAC iEval_clock
    \\ IMP_RES_TAC LESS_EQ_TRANS
    \\ IMP_RES_TAC LESS_EQ_dec_clock
    \\ REPEAT (Q.PAT_ASSUM `!x. bbb` (K ALL_TAC))
    \\ IMP_RES_TAC iEvalOp_const
    \\ SRW_TAC [] []
    \\ fs [check_clock_thm]
    \\ rfs [check_clock_thm]
    \\ fs [check_clock_thm, dec_clock_def]
    \\ IMP_RES_TAC LESS_EQ_TRANS
    \\ REPEAT (Q.PAT_ASSUM `!x. bbb` (K ALL_TAC))
    \\ fs [check_clock_thm]
    \\ imp_res_tac LESS_EQ_LESS_TRANS)
  in def end);

(* lemmas *)

val iEval_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case iEval (xs,s,env) of (Result res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC iEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [iEval_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("iEval_LENGTH", iEval_LENGTH);

val iEval_IMP_LENGTH = store_thm("iEval_IMP_LENGTH",
  ``(iEval (xs,s,env) = (Result res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL iEval_LENGTH) \\ fs []);

val iEval_CONS = store_thm("iEval_CONS",
  ``iEval (x::xs,env,s) =
      case iEval ([x],env,s) of
      | (Result v,s2) =>
         (case iEval (xs,env,s2) of
          | (Result vs,s1) => (Result (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ fs [iEval_def]
  \\ Cases_on `iEval ([x],env,s)` \\ fs [iEval_def]
  \\ Cases_on `q` \\ fs [iEval_def]
  \\ IMP_RES_TAC iEval_IMP_LENGTH
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val iEval_SNOC = store_thm("iEval_SNOC",
  ``!xs env s x.
      iEval (SNOC x xs,env,s) =
      case iEval (xs,env,s) of
      | (Result vs,s2) =>
         (case iEval ([x],env,s2) of
          | (Result v,s1) => (Result (vs ++ v),s1)
          | t => t)
      | t => t``,
  Induct THEN1
   (fs [SNOC_APPEND,iEval_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `iEval ([x],env,s)` \\ Cases_on `q` \\ fs [])
  \\ fs [SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [iEval_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `iEval ([h],env,s)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `iEval (xs,env,r)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `iEval ([x],env,r')` \\ Cases_on `q` \\ fs [iEval_def]
  \\ IMP_RES_TAC iEval_IMP_LENGTH
  \\ Cases_on `a''` \\ fs [LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ fs []);

val bvi_state_explode = store_thm("bvi_state_explode",
  ``!s1 (s2:bvi_state).
      s1 = s2 <=>
      (s1.code = s2.code) /\
      (s1.clock = s2.clock) /\
      (s1.globals = s2.globals) /\
      (s1.output = s2.output) /\
      (s1.refs = s2.refs)``,
  Cases \\ Cases \\ fs (TypeBase.updates_of ``:bvi_state`` @
                        TypeBase.accessors_of ``:bvi_state``)
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ fs []);

(* clean up *)

val _ = map delete_binding ["iEval_AUX_def", "iEval_primitive_def"];

val _ = export_theory();

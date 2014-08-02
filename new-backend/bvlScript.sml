open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open bytecodeTheory sptreeTheory lcsymtacs;

infix \\ val op \\ = op THEN;

val _ = type_abbrev("num_map",``:'a spt``);
val _ = type_abbrev("num_set",``:unit spt``);

(* BVL = bytecode-value language *)

(* BVL aims to be the point where the old and new CakeML compiler
   backend start. It's an interface point as the following diagram
   illustrates.
                                    bytecode → x86 machine code
                                  ↗
   CakeML → ... → IL → ... → BVL                  ARM
                                  ↘              ↗ x86
                                    (new backend) → MIPS
                                                  ↘ js.asm(?)
                                                     ...
*)


(* --- Syntax of BVL --- *)

(* All operations that are uninteresting from a control-flow
   and binding perspective are lumped together in bvl_op. *)

val _ = Datatype `
  bvl_op = Global num    (* load global var with index *)
         | AllocGlobal   (* make space for a new global *)
         | SetGlobal num (* assign a value to a global *)
         | Cons num      (* construct a Block with given tag *)
         | El num        (* read Block field index *)
         | Const int     (* integer *)
         | TagEq num     (* check whether Block's tag is eq *)
         | IsBlock       (* is it a Block value? *)
         | Equal         (* structural equality *)
         | Ref           (* makes a reference *)
         | Deref         (* loads a value from a reference *)
         | Update        (* updates a reference *)
         | Label num     (* constructs a CodePtr *)
         | Print         (* prints a value *)
         | PrintC char   (* prints a character *)
         | Add           (* + over the integers *)
         | Sub           (* - over the integers *)
         | Mult          (* * over the integers *)
         | Div           (* div over the integers *)
         | Mod           (* mod over the integers *)
         | Less          (* < over the integers *) `

(* There are only a handful of "interesting" operations. *)

(* BVL uses De Bruijn indices so there is no need for a variable name
   in the let-expression. *)

(* The optional number in the call expression below is the label to
   which the call will target. If that component is NONE, then the
   target address is read from the end of the argument list, i.e. in
   case of NONE, the last bvl_exp in the argument list must evaluate
   to a CodePointer. *)

val _ = Datatype `
  bvl_exp = Var num
          | If bvl_exp bvl_exp bvl_exp
          | Let (bvl_exp list) bvl_exp
          | Raise bvl_exp
          | Handle bvl_exp bvl_exp
          | Tick bvl_exp
          | Call (num option) (bvl_exp list)
          | Op bvl_op (bvl_exp list) `

(* --- Semantics of BVL --- *)

val _ = Datatype `
  bvl_result = Result 'a
             | Exception bc_value
             | TimeOut
             | Error `

val _ = Datatype `
  bvl_state =
    <| globals : (bc_value option) list
     ; refs    : num |-> ref_value
     ; clock   : num
     ; code    : (num # bvl_exp) num_map
     ; output  : string |> `

val get_global_def = Define `
  get_global n globals =
    if n < LENGTH globals then NONE else EL n globals`

val bEvalOp_def = Define `
  bEvalOp op vs (s:bvl_state) =
    case (op,vs) of
    | (Global n,[]) =>
        (case get_global n s.globals of
         | SOME v => SOME (v,s)
         | NONE => NONE)
    | (SetGlobal n,[v]) =>
        (case get_global n s.globals of
         | SOME v => NONE
         | NONE => SOME (Number 0,
             s with globals := (LUPDATE (SOME v) n s.globals)))
    | (AllocGlobal,[]) =>
        SOME (Number 0, s with globals := s.globals ++ [NONE])
    | (Const i,xs) => SOME (Number i, s)
    | (Cons tag,xs) => SOME (Block tag xs, s)
    | (El n,[Block tag xs]) =>
        if n < LENGTH xs then SOME (EL n xs, s) else NONE
    | (TagEq n,[Block tag xs]) =>
        SOME (bool_to_val (tag = n),s)
    | (Equal,[x1;x2]) =>
        (case bc_equal x1 x2 of
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
    | (Label n,[]) =>
        if n IN domain s.code then SOME (CodePtr n, s) else NONE
    | (Print, [x]) =>
        (case bv_to_string x of
         | SOME str => SOME (x, s with output := s.output ++ str)
         | NONE => NONE)
    | (PrintC c, []) =>
          SOME (Number 0, s with output := s.output ++ [c])
    | (Add,[Number n1; Number n2]) => SOME (Number (n1 + n2),s)
    | (Sub,[Number n1; Number n2]) => SOME (Number (n1 - n2),s)
    | (Mult,[Number n1; Number n2]) => SOME (Number (n1 * n2),s)
    | (Div,[Number n1; Number n2]) =>
         if n2 = 0 then NONE else SOME (Number (n1 / n2),s)
    | (Mod,[Number n1; Number n2]) =>
         if n2 = 0 then NONE else SOME (Number (n1 % n2),s)
    | (Less,[Number n1; Number n2]) =>
         SOME (bool_to_val (n1 < n2),s)
    | _ => NONE`;

val dec_clock_def = Define `
  dec_clock s = s with clock := s.clock - 1`;

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
   defined to evaluate a list of bvl_exp expressions. *)

val bEval_def = tDefine "bEval" `
  (bEval ([],env,s:bvl_state) = (Result [],s)) /\
  (bEval (x::y::xs,env,s) =
     case bEval ([x],env,s) of
     | (Result v1,s1) =>
         (case bEval (y::xs,env,check_clock s1 s) of
          | (Result vs,s2) => (Result (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (bEval ([Var n],env,s) =
     if n < LENGTH env then (Result [EL n env],s) else (Error,s)) /\
  (bEval ([If x1 x2 x3],env,s) =
     case bEval ([x1],env,s) of
     | (Result vs,s1) =>
          if bool_to_val T = HD vs then bEval([x2],env,check_clock s1 s) else
          if bool_to_val F = HD vs then bEval([x3],env,check_clock s1 s) else
            (Error,s1)
     | res => res) /\
  (bEval ([Let xs x2],env,s) =
     case bEval (xs,env,s) of
     | (Result vs,s1) => bEval ([x2],vs++env,check_clock s1 s)
     | res => res) /\
  (bEval ([Raise x1],env,s) =
     case bEval ([x1],env,s) of
     | (Result vs,s) => (Exception (HD vs),s)
     | res => res) /\
  (bEval ([Handle x1 x2],env,s1) =
     case bEval ([x1],env,s1) of
     | (Exception v,s) => bEval ([x2],v::env,check_clock s s1)
     | res => res) /\
  (bEval ([Op op xs],env,s) =
     case bEval (xs,env,s) of
     | (Result vs,s) => (case bEvalOp op vs s of
                          | NONE => (Error,s)
                          | SOME (v,s) => (Result [v],s))
     | res => res) /\
  (bEval ([Tick x],env,s) =
     if s.clock = 0 then (TimeOut,s) else bEval ([x],env,dec_clock s)) /\
  (bEval ([Call dest xs],env,s1) =
     case bEval (xs,env,s1) of
     | (Result vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Error,s)
          | SOME (args,exp) =>
              if (s.clock = 0) \/ (s1.clock = 0) then (TimeOut,s) else
                  bEval ([exp],args,dec_clock (check_clock s s1)))
     | res => res)`
 (WF_REL_TAC `(inv_image (measure I LEX measure bvl_exp1_size)
                            (\(xs,env,s). (s.clock,xs)))`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC
  \\ TRY (MATCH_MP_TAC check_clock_lemma \\ DECIDE_TAC)
  \\ EVAL_TAC \\ Cases_on `s.clock <= s1.clock`
  \\ FULL_SIMP_TAC (srw_ss()) [] \\ DECIDE_TAC);

(* We prove that the clock never increases. *)

val check_clock_IMP = prove(
  ``n <= (check_clock r s).clock ==> n <= s.clock``,
  SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val bEvalOp_const = store_thm("bEvalOp_const",
  ``(bEvalOp op args s1 = SOME (res,s2)) ==>
    (s2.clock = s1.clock) /\ (s2.code = s1.code)``,
  SIMP_TAC std_ss [bEvalOp_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val bEval_clock = store_thm("bEval_clock",
  ``!xs env s1 vs s2.
      (bEval (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "bEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [bEval_def]
  \\ FULL_SIMP_TAC std_ss [] \\ REPEAT BasicProvers.FULL_CASE_TAC
  \\ REPEAT STRIP_TAC \\ SRW_TAC [] [check_clock_def]
  \\ RES_TAC \\ IMP_RES_TAC check_clock_IMP
  \\ FULL_SIMP_TAC std_ss [PULL_FORALL] \\ RES_TAC
  \\ IMP_RES_TAC check_clock_IMP
  \\ IMP_RES_TAC bEvalOp_const
  \\ FULL_SIMP_TAC (srw_ss()) [dec_clock_def] \\ TRY DECIDE_TAC
  \\ POP_ASSUM MP_TAC \\ REPEAT (POP_ASSUM (K ALL_TAC))
  \\ SRW_TAC [] [check_clock_def] \\ DECIDE_TAC);

val bEval_check_clock = prove(
  ``!xs env s1 vs s2.
      (bEval (xs,env,s1) = (vs,s2)) ==> (check_clock s2 s1 = s2)``,
  METIS_TAC [bEval_clock,check_clock_thm]);

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

val bEval_ind = save_thm("bEval_ind",let
  val raw_ind = fetch "-" "bEval_ind"
  val goal = raw_ind |> concl |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val ind = prove(goal,
    STRIP_TAC \\ STRIP_TAC \\ MATCH_MP_TAC raw_ind
    \\ REVERSE (REPEAT STRIP_TAC) \\ ASM_REWRITE_TAC []
    THEN1 (Q.PAT_ASSUM `!dest xs env s1. bb ==> bbb` MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC bEval_clock
           \\ `s1.clock <> 0` by DECIDE_TAC
           \\ SRW_TAC [] []
           \\ FULL_SIMP_TAC (srw_ss()) []
           \\ IMP_RES_TAC bEval_check_clock
           \\ FULL_SIMP_TAC std_ss [])
    \\ FIRST_X_ASSUM (MATCH_MP_TAC)
    \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC \\ RES_TAC
    \\ REPEAT (Q.PAT_ASSUM `!x.bbb` (K ALL_TAC))
    \\ IMP_RES_TAC bEval_clock
    \\ FULL_SIMP_TAC std_ss [check_clock_thm])
  in ind end);

val bEval_def = save_thm("bEval_def",let
  val tm = fetch "-" "bEval_AUX_def"
           |> concl |> rand |> dest_abs |> snd |> rand |> rand
  val tm = ``^tm bEval (xs,env,s)``
  val rhs = SIMP_CONV std_ss [EVAL ``pair_CASE (x,y) f``] tm |> concl |> rand
  val goal = ``!xs env s. bEval (xs,env,s) = ^rhs`` |> remove_check_clock |> remove_disj
  (* set_goal([],goal) *)
  val def = prove(goal,
    recInduct bEval_ind
    \\ REPEAT STRIP_TAC
    \\ SIMP_TAC (srw_ss()) []
    \\ TRY (SIMP_TAC std_ss [Once bEval_def] \\ NO_TAC)
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ SIMP_TAC std_ss [Once bEval_def]
    \\ Cases_on `bEval (xs,env,s1)`
    \\ Cases_on `bEval (xs,env,s)`
    \\ Cases_on `bEval ([x],env,s)`
    \\ Cases_on `bEval ([x1],env,s)`
    \\ Cases_on `bEval ([x2],env,s)`
    \\ Cases_on `bEval ([x1],env,s1)`
    \\ Cases_on `bEval ([x2],env,s1)`
    \\ IMP_RES_TAC bEval_check_clock
    \\ IMP_RES_TAC bEval_clock
    \\ FULL_SIMP_TAC (srw_ss()) [EVAL ``pair_CASE (x,y) f``]
    \\ Cases_on `r.clock = 0` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `s1.clock = 0` \\ FULL_SIMP_TAC std_ss [])
  val new_def = bEval_def |> CONJUNCTS |> map (fst o dest_eq o concl o SPEC_ALL)
                  |> map (REWR_CONV def THENC SIMP_CONV (srw_ss()) [])
                  |> LIST_CONJ
  in new_def end);

(* lemmas *)

val bEval_LENGTH = prove(
  ``!xs s env. (\(xs,s,env).
      (case bEval (xs,s,env) of (Result res,s1) => (LENGTH xs = LENGTH res)
            | _ => T))
      (xs,s,env)``,
  HO_MATCH_MP_TAC bEval_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [bEval_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) [])
  |> SIMP_RULE std_ss [];

val _ = save_thm("bEval_LENGTH", bEval_LENGTH);

val bEval_IMP_LENGTH = store_thm("bEval_IMP_LENGTH",
  ``(bEval (xs,s,env) = (Result res,s1)) ==> (LENGTH xs = LENGTH res)``,
  REPEAT STRIP_TAC \\ MP_TAC (SPEC_ALL bEval_LENGTH) \\ fs []);

val bEval_CONS = store_thm("bEval_CONS",
  ``bEval (x::xs,env,s) =
      case bEval ([x],env,s) of
      | (Result v,s2) =>
         (case bEval (xs,env,s2) of
          | (Result vs,s1) => (Result (HD v::vs),s1)
          | t => t)
      | t => t``,
  Cases_on `xs` \\ fs [bEval_def]
  \\ Cases_on `bEval ([x],env,s)` \\ fs [bEval_def]
  \\ Cases_on `q` \\ fs [bEval_def]
  \\ IMP_RES_TAC bEval_IMP_LENGTH
  \\ Cases_on `a` \\ fs []
  \\ Cases_on `t` \\ fs []);

val bEval_SNOC = store_thm("bEval_SNOC",
  ``!xs env s x.
      bEval (SNOC x xs,env,s) =
      case bEval (xs,env,s) of
      | (Result vs,s2) =>
         (case bEval ([x],env,s2) of
          | (Result v,s1) => (Result (vs ++ v),s1)
          | t => t)
      | t => t``,
  Induct THEN1
   (fs [SNOC_APPEND,bEval_def] \\ REPEAT STRIP_TAC
    \\ Cases_on `bEval ([x],env,s)` \\ Cases_on `q` \\ fs [])
  \\ fs [SNOC_APPEND,APPEND]
  \\ ONCE_REWRITE_TAC [bEval_CONS]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `bEval ([h],env,s)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `bEval (xs,env,r)` \\ Cases_on `q` \\ fs []
  \\ Cases_on `bEval ([x],env,r')` \\ Cases_on `q` \\ fs [bEval_def]
  \\ IMP_RES_TAC bEval_IMP_LENGTH
  \\ Cases_on `a''` \\ fs [LENGTH]
  \\ REV_FULL_SIMP_TAC std_ss [LENGTH_NIL] \\ fs []);

(* clean up *)

val _ = map delete_binding ["bEval_AUX_def", "bEval_primitive_def"];

val _ = export_theory();

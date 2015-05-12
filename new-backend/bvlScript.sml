open HolKernel Parse boolLib bossLib; val _ = new_theory "bvl";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open sptreeTheory lcsymtacs;
open conLangTheory (* for true/false tags *);

infix \\ val op \\ = op THEN;

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
         | El            (* read Block field index *)
         | LengthBlock   (* get length of Block *)
         | Length        (* get length of reference *)
         | LengthByte    (* get length of byte array *)
         | RefByte       (* makes a byte array *)
         | RefArray      (* makes an array by replicating a value *)
         | DerefByte     (* loads a byte from a byte array *)
         | UpdateByte    (* updates a byte array *)
         | FromList num  (* convert list to packed Block *)
         | ToList        (* convert packed Block to list *)
         | Const int     (* integer *)
         | TagEq num     (* check whether Block's tag is eq *)
         | IsBlock       (* is it a Block value? *)
         | Equal         (* structural equality *)
         | Ref           (* makes a reference *)
         | Deref         (* loads a value from a reference *)
         | Update        (* updates a reference *)
         | Label num     (* constructs a CodePtr *)
      (* | Print         (* prints a value *) *)
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
   to a CodePointer. This first number in the Call expression is how
   many additional ticks the Call should do *)


val _ = Datatype `
  bvl_exp = Var num
          | If bvl_exp bvl_exp bvl_exp
          | Let (bvl_exp list) bvl_exp
          | Raise bvl_exp
          | Handle bvl_exp bvl_exp
          | Tick bvl_exp
          | Call num (num option) (bvl_exp list)
          | Op bvl_op (bvl_exp list) `

(* --- Semantics of BVL --- *)

(* these parts are shared by bytecode and, if bytecode is to be supported, need
   to move to a common ancestor *)

val _ = Datatype `
  bc_value =
    Number int                (* integer *)
  | Block num (bc_value list) (* cons block: tag and payload *)
  | CodePtr num               (* code pointer *)
  | RefPtr num                (* pointer to ref cell *)`;

val _ = Datatype`
  ref_value =
    ValueArray (bc_value list)
  | ByteArray (word8 list)`;

val string_tag_def = Define`string_tag = 0:num`
val vector_tag_def = Define`vector_tag = 1:num`
val pat_tag_shift_def = Define`pat_tag_shift = 2:num`
val closure_tag_def = Define`closure_tag = 0:num`
val partial_app_tag_def = Define`partial_app_tag = 1:num`
val clos_tag_shift_def = Define`clos_tag_shift = 2:num`

val bc_equal_def = tDefine"bc_equal"`
  (bc_equal (CodePtr _) _ = Eq_type_error) ∧
  (bc_equal _ (CodePtr _) = Eq_type_error) ∧
  (bc_equal (Number n1) (Number n2) = (Eq_val (n1 = n2))) ∧
  (bc_equal (Number _) _ = Eq_val F) ∧
  (bc_equal _ (Number _) = Eq_val F) ∧
  (bc_equal (RefPtr n1) (RefPtr n2) = (Eq_val (n1 = n2))) ∧
  (bc_equal (RefPtr _) _ = Eq_val F) ∧
  (bc_equal _ (RefPtr _) = Eq_val F) ∧
  (bc_equal (Block t1 l1) (Block t2 l2) =
   if (t1 = closure_tag) ∨ (t2 = closure_tag) ∨ (t1 = partial_app_tag) ∨ (t2 = partial_app_tag)
   then Eq_closure
   else if (t1 = t2) ∧ (LENGTH l1 = LENGTH l2)
        then bc_equal_list l1 l2
        else Eq_val F) ∧
  (bc_equal_list [] [] = Eq_val T) ∧
  (bc_equal_list (v1::vs1) (v2::vs2) =
   case bc_equal v1 v2 of
   | Eq_val T => bc_equal_list vs1 vs2
   | Eq_val F => Eq_val F
   | bad => bad) ∧
  (bc_equal_list _ _ = Eq_val F)`
  (WF_REL_TAC `measure (\x. case x of INL (v1,v2) => bc_value_size v1 | INR (vs1,vs2) => bc_value1_size vs1)`);

val bool_to_tag_def = Define`
  bool_to_tag b = ((if b then true_tag else false_tag) + pat_tag_shift + clos_tag_shift)`

val bool_to_tag_11 = store_thm("bool_to_tag_11[simp]",
  ``bool_to_tag b1 = bool_to_tag b2 ⇔ (b1 = b2)``,
  rw[bool_to_tag_def] >> EVAL_TAC >> simp[])

val bool_to_val_def = Define`
  bool_to_val b = Block (bool_to_tag b) []`

(* -- *)

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
    if n < LENGTH globals then SOME (EL n globals) else NONE`

val bEvalOp_def = Define `
  bEvalOp op vs (s:bvl_state) =
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
    | (Const i,[]) => SOME (Number i, s)
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
(*  | (Print, [x]) =>
        (case bv_to_string x of
         | SOME str => SOME (x, s with output := s.output ++ str)
         | NONE => NONE) *)
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
     | (Result vs,s) => (case bEvalOp op (REVERSE vs) s of
                          | NONE => (Error,s)
                          | SOME (v,s) => (Result [v],s))
     | res => res) /\
  (bEval ([Tick x],env,s) =
     if s.clock = 0 then (TimeOut,s) else bEval ([x],env,dec_clock 1 s)) /\
  (bEval ([Call ticks dest xs],env,s1) =
     case bEval (xs,env,s1) of
     | (Result vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Error,s)
          | SOME (args,exp) =>
              if (s.clock < ticks + 1) \/ (s1.clock < ticks + 1) then (TimeOut,s with clock := 0) else
                  bEval ([exp],args,dec_clock (ticks + 1) (check_clock s s1)))
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
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val bEvalOp_change_clock = store_thm("bEvalOp_change_clock",
  ``(bEvalOp op args s1 = SOME (res,s2)) ==>
    (bEvalOp op args (s1 with clock := ck) = SOME (res,s2 with clock := ck))``,
  SIMP_TAC std_ss [bEvalOp_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [] \\
  CCONTR_TAC >> fs [] >>
  rw [] >>
  fs [bc_equal_def]);

val bEval_clock = store_thm("bEval_clock",
  ``!xs env s1 vs s2.
      (bEval (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock``,
  recInduct (fetch "-" "bEval_ind") \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [bEval_def]
  \\ FULL_SIMP_TAC std_ss [] \\ BasicProvers.EVERY_CASE_TAC
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
    THEN1 (Q.PAT_ASSUM `!ticks dest xs env s1. bb ==> bbb` MATCH_MP_TAC
           \\ ASM_REWRITE_TAC [] \\ REPEAT STRIP_TAC
           \\ IMP_RES_TAC bEval_clock
           \\ `¬(s1.clock < ticks + 1)` by DECIDE_TAC
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
    \\ Cases_on `r.clock < ticks + 1` \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `s1.clock < ticks + 1` \\ FULL_SIMP_TAC std_ss [] >>
    `r.clock = s1.clock` by decide_tac >>
    fs [])
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
  \\ BasicProvers.EVERY_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
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

val bEval_APPEND = store_thm("bEval_APPEND",
  ``!xs env s ys.
      bEval (xs ++ ys,env,s) =
      case bEval (xs,env,s) of
        (Result vs,s2) =>
          (case bEval (ys,env,s2) of
             (Result ws,s1) => (Result (vs ++ ws),s1)
           | res => res)
      | res => res``,
  Induct \\ fs [APPEND,bEval_def] \\ REPEAT STRIP_TAC
  THEN1 REPEAT BasicProvers.CASE_TAC
  \\ ONCE_REWRITE_TAC [bEval_CONS]
  \\ REPEAT BasicProvers.CASE_TAC \\ fs []);

val bvl_state_explode = store_thm("bvl_state_explode",
  ``!s1 (s2:bvl_state).
      s1 = s2 <=>
      (s1.code = s2.code) /\
      (s1.clock = s2.clock) /\
      (s1.globals = s2.globals) /\
      (s1.output = s2.output) /\
      (s1.refs = s2.refs)``,
  Cases \\ Cases \\ fs (TypeBase.updates_of ``:bvl_state`` @
                        TypeBase.accessors_of ``:bvl_state``)
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ fs []);

val bEval_code = store_thm("bEval_code",
  ``!xs env s1 vs s2.
      (bEval (xs,env,s1) = (vs,s2)) ==> s2.code = s1.code``,
  recInduct bEval_ind \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ ONCE_REWRITE_TAC [bEval_def]
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

val bEval_mk_tick = Q.store_thm ("bEval_mk_tick",
`!exp env s n.
  bEval ([mk_tick n exp], env, s) =
    if s.clock < n then
      (TimeOut, s with clock := 0)
    else
      bEval ([exp], env, dec_clock n s)`,
 Induct_on `n` >>
 rw [mk_tick_def, bEval_def, dec_clock_def, FUNPOW] >>
 fs [mk_tick_def, bEval_def, dec_clock_def] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [dec_clock_def, ADD1]
 >- (`s with clock := s.clock = s`
            by rw [bvl_state_explode] >>
     rw [])
 >- (`s.clock = n` by decide_tac >>
     fs []));

val inc_clock_def = Define `
inc_clock ck s = s with clock := s.clock + ck`;

val inc_clock_code = Q.store_thm ("inc_clock_code",
`!n (s:bvl_state). (inc_clock n s).code = s.code`,
 rw [inc_clock_def]);

val inc_clock_refs = Q.store_thm ("inc_clock_refs",
`!n (s:bvl_state). (inc_clock n s).refs = s.refs`,
 rw [inc_clock_def]);

val inc_clock0 = Q.store_thm ("inc_clock0",
`!n (s:bvl_state). inc_clock 0 s = s`,
 simp [inc_clock_def, bvl_state_explode]);

val _ = export_rewrites ["inc_clock_refs", "inc_clock_code", "inc_clock0"];

val dec_clock_code = Q.store_thm ("dec_clock_code",
`!n (s:bvl_state). (dec_clock n s).code = s.code`,
 rw [dec_clock_def]);

val dec_clock_refs = Q.store_thm ("dec_clock_refs",
`!n (s:bvl_state). (dec_clock n s).refs = s.refs`,
 rw [dec_clock_def]);

val dec_clock0 = Q.store_thm ("dec_clock0",
`!n (s:bvl_state). dec_clock 0 s = s`,
 simp [dec_clock_def, bvl_state_explode]);

val _ = export_rewrites ["dec_clock_refs", "dec_clock_code", "dec_clock0"];

val bEval_add_clock = Q.store_thm ("bEval_add_clock",
`!exps env s1 res s2.
  bEval (exps,env,s1) = (res, s2) ∧
  res ≠ TimeOut
  ⇒
  !ck. bEval (exps,env,inc_clock ck s1) = (res, inc_clock ck s2)`,
 recInduct bEval_ind >>
 rw [bEval_def]
 >- (Cases_on `bEval ([x], env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     Cases_on `bEval (y::xs,env,r)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [])
 >- (Cases_on `bEval ([x1],env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     rw [])
 >- (Cases_on `bEval (xs,env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [])
 >- (Cases_on `bEval (xs,env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     rw [])
 >- (Cases_on `bEval ([x1],env,s1)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [])
 >- (Cases_on `bEval (xs,env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     Cases_on `bEval (xs,env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [inc_clock_def] >>
     BasicProvers.EVERY_CASE_TAC >>
     fs [] >>
     imp_res_tac bEvalOp_const >>
     imp_res_tac bEvalOp_change_clock >>
     fs [] >>
     rw [] >>
     pop_assum (qspec_then `r.clock` mp_tac) >>
     rw [] >>
     `r with clock := r.clock = r` by rw [bvl_state_explode] >>
     fs [])
 >- (rw [] >>
     fs [inc_clock_def, dec_clock_def] >>
     rw [] >>
     `s.clock + ck - 1 = s.clock - 1 + ck` by (srw_tac [ARITH_ss] [ADD1]) >>
     metis_tac [])
 >- (Cases_on `bEval (xs,env,s1)` >>
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

val _ = map delete_binding ["bEval_AUX_def", "bEval_primitive_def"];

val _ = export_theory();

open preamble bvlTheory closSemTheory

val _ = new_theory"bvlSem"

(* --- Semantics of BVL --- *)

(* these parts are shared by bytecode and, if bytecode is to be supported, need
   to move to a common ancestor *)

val _ = Datatype `
  v =
    Number int          (* integer *)
  | Word64 word64
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
    - Equal is non-recursive
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
         if 0 ≤ i ∧ (∃w:word8. b = & (w2n w)) then
           let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
             Rval (RefPtr ptr, s with refs := s.refs |+
               (ptr,ByteArray (REPLICATE (Num i) (i2w b))))
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
             then Rval (Number (& (w2n (EL (Num i) ws))),s)
             else Error)
         | _ => Error)
    | (UpdateByte,[RefPtr ptr; Number i; Number b]) =>
        (case FLOOKUP s.refs ptr of
         | SOME (ByteArray bs) =>
            (if 0 ≤ i ∧ i < &LENGTH bs ∧ (∃w:word8. b = & (w2n w))
             then
               Rval (Unit, s with refs := s.refs |+
                 (ptr, ByteArray (LUPDATE (i2w b) (Num i) bs)))
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
    | (Equal,[Word64 w1;Word64 w2]) => Rval (Boolv (w1 = w2), s)
    | (Equal,[RefPtr r1;RefPtr r2]) => Rval (Boolv (r1 = r2), s)
    | (BlockCmp,[Block t1 vs1;Block t2 vs2]) =>
        Rval (Boolv (t1 = t2 ∧ LENGTH vs1 = LENGTH vs2), s)
    | (IsBlock,[Number i]) => Rval (Boolv F, s)
    | (IsBlock,[Word64 _]) => Rval (Boolv F, s)
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
    | (WordOp W8 opw,[Number n1; Number n2]) =>
       (case some (w1:word8,w2:word8). n1 = &(w2n w1) ∧ n2 = &(w2n w2) of
        | NONE => Error
        | SOME (w1,w2) => Rval (Number &(w2n (opw_lookup opw w1 w2)),s))
    | (WordOp W64 opw,[Word64 w1; Word64 w2]) =>
        Rval (Word64 (opw_lookup opw w1 w2),s)
    | (WordShift W8 sh n, [Number i]) =>
       (case some (w:word8). i = &(w2n w) of
        | NONE => Error
        | SOME w => Rval (Number &(w2n (shift_lookup sh w n)),s))
    | (WordShift W64 sh n, [Word64 w]) =>
        Rval (Word64 (shift_lookup sh w n),s)
    | (WordFromInt, [Number i]) =>
        Rval (Word64 (i2w i),s)
    | (WordToInt, [Word64 w]) =>
        Rval (Number (&(w2n w)),s)
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
   fix_clock. At the bottom of this file, we remove all occurrences
   of fix_clock. *)

val fix_clock_def = Define `
  fix_clock s (res,s1) = (res,s1 with clock := MIN s.clock s1.clock)`

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (res,s1) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of exp expressions. *)

val evaluate_def = tDefine "evaluate" `
  (evaluate ([],env,s:'ffi bvlSem$state) = (Rval [],s)) /\
  (evaluate (x::y::xs,env,s) =
     case fix_clock s (evaluate ([x],env,s)) of
     | (Rval v1,s1) =>
         (case evaluate (y::xs,env,s1) of
          | (Rval vs,s2) => (Rval (HD v1::vs),s2)
          | res => res)
     | res => res) /\
  (evaluate ([Var n],env,s) =
     if n < LENGTH env then (Rval [EL n env],s) else (Rerr(Rabort Rtype_error),s)) /\
  (evaluate ([If x1 x2 x3],env,s) =
     case fix_clock s (evaluate ([x1],env,s)) of
     | (Rval vs,s1) =>
          if Boolv T = HD vs then evaluate([x2],env,s1) else
          if Boolv F = HD vs then evaluate([x3],env,s1) else
            (Rerr(Rabort Rtype_error),s1)
     | res => res) /\
  (evaluate ([Let xs x2],env,s) =
     case fix_clock s (evaluate (xs,env,s)) of
     | (Rval vs,s1) => evaluate ([x2],vs++env,s1)
     | res => res) /\
  (evaluate ([Raise x1],env,s) =
     case evaluate ([x1],env,s) of
     | (Rval vs,s) => (Rerr(Rraise (HD vs)),s)
     | res => res) /\
  (evaluate ([Handle x1 x2],env,s1) =
     case fix_clock s1 (evaluate ([x1],env,s1)) of
     | (Rerr(Rraise v),s) => evaluate ([x2],v::env,s)
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
     case fix_clock s1 (evaluate (xs,env,s1)) of
     | (Rval vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Rerr(Rabort Rtype_error),s)
          | SOME (args,exp) =>
              if s.clock < ticks + 1 then (Rerr(Rabort Rtimeout_error),s with clock := 0) else
                  evaluate ([exp],args,dec_clock (ticks + 1) s))
     | res => res)`
 (WF_REL_TAC `(inv_image (measure I LEX measure exp1_size)
                         (\(xs,env,s). (s.clock,xs)))`
  \\ rpt strip_tac
  \\ simp[dec_clock_def]
  \\ imp_res_tac fix_clock_IMP
  \\ FULL_SIMP_TAC (srw_ss()) []
  \\ decide_tac);

val evaluate_ind = theorem"evaluate_ind";		

(* We prove that the clock never increases. *)

val do_app_const = Q.store_thm("do_app_const",
  `(do_app op args s1 = Rval (res,s2)) ==>
    (s2.clock = s1.clock) /\ (s2.code = s1.code)`,
  SIMP_TAC std_ss [do_app_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []);

val evaluate_clock = Q.store_thm("evaluate_clock",
  `!xs env s1 vs s2.
				(evaluate (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock`,
  recInduct evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[dec_clock_def] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> fs[] >>
  imp_res_tac do_app_const >> fs[]);

val fix_clock_evaluate = Q.store_thm("fix_clock_evaluate",
  `fix_clock s (evaluate (xs,env,s)) = evaluate (xs,env,s)`,
  Cases_on `evaluate (xs,env,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]);

(* Finally, we remove fix_clock from the induction and definition theorems. *)

val evaluate_def = save_thm("evaluate_def",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

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

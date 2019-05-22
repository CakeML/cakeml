(*
  The formal semantics of BVI
*)
open preamble bviTheory;
local open backend_commonTheory bvlSemTheory in end;

val _ = new_theory"bviSem";

val _ = temp_overload_on ("num_stubs", ``bvl_num_stubs``)

val _ = Datatype `
  state =
    <| refs    : num |-> bvlSem$v ref
     ; clock   : num
     ; global  : num option
     ; compile : 'c -> (num # num # bvi$exp) list -> (word8 list # word64 list # 'c) option
     ; compile_oracle : num -> 'c # (num # num # bvi$exp) list
     ; code    : (num # bvi$exp) num_map
     ; ffi     : 'ffi ffi_state |> `

val dec_clock_def = Define `
  dec_clock x s = s with clock := s.clock - x`;

val LESS_EQ_dec_clock = Q.prove(
  `r.clock <= (dec_clock x s).clock ==> r.clock <= s.clock`,
  SRW_TAC [] [dec_clock_def] \\ DECIDE_TAC);

val bvi_to_bvl_def = Define `
  (bvi_to_bvl:('c,'ffi) bviSem$state->('c,'ffi) bvlSem$state) s =
    <| refs := s.refs
     ; clock := s.clock
     ; code := map (K ARB) s.code
     ; ffi := s.ffi |>`;

val bvl_to_bvi_def = Define `
  (bvl_to_bvi:('c,'ffi) bvlSem$state->('c,'ffi) bviSem$state->('c,'ffi) bviSem$state) s t =
    t with <| refs := s.refs
            ; clock := s.clock
            ; ffi := s.ffi |>`;

val s = ``(s:('c,'ffi) bviSem$state)``

val do_app_aux_def = Define `
  do_app_aux op (vs:bvlSem$v list) ^s =
    case (op,vs) of
    | (Const i,xs) => if small_enough_int i then
                        SOME (SOME (Number i, s))
                      else NONE
    | (Label l,xs) => (case xs of
                       | [] => if l IN domain s.code then
                                 SOME (SOME (CodePtr l, s))
                               else NONE
                       | _ => NONE)
    | (GlobalsPtr,xs) =>
        (case xs of
         | [] => (case s.global of
                  | SOME p => SOME (SOME (RefPtr p, s))
                  | NONE => NONE)
         | _ => NONE)
    | (SetGlobalsPtr,xs) =>
        (case xs of
         | [RefPtr p] => SOME (SOME (Unit, s with global := SOME p))
         | _ => NONE)
    | (FromList n, xs) =>
        (case xs of
         | [len;lv] =>
            (case v_to_list lv of
             | SOME vs => if len = Number (& (LENGTH vs))
                          then SOME (SOME (Block n vs, s))
                          else NONE
             | _ => NONE)
         | _ => NONE)
    | (RefByte f, xs) =>
        (case xs of
          | [Number i; Number b] =>
            if 0 ≤ i ∧ (∃w:word8. b = & (w2n w)) then
              let ptr = (LEAST ptr. ¬(ptr IN FDOM s.refs)) in
                SOME (SOME (RefPtr ptr, s with refs := s.refs |+
                  (ptr, ByteArray f (REPLICATE (Num i) (i2w b)))))
            else NONE
          | _ => NONE)
    | (Global n, _) => NONE
    | (SetGlobal n, _) => NONE
    | (AllocGlobal, _) => NONE
    | (String _, _) => NONE
    | (FromListByte, _) => NONE
    | (ConcatByteVec, _) => NONE
    | (CopyByte T, _) => NONE
    | _ => SOME NONE`

val do_install_def = Define `
  do_install vs ^s =
      (case vs of
       | [v1;v2;vl1;vl2] =>
           (case (v_to_bytes v1, v_to_words v2) of
            | (SOME bytes, SOME data) =>
               if vl1 <> Number (& LENGTH bytes) \/
                  vl2 <> Number (& LENGTH data)
               then Rerr(Rabort Rtype_error) else
               let (cfg,progs) = s.compile_oracle 0 in
               let new_oracle = shift_seq 1 s.compile_oracle in
                 if DISJOINT (domain s.code) (set (MAP FST progs)) ∧ ALL_DISTINCT (MAP FST progs) then
                 (case s.compile cfg progs, progs of
                  | SOME (bytes',data',cfg'), (k,prog)::_ =>
                      if bytes = bytes' ∧ data = data' ∧ FST(new_oracle 0) = cfg' then
                        let s' =
                          s with <|
                             code := union s.code (fromAList progs)
                           ; compile_oracle := new_oracle |>
                        in
                          Rval (CodePtr k, s')
                      else Rerr(Rabort Rtype_error)
                  | _ => Rerr(Rabort Rtype_error))
                  else Rerr(Rabort Rtype_error)
            | _ => Rerr(Rabort Rtype_error))
       | _ => Rerr(Rabort Rtype_error))`;

val do_app_def = Define `
  do_app op vs ^s =
    if op = Install then do_install vs s else
    case do_app_aux op vs s of
    | NONE => Rerr(Rabort Rtype_error)
    | SOME (SOME (v,t)) => Rval (v,t)
    | SOME NONE => (case bvlSem$do_app op vs (bvi_to_bvl s) of
                    | Rerr e => Rerr e
                    | Rval (v,t) => Rval (v, bvl_to_bvi t s))`

(* The evaluation is defined as a clocked functional version of
   a conventional big-step operational semantics. *)

val fix_clock_def = Define `
  fix_clock s (res,s1) = (res,s1 with clock := MIN s.clock s1.clock)`

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (res,s1) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

(* The semantics of expression evaluation is defined next. For
   convenience of subsequent proofs, the evaluation function is
   defined to evaluate a list of bvi_exp expressions. *)

val evaluate_def = tDefine "evaluate" `
  (evaluate ([],env,s) = (Rval [],s)) /\
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
  (evaluate ([Op op xs],env,s) =
     case evaluate (xs,env,s) of
     | (Rval vs,s) => (case do_app op (REVERSE vs) s of
                          | Rerr e => (Rerr e,s)
                          | Rval (v,s) => (Rval [v],s))
     | res => res) /\
  (evaluate ([Tick x],env,s) =
     if s.clock = 0 then (Rerr(Rabort Rtimeout_error),s) else
       evaluate ([x],env,dec_clock 1 s)) /\
  (evaluate ([Call ticks dest xs handler],env,s1) =
     if IS_NONE dest /\ IS_SOME handler then (Rerr(Rabort Rtype_error),s1) else
     case fix_clock s1 (evaluate (xs,env,s1)) of
     | (Rval vs,s) =>
         (case find_code dest vs s.code of
          | NONE => (Rerr(Rabort Rtype_error),s)
          | SOME (args,exp) =>
              if (s.clock < ticks + 1) then (Rerr(Rabort Rtimeout_error),s with clock := 0) else
                case fix_clock (dec_clock (ticks+1) s) (evaluate ([exp],args,dec_clock (ticks+1) s)) of
                | (Rerr(Rraise v),s) =>
                     (case handler of
                      | SOME x => evaluate ([x],v::env,s)
                      | NONE => (Rerr(Rraise v),s))
                | res => res)
     | res => res)`
  (WF_REL_TAC `(inv_image (measure I LEX measure exp2_size)
                          (\(xs,env,s). (s.clock,xs)))`
  >> rpt strip_tac
  >> simp[dec_clock_def]
  >> imp_res_tac fix_clock_IMP
  >> imp_res_tac LESS_EQ_dec_clock
  >> rw[]);

val evaluate_ind = theorem"evaluate_ind";

(* We prove that the clock never increases. *)

Theorem do_app_const:
   (bviSem$do_app op args s1 = Rval (res,s2)) ==>
    (s2.clock = s1.clock)
Proof
  SIMP_TAC std_ss [do_app_def,do_install_def]
  \\ IF_CASES_TAC
  THEN1 (ntac 2 (every_case_tac \\ fs [UNCURRY]) \\ rw [] \\ fs [])
  \\ Cases_on `do_app_aux op args s1` \\ fs []
  \\ Cases_on `x` \\ fs [] THEN1
   (Cases_on `do_app op args (bvi_to_bvl s1)` \\ fs []
    \\ Cases_on `a` \\ fs []
    \\ IMP_RES_TAC bvlSemTheory.do_app_const
    \\ SRW_TAC [] [bvl_to_bvi_def,bvi_to_bvl_def]
    \\ SRW_TAC [] [bvl_to_bvi_def,bvi_to_bvl_def])
  \\ Cases_on `x'` \\ fs []
  \\ fs [do_app_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs []
QED

Theorem evaluate_clock:
   !xs env s1 vs s2.
  (bviSem$evaluate (xs,env,s1) = (vs,s2)) ==> s2.clock <= s1.clock
Proof
  recInduct evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[dec_clock_def] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >>
  imp_res_tac do_app_const >> fs[]
QED

Theorem fix_clock_evaluate:
   fix_clock s (evaluate (xs,env,s)) = evaluate (xs,env,s)
Proof
  Cases_on `evaluate(xs,env,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]
QED


(* Finally, we remove fix_clock from the induction and definition theorems. *)

val evaluate_def = save_thm("evaluate_def[compute]",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

(* observational semantics *)

val initial_state_def = Define`
  initial_state ffi code co cc k = <|
    clock := k;
    ffi := ffi;
    code := code;
    compile := cc;
    compile_oracle := co;
    refs := FEMPTY;
    global := NONE |>`;

val semantics_def = Define`
  semantics init_ffi code co cc start =
  let es = [bvi$Call 0 (SOME start) [] NONE] in
  let init = initial_state init_ffi code co cc in
    if ∃k e. FST (evaluate (es,[],init k)) = Rerr e ∧ e ≠ Rabort Rtimeout_error
       ∧ (!f. e ≠ Rabort (Rffi_error f))
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate (es,[],init k) = (r,s) ∧
        (case r of
         | Rerr (Rabort (Rffi_error e)) => outcome = FFI_outcome e
         | Rval _ => outcome = Success
         | _ => F) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (SND
              (evaluate (es,[],init k))).ffi.io_events) UNIV))`;

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory()

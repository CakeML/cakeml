(*
  The formal semantics of dataLang
*)
open preamble dataLangTheory bvi_to_dataTheory;
local open bvlSemTheory bvlPropsTheory bviSemTheory in end;

val _ = new_theory"dataSem";

val _ = Datatype `
  stack = Env (bvlSem$v num_map)
        | Exc (bvlSem$v num_map) num`;

val _ = Datatype `
  state =
    <| locals  : bvlSem$v num_map
     ; stack   : stack list
     ; global  : num option
     ; handler : num
     ; refs    : num |-> bvlSem$v ref
     ; compile : 'c -> (num # num # dataLang$prog) list -> (word8 list # word64 list # 'c) option
     ; compile_oracle : num -> 'c # (num # num # dataLang$prog) list
     ; clock   : num
     ; code    : (num # dataLang$prog) num_map
     ; ffi     : 'ffi ffi_state
     ; space   : num |> `

val s = ``(s:('c,'ffi) dataSem$state)``

val data_to_bvi_def = Define `
  data_to_bvi ^s =
    <| refs := s.refs
     ; clock := s.clock
     ; code := map (K ARB) s.code
     ; ffi := s.ffi
     ; global := s.global |> : ('c,'ffi) bviSem$state`;

val bvi_to_data_def = Define `
  (bvi_to_data:('c,'ffi) bviSem$state->('c,'ffi) dataSem$state->('c,'ffi) dataSem$state) s t =
    t with <| refs := s.refs
            ; clock := s.clock
            ; ffi := s.ffi
            ; global := s.global |>`;

val add_space_def = Define `
  add_space ^s k = s with space := k`;

val consume_space_def = Define `
  consume_space k ^s =
    if s.space < k then NONE else SOME (s with space := s.space - k)`;

val do_space_def = Define `
  do_space op l ^s =
    if op_space_reset op then SOME (s with space := 0)
    else if op_space_req op l = 0 then SOME s
         else consume_space (op_space_req op l) s`;

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
            | _ => Rerr(Rabort Rtype_error))
       | _ => Rerr(Rabort Rtype_error))`;

val do_app_def = Define `
  do_app op vs ^s =
    if op = Install then do_install vs s else
    if MEM op [Greater; GreaterEq] then Rerr(Rabort Rtype_error) else
    case do_space op (LENGTH vs) s of
    | NONE => Rerr(Rabort Rtype_error)
    | SOME s1 => (case bviSem$do_app op vs (data_to_bvi s1) of
                  | Rerr e => Rerr e
                  | Rval (v,t) => Rval (v, bvi_to_data t s1))`

val get_var_def = Define `
  get_var v = lookup v`;

val get_vars_def = Define `
  (get_vars [] s = SOME []) /\
  (get_vars (v::vs) s =
     case get_var v s of
     | NONE => NONE
     | SOME x => (case get_vars vs s of
                  | NONE => NONE
                  | SOME xs => SOME (x::xs)))`;

val set_var_def = Define `
set_var v x s = (s with locals := (insert v x s.locals))`;

val dec_clock_def = Define`
dec_clock s = s with clock := s.clock -1`;

val fix_clock_def = Define `
  fix_clock s (res,s1) = (res,s1 with clock := MIN s.clock s1.clock)`

val fix_clock_IMP = Q.prove(
  `fix_clock s x = (res,s1) ==> s1.clock <= s.clock`,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val LESS_EQ_dec_clock = Q.prove(
  `r.clock <= (dec_clock s).clock ==> r.clock <= s.clock`,
  SRW_TAC [] [dec_clock_def] \\ DECIDE_TAC);

val call_env_def = Define `
  call_env args ^s =
    s with <| locals := fromList args |>`;

val push_env_def = Define `
  (push_env env F ^s = s with <| stack := Env env :: s.stack |>) /\
  (push_env env T ^s = s with <| stack := Exc env s.handler :: s.stack
                               ; handler := LENGTH s.stack |>)`;

val pop_env_def = Define `
  pop_env ^s =
    case s.stack of
    | (Env e::xs) => SOME (s with <| locals := e ; stack := xs |>)
    | (Exc e n::xs) => SOME (s with <| locals := e; stack := xs ; handler := n |>)
    | _ => NONE`;

val jump_exc_def = Define `
  jump_exc ^s =
    if s.handler < LENGTH s.stack then
      case LASTN (s.handler+1) s.stack of
      | Exc e n :: xs =>
          SOME (s with <| handler := n ; locals := e ; stack := xs |>)
      | _ => NONE
    else NONE`;

val cut_env_def = Define `
  cut_env (name_set:num_set) env =
    if domain name_set SUBSET domain env
    then SOME (mk_wf (inter env name_set))
    else NONE`

val cut_state_def = Define `
  cut_state names ^s =
    case cut_env names s.locals of
    | NONE => NONE
    | SOME env => SOME (s with locals := env)`;

val cut_state_opt_def = Define `
  cut_state_opt names s =
    case names of
    | NONE => SOME s
    | SOME names => cut_state names s`;

val pop_env_clock = Q.prove(
  `(pop_env s = SOME s1) ==> (s1.clock = s.clock)`,
  full_simp_tac(srw_ss())[pop_env_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val push_env_clock = Q.prove(
  `(push_env env b s).clock = s.clock`,
  Cases_on `b` \\ full_simp_tac(srw_ss())[push_env_def]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ SRW_TAC [] [] \\ full_simp_tac(srw_ss())[]);

val evaluate_def = tDefine "evaluate" `
  (evaluate (Skip,^s) = (NONE,s)) /\
  (evaluate (Move dest src,s) =
     case get_var src s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME v => (NONE, set_var dest v s)) /\
  (evaluate (Assign dest op args names_opt,s) =
     if op_requires_names op /\ IS_NONE names_opt then (SOME (Rerr(Rabort Rtype_error)),s) else
     case cut_state_opt names_opt s of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME s =>
       (case get_vars args s.locals of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME xs => (case do_app op xs s of
                      | Rerr e => (SOME (Rerr e),call_env [] s with stack := [])
                      | Rval (v,s) =>
                        (NONE, set_var dest v s)))) /\
  (evaluate (Tick,s) =
     if s.clock = 0 then (SOME (Rerr(Rabort Rtimeout_error)),call_env [] s with stack := [])
                    else (NONE,dec_clock s)) /\
  (evaluate (MakeSpace k names,s) =
     case cut_env names s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME env => (NONE,add_space s k with locals := env)) /\
  (evaluate (Raise n,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x =>
       (case jump_exc s of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME s => (SOME (Rerr(Rraise x)),s))) /\
  (evaluate (Return n,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x => (SOME (Rval x),call_env [] s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
       if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If n c1 c2,s) =
     case get_var n s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME x => if x = Boolv T then evaluate (c1,s) else
                 if x = Boolv F then evaluate (c2,s) else
                   (SOME (Rerr(Rabort Rtype_error)),s)) /\
  (evaluate (Call ret dest args handler,s) =
     case get_vars args s.locals of
     | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
     | SOME xs =>
       (case find_code dest xs s.code of
        | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
        | SOME (args1,prog) =>
          (case ret of
           | NONE (* tail call *) =>
             if handler = NONE then
               if s.clock = 0
               then (SOME (Rerr(Rabort Rtimeout_error)),
                     call_env [] s with stack := [])
               else
                 (case evaluate (prog, call_env args1 (dec_clock s)) of
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | (SOME res,s) => (SOME res,s))
               else (SOME (Rerr(Rabort Rtype_error)),s)
           | SOME (n,names) (* returning call, returns into var n *) =>
             (case cut_env names s.locals of
              | NONE => (SOME (Rerr(Rabort Rtype_error)),s)
              | SOME env =>
               if s.clock = 0
               then (SOME (Rerr(Rabort Rtimeout_error)),
                     call_env [] s with stack := [])
               else
                 (case fix_clock s (evaluate (prog, call_env args1
                        (push_env env (IS_SOME handler) (dec_clock s)))) of
                  | (SOME (Rval x),s2) =>
                     (case pop_env s2 of
                      | NONE => (SOME (Rerr(Rabort Rtype_error)),s2)
                      | SOME s1 => (NONE, set_var n x s1))
                  | (SOME (Rerr(Rraise x)),s2) =>
                     (case handler of (* if handler is present, then handle exc *)
                      | NONE => (SOME (Rerr(Rraise x)),s2)
                      | SOME (n,h) => evaluate (h, set_var n x s2))
                  | (NONE,s) => (SOME (Rerr(Rabort Rtype_error)),s)
                  | res => res)))))`
  (WF_REL_TAC `(inv_image (measure I LEX measure prog_size)
                          (\(xs,s). (s.clock,xs)))`
  \\ rpt strip_tac
  \\ simp[dec_clock_def]
  \\ imp_res_tac fix_clock_IMP
  \\ imp_res_tac (GSYM fix_clock_IMP)
  \\ FULL_SIMP_TAC (srw_ss()) [set_var_def,push_env_clock, call_env_def]
  \\ decide_tac);

val evaluate_ind = theorem"evaluate_ind";

(* We prove that the clock never increases. *)

Theorem do_app_clock
  `(dataSem$do_app op args s1 = Rval (res,s2)) ==> s2.clock <= s1.clock`
  (SIMP_TAC std_ss [do_app_def,do_space_def,consume_space_def,do_install_def]
  \\ IF_CASES_TAC
  THEN1 (
    every_case_tac \\ fs [] \\ pairarg_tac \\ fs []
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
  \\ SRW_TAC [] [] \\ REPEAT (BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[])
  \\ IMP_RES_TAC bviSemTheory.do_app_const \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[data_to_bvi_def,bvi_to_data_def] \\ SRW_TAC [] []);

Theorem evaluate_clock
`!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock`
  (recInduct evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[set_var_def,cut_state_opt_def,cut_state_def,call_env_def,dec_clock_def,add_space_def,jump_exc_def,push_env_clock] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> fs[] >>
  imp_res_tac pop_env_clock >>
  imp_res_tac do_app_clock >>
  imp_res_tac do_app_clock >> fs[] >>
  every_case_tac >> rw[] >> simp[] >> rfs[] >>
  first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[]
  \\ every_case_tac >> full_simp_tac(srw_ss())[]
  \\ imp_res_tac fix_clock_IMP >> full_simp_tac(srw_ss())[] >> simp[] >> rfs[]);

Theorem fix_clock_evaluate
  `fix_clock s (evaluate (xs,s)) = evaluate (xs,s)`
  (Cases_on `evaluate (xs,s)` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]);

Theorem fix_clock_evaluate_call
  `fix_clock s (evaluate (prog,call_env args1 (push_env env h (dec_clock s)))) =
   (evaluate (prog,call_env args1 (push_env env h (dec_clock s))))`
  (Cases_on `(evaluate (prog,call_env args1 (push_env env h (dec_clock s))))`
  >> fs [fix_clock_def]
  >> imp_res_tac evaluate_clock
  >> fs[MIN_DEF,theorem "state_component_equality",call_env_def,dec_clock_def,push_env_clock]
  >> imp_res_tac push_env_clock);

(* Finally, we remove fix_clock from the induction and definition theorems. *)

val evaluate_def = save_thm("evaluate_def",
  REWRITE_RULE [fix_clock_evaluate,fix_clock_evaluate_call] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate,fix_clock_evaluate_call] evaluate_ind);

(* observational semantics *)

val initial_state_def = Define`
  initial_state ffi code coracle cc k = <|
    locals := LN
  ; stack := []
  ; global := NONE
  ; handler := 0
  ; refs := FEMPTY
  ; clock := k
  ; code := code
  ; compile := cc
  ; compile_oracle := coracle
  ; ffi := ffi
  ; space := 0
  |>`;

val semantics_def = Define`
  semantics init_ffi code coracle cc start =
  let p = Call NONE (SOME start) [] NONE in
  let init = initial_state init_ffi code coracle cc in
    if ∃k. case FST(evaluate (p,init k)) of
             | SOME (Rerr e) => e ≠ Rabort Rtimeout_error /\ (!f. e ≠ Rabort(Rffi_error f))
             | NONE => T | _ => F
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate (p,init k) = (SOME r,s) ∧
        (case r of
         | Rerr (Rabort (Rffi_error e)) => outcome = FFI_outcome e
         | Rval _ => outcome = Success
         | _ => F) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (SND (evaluate (p,init k))).ffi.io_events) UNIV))`;

(* clean up *)

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

val _ = export_theory();

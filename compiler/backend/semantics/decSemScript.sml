open preamble conSemTheory

val _ = new_theory"decSem"

(* The values of decLang are the same as conLang.
 *
 * The semantics of decLang differ in that the global environment is now
 * store-like rather than environment-like. The expressions for extending and
 * initialising it modify the global environment (instead of just raising a
 * type error).
 *)

val _ = Datatype`
  state = <|
    clock   : num;
    refs    : conSem$v store;
    ffi     : 'ffi ffi_state;
    globals : (conSem$v option) list
  |>`;

val do_app_def = Define `
 (do_app s op vs =
  case (op,vs) of
   | (Op op, vs) =>
     (case conSem$do_app (s.refs,s.ffi) (Op op) vs of
      | NONE => NONE
      | SOME ((s',t),r) => SOME (s with <| refs := s'; ffi := t |>,r))
   | (Init_global_var idx, [v]) =>
     if idx < LENGTH s.globals then
       (case EL idx s.globals of
        | NONE => SOME (s with globals := LUPDATE (SOME v) idx s.globals, (Rval (Conv NONE [])))
        | SOME x => NONE)
     else NONE
   | _ => NONE)`;

val _ = Datatype`
  environment = <|
    v   : (varN, conSem$v) alist;
    exh : exh_ctors_env
  |>`;

val dec_clock_def = Define`
dec_clock s = s with clock := s.clock -1`;

val fix_clock_def = Define `
  fix_clock s (s1,res) = (s1 with clock := MIN s.clock s1.clock,res)`

val fix_clock_IMP = prove(
  ``fix_clock s x = (s1,res) ==> s1.clock <= s.clock``,
  Cases_on `x` \\ fs [fix_clock_def] \\ rw [] \\ fs []);

val evaluate_def = tDefine"evaluate"`
  (evaluate (env:decSem$environment) (s:'ffi decSem$state) ([]:conLang$exp list) = (s,Rval [])) ∧
  (evaluate env s (e1::e2::es) =
    case fix_clock s (evaluate env s [e1]) of
    | (s, Rval v) =>
        (case evaluate env s (e2::es) of
         | (s, Rval vs) => (s, Rval (HD v::vs))
         | res => res)
    | res => res) ∧
  (evaluate env s [(Lit l)] = (s, Rval [Litv l])) ∧
  (evaluate env s [Raise e] =
   case evaluate env s [e] of
   | (s, Rval v) => (s, Rerr (Rraise (HD v)))
   | res => res) ∧
  (evaluate env s [Handle e pes] =
   case fix_clock s (evaluate env s [e]) of
   | (s, Rerr (Rraise v)) => evaluate_match env s v pes v
   | res => res) ∧
  (evaluate env s [Con tag es] =
   case evaluate env s (REVERSE es) of
   | (s, Rval vs) => (s, Rval [Conv tag (REVERSE vs)])
   | res => res) ∧
  (evaluate env s [Var_local n] = (s,
   case ALOOKUP env.v n of
   | SOME v => Rval [v]
   | NONE => Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Var_global n] = (s,
   if n < LENGTH s.globals ∧ IS_SOME (EL n s.globals)
   then Rval [THE (EL n s.globals)]
   else Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Fun n e] = (s, Rval [Closure env.v n e])) ∧
  (evaluate env s [App op es] =
   case fix_clock s (evaluate env s (REVERSE es)) of
   | (s, Rval vs) =>
       if op = Op Opapp then
         (case do_opapp (REVERSE vs) of
          | SOME (env', e) =>
            if s.clock = 0 then
              (s, Rerr (Rabort Rtimeout_error))
            else
              evaluate (env with v := env') (dec_clock s) [e]
          | NONE => (s, Rerr (Rabort Rtype_error)))
       else
       (case (do_app s op (REVERSE vs)) of
        | NONE => (s, Rerr (Rabort Rtype_error))
        | SOME (s,r) => (s, list_result r))
   | res => res) ∧
  (evaluate env s [Mat e pes] =
   case fix_clock s (evaluate env s [e]) of
   | (s, Rval v) =>
       evaluate_match env s (HD v) pes
         (Conv (SOME (bind_tag, (TypeExn (Short "Bind")))) [])
   | res => res) ∧
  (evaluate env s [Let n e1 e2] =
   case fix_clock s (evaluate env s [e1]) of
   | (s, Rval vs) => evaluate (env with v updated_by opt_bind n (HD vs)) s [e2]
   | res => res) ∧
  (evaluate env s [Letrec funs e] =
   if ALL_DISTINCT (MAP FST funs)
   then evaluate (env with v := build_rec_env funs env.v env.v) s [e]
   else (s, Rerr (Rabort Rtype_error))) ∧
  (evaluate env s [Extend_global n] =
   (s with globals := s.globals++GENLIST(K NONE) n, Rval [Conv NONE []])) ∧
  (evaluate_match env s v [] err_v = (s, Rerr(Rraise err_v))) ∧
  (evaluate_match env s v ((p,e)::pes) err_v =
   if ALL_DISTINCT (pat_bindings p []) then
     case pmatch env.exh s.refs p v env.v of
     | Match env' => evaluate (env with v := env') s [e]
     | No_match => evaluate_match env s v pes err_v
     | _ => (s, Rerr(Rabort Rtype_error))
   else (s, Rerr(Rabort Rtype_error)))`
  (wf_rel_tac`inv_image ($< LEX $<)
                (λx. case x of (INL(_,s,es)) => (s.clock,exp6_size es)
                             | (INR(_,s,_,pes,_)) => (s.clock,exp3_size pes))`
  >> rpt strip_tac
  >> simp[dec_clock_def]
  >> imp_res_tac fix_clock_IMP
  >> rw[]);

val evaluate_ind = theorem"evaluate_ind"

val s = ``s1:'ffi decSem$state``

val evaluate_clock = Q.store_thm("evaluate_clock",
  `(∀env (s1:'a state) e r s2. evaluate env s1 e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
   (∀env (s1:'a state) v pes v_err r s2. evaluate_match env s1 v pes v_err = (s2,r) ⇒ s2.clock ≤ s1.clock)`,
  ho_match_mp_tac evaluate_ind >> rw[evaluate_def] >>
  every_case_tac >> fs[dec_clock_def] >> rw[] >> rfs[] >>
  imp_res_tac fix_clock_IMP >> fs[do_app_def] >>
  every_case_tac >> fs[] >> rw[])

val fix_clock_evaluate = Q.store_thm("fix_clock_evaluate",
  `fix_clock s (evaluate env s e) = evaluate env s e`,
  Cases_on `evaluate env s e` \\ fs [fix_clock_def]
  \\ imp_res_tac evaluate_clock
  \\ fs [MIN_DEF,theorem "state_component_equality"]);

val evaluate_def = save_thm("evaluate_def",
  REWRITE_RULE [fix_clock_evaluate] evaluate_def);

val evaluate_ind = save_thm("evaluate_ind",
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind);

val semantics_def = Define`
  semantics env st es =
    if ∃k. SND (evaluate env (st with clock := k) es) = Rerr (Rabort Rtype_error)
      then Fail
    else
    case some res.
      ∃k s r outcome.
        evaluate env (st with clock := k) es = (s,r) ∧
        (case s.ffi.final_event of
         | NONE => (∀a. r ≠ Rerr (Rabort a)) ∧ outcome = Success
         | SOME e => outcome = FFI_outcome e) ∧
        res = Terminate outcome s.ffi.io_events
    of SOME res => res
     | NONE =>
       Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (FST (evaluate env (st with clock := k) es)).ffi.io_events) UNIV))`;

val _ = map delete_const
  ["evaluate_UNION_aux","evaluate_UNION"];

val _ = export_theory()

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

val _ = Define `
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

val check_clock_def = Define`
  check_clock s' s =
    s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock`;

val check_clock_id = Q.store_thm("check_clock_id",
  `s'.clock ≤ s.clock ⇒ decSem$check_clock s' s = s'`,
  EVAL_TAC >> rw[theorem"state_component_equality"])

val dec_clock_def = Define`
  dec_clock s = s with clock := s.clock -1`;

val evaluate_def = tDefine"evaluate"`
  (evaluate (env:decSem$environment) (s:'ffi decSem$state) ([]:conLang$exp list) = (s,Rval [])) ∧
  (evaluate env s (e1::e2::es) =
    case evaluate env s [e1] of
    | (s', Rval v) =>
        (case evaluate env (check_clock s' s) (e2::es) of
         | (s, Rval vs) => (s, Rval (HD v::vs))
         | res => res)
    | res => res) ∧
  (evaluate env s [(Lit l)] = (s, Rval [Litv l])) ∧
  (evaluate env s [Raise e] =
   case evaluate env s [e] of
   | (s, Rval v) => (s, Rerr (Rraise (HD v)))
   | res => res) ∧
  (evaluate env s [Handle e pes] =
   case evaluate env s [e] of
   | (s', Rerr (Rraise v)) => evaluate_match env (check_clock s' s) v pes v
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
   case evaluate env s (REVERSE es) of
   | (s', Rval vs) =>
       if op = Op Opapp then
         (case do_opapp (REVERSE vs) of
          | SOME (env', e) =>
            if s'.clock = 0 ∨ s.clock = 0 then
              (s', Rerr (Rabort Rtimeout_error))
            else
              evaluate (env with v := env') (dec_clock (check_clock s' s)) [e]
          | NONE => (s', Rerr (Rabort Rtype_error)))
       else
       (case (do_app s' op (REVERSE vs)) of
        | NONE => (s', Rerr (Rabort Rtype_error))
        | SOME (s,r) => (s, list_result r))
   | res => res) ∧
  (evaluate env s [Mat e pes] =
   case evaluate env s [e] of
   | (s', Rval v) =>
       evaluate_match env (check_clock s' s) (HD v) pes
         (Conv (SOME (bind_tag, (TypeExn (Short "Bind")))) [])
   | res => res) ∧
  (evaluate env s [Let n e1 e2] =
   case evaluate env s [e1] of
   | (s', Rval vs) => evaluate (env with v updated_by opt_bind n (HD vs)) (check_clock s' s) [e2]
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
                             | (INR(_,s,_,pes,_)) => (s.clock,exp3_size pes))` >>
   simp[check_clock_def,dec_clock_def] >>
   rw[] >> simp[])

val _ = export_theory()

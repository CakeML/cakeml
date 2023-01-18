(*
  Deriviation of a functional big-step semantics from the relational one.
*)
open preamble;
open fpSemPropsTheory astTheory semanticPrimitivesTheory bigStepTheory;
open determTheory bigClockTheory;

val _ = new_theory "interp";

val st = ``st:'ffi state``;

Theorem run_eval_spec_lem:
  ?run_eval run_eval_list run_eval_match.
    (!env e ^st.
       evaluate T env st e (run_eval env e st)) ∧
    (!env es ^st.
       evaluate_list T env st es (run_eval_list env es st)) ∧
    (!env v pes err_v ^st.
       evaluate_match T env st v pes err_v (run_eval_match env v pes err_v st))
Proof
  simp [METIS_PROVE [] ``(?x y z. P x ∧ Q y ∧ R z) =
                         ((?x. P x) ∧ (?y. Q y) ∧ (?z. R z))``, GSYM SKOLEM_THM] >>
  strip_tac
  >- metis_tac [big_clocked_total, pair_CASES] >>
  strip_tac
  >- (induct_on `es` >>
      rw [Once evaluate_cases] >>
      `?s' r. evaluate T env st h (s',r)` by metis_tac [big_clocked_total, pair_CASES] >>
      metis_tac [pair_CASES, result_nchotomy]) >>
  strip_tac
  >-
   (induct_on `pes` >>
    rw [Once evaluate_cases] >>
    `(?p e. h = (p,e))` by metis_tac [pair_CASES] >>
    rw [] >>
    rw [] >>
    cases_on `pmatch env.c st.refs p v []` >>
    rw []
    >- metis_tac []
    >- metis_tac []
    >- (`?s' r. evaluate T (env with v := nsAppend (alist_to_ns a) env.v) st e (s',r)` by
          metis_tac [big_clocked_total, pair_CASES] >>
        metis_tac []))
QED

Theorem run_eval_spec =
        new_specification ("run_eval", ["run_eval", "run_eval_list", "run_eval_match"],
                           run_eval_spec_lem);

Theorem evaluate_run_eval:
  !env e r st.
    evaluate T env st e r
    =
    (run_eval env e st = r)
Proof
  metis_tac [big_exp_determ, run_eval_spec]
QED

Theorem evaluate_run_eval_list:
  !env es r st.
    evaluate_list T env st es r
    =
    (run_eval_list env es st = r)
Proof
  metis_tac [big_exp_determ, run_eval_spec]
QED

Theorem evaluate_run_eval_match:
  !env v pes r err_v st.
    evaluate_match T env st v pes err_v r
    =
    (run_eval_match env v pes err_v st = r)
Proof
  metis_tac [big_exp_determ, run_eval_spec]
QED

Type M = ``:'ffi state -> 'ffi state # ('a, v) result``

Definition result_bind_def:
  (result_bind : (α,'ffi) M -> (α -> (β,'ffi) M) -> (β,'ffi) M) x f =
  λs.
    case x s of
      (s, Rval v) => f v s
    | (s, Rerr err) => (s, Rerr err)
End

Definition result_return_def:
  (result_return (*: α -> (β, α, γ) M*)) x = λs. (s, Rval x)
End

Definition result_raise_def:
  result_raise err = \s. (s, Rerr err)
End

Definition get_store_def:
  (get_store : ('ffi state,'ffi) M) = (\s. (s, Rval s))
End

Definition set_store_def:
  (set_store : 'ffi state -> (unit,'ffi) M) s = \s'. (s, Rval ())
End

Definition dec_clock_def:
  (dec_clock : (unit,'ffi) M) =
    (\s. if s.clock = 0 then (s, Rerr (Rabort Rtimeout_error))
                        else (s with clock := s.clock - 1, Rval ()))
End

val _ =
    monadsyntax.declare_monad (
      "result_state",
      { bind = ``result_bind``, ignorebind = NONE, unit = ``result_return``,
        guard = NONE, choice = NONE, fail = NONE}
    )
val _ = monadsyntax.temp_enable_monad "result_state";

Overload raise[local] = ``result_raise``

Theorem remove_lambda_pair:
  ((\ (x,y). f x y) z) = f (FST z) (SND z)
Proof
  PairCases_on `z` >>
  rw []
QED

Theorem fst_lem:
  FST = (\ (x,y, z).x)
Proof
  rw [FUN_EQ_THM] >>
  PairCases_on `x` >>
  fs []
QED

val _ = temp_delsimps["getOpClass_def"]

Theorem getOpClass_opClass:
  (getOpClass op = FunApp ⇔ opClass op FunApp) ∧
  (getOpClass op = Simple ⇔ opClass op Simple) ∧
  (getOpClass op = Icing ⇔ opClass op Icing) ∧
  (getOpClass op = Reals ⇔ opClass op Reals)
Proof
  Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]
QED

Theorem evaluate_strict_fp_sticky:
  (∀ ck env ^st e r.
    evaluate ck env st e r ⇒
    ∀ st2 v.
    r = (st2, v) ∧
    st.fp_state.canOpt = Strict ⇒
    st2.fp_state.canOpt = Strict) ∧
  (∀ ck env ^st e r.
     evaluate_list ck env st e r ⇒
     ∀ st2 vs.
       r = (st2, vs) ∧
       st.fp_state.canOpt = Strict ⇒
       st2.fp_state.canOpt = Strict) ∧
  (∀ ck env ^st v ps vr r.
     evaluate_match ck env st v ps vr r ⇒
     ∀ st2 res.
     r = (st2, res) ∧
     st.fp_state.canOpt = Strict ⇒
     st2.fp_state.canOpt = Strict)
Proof
  ho_match_mp_tac evaluate_ind >> rw[evaluate_cases, shift_fp_opts_def]
QED

Theorem run_eval_def:
  (!^st env l.
    run_eval env (Lit l)
    =
    return (Litv l)) ∧
  (!^st env e.
    run_eval env (Raise e)
    =
    do v1 <- run_eval env e;
       raise (Rraise v1)
    od) ∧
  (!env e1 pes.
     run_eval env (Handle e1 pes)
     =
     (\st.
        case run_eval env e1 ^st of
          (st', Rerr (Rraise v)) =>
            (if can_pmatch_all env.c st'.refs (MAP FST pes) v then
               run_eval_match env v pes v st'
             else raise (Rabort Rtype_error) st')
        | (st', r) => (st',r))) ∧
  (!env cn es.
     run_eval env (Con cn es)
     =
     case cn of
       NONE =>
         do vs <- run_eval_list env (REVERSE es);
            return (Conv NONE (REVERSE vs))
         od
     | SOME n =>
         (case nsLookup env.c n of
          | NONE => raise (Rabort Rtype_error)
          | SOME (l,t) =>
              if l = LENGTH es then
                do vs <- run_eval_list env (REVERSE es);
                   return (Conv (SOME t) (REVERSE vs))
                od
              else
                raise (Rabort Rtype_error))) ∧
  (!env n.
     run_eval env (Var n)
     =
     case nsLookup env.v n of
       NONE => raise (Rabort Rtype_error)
     | SOME v => return v) ∧
  (!env n e.
     run_eval env (Fun n e)
     =
     return (Closure env n e)) ∧
  (!env op e1 e2.
     run_eval env (App op es)
     =
     do vs <- run_eval_list env (REVERSE es);
        ^st <- get_store;
        (case getOpClass op of
        | FunApp =>
          (case do_opapp (REVERSE vs) of
          | NONE => raise (Rabort Rtype_error)
          | SOME (env', e3) =>
              do () <- dec_clock;
                 run_eval env' e3
              od)
        | Simple =>
          (case do_app (st.refs,st.ffi) op (REVERSE vs) of
          | NONE => raise (Rabort Rtype_error)
          | SOME ((refs',ffi'),res) =>
              do () <- set_store (st with <| refs := refs'; ffi := ffi' |>);
                       combin$C return res
              od)
        | Icing =>
          (case do_app (st.refs,st.ffi) op (REVERSE vs) of
           | NONE => raise (Rabort Rtype_error)
           | SOME ((refs,ffi),r) => let
             fp_opt =
               (if (st.fp_state.canOpt = FPScope Opt) then
                (case (do_fprw r (st.fp_state.opts 0) st.fp_state.rws) of
                 (* if it fails, just use the old value tree *)
                 | NONE => r
                 | SOME r_opt => r_opt)
                (* If we cannot optimize, we should not allow matching on the
                   structure in the oracle *)
                else r);
             (stN:'ffi state) = (if st.fp_state.canOpt = FPScope Opt then shift_fp_opts st else st);
             fp_res = if (isFpBool op) then
                      (case fp_opt of
                         Rval (FP_BoolTree fv) => Rval (Boolv (compress_bool fv))
                       | v => v)
                      else fp_opt
            in
              do () <- set_store (stN with <| refs := refs; ffi := ffi |>);
                 combin$C return fp_res
              od)
        | Reals =>
            if (st.fp_state.real_sem) then
              (case do_app (st.refs,st.ffi) op (REVERSE vs) of
               | NONE => raise (Rabort Rtype_error)
               | SOME ((refs,ffi),r) =>
                   combin$C return r)
            else
              do () <- set_store (shift_fp_opts st);
                 raise (Rabort Rtype_error)
              od
        | _ => raise (Rabort Rtype_error))
     od) ∧
  (!env lop e1 e2.
     run_eval env (Log lop e1 e2)
     =
     do v1 <- run_eval env e1;
        case do_log lop v1 e2 of
          NONE => raise (Rabort Rtype_error)
        | SOME (Val v) => return v
        | SOME (Exp e') => run_eval env e'
     od) ∧
  (!env e1 e2 e3.
     run_eval env (If e1 e2 e3)
     =
     do v1 <- run_eval env e1;
        case do_if v1 e2 e3 of
          NONE => raise (Rabort Rtype_error)
        | SOME e' => run_eval env e'
     od) ∧
  (!env e pes.
     run_eval env (Mat e pes)
     =
     do v <- run_eval env e;
        ^st <- get_store;
        (if can_pmatch_all env.c st.refs (MAP FST pes) v then
           run_eval_match env v pes bind_exn_v
         else raise (Rabort Rtype_error))
     od) ∧
  (!env x e1 e2.
     run_eval env (Let x e1 e2)
     =
     do v1 <- run_eval env e1;
        run_eval (env with v := nsOptBind x v1 env.v) e2
     od) ∧
  (!env funs e.
     run_eval env (Letrec funs e)
     =
     if ALL_DISTINCT (MAP FST funs) then
       run_eval (env with v := build_rec_env funs env env.v) e
     else
       raise (Rabort Rtype_error)) ∧
  (!env t e.
     run_eval env (Tannot e t)
     =
     run_eval env e) ∧
  (!env l e.
     run_eval env (Lannot e l)
     =
     run_eval env e) ∧
  (!env e.
     run_eval env (FpOptimise sc e) =
     (** We expand the monad here as we need to alter the state
     even if evaluation fails to leave the optimizer in a consistent state **)
     λ ^st.
       let newSt = st with fp_state :=
                   (if (st.fp_state.canOpt = Strict) then st.fp_state
                   else st.fp_state with <| canOpt := FPScope sc|>)
       in
         case run_eval env e newSt of
         (st', Rval v) =>
           (st' with <| fp_state := st'.fp_state with <| canOpt := st.fp_state.canOpt |> |>,
            Rval (HD (do_fpoptimise sc [v])))
         | (st', Rerr e) =>
             (st' with<| fp_state := st'.fp_state with <| canOpt := st.fp_state.canOpt |> |>,
              Rerr e)) ∧
  (!env.
     run_eval_list env []
     =
     return []) ∧
  (!env e es.
     run_eval_list env (e::es)
     =
     do v <- run_eval env e;
        vs <- run_eval_list env es;
        return (v::vs)
     od) ∧
  (!env v err_v.
     run_eval_match env v [] err_v
     =
     raise (Rraise err_v)) ∧
  (!env v p e pes err_v.
     run_eval_match env v ((p,e)::pes) err_v
     =
     do ^st <- get_store;
        if ALL_DISTINCT (pat_bindings p []) then
          case pmatch env.c st.refs p v [] of
            Match_type_error => raise (Rabort Rtype_error)
          | No_match => run_eval_match env v pes err_v
          | Match env' => run_eval (env with v := nsAppend (alist_to_ns env') env.v) e
        else
          raise (Rabort Rtype_error)
     od)
Proof
  rw [GSYM evaluate_run_eval, FUN_EQ_THM, result_raise_def, result_return_def,
      result_bind_def, get_store_def, set_store_def] >>
  rw [Once evaluate_cases]
  >- (every_case_tac >>
      fs [GSYM evaluate_run_eval] >>
      metis_tac [run_eval_spec])
  >- (every_case_tac >>
      metis_tac [run_eval_spec])
  >- (every_case_tac >>
      fs [do_con_check_def, build_conv_def] >>
      metis_tac [run_eval_spec])
  >- (every_case_tac >>
      PairCases_on `q` >>
      fs [] >>
      rw [] >>
      fs [GSYM evaluate_run_eval] >>
      metis_tac [])
  >- (rw [dec_clock_def] >>
      Cases_on ‘getOpClass op = FunApp’ >> gs[]
      >- (every_case_tac >>
          rw [] >>
          fs [remove_lambda_pair, shift_fp_opts_def, getOpClass_opClass] >>
          rw [] >>
          every_case_tac >>
          fs [GSYM evaluate_run_eval_list] >>
          rw [] >>
          rw [] >> fs[state_transformerTheory.UNIT_DEF] >>
          metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec]) >>
      Cases_on ‘getOpClass op = Simple’ >> gs[]
      >- (‘~ opClass op Icing’ by (Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]) >>
          ‘~ opClass op FunApp’ by (Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]) >>
          ‘~ opClass op Reals’ by (Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]) >>
          gs[getOpClass_opClass] >>
          every_case_tac >>
          rw [] >>
          fs [remove_lambda_pair, shift_fp_opts_def] >>
          rw [] >>
          every_case_tac >>
          fs [GSYM evaluate_run_eval_list] >>
          rw [] >>
          rw [] >> fs[state_transformerTheory.UNIT_DEF] >>
          metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec]) >>
      Cases_on ‘getOpClass op = EvalOp’ >> gs[]
      >- (‘~ opClass op Icing’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
          ‘~ opClass op FunApp’ by (Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]) >>
          ‘~ opClass op Reals’ by (Cases_on ‘op’ >> gs[getOpClass_def, opClass_cases]) >>
          gs[] >> every_case_tac >> gs[remove_lambda_pair] >>
          fs [GSYM evaluate_run_eval_list] >>
          Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def] >> gs[do_app_def]
          >> disj1_tac >> first_x_assum $ irule_at Any >> every_case_tac >> gs[]) >>
      Cases_on ‘getOpClass op = Reals’ >> gs[]
      >- (‘~ opClass op Icing’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
          ‘~ opClass op FunApp’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
          ‘opClass op Reals’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
          gs[] >> every_case_tac >> gs[remove_lambda_pair] >>
          fs [GSYM evaluate_run_eval_list]
          >- (ntac 3 disj2_tac >> disj1_tac >> first_x_assum $ irule_at Any >> gs[])
          >- (disj2_tac >> disj1_tac >> first_x_assum $ irule_at Any >>
              fs[state_transformerTheory.UNIT_DEF, compress_if_bool_def] >>
              first_x_assum $ mp_then Any assume_tac (INST_TYPE [beta |-> “:'ffi”, alpha |->“:'ffi”] realOp_determ) >>
              Cases_on ‘q'’ >> gs[] >>
              res_tac >>
              first_x_assum $ qspec_then ‘q.ffi’ assume_tac >> gs[] >>
              rveq >> gs[state_component_equality])
          >> ntac 2 disj2_tac >> disj1_tac
          >> first_x_assum $ irule_at Any>> rw[]) >>
      ‘getOpClass op = Icing’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
      ‘~ opClass op FunApp’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
      ‘~ opClass op Simple’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
      ‘~ opClass op Reals’ by (Cases_on ‘op’ >> gs[opClass_cases, getOpClass_def]) >>
      gs[] >>
      ntac 2 TOP_CASE_TAC >> gs[GSYM evaluate_run_eval_list] >>
      TOP_CASE_TAC >> gs[]
      >- metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec] >>
      ntac 2 TOP_CASE_TAC >> gs[getOpClass_opClass] >>
      rename1 ‘s2.fp_state.canOpt = FPScope Opt’ >>
      reverse $ Cases_on ‘s2.fp_state.canOpt = FPScope Opt’ >> gs[]
      >- ( fs[state_transformerTheory.UNIT_DEF, compress_if_bool_def] >>
           metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec]) >>
      disj2_tac >>
      Cases_on ‘do_fprw r (s2.fp_state.opts 0) s2.fp_state.rws’ >> gs[] >>
      fs[state_transformerTheory.UNIT_DEF, compress_if_bool_def] >>
      metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
  >- (every_case_tac >>
      rw [] >>
      fs [remove_lambda_pair, GSYM evaluate_run_eval] >>
      metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
  >- (every_case_tac >>
      rw [] >>
      fs [remove_lambda_pair, GSYM evaluate_run_eval] >>
      metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
  >- (every_case_tac >>
      rw [] >>
      fs [remove_lambda_pair, GSYM evaluate_run_eval] >>
      metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
  >- (every_case_tac >>
      rw [] >>
      fs [remove_lambda_pair, GSYM evaluate_run_eval] >>
      metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
  >- metis_tac [fst_lem, run_eval_spec, pair_CASES]
  >- metis_tac [fst_lem, run_eval_spec]
  >- metis_tac [fst_lem, run_eval_spec]
  >- metis_tac [fst_lem, run_eval_spec]
  >- (every_case_tac >> rw[] >> gs [GSYM evaluate_run_eval] >>
      ‘st with fp_state := st.fp_state = st’ by gs[state_component_equality] >>
      gs[] >>
      imp_res_tac evaluate_strict_fp_sticky >> gs[] >>
      first_x_assum $ irule_at Any >> gs[state_component_equality, fpState_component_equality])
  >- (every_case_tac >> rw[] >> gs [GSYM evaluate_run_eval] >>
      ‘st with fp_state := st.fp_state = st’ by gs[state_component_equality] >>
      gs[] >>
      first_x_assum $ irule_at Any >> gs[state_component_equality, fpState_component_equality])
  >- (rw [GSYM evaluate_run_eval_list] >>
      rw [Once evaluate_cases])
  >- (every_case_tac >>
      rw [] >>
      fs [GSYM evaluate_run_eval_list, GSYM evaluate_run_eval] >>
      rw [Once evaluate_cases] >>
      metis_tac [])
  >- (rw [GSYM evaluate_run_eval_match] >>
      rw [Once evaluate_cases])
  >- (every_case_tac >>
      rw [] >>
      fs [GSYM evaluate_run_eval_match, GSYM evaluate_run_eval] >>
      rw [Once evaluate_cases] >>
      fs [] >>
      fs [] >>
      rw [] >>
      metis_tac [fst_lem, run_eval_spec, pair_CASES, FST])
  >- (every_case_tac >>
      rw [] >>
      fs [GSYM evaluate_run_eval_match, GSYM evaluate_run_eval] >>
      rw [Once evaluate_cases])
QED

Definition run_eval_dec_def:
  (run_eval_dec env ^st (Dlet _ p e) =
   if ALL_DISTINCT (pat_bindings p []) ∧
      every_exp (one_con_check env.c) e then
     case run_eval env e st of
     | (st', Rval v) =>
         (case pmatch env.c st'.refs p v [] of
          | Match env' => (st', Rval <| v := alist_to_ns env'; c := nsEmpty |>)
          | No_match => (st', Rerr (Rraise bind_exn_v))
          | Match_type_error => (st', Rerr (Rabort Rtype_error)))
     | (st', Rerr e) => (st', Rerr e)
   else
     (st, Rerr (Rabort Rtype_error))) ∧
  (run_eval_dec env ^st (Dletrec _ funs) =
   if ALL_DISTINCT (MAP FST funs) ∧
      EVERY (λ(_,_,e). every_exp (one_con_check env.c) e) funs then
     (st, Rval <| v := build_rec_env funs env nsEmpty; c := nsEmpty |>)
   else
     (st, Rerr (Rabort Rtype_error))) ∧
  (run_eval_dec env ^st (Dtype _ tds) =
   if EVERY check_dup_ctors tds then
     (st with next_type_stamp := st.next_type_stamp + LENGTH tds,
      Rval <| v := nsEmpty; c := build_tdefs st.next_type_stamp tds |>)
   else
     (st, Rerr (Rabort Rtype_error))) ∧
  (run_eval_dec env ^st (Denv n) =
   case declare_env st.eval_state env of
   | NONE => (st, Rerr (Rabort Rtype_error))
   | SOME (x, es') => (( st with<| eval_state := es' |>),
                       Rval <| v := (nsSing n x); c := nsEmpty |>)) ∧
  (run_eval_dec env ^st (Dtabbrev _ tvs tn t) =
   (st, Rval <| v := nsEmpty; c := nsEmpty |>)) ∧
  (run_eval_dec env ^st (Dexn _ cn ts) =
   (st with next_exn_stamp := st.next_exn_stamp + 1,
    Rval <| v := nsEmpty; c := nsSing cn (LENGTH ts, ExnStamp st.next_exn_stamp) |>)) ∧
  (run_eval_dec env st (Dmod mn ds) =
   case run_eval_decs env st ds of
     (st', Rval env') =>
       (st',  Rval <| v := nsLift mn env'.v; c := nsLift mn env'.c |>)
   | (st', Rerr err) =>
       (st', Rerr err)) ∧
  (run_eval_dec env st (Dlocal lds ds) =
   case run_eval_decs env st lds of
     (st', Rval env') =>
       (run_eval_decs (extend_dec_env env' env) st' ds)
   | (st', Rerr err) => (st', Rerr err)) ∧
  (run_eval_decs env st [] = (st,  Rval <| v := nsEmpty; c := nsEmpty |>)) ∧
  (run_eval_decs env st (d::ds) =
   case run_eval_dec env st d of
     (st', Rval env') =>
       (case run_eval_decs (extend_dec_env env' env) st' ds of
          (st'', r) =>
            (st'', combine_dec_result env' r))
   | (st',Rerr err) => (st',Rerr err))
End

Theorem run_eval_decs_spec:
  (!d (st:'a state) env st' r.
     (run_eval_dec env st d = (st', r)) ⇒
     evaluate_dec T env st d (st', r)) ∧
  (!ds env (st:'a state) st'  r.
     (run_eval_decs env st ds = (st',r)) ⇒
     evaluate_decs T env st ds (st',r))
Proof
  ho_match_mp_tac astTheory.dec_induction >>
  rw [] >>
  simp [Once evaluate_dec_cases] >>
  fs [run_eval_dec_def] >>
  every_case_tac >>
  rw [] >>
  fs [GSYM evaluate_run_eval, fst_lem, CaseEq"bool"] >>
  metis_tac []
QED

Theorem evaluate_dec_run_eval_dec:
  ∀env d r st. evaluate_dec T env st d r ⇔ run_eval_dec env st d = r
Proof
  rw[] >> reverse eq_tac >> rw[] >>
  Cases_on `run_eval_dec env st d`
  >- metis_tac[run_eval_decs_spec] >>
  drule $ cj 1 run_eval_decs_spec >> rw[] >>
  metis_tac[decs_determ]
QED

Theorem evaluate_decs_run_eval_decs:
  ∀env ds r st. evaluate_decs T env st ds r ⇔ run_eval_decs env st ds = r
Proof
  rw[] >> reverse eq_tac >> rw[] >>
  Cases_on `run_eval_decs env st ds`
  >- metis_tac[run_eval_decs_spec] >>
  drule $ cj 2 run_eval_decs_spec >> rw[] >>
  metis_tac[decs_determ]
QED

val _ = export_theory ();

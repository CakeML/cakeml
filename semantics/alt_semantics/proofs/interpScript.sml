(*
  Deriviation of a functional big-step semantics from the relational one.
*)
open preamble;
open semanticPrimitivesTheory bigStepTheory;
open terminationTheory;
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
  ((\(x,y). f x y) z) = f (FST z) (SND z)
Proof
  PairCases_on `z` >>
  rw []
QED

Theorem fst_lem:
  FST = (\(x,y, z).x)
Proof
  rw [FUN_EQ_THM] >>
  PairCases_on `x` >>
  fs []
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
        if op = Opapp then
          case do_opapp (REVERSE vs) of
          | NONE => raise (Rabort Rtype_error)
          | SOME (env', e3) =>
              do () <- dec_clock;
                 run_eval env' e3
              od
        else
          case do_app (st.refs,st.ffi) op (REVERSE vs) of
          | NONE => raise (Rabort Rtype_error)
          | SOME ((refs',ffi'),res) =>
              do () <- set_store (st with <| refs := refs'; ffi := ffi' |>);
                 combin$C return res
              od
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
      every_case_tac >>
      rw [] >>
      fs [remove_lambda_pair] >>
      rw [] >>
      every_case_tac >>
      fs [GSYM evaluate_run_eval] >>
      rw [] >>
      rw [] >> fs[state_transformerTheory.UNIT_DEF] >>
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
   if ALL_DISTINCT (pat_bindings p []) then
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
   if ALL_DISTINCT (MAP FST funs) then
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

val _ = export_theory ();

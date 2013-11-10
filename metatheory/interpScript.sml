open preamble;
open monadsyntax;
open semanticPrimitivesTheory bigStepTheory;
open terminationTheory;
open bigClockTheory;

val _ = new_theory "interp";

val run_eval_spec_lem = Q.prove (
`?run_eval run_eval_list run_eval_match.
  (!menv (cenv:envC) env e st. 
    evaluate T menv cenv st env e (run_eval menv cenv env e st)) ∧
  (!menv (cenv:envC) env es st.
    evaluate_list T menv cenv st env es (run_eval_list menv cenv env es st)) ∧
  (!menv (cenv:envC) env v pes err_v st.
    evaluate_match T menv cenv st env v pes err_v (run_eval_match menv cenv env v pes err_v st))`,
 simp [METIS_PROVE [] ``(?x y z. P x ∧ Q y ∧ R z) = ((?x. P x) ∧ (?y. Q y) ∧ (?z. R z))``,
       GSYM SKOLEM_THM] >>
 strip_tac
 >- metis_tac [big_clocked_total, pair_CASES] >> 
 strip_tac 
 >- (induct_on `es` >>
     rw [Once evaluate_cases] >>
     `?count' s' r. evaluate T menv cenv st env h ((count',s'),r)` by metis_tac [big_clocked_total, pair_CASES] >>
     metis_tac [pair_CASES, result_nchotomy]) >>
 strip_tac
 >- (induct_on `pes` >>
     rw [Once evaluate_cases] >>
     `(?count s. st = (count,s)) ∧ (?p e. h = (p,e))` by metis_tac [pair_CASES] >>
     rw [] >>
     cases_on `pmatch cenv s p v env` >>
     rw []
     >- metis_tac []
     >- metis_tac []
     >- (`?count'' s' r. evaluate T menv cenv (count',s) l e ((count'',s'),r)` by metis_tac [big_clocked_total, pair_CASES] >>
         metis_tac [])));

val run_eval_spec = 
 new_specification ("run_eval", ["run_eval", "run_eval_list", "run_eval_match"], run_eval_spec_lem);

val evaluate_run_eval = Q.store_thm ("evaluate_run_eval",
`!menv (cenv :envC) env e r st. 
  evaluate T menv cenv st env e r 
  = 
  (run_eval menv cenv env e st = r)`,
metis_tac [big_exp_determ, run_eval_spec]);

val evaluate_run_eval_list = Q.store_thm ("evaluate_run_eval_list",
`!menv (cenv :envC) env es r st. 
  evaluate_list T menv cenv st env es r 
  = 
  (run_eval_list menv cenv env es st = r)`,
metis_tac [big_exp_determ, run_eval_spec]);

val evaluate_run_eval_match = Q.store_thm ("evaluate_run_eval_match",
`!menv (cenv :envC) env v pes r err_v st. 
  evaluate_match T menv cenv st env v pes err_v r 
  = 
  (run_eval_match menv cenv env v pes err_v st = r)`,
metis_tac [big_exp_determ, run_eval_spec]);

val _ = type_abbrev("M", ``:count_store -> count_store # 'a result``);

val result_bind_def = Define `
(result_bind : α M -> (α -> β M) -> β M) x f =
  λs.
    case x s of
      (s, Rval v) => f v s
    | (s, Rerr err) => (s, Rerr err)`;

val result_return_def = Define `
(result_return (*: α -> (β, α, γ) M*)) x = 
  λs. (s, Rval x)`;

val result_raise_def = Define `
result_raise err = \s. (s, Rerr err)`;

val get_store_def = Define `
(get_store : store M) = \(count,s). ((count,s), Rval s)`;

val set_store_def = Define `
(set_store : store -> unit M) s = \(count,s'). ((count,s), Rval ())`;

val dec_clock_def = Define `
(dec_clock : unit M) = (\(count,s). if count = 0 then ((0,s), Rerr Rtimeout_error) else ((count - 1, s), Rval ()))`;

val _ = temp_overload_on ("monad_bind", ``result_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. result_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. result_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``result_return``);
val _ = temp_overload_on ("raise", ``result_raise``);

val remove_lambda_pair = Q.prove (
`((\(x,y). f x y) z) = f (FST z) (SND z)`,
PairCases_on `z` >>
rw []);

val fst_lem = Q.prove (
`FST = (\(x,y, z).x)`,
rw [FUN_EQ_THM] >>
PairCases_on `x` >>
fs []);

val run_eval_def = Q.store_thm ("run_eval_def",
`(!menv cenv st env l.
  run_eval menv cenv env (Lit l)
  =
  return (Litv l)) ∧
 (!menv cenv st env e.
  run_eval menv cenv env (Raise e)
  =
  do v1 <- run_eval menv cenv env e;
     raise (Rraise v1)
  od) ∧
 (!menv cenv env e1 pes.
  run_eval menv cenv env (Handle e1 pes)
  =
  (\st.
    case run_eval menv cenv env e1 st of
        (st', Rerr (Rraise v)) =>
          run_eval_match menv cenv env v pes v st'
      | (st', r) => (st',r))) ∧
 (!menv cenv env cn es.
  run_eval menv cenv env (Con cn es)
  =
  if do_con_check cenv cn (LENGTH es) then
    do vs <- run_eval_list menv cenv env es;
       return (Conv cn vs)
    od
  else
    raise Rtype_error) ∧
 (!menv cenv env n.
  run_eval menv cenv env (Var n)
  =
  case lookup_var_id n menv env of
       NONE => raise Rtype_error
     | SOME v => return v) ∧
 (!menv cenv env n e.
   run_eval menv cenv env (Fun n e)
   =
   return (Closure env n e)) ∧
 (!menv cenv st env uop e.
  run_eval menv cenv env (Uapp uop e)
  =
  do v <- run_eval menv cenv env e;
     st <- get_store;
     case do_uapp st uop v of
          NONE => raise Rtype_error
        | SOME (st',v) => 
            do () <- set_store st';
               return v 
            od
  od) ∧
 (!menv cenv env op e1 e2.
   run_eval menv cenv env (App op e1 e2)
   =
   do v1 <- run_eval menv cenv env e1;
      v2 <- run_eval menv cenv env e2;
      st <- get_store;
      case do_app st env op v1 v2 of
           NONE => raise Rtype_error
         | SOME (st', env', e3) =>
             do () <- if op = Opapp then dec_clock else return ();
                () <- set_store st';
                run_eval menv cenv env' e3
             od
   od) ∧
 (!menv cenv env lop e1 e2.
   run_eval menv cenv env (Log lop e1 e2)
   =
   do v1 <- run_eval menv cenv env e1;
      case do_log lop v1 e2 of
           NONE => raise Rtype_error
         | SOME e' => run_eval menv cenv env e'
   od) ∧
 (!menv cenv env e1 e2 e3.
   run_eval menv cenv env (If e1 e2 e3)
   =
   do v1 <- run_eval menv cenv env e1;
      case do_if v1 e2 e3 of
           NONE => raise Rtype_error
         | SOME e' => run_eval menv cenv env e'
   od) ∧
 (!menv cenv env e pes.
   run_eval menv cenv env (Mat e pes)
   =
   do v <- run_eval menv cenv env e;
      run_eval_match menv cenv env v pes (Conv (SOME (Short "Bind")) [])
   od) ∧
 (!menv cenv env x e1 e2.
   run_eval menv cenv env (Let x e1 e2)
   =
   do v1 <- run_eval menv cenv env e1;
      run_eval menv cenv (bind x v1 env) e2
   od) ∧
 (!menv cenv env funs e.
   run_eval menv cenv env (Letrec funs e)
   =
   if ALL_DISTINCT (MAP FST funs) then
     run_eval menv cenv (build_rec_env funs env env) e
   else
     raise Rtype_error) ∧
 (!menv cenv env.
   run_eval_list menv cenv env []
   =
   return []) ∧
 (!menv cenv env e es.
   run_eval_list menv cenv env (e::es)
   =
   do v <- run_eval menv cenv env e;
      vs <- run_eval_list menv cenv env es;
      return (v::vs)
   od) ∧
 (!menv cenv env v err_v.
   run_eval_match menv cenv env v [] err_v
   =
   raise (Rraise err_v)) ∧
 (!menv cenv env v p e pes err_v.
   run_eval_match menv cenv env v ((p,e)::pes) err_v
   =
   do st <- get_store;
      if ALL_DISTINCT (pat_bindings p []) then
        case pmatch cenv st p v env of
             Match_type_error => raise Rtype_error
           | No_match => run_eval_match menv cenv env v pes err_v
           | Match env' => run_eval menv cenv env' e
      else
        raise Rtype_error
   od)`,
 rw [GSYM evaluate_run_eval, FUN_EQ_THM, result_raise_def, result_return_def,
     result_bind_def, get_store_def, set_store_def] >>
 rw [Once evaluate_cases]
 >- (every_case_tac >>
     fs [GSYM evaluate_run_eval] >>
     metis_tac [run_eval_spec])
 >- (every_case_tac >>
     metis_tac [run_eval_spec])
 >- (every_case_tac >>
     metis_tac [run_eval_spec])
 >- (every_case_tac >>
     PairCases_on `q` >>
     fs [] >>
     rw [] >>
     fs [GSYM evaluate_run_eval] >>
     metis_tac [])
 >- (rw [dec_count_def, dec_clock_def] >>
     every_case_tac >>
     rw [] >>
     fs [remove_lambda_pair] >>
     rw [] >>
     every_case_tac >>
     fs [GSYM evaluate_run_eval] >>
     rw [] >>
     fs [do_app_cases] >>
     rw [] >>
     metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
 >- (rw [dec_count_def, dec_clock_def] >>
     every_case_tac >>
     rw [] >>
     fs [remove_lambda_pair] >>
     rw [] >>
     every_case_tac >>
     fs [GSYM evaluate_run_eval] >>
     rw [] >>
     fs [do_app_cases] >>
     rw [] >>
     metis_tac [PAIR_EQ, pair_CASES, SND, FST, run_eval_spec])
 >- (every_case_tac >>
     rw [] >>
     fs [remove_lambda_pair, GSYM evaluate_run_eval, dec_count_def] >>
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
     PairCases_on `x` >>
     fs [] >>
     metis_tac [run_eval_spec]));

val run_eval_dec_def = Define `
(run_eval_dec mn menv cenv st env (Dlet p e) =
  if ALL_DISTINCT (pat_bindings p []) then
    case run_eval menv cenv env e st of
       | (st', Rval v) =>
           (case pmatch cenv (SND st') p v emp of
              | Match env' => (st', Rval (emp, env'))
              | No_match => (st', Rerr (Rraise (Conv (SOME (Short "Bind")) [])))
              | Match_type_error => (st', Rerr Rtype_error))
       | (st', Rerr e) => (st', Rerr e)
  else
    (st, Rerr Rtype_error)) ∧
(run_eval_dec mn menv cenv st env (Dletrec funs) =
  if ALL_DISTINCT (MAP FST funs) then
    (st, Rval (emp, build_rec_env funs env emp))
  else
    (st, Rerr Rtype_error)) ∧
(run_eval_dec mn menv cenv st env (Dtype tds) =
  if check_dup_ctors mn cenv tds then
    (st, Rval (build_tdefs mn tds, emp))
  else
    (st, Rerr Rtype_error)) ∧
(run_eval_dec mn menv cenv st env (Dexn cn ts) =
  if lookup (mk_id mn cn) cenv = NONE then
    (st, Rval (bind (mk_id mn cn) (LENGTH ts, TypeExn) emp, emp))
  else
    (st, Rerr Rtype_error))`;

val run_eval_decs_def = Define `
(run_eval_decs mn menv cenv st env [] = (st, emp, Rval emp)) ∧
(run_eval_decs mn menv cenv st env (d::ds) =
  case run_eval_dec mn menv cenv st env d of
      (st', Rval (cenv',env')) =>
         (case run_eval_decs mn menv (merge cenv' cenv) st' (merge env' env) ds of
               (st'', cenv'', r) =>
                 (st'', merge cenv'' cenv', combine_dec_result env' r))
    | (st',Rerr err) => (st',emp,Rerr err))`;

val run_eval_top_def = Define `
(run_eval_top menv cenv st env (Tdec d) = 
  case run_eval_dec NONE menv cenv st env d of
       (st', Rval (cenv', env')) => (st', cenv', Rval (emp, env'))
     | (st', Rerr err) => (st', emp, Rerr err)) ∧
(run_eval_top menv cenv st env (Tmod mn specs ds) =
  if ~MEM mn (MAP FST menv) then
    case run_eval_decs (SOME mn) menv cenv st env ds of
         (st', cenv', Rval env') => (st', cenv', (Rval ([(mn, env')], emp)))
       | (st', cenv', Rerr err) => (st', cenv', Rerr err)
  else
    (st, emp, Rerr Rtype_error))`;

val run_eval_prog_def = Define `
(run_eval_prog menv cenv st env [] = (st, emp, Rval (emp, emp))) ∧
(run_eval_prog menv cenv st env (top::prog) =
  case run_eval_top menv cenv st env top of
       (st', cenv', Rval (menv', env')) =>
          (case run_eval_prog (merge menv' menv) (merge cenv' cenv) st' (merge env' env) prog of
              | (st'', cenv'', Rval (menv'', env'')) =>
                  (st'', merge cenv'' cenv', Rval (merge menv'' menv', merge env'' env'))
              | (st'', cenv'', Rerr err) => (st'', merge cenv'' cenv', Rerr err))
     | (st', cenv', Rerr err) => (st', cenv', Rerr err))`;

val run_eval_dec_spec = Q.store_thm ("run_eval_dec_spec",
`!mn menv cenv st env d st' r.
  (run_eval_dec mn menv cenv st env d = (st', r)) ∧
  r ≠ Rerr Rtimeout_error ⇒ 
  evaluate_dec mn menv cenv (SND st) env d (SND st', r)`,
 cases_on `d` >>
 rw [evaluate_dec_cases, run_eval_dec_def, fst_lem] >>
 every_case_tac >>
 fs [GSYM evaluate_run_eval] >>
 rw [] >>
 metis_tac [big_clocked_unclocked_equiv, clocked_min_counter, SND, pair_CASES, result_distinct, result_11]);

val run_eval_decs_spec = Q.store_thm ("run_eval_decs_spec",
`!mn menv cenv st env ds st' cenv' r.
  (run_eval_decs mn menv cenv st env ds = (st',cenv', r)) ∧
  r ≠ Rerr Rtimeout_error ⇒ 
  evaluate_decs mn menv cenv (SND st) env ds (SND st', cenv', r)`,
 induct_on `ds` >>
 rw [Once evaluate_decs_cases] >>
 fs [run_eval_decs_def] >>
 every_case_tac >>
 imp_res_tac run_eval_dec_spec >>
 fs [] >>
 rw [] 
 >- (cases_on `r'''` >>
     fs [combine_dec_result_def, libTheory.merge_def] >>
     every_case_tac >>
     fs [] >|
     [MAP_EVERY qexists_tac [`SND q`, `q'''`, `q'`, `r'`, `Rval a`] >>
          rw [],
      disj2_tac >>
          MAP_EVERY qexists_tac [`SND q`, `q'''`, `q'`, `r'`, `Rerr e`] >>
          rw []] >>
     NO_TAC) 
 >- metis_tac []);

val run_eval_top_spec = Q.store_thm ("run_eval_top_spec",
`!menv cenv st env top st' cenv' r.
  (run_eval_top menv cenv st env top = (st',cenv', r)) ∧
  r ≠ Rerr Rtimeout_error ⇒ 
  evaluate_top menv cenv (SND st) env top (SND st', cenv', r)`,
 cases_on `top` >>
 rw [evaluate_top_cases, run_eval_top_def]  >>
 every_case_tac >>
 imp_res_tac run_eval_decs_spec >>
 imp_res_tac run_eval_dec_spec >>
 fs [] >>
 rw [] >>
 metis_tac []);

val run_eval_prog_spec = Q.store_thm ("run_eval_prog_spec",
`!menv cenv st env prog st' cenv' r.
  (run_eval_prog menv cenv st env prog = (st',cenv', r)) ∧
  r ≠ Rerr Rtimeout_error ⇒ 
  evaluate_prog menv cenv (SND st) env prog (SND st', cenv', r)`,
 induct_on `prog` >>
 rw [run_eval_prog_def, Once evaluate_prog_cases] >>
 every_case_tac >>
 imp_res_tac run_eval_top_spec >>
 fs [] >>
 rw []
 >- (MAP_EVERY qexists_tac [`SND q`, `q''`, `q'`, `q''''`, `r'`, `Rval (q''''', r'')`] >>
     rw [combine_mod_result_def] >>
     NO_TAC) 
 >- (disj1_tac >>
     MAP_EVERY qexists_tac [`SND q`, `q''`, `q'`, `q''''`, `r'`, `Rerr e`] >>
     rw [combine_mod_result_def] >>
     NO_TAC));

val _ = export_theory ();

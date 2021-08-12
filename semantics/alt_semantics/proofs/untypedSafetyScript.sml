(*
  Prove that the small step semantics never gets stuck if there is
  still work to do (i.e., it must detect all type errors).  Thus, it
  either diverges or gives a result, and it can't do both.
*)

open preamble;
open libTheory astTheory bigStepTheory smallStepTheory semanticPrimitivesTheory
open determTheory bigSmallEquivTheory bigStepPropsTheory
open terminationTheory bigClockTheory;

val _ = new_theory "untypedSafety";

Theorem untyped_safety_exp_step:
  ∀env s e c.
    (e_step (env,s,e,c) = Estuck) =
    ((?v. e = Val v) ∧ ((c = []) ∨ (?env. c = [(Craise (), env)])))
Proof
  rw [e_step_def, continue_def, push_def, return_def] >>
  cases_on `e` >>
  rw [] >|
  [cases_on `e'`,
   cases_on `c`] >>
  rw [] >>
  every_case_tac >>
  fs [application_def, oneTheory.one, push_def, return_def] >>
  every_case_tac
QED

Theorem small_exp_safety1:
  !s env e r.
    ¬(e_diverges env s e ∧ ?r. small_eval env s e [] r)
Proof
  rw [e_diverges_def, METIS_PROVE [] ``(~x ∨ ~y) = (y ⇒ ~x)``] >>
  cases_on `r` >>
  cases_on `r'` >>
  (TRY (Cases_on `e'`)) >>
  fs [small_eval_def, e_step_reln_def]
  >- (`∀s'' env'' e'' c''.
            e_step (env',q,Val a,[]) ≠ Estep (env'',s'',e'',c'')`
         by rw [e_step_def, continue_def] >>
        metis_tac [])
  >- (`∀s'' env''' e''' c''.
            e_step (env',q,Val a,[(Craise (),env'')]) ≠ Estep (env''',s'',e''',c'')`
         by rw [push_def, e_step_def, continue_def] >>
        metis_tac [])
  >- metis_tac [e_step_result_distinct]
QED

Theorem small_exp_safety2:
  !menv cenv s env e. e_diverges env s e ∨ ?r. small_eval env s e [] r
Proof
  rw [e_diverges_def, METIS_PROVE [] ``(x ∨ y) = (~x ⇒ y)``, e_step_reln_def] >>
  cases_on `e_step (env',s',e',c')` >>
  fs [untyped_safety_exp_step]
  >- (PairCases_on `p` >>
      fs [])
  >- (qexists_tac `(s', Rerr (Rabort a))` >>
      rw [small_eval_def] >>
      metis_tac [])
  >- (qexists_tac `(s', Rval v)` >>
      rw [small_eval_def] >>
      metis_tac [])
  >- (qexists_tac `(s', Rerr (Rraise v))` >>
      rw [small_eval_def] >>
      metis_tac [])
QED

Theorem untyped_safety_exp:
  !s env e. (?r. small_eval env s e [] r) = ¬e_diverges env s e
Proof
  metis_tac [small_exp_safety2, small_exp_safety1]
QED

Triviality to_small_st_surj:
  ∀s. ∃y. s = to_small_st y
Proof
  srw_tac[QUANT_INST_ss[record_default_qp,std_qp]][to_small_st_def]
QED

Theorem untyped_safety_decs:
  (!d (s:'a state) env.
     s.eval_state = NONE ⇒
     (∃r. evaluate_dec F env s d r) = ~dec_diverges env s d) ∧
  (!ds (s:'a state) env.
     s.eval_state = NONE ⇒
     (?r. evaluate_decs F env s ds r) = ~decs_diverges env s ds)
Proof
  ho_match_mp_tac dec_induction >>
  rw [] >>
  rw [Once evaluate_dec_cases, Once dec_diverges_cases] >>
  rw [GSYM untyped_safety_exp]
  >-
   (cases_on `ALL_DISTINCT (pat_bindings p [])` >>
    fs [GSYM small_big_exp_equiv, to_small_st_def] >>
    eq_tac
    >- metis_tac []
    >> rw [] >>
    `?s. (?err. r = (s,Rerr err)) ∨ (?v. r = (s,Rval v))`
      by metis_tac [pair_CASES, result_nchotomy] >>
    rw []
    >- (qexists_tac `(s with <| refs := FST s'; ffi := SND s' |>,Rerr err)` >>
        rw []) >>
    Cases_on `pmatch env.c (FST s') p v []` >>
    rw []
    >- (
     qexists_tac `(s with <| refs := FST s'; ffi := SND s' |>,Rerr (Rraise bind_exn_v))` >>
     rw [] >>
     metis_tac [])
    >- (
     qexists_tac `(s with <| refs := FST s'; ffi := SND s' |>,Rerr (Rabort Rtype_error))` >>
     rw [] >>
     metis_tac [])
    >- (
     qexists_tac `(s with <| refs := FST s'; ffi := SND s' |>,Rval <|v := alist_to_ns a; c := nsEmpty|>)` >>
     rw [] >>
     metis_tac []))
  >- metis_tac []
  >- metis_tac [NOT_EVERY]
  >-
   (qpat_x_assum `!x. P x` (mp_tac o GSYM) >>
    rw [] >>
    eq_tac >>
    rw [] >>
    metis_tac [pair_CASES, result_nchotomy])
  >-
   (fs [EXISTS_PROD] >> fs [declare_env_def] >>
    pop_assum (mp_tac o GSYM) >>
    pop_assum (mp_tac o GSYM) >>
    pop_assum (mp_tac o GSYM) >>
    fs [] >> rw [] >>
    eq_tac >> rw [] >>
    imp_res_tac evaluate_dec_eval_state >> fs [] >>
    metis_tac [result_nchotomy, decs_determ, PAIR_EQ,
               result_11, result_distinct])
  >-
   (fs [EXISTS_PROD] >> fs [declare_env_def])
  >-
   (fs [EXISTS_PROD] >> fs [declare_env_def] >>
    pop_assum (mp_tac o GSYM) >>
    pop_assum (mp_tac o GSYM) >>
    rw [] >>
    eq_tac >>
    rw [] >>
    imp_res_tac evaluate_dec_eval_state >> fs [] >> res_tac >>
    imp_res_tac evaluate_dec_eval_state >> fs [] >>
    metis_tac [pair_CASES, result_nchotomy, result_distinct, decs_determ,
               PAIR_EQ, result_11])
QED

val _ = export_theory ();

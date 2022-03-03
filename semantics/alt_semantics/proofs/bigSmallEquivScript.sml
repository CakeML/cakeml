(*
  Big step/small step equivalence
*)
open preamble;
open libTheory semanticPrimitivesTheory bigStepTheory smallStepTheory;
open bigSmallInvariantsTheory semanticPrimitivesPropsTheory determTheory bigClockTheory;
open bigStepPropsTheory;

val _ = new_theory "bigSmallEquiv";

Theorem list_end_case[local]:
  !l. l = [] ∨ ?x l'. l = l' ++ [x]
Proof
  Induct_on `l` >>
  srw_tac[][] >>
  metis_tac [APPEND]
QED

Theorem application_thm[local]:
  !op env s vs c.
    application op env s vs c =
    if op = Opapp then
      case do_opapp vs of
      | NONE => Eabort Rtype_error
      | SOME (env,e) => Estep (env,s,Exp e,c)
    else
      case do_app s op vs of
      | NONE => Eabort Rtype_error
      | SOME (v1,Rval v') => return env v1 v' c
      | SOME (v1,Rerr (Rraise v)) => Estep (env,v1,Val v,(Craise (),env)::c)
      | SOME (v1,Rerr (Rabort a)) => Eabort a
Proof
  srw_tac[][application_def] >>
  cases_on `op` >>
  srw_tac[][]
QED

Theorem small_eval_prefix[local]:
  ∀s env e c cenv' s' env' e' c' r.
    e_step_reln^* (env,s,Exp e,c) (env',s',Exp e',c') ∧
    small_eval env' s' e' c' r
    ⇒
    small_eval env s e c r
Proof
  srw_tac[][] >>
  PairCases_on `r` >>
  cases_on `r2` >>
  full_simp_tac(srw_ss())[small_eval_def] >-
   metis_tac [transitive_RTC, transitive_def] >>
  cases_on `e''` >>
  TRY (Cases_on `a`) >>
  full_simp_tac(srw_ss())[small_eval_def] >>
  metis_tac [transitive_RTC, transitive_def]
QED

Theorem e_single_step_add_ctxt[local]:
  !s env e c s' env' e' c' c''.
    (e_step (env,s,e,c) = Estep (env',s',e',c'))
    ⇒
    (e_step (env,s,e,c++c'') = Estep (env',s',e',c'++c''))
Proof
  srw_tac[][e_step_def] >>
  cases_on `e` >>
  full_simp_tac(srw_ss())[push_def, return_def] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][]
  >- (full_simp_tac(srw_ss())[application_thm] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def])
  >- (full_simp_tac(srw_ss())[continue_def] >>
      cases_on `c` >>
      full_simp_tac(srw_ss())[] >>
      cases_on `h` >>
      full_simp_tac(srw_ss())[] >>
      cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[push_def, return_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[application_thm] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def])
QED

Theorem e_single_error_add_ctxt[local]:
  !env s e c c'.
    (e_step (env,s,e,c) = Eabort a)
    ⇒
    (e_step (env,s,e,c++c') = Eabort a)
Proof
  srw_tac[][e_step_def] >>
  cases_on `e` >>
  full_simp_tac(srw_ss())[push_def, return_def] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][]
  >- (full_simp_tac(srw_ss())[application_thm] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def])
  >- (full_simp_tac(srw_ss())[continue_def] >>
      cases_on `c` >>
      full_simp_tac(srw_ss())[] >>
      cases_on `h` >>
      full_simp_tac(srw_ss())[] >>
      cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[push_def, return_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[application_thm] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def])
QED

Theorem e_step_add_ctxt_help[local]:
  !st1 st2.
    e_step_reln^* st1 st2 ⇒
    !s1 env1 e1 c1 s2 env2 e2 c2 c'.
      (st1 = (env1,s1,e1,c1)) ∧ (st2 = (env2,s2,e2,c2))
      ⇒
      e_step_reln^* (env1,s1,e1,c1++c') (env2,s2,e2,c2++c')
Proof
  HO_MATCH_MP_TAC RTC_INDUCT >>
  srw_tac[][e_step_reln_def] >-
   metis_tac [RTC_REFL] >>
  PairCases_on `st1'` >>
  full_simp_tac(srw_ss())[] >>
  imp_res_tac e_single_step_add_ctxt >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][Once RTC_CASES1] >>
  metis_tac [e_step_reln_def]
QED

Theorem e_step_add_ctxt[local]:
  !s1 env1 e1 c1 s2 env2 e2 c2 c'.
    e_step_reln^* (env1,s1,e1,c1) (env2,s2,e2,c2)
    ⇒
    e_step_reln^* (env1,s1,e1,c1++c') (env2,s2,e2,c2++c')
Proof
  metis_tac [e_step_add_ctxt_help]
QED

Theorem e_step_raise[local]:
  !s env err c v env' env''.
    EVERY (\c. ¬?pes env. c = (Chandle () pes, env)) c ∧
    (c ≠ [])
    ⇒
    e_step_reln^* (env,s,Val v,(Craise (), env')::c) (env',s,Val v,[(Craise (), env')])
Proof
  induct_on `c` >>
  srw_tac[][] >>
  srw_tac[][Once RTC_CASES1] >>
  cases_on `c` >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][e_step_reln_def, e_step_def, continue_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  cases_on `o'` >>
  full_simp_tac(srw_ss())[]
QED

Theorem small_eval_err_add_ctxt[local]:
  !s env e c err c' s'.
    EVERY (\c. ¬?pes env. c = (Chandle () pes, env)) c'
    ⇒
    small_eval env s e c (s', Rerr err) ⇒ small_eval env s e (c++c') (s', Rerr err)
Proof
  srw_tac[][] >>
  `?a. err = Rabort a ∨ ?v. err = Rraise v`
                            by (cases_on `err` >> srw_tac[][]) >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[small_eval_def]
  >- (Cases_on `a` >>
      full_simp_tac(srw_ss())[small_eval_def] >>
      `e_step_reln^* (env,s,Exp e,c++c') (env',s',e',c''++c')`
        by metis_tac [e_step_add_ctxt] >>
      metis_tac [e_single_error_add_ctxt])
  >- (`e_step_reln^* (env,s,Exp e,c++c') (env',s',Val v,(Craise (),env'')::c')`
        by metis_tac [e_step_add_ctxt, APPEND] >>
      cases_on `c'` >>
      full_simp_tac(srw_ss())[] >-
       metis_tac [] >>
      `e_step_reln^* (env',s',Val v,(Craise (),env'')::h::t) (env'',s',Val v,[(Craise (),env'')])`
        by (match_mp_tac e_step_raise >> srw_tac[][]) >>
      metis_tac [transitive_RTC, transitive_def])
QED

Theorem small_eval_err_add_ctxt =
        SIMP_RULE (srw_ss ())
                  [METIS_PROVE [] ``!x y z. (x ⇒ y ⇒ z) = (x ∧ y ⇒ z)``]
                  small_eval_err_add_ctxt;

val small_eval_step_tac =
srw_tac[][do_con_check_def] >>
every_case_tac >>
full_simp_tac(srw_ss())[] >>
PairCases_on `r` >>
cases_on `r2` >|
[all_tac,
 cases_on `e`] >>
srw_tac[][small_eval_def] >>
EQ_TAC >>
srw_tac[][] >|
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     full_simp_tac(srw_ss())[return_def, e_step_reln_def, e_step_def, push_def, do_con_check_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[bind_exn_v_def] >>
     metis_tac [pair_CASES],
 srw_tac[][return_def, Once RTC_CASES1, e_step_reln_def, e_step_def, push_def,REVERSE_APPEND,
     do_con_check_def] >>
     fs [bind_exn_v_def] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     full_simp_tac(srw_ss())[e_step_reln_def, e_step_def, push_def, return_def, do_con_check_def, bind_exn_v_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [],
 srw_tac[][return_def, Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def,
     do_con_check_def] >>
     full_simp_tac(srw_ss())[REVERSE_APPEND, bind_exn_v_def] >>
     metis_tac [],
 qpat_x_assum `e_step_reln^* spat1 spat2`
             (ASSUME_TAC o
              SIMP_RULE (srw_ss()) [Once RTC_CASES1,e_step_reln_def,
                                    e_step_def, push_def]) >>
     full_simp_tac(srw_ss())[bind_exn_v_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[return_def, do_con_check_def] >>
     srw_tac[][] >-
     (full_simp_tac(srw_ss())[e_step_def, push_def] >>
      pop_assum MP_TAC >>
      srw_tac[][return_def, do_con_check_def, REVERSE_APPEND]) >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [],
 srw_tac[][return_def, Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def,
     do_con_check_def] >>
     full_simp_tac(srw_ss())[REVERSE_APPEND, bind_exn_v_def] >>
     metis_tac []];

Theorem small_eval_raise:
  !s env cn e1 pes c r.
    small_eval env s (Raise e1) c r =
    small_eval env s e1 ((Craise (),env)::c) r
Proof
  small_eval_step_tac
QED

Theorem small_eval_handle:
  !env s cn e1 pes c r.
    small_eval env s (Handle e1 pes) c r =
    small_eval env s e1 ((Chandle () pes,env)::c) r
Proof
  small_eval_step_tac
QED

Theorem small_eval_con:
  !env s cn e1 es ns c r.
    do_con_check env.c cn (LENGTH (es++[e1]))
    ⇒
    (small_eval env s (Con cn (es++[e1])) c r =
     small_eval env s e1 ((Ccon cn [] () (REVERSE es),env)::c) r)
Proof
  srw_tac[][do_con_check_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  small_eval_step_tac
QED

Theorem small_eval_app:
  !env s op es c r.
    small_eval env s (App op es) c r ⇔
      (es = [] ∧ small_eval env s (App op []) c r) ∨
      (?e es'. (es = es'++[e]) ∧ small_eval env s e ((Capp op [] () (REVERSE es'),env)::c) r)
Proof
  srw_tac[][] >>
  `es = [] ∨ ?e es'. es = es' ++ [e]` by metis_tac [list_end_case] >>
  srw_tac[][] >>
  `(?s' v. r = (s', Rval v)) ∨ (?s' a. r = (s', Rerr (Rabort a))) ∨
  (?s' err. r = (s', Rerr (Rraise err)))`
    by metis_tac [pair_CASES, result_nchotomy, error_result_nchotomy] >>
  TRY (cases_on `a`) >>
  full_simp_tac(srw_ss())[small_eval_def] >>
  srw_tac[][Once RTC_CASES1, e_step_reln_def, e_step_def] >>
  srw_tac[][push_def, application_thm] >>
  EQ_TAC >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[REVERSE_APPEND] >>
  metis_tac []
QED

Theorem small_eval_log:
  !env s op e1 e2 c r.
    small_eval env s (Log op e1 e2) c r =
    small_eval env s e1 ((Clog op () e2,env)::c) r
Proof
  small_eval_step_tac
QED

Theorem small_eval_if:
  !env s e1 e2 e3 c r.
    small_eval env s (If e1 e2 e3) c r =
    small_eval env s e1 ((Cif () e2 e3,env)::c) r
Proof
  small_eval_step_tac
QED

Theorem small_eval_match:
  !env s e1 pes c r err_v.
    small_eval env s (Mat e1 pes) c r =
    small_eval env s e1 ((Cmat_check () pes (Conv (SOME bind_stamp) []),env)::c) r
Proof
  small_eval_step_tac
QED

Theorem small_eval_let:
  !env s n e1 e2 c r.
    small_eval env s (Let n e1 e2) c r =
    small_eval env s e1 ((Clet n () e2,env)::c) r
Proof
  small_eval_step_tac
QED

Theorem small_eval_letrec:
  !menv cenv env s funs e1 c r.
    ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ⇒
    (small_eval env s (Letrec funs e1) c r =
     small_eval (env with v := build_rec_env funs env env.v) s e1 c r)
Proof
  small_eval_step_tac
QED

Theorem small_eval_tannot:
  !env s e1 t c r.
    small_eval env s (Tannot e1 t) c r =
    small_eval env s e1 ((Ctannot () t,env)::c) r
Proof
  small_eval_step_tac
QED

Theorem small_eval_lannot:
  !env s e1 l c r.
    small_eval env s (Lannot e1 l) c r =
    small_eval env s e1 ((Clannot () l,env)::c) r
Proof
  small_eval_step_tac
QED

Inductive small_eval_list:
  (!env s. small_eval_list env s [] (s, Rval [])) ∧
  (!s1 env e es v vs s2 s3 env'.
     e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ∧
     small_eval_list env s2 es (s3, Rval vs)
     ⇒
     small_eval_list env s1 (e::es) (s3, Rval (v::vs))) ∧
  (!s1 env e es env' s2 s3 v err_v env''.
     e_step_reln^* (env,s1,Exp e,[]) (env',s3,Val err_v,[(Craise (),env'')]) ∨
     (e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ∧
      small_eval_list env s2 es (s3, Rerr (Rraise err_v)))
     ⇒
     (small_eval_list env s1 (e::es) (s3, Rerr (Rraise err_v)))) ∧
  (!s1 env e es e' c' env' s2 v s3.
     (e_step_reln^* (env,s1,Exp e,[]) (env',s3,e',c') ∧
      (e_step (env',s3,e',c') = Eabort a)) ∨
     (e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ∧
      small_eval_list env s2 es (s3, Rerr (Rabort a)))
     ⇒
     (small_eval_list env s1 (e::es) (s3, Rerr (Rabort a))))
End

Triviality small_eval_list_length:
  !env s1 es r. small_eval_list env s1 es r ⇒
                !vs s2. (r = (s2, Rval vs)) ⇒ (LENGTH es = LENGTH vs)
Proof
  HO_MATCH_MP_TAC small_eval_list_ind >>
  srw_tac[][] >>
  srw_tac[][]
QED

Theorem small_eval_list_step:
  !env s2 es r. small_eval_list env s2 es r ⇒
                (!e v vs cn vs' env' s1 s3 v_con.
                   do_con_check env.c cn (LENGTH vs' + 1 + LENGTH vs) ∧
                   (build_conv env.c cn (REVERSE (REVERSE vs'++[v]++vs)) = SOME v_con) ∧
                   (r = (s3, Rval vs)) ∧ e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ⇒
                   e_step_reln^* (env,s1,Exp e,[(Ccon cn vs' () es,env)])
                              (env,s3,Val v_con,[]))
Proof
  HO_MATCH_MP_TAC (fetch "-" "small_eval_list_strongind") >>
  srw_tac[][] >|
  [`e_step_reln^* (env,s1,Exp e,[(Ccon cn vs' () [],env)])
   (env',s2,Val v,[(Ccon cn vs' () [],env)])`
     by metis_tac [e_step_add_ctxt,APPEND] >>
   `e_step_reln (env',s2,Val v,[(Ccon cn vs' () [],env)])
    (env,s2,Val v_con,[])`
     by fs[return_def, continue_def, e_step_reln_def, e_step_def, REVERSE_APPEND] >>
   metis_tac [transitive_RTC, transitive_def, RTC_SINGLE, APPEND],
   `LENGTH (v'::vs'') + 1 + LENGTH vs = LENGTH vs'' + 1 + SUC (LENGTH vs)`
     by (full_simp_tac(srw_ss())[] >>
         DECIDE_TAC) >>
   `REVERSE vs'' ++ [v'] ++ v::vs = (REVERSE vs'' ++ [v']) ++ [v] ++ vs`
     by metis_tac [APPEND, APPEND_ASSOC] >>
   `e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs'') () es,env)])
    (env,s3,Val v_con,[])`
     by metis_tac [APPEND_ASSOC, APPEND,REVERSE_DEF] >>
   `e_step_reln^* (env,s1,Exp e',[(Ccon cn vs'' () (e::es),env)])
    (env'',s2,Val v',[(Ccon cn vs'' () (e::es),env)])`
     by metis_tac [e_step_add_ctxt, APPEND] >>
   `LENGTH es = LENGTH vs` by metis_tac [small_eval_list_length] >>
   `e_step_reln (env'',s2,Val v',[(Ccon cn vs'' () (e::es),env)])
    (env,s2,Exp e,[(Ccon cn (v'::vs'') () es,env)])`
     by (srw_tac[][push_def,continue_def, e_step_reln_def, e_step_def] >>
         full_simp_tac (srw_ss() ++ ARITH_ss) [arithmeticTheory.ADD1]) >>
   full_simp_tac(srw_ss())[] >>
   `LENGTH vs'' + 1 + 1 + LENGTH es = LENGTH vs'' + 1 + SUC (LENGTH es)`
     by DECIDE_TAC >>
   `e_step_reln^* (env,s1,Exp e',[(Ccon cn vs'' () (e::es),env)])
    (env,s3,Val v_con,[])`
     by metis_tac [RTC_SINGLE, transitive_RTC, transitive_def] >>
   metis_tac [APPEND_ASSOC, APPEND]]
QED

Theorem small_eval_list_err:
  !env s2 es r. small_eval_list env s2 es r ⇒
                (!e v err_v cn vs' env' s1 s3.
                   do_con_check env.c cn (LENGTH vs' + 1 + LENGTH es) ∧
                   (r = (s3, Rerr (Rraise err_v))) ∧
                   e_step_reln^* (env,s1,e,[]) (env',s2,Val v,[]) ⇒
                   ?env'' env'''. e_step_reln^* (env,s1,e,[(Ccon cn vs' () es,env)])
                                             (env'',s3,Val err_v,[(Craise (), env''')]))
Proof
  ho_match_mp_tac small_eval_list_ind >>
  srw_tac[][] >>
  `e_step_reln^* (env,s1,e',[(Ccon cn vs' () (e::es),env)])
   (env''',s2,Val v',[(Ccon cn vs' () (e::es),env)])`
    by metis_tac [e_step_add_ctxt, APPEND] >>
  `LENGTH vs' + 1 + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
    by DECIDE_TAC >>
  `e_step_reln (env''',s2,Val v',[(Ccon cn vs' () (e::es),env)])
   (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])`
    by srw_tac[][push_def,continue_def, e_step_reln_def, e_step_def] >>
  full_simp_tac(srw_ss())[]
  >- (`e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
      (env',s3,Val err_v,[(Craise (), env'');(Ccon cn (v'::vs') () es,env)])`
        by metis_tac [e_step_add_ctxt,APPEND] >>
      `e_step_reln^* (env',s3,Val err_v,[(Craise (), env'');(Ccon cn (v'::vs') () es,env)])
       (env'',s3,Val err_v,[(Craise (), env'')])`
        by (match_mp_tac e_step_raise >>
            srw_tac[][]) >>
      metis_tac [RTC_SINGLE, transitive_RTC, transitive_def])
  >- (`LENGTH (v'::vs') + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
        by (full_simp_tac(srw_ss())[] >>
            DECIDE_TAC) >>
      `?env''' env''. e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
        (env'',s3,Val err_v, [(Craise (), env''')])`
        by metis_tac [] >>
      metis_tac [RTC_SINGLE, transitive_RTC, transitive_def])
QED

Theorem small_eval_list_terr:
  !env s2 es r. small_eval_list env s2 es r ⇒
                (!e v err cn vs' env' s1 s3.
                   do_con_check env.c cn (LENGTH vs' + 1 + LENGTH es) ∧
                   (r = (s3, Rerr (Rabort a))) ∧
                   e_step_reln^* (env,s1,e,[]) (env',s2,Val v,[]) ⇒
                   ?env'' e' c'. e_step_reln^* (env,s1,e,[(Ccon cn vs' () es,env)])
                                            (env'',s3,e',c') ∧
                                 (e_step (env'',s3,e',c') = (Eabort a)))
Proof
  HO_MATCH_MP_TAC small_eval_list_ind >>
  srw_tac[][] >>
  `e_step_reln^* (env,s1,e'',[(Ccon cn vs' () (e::es),env)])
   (env'',s2,Val v',[(Ccon cn vs' () (e::es),env)])`
    by metis_tac [e_step_add_ctxt, APPEND] >>
  `LENGTH vs' + 1 + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
    by DECIDE_TAC >>
  `e_step_reln (env'',s2,Val v',[(Ccon cn vs' () (e::es),env)])
   (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])`
    by srw_tac[][push_def,continue_def, e_step_reln_def, e_step_def] >>
  full_simp_tac(srw_ss())[] >|
  [`e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
   (env',s3,e',c'++[(Ccon cn (v'::vs') () es,env)])`
     by metis_tac [e_step_add_ctxt,APPEND] >>
   `e_step (env',s3,e',c'++[(Ccon cn (v'::vs') () es,env)]) = Eabort a`
     by metis_tac [e_single_error_add_ctxt] >>
   metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
   `LENGTH (v'::vs') + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
     by (full_simp_tac(srw_ss())[] >>
         DECIDE_TAC) >>
   `?env'' e' c'. e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
     (env'',s3,e',c') ∧
   (e_step (env'',s3,e',c') = Eabort a)`
     by metis_tac [] >>
   metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]]
QED

Inductive small_eval_match:
  (!env s err_v v. small_eval_match env s v [] err_v (s, Rerr (Rraise err_v))) ∧
  (!env s p e pes r v err_v.
     ALL_DISTINCT (pat_bindings p []) ∧
     pmatch env.c (FST s) p v [] = Match env' ∧
     small_eval (env with v := nsAppend (alist_to_ns env') env.v) s e [] r
     ⇒
     small_eval_match env s v ((p,e)::pes) err_v r) ∧
  (!env s e p pes r v err_v.
     ALL_DISTINCT (pat_bindings p []) ∧
     (pmatch env.c (FST s) p v [] = No_match) ∧
     small_eval_match env s v pes err_v r
     ⇒
     small_eval_match env s v ((p,e)::pes) err_v r) ∧
  (!env s p e pes v err_v.
     ¬(ALL_DISTINCT (pat_bindings p []))
     ⇒
     small_eval_match env s v ((p,e)::pes) err_v (s, Rerr (Rabort Rtype_error))) ∧
  (!env s p e pes v err_v.
     (pmatch env.c (FST s) p v [] = Match_type_error)
     ⇒
     small_eval_match env s v ((p,e)::pes) err_v (s, Rerr (Rabort Rtype_error)))
End

Definition alt_small_eval_def:
  (alt_small_eval env s1 e c (s2, Rval v) ⇔
     ∃env'. e_step_reln^* (env,s1,e,c) (env',s2,Val v,[])) ∧
  (alt_small_eval env s1 e c (s2, Rerr (Rraise err_v)) ⇔
     ∃env' env''.
       e_step_reln^* (env,s1,e,c) (env',s2,Val err_v,[(Craise (), env'')])) ∧
  (alt_small_eval env s1 e c (s2, Rerr (Rabort a)) ⇔
     ∃env' e' c'.
       e_step_reln^* (env,s1,e,c) (env',s2,e',c') ∧
       (e_step (env',s2,e',c') = Eabort a))
End

Theorem small_eval_match_thm:
  !env s v pes err_v r.
    small_eval_match env s v pes err_v r ⇒
    !env2. alt_small_eval env2 s (Val v) [(Cmat () pes err_v,env)] r
Proof
  HO_MATCH_MP_TAC small_eval_match_ind >>
  srw_tac[][alt_small_eval_def]
  >- (qexists_tac `env` >>
      qexists_tac `env` >>
      match_mp_tac RTC_SINGLE >>
      srw_tac[][e_step_reln_def, e_step_def, continue_def])
  >- (PairCases_on `r` >>
      cases_on `r2` >|
      [all_tac,
       cases_on `e'`] >>
      full_simp_tac(srw_ss())[alt_small_eval_def, small_eval_def]
      >- (srw_tac[][Once RTC_CASES1, e_step_reln_def] >>
          srw_tac[][e_step_def, continue_def] >>
          metis_tac[])
      >- (srw_tac[][Once RTC_CASES1, e_step_reln_def] >>
          srw_tac[][e_step_def, continue_def] >>
          metis_tac []) >>
      srw_tac[][] >>
      srw_tac[][Once RTC_CASES1, e_step_reln_def] >>
      qexists_tac `env''` >>
      qexists_tac `e'` >>
      qexists_tac `c'` >>
      srw_tac[][] >>
      srw_tac[][e_step_def, continue_def])
  >- (PairCases_on `r` >>
      cases_on `r2` >|
      [all_tac,
       cases_on `e'`] >>
      full_simp_tac(srw_ss())[alt_small_eval_def] >>
      srw_tac[][Once RTC_CASES1, e_step_reln_def] >> full_simp_tac(srw_ss())[] >|
      [srw_tac[][e_step_def, push_def, continue_def] >>
       metis_tac [],
       srw_tac[][e_step_def, push_def, continue_def] >>
       metis_tac [],
       srw_tac[][] >>
       pop_assum (qspec_then`env`strip_assume_tac) >>
       qexists_tac `env'` >>
       qexists_tac `e'` >>
       qexists_tac `c'` >>
       srw_tac[][] >>
       srw_tac[][e_step_def, push_def, continue_def]])
  >- (qexists_tac `env2` >>
      qexists_tac `Val v` >>
      qexists_tac `[(Cmat () ((p,e)::pes) err_v,env)]` >>
      srw_tac[][RTC_REFL] >>
      srw_tac[][e_step_def, continue_def] >>
      PairCases_on `env` >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [])
  >- (qexists_tac `env2` >>
      qexists_tac `Val v` >>
      qexists_tac `[(Cmat () ((p,e)::pes) err_v,env)]` >>
      srw_tac[][RTC_REFL] >>
      srw_tac[][e_step_def, continue_def] >>
      PairCases_on `env` >>
      full_simp_tac(srw_ss())[])
QED

Triviality result_cases:
  !r.
    (?s v. r = (s, Rval v)) ∨
    (?s v. r = (s, Rerr (Rraise v))) ∨
    (?s a. r = (s, Rerr (Rabort a)))
Proof
  cases_on `r` >>
  srw_tac[][] >>
  cases_on `r'` >>
  full_simp_tac(srw_ss())[] >>
  cases_on `e` >>
  full_simp_tac(srw_ss())[]
QED

Theorem small_eval_opapp_err:
  ∀env s es res.
    small_eval_list env s es res ⇒
    ∀s' vs.
      res = (s',Rval vs) ⇒
      ∀env0 v1 v0.
        LENGTH es + LENGTH v0 ≠ 1 ⇒
        ∃env' e' c'.
          e_step_reln^* (env0,s,Val v1,[Capp Opapp v0 () es,env]) (env',s',e',c') ∧
          e_step (env',s',e',c') = Eabort Rtype_error
Proof
  ho_match_mp_tac small_eval_list_ind >> simp[] >> srw_tac[][] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
  srw_tac[][Once e_step_def,continue_def,application_thm] >>
  Cases_on `v0` >>
  full_simp_tac(srw_ss())[do_opapp_def] >>
  Cases_on`t`>>full_simp_tac(srw_ss())[]) >>
  disj2_tac >>
  srw_tac[][Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp Opapp (v1::v0) () es,env]`strip_assume_tac) >>
  full_simp_tac(srw_ss())[] >>
  first_x_assum(qspecl_then[`env'`,`v`,`v1::v0`]mp_tac) >>
  impl_tac >- simp[] >>
  metis_tac[transitive_RTC,transitive_def]
QED

Theorem small_eval_app_err:
  ∀env s es res.
    small_eval_list env s es res ⇒
    ∀s' vs.
      res = (s',Rval vs) ⇒
      ∀op env0 v1 v0.
        LENGTH es + LENGTH v0 > 2 ∧ op ≠ Opapp
        ∧ op ≠ CopyStrStr ∧ op ≠ CopyStrAw8 ∧ op ≠ CopyAw8Str ∧ op ≠ CopyAw8Aw8
        ⇒
        ∃env' e' c'.
          e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
          e_step (env',s',e',c') = Eabort Rtype_error
Proof
  ho_match_mp_tac small_eval_list_ind >> simp[] >> srw_tac[][] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
  srw_tac[][Once e_step_def,continue_def,application_thm] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  Cases_on`s` \\ fs[do_app_cases] \\ rw[] \\ fs[]) \\
  disj2_tac >>
  srw_tac[][Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp op (v1::v0) () es,env]`strip_assume_tac) >>
  full_simp_tac(srw_ss())[] >>
  first_x_assum(qspecl_then[`op`,`env'`,`v`,`v1::v0`]mp_tac) >>
  impl_tac >- simp[] >>
  metis_tac[transitive_RTC,transitive_def]
QED

Theorem small_eval_app_err_more:
  ∀env s es res.
    small_eval_list env s es res ⇒
    ∀s' vs.
      res = (s',Rval vs) ⇒
      ∀op env0 v1 v0.
        LENGTH es + LENGTH v0 > 4 ∧ op ≠ Opapp
        ⇒
        ∃env' e' c'.
          e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
          e_step (env',s',e',c') = Eabort Rtype_error
Proof
  ho_match_mp_tac small_eval_list_ind >> simp[] >> srw_tac[][] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
  srw_tac[][Once e_step_def,continue_def,application_thm] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  Cases_on`s` \\ fs[do_app_cases] \\ rw[] \\ fs[]) \\
  disj2_tac >>
  srw_tac[][Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp op (v1::v0) () es,env]`strip_assume_tac) >>
  full_simp_tac(srw_ss())[] >>
  first_x_assum(qspecl_then[`op`,`env'`,`v`,`v1::v0`]mp_tac) >>
  impl_tac >- simp[] >>
  metis_tac[transitive_RTC,transitive_def]
QED

Theorem do_app_not_timeout:
  do_app s op vs = SOME (s', Rerr (Rabort a))
  ⇒
  a ≠ Rtimeout_error
Proof
  Cases_on `s` >>
  srw_tac[][do_app_cases] >>
  every_case_tac >>
  srw_tac[][]
QED

Theorem step_e_not_timeout:
  e_step (env',s3,e',c') = Eabort a ⇒ a ≠ Rtimeout_error
Proof
  full_simp_tac(srw_ss())[e_step_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[push_def, return_def, continue_def, application_thm] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  imp_res_tac do_app_not_timeout >>
  srw_tac[][]
QED

Theorem small_eval_list_not_timeout:
  ∀env s es res. small_eval_list env s es res ⇒
    SND res ≠ Rerr (Rabort Rtimeout_error)
Proof
  ho_match_mp_tac small_eval_list_ind >> srw_tac[][] >>
  metis_tac [step_e_not_timeout]
QED

Theorem small_eval_list_app_type_error:
  ∀env s es res.
    small_eval_list env s es res ⇒
    ∀s' err.
      res = (s',Rerr (Rabort a)) ⇒
      ∀op env0 v1 v0.
        ∃env' e' c'.
          e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
          e_step (env',s',e',c') = Eabort a
Proof
  ho_match_mp_tac (theorem"small_eval_list_strongind") >> simp[] >> srw_tac[][] >- (
  srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
  srw_tac[boolSimps.DNF_ss][] >> disj2_tac >>
  imp_res_tac e_step_add_ctxt >>
  Q.PAT_ABBREV_TAC`ctx = [(Capp A B C D,env)]` >>
  first_x_assum(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  first_assum(match_exists_tac o concl) >> srw_tac[][] >>
  metis_tac[e_single_error_add_ctxt] ) >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
  srw_tac[boolSimps.DNF_ss][] >> disj2_tac >>
  srw_tac[][Once RTC_CASES_RTC_TWICE] >>
  imp_res_tac e_step_add_ctxt >>
  Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
  first_x_assum(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  simp[PULL_EXISTS] >>
  first_assum(match_exists_tac o concl) >> srw_tac[][] >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`]
QED

Theorem small_eval_list_app_error:
  ∀env s es res.
    small_eval_list env s es res ⇒
    ∀s' v.
      res = (s',Rerr (Rraise v)) ⇒
      ∀op env0 v1 v0.
        ∃env' env''.
          e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',Val v,[(Craise (),env'')])
Proof
  ho_match_mp_tac (theorem"small_eval_list_strongind") >> simp[] >> srw_tac[][] >- (
  srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  Q.PAT_ABBREV_TAC`ctx = [(Capp A B C D,env)]` >>
  first_x_assum(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  srw_tac[][Once RTC_CASES_RTC_TWICE] >>
  first_assum(match_exists_tac o concl) >> srw_tac[][] >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
  metis_tac[RTC_REFL]) >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
  srw_tac[][Once RTC_CASES_RTC_TWICE] >>
  imp_res_tac e_step_add_ctxt >>
  Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
  first_x_assum(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  first_assum(match_exists_tac o concl) >> srw_tac[][] >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`]
QED

Theorem do_opapp_NONE_tail:
  do_opapp (h::t) = NONE ∧ LENGTH t ≠ 2 ⇒ do_opapp t = NONE
Proof
  srw_tac[][do_opapp_def] >> every_case_tac >> full_simp_tac(srw_ss())[]
QED

Theorem e_step_exp_err_any_ctxt:
  e_step (x,y,Exp z,c1) = Eabort a ⇒ e_step (x,y,Exp z,c2) = Eabort a
Proof
  srw_tac[][e_step_def] >> every_case_tac >>
  full_simp_tac(srw_ss())[push_def,return_def,continue_def,application_thm] >>
  every_case_tac >> full_simp_tac(srw_ss())[]
QED

Theorem do_opapp_too_many:
  !vs'. do_opapp (REVERSE (v''::vs') ++ [v'] ++ [v]) = NONE
Proof
  srw_tac[][] >>
  Induct_on `REVERSE vs'` >>
  srw_tac[][] >>
  `vs' = [] ∨ ?v vs''. vs' = vs''++[v]` by metis_tac [list_end_case] >>
  full_simp_tac(srw_ss())[do_opapp_def] >>
  srw_tac[][REVERSE_APPEND] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[]
QED

Theorem do_app_type_error:
  do_app s op es = SOME (x,Rerr (Rabort a)) ⇒ x = s
Proof
  PairCases_on `s` >>
  srw_tac[][do_app_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[LET_THM,UNCURRY] >>
  every_case_tac >> full_simp_tac(srw_ss())[]
QED

Definition to_small_st_def:
  to_small_st s = (s.refs,s.ffi)
End

Definition to_small_res_def:
  to_small_res r = (to_small_st (FST r), SND r)
End

val s = ``s:'ffi state``;

Theorem big_exp_to_small_exp:
  (∀ck env ^s e r.
     evaluate ck env s e r ⇒
     (ck = F) ⇒ small_eval env (to_small_st s) e [] (to_small_res r)) ∧
  (∀ck env ^s es r.
     evaluate_list ck env s es r ⇒
     (ck = F) ⇒ small_eval_list env (to_small_st s) es (to_small_res r)) ∧
  (∀ck env ^s v pes err_v r.
     evaluate_match ck env s v pes err_v r ⇒
     (ck = F) ⇒ small_eval_match env (to_small_st s) v pes err_v (to_small_res r))
Proof
   ho_match_mp_tac evaluate_ind >>
   srw_tac[][small_eval_log, small_eval_if, small_eval_match, small_eval_lannot,
             small_eval_handle, small_eval_let, small_eval_letrec, small_eval_tannot, to_small_res_def, small_eval_raise]
   >- (srw_tac[][return_def, small_eval_def, Once RTC_CASES1, e_step_reln_def, e_step_def] >>
       metis_tac [RTC_REFL])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Craise (),env)]) (to_small_st s2, Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Chandle () pes,env)]) (env',to_small_st s2,Val v,[(Chandle () pes,env)])`
                   by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s2,Val v,[(Chandle () pes,env)]) (env,to_small_st s2,Val v,[])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
       metis_tac [transitive_def, transitive_RTC, RTC_SINGLE])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Chandle () pes,env)])
                      (env',to_small_st s',Val v,[(Craise (),env'');(Chandle () pes,env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s',Val v,[(Craise (),env'');(Chandle () pes,env)])
                    (env'',to_small_st s',Val v,[(Cmat_check () pes v, env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
       `e_step_reln (env'',to_small_st s',Val v,[(Cmat_check () pes v, env)])
                    (env,to_small_st s',Val v,[(Cmat () pes v, env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]
                       \\ fs [to_small_st_def]) >>
       imp_res_tac small_eval_match_thm >>
       Q.ISPEC_THEN`r`assume_tac result_cases >>
       srw_tac[][] >>
       full_simp_tac(srw_ss())[small_eval_def, alt_small_eval_def] >>
       metis_tac [transitive_def, transitive_RTC, RTC_SINGLE])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Chandle () pes,env)]) (env',to_small_st s2,e',c'++[(Chandle () pes,env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
        metis_tac [APPEND, e_step_add_ctxt, transitive_RTC,
                   transitive_def, e_single_error_add_ctxt])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Chandle () pes,env)])
                      (env',to_small_st s2,Val v,[(Craise (),env'');(Chandle () pes,env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s2,Val v,[(Craise (),env'');(Chandle () pes,env)])
                    (env'',to_small_st s2,Val v,[(Cmat_check () pes v, env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
        `e_step (env'',to_small_st s2,Val v,[(Cmat_check () pes v, env)]) =
         Eabort Rtype_error` by
          (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]
           \\ fs [to_small_st_def]) >>
        goal_assum (first_assum o mp_then Any mp_tac) >>
        metis_tac [transitive_def, transitive_RTC, RTC_SINGLE])
   >- (`es = [] ∨ ?e es'. es = es' ++ [e]` by metis_tac [list_end_case] >>
       full_simp_tac(srw_ss())[LENGTH] >>
       srw_tac[][small_eval_con] >|
       [srw_tac[][small_eval_def] >>
            full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
            srw_tac[][return_def, small_eval_def, Once RTC_CASES1, e_step_reln_def, e_step_def] >>
            metis_tac [RTC_REFL],
        full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
            srw_tac[][small_eval_def] >>
            qexists_tac `env` >>
            match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] small_eval_list_step) >>
            MAP_EVERY qexists_tac [`s2`, `v'`, `vs'`, `env'`] >>
            srw_tac[][] >>
            full_simp_tac(srw_ss())[] >>
            imp_res_tac small_eval_list_length >>
            full_simp_tac(srw_ss())[] >>
            metis_tac [arithmeticTheory.ADD_COMM]])
   >- (srw_tac[][small_eval_def, e_step_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Con cn es)` >>
       srw_tac[][] >>
       metis_tac [RTC_REFL])
   >- (`es = [] ∨ ?e es'. es = es' ++ [e]` by metis_tac [list_end_case] >>
       srw_tac[][small_eval_con] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
       srw_tac[][small_eval_def] >|
       [`e_step_reln^* (env,to_small_st s,Exp e,[(Ccon cn [] () (REVERSE es'),env)])
                       (env',to_small_st s',Val err_v,[(Craise (), env'');(Ccon cn [] () (REVERSE es'),env)])`
                   by metis_tac [APPEND,e_step_add_ctxt] >>
            `e_step_reln (env',to_small_st s',Val err_v,[(Craise (), env'');(Ccon cn [] () (REVERSE es'),env)])
                         (env'',to_small_st s',Val err_v,[(Craise (), env'')])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
            metis_tac [transitive_def, transitive_RTC, RTC_SINGLE],
        `LENGTH ([]:v list) + 1 + LENGTH es' = SUC (LENGTH es')` by
                   (full_simp_tac(srw_ss())[] >>
                    DECIDE_TAC) >>
            metis_tac [small_eval_list_err, LENGTH_REVERSE, arithmeticTheory.ADD1],
        metis_tac [APPEND, e_step_add_ctxt, transitive_RTC, transitive_def, e_single_error_add_ctxt],
        `LENGTH ([]:v list) + 1 + LENGTH es' = SUC (LENGTH es')` by
                   (full_simp_tac(srw_ss())[] >>
                    DECIDE_TAC) >>
            metis_tac [small_eval_list_terr, arithmeticTheory.ADD1, LENGTH_REVERSE]])
   >- (srw_tac[][small_eval_def] >>
       qexists_tac `env` >>
       srw_tac[][Once RTC_CASES1, e_step_reln_def, return_def, e_step_def])
   >- (srw_tac[][small_eval_def, e_step_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Var n)` >>
       srw_tac[][] >>
       metis_tac [RTC_REFL])
   >- (srw_tac[][small_eval_def] >>
       qexists_tac `env` >>
       srw_tac[][Once RTC_CASES1, e_step_reln_def, return_def, e_step_def])
   >- (
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >- full_simp_tac(srw_ss())[do_opapp_def] >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >- full_simp_tac(srw_ss())[do_opapp_def] >>
     reverse(full_simp_tac(srw_ss())[Once small_eval_list_cases, SWAP_REVERSE_SYM]) >> srw_tac[][]
     >- metis_tac [do_opapp_too_many, NOT_SOME_NONE] >>
     srw_tac[][Once small_eval_app] >>
     match_mp_tac small_eval_prefix >>
     Q.PAT_ABBREV_TAC`ctx = (Capp B X Y Z,env)` >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[ctx]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     qabbrev_tac`ctx2 = (Capp Opapp [v] () [],env)` >>
     `e_step_reln^* (env'',s2',Val v,[ctx]) (env,s2',Exp e'',[ctx2])` by (
       simp[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] ) >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[ctx2]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     qmatch_assum_abbrev_tac`e_step_reln^* b c` >>
     qmatch_assum_abbrev_tac`e_step_reln^* a b` >>
     `e_step_reln^* a c` by metis_tac[transitive_RTC, transitive_def] >>
     qpat_x_assum`X b c`kall_tac >>
     qpat_x_assum`X a b`kall_tac >>
     qunabbrev_tac`b` >>
     ONCE_REWRITE_TAC[CONJ_COMM] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     qmatch_assum_abbrev_tac`e_step_reln^* d a` >>
     qmatch_abbrev_tac`e_step_reln^* d f` >>
     qsuff_tac`e_step_reln^* c f` >- metis_tac[transitive_RTC,transitive_def] >>
     unabbrev_all_tac >>
     simp[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,application_thm] )
   >- (
     full_simp_tac(srw_ss())[] >>
     srw_tac[][small_eval_def] >>
     srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,
        application_thm,do_opapp_def] >>
     srw_tac[boolSimps.DNF_ss][] >>
     srw_tac[][Once e_step_def,application_thm,do_opapp_def] >>
     BasicProvers.CASE_TAC >- full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
     disj2_tac >>
     srw_tac[][push_def] >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
     first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[(Capp Opapp [] () t,env)]`strip_assume_tac) >>
     full_simp_tac(srw_ss())[] >> srw_tac[][] >>
     Cases_on`LENGTH t = 1` >- (
       Cases_on`t`>>full_simp_tac(srw_ss())[LENGTH_NIL]>>srw_tac[][]>>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       qmatch_assum_abbrev_tac`e_step_reln^* a b` >>
       qpat_x_assum`e_step_reln^* a b`mp_tac >>
       first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`[Capp Opapp [v] () [],env]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
       qmatch_assum_abbrev_tac`e_step_reln^* c d` >>
       `e_step_reln^* b c` by (
         srw_tac[][Once RTC_CASES1,Abbr`b`,e_step_reln_def,e_step_def] >>
         srw_tac[][continue_def,push_def] ) >>
       strip_tac >>
       `e_step_reln^* a d` by metis_tac[transitive_RTC,transitive_def] >>
       qunabbrev_tac`d` >>
       first_assum(match_exists_tac o concl) >>
       simp[e_step_def,continue_def,application_thm] ) >>
     imp_res_tac small_eval_opapp_err >> full_simp_tac(srw_ss())[] >>
     first_x_assum(qspec_then`[]`mp_tac) >> simp[] >>
     disch_then(qspecl_then[`v`,`env'`]strip_assume_tac) >>
     metis_tac[transitive_RTC,transitive_def])
   >- (
     full_simp_tac(srw_ss())[SWAP_REVERSE_SYM, Once small_eval_list_cases] >> srw_tac[][] >- full_simp_tac(srw_ss())[do_app_def] >>
     srw_tac[][Once small_eval_app] >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >- (
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
       Cases_on`res`>> TRY(Cases_on`e'`) >>
       srw_tac[][small_eval_def] >>
       TRY (
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES2] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
         simp[application_thm,do_app_def,store_alloc_def,return_def,to_small_st_def] ) >>
       `(refs',ffi') = (s2.refs,s2.ffi)` by (
         imp_res_tac do_app_type_error ) >> full_simp_tac(srw_ss())[] >>
       full_simp_tac(srw_ss())[to_small_st_def] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[Once e_step_def,continue_def,Abbr`ctx`,application_thm]) >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >- (
       srw_tac[][small_eval_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
       Cases_on`res`>> TRY(Cases_on`e''`) >>
       srw_tac[][small_eval_def] >>
       TRY (
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] >>
         Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
         last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
         disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES2] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,application_thm,return_def,to_small_st_def] ) >>
       `(refs',ffi') = (s2.refs,s2.ffi)` by (
         imp_res_tac do_app_type_error ) >> full_simp_tac(srw_ss())[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
       simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] >>
       simp[Once e_step_def,continue_def,push_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
       full_simp_tac(srw_ss())[to_small_st_def] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[e_step_def,continue_def,Abbr`ctx`,application_thm]) >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >- (
       srw_tac[][small_eval_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
       Cases_on`res`>> TRY(Cases_on`e'''`) >>
       srw_tac[][small_eval_def] >>
       TRY (
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] >>
         Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
         last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
         disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] >>
         Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
         last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
         disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES2] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,application_thm,return_def,to_small_st_def] ) >>
       `(refs',ffi') = (s2.refs,s2.ffi)` by (
         imp_res_tac do_app_type_error ) >> full_simp_tac(srw_ss())[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
       simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] >>
       simp[Once e_step_def,continue_def,push_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
       simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] >>
       simp[Once e_step_def,continue_def,push_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
       full_simp_tac(srw_ss())[to_small_st_def] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[e_step_def,continue_def,Abbr`ctx`,application_thm]) >>
     full_simp_tac(srw_ss())[do_app_cases] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
     rw[small_eval_def] \\
     Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
     asm_exists_tac \\ simp[] \\
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
     TRY disj2_tac \\
     simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] \\
     Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
     asm_exists_tac \\ simp[] \\
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
     TRY disj2_tac \\
     simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] \\
     Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
     asm_exists_tac \\ simp[] \\
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
     TRY disj2_tac \\
     simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] \\
     Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
     asm_exists_tac \\ simp[] \\
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
     TRY disj2_tac \\
     simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] \\
     fs[Once small_eval_list_cases] \\ rw[] \\
     fs[Once small_eval_list_cases] \\ rw[] \\
     Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
     asm_exists_tac \\ simp[] \\
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
     TRY disj2_tac \\
     simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] \\
     simp[application_thm,do_app_def,to_small_st_def,return_def] \\
     simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1])
   >- (
     full_simp_tac(srw_ss())[] >>
     srw_tac[][small_eval_def] >>
     srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,application_thm,do_app_def] >>
     srw_tac[boolSimps.DNF_ss][] >>
     srw_tac[][Once e_step_def,application_thm,do_app_def] >>
     Cases_on`REVERSE es` >- (
       full_simp_tac(srw_ss())[Once small_eval_list_cases,to_small_st_def] >> rev_full_simp_tac(srw_ss())[] ) >>
     disj2_tac >>
     srw_tac[][push_def] >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases, SWAP_REVERSE_SYM] >>
     first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[(Capp op [] () t,env)]`strip_assume_tac) >>
     full_simp_tac(srw_ss())[] >> srw_tac[][] >>
     Cases_on`vs'` >- (
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >>
       srw_tac[][e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       srw_tac[][e_step_def,continue_def,application_thm,to_small_st_def] ) >>
     Cases_on`t'` >- (
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >>
       srw_tac[][e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       srw_tac[boolSimps.DNF_ss][push_def] >> disj2_tac >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp op X Y Z,env)]` >>
       last_x_assum(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) >> full_simp_tac(srw_ss())[] >>
       first_assum(match_exists_tac o concl) >>
       srw_tac[][e_step_def,continue_def,Abbr`ctx`,application_thm,to_small_st_def] ) >>
     Cases_on`t''` >- (
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases] >> srw_tac[][] >>
       srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >>
       srw_tac[][e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       srw_tac[boolSimps.DNF_ss][push_def] >> disj2_tac >>
       srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp op X Y Z,env)]` >>
       qpat_x_assum`e_step_reln^* (env,X,Exp e,[]) Y`(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) >> full_simp_tac(srw_ss())[] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,Abbr`ctx`,continue_def,application_thm] >>
       srw_tac[boolSimps.DNF_ss][push_def] >> disj2_tac >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp op X Y Z,env)]` >>
       qpat_x_assum`e_step_reln^* (env,_,Exp _,[]) _`(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) >> full_simp_tac(srw_ss())[] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       srw_tac[][e_step_def,continue_def,Abbr`ctx`,application_thm,to_small_st_def] ) >>
     Cases_on`op = CopyStrStr ∨ op = CopyStrAw8 ∨ op = CopyAw8Str ∨ op = CopyAw8Aw8` >- (
       pop_assum(fn th => assume_tac(ONCE_REWRITE_RULE[GSYM markerTheory.Abbrev_def]th))
       \\ fs[Once small_eval_list_cases]
       \\ fs[Once small_eval_list_cases]
       \\ fs[Once small_eval_list_cases]
       \\ rveq
       \\ qpat_abbrev_tac`ctx = [Capp _ _ _ _,env]`
       \\ srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE]
       \\ asm_exists_tac \\ simp[]
       \\ srw_tac[DNF_ss][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def]
       \\ disj2_tac
       \\ qpat_abbrev_tac`ctx = [Capp _ _ _ _,_]`
       \\ srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE]
       \\ last_x_assum(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) \\ fs[]
       \\ asm_exists_tac \\ simp[]
       \\ srw_tac[DNF_ss][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def]
       \\ disj2_tac
       \\ qpat_abbrev_tac`ctx = [Capp _ _ _ _,_]`
       \\ srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE]
       \\ last_x_assum(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) \\ fs[]
       \\ asm_exists_tac \\ simp[]
       \\ srw_tac[DNF_ss][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def]
       \\ disj2_tac
       \\ qpat_abbrev_tac`ctx = [Capp _ _ _ _,_]`
       \\ srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE]
       \\ last_x_assum(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) \\ fs[]
       \\ asm_exists_tac \\ simp[]
       \\ srw_tac[DNF_ss][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def]
       \\ simp[Once e_step_def,continue_def,application_thm,to_small_st_def]
       \\ fs[Once small_eval_list_cases] \\ rveq \\ fs[to_small_st_def]
       \\ simp[push_def]
       \\ qpat_abbrev_tac`ctx = [Capp _ _ _ _,_]`
       \\ srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE]
       \\ last_x_assum(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) \\ fs[]
       \\ asm_exists_tac \\ simp[]
       \\ srw_tac[DNF_ss][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def]
       \\ simp[Once e_step_def,continue_def,application_thm,to_small_st_def]
       \\ fs[Once small_eval_list_cases] \\ rveq \\ fs[to_small_st_def]
       \\ simp[push_def]
       \\ qpat_abbrev_tac`ctx = [Capp _ _ _ _,_]`
       \\ srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE]
       \\ last_x_assum(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) \\ fs[]
       \\ asm_exists_tac \\ simp[]
       \\ simp[Abbr`ctx`]
       \\ match_mp_tac (MP_CANON small_eval_app_err_more)
       \\ asm_exists_tac \\ simp[]) \\
     fs[] \\
     imp_res_tac small_eval_app_err >> full_simp_tac(srw_ss())[] >>
     first_x_assum(qspec_then`op`mp_tac) >> simp[] >>
     disch_then(qspec_then`[]`strip_assume_tac) >>
     full_simp_tac(srw_ss())[] >>
     `LENGTH t > 2`
                by (imp_res_tac small_eval_list_length >>
                    full_simp_tac(srw_ss())[] >>
                    DECIDE_TAC) >>
     full_simp_tac(srw_ss())[] >>
     metis_tac[transitive_RTC,transitive_def,to_small_st_def])
   >- (
     full_simp_tac(srw_ss())[] >>
     srw_tac[][Once small_eval_app] >>
     `es = [] ∨ ?e es'. es = es'++[e]` by metis_tac [list_end_case]
     >- full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
     srw_tac[][] >>
     Cases_on`err`>>srw_tac[][small_eval_def] >>
     TRY (imp_res_tac small_eval_list_not_timeout >> full_simp_tac(srw_ss())[] >> NO_TAC) >>
     full_simp_tac(srw_ss())[Once small_eval_list_cases] >>
     TRY (
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>full_simp_tac(srw_ss())[] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       metis_tac[e_single_error_add_ctxt] ) >>
     TRY (
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>full_simp_tac(srw_ss())[] >>
       srw_tac[][Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
       metis_tac[RTC_REFL]) >>
     TRY (
       imp_res_tac small_eval_list_app_type_error >> full_simp_tac(srw_ss())[] >>
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>full_simp_tac(srw_ss())[] >>
       srw_tac[][Once RTC_CASES_RTC_TWICE,PULL_EXISTS] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
       NO_TAC ) >>
     imp_res_tac small_eval_list_app_error >> full_simp_tac(srw_ss())[] >>
     imp_res_tac e_step_add_ctxt >>
     Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
     first_x_assum(qspec_then`ctx`strip_assume_tac)>>full_simp_tac(srw_ss())[] >>
     srw_tac[][Once RTC_CASES_RTC_TWICE,PULL_EXISTS] >>
     first_assum(match_exists_tac o concl) >> srw_tac[][] >>
     srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s',Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',Val v,[(Clog op () e2,env)])
                    (env,to_small_st s',Exp e',[])`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def] >>
       every_case_tac >>
       srw_tac[][] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def, small_eval_prefix])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s2,Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s2,Val v,[(Clog op () e2,env)])
                    (env,to_small_st s2,Val bv,[])`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, return_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def, small_eval_prefix])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s2,Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step (env',to_small_st s2,Val v,[(Clog op () e2,env)]) = Eabort Rtype_error`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Clog op () e2,env)]) (to_small_st s', Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Cif () e2 e3,env)])
                      (env',to_small_st s',Val v,[(Cif () e2 e3,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',Val v,[(Cif () e2 e3,env)])
                    (env,to_small_st s',Exp e',[])`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def] >>
       every_case_tac >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def,
                  small_eval_prefix])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Cif () e2 e3,env)])
                      (env',to_small_st s2,Val v,[(Cif () e2 e3,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step (env',to_small_st s2,Val v,[(Cif () e2 e3,env)]) = Eabort Rtype_error`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Cif () e2 e3,env)]) (to_small_st s', Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
   >- (full_simp_tac(srw_ss())[small_eval_def, bind_exn_v_def] >>
       imp_res_tac small_eval_match_thm >>
       PairCases_on `r` >>
       full_simp_tac(srw_ss())[] >>
       cases_on `r1` >|
       [all_tac,
        cases_on `e'`] >>
       srw_tac[][] >>
       full_simp_tac(srw_ss())[small_eval_def, alt_small_eval_def] >>
       `e_step_reln^*
          (env,to_small_st s,Exp e,[(Cmat_check () pes (Conv (SOME bind_stamp) []),env)])
          (env',to_small_st s',Val v,[(Cmat_check () pes (Conv (SOME bind_stamp) []),env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln
          (env',to_small_st s',Val v,[(Cmat_check () pes (Conv (SOME bind_stamp) []),env)])
          (env,to_small_st s',Val v,[(Cmat () pes (Conv (SOME bind_stamp) []),env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]
                       \\ fs [to_small_st_def]) >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (match_mp_tac (small_eval_err_add_ctxt |> SPEC_ALL |> Q.INST [`c`|->`[]`]
          |> SIMP_RULE std_ss [APPEND]) \\ fs [])
   >- (full_simp_tac(srw_ss())[small_eval_def, bind_exn_v_def]
       \\ qexists_tac `env'`
       \\ qexists_tac `Val v`
       \\ qexists_tac `[(Cmat_check () pes (Conv (SOME bind_stamp) []),env)]`
       \\ srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]
       \\ fs [to_small_st_def]
       \\ metis_tac [e_step_add_ctxt, APPEND])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Clet n () e',env)])
                      (env',to_small_st s',Val v,[(Clet n () e',env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',Val v,[(Clet n () e',env)])
                    (env with v := nsOptBind n v env.v,to_small_st s',Exp e',[])`
               by srw_tac[][e_step_def, e_step_reln_def, continue_def, push_def] >>
       Q.ISPEC_THEN`r`assume_tac result_cases >>
       full_simp_tac(srw_ss())[small_eval_def, sem_env_component_equality] >>
       full_simp_tac(srw_ss())[small_eval_def, sem_env_component_equality] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Clet n () e2,env)]) (to_small_st s', Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
   >- (srw_tac[][small_eval_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Letrec funs e)` >>
       qexists_tac `[]` >>
       srw_tac[][RTC_REFL, e_step_def])
   >- (
     fs []
     >> Cases_on `SND r`
     >| [all_tac,
        cases_on `e'`]
     >- (
       fs [small_eval_def]
       >> simp [Once RTC_CASES2]
       >> qexists_tac `env`
       >> qexists_tac `(env',to_small_st (FST r),Val a,[(Ctannot () t,env)])`
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> simp [e_step_reln_def, e_step_def, continue_def, return_def])
     >- (
       fs [small_eval_def]
       >> simp [Once RTC_CASES2]
       >> qexists_tac `env''`
       >> qexists_tac `env''`
       >> qexists_tac `(env',to_small_st (FST r),Val a,[(Craise (), env''); (Ctannot () t,env)])`
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> simp [e_step_reln_def, e_step_def, continue_def, return_def])
     >- (
       fs [small_eval_def]
       >> qexists_tac `env'`
       >> qexists_tac `e'`
       >> qexists_tac `c'++[(Ctannot () t,env)]`
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> metis_tac [e_single_error_add_ctxt]))
   >- (
     fs []
     >> Cases_on `SND r`
     >| [all_tac,
        cases_on `e'`]
     >- (
       fs [small_eval_def]
       >> simp [Once RTC_CASES2]
       >> qexists_tac `env`
       >> qexists_tac `(env',to_small_st (FST r),Val a,[(Clannot () l,env)])`
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> simp [e_step_reln_def, e_step_def, continue_def, return_def])
     >- (
       fs [small_eval_def]
       >> simp [Once RTC_CASES2]
       >> qexists_tac `env''`
       >> qexists_tac `env''`
       >> qexists_tac `(env',to_small_st (FST r),Val a,[(Craise (), env''); (Clannot () l,env)])`
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> simp [e_step_reln_def, e_step_def, continue_def, return_def])
     >- (
       fs [small_eval_def]
       >> qexists_tac `env'`
       >> qexists_tac `e'`
       >> qexists_tac `c'++[(Clannot () l,env)]`
       >> rw []
       >- metis_tac [APPEND,e_step_add_ctxt]
       >> metis_tac [e_single_error_add_ctxt]))
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules])
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules])
   >- (cases_on `err` >>
       full_simp_tac(srw_ss())[small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules])
   >- (cases_on `err` >>
       full_simp_tac(srw_ss())[small_eval_def] >-
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules] >-
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules] >>
       full_simp_tac(srw_ss())[Once small_eval_list_cases])
   >- metis_tac [small_eval_match_rules]
   >- metis_tac [small_eval_match_rules, FST, pair_CASES, to_small_st_def]
   >- metis_tac [small_eval_match_rules, FST, pair_CASES, to_small_st_def]
   >- metis_tac [small_eval_match_rules, FST, pair_CASES, to_small_st_def]
   >- metis_tac [small_eval_match_rules]
QED

Theorem evaluate_ctxts_cons:
  !s1 f cs res1 bv.
    evaluate_ctxts s1 (f::cs) res1 bv =
    ((?c s2 env v' res2 v.
        (res1 = Rval v) ∧
        (f = (c,env)) ∧
        evaluate_ctxt env s1 c v (s2, res2) ∧
        evaluate_ctxts s2 cs res2 bv) ∨
     (?c env err.
        (res1 = Rerr err) ∧
        (f = (c,env)) ∧
        ((∀pes. c ≠ Chandle () pes) ∨ ∀v. err ≠ Rraise v) ∧
        evaluate_ctxts s1 cs res1 bv) ∨
     (?pes s2 env v' res2 v.
        (res1 = Rerr (Rraise v)) ∧
        (f = (Chandle () pes,env)) ∧
        can_pmatch_all env.c s1.refs (MAP FST pes) v ∧
        evaluate_match F env s1 v pes v (s2, res2) ∧
        evaluate_ctxts s2 cs res2 bv) ∨
     (?pes env v' res2 v.
        (res1 = Rerr (Rraise v)) ∧
        (f = (Chandle () pes,env)) ∧
        ~can_pmatch_all env.c s1.refs (MAP FST pes) v ∧
        evaluate_ctxts s1 cs (Rerr (Rabort Rtype_error)) bv))
Proof
  srw_tac[][] >>
  srw_tac[][Once evaluate_ctxts_cases] >>
  EQ_TAC >>
  srw_tac[][] >>
  metis_tac []
QED

val tac1 =
full_simp_tac(srw_ss())[evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_ctxts_cases, evaluate_ctxt_cases] >>
srw_tac[][] >>
metis_tac [oneTheory.one];

val tac3 =
full_simp_tac(srw_ss())[evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
srw_tac[][] >>
full_simp_tac(srw_ss())[evaluate_ctxts_cons, evaluate_ctxt_cases] >>
ONCE_REWRITE_TAC [hd (tl (CONJUNCTS evaluate_cases))] >>
srw_tac[][] >>
full_simp_tac(srw_ss())[evaluate_ctxts_cons, evaluate_ctxt_cases] >>
srw_tac [boolSimps.DNF_ss] [] >>
metis_tac [DECIDE ``SUC x = x + 1``, pair_CASES, REVERSE_APPEND];

Theorem evaluate_state_app_cons:
  evaluate_state (env,s,Exp e,(Capp op [] () es,env)::c) bv
  ⇒ evaluate_state (env,s,Exp (App op (REVERSE es++[e])),c) bv
Proof
  srw_tac[][evaluate_state_cases] >>
  srw_tac[][Once evaluate_cases] >>
  full_simp_tac(srw_ss())[evaluate_ctxts_cons] >> srw_tac[][] >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> srw_tac[][] >- (
  full_simp_tac(srw_ss())[Once evaluate_ctxt_cases, REVERSE_REVERSE, REVERSE_APPEND] >> srw_tac[][] >>
  srw_tac[][Once evaluate_cases,PULL_EXISTS] >>
  full_simp_tac(srw_ss())[] >>
  TRY (
    disj1_tac >>
    CONV_TAC(STRIP_QUANT_CONV
             (move_conj_left(same_const``bigStep$evaluate`` o fst o strip_comb))) >>
    first_assum(match_exists_tac o concl) >> srw_tac[][] >>
    TRY(first_assum(split_pair_match o concl)) >>
    TRY(CONV_TAC(STRIP_QUANT_CONV
                 (move_conj_left(same_const``bigStep$evaluate_list`` o fst o strip_comb)))) >>
    first_assum(match_exists_tac o concl) >> srw_tac[][] >> NO_TAC) >>
  TRY (
    disj2_tac >> disj1_tac >>
    srw_tac[][Once evaluate_cases,PULL_EXISTS] >>
    first_assum(match_exists_tac o concl) >> srw_tac[][] >>
    first_assum(match_exists_tac o concl) >> srw_tac[][] >> NO_TAC ) >>
  rpt disj2_tac >>
  srw_tac[][Once evaluate_cases] >> disj2_tac >>
  first_assum(match_exists_tac o concl) >> srw_tac[][]) >>
  rpt disj2_tac >>
  srw_tac[][Once evaluate_cases]
QED

Theorem one_step_backward:
  !env s e c s' env' e' c' bv.
    (e_step (env,s,e,c) = Estep (env',s',e',c')) ∧
    evaluate_state (env',s',e',c') bv
    ⇒
    evaluate_state (env,s,e,c) bv
Proof
  srw_tac[][e_step_def] >>
  cases_on `e` >>
  full_simp_tac(srw_ss())[]
  >- (cases_on `e''` >>
      full_simp_tac(srw_ss())[push_def, return_def] >>
      srw_tac[][]
      >- (fs[evaluate_ctxts_cons, evaluate_state_cases, evaluate_ctxt_cases] >>
          srw_tac[][Once evaluate_cases] >>
          metis_tac [])
      >- (fs[evaluate_ctxts_cons, evaluate_state_cases, evaluate_ctxt_cases] >>
          rveq \\ fs [] \\ TRY (goal_assum (first_assum o mp_then Any mp_tac))
          >- (srw_tac[][Once evaluate_cases] \\ metis_tac [])
          >- (srw_tac[][Once evaluate_cases] \\ Cases_on `err` \\ fs [] \\ metis_tac [])
          >- (srw_tac[][Once evaluate_cases] \\ metis_tac [])
          \\ srw_tac[][Once evaluate_cases] \\ metis_tac [])
      >- tac3
      >- (every_case_tac >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[SWAP_REVERSE_SYM] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[] >>
          tac3)
      >- (every_case_tac >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          tac3)
      >- tac3
      >- (
       Cases_on `s` >>
       Cases_on `REVERSE l` >>
       full_simp_tac(srw_ss())[application_thm,do_opapp_def,do_app_def] >>
       srw_tac[][] >>
       full_simp_tac(srw_ss())[SWAP_REVERSE_SYM] >>
       metis_tac[evaluate_state_app_cons])
      >- tac3
      >- tac3
      >- tac3
      >- tac3
      >- (every_case_tac >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          tac3)
      >- tac3
      >- tac3)
  >- (full_simp_tac(srw_ss())[continue_def] >>
      cases_on `c` >>
      full_simp_tac(srw_ss())[] >>
      cases_on `h` >>
      full_simp_tac(srw_ss())[] >>
      cases_on `q` >>
      full_simp_tac(srw_ss())[] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[push_def, return_def, application_def] >>
      srw_tac[][] >>
      full_simp_tac (srw_ss() ++ ARITH_ss) [evaluate_state_cases, evaluate_ctxts_cons, evaluate_ctxt_cases, oneTheory.one,
                                            evaluate_ctxts_cons, evaluate_ctxt_cases, arithmeticTheory.ADD1]
      >- metis_tac []
      >- (rveq \\ fs [])
      >- (
       srw_tac[][] >>
       every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
       full_simp_tac(srw_ss())[do_app_def] >> every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
       srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
       srw_tac[][Once evaluate_cases] >>
       metis_tac[] )
      >- (
       srw_tac[][] >>
       every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
       srw_tac[][Once(CONJUNCT2 evaluate_cases)] >>
       srw_tac[][Once(CONJUNCT2 evaluate_cases)] >>
       srw_tac[][Once(CONJUNCT2 evaluate_cases)] >>
       full_simp_tac(srw_ss())[evaluate_ctxts_cons] >>
       full_simp_tac(srw_ss())[Once evaluate_ctxt_cases] >> srw_tac[][] >>
       metis_tac [pair_CASES]
       )
      >- (
       srw_tac[][Once evaluate_cases,PULL_EXISTS] >>
       srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] )
      >- (
       srw_tac[][Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >> disj2_tac >> disj1_tac >>
       srw_tac[][Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       first_assum(match_exists_tac o concl) >> srw_tac[][] >>
       metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC])
      >- (
       srw_tac[][Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
       metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC])
      >- (
       srw_tac[][Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >> disj2_tac >> disj1_tac >>
       srw_tac[][Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >>
       metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC])
      >- (
       srw_tac[boolSimps.DNF_ss][] >>
       rpt disj2_tac >>
       srw_tac[][Once evaluate_cases] >>
       metis_tac[])
      >- (
       srw_tac[boolSimps.DNF_ss][] >>
       rpt disj2_tac >>
       srw_tac[][Once evaluate_cases] >>
       metis_tac[])
      >- metis_tac []
      >- metis_tac []
      >- (fs [] \\ rfs [] \\ asm_exists_tac \\ fs [])
      >- (ONCE_REWRITE_TAC [evaluate_cases] >>
          srw_tac[][])
      >- (ONCE_REWRITE_TAC [evaluate_cases] >>
          srw_tac[][] >>
          metis_tac [FST])
      >- (ONCE_REWRITE_TAC [evaluate_cases] >>
          srw_tac[][] >> full_simp_tac(srw_ss())[] >> metis_tac [])
      >- metis_tac [] >>
      every_case_tac >>
      full_simp_tac (srw_ss()++ARITH_ss++boolSimps.DNF_ss) [] >>
      ONCE_REWRITE_TAC [evaluate_cases] >>
      srw_tac[][] >>
      metis_tac [APPEND_ASSOC, APPEND, REVERSE_APPEND, REVERSE_REVERSE, REVERSE_DEF])
QED

Theorem evaluate_ctxts_type_error:
  !a s c. evaluate_ctxts s c (Rerr (Rabort a)) (s,Rerr (Rabort a))
Proof
  induct_on `c` >>
  srw_tac[][] >>
  srw_tac[][Once evaluate_ctxts_cases] >>
  PairCases_on `h` >>
  srw_tac[][]
QED

Theorem evaluate_ctxts_type_error_matchable:
  !a s c. s' = s ⇒ evaluate_ctxts s c (Rerr (Rabort a)) (s',Rerr (Rabort a))
Proof
  metis_tac[evaluate_ctxts_type_error]
QED

Theorem one_step_backward_type_error:
  !env s e c.
    (e_step (env,to_small_st s,e,c) = Eabort a) ∧ s.eval_state = NONE
    ⇒
    evaluate_state (env,to_small_st s,e,c)
                   ((s with <| next_type_stamp := 0; next_exn_stamp := 0; clock := 0 |>),
                    Rerr (Rabort a))
Proof
  srw_tac[][e_step_def] >>
  cases_on `e` >>
  full_simp_tac(srw_ss())[]
  >- (
  reverse (cases_on `e'`) >>
  full_simp_tac(srw_ss())[push_def, return_def] >>
  every_case_tac >>
  srw_tac[][evaluate_state_cases] >>
  srw_tac[][Once evaluate_cases] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][to_small_st_def]
  >> TRY (
    match_mp_tac evaluate_ctxts_type_error_matchable >>
    srw_tac[][state_component_equality] )
  >- (
    full_simp_tac(srw_ss())[application_thm] >>
    pop_assum mp_tac >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[to_small_st_def] >> srw_tac[][] >>
    TRY(full_simp_tac(srw_ss())[do_app_def]>>NO_TAC) >>
    srw_tac[][Once evaluate_cases] >>
    srw_tac[][Once evaluate_cases] >>
    srw_tac[][Once evaluate_cases] >>
    full_simp_tac(srw_ss())[return_def] >>
    match_mp_tac evaluate_ctxts_type_error_matchable >>
    srw_tac[][state_component_equality] ) >>
  metis_tac[do_con_check_build_conv,NOT_SOME_NONE]) >>
  full_simp_tac(srw_ss())[continue_def] >>
  cases_on `c` >> full_simp_tac(srw_ss())[] >>
  cases_on `h` >> full_simp_tac(srw_ss())[] >>
  cases_on `q` >> full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[evaluate_state_cases, push_def, return_def] >>
  srw_tac[][evaluate_ctxts_cons, evaluate_ctxt_cases, to_small_st_def] >>
  srw_tac[][PULL_EXISTS] >- (
  full_simp_tac(srw_ss())[application_thm] >>
  every_case_tac >> full_simp_tac(srw_ss())[return_def] >>
  srw_tac[][oneTheory.one] >>
  srw_tac[][Once evaluate_cases] >>
  srw_tac[][Once evaluate_cases] >>
  srw_tac[][Once evaluate_cases] >>
  imp_res_tac do_app_type_error >>
  imp_res_tac do_app_not_timeout >>
  full_simp_tac(srw_ss())[to_small_st_def] >> srw_tac[][] >>
  srw_tac[DNF_ss][] >>
  match_mp_tac evaluate_ctxts_type_error_matchable >>
  srw_tac[][state_component_equality] ) >>
  srw_tac[][Once evaluate_cases] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [arithmeticTheory.ADD1,to_small_st_def] >>
  srw_tac[][Once evaluate_cases] >>
  srw_tac[DNF_ss][] >> full_simp_tac(srw_ss())[to_small_st_def] >>
  ((match_mp_tac evaluate_ctxts_type_error_matchable >>
    srw_tac[][state_component_equality]) ORELSE
   metis_tac[do_con_check_build_conv,NOT_SOME_NONE])
QED

Theorem small_exp_to_big_exp:
  !st st'.
    e_step_reln^* st st' ⇒
    !r.
      evaluate_state st' r
      ⇒
      evaluate_state st r
Proof
  HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >>
  srw_tac[][e_step_reln_def] >>
  PairCases_on `st` >>
  PairCases_on `st'` >>
  PairCases_on `st''` >>
  srw_tac[][] >>
  metis_tac [one_step_backward]
QED

Theorem evaluate_state_no_ctxt:
  !env (s:'a state) e r.
    evaluate_state (env,to_small_st s,Exp e,[]) r
    ⇔
      evaluate F env (s with <| next_type_stamp := 0; next_exn_stamp := 0; clock := 0;
                                eval_state := NONE |>) e r
Proof
  srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
  srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
  full_simp_tac(srw_ss())[to_small_st_def] >>
  Cases_on`r`>>simp[]>>
  rpt AP_THM_TAC >> AP_TERM_TAC >>
  simp[state_component_equality]
QED

Theorem evaluate_state_val_no_ctxt:
  !env (s:'a state) e.
    evaluate_state (env,to_small_st s,Val e,[]) r
    ⇔
      (r = (s with <| next_type_stamp := 0; next_exn_stamp := 0;
                      clock := 0; eval_state := NONE |>, Rval e))
Proof
  srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
  srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
  full_simp_tac(srw_ss())[to_small_st_def] >>
  eq_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[state_component_equality]
QED

Theorem evaluate_state_val_raise_ctxt:
  !env (s:'a state) v env'.
    evaluate_state (env,to_small_st s,Val v,[(Craise (), env')]) r
    ⇔
      (r = (s with <| next_type_stamp := 0; next_exn_stamp := 0;
                      clock := 0; eval_state := NONE |>, Rerr (Rraise v)))
Proof
  srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
  srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
  srw_tac[][evaluate_ctxt_cases] >>
  srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
  full_simp_tac(srw_ss())[to_small_st_def] >>
  eq_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[state_component_equality]
QED

Theorem evaluate_change_state = Q.prove(
  `evaluate a b c d (e,f) ∧ c = c' ∧ e = e' ⇒
   evaluate a b c' d (e',f)`,
   srw_tac[][] >> srw_tac[][]) |> GEN_ALL;

Theorem small_big_exp_equiv:
 !env s e s' r.
  s.eval_state = NONE ⇒
  (small_eval env (to_small_st s) e [] (to_small_st s',r) ∧
   s.clock = s'.clock ∧ s.next_type_stamp = s'.next_type_stamp ∧
   s.next_exn_stamp = s'.next_exn_stamp ∧ s.eval_state = s'.eval_state
   ⇔
   evaluate F env s e (s',r))
Proof
 srw_tac[][] >>
 eq_tac
 >- (srw_tac[][] >>
     cases_on `r` >|
     [all_tac,
      cases_on `e'`] >>
     full_simp_tac(srw_ss())[small_eval_def] >>
     imp_res_tac small_exp_to_big_exp >>
     full_simp_tac(srw_ss())[evaluate_state_val_no_ctxt, evaluate_state_no_ctxt, evaluate_state_val_raise_ctxt] >>
     imp_res_tac evaluate_ignores_types_exns >>
     full_simp_tac(srw_ss())[] >> TRY (
         pop_assum (qspecl_then [`s.next_exn_stamp`, `s.next_type_stamp`] mp_tac) >>
         srw_tac[][] >>
         match_mp_tac evaluate_change_state >>
         imp_res_tac big_unclocked >>
         first_x_assum(qspec_then`s.clock`strip_assume_tac) >>
         first_assum(match_exists_tac o concl) >>
         simp[state_component_equality] >> NO_TAC) >>
     (imp_res_tac one_step_backward_type_error >>
         full_simp_tac(srw_ss())[] >>
         res_tac >>
         imp_res_tac evaluate_ignores_types_exns >>
         pop_assum (qspecl_then [`s.next_exn_stamp`, `s.next_type_stamp`] mp_tac) >>
         srw_tac[][] >>
         pop_assum mp_tac >>
         ntac 3 (pop_assum kall_tac) >> strip_tac >>
         match_mp_tac evaluate_change_state >>
         imp_res_tac big_unclocked >>
         first_x_assum(qspec_then`s.clock`strip_assume_tac) >>
         first_assum(match_exists_tac o concl) >>
         simp[state_component_equality]))
 >- (srw_tac[][] >>
     imp_res_tac big_exp_to_small_exp >>
     full_simp_tac(srw_ss())[small_eval_def, to_small_res_def] >>
     metis_tac [evaluate_no_new_types_exns, FST, big_unclocked])
QED

(* ---------------------- Small step determinacy ------------------------- *)

Theorem small_exp_determ:
  !env s e r1 r2.
    small_eval env s e [] r1 ∧ small_eval env s e [] r2
    ⇒
    (r1 = r2)
Proof
  srw_tac[][] >>
  assume_tac small_big_exp_equiv >>
  full_simp_tac(srw_ss())[to_small_st_def] >>
  PairCases_on `r1` >>
  PairCases_on `r2` >>
  pop_assum (qspecl_then [`env`, `<| ffi := SND s; refs := FST s; clock := 0; next_type_stamp := 0; next_exn_stamp := 0; eval_state := NONE |>`, `e`] mp_tac) >>
  simp [] >>
  strip_tac >>
  first_assum (qspec_then `<| ffi := r11; refs := r10; clock := 0;
                              next_type_stamp := 0; next_exn_stamp := 0;
                              eval_state := NONE |>` mp_tac) >>
  first_assum (qspec_then `<| ffi := r21; refs := r20; clock := 0;
                              next_type_stamp := 0; next_exn_stamp := 0;
                              eval_state := NONE |>` mp_tac) >>
  pop_assum kall_tac >>
  simp [] >>
  strip_tac >>
  strip_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  imp_res_tac big_exp_determ >>
  full_simp_tac(srw_ss())[state_component_equality]
QED

(* ---------------------------------------------------------------------- *)

(**********

  Prove that the small step semantics never gets stuck if there is
  still work to do (i.e., it must detect all type errors).  Thus, it
  either diverges or gives a result, and it can't do both.

**********)

Theorem untyped_safety_exp_step:
  ∀env s e c.
    (e_step (env,s,e,c) = Estuck) ⇔
    (∃v. e = Val v) ∧ (c = [] ∨ ∃env. c = [(Craise (), env)])
Proof
  rw[e_step_def, continue_def, push_def, return_def] >>
  TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
  every_case_tac >> gvs[] >>
  gvs[application_def, push_def, return_def] >> every_case_tac >> gvs[]
QED

Theorem small_exp_safety1:
  ∀s env e r.
    ¬(e_diverges env s e ∧ ∃r. small_eval env s e [] r)
Proof
  rw[e_diverges_def, Once DISJ_COMM, DISJ_EQ_IMP] >>
  PairCases_on `r` >> Cases_on `r2` >> gvs[small_eval_def, e_step_reln_def]
  >- (goal_assum drule >> simp[e_step_def, continue_def]) >>
  Cases_on `e'` >> gvs[small_eval_def] >>
  goal_assum drule >> simp[e_step_def, continue_def]
QED

Theorem small_exp_safety2:
  ∀menv cenv s env e. e_diverges env s e ∨ ∃r. small_eval env s e [] r
Proof
  rw[e_diverges_def, DISJ_EQ_IMP, e_step_reln_def] >>
  Cases_on `e_step (env',s',e',c')` >> gvs[untyped_safety_exp_step]
  >- (PairCases_on `p` >> gvs[])
  >- (
    qexists_tac `(s', Rerr (Rabort a))` >> rw[small_eval_def] >>
    goal_assum drule >> simp[]
    )
  >- (
    qexists_tac `(s', Rval v)` >> rw[small_eval_def] >>
    goal_assum drule >> simp[]
    )
  >- (
    qexists_tac `(s', Rerr (Rraise v))` >> rw[small_eval_def] >>
    goal_assum drule >> simp[]
    )
QED

Theorem untyped_safety_exp:
  ∀s env e. (∃r. small_eval env s e [] r) = ¬e_diverges env s e
Proof
  metis_tac[small_exp_safety2, small_exp_safety1]
QED

Triviality to_small_st_surj:
  ∀s. ∃y. s = to_small_st y
Proof
  srw_tac [QUANT_INST_ss[record_default_qp,std_qp]] [to_small_st_def]
QED

Theorem untyped_safety_decs:
  (∀d (s:'ffi state) env.
     s.eval_state = NONE ⇒
     (∃r. evaluate_dec F env s d r) = ¬dec_diverges env s d) ∧
  (∀ds (s:'ffi state) env.
     s.eval_state = NONE ⇒
     (∃r. evaluate_decs F env s ds r) = ¬decs_diverges env s ds)
Proof
  ho_match_mp_tac astTheory.dec_induction >> rw[] >>
  rw[Once evaluate_dec_cases, Once dec_diverges_cases, GSYM untyped_safety_exp] >>
  gvs[]
  >- (
    Cases_on `ALL_DISTINCT (pat_bindings p [])` >>
    gvs[GSYM small_big_exp_equiv, to_small_st_def] >>
    eq_tac >- metis_tac[] >> rw[] >>
    PairCases_on `r` >>
    Q.REFINE_EXISTS_TAC `(s with <| refs := r0; ffi := r1 |>, res)` >> simp[] >>
    reverse $ Cases_on `r2` >> gvs[]
    >- (qexists_tac `Rerr e'` >> gvs[]) >>
    Cases_on `pmatch env.c r0 p a []` >> gvs[]
    >- (
      qexists_tac `Rerr (Rraise bind_exn_v)` >> gvs[] >>
      disj1_tac >> goal_assum drule >> simp[]
      )
    >- (
      qexists_tac `Rerr (Rabort Rtype_error)` >> gvs[] >>
      disj1_tac >> goal_assum drule >> simp[]
      )
    >- (
      qexists_tac `Rval <| v := alist_to_ns a' ; c := nsEmpty |>` >> gvs[] >>
      goal_assum drule >> simp[]
      )
    )
  >- metis_tac[]
  >- metis_tac[NOT_EVERY]
  >- (
    eq_tac >> rw[] >> gvs[EXISTS_PROD, PULL_EXISTS] >>
    metis_tac[result_nchotomy]
    )
  >- (
    gvs[EXISTS_PROD, PULL_EXISTS, declare_env_def] >>
    ntac 3 $ pop_assum $ mp_tac o GSYM >>
    gvs[] >> rw[] >> eq_tac >> rw[] >> gvs[] >>
    imp_res_tac evaluate_dec_eval_state >> gvs[] >>
    metis_tac[result_nchotomy, decs_determ, PAIR_EQ, result_11, result_distinct]
    )
  >- (gvs[EXISTS_PROD, declare_env_def])
  >- (
    gvs[EXISTS_PROD, declare_env_def] >>
    ntac 2 $ pop_assum $ mp_tac o GSYM >> rw[] >> eq_tac >> rw[] >>
    imp_res_tac evaluate_dec_eval_state >> gvs[] >> res_tac >>
    imp_res_tac evaluate_dec_eval_state >> gvs[] >>
    metis_tac[result_nchotomy, result_distinct, decs_determ, PAIR_EQ, result_11]
    )
QED

Theorem untyped_safety_decs_alt:
  ∀d (s:'ffi state) env.  s.eval_state = NONE ⇒
    (∀r. ¬evaluate_dec F env s d r) = dec_diverges env s d
Proof
  rw[] >> drule $ cj 1 untyped_safety_decs >> metis_tac[]
QED


(**********

  Prove equivalence between small-step and big-step semantics for declarations.

**********)

val _ = set_fixity "+++" (Infixl 480);
Overload "+++" = “extend_dec_env”;

val decl_step_ss = simpLib.named_rewrites "decl_step_ss"
  [decl_step_reln_def, decl_step_def, decl_continue_def];

Definition Rerr_to_decl_step_result_def[simp]:
  Rerr_to_decl_step_result (Rraise v) = Draise v ∧
  Rerr_to_decl_step_result (Rabort v) = Dabort v
End

Theorem small_eval_dec_def:
  (∀benv dst st e. small_eval_dec benv dst (st, Rval e) =
    (decl_step_reln benv)꙳ dst (st, Env e, [])) ∧
  (∀benv dst st err. small_eval_dec benv dst (st, Rerr err) =
    ∃dst'.
      (decl_step_reln benv)꙳ dst (st, dst') ∧
      decl_step benv (st, dst') = Rerr_to_decl_step_result err)
Proof
  rw[small_eval_dec_def] >>
  Cases_on `err` >> rw[small_eval_dec_def, EXISTS_PROD]
QED

Inductive small_eval_decs:
  small_eval_decs benv st [] (st, Rval empty_dec_env) ∧

  (small_eval_dec benv (st, Decl d, []) (st', Rval env) ∧
   small_eval_decs (env +++ benv) st' ds (st'', r)
      ⇒ small_eval_decs benv st (d::ds) (st'', combine_dec_result env r)) ∧

  (small_eval_dec benv (st, Decl d, []) (st', Rerr e)
      ⇒ small_eval_decs benv st (d::ds) (st', Rerr e))
End

Theorem decl_step_to_Ddone:
  decl_step env (st, dev, ds) = Ddone ⇔
  ∃e. dev = Env e ∧ ds = []
Proof
  rw[] >> reverse eq_tac >> rw[]
  >- (simp[decl_step_def, decl_continue_def]) >>
  reverse $ Cases_on `dev` >> gvs[decl_step_def]
  >- (gvs[decl_continue_def] >> every_case_tac >> gvs[])
  >- (
    pop_assum mp_tac >> simp[] >>
    qpat_abbrev_tac `foo = e_step_result_CASE _ _ _ _` >>
    TOP_CASE_TAC >> gvs[]
    >- (
      gvs[e_step_def, push_def, return_def] >>
      every_case_tac >> gvs[] >> unabbrev_all_tac >> gvs[] >>
      gvs[application_def] >> every_case_tac >> gvs[return_def]
      ) >>
    TOP_CASE_TAC >> gvs[] >- (every_case_tac >> gvs[]) >>
    Cases_on `∃env. h::t = [Craise (), env]` >> gvs[] >>
    qsuff_tac `foo ≠ Ddone` >- (rw[] >> every_case_tac >> gvs[]) >>
    unabbrev_all_tac >> every_case_tac >> gvs[] >>
    pop_assum mp_tac >> simp[] >>
    simp[e_step_def, continue_def, push_def, return_def, application_def] >>
    every_case_tac >> gvs[]
    )
  >- (every_case_tac >> gvs[])
QED

Theorem small_decl_total:
  ∀env a.
    (∀b. ¬small_eval_dec env a b) ⇔
    small_decl_diverges env a
Proof
  rw[small_decl_diverges_def] >>
  reverse eq_tac >> strip_tac >> gen_tac >> rw[] >> gvs[]
  >- (
    CCONTR_TAC >> last_x_assum mp_tac >> gvs[] >>
    PairCases_on `b` >> Cases_on `b1` >> gvs[small_eval_dec_def] >>
    goal_assum drule >> simp[SF decl_step_ss] >>
    Cases_on `e` >> gvs[]
    ) >>
  simp[SF decl_step_ss] >>
  Cases_on `decl_step env b` >> gvs[] >> PairCases_on `b`
  >- (
    last_x_assum mp_tac >> simp[] >> qexists_tac `(b0, Rerr $ Rabort a')` >>
    simp[small_eval_dec_def] >> goal_assum drule >> simp[]
    )
  >- (
    gvs[decl_step_to_Ddone] >>
    last_x_assum $ qspec_then `(b0,Rval e)` assume_tac >> gvs[small_eval_dec_def]
    )
  >- (
    last_x_assum mp_tac >> simp[] >> qexists_tac `(b0, Rerr $ Rraise v)` >>
    simp[small_eval_dec_def] >> goal_assum drule >> simp[]
    )
QED

Theorem extend_dec_env_empty_dec_env[simp]:
  (∀env. env +++ empty_dec_env = env) ∧
  (∀env. empty_dec_env +++ env = env)
Proof
  rw[extend_dec_env_def, empty_dec_env_def]
QED

Theorem collapse_env_def:
  (∀benv. collapse_env benv [] =  benv) ∧
  (∀benv mn env ds cs. collapse_env benv (Cdmod mn env ds :: cs) =
    env +++ (collapse_env benv cs)) ∧
  (∀benv lenv lds gds cs. collapse_env benv (CdlocalL lenv lds gds :: cs) =
    lenv +++ (collapse_env benv cs)) ∧
  (∀benv lenv genv gds cs. collapse_env benv (CdlocalG lenv genv gds :: cs) =
    genv +++ lenv +++ (collapse_env benv cs))
Proof
  rw[] >> simp[Once collapse_env_def, empty_dec_env_def]
QED

Theorem collapse_env_APPEND:
  ∀c1 c2 benv.
    collapse_env benv (c1 ++ c2) =
      collapse_env (collapse_env benv c2) c1
Proof
  Induct >> rw[collapse_env_def] >> Cases_on `h` >> gvs[collapse_env_def]
QED

Theorem extend_collapse_env:
  ∀c benv env.
    (collapse_env env c) +++ benv =
    collapse_env (extend_dec_env env benv) c
Proof
  Induct >> rw[collapse_env_def, empty_dec_env_def] >>
  Cases_on `h` >> simp[collapse_env_def] >>
  rewrite_tac[GSYM extend_dec_env_assoc] >>
  first_assum $ rewrite_tac o single
QED

Theorem collapse_env_unchanged:
  ∀c benv. collapse_env benv c = benv ⇔ collapse_env empty_dec_env c = empty_dec_env
Proof
  rw[] >> `benv = empty_dec_env +++ benv` by simp[] >>
  pop_assum $ rewrite_tac o single o Once >>
  simp[GSYM extend_collapse_env] >>
  simp[extend_dec_env_def] >>
  Cases_on `collapse_env empty_dec_env c` >> simp[] >>
  Cases_on `n` >> Cases_on `n0` >> gvs[] >>
  Cases_on `benv` >> Cases_on `n` >> Cases_on `n0` >> gvs[] >>
  simp[namespaceTheory.nsAppend_def, sem_env_component_equality] >>
  eq_tac >> rw[empty_dec_env_def, namespaceTheory.nsEmpty_def]
QED

Theorem collapse_env_split:
  ∀benv env. collapse_env benv env =
    extend_dec_env (collapse_env empty_dec_env env) benv
Proof
  simp[extend_collapse_env]
QED

Theorem collapse_env_APPEND_alt:
  ∀c1 c2 benv.
    collapse_env benv (c1 ++ c2) =
      extend_dec_env (collapse_env empty_dec_env c1) (collapse_env benv c2)
Proof
  simp[extend_collapse_env, collapse_env_APPEND]
QED

Theorem small_eval_dec_prefix:
  ∀benv dst dst' res.
    (decl_step_reln benv)꙳ dst dst' ⇒
    small_eval_dec benv dst' res
  ⇒ small_eval_dec benv dst res
Proof
  rw[] >> PairCases_on `res` >> Cases_on `res1` >> gvs[small_eval_dec_def]
  >- (simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >> simp[]) >>
  Cases_on `e` >> gvs[small_eval_dec_def] >>
  goal_assum $ drule_at Any >>
  simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >> simp[]
QED

Theorem decl_step_ctxt_weaken_Dstep:
  ∀benv extra (st:'ffi state) dev c s' dev' c'.
    decl_step (collapse_env benv extra) (st, dev, c) = Dstep (s', dev', c')
  ⇒ decl_step benv (st, dev, c ++ extra) = Dstep (s', dev', c' ++ extra)
Proof
  rw[decl_step_def] >>
  `collapse_env benv (c ++ extra) = collapse_env (collapse_env benv extra) c` by
    simp[collapse_env_APPEND] >>
  every_case_tac >> gvs[collapse_env_def] >>
  pop_assum mp_tac >> simp[decl_continue_def] >>
  every_case_tac >> gvs[]
QED

Theorem decl_step_ctxt_weaken_Dabort:
  ∀benv extra (st:'ffi state) dev c s' dev' c' a.
    decl_step (collapse_env benv extra) (st, dev, c) = Dabort a
  ⇒ decl_step benv (st, dev, c ++ extra) = Dabort a
Proof
  rw[decl_step_def] >>
  `collapse_env benv (c ++ extra) = collapse_env (collapse_env benv extra) c` by
    simp[collapse_env_APPEND] >>
  every_case_tac >> gvs[collapse_env_def] >>
  pop_assum mp_tac >> simp[decl_continue_def] >>
  every_case_tac >> gvs[]
QED

Theorem decl_step_ctxt_weaken_Draise:
  ∀benv extra (st:'ffi state) dev c s' dev' c' a.
    decl_step (collapse_env benv extra) (st, dev, c) = Draise a
  ⇒ decl_step benv (st, dev, c ++ extra) = Draise a
Proof
  rw[decl_step_def] >>
  `collapse_env benv (c ++ extra) = collapse_env (collapse_env benv extra) c` by
    simp[collapse_env_APPEND] >>
  every_case_tac >> gvs[collapse_env_def] >>
  pop_assum mp_tac >> simp[decl_continue_def] >>
  every_case_tac >> gvs[]
QED

Theorem decl_step_ctxt_weaken_err:
  ∀benv extra (st:'ffi state) dev c s' dev' c' a.
    decl_step (collapse_env benv extra) (st, dev, c) = Rerr_to_decl_step_result a
  ⇒ decl_step benv (st, dev, c ++ extra) = Rerr_to_decl_step_result a
Proof
  Cases_on `a` >> gvs[] >>
  simp[decl_step_ctxt_weaken_Dabort, decl_step_ctxt_weaken_Draise]
QED

Theorem RTC_decl_step_reln_ctxt_weaken:
  ∀benv extra (st : 'ffi state) dev c s' dev' c'.
    (decl_step_reln (collapse_env benv extra))꙳ (st, dev, c) (s', dev', c')
  ⇒ (decl_step_reln benv)꙳ (st, dev, c ++ extra) (s', dev', c' ++ extra)
Proof
  gen_tac >> gen_tac >>
  Induct_on `RTC (decl_step_reln (collapse_env benv extra))` >> rw[] >> simp[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  rename1 `decl_step_reln _ _ foo` >> PairCases_on `foo` >>
  gvs[decl_step_reln_def] >> drule decl_step_ctxt_weaken_Dstep >> simp[]
QED

Theorem decl_step_to_Draise:
  ∀env (st:'ffi state) dev c ex.
    decl_step env (st, dev, c) = Draise ex ⇔
      (∃env' v locs p.
        dev = ExpVal env' (Val v) [] locs p ∧
        ALL_DISTINCT (pat_bindings p []) ∧
        pmatch (collapse_env env c).c st.refs p v [] = No_match ∧
        ex = bind_exn_v) ∨
      (∃env' v env'' locs p.
        dev = ExpVal env' (Val v) [(Craise (), env'')] locs p ∧ ex = v)
Proof
  rw[] >> eq_tac >> rw[] >> gvs[decl_step_def] >>
  every_case_tac >> gvs[] >>
  gvs[decl_continue_def] >> every_case_tac >> gvs[]
QED

Theorem pmatch_nsAppend:
  (∀ns st pat v env m ns'.
    (pmatch ns st pat v env = No_match
   ⇒ pmatch (nsAppend ns ns') st pat v env = No_match) ∧
    (pmatch ns st pat v env = Match m
   ⇒ pmatch (nsAppend ns ns') st pat v env = Match m)) ∧
  (∀ns st pats vs env m ns'.
    (pmatch_list ns st pats vs env = No_match
   ⇒ pmatch_list (nsAppend ns ns') st pats vs env = No_match) ∧
    (pmatch_list ns st pats vs env = Match m
   ⇒ pmatch_list (nsAppend ns ns') st pats vs env = Match m))
Proof
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def]
  >- (
    pop_assum mp_tac >> TOP_CASE_TAC >>
    `nsLookup (nsAppend ns ns') n = SOME x` by
      gvs[namespacePropsTheory.nsLookup_nsAppend_some] >>
    gvs[] >> PairCases_on `x` >> gvs[] >>
    rpt (TOP_CASE_TAC >> gvs[])
    )
  >- (
    pop_assum mp_tac >> TOP_CASE_TAC >>
    `nsLookup (nsAppend ns ns') n = SOME x` by
      gvs[namespacePropsTheory.nsLookup_nsAppend_some] >>
    gvs[] >> PairCases_on `x` >> gvs[] >>
    rpt (TOP_CASE_TAC >> gvs[])
    )
  >- (TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[])
  >- (TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[])
  >- (
    pop_assum mp_tac >> TOP_CASE_TAC >> gvs[] >>
    TOP_CASE_TAC >> gvs[]
    )
  >- (
    pop_assum mp_tac >> TOP_CASE_TAC >> gvs[] >>
    TOP_CASE_TAC >> gvs[]
    )
QED

Theorem pmatch_nsAppend_No_match = pmatch_nsAppend |> cj 1 |> cj 1;
Theorem pmatch_nsAppend_Match = pmatch_nsAppend |> cj 1 |> cj 2;

Triviality e_step_reln_decl_step_reln:
  ∀env (stffi:('ffi,v) store_ffi) ev cs env' stffi' ev' cs'
    benv (st:'ffi state) locs p dcs.
  e_step_reln꙳ (env, stffi, ev, cs) (env', stffi', ev', cs')
  ⇒ (decl_step_reln benv)꙳
      (st with <| refs := FST stffi ; ffi := SND stffi |>,
          ExpVal env ev cs locs p, dcs)
      (st with <| refs := FST stffi' ; ffi := SND stffi' |>,
          ExpVal env' ev' cs' locs p, dcs)
Proof
  Induct_on `RTC e_step_reln` >> rw[] >> simp[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[decl_step_reln_def, decl_step_def] >> gvs[e_step_reln_def] >>
  every_case_tac >> gvs[e_step_def, continue_def]
QED

Theorem decl_step_eval_state_NONE:
  ∀benv (st:'ffi state) dev c st' dev' c'.
    decl_step benv (st, dev, c) = Dstep (st', dev', c') ∧
    st.eval_state = NONE
  ⇒ st'.eval_state = NONE
Proof
  rw[decl_step_def] >> every_case_tac >> gvs[] >>
  gvs[decl_continue_def, declare_env_def] >> every_case_tac >> gvs[]
QED

Theorem RTC_decl_step_reln_eval_state_NONE:
  ∀benv (st : 'ffi state) dev c st' dev' c'.
    (decl_step_reln benv)꙳ (st, dev, c) (st', dev', c') ∧
    st.eval_state = NONE
  ⇒ st'.eval_state = NONE
Proof
  rw[] >>
  qsuff_tac `
    ∀a b. (decl_step_reln benv)꙳ a b ⇒
    ∀(st:'ffi state) dev c st' dev' c'.
      a = (st, dev, c) ∧ b = (st', dev', c') ∧
      st.eval_state = NONE
    ⇒ st'.eval_state = NONE`
  >- (rw[] >> metis_tac[]) >>
  Induct_on `RTC (decl_step_reln benv)` >> rw[] >> simp[] >>
  PairCases_on `a'` >> gvs[] >> first_x_assum irule >>
  gvs[decl_step_reln_def] >>
  drule decl_step_eval_state_NONE >> simp[]
QED

Theorem small_eval_decs_eval_state_NONE:
  ∀env (st : 'ffi state) ds st' res.
    small_eval_decs env st ds (st', res) ∧
    st.eval_state = NONE
  ⇒ st'.eval_state = NONE
Proof
  Induct_on `small_eval_decs` >> rw[]
  >- (
    first_x_assum irule >> simp[] >>
    irule RTC_decl_step_reln_eval_state_NONE >> gvs[small_eval_dec_def] >>
    rpt $ goal_assum drule
    )
  >- (
    irule RTC_decl_step_reln_eval_state_NONE >> gvs[small_eval_dec_def] >>
    PairCases_on `dst'` >> rpt $ goal_assum drule
    )
QED

Theorem small_eval_decs_Rval_Dmod_lemma[local]:
  ∀env (st:'ffi state) decs st' new_env envc envb enva mn.
    small_eval_decs env st decs (st', Rval new_env) ∧
    env = envc +++ envb +++ enva ∧
    st.eval_state = NONE
  ⇒ (decl_step_reln enva)꙳ (st,Env envc,[Cdmod mn envb decs])
     (st', Env $ lift_dec_env mn (new_env +++ envc +++ envb), [])
Proof
  Induct_on `small_eval_decs` >> rw[] >> gvs[]
  >- (simp[Once RTC_CASES1, SF decl_step_ss]) >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[Cdmod mn (envc +++ envb) decs]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >>
  irule $ iffRL RTC_CASES_RTC_TWICE >> first_x_assum $ irule_at Any >> simp[] >>
  simp[extend_dec_env_def] >>
  irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
QED

Theorem small_eval_decs_Rval_Dmod:
  ∀env st ds res st' new_env mn.
   small_eval_decs env st ds (st', Rval new_env) ∧
   st.eval_state = NONE
  ⇒ small_eval_dec env (st, Decl (Dmod mn ds), [])
      (st', Rval $ lift_dec_env mn new_env)
Proof
  rw[] >> drule small_eval_decs_Rval_Dmod_lemma >>
  disch_then $ qspecl_then [`empty_dec_env`,`empty_dec_env`,`env`] mp_tac >>
  rw[small_eval_dec_def] >> simp[Once RTC_CASES1, SF decl_step_ss]
QED

Theorem small_eval_decs_Rerr_Dmod_lemma[local]:
  ∀env (st:'ffi state) decs st' err envc envb enva mn.
    small_eval_decs env st decs (st', Rerr err) ∧
    env = envc +++ envb +++ enva ∧
    st.eval_state = NONE
  ⇒ ∃dst.
     (decl_step_reln enva)꙳ (st,Env envc,[Cdmod mn envb decs]) (st', dst) ∧
     decl_step enva (st', dst) = Rerr_to_decl_step_result err
Proof
  Induct_on `small_eval_decs` >> reverse $ rw[] >> gvs[]
  >- (
    simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
    gvs[small_eval_dec_def] >>
    qspecl_then [`enva`,`[Cdmod mn (envc +++ envb) ds]`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> PairCases_on `dst'` >>
    disch_then drule >> simp[] >> strip_tac >> goal_assum drule >>
    irule decl_step_ctxt_weaken_err >> simp[collapse_env_def]
    ) >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[Cdmod mn (envc +++ envb) decs]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule_at Any $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >>
  first_x_assum irule >> simp[] >>
  irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
QED

Theorem small_eval_decs_Rerr_Dmod:
  ∀env st ds res st' err mn.
   small_eval_decs env st ds (st', Rerr err) ∧
   st.eval_state = NONE
  ⇒ small_eval_dec env (st, Decl (Dmod mn ds), []) (st', Rerr err)
Proof
  rw[] >> drule small_eval_decs_Rerr_Dmod_lemma >>
  disch_then $ qspecl_then [`empty_dec_env`,`empty_dec_env`,`env`] mp_tac >>
  rw[small_eval_dec_def] >> simp[Once RTC_CASES1, SF decl_step_ss] >>
  irule_at Any OR_INTRO_THM2 >> simp[]
QED

Theorem small_eval_decs_Rval_Dlocal_lemma_1[local]:
  ∀env (st:'ffi state) decs st' new_env envc envb enva gds.
    small_eval_decs env st decs (st', Rval new_env) ∧
    env = envc +++ envb +++ enva ∧
    st.eval_state = NONE
  ⇒ (decl_step_reln enva)꙳ (st,Env envc,[CdlocalL envb decs gds])
     (st', Env empty_dec_env,
      [CdlocalG (new_env +++ envc +++ envb) empty_dec_env gds])
Proof
  Induct_on `small_eval_decs` >> rw[] >> gvs[]
  >- (simp[Once RTC_CASES1, SF decl_step_ss]) >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[CdlocalL (envc +++ envb) decs gds]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >>
  irule $ iffRL RTC_CASES_RTC_TWICE >> first_x_assum $ irule_at Any >> simp[] >>
  simp[extend_dec_env_def] >>
  irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
QED

Theorem small_eval_decs_Rval_Dlocal_lemma_2[local]:
  ∀env (st:'ffi state) decs st' new_env envc lenv genv enva.
    small_eval_decs env st decs (st', Rval new_env) ∧
    env = envc +++ genv +++ lenv +++ enva ∧
    st.eval_state = NONE
  ⇒ (decl_step_reln enva)꙳ (st,Env envc,[CdlocalG lenv genv decs])
     (st', Env $ new_env +++ envc +++ genv, [])
Proof
  Induct_on `small_eval_decs` >> rw[] >> gvs[]
  >- (simp[Once RTC_CASES1, SF decl_step_ss]) >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[CdlocalG lenv (envc +++ genv) decs]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >>
  irule $ iffRL RTC_CASES_RTC_TWICE >> first_x_assum $ irule_at Any >> simp[] >>
  simp[extend_dec_env_def] >>
  irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
QED

Theorem small_eval_decs_Rval_Dlocal:
  ∀env (st:'ffi state) lds st' lenv gds st'' genv.
   small_eval_decs env st lds (st', Rval lenv) ∧
   small_eval_decs (lenv +++ env) st' gds (st'', Rval genv) ∧
   st.eval_state = NONE
  ⇒ small_eval_dec env (st, Decl (Dlocal lds gds), []) (st'', Rval $ genv)
Proof
  rw[] >>
  qpat_x_assum `small_eval_decs _ _ _ _` mp_tac >>
  drule small_eval_decs_Rval_Dlocal_lemma_1 >>
  disch_then $ qspecl_then [`empty_dec_env`,`empty_dec_env`,`env`,`gds`] mp_tac >>
  simp[] >> strip_tac >> strip_tac >>
  drule small_eval_decs_Rval_Dlocal_lemma_2 >>
  disch_then $ qspecl_then [`empty_dec_env`,`lenv`,`empty_dec_env`,`env`] mp_tac >>
  simp[] >> impl_tac >> rw[]
  >- (irule small_eval_decs_eval_state_NONE >> rpt $ goal_assum drule) >>
  simp[small_eval_dec_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >>
  irule $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >> simp[]
QED

Theorem small_eval_decs_Rerr_Dlocal_lemma_1[local]:
  ∀env (st:'ffi state) decs st' err envc envb enva gds.
    small_eval_decs env st decs (st', Rerr err) ∧
    env = envc +++ envb +++ enva ∧
    st.eval_state = NONE
  ⇒ ∃dst.
      (decl_step_reln enva)꙳ (st,Env envc,[CdlocalL envb decs gds]) (st', dst) ∧
      decl_step enva (st', dst) = Rerr_to_decl_step_result err
Proof
  Induct_on `small_eval_decs` >> reverse $ rw[] >> gvs[]
  >- (
    gvs[small_eval_dec_def] >>
    simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
    qspecl_then [`enva`,`[CdlocalL (envc +++ envb) ds gds]`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> PairCases_on `dst'` >>
    disch_then drule >> simp[] >> strip_tac >> goal_assum drule >>
    irule decl_step_ctxt_weaken_err >> simp[collapse_env_def]
    ) >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[CdlocalL (envc +++ envb) decs gds]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule_at Any $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >>
  first_x_assum $ irule_at Any >> simp[] >>
  irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
QED

Theorem small_eval_decs_Rerr_Dlocal_lemma_2[local]:
  ∀env (st:'ffi state) decs st' err envc lenv genv enva.
    small_eval_decs env st decs (st', Rerr err) ∧
    env = envc +++ genv +++ lenv +++ enva ∧
    st.eval_state = NONE
  ⇒ ∃dst.
      (decl_step_reln enva)꙳ (st,Env envc,[CdlocalG lenv genv decs]) (st',dst) ∧
      decl_step enva (st',dst) = Rerr_to_decl_step_result err
Proof
  Induct_on `small_eval_decs` >> reverse $ rw[] >> gvs[]
  >- (
    gvs[small_eval_dec_def] >>
    simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
    qspecl_then [`enva`,`[CdlocalG lenv (envc +++ genv) ds]`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> PairCases_on `dst'` >>
    disch_then drule >> simp[] >> strip_tac >> goal_assum drule >>
    irule decl_step_ctxt_weaken_err >> simp[collapse_env_def]
    ) >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[CdlocalG lenv (envc +++ genv) decs]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule_at Any $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >>
  first_x_assum $ irule_at Any >> simp[] >>
  irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
QED

Theorem small_eval_decs_Rerr_Dlocal:
  ∀env st lds gds res st' err mn.
   (small_eval_decs env st lds (st', Rerr err) ∨
    ∃st'' new_env.
      small_eval_decs env st lds (st'', Rval new_env) ∧
      small_eval_decs (new_env +++ env) st'' gds (st', Rerr err)) ∧
   st.eval_state = NONE
  ⇒ small_eval_dec env (st, Decl (Dlocal lds gds), []) (st', Rerr err)
Proof
  rw[small_eval_dec_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2
  >- (irule small_eval_decs_Rerr_Dlocal_lemma_1 >> simp[]) >>
  irule_at Any $ iffRL RTC_CASES_RTC_TWICE >>
  irule_at Any small_eval_decs_Rval_Dlocal_lemma_1 >>
  goal_assum drule >> simp[] >>
  irule small_eval_decs_Rerr_Dlocal_lemma_2 >> simp[] >>
  irule small_eval_decs_eval_state_NONE >> rpt $ goal_assum drule
QED

Theorem big_dec_to_small_dec:
  (∀ck env (st:'ffi state) d r.
    evaluate_dec ck env st d r ⇒
    ¬ck ∧ st.eval_state = NONE
  ⇒ small_eval_dec env (st, Decl d, []) r) ∧

  (∀ck env (st:'ffi state) ds r.
    evaluate_decs ck env st ds r ⇒
    ¬ck ∧ st.eval_state = NONE
  ⇒ small_eval_decs env st ds r)
Proof
  ho_match_mp_tac evaluate_dec_ind >> rw[small_eval_dec_def] >> gvs[]
  >- (
    simp[Once RTC_CASES1, SF decl_step_ss] >>
    drule_all $ iffRL small_big_exp_equiv >> strip_tac >>
    gvs[small_eval_def] >>
    drule e_step_reln_decl_step_reln >>
    disch_then $ qspecl_then [`env`,`st`,`locs`,`p`,`[]`] mp_tac >>
    simp[to_small_st_def] >>
    qmatch_goalsub_abbrev_tac `RTC _ (sta,_) (stb,_)` >> strip_tac >>
    `sta = st ∧ stb = s2` by (
      unabbrev_all_tac >> gvs[state_component_equality]) >> gvs[] >>
    qmatch_goalsub_abbrev_tac `Env new_env` >>
    drule small_eval_dec_prefix >>
    disch_then $ qspec_then `(s2, Rval new_env)` mp_tac >>
    simp[small_eval_dec_def, collapse_env_def] >> disch_then irule >>
    irule RTC_SINGLE >> simp[SF decl_step_ss, collapse_env_def]
    )
  >- (
    simp[Once RTC_CASES1, SF decl_step_ss] >>
    irule_at Any OR_INTRO_THM2 >>
    drule_all $ iffRL small_big_exp_equiv >> strip_tac >>
    gvs[small_eval_def] >>
    drule e_step_reln_decl_step_reln >>
    disch_then $ qspecl_then [`env`,`st`,`locs`,`p`,`[]`] mp_tac >>
    simp[to_small_st_def] >>
    qmatch_goalsub_abbrev_tac `RTC _ (sta,_) (stb,_)` >> strip_tac >>
    `sta = st ∧ stb = s2` by (
      unabbrev_all_tac >> gvs[state_component_equality]) >> gvs[] >>
    simp[collapse_env_def] >> goal_assum drule >>
    simp[decl_step_def, collapse_env_def]
    )
  >- (
    simp[Once RTC_CASES1, SF decl_step_ss] >>
    irule_at Any OR_INTRO_THM2 >>
    drule_all $ iffRL small_big_exp_equiv >> strip_tac >>
    gvs[small_eval_def] >>
    drule e_step_reln_decl_step_reln >>
    disch_then $ qspecl_then [`env`,`st`,`locs`,`p`,`[]`] mp_tac >>
    simp[to_small_st_def] >>
    qmatch_goalsub_abbrev_tac `RTC _ (sta,_) (stb,_)` >> strip_tac >>
    `sta = st ∧ stb = s2` by (
      unabbrev_all_tac >> gvs[state_component_equality]) >> gvs[] >>
    simp[collapse_env_def] >> goal_assum drule >>
    simp[decl_step_def, collapse_env_def]
    )
  >- (irule_at Any RTC_REFL >> simp[decl_step_def])
  >- (
    Cases_on `err` >> gvs[small_eval_dec_def] >> (
      simp[Once RTC_CASES1, SF decl_step_ss] >>
      irule_at Any OR_INTRO_THM2 >>
      drule_all $ iffRL small_big_exp_equiv >> strip_tac >>
      gvs[small_eval_def] >>
      drule e_step_reln_decl_step_reln >>
      disch_then $ qspecl_then [`env`,`st`,`locs`,`p`,`[]`] mp_tac >>
      simp[to_small_st_def] >>
      qmatch_goalsub_abbrev_tac `RTC _ (sta,_) (stb,_)` >> strip_tac >>
      `sta = st ∧ stb = s'` by (
        unabbrev_all_tac >> gvs[state_component_equality]) >> gvs[] >>
      simp[collapse_env_def] >> goal_assum drule >>
      simp[decl_step_def] >> gvs[to_small_st_def] >>
      rpt (TOP_CASE_TAC >> gvs[]) >> gvs[e_step_def, continue_def]
      )
    )
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss, collapse_env_def])
  >- (irule_at Any RTC_REFL >> simp[decl_step_def])
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss])
  >- (
    irule_at Any RTC_REFL >> simp[decl_step_def] >>
    IF_CASES_TAC >> gvs[] >> pop_assum mp_tac >> simp[]
    )
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss] >> gvs[declare_env_def])
  >- (irule_at Any RTC_REFL >> simp[SF decl_step_ss, collapse_env_def])
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss, empty_dec_env_def])
  >- (irule RTC_SINGLE >> simp[SF decl_step_ss])
  >- (
    drule small_eval_decs_Rval_Dmod >> simp[small_eval_dec_def, lift_dec_env_def]
    )
  >- (
    simp[GSYM small_eval_dec_def] >> irule small_eval_decs_Rerr_Dmod >> simp[]
    )
  >- (
    PairCases_on `r` >> gvs[] >> Cases_on `r1` >> gvs[]
    >- (
      irule small_eval_decs_Rval_Dlocal >> simp[] >>
      goal_assum drule >> first_x_assum irule >>
      irule small_eval_decs_eval_state_NONE >>
      rpt $ goal_assum drule
      )
    >- (
      irule small_eval_decs_Rerr_Dlocal >> simp[] >> disj2_tac >>
      goal_assum drule >> first_x_assum irule >>
      irule small_eval_decs_eval_state_NONE >>
      rpt $ goal_assum drule
      )
    )
  >- (
    simp[GSYM small_eval_dec_def] >> irule small_eval_decs_Rerr_Dlocal >> simp[]
    )
  >- simp[Once small_eval_decs_cases, empty_dec_env_def]
  >- (
    simp[Once small_eval_decs_cases] >> disj2_tac >>
    simp[small_eval_dec_def] >> goal_assum drule >> simp[]
    )
  >- (
    simp[Once small_eval_decs_cases] >> disj1_tac >>
    irule_at Any EQ_REFL >> simp[small_eval_dec_def] >>
    goal_assum drule >> simp[] >>
    first_x_assum irule >>
    irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
    )
QED

Theorem TC_functional_confluence:
  ∀R. (∀a b1 b2. R a b1 ∧ R a b2 ⇒ b1 = b2) ⇒
    ∀a b1 b2.
      R⁺ a b1 ∧ R⁺ a b2
    ⇒ (b1 = b2) ∨
      (R⁺ a b1 ∧ R⁺ b1 b2) ∨
      (R⁺ a b2 ∧ R⁺ b2 b1)
Proof
  ntac 2 strip_tac >> Induct_on `TC R` >> rw[]
  >- (
    qpat_x_assum `TC _ _ _` mp_tac >>
    simp[Once TC_CASES1] >> strip_tac >> gvs[] >- metis_tac[] >>
    `y = b1` by metis_tac[] >> gvs[] >>
    disj2_tac >> simp[Once TC_CASES1]
    ) >>
  rename1 `R⁺ mid b1` >>
  last_x_assum assume_tac >>
  last_x_assum $ qspec_then `b2` assume_tac >> gvs[]
  >- (
    last_x_assum drule >> strip_tac >> gvs[] >>
    disj2_tac >> disj1_tac >>
    irule $ cj 2 TC_RULES >> qexists_tac `mid` >> simp[]
    )
  >- (
    ntac 2 disj2_tac >>
    irule $ cj 2 TC_RULES >> goal_assum drule >> simp[]
    )
QED

Theorem TC_functional_deterministic:
  ∀R. (∀a b1 b2. R a b1 ∧ R a b2 ⇒ b1 = b2) ⇒
  ∀a b1 b2.
    R⁺ a b1 ∧ R⁺ a b2 ∧
    (∀c. ¬R b1 c) ∧ (∀c. ¬R b2 c)
  ⇒ b1 = b2
Proof
  rw[] >> drule TC_functional_confluence >> disch_then drule >>
  disch_then $ qspec_then `b1` assume_tac >> gvs[] >> metis_tac[TC_CASES1]
QED

Theorem RTC_functional_confluence:
  ∀R. (∀a b1 b2. R a b1 ∧ R a b2 ⇒ b1 = b2) ⇒
    ∀a b1 b2.
      R꙳ a b1 ∧ R꙳ a b2
    ⇒ (R꙳ a b1 ∧ R꙳ b1 b2) ∨
      (R꙳ a b2 ∧ R꙳ b2 b1)
Proof
  ntac 2 strip_tac >> Induct_on `RTC R` >>
  once_rewrite_tac[RTC_CASES1] >> rw[] >> gvs[] >>
  metis_tac[RTC_CASES1]
QED

Theorem RTC_functional_deterministic:
  ∀R. (∀a b1 b2. R a b1 ∧ R a b2 ⇒ b1 = b2) ⇒
  ∀a b1 b2.
    R꙳ a b1 ∧ R꙳ a b2 ∧
    (∀c. ¬R b1 c) ∧ (∀c. ¬R b2 c)
  ⇒ b1 = b2
Proof
  once_rewrite_tac[RTC_CASES_TC] >> rw[] >> gvs[]
  >- gvs[Once TC_CASES1] >- gvs[Once TC_CASES1] >>
  metis_tac[TC_functional_deterministic]
QED

Theorem small_eval_dec_cases:
  ∀env dev st res.
    small_eval_dec env dev res ⇔
      ∃dev'.
        (decl_step_reln env)꙳ dev dev' ∧
        ((∃env'. SND res = Rval env' ∧ dev' = (FST res, Env env', [])) ∨
         (∃err. SND res = Rerr err ∧ FST dev' = FST res ∧
            decl_step env dev' = Rerr_to_decl_step_result err))
Proof
  rw[] >> reverse eq_tac >> rw[] >> gvs[small_eval_dec_def] >>
  PairCases_on `res` >> gvs[small_eval_dec_def]
  >- (PairCases_on `dev'` >> simp[] >> goal_assum drule >> simp[]) >>
  Cases_on `res1` >> gvs[small_eval_dec_def] >>
  goal_assum drule >> simp[]
QED

Triviality decl_step_reln_functional:
  ∀env a b1 b2. decl_step_reln env a b1 ∧ decl_step_reln env a b2 ⇒ b1 = b2
Proof
  rw[decl_step_reln_def] >> gvs[]
QED

Triviality RTC_decl_step_confl = RTC_functional_confluence |>
  Q.ISPEC `decl_step_reln env` |>
  Lib.C MATCH_MP (Q.SPEC `env` decl_step_reln_functional) |> GEN_ALL

Triviality RTC_decl_step_determ = RTC_functional_deterministic |>
  Q.ISPEC `decl_step_reln env` |>
  Lib.C MATCH_MP (Q.SPEC `env` decl_step_reln_functional) |> GEN_ALL

Theorem small_eval_dec_determ:
    small_eval_dec env dev r1 ∧ small_eval_dec env dev r2
  ⇒ r1 = r2
Proof
  rw[small_eval_dec_cases] >> gvs[]
  >- (
    qmatch_asmsub_abbrev_tac `RTC _ _ a` >>
    last_x_assum assume_tac >> qmatch_asmsub_abbrev_tac `RTC _ _ b` >>
    qspecl_then [`env`,`dev`,`a`,`b`] assume_tac RTC_decl_step_determ >> gvs[] >>
    unabbrev_all_tac >> gvs[decl_step_reln_def, decl_step_def, decl_continue_def] >>
    metis_tac[PAIR]
    )
  >- (
    qmatch_asmsub_abbrev_tac `RTC _ _ a` >>
    last_x_assum assume_tac >> qmatch_asmsub_abbrev_tac `RTC _ _ b` >>
    qspecl_then [`env`,`dev`,`a`,`b`] assume_tac RTC_decl_step_determ >> gvs[] >>
    unabbrev_all_tac >> Cases_on `err` >>
    gvs[decl_step_reln_def, decl_step_def, decl_continue_def]
    )
  >- (
    qmatch_asmsub_abbrev_tac `RTC _ _ a` >>
    last_x_assum assume_tac >> qmatch_asmsub_abbrev_tac `RTC _ _ b` >>
    qspecl_then [`env`,`dev`,`a`,`b`] assume_tac RTC_decl_step_determ >> gvs[] >>
    unabbrev_all_tac >> Cases_on `err` >>
    gvs[decl_step_reln_def, decl_step_def, decl_continue_def]
    )
  >- (
    qmatch_asmsub_abbrev_tac `RTC _ _ a` >>
    last_x_assum assume_tac >> qmatch_asmsub_abbrev_tac `RTC _ _ b` >>
    qspecl_then [`env`,`dev`,`a`,`b`] assume_tac RTC_decl_step_determ >> gvs[] >>
    unabbrev_all_tac >> Cases_on `err` >> Cases_on `err'` >>
    gvs[decl_step_reln_def, decl_step_def, decl_continue_def] >>
    metis_tac[PAIR]
    )
QED

Triviality small_decl_diverges_prefix:
  ∀env a b.
    (decl_step_reln env)꙳ a b ∧
    small_decl_diverges env b
  ⇒ small_decl_diverges env a
Proof
  rw[small_decl_diverges_def] >>
  qspecl_then [`env`,`a`,`b`,`b'`] assume_tac RTC_decl_step_confl >> gvs[] >>
  pop_assum mp_tac >> simp[Once RTC_CASES1] >> rw[] >> gvs[] >> goal_assum drule
QED

Triviality small_decl_diverges_suffix:
  ∀env a b.
    (decl_step_reln env)꙳ b a ∧
    small_decl_diverges env b
  ⇒ small_decl_diverges env a
Proof
  rw[small_decl_diverges_def] >>
  first_x_assum irule >> simp[Once RTC_CASES_RTC_TWICE] >>
  goal_assum drule >> simp[]
QED

Triviality small_decl_diverges_ExpVal_lemma:
  ∀benv (st:'ffi state) env ev cs locs p dcs b.
    (decl_step_reln benv)꙳ (st,ExpVal env ev cs locs p,dcs) b ∧
    (∀res. (e_step_reln꙳ (env,(st.refs,st.ffi),ev,cs) res ⇒
      ∃res'. e_step_reln res res'))
  ⇒ ∃c. decl_step_reln benv b c
Proof
  gen_tac >> Induct_on `RTC (decl_step_reln benv)` >> rw[] >>
  gvs[decl_step_reln_def, e_step_reln_def]
  >- (
    last_x_assum $ qspec_then `(env,(st.refs,st.ffi),ev,cs)` mp_tac >> rw[] >>
    simp[decl_step_def] >> every_case_tac >> gvs[] >>
    gvs[e_step_def, continue_def]
    ) >>
  first_x_assum irule >>
  `∃r. e_step (env,(st.refs,st.ffi),ev,cs) = Estep r` by (
    first_x_assum irule >> simp[]) >>
  rename1 `Dstep dst` >> PairCases_on `dst` >> simp[] >>
  PairCases_on `r` >>
  qexistsl_tac [`r4`,`r0`,`r3`,`locs`,`p`] >>
  `r1 = dst0.refs ∧ r2 = dst0.ffi` by (
    gvs[decl_step_def] >> every_case_tac >> gvs[] >>
    gvs[e_step_def, continue_def]
    ) >>
  gvs[] >> reverse conj_asm2_tac
  >- (
    gvs[decl_step_def] >> every_case_tac >> gvs[] >>
    gvs[e_step_def, continue_def]
    ) >>
  gvs[] >> rw[] >> first_x_assum irule >> simp[Once RTC_CASES1, e_step_reln_def]
QED

Theorem small_decl_diverges_ExpVal:
  ∀env (st:'ffi state) e benv env e locs pat dcs.
    e_diverges env (st.refs,st.ffi) e
  ⇒ small_decl_diverges benv (st, ExpVal env (Exp e) [] locs pat, dcs)
Proof
  rw[e_diverges_def, small_decl_diverges_def] >>
  irule small_decl_diverges_ExpVal_lemma >>
  goal_assum $ drule_at Any >> simp[FORALL_PROD] >> rw[] >>
  last_x_assum drule >> rw[] >> goal_assum drule
QED

Theorem dec_diverges_imp_small_decl_diverges:
  (∀env (st:'ffi state) d. dec_diverges env st d ⇒
    ∀env' cs. collapse_env env' cs = env ∧ st.eval_state = NONE ⇒
      small_decl_diverges env' (st, Decl d, cs)) ∧

  (∀env (st:'ffi state) ds. decs_diverges env st ds ⇒
    (∀env' cs enva envb mn.
      enva +++ envb +++ collapse_env env' cs = env ∧
      st.eval_state = NONE
     ⇒ small_decl_diverges env' (st, Env enva, Cdmod mn envb ds :: cs)) ∧
    (∀env' cs enva envb gds.
      enva +++ envb +++ collapse_env env' cs = env ∧
      st.eval_state = NONE
     ⇒ small_decl_diverges env' (st, Env enva, CdlocalL envb ds gds :: cs)) ∧
    (∀env' cs enva lenv genv.
      enva +++ genv +++ lenv +++ collapse_env env' cs = env ∧
      st.eval_state = NONE
     ⇒ small_decl_diverges env' (st, Env enva, CdlocalG lenv genv ds :: cs)))
Proof
  ho_match_mp_tac dec_diverges_ind >> rw[]
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    irule small_decl_diverges_ExpVal >> simp[]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss]
    )
  >- (
    irule small_decl_diverges_prefix >>
    simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
    drule $ cj 2 big_dec_to_small_dec >> simp[] >> strip_tac >>
    drule small_eval_decs_Rval_Dlocal_lemma_1 >> simp[] >>
    disch_then $ qspecl_then [`empty_dec_env`,`empty_dec_env`] mp_tac >> simp[] >>
    disch_then $ qspec_then `ds` assume_tac >>
    drule RTC_decl_step_reln_ctxt_weaken >> simp[] >> disch_then $ irule_at Any >>
    first_x_assum $ irule >> simp[] >>
    irule small_eval_decs_eval_state_NONE >> rpt $ goal_assum drule
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    first_x_assum irule >> simp[collapse_env_def]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    first_x_assum irule >> simp[collapse_env_def]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    first_x_assum irule >> simp[collapse_env_def]
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    drule $ cj 1 big_dec_to_small_dec >> simp[] >> strip_tac >>
    irule small_decl_diverges_prefix >>
    qspecl_then [`env'`,`Cdmod mn (enva +++ envb) ds :: cs`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> gvs[small_eval_dec_def] >>
    disch_then drule >> simp[] >> disch_then $ irule_at Any >>
    first_x_assum irule >> simp[] >>
    irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    drule $ cj 1 big_dec_to_small_dec >> simp[] >> strip_tac >>
    irule small_decl_diverges_prefix >>
    qspecl_then [`env'`,`CdlocalL (enva +++ envb) ds gds :: cs`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> gvs[small_eval_dec_def] >>
    disch_then drule >> simp[] >> disch_then $ irule_at Any >>
    first_x_assum irule >> simp[] >>
    irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
    )
  >- (
    irule small_decl_diverges_prefix >>
    irule_at Any RTC_SINGLE >> simp[SF decl_step_ss] >>
    drule $ cj 1 big_dec_to_small_dec >> simp[] >> strip_tac >>
    irule small_decl_diverges_prefix >>
    qspecl_then [`env'`,`CdlocalG lenv (enva +++ genv) ds :: cs`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> gvs[small_eval_dec_def] >>
    disch_then drule >> simp[] >> disch_then $ irule_at Any >>
    first_x_assum irule >> simp[] >>
    irule RTC_decl_step_reln_eval_state_NONE >> rpt $ goal_assum drule
    )
QED

Theorem small_big_dec_equiv:
  ∀env (st:'ffi state) d r.  st.eval_state = NONE ⇒
    evaluate_dec F env st d r = small_eval_dec env (st, Decl d, []) r
Proof
  rw[] >> eq_tac >> rw[]
  >- (drule $ cj 1 big_dec_to_small_dec >> simp[]) >>
  Cases_on `∃res. evaluate_dec F env st d res` >> gvs[]
  >- (
    drule small_eval_dec_determ >>
    drule $ cj 1 big_dec_to_small_dec >> simp[] >> strip_tac >>
    disch_then drule >> rw[] >> gvs[]
    ) >>
  drule $ iffLR untyped_safety_decs_alt >>
  disch_then drule >> strip_tac >>
  drule_at Any $ cj 1 dec_diverges_imp_small_decl_diverges >> simp[] >>
  qexistsl_tac [`env`,`[]`] >> simp[collapse_env_def] >>
  simp[small_decl_diverges_def] >>
  PairCases_on `r` >> Cases_on `r1` >> gvs[small_eval_dec_def] >>
  goal_assum drule >> simp[SF decl_step_ss] >>
  Cases_on `e` >> simp[]
QED

Theorem small_big_dec_equiv_diverge:
  ∀env (st:'ffi state) d.  st.eval_state = NONE ⇒
    dec_diverges env st d = small_decl_diverges env (st, Decl d, [])
Proof
  rw[] >> eq_tac >> rw[]
  >- (
    irule $ cj 1 dec_diverges_imp_small_decl_diverges >> simp[collapse_env_def]
    ) >>
  CCONTR_TAC >> qpat_x_assum `small_decl_diverges _ _` mp_tac >> simp[] >>
  drule_all $ iffRL $ cj 1 untyped_safety_decs >> strip_tac >> gvs[] >>
  simp[GSYM small_decl_total] >>
  drule $ cj 1 big_dec_to_small_dec >> simp[] >> disch_then $ irule_at Any
QED

val _ = export_theory ();

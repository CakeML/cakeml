(*
  Properties about the small-step semantics.
*)
Theory smallStepProps
Ancestors
  semanticPrimitives ffi semanticPrimitivesProps evaluateProps
  smallStep determ ast
Libs
  preamble

(**
Theorem application_thm:
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
      | SOME (v1,Rerr (Rraise v)) => Estep (env,v1,Exn v,c)
      | SOME (v1,Rerr (Rabort a)) => Eabort a
Proof
  srw_tac[][application_def] >>
  cases_on `op` >>
  srw_tac[][]
QED
**)
Theorem application_thm = fetch "smallStep" "application_def";

(******************** Expressions *******************)

Theorem list_end_case[local]:
  !l. l = [] ∨ ?x l'. l = l' ++ [x]
Proof
  Induct_on `l` >>
  srw_tac[][] >>
  metis_tac [APPEND]
QED


Theorem small_eval_prefix:
  ∀s env e c cenv' s' env' e' c' r.
    e_step_reln^* (env,s,Exp e,c) (env',s',Exp e',c') ∧
    small_eval env' s' e' c' r
    ⇒
    small_eval env s e c r
Proof
  srw_tac[][] >>
  PairCases_on `r` >>
  rename [‘small_eval env s e c ((r0,r1),r2) (* g *)’] >>
  cases_on `r2` >>
  full_simp_tac(srw_ss())[small_eval_def] >-
   metis_tac [transitive_RTC, transitive_def] >>
  cases_on `e''` >>
  TRY (Cases_on `a`) >>
  full_simp_tac(srw_ss())[small_eval_def] >>
  metis_tac [transitive_RTC, transitive_def]
QED

Theorem e_single_step_add_ctxt:
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
  (** To avoid unnecessary cases *)
  TRY TOP_CASE_TAC >> gs[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][]
  >- (full_simp_tac(srw_ss())[application_thm] >>
      every_case_tac >> gs[] >>
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
      every_case_tac >> gs[] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def])
QED

Theorem e_single_error_add_ctxt:
  !env s fp e c c'.
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
  (** To avoid unnecessary cases *)
  TRY TOP_CASE_TAC >> gs[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >> gs[]
  >- (full_simp_tac(srw_ss())[application_thm] >>
      every_case_tac >> gs[] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def] >> rveq >>
      gs[])
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
      every_case_tac >> gs[] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def] >> rveq >>
      gs[])
QED

Theorem e_single_error_add_ctxt_optimise:
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
  (** To avoid unnecessary cases *)
  TRY TOP_CASE_TAC >> gs[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >> gs[]
  >- (full_simp_tac(srw_ss())[application_thm] >>
      every_case_tac >> gs[] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def] >> rveq >>
      gs[])
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
      every_case_tac >> gs[] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[return_def] >> rveq >>
      gs[])
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

Theorem e_step_add_ctxt:
  !s1 env1 e1 c1 s2 env2 e2 c2 c'.
    e_step_reln^* (env1,s1,e1,c1) (env2,s2,e2,c2)
    ⇒
    e_step_reln^* (env1,s1,e1,c1++c') (env2,s2,e2,c2++c')
Proof
  metis_tac [e_step_add_ctxt_help]
QED

Theorem e_step_raise_lemma:
  !s env fp c v.
    EVERY (\c. (¬?pes env. c = (Chandle () pes, env)) ) c ∧
    (c ≠ [])
    ⇒
    e_step_reln^* (env,s,Exn v,c) (env,s,Exn v,[])
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

Theorem small_eval_err_add_ctxt:
  !s env e c err c' s'.
    EVERY (\c. (¬?pes env. c = (Chandle () pes, env))) c'
    ⇒
    small_eval env s e c (s', Rerr err) ⇒ small_eval env s e (c++c') (s', Rerr err)
Proof
  srw_tac[][] >>
  ‘?a. err = Rabort a ∨ ?v. err = Rraise v’
                            by (cases_on ‘err’ >> srw_tac[][]) >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[small_eval_def]
  >- (Cases_on ‘a’ >>
      full_simp_tac(srw_ss())[small_eval_def] >>
      ‘e_step_reln^* (env,s,Exp e,c++c') (env',s',e',c''++c')’
        by metis_tac [e_step_add_ctxt] >>
      metis_tac [e_single_error_add_ctxt])
  >- (
      ‘e_step_reln^* (env,s,Exp e,c++c') (env',s',Exn v, c')’
        by metis_tac [e_step_add_ctxt, APPEND] >>
      cases_on ‘c'’ >>
      full_simp_tac(srw_ss())[] >-
       metis_tac [] >>
      ‘e_step_reln^* (env',s',Exn v,h::t) (env',s',Exn v,[])’
        by (match_mp_tac e_step_raise_lemma >> srw_tac[][]) >>
      metis_tac [transitive_RTC, transitive_def]
      )
QED

Theorem small_eval_err_add_ctxt[allow_rebind] =
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
     gs[] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[bind_exn_v_def] >>
     metis_tac [pair_CASES],
 srw_tac[][return_def, Once RTC_CASES1, e_step_reln_def, e_step_def, push_def,REVERSE_APPEND,
     do_con_check_def] >>
     fs [bind_exn_v_def] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     full_simp_tac(srw_ss())[e_step_reln_def, e_step_def, push_def, return_def, do_con_check_def, bind_exn_v_def] >>
     gs[] >>
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
     full_simp_tac(srw_ss())[bind_exn_v_def] >> gs[] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[return_def, do_con_check_def] >>
     srw_tac[][] >-
     (full_simp_tac(srw_ss())[e_step_def, push_def] >> gs[] >>
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
  ‘es = [] ∨ ?e es'. es = es' ++ [e]’ by metis_tac [list_end_case] >>
  srw_tac[][] >>
  ‘(?s' v. r = (s', Rval v)) ∨ (?s' a. r = (s', Rerr (Rabort a))) ∨
  (?s' err. r = (s', Rerr (Rraise err)))’
    by metis_tac [pair_CASES, result_nchotomy, error_result_nchotomy] >>
  TRY (cases_on ‘a’) >>
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
  (!s1 env e es env' s2 s3 v err_v.
     e_step_reln^* (env,s1,Exp e,[]) (env',s3,Exn err_v,[]) ∨
     (e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ∧
      small_eval_list env s2 es (s3, Rerr (Rraise err_v)))
     ⇒
     (small_eval_list env s1 (e::es) (s3, Rerr (Rraise err_v)))) ∧
  (!s1 env e es e' c' env' s2 v s3.
     (e_step_reln^* (env,s1,Exp e,[]) (env',s3,e',c') ∧
      (e_step (env',s3,e',c') = Eabort ( a))) ∨
     (e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ∧
      small_eval_list env s2 es (s3,  Rerr (Rabort a)))
     ⇒
     (small_eval_list env s1 (e::es) (s3,  Rerr (Rabort a))))
End

Theorem small_eval_list_length:
  !env s1 es r. small_eval_list env s1 es r ⇒
                !vs s2 . (r = (s2,  Rval vs)) ⇒ (LENGTH es = LENGTH vs)
Proof
  HO_MATCH_MP_TAC small_eval_list_ind >>
  srw_tac[][] >>
  srw_tac[][]
QED

Theorem small_eval_list_step:
  !env s2 es r.
    small_eval_list env s2 es r ⇒
    (!e v vs cn vs' env' s1 s3 v_con.
       do_con_check env.c cn (LENGTH vs' + 1 + LENGTH vs) ∧
       (build_conv env.c cn (REVERSE (REVERSE vs'++[v]++vs)) = SOME v_con) ∧
       (r = (s3,  Rval vs)) ∧ e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ⇒
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
                (!e v err_v cn vs' env' s1 s3 .
                   do_con_check env.c cn (LENGTH vs' + 1 + LENGTH es) ∧
                   (r = (s3,  Rerr (Rraise err_v))) ∧
                   e_step_reln^* (env,s1,e,[]) (env',s2,Val v,[]) ⇒
                   ?env''. e_step_reln^* (env,s1,e,[(Ccon cn vs' () es,env)])
                                             (env'',s3,Exn err_v,[]))
Proof
  ho_match_mp_tac small_eval_list_ind >>
  srw_tac[][] >>
  `e_step_reln^* (env,s1,e',[(Ccon cn vs' () (e::es),env)])
   (env'',s2,Val v',[(Ccon cn vs' () (e::es),env)])`
    by metis_tac [e_step_add_ctxt, APPEND] >>
  `LENGTH vs' + 1 + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
    by DECIDE_TAC >>
  `e_step_reln (env'',s2,Val v',[(Ccon cn vs' () (e::es),env)])
   (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])`
    by srw_tac[][push_def,continue_def, e_step_reln_def, e_step_def] >>
  full_simp_tac(srw_ss())[]
  >- (`e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
      (env',s3,Exn err_v,[(Ccon cn (v'::vs') () es,env)])`
        by metis_tac [e_step_add_ctxt,APPEND] >>
      `e_step_reln^*
        (env',s3,Exn err_v,[(Ccon cn (v'::vs') () es,env)])
        (env',s3,Exn err_v,[])`
        by (match_mp_tac e_step_raise_lemma >>
            srw_tac[][]) >>
      rpt (simp[Once RTC_CASES_RTC_TWICE] >> first_x_assum $ irule_at Any) >>
      simp[])
  >- (`LENGTH (v'::vs') + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
        by (full_simp_tac(srw_ss())[] >>
            DECIDE_TAC) >>
      `?env''. e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
        (env'',s3,Exn err_v, [])`
        by metis_tac [] >>
      metis_tac [RTC_SINGLE, transitive_RTC, transitive_def])
QED

Theorem small_eval_list_terr:
  !env s2 es r.
    small_eval_list env s2 es r ⇒
    (!e v err cn vs' env' s1 s3 .
       do_con_check env.c cn (LENGTH vs' + 1 + LENGTH es) ∧
       (r = (s3,  Rerr (Rabort a))) ∧
       e_step_reln^* (env,s1,e,[]) (env',s2,Val v,[]) ⇒
       ?env'' e' c' . e_step_reln^* (env,s1,e,[(Ccon cn vs' () es,env)])
                                    (env'',s3,e',c') ∧
                         (e_step (env'',s3,e',c') = (Eabort (a))))
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
   `e_step (env',s3,e',c'++[(Ccon cn (v'::vs') () es,env)]) = Eabort ( a)`
     by (irule e_single_error_add_ctxt >> gs[]) >>
   metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
   `LENGTH (v'::vs') + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
     by (full_simp_tac(srw_ss())[] >>
         DECIDE_TAC) >>
   `?env'' e' c' . e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
     (env'',s3,e',c') ∧
   (e_step (env'',s3,e',c') = Eabort (a))`
     by metis_tac [] >>
   metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]]
QED

Inductive small_eval_match:
  (!env s err_v v. small_eval_match env s v [] err_v (s,  Rerr (Rraise err_v))) ∧
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
     small_eval_match env s v ((p,e)::pes) err_v (s,  Rerr (Rabort Rtype_error))) ∧
  (!env s p e pes v err_v.
     (pmatch env.c (FST s) p v [] = Match_type_error)
     ⇒
     small_eval_match env s v ((p,e)::pes) err_v (s,  Rerr (Rabort Rtype_error)))
End

Definition alt_small_eval_def:
  (alt_small_eval env s1 e c (s2,  Rval v) ⇔
     ∃env'. e_step_reln^* (env,s1,e,c) (env',s2,Val v,[])) ∧
  (alt_small_eval env s1 e c (s2,  Rerr (Rraise err_v)) ⇔
     ∃env'.
       e_step_reln^* (env,s1,e,c) (env',s2,Exn err_v,[])) ∧
  (alt_small_eval env s1 e c (s2,  Rerr (Rabort a)) ⇔
     ∃env' e' c' .
       e_step_reln^* (env,s1,e,c) (env',s2,e',c') ∧
       (e_step (env',s2,e',c') = Eabort (a)))
End

Theorem small_eval_match_thm:
  !env s v pes err_v r.
    small_eval_match env s v pes err_v r ⇒
    !env2. alt_small_eval env2 s (Val v) [(Cmat () pes err_v,env)] r
Proof
  HO_MATCH_MP_TAC small_eval_match_ind >>
  srw_tac[][alt_small_eval_def]
  >- (qexists_tac `env` >>
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
      srw_tac[][e_step_def, continue_def]
      (* PairCases_on `env` >>
      full_simp_tac(srw_ss())[] >>
      metis_tac []*))
  >- (qexists_tac `env2` >>
      qexists_tac `Val v` >>
      qexists_tac `[(Cmat () ((p,e)::pes) err_v,env)]` >>
      srw_tac[][RTC_REFL] >>
      srw_tac[][e_step_def, continue_def]
      (* PairCases_on `env` >>
      full_simp_tac(srw_ss())[]*))
QED

Theorem small_eval_opapp_err:
  ∀env s es res.
    small_eval_list env s es res ⇒
    ∀s' vs.
      res = (s', Rval vs) ⇒
      ∀env0 v1 v0.
        LENGTH es + LENGTH v0 ≠ 1 ⇒
        ∃env' e' c'.
          e_step_reln^* (env0,s,Val v1,[Capp Opapp v0 () es,env]) (env',s',e',c') ∧
          e_step (env',s',e',c') = Eabort (Rtype_error)
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
      res = (s', Rval vs) ⇒
      ∀op env0 v1 v0.
        LENGTH es + LENGTH v0 > 2 ∧ op ≠ Opapp ∧ op ≠ AallocFixed
        ∧ op ≠ CopyStrStr ∧ op ≠ CopyStrAw8 ∧ op ≠ CopyAw8Str ∧ op ≠ CopyAw8Aw8
        ∧ op ≠ Arith FMA Float64T
        ⇒
        ∃env' e' c'.
          e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
          e_step (env',s',e',c') = Eabort Rtype_error
Proof
  ho_match_mp_tac small_eval_list_ind >> simp[] >> srw_tac[][] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
    srw_tac[][Once e_step_def,continue_def,application_thm,return_def] >>
    BasicProvers.CASE_TAC >>
    TRY BasicProvers.CASE_TAC >>
    Cases_on`s` >> fs[do_app_cases] >> rw[] >> fs[] >>
    TRY(PairCases_on`x`) >>
    gvs[CaseEq"prod",CaseEq"result",CaseEq"error_result",
        do_app_cases,PULL_EXISTS]
    >~ [`do_arith a p`] >- (
      Cases_on`a` \\ Cases_on ‘p’ using prim_type_cases
      \\ gvs[do_arith_def, CaseEq"list"] ) >>
    (* ThunkOp *)
    namedCases_on ‘v0’ ["", "hd tl"] >> gvs[]
    >- (Cases_on`v1` \\ simp[])
    >> Cases_on ‘tl’ >> gvs[] >>
    simp[do_app_def] >>
    gvs[oneline thunk_op_def, AllCaseEqs()] >>
    Cases_on`t` \\ gvs[]
    >- (Cases_on`v1` \\ simp[]) ) >>
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
      res = (s', Rval vs) ⇒
      ∀op env0 v1 v0.
        LENGTH es + LENGTH v0 > 4 ∧ op ≠ Opapp ∧ op ≠ AallocFixed
        ⇒
        ∃env' e' c' .
          e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
          e_step (env',s',e',c') = Eabort Rtype_error
Proof
  ho_match_mp_tac small_eval_list_ind >> simp[] >> srw_tac[][] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
    srw_tac[][Once e_step_def,continue_def,application_thm] >>
    BasicProvers.CASE_TAC >>
    TRY BasicProvers.CASE_TAC >>
    Cases_on`s` >> fs[do_app_cases] >> rw[] >> fs[] >>
    TRY(PairCases_on`x`) >>
    gvs[CaseEq"prod",CaseEq"result",CaseEq"error_result",
        do_app_cases,PULL_EXISTS]
    >~ [`do_arith a p`] >- (
      Cases_on`a` \\ Cases_on ‘p’ using prim_type_cases
      \\ gvs[do_arith_def, CaseEq"list"]
      \\ Cases_on`v0` \\ gvs[] ) >>
    (* ThunkOp *)
    namedCases_on ‘v0’ ["", "hd tl"] >> gvs[]
    >- (Cases_on`v1` \\ simp[])
    >> Cases_on ‘tl’ >> gvs[] >>
    simp[do_app_def] >>
    gvs[oneline thunk_op_def, AllCaseEqs()] >>
    Cases_on`t` \\ gvs[]
    \\ Cases_on`v1` \\ simp[] ) >>
  disj2_tac >>
  srw_tac[][Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp op (v1::v0) () es,env]`strip_assume_tac) >>
  full_simp_tac(srw_ss())[] >>
  first_x_assum(qspecl_then[`op`,`env'`,`v`,`v1::v0`]mp_tac) >>
  impl_tac >- simp[] >>
  metis_tac[transitive_RTC,transitive_def]
QED

val _ = temp_delsimps ["getOpClass_def"]

Theorem step_e_not_timeout:
  e_step (env',s3,e',c') = Eabort a ⇒ a ≠ Rtimeout_error
Proof
  full_simp_tac(srw_ss())[e_step_def] >>
  gs[push_def, return_def, continue_def, application_thm] >>
  rpt (TOP_CASE_TAC >> gs[]) >>
  imp_res_tac do_app_not_timeout >> strip_tac >>
  gs[] >>
  every_case_tac >> rveq >> gs[] >>
  imp_res_tac do_app_not_timeout >>
  every_case_tac >> fs[]
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
      res = (s', Rerr (Rabort a)) ⇒
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
  irule e_single_error_add_ctxt >> unabbrev_all_tac >> gs[]) >>
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
          e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',Exn v,[])
Proof
  ho_match_mp_tac (theorem"small_eval_list_strongind") >> simp[] >> srw_tac[][]
  >- (
  srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  Q.PAT_ABBREV_TAC`ctx = [(Capp A B C D,env)]` >>
  first_x_assum(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  srw_tac[][Once RTC_CASES_RTC_TWICE] >>
  first_assum(match_exists_tac o concl) >> srw_tac[][] >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def] >>
  metis_tac[RTC_REFL]) >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
  srw_tac[][Once RTC_CASES_RTC_TWICE] >>
  imp_res_tac e_step_add_ctxt >>
  Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
  first_x_assum(qspec_then`ctx`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  first_assum(match_exists_tac o concl) >> srw_tac[][] >>
  srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`]
QED

(** Does not hold anymore with floating-point optimization semantics
Theorem e_step_exp_err_any_ctxt:
  e_step (x,y,Exp z,c1) = Eabort ( a) ⇒
  e_step (x,y,Exp z,c2) = Eabort ( a)
Proof
  srw_tac[][e_step_def] >>
  rpt (TOP_CASE_TAC >> gs[]) >>
  full_simp_tac(srw_ss())[push_def,return_def,continue_def,application_thm] >>
  gs[] >>
  every_case_tac >> full_simp_tac(srw_ss())[]
QED **)

Inductive e_step_to_match:
  (ALL_DISTINCT (pat_bindings p []) ∧
   pmatch env.c (FST s) p v [] = Match env' ∧
   RTC e_step_reln (env with v := nsAppend (alist_to_ns env') env.v, s,  Exp e, [])
    (env'', s', ev, cs)
  ⇒ e_step_to_match env s v ((p,e)::pes) s') ∧

  (ALL_DISTINCT (pat_bindings p []) ∧
   pmatch env.c (FST s) p v [] = No_match ∧
   e_step_to_match env s v pes s'
  ⇒ e_step_to_match env s v ((p,e)::pes) s' )
End

Theorem e_step_to_match_Cmat:
  ∀env s v pes s'.  e_step_to_match env s v pes s'  ⇒
  ∀env''. ∃ev env' cs.
    RTC e_step_reln (env'', s,  Val v, [(Cmat () pes v, env)]) (env', s', ev, cs)
Proof
  ntac 3 strip_tac >> ho_match_mp_tac e_step_to_match_ind >> rw[] >>
  irule_at Any $ cj 2 RTC_rules >>
  simp[e_step_reln_def, e_step_def, continue_def, SF SFY_ss] >>
  first_x_assum $ qspec_then ‘env’ strip_assume_tac >>
  first_x_assum $ irule_at Any
QED

Theorem e_step_to_Con:
  ∀left mid right env s e sm vals cn vs.
    small_eval_list env s (e::left) (sm,Rval vals) ∧
    do_con_check env.c cn (LENGTH left + LENGTH right + LENGTH vs + 2)
    ⇒
    RTC e_step_reln
        (env,s,Exp e,[Ccon cn vs () (left ++ [mid] ++ right),env])
        (env,sm,Exp mid,[Ccon cn (REVERSE vals ++ vs) () right,env])
Proof
  Induct >> rw[] >> gvs[ADD1]
  >- (
    ntac 2 $ gvs[Once small_eval_list_cases] >>
    drule e_step_add_ctxt >> simp[] >>
    disch_then $ qspec_then `[Ccon cn vs () (mid::right),env]` assume_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, push_def]
    ) >>
  qpat_x_assum `small_eval_list _ _ _ _` mp_tac >>
  simp[Once small_eval_list_cases] >> rw[] >>
  drule e_step_add_ctxt >> simp[] >>
  disch_then $ qspec_then
    `[Ccon cn vs () (h::(left ++ [mid] ++ right)),env]` assume_tac >>
  simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
  irule_at Any $ cj 2 RTC_rules >>
  simp[e_step_reln_def, e_step_def, continue_def, push_def] >>
  last_x_assum drule >>
  disch_then $ qspecl_then [`mid`,`right`,`cn`,`v::vs`] mp_tac >>
  simp[ADD1, APPEND_ASSOC_CONS]
QED

Theorem e_step_to_App_mid:
  ∀left mid right env s e sm vals op vs.
  small_eval_list env s (e::left) (sm, Rval vals) ⇒
  RTC e_step_reln
    (env,s,Exp e,[Capp op vs () (left ++ [mid] ++ right),env])
    (env,sm,Exp mid,[Capp op (REVERSE vals ++ vs) () right,env])
Proof
  Induct >> rw[] >> gvs[]
  >- (
    ntac 2 $ gvs[Once small_eval_list_cases] >>
    drule e_step_add_ctxt >> simp[] >>
    disch_then $ qspec_then `[Capp op vs () (mid::right),env]` assume_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
    irule_at Any $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, push_def]
    ) >>
  qpat_x_assum `small_eval_list _ _ _ _` mp_tac >>
  simp[Once small_eval_list_cases] >> rw[] >>
  drule e_step_add_ctxt >> simp[] >>
  disch_then $ qspec_then
    `[Capp op vs () (h::(left ++ [mid] ++ right)),env]` assume_tac >>
  simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
  irule_at Any $ cj 2 RTC_rules >>
  simp[e_step_reln_def, e_step_def, continue_def, push_def] >>
  last_x_assum drule >>
  disch_then $ qspecl_then [`mid`,`right`,`op`,`v::vs`] mp_tac >>
  simp[ADD1, APPEND_ASSOC_CONS]
QED

Theorem small_eval_list_Rval_APPEND:
  small_eval_list env s (left ++ right) (s', Rval vs) ⇔
  ∃lvs rvs sl. vs = lvs ++ rvs ∧
    small_eval_list env s left (sl, Rval lvs) ∧
    small_eval_list env sl right (s', Rval rvs)
Proof
  reverse eq_tac >> rw[]
  >- (
    ntac 2 $ pop_assum mp_tac >>
    qid_spec_tac `lvs` >> Induct_on `small_eval_list` >> rw[] >> gvs[] >>
    simp[Once small_eval_list_cases, SF SFY_ss]
    ) >>
  pop_assum mp_tac >>
  map_every qid_spec_tac [`vs`,`right`,`left`] >>
  Induct_on `small_eval_list` >> rw[]
  >- (ntac 2 $ simp[Once small_eval_list_cases]) >>
  Cases_on `left` >> gvs[]
  >- (ntac 2 $ simp[Once small_eval_list_cases] >> goal_assum drule >> simp[]) >>
  simp[Once small_eval_list_cases, PULL_EXISTS] >>
  goal_assum $ drule_at Any >>
  pop_assum $ qspecl_then [`t`,`right`] mp_tac >> rw[] >>
  irule_at Any EQ_REFL >> gvs[SF SFY_ss]
QED

Theorem e_step_over_App_Opapp:
  ∀env s e es s' vals vs.
    small_eval_list env s (e::es) (s', Rval vals) ∧
    do_opapp (REVERSE vals ++ vs) = SOME (env', ea) ⇒
  RTC e_step_reln
    (env,s,Exp e,[Capp Opapp vs () es,env])
    (env',s',Exp ea,[])
Proof
  rw[] >> Cases_on `es` >> gvs[]
  >- (
    ntac 2 $ gvs[Once small_eval_list_cases] >>
    dxrule e_step_add_ctxt >> simp[] >>
    disch_then $ qspec_then `[Capp Opapp vs () [],env]` assume_tac >>
    simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
    irule $ cj 2 RTC_rules >>
    simp[e_step_reln_def, e_step_def, continue_def, application_thm,
         astTheory.getOpClass_def]
    ) >>
  qmatch_goalsub_abbrev_tac `Capp _ _ _ l` >>
  `l ≠ []` by (unabbrev_all_tac >> gvs[]) >> qpat_x_assum `Abbrev _` kall_tac >>
  Cases_on `l` using SNOC_CASES >> gvs[SNOC_APPEND] >>
  last_x_assum mp_tac >> rewrite_tac[Once $ GSYM APPEND] >>
  rewrite_tac[small_eval_list_Rval_APPEND] >> strip_tac >> gvs[] >>
  rev_dxrule e_step_to_App_mid >>
  disch_then $ qspecl_then [`x`,`[]`,`Opapp`,`vs`] assume_tac >> gvs[] >>
  simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
  ntac 2 $ gvs[Once small_eval_list_cases] >>
  dxrule e_step_add_ctxt >> simp[] >>
  disch_then $ qspec_then `[Capp Opapp (REVERSE lvs ++ vs) () [],env]` assume_tac >>
  simp[Once RTC_CASES_RTC_TWICE] >> goal_assum dxrule >>
  irule $ cj 2 RTC_rules >> gvs[REVERSE_APPEND] >>
  simp[e_step_reln_def, e_step_def, continue_def, application_thm,
       astTheory.getOpClass_def]
QED

(**********

  Prove that the small step semantics never gets stuck if there is
  still work to do (i.e., it must detect all type errors).  Thus, it
  either diverges or gives a result, and it can't do both.

**********)

Theorem untyped_safety_exp_step:
  ∀env s e c.
    (e_step (env,s,e,c) = Estuck) ⇔ (∃v. e = Val v ∨ e = Exn v) ∧ c = []
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
  PairCases_on `r` >>
  rename [‘small_eval env s e [] ((stl, ffi), result)’] >>
  Cases_on ‘result’ >>
  gvs[small_eval_def, e_step_reln_def]
  >- (goal_assum drule >> simp[e_step_def, continue_def]) >>
  rename [‘((stl,ffi), Rerr err)’] >>
  Cases_on `err` >> gvs[small_eval_def] >>
  goal_assum drule >> simp[e_step_def, continue_def]
QED

Theorem small_exp_safety2:
  ∀menv cenv s env e. e_diverges env s e ∨ ∃r. small_eval env s e [] r
Proof
  rw[e_diverges_def, DISJ_EQ_IMP, e_step_reln_def] >>
  rename [‘e_step (env',s',e',c') ≠ Estep _’] >>
  Cases_on ‘e_step (env',s',e',c')’ >> gvs[untyped_safety_exp_step]
  >- (PairCases_on `p` >> gvs[]) >~
  [‘e_step _ = Eabort a’]
  >- (
    qexists_tac `(s', Rerr (Rabort a))` >> rw[small_eval_def] >>
    goal_assum drule >> simp[]
    ) >~
  [‘e_step_reln꙳ _ (env', s', Val v, [])’]
  >- (qexists_tac `(s',Rval v)` >> rw[small_eval_def] >> goal_assum drule >>
      simp[]) >~
  [‘e_step_reln꙳ _ (env', s', Exn ex, [])’]
  >- (
    qexists_tac ‘(s', Rerr (Rraise ex))’ >> rw[small_eval_def] >>
    goal_assum drule >> simp[])
QED

Theorem untyped_safety_exp:
  ∀s env e. (∃r. small_eval env s e [] r) = ¬e_diverges env s e
Proof
  metis_tac[small_exp_safety2, small_exp_safety1]
QED



(******************** Declarations *******************)

val decl_step_ss = simpLib.named_rewrites "decl_step_ss"
  [decl_step_reln_def, decl_step_def, decl_continue_def];

Inductive small_eval_decs:
  small_eval_decs benv st [] (st, Rval empty_dec_env) ∧

  (small_eval_dec benv (st, Decl d, []) (st', Rval env) ∧
   small_eval_decs (env +++ benv) st' ds (st'', r)
      ⇒ small_eval_decs benv st (d::ds) (st'', combine_dec_result env r)) ∧

  (small_eval_dec benv (st, Decl d, []) (st', Rerr e)
      ⇒ small_eval_decs benv st (d::ds) (st', Rerr e))
End

Theorem small_eval_decs_determ:
  ∀env st ds r1 r2.
    small_eval_decs env st ds r1 ∧ small_eval_decs env st ds r2 ⇒ r1 = r2
Proof
  Induct_on `small_eval_decs` >> rw[]
  >- gvs[Once small_eval_decs_cases] >>
  pop_assum mp_tac >> rw[Once small_eval_decs_cases] >> gvs[] >>
  rev_drule small_eval_dec_determ >> disch_then drule >> strip_tac >> gvs[] >>
  first_x_assum drule >> rw[] >> gvs[]
QED

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
    TOP_CASE_TAC >> gvs[AllCaseEqs()] >> rw[untyped_safety_exp_step]
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
  Cases_on `decl_step env b` >> gvs[] >> PairCases_on `b` >~
  [‘decl_step _ _ = Dabort ab’]
  >- (last_x_assum mp_tac >> simp[] >>
      qexists ‘(b0, Rerr $ Rabort ab)’ >>
      simp[small_eval_dec_def] >> metis_tac[]) >~
  [‘decl_step _ _ = Ddone’]
  >- (
    gvs[decl_step_to_Ddone] >>
    last_x_assum $ qspec_then `(b0,Rval e)` assume_tac >>
    gvs[small_eval_dec_def]) >~
  [‘decl_step _ _ = Draise exn’]
  >- (
    last_x_assum mp_tac >> simp[] >>
    qexists ‘(b0, Rerr $ Rraise exn)’ >>
    simp[small_eval_dec_def] >> metis_tac[])
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
  ∀benv extra (st:'ffi state) dev c s' dev' c' a .
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
  ∀env (st:'ffi state) dev c ex .
    decl_step env (st, dev, c) = Draise ex ⇔
      (∃env' v locs p.
        dev = ExpVal env' (Val v) [] locs p ∧
        ALL_DISTINCT (pat_bindings p []) ∧
        pmatch (collapse_env env c).c st.refs p v [] = No_match ∧
        ex = bind_exn_v) ∨
      (∃env' v env'' locs p.
        dev = ExpVal env' (Exn v) [] locs p ∧ ex = v)
Proof
  rw[] >> eq_tac >> rw[] >> gvs[decl_step_def] >>
  every_case_tac >> gvs[] >>
  gvs[decl_continue_def] >> every_case_tac >> gvs[]
QED

Theorem e_step_reln_decl_step_reln:
  ∀env (stffi:('ffi,v) store_ffi) ev cs env' stffi' ev' cs'
    benv (st:'ffi state) locs p dcs.
  e_step_reln꙳ (env, stffi,  ev, cs) (env', stffi', ev', cs')
  ⇒ (decl_step_reln benv)꙳
      (st with <| refs := FST stffi ; ffi := SND stffi ; |>,
          ExpVal env ev cs locs p, dcs)
      (st with <| refs := FST stffi' ; ffi := SND stffi' ; |>,
          ExpVal env' ev' cs' locs p, dcs)
Proof
  Induct_on `RTC e_step_reln` >> rw[] >> simp[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[decl_step_reln_def, decl_step_def] >> gvs[e_step_reln_def] >>
  every_case_tac >> gvs[e_step_def, continue_def] >>
  gs[push_def, return_def] >>
  gvs[decl_step_reln_def, decl_step_def]
QED

Theorem small_eval_decs_Rval_Dmod_lemma:
  ∀env (st:'ffi state) decs st' new_env envc envb enva mn.
    small_eval_decs env st decs (st', Rval new_env) ∧
    env = envc +++ envb +++ enva
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
  irule $ iffRL RTC_CASES_RTC_TWICE >>
  first_x_assum $ irule_at Any >> simp[extend_dec_env_def]
QED

Theorem small_eval_decs_Rval_Dmod:
  ∀env st ds res st' new_env mn.
   small_eval_decs env st ds (st', Rval new_env)
  ⇒ small_eval_dec env (st, Decl (Dmod mn ds), [])
      (st', Rval $ lift_dec_env mn new_env)
Proof
  rw[] >> drule small_eval_decs_Rval_Dmod_lemma >>
  disch_then $ qspecl_then [`empty_dec_env`,`empty_dec_env`,`env`] mp_tac >>
  rw[small_eval_dec_def] >> simp[Once RTC_CASES1, SF decl_step_ss]
QED

Theorem small_eval_decs_Rerr_Dmod_lemma:
  ∀env (st:'ffi state) decs st' err envc envb enva mn.
    small_eval_decs env st decs (st', Rerr err) ∧
    env = envc +++ envb +++ enva
  ⇒ ∃dst.
     (decl_step_reln enva)꙳ (st,Env envc,[Cdmod mn envb decs]) (st',dst) ∧
     decl_step enva (st',dst) = Rerr_to_decl_step_result err
Proof
  Induct_on ‘small_eval_decs’ >> reverse $ rw[] >> gvs[]
  >- (
    simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
    gvs[small_eval_dec_def] >>
    qspecl_then [`enva`,`[Cdmod mn (envc +++ envb) ds]`]
      mp_tac RTC_decl_step_reln_ctxt_weaken >>
    simp[collapse_env_def] >> PairCases_on `dst'` >>
    disch_then drule >> simp[] >> strip_tac >> goal_assum drule >>
    irule decl_step_ctxt_weaken_err >> simp[collapse_env_def]) >>
  rename [‘combine_dec_result env' r’] >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[Cdmod mn (envc +++ envb) decs]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule_at Any $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >>
  first_x_assum $ qspecl_then [‘env'’, ‘envc +++ envb’, ‘enva’, ‘mn’] mp_tac >>
  simp[] >> strip_tac >>
  first_x_assum $ irule_at Any >> simp[]
QED

Theorem small_eval_decs_Rerr_Dmod:
  ∀env st ds res st' err mn.
   small_eval_decs env st ds (st', Rerr err)
  ⇒ small_eval_dec env (st, Decl (Dmod mn ds), []) (st', Rerr err)
Proof
  rw[] >> drule small_eval_decs_Rerr_Dmod_lemma >>
  disch_then $ qspecl_then [`empty_dec_env`,`empty_dec_env`,`env`] mp_tac >>
  rw[small_eval_dec_def] >> simp[Once RTC_CASES1, SF decl_step_ss] >>
  irule_at Any OR_INTRO_THM2 >> simp[] >>
  first_x_assum $ qspec_then ‘mn’ strip_assume_tac >>
  rename [‘decl_step env st2’] >> Cases_on ‘st2’ >>
  metis_tac[]
QED

Theorem small_eval_decs_Rval_Dlocal_lemma_1:
  ∀env (st:'ffi state) decs st' new_env envc envb enva gds.
    small_eval_decs env st decs (st', Rval new_env) ∧
    env = envc +++ envb +++ enva
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
  irule $ iffRL RTC_CASES_RTC_TWICE >>
  first_x_assum $ irule_at Any >> simp[extend_dec_env_def]
QED

Theorem small_eval_decs_Rval_Dlocal_lemma_2:
  ∀env (st:'ffi state) decs st' new_env envc lenv genv enva.
    small_eval_decs env st decs (st', Rval new_env) ∧
    env = envc +++ genv +++ lenv +++ enva
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
  irule $ iffRL RTC_CASES_RTC_TWICE >>
  first_x_assum $ irule_at Any >> simp[extend_dec_env_def]
QED

Theorem small_eval_decs_Rval_Dlocal:
  ∀env (st:'ffi state) lds st' lenv gds st'' genv.
   small_eval_decs env st lds (st', Rval lenv) ∧
   small_eval_decs (lenv +++ env) st' gds (st'', Rval genv)
  ⇒ small_eval_dec env (st, Decl (Dlocal lds gds), []) (st'', Rval $ genv)
Proof
  rw[] >>
  qpat_x_assum `small_eval_decs _ _ _ _` mp_tac >>
  drule small_eval_decs_Rval_Dlocal_lemma_1 >>
  disch_then $ qspecl_then [`empty_dec_env`,`empty_dec_env`,`env`,`gds`] mp_tac >>
  simp[] >> strip_tac >> strip_tac >>
  drule small_eval_decs_Rval_Dlocal_lemma_2 >>
  disch_then $ qspecl_then [`empty_dec_env`,`lenv`,`empty_dec_env`,`env`] mp_tac >>
  rw[] >> simp[small_eval_dec_def] >> simp[Once RTC_CASES1, SF decl_step_ss] >>
  irule $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >> simp[]
QED

Theorem small_eval_decs_Rerr_Dlocal_lemma_1:
  ∀env (st:'ffi state) decs st' err envc envb enva gds.
    small_eval_decs env st decs (st', Rerr err) ∧
    env = envc +++ envb +++ enva
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
    irule_at Any decl_step_ctxt_weaken_err >> simp[collapse_env_def]
    ) >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[CdlocalL (envc +++ envb) decs gds]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule_at Any $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >> simp[]
QED

Theorem small_eval_decs_Rerr_Dlocal_lemma_2:
  ∀env (st:'ffi state) decs st' err envc lenv genv enva.
    small_eval_decs env st decs (st', Rerr err) ∧
    env = envc +++ genv +++ lenv +++ enva
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
    irule_at Any decl_step_ctxt_weaken_err >> simp[collapse_env_def]
    ) >>
  Cases_on `r` >> gvs[combine_dec_result_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2 >>
  gvs[small_eval_dec_def] >>
  qspecl_then [`enva`,`[CdlocalG lenv (envc +++ genv) decs]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> simp[] >> strip_tac >>
  irule_at Any $ iffRL RTC_CASES_RTC_TWICE >> goal_assum drule >> simp[]
QED

Theorem small_eval_decs_Rerr_Dlocal:
  ∀env st lds gds st' err.
   (small_eval_decs env st lds (st', Rerr err) ∨
    ∃st'' new_env.
      small_eval_decs env st lds (st'', Rval new_env) ∧
      small_eval_decs (new_env +++ env) st'' gds (st', Rerr err))
  ⇒ small_eval_dec env (st, Decl (Dlocal lds gds), []) (st', Rerr err)
Proof
  rw[small_eval_dec_def] >>
  simp[Once RTC_CASES1, SF decl_step_ss] >> irule_at Any OR_INTRO_THM2
  >- (irule small_eval_decs_Rerr_Dlocal_lemma_1 >> simp[]) >>
  irule_at Any $ iffRL RTC_CASES_RTC_TWICE >>
  irule_at Any small_eval_decs_Rval_Dlocal_lemma_1 >>
  goal_assum drule >> simp[] >>
  irule small_eval_decs_Rerr_Dlocal_lemma_2 >> simp[]
QED

Theorem small_decl_diverges_prefix:
  ∀env a b.
    (decl_step_reln env)꙳ a b ∧
    small_decl_diverges env b
  ⇒ small_decl_diverges env a
Proof
  rw[small_decl_diverges_def] >>
  qspecl_then [`env`,`a`,`b`,`b'`] assume_tac RTC_decl_step_confl >> gvs[] >>
  pop_assum mp_tac >> simp[Once RTC_CASES1] >> rw[] >> gvs[] >> goal_assum drule
QED

Theorem small_decl_diverges_suffix:
  ∀env a b.
    (decl_step_reln env)꙳ b a ∧
    small_decl_diverges env b
  ⇒ small_decl_diverges env a
Proof
  rw[small_decl_diverges_def] >>
  first_x_assum irule >> simp[Once RTC_CASES_RTC_TWICE] >>
  goal_assum drule >> simp[]
QED

Theorem small_decl_diverges_ExpVal_lemma[local]:
  ∀benv (st:'ffi state) env ev cs locs p dcs b.
    (decl_step_reln benv)꙳ (st,ExpVal env ev cs locs p,dcs) b ∧
    (∀res. (e_step_reln꙳ (env,(st.refs,st.ffi),ev,cs) res ⇒
      ∃res'. e_step_reln res res'))
  ⇒ ∃c. decl_step_reln benv b c
Proof
  gen_tac >> Induct_on ‘RTC (decl_step_reln benv)’ >> rw[] >>
  gvs[decl_step_reln_def, e_step_reln_def]
  >- (
    last_x_assum $ qspec_then ‘(env,(st.refs,st.ffi),ev,cs)’ mp_tac >> rw[] >>
    simp[decl_step_def] >> every_case_tac >> gvs[] >>
    gvs[e_step_def, continue_def]
    ) >>
  first_x_assum irule >>
  ‘∃r. e_step (env,(st.refs,st.ffi),ev,cs) = Estep r’ by (
    first_x_assum irule >> simp[]) >>
  rename1 ‘Dstep dst’ >> PairCases_on ‘dst’ >> simp[] >>
  PairCases_on ‘r’ >>
  rename [‘e_step _ = Estep (env1, (stl,ffs), eve, stk)’] >>
  qexistsl_tac [‘stk’,‘env1’,‘eve’,‘locs’,‘p’] >>
  ‘stl = dst0.refs ∧ ffs = dst0.ffi’ by (
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

Theorem decl_step_to_Dmod:
  ∀left mid right env (s:'ffi state) sm envm envc envb enva mn.
    small_eval_decs env s left (sm, Rval envm) ∧
    env = envc +++ envb +++ enva
  ⇒ RTC (decl_step_reln enva)
      (s, Env envc, [Cdmod mn envb (left ++ [mid] ++ right)])
      (sm, Decl mid, [Cdmod mn (envm +++ envc +++ envb) right])
Proof
  Induct >> rw[] >> gvs[]
  >- (
    gvs[Once small_eval_decs_cases] >>
    irule RTC_SUBSET >>
    simp[decl_step_reln_def, decl_step_def, decl_continue_def]
    ) >>
  qpat_x_assum `small_eval_decs _ _ _ _` mp_tac >>
  simp[Once small_eval_decs_cases] >> rw[small_eval_dec_def] >>
  simp[Once RTC_CASES1, decl_step_reln_def, decl_step_def, decl_continue_def] >>
  qspecl_then [`enva`,`[Cdmod mn (envc +++ envb) (left ++ [mid] ++ right)]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> rw[] >>
  simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
  `∃envl. r = Rval envl` by (Cases_on `r` >> gvs[combine_dec_result_def]) >> gvs[] >>
  `envm = envl +++ env` by gvs[combine_dec_result_def, extend_dec_env_def] >> gvs[] >>
  once_rewrite_tac[GSYM extend_dec_env_assoc] >> last_x_assum irule >> simp[]
QED

Theorem decl_step_to_Dlocal_global:
  ∀left mid right env (s:'ffi state) sm envm envd envc envb enva.
    small_eval_decs env s left (sm, Rval envm) ∧
    env = envd +++ envc +++ envb +++ enva
  ⇒ RTC (decl_step_reln enva)
      (s, Env envd, [CdlocalG envb envc (left ++ [mid] ++ right)])
      (sm, Decl mid, [CdlocalG envb (envm +++ envd +++ envc) right])
Proof
  Induct >> rw[] >> gvs[]
  >- (
    gvs[Once small_eval_decs_cases] >>
    irule RTC_SUBSET >>
    simp[decl_step_reln_def, decl_step_def, decl_continue_def]
    ) >>
  qpat_x_assum `small_eval_decs _ _ _ _` mp_tac >>
  simp[Once small_eval_decs_cases] >> rw[small_eval_dec_def] >>
  simp[Once RTC_CASES1, decl_step_reln_def, decl_step_def, decl_continue_def] >>
  qspecl_then [`enva`,`[CdlocalG envb (envd +++ envc) (left ++ [mid] ++ right)]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> rw[] >>
  simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
  `∃envl. r = Rval envl` by (Cases_on `r` >> gvs[combine_dec_result_def]) >> gvs[] >>
  `envm = envl +++ env` by gvs[combine_dec_result_def, extend_dec_env_def] >> gvs[] >>
  once_rewrite_tac[GSYM extend_dec_env_assoc] >> last_x_assum irule >> simp[]
QED

Theorem decl_step_to_Dlocal_local:
  ∀left mid right env (s:'ffi state) sm envm envc envb enva ds.
    small_eval_decs env s left (sm, Rval envm) ∧
    env = envc +++ envb +++ enva
  ⇒ RTC (decl_step_reln enva)
      (s, Env envc, [CdlocalL envb (left ++ [mid] ++ right) ds])
      (sm, Decl mid, [CdlocalL (envm +++ envc +++ envb) right ds])
Proof
  Induct >> rw[] >> gvs[]
  >- (
    gvs[Once small_eval_decs_cases] >>
    irule RTC_SUBSET >>
    simp[decl_step_reln_def, decl_step_def, decl_continue_def]
    ) >>
  qpat_x_assum `small_eval_decs _ _ _ _` mp_tac >>
  simp[Once small_eval_decs_cases] >> rw[small_eval_dec_def] >>
  simp[Once RTC_CASES1, decl_step_reln_def, decl_step_def, decl_continue_def] >>
  qspecl_then [`enva`,`[CdlocalL (envc +++ envb) (left ++ [mid] ++ right) ds]`]
    mp_tac RTC_decl_step_reln_ctxt_weaken >>
  simp[collapse_env_def] >> disch_then drule >> rw[] >>
  simp[Once RTC_CASES_RTC_TWICE] >> goal_assum drule >>
  `∃envl. r = Rval envl` by (Cases_on `r` >> gvs[combine_dec_result_def]) >> gvs[] >>
  `envm = envl +++ env` by gvs[combine_dec_result_def, extend_dec_env_def] >> gvs[] >>
  once_rewrite_tac[GSYM extend_dec_env_assoc] >> last_x_assum irule >> simp[]
QED

Theorem decl_step_ignore_clock:
  decl_step env (st,dev,dcs) = Dstep (st',dev',dcs') ⇒
  decl_step env (st with clock := clk,dev,dcs) = Dstep (st' with clock := clk,dev',dcs')
Proof
  Cases_on `dev` >> rw[decl_step_def] >> gvs[decl_continue_def, AllCaseEqs()]
QED

Theorem RTC_decl_step_reln_ignore_clock:
  ∀env clk st dev dcs st' dev' dcs'.
    RTC (decl_step_reln env) (st,dev,dcs) (st',dev',dcs') ⇒
    RTC (decl_step_reln env)
      (st with clock := clk,dev,dcs) (st' with clock := clk,dev',dcs')
Proof
  ntac 2 gen_tac >> Induct_on `RTC` >> rw[] >> simp[] >>
  gvs[decl_step_reln_def] >> rename1 `Dstep foo` >> PairCases_on `foo` >> gvs[] >>
  irule $ cj 2 RTC_RULES >> goal_assum $ dxrule_at Any >>
  simp[decl_step_reln_def] >> metis_tac[decl_step_ignore_clock]
QED



(******************** IO traces *******************)

Theorem application_ffi_unchanged:
  ∀op env st ffi vs cs env' st' ffi' ev cs'.
    (∀s. op ≠ FFI s) ∧
    application op env (st, ffi) vs cs = Estep (env', (st', ffi'), ev, cs')
  ⇒ ffi = ffi'
Proof
  rpt gen_tac >> rw[application_thm, return_def] >>
  qspecl_then [`st`,`ffi`,`op`,`vs`]
    assume_tac semanticPrimitivesPropsTheory.do_app_ffi_unchanged >>
  qspecl_then [`st`,`ffi`,`op`,`REVERSE vs`]
    assume_tac semanticPrimitivesPropsTheory.do_app_ffi_unchanged >>
  every_case_tac >> gvs[]
QED

Theorem e_step_ffi_changed:
  ∀env st ffi ev cs ffi' env' st' ev' cs'.
  e_step (env, (st, ffi),  ev, cs) = Estep (env', (st', ffi'), ev', cs') ∧
  ffi ≠ ffi' ⇒
  ∃ s conf lnum ccs ws ffi_st ws' b.
    ev = Val (Litv (StrLit conf)) ∧
    cs = (Capp (FFI s) [Loc b lnum] () [], env') :: ccs ∧
    store_lookup lnum st = SOME (W8array ws) ∧
    s ≠ «» ∧
    ffi.oracle
       (ExtCall s) ffi.ffi_state (MAP (λc. n2w $ ORD c) (explode conf)) ws =
       Oracle_return ffi_st ws' ∧
    LENGTH ws = LENGTH ws' ∧
    ev' = Val (Conv NONE []) ∧
    cs' = ccs ∧
    st' = LUPDATE (W8array ws') lnum st ∧
    ffi'.oracle = ffi.oracle ∧
    ffi'.ffi_state = ffi_st ∧
    ffi'.io_events =
      ffi.io_events ++
        [IO_event (ExtCall s) (MAP (λc. n2w $ ORD c) (explode conf))
                  (ZIP (ws,ws'))]
Proof
  rpt gen_tac >> simp[e_step_def] >>
  every_case_tac >> gvs[return_def, push_def, continue_def]
  >- (
    strip_tac >> rename1 `application op _ _ _ _ ` >>
    Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (irule application_ffi_unchanged >> rpt $ goal_assum drule) >>
    gvs[application_def, do_app_def] >>
    every_case_tac  >> gs[]
    ) >>
  every_case_tac >> gvs[] >>
  rename1 `application op _ _ _ _ ` >>
  (
    strip_tac >> Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (drule_all application_ffi_unchanged >> gvs[]) >>
    gvs[application_def, do_app_def, call_FFI_def, astTheory.getOpClass_def] >>
    every_case_tac >> gvs[return_def, store_lookup_def, store_assign_def]
  ) >>
  fs[combinTheory.o_DEF]
QED

Theorem decl_step_ffi_changed:
  decl_step benv (st, dev, dcs) = Dstep (st', dev', dcs') ∧ st.ffi ≠ st'.ffi ⇒
  ∃env conf s lnum env' ccs locs pat ws ffi_st ws' b.
    dev = ExpVal env (Val (Litv (StrLit conf)))
            ((Capp (FFI s) [Loc b lnum] () [], env')::ccs) locs pat ∧
    store_lookup lnum st.refs = SOME (W8array ws) ∧
    s ≠ «» ∧
    st.ffi.oracle (ExtCall s) st.ffi.ffi_state
      (MAP (λc. n2w $ ORD c) (explode conf)) ws =
      Oracle_return ffi_st ws' ∧
    LENGTH ws = LENGTH ws' ∧
    dev' = ExpVal env' (Val (Conv NONE [])) ccs locs pat ∧
    st' = st with <|
            refs := LUPDATE (W8array ws') lnum st.refs;
            ffi := st.ffi with <|
              ffi_state := ffi_st;
              io_events := st.ffi.io_events ++
                 [IO_event (ExtCall s) (MAP (λc. n2w $ ORD c) (explode conf))
                           (ZIP (ws,ws'))] |>
            |> ∧
    dcs = dcs'
Proof
  simp[decl_step_def] >>
  Cases_on `∃d. dev = Decl d` >> gvs[]
  >- (every_case_tac >> gvs[state_component_equality]) >>
  Cases_on ‘∃e. dev = Env e’ >> gvs[]
  >- (simp[decl_continue_def] >> every_case_tac >> gvs[state_component_equality]) >>
  TOP_CASE_TAC >> gvs[] >>
  qmatch_goalsub_abbrev_tac `e_step_result_CASE stepe` >>
  qpat_abbrev_tac `foo = e_step_result_CASE _ _ _ _` >> strip_tac >>
  qspecl_then [‘s’,‘st.refs’,‘st.ffi’,‘e’,‘l’,‘st'.ffi’] assume_tac e_step_ffi_changed >>
  gvs[Abbr `stepe`] >> last_x_assum assume_tac >> last_x_assum mp_tac >>
  TOP_CASE_TAC >> gvs[]
  >- (unabbrev_all_tac >> gvs[] >> every_case_tac >> gvs[state_component_equality]) >>
  every_case_tac >> gvs[Abbr `foo`, state_component_equality] >> rw[] >> gvs[] >>
  gvs[e_step_def, continue_def, application_thm, do_app_def, call_FFI_def,
      return_def, store_assign_def, store_lookup_def, store_v_same_type_def,
      astTheory.getOpClass_def, combinTheory.o_DEF]
QED

Theorem io_events_mono_e_step:
  e_step e1 = Estep e2 ⇒
  io_events_mono (SND $ FST $ SND e1) (SND $ FST $ SND e2)
Proof
  PairCases_on `e1` >> PairCases_on `e2` >> gvs[] >> rw[] >>
  rename1 `e_step (env1,(st1,ffi1),ev1,cs1) = _ (env2,(st2,ffi2),ev2,cs2)` >>
  Cases_on `ffi1 = ffi2` >- simp[io_events_mono_refl] >>
  drule_all e_step_ffi_changed >> rw[] >> gvs[] >>
  rw[io_events_mono_def]
QED

Theorem io_events_mono_decl_step:
  decl_step env dst1 = Dstep dst2 ⇒
  io_events_mono (FST dst1).ffi (FST dst2).ffi
Proof
  PairCases_on `dst1` >> PairCases_on `dst2` >> gvs[] >> rw[] >>
  Cases_on `dst10.ffi = dst20.ffi` >- simp[io_events_mono_refl] >>
  drule_all decl_step_ffi_changed >> rw[] >> gvs[] >>
  rw[io_events_mono_def]
QED

Theorem RTC_e_step_reln_io_events_mono:
  ∀env s ev cs env' s' ev' cs'.
    RTC e_step_reln (env,s,ev,cs) (env',s',ev',cs')
  ⇒ io_events_mono (SND s) (SND s')
Proof
  Induct_on `RTC` >> rw[] >> simp[] >>
  rename1 `(_,_) = ctxt` >> PairCases_on `ctxt` >> gvs[e_step_reln_def] >>
  imp_res_tac io_events_mono_e_step >> gvs[] >>
  metis_tac[io_events_mono_trans]
QED

Theorem RTC_decl_step_reln_io_events_mono:
  ∀env s s'.
    RTC (decl_step_reln env) s s'
  ⇒ io_events_mono (FST s).ffi (FST s').ffi
Proof
  gen_tac >> Induct_on `RTC` >> rw[] >> simp[] >>
  PairCases_on `s` >> PairCases_on `s'` >> gvs[decl_step_reln_def] >>
  imp_res_tac io_events_mono_decl_step >> gvs[] >>
  metis_tac[io_events_mono_trans]
QED

Theorem lprefix_chain_RTC_decl_step_reln:
  lprefix_chain
    { fromList (FST st').ffi.io_events | RTC (decl_step_reln env) st st' }
Proof
  rw[lprefix_chain_def] >> simp[LPREFIX_fromList, from_toList] >>
  rev_drule RTC_decl_step_confl >> disch_then drule >> rw[] >>
  imp_res_tac RTC_decl_step_reln_io_events_mono >> gvs[io_events_mono_def]
QED

(*
  Big step/small step equivalence
*)
open preamble;
open libTheory semanticPrimitivesTheory bigStepTheory smallStepTheory;
open bigSmallInvariantsTheory semanticPrimitivesPropsTheory determTheory bigClockTheory;
open bigStepPropsTheory;

val _ = new_theory "bigSmallEquiv";

(* ------------------------ Big step/small step equivalence ----------------- *)

val list_end_case = Q.prove (
`!l. l = [] ∨ ?x l'. l = l' ++ [x]`,
 Induct_on `l` >>
 srw_tac[][] >>
 metis_tac [APPEND]);

val application_thm = Q.prove (
`!op env s vs c.
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
       | SOME (v1,Rerr (Rabort a)) => Eabort a`,
 srw_tac[][application_def] >>
 cases_on `op` >>
 srw_tac[][]);

val small_eval_prefix = Q.prove (
`∀s env e c cenv' s' env' e' c' r.
  e_step_reln^* (env,s,Exp e,c) (env',s',Exp e',c') ∧
  small_eval env' s' e' c' r
  ⇒
  small_eval env s e c r`,
 srw_tac[][] >>
 PairCases_on `r` >>
 cases_on `r2` >>
 full_simp_tac(srw_ss())[small_eval_def] >-
 metis_tac [transitive_RTC, transitive_def] >>
 cases_on `e''` >>
 TRY (Cases_on `a`) >>
 full_simp_tac(srw_ss())[small_eval_def] >>
 metis_tac [transitive_RTC, transitive_def]);

val e_single_step_add_ctxt = Q.prove (
`!s env e c s' env' e' c' c''.
  (e_step (env,s,e,c) = Estep (env',s',e',c'))
  ⇒
  (e_step (env,s,e,c++c'') = Estep (env',s',e',c'++c''))`,
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
     full_simp_tac(srw_ss())[return_def]));

val e_single_error_add_ctxt = Q.prove (
`!env s e c c'.
  (e_step (env,s,e,c) = Eabort a)
  ⇒
  (e_step (env,s,e,c++c') = Eabort a)`,
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
     full_simp_tac(srw_ss())[return_def]));

val e_step_add_ctxt_help = Q.prove (
`!st1 st2. e_step_reln^* st1 st2 ⇒
  !s1 env1 e1 c1 s2 env2 e2 c2 c'.
    (st1 = (env1,s1,e1,c1)) ∧ (st2 = (env2,s2,e2,c2))
    ⇒
    e_step_reln^* (env1,s1,e1,c1++c') (env2,s2,e2,c2++c')`,
HO_MATCH_MP_TAC RTC_INDUCT >>
srw_tac[][e_step_reln_def] >-
metis_tac [RTC_REFL] >>
PairCases_on `st1'` >>
full_simp_tac(srw_ss())[] >>
imp_res_tac e_single_step_add_ctxt >>
full_simp_tac(srw_ss())[] >>
srw_tac[][Once RTC_CASES1] >>
metis_tac [e_step_reln_def]);

val e_step_add_ctxt = Q.prove (
`!s1 env1 e1 c1 s2 env2 e2 c2 c'.
   e_step_reln^* (env1,s1,e1,c1) (env2,s2,e2,c2)
   ⇒
   e_step_reln^* (env1,s1,e1,c1++c') (env2,s2,e2,c2++c')`,
metis_tac [e_step_add_ctxt_help]);

val e_step_raise = Q.prove (
`!s env err c v env' env''.
  EVERY (\c. ¬?pes env. c = (Chandle () pes, env)) c ∧
  (c ≠ [])
  ⇒
  e_step_reln^* (env,s,Val v,(Craise (), env')::c) (env',s,Val v,[(Craise (), env')])`,
induct_on `c` >>
srw_tac[][] >>
srw_tac[][Once RTC_CASES1] >>
cases_on `c` >>
full_simp_tac(srw_ss())[] >>
srw_tac[][e_step_reln_def, e_step_def, continue_def] >>
every_case_tac >>
full_simp_tac(srw_ss())[] >>
cases_on `o'` >>
full_simp_tac(srw_ss())[]);

val small_eval_err_add_ctxt = Q.prove (
`!s env e c err c' s'.
  EVERY (\c. ¬?pes env. c = (Chandle () pes, env)) c'
  ⇒
  small_eval env s e c (s', Rerr err) ⇒ small_eval env s e (c++c') (s', Rerr err)`,
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
     metis_tac [transitive_RTC, transitive_def]))

val small_eval_err_add_ctxt =
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

val small_eval_raise = Q.prove (
`!s env cn e1 pes c r.
  small_eval env s (Raise e1) c r =
  small_eval env s e1 ((Craise (),env)::c) r`,
 small_eval_step_tac);

val small_eval_handle = Q.prove (
`!env s cn e1 pes c r.
  small_eval env s (Handle e1 pes) c r =
  small_eval env s e1 ((Chandle () pes,env)::c) r`,
small_eval_step_tac);

val small_eval_con = Q.prove (
`!env s cn e1 es ns c r.
  do_con_check env.c cn (LENGTH (es++[e1]))
  ⇒
  (small_eval env s (Con cn (es++[e1])) c r =
   small_eval env s e1 ((Ccon cn [] () (REVERSE es),env)::c) r)`,
 srw_tac[][do_con_check_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 small_eval_step_tac);

val small_eval_app = Q.prove (
`!env s op es c r.
  small_eval env s (App op es) c r ⇔
  (es = [] ∧ small_eval env s (App op []) c r) ∨
  (?e es'. (es = es'++[e]) ∧ small_eval env s e ((Capp op [] () (REVERSE es'),env)::c) r)`,
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
 metis_tac []);

val small_eval_log = Q.prove (
`!env s op e1 e2 c r.
  small_eval env s (Log op e1 e2) c r =
  small_eval env s e1 ((Clog op () e2,env)::c) r`,
small_eval_step_tac);

val small_eval_if = Q.prove (
`!env s e1 e2 e3 c r.
  small_eval env s (If e1 e2 e3) c r =
  small_eval env s e1 ((Cif () e2 e3,env)::c) r`,
small_eval_step_tac);

val small_eval_match = Q.prove (
`!env s e1 pes c r err_v.
  small_eval env s (Mat e1 pes) c r =
  small_eval env s e1 ((Cmat () pes (Conv (SOME bind_stamp) []),env)::c) r`,
small_eval_step_tac);

val small_eval_let = Q.prove (
`!env s n e1 e2 c r.
  small_eval env s (Let n e1 e2) c r =
  small_eval env s e1 ((Clet n () e2,env)::c) r`,
small_eval_step_tac);

val small_eval_letrec = Q.prove (
`!menv cenv env s funs e1 c r.
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ⇒
  (small_eval env s (Letrec funs e1) c r =
   small_eval (env with v := build_rec_env funs env env.v) s e1 c r)`,
small_eval_step_tac);

val small_eval_tannot = Q.prove (
`!env s e1 t c r.
  small_eval env s (Tannot e1 t) c r =
  small_eval env s e1 ((Ctannot () t,env)::c) r`,
 small_eval_step_tac);

val small_eval_lannot = Q.prove (
`!env s e1 l c r.
  small_eval env s (Lannot e1 l) c r =
  small_eval env s e1 ((Clannot () l,env)::c) r`,
 small_eval_step_tac);

val (small_eval_list_rules, small_eval_list_ind, small_eval_list_cases) = Hol_reln `
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
  (small_eval_list env s1 (e::es) (s3, Rerr (Rabort a))))`;

val small_eval_list_length = Q.prove (
`!env s1 es r. small_eval_list env s1 es r ⇒
  !vs s2. (r = (s2, Rval vs)) ⇒ (LENGTH es = LENGTH vs)`,
HO_MATCH_MP_TAC small_eval_list_ind >>
srw_tac[][] >>
srw_tac[][]);

val small_eval_list_step = Q.prove (
`!env s2 es r. small_eval_list env s2 es r ⇒
  (!e v vs cn vs' env' s1 s3 v_con.
     do_con_check env.c cn (LENGTH vs' + 1 + LENGTH vs) ∧
     (build_conv env.c cn (REVERSE (REVERSE vs'++[v]++vs)) = SOME v_con) ∧
     (r = (s3, Rval vs)) ∧ e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ⇒
     e_step_reln^* (env,s1,Exp e,[(Ccon cn vs' () es,env)])
                   (env,s3,Val v_con,[]))`,
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
     metis_tac [APPEND_ASSOC, APPEND]]);

val small_eval_list_err = Q.prove (
`!env s2 es r. small_eval_list env s2 es r ⇒
  (!e v err_v cn vs' env' s1 s3.
     do_con_check env.c cn (LENGTH vs' + 1 + LENGTH es) ∧
     (r = (s3, Rerr (Rraise err_v))) ∧
     e_step_reln^* (env,s1,e,[]) (env',s2,Val v,[]) ⇒
     ?env'' env'''. e_step_reln^* (env,s1,e,[(Ccon cn vs' () es,env)])
                              (env'',s3,Val err_v,[(Craise (), env''')]))`,
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
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]));

val small_eval_list_terr = Q.prove (
`!env s2 es r. small_eval_list env s2 es r ⇒
  (!e v err cn vs' env' s1 s3.
     do_con_check env.c cn (LENGTH vs' + 1 + LENGTH es) ∧
     (r = (s3, Rerr (Rabort a))) ∧
     e_step_reln^* (env,s1,e,[]) (env',s2,Val v,[]) ⇒
     ?env'' e' c'. e_step_reln^* (env,s1,e,[(Ccon cn vs' () es,env)])
                                    (env'',s3,e',c') ∧
                   (e_step (env'',s3,e',c') = (Eabort a)))`,
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
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def]]);

val (small_eval_match_rules, small_eval_match_ind, small_eval_match_cases) = Hol_reln `
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
  small_eval_match env s v ((p,e)::pes) err_v (s, Rerr (Rabort Rtype_error)))`;

val alt_small_eval_def = Define `
(alt_small_eval env s1 e c (s2, Rval v) =
    ∃env'. e_step_reln^* (env,s1,e,c) (env',s2,Val v,[])) ∧
(alt_small_eval env s1 e c (s2, Rerr (Rraise err_v)) ⇔
    ∃env' env''.
      e_step_reln^* (env,s1,e,c) (env',s2,Val err_v,[(Craise (), env'')])) ∧
(alt_small_eval env s1 e c (s2, Rerr (Rabort a)) ⇔
    ∃env' e' c'.
      e_step_reln^* (env,s1,e,c) (env',s2,e',c') ∧
      (e_step (env',s2,e',c') = Eabort a))`;

val small_eval_match_thm = Q.prove (
  `!env s v pes err_v r.
    small_eval_match env s v pes err_v r ⇒
    !env2. alt_small_eval env2 s (Val v) [(Cmat () pes err_v,env)] r`,
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
      full_simp_tac(srw_ss())[]));

val result_cases = Q.prove (
`!r.
 (?s v. r = (s, Rval v)) ∨
 (?s v. r = (s, Rerr (Rraise v))) ∨
 (?s a. r = (s, Rerr (Rabort a)))`,
 cases_on `r` >>
 srw_tac[][] >>
 cases_on `r'` >>
 full_simp_tac(srw_ss())[] >>
 cases_on `e` >>
 full_simp_tac(srw_ss())[]);

val small_eval_opapp_err = Q.prove(
  `∀env s es res. small_eval_list env s es res ⇒
    ∀s' vs. res = (s',Rval vs) ⇒
      ∀env0 v1 v0. LENGTH es + LENGTH v0 ≠ 1 ⇒
        ∃env' e' c'.
        e_step_reln^* (env0,s,Val v1,[Capp Opapp v0 () es,env]) (env',s',e',c') ∧
        e_step (env',s',e',c') = Eabort Rtype_error`,
  ho_match_mp_tac small_eval_list_ind >> simp[] >> srw_tac[][] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
    srw_tac[][Once e_step_def,continue_def,application_thm] >>
    Cases_on `v0` >>
    full_simp_tac(srw_ss())[do_opapp_def] >>
    Cases_on`t`>>full_simp_tac(srw_ss())[]) >>
  disj2_tac >>
  srw_tac[][Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp Opapp (v1::v0) () es,env]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspecl_then[`env'`,`v`,`v1::v0`]mp_tac) >>
  impl_tac >- simp[] >>
  metis_tac[transitive_RTC,transitive_def] );

val small_eval_app_err = Q.prove(
  `∀env s es res. small_eval_list env s es res ⇒
    ∀s' vs. res = (s',Rval vs) ⇒
      ∀op env0 v1 v0. LENGTH es + LENGTH v0 > 2 ∧ op ≠ Opapp
        ∧ op ≠ CopyStrStr ∧ op ≠ CopyStrAw8 ∧ op ≠ CopyAw8Str ∧ op ≠ CopyAw8Aw8
        ⇒
        ∃env' e' c'.
        e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
        e_step (env',s',e',c') = Eabort Rtype_error`,
  ho_match_mp_tac small_eval_list_ind >> simp[] >> srw_tac[][] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
    srw_tac[][Once e_step_def,continue_def,application_thm] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    Cases_on`s` \\ fs[do_app_cases] \\ rw[] \\ fs[]) \\
  disj2_tac >>
  srw_tac[][Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp op (v1::v0) () es,env]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspecl_then[`op`,`env'`,`v`,`v1::v0`]mp_tac) >>
  impl_tac >- simp[] >>
  metis_tac[transitive_RTC,transitive_def] );

val small_eval_app_err_more = Q.prove(
  `∀env s es res. small_eval_list env s es res ⇒
    ∀s' vs. res = (s',Rval vs) ⇒
      ∀op env0 v1 v0. LENGTH es + LENGTH v0 > 4 ∧ op ≠ Opapp
        ⇒
        ∃env' e' c'.
        e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
        e_step (env',s',e',c') = Eabort Rtype_error`,
  ho_match_mp_tac small_eval_list_ind >> simp[] >> srw_tac[][] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
    srw_tac[][Once e_step_def,continue_def,application_thm] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    Cases_on`s` \\ fs[do_app_cases] \\ rw[] \\ fs[]) \\
  disj2_tac >>
  srw_tac[][Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp op (v1::v0) () es,env]`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspecl_then[`op`,`env'`,`v`,`v1::v0`]mp_tac) >>
  impl_tac >- simp[] >>
  metis_tac[transitive_RTC,transitive_def] );

val do_app_not_timeout = Q.prove (
`do_app s op vs = SOME (s', Rerr (Rabort a))
 ⇒
 a ≠ Rtimeout_error`,
 Cases_on `s` >>
 srw_tac[][do_app_cases] >>
 every_case_tac >>
 srw_tac[][]);

val step_e_not_timeout = Q.prove (
`e_step (env',s3,e',c') = Eabort a ⇒ a ≠ Rtimeout_error`,
  full_simp_tac(srw_ss())[e_step_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[push_def, return_def, continue_def, application_thm] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  imp_res_tac do_app_not_timeout >>
  srw_tac[][]);

val small_eval_list_not_timeout = Q.prove(
  `∀env s es res. small_eval_list env s es res ⇒
    SND res ≠ Rerr (Rabort Rtimeout_error)`,
  ho_match_mp_tac small_eval_list_ind >> srw_tac[][] >>
  metis_tac [step_e_not_timeout]);

val small_eval_list_app_type_error = Q.prove(
  `∀env s es res. small_eval_list env s es res ⇒
      ∀s' err. res = (s',Rerr (Rabort a)) ⇒
        ∀op env0 v1 v0.
          ∃env' e' c'.
            e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
            e_step (env',s',e',c') = Eabort a`,
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
  srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`])

val small_eval_list_app_error = Q.prove(
  `∀env s es res. small_eval_list env s es res ⇒
      ∀s' v. res = (s',Rerr (Rraise v)) ⇒
        ∀op env0 v1 v0.
          ∃env' env''.
            e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',Val v,[(Craise (),env'')])`,
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
  srw_tac[][Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`])


val do_opapp_NONE_tail = Q.prove(
  `do_opapp (h::t) = NONE ∧ LENGTH t ≠ 2 ⇒ do_opapp t = NONE`,
  srw_tac[][do_opapp_def] >> every_case_tac >> full_simp_tac(srw_ss())[])

val e_step_exp_err_any_ctxt = Q.prove(
  `e_step (x,y,Exp z,c1) = Eabort a ⇒ e_step (x,y,Exp z,c2) = Eabort a`,
  srw_tac[][e_step_def] >> every_case_tac >>
  full_simp_tac(srw_ss())[push_def,return_def,continue_def,application_thm] >>
  every_case_tac >> full_simp_tac(srw_ss())[] )

val do_opapp_too_many = Q.prove (
`!vs'. do_opapp (REVERSE (v''::vs') ++ [v'] ++ [v]) = NONE`,
 srw_tac[][] >>
 Induct_on `REVERSE vs'` >>
 srw_tac[][] >>
 `vs' = [] ∨ ?v vs''. vs' = vs''++[v]` by metis_tac [list_end_case] >>
 full_simp_tac(srw_ss())[do_opapp_def] >>
 srw_tac[][REVERSE_APPEND] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[]);

val do_app_type_error = Q.prove(
  `do_app s op es = SOME (x,Rerr (Rabort a)) ⇒ x = s`,
  PairCases_on `s` >>
  srw_tac[][do_app_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[LET_THM,UNCURRY] >>
  every_case_tac >> full_simp_tac(srw_ss())[])

val to_small_st_def = Define `
to_small_st s = (s.refs,s.ffi)`;

val to_small_res_def = Define `
to_small_res r = (to_small_st (FST r), SND r)`;

val s = ``s:'ffi state``;

val big_exp_to_small_exp = Q.prove (
  `(∀ck env ^s e r.
     evaluate ck env s e r ⇒
     (ck = F) ⇒ small_eval env (to_small_st s) e [] (to_small_res r)) ∧
   (∀ck env ^s es r.
     evaluate_list ck env s es r ⇒
     (ck = F) ⇒ small_eval_list env (to_small_st s) es (to_small_res r)) ∧
   (∀ck env ^s v pes err_v r.
     evaluate_match ck env s v pes err_v r ⇒
     (ck = F) ⇒ small_eval_match env (to_small_st s) v pes err_v (to_small_res r))`,
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
       `e_step_reln^* (env,to_small_st s,Exp e,[(Chandle () pes,env)]) (env',to_small_st s',Val v,[(Craise (),env'');(Chandle () pes,env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s',Val v,[(Craise (),env'');(Chandle () pes,env)]) (env'',to_small_st s',Val v,[(Cmat () pes v, env)])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
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
                   (*
   >- (full_simp_tac(srw_ss())[small_eval_def] >>
       `e_step_reln^* (env,SND s,Exp e,[(Chandle () pes,env)]) (env',SND s',Exp (Raise (Int_error n)),[(Chandle () pes,env)])`
                   by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',SND s',Exp (Raise (Int_error n)),[(Chandle () pes,env)])
                    (menv,cenv,SND s',(bind var (Litv (IntLit n)) env),Exp e',[])`
                   by (srw_tac[][e_step_reln_def, e_step_def, continue_def, return_def]) >>
       metis_tac [RTC_SINGLE, small_eval_prefix])
       *)
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
       metis_tac [transitive_def, transitive_RTC, e_step_add_ctxt, APPEND])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Cmat () pes (Conv (SOME bind_stamp) []),env)]) (to_small_st s', Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   srw_tac[][]) >>
       full_simp_tac(srw_ss())[])
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
   >- metis_tac [small_eval_match_rules]);

val evaluate_ctxts_cons = Q.prove (
`!s1 f cs res1 bv.
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
     evaluate_match F env s1 v pes v (s2, res2) ∧
     evaluate_ctxts s2 cs res2 bv))`,
srw_tac[][] >>
srw_tac[][Once evaluate_ctxts_cases] >>
EQ_TAC >>
srw_tac[][] >>
metis_tac []);

val tac1 =
full_simp_tac(srw_ss())[evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_ctxts_cases, evaluate_ctxt_cases] >>
srw_tac[][] >>
metis_tac [oneTheory.one]

val tac3 =
full_simp_tac(srw_ss())[evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
srw_tac[][] >>
full_simp_tac(srw_ss())[evaluate_ctxts_cons, evaluate_ctxt_cases] >>
ONCE_REWRITE_TAC [hd (tl (CONJUNCTS evaluate_cases))] >>
srw_tac[][] >>
full_simp_tac(srw_ss())[evaluate_ctxts_cons, evaluate_ctxt_cases] >>
srw_tac [boolSimps.DNF_ss] [] >>
metis_tac [DECIDE ``SUC x = x + 1``, pair_CASES, REVERSE_APPEND]

val evaluate_state_app_cons = Q.prove(
  `evaluate_state (env,s,Exp e,(Capp op [] () es,env)::c) bv
    ⇒ evaluate_state (env,s,Exp (App op (REVERSE es++[e])),c) bv`,
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
  srw_tac[][Once evaluate_cases]);

val one_step_backward = Q.prove (
`!env s e c s' env' e' c' bv.
  (e_step (env,s,e,c) = Estep (env',s',e',c')) ∧
  evaluate_state (env',s',e',c') bv
  ⇒
  evaluate_state (env,s,e,c) bv`,
 srw_tac[][e_step_def] >>
 cases_on `e` >>
 full_simp_tac(srw_ss())[]
 >- (cases_on `e''` >>
     full_simp_tac(srw_ss())[push_def, return_def] >>
     srw_tac[][]
     >- (full_simp_tac(srw_ss())[evaluate_ctxts_cons, evaluate_state_cases, evaluate_ctxt_cases] >>
         srw_tac[][Once evaluate_cases] >>
         metis_tac [])
     >- (full_simp_tac(srw_ss())[evaluate_ctxts_cons, evaluate_state_cases, evaluate_ctxt_cases] >>
         srw_tac[][Once evaluate_cases]
         >- metis_tac []
         >- (cases_on `err` >>
               full_simp_tac(srw_ss())[] >-
               metis_tac [] >>
               TRY (cases_on `e'`) >>
               full_simp_tac(srw_ss())[] >>
               metis_tac [])
         >- metis_tac [])
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
     metis_tac [APPEND_ASSOC, APPEND, REVERSE_APPEND, REVERSE_REVERSE, REVERSE_DEF]));

val evaluate_ctxts_type_error = Q.prove (
`!a s c. evaluate_ctxts s c (Rerr (Rabort a)) (s,Rerr (Rabort a))`,
induct_on `c` >>
srw_tac[][] >>
srw_tac[][Once evaluate_ctxts_cases] >>
PairCases_on `h` >>
srw_tac[][]);

val evaluate_ctxts_type_error_matchable = Q.prove (
`!a s c. s' = s ⇒ evaluate_ctxts s c (Rerr (Rabort a)) (s',Rerr (Rabort a))`,
metis_tac[evaluate_ctxts_type_error]);

val one_step_backward_type_error = Q.prove (
  `!env s e c.
    (e_step (env,to_small_st s,e,c) = Eabort a)
    ⇒
    evaluate_state (env,to_small_st s,e,c)
      ((s with <| next_type_stamp := 0; next_exn_stamp := 0; clock := 0 |>),
       Rerr (Rabort a))`,
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
  full_simp_tac (srw_ss() ++ ARITH_ss) [arithmeticTheory.ADD1] >>
  srw_tac[][Once evaluate_cases] >>
  srw_tac[DNF_ss][] >> full_simp_tac(srw_ss())[to_small_st_def] >>
  ((match_mp_tac evaluate_ctxts_type_error_matchable >>
    srw_tac[][state_component_equality]) ORELSE
   metis_tac[do_con_check_build_conv,NOT_SOME_NONE]));

val small_exp_to_big_exp = Q.prove (
`!st st'. e_step_reln^* st st' ⇒
  !r.
    evaluate_state st' r
    ⇒
    evaluate_state st r`,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >>
srw_tac[][e_step_reln_def] >>
PairCases_on `st` >>
PairCases_on `st'` >>
PairCases_on `st''` >>
srw_tac[][] >>
metis_tac [one_step_backward]);

val evaluate_state_no_ctxt = Q.prove (
`!env s e r.
  evaluate_state (env,to_small_st s,Exp e,[]) r
  ⇔
  evaluate F env (s with <| next_type_stamp := 0; next_exn_stamp := 0; clock := 0 |>) e r`,
 srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
 srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
 full_simp_tac(srw_ss())[to_small_st_def] >>
 Cases_on`r`>>simp[]>>
 rpt AP_THM_TAC >> AP_TERM_TAC >>
 simp[state_component_equality]);

val evaluate_state_val_no_ctxt = Q.prove (
`!env s e.
  evaluate_state (env,to_small_st s,Val e,[]) r
  ⇔
  (r = (s with <| next_type_stamp := 0; next_exn_stamp := 0; clock := 0 |>, Rval e))`,
 srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
 srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
 full_simp_tac(srw_ss())[to_small_st_def] >>
 eq_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[state_component_equality]);

val evaluate_state_val_raise_ctxt = Q.prove (
`!env s v env'.
  evaluate_state (env,to_small_st s,Val v,[(Craise (), env')]) r
  ⇔
  (r = (s with <| next_type_stamp := 0; next_exn_stamp := 0; clock := 0 |>, Rerr (Rraise v)))`,
 srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
 srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
 srw_tac[][evaluate_ctxt_cases] >>
 srw_tac[][evaluate_state_cases, Once evaluate_ctxts_cases] >>
 full_simp_tac(srw_ss())[to_small_st_def] >>
 eq_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[state_component_equality]);

val evaluate_change_state = Q.prove(
  `evaluate a b c d (e,f) ∧ c = c' ∧ e = e' ⇒
   evaluate a b c' d (e',f)`,
   srw_tac[][] >> srw_tac[][]) |> GEN_ALL;

Theorem small_big_exp_equiv:
 !env s e s' r.
  (small_eval env (to_small_st s) e [] (to_small_st s',r) ∧
   s.clock = s'.clock ∧ s.next_type_stamp = s'.next_type_stamp ∧ s.next_exn_stamp= s'.next_exn_stamp)
  ⇔
  evaluate F env s e (s',r)
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
 pop_assum (qspecl_then [`env`, `<| ffi := SND s; refs := FST s; clock := 0; next_type_stamp := 0; next_exn_stamp := 0 |>`, `e`] mp_tac) >>
 simp [] >>
 strip_tac >>
 first_assum (qspec_then `<| ffi := r11; refs := r10; clock := 0; next_type_stamp := 0; next_exn_stamp := 0 |>` mp_tac) >>
 first_assum (qspec_then `<| ffi := r21; refs := r20; clock := 0; next_type_stamp := 0; next_exn_stamp := 0 |>` mp_tac) >>
 pop_assum kall_tac >>
 simp [] >>
 strip_tac >>
 strip_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 imp_res_tac big_exp_determ >>
 full_simp_tac(srw_ss())[]
QED

val _ = export_theory ();

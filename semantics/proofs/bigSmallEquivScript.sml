open preamble;
open libTheory semanticPrimitivesTheory bigStepTheory smallStepTheory;
open bigSmallInvariantsTheory evalPropsTheory determTheory bigClockTheory;

val _ = new_theory "bigSmallEquiv";

(* ------------------------ Big step/small step equivalence ----------------- *)

val list_end_case = Q.prove (
`!l. l = [] ∨ ?x l'. l = l' ++ [x]`,
 Induct_on `l` >>
 rw [] >>
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
 rw [application_def] >>
 cases_on `op` >>
 rw []);

val small_eval_prefix = Q.prove (
`∀s env e c cenv' s' env' e' c' r.
  e_step_reln^* (env,s,Exp e,c) (env',s',Exp e',c') ∧
  small_eval env' s' e' c' r
  ⇒
  small_eval env s e c r`,
 rw [] >>
 PairCases_on `r` >>
 cases_on `r3` >>
 fs [small_eval_def] >-
 metis_tac [transitive_RTC, transitive_def] >>
 cases_on `e''` >>
 TRY (Cases_on `a`) >>
 fs [small_eval_def] >>
 metis_tac [transitive_RTC, transitive_def]);

val e_single_step_add_ctxt = Q.prove (
`!s env e c s' env' e' c' c''.
  (e_step (env,s,e,c) = Estep (env',s',e',c'))
  ⇒
  (e_step (env,s,e,c++c'') = Estep (env',s',e',c'++c''))`,
 rw [e_step_def] >>
 cases_on `e` >>
 fs [push_def, return_def] >>
 rw [] >>
 fs [] >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 rw []
 >- (fs [application_thm] >>
     every_case_tac >>
     fs [return_def])
 >- (fs [continue_def] >>
     cases_on `c` >>
     fs [] >>
     cases_on `h` >>
     fs [] >>
     cases_on `q` >>
     fs [] >>
     every_case_tac >>
     fs [push_def, return_def] >>
     rw [] >>
     fs [application_thm] >>
     every_case_tac >>
     fs [return_def]));

val e_single_error_add_ctxt = Q.prove (
`!env s e c c'.
  (e_step (env,s,e,c) = Eabort a)
  ⇒
  (e_step (env,s,e,c++c') = Eabort a)`,
rw [e_step_def] >>
cases_on `e` >>
fs [push_def, return_def] >>
rw [] >>
fs [] >>
rw [] >>
every_case_tac >>
fs [] >>
rw []
 >- (fs [application_thm] >>
     every_case_tac >>
     fs [return_def])
 >- (fs [continue_def] >>
     cases_on `c` >>
     fs [] >>
     cases_on `h` >>
     fs [] >>
     cases_on `q` >>
     fs [] >>
     every_case_tac >>
     fs [push_def, return_def] >>
     rw [] >>
     fs [application_thm] >>
     every_case_tac >>
     fs [return_def]));

val e_step_add_ctxt_help = Q.prove (
`!st1 st2. e_step_reln^* st1 st2 ⇒
  !s1 env1 e1 c1 s2 env2 e2 c2 c'.
    (st1 = (env1,s1,e1,c1)) ∧ (st2 = (env2,s2,e2,c2))
    ⇒
    e_step_reln^* (env1,s1,e1,c1++c') (env2,s2,e2,c2++c')`,
HO_MATCH_MP_TAC RTC_INDUCT >>
rw [e_step_reln_def] >-
metis_tac [RTC_REFL] >>
PairCases_on `st1'` >>
fs [] >>
imp_res_tac e_single_step_add_ctxt >>
fs [] >>
rw [Once RTC_CASES1] >>
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
rw [] >>
rw [Once RTC_CASES1] >>
cases_on `c` >>
fs [] >>
rw [e_step_reln_def, e_step_def, continue_def] >>
every_case_tac >>
fs [] >>
cases_on `o'` >>
fs []);

val small_eval_err_add_ctxt = Q.prove (
`!s env e c err c' s'.
  EVERY (\c. ¬?pes env. c = (Chandle () pes, env)) c'
  ⇒
  small_eval env s e c (s', Rerr err) ⇒ small_eval env s e (c++c') (s', Rerr err)`,
 rw [] >>
 `?a. err = Rabort a ∨ ?v. err = Rraise v` 
          by (cases_on `err` >> rw []) >>
 rw [] >>
 fs [small_eval_def]
 >- (Cases_on `a` >>
     fs [small_eval_def] >>
     `e_step_reln^* (env,s,Exp e,c++c') (env',s',e',c''++c')`
            by metis_tac [e_step_add_ctxt] >>
     metis_tac [e_single_error_add_ctxt])
 >- (`e_step_reln^* (env,s,Exp e,c++c') (env',s',Val v,(Craise (),env'')::c')`
            by metis_tac [e_step_add_ctxt, APPEND] >>
     cases_on `c'` >>
     fs [] >-
     metis_tac [] >>
     `e_step_reln^* (env',s',Val v,(Craise (),env'')::h::t) (env'',s',Val v,[(Craise (),env'')])`
            by (match_mp_tac e_step_raise >> rw []) >>
     metis_tac [transitive_RTC, transitive_def]))

val small_eval_err_add_ctxt =
SIMP_RULE (srw_ss ()) 
   [METIS_PROVE [] ``!x y z. (x ⇒ y ⇒ z) = (x ∧ y ⇒ z)``]
   small_eval_err_add_ctxt;

val small_eval_step_tac =
rw [do_con_check_def] >>
every_case_tac >>
fs [] >>
PairCases_on `r` >>
cases_on `r3` >|
[all_tac,
 cases_on `e`] >>
rw [small_eval_def] >>
EQ_TAC >>
rw [] >|
[pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     fs [return_def, e_step_reln_def, e_step_def, push_def, do_con_check_def] >>
     every_case_tac >>
     fs [] >>
     metis_tac [pair_CASES],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, e_step_def, push_def,REVERSE_APPEND,
     do_con_check_def] >>
     metis_tac [],
 pop_assum (ASSUME_TAC o SIMP_RULE (srw_ss()) [Once RTC_CASES1]) >>
     fs [e_step_reln_def, e_step_def, push_def, return_def, do_con_check_def] >>
     every_case_tac >>
     fs [] >>
     metis_tac [],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def,
     do_con_check_def] >>
     fs [REVERSE_APPEND] >>
     metis_tac [],
 qpat_assum `e_step_reln^* spat1 spat2`
             (ASSUME_TAC o
              SIMP_RULE (srw_ss()) [Once RTC_CASES1,e_step_reln_def,
                                    e_step_def, push_def]) >>
     fs [] >>
     every_case_tac >>
     fs [return_def, do_con_check_def] >>
     rw [] >-
     (fs [e_step_def, push_def] >>
      pop_assum MP_TAC >>
      rw [return_def, do_con_check_def, REVERSE_APPEND]) >>
     fs [] >>
     metis_tac [],
 rw [return_def, Once RTC_CASES1, e_step_reln_def, Once e_step_def, push_def,
     do_con_check_def] >>
     fs [REVERSE_APPEND] >>
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
 rw [do_con_check_def] >>
 every_case_tac >>
 fs [] >>
 small_eval_step_tac);

val small_eval_app = Q.prove (
`!env s op es c r.
  small_eval env s (App op es) c r ⇔
  (es = [] ∧ small_eval env s (App op []) c r) ∨
  (?e es'. (es = es'++[e]) ∧ small_eval env s e ((Capp op [] () (REVERSE es'),env)::c) r)`,
 rw [] >>
 `es = [] ∨ ?e es'. es = es' ++ [e]` by metis_tac [list_end_case] >>
 rw [] >>
 `(?s' v. r = (s', Rval v)) ∨ (?s' a. r = (s', Rerr (Rabort a))) ∨
  (?s' err. r = (s', Rerr (Rraise err)))`
              by metis_tac [pair_CASES, result_nchotomy, error_result_nchotomy] >>
 TRY (cases_on `a`) >>
 fs [small_eval_def] >>
 rw [Once RTC_CASES1, e_step_reln_def, e_step_def] >>
 rw [push_def, application_thm] >>
 EQ_TAC >>
 rw [] >>
 fs [REVERSE_APPEND] >>
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
  small_eval env s e1 ((Cmat () pes (Conv (SOME ("Bind", TypeExn (Short "Bind"))) []),env)::c) r`,
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
rw [] >>
rw []);

val small_eval_list_step = Q.prove (
`!env s2 es r. small_eval_list env s2 es r ⇒
  (!e v vs cn vs' env' s1 s3 v_con.
     do_con_check env.c cn (LENGTH vs' + 1 + LENGTH vs) ∧
     (build_conv env.c cn (REVERSE (REVERSE vs'++[v]++vs)) = SOME v_con) ∧
     (r = (s3, Rval vs)) ∧ e_step_reln^* (env,s1,Exp e,[]) (env',s2,Val v,[]) ⇒
     e_step_reln^* (env,s1,Exp e,[(Ccon cn vs' () es,env)])
                   (env,s3,Val v_con,[]))`,
HO_MATCH_MP_TAC (fetch "-" "small_eval_list_strongind") >>
rw [] >|
[`e_step_reln^* (env,s1,Exp e,[(Ccon cn vs' () [],env)])
                (env',s2,Val v,[(Ccon cn vs' () [],env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step_reln (env',s2,Val v,[(Ccon cn vs' () [],env)])
                  (env,s2,Val v_con,[])`
             by rw [return_def, continue_def, e_step_reln_def, e_step_def] >>
     fs [REVERSE_APPEND] >>
     metis_tac [transitive_RTC, transitive_def, RTC_SINGLE, APPEND],
 `LENGTH (v'::vs'') + 1 + LENGTH vs = LENGTH vs'' + 1 + SUC (LENGTH vs)`
              by (fs [] >>
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
             by (rw [push_def,continue_def, e_step_reln_def, e_step_def] >>
                 full_simp_tac (srw_ss() ++ ARITH_ss) [arithmeticTheory.ADD1]) >>
     fs [] >>
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
 rw [] >>
 `e_step_reln^* (env,s1,e',[(Ccon cn vs' () (e::es),env)])
                (env''',s2,Val v',[(Ccon cn vs' () (e::es),env)])`
              by metis_tac [e_step_add_ctxt, APPEND] >>
 `e_step_reln (env''',s2,Val v',[(Ccon cn vs' () (e::es),env)])
              (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])`
         by rw [push_def,continue_def, e_step_reln_def, e_step_def] >>
 `LENGTH vs' + 1 + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
                 by DECIDE_TAC >>
 fs []
 >- (`e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
                    (env',s3,Val err_v,[(Craise (), env'');(Ccon cn (v'::vs') () es,env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step_reln^* (env',s3,Val err_v,[(Craise (), env'');(Ccon cn (v'::vs') () es,env)])
                    (env'',s3,Val err_v,[(Craise (), env'')])`
             by (match_mp_tac e_step_raise >>
                 rw []) >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def])
 >- (`LENGTH (v'::vs') + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
              by (fs [] >>
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
rw [] >>
`e_step_reln^* (env,s1,e'',[(Ccon cn vs' () (e::es),env)])
               (env'',s2,Val v',[(Ccon cn vs' () (e::es),env)])`
             by metis_tac [e_step_add_ctxt, APPEND] >>
`e_step_reln (env'',s2,Val v',[(Ccon cn vs' () (e::es),env)])
             (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])`
        by rw [push_def,continue_def, e_step_reln_def, e_step_def] >>
`LENGTH vs' + 1 + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
                by DECIDE_TAC >>
fs [] >|
[`e_step_reln^* (env,s2,Exp e,[(Ccon cn (v'::vs') () es,env)])
                (env',s3,e',c'++[(Ccon cn (v'::vs') () es,env)])`
             by metis_tac [e_step_add_ctxt,APPEND] >>
     `e_step (env',s3,e',c'++[(Ccon cn (v'::vs') () es,env)]) = Eabort a`
             by metis_tac [e_single_error_add_ctxt] >>
     metis_tac [RTC_SINGLE, transitive_RTC, transitive_def],
 `LENGTH (v'::vs') + 1 + LENGTH es = LENGTH vs' + 1 + SUC (LENGTH es)`
              by (fs [] >>
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
  pmatch env.c (FST s) p v env.v = Match env' ∧
  small_eval (env with v := env') s e [] r
  ⇒
  small_eval_match env s v ((p,e)::pes) err_v r) ∧
(!env s e p pes r v err_v.
  ALL_DISTINCT (pat_bindings p []) ∧
  (pmatch env.c (FST s) p v env.v = No_match) ∧
  small_eval_match env s v pes err_v r
  ⇒
  small_eval_match env s v ((p,e)::pes) err_v r) ∧
(!env s p e pes v err_v.
  ¬(ALL_DISTINCT (pat_bindings p []))
  ⇒
  small_eval_match env s v ((p,e)::pes) err_v (s, Rerr (Rabort Rtype_error))) ∧
(!env s p e pes v err_v.
  (pmatch env.c (FST s) p v env.v = Match_type_error)
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
  rw [alt_small_eval_def]
  >- (qexists_tac `env` >>
      qexists_tac `env` >>
      match_mp_tac RTC_SINGLE >>
      rw [e_step_reln_def, e_step_def, continue_def])
  >- (PairCases_on `r` >>
      cases_on `r3` >|
      [all_tac,
       cases_on `e'`] >>
      fs [alt_small_eval_def, small_eval_def]
      >- (rw [Once RTC_CASES1, e_step_reln_def] >>
          rw [e_step_def, continue_def] >>
          metis_tac[])
      >- (rw [Once RTC_CASES1, e_step_reln_def] >>
          rw [e_step_def, continue_def] >>
          metis_tac []) >>
      rw [] >>
      rw [Once RTC_CASES1, e_step_reln_def] >>
      qexists_tac `env''` >>
      qexists_tac `e'` >>
      qexists_tac `c'` >>
      rw [] >>
      rw [e_step_def, continue_def])
  >- (PairCases_on `r` >>
      cases_on `r3` >|
      [all_tac,
       cases_on `e'`] >>
      fs [alt_small_eval_def] >>
      rw [Once RTC_CASES1, e_step_reln_def] >> fs [] >|
      [rw [e_step_def, push_def, continue_def] >>
           metis_tac [],
       rw [e_step_def, push_def, continue_def] >>
           metis_tac [],
       rw [] >>
           pop_assum (qspec_then`env`strip_assume_tac) >>
           qexists_tac `env'` >>
           qexists_tac `e'` >>
           qexists_tac `c'` >>
           rw [] >>
           rw [e_step_def, push_def, continue_def]])
  >- (qexists_tac `env2` >>
      qexists_tac `Val v` >>
      qexists_tac `[(Cmat () ((p,e)::pes) err_v,env)]` >>
      rw [RTC_REFL] >>
      rw [e_step_def, continue_def] >>
      PairCases_on `env` >>
      fs [] >>
      metis_tac [])
  >- (qexists_tac `env2` >>
      qexists_tac `Val v` >>
      qexists_tac `[(Cmat () ((p,e)::pes) err_v,env)]` >>
      rw [RTC_REFL] >>
      rw [e_step_def, continue_def] >>
      PairCases_on `env` >>
      fs []));

val result_cases = Q.prove (
`!r.
 (?s v. r = (s, Rval v)) ∨
 (?s v. r = (s, Rerr (Rraise v))) ∨
 (?s a. r = (s, Rerr (Rabort a)))`,
 cases_on `r` >>
 rw [] >>
 cases_on `r'` >>
 fs [] >>
 cases_on `e` >>
 fs []);

val small_eval_opapp_err = prove(
  ``∀env s es res. small_eval_list env s es res ⇒
    ∀s' vs. res = (s',Rval vs) ⇒
      ∀env0 v1 v0. LENGTH es + LENGTH v0 ≠ 1 ⇒
        ∃env' e' c'.
        e_step_reln^* (env0,s,Val v1,[Capp Opapp v0 () es,env]) (env',s',e',c') ∧
        e_step (env',s',e',c') = Eabort Rtype_error``,
  ho_match_mp_tac small_eval_list_ind >> simp[] >> rw[] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
    rw[Once e_step_def,continue_def,application_thm] >>
    Cases_on `v0` >>
    fs [do_opapp_def] >>
    Cases_on`t`>>fs[]) >>
  disj2_tac >>
  rw[Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp Opapp (v1::v0) () es,env]`strip_assume_tac) >> fs[] >>
  first_x_assum(qspecl_then[`env'`,`v`,`v1::v0`]mp_tac) >>
  discharge_hyps >- simp[] >>
  metis_tac[transitive_RTC,transitive_def] );

val small_eval_app_err = prove(
  ``∀env s es res. small_eval_list env s es res ⇒
    ∀s' vs. res = (s',Rval vs) ⇒
      ∀op env0 v1 v0. LENGTH es + LENGTH v0 > 2 ∧ op ≠ Opapp ⇒
        ∃env' e' c'.
        e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
        e_step (env',s',e',c') = Eabort Rtype_error``,
  ho_match_mp_tac small_eval_list_ind >> simp[] >> rw[] >>
  srw_tac[boolSimps.DNF_ss][Once RTC_CASES1,e_step_reln_def] >- (
    rw[Once e_step_def,continue_def,application_thm] >>
    BasicProvers.CASE_TAC >>
    Cases_on`op`>>
    Cases_on`v0`>>Cases_on `s` >>fs[do_app_def] >>
    every_case_tac >> fs[]) >>
  disj2_tac >>
  rw[Once e_step_def,continue_def,push_def] >>
  imp_res_tac e_step_add_ctxt >>
  pop_assum(qspec_then`[Capp op (v1::v0) () es,env]`strip_assume_tac) >> fs[] >>
  first_x_assum(qspecl_then[`op`,`env'`,`v`,`v1::v0`]mp_tac) >>
  discharge_hyps >- simp[] >>
  metis_tac[transitive_RTC,transitive_def] );

val do_app_not_timeout = Q.prove (
`do_app s op vs = SOME (s', Rerr (Rabort a))
 ⇒
 a ≠ Rtimeout_error`,
 Cases_on `s` >>
 rw [do_app_cases] >>
 every_case_tac >>
 rw []);

val step_e_not_timeout = Q.prove (
`e_step (env',s3,e',c') = Eabort a ⇒ a ≠ Rtimeout_error`,
  fs [e_step_def] >>
  every_case_tac >>
  fs [push_def, return_def, continue_def, application_thm] >>
  rw [] >>
  every_case_tac >>
  fs [] >>
  rw [] >>
  imp_res_tac do_app_not_timeout >>
  rw []);

val small_eval_list_not_timeout = prove(
  ``∀env s es res. small_eval_list env s es res ⇒
    SND res ≠ Rerr (Rabort Rtimeout_error)``,
  ho_match_mp_tac small_eval_list_ind >> rw[] >>
  metis_tac [step_e_not_timeout]);

val small_eval_list_app_type_error = prove(
  ``∀env s es res. small_eval_list env s es res ⇒
      ∀s' err. res = (s',Rerr (Rabort a)) ⇒
        ∀op env0 v1 v0.
          ∃env' e' c'.
            e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',e',c') ∧
            e_step (env',s',e',c') = Eabort a``,
  ho_match_mp_tac (theorem"small_eval_list_strongind") >> simp[] >> rw[] >- (
    rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
    srw_tac[boolSimps.DNF_ss][] >> disj2_tac >>
    imp_res_tac e_step_add_ctxt >>
    Q.PAT_ABBREV_TAC`ctx = [(Capp A B C D,env)]` >>
    first_x_assum(qspec_then`ctx`strip_assume_tac) >> fs[] >>
    first_assum(match_exists_tac o concl) >> rw[] >>
    metis_tac[e_single_error_add_ctxt] ) >>
  rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
  srw_tac[boolSimps.DNF_ss][] >> disj2_tac >>
  rw[Once RTC_CASES_RTC_TWICE] >>
  imp_res_tac e_step_add_ctxt >>
  Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
  first_x_assum(qspec_then`ctx`strip_assume_tac) >> fs[] >>
  simp[PULL_EXISTS] >>
  first_assum(match_exists_tac o concl) >> rw[] >>
  rw[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`])

val small_eval_list_app_error = prove(
  ``∀env s es res. small_eval_list env s es res ⇒
      ∀s' v. res = (s',Rerr (Rraise v)) ⇒
        ∀op env0 v1 v0.
          ∃env' env''.
            e_step_reln^* (env0,s,Val v1,[Capp op v0 () es,env]) (env',s',Val v,[(Craise (),env'')])``,
  ho_match_mp_tac (theorem"small_eval_list_strongind") >> simp[] >> rw[] >- (
    rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
    imp_res_tac e_step_add_ctxt >>
    Q.PAT_ABBREV_TAC`ctx = [(Capp A B C D,env)]` >>
    first_x_assum(qspec_then`ctx`strip_assume_tac) >> fs[] >>
    rw[Once RTC_CASES_RTC_TWICE] >>
    first_assum(match_exists_tac o concl) >> rw[] >>
    rw[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
    metis_tac[RTC_REFL]) >>
  rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,push_def] >>
  rw[Once RTC_CASES_RTC_TWICE] >>
  imp_res_tac e_step_add_ctxt >>
  Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
  first_x_assum(qspec_then`ctx`strip_assume_tac) >> fs[] >>
  first_assum(match_exists_tac o concl) >> rw[] >>
  rw[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`])


val do_opapp_NONE_tail = prove(
  ``do_opapp (h::t) = NONE ∧ LENGTH t ≠ 2 ⇒ do_opapp t = NONE``,
  rw[do_opapp_def] >> every_case_tac >> fs[])

val e_step_exp_err_any_ctxt = prove(
  ``e_step (x,y,Exp z,c1) = Eabort a ⇒ e_step (x,y,Exp z,c2) = Eabort a``,
  rw[e_step_def] >> every_case_tac >>
  fs[push_def,return_def,continue_def,application_thm] >>
  every_case_tac >> fs[] )

val do_opapp_too_many = Q.prove (
`!vs'. do_opapp (REVERSE (v''::vs') ++ [v'] ++ [v]) = NONE`,
 rw [] >>
 Induct_on `REVERSE vs'` >>
 rw [] >>
 `vs' = [] ∨ ?v vs''. vs' = vs''++[v]` by metis_tac [list_end_case] >>
 fs [do_opapp_def] >>
 rw [REVERSE_APPEND] >>
 every_case_tac >>
 fs []);

val do_app_type_error = prove(
  ``do_app s op es = SOME (x,Rerr (Rabort a)) ⇒ x = s``,
  PairCases_on `s` >>
  rw[do_app_def] >>
  every_case_tac >> fs[LET_THM,UNCURRY] >>
  every_case_tac >> fs[])

val to_small_st_def = Define `
to_small_st s = (s.refs,s.ffi)`;

val to_small_res_def = Define `
to_small_res r = (to_small_st (FST r), SND r)`;

val s = ``s:'ffi state``

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
   rw [small_eval_log, small_eval_if, small_eval_match,
       small_eval_handle, small_eval_let, small_eval_letrec,
       to_small_res_def, small_eval_raise]
   >- (rw [return_def, small_eval_def, Once RTC_CASES1, e_step_reln_def, e_step_def] >>
       metis_tac [RTC_REFL])
   >- (fs [small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Craise (),env)]) (to_small_st s2, Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   rw []) >>
       fs [])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Chandle () pes,env)]) (env',to_small_st s2,Val v,[(Chandle () pes,env)])`
                   by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s2,Val v,[(Chandle () pes,env)]) (env,to_small_st s2,Val v,[])`
                   by (rw [e_step_reln_def, e_step_def, continue_def, return_def]) >>
       metis_tac [transitive_def, transitive_RTC, RTC_SINGLE])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Chandle () pes,env)]) (env',to_small_st s',Val v,[(Craise (),env'');(Chandle () pes,env)])`
                  by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',to_small_st s',Val v,[(Craise (),env'');(Chandle () pes,env)]) (env'',to_small_st s',Val v,[(Cmat () pes v, env)])`
                   by (rw [e_step_reln_def, e_step_def, continue_def, return_def]) >>
       imp_res_tac small_eval_match_thm >>
       Q.ISPEC_THEN`r`assume_tac result_cases >>
       rw [] >>
       fs [small_eval_def, alt_small_eval_def] >>
       metis_tac [transitive_def, transitive_RTC, RTC_SINGLE])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Chandle () pes,env)]) (env',to_small_st s2,e',c'++[(Chandle () pes,env)])` 
                  by metis_tac [APPEND,e_step_add_ctxt] >>
        metis_tac [APPEND, e_step_add_ctxt, transitive_RTC,
                   transitive_def, e_single_error_add_ctxt])
                   (*
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,SND s,Exp e,[(Chandle () pes,env)]) (env',SND s',Exp (Raise (Int_error n)),[(Chandle () pes,env)])`
                   by metis_tac [APPEND,e_step_add_ctxt] >>
       `e_step_reln (env',SND s',Exp (Raise (Int_error n)),[(Chandle () pes,env)]) 
                    (menv,cenv,SND s',(bind var (Litv (IntLit n)) env),Exp e',[])`
                   by (rw [e_step_reln_def, e_step_def, continue_def, return_def]) >>
       metis_tac [RTC_SINGLE, small_eval_prefix])
       *)
   >- (`es = [] ∨ ?e es'. es = es' ++ [e]` by metis_tac [list_end_case] >>
       fs [LENGTH] >>
       rw [small_eval_con] >|
       [rw [small_eval_def] >>
            fs [Once small_eval_list_cases] >>
            rw [return_def, small_eval_def, Once RTC_CASES1, e_step_reln_def, e_step_def] >>
            metis_tac [RTC_REFL],
        fs [Once small_eval_list_cases] >>
            rw [small_eval_def] >>
            qexists_tac `env` >>
            match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] small_eval_list_step) >>
            MAP_EVERY qexists_tac [`s2`, `v'`, `vs'`, `env'`] >>
            rw [] >>
            fs [] >>
            imp_res_tac small_eval_list_length >>
            fs [] >>
            metis_tac [arithmeticTheory.ADD_COMM]])
   >- (rw [small_eval_def, e_step_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Con cn es)` >>
       rw [] >>
       metis_tac [RTC_REFL])
   >- (`es = [] ∨ ?e es'. es = es' ++ [e]` by metis_tac [list_end_case] >>
       rw [small_eval_con] >>
       fs [Once small_eval_list_cases] >>
       rw [small_eval_def] >|
       [`e_step_reln^* (env,to_small_st s,Exp e,[(Ccon cn [] () (REVERSE es'),env)]) 
                       (env',to_small_st s',Val err_v,[(Craise (), env'');(Ccon cn [] () (REVERSE es'),env)])`
                   by metis_tac [APPEND,e_step_add_ctxt] >>
            `e_step_reln (env',to_small_st s',Val err_v,[(Craise (), env'');(Ccon cn [] () (REVERSE es'),env)]) 
                         (env'',to_small_st s',Val err_v,[(Craise (), env'')])`
                   by (rw [e_step_reln_def, e_step_def, continue_def, return_def]) >>
            metis_tac [transitive_def, transitive_RTC, RTC_SINGLE],
        `LENGTH ([]:v list) + 1 + LENGTH es' = SUC (LENGTH es')` by
                   (fs [] >>
                    DECIDE_TAC) >>
            metis_tac [small_eval_list_err, LENGTH_REVERSE, arithmeticTheory.ADD1],
        metis_tac [APPEND, e_step_add_ctxt, transitive_RTC, transitive_def, e_single_error_add_ctxt],
        `LENGTH ([]:v list) + 1 + LENGTH es' = SUC (LENGTH es')` by
                   (fs [] >>
                    DECIDE_TAC) >>
            metis_tac [small_eval_list_terr, arithmeticTheory.ADD1, LENGTH_REVERSE]])
   >- (rw [small_eval_def] >>
       qexists_tac `env` >>
       rw [Once RTC_CASES1, e_step_reln_def, return_def, e_step_def])
   >- (rw [small_eval_def, e_step_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Var n)` >>
       rw [] >>
       metis_tac [RTC_REFL])
   >- (rw [small_eval_def] >>
       qexists_tac `env` >>
       rw [Once RTC_CASES1, e_step_reln_def, return_def, e_step_def])
   >- (
     fs[Once small_eval_list_cases] >> rw[] >- fs[do_opapp_def] >>
     fs[Once small_eval_list_cases] >> rw[] >- fs[do_opapp_def] >>
     reverse(fs[Once small_eval_list_cases, SWAP_REVERSE_SYM]) >> rw[] 
     >- metis_tac [do_opapp_too_many, NOT_SOME_NONE] >> 
     rw[Once small_eval_app] >>
     match_mp_tac small_eval_prefix >>
     Q.PAT_ABBREV_TAC`ctx = (Capp B X Y Z,env)` >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[ctx]`strip_assume_tac) >> fs[] >>
     qabbrev_tac`ctx2 = (Capp Opapp [v] () [],env)` >>
     `e_step_reln^* (env'',s2',Val v,[ctx]) (env,s2',Exp e'',[ctx2])` by (
       simp[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] ) >>
     last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[ctx2]`strip_assume_tac) >> fs[] >>
     qmatch_assum_abbrev_tac`e_step_reln^* b c` >>
     qmatch_assum_abbrev_tac`e_step_reln^* a b` >>
     `e_step_reln^* a c` by metis_tac[transitive_RTC, transitive_def] >>
     qpat_assum`X b c`kall_tac >>
     qpat_assum`X a b`kall_tac >>
     qunabbrev_tac`b` >>
     ONCE_REWRITE_TAC[CONJ_COMM] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     qmatch_assum_abbrev_tac`e_step_reln^* d a` >>
     qmatch_abbrev_tac`e_step_reln^* d f` >>
     qsuff_tac`e_step_reln^* c f` >- metis_tac[transitive_RTC,transitive_def] >>
     unabbrev_all_tac >>
     simp[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,application_thm] )
   >- (
     fs[] >>
     rw[small_eval_def] >>
     rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,
        application_thm,do_opapp_def] >>
     srw_tac[boolSimps.DNF_ss][] >>
     rw[Once e_step_def,application_thm,do_opapp_def] >>
     BasicProvers.CASE_TAC >- fs[Once small_eval_list_cases] >>
     disj2_tac >>
     rw[push_def] >>
     fs[Once small_eval_list_cases] >>
     first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[(Capp Opapp [] () t,env)]`strip_assume_tac) >>
     fs[] >> rw[] >>
     Cases_on`LENGTH t = 1` >- (
       Cases_on`t`>>fs[LENGTH_NIL]>>rw[]>>
       fs[Once small_eval_list_cases] >> rw[] >>
       fs[Once small_eval_list_cases] >> rw[] >>
       qmatch_assum_abbrev_tac`e_step_reln^* a b` >>
       qpat_assum`e_step_reln^* a b`mp_tac >>
       first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`[Capp Opapp [v] () [],env]`strip_assume_tac) >> fs[] >>
       qmatch_assum_abbrev_tac`e_step_reln^* c d` >>
       `e_step_reln^* b c` by (
         rw[Once RTC_CASES1,Abbr`b`,e_step_reln_def,e_step_def] >>
         rw[continue_def,push_def] ) >>
       strip_tac >>
       `e_step_reln^* a d` by metis_tac[transitive_RTC,transitive_def] >>
       qunabbrev_tac`d` >>
       first_assum(match_exists_tac o concl) >>
       simp[e_step_def,continue_def,application_thm] ) >>
     imp_res_tac small_eval_opapp_err >> fs[] >>
     first_x_assum(qspec_then`[]`mp_tac) >> simp[] >>
     disch_then(qspecl_then[`v`,`env'`]strip_assume_tac) >>
     metis_tac[transitive_RTC,transitive_def])
   >- (
     fs[SWAP_REVERSE_SYM, Once small_eval_list_cases] >> rw[] >- fs[do_app_def] >>
     rw[Once small_eval_app] >>
     fs[Once small_eval_list_cases] >> rw[] >- (
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
       Cases_on`res`>> TRY(Cases_on`e'`) >>
       rw[small_eval_def] >>
       TRY (
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES2] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
         simp[application_thm,do_app_def,store_alloc_def,return_def,to_small_st_def] ) >>
       `(refs',ffi') = (s2.refs,s2.ffi)` by (
         imp_res_tac do_app_type_error ) >> fs[] >>
       fs[to_small_st_def] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[Once e_step_def,continue_def,Abbr`ctx`,application_thm]) >>
     fs[Once small_eval_list_cases] >> rw[] >- (
       rw[small_eval_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
       Cases_on`res`>> TRY(Cases_on`e''`) >>
       rw[small_eval_def] >>
       TRY (
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] >>
         Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
         last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
         disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES2] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,application_thm,return_def,to_small_st_def] ) >>
       `(refs',ffi') = (s2.refs,s2.ffi)` by (
         imp_res_tac do_app_type_error ) >> fs[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
       simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] >>
       simp[Once e_step_def,continue_def,push_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
       fs[to_small_st_def] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[e_step_def,continue_def,Abbr`ctx`,application_thm]) >>
     fs[Once small_eval_list_cases] >> rw[] >- (
       rw[small_eval_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
       Cases_on`res`>> TRY(Cases_on`e'''`) >>
       rw[small_eval_def] >>
       TRY (
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] >>
         Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
         last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
         disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,push_def] >>
         Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
         last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
         disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
         simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES2] >>
         first_assum(match_exists_tac o concl) >> simp[] >>
         simp[e_step_reln_def,e_step_def,continue_def,Abbr`ctx`,application_thm,return_def,to_small_st_def] ) >>
       `(refs',ffi') = (s2.refs,s2.ffi)` by (
         imp_res_tac do_app_type_error ) >> fs[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
       simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] >>
       simp[Once e_step_def,continue_def,push_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp_tac(srw_ss()++boolSimps.DNF_ss)[Once RTC_CASES1] >>
       simp[e_step_reln_def,Once e_step_def,continue_def,Abbr`ctx`,push_def] >>
       simp[Once e_step_def,continue_def,push_def] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp A X Y Z,env)]` >>
       last_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
       disch_then(qspec_then`ctx`strip_assume_tac) >> fs[] >>
       fs[to_small_st_def] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[e_step_def,continue_def,Abbr`ctx`,application_thm]) >>
     fs[do_app_cases] >> rw[] >> fs[])
   >- (
     fs[] >>
     rw[small_eval_def] >>
     rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,application_thm,do_app_def] >>
     srw_tac[boolSimps.DNF_ss][] >>
     rw[Once e_step_def,application_thm,do_app_def] >>
     Cases_on`REVERSE es` >- (
       fs[Once small_eval_list_cases,to_small_st_def] >> rfs[] ) >>
     disj2_tac >>
     rw[push_def] >>
     fs[Once small_eval_list_cases, SWAP_REVERSE_SYM] >>
     first_x_assum(mp_tac o MATCH_MP e_step_add_ctxt) >>
     disch_then(qspec_then`[(Capp op [] () t,env)]`strip_assume_tac) >>
     fs[] >> rw[] >>
     Cases_on`vs'` >- (
       fs[Once small_eval_list_cases] >> rw[] >>
       srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >>
       rw[e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       rw[e_step_def,continue_def,application_thm,to_small_st_def] ) >>
     Cases_on`t'` >- (
       fs[Once small_eval_list_cases] >> rw[] >>
       fs[Once small_eval_list_cases] >> rw[] >>
       srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >>
       rw[e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       srw_tac[boolSimps.DNF_ss][push_def] >> disj2_tac >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp op X Y Z,env)]` >>
       last_x_assum(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) >> fs[] >>
       first_assum(match_exists_tac o concl) >>
       rw[e_step_def,continue_def,Abbr`ctx`,application_thm,to_small_st_def] ) >>
     Cases_on`t''` >- (
       fs[Once small_eval_list_cases] >> rw[] >>
       fs[Once small_eval_list_cases] >> rw[] >>
       fs[Once small_eval_list_cases] >> rw[] >>
       srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >>
       rw[e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,continue_def,application_thm] >>
       srw_tac[boolSimps.DNF_ss][push_def] >> disj2_tac >>
       srw_tac[boolSimps.DNF_ss][Once RTC_CASES_RTC_TWICE] >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp op X Y Z,env)]` >>
       qpat_assum`e_step_reln^* (env,X,Exp e,[]) Y`(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) >> fs[] >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       rw[Once RTC_CASES1,e_step_reln_def,Once e_step_def,Abbr`ctx`,continue_def,application_thm] >>
       srw_tac[boolSimps.DNF_ss][push_def] >> disj2_tac >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp op X Y Z,env)]` >>
       qpat_assum`e_step_reln^* (env,X,Exp h,[]) Y`(qspec_then`ctx`strip_assume_tac o MATCH_MP e_step_add_ctxt) >> fs[] >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       rw[e_step_def,continue_def,Abbr`ctx`,application_thm,to_small_st_def] ) >>
     imp_res_tac small_eval_app_err >> fs[] >>
     first_x_assum(qspec_then`op`mp_tac) >> simp[] >>
     disch_then(qspec_then`[]`strip_assume_tac) >>
     fs [] >>
     `LENGTH t > 2`
                by (imp_res_tac small_eval_list_length >>
                    fs [] >>
                    DECIDE_TAC) >>
     fs [] >>
     metis_tac[transitive_RTC,transitive_def,to_small_st_def])
   >- (
     fs[] >>
     rw[Once small_eval_app] >>
     `es = [] ∨ ?e es'. es = es'++[e]` by metis_tac [list_end_case]
     >- fs[Once small_eval_list_cases] >> 
     rw[] >>
     Cases_on`err`>>rw[small_eval_def] >>
     TRY (imp_res_tac small_eval_list_not_timeout >> fs[] >> NO_TAC) >>
     fs[Once small_eval_list_cases] >>
     TRY (
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>fs[] >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       metis_tac[e_single_error_add_ctxt] ) >>
     TRY (
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>fs[] >>
       rw[Once RTC_CASES_RTC_TWICE] >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       rw[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
       metis_tac[RTC_REFL]) >>
     TRY (
       imp_res_tac small_eval_list_app_type_error >> fs[] >>
       imp_res_tac e_step_add_ctxt >>
       Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
       first_x_assum(qspec_then`ctx`strip_assume_tac)>>fs[] >>
       rw[Once RTC_CASES_RTC_TWICE,PULL_EXISTS] >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       rw[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`] >>
       NO_TAC ) >>
     imp_res_tac small_eval_list_app_error >> fs[] >>
     imp_res_tac e_step_add_ctxt >>
     Q.PAT_ABBREV_TAC`ctx = [(Capp X Y Z A,env)]` >>
     first_x_assum(qspec_then`ctx`strip_assume_tac)>>fs[] >>
     rw[Once RTC_CASES_RTC_TWICE,PULL_EXISTS] >>
     first_assum(match_exists_tac o concl) >> rw[] >>
     rw[Once RTC_CASES1,e_step_reln_def,e_step_def,continue_def,Abbr`ctx`])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s',Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',Val v,[(Clog op () e2,env)])
                    (env,to_small_st s',Exp e',[])`
               by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
       every_case_tac >>
       rw [] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def, small_eval_prefix])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s2,Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s2,Val v,[(Clog op () e2,env)])
                    (env,to_small_st s2,Val bv,[])`
               by rw [e_step_def, e_step_reln_def, continue_def, return_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def, small_eval_prefix])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Clog op () e2,env)])
                      (env',to_small_st s2,Val v,[(Clog op () e2,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step (env',to_small_st s2,Val v,[(Clog op () e2,env)]) = Eabort Rtype_error`
               by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Clog op () e2,env)]) (to_small_st s', Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   rw []) >>
       fs [])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Cif () e2 e3,env)])
                      (env',to_small_st s',Val v,[(Cif () e2 e3,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',Val v,[(Cif () e2 e3,env)])
                    (env,to_small_st s',Exp e',[])`
               by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
       every_case_tac >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def,
                  small_eval_prefix])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Cif () e2 e3,env)])
                      (env',to_small_st s2,Val v,[(Cif () e2 e3,env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step (env',to_small_st s2,Val v,[(Cif () e2 e3,env)]) = Eabort Rtype_error`
               by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Cif () e2 e3,env)]) (to_small_st s', Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   rw []) >>
       fs [])
   >- (fs [small_eval_def] >>
       imp_res_tac small_eval_match_thm >>
       PairCases_on `r` >>
       fs [] >>
       cases_on `r1` >|
       [all_tac,
        cases_on `e'`] >>
       rw [] >>
       fs [small_eval_def, alt_small_eval_def] >>
       metis_tac [transitive_def, transitive_RTC, e_step_add_ctxt, APPEND])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Cmat () pes (Conv (SOME ("Bind", TypeExn (Short "Bind"))) []),env)]) (to_small_st s', Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   rw []) >>
       fs [])
   >- (fs [small_eval_def] >>
       `e_step_reln^* (env,to_small_st s,Exp e,[(Clet n () e',env)])
                      (env',to_small_st s',Val v,[(Clet n () e',env)])`
               by metis_tac [e_step_add_ctxt, APPEND] >>
       `e_step_reln (env',to_small_st s',Val v,[(Clet n () e',env)])
                    (env with v := opt_bind n v env.v,to_small_st s',Exp e',[])`
               by rw [e_step_def, e_step_reln_def, continue_def, push_def] >>
       Q.ISPEC_THEN`r`assume_tac result_cases >>
       fs [small_eval_def, environment_component_equality] >>
       fs [small_eval_def, environment_component_equality] >>
       metis_tac [transitive_RTC, RTC_SINGLE, transitive_def])
   >- (`small_eval env (to_small_st s) e ([] ++ [(Clet n () e2,env)]) (to_small_st s', Rerr err)`
               by (match_mp_tac small_eval_err_add_ctxt >>
                   rw []) >>
       fs [])
   >- (rw [small_eval_def] >>
       qexists_tac `env` >>
       qexists_tac `Exp (Letrec funs e)` >>
       qexists_tac `[]` >>
       rw [RTC_REFL, e_step_def])
   >- (fs [small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules])
   >- (fs [small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules])
   >- (cases_on `err` >>
       fs [small_eval_def] >>
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules])
   >- (cases_on `err` >>
       fs [small_eval_def] >-
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules] >-
       metis_tac [APPEND,e_step_add_ctxt, small_eval_list_rules] >>
       fs [Once small_eval_list_cases])
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
rw [] >>
rw [Once evaluate_ctxts_cases] >>
EQ_TAC >>
rw [] >>
metis_tac []);

val tac1 =
fs [evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_ctxts_cases, evaluate_ctxt_cases] >>
rw [] >>
metis_tac [oneTheory.one]

val tac3 =
fs [evaluate_state_cases] >>
ONCE_REWRITE_TAC [evaluate_cases] >>
rw [] >>
fs [evaluate_ctxts_cons, evaluate_ctxt_cases] >>
ONCE_REWRITE_TAC [hd (tl (CONJUNCTS evaluate_cases))] >>
rw [] >>
fs [evaluate_ctxts_cons, evaluate_ctxt_cases] >>
srw_tac [boolSimps.DNF_ss] [] >>
metis_tac [DECIDE ``SUC x = x + 1``, pair_CASES, REVERSE_APPEND]

val evaluate_state_app_cons = Q.prove(
  `evaluate_state (env,s,Exp e,(Capp op [] () es,env)::c) bv
    ⇒ evaluate_state (env,s,Exp (App op (REVERSE es++[e])),c) bv`,
  rw[evaluate_state_cases] >>
  rw[Once evaluate_cases] >>
  fs[evaluate_ctxts_cons] >> rw[] >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> rw[] >- (
    fs[Once evaluate_ctxt_cases, REVERSE_REVERSE, REVERSE_APPEND] >> rw[] >>
    rw[Once evaluate_cases,PULL_EXISTS] >>
    fs [] >>
    TRY (
      disj1_tac >>
      CONV_TAC(STRIP_QUANT_CONV
        (lift_conjunct_conv(same_const``bigStep$evaluate`` o fst o strip_comb))) >>
      first_assum(match_exists_tac o concl) >> rw[] >>
      TRY(first_assum(split_pair_match o concl)) >>
      first_assum(match_exists_tac o concl) >> rw[] >> NO_TAC) >>
    TRY (
      disj2_tac >> disj1_tac >>
      rw[Once evaluate_cases,PULL_EXISTS] >>
      first_assum(match_exists_tac o concl) >> rw[] >>
      first_assum(match_exists_tac o concl) >> rw[] >> NO_TAC ) >>
    rpt disj2_tac >>
    rw[Once evaluate_cases] >> disj2_tac >>
    first_assum(match_exists_tac o concl) >> rw[]) >>
  rpt disj2_tac >>
  rw[Once evaluate_cases]);

val one_step_backward = Q.prove (
`!env s e c s' env' e' c' bv.
  (e_step (env,s,e,c) = Estep (env',s',e',c')) ∧
  evaluate_state (env',s',e',c') bv
  ⇒
  evaluate_state (env,s,e,c) bv`,
 rw [e_step_def] >>
 cases_on `e` >>
 fs []
 >- (cases_on `e''` >>
     fs [push_def, return_def] >>
     rw []
     >- (fs [evaluate_ctxts_cons, evaluate_state_cases, evaluate_ctxt_cases] >>
         rw [Once evaluate_cases] >>
         metis_tac [])
     >- (fs [evaluate_ctxts_cons, evaluate_state_cases, evaluate_ctxt_cases] >>
         rw [Once evaluate_cases]
         >- metis_tac []
         >- (cases_on `err` >>
               fs [] >-
               metis_tac [] >>
               TRY (cases_on `e'`) >>
               fs [] >>
               metis_tac [])
         >- metis_tac [])
      >- tac3
      >- (every_case_tac >>
          fs [] >>
          rw [] >>
          fs [SWAP_REVERSE_SYM] >>
          rw [] >>
          fs [] >>
          tac3)
      >- (every_case_tac >>
          fs [] >>
          rw [] >>
          tac3)
      >- tac3
      >- (
        Cases_on `s` >>
        Cases_on `REVERSE l` >>
        fs[application_thm,do_opapp_def,do_app_def] >>
        rw [] >>
        fs [SWAP_REVERSE_SYM] >>
        metis_tac[evaluate_state_app_cons])
      >- tac3
      >- tac3
      >- tac3
      >- tac3
      >- (every_case_tac >>
          fs [] >>
          rw [] >>
          tac3))
 >- (fs [continue_def] >>
     cases_on `c` >>
     fs [] >>
     cases_on `h` >>
     fs [] >>
     cases_on `q` >>
     fs [] >>
     every_case_tac >>
     fs [push_def, return_def, application_def] >>
     rw [] >>
     full_simp_tac (srw_ss() ++ ARITH_ss) [evaluate_state_cases, evaluate_ctxts_cons, evaluate_ctxt_cases, oneTheory.one,
         evaluate_ctxts_cons, evaluate_ctxt_cases, arithmeticTheory.ADD1]
     >- metis_tac []
     >- (
       rw[] >>
       every_case_tac >> fs[] >> rw[] >>
       fs[do_app_def] >> every_case_tac >> fs[] >> rw[] >>
       srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
       rw[Once evaluate_cases] >>
       metis_tac[] )
     >- (
       rw[] >>
       every_case_tac >> fs[] >> rw[] >>
       rw[Once(CONJUNCT2 evaluate_cases)] >>
       rw[Once(CONJUNCT2 evaluate_cases)] >>
       rw[Once(CONJUNCT2 evaluate_cases)] >>
       fs[evaluate_ctxts_cons] >>
       fs[Once evaluate_ctxt_cases] >> rw[] >>
       metis_tac [pair_CASES]
       )
     >- (
       rw[Once evaluate_cases,PULL_EXISTS] >>
       srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] )
     >- (
       rw[Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >> disj2_tac >> disj1_tac >>
       rw[Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       first_assum(match_exists_tac o concl) >> rw[] >>
       metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC])
     >- (
       rw[Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
       metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC])
     >- (
       rw[Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >> disj2_tac >> disj1_tac >>
       rw[Once evaluate_cases] >>
       srw_tac[boolSimps.DNF_ss][] >>
       metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC])
     >- (
       srw_tac[boolSimps.DNF_ss][] >>
       rpt disj2_tac >>
       rw[Once evaluate_cases] >>
       metis_tac[])
     >- (
       srw_tac[boolSimps.DNF_ss][] >>
       rpt disj2_tac >>
       rw[Once evaluate_cases] >>
       metis_tac[])
     >- metis_tac []
     >- metis_tac []
     >- (ONCE_REWRITE_TAC [evaluate_cases] >>
         rw [])
     >- (ONCE_REWRITE_TAC [evaluate_cases] >>
         rw [] >>
         metis_tac [FST])
     >- (ONCE_REWRITE_TAC [evaluate_cases] >>
         rw [] >> fs[] >> metis_tac [])
     >- metis_tac [] >>
     every_case_tac >>
     full_simp_tac (srw_ss()++ARITH_ss++boolSimps.DNF_ss) [] >>
     ONCE_REWRITE_TAC [evaluate_cases] >>
     rw [] >>
     metis_tac [APPEND_ASSOC, APPEND, REVERSE_APPEND, REVERSE_REVERSE, REVERSE_DEF]));

val evaluate_ctxts_type_error = Q.prove (
`!a s c. evaluate_ctxts s c (Rerr (Rabort a)) (s,Rerr (Rabort a))`,
induct_on `c` >>
rw [] >>
rw [Once evaluate_ctxts_cases] >>
PairCases_on `h` >>
rw []);

val evaluate_ctxts_type_error_matchable = Q.prove (
`!a s c. s' = s ⇒ evaluate_ctxts s c (Rerr (Rabort a)) (s',Rerr (Rabort a))`,
metis_tac[evaluate_ctxts_type_error])

val one_step_backward_type_error = Q.prove (
  `!env s e c.
    (e_step (env,to_small_st s,e,c) = Eabort a)
    ⇒
    evaluate_state (env,to_small_st s,e,c)
      ((s with <| defined_mods := {}; defined_types := {}; clock := 0 |>),
       Rerr (Rabort a))`,
  rw [e_step_def] >>
  cases_on `e` >>
  fs []
  >- (
    reverse (cases_on `e'`) >>
    fs [push_def, return_def] >>
    every_case_tac >>
    rw [evaluate_state_cases] >>
    rw [Once evaluate_cases] >>
    fs [] >>
    rw [to_small_st_def]
    >> TRY (
      match_mp_tac evaluate_ctxts_type_error_matchable >>
      rw[state_component_equality] )
    >- (
      fs[application_thm] >>
      pop_assum mp_tac >> rw[] >>
      every_case_tac >> fs[to_small_st_def] >> rw[] >>
      TRY(fs[do_app_def]>>NO_TAC) >>
      rw[Once evaluate_cases] >>
      rw[Once evaluate_cases] >>
      rw[Once evaluate_cases] >>
      fs [return_def] >>
      match_mp_tac evaluate_ctxts_type_error_matchable >>
      rw[state_component_equality] ) >>
    metis_tac[do_con_check_build_conv,NOT_SOME_NONE]) >>
  fs [continue_def] >>
  cases_on `c` >> fs [] >>
  cases_on `h` >> fs [] >>
  cases_on `q` >> fs [] >>
  every_case_tac >>
  fs [evaluate_state_cases, push_def, return_def] >>
  rw [evaluate_ctxts_cons, evaluate_ctxt_cases, to_small_st_def] >>
  rw [PULL_EXISTS] >- (
    fs[application_thm] >>
    every_case_tac >> fs[return_def] >>
    rw[oneTheory.one] >>
    rw[Once evaluate_cases] >>
    rw[Once evaluate_cases] >>
    rw[Once evaluate_cases] >>
    imp_res_tac do_app_type_error >>
    imp_res_tac do_app_not_timeout >>
    fs[to_small_st_def] >> rw[] >>
    srw_tac[DNF_ss][] >>
    match_mp_tac evaluate_ctxts_type_error_matchable >>
    rw[state_component_equality] ) >>
  rw [Once evaluate_cases] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [arithmeticTheory.ADD1] >>
  rw [Once evaluate_cases] >>
  srw_tac[DNF_ss][] >> fs[to_small_st_def] >>
  ((match_mp_tac evaluate_ctxts_type_error_matchable >>
    rw[state_component_equality]) ORELSE
   metis_tac[do_con_check_build_conv,NOT_SOME_NONE]));

val small_exp_to_big_exp = Q.prove (
`!st st'. e_step_reln^* st st' ⇒
  !r.
    evaluate_state st' r
    ⇒
    evaluate_state st r`,
HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >>
rw [e_step_reln_def] >>
PairCases_on `st` >>
PairCases_on `st'` >>
PairCases_on `st''` >>
rw [] >>
metis_tac [one_step_backward]);

val evaluate_state_no_ctxt = Q.prove (
`!env s e r.
  evaluate_state (env,to_small_st s,Exp e,[]) r 
  ⇔ 
  evaluate F env (s with <| defined_mods := {}; defined_types := {}; clock := 0 |>) e r`,
 rw [evaluate_state_cases, Once evaluate_ctxts_cases] >>
 rw [evaluate_state_cases, Once evaluate_ctxts_cases] >>
 fs [to_small_st_def] >>
 Cases_on`r`>>simp[]>>
 rpt AP_THM_TAC >> AP_TERM_TAC >>
 simp[state_component_equality]);

val evaluate_state_val_no_ctxt = Q.prove (
`!env s e.
  evaluate_state (env,to_small_st s,Val e,[]) r
  ⇔ 
  (r = (s with <| defined_mods := {}; defined_types := {}; clock := 0 |>, Rval e))`,
 rw [evaluate_state_cases, Once evaluate_ctxts_cases] >>
 rw [evaluate_state_cases, Once evaluate_ctxts_cases] >>
 fs [to_small_st_def] >>
 eq_tac >>
 rw [] >>
 fs [state_component_equality]);

val evaluate_state_val_raise_ctxt = Q.prove (
`!env s v env'.
  evaluate_state (env,to_small_st s,Val v,[(Craise (), env')]) r 
  ⇔ 
  (r = (s with <| defined_mods := {}; defined_types := {}; clock := 0 |>, Rerr (Rraise v)))`,
 rw [evaluate_state_cases, Once evaluate_ctxts_cases] >>
 rw [evaluate_state_cases, Once evaluate_ctxts_cases] >>
 rw [evaluate_ctxt_cases] >>
 rw [evaluate_state_cases, Once evaluate_ctxts_cases] >>
 fs [to_small_st_def] >>
 eq_tac >>
 rw [] >>
 fs [state_component_equality]);

val evaluate_change_state = Q.prove(
  `evaluate a b c d (e,f) ∧ c = c' ∧ e = e' ⇒
   evaluate a b c' d (e',f)`,
   rw[] >> rw[]) |> GEN_ALL

val small_big_exp_equiv = Q.store_thm ("small_big_exp_equiv",
`!env s e s' r.
  (small_eval env (to_small_st s) e [] (to_small_st s',r) ∧ 
   s.clock = s'.clock ∧ s.defined_types = s'.defined_types ∧ s.defined_mods = s'.defined_mods)
  ⇔ 
  evaluate F env s e (s',r)`,
 rw [] >>
 eq_tac
 >- (rw [] >>
     cases_on `r` >|
     [all_tac,
      cases_on `e'`] >>
     fs [small_eval_def] >>
     imp_res_tac small_exp_to_big_exp >>
     fs [evaluate_state_val_no_ctxt, evaluate_state_no_ctxt, evaluate_state_val_raise_ctxt] >>
     imp_res_tac evaluate_ignores_types_mods >>
     fs [] >> TRY (
         pop_assum (qspecl_then [`s.defined_mods`, `s.defined_types`] mp_tac) >>
         rw [] >>
         match_mp_tac evaluate_change_state >>
         imp_res_tac big_unclocked >>
         first_x_assum(qspec_then`s.clock`strip_assume_tac) >>
         first_assum(match_exists_tac o concl) >>
         simp[state_component_equality] >> NO_TAC) >>
     (imp_res_tac one_step_backward_type_error >>
         fs [] >>
         res_tac >>
         imp_res_tac evaluate_ignores_types_mods >>
         pop_assum (qspecl_then [`s.defined_mods`, `s.defined_types`] mp_tac) >>
         rw [] >>
         pop_assum mp_tac >>
         ntac 3 (pop_assum kall_tac) >> strip_tac >>
         match_mp_tac evaluate_change_state >>
         imp_res_tac big_unclocked >>
         first_x_assum(qspec_then`s.clock`strip_assume_tac) >>
         first_assum(match_exists_tac o concl) >>
         simp[state_component_equality]))
 >- (rw [] >>
     imp_res_tac big_exp_to_small_exp >>
     fs [small_eval_def, to_small_res_def] >>
     metis_tac [evaluate_no_new_types_mods, FST, big_unclocked]));

(* ---------------------- Small step determinacy ------------------------- *)

val small_exp_determ = Q.store_thm ("small_exp_determ",
`!env s e r1 r2.
  small_eval env s e [] r1 ∧ small_eval env s e [] r2
  ⇒
  (r1 = r2)`,
 rw [] >>
 assume_tac small_big_exp_equiv >>
 fs [to_small_st_def] >>
 PairCases_on `r1` >>
 PairCases_on `r2` >>
 pop_assum (qspecl_then [`env`, `<| ffi := SND s; refs := FST s; clock := 0; defined_types := {}; defined_mods := {} |>`, `e`] mp_tac) >>
 simp [] >>
 strip_tac >>
 first_assum (qspec_then `<| ffi := (r11,r12); refs := r10; clock := 0; defined_types := {}; defined_mods := {} |>` mp_tac) >>
 first_assum (qspec_then `<| ffi := (r21,r22); refs := r20; clock := 0; defined_types := {}; defined_mods := {} |>` mp_tac) >>
 pop_assum kall_tac >>
 simp [] >>
 strip_tac >>
 strip_tac >>
 fs [] >>
 rw [] >>
 imp_res_tac big_exp_determ >>
 fs []);

val _ = export_theory ();

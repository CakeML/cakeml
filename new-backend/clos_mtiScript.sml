open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory
open rich_listTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory;

val _ = new_theory "clos_mti";

val ect = BasicProvers.EVERY_CASE_TAC;

(* Copied from clos_to_bvlScript.sml *)
val cEval_length_imp = Q.prove (
`!xs env s1 vs s2.
  cEval (xs, env, s1) = (Result vs, s2)
  ⇒
  LENGTH xs = LENGTH vs`,
 rw [] >>
 assume_tac (Q.SPECL [`xs`, `env`, `s1`] (hd (CONJUNCTS cEval_LENGTH))) >>
 rfs []);

val collect_args_def = Define `
(collect_args max_app num_args (Fn loc fvs num_args' e) =
  if num_args + num_args' ≤ max_app then
    collect_args max_app (num_args + num_args') e
  else 
    (max_app, Fn loc fvs (num_args + num_args' - max_app) e)) ∧
(collect_args max_app num_args e = (num_args, e))`;

val collect_args_size = Q.prove (
`!max_app num_args e num_args' e'.
  (num_args', e') = collect_args max_app num_args e ⇒ 
  num_args' + clos_exp_size e' ≤ num_args + clos_exp_size e`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def, clos_exp_size_def] >>
 rw [clos_exp_size_def] >>
 res_tac >>
 decide_tac);

val intro_multi_def = tDefine "intro_multi"`
(intro_multi [] = []) ∧
(intro_multi (e1::e2::es) = 
  HD (intro_multi [e1]) :: HD (intro_multi [e2]) :: intro_multi es) ∧
(intro_multi [Var n] = [Var n]) ∧
(intro_multi [If e1 e2 e3] =
  [If (HD (intro_multi [e1])) (HD (intro_multi [e2])) (HD (intro_multi [e3]))]) ∧
(intro_multi [Let es e] =
  [Let (intro_multi es) (HD (intro_multi [e]))]) ∧
(intro_multi [Raise e] =
  [Raise (HD (intro_multi [e]))]) ∧
(intro_multi [Handle e1 e2] =
  [Handle (HD (intro_multi [e1])) (HD (intro_multi [e2]))]) ∧
(intro_multi [Tick e] =
  [Tick (HD (intro_multi [e]))]) ∧
(intro_multi [Call n es] =
  [Call n (intro_multi es)]) ∧
(intro_multi [App loc e es] =
  [App loc (HD (intro_multi [e])) (intro_multi es)]) ∧
(intro_multi [Fn loc fvs num_args e] =
  let (num_args', e') = collect_args max_app num_args e in
    [Fn loc fvs num_args' (HD (intro_multi [e']))]) ∧
(intro_multi [Letrec loc fvs funs e] =
  [Letrec loc fvs (MAP (\(num_args, e). 
                         let (num_args', e') = collect_args max_app num_args e in
                           (num_args', HD (intro_multi [e'])))
                       funs)
      (HD (intro_multi [e]))]) ∧
(intro_multi [Op op es] =
  [Op op (intro_multi es)])`
 (WF_REL_TAC `measure clos_exp3_size` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  imp_res_tac collect_args_size >>
  TRY decide_tac >>
  `num_args + clos_exp_size e' ≤ clos_exp1_size funs` 
          by (Induct_on `funs` >>
              rw [clos_exp_size_def] >>
              rw [clos_exp_size_def] >>
              res_tac >>
              decide_tac) >>
  decide_tac);

val clos_val_size_el = Q.prove (
`!n es. n < LENGTH es ⇒ clos_val_size (EL n es) ≤ clos_val1_size es`,
 Induct_on `es` >>
 rw [clos_val_size_def] >>
 Cases_on `0 < n` >>
 rw [EL_CONS]
 >- (first_x_assum (qspec_then `n-1` mp_tac) >>
     rw [PRE_SUB1] >>
     fs [ADD1] >>
     decide_tac)
 >- (`n = 0` by decide_tac >>
     fs [] >>
     decide_tac));

val exp_rel_def = Define `
exp_rel (num_args,e) (num_args',e') ⇔
  num_args ≤ max_app ∧
  0 < num_args ∧
  num_args' ≤ max_app ∧
  0 < num_args' ∧
  num_args ≤ num_args' ∧
  ?e''.
    (num_args',e'') = collect_args num_args' num_args e ∧
    e' = HD (intro_multi [e''])`;

val (val_rel_rules, val_rel_ind, val_rel_cases) = Hol_reln `
(!n. 
  val_rel (Number n) (Number n)) ∧
(!n vs vs'.
  LIST_REL val_rel vs vs'
  ⇒
  val_rel (Block n vs) (Block n vs')) ∧
(!n.
  val_rel (RefPtr n) (RefPtr n)) ∧
(!num_args' e' e args' args env env' loc num_args.
  LIST_REL val_rel args args' ∧
  LIST_REL val_rel env env' ∧
  exp_rel (num_args,e) (num_args',e')
  ⇒
  val_rel (Closure loc args env num_args e) 
          (Closure loc args' env' num_args' e')) ∧
(!args args' env env' funs funs' i.
  LIST_REL val_rel args args' ∧
  LIST_REL val_rel env env' ∧
  LIST_REL exp_rel funs funs'
  ⇒
  val_rel (Recclosure loc args env funs i)
          (Recclosure loc args' env' funs' i))`;

val (res_rel_rules, res_rel_ind, res_rel_cases) = Hol_reln `
(!vs.
  LIST_REL val_rel vs vs'
  ⇒
  res_rel (Result vs) (Result vs')) ∧
(!v.
  res_rel (Exception v) (Exception v)) ∧
(res_rel TimeOut TimeOut)`;

val (ref_v_rel_rules, ref_v_rel_ind, ref_v_rel_cases) = Hol_reln `
(!ws.
  ref_v_rel (ByteArray ws) (ByteArray ws)) ∧
(!vs vs'.
  LIST_REL val_rel vs vs'
  ⇒
  ref_v_rel (ValueArray vs) (ValueArray vs'))`;

val state_rel_def = Define `
state_rel (s:clos_state) s' ⇔
  LIST_REL (OPTION_REL val_rel) s.globals s'.globals ∧
  fmap_rel ref_v_rel s.refs s'.refs ∧
  s.clock = s'.clock ∧
  fmap_rel exp_rel s.code s'.code ∧
  s.output = s'.output ∧
  s.restrict_envs = s'.restrict_envs`;

val lookup_vars_list_rel = Q.prove (
`!vs env env' f. 
  LIST_REL f env env'
  ⇒
  OPTION_REL (LIST_REL f) (lookup_vars vs env) (lookup_vars vs env')`,
 Induct_on `vs` >>
 rw [lookup_vars_def] >>
 ect >>
 fs [OPTREL_def] >>
 res_tac >>
 fs [LIST_REL_EL_EQN] >>
 metis_tac []);

val collect_args_more = Q.prove (
`!max_app num_args e num_args' e'.
  num_args ≤ max_app ∧
  (num_args', e') = collect_args max_app num_args e
  ⇒
  num_args ≤ num_args' ∧ num_args' ≤ max_app`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def] >>
 rw [] >>
 res_tac >>
 decide_tac);

val collect_args_mono = Q.prove (
`!num_args4 num_args2 exp num_args3 exp' num_args1.
  num_args2 ≤ num_args3 ∧
  num_args3 ≤ num_args1 ∧
  num_args4 = num_args3 ∧
  collect_args num_args1 num_args2 exp = (num_args3, exp')
  ⇒
  collect_args num_args4 num_args2 exp = (num_args3, exp')`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def] >>
 rw [] >>
 fs [NOT_LESS_EQUAL] >>
 ect >>
 fs [] >>
 fs [NOT_LESS_EQUAL] >>
 rw [] >>
 TRY (first_x_assum match_mp_tac) >>
 full_simp_tac (srw_ss()++ARITH_ss) []
 >- metis_tac [] >>
 pop_assum mp_tac >>
 pop_assum (mp_tac o GSYM) >>
 rw [] >>
 imp_res_tac collect_args_more >>
 full_simp_tac (srw_ss()++ARITH_ss) []);

val intro_multi_length = Q.prove ( 
`!es. LENGTH (intro_multi es) = LENGTH es`,
 recInduct (fetch "-" "intro_multi_ind") >>
 rw [intro_multi_def] >>
 rw [intro_multi_def]);

val intro_multi_sing = Q.prove (
`!e. ?e'. intro_multi [e] = [e']`,
 Cases_on `e` >>
 rw [intro_multi_def] >>
 Cases_on `collect_args max_app n c` >>
 fs []);

 (*
val (dest_cl_res_rel_rules, dest_cl_res_rel_ind, dest_cl_res_rel_cases) = Hol_reln `
(!v v'.
  val_rel v v'
  ⇒ 
  dest_cl_res_rel (Partial_app v) (Partial_app v')) ∧
(!env env' args args'.
  LIST_REL val_rel env env' ∧
  LIST_REL val_rel args args'
  ⇒
  (dest_cl_res_rel (Full_app e env args) (Full_app (HD (intro_multi [e])) env' args')))`;

val dest_closure_thm = Q.prove (
`!loc f args res f' args' res'.
  dest_closure NONE f args = SOME res ∧
  0 < LENGTH args ∧
  val_rel f f' ∧
  LIST_REL val_rel args args'
  ⇒
  ?res'.
    dest_cl_res_rel res res' ∧
    dest_closure NONE f' args' = SOME res'`,

 rw [dest_closure_def] >>
 ect >>
 fs [Once val_rel_cases, dest_cl_res_rel_cases] >>
 rw [] >>
 fs [check_loc_def, exp_rel_def] >>
 imp_res_tac EVERY2_LENGTH >>
 TRY (`n - LENGTH l ≤ LENGTH args'` by decide_tac) >>
 TRY (`n' - LENGTH l' ≤ LENGTH args` by decide_tac) >>
 rw [DROP_REVERSE, TAKE_REVERSE, LASTN_MAP, ETA_THM, BUTLASTN_MAP] >>
 fs [] >>
 rev_full_simp_tac (srw_ss()++ARITH_ss) [NOT_LESS] >>
 rw [] >>

 Cases_on `f` >>
 fs []
 Cases_on `f'` >>
 fs [] >>
 fs [Once val_rel_cases] >>
 rw []
 Cases_on `¬(LENGTH args + LENGTH l < n)` >>
 fs []

 metis_tac [EVERY2_APPEND]

 imp_res_tac EVERY2_LENGTH >>

 simp []
 fs [check_loc_def]
 `n ≤ n'` by fs [exp_rel_def] >>
 rw []


 Cases_on `c'` >>
 fs [intro_multi_def, collect_args_def]
 ect >>
 fs []

val intro_multi_correct = Q.prove (
`(!tmp es env s1 res s2 s1' env'.
   tmp = (es,env,s1) ∧
   cEval tmp = (res, s2) ∧
   res ≠ Error ∧
   LIST_REL val_rel env env' ∧
   state_rel s1 s1'
   ⇒
   ?res' s2'.
     state_rel s2 s2' ∧
     res_rel res res' ∧
     cEval (intro_multi es, env', s1') = (res', s2')) ∧
 (!loc_opt func args s1 res s2 func' args' s1'.
   cEvalApp loc_opt func args s1 = (res, s2) ∧
   res ≠ Error ∧
   val_rel func func' ∧
   LIST_REL val_rel args args' ∧
   state_rel s1 s1'
   ⇒
   ?res' s2'.
     state_rel s2 s2' ∧
     res_rel res res' ∧
     cEvalApp loc_opt func' args' s1' = (res', s2'))`,

 ho_match_mp_tac cEval_ind >>
 rpt strip_tac
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def, res_rel_cases])
 >- cheat
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     imp_res_tac EVERY2_LENGTH >>
     fs [LIST_REL_EL_EQN] >>
     rw [res_rel_cases])
 >- cheat
 >- cheat
 >- cheat
 >- cheat
 >- cheat
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     rw [cEval_def] >>
     fs [] >>
     ect >>
     fs [] >>
     rw [] >>
     `s.restrict_envs = s1'.restrict_envs` by fs [state_rel_def] >>
     fs [res_rel_cases, clos_env_def]
     >- (ect >>
         fs [] >>
         imp_res_tac lookup_vars_list_rel >>
         pop_assum (qspec_then `vs` mp_tac) >>
         rw [OPTREL_def]) >>
     `LIST_REL val_rel x' x`
           by (ect >>
               fs [] >>
               imp_res_tac lookup_vars_list_rel >>
               pop_assum (qspec_then `vs` mp_tac) >>
               rw [OPTREL_def]) >>
     `?num_args' e'. collect_args max_app num_args exp = (num_args', e')` by metis_tac [pair_CASES] >>
     simp [] >>
     `num_args' ≤ max_app ∧ num_args ≤ num_args'` by metis_tac [collect_args_more] >>
     simp [] >>
     rw [Once val_rel_cases] >>
     simp [exp_rel_def] >>
     qexists_tac `e'` >>
     rw [] >>
     metis_tac [collect_args_mono])
 >- cheat
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     fs [intro_multi_length] >>
     `?res1 s1. cEval (args, env, s) = (res1,s1)` by metis_tac [pair_CASES] >>
     fs [] >>
     reverse (Cases_on `res1`) >>
     fs [] >>
     rw []
     >- (res_tac >>
         rw [] >>
         fs [res_rel_cases] >>
         rw [])
     >- (res_tac >>
         rw [] >>
         fs [res_rel_cases] >>
         rw []) >>
     `?res2 s2. cEval ([x1], env, s1) = (res2,s2)` by metis_tac [pair_CASES] >>
     `?x1'. intro_multi [x1] = [x1']` by metis_tac [intro_multi_sing] >>
     fs [] >>
     reverse (Cases_on `res2`) >>
     fs [] >>
     rw [] >>
     res_tac >>
     rw [] >>
     fs [res_rel_cases] >>
     rw [] >>
     first_x_assum match_mp_tac >>
     rw [] >>
     Cases_on `a'` >>
     Cases_on `vs'''` >>
     fs [] >>
     imp_res_tac cEval_length_imp >>
     fs [])
 >- cheat
 >- cheat
 >- (fs [cEval_def] >>
     Cases_on `res` >>
     fs [res_rel_cases] >>
     metis_tac [])

 >- (fs [cEval_def] >>
     ect >>
     fs []

     rw []
     *)


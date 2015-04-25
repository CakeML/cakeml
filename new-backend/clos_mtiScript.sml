open HolKernel Parse boolLib bossLib;

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory
open rich_listTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory;

val _ = new_theory "clos_mti";

val ect = BasicProvers.EVERY_CASE_TAC;

val el_butlastn = Q.prove (
`!n m l. n+m < LENGTH l ⇒ EL n (BUTLASTN m l) = EL n l`,
 rw [] >>
 `n ≤ LENGTH l ∧ m ≤ LENGTH l` by decide_tac >>
 `n < LENGTH l - m` by decide_tac >>
 rw [BUTLASTN_TAKE, EL_TAKE]);

val butlastn_ident = Q.prove (
`!l n. (n ≤ LENGTH l ∧ BUTLASTN n l = l) ⇔ n = 0`,
 Induct >>
 rw [] >>
 Cases_on `n ≤ LENGTH l` >>
 eq_tac >>
 fs [BUTLASTN_CONS, NOT_LESS_EQUAL, BUTLASTN] >>
 rw []
 >- metis_tac [] >>
 `n = LENGTH l + 1` by decide_tac >>
 rw [] >>
 `LENGTH l + 1 = LENGTH (h::l)` by rw [ADD1] >>
 full_simp_tac std_ss [BUTLASTN_LENGTH_NIL] >>
 fs []);

(* Copied from clos_to_bvlScript.sml *)
val cEval_length_imp = Q.prove (
`!xs env s1 vs s2.
  cEval (xs, env, s1) = (Result vs, s2)
  ⇒
  LENGTH xs = LENGTH vs`,
 rw [] >>
 assume_tac (Q.SPECL [`xs`, `env`, `s1`] (hd (CONJUNCTS cEval_LENGTH))) >>
 rfs []);

val add_args_def = Define `
(add_args (Closure loc_opt args env num_args exp : clos_val) args' =
  SOME (Closure loc_opt (args'++args) env num_args exp)) ∧
(add_args (Recclosure loc_opt args env funs i : clos_val) args' =
  SOME (Recclosure loc_opt (args'++args) env funs i)) ∧
(add_args _ _ = NONE)`;
(* END COPY *)

val collect_args_def = Define `
(collect_args num_args (Fn loc fvs num_args' e) =
  if num_args + num_args' ≤ max_app then
    collect_args (num_args + num_args') e
  else
    (max_app, Fn loc fvs (num_args + num_args' - max_app) e)) ∧
(collect_args num_args e = (num_args, e))`;

val collect_args_size = Q.prove (
`!num_args e num_args' e'.
  (num_args', e') = collect_args num_args e ⇒
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
  let (num_args', e') = collect_args num_args e in
    [Fn loc fvs num_args' (HD (intro_multi [e']))]) ∧
(intro_multi [Letrec loc fvs funs e] =
  [Letrec loc fvs (MAP (\(num_args, e).
                         let (num_args', e') = collect_args num_args e in
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

val intro_multi_length = Q.prove (
`!es. LENGTH (intro_multi es) = LENGTH es`,
 recInduct (fetch "-" "intro_multi_ind") >>
 rw [intro_multi_def] >>
 rw [intro_multi_def]);

val intro_multi_sing = Q.prove (
`!e. ?e'. intro_multi [e] = [e']`,
 Cases_on `e` >>
 rw [intro_multi_def] >>
 Cases_on `collect_args n c` >>
 fs []);

val collect_args_more = Q.prove (
`!num_args e num_args' e'.
  num_args ≤ max_app ∧
  (num_args', e') = collect_args num_args e
  ⇒
  num_args' ≤ max_app ∧ num_args ≤ num_args'`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def] >>
 rw [] >>
 res_tac >>
 decide_tac);

val collect_args_zero = Q.prove (
`!num_args e e'.
  collect_args num_args e = (0, e')
  ⇒
  num_args = 0`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def] >>
 rw [collect_args_def] >>
 fs [max_app_def]);

val collect_args_idem = Q.prove (
`!num_args e num_args' e'.
  collect_args num_args e = (num_args', e')
  ⇒
  collect_args num_args' (HD (intro_multi [e'])) = (num_args', (HD (intro_multi [e'])))`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def, intro_multi_def] >>
 rw [collect_args_def, intro_multi_def] >>
 fs [NOT_LESS_EQUAL] >>
 `num_args'' = 0` by decide_tac >>
 rw [] >>
 imp_res_tac collect_args_zero >>
 fs [] >>
 `max_app< max_app` by decide_tac >>
 fs []);

val intro_multi_idem = Q.prove (
`!e. intro_multi (intro_multi e) = intro_multi e`,
 ho_match_mp_tac (fetch "-" "intro_multi_ind") >>
 rw [intro_multi_def] >>
 rw [intro_multi_def]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD]
 >- metis_tac [intro_multi_sing, HD, collect_args_idem, PAIR_EQ]
 >- (rw [LET_THM, inferPropsTheory.remove_pair_lem, MAP_MAP_o, combinTheory.o_DEF] >>
     rw [MAP_EQ_f] >>
     PairCases_on `x` >>
     simp [] >>
     Cases_on `collect_args x0 x1` >>
     simp [] >>
     res_tac >>
     rfs [] >>
     metis_tac [intro_multi_sing, HD, collect_args_idem, PAIR_EQ, FST, SND])
 >- metis_tac [intro_multi_sing, HD]);

val collect_all_args_def = Define `
(collect_all_args num_args (Fn loc fvs num_args' e) =
  collect_all_args (num_args + num_args') e) ∧
(collect_all_args num_args e = (num_args, e))`;

val count_all_args_def = Define
`(count_all_args (Fn loc fvs num_args e) = num_args + count_all_args e) ∧
 (count_all_args _ = 0)`;

val strip_fns_def = Define
`(strip_fns (Fn loc fvs num_args e) = strip_fns e) ∧
 (strip_fns x = x)`;

val collect_all_args_decomp = Q.prove (
`!num_args e.
  collect_all_args num_args e = (num_args + count_all_args e, strip_fns e)`,
 ho_match_mp_tac (fetch "-" "collect_all_args_ind") >>
 rw [collect_all_args_def, count_all_args_def, strip_fns_def] >>
 decide_tac);

val strip_fns_collect_args = Q.prove (
`!num_args e num_args' e'.
  collect_args num_args e = (num_args', e')
  ⇒
  strip_fns e = strip_fns e'`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def, strip_fns_def] >>
 rw [collect_args_def, strip_fns_def]);

val count_all_args_collect_args = Q.prove (
`!num_args e num_args' e'.
  collect_args num_args e = (num_args', e')
  ⇒
  num_args + count_all_args e = num_args' + count_all_args e'`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def, count_all_args_def] >>
 rw [collect_args_def, count_all_args_def] >>
 TRY decide_tac >>
 fs [] >>
 simp []);

val count_all_args_intro = Q.prove (
`!e. count_all_args (HD (intro_multi [e])) = count_all_args e`,
 completeInduct_on `clos_exp_size e` >>
 Cases_on `e` >>
 rw [count_all_args_def, intro_multi_def] >>
 rw [count_all_args_def, intro_multi_def] >>
 fs [clos_exp_size_def, ADD1] >>
 imp_res_tac count_all_args_collect_args >>
 rw [] >>
 fs [PULL_FORALL] >>
 first_x_assum match_mp_tac >>
 pop_assum kall_tac >>
 pop_assum (assume_tac o GSYM) >>
 imp_res_tac collect_args_size >>
 decide_tac);

val strip_fns_intro = Q.prove (
`!e. strip_fns (HD (intro_multi [e])) = HD (intro_multi [strip_fns e])`,
 completeInduct_on `clos_exp_size e` >>
 Cases_on `e` >>
 rw [strip_fns_def, intro_multi_def] >>
 rw [strip_fns_def, intro_multi_def] >>
 fs [clos_exp_size_def, ADD1] >>
 imp_res_tac strip_fns_collect_args >>
 rw [] >>
 fs [PULL_FORALL] >>
 first_x_assum match_mp_tac >>
 pop_assum kall_tac >>
 pop_assum (assume_tac o GSYM) >>
 imp_res_tac collect_args_size >>
 decide_tac);

val collect_all_args_intro = Q.prove (
`!num_args e num_args' e' num_args'' e''.
  collect_all_args num_args e = (num_args', e') ∧
  collect_all_args num_args (HD (intro_multi [e])) = (num_args'', e'')
  ⇒
  num_args' = num_args''  ∧
  e'' = HD (intro_multi [e'])`,
 rw [collect_all_args_decomp] >>
 metis_tac [strip_fns_intro, count_all_args_intro]);

val collect_args_then_all = Q.prove (
`!num_args e num_args' e'.
  collect_args num_args e = (num_args', e')
  ⇒
  collect_all_args num_args e = collect_all_args num_args' e'`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_all_args_def, collect_args_def] >>
 simp [collect_all_args_def]);

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

val norm_exp_def = Define `
norm_exp (num_args, e) =
  let (num_args', e') = collect_all_args num_args e in
    (num_args', HD (intro_multi [e']))`;

val norm_closure_def = Define `
(norm_closure (Closure loc args env num_args e) =
  let (num_args', e') = norm_exp (num_args, e) in
    if LENGTH args ≤ num_args' then
      SOME (args++env, num_args'-LENGTH args, e')
    else
      NONE) ∧
(norm_closure (Recclosure loc args env funs i) =
  let (num_args', e') = norm_exp (EL i funs) in
    if LENGTH args ≤ num_args' then
      SOME (args ++ GENLIST (Recclosure loc [] env funs) (LENGTH funs) ++ env, num_args'-LENGTH args, e')
    else
      NONE) ∧
(norm_closure _ = NONE)`;

val cl_ok_def = Define `
(cl_ok (Closure loc args env num_args e) ⇔
  0 < num_args ∧ LENGTH args < num_args) ∧
(cl_ok (Recclosure loc args env funs i) ⇔
  let (num_args, e) = EL i funs in
    i < LENGTH funs ∧ 0 < num_args ∧ LENGTH args < num_args)`;

val (val_rel_rules, val_rel_ind, val_rel_cases) = Hol_reln `
(!n.
  val_rel (Number n) (Number n)) ∧
(!n vs vs'.
  LIST_REL val_rel vs vs'
  ⇒
  val_rel (Block n vs) (Block n vs')) ∧
(!n.
  val_rel (RefPtr n) (RefPtr n)) ∧
(!cl1 cl2 env1 env2.
  cl_ok cl1 ∧
  cl_ok cl2 ∧
  norm_closure cl1 = SOME (env1, num_args, e) ∧
  norm_closure cl2 = SOME (env2, num_args, e) ∧
  LIST_REL val_rel env1 env2
  ⇒
  val_rel cl1 cl2)`;

val exp_rel_def = Define `
exp_rel e1 e2 ⇔ norm_exp e1 = norm_exp e2`;

val (res_rel_rules, res_rel_ind, res_rel_cases) = Hol_reln `
(!vs.
  LIST_REL val_rel vs vs'
  ⇒
  res_rel (Result vs) (Result vs')) ∧
(!v v'.
  val_rel v v'
  ⇒
  res_rel (Exception v) (Exception v')) ∧
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

val collect_all_args_more = Q.prove (
`!num_args e num_args' e'.
  (num_args', e') = collect_all_args num_args e
  ⇒
  num_args ≤ num_args'`,
 ho_match_mp_tac (fetch "-" "collect_all_args_ind") >>
 rw [collect_all_args_def] >>
 rw [] >>
 res_tac >>
 decide_tac);


 (*
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
 *)

val dest_closure_some_imp = Q.prove (
`!f args res f' args'.
  val_rel f f' ∧
  LIST_REL val_rel args args' ∧
  dest_closure NONE f args = SOME res
  ⇒
  ?res'. dest_closure NONE f' args' = SOME res'`,
 rw [dest_closure_def] >>
 ect >>
 fs [val_rel_cases, LET_THM] >>
 fs [check_loc_def] >>
 imp_res_tac EVERY2_LENGTH >>
 fs [norm_exp_def, norm_closure_def, LET_THM, inferPropsTheory.remove_pair_lem,
     NOT_LESS_EQUAL, NOT_LESS, cl_ok_def] >>
 TRY decide_tac >>
 rw []);

val dest_closure_partial_partial = Q.prove (
`!f args f' args' v v'.
  val_rel f f' ∧
  LIST_REL val_rel args args' ∧
  dest_closure NONE f args = SOME (Partial_app v) ∧
  dest_closure NONE f' args' = SOME (Partial_app v')
  ⇒
  val_rel v v'`,
 rw [dest_closure_def] >>
 ect >>
 fs [val_rel_cases, LET_THM] >>
 rw [] >>
 fs [check_loc_def] >>
 imp_res_tac EVERY2_LENGTH >>
 fs [cl_ok_def, norm_exp_def, norm_closure_def, LET_THM, inferPropsTheory.remove_pair_lem]
 >- (rw [] >>
     TRY decide_tac >>
     metis_tac [EVERY2_APPEND, APPEND_ASSOC, collect_all_args_more, FST,
                pair_CASES, LESS_EQ_TRANS, LESS_IMP_LESS_OR_EQ])
 >- (ect >>
     fs [] >>
     rw [norm_closure_def, cl_ok_def] >>
     `?num_args e. EL n' l1 = (num_args, e)` by metis_tac [pair_CASES] >>
     fs [norm_exp_def] >>
     qexists_tac `args++l'++GENLIST (Recclosure n0' [] l0' l1) (LENGTH l1)++l0'` >>
     simp [] >>
     `?num_args1 e1. collect_all_args num_args e = (num_args1, e1)` by metis_tac [pair_CASES] >>
     simp [markerTheory.Abbrev_def] >>
     fs [LET_THM] >>
     rw [] >>
     TRY decide_tac >>
     metis_tac [EVERY2_APPEND, APPEND_ASSOC, collect_all_args_more, FST,
                pair_CASES, LESS_EQ_TRANS, LESS_IMP_LESS_OR_EQ])
 >- (ect >>
     fs [] >>
     rw [norm_closure_def, cl_ok_def] >>
     `?num_args e. EL n l1 = (num_args, e)` by metis_tac [pair_CASES] >>
     fs [norm_exp_def] >>
     qexists_tac `args'++l++GENLIST (Recclosure n0 [] l0 l1) (LENGTH l1)++l0` >>
     simp [] >>
     `?num_args1 e1. collect_all_args num_args e = (num_args1, e1)` by metis_tac [pair_CASES] >>
     simp [markerTheory.Abbrev_def] >>
     fs [LET_THM] >>
     rw [] >>
     TRY decide_tac >>
     metis_tac [EVERY2_APPEND, APPEND_ASSOC, collect_all_args_more, FST,
                pair_CASES, LESS_EQ_TRANS, LESS_IMP_LESS_OR_EQ])
 >- (ect >>
     fs [] >>
     rw [norm_closure_def, cl_ok_def] >>
     `?num_args e. EL n l1 = (num_args, e)` by metis_tac [pair_CASES] >>
     `?num_args2 e2. EL n' l1' = (num_args2, e2)` by metis_tac [pair_CASES] >>
     rw [norm_exp_def] >>
     `?num_args3 e3. collect_all_args num_args e = (num_args3, e3)` by metis_tac [pair_CASES] >>
     `?num_args4 e4. collect_all_args num_args2 e2 = (num_args4, e4)` by metis_tac [pair_CASES] >>
     simp [] >>
     fs [norm_exp_def, LET_THM] >>
     rw [] >>
     TRY decide_tac >>
     metis_tac [EVERY2_APPEND, APPEND_ASSOC, collect_all_args_more, FST,
                pair_CASES, LESS_EQ_TRANS, LESS_IMP_LESS_OR_EQ]));

val norm_exp_thm = Q.prove (
`!num_args e num_args' e' e''.
  collect_args num_args e = (num_args',e') ∧
  [e''] = intro_multi [e']
  ⇒
  norm_exp (num_args', e'') = norm_exp (num_args, e)`,
 rw [norm_exp_def] >>
 imp_res_tac collect_args_then_all >>
 fs [] >>
 metis_tac [collect_all_args_intro, HD, intro_multi_sing, intro_multi_idem]);

val intro_multi_cons = Q.prove (
`!x xs. intro_multi (x::xs) = HD (intro_multi [x])::intro_multi xs`,
 Induct_on `xs` >>
 rw [intro_multi_def] >>
 Cases_on `x` >>
 rw [intro_multi_def]);

val intro_multi_sing = Q.prove (
`!x. [HD (intro_multi [x])] = intro_multi [x]`,
 Cases_on `x` >>
 rw [intro_multi_def]);


(* HERE

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
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def, res_rel_cases] >>
     fs [intro_multi_sing] >>
     Cases_on `cEval ([x],env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     res_tac >>
     rw []
     >- (Cases_on `cEval (y::xs,env,r)` >>
         fs [] >>
         Cases_on `q` >>
         fs [] >>
         rw [] >>
         res_tac >>
         rw [] >>
         fs [res_rel_cases] >>
         rw [] >>
         fs [Once intro_multi_cons] >>
         fs [LIST_REL_EL_EQN] >>
         rw [] >>
         imp_res_tac cEval_length_imp >>
         fs [] >>
         metis_tac [EL, DECIDE ``0<1:num``]) >>
     fs [res_rel_cases] >>
     rw [])
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     imp_res_tac EVERY2_LENGTH >>
     fs [LIST_REL_EL_EQN] >>
     rw [res_rel_cases])
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     fs [intro_multi_sing] >>
     Cases_on `cEval ([x1],env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     res_tac >>
     rw []
     >- (fs [] >>
         rw [] >>
         `HD a = Block 0 [] ∨ HD a = Block 1 []`
               by (Cases_on `Block 1 [] = HD a` >>
                   fs [] >>
                   Cases_on `HD a = Block 0 []` >>
                   fs []) >>
         fs [] >>
         rw [] >>
         qpat_assum `res_rel (Result a) res'` (mp_tac o SIMP_RULE (srw_ss()) [res_rel_cases]) >>
         rw [] >>
         res_tac >>
         simp [] >>
         qexists_tac `res''''` >>
         qexists_tac `s2''''` >>
         simp [] >>
         imp_res_tac cEval_length_imp >>
         `LENGTH vs' =  LENGTH [x1]` by metis_tac [intro_multi_length] >>
         `HD vs' = HD a`
               by (Cases_on `vs'` >>
                   Cases_on `a` >>
                   fs [] >>
                   rw [] >>
                   fs [val_rel_cases, norm_closure_def]) >>
         fs [] >>
         rw [] >>
         fs []) >>
     fs [res_rel_cases] >>
     rw [])
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     Cases_on `cEval (xs,env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [res_rel_cases] >>
     rw [] >>
     `LIST_REL val_rel (a++env) (vs'++env'')` by metis_tac [EVERY2_APPEND] >>
     last_x_assum (qspecl_then [`s2'`, `vs'++env''`] mp_tac) >>
     rw [] >>
     metis_tac [intro_multi_sing])
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     Cases_on `cEval ([x1],env,s)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [res_rel_cases] >>
     rw [intro_multi_sing] >>
     imp_res_tac cEval_length_imp >>
     `LENGTH vs' =  LENGTH [x1]` by metis_tac [intro_multi_length] >>
     Cases_on `vs'` >>
     Cases_on `a` >>
     fs [] >>
     rw [])
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     Cases_on `cEval ([x1],env,s1)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [res_rel_cases] >>
     rw [intro_multi_sing])
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
     `?num_args' e'. collect_args num_args exp = (num_args', e')` by metis_tac [pair_CASES] >>
     simp [] >>
     `num_args' ≤ max_app ∧ num_args ≤ num_args'` by metis_tac [collect_args_more] >>
     simp [] >>
     rw [val_rel_cases] >>
     simp [cl_ok_def, norm_closure_def, inferPropsTheory.remove_pair_lem] >>
     metis_tac [intro_multi_sing, norm_exp_thm, HD, pair_CASES])
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
 >- (fs [cEval_def, intro_multi_def] >>
     rw [] >>
     simp [cEval_def, intro_multi_def] >>
     fs [] >>
     Cases_on `s.clock = 0` >>
     fs []
     >- (fs [state_rel_def] >>
         rw [res_rel_cases]) >>
     `state_rel (dec_clock 1 s) (dec_clock 1 s1')`
                by (fs [state_rel_def] >> rw [dec_clock_def]) >>
     res_tac >>
     `s1'.clock ≠ 0` by (fs [state_rel_def] >> metis_tac []) >>
     metis_tac [intro_multi_sing])
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def] >>
     Cases_on `cEval (xs,env,s1)` >>
     fs [] >>
     Cases_on `q` >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [res_rel_cases] >>
     rw [] >>
     Cases_on `find_code dest a r.code` >>
     fs [] >>
     PairCases_on `x` >>
     fs [] >>
     rw [] >>
     (*`find_code dest vs' s2'.code = SOME (x0,x1)` *)
     cheat)
 >- (fs [cEval_def] >>
     Cases_on `res` >>
     fs [res_rel_cases] >>
     metis_tac [])

>- ((* Real application *)
     fs [cEval_def] >>
     qabbrev_tac `args = v41::v42` >>
     rw [] >>
     qabbrev_tac `args' = y::ys` >>
     `SUC (LENGTH v42) = LENGTH args ∧ SUC (LENGTH ys) = LENGTH args'` by rw [Abbr `args`, Abbr `args'`] >>
     fs [] >>
     `LIST_REL val_rel args args'` by metis_tac [LIST_REL_def] >>
     pop_assum mp_tac >>
     ntac 4 (pop_assum kall_tac) >>
     pop_assum mp_tac >>
     ntac 2 (pop_assum kall_tac) >>
     rw [] >>
     Cases_on `dest_closure loc_opt func args`  >>
     fs [] >>

     Cases_on `x` >>
     fs [] >>
     `loc_opt = NONE` by cheat >> (* TODO forbid App SOME in the input *)
     rw []
     >- ((* A partial application on the unoptimised side *)
         imp_res_tac dest_closure_partial_thm >>
         imp_res_tac EVERY2_LENGTH >>
         fs [] >>
         Cases_on `s1.clock < LENGTH args'` >>
         fs [] >>
         rw [] >>
         fs [state_rel_def, res_rel_cases, dec_clock_def] >>
         rfs []) >>
     `s1.clock = s1'.clock` by fs [state_rel_def] >>
     Cases_on `s1'.clock < LENGTH args - LENGTH l0` >>
     fs []
     >- ((* A timeout before running the unoptimised body *)
         rw [res_rel_cases] >>
         first_assum (fn th => mp_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dest_closure_full_thm) th)) >>
         rw [] >>
         rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
         imp_res_tac LIST_REL_LENGTH >>
         simp [] >>
         fs [state_rel_def] >>
         rfs [] >>
         simp [LENGTH_BUTLASTN]) >>
     imp_res_tac LIST_REL_LENGTH >>
     fs [NOT_LESS] >>
     first_assum (fn th => mp_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dest_closure_full_thm) th)) >>
     rw [] >>
     rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
     simp []

     >- ((* The optimised code gives a partial function application *)
         BasicProvers.VAR_EQ_TAC >>
         fs [add_args_def, cEval_def] >>
         Cases_on `num_args' ≤ max_app ∧ num_args' ≠ 0` >>
         fs [] >>
         fs [] >>
         Cases_on `clos_env (dec_clock (LENGTH args' − LENGTH l0) s1).restrict_envs fvs' l` >>
         fs [] >>
         fs [] >>
         Cases_on `l0` >>
         fs [] >>
         simp []
         >- (fs [cEval_def] >>
             rw [res_rel_cases]
             >- fs [state_rel_def, dec_clock_def] >>
             simp [Once val_rel_cases] >>
             qpat_assum `val_rel func func'` mp_tac >>
             simp [Once val_rel_cases] >>
             rw [] >>
             fs [add_args_def] >>
             rw []

             *)


     (*
     * OLD VALUE RELATION
val (val_rel_rules, val_rel_ind, val_rel_cases) = Hol_reln `
(!n.
  val_rel (Number n) (Number n)) ∧
(!n vs vs'.
  LIST_REL val_rel vs vs'
  ⇒
  val_rel (Block n vs) (Block n vs')) ∧
(!n.
  val_rel (RefPtr n) (RefPtr n)) ∧
(!num_args' e' e args' args env env' loc num_args extra extra'.
  LIST_REL val_rel args args' ∧
  LIST_REL val_rel env env' ∧
  LIST_REL val_rel extra extra' ∧
  exp_rel (num_args,e) (num_args',e')
  ⇒
  val_rel (Closure loc args (extra++env) num_args e)
          (Closure loc (extra'++args') env' num_args' e')) ∧
(!args args' env env' funs funs' i extra extra'.
  LIST_REL val_rel args args' ∧
  LIST_REL val_rel env env' ∧
  LIST_REL val_rel extra extra' ∧
  LIST_REL exp_rel funs funs'
  ⇒
  val_rel (Recclosure loc args (extra++env) funs i)
          (Recclosure loc (extra'++args') env' funs' i)) ∧
(∀args args' env env' funs funs' i loc.
  LIST_REL val_rel args args' ∧
  LIST_REL val_rel env env' ∧
  LIST_REL val_rel extra extra' ∧
  LIST_REL exp_rel funs funs' ∧
  i < LENGTH funs ∧
  EL i funs = (num_args, e)
  ⇒
  val_rel (Closure (loc+i) args (GENLIST (Recclosure loc [] env funs) (LENGTH funs) ++ env) num_args e)
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

val dest_closure_partial_thm = Q.prove (
`!loc f args res f' args' res' v.
  dest_closure NONE f args = SOME (Partial_app v) ∧
  val_rel f f' ∧
  LIST_REL val_rel args args'
  ⇒
  ?v'.
    val_rel v v' ∧
    dest_closure NONE f' args' = SOME (Partial_app v')`,
 rw [dest_closure_def] >>
 ect >>
 fs [Once val_rel_cases, LET_THM] >>
 rw [] >>
 fs [check_loc_def] >>
 imp_res_tac EVERY2_LENGTH >>
 fs [exp_rel_def] >>
 TRY decide_tac
 >- metis_tac [EVERY2_APPEND]
 >- (
     `exp_rel (EL n funs) (EL n l1)` by fs [LIST_REL_EL_EQN] >>
     Cases_on `EL n l1` >>
     Cases_on `EL n funs` >>
     fs [exp_rel_def] >>
     rw [] >>
     fs [] >>
     TRY decide_tac >>
     MAP_EVERY qexists_tac [`env`, `funs`] >>
     rw [] >>
     metis_tac [EVERY2_APPEND]) >>
 Cases_on `EL n l1'` >>
 fs [LET_THM] >>
 ect >>
 fs [] >>
 rw [] >>
 fs [LIST_REL_EL_EQN] >>
 `n < LENGTH l1` by decide_tac >>
 res_tac >>
 pop_assum mp_tac >>
 Cases_on `EL n l1` >>
 simp [exp_rel_def] >>
 rw [] >>
 `n' < LENGTH args' ∨ LENGTH args' ≤ n'` by decide_tac >>
 rw [EL_APPEND1, EL_APPEND2] >>
 first_x_assum match_mp_tac >>
 decide_tac);

val lastn_lemma = Q.prove (
`!l n1 n2 n3.
  n3 ≤ n2 ∧
  n2 ≤ n1 ∧
  n2-n3 ≤ LENGTH l ∧
  n1-n3 ≤ LENGTH l
  ⇒
  LASTN (n1 - n3) l = LASTN (n1 - n2) (BUTLASTN (n2 - n3) l) ++ LASTN (n2 - n3) l`,
 recInduct SNOC_INDUCT >>
 rw [] >>
 Cases_on `n1-n3` >>
 rw [LASTN]
 >- (`n2-n3 = 0` by decide_tac >>
     `n1-n2 = 0` by decide_tac >>
     rw [BUTLASTN, LASTN])
 >- (`n2-n3 = 0` by decide_tac >>
     `n1-n2 = 0` by decide_tac >>
     rw [BUTLASTN, LASTN])
 >- full_simp_tac (srw_ss()++ARITH_ss) [BUTLASTN, LASTN]
 >- (`n1 = n2 ∧ n2 = n3` by decide_tac >>
     rw [BUTLASTN, LASTN])
 >- (`n1 = n2 ∧ n2 = n3` by decide_tac >>
     rw [BUTLASTN, LASTN]) >>
 rw_tac std_ss [LASTN, GSYM SNOC_APPEND] >>
 Cases_on `n2-n3` >>
 rw [LASTN, BUTLASTN] >>
 fs []
 >- (`n2 = n3` by decide_tac >>
     rw_tac std_ss [LASTN, GSYM SNOC_APPEND]) >>
 rw_tac std_ss [BUTLASTN, GSYM SNOC_APPEND, LASTN] >>
 fs [] >>
 first_x_assum (qspecl_then [`n1`, `n2`, `n3+1`] mp_tac) >>
 rw [] >>
 rev_full_simp_tac (srw_ss()++ARITH_ss) [] >>
 `n = n1 -(n3 + 1)` by decide_tac >>
 `n' = n2 -(n3 + 1)` by decide_tac >>
 rw []);

val dest_closure_full_thm = Q.prove (
`!f args f' args' e env rest_args.
  dest_closure NONE f args = SOME (Full_app e env rest_args) ∧
  val_rel f f' ∧
  LIST_REL val_rel args args'
  ⇒
  (?f'' loc' fvs' num_args' e'.
    e = Fn loc' fvs' num_args' e' ∧
    add_args f' args' = SOME f'' ∧
    dest_closure NONE f' args' = SOME (Partial_app f'')) ∨
  (∃e' n n' env' rest_args'.
    LIST_REL val_rel env env' ∧
    LIST_REL val_rel rest_args rest_args' ∧
    exp_rel (n,e) (n',e') ∧
    n'-n ≤ LENGTH rest_args' ∧
    dest_closure NONE f' args' =
      SOME (Full_app e' (LASTN (n'-n) rest_args' ++ env') (BUTLASTN (n'-n) rest_args')))`,
 rw [dest_closure_def] >>
 ect >>
 fs [Once val_rel_cases, LET_THM] >>
 rw [] >>
 fs [check_loc_def, NOT_LESS] >>
 imp_res_tac EVERY2_LENGTH
 >- (qabbrev_tac `num_args1 = n' - LENGTH l'` >>
     qabbrev_tac `num_args2 = n - LENGTH l` >>
     `num_args1 ≤ LENGTH args` by simp [Abbr `num_args1`] >>
     `num_args2 ≤ LENGTH args'` by simp [Abbr `num_args2`] >>
     rw [DROP_REVERSE, TAKE_REVERSE, LASTN_MAP, ETA_THM, BUTLASTN_MAP] >>
     MAP_EVERY qexists_tac [`n'`, `n`, `LASTN num_args1 args'++l++l0`,
                            `BUTLASTN num_args1 args'`] >>
     rw []
     >- (rfs [] >>
         `LIST_REL val_rel (LASTN num_args1 args) (LASTN num_args1 args')`
                by (rfs [LIST_REL_EL_EQN, LENGTH_LASTN] >>
                    rw [] >>
                    `n'' + (LENGTH args' - num_args1) < LENGTH args'` by decide_tac >>
                    rw [LASTN_DROP, EL_DROP]) >>
         metis_tac [EVERY2_APPEND])
     >- (rfs [] >>
         rw [LIST_REL_EL_EQN, LENGTH_BUTLASTN] >>
         `n'' + num_args1 < LENGTH args'` by simp [Abbr `num_args1`] >>
         fs [LIST_REL_EL_EQN, el_butlastn] >>
         first_x_assum match_mp_tac >>
         decide_tac)
     >- (unabbrev_all_tac >>
         simp [LENGTH_BUTLASTN])
     >- (unabbrev_all_tac >>
         rw [] >>
         match_mp_tac lastn_lemma >>
         simp [] >>
         fs [exp_rel_def])
     >- (`(n-n') + num_args1 ≤ LENGTH args'` by simp [Abbr `num_args1`] >>
         rw [BUTLASTN_BUTLASTN] >>
         unabbrev_all_tac >>
         rw [] >>
         fs [exp_rel_def] >>
         simp []))
 >- fs [exp_rel_def]
 >- (fs [exp_rel_def] >>
     decide_tac)
 >- (rw [add_args_def] >>
     fs [exp_rel_def] >>
     Cases_on `c'` >>
     fs [collect_args_def] >>
     rw [] >>
     fs [intro_multi_def] >>
     decide_tac)
 >- fs [exp_rel_def]
 >- (fs [exp_rel_def] >>
     decide_tac)
 >- cheat
 >- (Cases_on `EL n l1'` >>
     fs [] >>
     Cases_on `q ≤ LENGTH args' + LENGTH l` >>
     fs [] >>
     Cases_on `EL n l1` >>
     simp [add_args_def] >>
     reverse (rw []) >>
     fs [NOT_LESS_EQUAL] >>
     `q ≤ q'` by (fs [LIST_REL_EL_EQN] >> metis_tac [exp_rel_def])
     >- (fs [LIST_REL_EL_EQN] >>
         `exp_rel (q,e) (q',r')` by metis_tac [] >>
         fs [exp_rel_def] >>
         Cases_on `e` >>
         fs [collect_args_def] >>
         rw [] >>
         fs [intro_multi_def] >>
         decide_tac) >>
     qabbrev_tac `num_args1 = q - LENGTH l` >>
     qabbrev_tac `num_args2 = q' - LENGTH l` >>
     `num_args1 ≤ LENGTH args` by simp [Abbr `num_args1`] >>
     `num_args2 ≤ LENGTH args'` by simp [Abbr `num_args2`] >>
     rw [DROP_REVERSE, TAKE_REVERSE, LASTN_MAP, ETA_THM, BUTLASTN_MAP] >>
     MAP_EVERY qexists_tac [`q`, `q'`, `LASTN num_args1 args'++l++GENLIST (Recclosure n0 [] l0 l1) (LENGTH l1)++l0`,
                            `BUTLASTN num_args1 args'`] >>
     rw []
     >- (rfs [] >>
         `LIST_REL val_rel (LASTN num_args1 args) (LASTN num_args1 args')`
                by (rfs [LIST_REL_EL_EQN, LENGTH_LASTN] >>
                    rw [] >>
                    `n' + (LENGTH args' - num_args1) < LENGTH args'` by decide_tac >>
                    rw [LASTN_DROP, EL_DROP]) >>
         `LIST_REL val_rel (GENLIST (Recclosure n0 [] l0' l1') (LENGTH l1)) (GENLIST (Recclosure n0 [] l0 l1) (LENGTH l1))`
                by (rw [LIST_REL_EL_EQN, Once val_rel_cases] >>
                    fs [LIST_REL_EL_EQN]) >>
         metis_tac [EVERY2_APPEND])
     >- (rfs [] >>
         rw [LIST_REL_EL_EQN, LENGTH_BUTLASTN] >>
         `n' + num_args1 < LENGTH args'` by simp [Abbr `num_args1`] >>
         fs [LIST_REL_EL_EQN, el_butlastn] >>
         first_x_assum match_mp_tac >>
         decide_tac)
     >- (fs [LIST_REL_EL_EQN] >>
         metis_tac [])
     >- (unabbrev_all_tac >>
         simp [LENGTH_BUTLASTN])
     >- decide_tac
     >- (unabbrev_all_tac >>
         rw [] >>
         match_mp_tac lastn_lemma >>
         simp [] >>
         fs [exp_rel_def] >>
         fs [LIST_REL_EL_EQN] >>
         metis_tac [exp_rel_def])
     >- (`(q'-q) + num_args1 ≤ LENGTH args'` by simp [Abbr `num_args1`] >>
         rw [BUTLASTN_BUTLASTN] >>
         unabbrev_all_tac >>
         rw [] >>
         fs [LIST_REL_EL_EQN] >>
         `q ≤ q'` by metis_tac [exp_rel_def] >>
         simp [])));

         (*
val run_exp_rel = Q.prove (
`!n e n' e' env env' s s' l.
  LIST_REL val_rel env env' ∧
  state_rel s s' ∧
  exp_rel (n,e) (n',e')
  ⇒
  cEval ([e], env, s) = cEval ([e'], l++env, dec_clock (n' - n) s)`,
 rw [exp_rel_def] >>
 Cases_on `e` >>
 fs [collect_args_def, intro_multi_def]
 *)

 (*
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

 >- ((* Real application *)
     fs [cEval_def] >>
     qabbrev_tac `args = v41::v42` >>
     rw [] >>
     qabbrev_tac `args' = y::ys` >>
     `SUC (LENGTH v42) = LENGTH args ∧ SUC (LENGTH ys) = LENGTH args'` by rw [Abbr `args`, Abbr `args'`] >>
     fs [] >>
     `LIST_REL val_rel args args'` by metis_tac [LIST_REL_def] >>
     pop_assum mp_tac >>
     ntac 4 (pop_assum kall_tac) >>
     pop_assum mp_tac >>
     ntac 2 (pop_assum kall_tac) >>
     rw [] >>
     Cases_on `dest_closure loc_opt func args`  >>
     fs [] >>
     Cases_on `x` >>
     fs [] >>
     `loc_opt = NONE` by cheat >> (* TODO forbid App SOME in the input *)
     rw []
     >- ((* A partial application on the unoptimised side *)
         imp_res_tac dest_closure_partial_thm >>
         imp_res_tac EVERY2_LENGTH >>
         fs [] >>
         Cases_on `s1.clock < LENGTH args'` >>
         fs [] >>
         rw [] >>
         fs [state_rel_def, res_rel_cases, dec_clock_def] >>
         rfs []) >>
     `s1.clock = s1'.clock` by fs [state_rel_def] >>
     Cases_on `s1'.clock < LENGTH args - LENGTH l0` >>
     fs []
     >- ((* A timeout before running the unoptimised body *)
         rw [res_rel_cases] >>
         first_assum (fn th => mp_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dest_closure_full_thm) th)) >>
         rw [] >>
         rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
         imp_res_tac LIST_REL_LENGTH >>
         simp [] >>
         fs [state_rel_def] >>
         rfs [] >>
         simp [LENGTH_BUTLASTN]) >>
     imp_res_tac LIST_REL_LENGTH >>
     fs [NOT_LESS] >>
     first_assum (fn th => mp_tac (MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] dest_closure_full_thm) th)) >>
     rw [] >>
     rpt (pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th))) >>
     simp []

     >- ((* The optimised code gives a partial function application *)
         BasicProvers.VAR_EQ_TAC >>
         fs [add_args_def, cEval_def] >>
         Cases_on `num_args' ≤ max_app ∧ num_args' ≠ 0` >>
         fs [] >>
         fs [] >>
         Cases_on `clos_env (dec_clock (LENGTH args' − LENGTH l0) s1).restrict_envs fvs' l` >>
         fs [] >>
         fs [] >>
         Cases_on `l0` >>
         fs [] >>
         simp []
         >- (fs [cEval_def] >>
             rw [res_rel_cases]
             >- fs [state_rel_def, dec_clock_def] >>
             simp [Once val_rel_cases] >>
             qpat_assum `val_rel func func'` mp_tac >>
             simp [Once val_rel_cases] >>
             rw [] >>
             fs [add_args_def] >>
             rw []





             *)
             *)

val _ = export_theory ();

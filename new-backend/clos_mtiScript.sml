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

val val_comp_def = tDefine "val_comp" `
(val_comp (Number n) = Number n) ∧
(val_comp (Block n vs) = Block n (MAP val_comp vs)) ∧
(val_comp (RefPtr n) = RefPtr n) ∧
(val_comp (Closure loc args env num_args e) =
  let (num_args', e') = collect_args num_args e in
    Closure loc (MAP val_comp args) (MAP val_comp env) num_args' (HD (intro_multi [e']))) ∧
(val_comp (Recclosure loc args env funs i) =
  Recclosure loc (MAP val_comp args) (MAP val_comp env)
             (MAP (\(num_args, e). 
                         let (num_args', e') = collect_args num_args e in
                           (num_args', HD (intro_multi [e'])))
                  funs)
             i)`
(WF_REL_TAC `measure clos_val_size` >>
 rw [] >>
 fs [MEM_EL] >>
 rw [] >>
 imp_res_tac clos_val_size_el >>
 decide_tac);

val res_comp_def = Define `
(res_comp (Result vs) = Result (MAP val_comp vs)) ∧
(res_comp (Exception vs) = Exception (val_comp vs)) ∧
(res_comp x = x)`;

val state_comp_def = Define `
state_comp (s:clos_state) =
  s with <| globals := MAP (OPTION_MAP val_comp) s.globals;
            refs := (\vr. case vr of ValueArray vs => ValueArray (MAP val_comp vs)
                                   | ByteArray ws => ByteArray ws)
                    o_f s.refs;
            code := (\(n,e). (n, HD (intro_multi [e]))) o_f s.code |>`;

val lookup_vars_map = Q.prove (
`!vs env f. lookup_vars vs (MAP f env) = OPTION_MAP (MAP f) (lookup_vars vs env)`,
 Induct_on `vs` >>
 rw [lookup_vars_def] >>
 ect >>
 fs [EL_MAP]);

val collect_args_more = Q.prove (
`!num_args e num_args' e'.
  num_args ≤ max_app ∧
  collect_args num_args e = (num_args', e')
  ⇒
  num_args ≤ num_args' ∧ num_args' ≤ max_app`,
 ho_match_mp_tac (fetch "-" "collect_args_ind") >>
 rw [collect_args_def] >>
 rw [] >>
 res_tac >>
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

val dest_cl_res_comp_def = Define `
(dest_cl_res_comp (Partial_app v) = Partial_app (val_comp v)) ∧
(dest_cl_res_comp (Full_app e env args) = 
  Full_app (HD (intro_multi [e])) (MAP val_comp env) (MAP val_comp args))`;

  (*
val dest_closure_thm = Q.prove (
`!loc f args res.
  dest_closure NONE f args = SOME res
  ⇒
  dest_closure NONE (val_comp f) (MAP val_comp args) = SOME (dest_cl_res_comp res)`,

 rw [dest_closure_def] >>
 Cases_on `f` >>
 rw [val_comp_def] >>
 fs [check_loc_def] >>
 rw [] >>
 ect >>
 fs [] >>
 imp_res_tac collect_args_more >>
 

 fs [val_comp_def] >>
 Cases_on `collect_args n c` >>
 Cases_on `collect_args n' c` >>
 Cases_on `collect_args n' c'` >>
 fs [LET_THM, dest_cl_res_comp_def] >>
 rw [] >>
 fs [] >>
 TRY (`n - LENGTH l' ≤ LENGTH args` by decide_tac) >>
 TRY (`n - LENGTH l' ≤ LENGTH (MAP val_comp args)` by (rw_tac list_ss [] >> NO_TAC)) >>
 TRY (`n' - LENGTH l' ≤ LENGTH args` by decide_tac) >>
 TRY (`n' - LENGTH l' ≤ LENGTH (MAP val_comp args)` by (rw_tac list_ss [] >> NO_TAC)) >>
 rw [DROP_REVERSE, TAKE_REVERSE, LASTN_MAP, ETA_THM, BUTLASTN_MAP] >>
 fs [] >>
 fs [val_comp_def, LET_THM, ETA_THM]

val intro_multi_correct = Q.prove (
`(!tmp es env s1 res s2.
   tmp = (es,env,s1) ∧
   cEval tmp = (res, s2) ∧
   res ≠ Error
   ⇒
   cEval (intro_multi es, MAP val_comp env, state_comp s1) = (res_comp res, state_comp s2)) ∧
 (!loc_opt func args s1 res s2.
   cEvalApp loc_opt func args s1 = (res, s2) ∧
   res ≠ Error
   ⇒
   cEvalApp loc_opt (val_comp func) (MAP val_comp args) (state_comp s1) = (res_comp res, state_comp s2))`,

 ho_match_mp_tac cEval_ind >>
 rpt strip_tac
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def, res_comp_def])
 >- cheat
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def, res_comp_def] >>
     fs [] >>
     rw [res_comp_def, EL_MAP])
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
     rw [res_comp_def] >>
     fs [state_comp_def, clos_env_def] >>
     ect >>
     fs [val_comp_def, lookup_vars_map] >>
     rw [ETA_THM] >>
     imp_res_tac collect_args_more  >>
     decide_tac)
 >- cheat
 >- (fs [cEval_def, intro_multi_def] >>
     rw [cEval_def, intro_multi_def, res_comp_def] >>
     fs [intro_multi_length] >>
     ect >>
     fs [] >>
     rw [] >>
     rfs [res_comp_def] >>
     rw [] >>
     fs [] >>
     rfs [] >>
     `?x1'. intro_multi [x1] = [x1']` by metis_tac [intro_multi_sing] >>
     fs [] >>
     rfs [] >>
     imp_res_tac cEval_length_imp >>
     fs [] >>
     Cases_on `a''` >>
     fs [] >>
     Cases_on `a` >>
     fs [] >>
     metis_tac [])
 >- cheat
 >- cheat
 >- (fs [cEval_def] >>
     Cases_on `res` >>
     fs [res_comp_def] >>
     metis_tac [MAP])

 >- (fs [cEval_def] >>
     ect >>
     fs []

     rw []
     *)


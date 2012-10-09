open preamble MiniMLTheory

val _ = new_theory "evaluateEquations"

(* functional equations for evaluate *)

val evaluate_raise = Q.store_thm (
"evaluate_raise",
`!cenv env err bv.
  (evaluate cenv env (Raise err) bv = (bv = Rerr (Rraise err)))`,
rw [Once evaluate_cases]);

val evaluate_lit = Q.store_thm(
"evaluate_lit",
`!cenv env l r.
  (evaluate cenv env (Lit l) r = (r = Rval (Litv l)))`,
rw [Once evaluate_cases]);

val evaluate_var = store_thm(
"evaluate_var",
``∀cenv env n r. evaluate cenv env (Var n) r =
  (∃v. (lookup n env = SOME v) ∧ (r = Rval v)) ∨
  ((lookup n env = NONE) ∧ (r = Rerr Rtype_error))``,
rw [Once evaluate_cases] >>
metis_tac [])

val evaluate_fun = store_thm(
"evaluate_fun",
``∀cenv env n e r. evaluate cenv env (Fun n e) r = (r = Rval (Closure env n e))``,
rw [Once evaluate_cases])

val _ = export_rewrites["evaluate_raise","evaluate_lit","evaluate_fun"];

val evaluate_con = Q.store_thm(
"evaluate_con",
`!cenv env cn es r.
  (evaluate cenv env (Con cn es) r =
   if do_con_check cenv cn (LENGTH es) then
     (∃err. evaluate_list cenv env es (Rerr err) ∧
            (r = Rerr err)) ∨
     (∃vs. evaluate_list cenv env es (Rval vs) ∧
           (r = Rval (Conv cn vs)))
   else (r = Rerr Rtype_error))`,
rw [Once evaluate_cases] >>
metis_tac []);

val evaluate_app = store_thm(
"evaluate_app",
``∀cenv env op e1 e2 r. evaluate cenv env (App op e1 e2) r =
  (∃v1 v2 env' e. evaluate cenv env e1 (Rval v1) ∧ (evaluate cenv env e2 (Rval v2)) ∧
                  (do_app env op v1 v2 = SOME (env',e)) ∧
                  evaluate cenv env' e r) ∨
  (∃v1 v2. evaluate cenv env e1 (Rval v1) ∧ (evaluate cenv env e2 (Rval v2)) ∧
           (do_app env op v1 v2 = NONE) ∧
           (r = Rerr Rtype_error)) ∨
  (∃v1 err. evaluate cenv env e1 (Rval v1) ∧ (evaluate cenv env e2 (Rerr err)) ∧
            (r = Rerr err)) ∨
  (∃err. evaluate cenv env e1 (Rerr err) ∧
         (r = Rerr err))``,
rw[Once evaluate_cases] >>
metis_tac [])

val evaluate'_raise = store_thm(
"evaluate'_raise",
``∀env err r. evaluate' env (Raise err) r = (r = Rerr (Rraise err))``,
rw [Once evaluate'_cases])

val evaluate'_lit = store_thm(
"evaluate'_lit",
``∀env l r. evaluate' env (Lit l) r = (r = Rval (Litv l))``,
rw [Once evaluate'_cases])

val evaluate'_fun = store_thm(
"evaluate'_fun",
``∀env n e r. evaluate' env (Fun n e) r = (r = Rval (Closure env n e))``,
rw [Once evaluate'_cases])

val _ = export_rewrites["evaluate'_raise","evaluate'_lit","evaluate'_fun"]

val evaluate'_con = store_thm(
"evaluate'_con",
``∀env cn es r. evaluate' env (Con cn es) r =
  (∃err. evaluate_list' env es (Rerr err) ∧ (r = Rerr err)) ∨
  (∃vs. evaluate_list' env es (Rval vs) ∧ (r = Rval (Conv cn vs)))``,
rw [Once evaluate'_cases] >>
metis_tac [])

val evaluate'_var = store_thm(
"evaluate'_var",
``∀env n r. evaluate' env (Var n) r =
  (∃v. (lookup n env = SOME v) ∧ (r = Rval v)) ∨
  ((lookup n env = NONE) ∧ (r = Rerr Rtype_error))``,
rw [Once evaluate'_cases] >>
metis_tac [])

val evaluate_list'_thm = store_thm(
"evaluate_list'_thm",
``∀env r.
  (evaluate_list' env [] r = (r = Rval [])) ∧
  (∀e es. evaluate_list' env (e::es) r =
   (∃v vs. evaluate' env e (Rval v) ∧ evaluate_list' env es (Rval vs) ∧
           (r = Rval (v::vs))) ∨
   (∃err. evaluate' env e (Rerr err) ∧
          (r = Rerr err)) ∨
   (∃v err. evaluate' env e (Rval v) ∧ evaluate_list' env es (Rerr err) ∧
            (r = Rerr err)))``,
rw[] >-
  rw[Once evaluate'_cases] >>
rw[EQ_IMP_THM] >- (
  pop_assum (mp_tac o (SIMP_RULE (srw_ss()) [Once evaluate'_cases])) >>
  rw [] >> metis_tac[] )
>- rw [evaluate'_rules]
>- rw [evaluate'_rules] >>
rw[Once evaluate'_cases] >>
metis_tac [])

val evaluate'_app = store_thm(
"evaluate'_app",
``∀env op e1 e2 r. evaluate' env (App op e1 e2) r =
  (∃v1 v2 env' e. evaluate' env e1 (Rval v1) ∧ (evaluate' env e2 (Rval v2)) ∧
                  (do_app env op v1 v2 = SOME (env',e)) ∧
                  evaluate' env' e r) ∨
  (∃v1 v2. evaluate' env e1 (Rval v1) ∧ (evaluate' env e2 (Rval v2)) ∧
           (do_app env op v1 v2 = NONE) ∧
           (r = Rerr Rtype_error)) ∨
  (∃v1 err. evaluate' env e1 (Rval v1) ∧ (evaluate' env e2 (Rerr err)) ∧
            (r = Rerr err)) ∨
  (∃err. evaluate' env e1 (Rerr err) ∧
         (r = Rerr err))``,
rw[Once evaluate'_cases] >>
metis_tac [])

val evaluate'_log = store_thm(
"evaluate'_log",
``∀env lg e1 e2 r. evaluate' env (Log lg e1 e2) r =
  (∃v1 env' e. evaluate' env e1 (Rval v1) ∧ (do_log lg v1 e2 = SOME e) ∧ (evaluate' env e r)) ∨
  (∃v1. evaluate' env e1 (Rval v1) ∧ (do_log lg v1 e2 = NONE) ∧ (r = Rerr Rtype_error)) ∨
  (∃err. evaluate' env e1 (Rerr err) ∧ (r = Rerr err))``,
rw[Once evaluate'_cases] >>
metis_tac [])

val _ = export_theory ()

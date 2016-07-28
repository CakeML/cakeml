open preamble closLangTheory;

val _ = new_theory "clos_mti";

val collect_args_def = Define `
  (collect_args max_app num_args (Fn NONE NONE num_args' e) =
    if num_args + num_args' ≤ max_app then
      collect_args max_app (num_args + num_args') e
    else
      (num_args, Fn NONE NONE num_args' e)) ∧
  (collect_args max_app num_args e = (num_args, e))`;

val collect_args_ind = theorem "collect_args_ind";

val collect_args_size = Q.prove (
  `!max_app num_args e num_args' e'.
    (num_args', e') = collect_args max_app num_args e ⇒
    num_args' + exp_size e' ≤ num_args + exp_size e`,
   ho_match_mp_tac collect_args_ind >>
   srw_tac[][collect_args_def, exp_size_def] >>
   srw_tac[][exp_size_def] >>
   res_tac >>
   decide_tac);

val collect_args_more = Q.prove (
  `!max_app num_args e num_args' e'.
    (num_args', e') = collect_args max_app num_args e
    ⇒
    num_args ≤ num_args'`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def] >>
  srw_tac[][] >>
  res_tac >>
  decide_tac);

val collect_args_zero = Q.store_thm("collect_args_zero",
  `!max_app num_args e e'.
    collect_args max_app num_args e = (0, e')
    ⇒
    num_args = 0`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def] >>
  srw_tac[][collect_args_def] >>
  full_simp_tac(srw_ss())[]);

val collect_apps_def = Define `
  (collect_apps max_app args (App NONE e es) =
    if LENGTH args + LENGTH es ≤ max_app then
      collect_apps max_app (args ++ es) e
    else
      (args, App NONE e es)) ∧
  (collect_apps max_app args e = (args, e))`;

val collect_apps_ind = theorem "collect_apps_ind";

val exp3_size_append = Q.prove (
`!es1 es2. exp3_size (es1 ++ es2) = exp3_size es1 + exp3_size es2`,
 Induct_on `es1` >>
 simp [exp_size_def]);

val collect_apps_size = Q.prove (
  `!max_app args e args' e'.
    (args', e') = collect_apps max_app args e ⇒
    exp3_size args' + exp_size e' ≤ exp3_size args + exp_size e`,
   ho_match_mp_tac collect_apps_ind >>
   simp [collect_apps_def, exp_size_def, basicSizeTheory.option_size_def] >>
   srw_tac[][] >>
   simp [exp_size_def, basicSizeTheory.option_size_def] >>
   res_tac >>
   full_simp_tac(srw_ss())[exp_size_def, exp3_size_append] >>
   decide_tac);

val collect_apps_more = Q.prove (
  `!max_app args e args' e'.
    (args', e') = collect_apps max_app args e
    ⇒
    LENGTH args ≤ LENGTH args'`,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def] >>
  srw_tac[][] >>
  res_tac >>
  decide_tac);

val intro_multi_def = tDefine "intro_multi"`
  (intro_multi max_app [] = []) ∧
  (intro_multi max_app (e1::e2::es) =
    HD (intro_multi max_app [e1]) :: HD (intro_multi max_app [e2]) :: intro_multi max_app es) ∧
  (intro_multi max_app [Var n] = [Var n]) ∧
  (intro_multi max_app [If e1 e2 e3] =
   [If (HD (intro_multi max_app [e1]))
       (HD (intro_multi max_app [e2]))
       (HD (intro_multi max_app [e3]))]) ∧
  (intro_multi max_app [Let es e] =
    [Let (intro_multi max_app es) (HD (intro_multi max_app [e]))]) ∧
  (intro_multi max_app [Raise e] =
    [Raise (HD (intro_multi max_app [e]))]) ∧
  (intro_multi max_app [Handle e1 e2] =
    [Handle (HD (intro_multi max_app [e1])) (HD (intro_multi max_app [e2]))]) ∧
  (intro_multi max_app [Tick e] =
    [Tick (HD (intro_multi max_app [e]))]) ∧
  (intro_multi max_app [Call ticks n es] =
    [Call ticks n (intro_multi max_app es)]) ∧
  (intro_multi max_app [App NONE e es] =
    let (es', e') = collect_apps max_app es e in
      [App NONE (HD (intro_multi max_app [e'])) (intro_multi max_app es')]) ∧
  (intro_multi max_app [App (SOME l) e es] =
    [App (SOME l) (HD (intro_multi max_app [e])) (intro_multi max_app es)]) ∧
  (intro_multi max_app [Fn NONE NONE num_args e] =
    let (num_args', e') = collect_args max_app num_args e in
      [Fn NONE NONE num_args' (HD (intro_multi max_app [e']))]) ∧
  (intro_multi max_app [Fn loc fvs num_args e] =
      [Fn loc fvs num_args (HD (intro_multi max_app [e]))]) ∧
  (intro_multi max_app [Letrec NONE NONE funs e] =
    [Letrec NONE NONE (MAP (\(num_args, e).
                            let (num_args', e') = collect_args max_app num_args e in
                              (num_args', HD (intro_multi max_app [e'])))
                          funs)
            (HD (intro_multi max_app [e]))]) ∧
  (intro_multi max_app [Letrec (SOME loc) fvs funs e] =
     [Letrec (SOME loc) fvs funs (HD (intro_multi max_app [e]))]) ∧
  (intro_multi max_app [Letrec NONE (SOME fvs) funs e] =
     [Letrec NONE (SOME fvs) funs (HD (intro_multi max_app [e]))]) ∧
  (intro_multi max_app [Op op es] =
    [Op op (intro_multi max_app es)])`
  (WF_REL_TAC `measure (exp3_size o SND)` >>
   srw_tac [ARITH_ss] [exp_size_def] >>
   imp_res_tac collect_args_size >>
   imp_res_tac collect_apps_size >>
   TRY decide_tac >>
   `num_args + exp_size e' ≤ exp1_size funs`
           by (Induct_on `funs` >>
               srw_tac[][exp_size_def] >>
               srw_tac[][exp_size_def] >>
               res_tac >>
               decide_tac) >>
   decide_tac);

val intro_multi_ind = theorem "intro_multi_ind";

val intro_multi_length = Q.store_thm("intro_multi_length",
  `!max_app es. LENGTH (intro_multi max_app es) = LENGTH es`,
  recInduct intro_multi_ind >>
  srw_tac[][intro_multi_def] >>
  Cases_on `intro_multi max_app [e1]` >>
  full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[]);

val intro_multi_sing = Q.store_thm ("intro_multi_sing",
  `!e max_app. ?e'. intro_multi max_app [e] = [e']`,
  Induct_on `e` >>
  srw_tac[][intro_multi_def] >>
  TRY (rename1 `App loc e es` >> Cases_on `loc`) >>
  TRY (rename1 `Fn loc vars num_args e` >> Cases_on `loc` >> Cases_on `vars`) >>
  TRY (rename1 `Letrec locopt _ _ _` >> Cases_on `locopt`) >>
  TRY (rename1 `Letrec _ fvopt _ _` >> Cases_on `fvopt`) >>
  srw_tac[][intro_multi_def] >>
  TRY (Cases_on `collect_args max_app num_args e`) >>
  TRY (Cases_on `collect_apps max_app es e`) >>
  full_simp_tac(srw_ss())[]);

val collect_args_idem = Q.store_thm (
  "collect_args_idem",
  `!max_app num_args e num_args' e'.
    collect_args max_app num_args e = (num_args', e')
    ⇒
    collect_args max_app num_args' (HD (intro_multi max_app [e'])) = (num_args', (HD (intro_multi max_app [e'])))`,
  ho_match_mp_tac collect_args_ind >>
  srw_tac[][collect_args_def, intro_multi_def] >>
  srw_tac[][collect_args_def, intro_multi_def] >>
  full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
  >- (
    `num_args'' < num_args'` by decide_tac >>
    `num_args' ≤ num_args''` by metis_tac [collect_args_more] >>
    full_simp_tac (srw_ss()++ARITH_ss) [])
 >- (rename1 `App loc e es` >>
     Cases_on `loc` >>
     srw_tac[][collect_args_def, intro_multi_def] >>
     srw_tac[][collect_args_def, intro_multi_def])
 >- (rename1 `Letrec locopt fvsopt` >>
     Cases_on `locopt` >> Cases_on `fvsopt` >>
     rw[intro_multi_def, collect_args_def]));

val collect_apps_idem = Q.store_thm (
  "collect_apps_idem",
  `!max_app args e args' e'.
    collect_apps max_app args e = (args', e')
    ⇒
    collect_apps max_app (intro_multi max_app args') (HD (intro_multi max_app [e'])) = (intro_multi max_app args', (HD (intro_multi max_app [e'])))`,
  ho_match_mp_tac collect_apps_ind >>
  srw_tac[][collect_apps_def, intro_multi_def] >>
  srw_tac[][collect_apps_def, intro_multi_def] >>
  full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
  >- (
    full_simp_tac(srw_ss())[intro_multi_length] >>
    `LENGTH es' < LENGTH es` by decide_tac >>
    `LENGTH es ≤ LENGTH es'` by metis_tac [collect_apps_more] >>
    full_simp_tac (srw_ss()++ARITH_ss) []) >>
 FIRST [
   rename1 `Fn loc vars _ _` >>
   Cases_on `loc` >>
   Cases_on `vars` >>
   srw_tac[][collect_apps_def, intro_multi_def] >>
   srw_tac[][collect_apps_def, intro_multi_def]
 ,
   rename1 `Letrec locopt fvsopt` >>
   Cases_on `locopt` >> Cases_on `fvsopt` >>
   simp[collect_apps_def, intro_multi_def]
 ]);

val intro_multi_idem = Q.store_thm("intro_multi_idem",
  `!max_app e. intro_multi max_app (intro_multi max_app e) = intro_multi max_app e`,
  ho_match_mp_tac intro_multi_ind >>
  srw_tac[][intro_multi_def] >>
  srw_tac[][intro_multi_def]
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
  >- metis_tac [intro_multi_sing, HD, collect_apps_idem, PAIR_EQ]
  >- metis_tac [intro_multi_sing, HD]
  >- metis_tac [intro_multi_sing, HD, collect_args_idem, PAIR_EQ]
  >- metis_tac [intro_multi_sing, HD]
  >- metis_tac [intro_multi_sing, HD]
  >- (srw_tac[][LET_THM, MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
      srw_tac[][MAP_EQ_f] >>
      PairCases_on `x` >>
      simp [] >>
      Cases_on `collect_args max_app x0 x1` >>
      simp [] >>
      res_tac >>
      rev_full_simp_tac(srw_ss())[] >>
      metis_tac [intro_multi_sing, HD, collect_args_idem, PAIR_EQ, FST, SND])
  >- metis_tac [intro_multi_sing, HD]
  >- metis_tac [intro_multi_sing, HD]
  >- metis_tac [intro_multi_sing, HD]);

val compile_def = Define`
  compile F max_app exps = exps /\
  compile T max_app exps = intro_multi max_app exps`

val _ = export_theory()

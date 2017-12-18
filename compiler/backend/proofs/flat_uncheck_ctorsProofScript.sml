open preamble;
open flatLangTheory flatSemTheory flatPropsTheory flat_uncheck_ctorsTheory;

val _ = new_theory "flat_uncheck_ctorsProof";

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!lit.
    v_rel (flatSem$Litv lit) (flatSem$Litv lit)) ∧
  (!cn vs vs' t.
    LIST_REL v_rel vs vs'
    ⇒
    v_rel (flatSem$Conv cn vs) (flatSem$Conv (SOME (the (0,t) cn)) vs')) ∧
  (!env x e env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env env'
    ⇒
    v_rel (flatSem$Closure env x e) (flatSem$Closure env' x (HD (compile [e])))) ∧
  (!env funs x env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env env'
    ⇒
    v_rel (Recclosure env funs x)
      (Recclosure env' (MAP (\(f,x,e). (f, x, HD (compile [e]))) funs) x)) ∧
  (!loc.
    v_rel (Loc loc) (Loc loc)) ∧
  (!vs vs'.
    LIST_REL v_rel vs vs'
    ⇒
    v_rel (Vectorv vs) (Vectorv vs'))`;

val (sv_rel_rules, sv_rel_ind, sv_rel_cases) = Hol_reln `
  (!v v'.
    v_rel v v'
    ⇒
    sv_rel (Refv v) (Refv v')) ∧
  (!w.
    sv_rel (W8array w) (W8array w)) ∧
  (!vs vs'.
    LIST_REL v_rel vs vs'
    ⇒
    sv_rel (Varray vs) (Varray vs'))`;

val (s_rel_rules, s_rel_ind, s_rel_cases) = Hol_reln `
  (!s s'.
    s.clock = s'.clock ∧
    LIST_REL sv_rel s.refs s'.refs ∧
    s.ffi = s'.ffi ∧
    LIST_REL (OPTION_REL v_rel) s.globals s'.globals
    ⇒
    s_rel s s')`;

val (env_rel_rules, env_rel_ind, env_rel_cases) = Hol_reln `
  (!env env'.
    LIST_REL (\(x,v1) (y,v2). x = y ∧ v_rel v1 v2) env.v env'.v ∧
    env.exh_pat = env'.exh_pat ∧
    env.check_ctor ∧
    ~env'.check_ctor
    ⇒
    env_rel env env')`;

val (result_rel_rules, result_rel_ind, result_rel_cases) = Hol_reln `
  (∀v v'.
    f v v'
    ⇒
    result_rel f (Rval v) (Rval v')) ∧
  (∀v v'.
    v_rel v v'
    ⇒
    result_rel f (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
  (!a.
    result_rel f (Rerr (Rabort a)) (Rerr (Rabort a)))`;

val compile_exp_correct = Q.prove (
  `(∀env (s : 'a flatSem$state) es s' r s1 env'.
    evaluate env s es = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1
    ⇒
    ?s1' r1.
      result_rel (LIST_REL v_rel) r r1 ∧
      s_rel s' s1' ∧
      evaluate env' s1 (compile es) = (s1', r1)) ∧
   (∀env (s : 'a flatSem$state) v pes err_v s' r s1 env' err_v1 v1.
    evaluate_match env s v pes err_v = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    env_rel env env' ∧
    s_rel s s1 ∧
    v_rel v v1 ∧
    v_rel err_v err_v1
    ⇒
    ?s1' r1.
      result_rel (LIST_REL v_rel) r r1 ∧
      s_rel s' s1' ∧
      evaluate_match env' s1 v1 pes err_v1 = (s1', r1))`,
  ho_match_mp_tac evaluate_ind >>
  rw [evaluate_def, result_rel_cases, compile_def] >>
  rw [] >>
  TRY (fs [env_rel_cases] >> NO_TAC)
  >- (
    every_case_tac >>
    fs [] >>
    rw [PULL_EXISTS] >>
    rfs [] >>
    rw [] >>
    cheat)
  >- rw [Once v_rel_cases]
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- (
    every_case_tac >>
    fs [] >>
    cheat)
  >- (
    simp [Once v_rel_cases] >>
    fs [env_rel_cases])
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat
  >- cheat);

val _ = export_theory ();


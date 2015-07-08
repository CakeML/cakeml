open preamble closLangTheory closSemTheory closPropsTheory;

val _ = new_theory "closRelation";


(* Move to props *)

val clock_lemmas = Q.store_thm ("clock_lemmas",
`!s. (s with clock := s.clock) = s`,
 rw [state_component_equality]);

val evaluate_app_rw = Q.store_thm ("evaluate_app_rw",
`(!args loc_opt f s.
  args ≠ [] ⇒ 
  evaluate_app loc_opt f args s =
    case dest_closure loc_opt f args of
       | NONE => (Rerr(Rabort Rtype_error),s)
       | SOME (Partial_app v) =>
           if s.clock < LENGTH args then 
             (Rerr(Rabort Rtimeout_error),s with clock := 0)
           else (Rval [v], dec_clock (LENGTH args) s)
       | SOME (Full_app exp env rest_args) =>
           if s.clock < (LENGTH args - LENGTH rest_args) then 
             (Rerr(Rabort Rtimeout_error),s with clock := 0)
           else
             case evaluate ([exp],env,dec_clock (LENGTH args - LENGTH rest_args) s) of
                | (Rval [v], s1) =>
                    evaluate_app loc_opt v rest_args s1
                | res => res)`,
 Cases_on `args` >>
 fs [evaluate_def]);

(* END MOVE *)

val is_closure_def = Define `
(is_closure (Closure _ _ _ _ _) ⇔ T) ∧
(is_closure (Recclosure _ _ _ _ _) ⇔ T) ∧
(is_closure _ ⇔ F)`;

val val_rel_def = tDefine "val_rel" `
(val_rel (i:num) (Number n) (Number n') ⇔
  n = n') ∧
(val_rel (i:num) (Block n vs) (Block n' vs') ⇔ 
  n = n' ∧ LIST_REL (val_rel i) vs vs') ∧
(val_rel (i:num) (RefPtr p) (RefPtr p') ⇔ p = p') ∧
(val_rel (i:num) cl cl' ⇔
  if is_closure cl ∧ is_closure cl' then
    !i' args args' s s'.
      if i' < i then
        state_rel i' s s' ∧
        args ≠ [] ∧
        LIST_REL (val_rel i') args args'
        ⇒
        exec_cl_rel i' (cl, args, s) (cl', args', s')
      else
        T
  else
    F) ∧
(exec_rel i (es, env, s) (es', env', s') ⇔
  !i'.
    if i' ≤ i then
      let (r, s1) = evaluate (es, env, s with clock := i') in
      let (r', s1') = evaluate (es', env', s' with clock := i') in
        case (r, r') of
           | (Rval vs, Rval vs') =>
               s1.clock = s1'.clock ∧
               state_rel s1.clock s1 s1' ∧
               LIST_REL (val_rel s1'.clock) vs vs'
           | (Rerr (Rraise v), Rerr (Rraise v')) =>
               s1.clock = s1'.clock ∧
               state_rel s1.clock s1 s1' ∧
               val_rel s1.clock v v'
           | (Rerr (Rabort Rtimeout_error), Rerr (Rabort Rtimeout_error)) =>
               state_rel s1.clock s1 s1'
           | (Rerr (Rabort Rtype_error), _) => T
           | _ => F
    else
      T) ∧
(exec_cl_rel i (cl, args, s) (cl', args', s') ⇔
  !i' loc.
    if i' ≤ i then
      let (r, s1) = evaluate_app loc cl args (s with clock := i') in
      let (r', s1') = evaluate_app loc cl' args' (s' with clock := i') in
        case (r, r') of
           | (Rval vs, Rval vs') =>
               s1.clock = s1'.clock ∧
               state_rel s1.clock s1 s1' ∧
               LIST_REL (val_rel s1'.clock) vs vs'
           | (Rerr (Rraise v), Rerr (Rraise v')) =>
               s1.clock = s1'.clock ∧
               state_rel s1.clock s1 s1' ∧
               val_rel s1.clock v v'
           | (Rerr (Rabort Rtimeout_error), Rerr (Rabort Rtimeout_error)) =>
               state_rel s1.clock s1 s1'
           | (Rerr (Rabort Rtype_error), _) => T
           | _ => F
    else
      T) ∧
(ref_v_rel i (ByteArray ws) (ByteArray ws') ⇔ ws = ws') ∧
(ref_v_rel i (ValueArray vs) (ValueArray vs') ⇔ LIST_REL (val_rel i) vs vs') ∧
(ref_v_rel i _ _ ⇔ F) ∧
(state_rel i s s' ⇔
  LIST_REL (OPTION_REL (val_rel i)) s.globals s'.globals ∧
  fmap_rel (ref_v_rel i) s.refs s'.refs ∧
  fmap_rel (λ(n,e) (n',e'). 
             n = n' ∧ 
             !i' env env' s s'.
               if i' < i then
                 state_rel i' s s' ∧
                 LIST_REL (val_rel i') env env'
                 ⇒
                 exec_rel i' ([e],env,s) ([e'],env',s')
               else
                 T)
           s.code s'.code ∧
  s.io = s'.io ∧
  s.restrict_envs = s'.restrict_envs)`
(WF_REL_TAC `inv_image ($< LEX $< LEX $<) 
             \x. case x of 
                     | INL (i,v,v') => (i:num,0:num,v_size v) 
                     | INR (INL (i,st,st')) => (i,3,0)
                     | INR (INR (INL (i,st,st'))) => (i,3,0)
                     | INR (INR (INR (INL (i,rv,rv')))) => (i,1,0)
                     | INR (INR (INR (INR (i,s,s')))) => (i,2,0)` >>
 rw [] >>
 rpt (first_x_assum (mp_tac o GSYM)) >>
 rw [] >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 TRY decide_tac
 >- (Induct_on `vs` >>
     rw [v_size_def] >>
     res_tac >>
     decide_tac));

val res_rel_def = Define `
(res_rel (Rval vs, s) (Rval vs', s') ⇔
  s.clock = s'.clock ∧
  state_rel s.clock s s' ∧ 
  LIST_REL (val_rel s.clock) vs vs') ∧ 
(res_rel (Rerr (Rraise v), s) (Rerr (Rraise v'), s') ⇔
  s.clock = s'.clock ∧
  state_rel s.clock s s' ∧ 
  val_rel s.clock v v') ∧ 
(res_rel (Rerr (Rabort Rtimeout_error), s) (Rerr (Rabort Rtimeout_error), s') ⇔
  state_rel s.clock s s') ∧
(res_rel (Rerr (Rabort Rtype_error), _) _ ⇔ T) ∧
(res_rel _ _ ⇔ F)`;

val res_rel_rw = Q.store_thm ("res_rel_rw",
`(res_rel (Rval vs, s) x ⇔ 
  ?vs' s'. x = (Rval vs', s') ∧
  LIST_REL (val_rel s.clock) vs vs' ∧ 
  state_rel s.clock s s' ∧
  s.clock = s'.clock) ∧
 (res_rel (Rerr (Rraise v), s) x ⇔ 
  ?v' s'. x = (Rerr (Rraise v'), s') ∧ 
  val_rel s.clock v v' ∧ 
  state_rel s.clock s s' ∧ 
  s.clock = s'.clock) ∧
 (res_rel (Rerr (Rabort Rtimeout_error), s) x ⇔ 
   ?s'. x = (Rerr (Rabort Rtimeout_error), s') ∧ state_rel s.clock s s') ∧
 (res_rel (Rerr (Rabort Rtype_error), s) x ⇔ T)`,
 rw [] >>
 Cases_on `x` >>
 Cases_on `q` >>
 TRY (Cases_on `e`) >>
 TRY (Cases_on `a`) >>
 fs [res_rel_def] >>
 metis_tac []);

val exp_rel_def = Define `
exp_rel es es' ⇔
  !i env env' s s'.
    state_rel i s s' ∧
    LIST_REL (val_rel i) env env' ⇒
    exec_rel i (es, env, s) (es', env', s')`;

val val_rel_ind = theorem "val_rel_ind";

val fun_lemma = Q.prove (
`!f x. (\a a'. f x a a') = f x`,
 rw [FUN_EQ_THM]);

fun find_clause good_const = 
  good_const o fst o strip_comb o fst o dest_eq o snd o strip_forall o concl;

val result_store_cases = Q.store_thm ("result_store_cases",
`!r. ?s. 
  (?vs. r = (Rval vs, s)) ∨
  (?v. r = (Rerr (Rraise v), s)) ∨
  (r = (Rerr (Rabort Rtimeout_error), s)) ∨
  (r = (Rerr (Rabort Rtype_error), s))`,
 Cases_on `r` >>
 rw [] >>
 qexists_tac `r'` >>
 rw [] >>
 Cases_on `q` >>
 rw [] >>
 Cases_on `e` >>
 rw [] >>
 Cases_on `a` >>
 rw []);

val val_rel_rw = 
  let val clauses = CONJUNCTS val_rel_def
      fun good_const x = same_const ``val_rel`` x
  in
    SIMP_RULE (srw_ss()) [fun_lemma, AND_IMP_INTRO, is_closure_def]
        (LIST_CONJ (List.filter (find_clause good_const) clauses))
  end;

val _ = save_thm ("val_rel_rw", val_rel_rw);

val state_rel_rw = 
  let val clauses = CONJUNCTS val_rel_def
      fun good_const x = same_const ``state_rel`` x orelse same_const ``ref_v_rel`` x
  in
    SIMP_RULE (srw_ss()) [fun_lemma] 
         (LIST_CONJ (List.filter (find_clause good_const) clauses))
  end;

val _ = save_thm ("state_rel_rw", state_rel_rw);

val exec_rel_rw = Q.store_thm ("exec_rel_rw",
`(exec_rel i (es,env,s) (es',env',s') ⇔
  !i'. i' ≤ i ⇒
    res_rel (evaluate (es,env,s with clock := i')) 
            (evaluate (es',env',s' with clock := i'))) ∧
 (exec_cl_rel i (cl,args,s) (cl',args',s') ⇔
  !i' loc. i' ≤ i ⇒
    res_rel (evaluate_app loc cl args (s with clock := i')) 
            (evaluate_app loc cl' args' (s' with clock := i')))`,
 rw [] >>
 ONCE_REWRITE_TAC [val_rel_def] >>
 rw [fun_lemma] >>
 eq_tac >>
 fs [] >>
 rw []
 >- (strip_assume_tac (Q.ISPEC `evaluate (es,env,s with clock := i')`
                         result_store_cases) >>
     strip_assume_tac (Q.ISPEC `evaluate (es',env',s' with clock := i')` 
                         result_store_cases) >>
     simp [res_rel_rw] >>
     res_tac >>
     fs [] >>
     rfs [])
 >- (first_x_assum (qspec_then `i'` mp_tac) >>
     rw [] >>
     strip_assume_tac (Q.ISPEC `evaluate (es,env,s with clock := i')` 
                         result_store_cases) >>
     strip_assume_tac (Q.ISPEC `evaluate (es',env',s' with clock := i')` 
                         result_store_cases) >>
     fs [] >>
     rw [] >>
     fs [res_rel_rw] >>
     fs [])
 >- (strip_assume_tac (Q.ISPEC `evaluate_app loc cl args (s with clock := i')`
                         result_store_cases) >>
     strip_assume_tac (Q.ISPEC `evaluate_app loc cl' args' (s' with clock := i')` 
                         result_store_cases) >>
     simp [res_rel_rw] >>
     res_tac >>
     fs [] >>
     rfs [])
 >- (first_x_assum (qspecl_then [`i'`, `loc`] mp_tac) >>
     rw [] >>
     strip_assume_tac (Q.ISPEC `evaluate_app loc cl args (s with clock := i')` 
                         result_store_cases) >>
     strip_assume_tac (Q.ISPEC `evaluate_app loc cl' args' (s' with clock := i')` 
                         result_store_cases) >>
     fs [] >>
     rw [] >>
     fs [res_rel_rw] >>
     fs []));

val val_rel_cl_rw = Q.store_thm ("val_rel_cl_rw",
`!c v v'.
  is_closure v
  ⇒
  (val_rel c v v' ⇔
    if is_closure v' then
      !i' args args' s s'.
        i' < c
        ⇒
        state_rel i' s s' ∧
        args ≠ [] ∧
        LIST_REL (val_rel i') args args'
        ⇒
        exec_cl_rel i' (v, args, s) (v', args', s')
    else
      F)`,
 rw [] >>
 Cases_on `v` >>
 Cases_on `v'` >>
 fs [val_rel_rw, is_closure_def] >>
 metis_tac []);

val val_rel_mono = Q.store_thm ("val_rel_mono",
`(!i v v'. val_rel i v v' ⇒ ∀i'. i' ≤ i ⇒ val_rel i' v v') ∧
 (!i st st'. exec_rel i st st' ⇒ !i'. i' ≤ i ⇒ exec_rel i' st st') ∧
 (!i st st'. exec_cl_rel i st st' ⇒ !i'. i' ≤ i ⇒ exec_cl_rel i' st st') ∧
 (!i rv rv'. ref_v_rel i rv rv' ⇒ !i'. i' ≤ i ⇒ ref_v_rel i' rv rv') ∧
 (!i s s'. state_rel i s s' ⇒ !i'. i' ≤ i ⇒ state_rel i' s s')`,
 ho_match_mp_tac val_rel_ind >>
 rw [val_rel_rw, exec_rel_rw] >>
 fs [is_closure_def] >>
 rw []
 >- (fs [LIST_REL_EL_EQN] >>
     rw [] >>
     metis_tac [MEM_EL])
 >- (`i''' < i ∧ i'' < i` by decide_tac >>
     metis_tac [])
 >- (`i''' < i ∧ i'' < i` by decide_tac >>
     metis_tac [])
 >- (`i'' ≤ i` by decide_tac >>
     metis_tac [])
 >- (`i'' ≤ i` by decide_tac >>
     metis_tac [])
 >- fs [state_rel_rw]
 >- (fs [state_rel_rw, LIST_REL_EL_EQN] >>
     rw [] >>
     metis_tac [MEM_EL])
 >- fs [state_rel_rw]
 >- fs [state_rel_rw]
 >- (qpat_assum `state_rel P1 P2 P3` mp_tac >>
     ONCE_REWRITE_TAC [state_rel_rw] >>
     rw []
     >- (fs [LIST_REL_EL_EQN] >>
         rw [] >>
         metis_tac [MEM_EL, OPTREL_MONO])
     >- metis_tac [fmap_rel_mono]
     >- (imp_res_tac ((GEN_ALL o SIMP_RULE (srw_ss()) [AND_IMP_INTRO]) fmap_rel_mono) >>
         pop_assum kall_tac >>
         pop_assum match_mp_tac >> 
         rw [] >>
         PairCases_on `x` >>
         PairCases_on `y` >>
         fs [] >>
         rw [] >>
         `i'' < i` by decide_tac >>
         metis_tac [])));
  
val val_rel_mono_list = Q.store_thm ("val_rel_mono_list",
`!i i' vs1 vs2.
  i' ≤ i ∧ LIST_REL (val_rel i) vs1 vs2
  ⇒
  LIST_REL (val_rel i') vs1 vs2`,
 rw [LIST_REL_EL_EQN] >>
 metis_tac [val_rel_mono]);

val state_rel_clock = Q.store_thm ("state_rel_clock[simp]",
`!c1 c2 s s'.
  (state_rel c1 (s with clock := c2) s' ⇔ state_rel c1 s s') ∧
  (state_rel c1 s (s' with clock := c2) ⇔ state_rel c1 s s')`,
 rw [] >>
 ONCE_REWRITE_TAC [state_rel_rw] >>
 rw []);

val res_rel_evaluate_app = Q.store_thm ("res_rel_evaluate_app",
`!c v v' vs vs' s s' loc.
  val_rel c v v' ∧
  vs ≠ [] ∧
  LIST_REL (val_rel c) vs vs' ∧
  state_rel c s s' ∧
  s.clock = c ∧
  s'.clock = c
  ⇒
  res_rel (evaluate_app loc v vs s) (evaluate_app loc v' vs' s')`, 
 rw [] >>
 `vs' ≠ []` by (Cases_on `vs'` >> fs []) >>
 rw [evaluate_app_rw] >>
 Cases_on `dest_closure loc v vs` >>
 simp [res_rel_rw] >>
 Cases_on `dest_closure loc v' vs'` >>
 simp [res_rel_rw] >>
 cheat);

val res_rel_do_app = Q.store_thm ("res_rel_do_app",
`!c op vs vs' s s'.
  state_rel c s s' ∧
  LIST_REL (val_rel c) vs vs' ∧
  s.clock = c ∧
  s'.clock = c
  ⇒
  res_rel
  (case do_app op (REVERSE vs) s of
     Rval (v,s) => (Rval [v],s)
   | Rerr err => (Rerr err,s))
  (case do_app op (REVERSE vs') s' of
     Rval (v,s') => (Rval [v],s')
   | Rerr err => (Rerr err,s'))`,
 cheat);

val val_rel_clos_env = Q.store_thm ("val_rel_clos_env",
`!c restrict vars vs1 vs1' vs2 vs2'.
  LIST_REL (val_rel c) vs1 vs1' ∧
  clos_env restrict vars vs1 = SOME vs2
  ⇒
  ?vs2'.
    clos_env restrict vars vs1' = SOME vs2' ∧
    LIST_REL (val_rel c) vs2 vs2'`,
 cheat);

val compat_nil = Q.store_thm ("compat_nil",
`exp_rel [] []`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, res_rel_rw] >>
 metis_tac [val_rel_mono]);

val compat_cons = Q.store_thm ("compat_cons",
`!e es e' es'.
  exp_rel [e] [e'] ∧
  exp_rel es es'
  ⇒
  exp_rel (e::es) (e'::es')`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw] >>
 ONCE_REWRITE_TAC [evaluate_CONS] >>
 rw [] >>
 `exec_rel i' ([e], env, s with clock := i') ([e'], env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e],env,s with clock := i')`
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 first_x_assum (qspecl_then [`s''.clock`, `env`, `env'`, `s''`, `s'''`] mp_tac) >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 `LIST_REL (val_rel s'''.clock) env env'` by metis_tac [val_rel_mono_list] >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `s'''.clock` mp_tac) >>
 rw [clock_lemmas] >>
 `(s'' with clock := s'''.clock) = s''` by metis_tac [clock_lemmas] >>
 fs [] >> 
 reverse (strip_assume_tac (Q.ISPEC `evaluate (es,env,s'')` result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 imp_res_tac evaluate_SING >>
 fs [] >>
 rw [] >>
 metis_tac [val_rel_mono]);

val compat_var = Q.store_thm ("compat_var",
`!n. exp_rel [Var n] [Var n]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def] >>
 rw [res_rel_rw] >>
 fs [LIST_REL_EL_EQN] >>
 metis_tac [MEM_EL, val_rel_mono]);

val compat_if = Q.store_thm ("compat_if",
`!e1 e2 e3 e1' e2' e3'.
  exp_rel [e1] [e1'] ∧
  exp_rel [e2] [e2'] ∧
  exp_rel [e3] [e3']
  ⇒
  exp_rel [If e1 e2 e3] [If e1' e2' e3']`,
 rw [Boolv_def, exp_rel_def, exec_rel_rw, evaluate_def] >>
 fs [PULL_FORALL] >>
 imp_res_tac val_rel_mono >>
 imp_res_tac val_rel_mono_list >>
 last_x_assum (qspecl_then [`i'`, `env`, `env'`, `s`, `s'`, `i'`] mp_tac) >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e1],env,s with clock := i')`
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 simp []
 >- metis_tac [] >>
 `?v v'. vs = [v] ∧ vs' = [v']` by metis_tac [evaluate_SING] >>
 fs [] >>
 rw [] >>
 fs [val_rel_rw]
 >- (imp_res_tac evaluate_clock >>
     fs [] >>
     metis_tac [val_rel_mono_list, LESS_EQ_REFL, clock_lemmas])
 >- (Cases_on `v'` >>
     fs [val_rel_rw] >>
     fs [])
 >- (imp_res_tac evaluate_clock >>
     fs [] >>
     metis_tac [val_rel_mono_list, LESS_EQ_REFL, clock_lemmas])
 >- (Cases_on `v'` >>
     fs [val_rel_rw] >>
     fs []));

val compat_let = Q.store_thm ("compat_let",
`!e es e' es'.
  exp_rel es es' ∧
  exp_rel [e] [e']
  ⇒
  exp_rel [Let es e] [Let es' e']`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def] >>
 rw [] >>
 `exec_rel i' (es, env, s with clock := i') (es', env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate (es,env,s with clock := i')`
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 first_x_assum (qspecl_then [`s''.clock`, `vs++env`, `vs'++env'`, `s''`, `s'''`] mp_tac) >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 `LIST_REL (val_rel s'''.clock) env env'` by metis_tac [val_rel_mono_list] >>
 imp_res_tac EVERY2_APPEND >>
 simp [exec_rel_rw] >>
 metis_tac [clock_lemmas, LESS_EQ_REFL]);

val compat_raise = Q.store_thm ("compat_raise",
`!e e'.
  exp_rel [e] [e']
  ⇒
  exp_rel [Raise e] [Raise e']`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw] >>
 rw [evaluate_def] >>
 `exec_rel i' ([e],env,s with clock := i') ([e'],env',s' with clock := i')`
         by metis_tac [val_rel_mono, val_rel_mono_list, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e],env,s with clock := i')`
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 imp_res_tac evaluate_SING >>
 fs []);

val compat_handle = Q.store_thm ("compat_handle",
`!e1 e2 e1' e2'.
  exp_rel [e1] [e1'] ∧
  exp_rel [e2] [e2']
  ⇒
  exp_rel [Handle e1 e2] [Handle e1' e2']`,
 rw [exp_rel_def] >>
 rw [exec_rel_rw, evaluate_def] >>
 `exec_rel i' ([e1],env,s with clock := i') ([e1'],env',s' with clock := i')`
         by metis_tac [val_rel_mono, val_rel_mono_list, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e1],env,s with clock := i')`
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw] >>
 rw [] >>
 fs [] >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 imp_res_tac val_rel_mono_list >>
 first_x_assum (qspecl_then [`s''.clock`, `v::env`, `v'::env'`, `s''`, `s'''`] mp_tac) >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `s'''.clock` mp_tac) >>
 rw [] >>
 `(s'' with clock := s'''.clock) = s''` by metis_tac [clock_lemmas] >>
 fs [clock_lemmas] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e2],v::env,s'')`
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]);

val compat_tick = Q.store_thm ("compat_tick",
`!e e'.
  exp_rel [e] [e']
  ⇒
  exp_rel [Tick e] [Tick e']`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw] >>
 rw [evaluate_def, res_rel_rw]
 >- (`0 ≤ i` by decide_tac >>
     metis_tac [val_rel_mono]) >>
 fs [dec_clock_def] >>
 `exec_rel i' ([e],env,s with clock := i'-1) ([e'],env',s' with clock := i'-1)`
         by metis_tac [val_rel_mono, val_rel_mono_list, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 rw []);

val compat_call = Q.store_thm ("compat_call",
`!n es es'.
  exp_rel es es'
  ⇒
  exp_rel [Call n es] [Call n es']`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def] >>
 rw [] >>
 `exec_rel i' (es, env, s with clock := i') (es', env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate (es,env,s with clock := i')`
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 Cases_on `find_code n vs s''.code` >>
 fs [res_rel_rw] >>
 cheat);

val compat_app = Q.store_thm ("compat_app",
`!loc e es e' es'.
  exp_rel [e] [e'] ∧
  exp_rel es es'
  ⇒
  exp_rel [App loc e es] [App loc e' es']`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def] >>
 Cases_on `LENGTH es > 0` >>
 simp [res_rel_rw] >>
 gen_tac >>
 DISCH_TAC >>
 first_x_assum (qspecl_then [`i'`, `env`, `env'`, `s`, `s'`] mp_tac) >>
 imp_res_tac val_rel_mono >>
 imp_res_tac val_rel_mono_list >>
 simp [exec_rel_rw] >>
 DISCH_TAC >>
 pop_assum (qspec_then `i'` assume_tac) >>
 fs [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate (es,env,s with clock := i')`
                         result_store_cases)) >>
 fs [res_rel_rw]
 >- (Cases_on `es'` >>
     rw [] >>
     fs [evaluate_def])
 >- (Cases_on `es'` >>
     rw [] >>
     fs [evaluate_def]) >>
 imp_res_tac evaluate_IMP_LENGTH >>
 imp_res_tac LIST_REL_LENGTH >>
 fs [] >>
 first_x_assum (qspecl_then [`s''.clock`, `env`, `env'`, `s''`, `s'''`] mp_tac) >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 `s''.clock ≤ i` by decide_tac >>
 imp_res_tac val_rel_mono_list >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `s'''.clock` assume_tac) >>
 fs [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e],env,s'')`
                         result_store_cases)) >>
 fs [res_rel_rw, clock_lemmas] >>
 `(s'' with clock := s'''.clock) = s''` by metis_tac [clock_lemmas] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 `?v v'. vs'' = [v] ∧ vs''' = [v']` by metis_tac [evaluate_SING] >>
 rw [] >>
 fs [] >>
 `vs ≠ []` by (Cases_on `vs` >> fs []) >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 metis_tac [res_rel_evaluate_app]);

val compat_fn = Q.store_thm ("compat_fn",
`!loc vars num_args e e'.
  exp_rel [e] [e']
  ⇒
  exp_rel [Fn loc vars num_args e] [Fn loc vars num_args e']`,

 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def] >>
 rw [res_rel_rw] >>
 Cases_on `clos_env s.restrict_envs vars env` >>
 fs [res_rel_rw] >>
 `s'.restrict_envs = s.restrict_envs` by fs [Once state_rel_rw] >>
 rw [] >>
 imp_res_tac val_rel_clos_env >>
 imp_res_tac val_rel_mono >>
 rw [is_closure_def, val_rel_rw, exec_rel_rw] >>
 simp [evaluate_app_rw, dest_closure_def, res_rel_rw] >>
 cheat);

val compat_letrec = Q.store_thm ("compat_letrec",
`!loc names funs e funs' e'.
  LIST_REL (\(n,e) (n',e'). n = n' ∧ exp_rel [e] [e']) funs funs' ∧
  exp_rel [e] [e']
  ⇒
  exp_rel [Letrec loc names funs e] [Letrec loc names funs' e']`,
 cheat);

val compat_op = Q.store_thm ("compat_op",
`!op es es'.
  exp_rel es es'
  ⇒
  exp_rel [Op op es] [Op op es']`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def] >>
 rw [] >>
 `exec_rel i' (es, env, s with clock := i') (es', env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate (es,env,s with clock := i')`
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 metis_tac [res_rel_do_app]);

val compat = save_thm ("compat",
  LIST_CONJ [compat_nil, compat_cons, compat_var, compat_if, compat_let, compat_raise,
             compat_handle, compat_tick, compat_call, compat_app, compat_fn,
             compat_letrec, compat_op]);

val exp_rel_refl = Q.store_thm ("exp_rel_refl",
`(!e. exp_rel [e] [e]) ∧
 (!es. exp_rel es es) ∧
 (!(ne :num # closLang$exp). FST ne = FST ne ∧ exp_rel [SND ne] [SND ne]) ∧
 (!funs. LIST_REL (\(n:num,e) (n',e'). n = n' ∧ exp_rel [e] [e']) funs funs)`,
 Induct >>
 rw [] >>
 TRY (PairCases_on `ne`) >>
 fs [] >>
 metis_tac [compat]);

val val_rel_refl = Q.store_thm ("val_rel_refl",
`(!v. val_rel i v v) ∧
 (!vs. LIST_REL (val_rel i) vs vs)`,
 ho_match_mp_tac v_induction >>
 rw [val_rel_rw, is_closure_def] >>
 `exp_rel [e] [e]` by metis_tac [exp_rel_refl] >>
 fs [exp_rel_def] >>
 cheat);

val state_rel_refl = Q.store_thm ("state_rel_refl",
`(!s. state_rel i s s)`,
 cheat);

val val_rel_trans = Q.store_thm ("val_rel_trans",
`(!i v1 v2. val_rel i v1 v2 ⇒ 
    !v3. (!i'. val_rel i' v2 v3) ⇒ val_rel i v1 v3) ∧
 (!i st1 st2. exec_rel i st1 st2 ⇒ 
     !st3. (!i'. exec_rel i' st2 st3) ⇒ exec_rel i st1 st3) ∧
 (!i st1 st2. exec_cl_rel i st1 st2 ⇒ 
     !st3. (!i'. exec_cl_rel i' st2 st3) ⇒ exec_cl_rel i st1 st3) ∧
 (!i rv1 rv2. ref_v_rel i rv1 rv2 ⇒ 
     !rv3. (!i'. ref_v_rel i' rv2 rv3) ⇒ ref_v_rel i rv1 rv3) ∧
 (!i s1 s2. state_rel i s1 s2 ⇒ 
     !s3. (!i'. state_rel i' s2 s3) ⇒ state_rel i s1 s3)`,
 ho_match_mp_tac val_rel_ind >>
 rw [val_rel_rw] >>
 cheat);

val exp_rel_trans = Q.store_thm ("exp_rel_trans",
`!e1 e2 e3. exp_rel e1 e2 ∧ exp_rel e2 e3 ⇒ exp_rel e1 e3`,
 rw [exp_rel_def] >>
 `!i. state_rel i s' s' ∧ LIST_REL (val_rel i) env' env'` by metis_tac [val_rel_refl, state_rel_refl] >>
 metis_tac [val_rel_trans]);

val _ = export_theory ();

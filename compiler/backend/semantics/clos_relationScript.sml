open preamble closLangTheory closSemTheory closPropsTheory;

val _ = new_theory "clos_relation";

val butlastn_nil = Q.store_thm ("butlastn_nil",
`!n l. n ≤ LENGTH l ⇒ (BUTLASTN n l = [] ⇔ LENGTH l = n)`,
 Induct_on `n` >>
 rw [BUTLASTN]
 >- (Cases_on `l` >> rw []) >>
 `l = [] ∨ ?x y. l = SNOC x y` by metis_tac [SNOC_CASES] >>
 ASM_REWRITE_TAC [BUTLASTN] >>
 simp [] >>
 fs [ADD1]);

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

val op_thms = { nchotomy = op_nchotomy, case_def = op_case_def}
val list_thms = { nchotomy = list_nchotomy, case_def = list_case_def}
val option_thms = { nchotomy = option_nchotomy, case_def = option_case_def}
val v_thms = { nchotomy = v_nchotomy, case_def = v_case_def}
val ref_thms = { nchotomy = ref_nchotomy, case_def = ref_case_def}
val result_thms = { nchotomy = TypeBase.nchotomy_of ``:('a,'b)result``,
                    case_def = TypeBase.case_def_of ``:('a,'b)result`` }
val appkind_thms = { nchotomy = TypeBase.nchotomy_of ``:app_kind``,
                     case_def = TypeBase.case_def_of ``:app_kind`` }
val eqs = LIST_CONJ (map prove_case_eq_thm [op_thms, list_thms, option_thms, v_thms, ref_thms, result_thms, appkind_thms])

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 rw []);

val bool_case_eq = Q.prove(
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  rw[] >> metis_tac[]);

val pair_lam_lem = Q.prove (
`!f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)`,
 rw []);

val do_app_cases_val = save_thm ("do_app_cases_val",
``do_app op vs s = Rval (v,s')`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV));

val do_app_cases_err = save_thm ("do_app_cases_err",
``do_app op vs s = Rerr (Rraise v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV));

val do_app_cases_timeout = save_thm ("do_app_cases_timeout",
``do_app op vs s = Rerr (Rabort Rtimeout_error)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV));

val dest_closure_none_loc = Q.store_thm ("dest_closure_none_loc",
`!l cl vs v e env rest.
  (dest_closure l cl vs = SOME (Partial_app v) ⇒ l = NONE) ∧
  (dest_closure l cl vs = SOME (Full_app e env rest) ∧ rest ≠ [] ⇒ l = NONE)`,
 rpt gen_tac >>
 simp [dest_closure_def] >>
 Cases_on `cl` >>
 simp [] >>
 rw [] >>
 Cases_on `l` >>
 fs [check_loc_def] >>
 rw [] >>
 rfs [DROP_NIL] >>
 Cases_on `EL n l1` >>
 fs [] >>
 rw [] >>
 rfs [DROP_NIL]);

val is_closure_def = Define `
(is_closure (Closure _ _ _ _ _) ⇔ T) ∧
(is_closure (Recclosure _ _ _ _ _) ⇔ T) ∧
(is_closure _ ⇔ F)`;

val clo_to_loc_def = Define `
(clo_to_loc (Closure l _ _ _ _) = l) ∧
(clo_to_loc (Recclosure l _ _ _ i) = OPTION_MAP ((+) i) l)`;

val clo_to_env_def = Define `
(clo_to_env (Closure _ _ env _ _) = env) ∧
(clo_to_env (Recclosure loc _ env fns _) =
  GENLIST (Recclosure loc [] env fns) (LENGTH fns) ++ env)`;

val clo_to_partial_args_def = Define `
(clo_to_partial_args (Closure _ args _ _ _) = args) ∧
(clo_to_partial_args (Recclosure _ args _ _ _) = args)`;

val clo_add_partial_args_def = Define `
(clo_add_partial_args args (Closure x1 args' x2 x3 x4) =
  Closure x1 (args ++ args') x2 x3 x4) ∧
(clo_add_partial_args args (Recclosure x1 args' x2 x3 x4) =
  Recclosure x1 (args ++ args') x2 x3 x4)`;

val clo_to_num_params_def = Define `
(clo_to_num_params (Closure _ _ _ n _) = n) ∧
(clo_to_num_params (Recclosure _ _ _ fns i) = FST (EL i fns))`;

val rec_clo_ok_def = Define `
(rec_clo_ok (Recclosure _ _ _ fns i) ⇔ i < LENGTH fns) ∧
(rec_clo_ok (Closure _ _ _ _ _) ⇔ T)`;

val dest_closure_full_length = Q.store_thm ("dest_closure_full_length",
`!l v vs e args rest.
  dest_closure l v vs = SOME (Full_app e args rest)
  ⇒
  LENGTH (clo_to_partial_args v) < clo_to_num_params v ∧
  LENGTH vs + LENGTH (clo_to_partial_args v) = clo_to_num_params v + LENGTH rest ∧
  LENGTH args = clo_to_num_params v + LENGTH (clo_to_env v)`,
 rpt gen_tac >>
 simp [dest_closure_def] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [is_closure_def, clo_to_partial_args_def, clo_to_num_params_def, clo_to_env_def]
 >- (`n - LENGTH l' ≤ LENGTH vs` by decide_tac >>
     rw [] >>
     simp [LENGTH_TAKE]) >>
 Cases_on `EL n l1` >>
 fs [] >>
 rw [] >>
 simp []);

val evaluate_app_clock_less = Q.store_thm ("evaluate_app_clock_less",
`!loc_opt f args s1 vs s2.
  args ≠ [] ∧
  evaluate_app loc_opt f args s1 = (Rval vs, s2)
  ⇒
  s2.clock < s1.clock`,
 rw [] >>
 rfs [evaluate_app_rw] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 rw [] >>
 TRY decide_tac >>
 imp_res_tac evaluate_SING >>
 fs [] >>
 imp_res_tac evaluate_clock >>
 fs [dec_clock_def] >>
 imp_res_tac dest_closure_full_length >>
 TRY decide_tac >>
 Cases_on `args` >>
 fs [] >>
 decide_tac);

val clo_add_partial_args_nil = Q.store_thm ("clo_add_partial_args_nil[simp]",
`!x. is_closure x ⇒ clo_add_partial_args [] x = x`,
 Cases_on `x` >>
 rw [is_closure_def, clo_add_partial_args_def]);

(* END MOVE *)

val clo_can_apply_def = Define `
clo_can_apply loc cl num_args ⇔
  LENGTH (clo_to_partial_args cl) < clo_to_num_params cl ∧
  rec_clo_ok cl ∧
  (loc ≠ NONE ⇒
   loc = clo_to_loc cl ∧
   num_args = clo_to_num_params cl ∧
   clo_to_partial_args cl = [])`;

val check_closures_def = Define `
check_closures cl cl' ⇔
  !loc num_args.
    clo_can_apply loc cl num_args ⇒ clo_can_apply loc cl' num_args`;

val _ = Datatype `
val_or_exp =
  | Val closSem$v
  | Exp1 (num option) closLang$exp (closSem$v list) (closSem$v list)
  | Exp (closLang$exp list) (closSem$v list)`;

val evaluate_ev_def = Define `
(evaluate_ev i (Val v) s = (Rval [v], s with clock := i)) ∧
(evaluate_ev i (Exp1 loc e env vs) s =
  case evaluate ([e], env, s with clock := i) of
     | (Rval [v1], s1) => evaluate_app loc v1 vs s1
     | res => res) ∧
(evaluate_ev i (Exp es env) s = evaluate (es, env, s with clock := i))`;

val evaluate_ev_clock = Q.store_thm ("evaluate_ev_clock",
`!x s1 vs s2. evaluate_ev c x s1 = (vs,s2) ⇒ s2.clock ≤ c`,
 Cases_on `x` >>
 rw [evaluate_ev_def] >>
 rw [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 imp_res_tac evaluate_clock >>
 fs []
 >- decide_tac >>
 rw []);

val val_rel_def = tDefine "val_rel" `
(val_rel (:'ffi) (i:num) (Number n) (Number n') ⇔
  n = n') ∧
(val_rel (:'ffi) (i:num) (Block n vs) (Block n' vs') ⇔
  n = n' ∧ LIST_REL (val_rel (:'ffi) i) vs vs') ∧
(val_rel (:'ffi) (i:num) (RefPtr p) (RefPtr p') ⇔ p = p') ∧
(val_rel (:'ffi) (i:num) cl cl' ⇔
  if is_closure cl ∧ is_closure cl' ∧ check_closures cl cl' then
    !i' vs vs' (s:'ffi closSem$state) (s':'ffi closSem$state).
      if i' < i then
        state_rel i' s s' ∧
        vs ≠ [] ∧
        LIST_REL (val_rel (:'ffi) i') vs vs'
        ⇒
        case (dest_closure NONE cl vs, dest_closure NONE cl' vs') of
           | (NONE, _) => T
           | (_, NONE) => F
           | (SOME (Partial_app v), SOME (Partial_app v')) =>
               exec_rel i' (Val v, s) (Val v', s')
           | (SOME (Partial_app v), SOME (Full_app e' env' vs')) =>
               exec_rel i' (Val v, s) (Exp1 NONE e' env' vs', s')
           | (SOME (Full_app e env vs), SOME (Partial_app v')) =>
               exec_rel i' (Exp1 NONE e env vs, s) (Val v', s')
           | (SOME (Full_app e env vs), SOME (Full_app e' env' vs')) =>
               exec_rel i' (Exp1 NONE e env vs, s) (Exp1 NONE e' env' vs', s')
      else
        T
  else
    F) ∧
(exec_rel i (x:val_or_exp, (s:'ffi closSem$state)) (x':val_or_exp, (s':'ffi closSem$state)) ⇔
  !i'.
    if i' ≤ i then
      let (r, s1) = evaluate_ev i' x s in
      let (r', s1') = evaluate_ev i' x' s' in
        case (r, r') of
           | (Rval vs, Rval vs') =>
               s1.clock = s1'.clock ∧
               state_rel s1.clock s1 s1' ∧
               LIST_REL (val_rel (:'ffi) s1'.clock) vs vs'
           | (Rerr (Rraise v), Rerr (Rraise v')) =>
               s1.clock = s1'.clock ∧
               state_rel s1.clock s1 s1' ∧
               val_rel (:'ffi) s1.clock v v'
           | (Rerr (Rabort Rtimeout_error), Rerr (Rabort Rtimeout_error)) =>
               state_rel s1.clock s1 s1'
           | (Rerr (Rabort Rtype_error), _) => T
           | _ => F
    else
      T) ∧
(ref_v_rel (:'ffi) i (ByteArray ws) (ByteArray ws') ⇔ ws = ws') ∧
(ref_v_rel (:'ffi) i (ValueArray vs) (ValueArray vs') ⇔ LIST_REL (val_rel (:'ffi) i) vs vs') ∧
(ref_v_rel (:'ffi) i _ _ ⇔ F) ∧
(* state_rel is not very flexible *)
(state_rel i s s' ⇔
  LIST_REL (OPTION_REL (val_rel (:'ffi) i)) s.globals s'.globals ∧
  fmap_rel (ref_v_rel (:'ffi) i) s.refs s'.refs ∧
  fmap_rel (λ(n,e) (n',e').
             n = n' ∧
             !i' env env' s s'.
               if i' < i then
                 state_rel i' s s' ∧
                 LIST_REL (val_rel (:'ffi) i') env env'
                 ⇒
                 exec_rel i' (Exp [e] env, s) (Exp [e'] env', s')
               else
                 T)
           s.code s'.code ∧
  s.ffi = s'.ffi)`
(WF_REL_TAC `inv_image ($< LEX $< LEX $<)
             \x. case x of
                     | INL (_,i,v,v') => (i:num,0:num,v_size v)
                     | INR (INL (i,st,st')) => (i,3,0)
                     | INR (INR (INL (_,i,rv,rv'))) => (i,1,0)
                     | INR (INR (INR (i,s,s'))) => (i,2,0)` >>
 rw [] >>
 rpt (first_x_assum (mp_tac o GSYM)) >>
 rw [] >>
 imp_res_tac evaluate_ev_clock >>
 fs [] >>
 TRY decide_tac
 >- (Induct_on `vs` >>
     rw [v_size_def] >>
     res_tac >>
     decide_tac));

val res_rel_def = Define `
(res_rel (Rval vs, (s:'ffi closSem$state)) (Rval vs', s') ⇔
  s.clock = s'.clock ∧
  state_rel s.clock s s' ∧
  LIST_REL (val_rel (:'ffi) s.clock) vs vs') ∧
(res_rel (Rerr (Rraise v), s) (Rerr (Rraise v'), s') ⇔
  s.clock = s'.clock ∧
  state_rel s.clock s s' ∧
  val_rel (:'ffi) s.clock v v') ∧
(res_rel (Rerr (Rabort Rtimeout_error), s) (Rerr (Rabort Rtimeout_error), s') ⇔
  state_rel s.clock s s') ∧
(res_rel (Rerr (Rabort Rtype_error), _) _ ⇔ T) ∧
(res_rel _ _ ⇔ F)`;

val res_rel_rw = Q.store_thm ("res_rel_rw",
`(res_rel (Rval vs, (s:'ffi closSem$state)) x ⇔
  ?vs' s'. x = (Rval vs', s') ∧
  LIST_REL (val_rel (:'ffi) s.clock) vs vs' ∧
  state_rel s.clock s s' ∧
  s.clock = s'.clock) ∧
 (res_rel (Rerr (Rraise v), s) x ⇔
  ?v' s'. x = (Rerr (Rraise v'), s') ∧
  val_rel (:'ffi) s.clock v v' ∧
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
exp_rel (:'ffi) es es' ⇔
  !i env env' (s:'ffi closSem$state) (s':'ffi closSem$state).
    state_rel i s s' ∧
    LIST_REL (val_rel (:'ffi) i) env env' ⇒
    exec_rel i (Exp es env, s) (Exp es' env', s')`;

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

val ref_v_rel_rw = Q.store_thm ("ref_v_rel_rw",
`(ref_v_rel (:'ffi) c (ByteArray ws) x ⇔ x = ByteArray ws) ∧
 (ref_v_rel (:'ffi) c (ValueArray vs) x ⇔
   ?vs'. x = ValueArray vs' ∧
         LIST_REL (val_rel (:'ffi) c) vs vs')`,
 Cases_on `x` >>
 fs [Once val_rel_def, fun_lemma] >>
 fs [Once val_rel_def, fun_lemma] >>
 metis_tac []);

val exec_rel_rw = Q.store_thm ("exec_rel_rw",
`exec_rel i (x,s) (x',s') ⇔
  !i'. i' ≤ i ⇒
  res_rel (evaluate_ev i' x s) (evaluate_ev i' x' s')`,
 rw [] >>
 ONCE_REWRITE_TAC [val_rel_def] >>
 rw [fun_lemma] >>
 eq_tac >>
 fs [] >>
 rw []
 >- (strip_assume_tac (Q.ISPEC `evaluate_ev i' x s` result_store_cases) >>
     strip_assume_tac (Q.ISPEC `evaluate_ev i' x' s'` result_store_cases) >>
     simp [res_rel_rw] >>
     res_tac >>
     fs [])
 >- (first_x_assum (qspec_then `i'` mp_tac) >>
     rw [] >>
     strip_assume_tac (Q.ISPEC `evaluate_ev i' x s` result_store_cases) >>
     strip_assume_tac (Q.ISPEC `evaluate_ev i' x' s'` result_store_cases) >>
     fs [] >>
     rw [] >>
     fs [res_rel_rw] >>
     fs []));

val val_rel_cl_rw = Q.store_thm ("val_rel_cl_rw",
`!c v v'.
  is_closure v
  ⇒
  (val_rel (:'ffi) c v v' ⇔
    if is_closure v' ∧ check_closures v v' then
    !i' vs vs' (s:'ffi closSem$state) s'.
      if i' < c then
        state_rel i' s s' ∧
        vs ≠ [] ∧
        LIST_REL (val_rel (:'ffi) i') vs vs'
        ⇒
        case (dest_closure NONE v vs, dest_closure NONE v' vs') of
           | (NONE, _) => T
           | (_, NONE) => F
           | (SOME (Partial_app v), SOME (Partial_app v')) =>
               exec_rel i' (Val v, s) (Val v', s')
           | (SOME (Partial_app v), SOME (Full_app e' env' rest')) =>
               exec_rel i' (Val v, s) (Exp1 NONE e' env' rest', s')
           | (SOME (Full_app e env rest), SOME (Partial_app v')) =>
               exec_rel i' (Exp1 NONE e env rest, s) (Val v', s')
           | (SOME (Full_app e env rest), SOME (Full_app e' env' rest')) =>
               exec_rel i' (Exp1 NONE e env rest, s) (Exp1 NONE e' env' rest', s')
      else
        T
    else
      F)`,
 rw [] >>
 Cases_on `v` >>
 Cases_on `v'` >>
 fs [val_rel_rw, is_closure_def] >>
 metis_tac []);

val val_rel_mono = Q.store_thm ("val_rel_mono",
`(!(ffi:'ffi itself) i v v'. val_rel ffi i v v' ⇒ ∀i'. i' ≤ i ⇒ val_rel ffi i' v v') ∧
 (!i (st:val_or_exp # 'ffi closSem$state) st'. exec_rel i st st' ⇒ !i'. i' ≤ i ⇒ exec_rel i' st st') ∧
 (!(ffi:'ffi itself) i rv rv'. ref_v_rel ffi i rv rv' ⇒ !i'. i' ≤ i ⇒ ref_v_rel ffi i' rv rv') ∧
 (!i (s:'ffi closSem$state) s'. state_rel i s s' ⇒ !i'. i' ≤ i ⇒ state_rel i' s s')`,
 ho_match_mp_tac val_rel_ind >>
 rw [val_rel_rw, exec_rel_rw] >>
 fs [is_closure_def] >>
 rw []
 >- (fs [LIST_REL_EL_EQN] >>
     rw [] >>
     metis_tac [MEM_EL])
 >- (first_x_assum match_mp_tac >>
     simp [])
 >- (first_x_assum match_mp_tac >>
     simp [])
 >- (first_x_assum match_mp_tac >>
     simp [])
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
  i' ≤ i ∧ LIST_REL (val_rel (:'ffi) i) vs1 vs2
  ⇒
  LIST_REL (val_rel (:'ffi) i') vs1 vs2`,
 rw [LIST_REL_EL_EQN] >>
 metis_tac [val_rel_mono]);

val state_rel_clock = Q.store_thm ("state_rel_clock[simp]",
`!c1 c2 s s'.
  (state_rel c1 (s with clock := c2) s' ⇔ state_rel c1 s s') ∧
  (state_rel c1 s (s' with clock := c2) ⇔ state_rel c1 s s')`,
 rw [] >>
 ONCE_REWRITE_TAC [state_rel_rw] >>
 rw []);

val find_code_related = Q.store_thm ("find_code_related",
`!c n vs (s:'ffi closSem$state) args e vs' s'.
  state_rel c s s' ∧
  LIST_REL (val_rel (:'ffi) c) vs vs' ∧
  find_code n vs s.code = SOME (args,e)
  ⇒
  ?args' e'.
    find_code n vs' s'.code = SOME (args',e') ∧
    LIST_REL (val_rel (:'ffi) c) args args' ∧
    (c ≠ 0 ⇒ exec_rel (c-1) (Exp [e] args, s) (Exp [e'] args', s'))`,
 rw [find_code_def] >>
 `c-1 ≤ c` by decide_tac >>
 `state_rel (c-1) s s'` by metis_tac [val_rel_mono] >>
 qpat_assum `state_rel c s s'` mp_tac >>
 simp [Once state_rel_rw, fmap_rel_OPTREL_FLOOKUP] >>
 rw [] >>
 first_assum (qspec_then `n` mp_tac) >>
 Cases_on `FLOOKUP s.code n` >>
 fs [OPTREL_SOME] >>
 rw [] >>
 Cases_on `x` >>
 Cases_on `z` >>
 fs [] >>
 simp [] >>
 rw []
 >- metis_tac [LIST_REL_LENGTH] >>
 fs [AND_IMP_INTRO] >>
 first_x_assum match_mp_tac >>
 simp [] >>
 `c-1 ≤ c` by decide_tac >>
 metis_tac [val_rel_mono_list]);

val dest_closure_opt = Q.store_thm ("dest_closure_opt",
`!c loc v vs v' vs' x.
  check_closures v v' ∧
  is_closure v ∧
  is_closure v' ∧
  LENGTH vs = LENGTH vs' ∧
  dest_closure loc v vs = SOME x
  ⇒
  ?x'. dest_closure loc v' vs' = SOME x'`,
 rw [] >>
 Cases_on `loc`
 >- (Cases_on `v` >>
     Cases_on `v'` >>
     fs [dest_closure_def, check_closures_def, is_closure_def, clo_to_num_params_def,
         clo_to_partial_args_def, clo_can_apply_def, check_loc_def, rec_clo_ok_def,
         clo_to_loc_def]
     >- metis_tac []
     >- (Cases_on `EL n' l1` >>
         simp [] >>
         rw [] >>
         fs [NOT_LESS_EQUAL] >>
         metis_tac [])
     >- (Cases_on `EL n l1` >>
         simp [] >>
         rw [] >>
         fs [LET_THM] >>
         metis_tac [NOT_LESS_EQUAL])
     >- (Cases_on `EL n l1` >>
         Cases_on `EL n' l1'` >>
         fs [LET_THM] >>
         rw [] >>
         metis_tac [NOT_LESS_EQUAL])) >>
 Cases_on `v` >>
 Cases_on `v'` >>
 fs [dest_closure_def, check_loc_def, is_closure_def, check_closures_def, clo_to_loc_def,
     clo_can_apply_def, clo_to_num_params_def, clo_to_partial_args_def, rec_clo_ok_def] >>
 rfs [] >>
 simp []
 >- metis_tac [NOT_SOME_NONE, LENGTH_EQ_NUM]
 >- (Cases_on `EL n' l1` >>
     fs [] >>
     Cases_on `o''` >>
     fs [] >>
     rw [] >>
     metis_tac [NOT_SOME_NONE, LENGTH_EQ_NUM, NOT_LESS_EQUAL])
 >- (Cases_on `EL n l1` >>
     fs [LET_THM] >>
     rfs [] >>
     rw [] >>
     fs [OPTION_MAP_DEF] >>
     metis_tac [NOT_SOME_NONE, LENGTH_EQ_NUM, NOT_LESS_EQUAL])
 >- (Cases_on `EL n l1` >>
     Cases_on `EL n' l1'` >>
     fs [LET_THM] >>
     rfs [] >>
     rw [] >>
     fs [OPTION_MAP_DEF] >>
     metis_tac [NOT_SOME_NONE, LENGTH_EQ_NUM, NOT_LESS_EQUAL]));

val dest_closure_partial_split = Q.prove (
`!v1 vs v2 n.
  dest_closure NONE v1 vs = SOME (Partial_app v2) ∧
  n ≤ LENGTH vs
  ⇒
  ?v3.
    dest_closure NONE v1 (DROP n vs) = SOME (Partial_app v3) ∧
    v2 = clo_add_partial_args (TAKE n vs) v3`,
 rw [dest_closure_def] >>
 Cases_on `v1` >>
 simp [] >>
 fs [check_loc_def]
 >- (Cases_on `LENGTH vs + LENGTH l < n'` >>
     fs [] >>
     rw [clo_add_partial_args_def] >>
     decide_tac) >>
 fs [LET_THM] >>
 Cases_on `EL n' l1` >>
 fs [] >>
 rw [clo_add_partial_args_def] >>
 fs [] >>
 simp [] >>
 Cases_on `LENGTH vs + LENGTH l < q` >>
 fs [] >>
 decide_tac);

val dest_closure_full_split = Q.prove (
`!v1 vs e env rest.
  dest_closure NONE v1 vs = SOME (Full_app e env rest)
  ⇒
  dest_closure NONE v1 (DROP (LENGTH rest) vs) = SOME (Full_app e env []) ∧
  rest = TAKE (LENGTH rest) vs`,
 rpt gen_tac >>
 simp [dest_closure_def] >>
 Cases_on `v1` >>
 simp [] >>
 fs [check_loc_def]
 >- (DISCH_TAC >>
     Cases_on `LENGTH l + LENGTH vs < n` >>
     fs [] >>
     simp [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [DROP_NIL] >>
     Cases_on `LENGTH vs − LENGTH rest + LENGTH l < n` >>
     simp [] >>
     rw [] >>
     fs []
     >- decide_tac >>
     fs [REVERSE_DROP] >>
     simp [] >>
     qabbrev_tac `i = n - LENGTH l` >>
     `0 < i` by decide_tac >>
     `i ≤ LENGTH vs` by full_simp_tac (srw_ss()++ARITH_ss) [Abbr `i`] >>
     simp [TAKE_REVERSE, DROP_REVERSE, LENGTH_LASTN, LASTN_LASTN, BUTLASTN_LASTN_NIL] >>
     simp [BUTLASTN_TAKE, Abbr `i`])
 >- (Cases_on `EL n l1` >>
     fs [] >>
     DISCH_TAC >>
     fs [] >>
     Cases_on `LENGTH l + LENGTH vs < q` >>
     fs [] >>
     simp [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [DROP_NIL] >>
     Cases_on `LENGTH vs − LENGTH rest + LENGTH l < q` >>
     simp [] >>
     rw [] >>
     fs []
     >- decide_tac >>
     fs [REVERSE_DROP] >>
     simp [] >>
     qabbrev_tac `i = q - LENGTH l` >>
     `0 < i` by decide_tac >>
     `i ≤ LENGTH vs` by full_simp_tac (srw_ss()++ARITH_ss) [Abbr `i`] >>
     simp [TAKE_REVERSE, DROP_REVERSE, LENGTH_LASTN, LASTN_LASTN, BUTLASTN_LASTN_NIL] >>
     simp [BUTLASTN_TAKE, Abbr `i`]));

val dest_closure_partial_is_closure = Q.store_thm(
  "dest_closure_partial_is_closure",
  `dest_closure l v vs = SOME (Partial_app v') ⇒
   is_closure v'`,
  dsimp[dest_closure_def, eqs, bool_case_eq, is_closure_def, UNCURRY]);

val is_closure_add_partial_args_nil = Q.store_thm(
  "is_closure_add_partial_args_nil",
  `is_closure v ⇒ (clo_add_partial_args [] v = v)`,
  Cases_on `v` >> simp[]);

val evaluate_app_clock0 = Q.store_thm(
  "evaluate_app_clock0",
  `s0.clock = 0 ∧ args ≠ [] ⇒
   evaluate_app lopt r args s0 ≠ (Rval vs, s)`,
  strip_tac >> `∃a1 args0. args = a1::args0` by (Cases_on `args` >> fs[]) >>
  simp[evaluate_def] >>
  Cases_on `dest_closure lopt r (a1::args0)` >> simp[] >>
  qcase_tac `dest_closure lopt r (a1::args0) = SOME c` >>
  Cases_on `c` >> simp[] >>
  qcase_tac `dest_closure lopt r (a1::args0) = SOME (Full_app b env rest)` >>
  rw[] >>
  `SUC (LENGTH args0) ≤ LENGTH rest` by simp[] >>
  imp_res_tac dest_closure_full_length >> lfs[])

val evaluate_app_clock_drop = Q.store_thm(
  "evaluate_app_clock_drop",
  `∀args f lopt s0 s vs.
     evaluate_app lopt f args s0 = (Rval vs, s) ⇒
     s.clock + LENGTH args ≤ s0.clock`,
  gen_tac >> completeInduct_on `LENGTH args` >>
  full_simp_tac (srw_ss() ++ DNF_ss) [] >> qx_gen_tac `args` >>
  `args = [] ∨ ∃a1 as. args = a1::as` by (Cases_on `args` >> simp[]) >>
  dsimp[evaluate_def, eqs, bool_case_eq, pair_case_eq, dec_clock_def] >>
  rpt strip_tac >> imp_res_tac evaluate_SING >> fs[] >> rw[] >>
  qcase_tac `evaluate_app lopt r1 args' s1` >>
  Cases_on `args' = []`
  >- (fs[evaluate_def] >> rw[] >> imp_res_tac evaluate_clock >> fs[] >> simp[])
  >- (`SUC (LENGTH as) ≤ LENGTH args' + s0.clock` by simp[] >>
      `LENGTH args' < SUC (LENGTH as)`
        by (imp_res_tac dest_closure_full_length >> lfs[]) >>
      `s.clock + LENGTH args' ≤ s1.clock` by metis_tac[] >>
      imp_res_tac evaluate_clock  >> fs[] >> simp[]))

val val_rel_is_closure = Q.store_thm(
  "val_rel_is_closure",
  `val_rel (:'ffi) c cl1 cl2 ∧ is_closure cl1 ⇒
   is_closure cl2 ∧ check_closures cl1 cl2`,
  Cases_on `cl1` >> simp[is_closure_def, val_rel_rw]);

val dest_closure_is_closure = Q.store_thm(
  "dest_closure_is_closure",
  `dest_closure lopt f vs = SOME r ⇒ is_closure f`,
  Cases_on `f` >> simp[is_closure_def, dest_closure_def]);

val stage_partial_app = Q.store_thm(
  "stage_partial_app",
  `is_closure c ∧
   dest_closure NONE v (rest ++ used) =
     SOME (Partial_app (clo_add_partial_args rest c)) ⇒
   dest_closure NONE c rest =
     SOME (Partial_app (clo_add_partial_args rest c))`,
  Cases_on `v` >> simp[dest_closure_def, eqs, bool_case_eq, UNCURRY] >>
  Cases_on `c` >>
  simp[clo_add_partial_args_def, is_closure_def, check_loc_def]);

val res_rel_evaluate_app = Q.store_thm ("res_rel_evaluate_app",
`!c v v' vs vs' (s:'ffi closSem$state) s' loc.
  val_rel (:'ffi) c v v' ∧
  vs ≠ [] ∧
  LIST_REL (val_rel (:'ffi) c) vs vs' ∧
  state_rel c s s' ∧
  s.clock = c ∧
  s'.clock = c
  ⇒
  res_rel (evaluate_app loc v vs s) (evaluate_app loc v' vs' s')`,
 qx_gen_tac `c` >> completeInduct_on `c` >>
 rw [] >>
 `vs' ≠ []` by (Cases_on `vs'` >> fs []) >>
 rw [evaluate_app_rw] >>
 Cases_on `dest_closure loc v vs` >>
 simp [res_rel_rw] >>
 qcase_tac `dest_closure loc v vs = SOME c` >>
 `is_closure v ∧ is_closure v' ∧ check_closures v v'`
          by (Cases_on `v` >>
              Cases_on `v'` >>
              fs [val_rel_rw, dest_closure_def, is_closure_def]) >>
 imp_res_tac LIST_REL_LENGTH >>
 `?c'. dest_closure loc v' vs' = SOME c'` by metis_tac [dest_closure_opt] >>
 simp [] >>
 `LENGTH vs ≠ 0` by (Cases_on `vs` >> fs []) >>
 Cases_on `s'.clock = 0` >>
 rw []
 >- (Cases_on `c` >>
     Cases_on `c'` >>
     fs [] >>
     imp_res_tac dest_closure_full_length >>
     rw [res_rel_rw, dec_clock_def] >>
     fs [] >>
     TRY decide_tac
     >- (`LENGTH vs' + LENGTH (clo_to_partial_args v') < clo_to_num_params v' + LENGTH l0`
                   by decide_tac >>
         rfs [])
     >- (`LENGTH vs' + LENGTH (clo_to_partial_args v') < clo_to_num_params v' + LENGTH l0'`
                by decide_tac >>
         rfs [])) >>
 Cases_on `c` >> Cases_on `c'` >> fs []
 >- ((* Partial, Partial *)
     `loc = NONE` by metis_tac [dest_closure_none_loc] >>
     Cases_on `s'.clock < LENGTH vs'` >>
     simp [res_rel_rw, dec_clock_def]
     >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
     >- (fs [val_rel_cl_rw] >>
         `s'.clock - LENGTH vs ≤ s'.clock` by decide_tac >>
         first_x_assum (qspecl_then [`s'.clock - LENGTH vs`, `vs`, `vs'`, `s`, `s'`] mp_tac) >>
         simp [exec_rel_rw, evaluate_ev_def, res_rel_def] >>
         metis_tac [LESS_EQ_REFL, val_rel_mono, val_rel_mono_list]))
 >- ((* Partial, Full *)
     `loc = NONE` by metis_tac [dest_closure_none_loc] >>
     imp_res_tac dest_closure_full_length >>
     fs [val_rel_cl_rw] >>
     qcase_tac `dest_closure NONE v vs = SOME (Partial_app b)` >>
     qcase_tac `dest_closure NONE v' vs' = SOME (Full_app b' args' rest')` >>
     first_x_assum
       (qspecl_then [`s'.clock - (LENGTH vs - LENGTH rest')`,
                     `DROP (LENGTH rest') vs`,
                     `DROP (LENGTH rest') vs'`, `s`, `s'`] mp_tac) >>
     simp [exec_rel_rw, evaluate_ev_def, res_rel_def] >>
     `LENGTH rest' + s'.clock − LENGTH vs' ≤ s'.clock` by decide_tac >>
     imp_res_tac val_rel_mono >>
     imp_res_tac val_rel_mono_list >>
     simp [] >>
     `LENGTH rest' ≠ LENGTH vs` by decide_tac >>
     simp [DROP_NIL, EVERY2_DROP] >>
     `LENGTH rest' ≤ LENGTH vs` by decide_tac >>
     imp_res_tac dest_closure_partial_split >>
     simp [] >>
     fs [] >>
     rfs [] >>
     imp_res_tac dest_closure_full_split >>
     fs [] >>
     disch_then (qspec_then `LENGTH rest' + s'.clock − LENGTH vs'` mp_tac) >>
     simp [] >> rveq >> simp[SimpL ``$==>``, res_rel_rw, eqs, pair_case_eq] >>
     simp[PULL_EXISTS] >> csimp[] >>
     simp[evaluate_def] >>
     rpt strip_tac >>
     qcase_tac `evaluate ([b'], args', _) = (Rval [bv'], s2)` >>
     simp[dec_clock_def] >>
     qabbrev_tac `used' = DROP (LENGTH rest') vs'` >>
     `vs' = rest' ++ used'` by metis_tac[TAKE_DROP] >>
     qcase_tac
       `dest_closure NONE v (DROP (LENGTH rest') vs) = SOME (Partial_app b0)`>>
     `is_closure b0` by metis_tac[dest_closure_partial_is_closure] >>
     Cases_on `rest' = []`
     >- (fs[] >> rw[] >> dsimp[res_rel_rw, clo_add_partial_args_def]
         >- metis_tac[val_rel_mono, ZERO_LESS_EQ]
         >- simp[evaluate_def]) >>
     `LENGTH rest' ≠ 0` by (Cases_on `rest'` >> fs[]) >>
     fs[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
     Cases_on `s'.clock < LENGTH used'`
     >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, ZERO_LESS_EQ]) >>
     full_simp_tac(srw_ss() ++ numSimps.ARITH_NORM_ss) [] >>
     qabbrev_tac `used = DROP (LENGTH rest') vs` >>
     qabbrev_tac `rest = TAKE (LENGTH rest') vs` >>
     `vs = rest ++ used` by simp[Abbr`used`, Abbr`rest`, TAKE_DROP] >>
     `LENGTH rest' = LENGTH rest ∧ LENGTH used' = LENGTH used`
        by simp[Abbr`rest`, Abbr`used`] >>
     `rest ≠ []` by (Cases_on `rest` >> fs[]) >> fs[] >> rw[] >>
     markerLib.RM_ALL_ABBREVS_TAC
     >- (first_x_assum (qspec_then `s2.clock` mp_tac) >> simp[] >>
         strip_tac >>
         qmatch_abbrev_tac `res_rel (r1,s1) (evaluate_app NONE bv' rest' s2)` >>
         `evaluate_app NONE b0 rest (s with clock := s2.clock) = (r1,s1)`
            suffices_by
            (disch_then (SUBST_ALL_TAC o SYM) >> first_x_assum match_mp_tac >>
             simp[] >> metis_tac[LIST_REL_APPEND_IMP]) >>
         dsimp[evaluate_app_rw, eqs, Abbr`r1`, Abbr`s1`, bool_case_eq] >>
         disj1_tac >>
         `dest_closure NONE b0 rest =
            SOME (Partial_app (clo_add_partial_args rest b0))`
           by metis_tac[stage_partial_app] >> simp[])
     >- (first_x_assum (qspec_then `s2.clock` mp_tac) >> simp[] >>
         strip_tac >>
         qmatch_abbrev_tac `res_rel (r1,s1) (evaluate_app NONE bv' rest' s2)` >>
         `evaluate_app NONE b0 rest (s with clock := s2.clock) = (r1,s1)`
            suffices_by
            (disch_then (SUBST_ALL_TAC o SYM) >> first_x_assum match_mp_tac >>
             simp[] >> metis_tac[LIST_REL_APPEND_IMP]) >>
         dsimp[evaluate_app_rw, eqs, Abbr`r1`, Abbr`s1`, bool_case_eq,
               dec_clock_def] >>
         disj1_tac >>
         metis_tac[stage_partial_app]))
 >- ((* Full, Partial *) cheat)
 >- ((* Full, Full *) cheat))

val state_rel_refs = Q.prove (
`!c (s:'ffi closSem$state) s' n rv p.
  state_rel c s s' ∧
  FLOOKUP s.refs p = SOME rv
  ⇒
  ?rv'.
    FLOOKUP s'.refs p = SOME rv' ∧
    ref_v_rel (:'ffi) c rv rv'`,
 rw [Once state_rel_rw] >>
 fs [fmap_rel_OPTREL_FLOOKUP] >>
 last_x_assum (qspec_then `p` mp_tac) >>
 fs [OPTREL_SOME] >>
 rw [] >>
 fs []);

val res_rel_do_app = Q.store_thm ("res_rel_do_app",
`!c op vs vs' (s:'ffi closSem$state) s'.
  state_rel c s s' ∧
  LIST_REL (val_rel (:'ffi) c) vs vs' ∧
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
 rw [] >>
 Cases_on `do_app op (REVERSE vs) s`
 >- (`?v s'. a = (v,s')` by metis_tac [pair_CASES] >>
     rw [] >>
     rw [res_rel_rw] >>
     imp_res_tac do_app_cases_val >>
     fs [] >>
     rw [] >>
     fs [do_app_def, val_rel_rw]
     >- ((* global lookup *)
         cheat)
     >- ((* global init *)
         cheat)
     >- ((* global extend *)
         rw [Unit_def, val_rel_rw] >>
         cheat)
     >- rw [EVERY2_REVERSE]
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw] >>
         rw [] >>
         fs [LIST_REL_EL_EQN] >>
         decide_tac)
     >- (Cases_on `y` >>
         fs [val_rel_rw, LIST_REL_EL_EQN])
     >- (Cases_on `y` >>
         fs [val_rel_rw] >>
         imp_res_tac state_rel_refs >>
         fs [val_rel_rw, ref_v_rel_rw] >>
         rw [val_rel_rw] >>
         fs [LIST_REL_EL_EQN])
     >- (Cases_on `y` >>
         fs [val_rel_rw] >>
         imp_res_tac state_rel_refs >>
         fs [val_rel_rw, ref_v_rel_rw] >>
         rw [val_rel_rw, LIST_REL_EL_EQN])
     >- (fs [LET_THM, SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw] >>
         rw [val_rel_rw] >>
         `(LEAST ptr. ptr ∉ FDOM s.refs) = LEAST ptr. ptr ∉ FDOM s'.refs`
                by fs [Once state_rel_rw, fmap_rel_def] >>
         fs [Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         rw [ref_v_rel_rw])
     >- (fs [LET_THM, SWAP_REVERSE_SYM] >>
         Cases_on `y'` >>
         fs [val_rel_rw] >>
         rw [val_rel_rw] >>
         `(LEAST ptr. ptr ∉ FDOM s.refs) = LEAST ptr. ptr ∉ FDOM s'.refs`
                by fs [Once state_rel_rw, fmap_rel_def] >>
         fs [Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         rw [ref_v_rel_rw, LIST_REL_REPLICATE_same])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw] >>
         rw [val_rel_rw] >>
         imp_res_tac state_rel_refs >>
         fs [ref_v_rel_rw] >>
         rw [val_rel_rw])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         Cases_on `y''` >>
         fs [val_rel_rw] >>
         rw [val_rel_rw] >>
         imp_res_tac state_rel_refs >>
         fs [ref_v_rel_rw] >>
         rw [val_rel_rw, Unit_def] >>
         fs [Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         simp [state_rel_rw])
     >- cheat
     >- (Cases_on `y` >>
         fs [val_rel_rw] >>
         cheat)
     >- (Cases_on `y` >>
         fs [val_rel_rw] >>
         rw [val_rel_rw, Boolv_def] >>
         fs [LIST_REL_EL_EQN])
     >- (Cases_on `y` >>
         fs [val_rel_rw] >>
         rw [val_rel_rw, Boolv_def])
     >- (fs [LET_THM] >>
         rw [val_rel_rw] >>
         `(LEAST ptr. ptr ∉ FDOM s.refs) = LEAST ptr. ptr ∉ FDOM s'.refs`
                by fs [Once state_rel_rw, fmap_rel_def] >>
         fs [Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         rw [ref_v_rel_rw, EVERY2_REVERSE])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw] >>
         rw [] >>
         imp_res_tac state_rel_refs >>
         fs [ref_v_rel_rw, LIST_REL_EL_EQN] >>
         rw [] >>
         `Num i < LENGTH xs` by intLib.ARITH_TAC
         >- metis_tac [MEM_EL] >>
         intLib.ARITH_TAC)
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y'` >>
         Cases_on `y''` >>
         fs [val_rel_rw] >>
         rw [] >>
         imp_res_tac state_rel_refs >>
         fs [ref_v_rel_rw, LIST_REL_EL_EQN] >>
         rw [val_rel_rw, Unit_def]
         >- (fs [Once state_rel_rw] >>
             match_mp_tac fmap_rel_FUPDATE_same >>
             rw [ref_v_rel_rw] >>
             match_mp_tac EVERY2_LUPDATE_same >>
             rw [LIST_REL_EL_EQN])
         >- intLib.ARITH_TAC)
     >- (Cases_on `y` >>
         fs [val_rel_rw] >>
         rw [] >>
         imp_res_tac state_rel_refs >>
         fs [ref_v_rel_rw, LIST_REL_EL_EQN] >>
         rw [] >>
         `s'.ffi = s.ffi` by fs [Once state_rel_rw] >>
         rw [Unit_def, val_rel_rw] >>
         fs [Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         rw [ref_v_rel_rw])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `do_eq x1 x2` >>
         fs [] >>
         rw [] >>
         cheat)
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw] >>
         rw [val_rel_rw])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw] >>
         rw [val_rel_rw])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw, Boolv_def] >>
         rw [val_rel_rw])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw, Boolv_def])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw, Boolv_def])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw, Boolv_def])
     >- (fs [SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         fs [val_rel_rw, Boolv_def]))
 >- (Cases_on `e` >>
     rw [res_rel_rw]
     >- (imp_res_tac do_app_cases_err >>
         fs [] >>
         rw [] >>
         Cases_on `do_eq x1 x2` >>
         fs [] >>
         `vs = REVERSE [x1;x2]` by metis_tac [REVERSE_REVERSE] >>
         rw [] >>
         fs [] >>
         rw [do_app_def] >>
         cheat)
     >- (Cases_on `a` >>
         fs [res_rel_rw] >>
         imp_res_tac do_app_cases_timeout >>
         fs [] >>
         rw [] >>
         Cases_on `do_eq x1 x2` >>
         fs [])));

val val_rel_lookup_vars = Q.store_thm ("val_rel_lookup_vars",
`!c vars vs1 vs1' vs2.
  LIST_REL (val_rel (:'ffi) c) vs1 vs1' ∧
  lookup_vars vars vs1 = SOME vs2
  ⇒
  ?vs2'.
    lookup_vars vars vs1' = SOME vs2' ∧
    LIST_REL (val_rel (:'ffi) c) vs2 vs2'`,
 Induct_on `vars` >>
 fs [lookup_vars_def] >>
 rw [] >>
 every_case_tac >>
 fs []
 >- (res_tac >> fs []) >>
 imp_res_tac LIST_REL_LENGTH >>
 fs [] >>
 rw []
 >- (fs [LIST_REL_EL_EQN] >> metis_tac [MEM_EL]) >>
 metis_tac [SOME_11]);

val val_rel_clos_env = Q.store_thm ("val_rel_clos_env",
`!c restrict vars vs1 vs1' vs2.
  LIST_REL (val_rel (:'ffi) c) vs1 vs1' ∧
  clos_env restrict vars vs1 = SOME vs2
  ⇒
  ?vs2'.
    clos_env restrict vars vs1' = SOME vs2' ∧
    LIST_REL (val_rel (:'ffi) c) vs2 vs2'`,
 rw [clos_env_def] >>
 rw [] >>
 metis_tac [val_rel_lookup_vars]);

val compat_nil = Q.store_thm ("compat_nil",
`exp_rel (:'ffi) [] []`,
 rw [exp_rel_def, exec_rel_rw, evaluate_def, res_rel_rw, evaluate_ev_def] >>
 metis_tac [val_rel_mono]);

val compat_cons = Q.store_thm ("compat_cons",
`!e es e' es'.
  exp_rel (:'ffi) [e] [e'] ∧
  exp_rel (:'ffi) es es'
  ⇒
  exp_rel (:'ffi) (e::es) (e'::es')`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_ev_def] >>
 ONCE_REWRITE_TAC [evaluate_CONS] >>
 rw [] >>
 `exec_rel i' (Exp [e] env, s with clock := i') (Exp [e'] env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw, evaluate_ev_def] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse ((Q.ISPEC_THEN `evaluate ([e],env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 first_x_assum (qspecl_then [`s''.clock`, `env`, `env'`, `s''`, `s'''`] mp_tac) >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 `LIST_REL (val_rel (:'ffi) s'''.clock) env env'` by metis_tac [val_rel_mono_list] >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `s'''.clock` mp_tac) >>
 rw [clock_lemmas] >>
 `(s'' with clock := s'''.clock) = s''` by metis_tac [clock_lemmas] >>
 fs [] >>
 reverse (Q.ISPEC_THEN `evaluate (es,env,s'')` strip_assume_tac result_store_cases) >>
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
`!n. exp_rel (:'ffi) [Var n] [Var n]`,
 rw [exp_rel_def, exec_rel_rw, evaluate_ev_def, evaluate_def] >>
 rw [res_rel_rw] >>
 fs [LIST_REL_EL_EQN] >>
 metis_tac [MEM_EL, val_rel_mono]);

val compat_if = Q.store_thm ("compat_if",
`!e1 e2 e3 e1' e2' e3'.
  exp_rel (:'ffi) [e1] [e1'] ∧
  exp_rel (:'ffi) [e2] [e2'] ∧
  exp_rel (:'ffi) [e3] [e3']
  ⇒
  exp_rel (:'ffi) [If e1 e2 e3] [If e1' e2' e3']`,
 rw [Boolv_def, exp_rel_def, exec_rel_rw, evaluate_ev_def, evaluate_def] >>
 fs [PULL_FORALL] >>
 imp_res_tac val_rel_mono >>
 imp_res_tac val_rel_mono_list >>
 last_x_assum (qspecl_then [`i'`, `env`, `env'`, `s`, `s'`, `i'`] mp_tac) >>
 reverse ((Q.ISPEC_THEN `evaluate ([e1],env,s with clock := i')`strip_assume_tac
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
  exp_rel (:'ffi) es es' ∧
  exp_rel (:'ffi) [e] [e']
  ⇒
  exp_rel (:'ffi) [Let es e] [Let es' e']`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_ev_def, evaluate_def] >>
 rw [] >>
 `exec_rel i' (Exp es env, s with clock := i') (Exp es' env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse ((Q.ISPEC_THEN `evaluate (es,env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 first_x_assum (qspecl_then [`s''.clock`, `vs++env`, `vs'++env'`, `s''`, `s'''`] mp_tac) >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 `LIST_REL (val_rel (:'ffi) s'''.clock) env env'` by metis_tac [val_rel_mono_list] >>
 imp_res_tac EVERY2_APPEND >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 metis_tac [clock_lemmas, LESS_EQ_REFL]);

val compat_raise = Q.store_thm ("compat_raise",
`!e e'.
  exp_rel (:'ffi) [e] [e']
  ⇒
  exp_rel (:'ffi) [Raise e] [Raise e']`,
 rw [exp_rel_def] >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw [evaluate_def] >>
 `exec_rel i' (Exp [e] env, s with clock := i') (Exp [e'] env', s' with clock := i')`
         by metis_tac [val_rel_mono, val_rel_mono_list, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse ((Q.ISPEC_THEN `evaluate ([e],env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 imp_res_tac evaluate_SING >>
 fs []);

val compat_handle = Q.store_thm ("compat_handle",
`!e1 e2 e1' e2'.
  exp_rel (:'ffi) [e1] [e1'] ∧
  exp_rel (:'ffi) [e2] [e2']
  ⇒
  exp_rel (:'ffi) [Handle e1 e2] [Handle e1' e2']`,
 rw [exp_rel_def] >>
 rw [evaluate_ev_def, exec_rel_rw, evaluate_def] >>
 `exec_rel i' (Exp [e1] env,s with clock := i') (Exp [e1'] env',s' with clock := i')`
         by metis_tac [val_rel_mono, val_rel_mono_list, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse ((Q.ISPEC_THEN `evaluate ([e1],env,s with clock := i')` strip_assume_tac
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw] >>
 rw [] >>
 fs [] >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 imp_res_tac val_rel_mono_list >>
 first_x_assum (qspecl_then [`s''.clock`, `v::env`, `v'::env'`, `s''`, `s'''`] mp_tac) >>
 simp [evaluate_ev_def, exec_rel_rw] >>
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
  exp_rel (:'ffi) [e] [e']
  ⇒
  exp_rel (:'ffi) [Tick e] [Tick e']`,
 rw [exp_rel_def] >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw [evaluate_def, res_rel_rw]
 >- (`0 ≤ i` by decide_tac >>
     metis_tac [val_rel_mono]) >>
 fs [dec_clock_def] >>
 `exec_rel i' (Exp [e] env,s with clock := i'-1) (Exp [e'] env',s' with clock := i'-1)`
         by metis_tac [val_rel_mono, val_rel_mono_list, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw []);

val compat_call = Q.store_thm ("compat_call",
`!n es es'.
  exp_rel (:'ffi) es es'
  ⇒
  exp_rel (:'ffi) [Call n es] [Call n es']`,
 rw [exp_rel_def] >>
 simp [evaluate_ev_def, exec_rel_rw, evaluate_def] >>
 rw [] >>
 `exec_rel i' (Exp es env, s with clock := i') (Exp es' env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 reverse ((Q.ISPEC_THEN `evaluate (es,env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 Cases_on `find_code n vs s''.code` >>
 fs [res_rel_rw] >>
 `?args e. x = (args,e)` by metis_tac [pair_CASES] >>
 fs [] >>
 `?args' e'.
   find_code n vs' s'''.code = SOME (args',e') ∧
   LIST_REL (val_rel (:'ffi) s'''.clock) args args' ∧
   (s'''.clock ≠ 0 ⇒ exec_rel (s'''.clock − 1) (Exp [e] args,s'') (Exp [e'] args',s'''))`
         by metis_tac [find_code_related] >>
 rw [res_rel_rw]
 >- (`0 ≤ i` by decide_tac >>
     metis_tac [val_rel_mono]) >>
 fs [evaluate_ev_def, exec_rel_rw, dec_clock_def] >>
 `s'''.clock - 1 ≤ s'''.clock - 1` by decide_tac >>
 metis_tac []);

val compat_app = Q.store_thm ("compat_app",
`!loc e es e' es'.
  exp_rel (:'ffi) [e] [e'] ∧
  exp_rel (:'ffi) es es'
  ⇒
  exp_rel (:'ffi) [App loc e es] [App loc e' es']`,
 rw [exp_rel_def] >>
 simp [evaluate_ev_def, exec_rel_rw, evaluate_def] >>
 Cases_on `LENGTH es > 0` >>
 simp [res_rel_rw] >>
 gen_tac >>
 DISCH_TAC >>
 first_x_assum (qspecl_then [`i'`, `env`, `env'`, `s`, `s'`] mp_tac) >>
 imp_res_tac val_rel_mono >>
 imp_res_tac val_rel_mono_list >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 DISCH_TAC >>
 pop_assum (qspec_then `i'` assume_tac) >>
 fs [] >>
 reverse ((Q.ISPEC_THEN `evaluate (es,env,s with clock := i')`strip_assume_tac
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
 simp [evaluate_ev_def, exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `s'''.clock` assume_tac) >>
 fs [] >>
 reverse ((Q.ISPEC_THEN `evaluate ([e],env,s'')` strip_assume_tac result_store_cases)) >>
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

 (*
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
 rw [is_closure_def]
 rw [is_closure_def , val_rel_rw, exec_rel_rw, check_closures_def] >>
 fs [clo_can_apply_def, clo_to_partial_args_def, clo_to_num_params_def, rec_clo_ok_def,
     clo_to_loc_def] >>
 `LENGTH args = LENGTH args'` by metis_tac [LIST_REL_LENGTH] >>
 `args ≠ [] ∧ args' ≠ []`
       by (Cases_on `args` >> Cases_on `args'` >> fs []) >>
 simp [evaluate_app_rw, dest_closure_def, res_rel_rw] >>
 Cases_on `check_loc loc' loc num_args (LENGTH args') 0` >>
 simp [res_rel_rw] >>

 Cases_on `LENGTH args' < num_args` >>
 simp [res_rel_rw] >>
 rfs []
 >- (`0 ≤ i''` by decide_tac >>
     metis_tac [val_rel_mono]) >>
 fs [dec_clock_def] >>
 first_x_assum (qspecl_then [`i'''`,
                             `REVERSE (TAKE (LENGTH args') (REVERSE args)) ++ x`,
                             `REVERSE (TAKE (LENGTH args') (REVERSE args')) ++ vs2'`,
                             `s'' with clock := i''' − LENGTH args'`,
                             `s''' with clock := i''' − LENGTH args'`] mp_tac) >>
 `i''' ≤ i` by decide_tac >>
 imp_res_tac val_rel_mono >>
 imp_res_tac val_rel_mono_list >>
 `LAST_N (LENGTH args) args = args` by simp [LAST_N_LENGTH] >>
 rfs [] >>
 simp [GSYM LAST_N_def, LAST_N_LENGTH] >>
 `LIST_REL (val_rel i''') (args ++ x) (args' ++ vs2')` by metis_tac [EVERY2_APPEND_suff] >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i''' - LENGTH args` mp_tac) >>
 rw [] >>
 qabbrev_tac `l = LENGTH args'` >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e],args ++ x,s'' with clock := i''' − l)`
                         result_store_cases)) >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 imp_res_tac evaluate_SING >>
 fs [Abbr `l`, DROP_REVERSE, BUTLASTN_LENGTH_NIL] >>
 `BUTLASTN (LENGTH args) args = []` by rw [BUTLASTN_LENGTH_NIL] >>
 rfs [evaluate_def, res_rel_rw]);

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
*)
val exp_rel_refl = Q.store_thm ("exp_rel_refl",
`(!e. exp_rel (:'ffi) [e] [e]) ∧
 (!es. exp_rel (:'ffi) es es) ∧
 (!(ne :num # closLang$exp). FST ne = FST ne ∧ exp_rel (:'ffi) [SND ne] [SND ne]) ∧
 (!funs. LIST_REL (\(n:num,e) (n',e'). n = n' ∧ exp_rel (:'ffi) [e] [e']) funs funs)`,
 cheat (* Induct >>
 rw [] >>
 TRY (PairCases_on `ne`) >>
 fs [] >>
 metis_tac [compat] *));
(*
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
 *)
val _ = export_theory ();

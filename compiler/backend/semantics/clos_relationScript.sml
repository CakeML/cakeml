open preamble closLangTheory closSemTheory closPropsTheory;

val _ = new_theory "clos_relation";

val refl_list_rel_refl = Q.store_thm ("refl_list_rel_refl",
`!r. (!x. r x x) ⇒ !l. LIST_REL r l l`,
 srw_tac[][] >>
 match_mp_tac EVERY2_refl >>
 srw_tac[][]);

val butlastn_nil = Q.store_thm ("butlastn_nil",
`!n l. n ≤ LENGTH l ⇒ (BUTLASTN n l = [] ⇔ LENGTH l = n)`,
 Induct_on `n` >>
 srw_tac[][BUTLASTN] >>
 `l = [] ∨ ?x y. l = SNOC x y` by metis_tac [SNOC_CASES] >>
 ASM_REWRITE_TAC [BUTLASTN] >>
 simp [] >>
 full_simp_tac(srw_ss())[ADD1]);

val _ = Datatype `
val_or_exp =
  | Val closSem$v num
  | Exp1 (num option) closLang$exp (closSem$v list) (closSem$v list) num
  | Exp (closLang$exp list) (closSem$v list)`;

val evaluate_ev_def = Define `
(evaluate_ev i (Val v dec) s =
  if dec - 1 ≤ i then
    (Rval [v], s with clock := i - (dec - 1))
  else
    (Rerr (Rabort Rtimeout_error), s with clock := 0)) ∧
(evaluate_ev i (Exp1 loc e env vs dec) s =
  if dec - 1 ≤ i then
    case evaluate ([e], env, s with clock := i - (dec - 1)) of
    | (Rval [v1], s1) => evaluate_app loc v1 vs s1
    | res => res
  else
    (Rerr (Rabort Rtimeout_error), s with clock := 0)) ∧
(evaluate_ev i (Exp es env) s = evaluate (es, env, s with clock := i))`;

val evaluate_ev_clock = Q.store_thm ("evaluate_ev_clock",
`!x s1 vs s2. evaluate_ev c x s1 = (vs,s2) ⇒ s2.clock ≤ c`,
 Cases_on `x` >>
 srw_tac[][evaluate_ev_def] >>
 srw_tac[][] >>
 BasicProvers.EVERY_CASE_TAC >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac evaluate_clock >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 decide_tac);

val OPTREL_Cong = Q.store_thm(
  "OPTREL_Cong[defncong]",
  `∀o1 o2 o1' o2' R1 R2.
      (o1 = o1') ∧ (o2 = o2') ∧
      (∀x y. o1' = SOME x ∧ o2' = SOME y ⇒ (R1 x y ⇔ R2 x y)) ⇒
      (OPTREL R1 o1 o2 ⇔ OPTREL R2 o1' o2')`,
  Cases >> Cases >> Cases >> Cases >> simp[OPTREL_def]);

val val_rel_def = tDefine "val_rel" `
(val_rel (:'ffi) (i:num) w (Number n) (Number n') ⇔
  n = n') ∧
(val_rel (:'ffi) (i:num) w (Word64 wd) (Word64 wd') ⇔
  wd = wd') ∧
(val_rel (:'ffi) (i:num) w (Block n vs) (Block n' vs') ⇔
  n = n' ∧ LIST_REL (val_rel (:'ffi) i w) vs vs') ∧
(val_rel (:'ffi) (i:num) w (ByteVector ws) (ByteVector ws') ⇔
  ws = ws') ∧
(val_rel (:'ffi) (i:num) w (RefPtr p) (RefPtr p') ⇔ p = p') ∧
(val_rel (:'ffi) (i:num) w cl cl' ⇔
  if is_closure cl ∧ is_closure cl' ∧ check_closures cl cl' then
    !i' vs vs' (s:'ffi closSem$state) (s':'ffi closSem$state) locopt.
      if i' < i then
        state_rel i' w s s' ∧
        vs ≠ [] ∧
        LIST_REL (val_rel (:'ffi) i' w) vs vs'
        ⇒
        case (dest_closure s.max_app locopt cl vs, dest_closure s'.max_app locopt cl' vs') of
           | (NONE, _) => T
           | (_, NONE) => F
           | (SOME (Partial_app v), SOME (Partial_app v')) =>
               exec_rel i' w (Val v (LENGTH vs), s) (Val v' (LENGTH vs'), s')
           | (SOME (Partial_app v), SOME (Full_app e' env' rem_vs')) =>
               exec_rel i' w
                        (Val v (LENGTH vs), s)
                        (Exp1 locopt e' env' rem_vs'
                              (LENGTH vs' - LENGTH rem_vs'), s')
           | (SOME (Full_app e env rem_vs), SOME (Partial_app v')) =>
               exec_rel i' w
                 (Exp1 locopt e env rem_vs (LENGTH vs - LENGTH rem_vs), s)
                 (Val v' (LENGTH vs'), s')
           | (SOME (Full_app e env rem_vs), SOME (Full_app e' env' rem_vs')) =>
               exec_rel i' w
                 (Exp1 locopt e env rem_vs (LENGTH vs - LENGTH rem_vs), s)
                 (Exp1 locopt e' env' rem_vs' (LENGTH vs' - LENGTH rem_vs'), s')
      else
        T
  else
    F) ∧
(exec_rel i w (x:val_or_exp, (s:'ffi closSem$state)) (x':val_or_exp, (s':'ffi closSem$state)) ⇔
  !i'.
    if i' ≤ i then
      let (r, s1) = evaluate_ev i' x s in
      let (r', s1') = evaluate_ev i' x' s' in
        case (r, r') of
           | (Rval vs, Rval vs') =>
               s1.clock = s1'.clock ∧
               state_rel s1.clock w s1 s1' ∧
               LIST_REL (val_rel (:'ffi) s1'.clock w) vs vs'
           | (Rerr (Rraise v), Rerr (Rraise v')) =>
               s1.clock = s1'.clock ∧
               state_rel s1.clock w s1 s1' ∧
               val_rel (:'ffi) s1.clock w v v'
           | (Rerr (Rabort Rtimeout_error), Rerr (Rabort Rtimeout_error)) =>
               state_rel s1.clock w s1 s1'
           | (Rerr (Rabort Rtype_error), _) => T
           | _ => F
    else
      T) ∧
(ref_v_rel (:'ffi) i w (ByteArray f ws) (ByteArray f' ws') ⇔ f = f' ∧ ws = ws') ∧
(ref_v_rel (:'ffi) i w (ValueArray vs) (ValueArray vs') ⇔ LIST_REL (val_rel (:'ffi) i w) vs vs') ∧
(ref_v_rel (:'ffi) i w _ _ ⇔ F) ∧
(* state_rel is not very flexible *)
(state_rel i w s s' ⇔
  LIST_REL (OPTION_REL (val_rel (:'ffi) i w)) s.globals s'.globals ∧
  fmap_rel (ref_v_rel (:'ffi) i w) s.refs s'.refs ∧
  fmap_rel (λ(n,e) (n',e').
             n = n' ∧
             !i' env env' s s'.
               if i' < i then
                 state_rel i' w s s' ∧
                 LIST_REL (val_rel (:'ffi) i' w) env env'
                 ⇒
                 exec_rel i' w (Exp [e] env, s) (Exp [e'] env', s')
               else
                 T)
           s.code s'.code ∧
  s.max_app = w ∧ s'.max_app = w ∧
  s.ffi = s'.ffi)`
(WF_REL_TAC `inv_image ($< LEX $< LEX $<)
             \x. case x of
                     | INL (_,i,_,v,v') => (i:num,0:num,v_size v)
                     | INR (INL (i,_,st,st')) => (i,3,0)
                     | INR (INR (INL (_,i,_,rv,rv'))) => (i,1,0)
                     | INR (INR (INR (i,_,s,s'))) => (i,2,0)` >>
 srw_tac[][] >>
 rpt (first_x_assum (mp_tac o GSYM)) >>
 srw_tac[][] >>
 imp_res_tac evaluate_ev_clock >>
 full_simp_tac(srw_ss())[] >>
 TRY decide_tac
 >- (Induct_on `vs` >>
     srw_tac[][v_size_def] >>
     res_tac >>
     decide_tac));

val res_rel_def = Define `
(res_rel w (Rval vs, (s:'ffi closSem$state)) (Rval vs', s') ⇔
  s.clock = s'.clock ∧
  state_rel s.clock w s s' ∧
  LIST_REL (val_rel (:'ffi) s.clock w) vs vs') ∧
(res_rel w (Rerr (Rraise v), s) (Rerr (Rraise v'), s') ⇔
  s.clock = s'.clock ∧
  state_rel s.clock w s s' ∧
  val_rel (:'ffi) s.clock w v v') ∧
(res_rel w (Rerr (Rabort Rtimeout_error), s) (Rerr (Rabort Rtimeout_error), s') ⇔
  state_rel s.clock w s s') ∧
(res_rel w (Rerr (Rabort Rtype_error), _) _ ⇔ T) ∧
(res_rel _ _ _ ⇔ F)`;

val res_rel_rw = Q.store_thm ("res_rel_rw",
`(res_rel w (Rval vs, (s:'ffi closSem$state)) x ⇔
  ?vs' s'. x = (Rval vs', s') ∧
  LIST_REL (val_rel (:'ffi) s.clock w) vs vs' ∧
  state_rel s.clock w s s' ∧
  s.clock = s'.clock) ∧
 (res_rel w (Rerr (Rraise v), s) x ⇔
  ?v' s'. x = (Rerr (Rraise v'), s') ∧
  val_rel (:'ffi) s.clock w v v' ∧
  state_rel s.clock w s s' ∧
  s.clock = s'.clock) ∧
 (res_rel w (Rerr (Rabort Rtimeout_error), s) x ⇔
   ?s'. x = (Rerr (Rabort Rtimeout_error), s') ∧ state_rel s.clock w s s') ∧
 (res_rel w (Rerr (Rabort Rtype_error), s) x ⇔ T)`,
 srw_tac[][] >>
 Cases_on `x` >>
 Cases_on `q` >>
 TRY (Cases_on `e`) >>
 TRY (Cases_on `a`) >>
 full_simp_tac(srw_ss())[res_rel_def] >>
 metis_tac []);

val exp_rel_def = Define `
exp_rel (:'ffi) w es es' ⇔
  !i env env' (s:'ffi closSem$state) (s':'ffi closSem$state).
    state_rel i w s s' ∧
    LIST_REL (val_rel (:'ffi) i w) env env' ⇒
    exec_rel i w (Exp es env, s) (Exp es' env', s')`;

val val_rel_ind = theorem "val_rel_ind";

val fun_lemma = Q.prove (
`!f x. (\a a'. f x a a') = f x`,
 srw_tac[][FUN_EQ_THM]);

fun find_clause good_const =
  good_const o fst o strip_comb o fst o dest_eq o snd o strip_forall o concl;

val result_store_cases = Q.store_thm ("result_store_cases",
`!r. ?s.
  (?vs. r = (Rval vs, s)) ∨
  (?v. r = (Rerr (Rraise v), s)) ∨
  (r = (Rerr (Rabort Rtimeout_error), s)) ∨
  (r = (Rerr (Rabort Rtype_error), s))`,
 Cases_on `r` >>
 srw_tac[][] >>
 qexists_tac `r'` >>
 srw_tac[][] >>
 Cases_on `q` >>
 srw_tac[][] >>
 Cases_on `e` >>
 srw_tac[][] >>
 Cases_on `a` >>
 srw_tac[][]);

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
`(ref_v_rel (:'ffi) c w (ByteArray f ws) x ⇔ x = ByteArray f ws) ∧
 (ref_v_rel (:'ffi) c w (ValueArray vs) x ⇔
   ?vs'. x = ValueArray vs' ∧
         LIST_REL (val_rel (:'ffi) c w) vs vs')`,
 Cases_on `x` >>
 full_simp_tac(srw_ss())[Once val_rel_def, fun_lemma] >>
 full_simp_tac(srw_ss())[Once val_rel_def, fun_lemma] >>
 metis_tac []);

val exec_rel_rw = Q.store_thm ("exec_rel_rw",
`exec_rel i w (x,s) (x',s') ⇔
  !i'. i' ≤ i ⇒
  res_rel w (evaluate_ev i' x s) (evaluate_ev i' x' s')`,
 srw_tac[][] >>
 ONCE_REWRITE_TAC [val_rel_def] >>
 srw_tac[][fun_lemma] >>
 eq_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][]
 >- (strip_assume_tac (Q.ISPEC `evaluate_ev i' x s` result_store_cases) >>
     strip_assume_tac (Q.ISPEC `evaluate_ev i' x' s'` result_store_cases) >>
     simp [res_rel_rw] >>
     res_tac >>
     full_simp_tac(srw_ss())[])
 >- (first_x_assum (qspec_then `i'` mp_tac) >>
     srw_tac[][] >>
     strip_assume_tac (Q.ISPEC `evaluate_ev i' x s` result_store_cases) >>
     strip_assume_tac (Q.ISPEC `evaluate_ev i' x' s'` result_store_cases) >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[res_rel_rw] >>
     full_simp_tac(srw_ss())[]));

val val_rel_cl_rw = Q.store_thm ("val_rel_cl_rw",
`!c w v v'.
  is_closure v
  ⇒
  (val_rel (:'ffi) c w v v' ⇔
    if is_closure v' ∧ check_closures v v' then
    !i' vs vs' (s:'ffi closSem$state) s' locopt.
      if i' < c then
        state_rel i' w s s' ∧
        vs ≠ [] ∧
        LIST_REL (val_rel (:'ffi) i' w) vs vs'
        ⇒
        case (dest_closure s.max_app locopt v vs, dest_closure s'.max_app locopt v' vs') of
           | (NONE, _) => T
           | (_, NONE) => F
           | (SOME (Partial_app v), SOME (Partial_app v')) =>
               exec_rel i' w (Val v (LENGTH vs), s) (Val v' (LENGTH vs'), s')
           | (SOME (Partial_app v), SOME (Full_app e' env' rest')) =>
               exec_rel i' w
                 (Val v (LENGTH vs), s)
                 (Exp1 locopt e' env' rest' (LENGTH vs' - LENGTH rest'), s')
           | (SOME (Full_app e env rest), SOME (Partial_app v')) =>
               exec_rel i' w
               (Exp1 locopt e env rest (LENGTH vs - LENGTH rest), s)
               (Val v' (LENGTH vs'), s')
           | (SOME (Full_app e env rest), SOME (Full_app e' env' rest')) =>
               exec_rel i' w
                 (Exp1 locopt e env rest (LENGTH vs - LENGTH rest), s)
                 (Exp1 locopt e' env' rest' (LENGTH vs' - LENGTH rest'), s')
      else
        T
    else
      F)`,
 srw_tac[][] >>
 Cases_on `v` >>
 Cases_on `v'` >>
 full_simp_tac(srw_ss())[val_rel_rw, is_closure_def] >>
 metis_tac []);

val val_rel_mono = Q.store_thm ("val_rel_mono",
`(!(ffi:'ffi itself) i w v v'. val_rel ffi i w v v' ⇒ ∀i'. i' ≤ i ⇒ val_rel ffi i' w v v') ∧
 (!i w (st:val_or_exp # 'ffi closSem$state) st'. exec_rel i w st st' ⇒ !i'. i' ≤ i ⇒ exec_rel i' w st st') ∧
 (!(ffi:'ffi itself) i w rv rv'. ref_v_rel ffi i w rv rv' ⇒ !i'. i' ≤ i ⇒ ref_v_rel ffi i' w rv rv') ∧
 (!i w (s:'ffi closSem$state) s'. state_rel i w s s' ⇒ !i'. i' ≤ i ⇒ state_rel i' w s s')`,
 ho_match_mp_tac val_rel_ind >>
 srw_tac[][val_rel_rw, exec_rel_rw] >>
 full_simp_tac(srw_ss())[is_closure_def] >>
 srw_tac[][]
 >- (full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
     srw_tac[][] >>
     metis_tac [MEM_EL])
 >- (first_x_assum match_mp_tac >>
     simp [])
 >- (first_x_assum match_mp_tac >>
     simp [])
 >- (first_x_assum match_mp_tac >>
     simp [])
 >- full_simp_tac(srw_ss())[state_rel_rw]
 >- (full_simp_tac(srw_ss())[state_rel_rw, LIST_REL_EL_EQN] >>
     srw_tac[][] >>
     metis_tac [MEM_EL])
 >- full_simp_tac(srw_ss())[state_rel_rw]
 >- full_simp_tac(srw_ss())[state_rel_rw]
 >- (qpat_x_assum `state_rel _ _ _ _` mp_tac >>
     ONCE_REWRITE_TAC [state_rel_rw] >>
     srw_tac[][]
     >- (full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
         srw_tac[][] >>
         rename1 `OPTREL (val_rel (:'ffi) N w)
                      (EL idx s1.globals) (EL idx s2.globals)` >>
         first_x_assum (qspec_then `idx` mp_tac) >> simp[] >>
         Cases_on `EL idx s1.globals` >> Cases_on `EL idx s2.globals` >>
         simp[OPTREL_def] >> metis_tac [MEM_EL])
     >- metis_tac [fmap_rel_mono]
     >- (imp_res_tac ((GEN_ALL o SIMP_RULE (srw_ss()) [AND_IMP_INTRO]) fmap_rel_mono) >>
         pop_assum kall_tac >>
         pop_assum match_mp_tac >>
         srw_tac[][] >>
         PairCases_on `x` >>
         PairCases_on `y` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         `i'' < i` by decide_tac >>
         metis_tac [])));

val val_rel_mono_list = Q.store_thm ("val_rel_mono_list",
`!i i' vs1 vs2.
  i' ≤ i ∧ LIST_REL (val_rel (:'ffi) i w) vs1 vs2
  ⇒
  LIST_REL (val_rel (:'ffi) i' w) vs1 vs2`,
 srw_tac[][LIST_REL_EL_EQN] >>
 metis_tac [val_rel_mono]);

val state_rel_clock = Q.store_thm ("state_rel_clock[simp]",
`!c1 c2 s s'.
  (state_rel c1 w (s with clock := c2) s' ⇔ state_rel c1 w s s') ∧
  (state_rel c1 w s (s' with clock := c2) ⇔ state_rel c1 w s s')`,
 srw_tac[][] >>
 ONCE_REWRITE_TAC [state_rel_rw] >>
 srw_tac[][]);

val state_rel_max_app = Q.store_thm("state_rel_max_app",
  `state_rel c w s1 s2 ⇒ s2.max_app = w ∧ s1.max_app = w`,
  ONCE_REWRITE_TAC[state_rel_rw] \\ rw[]);

val find_code_related = Q.store_thm ("find_code_related",
`!c tt n vs (s:'ffi closSem$state) args e vs' s'.
  state_rel c w s s' ∧
  LIST_REL (val_rel (:'ffi) c w) vs vs' ∧
  find_code n vs s.code = SOME (args,e)
  ⇒
  ?args' e'.
    find_code n vs' s'.code = SOME (args',e') ∧
    LIST_REL (val_rel (:'ffi) c w) args args' ∧
    (¬(c < (tt+1)) ⇒ exec_rel (c-(tt+1)) w (Exp [e] args, s) (Exp [e'] args', s'))`,
 srw_tac[][find_code_def] >>
 `c-(tt+1) ≤ c` by decide_tac >>
 `state_rel (c-(tt+1)) w s s'` by metis_tac [val_rel_mono] >>
 qpat_x_assum `state_rel c w s s'` mp_tac >>
 simp [Once state_rel_rw, fmap_rel_OPTREL_FLOOKUP] >>
 srw_tac[][] >>
 first_assum (qspec_then `n` mp_tac) >>
 Cases_on `FLOOKUP s.code n` >>
 full_simp_tac(srw_ss())[OPTREL_SOME] >>
 srw_tac[][] >>
 Cases_on `x` >>
 Cases_on `z` >>
 full_simp_tac(srw_ss())[] >>
 simp [] >>
 srw_tac[][]
 >- metis_tac [LIST_REL_LENGTH] >>
 full_simp_tac(srw_ss())[AND_IMP_INTRO] >>
 first_x_assum match_mp_tac >>
 simp [] >>
 `c-(tt+1) ≤ c` by decide_tac >>
 metis_tac [val_rel_mono_list]);

val dest_closure_opt = Q.store_thm ("dest_closure_opt",
`!c loc v vs v' vs' x.
  check_closures v v' ∧
  is_closure v ∧
  is_closure v' ∧
  LENGTH vs = LENGTH vs' ∧
  dest_closure max_app loc v vs = SOME x
  ⇒
  ?x'. dest_closure max_app loc v' vs' = SOME x'`,
 srw_tac[][] >>
 Cases_on `loc`
 >- (Cases_on `v` >>
     Cases_on `v'` >>
     full_simp_tac(srw_ss())[dest_closure_def, check_closures_def, is_closure_def, clo_to_num_params_def,
         clo_to_partial_args_def, clo_can_apply_def, check_loc_def, rec_clo_ok_def,
         clo_to_loc_def]
     >- metis_tac []
     >- (Cases_on `EL n' l1` >>
         simp [] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[NOT_LESS_EQUAL] >>
         metis_tac [])
     >- (Cases_on `EL n l1` >>
         simp [] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[LET_THM] >>
         metis_tac [NOT_LESS_EQUAL])
     >- (Cases_on `EL n l1` >>
         Cases_on `EL n' l1'` >>
         full_simp_tac(srw_ss())[LET_THM] >>
         srw_tac[][] >>
         metis_tac [NOT_LESS_EQUAL])) >>
 Cases_on `v` >>
 Cases_on `v'` >>
 full_simp_tac(srw_ss())[dest_closure_def, check_loc_def, is_closure_def, check_closures_def, clo_to_loc_def,
     clo_can_apply_def, clo_to_num_params_def, clo_to_partial_args_def, rec_clo_ok_def] >>
 rev_full_simp_tac(srw_ss())[] >>
 simp []
 >- metis_tac [NOT_SOME_NONE, LENGTH_EQ_NUM]
 >- (Cases_on `EL n' l1` >>
     full_simp_tac(srw_ss())[] >>
     Cases_on `o''` >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     metis_tac [NOT_SOME_NONE, LENGTH_EQ_NUM, NOT_LESS_EQUAL])
 >- (Cases_on `EL n l1` >>
     full_simp_tac(srw_ss())[LET_THM] >>
     rev_full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[OPTION_MAP_DEF] >>
     metis_tac [NOT_SOME_NONE, LENGTH_EQ_NUM, NOT_LESS_EQUAL])
 >- (Cases_on `EL n l1` >>
     Cases_on `EL n' l1'` >>
     full_simp_tac(srw_ss())[LET_THM] >>
     rev_full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[OPTION_MAP_DEF] >>
     metis_tac [NOT_SOME_NONE, LENGTH_EQ_NUM, NOT_LESS_EQUAL]));

val dest_closure_full_split = Q.prove (
`!v1 vs e env rest.
  dest_closure max_app NONE v1 vs = SOME (Full_app e env rest)
  ⇒
  dest_closure max_app NONE v1 (DROP (LENGTH rest) vs) = SOME (Full_app e env []) ∧
  rest = TAKE (LENGTH rest) vs`,
 rpt gen_tac >>
 simp [dest_closure_def] >>
 Cases_on `v1` >>
 simp [] >>
 full_simp_tac(srw_ss())[check_loc_def]
 >- (DISCH_TAC >>
     Cases_on `LENGTH l + LENGTH vs < n` >>
     full_simp_tac(srw_ss())[] >>
     simp [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [DROP_NIL] >>
     Cases_on `LENGTH vs − LENGTH rest + LENGTH l < n` >>
     simp [] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[]
     >- decide_tac >>
     full_simp_tac(srw_ss())[REVERSE_DROP] >>
     simp [] >>
     qabbrev_tac `i = n - LENGTH l` >>
     `0 < i` by decide_tac >>
     `i ≤ LENGTH vs` by full_simp_tac (srw_ss()++ARITH_ss) [Abbr `i`] >>
     simp [TAKE_REVERSE, DROP_REVERSE, LENGTH_LASTN, LASTN_LASTN, BUTLASTN_LASTN_NIL] >>
     simp [BUTLASTN_TAKE, Abbr `i`])
 >- (Cases_on `EL n l1` >>
     full_simp_tac(srw_ss())[] >>
     DISCH_TAC >>
     full_simp_tac(srw_ss())[] >>
     Cases_on `LENGTH l + LENGTH vs < q` >>
     full_simp_tac(srw_ss())[] >>
     simp [] >>
     full_simp_tac (srw_ss()++ARITH_ss) [DROP_NIL] >>
     Cases_on `LENGTH vs − LENGTH rest + LENGTH l < q` >>
     simp [] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[]
     >- decide_tac >>
     full_simp_tac(srw_ss())[REVERSE_DROP] >>
     simp [] >>
     qabbrev_tac `i = q - LENGTH l` >>
     `0 < i` by decide_tac >>
     `i ≤ LENGTH vs` by full_simp_tac (srw_ss()++ARITH_ss) [Abbr `i`] >>
     simp [TAKE_REVERSE, DROP_REVERSE, LENGTH_LASTN, LASTN_LASTN, BUTLASTN_LASTN_NIL] >>
     simp [BUTLASTN_TAKE, Abbr `i`]));

val val_rel_is_closure = Q.store_thm(
  "val_rel_is_closure",
  `val_rel (:'ffi) c w cl1 cl2 ∧ is_closure cl1 ⇒
   is_closure cl2 ∧ check_closures cl1 cl2`,
  Cases_on `cl1` >> simp[is_closure_def, val_rel_rw]);

val val_rel_mono_list' = Q.store_thm(
  "val_rel_mono_list'",
  `LIST_REL (val_rel (:'ffi) m w) l1 l2 ⇒
   ∀i. i ≤ m ⇒ LIST_REL (val_rel (:'ffi) i w) l1 l2`,
  metis_tac[val_rel_mono_list]);

val DROP_LEN_REV = Q.prove(
  `DROP (LENGTH l) (REVERSE l) = []`,
  metis_tac[DROP_APPEND2,DECIDE ``x:num - x = 0``,DROP,APPEND_NIL,
            LENGTH_REVERSE, DECIDE ``x:num ≤ x``]);

val TAKE_LEN_REV = Q.prove(
  `TAKE (LENGTH l) (REVERSE l) = REVERSE l`,
  simp[TAKE_LENGTH_TOO_LONG])

val res_rel_timeout2 = Q.store_thm(
  "res_rel_timeout2",
  `res_rel w rs (Rerr (Rabort Rtimeout_error), s) ⇔
   (∃s'. rs = (Rerr (Rabort Rtimeout_error), s') ∧ state_rel s'.clock w s' s) ∨
   (∃s'. rs = (Rerr (Rabort Rtype_error), s'))`,
  Cases_on `rs` >> simp[] >> rename1 `res_rel _ (rr, _)` >>
  Cases_on `rr` >> simp[res_rel_rw] >> rename1 `res_rel _ (Rerr ee, _)` >>
  Cases_on `ee` >> simp[res_rel_rw] >>
  rename1 `res_rel _ (Rerr (Rabort aa), _)` >> Cases_on `aa` >>
  simp[res_rel_rw]);

val res_rel_evaluate_app = Q.store_thm ("res_rel_evaluate_app",
`!c v v' vs vs' (s:'ffi closSem$state) s' loc.
  val_rel (:'ffi) c w v v' ∧
  vs ≠ [] ∧
  LIST_REL (val_rel (:'ffi) c w) vs vs' ∧
  state_rel c w s s' ∧
  s.clock = c ∧
  s'.clock = c
  ⇒
  res_rel w (evaluate_app loc v vs s) (evaluate_app loc v' vs' s')`,
 qx_gen_tac `c` >> completeInduct_on `c` >>
 srw_tac[][] >>
 `vs' ≠ []` by (Cases_on `vs'` >> full_simp_tac(srw_ss())[]) >>
 srw_tac[][evaluate_app_rw] >>
 Cases_on `dest_closure s.max_app loc v vs` >>
 simp [res_rel_rw] >>
 rename1 `dest_closure _ loc v vs = SOME c` >>
 `is_closure v ∧ is_closure v' ∧ check_closures v v'`
          by (Cases_on `v` >>
              Cases_on `v'` >>
              full_simp_tac(srw_ss())[val_rel_rw, dest_closure_def, is_closure_def]) >>
 imp_res_tac LIST_REL_LENGTH >>
 `?c'. dest_closure s.max_app loc v' vs' = SOME c'` by metis_tac [dest_closure_opt] >>
 simp [] >>
 `LENGTH vs ≠ 0` by (Cases_on `vs` >> full_simp_tac(srw_ss())[]) >>
 Cases_on `s'.clock = 0` >>
 srw_tac[][]
 >- (Cases_on `c` >>
     Cases_on `c'` >>
     full_simp_tac(srw_ss())[] >>
     imp_res_tac state_rel_max_app >>
     imp_res_tac dest_closure_full_length >>
     srw_tac[][res_rel_rw, dec_clock_def] >>
     full_simp_tac(srw_ss())[] >>
     TRY decide_tac
     >- (`LENGTH vs' + LENGTH (clo_to_partial_args v') < clo_to_num_params v' + LENGTH l0`
                   by decide_tac >>
         rev_full_simp_tac(srw_ss())[])
     >- (`LENGTH vs' + LENGTH (clo_to_partial_args v') < clo_to_num_params v' + LENGTH l0'`
                by decide_tac >>
         rev_full_simp_tac(srw_ss())[])) >>
 imp_res_tac state_rel_max_app >>
 Cases_on `c` >> Cases_on `c'` >> full_simp_tac(srw_ss())[]
 >- ((* Partial, Partial *)
     `loc = NONE` by metis_tac [dest_closure_none_loc] >>
     Cases_on `s'.clock < LENGTH vs'` >>
     simp [res_rel_rw, dec_clock_def]
     >- metis_tac [val_rel_mono, ZERO_LESS_EQ]
     >- (full_simp_tac(srw_ss())[val_rel_cl_rw] >>
         `s'.clock - LENGTH vs ≤ s'.clock` by decide_tac >>
         first_x_assum
           (qspecl_then [`s'.clock - 1`, `vs`, `vs'`, `s`, `s'`, `NONE`]
                        mp_tac) >>
         simp [exec_rel_rw, evaluate_ev_def, res_rel_def] >>
         `s'.clock - 1 ≤ s'.clock` by decide_tac >>
         `state_rel (s'.clock − 1) w s s' ∧
          LIST_REL (val_rel (:'ffi) (s'.clock − 1) w) vs vs'`
           by metis_tac [val_rel_mono, val_rel_mono_list] >>
         simp [] >>
         disch_then (qspec_then `s'.clock - 1` mp_tac) >>
         simp [res_rel_rw] >>
         `LENGTH vs' ≠ 0` by rw [] >>
         simp []))
 >- ((* Partial, Full *)
     rename1 `dest_closure _ loc v vs = SOME (Partial_app cl)` >>
     rename1 `dest_closure _ loc v' vs' = SOME (Full_app b' env' rest')` >>
     rename1 `st.clock < LENGTH vs' - LENGTH rest'` >>
     Cases_on `st.clock < LENGTH vs' - LENGTH rest'`
     >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, ZERO_LESS_EQ]) >>
     `LENGTH rest' < LENGTH vs'`
       by (imp_res_tac dest_closure_full_length >> simp[]) >>
     Q.UNDISCH_THEN `¬(st.clock < LENGTH vs' - LENGTH rest')`
       (fn th => `LENGTH vs' ≤ st.clock + LENGTH rest'` by simp[th]) >>
     simp[] >>
     `loc = NONE` by metis_tac[dest_closure_none_loc] >>
     pop_assum SUBST_ALL_TAC >>
     IMP_RES_THEN
       (qx_choose_then `used'` strip_assume_tac)
       (GEN_ALL dest_closure_full_split') >>
     `LENGTH vs' - LENGTH rest' = LENGTH used'`
       by (first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     pop_assum SUBST_ALL_TAC >>
     `0 < LENGTH used'` by lfs[] >>
     `used' ≠ []` by (Cases_on `used'` >> full_simp_tac(srw_ss())[]) >>
     full_simp_tac (srw_ss() ++ numSimps.ARITH_NORM_ss) [] >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >> rveq >>
     simp[dec_clock_def] >>
     qspecl_then [`s.max_app`,`LENGTH rest'`, `v`, `vs`, `cl`]
       mp_tac dest_closure_partial_split' >> simp[] >>
     disch_then (qx_choosel_then [`cl0`, `used`, `rest`] strip_assume_tac) >>
     `is_closure cl0` by metis_tac[dest_closure_partial_is_closure] >>
     `LENGTH used' = LENGTH used`
        by (first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     `used ≠ []` by (spose_not_then assume_tac >> full_simp_tac(srw_ss())[]) >> full_simp_tac(srw_ss())[] >> rveq >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
     `LIST_REL (val_rel (:'ffi) st.clock s.max_app) rest rest' ∧
      LIST_REL (val_rel (:'ffi) st.clock s.max_app) used used'`
       by metis_tac[EVERY2_APPEND] >>
     qspecl_then [`st.clock`, `s.max_app`, `v`, `v'`] mp_tac val_rel_cl_rw >> simp[] >>
     disch_then
       (qspecl_then [`st.clock - 1`, `used`, `used'`] mp_tac) >>
     simp[] >>
     rename1 `state_rel _ _ s0 s0'` >>
     disch_then (qspecl_then [`s0`, `s0'`, `NONE`] mp_tac) >>
     IMP_RES_THEN strip_assume_tac val_rel_mono >> simp[] >>
     IMP_RES_THEN strip_assume_tac val_rel_mono_list' >> simp[] >>
     simp[exec_rel_rw, evaluate_ev_def] >>
     disch_then (qspec_then `s0'.clock - 1` mp_tac) >> simp[] >>
     Cases_on `LENGTH rest = 0` >- (full_simp_tac(srw_ss())[LENGTH_NIL] >> simp[]) >>
     qabbrev_tac `
       ev0 = evaluate([b'],env',s0' with clock := s0'.clock - LENGTH used)` >>
     reverse
        (`(∃rv' s1'. ev0 = (Rval [rv'], s1')) ∨ ∃err s1'. ev0 = (Rerr err, s1')`
           by metis_tac[TypeBase.nchotomy_of ``:('a,'b) result``, pair_CASES,
                        evaluate_SING])
     >- (Cases_on `err` >> simp[res_rel_rw] >>
         rename1 `ev0 = (Rerr (Rabort a), s1)` >>
         Cases_on `a` >> simp[res_rel_rw]) >>
     simp[] >>
     simp[SimpL ``$==>``, res_rel_rw, evaluate_def] >> strip_tac >>
     qmatch_abbrev_tac `res_rel _ LHS (evaluate_app NONE rv' rest' s1')` >>
     `LHS = evaluate_app NONE cl0 rest (s0 with clock := s1'.clock)`
     suffices_by
       (strip_tac >> simp[] >> first_assum irule >- (full_simp_tac(srw_ss())[LENGTH_NIL]) >>
        simp[] >> strip_tac >> full_simp_tac(srw_ss())[] >> strip_tac >> full_simp_tac(srw_ss())[]) >>
     qunabbrev_tac `LHS` >>
     `rest ≠ []` by metis_tac [LENGTH] >>
     `dest_closure s0.max_app NONE cl0 rest =
        SOME (Partial_app (clo_add_partial_args rest cl0))`
       by metis_tac[dest_closure_partial_is_closure, stage_partial_app] >>
     simp[evaluate_app_rw] >> simp[dec_clock_def] >>
     rename1 `s0'.clock < LENGTH rr + LENGTH uu` >>
     `s0'.clock < LENGTH rr + LENGTH uu ⇔ s1'.clock < LENGTH rr` by simp[] >>
     simp[] >> srw_tac[][] >>
     Q.PAT_X_ASSUM `X = s1'.clock` (mp_tac o SYM) >> simp[])
 >- ((* Full, Partial *)
     rename1 `dest_closure _ loc v vs = SOME (Full_app b env rest)` >>
     rename1 `dest_closure _ loc v' vs' = SOME (Partial_app cl')` >>
     rename1 `st.clock < LENGTH vs' - LENGTH rest` >>
     Cases_on `st.clock < LENGTH vs' - LENGTH rest`
     >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, ZERO_LESS_EQ]) >>
     `LENGTH rest < LENGTH vs`
       by (imp_res_tac dest_closure_full_length >> simp[]) >>
     Q.UNDISCH_THEN `¬(st.clock < LENGTH vs' - LENGTH rest)`
       (fn th => `LENGTH vs ≤ st.clock + LENGTH rest` by simp[th]) >>
     simp[] >>
     `loc = NONE` by metis_tac[dest_closure_none_loc] >>
     pop_assum SUBST_ALL_TAC >>
     IMP_RES_THEN
       (qx_choose_then `used` strip_assume_tac)
       (GEN_ALL dest_closure_full_split') >>
     `LENGTH vs' - LENGTH rest = LENGTH used`
       by (first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     pop_assum SUBST_ALL_TAC >>
     `0 < LENGTH used` by lfs[] >>
     `used ≠ []` by (Cases_on `used` >> full_simp_tac(srw_ss())[]) >>
     full_simp_tac (srw_ss() ++ numSimps.ARITH_NORM_ss) [] >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >> rveq >>
     simp[dec_clock_def] >>
     qspecl_then [`s.max_app`,`LENGTH rest`, `v'`, `vs'`, `cl'`]
       mp_tac dest_closure_partial_split' >> simp[] >>
     disch_then (qx_choosel_then [`cl0'`, `used'`, `rest'`] strip_assume_tac) >>
     `is_closure cl0'` by metis_tac[dest_closure_partial_is_closure] >>
     `LENGTH used' = LENGTH used`
        by (first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     `used' ≠ []` by (spose_not_then assume_tac >> full_simp_tac(srw_ss())[]) >> full_simp_tac(srw_ss())[] >> rveq >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
     `LIST_REL (val_rel (:'ffi) st.clock s.max_app) rest rest' ∧
      LIST_REL (val_rel (:'ffi) st.clock s.max_app) used used'`
       by metis_tac[EVERY2_APPEND] >>
     qspecl_then [`st.clock`, `s.max_app`, `v`, `v'`] mp_tac val_rel_cl_rw >> simp[] >>
     disch_then
       (qspecl_then [`st.clock - 1`, `used`, `used'`] mp_tac) >>
     simp[] >>
     rename1 `state_rel _ _ s0 s0'` >>
     disch_then (qspecl_then [`s0`, `s0'`, `NONE`] mp_tac) >>
     IMP_RES_THEN strip_assume_tac val_rel_mono >> simp[] >>
     IMP_RES_THEN strip_assume_tac val_rel_mono_list' >> simp[] >>
     simp[exec_rel_rw, evaluate_ev_def] >>
     disch_then (qspec_then `s0'.clock - 1` mp_tac) >> simp[] >>
     Cases_on `LENGTH rest = 0` >- (full_simp_tac(srw_ss())[LENGTH_NIL] >> simp[]) >>
     qabbrev_tac `
       ev0 = evaluate([b],env,s0 with clock := s0'.clock - LENGTH used)` >>
     reverse
        (`(∃rv s1. ev0 = (Rval [rv], s1)) ∨ ∃err s1. ev0 = (Rerr err, s1)`
           by metis_tac[TypeBase.nchotomy_of ``:('a,'b) result``, pair_CASES,
                        evaluate_SING])
     >- (Cases_on `err` >> simp[res_rel_rw] >>
         rename1 `ev0 = (Rerr (Rabort a), s1)` >>
         Cases_on `a` >> simp[res_rel_rw]) >>
     simp[] >>
     simp[SimpL ``$==>``, res_rel_rw, evaluate_def] >> strip_tac >>
     qmatch_abbrev_tac `res_rel _ (evaluate_app NONE rv rest s1) RHS` >>
     `RHS = evaluate_app NONE cl0' rest' (s0' with clock := s1.clock)`
     suffices_by
       (strip_tac >> simp[] >> first_assum irule >- (full_simp_tac(srw_ss())[LENGTH_NIL]) >>
        simp[] >> strip_tac >> full_simp_tac(srw_ss())[]) >>
     qunabbrev_tac `RHS` >>
     `rest' ≠ []` by metis_tac [LENGTH] >>
     `dest_closure s0.max_app NONE cl0' rest' =
        SOME (Partial_app (clo_add_partial_args rest' cl0'))`
       by metis_tac[dest_closure_partial_is_closure, stage_partial_app] >>
     simp[evaluate_app_rw] >> simp[dec_clock_def])
 >- ((* Full, Full *)
     rename1 `dest_closure _ loc v vs = SOME (Full_app b1 env1 rest1)` >>
     rename1 `dest_closure _ loc v' vs' = SOME (Full_app b2 env2 rest2)` >>
     `(∃used1. vs = rest1 ++ used1 ∧
               dest_closure s.max_app loc v used1 = SOME (Full_app b1 env1 [])) ∧
      (∃used2. vs' = rest2 ++ used2 ∧
               dest_closure s.max_app loc v' used2 = SOME (Full_app b2 env2 []))`
       by metis_tac[dest_closure_full_split'] >>
     `LENGTH rest1 < LENGTH vs ∧ LENGTH rest2 < LENGTH vs'`
       by (imp_res_tac dest_closure_full_length >> simp[]) >>
     `used1 ≠ [] ∧ used2 ≠ []`
       by (ntac 2 (first_x_assum (assume_tac o Q.AP_TERM `list$LENGTH`)) >>
           rpt strip_tac >> lfs[]) >>
     `0 < LENGTH used1 ∧ 0 < LENGTH used2`
         by (Cases_on `used1` >> Cases_on `used2` >> full_simp_tac(srw_ss())[]) >>
     rveq >> lfs[] >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
     `LENGTH used1 = LENGTH used2 ∨ LENGTH used1 < LENGTH used2 ∨
      LENGTH used2 < LENGTH used1` by decide_tac
     >- ((* lengths equal *)
         full_simp_tac (srw_ss() ++ ARITH_ss ++ numSimps.ARITH_NORM_ss) [] >>
         srw_tac[][] >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, ZERO_LESS_EQ]) >>
         `LIST_REL (val_rel (:'ffi) s'.clock s.max_app) rest1 rest2 ∧
          LIST_REL (val_rel (:'ffi) s'.clock s.max_app) used1 used2`
           by metis_tac[EVERY2_APPEND, LENGTH_APPEND] >>
         Q.UNDISCH_THEN `val_rel (:'ffi) s'.clock s.max_app v v'` mp_tac >>
         simp[val_rel_cl_rw] >>
         disch_then
           (qspecl_then [`s'.clock - 1`, `used1`, `used2`, `s`, `s'`, `loc`]
                        mp_tac) >> simp[] >>
         `s'.clock - 1 ≤ s'.clock` by decide_tac >>
         `state_rel (s'.clock - 1) s.max_app s s' ∧
          LIST_REL (val_rel (:'ffi) (s'.clock - 1) s.max_app) used1 used2`
            by metis_tac[val_rel_mono, val_rel_mono_list] >> simp[] >>
         simp[exec_rel_rw, evaluate_ev_def] >>
         disch_then (qspec_then `s'.clock - 1` mp_tac) >>
         simp[dec_clock_def, evaluate_def] >>
         Cases_on `rest1 = []`
         >- (full_simp_tac(srw_ss())[LENGTH_NIL, LENGTH_NIL_SYM] >> rveq >> full_simp_tac(srw_ss())[evaluate_def]) >>
         `(∃r1 s1.
            evaluate ([b1], env1, s with clock := s'.clock - LENGTH used2) =
            (r1, s1)) ∧
          (∃r2 s2.
            evaluate ([b2], env2, s' with clock := s'.clock - LENGTH used2) =
            (r2, s2))` by metis_tac[PAIR] >> simp[] >>
         `(∃rv1. r1 = Rval [rv1]) ∨ (∃a1. r1 = Rerr (Rraise a1)) ∨
          r1 = Rerr (Rabort Rtimeout_error) ∨ r1 = Rerr (Rabort Rtype_error)`
           by (Cases_on `r1` >- (simp[] >> metis_tac[evaluate_SING]) >>
               rename1 `Rerr ee = Rerr _` >> Cases_on `ee` >> simp[] >>
               rename1 `aa = Rtype_error` >> Cases_on `aa` >> simp[]) >>
         rveq >>
         dsimp[SimpL ``$==>``, res_rel_rw, case_eq_thms]
         >- (qx_gen_tac `rv2` >> simp[] >> strip_tac >> first_assum irule
             >- first_x_assum ACCEPT_TAC >>
             qexists_tac `s1.clock` >> simp[] >>
             `s2.clock < s'.clock`
               suffices_by
               metis_tac[val_rel_mono_list, DECIDE ``x:num < y ⇒ x ≤ y``] >>
             imp_res_tac evaluate_clock >> lfs[])
         >- csimp[res_rel_rw]
         >- csimp[res_rel_rw])
     >- ((* LENGTH used1 < LENGTH used2 *)
         `LENGTH rest2 < LENGTH rest1` by simp[] >>
         `rest1 ≠ []` by (strip_tac >> lfs[]) >>
         `loc = NONE` by metis_tac[dest_closure_none_loc] >> rveq >>
         `LENGTH rest2 + LENGTH used2 - LENGTH rest1 = LENGTH used1`
           by simp[] >> simp[dec_clock_def] >>
         `s'.clock < LENGTH used1 ∨ LENGTH used1 ≤ s'.clock` by simp[]
         >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, ZERO_LESS_EQ]) >>
         qabbrev_tac `upfx2 = TAKE (LENGTH used2 - LENGTH used1) used2` >>
         qabbrev_tac `usfx2 = DROP (LENGTH used2 - LENGTH used1) used2` >>
         `LENGTH usfx2 = LENGTH used1` by simp[Abbr`usfx2`] >>
         `used2 = upfx2 ++ usfx2` by simp[Abbr`upfx2`, Abbr`usfx2`] >>
         `usfx2 ≠ []` by (strip_tac >> full_simp_tac(srw_ss())[]) >>
         markerLib.RM_ALL_ABBREVS_TAC >> rveq >> full_simp_tac(srw_ss())[] >>
         full_simp_tac (srw_ss() ++ numSimps.ARITH_NORM_ss) [] >> full_simp_tac(srw_ss())[] >>
         simp[] >>
         `upfx2 ≠ []` by (strip_tac >> full_simp_tac(srw_ss())[]) >>
         `∃cl2. dest_closure s.max_app NONE v' usfx2 = SOME (Partial_app cl2) ∧
                dest_closure s.max_app NONE cl2 upfx2 = SOME (Full_app b2 env2 [])`
           by metis_tac[dest_closure_NONE_Full_to_Partial] >>
         rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
         `LIST_REL (val_rel (:'ffi) s'.clock s.max_app) rest1 (rest2 ++ upfx2) ∧
          LIST_REL (val_rel (:'ffi) s'.clock s.max_app) used1 usfx2`
            by metis_tac[LENGTH_APPEND, EVERY2_APPEND, APPEND_ASSOC] >>
         qspecl_then [`s'.clock`, `s.max_app`, `v`, `v'`] mp_tac val_rel_cl_rw >> simp[] >>
         disch_then (qspecl_then [`s'.clock - 1`, `used1`, `usfx2`,
                                  `s`, `s'`, `NONE`]
                                 mp_tac) >> simp[] >>
         `state_rel (s'.clock - 1) s.max_app s s'`
           by metis_tac[val_rel_mono, DECIDE ``x - 1n ≤ x``] >>
         pop_assum (fn th => simp[th]) >>
         `LIST_REL (val_rel (:'ffi) (s'.clock - 1) s.max_app) used1 usfx2`
           by metis_tac[val_rel_mono_list, DECIDE ``x - 1n ≤ x``] >>
         pop_assum (fn th => simp[th]) >>
         simp[exec_rel_rw, evaluate_ev_def] >>
         disch_then (qspec_then `s'.clock - 1` mp_tac) >> simp[] >>
         `(∃r1 s1.
            evaluate ([b1], env1, s with clock := s'.clock - LENGTH used1) =
            (r1, s1))` by metis_tac[PAIR] >>
         `(∃rv1. r1 = Rval [rv1]) ∨ (∃a1. r1 = Rerr (Rraise a1)) ∨
          r1 = Rerr (Rabort Rtimeout_error) ∨ r1 = Rerr (Rabort Rtype_error)`
           by (Cases_on `r1` >- (simp[] >> metis_tac[evaluate_SING]) >>
               rename1 `Rerr ee = Rerr _` >> Cases_on `ee` >> simp[] >>
               rename1 `aa = Rtype_error` >> Cases_on `aa` >> simp[]) >>
         rveq >>
         dsimp[SimpL ``$==>``, res_rel_rw, bool_case_eq, case_eq_thms, pair_case_eq] >>
         simp[] >> strip_tac >>
         qmatch_abbrev_tac `res_rel _ (evaluate_app NONE rv1 rest1 s1) RHS` >>
         rename1 `state_rel s1.clock _ s1 s2` >>
         `RHS = evaluate_app NONE cl2 (rest2 ++ upfx2)
                   (s2 with clock := s1.clock)`
           suffices_by (
             disch_then SUBST1_TAC >> first_assum irule
             >- first_x_assum ACCEPT_TAC >>
             simp[] >> metis_tac[val_rel_mono_list, DECIDE ``x:num - y ≤ x``])>>
         simp[Abbr`RHS`] >> full_simp_tac(srw_ss())[] >>
         simp[Once evaluate_app_rw, SimpRHS] >>
         Q.UNDISCH_THEN
           `dest_closure s.max_app NONE cl2 upfx2 = SOME (Full_app b2 env2 [])`
           (fn th => mp_tac (MATCH_MP (dest_closure_full_addargs
                                         |> GEN_ALL
                                         |> REWRITE_RULE [GSYM AND_IMP_INTRO])
                                      th)) >>
         disch_then (qspec_then `rest2` mp_tac) >>
         `LENGTH rest2 + LENGTH upfx2 ≤ s.max_app`
           by (imp_res_tac dest_closure_full_maxapp >> full_simp_tac(srw_ss())[] >> simp[]) >>
         simp[dec_clock_def] >>
         `LENGTH rest1 + LENGTH used1 - LENGTH rest2 =
           LENGTH upfx2 + LENGTH used1` by simp[] >> simp[] >> srw_tac[][] >>
         `s2.clock - (LENGTH upfx2 + LENGTH used1) =
          LENGTH rest2 + s2.clock - (LENGTH rest1 + LENGTH used1)` by simp[] >>
          simp[]
        )
     >- ((* LENGTH used2 < LENGTH used1 *)
         `LENGTH rest1 < LENGTH rest2` by simp[] >>
         `rest2 ≠ []` by (strip_tac >> lfs[]) >>
         `loc = NONE` by metis_tac[dest_closure_none_loc] >> rveq >>
         `LENGTH rest2 + LENGTH used2 - LENGTH rest1 = LENGTH used1`
           by simp[] >> simp[dec_clock_def] >>
         `s'.clock < LENGTH used2 ∨ LENGTH used2 ≤ s'.clock` by simp[]
         >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, ZERO_LESS_EQ]) >>
         qabbrev_tac `upfx1 = TAKE (LENGTH used1 - LENGTH used2) used1` >>
         qabbrev_tac `usfx1 = DROP (LENGTH used1 - LENGTH used2) used1` >>
         `LENGTH usfx1 = LENGTH used2` by simp[Abbr`usfx1`] >>
         `used1 = upfx1 ++ usfx1` by simp[Abbr`upfx1`, Abbr`usfx1`] >>
         `usfx1 ≠ []` by (strip_tac >> full_simp_tac(srw_ss())[]) >>
         markerLib.RM_ALL_ABBREVS_TAC >> rveq >> full_simp_tac(srw_ss())[] >>
         full_simp_tac (srw_ss() ++ numSimps.ARITH_NORM_ss) [] >> full_simp_tac(srw_ss())[] >>
         simp[] >>
         `upfx1 ≠ []` by (strip_tac >> full_simp_tac(srw_ss())[]) >>
         `∃cl1. dest_closure s.max_app NONE v usfx1 = SOME (Partial_app cl1) ∧
                dest_closure s.max_app NONE cl1 upfx1 = SOME (Full_app b1 env1 [])`
           by metis_tac[dest_closure_NONE_Full_to_Partial] >>
         rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
         `LIST_REL (val_rel (:'ffi) s'.clock s.max_app) (rest1 ++ upfx1) rest2 ∧
          LIST_REL (val_rel (:'ffi) s'.clock s.max_app) usfx1 used2`
            by metis_tac[LENGTH_APPEND, EVERY2_APPEND, APPEND_ASSOC] >>
         qspecl_then [`s'.clock`, `s.max_app`, `v`, `v'`] mp_tac val_rel_cl_rw >> simp[] >>
         disch_then (qspecl_then [`s'.clock - 1`, `usfx1`, `used2`,
                                  `s`, `s'`, `NONE`]
                                 mp_tac) >> simp[] >>
         `state_rel (s'.clock - 1) s.max_app s s'`
           by metis_tac[val_rel_mono, DECIDE ``x - 1n ≤ x``] >>
         pop_assum (fn th => simp[th]) >>
         `LIST_REL (val_rel (:'ffi) (s'.clock - 1) s.max_app) usfx1 used2`
           by metis_tac[val_rel_mono_list, DECIDE ``x - 1n ≤ x``] >>
         pop_assum (fn th => simp[th]) >>
         simp[exec_rel_rw, evaluate_ev_def] >>
         disch_then (qspec_then `s'.clock - 1` mp_tac) >> simp[] >>
         `(∃r2 s2.
            evaluate ([b2], env2, s' with clock := s'.clock - LENGTH used2) =
            (r2, s2))` by metis_tac[PAIR] >>
         `(∃rv2. r2 = Rval [rv2]) ∨ (∃a2. r2 = Rerr (Rraise a2)) ∨
          r2 = Rerr (Rabort Rtimeout_error) ∨ r2 = Rerr (Rabort Rtype_error)`
           by (Cases_on `r2` >- (simp[] >> metis_tac[evaluate_SING]) >>
               rename1 `Rerr ee = Rerr _` >> Cases_on `ee` >> simp[] >>
               rename1 `aa = Rtype_error` >> Cases_on `aa` >> simp[]) >>
         rveq >>
         dsimp[SimpL ``$==>``, res_rel_rw, bool_case_eq, case_eq_thms, pair_case_eq] >>
         simp[] >> strip_tac >>
         qmatch_abbrev_tac `res_rel _ LHS (evaluate_app NONE rv2 rest2 s2)` >>
         full_simp_tac(srw_ss())[] >> rename1 `state_rel s2.clock _ s1 s2` >>
         `LHS = evaluate_app NONE cl1 (rest1 ++ upfx1)
                   (s1 with clock := s2.clock)`
           suffices_by (
             disch_then SUBST1_TAC >> first_assum irule
             >- full_simp_tac(srw_ss())[LENGTH_NIL] >>
             simp[] >> metis_tac[val_rel_mono_list, DECIDE ``x:num - y ≤ x``])>>
         simp[Abbr`LHS`] >> full_simp_tac(srw_ss())[] >>
         simp[Once evaluate_app_rw, SimpRHS] >>
         Q.UNDISCH_THEN
           `dest_closure s1.max_app NONE cl1 upfx1 = SOME (Full_app b1 env1 [])`
           (fn th => mp_tac (MATCH_MP (dest_closure_full_addargs
                                         |> GEN_ALL
                                         |> REWRITE_RULE [GSYM AND_IMP_INTRO])
                                      th)) >>
         disch_then (qspec_then `rest1` mp_tac) >>
         `LENGTH rest1 + LENGTH upfx1 ≤ s1.max_app`
           by (imp_res_tac dest_closure_full_maxapp >> full_simp_tac(srw_ss())[] >> simp[]) >>
         simp[dec_clock_def] >>
         `s'.clock < LENGTH upfx1 + LENGTH used2 ⇔ s2.clock < LENGTH upfx1`
            by simp[] >> simp[] >> srw_tac[][] >>
         `s'.clock - (LENGTH upfx1 + LENGTH used2) = s2.clock - LENGTH upfx1`
            by simp[] >>
         simp[]
        )
    )
)

val state_rel_refs = Q.prove (
`!c w (s:'ffi closSem$state) s' n rv p.
  state_rel c w s s' ∧
  FLOOKUP s.refs p = SOME rv
  ⇒
  ?rv'.
    FLOOKUP s'.refs p = SOME rv' ∧
    ref_v_rel (:'ffi) c w rv rv'`,
 srw_tac[][Once state_rel_rw] >>
 full_simp_tac(srw_ss())[fmap_rel_OPTREL_FLOOKUP] >>
 last_x_assum (qspec_then `p` mp_tac) >>
 full_simp_tac(srw_ss())[OPTREL_SOME] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[]);

val do_eq_val_rel = Q.store_thm ("do_eq_val_rel",
`(!v1 v2 i w v1' v2' res.
  val_rel (:'ffi) i w v1 v1' ∧
  val_rel (:'ffi) i w v2 v2'
  ⇒
  do_eq v1 v2 = do_eq v1' v2') ∧
 (!vs1 vs2 i w vs1' vs2'.
  LIST_REL (val_rel (:'ffi) i w) vs1 vs1' ∧
  LIST_REL (val_rel (:'ffi) i w) vs2 vs2'
  ⇒
  do_eq_list vs1 vs2 = do_eq_list vs1' vs2')`,
 ho_match_mp_tac do_eq_ind
 \\ conj_tac
 >- (
   simp[PULL_FORALL]
   \\ rpt gen_tac \\ strip_tac
   \\ strip_tac
   \\ Cases_on`v1`\\Cases_on`v1'`\\full_simp_tac(srw_ss())[val_rel_rw,is_closure_def]
   \\ srw_tac[][do_eq_def]
   \\ every_case_tac \\ full_simp_tac(srw_ss())[val_rel_rw,is_closure_def]
   \\ metis_tac[LIST_REL_LENGTH] )
 \\ conj_tac >- srw_tac[][do_eq_def]
 \\ conj_tac
 >- (
   simp[PULL_FORALL]
   \\ rpt gen_tac \\ strip_tac
   \\ strip_tac \\ rveq
   \\ simp[Once do_eq_def]
   \\ simp[Once do_eq_def,SimpRHS]
   \\ every_case_tac \\ full_simp_tac(srw_ss())[val_rel_rw,is_closure_def]
   \\ metis_tac[LIST_REL_LENGTH,semanticPrimitivesTheory.eq_result_11,semanticPrimitivesTheory.eq_result_distinct] )
 \\ srw_tac[][do_eq_def]
 \\ srw_tac[][do_eq_def]);

val get_global_state_rel = Q.store_thm ("get_global_state_rel",
`!i w (s : 'ffi closSem$state) s'.
  state_rel i w s s'
  ⇒
  OPTREL (OPTREL (val_rel (:'ffi) i w)) (get_global n s.globals) (get_global n s'.globals)`,
 srw_tac[][Once state_rel_rw, get_global_def] >>
 full_simp_tac(srw_ss())[quotient_optionTheory.OPTION_REL_def] >>
 imp_res_tac LIST_REL_LENGTH >>
 full_simp_tac(srw_ss())[] >>
 metis_tac [LIST_REL_EL_EQN]);

val v_to_list_val_rel = Q.store_thm ("v_to_list_val_rel",
`!v v' i w.
  val_rel (:'ffi) i w v v'
  ⇒
  OPTREL (LIST_REL (val_rel (:'ffi) i w)) (v_to_list v) (v_to_list v')`,
 ho_match_mp_tac v_to_list_ind >>
 srw_tac[][v_to_list_def] >>
 Cases_on `v'` >>
 srw_tac[][v_to_list_def] >>
 full_simp_tac(srw_ss())[val_rel_rw, is_closure_def] >>
 srw_tac[][v_to_list_def, OPTREL_SOME] >>
 TRY (simp [OPTREL_def] >> NO_TAC) >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[OPTREL_def] >>
 metis_tac [NOT_SOME_NONE, SOME_11]);

val LIST_REL_SNOC = prove(
  ``!xs x ys.
      LIST_REL P (xs ++ [x]) ys <=>
      ?y zs. ys = zs ++ [y] /\ LIST_REL P xs zs /\ P x y``,
  Induct \\ fs [] \\ rw [] \\ fs [PULL_EXISTS] \\ metis_tac []);

val res_rel_do_app = Q.store_thm ("res_rel_do_app",
`!c w op vs vs' (s:'ffi closSem$state) s'.
  state_rel c w s s' ∧
  LIST_REL (val_rel (:'ffi) c w) vs vs' ∧
  s.clock = c ∧
  s'.clock = c
  ⇒
  res_rel w
  (case do_app op (REVERSE vs) s of
     Rval (v,s) => (Rval [v],s)
   | Rerr err => (Rerr err,s))
  (case do_app op (REVERSE vs') s' of
     Rval (v,s') => (Rval [v],s')
   | Rerr err => (Rerr err,s'))`,
 srw_tac[][] >>
 Cases_on `op = ConfigGC` THEN1
  (Cases_on `do_app op (REVERSE vs) s` >>
   `?v s'. a = (v,s')` by metis_tac [pair_CASES] >>
   srw_tac[][] >>
   srw_tac[][res_rel_rw] >>
   fs[do_app_cases_val,do_app_cases_err] >> rw[] >>
   TRY (Cases_on `e`) >>
   srw_tac[][res_rel_rw] >>
   fs [do_app_cases_err] >>
   TRY (Cases_on `a`) >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   fs [do_app_cases_timeout] >>
   full_simp_tac(srw_ss())[] >>
   fs[SWAP_REVERSE_SYM] >> rveq >> fs [] >>
   full_simp_tac(srw_ss())[do_app_def, val_rel_rw] >>
   Cases_on `y` >>
   full_simp_tac(srw_ss())[do_app_def, val_rel_rw] >>
   Cases_on `y'` >>
   full_simp_tac(srw_ss())[do_app_def, val_rel_rw,Unit_def]) >>
 Cases_on `do_app op (REVERSE vs) s`
 >- (`?v s'. a = (v,s')` by metis_tac [pair_CASES] >>
     srw_tac[][] >>
     srw_tac[][res_rel_rw] >>
     fs[do_app_cases_val] >> rw[] >>
     full_simp_tac(srw_ss())[do_app_def, val_rel_rw]
     >> TRY (
       fs[SWAP_REVERSE_SYM] >>
       Cases_on`y` >>
       fs[val_rel_rw, Boolv_def, LIST_REL_EL_EQN, ref_v_rel_rw] >>
       imp_res_tac state_rel_refs >>
       fs[val_rel_rw, Boolv_def, LIST_REL_EL_EQN, ref_v_rel_rw] >> rw[val_rel_rw] >>
       Cases_on `y'` >>
       fs[val_rel_rw, Boolv_def, LIST_REL_EL_EQN, ref_v_rel_rw] >> rw[val_rel_rw] >>
       NO_TAC)
     >- ((* global lookup *)
       imp_res_tac get_global_state_rel >>
       pop_assum (qspec_then `n` mp_tac) >>
       simp [OPTREL_SOME] >>
       srw_tac[][] >>
       srw_tac[][])
     >- ((* global extend *)
       srw_tac[][Unit_def, val_rel_rw] >>
       rpt (pop_assum mp_tac) >>
       ONCE_REWRITE_TAC [state_rel_rw] >>
       srw_tac[][] >>
       srw_tac[][OPTREL_def])
     >- (full_simp_tac(srw_ss())[LET_THM, SWAP_REVERSE_SYM] >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         `(LEAST ptr. ptr ∉ FDOM s.refs) = LEAST ptr. ptr ∉ FDOM s'.refs`
                by full_simp_tac(srw_ss())[Once state_rel_rw, fmap_rel_def] >>
         full_simp_tac(srw_ss())[Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         srw_tac[][ref_v_rel_rw])
     >- ((* global init *)
       imp_res_tac get_global_state_rel >>
       pop_assum (qspec_then `n'` mp_tac) >>
       simp [OPTREL_SOME] >>
       srw_tac[][] >>
       srw_tac[][] >>
       full_simp_tac(srw_ss())[OPTREL_def, val_rel_rw, Unit_def] >>
       rpt (pop_assum mp_tac) >>
       ONCE_REWRITE_TAC [state_rel_rw] >>
       srw_tac[][] >>
       match_mp_tac EVERY2_LUPDATE_same >>
       srw_tac[][OPTREL_SOME])
     >- (
       fs[SWAP_REVERSE_SYM]
       \\ Cases_on `vs' = []` \\ fs []
       \\ drule (SNOC_CASES |> REWRITE_RULE [METIS_PROVE [] ``b \/ v <=> ~b ==> v``])
       \\ strip_tac \\ fs [SNOC_APPEND] \\ fs []
       \\ fs[GSYM SWAP_REVERSE_SYM]
       \\ once_rewrite_tac [EVERY2_REVERSE1] \\ asm_rewrite_tac [])
     >- ( (* ConsExtend *)
       drule EVERY2_REVERSE >>
       asm_simp_tac bool_ss [] >>
       rw [] >>
       rename1 `val_rel _ _ _ _ arg` >>
       Cases_on `arg` >>
       fs [val_rel_rw] >>
       rename1 `val_rel _ _ _ _ arg` >>
       Cases_on `arg` >>
       fs [val_rel_rw] >>
       rename1 `val_rel _ _ _ _ arg` >>
       Cases_on `arg` >>
       fs [val_rel_rw] >>
       rename1 `val_rel _ _ _ _ arg` >>
       Cases_on `arg` >>
       fs [val_rel_rw] >>
       rw [] >>
       imp_res_tac LIST_REL_LENGTH
       >- intLib.ARITH_TAC >>
       simp [val_rel_rw] >>
       irule EVERY2_APPEND_suff >>
       simp [] >>
       irule EVERY2_TAKE >>
       irule EVERY2_DROP >>
       rw [])
     >- (full_simp_tac(srw_ss())[LET_THM, SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         rveq \\ simp[val_rel_rw] >>
         `(LEAST ptr. ptr ∉ FDOM s.refs) = LEAST ptr. ptr ∉ FDOM s'.refs`
                by full_simp_tac(srw_ss())[Once state_rel_rw, fmap_rel_def] >>
         full_simp_tac(srw_ss())[Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         srw_tac[][ref_v_rel_rw, LIST_REL_REPLICATE_same])
     >- (full_simp_tac(srw_ss())[LET_THM, SWAP_REVERSE_SYM] >>
         Cases_on `y'` >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         rveq \\ simp[val_rel_rw] >>
         `(LEAST ptr. ptr ∉ FDOM s.refs) = LEAST ptr. ptr ∉ FDOM s'.refs`
                by full_simp_tac(srw_ss())[Once state_rel_rw, fmap_rel_def] >>
         full_simp_tac(srw_ss())[Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         srw_tac[][ref_v_rel_rw, LIST_REL_REPLICATE_same])
     >- (full_simp_tac(srw_ss())[SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         Cases_on `y''` >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         srw_tac[][val_rel_rw] >>
         imp_res_tac state_rel_refs >>
         full_simp_tac(srw_ss())[ref_v_rel_rw] >>
         srw_tac[][val_rel_rw, Unit_def] >>
         full_simp_tac(srw_ss())[Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         simp [state_rel_rw])
     >- (
       fs[]
       \\ qpat_x_assum`$some _ = SOME _`mp_tac
       \\ DEEP_INTRO_TAC some_intro \\ fs[] \\ strip_tac \\ rveq
       \\ imp_res_tac v_to_list_val_rel
       \\ rfs[OPTREL_SOME]
       \\ fs[EVERY2_MAP]
       \\ DEEP_INTRO_TAC some_intro \\ fs[val_rel_rw]
       \\ fs[state_rel_refs]
       \\ reverse conj_asm2_tac
       >- (
         fs[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP]
         \\ map_every qexists_tac[`wss`]
         \\ simp[EL_MAP] \\ rfs[EL_MAP]
         \\ simp[GSYM FORALL_AND_THM,GSYM IMP_CONJ_THM]
         \\ qx_gen_tac`x` \\ strip_tac
         \\ rpt(first_x_assum(qspec_then`x`mp_tac))
         \\ Cases_on`EL x z` \\ simp[val_rel_rw])
       \\ rw[]
       \\ imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF] \\ rveq
       \\ imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF]
       \\ fs[EVERY2_MAP,val_rel_rw]
       \\ AP_TERM_TAC
       \\ fs[LIST_REL_EL_EQN,LIST_EQ_REWRITE])
     >- (
       fs[SWAP_REVERSE_SYM] \\ rw[] \\
       rpt(
         qhdtm_x_assum`val_rel`mp_tac \\
         qmatch_rename_tac`val_rel _ _ _ _ v ⇒ _` \\
         Cases_on`v` \\ rw[val_rel_rw] ) \\
       imp_res_tac state_rel_refs \\
       fs[case_eq_thms,PULL_EXISTS,ref_v_rel_rw] \\
       rw[Unit_def,val_rel_rw] \\
       fs[Once state_rel_rw]
       \\ match_mp_tac fmap_rel_FUPDATE_same
       \\ fs[ref_v_rel_rw] )
     >- (
       fs[SWAP_REVERSE_SYM] \\ rw[] \\
       rpt(
         qhdtm_x_assum`val_rel`mp_tac \\
         qmatch_rename_tac`val_rel _ _ _ _ v ⇒ _` \\
         Cases_on`v` \\ rw[val_rel_rw] ) \\
       imp_res_tac state_rel_refs \\
       fs[case_eq_thms,PULL_EXISTS,ref_v_rel_rw] \\
       rw[Unit_def,val_rel_rw] \\
       fs[Once state_rel_rw]
       \\ match_mp_tac fmap_rel_FUPDATE_same
       \\ fs[ref_v_rel_rw] )
     >- (
       fs[SWAP_REVERSE_SYM] \\ rw[] \\
       rpt(
         qhdtm_x_assum`val_rel`mp_tac \\
         qmatch_rename_tac`val_rel _ _ _ _ v ⇒ _` \\
         Cases_on`v` \\ rw[val_rel_rw] ) \\
       imp_res_tac state_rel_refs \\
       fs[case_eq_thms,PULL_EXISTS,ref_v_rel_rw] \\
       rw[Unit_def,val_rel_rw])
     >- (
       fs[SWAP_REVERSE_SYM] \\ rw[] \\
       rpt(
         qhdtm_x_assum`val_rel`mp_tac \\
         qmatch_rename_tac`val_rel _ _ _ _ v ⇒ _` \\
         Cases_on`v` \\ rw[val_rel_rw] ) \\
       imp_res_tac state_rel_refs \\
       fs[case_eq_thms,PULL_EXISTS,ref_v_rel_rw] \\
       rw[Unit_def,val_rel_rw])
     >- (
       imp_res_tac v_to_list_val_rel >>
       pop_assum mp_tac >>
       simp [OPTREL_SOME] >>
       srw_tac[][] >>
       srw_tac[][val_rel_rw])
     >- (
       Cases_on`REVERSE vs'` \\ fs[] \\ rfs[PULL_EXISTS] \\
       fs[SWAP_REVERSE_SYM,LIST_REL_REVERSE_EQ] \\
       rpt(qpat_x_assum`$some _ = _`mp_tac) \\
       rpt(DEEP_INTRO_TAC some_intro) \\ fs[] \\ rw[val_rel_rw] \\
       spose_not_then strip_assume_tac \\
       imp_res_tac v_to_list_val_rel \\ fs[] \\ rfs[OPTREL_def] \\
       TRY (
         fs[EVERY2_MAP,val_rel_rw] \\
         fs[LIST_EQ_REWRITE,LIST_REL_EL_EQN,EL_MAP] \\
         NO_TAC ) \\ fs[] \\
       qhdtm_x_assum`$!`mp_tac \\ simp[] \\
       first_assum(part_match_exists_tac (el 2 o strip_conj) o concl) \\ fs[] \\
       rfs[LIST_REL_EL_EQN,LIST_EQ_REWRITE,EL_MAP] \\ rw[] \\
       first_x_assum(qspec_then`x`mp_tac) \\ simp[] \\
       Cases_on`EL x y0` \\ fs[val_rel_rw])
     >- (full_simp_tac(srw_ss())[LET_THM] >>
         srw_tac[][val_rel_rw] >>
         `(LEAST ptr. ptr ∉ FDOM s.refs) = LEAST ptr. ptr ∉ FDOM s'.refs`
                by full_simp_tac(srw_ss())[Once state_rel_rw, fmap_rel_def] >>
         full_simp_tac(srw_ss())[Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         fs[SWAP_REVERSE_SYM] >>
         srw_tac[][ref_v_rel_rw, EVERY2_REVERSE] >>
         imp_res_tac EVERY2_REVERSE \\ fs[LIST_REL_SNOC] >>
         once_rewrite_tac [EVERY2_REVERSE1] \\ asm_rewrite_tac [])
     >- (full_simp_tac(srw_ss())[SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         Cases_on `y'` >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         srw_tac[][] >>
         imp_res_tac state_rel_refs >>
         full_simp_tac(srw_ss())[ref_v_rel_rw, LIST_REL_EL_EQN] >>
         srw_tac[][] >>
         `Num i < LENGTH xs` by intLib.ARITH_TAC
         >- metis_tac [MEM_EL] >>
         intLib.ARITH_TAC)
     >- (full_simp_tac(srw_ss())[SWAP_REVERSE_SYM] >>
         Cases_on `y'` >>
         Cases_on `y''` >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         srw_tac[][] >>
         imp_res_tac state_rel_refs >>
         full_simp_tac(srw_ss())[ref_v_rel_rw, LIST_REL_EL_EQN] >>
         srw_tac[][val_rel_rw, Unit_def]
         >- (full_simp_tac(srw_ss())[Once state_rel_rw] >>
             match_mp_tac fmap_rel_FUPDATE_same >>
             srw_tac[][ref_v_rel_rw] >>
             match_mp_tac EVERY2_LUPDATE_same >>
             srw_tac[][LIST_REL_EL_EQN])
         >- intLib.ARITH_TAC)
     >- (fs[SWAP_REVERSE_SYM] >>
         Cases_on `y` >> Cases_on `y'` >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         srw_tac[][] >>
         imp_res_tac state_rel_refs >>
         full_simp_tac(srw_ss())[ref_v_rel_rw, LIST_REL_EL_EQN] >>
         srw_tac[][] >>
         `s'.ffi = s.ffi` by full_simp_tac(srw_ss())[Once state_rel_rw] >>
         srw_tac[][Unit_def, val_rel_rw] >>
         full_simp_tac(srw_ss())[Once state_rel_rw] >>
         match_mp_tac fmap_rel_FUPDATE_same >>
         srw_tac[][ref_v_rel_rw])
     >- (full_simp_tac(srw_ss())[SWAP_REVERSE_SYM] >>
         Cases_on `do_eq x1 x2` >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         `do_eq y' y = Eq_val b` by metis_tac [do_eq_val_rel] >>
         srw_tac[][val_rel_rw, Boolv_def])
     >- (full_simp_tac(srw_ss())[SWAP_REVERSE_SYM] >>
         Cases_on `y` >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         Cases_on `y'` >>
         full_simp_tac(srw_ss())[val_rel_rw] >>
         srw_tac[][val_rel_rw, Boolv_def] >>
         fs [LIST_REL_EL_EQN] \\ rfs []))
 >- (Cases_on `e` >>
     srw_tac[][res_rel_rw]
     >- (imp_res_tac do_app_cases_err >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         Cases_on `do_eq x1 x2` >>
         full_simp_tac(srw_ss())[] >>
         `vs = REVERSE [x1;x2]` by metis_tac [REVERSE_REVERSE] >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][do_app_def] >>
         imp_res_tac do_eq_val_rel >>
         every_case_tac >>
         full_simp_tac(srw_ss())[val_rel_rw])
     >- (Cases_on `a` >>
         full_simp_tac(srw_ss())[res_rel_rw] >>
         imp_res_tac do_app_cases_timeout >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][] >>
         Cases_on `do_eq x1 x2` >>
         full_simp_tac(srw_ss())[])));

val val_rel_lookup_vars = Q.store_thm ("val_rel_lookup_vars",
`!c w vars vs1 vs1' vs2.
  LIST_REL (val_rel (:'ffi) c w) vs1 vs1' ∧
  lookup_vars vars vs1 = SOME vs2
  ⇒
  ?vs2'.
    lookup_vars vars vs1' = SOME vs2' ∧
    LIST_REL (val_rel (:'ffi) c w) vs2 vs2'`,
 Induct_on `vars` >>
 full_simp_tac(srw_ss())[lookup_vars_def] >>
 srw_tac[][] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[]
 >- (res_tac >> full_simp_tac(srw_ss())[]) >>
 imp_res_tac LIST_REL_LENGTH >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][]
 >- (full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> metis_tac [MEM_EL]) >>
 metis_tac [SOME_11]);

val val_rel_clos_env = Q.store_thm ("val_rel_clos_env",
`!c w restrict vars vs1 vs1' vs2.
  LIST_REL (val_rel (:'ffi) c w) vs1 vs1' ∧
  clos_env restrict vars vs1 = SOME vs2
  ⇒
  ?vs2'.
    clos_env restrict vars vs1' = SOME vs2' ∧
    LIST_REL (val_rel (:'ffi) c w) vs2 vs2'`,
 srw_tac[][clos_env_def] >>
 srw_tac[][] >>
 metis_tac [val_rel_lookup_vars]);

val compat_nil = Q.store_thm ("compat_nil",
`exp_rel (:'ffi) w [] []`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_def, res_rel_rw, evaluate_ev_def] >>
 metis_tac [val_rel_mono]);

val compat_cons = Q.store_thm ("compat_cons",
`!e es e' es'.
  exp_rel (:'ffi) w [e] [e'] ∧
  exp_rel (:'ffi) w es es'
  ⇒
  exp_rel (:'ffi) w (e::es) (e'::es')`,
 srw_tac[][exp_rel_def] >>
 simp [exec_rel_rw, evaluate_ev_def] >>
 ONCE_REWRITE_TAC [evaluate_CONS] >>
 srw_tac[][] >>
 `exec_rel i' w (Exp [e] env, s with clock := i') (Exp [e'] env', s' with clock := i')`
 by (
   first_x_assum match_mp_tac \\ simp[]
   \\ metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] ) >>
 pop_assum mp_tac >>
 simp [exec_rel_rw, evaluate_ev_def] >>
 srw_tac[][] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 srw_tac[][] >>
 reverse ((Q.ISPEC_THEN `evaluate ([e],env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- metis_tac [] >>
 first_x_assum (qspecl_then [`s''.clock`, `env`, `env'`, `s''`, `s'''`] mp_tac) >>
 imp_res_tac evaluate_clock >>
 imp_res_tac evaluate_const >>
 full_simp_tac(srw_ss())[] >>
 `LIST_REL (val_rel (:'ffi) s'''.clock w) env env'` by metis_tac [val_rel_mono_list] >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][] >>
 pop_assum (qspec_then `s'''.clock` mp_tac) >>
 srw_tac[][clock_lemmas] >>
 `(s'' with clock := s'''.clock) = s''` by metis_tac [clock_lemmas] >>
 full_simp_tac(srw_ss())[] >>
 reverse (Q.ISPEC_THEN `evaluate (es,env,s'')` strip_assume_tac result_store_cases) >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- metis_tac [] >>
 imp_res_tac evaluate_clock >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac evaluate_SING >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 metis_tac [val_rel_mono]);

val compat_var = Q.store_thm ("compat_var",
`!n t t'. exp_rel (:'ffi) w [Var t n] [Var t' n]`,
 srw_tac[][exp_rel_def, exec_rel_rw, evaluate_ev_def, evaluate_def] >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
 metis_tac [MEM_EL, val_rel_mono]);

val compat_if = Q.store_thm ("compat_if",
`!e1 e2 e3 e1' e2' e3' t t'.
  exp_rel (:'ffi) w [e1] [e1'] ∧
  exp_rel (:'ffi) w [e2] [e2'] ∧
  exp_rel (:'ffi) w [e3] [e3']
  ⇒
  exp_rel (:'ffi) w [If t1 e1 e2 e3] [If t1' e1' e2' e3']`,
 srw_tac[][Boolv_def, exp_rel_def, exec_rel_rw, evaluate_ev_def, evaluate_def] >>
 full_simp_tac(srw_ss())[PULL_FORALL] >>
 imp_res_tac val_rel_mono >>
 imp_res_tac val_rel_mono_list >>
 last_x_assum (qspecl_then [`i'`, `env`, `env'`, `s`, `s'`, `i'`] mp_tac) >>
 reverse ((Q.ISPEC_THEN `evaluate ([e1],env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 srw_tac[][res_rel_rw] >>
 simp []
 >- metis_tac [] >>
 `?v v'. vs = [v] ∧ vs' = [v']` by metis_tac [evaluate_SING] >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[val_rel_rw]
 >- (imp_res_tac evaluate_clock >>
     imp_res_tac evaluate_const >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [val_rel_mono_list, LESS_EQ_REFL, clock_lemmas])
 >- (Cases_on `v'` >>
     full_simp_tac(srw_ss())[val_rel_rw] >>
     full_simp_tac(srw_ss())[])
 >- (imp_res_tac evaluate_clock >>
     imp_res_tac evaluate_const >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [val_rel_mono_list, LESS_EQ_REFL, clock_lemmas])
 >- (Cases_on `v'` >>
     full_simp_tac(srw_ss())[val_rel_rw] >>
     full_simp_tac(srw_ss())[]));

val compat_let = Q.store_thm ("compat_let",
`!e es e' es' t t'.
  exp_rel (:'ffi) w es es' ∧
  exp_rel (:'ffi) w [e] [e']
  ⇒
  exp_rel (:'ffi) w [Let t es e] [Let t' es' e']`,
 srw_tac[][exp_rel_def] >>
 simp [exec_rel_rw, evaluate_ev_def, evaluate_def] >>
 srw_tac[][] >>
 `exec_rel i' w (Exp es env, s with clock := i') (Exp es' env', s' with clock := i')`
 by (
   first_x_assum match_mp_tac \\ simp[]
   \\ metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] ) >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 srw_tac[][] >>
 reverse ((Q.ISPEC_THEN `evaluate (es,env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- metis_tac [] >>
 first_x_assum (qspecl_then [`s''.clock`, `vs++env`, `vs'++env'`, `s''`, `s'''`] mp_tac) >>
 imp_res_tac evaluate_clock >>
 imp_res_tac evaluate_const >>
 full_simp_tac(srw_ss())[] >>
 `LIST_REL (val_rel (:'ffi) s'''.clock w) env env'` by metis_tac [val_rel_mono_list] >>
 imp_res_tac EVERY2_APPEND >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 metis_tac [clock_lemmas, LESS_EQ_REFL]);

val compat_raise = Q.store_thm ("compat_raise",
`!e e' t t'.
  exp_rel (:'ffi) w [e] [e']
  ⇒
  exp_rel (:'ffi) w [Raise t e] [Raise t' e']`,
 srw_tac[][exp_rel_def] >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][evaluate_def] >>
 `exec_rel i' w (Exp [e] env, s with clock := i') (Exp [e'] env', s' with clock := i')`
         by metis_tac [val_rel_mono, val_rel_mono_list, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 srw_tac[][] >>
 reverse ((Q.ISPEC_THEN `evaluate ([e],env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- metis_tac [] >>
 imp_res_tac evaluate_SING >>
 full_simp_tac(srw_ss())[]);

val compat_handle = Q.store_thm ("compat_handle",
`!e1 e2 e1' e2' t t'.
  exp_rel (:'ffi) w [e1] [e1'] ∧
  exp_rel (:'ffi) w [e2] [e2']
  ⇒
  exp_rel (:'ffi) w [Handle t e1 e2] [Handle t' e1' e2']`,
 srw_tac[][exp_rel_def] >>
 srw_tac[][evaluate_ev_def, exec_rel_rw, evaluate_def] >>
 `exec_rel i' w (Exp [e1] env,s with clock := i') (Exp [e1'] env',s' with clock := i')`
 by (
   first_x_assum match_mp_tac \\ simp[]
   \\ metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] ) >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 srw_tac[][] >>
 reverse ((Q.ISPEC_THEN `evaluate ([e1],env,s with clock := i')` strip_assume_tac
                         result_store_cases)) >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[res_rel_rw] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac evaluate_clock >>
 imp_res_tac evaluate_const >>
 full_simp_tac(srw_ss())[] >>
 imp_res_tac val_rel_mono_list >>
 first_x_assum (qspecl_then [`s''.clock`, `v::env`, `v'::env'`, `s''`, `s'''`] mp_tac) >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][] >>
 pop_assum (qspec_then `s'''.clock` mp_tac) >>
 srw_tac[][] >>
 `(s'' with clock := s'''.clock) = s''` by metis_tac [clock_lemmas] >>
 full_simp_tac(srw_ss())[clock_lemmas] >>
 reverse (strip_assume_tac (Q.ISPEC `evaluate ([e2],v::env,s'')`
                         result_store_cases)) >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[res_rel_rw]);

val compat_tick = Q.store_thm ("compat_tick",
`!e e' t t'.
  exp_rel (:'ffi) w [e] [e']
  ⇒
  exp_rel (:'ffi) w [Tick t e] [Tick t' e']`,
 srw_tac[][exp_rel_def] >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][evaluate_def, res_rel_rw]
 >- (`0 ≤ i` by decide_tac >>
     metis_tac [val_rel_mono]) >>
 full_simp_tac(srw_ss())[dec_clock_def] >>
 `exec_rel i' w (Exp [e] env,s with clock := i'-1) (Exp [e'] env',s' with clock := i'-1)`
 by (
   first_x_assum match_mp_tac \\ simp[]
   \\ metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] ) >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][]);

val compat_call = Q.store_thm ("compat_call",
`!ticks n es es' t t'.
  exp_rel (:'ffi) w es es'
  ⇒
  exp_rel (:'ffi) w [Call t ticks n es] [Call t' ticks n es']`,
 srw_tac[][exp_rel_def] >>
 simp [evaluate_ev_def, exec_rel_rw, evaluate_def] >>
 srw_tac[][] >>
 `exec_rel i' w (Exp es env, s with clock := i') (Exp es' env', s' with clock := i')`
 by (
   first_x_assum match_mp_tac \\ simp[]
   \\ metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] ) >>
 pop_assum mp_tac >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 srw_tac[][] >>
 reverse ((Q.ISPEC_THEN `evaluate (es,env,s with clock := i')`strip_assume_tac
                         result_store_cases)) >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- metis_tac [] >>
 Cases_on `find_code n vs s''.code` >>
 full_simp_tac(srw_ss())[res_rel_rw] >>
 `?args e. x = (args,e)` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss())[] >>
 `?args' e'.
   find_code n vs' s'''.code = SOME (args',e') ∧
   LIST_REL (val_rel (:'ffi) s'''.clock w) args args' ∧
   (¬(s'''.clock < ticks+1) ⇒ exec_rel (s'''.clock − (ticks+1)) w (Exp [e] args,s'') (Exp [e'] args',s'''))`
         by metis_tac [find_code_related] >>
 srw_tac[][res_rel_rw]
 >- (`0 ≤ s'''.clock` by decide_tac >>
     metis_tac [val_rel_mono]) >>
 full_simp_tac(srw_ss())[evaluate_ev_def, exec_rel_rw, dec_clock_def] >>
 `s'''.clock - (ticks+1) ≤ s'''.clock - (ticks+1)` by decide_tac >>
 metis_tac []);

val compat_app = Q.store_thm ("compat_app",
`!loc e es e' es' t t'.
  exp_rel (:'ffi) w [e] [e'] ∧
  exp_rel (:'ffi) w es es'
  ⇒
  exp_rel (:'ffi) w [App t loc e es] [App t' loc e' es']`,
 srw_tac[][exp_rel_def] >>
 simp [evaluate_ev_def, exec_rel_rw, evaluate_def] >>
 Cases_on `LENGTH es > 0` >>
 simp [res_rel_rw] >>
 qx_gen_tac `j` >>
 DISCH_TAC >>
 first_x_assum (qspecl_then [`j`, `env`, `env'`, `s`, `s'`] mp_tac) >>
 imp_res_tac val_rel_mono >>
 imp_res_tac val_rel_mono_list >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 disch_then (qspec_then `j` assume_tac) >>
 full_simp_tac(srw_ss())[] >>
 reverse ((Q.ISPEC_THEN `evaluate (es,env,s with clock := j)`strip_assume_tac
                         result_store_cases)) >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- (Cases_on `es'` >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[evaluate_def])
 >- (Cases_on `es'` >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[evaluate_def]) >>
 imp_res_tac evaluate_IMP_LENGTH >>
 imp_res_tac LIST_REL_LENGTH >>
 full_simp_tac(srw_ss())[] >>
 first_x_assum (qspecl_then [`s''.clock`, `env`, `env'`, `s''`, `s'''`] mp_tac) >>
 imp_res_tac evaluate_clock >>
 imp_res_tac evaluate_const >>
 full_simp_tac(srw_ss())[] >>
 `s''.clock ≤ i` by decide_tac >>
 imp_res_tac val_rel_mono_list >>
 simp [evaluate_ev_def, exec_rel_rw] >>
 srw_tac[][] >>
 pop_assum (qspec_then `s'''.clock` assume_tac) >>
 full_simp_tac(srw_ss())[] >>
 reverse ((Q.ISPEC_THEN `evaluate ([e],env,s'')` strip_assume_tac result_store_cases)) >>
 full_simp_tac(srw_ss())[res_rel_rw, clock_lemmas] >>
 `(s'' with clock := s'''.clock) = s''` by metis_tac [clock_lemmas] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- metis_tac [] >>
 `?v v'. vs'' = [v] ∧ vs''' = [v']` by metis_tac [evaluate_SING] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[] >>
 `vs ≠ []` by (Cases_on `vs` >> full_simp_tac(srw_ss())[]) >>
 imp_res_tac evaluate_clock >>
 full_simp_tac(srw_ss())[] >>
 metis_tac [res_rel_evaluate_app]);

val fn_partial_arg = Q.store_thm ("fn_partial_arg",
`!i' i w vs vs' env env' args args' num_args e e'.
 i' ≤ i ∧
 LIST_REL (val_rel (:'ffi) i w) vs vs' ∧
 LIST_REL (val_rel (:'ffi) i w) env env' ∧
 LIST_REL (val_rel (:'ffi) i w) args args' ∧
 exp_rel (:'ffi) w [e] [e']
 ⇒
 val_rel (:'ffi) i' w
  (Closure NONE args (vs ++ env) num_args e)
  (Closure NONE (args' ++ vs') env' (num_args + LENGTH vs') e')`,
 completeInduct_on `i'` >>
 srw_tac[][val_rel_rw, is_closure_def] >>
 imp_res_tac LIST_REL_LENGTH
 >- simp [check_closures_def, clo_can_apply_def, clo_to_num_params_def,
          clo_to_partial_args_def, rec_clo_ok_def, clo_to_loc_def] >>
 Cases_on `locopt` >>
 simp [dest_closure_def, check_loc_def] >>
 srw_tac[][] >>
 imp_res_tac state_rel_max_app >>
 TRY decide_tac >>
 srw_tac[][exec_rel_rw, evaluate_ev_def, evaluate_def, check_loc_def] >>
 full_simp_tac(srw_ss())[NOT_LESS] >>
 srw_tac[][res_rel_rw]
 >- (
   full_simp_tac(srw_ss())[exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
   first_x_assum (qspecl_then [`i''`,
                           `REVERSE (TAKE (num_args - LENGTH args') (REVERSE vs'')) ++ args ++ vs ++ env`,
                           `REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs''')) ++ args' ++ vs' ++ env'`,
                           `s`,
                           `s'`] mp_tac) >>
   simp [] >>
   `LIST_REL (val_rel (:'ffi) i'' s.max_app) (REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs'')) ++ args ++ vs ++ env)
            (REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs''')) ++ args' ++ vs' ++ env')` by (
     match_mp_tac EVERY2_APPEND_suff >>
     `i'' ≤ i` by decide_tac >>
     reverse (srw_tac[][])
     >- metis_tac [val_rel_mono_list] >>
     match_mp_tac EVERY2_APPEND_suff >>
     reverse (srw_tac[][])
     >- metis_tac [val_rel_mono_list] >>
     match_mp_tac EVERY2_APPEND_suff >>
     srw_tac[][LIST_REL_REVERSE_EQ, EVERY2_TAKE] >>
     metis_tac [val_rel_mono_list]) >>
   simp [] >>
   disch_then (qspec_then `i''' + (LENGTH args' + 1) − num_args` mp_tac) >>
   simp [] >>
   srw_tac[][] >>
   every_case_tac >>
   simp [res_rel_rw] >>
   imp_res_tac evaluate_SING >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   TRY (rename1 `(Rerr error, r)`)
   >- (
     Cases_on `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs'')) = []`
     >- (
       `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs''')) = []` by (
         full_simp_tac(srw_ss())[DROP_NIL] >>
         decide_tac) >>
       simp [evaluate_def, res_rel_rw] >>
       metis_tac []) >>
     match_mp_tac res_rel_evaluate_app >>
     simp [LIST_REL_REVERSE_EQ] >>
     match_mp_tac EVERY2_DROP >>
     simp [LIST_REL_REVERSE_EQ] >>
     imp_res_tac evaluate_clock >>
     full_simp_tac(srw_ss())[] >>
     `r'.clock ≤ i''` by decide_tac >>
     metis_tac [val_rel_mono_list])
  >- (
    Cases_on `error` >>
    full_simp_tac(srw_ss())[res_rel_rw] >>
    rename1 `(Rerr (Rabort abort), r)` >>
    Cases_on `abort` >>
    full_simp_tac(srw_ss())[res_rel_rw]))
 >- metis_tac [ZERO_LESS_EQ, val_rel_mono]
 >- (
   first_x_assum (match_mp_tac o SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO]) >>
   simp [] >>
   qexists_tac `i''` >>
   simp [] >>
   `i'' ≤ i` by decide_tac >>
   metis_tac [val_rel_mono_list, EVERY2_APPEND])
 >- (
   `i''' − (LENGTH vs''' − 1) ≤ i''` by decide_tac >>
   metis_tac [val_rel_mono])
 >- metis_tac [ZERO_LESS_EQ, val_rel_mono]);

val compat_closure_none = Q.prove (
`!i w loc env env' args args' num_args e e'.
  exp_rel (:'ffi) w [e] [e'] ∧
  LIST_REL (val_rel (:'ffi) i w) env env' ∧
  LIST_REL (val_rel (:'ffi) i w) args args'
  ⇒
  val_rel (:'ffi) i w (Closure NONE args env num_args e) (Closure NONE args' env' num_args e')`,
 srw_tac[][] >>
 qspecl_then [`i`,`i`, `w`, `[]`, `[]`, `env`, `env'`, `args`, `args'`]
       (match_mp_tac o SIMP_RULE (srw_ss()) []) fn_partial_arg >>
 srw_tac[][]);

val compat_closure_some = Q.prove (
`!i w l env env' args args' num_args e e'.
  LIST_REL (val_rel (:'ffi) i w) env env' ∧
  LIST_REL (val_rel (:'ffi) i w) args args' ∧
  exp_rel (:'ffi) w [e] [e']
  ⇒
  val_rel (:'ffi) i w (Closure (SOME l) args env num_args e) (Closure (SOME l) args' env' num_args e')`,
 completeInduct_on `i` >>
 srw_tac[][val_rel_rw, is_closure_def] >>
 imp_res_tac LIST_REL_LENGTH
 >- (
   srw_tac[][check_closures_def, clo_can_apply_def, clo_to_num_params_def,
       clo_to_partial_args_def, rec_clo_ok_def, clo_to_loc_def] >>
   full_simp_tac(srw_ss())[]) >>
 `(?l. locopt = SOME l) ∨ locopt = NONE` by metis_tac [option_nchotomy]
 >- (
   simp [dest_closure_def, check_loc_def] >>
   srw_tac[][] >>
   full_simp_tac(srw_ss())[exec_rel_rw, evaluate_ev_def] >>
   reverse (srw_tac[][res_rel_rw])
   >- metis_tac [val_rel_mono, ZERO_LESS_EQ] >>
   full_simp_tac(srw_ss())[REVERSE_DROP, LASTN, res_rel_rw, TAKE_REVERSE, LASTN_LENGTH_ID] >>
   `LASTN (LENGTH vs') vs = vs` by metis_tac [LASTN_LENGTH_ID] >>
   full_simp_tac(srw_ss())[] >>
   `exec_rel (i'' − (LENGTH vs' − 1)) w
             (Exp [e] (vs++env),s with clock := i'' − (LENGTH vs' − 1))
             (Exp [e'] (vs'++env'),s' with clock := i'' − (LENGTH vs' − 1))`
   by (
     full_simp_tac(srw_ss())[exp_rel_def] >>
     first_x_assum match_mp_tac >>
     srw_tac[][] >>
     `i'' − (LENGTH vs' − 1) ≤ i' ∧ i'' − (LENGTH vs' − 1) ≤ i` by decide_tac >>
     metis_tac [val_rel_mono_list, EVERY2_APPEND, val_rel_mono]) >>
   full_simp_tac(srw_ss())[exec_rel_rw, evaluate_ev_def] >>
   pop_assum (qspec_then `i'' - (LENGTH vs' - 1)` mp_tac) >>
   simp [] >>
   srw_tac[][] >>
   every_case_tac >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   imp_res_tac evaluate_SING >>
   full_simp_tac(srw_ss())[]) >>
 simp [dest_closure_def, check_loc_def] >>
 srw_tac[][] >>
 imp_res_tac state_rel_max_app >> fs[] >>
 srw_tac[][exec_rel_rw, evaluate_ev_def, evaluate_def, check_loc_def] >>
 full_simp_tac(srw_ss())[NOT_LESS] >>
 srw_tac[][res_rel_rw]
 >- (
   full_simp_tac(srw_ss())[exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
   first_x_assum (qspecl_then [`i'`,
                           `REVERSE (TAKE (num_args - LENGTH args') (REVERSE vs)) ++ args ++ env`,
                           `REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs')) ++ args' ++ env'`,
                           `s`,
                           `s'`] mp_tac) >>
   simp [] >>
   `LIST_REL (val_rel (:'ffi) i' s.max_app) (REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs)) ++ args ++ env)
            (REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs')) ++ args' ++ env')` by (
     match_mp_tac EVERY2_APPEND_suff >>
     `i' ≤ i` by decide_tac >>
     reverse (srw_tac[][])
     >- metis_tac [val_rel_mono_list] >>
     match_mp_tac EVERY2_APPEND_suff >>
     reverse (srw_tac[][])
     >- metis_tac [val_rel_mono_list] >>
     srw_tac[][LIST_REL_REVERSE_EQ] >>
     match_mp_tac EVERY2_TAKE >>
     srw_tac[][LIST_REL_REVERSE_EQ] >>
     metis_tac [val_rel_mono_list]) >>
   simp [] >>
   disch_then (qspec_then `i'' + (LENGTH args' + 1) − num_args` mp_tac) >>
   simp [] >>
   srw_tac[][] >>
   every_case_tac >>
   simp [res_rel_rw] >>
   imp_res_tac evaluate_SING >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   TRY (rename1 `(Rerr error, r)`)
   >- (
     Cases_on `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs)) = []`
     >- (
       `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs')) = []` by (
         full_simp_tac(srw_ss())[DROP_NIL] >>
         decide_tac) >>
       simp [evaluate_def, res_rel_rw] >>
       metis_tac []) >>
     match_mp_tac res_rel_evaluate_app >>
     simp [LIST_REL_REVERSE_EQ] >>
     match_mp_tac EVERY2_DROP >>
     simp [LIST_REL_REVERSE_EQ] >>
     imp_res_tac evaluate_clock >>
     full_simp_tac(srw_ss())[] >>
     `r'.clock ≤ i''` by decide_tac >>
     metis_tac [val_rel_mono_list])
  >- (
    Cases_on `error` >>
    full_simp_tac(srw_ss())[res_rel_rw] >>
    rename1 `(Rerr (Rabort abort), r)` >>
    Cases_on `abort` >>
    full_simp_tac(srw_ss())[res_rel_rw]))
 >- metis_tac [ZERO_LESS_EQ, val_rel_mono]
 >- (
   first_x_assum (match_mp_tac o SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO]) >>
   simp [] >>
   `i'' - (LENGTH vs' - 1) ≤ i ∧ i'' - (LENGTH vs' - 1) ≤ i'` by decide_tac >>
   metis_tac [val_rel_mono_list, EVERY2_APPEND])
 >- (
   `i'' − (LENGTH vs' − 1) ≤ i'` by decide_tac >>
   metis_tac [val_rel_mono])
 >- metis_tac [ZERO_LESS_EQ, val_rel_mono]);

val compat_closure = Q.store_thm ("compat_closure",
`!i w l env env' args args' num_args e e'.
 LIST_REL (val_rel (:'ffi) i w) env env' ∧
 LIST_REL (val_rel (:'ffi) i w) args args' ∧
 exp_rel (:'ffi) w [e] [e']
 ⇒
 val_rel (:'ffi) i w (Closure l args env num_args e) (Closure l args' env' num_args e')`,
 srw_tac[][] >>
 Cases_on `l` >>
 metis_tac [compat_closure_some, compat_closure_none]);

val compat_fn = Q.store_thm ("compat_fn",
`!vars num_args e e' loc t t'.
  exp_rel (:'ffi) w [e] [e']
  ⇒
  exp_rel (:'ffi) w [Fn t loc vars num_args e] [Fn t' loc vars num_args e']`,
 rpt strip_tac >>
 srw_tac[][exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def, evaluate_ev_def] >>
 srw_tac[][res_rel_rw] >>
 imp_res_tac state_rel_max_app >>
 Cases_on `vars` >>
 full_simp_tac(srw_ss())[]
 >- (
   reverse (srw_tac[][res_rel_rw])
   >- metis_tac [val_rel_mono] >>
   metis_tac [compat_closure, val_rel_mono_list, LIST_REL_NIL])
 >- (
   Cases_on `lookup_vars x env` >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   imp_res_tac val_rel_lookup_vars >>
   reverse (srw_tac[][])
   >- metis_tac [val_rel_mono] >>
   metis_tac [compat_closure, val_rel_mono_list, LIST_REL_NIL]));

val optCASE_NONE_T = Q.prove(
  `option_CASE opt T f ⇔ (∀r. opt = SOME r ⇒ f r)`,
  Cases_on `opt` >> simp[]);

val optCASE_NONE_F = Q.prove(
  `option_CASE opt F f ⇔ ∃r. opt = SOME r ∧ f r`,
  Cases_on `opt` >> simp[]);

val exp_rel_sing =
    exp_rel_def |> Q.SPECL [`w`, `[e1]`, `[e2]`]
                |> SIMP_RULE (srw_ss()) [exec_rel_rw, evaluate_ev_def]

val compat_recclosure = Q.store_thm ("compat_recclosure",
`!i w l env env' args args' funs funs' idx.
  LIST_REL (λ(n,e) (n',e'). n = n' ∧ exp_rel (:'ffi) w [e] [e']) funs funs' ∧
  LIST_REL (val_rel (:'ffi) i w) env env' ∧
  LIST_REL (val_rel (:'ffi) i w) args args'
  ⇒
  val_rel (:'ffi) i w (Recclosure l args env funs idx)
                      (Recclosure l args' env' funs' idx)`,
  qx_gen_tac `i` >> completeInduct_on `i` >>
  simp[val_rel_rw, is_closure_def, check_closures_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qx_genl_tac [`loc`, `N`] >>
      simp[clo_can_apply_def, clo_to_partial_args_def, clo_to_num_params_def,
           clo_to_loc_def, rec_clo_ok_def] >>
      rename1 `EL idx funs1` >> rename1 `LIST_REL _ funs1 funs2` >>
      rename1 `LENGTH args1 < FST (EL idx funs1)` >>
      rename1 `LENGTH args2 < FST (EL idx funs2)` >>
      `LENGTH funs2 = LENGTH funs1 ∧ LENGTH args2 = LENGTH args1`
        by metis_tac[LIST_REL_EL_EQN] >>
      qmatch_assum_abbrev_tac `LIST_REL FR funs1 funs2` >>
      rename1 `loc ≠ NONE` >> strip_tac >>
      `FR (EL idx funs1) (EL idx funs2)` by metis_tac[LIST_REL_EL_EQN] >>
      pop_assum mp_tac >> simp[Abbr`FR`, UNCURRY] >> strip_tac >>
      Cases_on `loc` >> full_simp_tac(srw_ss())[]) >>
  rename1 `Recclosure loc args1 env1 funs1 idx` >>
  rename1 `LIST_REL _ funs1 funs2` >>
  rename1 `LIST_REL _ env1 env2` >>
  rename1 `LIST_REL _ args1 args2` >>
  `LENGTH funs2 = LENGTH funs1 ∧ LENGTH env2 = LENGTH env1 ∧
   LENGTH args2 = LENGTH args1` by metis_tac[LIST_REL_EL_EQN] >>
  simp[optCASE_NONE_T, optCASE_NONE_F] >> rpt gen_tac >> strip_tac >>
  qx_gen_tac `dc1` >>
  simp[dest_closure_def, SimpL ``$==>``, UNCURRY] >>
  Cases_on `idx < LENGTH funs1` >> simp[] >>
  `∃fn1 fe1. EL idx funs1 = (fn1, fe1)`
     by (Cases_on `EL idx funs1` >> simp[]) >> simp[] >>
  rename1 `LIST_REL (val_rel (:'ffi) j w) vs1 vs2` >>
  `LENGTH vs2 = LENGTH vs1` by metis_tac[LIST_REL_EL_EQN] >>
  simp[revdroprev, revtakerev] >> Cases_on `LENGTH args1 < fn1` >> simp[] >>
  simp[bool_case_eq] >>
  qmatch_assum_abbrev_tac `LIST_REL FR funs1 funs2` >>
  `∃fe2. EL idx funs2 = (fn1, fe2) ∧ exp_rel (:'ffi) w [fe1] [fe2]`
    by (`FR (EL idx funs1) (EL idx funs2)` by metis_tac [LIST_REL_EL_EQN] >>
        pop_assum mp_tac >>
        Cases_on `EL idx funs2` >> simp[Abbr`FR`]) >>
  imp_res_tac state_rel_max_app >> fs[] >>
  strip_tac >>
  simp[dest_closure_def, revdroprev, revtakerev, exec_rel_rw,
       evaluate_ev_def] >>
  qx_gen_tac `k`
  >- (reverse (srw_tac[][])
      >- (simp[res_rel_rw] >> metis_tac[DECIDE ``0n ≤ x``, val_rel_mono]) >>
      qmatch_abbrev_tac `
        res_rel w (pair_CASE (evaluate ([fe1], ENV1, _)) _)
                  (pair_CASE (evaluate ([fe2], ENV2, _)) _)` >>
      `LIST_REL (val_rel (:'ffi) j w) ENV1 ENV2`
        by (simp[Abbr`ENV1`, Abbr`ENV2`] >>
            reverse (irule EVERY2_APPEND_suff)
            >- metis_tac[val_rel_mono_list, DECIDE ``x < y:num ⇒ x ≤ y``] >>
            reverse (irule EVERY2_APPEND_suff)
            >- (simp[LIST_REL_GENLIST] >> rpt strip_tac >>
                first_x_assum irule >> simp[] >>
                metis_tac[val_rel_mono_list, DECIDE ``x < y:num ⇒ x ≤ y``]) >>
            irule EVERY2_APPEND_suff >- simp[EVERY2_DROP] >>
            metis_tac[val_rel_mono_list, DECIDE ``x < y:num ⇒ x ≤ y``]) >>
      Q.UNDISCH_THEN `exp_rel (:'ffi) w [fe1] [fe2]` mp_tac >>
      DISCH_THEN (mp_tac o SIMP_RULE (srw_ss()) [exp_rel_sing]) >>
      DISCH_THEN (qspecl_then [`j`, `ENV1`, `ENV2`, `s`, `s'`] mp_tac) >>
      simp[] >>
      DISCH_THEN (qspec_then `k + (LENGTH args1 + 1) - fn1` mp_tac) >>
      simp[] >>
      qabbrev_tac `CK = k + (LENGTH args1 + 1) - fn1` >>
      qabbrev_tac `ev1 = evaluate([fe1],ENV1,s with clock := CK)` >>
      reverse
        (`(∃rv1 s1'. ev1 = (Rval [rv1], s1')) ∨ ∃err s1'. ev1 = (Rerr err, s1')`
           by metis_tac[TypeBase.nchotomy_of ``:('a,'b) result``, pair_CASES,
                        evaluate_SING])
      >- (Cases_on `err` >> simp[res_rel_rw]
          >- (rpt strip_tac >> simp[] >> full_simp_tac(srw_ss())[]) >>
          rename1 `ev1 = (Rerr (Rabort a), s1)` >>
          Cases_on `a` >> simp[res_rel_rw] >> rpt strip_tac >> simp[] >>
          full_simp_tac(srw_ss())[]) >>
      simp[res_rel_rw] >> dsimp[] >> rpt strip_tac >>
      rename1 `evaluate([fe2], ENV2, _) = (Rval [rv2], s2')` >>
      qmatch_abbrev_tac `res_rel w (evaluate_app _ _ (TAKE N vs1) _) _` >>
      `N ≤ LENGTH vs1` by simp[Abbr`N`] >>
      Cases_on `N = 0` >- (simp[res_rel_rw] >> full_simp_tac(srw_ss())[]) >>
      irule res_rel_evaluate_app
      >- (Cases_on `N` >> full_simp_tac(srw_ss())[] >> Cases_on `vs1` >> full_simp_tac(srw_ss())[]) >>
      simp[] >> irule EVERY2_TAKE >>
      irule val_rel_mono_list >> qexists_tac `j` >> simp[] >>
      imp_res_tac evaluate_clock >> full_simp_tac(srw_ss())[] >> simp[Abbr`CK`]) >>
  reverse (srw_tac[][])
  >- (simp[res_rel_rw] >> metis_tac[DECIDE ``0n ≤ x``, val_rel_mono]) >>
  simp[res_rel_rw] >> conj_tac
  >- (first_x_assum irule >> simp[]
      >- (irule EVERY2_APPEND_suff >> irule val_rel_mono_list
          >- (qexists_tac `j` >> simp[]) >>
          qexists_tac `i` >> simp[]) >>
      irule val_rel_mono_list >> qexists_tac `i` >> simp[]) >>
  irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `j` >> simp[])

val compat_letrec = Q.store_thm ("compat_letrec",
`!loc vars funs e funs' e' t t'.
  LIST_REL (\(n,e) (n',e'). n = n' ∧ exp_rel (:'ffi) w [e] [e']) funs funs' ∧
  exp_rel (:'ffi) w [e] [e']
  ⇒
  exp_rel (:'ffi) w [Letrec t loc vars funs e] [Letrec t' loc vars funs' e']`,
 rpt strip_tac >>
 srw_tac[][exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def, evaluate_ev_def] >>
 imp_res_tac state_rel_max_app >>
 reverse (srw_tac[][res_rel_rw])
 >- (
   full_simp_tac std_ss [LIST_REL_EL_EQN, EVERY_EL] >>
   full_simp_tac(srw_ss())[] >>
   Cases_on `EL n funs` >>
   Cases_on `EL n funs'` >>
   full_simp_tac(srw_ss())[] >>
   rpt (first_x_assum (qspec_then `n` mp_tac)) >>
   srw_tac[][]) >>
 Cases_on `vars` >>
 full_simp_tac(srw_ss())[]
 >- (
   `exec_rel i' s.max_app
      (Exp [e] (GENLIST (Recclosure loc [] env funs) (LENGTH funs) ++ env), s)
      (Exp [e'] (GENLIST (Recclosure loc [] env' funs') (LENGTH funs') ++ env'), s')`
   by (
     full_simp_tac(srw_ss())[exp_rel_def] >>
     first_x_assum match_mp_tac >>
     srw_tac[][]
     >- metis_tac [val_rel_mono] >>
     match_mp_tac EVERY2_APPEND_suff >>
     reverse conj_tac
     >- metis_tac [val_rel_mono_list] >>
     imp_res_tac LIST_REL_LENGTH >>
     srw_tac[][LIST_REL_GENLIST] >>
     match_mp_tac compat_recclosure >>
     srw_tac[][exp_rel_def] >>
     metis_tac [val_rel_mono_list]) >>
   full_simp_tac(srw_ss())[exec_rel_rw, evaluate_ev_def])
 >- (
   Cases_on `lookup_vars x env` >>
   full_simp_tac(srw_ss())[res_rel_rw] >>
   imp_res_tac val_rel_lookup_vars >>
   srw_tac[][] >>
   `exec_rel i' s.max_app
       (Exp [e] (GENLIST (Recclosure loc [] x' funs) (LENGTH funs) ++ env), s)
       (Exp [e'] (GENLIST (Recclosure loc [] vs2'' funs') (LENGTH funs') ++ env'), s')`
   by (
     full_simp_tac(srw_ss())[exp_rel_def] >>
     first_x_assum match_mp_tac >>
     srw_tac[][]
     >- metis_tac [val_rel_mono] >>
     match_mp_tac EVERY2_APPEND_suff >>
     reverse conj_tac
     >- metis_tac [val_rel_mono_list] >>
     imp_res_tac LIST_REL_LENGTH >>
     srw_tac[][LIST_REL_GENLIST] >>
     match_mp_tac compat_recclosure >>
     srw_tac[][exp_rel_def] >>
     metis_tac [val_rel_mono_list]) >>
   full_simp_tac(srw_ss())[exec_rel_rw, evaluate_ev_def]));

val compat_op = Q.store_thm ("compat_op",
`!op es es'.
  exp_rel (:'ffi) w es es'
  ⇒
  exp_rel (:'ffi) w [Op t op es] [Op t' op es']`,
 srw_tac[][exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def] >>
 srw_tac[][] >>
 `exec_rel i' w (Exp es env, s with clock := i') (Exp es' env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 srw_tac[][] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[evaluate_ev_def, evaluate_def] >>
 reverse (Q.ISPEC_THEN `evaluate (es,env,s with clock := i')` strip_assume_tac
                         result_store_cases) >>
 srw_tac[][res_rel_rw] >>
 full_simp_tac(srw_ss())[res_rel_rw]
 >- metis_tac [] >>
 metis_tac [res_rel_do_app]);

val compat = save_thm ("compat",
  LIST_CONJ [compat_nil, compat_cons, compat_var, compat_if, compat_let, compat_raise,
             compat_handle, compat_tick, compat_call, compat_app,
             compat_fn, compat_letrec, compat_op]);

val exp_rel_refl = Q.store_thm ("exp_rel_refl",
`(!e. exp_rel (:'ffi) w [e] [e]) ∧
 (!es. exp_rel (:'ffi) w es es) ∧
 (!(ne :num # closLang$exp). FST ne = FST ne ∧ exp_rel (:'ffi) w [SND ne] [SND ne]) ∧
 (!funs. LIST_REL (\(n:num,e) (n',e'). n = n' ∧ exp_rel (:'ffi) w [e] [e']) funs funs)`,
 Induct >>
 srw_tac[][] >>
 TRY (PairCases_on `ne`) >>
 full_simp_tac(srw_ss())[] >>
 metis_tac [compat]);

val val_rel_refl = Q.store_thm ("val_rel_refl",
`(!v. val_rel (:'ffi) i w v v) ∧
 (!vs. LIST_REL (val_rel (:'ffi) i w) vs vs)`,
 ho_match_mp_tac v_induction >>
 srw_tac[][]
 >- srw_tac[][val_rel_rw]
 >- srw_tac[][val_rel_rw]
 >- srw_tac[][val_rel_rw]
 >- srw_tac[][val_rel_rw]
 >- srw_tac[][val_rel_rw]
 >- metis_tac [exp_rel_refl, compat_closure]
 >- metis_tac [exp_rel_refl, compat_recclosure]);

val ref_v_rel_refl = Q.store_thm ("ref_v_rel_refl",
`!i w rv. ref_v_rel (:'ffi) i w rv rv`,
 srw_tac[][] >>
 Cases_on `rv` >>
 srw_tac[][ref_v_rel_rw] >>
 metis_tac [val_rel_refl, refl_list_rel_refl]);

val state_rel_refl = Q.store_thm ("state_rel_refl",
`(!i s. state_rel i s.max_app s s)`,
 srw_tac[][Once state_rel_rw]
 >- metis_tac [refl_list_rel_refl, val_rel_refl, OPTREL_refl]
 >- metis_tac [fmap_rel_refl, ref_v_rel_refl]
 >- (
   match_mp_tac fmap_rel_refl >>
   simp [FORALL_PROD] >>
   srw_tac[][] >>
   `exp_rel (:'a) s.max_app [p_2] [p_2]` by metis_tac [exp_rel_refl] >>
   full_simp_tac(srw_ss())[exp_rel_def]));

val val_rel_closure = Q.store_thm(
  "val_rel_closure",
  `val_rel (:'ffi) i w C1 C2 ∧ is_closure C1 ⇒
   is_closure C2 ∧ check_closures C1 C2`,
  Cases_on `C1` >> simp[is_closure_def] >> simp[val_rel_rw]);

val check_closures_trans = Q.store_thm(
  "check_closures_trans",
  `check_closures c1 c2 ∧ check_closures c2 c3 ⇒ check_closures c1 c3`,
  simp[check_closures_def] >> metis_tac[]);

fun PART_MATCH' f th t =
  let
    val (vs, b) = strip_forall (concl th)
    val specth = SPEC_ALL th
    val pat = f (concl specth)
    val localconsts = hyp_frees specth
    val localtycons = HOLset.listItems (hyp_tyvars specth)
    val theta as (tms, tys) = match_terml localtycons localconsts pat t
    val vs' = op_set_diff aconv (map (Term.inst tys) vs) (map #redex tms)
  in
    GENL vs' (INST_TY_TERM theta specth)
  end

val fmap_rel_t = prim_mk_const{Thy = "finite_map", Name = "fmap_rel"}

val evaluate_ev_timeout_clocks0 = Q.store_thm(
  "evaluate_ev_timeout_clocks0",
  `evaluate_ev j e s0 = (Rerr (Rabort Rtimeout_error), s) ⇒ s.clock = 0`,
  Cases_on `e` >> dsimp[evaluate_ev_def, case_eq_thms, pair_case_eq, bool_case_eq] >>
  rpt strip_tac >> imp_res_tac evaluate_timeout_clocks0);

val val_rel_trans = Q.store_thm ("val_rel_trans",
`(!(ffi:'ffi itself) i w v1 v2.
    val_rel ffi i w v1 v2 ⇒ !v3. val_rel ffi i w v2 v3 ⇒ val_rel ffi i w v1 v3) ∧
 (!i w (st1:val_or_exp # 'ffi closSem$state) st2.
    exec_rel i w st1 st2 ⇒ !st3. exec_rel i w st2 st3 ⇒ exec_rel i w st1 st3) ∧
 (!(ffi:'ffi itself) i w rv1 rv2.
    ref_v_rel ffi i w rv1 rv2 ⇒
    !rv3. ref_v_rel ffi i w rv2 rv3 ⇒ ref_v_rel ffi i w rv1 rv3) ∧
 (!i w (s1 : 'ffi closSem$state) s2.
    state_rel i w s1 s2 ⇒ !s3. state_rel i w s2 s3 ⇒ state_rel i w s1 s3)`,
 ho_match_mp_tac val_rel_ind >>
 srw_tac[][is_closure_def]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- (
   full_simp_tac(srw_ss())[val_rel_rw] >>
   Cases_on `v3` >>
   full_simp_tac(srw_ss())[val_rel_rw] >>
   match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] LIST_REL_trans) >>
   metis_tac [LIST_REL_LENGTH, MEM_EL, LIST_REL_EL_EQN])
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 >- full_simp_tac(srw_ss())[val_rel_rw]
 (* Closure *)
 >- (
  rename1 `val_rel _ i w (Closure locopt argE closE n e) V` >>
  qmatch_assum_rename_tac `val_rel _ i w (Closure _ _ _ _ _) V0` >>
  qabbrev_tac `C1 = Closure locopt argE closE n e` >>
  `is_closure C1` by (simp_tac (srw_ss()) [Abbr`C1`, is_closure_def]) >>
  Q.SUBGOAL_THEN
    `is_closure V0 ∧ check_closures C1 V0 ∧ is_closure V ∧
     check_closures V0 V
    `
    (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
              STRIP_ASSUME_TAC th)
  >- metis_tac[val_rel_closure] >>
  Q.UNABBREV_TAC `C1` >>
  simp_tac (srw_ss()) [val_rel_rw, optCASE_NONE_F, optCASE_NONE_T] >>
  conj_tac >- metis_tac[check_closures_trans] >>
  qx_genl_tac [`j`, `vs1`, `vs2`, `s1`, `s2`, `clocopt`] >> strip_tac >>
  imp_res_tac state_rel_max_app >>
  rpt (first_x_assum (qspecl_then [`j`, `s1`, `s2`]
                        (fn th => mp_tac th >>
                                  simp[SimpL ``$==>``] >>
                                  strip_tac))) >>
  rpt (first_x_assum (qspecl_then [`vs1`, `vs2`, `clocopt`]
        (fn th => mp_tac th >>
                  asm_simp_tac (srw_ss() ++ ETA_ss) [SimpL ``$==>``] >>
                  strip_tac))) >>
  qx_gen_tac `dcres` >>
  rveq >>
  qpat_x_assum`_ = s1.max_app`(assume_tac o SYM)
  \\ full_simp_tac std_ss [] >>
  disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                       mp_tac th) >> strip_tac >>
  qpat_x_assum `val_rel _ i _ _ V0` mp_tac >>
  simp[SimpL ``$==>``, val_rel_rw] >>
  disch_then (qspecl_then [`j`, `vs1`, `vs2`, `s1`, `s2`, `clocopt`] mp_tac) >>
  simp[SimpL ``$==>``, optCASE_NONE_F] >>
  disch_then (qx_choose_then `dcres2` mp_tac) >>
  `vs2 ≠ []` by (strip_tac >> full_simp_tac(srw_ss())[]) >>
  rev_full_simp_tac std_ss [] >>
  Cases_on `dcres` >> Cases_on `dcres2` >> simp[SimpL ``$==>``] >>
  disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                       strip_assume_tac th) >>
  simp_tac (srw_ss()) [] >>
  Q.UNDISCH_THEN `val_rel (:'ffi) i s2.max_app V0 V` mp_tac >>
  Cases_on `V0` >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [is_closure_def]) >>
  simp[SimpL ``$==>``, val_rel_rw] >> TRY (FIRST_ASSUM ACCEPT_TAC) >>
  simp[optCASE_NONE_F, optCASE_NONE_T] >>
  disch_then (mp_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  disch_then (fn th => first_assum (fn termth =>
    mp_tac (PART_MATCH' (fn t => t |> dest_imp |> #2 |> dest_imp |> #1)
                        th (concl termth)))) >>
  simp[SimpL ``$==>``] >> simp_tac(srw_ss()) [] >> simp[] >>
  disch_then (mp_tac o
              CONV_RULE (RESORT_FORALL_CONV (sort_vars ["s'", "vs'"]))) >>
  disch_then (qspecl_then [ `s2`, `vs2`] mp_tac) >>
  simp[val_rel_refl, state_rel_refl] >>
  disch_then (qspec_then `j` mp_tac) >>
  simp[] >> Cases_on `dest_closure s2.max_app clocopt V vs2` >> simp[] >>
  rename1 `dest_closure s2.max_app clocopt V vs2 = SOME cl` >> Cases_on `cl` >>
  simp[])
 (* RecClosure *)
 >- (
  rename1 `val_rel _ i _ (Recclosure locopt argE closE fns idx) C3` >>
  qmatch_assum_rename_tac `val_rel _ i _ (Recclosure _ _ _ _ _) C2` >>
  qabbrev_tac `C1 = Recclosure locopt argE closE fns idx` >>
  `is_closure C1` by (simp_tac (srw_ss()) [Abbr`C1`, is_closure_def]) >>
  Q.SUBGOAL_THEN
    `is_closure C2 ∧ check_closures C1 C2 ∧ is_closure C3 ∧
     check_closures C2 C3
    `
    (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
              STRIP_ASSUME_TAC th)
  >- metis_tac[val_rel_closure] >>
  Q.UNABBREV_TAC `C1` >>
  simp_tac (srw_ss()) [val_rel_rw, optCASE_NONE_F, optCASE_NONE_T] >>
  conj_tac >- metis_tac[check_closures_trans] >>
  qx_genl_tac [`j`, `vs1`, `vs2`, `s1`, `s2`, `clocopt`] >> strip_tac >>
  imp_res_tac state_rel_max_app >>
  rveq >> pop_assum(ASSUME_TAC o SYM) >>
  rpt (first_x_assum (qspecl_then [`j`, `s1`, `s2`]
                        (fn th => mp_tac th >>
                                  simp[SimpL ``$==>``] >>
                                  strip_tac))) >>
  rpt (first_x_assum (qspecl_then [`vs1`, `vs2`, `clocopt`]
        (fn th => mp_tac th >>
                  asm_simp_tac (srw_ss() ++ ETA_ss) [SimpL ``$==>``] >>
                  strip_tac))) >>
  qx_gen_tac `dcres` >>
  rev_full_simp_tac std_ss [] >>
  disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                       mp_tac th) >> strip_tac >>
  qpat_x_assum `val_rel _ i _ _ C2` mp_tac >>
  full_simp_tac std_ss [] >>
  simp[SimpL ``$==>``, val_rel_rw] >>
  disch_then (qspecl_then [`j`, `vs1`, `vs2`, `s1`, `s2`, `clocopt`] mp_tac) >>
  simp[SimpL ``$==>``, optCASE_NONE_F] >>
  disch_then (qx_choose_then `dcres2` mp_tac) >>
  `vs2 ≠ []` by (strip_tac >> full_simp_tac(srw_ss())[]) >>
  Cases_on `dcres` >> Cases_on `dcres2` >> simp[SimpL ``$==>``] >>
  disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                       strip_assume_tac th) >>
  simp_tac (srw_ss()) [] >>
  Q.UNDISCH_THEN `val_rel (:'ffi) i s2.max_app C2 C3` mp_tac >>
  Cases_on `C2` >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [is_closure_def]) >>
  simp[SimpL ``$==>``, val_rel_rw] >> TRY (FIRST_ASSUM ACCEPT_TAC) >>
  simp[optCASE_NONE_F, optCASE_NONE_T] >>
  disch_then (mp_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  disch_then (fn th => first_assum (fn termth =>
    mp_tac (PART_MATCH' (fn t => t |> dest_imp |> #2 |> dest_imp |> #1)
                        th (concl termth)))) >>
  simp[SimpL ``$==>``] >> simp_tac(srw_ss()) [] >> simp[] >>
  disch_then (qspecl_then [`j`, `vs2`, `s2`] mp_tac) >>
  simp[val_rel_refl, state_rel_refl] >>
  Cases_on `dest_closure s2.max_app clocopt C3 vs2` >> simp[] >>
  rename1 `dest_closure s2.max_app clocopt C3 vs2 = SOME cl` >> Cases_on `cl` >>
  simp[])
 >- ((* exec_rel *)
  rename1 `exec_rel i w (e0,s0) es` >>
  `∃e2 s2. es = (e2,s2)` by (Cases_on `es` >> simp[]) >> srw_tac[][] >>
  qmatch_assum_rename_tac `exec_rel i w (e0,s0) (e1,s1)` >>
  simp[exec_rel_rw] >> qx_gen_tac `j` >> strip_tac >>
  Q.UNDISCH_THEN `exec_rel i w (e0,s0) (e1,s1)` mp_tac >>
  simp[exec_rel_rw] >> disch_then strip_assume_tac >>

  rpt (first_x_assum (mp_tac o
                      C (PART_MATCH' (hd o strip_conj o #1 o dest_imp))
                        ``j:num ≤ i``) >>
       simp[] >> strip_tac) >>

  `∃r0 s0'. evaluate_ev j e0 s0 = (r0,s0')`
    by (Cases_on `evaluate_ev j e0 s0` >> simp[]) >> full_simp_tac(srw_ss())[] >>
  `∃r1 s1'. evaluate_ev j e1 s1 = (r1,s1')`
    by (Cases_on `evaluate_ev j e1 s1` >> simp[]) >> full_simp_tac(srw_ss())[] >>

  qpat_x_assum `exec_rel i w (e1,s1) _` mp_tac >>
  simp[exec_rel_rw] >> disch_then (qspec_then `j` mp_tac) >> simp[] >>
  strip_tac >>

  reverse (Cases_on `r0`) >> full_simp_tac(srw_ss())[]
  >- (rename1 `evaluate_ev _ _ s0 = (Rerr ee, _)` >>
      reverse (Cases_on `ee`) >> full_simp_tac(srw_ss())[]
      >- (rename1 `evaluate_ev _ _ _ = (Rerr (Rabort abt), _)` >>
          Cases_on `abt` >> full_simp_tac(srw_ss())[res_rel_rw] >> srw_tac[][] >>
          full_simp_tac(srw_ss())[res_rel_rw] >>
          `s1'.clock = s0'.clock`
            by (imp_res_tac evaluate_ev_timeout_clocks0 >> simp[]) >>
          metis_tac[]) >>
      full_simp_tac(srw_ss())[res_rel_rw] >> srw_tac[][] >> full_simp_tac(srw_ss())[res_rel_rw] >> metis_tac[]) >>
  full_simp_tac(srw_ss())[res_rel_rw] >> srw_tac[][] >> full_simp_tac(srw_ss())[res_rel_rw] >> reverse conj_tac >- metis_tac[] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> metis_tac[MEM_EL])
 >- full_simp_tac(srw_ss())[ref_v_rel_rw]
 >- (
   Cases_on `rv3` >>
   full_simp_tac(srw_ss())[ref_v_rel_rw] >>
   match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] LIST_REL_trans) >>
   metis_tac [LIST_REL_LENGTH, MEM_EL, LIST_REL_EL_EQN])
 >- full_simp_tac(srw_ss())[ref_v_rel_rw]
 >- full_simp_tac(srw_ss())[ref_v_rel_rw]
 >- ( (* state_rel *)
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   ONCE_REWRITE_TAC [state_rel_rw] >>
   srw_tac[][]
   >- (rpt (first_x_assum
              (kall_tac o
               assert (can (find_term (same_const fmap_rel_t)) o concl))) >>
       full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >> qx_gen_tac `idx` >> strip_tac >>
       rename1 `OPTREL (val_rel (:'ffi) N w)
                    (EL idx s1.globals) (EL idx s3.globals)` >>
       full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> res_tac >>
       Cases_on `EL idx s1.globals` >> Cases_on `EL idx s3.globals` >>
       full_simp_tac(srw_ss())[OPTREL_def] >> full_simp_tac(srw_ss())[] >> metis_tac[MEM_EL])
   >- (irule fmap_rel_trans >> metis_tac[])
   >- (irule fmap_rel_trans
       >- (simp_tac (srw_ss()) [FORALL_PROD] >> rpt strip_tac >>
           first_x_assum irule >- simp[] >>
           simp_tac (srw_ss() ++ ETA_ss) [] >>
           rename1 `LIST_REL (val_rel (:'ffi) j _) E1 _` >>
           rename1 `exec_rel j _ (Exp [e1] E1, s1')` >>
           rename1 `exec_rel j _ _ (Exp [e3] E3, s3')` >>
           rename1 `exec_rel _ _ (Exp [e1] _, _) (Exp [e2] _, _)` >>
           map_every qexists_tac [`e2`, `E3`, `s3'`] >> simp[] >>
           first_x_assum irule >> simp[val_rel_refl, state_rel_refl] >>
           imp_res_tac state_rel_max_app >>
           metis_tac[state_rel_refl]) >>
       metis_tac[])
  ));

val exp_rel_trans = Q.store_thm ("exp_rel_trans",
`!e1 e2 e3. exp_rel (:'ffi) w e1 e2 ∧ exp_rel (:'ffi) w e2 e3 ⇒ exp_rel (:'ffi) w e1 e3`,
 srw_tac[][exp_rel_def] >>
 imp_res_tac state_rel_max_app >>
 `!i. state_rel i s'.max_app s' s' ∧ LIST_REL (val_rel (:'ffi) i s'.max_app) env' env'` by metis_tac [val_rel_refl, state_rel_refl] >>
 metis_tac [val_rel_trans]);

val _ = export_theory ();

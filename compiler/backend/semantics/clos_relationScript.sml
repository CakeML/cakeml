open preamble closLangTheory closSemTheory closPropsTheory;

val _ = new_theory "clos_relation";

val refl_list_rel_refl = Q.store_thm ("refl_list_rel_refl",
`!r. (!x. r x x) ⇒ !l. LIST_REL r l l`,
 rw [] >>
 match_mp_tac EVERY2_refl >>
 rw []);

val bool_case_eq = Q.prove(
  `COND b t f = v ⇔ b /\ v = t ∨ ¬b ∧ v = f`,
  rw[] >> metis_tac[]);

val pair_case_eq = Q.prove (
`pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v`,
 Cases_on `x` >>
 rw []);

val butlastn_nil = Q.store_thm ("butlastn_nil",
`!n l. n ≤ LENGTH l ⇒ (BUTLASTN n l = [] ⇔ LENGTH l = n)`,
 Induct_on `n` >>
 rw [BUTLASTN]
 >- (Cases_on `l` >> rw []) >>
 `l = [] ∨ ?x y. l = SNOC x y` by metis_tac [SNOC_CASES] >>
 ASM_REWRITE_TAC [BUTLASTN] >>
 simp [] >>
 fs [ADD1]);

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
 rw [evaluate_ev_def] >>
 rw [] >>
 BasicProvers.EVERY_CASE_TAC >>
 fs [] >>
 imp_res_tac evaluate_clock >>
 fs [] >>
 rw [] >>
 decide_tac);

val OPTREL_Cong = Q.store_thm(
  "OPTREL_Cong[defncong]",
  `∀o1 o2 o1' o2' R1 R2.
      (o1 = o1') ∧ (o2 = o2') ∧
      (∀x y. o1' = SOME x ∧ o2' = SOME y ⇒ (R1 x y ⇔ R2 x y)) ⇒
      (OPTREL R1 o1 o2 ⇔ OPTREL R2 o1' o2')`,
  Cases >> Cases >> Cases >> Cases >> simp[OPTREL_def]);

val val_rel_def = tDefine "val_rel" `
(val_rel (:'ffi) (i:num) (Number n) (Number n') ⇔
  n = n') ∧
(val_rel (:'ffi) (i:num) (Block n vs) (Block n' vs') ⇔
  n = n' ∧ LIST_REL (val_rel (:'ffi) i) vs vs') ∧
(val_rel (:'ffi) (i:num) (RefPtr p) (RefPtr p') ⇔ p = p') ∧
(val_rel (:'ffi) (i:num) cl cl' ⇔
  if is_closure cl ∧ is_closure cl' ∧ check_closures cl cl' then
    !i' vs vs' (s:'ffi closSem$state) (s':'ffi closSem$state) locopt.
      if i' < i then
        state_rel i' s s' ∧
        vs ≠ [] ∧
        LIST_REL (val_rel (:'ffi) i') vs vs'
        ⇒
        case (dest_closure locopt cl vs, dest_closure locopt cl' vs') of
           | (NONE, _) => T
           | (_, NONE) => F
           | (SOME (Partial_app v), SOME (Partial_app v')) =>
               exec_rel i' (Val v (LENGTH vs), s) (Val v' (LENGTH vs'), s')
           | (SOME (Partial_app v), SOME (Full_app e' env' rem_vs')) =>
               exec_rel i'
                        (Val v (LENGTH vs), s)
                        (Exp1 locopt e' env' rem_vs'
                              (LENGTH vs' - LENGTH rem_vs'), s')
           | (SOME (Full_app e env rem_vs), SOME (Partial_app v')) =>
               exec_rel i'
                 (Exp1 locopt e env rem_vs (LENGTH vs - LENGTH rem_vs), s)
                 (Val v' (LENGTH vs'), s')
           | (SOME (Full_app e env rem_vs), SOME (Full_app e' env' rem_vs')) =>
               exec_rel i'
                 (Exp1 locopt e env rem_vs (LENGTH vs - LENGTH rem_vs), s)
                 (Exp1 locopt e' env' rem_vs' (LENGTH vs' - LENGTH rem_vs'), s')
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
    !i' vs vs' (s:'ffi closSem$state) s' locopt.
      if i' < c then
        state_rel i' s s' ∧
        vs ≠ [] ∧
        LIST_REL (val_rel (:'ffi) i') vs vs'
        ⇒
        case (dest_closure locopt v vs, dest_closure locopt v' vs') of
           | (NONE, _) => T
           | (_, NONE) => F
           | (SOME (Partial_app v), SOME (Partial_app v')) =>
               exec_rel i' (Val v (LENGTH vs), s) (Val v' (LENGTH vs'), s')
           | (SOME (Partial_app v), SOME (Full_app e' env' rest')) =>
               exec_rel i'
                 (Val v (LENGTH vs), s)
                 (Exp1 locopt e' env' rest' (LENGTH vs' - LENGTH rest'), s')
           | (SOME (Full_app e env rest), SOME (Partial_app v')) =>
               exec_rel i'
               (Exp1 locopt e env rest (LENGTH vs - LENGTH rest), s)
               (Val v' (LENGTH vs'), s')
           | (SOME (Full_app e env rest), SOME (Full_app e' env' rest')) =>
               exec_rel i'
                 (Exp1 locopt e env rest (LENGTH vs - LENGTH rest), s)
                 (Exp1 locopt e' env' rest' (LENGTH vs' - LENGTH rest'), s')
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

val val_rel_is_closure = Q.store_thm(
  "val_rel_is_closure",
  `val_rel (:'ffi) c cl1 cl2 ∧ is_closure cl1 ⇒
   is_closure cl2 ∧ check_closures cl1 cl2`,
  Cases_on `cl1` >> simp[is_closure_def, val_rel_rw]);

val val_rel_mono_list' = Q.store_thm(
  "val_rel_mono_list'",
  `LIST_REL (val_rel (:'ffi) m) l1 l2 ⇒
   ∀i. i ≤ m ⇒ LIST_REL (val_rel (:'ffi) i) l1 l2`,
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
  `res_rel rs (Rerr (Rabort Rtimeout_error), s) ⇔
   (∃s'. rs = (Rerr (Rabort Rtimeout_error), s') ∧ state_rel s'.clock s' s) ∨
   (∃s'. rs = (Rerr (Rabort Rtype_error), s'))`,
  Cases_on `rs` >> simp[] >> qcase_tac `res_rel (rr, _)` >>
  Cases_on `rr` >> simp[res_rel_rw] >> qcase_tac `res_rel (Rerr ee, _)` >>
  Cases_on `ee` >> simp[res_rel_rw] >>
  qcase_tac `res_rel (Rerr (Rabort aa), _)` >> Cases_on `aa` >>
  simp[res_rel_rw]);

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
         first_x_assum
           (qspecl_then [`s'.clock - 1`, `vs`, `vs'`, `s`, `s'`, `NONE`]
                        mp_tac) >>
         simp [exec_rel_rw, evaluate_ev_def, res_rel_def] >>
         `s'.clock - 1 ≤ s'.clock` by decide_tac >>
         `state_rel (s'.clock − 1) s s' ∧
          LIST_REL (val_rel (:'ffi) (s'.clock − 1)) vs vs'`
           by metis_tac [val_rel_mono, val_rel_mono_list] >>
         simp [] >>
         disch_then (qspec_then `s'.clock - 1` mp_tac) >>
         simp [res_rel_rw]))
 >- ((* Partial, Full *)
     qcase_tac `dest_closure loc v vs = SOME (Partial_app cl)` >>
     qcase_tac `dest_closure loc v' vs' = SOME (Full_app b' env' rest')` >>
     qcase_tac `st.clock < LENGTH vs' - LENGTH rest'` >>
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
     `used' ≠ []` by (Cases_on `used'` >> fs[]) >>
     full_simp_tac (srw_ss() ++ numSimps.ARITH_NORM_ss) [] >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >> rveq >>
     simp[dec_clock_def] >>
     qspecl_then [`LENGTH rest'`, `v`, `vs`, `cl`]
       mp_tac dest_closure_partial_split' >> simp[] >>
     disch_then (qx_choosel_then [`cl0`, `used`, `rest`] strip_assume_tac) >>
     `is_closure cl0` by metis_tac[dest_closure_partial_is_closure] >>
     `LENGTH used' = LENGTH used`
        by (first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     `used ≠ []` by (spose_not_then assume_tac >> fs[]) >> fs[] >> rveq >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
     `LIST_REL (val_rel (:'ffi) st.clock) rest rest' ∧
      LIST_REL (val_rel (:'ffi) st.clock) used used'`
       by metis_tac[EVERY2_APPEND] >>
     qspecl_then [`st.clock`, `v`, `v'`] mp_tac val_rel_cl_rw >> simp[] >>
     disch_then
       (qspecl_then [`st.clock - 1`, `used`, `used'`] mp_tac) >>
     simp[] >>
     qcase_tac `state_rel _ s0 s0'` >>
     disch_then (qspecl_then [`s0`, `s0'`, `NONE`] mp_tac) >>
     IMP_RES_THEN strip_assume_tac val_rel_mono >> simp[] >>
     IMP_RES_THEN strip_assume_tac val_rel_mono_list' >> simp[] >>
     simp[exec_rel_rw, evaluate_ev_def] >>
     disch_then (qspec_then `s0'.clock - 1` mp_tac) >> simp[] >>
     Cases_on `LENGTH rest = 0` >- (fs[LENGTH_NIL] >> simp[]) >>
     qabbrev_tac `
       ev0 = evaluate([b'],env',s0' with clock := s0'.clock - LENGTH used)` >>
     reverse
        (`(∃rv' s1'. ev0 = (Rval [rv'], s1')) ∨ ∃err s1'. ev0 = (Rerr err, s1')`
           by metis_tac[TypeBase.nchotomy_of ``:('a,'b) result``, pair_CASES,
                        evaluate_SING])
     >- (Cases_on `err` >> simp[res_rel_rw] >>
         qcase_tac `ev0 = (Rerr (Rabort a), s1)` >>
         Cases_on `a` >> simp[res_rel_rw]) >>
     simp[] >>
     simp[SimpL ``$==>``, res_rel_rw, evaluate_def] >> strip_tac >>
     qmatch_abbrev_tac `res_rel LHS (evaluate_app NONE rv' rest' s1')` >>
     `LHS = evaluate_app NONE cl0 rest (s0 with clock := s1'.clock)`
     suffices_by
       (strip_tac >> simp[] >> first_assum irule >- (fs[LENGTH_NIL]) >>
        simp[] >> strip_tac >> fs[] >> strip_tac >> fs[]) >>
     qunabbrev_tac `LHS` >>
     `rest ≠ []` by metis_tac [LENGTH] >>
     `dest_closure NONE cl0 rest =
        SOME (Partial_app (clo_add_partial_args rest cl0))`
       by metis_tac[dest_closure_partial_is_closure, stage_partial_app] >>
     simp[evaluate_app_rw] >> simp[dec_clock_def] >>
     qcase_tac `s0'.clock < LENGTH rr + LENGTH uu` >>
     `s0'.clock < LENGTH rr + LENGTH uu ⇔ s1'.clock < LENGTH rr` by simp[] >>
     simp[] >> rw[] >>
     Q.PAT_ASSUM `X = s1'.clock` (mp_tac o SYM) >> simp[])
 >- ((* Full, Partial *)
     qcase_tac `dest_closure loc v vs = SOME (Full_app b env rest)` >>
     qcase_tac `dest_closure loc v' vs' = SOME (Partial_app cl')` >>
     qcase_tac `st.clock < LENGTH vs' - LENGTH rest` >>
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
     `used ≠ []` by (Cases_on `used` >> fs[]) >>
     full_simp_tac (srw_ss() ++ numSimps.ARITH_NORM_ss) [] >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >> rveq >>
     simp[dec_clock_def] >>
     qspecl_then [`LENGTH rest`, `v'`, `vs'`, `cl'`]
       mp_tac dest_closure_partial_split' >> simp[] >>
     disch_then (qx_choosel_then [`cl0'`, `used'`, `rest'`] strip_assume_tac) >>
     `is_closure cl0'` by metis_tac[dest_closure_partial_is_closure] >>
     `LENGTH used' = LENGTH used`
        by (first_x_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     `used' ≠ []` by (spose_not_then assume_tac >> fs[]) >> fs[] >> rveq >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
     `LIST_REL (val_rel (:'ffi) st.clock) rest rest' ∧
      LIST_REL (val_rel (:'ffi) st.clock) used used'`
       by metis_tac[EVERY2_APPEND] >>
     qspecl_then [`st.clock`, `v`, `v'`] mp_tac val_rel_cl_rw >> simp[] >>
     disch_then
       (qspecl_then [`st.clock - 1`, `used`, `used'`] mp_tac) >>
     simp[] >>
     qcase_tac `state_rel _ s0 s0'` >>
     disch_then (qspecl_then [`s0`, `s0'`, `NONE`] mp_tac) >>
     IMP_RES_THEN strip_assume_tac val_rel_mono >> simp[] >>
     IMP_RES_THEN strip_assume_tac val_rel_mono_list' >> simp[] >>
     simp[exec_rel_rw, evaluate_ev_def] >>
     disch_then (qspec_then `s0'.clock - 1` mp_tac) >> simp[] >>
     Cases_on `LENGTH rest = 0` >- (fs[LENGTH_NIL] >> simp[]) >>
     qabbrev_tac `
       ev0 = evaluate([b],env,s0 with clock := s0'.clock - LENGTH used)` >>
     reverse
        (`(∃rv s1. ev0 = (Rval [rv], s1)) ∨ ∃err s1. ev0 = (Rerr err, s1)`
           by metis_tac[TypeBase.nchotomy_of ``:('a,'b) result``, pair_CASES,
                        evaluate_SING])
     >- (Cases_on `err` >> simp[res_rel_rw] >>
         qcase_tac `ev0 = (Rerr (Rabort a), s1)` >>
         Cases_on `a` >> simp[res_rel_rw]) >>
     simp[] >>
     simp[SimpL ``$==>``, res_rel_rw, evaluate_def] >> strip_tac >>
     qmatch_abbrev_tac `res_rel (evaluate_app NONE rv rest s1) RHS` >>
     `RHS = evaluate_app NONE cl0' rest' (s0' with clock := s1.clock)`
     suffices_by
       (strip_tac >> simp[] >> first_assum irule >- (fs[LENGTH_NIL]) >>
        simp[] >> strip_tac >> fs[]) >>
     qunabbrev_tac `RHS` >>
     `rest' ≠ []` by metis_tac [LENGTH] >>
     `dest_closure NONE cl0' rest' =
        SOME (Partial_app (clo_add_partial_args rest' cl0'))`
       by metis_tac[dest_closure_partial_is_closure, stage_partial_app] >>
     simp[evaluate_app_rw] >> simp[dec_clock_def])
 >- ((* Full, Full *)
     qcase_tac `dest_closure loc v vs = SOME (Full_app b1 env1 rest1)` >>
     qcase_tac `dest_closure loc v' vs' = SOME (Full_app b2 env2 rest2)` >>
     `(∃used1. vs = rest1 ++ used1 ∧
               dest_closure loc v used1 = SOME (Full_app b1 env1 [])) ∧
      (∃used2. vs' = rest2 ++ used2 ∧
               dest_closure loc v' used2 = SOME (Full_app b2 env2 []))`
       by metis_tac[dest_closure_full_split'] >>
     `LENGTH rest1 < LENGTH vs ∧ LENGTH rest2 < LENGTH vs'`
       by (imp_res_tac dest_closure_full_length >> simp[]) >>
     `used1 ≠ [] ∧ used2 ≠ []`
       by (ntac 2 (first_x_assum (assume_tac o Q.AP_TERM `list$LENGTH`)) >>
           rpt strip_tac >> lfs[]) >>
     `0 < LENGTH used1 ∧ 0 < LENGTH used2`
         by (Cases_on `used1` >> Cases_on `used2` >> fs[]) >>
     rveq >> lfs[] >>
     rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
     `LENGTH used1 = LENGTH used2 ∨ LENGTH used1 < LENGTH used2 ∨
      LENGTH used2 < LENGTH used1` by decide_tac
     >- ((* lengths equal *)
         full_simp_tac (srw_ss() ++ ARITH_ss ++ numSimps.ARITH_NORM_ss) [] >>
         rw[] >- (simp[res_rel_rw] >> metis_tac[val_rel_mono, ZERO_LESS_EQ]) >>
         `LIST_REL (val_rel (:'ffi) s'.clock) rest1 rest2 ∧
          LIST_REL (val_rel (:'ffi) s'.clock) used1 used2`
           by metis_tac[EVERY2_APPEND, LENGTH_APPEND] >>
         Q.UNDISCH_THEN `val_rel (:'ffi) s'.clock v v'` mp_tac >>
         simp[val_rel_cl_rw] >>
         disch_then
           (qspecl_then [`s'.clock - 1`, `used1`, `used2`, `s`, `s'`, `loc`]
                        mp_tac) >> simp[] >>
         `s'.clock - 1 ≤ s'.clock` by decide_tac >>
         `state_rel (s'.clock - 1) s s' ∧
          LIST_REL (val_rel (:'ffi) (s'.clock - 1)) used1 used2`
            by metis_tac[val_rel_mono, val_rel_mono_list] >> simp[] >>
         simp[exec_rel_rw, evaluate_ev_def] >>
         disch_then (qspec_then `s'.clock - 1` mp_tac) >>
         simp[dec_clock_def, evaluate_def] >>
         Cases_on `rest1 = []`
         >- (fs[LENGTH_NIL, LENGTH_NIL_SYM] >> rveq >> fs[evaluate_def]) >>
         `(∃r1 s1.
            evaluate ([b1], env1, s with clock := s'.clock - LENGTH used2) =
            (r1, s1)) ∧
          (∃r2 s2.
            evaluate ([b2], env2, s' with clock := s'.clock - LENGTH used2) =
            (r2, s2))` by metis_tac[PAIR] >> simp[] >>
         `(∃rv1. r1 = Rval [rv1]) ∨ (∃a1. r1 = Rerr (Rraise a1)) ∨
          r1 = Rerr (Rabort Rtimeout_error) ∨ r1 = Rerr (Rabort Rtype_error)`
           by (Cases_on `r1` >- (simp[] >> metis_tac[evaluate_SING]) >>
               qcase_tac `Rerr ee = Rerr _` >> Cases_on `ee` >> simp[] >>
               qcase_tac `aa = Rtype_error` >> Cases_on `aa` >> simp[]) >>
         rveq >>
         dsimp[SimpL ``$==>``, res_rel_rw, eqs]
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
         `usfx2 ≠ []` by (strip_tac >> fs[]) >>
         markerLib.RM_ALL_ABBREVS_TAC >> rveq >> fs[] >>
         full_simp_tac (srw_ss() ++ numSimps.ARITH_NORM_ss) [] >> fs[] >>
         simp[] >>
         `upfx2 ≠ []` by (strip_tac >> fs[]) >>
         `∃cl2. dest_closure NONE v' usfx2 = SOME (Partial_app cl2) ∧
                dest_closure NONE cl2 upfx2 = SOME (Full_app b2 env2 [])`
           by metis_tac[dest_closure_NONE_Full_to_Partial] >>
         rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
         `LIST_REL (val_rel (:'ffi) s'.clock) rest1 (rest2 ++ upfx2) ∧
          LIST_REL (val_rel (:'ffi) s'.clock) used1 usfx2`
            by metis_tac[LENGTH_APPEND, EVERY2_APPEND, APPEND_ASSOC] >>
         qspecl_then [`s'.clock`, `v`, `v'`] mp_tac val_rel_cl_rw >> simp[] >>
         disch_then (qspecl_then [`s'.clock - 1`, `used1`, `usfx2`,
                                  `s`, `s'`, `NONE`]
                                 mp_tac) >> simp[] >>
         `state_rel (s'.clock - 1) s s'`
           by metis_tac[val_rel_mono, DECIDE ``x - 1n ≤ x``] >>
         pop_assum (fn th => simp[th]) >>
         `LIST_REL (val_rel (:'ffi) (s'.clock - 1)) used1 usfx2`
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
               qcase_tac `Rerr ee = Rerr _` >> Cases_on `ee` >> simp[] >>
               qcase_tac `aa = Rtype_error` >> Cases_on `aa` >> simp[]) >>
         rveq >>
         dsimp[SimpL ``$==>``, res_rel_rw, bool_case_eq, eqs, pair_case_eq] >>
         simp[] >> strip_tac >>
         qmatch_abbrev_tac `res_rel (evaluate_app NONE rv1 rest1 s1) RHS` >>
         qcase_tac `state_rel s1.clock s1 s2` >>
         `RHS = evaluate_app NONE cl2 (rest2 ++ upfx2)
                   (s2 with clock := s1.clock)`
           suffices_by (
             disch_then SUBST1_TAC >> first_assum irule
             >- first_x_assum ACCEPT_TAC >>
             simp[] >> metis_tac[val_rel_mono_list, DECIDE ``x:num - y ≤ x``])>>
         simp[Abbr`RHS`] >> fs[] >>
         simp[Once evaluate_app_rw, SimpRHS] >>
         Q.UNDISCH_THEN
           `dest_closure NONE cl2 upfx2 = SOME (Full_app b2 env2 [])`
           (fn th => mp_tac (MATCH_MP (dest_closure_full_addargs
                                         |> GEN_ALL
                                         |> REWRITE_RULE [GSYM AND_IMP_INTRO])
                                      th)) >>
         disch_then (qspec_then `rest2` mp_tac) >>
         `LENGTH rest2 + LENGTH upfx2 ≤ max_app`
           by (imp_res_tac dest_closure_full_maxapp >> fs[] >> simp[]) >>
         simp[dec_clock_def] >>
         `LENGTH rest1 + LENGTH used1 - LENGTH rest2 =
           LENGTH upfx2 + LENGTH used1` by simp[] >> simp[] >> rw[] >>
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
         `usfx1 ≠ []` by (strip_tac >> fs[]) >>
         markerLib.RM_ALL_ABBREVS_TAC >> rveq >> fs[] >>
         full_simp_tac (srw_ss() ++ numSimps.ARITH_NORM_ss) [] >> fs[] >>
         simp[] >>
         `upfx1 ≠ []` by (strip_tac >> fs[]) >>
         `∃cl1. dest_closure NONE v usfx1 = SOME (Partial_app cl1) ∧
                dest_closure NONE cl1 upfx1 = SOME (Full_app b1 env1 [])`
           by metis_tac[dest_closure_NONE_Full_to_Partial] >>
         rpt (Q.UNDISCH_THEN `bool$T` kall_tac) >>
         `LIST_REL (val_rel (:'ffi) s'.clock) (rest1 ++ upfx1) rest2 ∧
          LIST_REL (val_rel (:'ffi) s'.clock) usfx1 used2`
            by metis_tac[LENGTH_APPEND, EVERY2_APPEND, APPEND_ASSOC] >>
         qspecl_then [`s'.clock`, `v`, `v'`] mp_tac val_rel_cl_rw >> simp[] >>
         disch_then (qspecl_then [`s'.clock - 1`, `usfx1`, `used2`,
                                  `s`, `s'`, `NONE`]
                                 mp_tac) >> simp[] >>
         `state_rel (s'.clock - 1) s s'`
           by metis_tac[val_rel_mono, DECIDE ``x - 1n ≤ x``] >>
         pop_assum (fn th => simp[th]) >>
         `LIST_REL (val_rel (:'ffi) (s'.clock - 1)) usfx1 used2`
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
               qcase_tac `Rerr ee = Rerr _` >> Cases_on `ee` >> simp[] >>
               qcase_tac `aa = Rtype_error` >> Cases_on `aa` >> simp[]) >>
         rveq >>
         dsimp[SimpL ``$==>``, res_rel_rw, bool_case_eq, eqs, pair_case_eq] >>
         simp[] >> strip_tac >>
         qmatch_abbrev_tac `res_rel LHS (evaluate_app NONE rv2 rest2 s2)` >>
         fs[] >> qcase_tac `state_rel s2.clock s1 s2` >>
         `LHS = evaluate_app NONE cl1 (rest1 ++ upfx1)
                   (s1 with clock := s2.clock)`
           suffices_by (
             disch_then SUBST1_TAC >> first_assum irule
             >- fs[LENGTH_NIL] >>
             simp[] >> metis_tac[val_rel_mono_list, DECIDE ``x:num - y ≤ x``])>>
         simp[Abbr`LHS`] >> fs[] >>
         simp[Once evaluate_app_rw, SimpRHS] >>
         Q.UNDISCH_THEN
           `dest_closure NONE cl1 upfx1 = SOME (Full_app b1 env1 [])`
           (fn th => mp_tac (MATCH_MP (dest_closure_full_addargs
                                         |> GEN_ALL
                                         |> REWRITE_RULE [GSYM AND_IMP_INTRO])
                                      th)) >>
         disch_then (qspec_then `rest1` mp_tac) >>
         `LENGTH rest1 + LENGTH upfx1 ≤ max_app`
           by (imp_res_tac dest_closure_full_maxapp >> fs[] >> simp[]) >>
         simp[dec_clock_def] >>
         `s'.clock < LENGTH upfx1 + LENGTH used2 ⇔ s2.clock < LENGTH upfx1`
            by simp[] >> simp[] >> rw[] >>
         `s'.clock - (LENGTH upfx1 + LENGTH used2) = s2.clock - LENGTH upfx1`
            by simp[] >>
         simp[]
        )
    )
)

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

val do_eq_val_rel = Q.store_thm ("do_eq_val_rel",
`(!v1 v2 i v1' v2' res.
  val_rel (:'ffi) i v1 v1' ∧
  val_rel (:'ffi) i v2 v2'
  ⇒
  do_eq v1 v2 = do_eq v1' v2') ∧
 (!vs1 vs2 i vs1' vs2'.
  LIST_REL (val_rel (:'ffi) i) vs1 vs1' ∧
  LIST_REL (val_rel (:'ffi) i) vs2 vs2'
  ⇒
  do_eq_list vs1 vs2 = do_eq_list vs1' vs2')`,
 ho_match_mp_tac do_eq_ind >>
 rw [do_eq_def] >>
 rw [do_eq_def]
 >- (
   every_case_tac >>
   fs [val_rel_rw, is_closure_def] >>
   metis_tac [LIST_REL_LENGTH])
 >- (
   Cases_on `v1` >>
   Cases_on `y` >>
   fs [val_rel_rw, is_closure_def] >>
   Cases_on `v2` >>
   Cases_on `y'` >>
   fs [val_rel_rw, is_closure_def]
   >- metis_tac [LIST_REL_LENGTH]
   >- (
     rw []
     >- (
       fs [] >>
       first_x_assum (qspecl_then [`i`, `Block n l'`, `Block n l'''`] mp_tac) >>
       simp [val_rel_rw] >>
       rw [] >>
       every_case_tac >>
       rw [] >>
       metis_tac [LIST_REL_LENGTH]) >>
     metis_tac [LIST_REL_LENGTH])
   >- metis_tac [LIST_REL_LENGTH]));

val get_global_state_rel = Q.store_thm ("get_global_state_rel",
`!i (s : 'ffi closSem$state) s'.
  state_rel i s s'
  ⇒
  OPTREL (OPTREL (val_rel (:'ffi) i)) (get_global n s.globals) (get_global n s'.globals)`,
 rw [Once state_rel_rw, get_global_def] >>
 fs [quotient_optionTheory.OPTION_REL_def] >>
 imp_res_tac LIST_REL_LENGTH >>
 fs [] >>
 metis_tac [LIST_REL_EL_EQN]);

val v_to_list_val_rel = Q.store_thm ("v_to_list_val_rel",
`!v v' i.
  val_rel (:'ffi) i v v'
  ⇒
  OPTREL (LIST_REL (val_rel (:'ffi) i)) (v_to_list v) (v_to_list v')`,
 ho_match_mp_tac v_to_list_ind >>
 rw [v_to_list_def] >>
 Cases_on `v'` >>
 rw [v_to_list_def] >>
 fs [val_rel_rw, is_closure_def] >>
 rw [v_to_list_def, OPTREL_SOME] >>
 TRY (simp [OPTREL_def] >> NO_TAC) >>
 every_case_tac >>
 rw [] >>
 fs [OPTREL_def] >>
 metis_tac [NOT_SOME_NONE, SOME_11]);

val list_to_v_val_rel = Q.store_thm ("list_to_v_val_rel",
`!i vs vs'.
  LIST_REL (val_rel (:'ffi) i) vs vs'
  ⇒
  val_rel (:'ffi) i (list_to_v vs) (list_to_v vs')`,
 Induct_on `vs` >>
 rw [list_to_v_def, val_rel_rw] >>
 rw [list_to_v_def, val_rel_rw]);

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
       imp_res_tac get_global_state_rel >>
       pop_assum (qspec_then `n` mp_tac) >>
       simp [OPTREL_SOME] >>
       rw [] >>
       rw [])
     >- ((* global init *)
       imp_res_tac get_global_state_rel >>
       pop_assum (qspec_then `n'` mp_tac) >>
       simp [OPTREL_SOME] >>
       rw [] >>
       rw [] >>
       fs [OPTREL_def, val_rel_rw, Unit_def] >>
       rpt (pop_assum mp_tac) >>
       ONCE_REWRITE_TAC [state_rel_rw] >>
       rw [] >>
       match_mp_tac EVERY2_LUPDATE_same >>
       rw [OPTREL_SOME])
     >- ((* global extend *)
       rw [Unit_def, val_rel_rw] >>
       rpt (pop_assum mp_tac) >>
       ONCE_REWRITE_TAC [state_rel_rw] >>
       rw [] >>
       rw [OPTREL_def])
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
     >- (
       imp_res_tac v_to_list_val_rel >>
       pop_assum mp_tac >>
       simp [OPTREL_SOME] >>
       rw [] >>
       rw [val_rel_rw])
     >- (Cases_on `y` >>
         fs [val_rel_rw] >>
         metis_tac [list_to_v_val_rel])
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
         `do_eq y' y = Eq_val b` by metis_tac [do_eq_val_rel] >>
         rw [val_rel_rw, Boolv_def])
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
         imp_res_tac do_eq_val_rel >>
         every_case_tac >>
         fs [val_rel_rw])
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

val fn_partial_arg = Q.store_thm ("fn_partial_arg",
`!i' i vs vs' env env' args args' num_args e e'.
 i' ≤ i ∧
 LIST_REL (val_rel (:'ffi) i) vs vs' ∧
 LIST_REL (val_rel (:'ffi) i) env env' ∧
 LIST_REL (val_rel (:'ffi) i) args args' ∧
 exp_rel (:'ffi) [e] [e']
 ⇒
 val_rel (:'ffi) i'
  (Closure NONE args (vs ++ env) num_args e)
  (Closure NONE (args' ++ vs') env' (num_args + LENGTH vs') e')`,
 completeInduct_on `i'` >>
 rw [val_rel_rw, is_closure_def] >>
 imp_res_tac LIST_REL_LENGTH
 >- simp [check_closures_def, clo_can_apply_def, clo_to_num_params_def,
          clo_to_partial_args_def, rec_clo_ok_def, clo_to_loc_def] >>
 Cases_on `locopt` >>
 simp [dest_closure_def, check_loc_def] >>
 rw [] >>
 TRY decide_tac >>
 rw [exec_rel_rw, evaluate_ev_def, evaluate_def, check_loc_def] >>
 fs [NOT_LESS] >>
 rw [res_rel_rw]
 >- (
   fs [exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
   first_x_assum (qspecl_then [`i''`,
                           `REVERSE (TAKE (num_args - LENGTH args') (REVERSE vs'')) ++ args ++ vs ++ env`,
                           `REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs''')) ++ args' ++ vs' ++ env'`,
                           `s`,
                           `s'`] mp_tac) >>
   simp [] >>
   `LIST_REL (val_rel (:'ffi) i'') (REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs'')) ++ args ++ vs ++ env)
            (REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs''')) ++ args' ++ vs' ++ env')` by (
     match_mp_tac EVERY2_APPEND_suff >>
     `i'' ≤ i` by decide_tac >>
     reverse (rw [])
     >- metis_tac [val_rel_mono_list] >>
     match_mp_tac EVERY2_APPEND_suff >>
     reverse (rw [])
     >- metis_tac [val_rel_mono_list] >>
     match_mp_tac EVERY2_APPEND_suff >>
     rw [LIST_REL_REVERSE_EQ, EVERY2_TAKE] >>
     metis_tac [val_rel_mono_list]) >>
   simp [] >>
   disch_then (qspec_then `i''' + (LENGTH args' + 1) − num_args` mp_tac) >>
   simp [] >>
   rw [] >>
   every_case_tac >>
   simp [res_rel_rw] >>
   imp_res_tac evaluate_SING >>
   fs [res_rel_rw] >>
   TRY (qcase_tac `(Rerr error, r)`)
   >- (
     Cases_on `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs'')) = []`
     >- (
       `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs''')) = []` by (
         fs [DROP_NIL] >>
         decide_tac) >>
       simp [evaluate_def, res_rel_rw] >>
       metis_tac []) >>
     match_mp_tac res_rel_evaluate_app >>
     simp [LIST_REL_REVERSE_EQ] >>
     match_mp_tac EVERY2_DROP >>
     simp [LIST_REL_REVERSE_EQ] >>
     imp_res_tac evaluate_clock >>
     fs [] >>
     `r'.clock ≤ i''` by decide_tac >>
     metis_tac [val_rel_mono_list])
  >- (
    Cases_on `error` >>
    fs [res_rel_rw] >>
    qcase_tac `(Rerr (Rabort abort), r)` >>
    Cases_on `abort` >>
    fs [res_rel_rw]))
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
`!i loc env env' args args' num_args e e'.
  exp_rel (:'ffi) [e] [e'] ∧
  LIST_REL (val_rel (:'ffi) i) env env' ∧
  LIST_REL (val_rel (:'ffi) i) args args'
  ⇒
  val_rel (:'ffi) i (Closure NONE args env num_args e) (Closure NONE args' env' num_args e')`,
 rw [] >>
 qspecl_then [`i`, `i`, `[]`, `[]`, `env`, `env'`, `args`, `args'`]
       (match_mp_tac o SIMP_RULE (srw_ss()) []) fn_partial_arg >>
 rw []);

val compat_closure_some = Q.prove (
`!i l env env' args args' num_args e e'.
  LIST_REL (val_rel (:'ffi) i) env env' ∧
  LIST_REL (val_rel (:'ffi) i) args args' ∧
  exp_rel (:'ffi) [e] [e']
  ⇒
  val_rel (:'ffi) i (Closure (SOME l) args env num_args e) (Closure (SOME l) args' env' num_args e')`,
 completeInduct_on `i` >>
 rw [val_rel_rw, is_closure_def] >>
 imp_res_tac LIST_REL_LENGTH
 >- (
   rw [check_closures_def, clo_can_apply_def, clo_to_num_params_def,
       clo_to_partial_args_def, rec_clo_ok_def, clo_to_loc_def] >>
   fs []) >>
 `(?l. locopt = SOME l) ∨ locopt = NONE` by metis_tac [option_nchotomy]
 >- (
   simp [dest_closure_def, check_loc_def] >>
   rw [] >>
   fs [exec_rel_rw, evaluate_ev_def] >>
   reverse (rw [res_rel_rw])
   >- metis_tac [val_rel_mono, ZERO_LESS_EQ] >>
   fs [REVERSE_DROP, LASTN, res_rel_rw, TAKE_REVERSE, LASTN_LENGTH_ID] >>
   `LASTN (LENGTH vs') vs = vs` by metis_tac [LASTN_LENGTH_ID] >>
   fs [] >>
   `exec_rel (i'' − (LENGTH vs' − 1))
             (Exp [e] (vs++args++env),s with clock := i'' − (LENGTH vs' − 1))
             (Exp [e'] (vs'++args'++env'),s' with clock := i'' − (LENGTH vs' − 1))`
   by (
     fs [exp_rel_def] >>
     first_x_assum match_mp_tac >>
     rw [] >>
     `i'' − (LENGTH vs' − 1) ≤ i' ∧ i'' − (LENGTH vs' − 1) ≤ i` by decide_tac >>
     metis_tac [val_rel_mono_list, EVERY2_APPEND, val_rel_mono]) >>
   fs [exec_rel_rw, evaluate_ev_def] >>
   pop_assum (qspec_then `i'' - (LENGTH vs' - 1)` mp_tac) >>
   simp [] >>
   rw [] >>
   every_case_tac >>
   fs [res_rel_rw] >>
   imp_res_tac evaluate_SING >>
   fs []) >>
 simp [dest_closure_def, check_loc_def] >>
 rw [] >>
 rw [exec_rel_rw, evaluate_ev_def, evaluate_def, check_loc_def] >>
 fs [NOT_LESS] >>
 rw [res_rel_rw]
 >- (
   fs [exp_rel_def, exec_rel_rw, evaluate_ev_def] >>
   first_x_assum (qspecl_then [`i'`,
                           `REVERSE (TAKE (num_args - LENGTH args') (REVERSE vs)) ++ args ++ env`,
                           `REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs')) ++ args' ++ env'`,
                           `s`,
                           `s'`] mp_tac) >>
   simp [] >>
   `LIST_REL (val_rel (:'ffi) i') (REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs)) ++ args ++ env)
            (REVERSE (TAKE (num_args − LENGTH args') (REVERSE vs')) ++ args' ++ env')` by (
     match_mp_tac EVERY2_APPEND_suff >>
     `i' ≤ i` by decide_tac >>
     reverse (rw [])
     >- metis_tac [val_rel_mono_list] >>
     match_mp_tac EVERY2_APPEND_suff >>
     reverse (rw [])
     >- metis_tac [val_rel_mono_list] >>
     rw [LIST_REL_REVERSE_EQ] >>
     match_mp_tac EVERY2_TAKE >>
     rw [LIST_REL_REVERSE_EQ] >>
     metis_tac [val_rel_mono_list]) >>
   simp [] >>
   disch_then (qspec_then `i'' + (LENGTH args' + 1) − num_args` mp_tac) >>
   simp [] >>
   rw [] >>
   every_case_tac >>
   simp [res_rel_rw] >>
   imp_res_tac evaluate_SING >>
   fs [res_rel_rw] >>
   TRY (qcase_tac `(Rerr error, r)`)
   >- (
     Cases_on `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs)) = []`
     >- (
       `REVERSE (DROP (num_args − LENGTH args') (REVERSE vs')) = []` by (
         fs [DROP_NIL] >>
         decide_tac) >>
       simp [evaluate_def, res_rel_rw] >>
       metis_tac []) >>
     match_mp_tac res_rel_evaluate_app >>
     simp [LIST_REL_REVERSE_EQ] >>
     match_mp_tac EVERY2_DROP >>
     simp [LIST_REL_REVERSE_EQ] >>
     imp_res_tac evaluate_clock >>
     fs [] >>
     `r'.clock ≤ i''` by decide_tac >>
     metis_tac [val_rel_mono_list])
  >- (
    Cases_on `error` >>
    fs [res_rel_rw] >>
    qcase_tac `(Rerr (Rabort abort), r)` >>
    Cases_on `abort` >>
    fs [res_rel_rw]))
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
`!i l env env' args args' num_args e e'.
 LIST_REL (val_rel (:'ffi) i) env env' ∧
 LIST_REL (val_rel (:'ffi) i) args args' ∧
 exp_rel (:'ffi) [e] [e']
 ⇒
 val_rel (:'ffi) i (Closure l args env num_args e) (Closure l args' env' num_args e')`,
 rw [] >>
 Cases_on `l` >>
 metis_tac [compat_closure_some, compat_closure_none]);

val compat_fn = Q.store_thm ("compat_fn",
`!vars num_args e e' loc.
  exp_rel (:'ffi) [e] [e']
  ⇒
  exp_rel (:'ffi) [Fn loc vars num_args e] [Fn loc vars num_args e']`,
 rpt strip_tac >>
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def, evaluate_ev_def] >>
 rw [res_rel_rw] >>
 Cases_on `vars` >>
 fs []
 >- (
   reverse (rw [res_rel_rw])
   >- metis_tac [val_rel_mono] >>
   metis_tac [compat_closure, val_rel_mono_list, LIST_REL_NIL])
 >- (
   Cases_on `lookup_vars x env` >>
   fs [res_rel_rw] >>
   imp_res_tac val_rel_lookup_vars >>
   reverse (rw [])
   >- metis_tac [val_rel_mono] >>
   metis_tac [compat_closure, val_rel_mono_list, LIST_REL_NIL]));

val optCASE_NONE_T = Q.prove(
  `option_CASE opt T f ⇔ (∀r. opt = SOME r ⇒ f r)`,
  Cases_on `opt` >> simp[]);

val optCASE_NONE_F = Q.prove(
  `option_CASE opt F f ⇔ ∃r. opt = SOME r ∧ f r`,
  Cases_on `opt` >> simp[]);

val revtakerev = Q.store_thm("revtakerev",
  `∀n l. n ≤ LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = DROP (LENGTH l - n) l`,
  Induct >> simp[DROP_LENGTH_NIL] >>
  qx_gen_tac `l` >>
  `l = [] ∨ ∃f e. l = SNOC e f` by metis_tac[SNOC_CASES] >> simp[] >>
  simp[DROP_APPEND1]);

val exp_rel_sing =
    exp_rel_def |> Q.SPECL [`[e1]`, `[e2]`]
                |> SIMP_RULE (srw_ss()) [exec_rel_rw, evaluate_ev_def]

val compat_recclosure = Q.store_thm ("compat_recclosure",
`!i l env env' args args' funs funs' idx.
  LIST_REL (λ(n,e) (n',e'). n = n' ∧ exp_rel (:'ffi) [e] [e']) funs funs' ∧
  LIST_REL (val_rel (:'ffi) i) env env' ∧
  LIST_REL (val_rel (:'ffi) i) args args'
  ⇒
  val_rel (:'ffi) i (Recclosure l args env funs idx)
                    (Recclosure l args' env' funs' idx)`,
  qx_gen_tac `i` >> completeInduct_on `i` >>
  simp[val_rel_rw, is_closure_def, check_closures_def] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qx_genl_tac [`loc`, `N`] >>
      simp[clo_can_apply_def, clo_to_partial_args_def, clo_to_num_params_def,
           clo_to_loc_def, rec_clo_ok_def] >>
      qcase_tac `EL idx funs1` >> qcase_tac `LIST_REL _ funs1 funs2` >>
      qcase_tac `LENGTH args1 < FST (EL idx funs1)` >>
      qcase_tac `LENGTH args2 < FST (EL idx funs2)` >>
      `LENGTH funs2 = LENGTH funs1 ∧ LENGTH args2 = LENGTH args1`
        by metis_tac[LIST_REL_EL_EQN] >>
      qmatch_assum_abbrev_tac `LIST_REL FR funs1 funs2` >>
      qcase_tac `loc ≠ NONE` >> strip_tac >>
      `FR (EL idx funs1) (EL idx funs2)` by metis_tac[LIST_REL_EL_EQN] >>
      pop_assum mp_tac >> simp[Abbr`FR`, UNCURRY] >> strip_tac >>
      Cases_on `loc` >> fs[]) >>
  qcase_tac `Recclosure loc args1 env1 funs1 idx` >>
  qcase_tac `LIST_REL _ funs1 funs2` >>
  qcase_tac `LIST_REL _ env1 env2` >>
  qcase_tac `LIST_REL _ args1 args2` >>
  `LENGTH funs2 = LENGTH funs1 ∧ LENGTH env2 = LENGTH env1 ∧
   LENGTH args2 = LENGTH args1` by metis_tac[LIST_REL_EL_EQN] >>
  simp[optCASE_NONE_T, optCASE_NONE_F] >> rpt gen_tac >> strip_tac >>
  qx_gen_tac `dc1` >>
  simp[dest_closure_def, SimpL ``$==>``, UNCURRY] >>
  Cases_on `idx < LENGTH funs1` >> simp[] >>
  `∃fn1 fe1. EL idx funs1 = (fn1, fe1)`
     by (Cases_on `EL idx funs1` >> simp[]) >> simp[] >>
  qcase_tac `LIST_REL (val_rel (:'ffi) j) vs1 vs2` >>
  `LENGTH vs2 = LENGTH vs1` by metis_tac[LIST_REL_EL_EQN] >>
  simp[revdroprev, revtakerev] >> Cases_on `LENGTH args1 < fn1` >> simp[] >>
  simp[bool_case_eq] >>
  qmatch_assum_abbrev_tac `LIST_REL FR funs1 funs2` >>
  `∃fe2. EL idx funs2 = (fn1, fe2) ∧ exp_rel (:'ffi) [fe1] [fe2]`
    by (`FR (EL idx funs1) (EL idx funs2)` by metis_tac [LIST_REL_EL_EQN] >>
        pop_assum mp_tac >>
        Cases_on `EL idx funs2` >> simp[Abbr`FR`]) >>
  strip_tac >>
  simp[dest_closure_def, revdroprev, revtakerev, exec_rel_rw,
       evaluate_ev_def] >>
  qx_gen_tac `k`
  >- (reverse (rw[])
      >- (simp[res_rel_rw] >> metis_tac[DECIDE ``0n ≤ x``, val_rel_mono]) >>
      qmatch_abbrev_tac `
        res_rel (pair_CASE (evaluate ([fe1], ENV1, _)) _)
                (pair_CASE (evaluate ([fe2], ENV2, _)) _)` >>
      `LIST_REL (val_rel (:'ffi) j) ENV1 ENV2`
        by (simp[Abbr`ENV1`, Abbr`ENV2`] >>
            reverse (irule EVERY2_APPEND_suff)
            >- metis_tac[val_rel_mono_list, DECIDE ``x < y:num ⇒ x ≤ y``] >>
            reverse (irule EVERY2_APPEND_suff)
            >- (simp[LIST_REL_GENLIST] >> rpt strip_tac >>
                first_x_assum irule >> simp[] >>
                metis_tac[val_rel_mono_list, DECIDE ``x < y:num ⇒ x ≤ y``]) >>
            irule EVERY2_APPEND_suff >- simp[EVERY2_DROP] >>
            metis_tac[val_rel_mono_list, DECIDE ``x < y:num ⇒ x ≤ y``]) >>
      Q.UNDISCH_THEN `exp_rel (:'ffi) [fe1] [fe2]` mp_tac >>
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
          >- (rpt strip_tac >> simp[] >> fs[]) >>
          qcase_tac `ev1 = (Rerr (Rabort a), s1)` >>
          Cases_on `a` >> simp[res_rel_rw] >> rpt strip_tac >> simp[]) >>
      simp[res_rel_rw] >> dsimp[] >> rpt strip_tac >>
      qcase_tac `evaluate([fe2], ENV2, _) = (Rval [rv2], s2')` >>
      qmatch_abbrev_tac `res_rel (evaluate_app _ _ (TAKE N vs1) _) _` >>
      `N ≤ LENGTH vs1` by simp[Abbr`N`] >>
      Cases_on `N = 0` >- (simp[res_rel_rw] >> fs[]) >>
      irule res_rel_evaluate_app
      >- (Cases_on `N` >> fs[] >> Cases_on `vs1` >> fs[]) >>
      simp[] >> irule EVERY2_TAKE >>
      irule val_rel_mono_list >> qexists_tac `j` >> simp[] >>
      imp_res_tac evaluate_clock >> fs[] >> simp[Abbr`CK`]) >>
  reverse (rw[])
  >- (simp[res_rel_rw] >> metis_tac[DECIDE ``0n ≤ x``, val_rel_mono]) >>
  simp[res_rel_rw] >> conj_tac
  >- (first_x_assum irule >> simp[]
      >- (irule EVERY2_APPEND_suff >> irule val_rel_mono_list
          >- (qexists_tac `j` >> simp[]) >>
          qexists_tac `i` >> simp[]) >>
      irule val_rel_mono_list >> qexists_tac `i` >> simp[]) >>
  irule (last (CONJUNCTS val_rel_mono)) >> qexists_tac `j` >> simp[])

val compat_letrec = Q.store_thm ("compat_letrec",
`!loc vars funs e funs' e'.
  LIST_REL (\(n,e) (n',e'). n = n' ∧ exp_rel (:'ffi) [e] [e']) funs funs' ∧
  exp_rel (:'ffi) [e] [e']
  ⇒
  exp_rel (:'ffi) [Letrec loc vars funs e] [Letrec loc vars funs' e']`,
 rpt strip_tac >>
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def, evaluate_ev_def] >>
 reverse (rw [res_rel_rw])
 >- (
   full_simp_tac std_ss [LIST_REL_EL_EQN, EVERY_EL] >>
   fs [] >>
   Cases_on `EL n funs` >>
   Cases_on `EL n funs'` >>
   fs [] >>
   rpt (first_x_assum (qspec_then `n` mp_tac)) >>
   rw []) >>
 Cases_on `vars` >>
 fs []
 >- (
   `exec_rel i' (Exp [e] (GENLIST (Recclosure loc [] env funs) (LENGTH funs) ++ env), s)
                (Exp [e'] (GENLIST (Recclosure loc [] env' funs') (LENGTH funs') ++ env'), s')`
   by (
     fs [exp_rel_def] >>
     first_x_assum match_mp_tac >>
     rw []
     >- metis_tac [val_rel_mono] >>
     match_mp_tac EVERY2_APPEND_suff >>
     reverse conj_tac
     >- metis_tac [val_rel_mono_list] >>
     imp_res_tac LIST_REL_LENGTH >>
     rw [LIST_REL_GENLIST] >>
     match_mp_tac compat_recclosure >>
     rw [exp_rel_def] >>
     metis_tac [val_rel_mono_list]) >>
   fs [exec_rel_rw, evaluate_ev_def])
 >- (
   Cases_on `lookup_vars x env` >>
   fs [res_rel_rw] >>
   imp_res_tac val_rel_lookup_vars >>
   rw [] >>
   `exec_rel i' (Exp [e] (GENLIST (Recclosure loc [] x' funs) (LENGTH funs) ++ env), s)
                (Exp [e'] (GENLIST (Recclosure loc [] vs2'' funs') (LENGTH funs') ++ env'), s')`
   by (
     fs [exp_rel_def] >>
     first_x_assum match_mp_tac >>
     rw []
     >- metis_tac [val_rel_mono] >>
     match_mp_tac EVERY2_APPEND_suff >>
     reverse conj_tac
     >- metis_tac [val_rel_mono_list] >>
     imp_res_tac LIST_REL_LENGTH >>
     rw [LIST_REL_GENLIST] >>
     match_mp_tac compat_recclosure >>
     rw [exp_rel_def] >>
     metis_tac [val_rel_mono_list]) >>
   fs [exec_rel_rw, evaluate_ev_def]));

val compat_op = Q.store_thm ("compat_op",
`!op es es'.
  exp_rel (:'ffi) es es'
  ⇒
  exp_rel (:'ffi) [Op op es] [Op op es']`,
 rw [exp_rel_def] >>
 simp [exec_rel_rw, evaluate_def] >>
 rw [] >>
 `exec_rel i' (Exp es env, s with clock := i') (Exp es' env', s' with clock := i')`
         by metis_tac [val_rel_mono_list, val_rel_mono, state_rel_clock] >>
 pop_assum mp_tac >>
 simp [exec_rel_rw] >>
 rw [] >>
 pop_assum (qspec_then `i'` mp_tac) >>
 rw [] >>
 fs [evaluate_ev_def, evaluate_def] >>
 reverse (Q.ISPEC_THEN `evaluate (es,env,s with clock := i')` strip_assume_tac
                         result_store_cases) >>
 rw [res_rel_rw] >>
 fs [res_rel_rw]
 >- metis_tac [] >>
 metis_tac [res_rel_do_app]);

val compat = save_thm ("compat",
  LIST_CONJ [compat_nil, compat_cons, compat_var, compat_if, compat_let, compat_raise,
             compat_handle, compat_tick, compat_call, compat_app,
             compat_fn, compat_letrec, compat_op]);

val exp_rel_refl = Q.store_thm ("exp_rel_refl",
`(!e. exp_rel (:'ffi) [e] [e]) ∧
 (!es. exp_rel (:'ffi) es es) ∧
 (!(ne :num # closLang$exp). FST ne = FST ne ∧ exp_rel (:'ffi) [SND ne] [SND ne]) ∧
 (!funs. LIST_REL (\(n:num,e) (n',e'). n = n' ∧ exp_rel (:'ffi) [e] [e']) funs funs)`,
 Induct >>
 rw [] >>
 TRY (PairCases_on `ne`) >>
 fs [] >>
 metis_tac [compat]);

val val_rel_refl = Q.store_thm ("val_rel_refl",
`(!v. val_rel (:'ffi) i v v) ∧
 (!vs. LIST_REL (val_rel (:'ffi) i) vs vs)`,
 ho_match_mp_tac v_induction >>
 rw []
 >- rw [val_rel_rw]
 >- rw [val_rel_rw]
 >- rw [val_rel_rw]
 >- metis_tac [exp_rel_refl, compat_closure]
 >- metis_tac [exp_rel_refl, compat_recclosure]);

val ref_v_rel_refl = Q.store_thm ("ref_v_rel_refl",
`!i rv. ref_v_rel (:'ffi) i rv rv`,
 rw [] >>
 Cases_on `rv` >>
 rw [ref_v_rel_rw] >>
 metis_tac [val_rel_refl, refl_list_rel_refl]);

val state_rel_refl = Q.store_thm ("state_rel_refl",
`(!i s. state_rel i s s)`,
 rw [Once state_rel_rw]
 >- metis_tac [refl_list_rel_refl, val_rel_refl, OPTREL_refl]
 >- metis_tac [fmap_rel_refl, ref_v_rel_refl]
 >- (
   match_mp_tac fmap_rel_refl >>
   simp [FORALL_PROD] >>
   rw [] >>
   `exp_rel (:'a) [p_2] [p_2]` by metis_tac [exp_rel_refl] >>
   fs [exp_rel_def]));

val val_rel_closure = Q.store_thm(
  "val_rel_closure",
  `val_rel (:'ffi) i C1 C2 ∧ is_closure C1 ⇒
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
    val vs' = set_diff (map (Term.inst tys) vs) (map #redex tms)
  in
    GENL vs' (INST_TY_TERM theta specth)
  end

val val_rel_trans = Q.store_thm ("val_rel_trans",
`(!(ffi:'ffi itself) i v1 v2.
    val_rel ffi i v1 v2 ⇒ !v3. (!i. val_rel ffi i v2 v3) ⇒ val_rel ffi i v1 v3) ∧
 (!i (st1:val_or_exp # 'ffi closSem$state) st2.
    exec_rel i st1 st2 ⇒ !st3. (!i. exec_rel i st2 st3) ⇒ exec_rel i st1 st3) ∧
 (!(ffi:'ffi itself) i rv1 rv2.
    ref_v_rel ffi i rv1 rv2 ⇒
    !rv3. (!i. ref_v_rel ffi i rv2 rv3) ⇒ ref_v_rel ffi i rv1 rv3) ∧
 (!i (s1 : 'ffi closSem$state) s2.
    state_rel i s1 s2 ⇒ !s3. (!i. state_rel i s2 s3) ⇒ state_rel i s1 s3)`,
 ho_match_mp_tac val_rel_ind >>
 rw [is_closure_def]
 >- fs [val_rel_rw]
 >- (
   fs [val_rel_rw] >>
   Cases_on `v3` >>
   fs [val_rel_rw] >>
   match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] LIST_REL_trans) >>
   metis_tac [LIST_REL_LENGTH, MEM_EL, LIST_REL_EL_EQN])
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- fs [val_rel_rw]
 >- (
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [val_rel_rw]) >> fs[]
 )
 (* Closure *)
 >- (
  qcase_tac `val_rel _ i (Closure locopt argE closE n e) V` >>
  qmatch_assum_rename_tac `val_rel _ i (Closure _ _ _ _ _) V0` >>
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
  rpt (first_x_assum (qspecl_then [`j`, `s1`, `s2`]
                        (fn th => mp_tac th >>
                                  simp[SimpL ``$==>``] >>
                                  strip_tac))) >>
  rpt (first_x_assum (qspecl_then [`vs1`, `vs2`, `clocopt`]
        (fn th => mp_tac th >>
                  asm_simp_tac (srw_ss() ++ ETA_ss) [SimpL ``$==>``] >>
                  strip_tac))) >>
  qx_gen_tac `dcres` >>
  disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                       mp_tac th) >> strip_tac >>
  qpat_assum `val_rel _ i _ V0` mp_tac >>
  simp[SimpL ``$==>``, val_rel_rw] >>
  disch_then (qspecl_then [`j`, `vs1`, `vs2`, `s1`, `s2`, `clocopt`] mp_tac) >>
  simp[SimpL ``$==>``, optCASE_NONE_F] >>
  disch_then (qx_choose_then `dcres2` mp_tac) >>
  `vs2 ≠ []` by (strip_tac >> fs[]) >>
  Cases_on `dcres` >> Cases_on `dcres2` >> simp[SimpL ``$==>``] >>
  disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                       strip_assume_tac th) >>
  simp_tac (srw_ss()) [] >>
  Q.UNDISCH_THEN `!i. val_rel (:'ffi) i V0 V` mp_tac >>
  Cases_on `V0` >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [is_closure_def]) >>
  simp[SimpL ``$==>``, val_rel_rw] >> TRY (FIRST_ASSUM ACCEPT_TAC) >>
  simp[optCASE_NONE_F, optCASE_NONE_T] >>
  disch_then (mp_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  disch_then (fn th => first_assum (fn termth =>
    mp_tac (PART_MATCH' (fn t => t |> dest_imp |> #2 |> dest_imp |> #1)
                        th (concl termth)))) >>
  simp[SimpL ``$==>``] >> simp_tac(srw_ss()) [] >> simp[] >>
  disch_then (mp_tac o
              CONV_RULE (RESORT_FORALL_CONV (sort_vars ["s", "s'", "vs'"]))) >>
  disch_then (qspecl_then [`s2`, `s2`, `vs2`] mp_tac) >>
  simp[val_rel_refl, state_rel_refl] >>
  disch_then (qspecl_then [`SUC k`, `k`] (mp_tac o Q.GEN `k`)) >>
  simp[] >> Cases_on `dest_closure clocopt V vs2` >> simp[] >>
  qcase_tac `dest_closure clocopt V vs2 = SOME cl` >> Cases_on `cl` >>
  simp[])
 (* RecClosure *)
 >- (
  qcase_tac `val_rel _ i (Recclosure locopt argE closE fns idx) C3` >>
  qmatch_assum_rename_tac `val_rel _ i (Recclosure _ _ _ _ _) C2` >>
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
  rpt (first_x_assum (qspecl_then [`j`, `s1`, `s2`]
                        (fn th => mp_tac th >>
                                  simp[SimpL ``$==>``] >>
                                  strip_tac))) >>
  rpt (first_x_assum (qspecl_then [`vs1`, `vs2`, `clocopt`]
        (fn th => mp_tac th >>
                  asm_simp_tac (srw_ss() ++ ETA_ss) [SimpL ``$==>``] >>
                  strip_tac))) >>
  qx_gen_tac `dcres` >>
  disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                       mp_tac th) >> strip_tac >>
  qpat_assum `val_rel _ i _ C2` mp_tac >>
  simp[SimpL ``$==>``, val_rel_rw] >>
  disch_then (qspecl_then [`j`, `vs1`, `vs2`, `s1`, `s2`, `clocopt`] mp_tac) >>
  simp[SimpL ``$==>``, optCASE_NONE_F] >>
  disch_then (qx_choose_then `dcres2` mp_tac) >>
  `vs2 ≠ []` by (strip_tac >> fs[]) >>
  Cases_on `dcres` >> Cases_on `dcres2` >> simp[SimpL ``$==>``] >>
  disch_then (fn th => RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [th]) >>
                       strip_assume_tac th) >>
  simp_tac (srw_ss()) [] >>
  Q.UNDISCH_THEN `!i. val_rel (:'ffi) i C2 C3` mp_tac >>
  Cases_on `C2` >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [is_closure_def]) >>
  simp[SimpL ``$==>``, val_rel_rw] >> TRY (FIRST_ASSUM ACCEPT_TAC) >>
  simp[optCASE_NONE_F, optCASE_NONE_T] >>
  disch_then (mp_tac o SIMP_RULE (srw_ss() ++ DNF_ss) []) >>
  disch_then (fn th => first_assum (fn termth =>
    mp_tac (PART_MATCH' (fn t => t |> dest_imp |> #2 |> dest_imp |> #1)
                        th (concl termth)))) >>
  simp[SimpL ``$==>``] >> simp_tac(srw_ss()) [] >> simp[] >>
  disch_then (mp_tac o
              CONV_RULE (RESORT_FORALL_CONV (sort_vars ["s", "s'", "vs'"]))) >>
  disch_then (qspecl_then [`s2`, `s2`, `vs2`] mp_tac) >>
  simp[val_rel_refl, state_rel_refl] >>
  disch_then (qspecl_then [`SUC k`, `k`] (mp_tac o Q.GEN `k`)) >>
  simp[] >> Cases_on `dest_closure clocopt C3 vs2` >> simp[] >>
  qcase_tac `dest_closure clocopt C3 vs2 = SOME cl` >> Cases_on `cl` >>
  simp[])
 (* exec_rel *)
 >- cheat
 >- fs [ref_v_rel_rw]
 >- (
   Cases_on `rv3` >>
   fs [ref_v_rel_rw] >>
   match_mp_tac (SIMP_RULE (srw_ss()) [PULL_FORALL, AND_IMP_INTRO] LIST_REL_trans) >>
   metis_tac [LIST_REL_LENGTH, MEM_EL, LIST_REL_EL_EQN])
 >- fs [ref_v_rel_rw]
 >- fs [ref_v_rel_rw]
 >- ( (* state_rel *)
   pop_assum mp_tac >>
   pop_assum mp_tac >>
   ONCE_REWRITE_TAC [state_rel_rw] >>
   rw []
   >- cheat
   >- cheat
   >- cheat));

val exp_rel_trans = Q.store_thm ("exp_rel_trans",
`!e1 e2 e3. exp_rel (:'ffi) e1 e2 ∧ exp_rel (:'ffi) e2 e3 ⇒ exp_rel (:'ffi) e1 e3`,
 rw [exp_rel_def] >>
 `!i. state_rel i s' s' ∧ LIST_REL (val_rel (:'ffi) i) env' env'` by metis_tac [val_rel_refl, state_rel_refl] >>
 metis_tac [val_rel_trans]);

val _ = export_theory ();

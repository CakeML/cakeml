open HolKernel Parse boolLib bossLib;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory
open rich_listTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory;

val _ = new_theory "clos_relation";

val cEval_length_imp = Q.prove (
`!xs env s1 vs s2.
  cEval (xs, env, s1) = (Result vs, s2)
  ⇒
  LENGTH xs = LENGTH vs`,
 rw [] >>
 assume_tac (Q.SPECL [`xs`, `env`, `s1`] (hd (CONJUNCTS cEval_LENGTH))) >>
 rfs []);

val ect = BasicProvers.EVERY_CASE_TAC;

val is_closure_def = Define `
(is_closure (Closure _ _ _ _ _) = T) ∧
(is_closure (Recclosure _ _ _ _ _) = T) ∧
(is_closure _ = F)`;

(*
val (val_rel_rules, val_rel_ind, val_rel_cases) = Hol_reln `
(!n. val_rel (Number n) (Number n)) ∧
(!n vs vs'. 
  LIST_REL val_rel vs vs'
  ⇒
  val_rel (Block n vs) (Block n vs')) ∧
(!l.
  val_rel (RefPtr l) (RefPtr l)) ∧
(!v v'.
  is_closure v ∧ 
  is_closure v' ∧
  (!vs vs' s s' r r' s1 s1'.
    LIST_REL val_rel vs vs' ∧
    state_rel s s' ∧
    cEvalApp NONE v vs s = (r,s1) ∧
    cEvalApp NONE v' vs' s' = (r',s1')
    ⇒ 
    res_rel r r' ∧
    state_rel s1 s1')
  ⇒
  val_rel v v') ∧
(!ws.
  ref_v_rel (ByteArray ws) (ByteArray ws)) ∧
(!vs vs'.
  LIST_REL val_rel vs vs'
  ⇒
  ref_v_rel (ValueArray vs) (ValueArray vs')) ∧
(!s s'.
  LIST_REL (OPTION_REL val_rel) s.globals s'.globals ∧
  fmap_rel ref_v_rel s.refs s'.refs ∧
  s.clock = s'.clock ∧
  s.code = s'.code ∧
  s.output = s'.output ∧
  s.restrict_envs = s'.restrict_envs
  ⇒
  state_rel s s') ∧
(!vs vs'.
  LIST_REL val_rel vs vs'
  ⇒
  res_rel (Result vs) (Result vs')) ∧
(!v v'.
  val_rel v v'
  ⇒
  res_rel (Exception v) (Exception v')) ∧
(res_rel TimeOut TimeOut)`;
*)

val check_clocks_def = Define `
check_clocks f i s1 s2 ⇔
  s1.clock = i ∧ s2.clock = f i`;

val dec_clock_fn_def = Define `
dec_clock_fn f (old_start : num) new_start = (\clock. f (clock + (old_start - new_start)))`;

val good_clock_fn_def = Define `
good_clock_fn (f : num -> num) ⇔
  (!x y. x ≤ y ⇒ f x ≤ f y) ∧
  (!x. ?y. x < f y)`;

val good_clock_fn_id = Q.store_thm ("good_clock_fn_id[simp]",
`good_clock_fn I`,
 rw [good_clock_fn_def] >>
 qexists_tac `x + 1` >>
 simp []);

val dec_clock_fn_id = Q.prove (
`!f c. dec_clock_fn f c c = f`,
 rw [dec_clock_fn_def, FUN_EQ_THM]);

val good_clock_fn_dec = Q.prove (
`!f x y. good_clock_fn f ⇒ good_clock_fn (dec_clock_fn f x y)`,
 rw [dec_clock_fn_def, good_clock_fn_def] >>
 pop_assum (qspec_then `x'` mp_tac) >>
 rw [] >>
 qexists_tac `y'` >>
 `y' ≤ y' + (x - y)` by decide_tac >>
 res_tac >>
 decide_tac);

val val_rel_def = tDefine "val_rel" `
(val_rel (f : num -> num) (i:num) (Number n) (Number n') ⇔ n = n') ∧
(val_rel f i (Block n' vs) (Block n vs') ⇔ n = n' ∧ LIST_REL (val_rel f i) vs vs') ∧
(val_rel f i (RefPtr l) (RefPtr l') ⇔ l = l') ∧
(val_rel f i v v' ⇔
  if is_closure v ∧ is_closure v' then
    !i' vs vs' s s'.
      if i' < i ∧ check_clocks f i' s s' then
        LIST_REL (val_rel f i') vs vs' ∧ state_rel f s s' ⇒
        res_rel (dec_clock_fn f s.clock) (cEvalApp NONE v vs s) (cEvalApp NONE v' vs' s')
      else
        T 
  else 
    F) ∧
(ref_v_rel f i (ByteArray ws) (ByteArray ws') ⇔ ws = ws') ∧
(ref_v_rel f i (ValueArray vs) (ValueArray vs') ⇔ LIST_REL (val_rel f i) vs vs') ∧
(ref_v_rel f i _ _ ⇔ F) ∧
(state_rel f s s' ⇔
  LIST_REL (OPTION_REL (val_rel f s.clock)) s.globals s'.globals ∧
  fmap_rel (ref_v_rel f s.clock) s.refs s'.refs ∧
  fmap_rel (λ(n,e) (n',e'). n = n' ∧ code_rel f s.clock [e] [e']) s.code s'.code ∧
  s.output = s'.output ∧
  s.restrict_envs = s'.restrict_envs) ∧
(res_rel (f' : num -> num -> num) (Result vs, s) (Result vs', s') ⇔ 
  LIST_REL (val_rel (f' s.clock) s.clock) vs vs' ∧
  state_rel (f' s.clock) s s') ∧
(res_rel f' (Exception v, s) (Exception v', s') ⇔ 
  val_rel (f' s.clock) s.clock v v' ∧
  state_rel (f' s.clock) s s') ∧
(res_rel f' (TimeOut, s) (TimeOut, s') ⇔
  state_rel (f' s.clock) s s') ∧
(res_rel f' (Error, s) _ ⇔ T) ∧
(res_rel f' _ _ ⇔ F) ∧
(code_rel f i es es' ⇔
  !env env' s s' i'.
    if i' < i ∧ check_clocks f i' s s' then
      LIST_REL (val_rel f i') env env' ∧ state_rel f s s' ⇒
      res_rel (dec_clock_fn f s.clock) (cEval (es,env,s)) (cEval (es',env',s'))
    else
      T)`
(WF_REL_TAC `inv_image ($< LEX $< LEX $<) 
             (\x. case x of 
                     | INL (f,i,v,v') => (i:num,0:num,clos_val_size v) 
                     | INR (INL (f,i,r,r')) => (i,1,0)
                     | INR (INR (INL (f,s,s'))) => (s.clock,3,0)
                     | INR (INR (INR (INL (f,res,res')))) => ((SND res).clock,4,0)
                     | INR (INR (INR (INR (f,i,es,es')))) => (i,2,0))` >>
 rw [] >>
 simp [clos_val_size_def] >>
 fs [is_closure_def, check_clocks_def]
 >- (Cases_on `cEvalApp NONE (Closure v17 v18 v19 v20 v21) vs s` >>
     fs [] >>
     imp_res_tac cEvalApp_clock >>
     decide_tac)
 >- (Cases_on `cEvalApp NONE (Recclosure v22 v23 v24 v25 v26) vs s` >>
     fs [] >>
     imp_res_tac cEvalApp_clock >>
     decide_tac)
 >- (Cases_on `cEval (es,env,s)` >>
     fs [check_clocks_def] >>
     rw [] >>
     imp_res_tac cEval_clock >>
     decide_tac)
 >- (Induct_on `vs` >>
     rw [] >>
     res_tac >>
     simp [clos_val_size_def]));

val val_rel_ind = fetch "-" "val_rel_ind";

fun find_clause good_const = 
  good_const o fst o strip_comb o fst o dest_eq o snd o strip_forall o concl;

val val_rel_rw = 
  let val clauses = CONJUNCTS val_rel_def
      fun good_const x = same_const ``val_rel`` x orelse same_const ``ref_v_rel`` x orelse same_const ``res_rel`` x
  in
    LIST_CONJ (List.filter (find_clause good_const) clauses)
  end;

val code_rel_rw = 
  let val clauses = CONJUNCTS val_rel_def
      fun good_const x = same_const ``code_rel`` x
  in
    LIST_CONJ (List.filter (find_clause good_const) clauses)
  end;

val state_rel_rw = 
  let val clauses = CONJUNCTS val_rel_def
      fun good_const x = same_const ``state_rel`` x
  in
    LIST_CONJ (List.filter (find_clause good_const) clauses)
  end;

val exp_rel_def = Define `
exp_rel es es' ⇔ !i. ?f. good_clock_fn f ∧ code_rel f i es es'`;

val val_rel_mono = Q.prove (
`(!f i v v'. val_rel f i v v' ⇒ ∀i'. i' ≤ i ⇒ val_rel f i' v v') ∧
 (!f i r r'. ref_v_rel f i r r' ⇒ ∀i'. i' ≤ i ⇒ ref_v_rel f i' r r') ∧
 (!f s s'. state_rel f s s' ⇒ state_rel f s s') ∧
 (!f res res'. res_rel f res res' ⇒ res_rel f res res') ∧
 (!f i es es'. code_rel f i es es' ⇒ ∀i'. i' ≤ i ⇒ code_rel f i' es es')`,
 ho_match_mp_tac val_rel_ind >>
 rw [] >>
 TRY (fs [Once val_rel_def, is_closure_def]  >> NO_TAC)
 >- (fs [val_rel_def, LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
 >- (fs [val_rel_rw] >>
     Cases_on `v'` >>
     fs [is_closure_def] >>
     rw [val_rel_rw, is_closure_def] >>
     `i'' < i` by decide_tac >>
     fs [] >>
     metis_tac [])
 >- (fs [val_rel_rw] >>
     Cases_on `v'` >>
     fs [is_closure_def] >>
     rw [val_rel_rw, is_closure_def] >>
     `i'' < i` by decide_tac >>
     fs [] >>
     metis_tac [])
 >- (fs [val_rel_rw, LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
     (*
 >- (qpat_assum `state_rel i x y` mp_tac >>
     simp [Once val_rel_def] >>
     rw [] >>
     simp [Once val_rel_def] >>
     fs [LIST_REL_EL_EQN, fmap_rel_def] >>
     rw []
     >- (`OPTREL (λa' a. val_rel i a' a) (EL n s.globals) (EL n s'.globals)` by metis_tac [] >>
         pop_assum mp_tac >>
         match_mp_tac OPTREL_MONO >>
         rw [] >>
         Cases_on `s.globals` >>
         Cases_on `s'.globals` >>
         fs [])
     >- (Cases_on `s'.code ' x` >>
         Cases_on `s.code ' x` >>
         rw [] >>
         res_tac >>
         pop_assum mp_tac >>
         ASM_REWRITE_TAC [] >>
         simp []))
 >- (fs [val_rel_rw] >>
     rw [] >>
     simp [state_rel_rw] >>
     fs [LIST_REL_EL_EQN] >>
     rw [] >>
     `i' - s.clock ≤ i - s.clock` by decide_tac >>
     metis_tac [EL_MEM])
 >- (qpat_assum `res_rel i x y` mp_tac >>
     simp [Once val_rel_def] >>
     rw [] >>
     simp [Once val_rel_def] >>
     fs [LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
     *)
 >- (qpat_assum `code_rel f i x y` mp_tac >>
     simp [Once val_rel_def] >>
     rw [] >>
     simp [Once val_rel_def] >>
     rw [] >>
     `i'' < i` by decide_tac >>
     metis_tac []));

val val_rel_mono_list = Q.prove (
`!f i i' vs1 vs2.
  i' ≤ i ∧ LIST_REL (\x y. val_rel f i x y) vs1 vs2
  ⇒
  LIST_REL (\x y. val_rel f i' x y) vs1 vs2`,
 rw [LIST_REL_EL_EQN] >>
 metis_tac [val_rel_mono]);

val exp_rel_empty = Q.prove (
`exp_rel [] []`,
 rw [exp_rel_def, cEval_def, val_rel_rw] >>
 qexists_tac `I` >>
 rw [code_rel_rw, val_rel_rw, cEval_def] >>
 metis_tac [dec_clock_fn_id, val_rel_mono, check_clocks_def]);

 (*
val exp_rel_cons = Q.prove (
`!e es e' es'.
  exp_rel [e] [e'] ∧
  exp_rel es es'
  ⇒
  exp_rel (e::es) (e'::es')`,

 rw [exp_rel_def, code_rel_rw, SKOLEM_THM] >>
 ONCE_REWRITE_TAC [cEval_CONS] >>
 ntac 2 (last_x_assum (qspec_then `i` strip_assume_tac)) >>
 qexists_tac 
 Cases_on `cEval ([e],env,s)` >>
 Cases_on `q` >>


 `res_rel (cEval ([e],env,s)) (cEval ([e'],env',s'))` by metis_tac [] >>
 fs [] >>
 rw [] >>
 Cases_on `cEval ([e'],env',s')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 rfs [] >>
 fs [val_rel_rw] >>
 imp_res_tac cEval_clock >>
 `r.clock ≤ i' ∧ r.clock < i` by (fs [check_clocks_def] >> decide_tac) >>
 `LIST_REL (λa' a. val_rel f r.clock a' a) env env'` by metis_tac [val_rel_mono_list] >>

 `check_clocks f r.clock r r'` by (fs [state_rel_rw, check_clocks_def])
 `res_rel f (cEval (es,env,r)) (cEval (es',env',r'))` by metis_tac [val_rel_mono, val_rel_mono_list] >>
 ect >>
 fs [] >>
 rw [] >>
 simp [val_rel_rw, LIST_REL_EL_EQN] >>
 imp_res_tac cEval_length_imp >>
 Cases_on `a` >>
 fs [] >>
 Cases_on `a'` >>
 fs [] >>
 metis_tac []
 );

val exp_rel_var = Q.prove (
`!x. exp_rel [Var x] [Var x]`,
 rw [exp_rel_def, cEval_def] >>
 ect >>
 fs [] >>
 rw [val_rel_def] >>
 fs [LIST_REL_EL_EQN] >>
 metis_tac []);

val val_rel_bool_to_val = Q.prove (
`!i b v. val_rel i (bool_to_val b) v ⇔ v = bool_to_val b`,
 rw [] >>
 Cases_on `v` >>
 Cases_on `b` >>
 fs [val_rel_def, bool_to_val_def, is_closure_def]);

val exp_rel_if = Q.prove (
`!e1 e2 e3 e1' e2' e3'.
  exp_rel [e1] [e1'] ∧
  exp_rel [e2] [e2'] ∧
  exp_rel [e3] [e3']
  ⇒
  exp_rel [If e1 e2 e3] [If e1' e2' e3']`,
 rw [exp_rel_def, cEval_def] >>
 Cases_on `cEval ([e1],env,s)` >>
 Cases_on `q` >>
 fs [] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 Cases_on `cEval ([e1'],env',s')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 TRY (fs [Once val_rel_def] >> NO_TAC) >>
 `LIST_REL (val_rel i) a a'` by fs [Once val_rel_def, LIST_REL_EL_EQN] >> 
 imp_res_tac cEval_length_imp >>
 Cases_on `a` >>
 fs [] >>
 Cases_on `a'` >>
 fs [] >>
 rw [] >>
 Cases_on `bool_to_val T = h` >>
 fs [] >>
 rw [] >>
 fs [val_rel_bool_to_val] >>
 Cases_on `bool_to_val F = h` >>
 fs [] >>
 rw [] >>
 fs [val_rel_bool_to_val] >>
 rw [] >>
 metis_tac []);

val exp_rel_let = Q.prove (
`!e e' es es'.
  exp_rel es es' ∧
  exp_rel [e] [e']
  ⇒
  exp_rel [Let es e] [Let es' e']`,
 rw [exp_rel_def, cEval_def] >>
 Cases_on `cEval (es,env,s)` >>
 Cases_on `q` >>
 fs [] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 Cases_on `cEval (es',env',s')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 `LIST_REL (val_rel i) (a ++ env) (a' ++ env')` 
                 by (match_mp_tac EVERY2_APPEND_suff >>
                     rw [] >>
                     fs [Once val_rel_def, LIST_REL_EL_EQN]) >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 fs [Once val_rel_def]);

val exp_rel_raise = Q.prove (
`!e e'.
  exp_rel [e] [e']
  ⇒
  exp_rel [Raise e] [Raise e']`,
 rw [exp_rel_def, cEval_def] >>
 Cases_on `cEval ([e],env,s)` >>
 Cases_on `q` >>
 fs [] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 Cases_on `cEval ([e'],env',s')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 fs [Once val_rel_def] >>
 imp_res_tac cEval_length_imp >>
 Cases_on `a` >>
 fs [] >>
 Cases_on `a'` >>
 fs []);

val exp_rel_handle = Q.prove (
`!e1 e2 e1' e2'.
  exp_rel [e1] [e1'] ∧
  exp_rel [e2] [e2']
  ⇒
  exp_rel [Handle e1 e2] [Handle e1' e2']`,
 rw [exp_rel_def, cEval_def] >>
 Cases_on `cEval ([e1],env,s)` >>
 Cases_on `q` >>
 fs [] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 Cases_on `cEval ([e1'],env',s')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 TRY (fs [Once val_rel_def] >> NO_TAC) >>
 `LIST_REL (val_rel i) (c::env) (c'::env')` 
                 by (rw [] >>
                     fs [Once val_rel_def, LIST_REL_EL_EQN]) >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw []);

val state_rel_dec_clock = Q.prove (
`!i s s' n.
  state_rel i s s'
  ⇒
  state_rel i (dec_clock n s) (dec_clock n s')`,
 rw [val_rel_def, LIST_REL_EL_EQN, dec_clock_def]);

val exp_rel_tick = Q.prove (
`!e e'.
  exp_rel [e] [e']
  ⇒
  exp_rel [Tick e] [Tick e']`,
 rw [exp_rel_def, cEval_def] >>
 `state_rel i (dec_clock 1 s) (dec_clock 1 s')` by metis_tac [state_rel_dec_clock] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 ect >>
 fs [val_rel_def] >>
 rw [val_rel_def]);

val exp_rel_call = Q.prove (
`!loc es es'.
  exp_rel es es'
  ⇒
  exp_rel [Call loc es] [Call loc es']`,
 rw [exp_rel_def, cEval_def] >>
 Cases_on `cEval (es,env,s)` >>
 Cases_on `q` >>
 fs [] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 Cases_on `cEval (es',env',s')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 TRY (fs [Once val_rel_def] >> NO_TAC) >>
 `r''.code = r'''.code` by fs [Once val_rel_def] >>
 fs [find_code_def] >>
 ect >>
 fs [] >>
 rw [] >>
 TRY (fs [Once val_rel_def] >> NO_TAC) >>
 (* Need something about the call, probably in the state_rel *)
 cheat);

val exp_rel_cEvalApp = Q.prove (
`!i loc v vs s v' vs' s' r1 r1' s1 s1'.
  val_rel i v v' ∧
  LIST_REL (val_rel i) vs vs' ∧
  state_rel i s s' ∧
  LENGTH vs > 0 ∧
  cEvalApp loc v vs s = (r1,s1) ∧
  cEvalApp loc v' vs' s' = (r1',s1')
  ⇒
  res_rel i r1 r1' ∧
  state_rel i s1 s1'`,
 rpt gen_tac >>
 DISCH_TAC >>
 fs [] >>
 imp_res_tac EVERY2_LENGTH >>
 Cases_on `vs` >>
 Cases_on `vs'` >>
 fs [cEval_def] >>
 rpt BasicProvers.VAR_EQ_TAC >>
 fs [] >>
 qabbrev_tac `vs = h::t` >>
 qabbrev_tac `vs' = h'::t'` >>
 cheat);

val exp_rel_app = Q.prove (
`!loc e e' es es'.
  exp_rel [e] [e'] ∧
  exp_rel es es'
  ⇒
  exp_rel [App loc e es] [App loc e' es']`,
 rw [exp_rel_def, cEval_def] >>
 Cases_on `LENGTH es > 0` >>
 fs [] >>
 Cases_on `cEval (es,env,s)` >>
 Cases_on `q` >>
 fs [] >>
 first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 Cases_on `LENGTH es' > 0` >>
 Cases_on `cEval (es',env',s')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 TRY (fs [Once val_rel_def] >> NO_TAC) >>
 `LENGTH es = LENGTH es'` by cheat >>
 fs [] >>
last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 Cases_on `cEval ([e],env,r'')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 Cases_on `cEval ([e'],env',r''')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 TRY (fs [Once val_rel_def] >> NO_TAC) >>
 imp_res_tac cEval_length_imp >>
 Cases_on `a''` >>
 Cases_on `a'''` >>
 fs [LENGTH_EQ_NUM] >>
 rw [] >>
 `val_rel i h h'` by fs [val_rel_def] >>
 `LIST_REL (val_rel i) a a'` by fs [val_rel_def, LIST_REL_EL_EQN] >>
 metis_tac [exp_rel_cEvalApp]);

 (*
 val val_rel_refl = Q.prove (
`(!i v. val_rel i v v) ∧
 (!i r. ref_v_rel i r r) ∧
 (!i s. state_rel i s s) ∧
 (!i res. res_rel i res res)`,
 rw []


 `(!v. val_rel i v v) ∧
  (!vs. LIST_REL (val_rel i) vs vs)` 

 ho_match_mp_tac clos_val_induction >>
 rw []
 >- rw [val_rel_def]
 >- fs [val_rel_def, LIST_REL_EL_EQN]
 >- rw [val_rel_def]
 >- (simp [val_rel_def, is_closure_def] >>
     rpt gen_tac >>
     DISCH_TAC >>
     rpt gen_tac >>
     DISCH_TAC >>
     fs [cEval_def] >>

val opt_def = Define `
opt (es : clos_exp list) = ARB : clos_exp list`;

val opt_ok = Q.prove (
`!es. exp_rel es (opt es)`,
cheat);



*)
*)

val _ = export_theory ();

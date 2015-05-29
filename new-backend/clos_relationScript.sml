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

val val_rel_def = tDefine "val_rel" `
(val_rel (i:num) (Number n) (Number n') ⇔ n = n') ∧
(val_rel i (Block n' vs) (Block n vs') ⇔ n = n' ∧ LIST_REL (val_rel i) vs vs') ∧
(val_rel i (RefPtr l) (RefPtr l') ⇔ l = l') ∧
(val_rel i v v' ⇔
  if is_closure v ∧ is_closure v' then
    !i'.
      if i' < i then
        (!vs vs' s s' r r' s1 s1'.
          LIST_REL (val_rel i') vs vs' ∧
          state_rel i' s s' ∧
          cEvalApp NONE v vs s = (r,s1) ∧
          cEvalApp NONE v' vs' s' = (r',s1') ∧
          r ≠ Error
          ⇒ 
          res_rel i' r r' ∧
          state_rel i' s1 s1') 
      else
        T
  else 
    F) ∧
(ref_v_rel i (ByteArray ws) (ByteArray ws') ⇔ ws = ws') ∧
(ref_v_rel i (ValueArray vs) (ValueArray vs') ⇔ LIST_REL (val_rel i) vs vs') ∧
(ref_v_rel i _ _ ⇔ F) ∧
(state_rel i s s' ⇔
  LIST_REL (OPTION_REL (val_rel i)) s.globals s'.globals ∧
  fmap_rel (ref_v_rel i) s.refs s'.refs ∧
  s.clock = s'.clock ∧
  s.code = s'.code ∧
  s.output = s'.output ∧
  s.restrict_envs = s'.restrict_envs) ∧
(res_rel i (Result vs) (Result vs') ⇔ LIST_REL (val_rel i) vs vs') ∧
(res_rel i (Exception v) (Exception v') ⇔ val_rel i v v') ∧
(res_rel i TimeOut TimeOut ⇔ T) ∧
(res_rel i _ _ ⇔ F)`
(WF_REL_TAC `inv_image ($< LEX $< LEX $<) 
             (\x. case x of 
                     | INL (i,v,v') => (i:num,0:num,clos_val_size v) 
                     | INR (INL (i,r,r')) => (i,1,0)
                     | INR (INR (INL (i,s,s'))) => (i,2,0)
                     | INR (INR (INR (i,res,res'))) => (i,1,0))` >>
 rw [] >>
 Induct_on `vs` >>
 rw [] >>
 res_tac >>
 simp [clos_val_size_def]);

val val_rel_ind = fetch "-" "val_rel_ind";

val exp_rel_def = Define `
exp_rel es es' ⇔
  !env env' s s' r r' s1 s1' i.
    LIST_REL (val_rel i) env env' ∧
    state_rel i s s' ∧
    cEval (es,env,s) = (r,s1) ∧
    cEval (es',env',s') = (r',s1') ∧
    r ≠ Error
    ⇒
    res_rel i r r' ∧ state_rel i s1 s1'`;

val val_rel_mono = Q.prove (
`(!i v v'. val_rel i v v' ⇒ ∀i'. i' ≤ i ⇒ val_rel i' v v') ∧
 (!i r r'. ref_v_rel i r r' ⇒ ∀i'. i' ≤ i ⇒ ref_v_rel i' r r') ∧
 (!i s s'. state_rel i s s' ⇒ ∀i'. i' ≤ i ⇒ state_rel i' s s') ∧
 (!i res res'. res_rel i res res' ⇒ ∀i'. i' ≤ i ⇒ res_rel i' res res')`,
 ho_match_mp_tac val_rel_ind >>
 rw [] >>
 fs [Once val_rel_def, is_closure_def] 
 >- (rw [val_rel_def] >>
     fs [LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
 >- (Cases_on `v'` >>
     fs [is_closure_def] >>
     rw [Once val_rel_def, is_closure_def] >>
     `i'' < i` by decide_tac >>
     fs [] >>
     metis_tac [])
 >- (Cases_on `v'` >>
     fs [is_closure_def] >>
     rw [Once val_rel_def, is_closure_def] >>
     `i'' < i` by decide_tac >>
     fs [] >>
     metis_tac [])
 >- (fs [LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
 >- cheat
 >- (fs [LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM]));

val exp_rel_empty = Q.prove (
`exp_rel [] []`,
 rw [exp_rel_def, cEval_def, val_rel_def]);

val exp_rel_cons = Q.prove (
`!e es e' es'.
  exp_rel [e] [e'] ∧
  exp_rel es es'
  ⇒
  exp_rel (e::es) (e'::es')`,
 rw [exp_rel_def] >>
 qpat_assum `cEval (e::es,env,s) = y` mp_tac >>
 rw [Once cEval_CONS] >>
 Cases_on `cEval ([e],env,s)` >>
 Cases_on `q` >>
 fs [] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 qpat_assum `cEval (e'::es',env',s') = y` mp_tac >>
 rw [Once cEval_CONS] >>
 Cases_on `cEval ([e'],env',s')` >>
 Cases_on `q` >>
 fs [] >>
 rw [] >>
 last_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
 rpt (pop_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th)))) >>
 fs [] >>
 rw [] >>
 TRY (fs [val_rel_def] >> NO_TAC) >>
 ect >>
 fs [] >>
 rw [] >>
 TRY (fs [val_rel_def] >> NO_TAC) >>
 fs [val_rel_def, LIST_REL_EL_EQN] >>
 imp_res_tac cEval_length_imp >>
 Cases_on `a` >>
 fs [] >>
 Cases_on `a'` >>
 fs []);

val exp_rel_var = Q.prove (
`!x. exp_rel [Var x] [Var x]`,
 rw [exp_rel_def, cEval_def] >>
 ect >>
 fs [] >>
 rw [val_rel_def] >>
 fs [LIST_REL_EL_EQN] >>
 metis_tac []);

exp_rel_if = Q.prove (
`!e1 e2 e3 e1' e2' e3'.
  exp_rel [e1] [e1'] ∧
  exp_rel [e2] [e2'] ∧
  exp_rel [e3] [e3']
  ⇒
  exp_rel [If e1 e2 e3] [If e1' e2' e3']`,
 rw [exp_rel_def, cEval_def] >>
 res_tac

 Cases_on `cEval ([e1],env,s)` >>
 Cases_on `q` >>
 fs []
 rw []

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

val _ = export_theory ();

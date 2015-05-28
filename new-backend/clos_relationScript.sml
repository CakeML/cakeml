open HolKernel Parse boolLib bossLib;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory
open rich_listTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory;

val _ = new_theory "clos_relation";

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
    if 0 < i then
      (!vs vs' s s' r r' s1 s1'.
        LIST_REL (val_rel (i-1)) vs vs' ∧
        state_rel (i-1) s s' ∧
        cEvalApp NONE v vs s = (r,s1) ∧
        cEvalApp NONE v' vs' s' = (r',s1')
        ⇒ 
        res_rel (i-1) r r' ∧
        state_rel (i-1) s1 s1') 
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
    cEval (es,env,s) = (r,s1) ∧
    cEval (es',env',s') = (r',s1')
    ⇒
    res_rel i r r' ∧ state_rel i s s'`;

    (*
val rel_mono = Q.prove (
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
     `0 < i` by decide_tac >>
     fs []
     `i - 1 ≤ i - 1` by decide_tac >>
     metis_tac []
     metis_tac [EL_MEM, DECIDE ``!x:num. x ≤ x``, DECIDE ``!x y z:num. x ≤ y ∧ y ≤ z ⇒ x ≤ z``]

 >- (Cases_on `v'` >>
     fs [is_closure_def] >>
     rw [Once val_rel_def, is_closure_def] >>
     fs [LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
 >- metis_tac [EL_MEM]
 >- cheat
 >- metis_tac [EL_MEM]);


val val_rel_sym = Q.prove (
`(!i v v'. val_rel i v v' ⇒ val_rel i v' v) ∧
 (!i r r'. ref_v_rel i r r' ⇒ ref_v_rel i r' r) ∧
 (!i s s'. state_rel i s s' ⇒ state_rel i s' s) ∧
 (!i res res'. res_rel i res res' ⇒ res_rel i res' res)`,
 ho_match_mp_tac val_rel_ind >>
 rw [] >>
 fs [Once val_rel_def, LIST_REL_EL_EQN, is_closure_def] 
 >- (rw [val_rel_def, LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
 >- (Cases_on `v'` >>
     fs [is_closure_def] >>
     rw [Once val_rel_def, is_closure_def] >>
     fs [LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
 >- (Cases_on `v'` >>
     fs [is_closure_def] >>
     rw [Once val_rel_def, is_closure_def] >>
     fs [LIST_REL_EL_EQN] >>
     metis_tac [EL_MEM])
 >- metis_tac [EL_MEM]
 >- cheat
 >- metis_tac [EL_MEM]);

val exp_rel_sym = Q.prove (
`(!es es'. exp_rel es es' ⇒ exp_rel es' es)`,
 rw [exp_rel_def] >>
 metis_tac [val_rel_sym]);

val opt_def = Define `
opt (es : clos_exp list) = ARB : clos_exp list`;

val opt_ok = Q.prove (
`!es. exp_rel es (opt es)`,
cheat);



*)

val _ = export_theory ();

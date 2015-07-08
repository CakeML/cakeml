open preamble closLangTheory closSemTheory closPropsTheory;

val _ = new_theory "closRelation";

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
  !i'.
    if i' ≤ i then
      let (r, s1) = evaluate_app NONE cl args (s with clock := i') in
      let (r', s1') = evaluate_app NONE cl' args' (s' with clock := i') in
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
                 exec_rel i ([e],env,s) ([e'],env',s')
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
     decide_tac) >>
     cheat); 

val _ = export_theory ();

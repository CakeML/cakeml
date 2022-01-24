(*
  Lemmas used in repl_typesTheory. These lemmas show that a plain
  evaluate run can be replicated in a state with junk refs, extra type
  stamps and unused exception definitions.
*)
open preamble
open evaluateTheory semanticPrimitivesTheory evaluatePropsTheory

val _ = new_theory "evaluate_skip";

Inductive stamp_rel:
  (∀(ft: num |-> num) (fe: num |-> num).
    stamp_rel ft fe NONE NONE)
  ∧
  (∀ft fe n m1 m2.
    FLOOKUP ft m1 = SOME m2 ⇒
    stamp_rel ft fe (SOME (TypeStamp n m1)) (SOME (TypeStamp n m2)))
  ∧
  (∀ft fe m1 m2.
    FLOOKUP fe m1 = SOME m2 ⇒
    stamp_rel ft fe (SOME (ExnStamp m1)) (SOME (ExnStamp m2)))
End

Inductive v_rel:
  (∀fr ft fe l.
     v_rel (fr: num |-> num) (ft: num |-> num) (fe: num |-> num) (Litv l) (Litv l))
  ∧
  (∀fr ft fe t1 t2 xs ys.
     LIST_REL (v_rel fr ft fe) xs ys ∧ stamp_rel ft fe t1 t2 ⇒
     v_rel fr ft fe (Conv t1 xs) (Conv t2 ys))
  ∧
  (∀fr ft fe l1 l2.
     FLOOKUP fr l1 = SOME l2 ⇒
     v_rel (fr: num |-> num) (ft: num |-> num) (fe: num |-> num) (Loc l1) (Loc l2))
End

Definition env_rel_def:
  env_rel fr ft fe env env1 ⇔
    (∀n:(string,string) id. nsLookup env.v n = NONE ⇒ nsLookup env1.v n = NONE) ∧
    ∀n v. nsLookup env.v n = SOME v ⇒
          ∃w. nsLookup env1.v n = SOME w ∧ v_rel fr ft fe v w
End

Definition ref_rel_def:
  (ref_rel f (Refv v) (Refv w) = f v w) ∧
  (ref_rel f (Varray vs) (Varray ws) = LIST_REL f vs ws) ∧
  (ref_rel f x y = (x = y))
End

Definition state_rel_def:
  state_rel l fr ft fe (s:'ffi semanticPrimitives$state) (t:'ffi semanticPrimitives$state) ⇔
    INJ ($' fr) (FDOM fr) (count (LENGTH t.refs)) ∧
    INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
    INJ ($' fe) (FDOM fe) (count t.next_exn_stamp) ∧
    FDOM fr = count (LENGTH s.refs) ∧
    FDOM ft = count s.next_type_stamp ∧
    FDOM fe = count s.next_exn_stamp ∧
    t.clock = s.clock ∧
    s.eval_state = NONE ∧
    t.eval_state = NONE ∧
    t.ffi = s.ffi ∧
    (∀n. n < l ⇒ FLOOKUP fr n = SOME (n:num) ∧ n < LENGTH s.refs) ∧
    FLOOKUP ft bool_type_num = SOME bool_type_num ∧
    (∀n. if n < LENGTH s.refs then
           (∃m. FLOOKUP fr n = SOME m ∧
                m < LENGTH t.refs ∧
                ref_rel (v_rel fr ft fe) (EL n s.refs) (EL m t.refs))
         else FLOOKUP fr n = NONE)
End

Definition res_rel_def[simp]:
  (res_rel f g (Rval e) (Rval e1) ⇔ f e e1) ∧
  (res_rel f g (Rerr e) (Rval e1) ⇔ F) ∧
  (res_rel f g (Rval e) (Rerr e1) ⇔ F) ∧
  (res_rel f g (Rerr (Rraise e)) (Rerr (Rraise e1)) ⇔ g e e1) ∧
  (res_rel f g x y ⇔ x = y)
End

Theorem env_rel_update:
  env_rel fr ft fe env1 env2 ∧ fr ⊑ fr1 ∧ ft ⊑ ft1 ∧ fe ⊑ fe1 ⇒
  env_rel fr1 ft1 fe1 env1 env2
Proof
  cheat
QED

Theorem evaluate_decs_skip:
  ∀s env decs t s1 res fr ft fe env1 l.
    evaluate_decs s env decs = (s1,res) ∧
    state_rel l fr ft fe s t ∧ env_rel fr ft fe env env1 ⇒
    ∃t1 res1 fr1 ft1 fe1.
      fr ⊑ fr1 ∧ ft ⊑ ft1 ∧ fe ⊑ fe1 ∧
      evaluate_decs t env1 decs = (t1,res1) ∧
      state_rel l fr1 ft1 fe1 s1 t1 ∧
      res_rel (λenv' env1'. env_rel fr1 ft1 fe1 (extend_dec_env env' env)
                                                (extend_dec_env env1' env1))
        (v_rel fr1 ft1 fe1) res res1
Proof
  cheat
QED

Theorem evaluate_decs_init:
  evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,Rval env) ⇒
  ∃fr ft fe.
     fr = FUN_FMAP I (count (LENGTH s.refs)) ∧
     ft = FUN_FMAP I (count s.next_type_stamp) ∧
     fe = FUN_FMAP I (count s.next_exn_stamp) ∧
     state_rel (LENGTH s.refs) fr ft fe s s ∧
     env_rel fr ft fe (extend_dec_env env init_env) (extend_dec_env env init_env)
Proof
  cheat
QED

val _ = export_theory();

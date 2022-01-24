(*
  Lemmas used in repl_typesTheory. These lemmas show that a plain
  evaluate run can be replicated in a state with junk refs, extra type
  stamps and unused exception definitions.
*)
open preamble
open evaluateTheory semanticPrimitivesTheory evaluatePropsTheory

val _ = new_theory "evaluate_skip";

Inductive stamp_rel:
  (∀ft fe n m1 m2.
    FLOOKUP ft m1 = SOME m2 ⇒
    stamp_rel ft fe (TypeStamp n m1) (TypeStamp n m2))
  ∧
  (∀ft fe m1 m2.
    FLOOKUP fe m1 = SOME m2 ⇒
    stamp_rel ft fe (ExnStamp m1) (ExnStamp m2))
End

Definition ctor_rel_def:
  ctor_rel ft fe envc1 (envc2: (modN, conN, (num # stamp)) namespace) ⇔
    ∀n. OPTREL ((=) ### (stamp_rel ft fe)) (nsLookup envc1 n) (nsLookup envc2 n)
End

Inductive v_rel:
  (∀fr ft fe l.
     v_rel (fr: num |-> num) (ft: num |-> num) (fe: num |-> num) (Litv l) (Litv l))
  ∧
  (∀fr ft fe t1 t2 xs ys.
     LIST_REL (v_rel fr ft fe) xs ys ∧ OPTREL (stamp_rel ft fe) t1 t2 ⇒
     v_rel fr ft fe (Conv t1 xs) (Conv t2 ys))
  ∧
  (∀fr ft fe xs ys.
     LIST_REL (v_rel fr ft fe) xs ys ⇒
     v_rel fr ft fe (Vectorv xs) (Vectorv ys))
  ∧
  (∀fr ft fe l1 l2.
     FLOOKUP fr l1 = SOME l2 ⇒
     v_rel fr ft fe (Loc l1) (Loc l2))
  ∧
  (∀fr ft fe env1 env2 n e.
     v_rel fr ft fe (Closure env1 n e) (Closure env2 n e))
  ∧
  (∀fr ft fe env1 env2 fns n.
     v_rel fr ft fe (Recclosure env1 fns n) (Recclosure env2 fns n))
  ∧
  (∀fr ft fe env1 env2.
     ctor_rel ft fe env1.c env2.c ∧
     (∀n. nsLookup env1.v n = NONE ⇒ nsLookup env2.v n = NONE) ∧
     (∀n v. nsLookup env1.v n = SOME v ⇒
            ∃w. nsLookup env2.v n = SOME w ∧ v_rel fr ft fe v w) ⇒
     env_rel fr ft fe env1 env2)
End

Theorem env_rel_def =
  “env_rel fr ft fe env1 env2” |> SIMP_CONV std_ss [Once v_rel_cases];

Definition ref_rel_def:
  ref_rel f (Refv v)    (Refv w)    = f v w            ∧
  ref_rel f (Varray vs) (Varray ws) = LIST_REL f vs ws ∧
  ref_rel f (W8array a) (W8array b) = (a = b)          ∧
  ref_rel f _           _           = F
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
    FLOOKUP ft list_type_num = SOME list_type_num ∧
    FLOOKUP fe 0 = SOME 0 ∧ (* Bind      *)
    FLOOKUP fe 1 = SOME 1 ∧ (* Chr       *)
    FLOOKUP fe 2 = SOME 2 ∧ (* Div       *)
    FLOOKUP fe 3 = SOME 3 ∧ (* Subscript *)
    (∀n. if n < LENGTH s.refs then
           (∃m. FLOOKUP fr n = SOME m ∧
                m < LENGTH t.refs ∧
                ref_rel (v_rel fr ft fe) (EL n s.refs) (EL m t.refs))
         else FLOOKUP fr n = NONE)
End

Definition res_rel_def[simp]:
  (res_rel f g (Rval e)          (Rval e1)          ⇔ f e e1) ∧
  (res_rel f g (Rerr (Rraise e)) (Rerr (Rraise e1)) ⇔ g e e1) ∧
  (res_rel f g (Rerr (Rabort e)) (Rerr (Rabort e1)) ⇔ e = e1) ∧
  (res_rel f g x y                                  ⇔ F)
End

Theorem env_rel_update:
  env_rel fr ft fe env1 env2 ∧ fr ⊑ fr1 ∧ ft ⊑ ft1 ∧ fe ⊑ fe1 ⇒
  env_rel fr1 ft1 fe1 env1 env2
Proof
  cheat
QED

(*
Definition env_rel_def:  (* TODO: delete this *)
  env_rel fr ft fe env1 env2 ⇔
     (∀n. nsLookup env1 n = NONE ⇒ nsLookup env2 n = NONE) ∧
     (∀n v. nsLookup env1 n = SOME v ⇒
            ∃w. nsLookup env2 n = SOME w ∧ v_rel fr ft fe v w)
End
*)

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

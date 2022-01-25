(*
  Lemmas used in repl_typesTheory. These lemmas show that a plain
  evaluate run can be replicated in a state with junk refs, extra type
  stamps and unused exception definitions.
*)
open preamble
open evaluateTheory semanticPrimitivesTheory evaluatePropsTheory

val _ = new_theory "evaluate_skip";

val _ = numLib.prefer_num ();

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

Theorem stamp_rel_update:
  ∀ft fe x y.
    stamp_rel ft fe x y ⇒
      ∀ft1 fe1.
        ft ⊑ ft1 ∧ fe ⊑ fe1 ⇒
          stamp_rel ft1 fe1 x y
Proof
  ho_match_mp_tac stamp_rel_ind \\ rw []
  \\ gs [stamp_rel_rules, FLOOKUP_SUBMAP, SF SFY_ss]
QED

Theorem ctor_rel_update:
  ctor_rel ft fe envc1 envc2 ∧
  ft ⊑ ft1 ∧
  fe ⊑ fe1 ⇒
    ctor_rel ft1 fe1 envc1 envc2
Proof
  rw [ctor_rel_def, OPTREL_def]
  \\ first_x_assum (qspec_then ‘n’ strip_assume_tac) \\ gs []
  \\ PairCases_on ‘x0’ \\ PairCases_on ‘y0’ \\ gs [PAIR_MAP]
  \\ irule stamp_rel_update
  \\ gs [SF SFY_ss]
QED

Theorem v_rel_update:
  (∀fr ft fe v w.
    v_rel fr ft fe v w ⇒
      ∀fr1 ft1 fe1.
        fr ⊑ fr1 ∧
        ft ⊑ ft1 ∧
        fe ⊑ fe1 ⇒
          v_rel fr1 ft1 fe1 v w) ∧
  (∀fr ft fe env1 env2.
   env_rel fr ft fe env1 env2 ⇒
     ∀fr1 ft1 fe1.
       fr ⊑ fr1 ∧
       ft ⊑ ft1 ∧
       fe ⊑ fe1 ⇒
         env_rel fr1 ft1 fe1 env1 env2)
Proof
  ho_match_mp_tac v_rel_ind \\ rw []
  \\ FIRST (map irule (CONJUNCTS v_rel_rules)) \\ gs []
  >- (
    irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule OPTREL_MONO
    \\ first_assum (irule_at Any) \\ gs [] \\ rw []
    \\ irule stamp_rel_update
    \\ gs [SF SFY_ss]
  )
  >- (
    irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >- (
    irule FLOOKUP_SUBMAP
    \\ first_assum (irule_at Any) \\ gs [])
  \\ rw []
  >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ gs [])
  \\ irule ctor_rel_update
  \\ gs [SF SFY_ss]
QED

Theorem env_rel_update = CONJUNCT2 v_rel_update;

Theorem fmap_greatest[local]:
  ∀m. ∃y. ∀x. x ∈ FRANGE m ⇒ x < y
Proof
  Induct \\ rw []
  \\ qmatch_goalsub_rename_tac ‘_ = z ∨ _’
  \\ qexists_tac ‘SUC y + z’
  \\ qx_gen_tac ‘k’
  \\ rw [] \\ gs []
  \\ mp_tac (Q.ISPECL [‘x’,‘m: 'a |-> num’, ‘λx. x < y’]
                      (GEN_ALL IN_FRANGE_DOMSUB_suff))
  \\ rw [] \\ gs []
  \\ first_x_assum drule \\ gs []
QED

Theorem state_rel_with_next_exn_stamp:
  state_rel l fr ft fe s t ⇒
    ∃fe1.
      fe ⊑ fe1 ∧
      state_rel l fr ft fe1 (s with next_exn_stamp := s.next_exn_stamp + extra)
                            (t with next_exn_stamp := t.next_exn_stamp + extra)
Proof
  rw [state_rel_def] \\ gs []
  \\ qspec_then ‘fe’ (qx_choose_then ‘j’ assume_tac) fmap_greatest
  \\ qabbrev_tac ‘keys = GENLIST ($+ (SUC s.next_exn_stamp)) extra’
  \\ qabbrev_tac ‘vals = GENLIST ($+ j) extra’
  \\ ‘MAP FST (ZIP (keys, vals)) = keys’
    by gs [Abbr ‘keys’, Abbr ‘vals’, MAP_ZIP]
  \\ ‘ALL_DISTINCT (MAP FST (ZIP (keys, vals))) ∧
      ALL_DISTINCT (MAP FST (REVERSE (ZIP (keys, vals))))’
    by rw [ALL_DISTINCT_GENLIST, MAP_REVERSE, Abbr ‘keys’]
  \\ qexists_tac ‘fe |++ ZIP (keys, vals)’
  \\ conj_tac
  >- (
    rw [SUBMAP_DEF, FDOM_FUPDATE_LIST]
    \\ ‘¬MEM x (MAP FST (ZIP (keys, vals)))’
      by (strip_tac \\ gvs [Abbr ‘keys’, MEM_GENLIST])
    \\ drule_then (qspec_then ‘fe’ mp_tac) FUPDATE_LIST_APPLY_NOT_MEM
    \\ simp [])
  \\ conj_tac
  >- cheat
  \\ conj_tac
  >- (
    simp [FDOM_FUPDATE_LIST]
    \\ cheat
  )
  \\ ‘∀k. k < s.next_exn_stamp ⇒ ¬MEM k keys’
    by (rpt strip_tac \\ gvs [Abbr ‘keys’, MEM_GENLIST])
  \\ drule MEM_ALOOKUP
  \\ disch_then (assume_tac o GSYM)
  \\ simp [flookup_fupdate_list, REVERSE_ZIP]
  \\ ntac 4 CASE_TAC \\ gs [Abbr ‘keys’, Abbr ‘vals’, MEM_ZIP, ADD1, flookup_thm]
  \\ rw []
  \\ cheat (* ref_rel_mono *)
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
  ho_match_mp_tac evaluate_decs_ind \\ rw []
  >- ((* nil *)
    simp [extend_dec_env_def]
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* cons *)
    gvs [evaluate_decs_def, CaseEqs ["prod", "result"], PULL_EXISTS]
    >~ [‘Rerr err’] >- (
        first_x_assum (drule_all_then strip_assume_tac) \\ gs []
        \\ first_assum (irule_at Any)
        \\ Cases_on ‘res1’ \\ gs [res_rel_def])
    \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
    \\ Cases_on ‘res1’ \\ gs [res_rel_def]
    \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
    \\ gs [combine_dec_result_def]
    \\ cheat)
  >~ [‘Dlet locs p e’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result", "bool", "match_result"],
         PULL_EXISTS]
    \\ cheat (* evaluate theorem *))
  >~ [‘Dletrec locs funs’] >- (
    cheat
  )
  >~ [‘Dtype locs tds’] >- (
    cheat
  )
  >~ [‘Dtabbrev locs tvs tn t’] >- (
    cheat
  )
  >~ [‘Denv n’] >- (
    cheat
  )
  >~ [‘Dexn locs cn ts’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result"], PULL_EXISTS]
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ drule_then (qspec_then ‘1’ strip_assume_tac)
                  state_rel_with_next_exn_stamp
    \\ first_assum (irule_at Any) \\ gs []
    \\ cheat (* env_rel_extend_dec_env *)
  )
  >~ [‘Dmod mn decs’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result"], PULL_EXISTS]
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ first_assum (irule_at Any) \\ gs []
    \\ Cases_on ‘res1’ \\ gs [res_rel_def, extend_dec_env_def]
    \\ cheat (* env_rel nsAppend *)
  )
  >~ [‘Dlocal ds1 ds2’] >- (
    gvs [evaluate_decs_def, CaseEqs ["prod", "result"], PULL_EXISTS]
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ first_assum (irule_at Any) \\ gs []
    \\ Cases_on ‘res1’ \\ gs [res_rel_def]
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ first_assum (irule_at Any) \\ gs []
    \\ cheat (* env_rel transitive *)
  )
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

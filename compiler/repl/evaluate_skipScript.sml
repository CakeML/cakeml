(*
  Lemmas used in repl_typesTheory. These lemmas show that a plain
  evaluate run can be replicated in a state with junk refs, extra type
  stamps and unused exception definitions.
*)
Theory evaluate_skip
Ancestors
  evaluate semanticPrimitives evaluateProps namespaceProps
  ml_prog
Libs
  preamble helperLib[qualified]


val _ = numLib.temp_prefer_num ();

Theorem NOT_NIL_CONS:
  xs ≠ [] ⇔ ∃y ys. xs = y::ys
Proof
  Cases_on ‘xs’ \\ gs []
QED

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
    nsAll2 (λid. ($= ### stamp_rel ft fe)) envc1 envc2
End

Inductive v_rel:
  (∀(fr: num |-> num) (ft: num |-> num) (fe: num |-> num) l.
     v_rel fr ft fe (Litv l) (Litv l))
  ∧
  (∀fr ft fe t1 t2 xs ys.
     LIST_REL (v_rel fr ft fe) xs ys ∧ OPTREL (stamp_rel ft fe) t1 t2 ⇒
     v_rel fr ft fe (Conv t1 xs) (Conv t2 ys))
  ∧
  (∀fr ft fe xs ys.
     LIST_REL (v_rel fr ft fe) xs ys ⇒
     v_rel fr ft fe (Vectorv xs) (Vectorv ys))
  ∧
  (∀fr ft fe l1 l2 b.
     FLOOKUP fr l1 = SOME l2 ⇒
     v_rel fr ft fe (Loc b l1) (Loc b l2))
  ∧
  (∀fr ft fe env1 env2 n e.
     env_rel fr ft fe env1 env2 ⇒
       v_rel fr ft fe (Closure env1 n e) (Closure env2 n e))
  ∧
  (∀fr ft fe env1 env2 fns n.
     env_rel fr ft fe env1 env2 ⇒
       v_rel fr ft fe (Recclosure env1 fns n) (Recclosure env2 fns n))
  ∧
  (∀fr ft fe env1 env2 ns.
    env_rel fr ft fe env1 env2 ⇒
     v_rel fr ft fe (Env env1 ns) (Env env2 ns))
  ∧
  (∀fr ft fe env1 env2.
     ctor_rel ft fe env1.c env2.c ∧
     nsAll2 (λid. v_rel fr ft fe) env1.v env2.v ⇒
     env_rel fr ft fe env1 env2)
End

Theorem v_rel_def =
  [“v_rel fr ft fe (Conv opt vs) v”,
   “v_rel fr ft fe (Closure env n x) v”,
   “v_rel fr ft fe (Recclosure env f n) v”,
   “v_rel fr ft fe (Vectorv vs) v”,
   “v_rel fr ft fe (Litv lit) v”,
   “v_rel fr ft fe (Loc b loc) v”,
   “v_rel fr ft fe (Env env ns) v”,
   “v_rel fr ft fe v (Conv opt vs)”,
   “v_rel fr ft fe v (Closure env n x)”,
   “v_rel fr ft fe v (Recclosure env f n)”,
   “v_rel fr ft fe v (Vectorv vs)”,
   “v_rel fr ft fe v (Litv lit)”,
   “v_rel fr ft fe v (Loc b loc)”,
   “v_rel fr ft fe v (Env env ns)”]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem env_rel_def =
  “env_rel fr ft fe env1 env2” |> SIMP_CONV std_ss [Once v_rel_cases];

Definition ref_rel_def:
  ref_rel f (Refv v)      (Refv w)      = f v w                 ∧
  ref_rel f (Varray vs)   (Varray ws)   = LIST_REL f vs ws      ∧
  ref_rel f (W8array a)   (W8array b)   = (a = b)               ∧
  ref_rel f (Thunk m1 v1) (Thunk m2 v2) = ((m1 = m2) ∧ f v1 v2) ∧
  ref_rel f _           _               = F
End

Theorem ref_rel_mono:
  ref_rel P v w ∧
  (∀v w. P v w ⇒ Q v w) ⇒
    ref_rel Q v w
Proof
  Cases_on ‘v’ \\ Cases_on ‘w’ \\ gs [ref_rel_def] \\ rw []
  \\ irule LIST_REL_mono
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem ref_rel_refl:
  (∀x. P x x) ⇒
  ref_rel P x x
Proof
  Cases_on ‘x’ \\ rw [ref_rel_def]
  \\ Induct_on ‘l’ \\ gs []
QED

Definition state_rel_def:
  state_rel l fr ft fe (s:'ffi semanticPrimitives$state)
                       (t:'ffi semanticPrimitives$state) ⇔
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

Theorem res_rel_abort[simp]:
  res_rel R Q (Rerr (Rabort x)) r ⇔ r = Rerr (Rabort x)
Proof
  Cases_on ‘r’ \\ gs []
  \\ Cases_on ‘e’ \\ gs []
  \\ rw [EQ_SYM_EQ]
QED

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
  rw [ctor_rel_def]
  \\ irule nsAll2_mono
  \\ first_assum (irule_at Any)
  \\ simp [FORALL_PROD] \\ rw []
  \\ irule stamp_rel_update
  \\ gs [SF SFY_ss]
QED

Theorem v_rel_update_lemma:
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
  >- ((* Conv *)
    irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule OPTREL_MONO
    \\ first_assum (irule_at Any) \\ gs [] \\ rw []
    \\ irule stamp_rel_update
    \\ gs [SF SFY_ss])
  >- ((* Vectorv *)
    irule_at Any LIST_REL_mono
    \\ first_assum (irule_at Any) \\ gs [])
  >- ((* Loc *)
    irule FLOOKUP_SUBMAP
    \\ first_assum (irule_at Any) \\ gs [])
  \\ irule_at Any nsAll2_mono
  \\ first_assum (irule_at Any)
  \\ simp [FORALL_PROD]
  \\ irule ctor_rel_update
  \\ gs [SF SFY_ss]
QED

Theorem env_rel_update = CONJUNCT2 v_rel_update_lemma;

Theorem v_rel_update = CONJUNCT1 v_rel_update_lemma;

Theorem ctor_rel_nsAppend:
  ctor_rel ft fe x1.c x2.c ∧
  ctor_rel ft fe y1.c y2.c ⇒
    ctor_rel ft fe (nsAppend x1.c y1.c) (nsAppend x2.c y2.c)
Proof
  rw [ctor_rel_def]
  \\ irule nsAll2_nsAppend \\ gs []
QED

Theorem env_rel_nsAppend:
 env_rel fr ft fe x1 x2 ∧
 env_rel fr ft fe y1 y2 ⇒
   env_rel fr ft fe <|v:= nsAppend x1.v y1.v; c:= nsAppend x1.c y1.c|>
                    <|v:= nsAppend x2.v y2.v; c:= nsAppend x2.c y2.c|>
Proof
  simp [env_rel_def] \\ strip_tac
  \\ irule_at Any ctor_rel_nsAppend \\ gs []
  \\ irule nsAll2_nsAppend \\ gs []
QED

Theorem env_rel_extend_dec_env:
  env_rel fr ft fe env1 env2 ∧
  env_rel fr ft fe env1' env2' ⇒
    env_rel fr ft fe (extend_dec_env env1' env1)
                     (extend_dec_env env2' env2)
Proof
  rw [extend_dec_env_def]
  \\ irule env_rel_nsAppend
  \\ gs []
QED

Theorem env_rel_nsBind:
  env_rel fr ft fe env1 env2 ∧
  v_rel fr ft fe v w ⇒
    env_rel fr ft fe (env1 with v := nsBind n v env1.v)
                     (env2 with v := nsBind n w env2.v)
Proof
  rw [env_rel_def]
  \\ irule nsAll2_nsBind
  \\ gs []
QED

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

(* --------------------------------------------------------------------------
 *
 * -------------------------------------------------------------------------- *)

Definition match_res_rel_def[simp]:
  (match_res_rel R (Match env1) (Match env2) ⇔ R env1 env2) ∧
  (match_res_rel R No_match No_match ⇔ T) ∧
  (match_res_rel R Match_type_error Match_type_error ⇔ T) ∧
  (match_res_rel R _ _ ⇔ F)
End

Theorem pmatch_update:
  (∀envC s p v ws res.
    pmatch envC s p v ws = res ⇒
      ∀envC' s' v' ws' res' ns ms.
        ctor_rel ft fe envC envC' ∧
        v_rel fr ft fe v v' ∧
        INJ ($' ft) (FDOM ft) ns ∧
        INJ ($' fe) (FDOM fe) ms ∧
        LIST_REL (λ(n,v) (m,w). n = m ∧ v_rel fr ft fe v w) ws ws' ∧
        pmatch envC' s' p v' ws' = res' ∧
        (∀n. if n < LENGTH s then
             ∃m. FLOOKUP fr n = SOME m ∧ m < LENGTH s' ∧
                 ref_rel (v_rel fr ft fe) (EL n s) (EL m s')
           else FLOOKUP fr n = NONE) ⇒
          match_res_rel (λenv env'.
            LIST_REL (λ(n,v) (m,w). n = m ∧ v_rel fr ft fe v w)
                     env env') res res') ∧
  (∀envC s ps vs ws res.
    pmatch_list envC s ps vs ws = res ⇒
      ∀envC' s' vs' ws' res' ns ms.
        INJ ($' ft) (FDOM ft) ns ∧
        INJ ($' fe) (FDOM fe) ms ∧
        ctor_rel ft fe envC envC' ∧
        LIST_REL (v_rel fr ft fe) vs vs' ∧
        LIST_REL (λ(n,v) (m,w). n = m ∧ v_rel fr ft fe v w) ws ws' ∧
        pmatch_list envC' s' ps vs' ws' = res' ∧
        (∀n. if n < LENGTH s then
             ∃m. FLOOKUP fr n = SOME m ∧ m < LENGTH s' ∧
                 ref_rel (v_rel fr ft fe) (EL n s) (EL m s')
           else FLOOKUP fr n = NONE) ⇒
          match_res_rel (λenv env'.
            LIST_REL (λ(n,v) (m,w). n = m ∧ v_rel fr ft fe v w)
                     env env') res res')
Proof[exclude_simps = option.OPTREL_NONE]
  ho_match_mp_tac pmatch_ind \\ rw [] \\ gvs [pmatch_def, v_rel_def, SF SFY_ss]
  >- (rw [] \\ gs [])
  >- (
    gvs [CaseEqs ["bool", "option", "prod"], v_rel_def, pmatch_def]
    \\ rename1 ‘pmatch _ _ _ (Conv tt _)’
    \\ Cases_on ‘tt’ \\ gvs [pmatch_def, CaseEqs ["prod", "option", "bool"]]
    \\ CASE_TAC \\ gs []
    >- (
      gs [ctor_rel_def]
      \\ drule_all_then assume_tac nsAll2_nsLookup_none \\ gs [])
    \\ CASE_TAC \\ gs [ctor_rel_def]
    \\ drule_all_then strip_assume_tac nsAll2_nsLookup1 \\ gs []
    \\ PairCases_on ‘v2’ \\ gvs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gs []
    \\ gvs [stamp_rel_cases, same_ctor_def, same_type_def]
    \\ rw [] \\ gs []
    \\ TRY (first_x_assum irule \\ gs [SF SFY_ss])
    \\ fs [INJ_DEF] \\ fs [flookup_thm] \\ gs [])
  >- (
    rename1 ‘pmatch _ _ _ (Conv tt _)’
    \\ Cases_on ‘tt’ \\ gvs [pmatch_def, CaseEqs ["prod", "option", "bool"]]
    \\ rw [] \\ gs []
    \\ imp_res_tac LIST_REL_LENGTH \\ gs []
    \\ first_x_assum irule
    \\ gs [SF SFY_ss])
  >- (
    CASE_TAC \\ gs [store_lookup_def] \\ gvs []
    >- (
      first_x_assum (qspec_then ‘lnum’ assume_tac) \\ gs [])
    \\ first_assum (qspec_then ‘lnum’ mp_tac)
    \\ IF_CASES_TAC \\ simp_tac std_ss [] \\ rw [] \\ gs []
    \\ rpt CASE_TAC \\ gs [ref_rel_def]
    \\ first_x_assum irule \\ gs [SF SFY_ss])
  >- (
    rename1 ‘pmatch _ _ _ (Conv tt _)’
    \\ Cases_on ‘tt’ \\ gvs [pmatch_def, CaseEqs ["prod", "option", "bool"]])
  >- (
    rename1 ‘pmatch _ _ _ (Conv tt _)’
    \\ Cases_on ‘tt’ \\ gvs [pmatch_def, CaseEqs ["prod", "option", "bool"]])
  >- (
    Cases_on ‘pmatch envC s p v ws’ \\ gs []
    \\ rpt (first_x_assum drule_all \\ rw [] \\ gs [])
    \\ rpt (CASE_TAC \\ gs [])
    \\ first_x_assum irule \\ gs [SF SFY_ss])
QED

local
  val ind_thm =
    full_evaluate_ind
    |> Q.SPECL [
      ‘λs env xs. ∀res s1 l fr ft fe t env1.
        evaluate s env xs = (s1, res) ∧
        state_rel l fr ft fe s t ∧
        env_rel fr ft fe env env1 ⇒
          ∃fr1 ft1 fe1 t1 res1.
            fr ⊑ fr1 ∧ ft ⊑ ft1 ∧ fe ⊑ fe1 ∧
            state_rel l fr1 ft1 fe1 s1 t1 ∧
            evaluate t env1 xs = (t1, res1) ∧
            res_rel (LIST_REL (v_rel fr1 ft1 fe1))
                    (v_rel fr1 ft1 fe1) res res1’,
      ‘λs env v ps errv. ∀res s1 l fr ft fe t env1 w errw.
        evaluate_match s env v ps errv = (s1, res) ∧
        state_rel l fr ft fe s t ∧
        env_rel fr ft fe env env1 ∧
        v_rel fr ft fe v w ∧
        v_rel fr ft fe errv errw ⇒
          ∃fr1 ft1 fe1 t1 res1.
            fr ⊑ fr1 ∧ ft ⊑ ft1 ∧ fe ⊑ fe1 ∧
            state_rel l fr1 ft1 fe1 s1 t1 ∧
            evaluate_match t env1 w ps errw = (t1, res1) ∧
            res_rel (LIST_REL (v_rel fr1 ft1 fe1))
                    (v_rel fr1 ft1 fe1) res res1’,
      ‘λs env ds. ∀res s1 l fr ft fe t env1.
        evaluate_decs s env ds = (s1, res) ∧
        state_rel l fr ft fe s t ∧
        env_rel fr ft fe env env1 ⇒
          ∃fr1 ft1 fe1 t1 res1.
            fr ⊑ fr1 ∧ ft ⊑ ft1 ∧ fe ⊑ fe1 ∧
            state_rel l fr1 ft1 fe1 s1 t1 ∧
            evaluate_decs t env1 ds = (t1, res1) ∧
            res_rel (λenv' env1'.
                       env_rel fr1 ft1 fe1 env' env1') (*
                       env_rel fr1 ft1 fe1 (extend_dec_env env' env)
                                           (extend_dec_env env1' env1)) *)
                    (v_rel fr1 ft1 fe1) res res1’]
    |> CONV_RULE (DEPTH_CONV BETA_CONV);
  val ind_goals =
    ind_thm |> concl |> dest_imp |> fst
            |> helperLib.list_dest dest_conj
in
  fun get_goal s =
    first (can (find_term (can (match_term (Term [QUOTE s]))))) ind_goals
    |> helperLib.list_dest dest_forall
    |> last
  fun evaluate_update () = ind_thm |> concl |> rand
  fun the_ind_thm () = ind_thm
end

Theorem evaluate_update_Nil:
  ^(get_goal "[]")
Proof
  rw [evaluate_def]
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_update_Cons:
  ^(get_goal "_::_::_")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["result", "prod"], PULL_EXISTS]
  >~ [‘evaluate _ _ [_] = (_, Rerr err)’] >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ Cases_on ‘res1’ \\ gs []
    \\ rename1 ‘_ _ (Rerr err) (Rerr err1)’
    \\ Cases_on ‘err’ \\ Cases_on ‘err1’ \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ Cases_on ‘res1’ \\ gs []
  \\ drule_all_then assume_tac env_rel_update
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ Cases_on ‘res1’ \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [SUBMAP_TRANS, SF SFY_ss]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ irule v_rel_update
  \\ gs [SUBMAP_TRANS, SF SFY_ss]
  \\ first_assum (irule_at (Pos last))
QED

Theorem evaluate_update_Lit:
  ^(get_goal "Lit l")
Proof
  rw [evaluate_def] \\ gs []
  \\ first_assum (irule_at Any)
  \\ simp [v_rel_rules]
QED

Theorem evaluate_update_Raise:
  ^(get_goal "Raise e")
Proof
  rw [evaluate_def] \\ gs []
  \\ gvs [CaseEqs ["result", "prod"], PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ Cases_on ‘res1’ \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
QED

Theorem can_pmatch_all_thm:
  ∀ps envc1 s v envc2 t w ms ns.
    ctor_rel ft fe envc1 envc2 ∧
    INJ ($' ft) (FDOM ft) ns ∧
    INJ ($' fe) (FDOM fe) ms ∧
    (∀n. if n < LENGTH s then
           ∃m. FLOOKUP fr n = SOME m ∧ m < LENGTH t ∧
           ref_rel (v_rel fr ft fe) (EL n s) (EL m t)
         else FLOOKUP fr n = NONE) ∧
    v_rel fr ft fe v w ⇒
    (can_pmatch_all envc1 s ps v ⇔ can_pmatch_all envc2 t ps w)
Proof
  Induct \\ rw [can_pmatch_all_def]
  \\ first_x_assum drule_all \\ rw []
  \\ rw [EQ_IMP_THM] \\ gs []
  >- (
    ‘∃res. pmatch envc1 s h v [] = res’ by gs []
    \\ drule (CONJUNCT1 pmatch_update)
    \\ rpt (disch_then drule) \\ gs []
    \\ rpt (disch_then drule) \\ gs [] \\ rw []
    \\ Cases_on ‘pmatch envc1 s h v []’ \\ Cases_on ‘pmatch envc2 t h w []’
    \\ gs [])
  >- (
    strip_tac
    \\ drule (CONJUNCT1 pmatch_update)
    \\ rpt (disch_then drule) \\ gs []
    \\ qexists_tac ‘t’ \\ gs []
    \\ Cases_on ‘pmatch envc1 s h v []’ \\ Cases_on ‘pmatch envc2 t h w []’
    \\ gs [])
QED

Theorem evaluate_update_Handle:
  ^(get_goal "Handle e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "error_result", "bool"], PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  >~ [‘evaluate _ _ [_] = (_, Rerr (Rabort _))’] >- (
    first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘evaluate _ _ [_] = (_, Rval _)’] >- (
    first_assum (irule_at Any) \\ gs [])
  \\ rename1 ‘res_rel _ _ (Rerr _) (Rerr err)’
  \\ Cases_on ‘err’ \\ gs []
  \\ drule_all_then assume_tac env_rel_update
  >- (
    first_x_assum (drule_all_then strip_assume_tac) \\ gs []
    \\ first_assum (irule_at (Pat ‘state_rel’)) \\ gs []
    \\ first_assum (irule_at Any)
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
    \\ gs [state_rel_def, env_rel_def]
    \\ drule can_pmatch_all_thm \\ gs []
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then ‘MAP FST pes’ assume_tac)
    \\ gs [SF SFY_ss])
  \\ first_assum (irule_at (Pat ‘state_rel’)) \\ gs []
  \\ gs [state_rel_def, env_rel_def]
  \\ drule can_pmatch_all_thm \\ gs []
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then ‘MAP FST pes’ assume_tac)
  \\ gs [SF SFY_ss]
QED

Theorem do_con_check_update:
  env_rel fr ft fe env env1 ⇒
    do_con_check env.c cn n = do_con_check env1.c cn n
Proof
  strip_tac \\ eq_tac \\ gs [env_rel_def, ctor_rel_def]
  \\ rw [do_con_check_def]
  \\ CASE_TAC \\ gs []
  \\ Cases_on ‘nsLookup env.c x’ \\ gs []
  \\ Cases_on ‘nsLookup env1.c x’ \\ gs []
  \\ rename1 ‘pair_CASE z’
  \\ PairCases_on ‘z’ \\ gvs []
  \\ imp_res_tac nsAll2_nsLookup_none
  \\ imp_res_tac nsAll2_nsLookup1 \\ imp_res_tac nsAll2_nsLookup2 \\ gvs []
  \\ (PairCases_on ‘v1’ ORELSE PairCases_on ‘v2’) \\ gs []
QED

Theorem evaluate_update_Con:
  ^(get_goal "Con cn es")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option"], PULL_EXISTS]
  \\ drule_then assume_tac do_con_check_update \\ gs []
  >~ [‘¬do_con_check _ _ _’] >- (
    first_assum (irule_at Any) \\ gs [])
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ Cases_on ‘res1’ \\ gs []
  \\ gs [env_rel_def, ctor_rel_def, build_conv_def]
  \\ gvs [CaseEqs ["prod", "option"]]
  \\ first_assum (irule_at Any) \\ gs [v_rel_rules]
  \\ rename1 ‘nsLookup env1.c id’
  >- (
    dxrule_all nsAll2_nsLookup_none \\ rw []
    \\ dxrule_all nsAll2_nsLookup_none \\ rw []
    \\ gs [])
  \\ gs [PULL_EXISTS]
  \\ imp_res_tac nsAll2_nsLookup1 \\ gs[ ]
  \\ PairCases_on ‘v2’ \\ gs []
  \\ simp [v_rel_def]
  \\ irule stamp_rel_update
  \\ gs [SF SFY_ss]
QED

Theorem evaluate_update_Var:
  ^(get_goal "ast$Var n")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  \\ first_assum (irule_at Any) \\ gs [] \\ dsimp []
  \\ gs [env_rel_def, ctor_rel_def]
  >- (
    dxrule_all nsAll2_nsLookup_none
    \\ dxrule_all nsAll2_nsLookup_none \\ rw []
    \\ gs [])
  \\ imp_res_tac nsAll2_nsLookup1 \\ gs[ ]
QED

Theorem evaluate_update_Fun:
  ^(get_goal "ast$Fun n e")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option"]]
  \\ first_assum (irule_at Any) \\ gs []
  \\ simp [v_rel_def]
QED

Theorem evaluate_update_Eval:
  op = Eval ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [AllCaseEqs(), evaluateTheory.do_eval_res_def]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ first_assum (irule_at Any)
  \\ Cases_on ‘res1’ \\ gs []
  \\ dsimp []
  \\ gs [state_rel_def, do_eval_def]
QED

Theorem state_rel_store_lookup:
  state_rel l fr ft fe s t ∧
  FLOOKUP fr n = SOME m ⇒
    OPTREL (ref_rel (v_rel fr ft fe))
           (store_lookup n s.refs)
           (store_lookup m t.refs)
Proof
  rw [OPTREL_def, store_lookup_def, state_rel_def]
  \\ first_x_assum (qspec_then ‘n’ assume_tac) \\ gs []
QED

Theorem state_rel_store_assign:
  state_rel l fr ft fe s t ∧
  FLOOKUP fr n = SOME m ∧
  ref_rel (v_rel fr ft fe) v w ⇒
    OPTREL
      (λr1 r2. state_rel l fr ft fe (s with refs := r1) (t with refs := r2))
      (store_assign n v s.refs)
      (store_assign m w t.refs)
Proof
  rw [OPTREL_def] \\ gvs []
  \\ ‘n < LENGTH s.refs ∧ m < LENGTH t.refs’ by (
    gvs [state_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
    \\ qpat_x_assum ‘FLOOKUP fr n = _’ mp_tac
    \\ rw [INJ_DEF, flookup_thm]
    \\ first_x_assum drule \\ rw [])
  \\ Cases_on ‘store_assign n v s.refs’ \\ gvs []
  >- (
    gvs [store_assign_def, NOT_LESS]
    \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [ref_rel_def]
    \\ Cases_on ‘EL n s.refs’ \\ Cases_on ‘EL m t.refs’
    \\ gvs [store_v_same_type_def, state_rel_def]
    \\ first_x_assum $ qspec_then `n` assume_tac \\ gvs [ref_rel_def])
  \\ gvs [store_assign_def]
  \\ Cases_on ‘v’ \\ Cases_on ‘w’ \\ gvs [ref_rel_def]
  \\ (
    Cases_on ‘EL n s.refs’ \\ gvs [Once store_v_same_type_def]
    \\ gvs [state_rel_def, EL_LUPDATE] \\ rw []
    >- (
      first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs []
      \\ Cases_on ‘EL m t.refs’ \\ gvs [ref_rel_def, store_v_same_type_def])
    >- simp [ref_rel_def]
    >- (
      first_x_assum $ qspec_then ‘n'’ assume_tac \\ gvs []
      \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ qpat_x_assum ‘FLOOKUP fr n = SOME m’ mp_tac
      \\ qpat_x_assum ‘FLOOKUP fr n' = SOME m'’ mp_tac
      \\ rw [INJ_DEF, FLOOKUP_DEF] \\ gvs [])
    >- (
      gvs [NOT_LESS]
      \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ rw [INJ_DEF, FLOOKUP_DEF] \\ gvs []))
QED

Theorem v_rel_v_to_list:
  ∀x1 res1 x2 res2.
    v_rel fr ft fe x1 x2 ∧
    v_to_list x1 = res1 ∧
    v_to_list x2 = res2 ∧
    INJ ($' ft) (FDOM ft) (count ns) ∧
    FLOOKUP ft list_type_num = SOME list_type_num ∧
    list_type_num < ns ⇒
      OPTREL (LIST_REL (v_rel fr ft fe)) res1 res2
Proof
  ho_match_mp_tac v_to_list_ind \\ gs []
  \\ rw [] \\ gvs [v_rel_def, v_to_list_def]
  \\ gvs [OPTREL_def, stamp_rel_cases, v_to_list_def, flookup_thm]
  >- (
    Cases_on ‘m1 = list_type_num’ \\ gs []
    \\ rpt strip_tac \\ gvs []
    \\ gs [INJ_DEF])
  \\ gs [CaseEq "option"]
  \\ Cases_on ‘m1 = list_type_num ∧ n = «::»’ \\ gvs []
  >- (
    first_x_assum (drule_all_then assume_tac)
    \\ gs [])
  \\ Cases_on ‘m1 = list_type_num’ \\ gs [] \\ rw []
  \\ gs [INJ_DEF]
QED

Theorem v_rel_vs_to_string:
  ∀x1 res1 x2 res2.
    LIST_REL (v_rel fr ft fe) x1 x2 ∧
    vs_to_string x1 = res1 ∧
    vs_to_string x2 = res2 ∧
    INJ ($' ft) (FDOM ft) (count ns) ∧
    FLOOKUP ft list_type_num = SOME list_type_num ∧
    list_type_num < ns ⇒
      res1 = res2
Proof
  ho_match_mp_tac vs_to_string_ind \\ gs []
  \\ rw [] \\ gvs [v_rel_def, vs_to_string_def]
  \\ gs [CaseEq "option"]
  \\ first_x_assum (drule_all_then assume_tac)
  \\ gs [option_nchotomy]
QED

Theorem v_rel_list_to_v:
  ∀x1 xs1 x2 xs2.
    v_to_list x1 = SOME xs1 ∧
    v_to_list x2 = SOME xs2 ∧
    LIST_REL (v_rel fr ft fe) xs1 xs2 ∧
    FLOOKUP ft list_type_num = SOME list_type_num ⇒
      v_rel fr ft fe (list_to_v xs1) (list_to_v xs2)
Proof
  ho_match_mp_tac v_to_list_ind
  \\ rw [] \\ gvs [v_to_list_def, list_to_v_def, v_rel_def, stamp_rel_cases,
                   CaseEq "option"]
  \\ Cases_on ‘x2’ \\ gs [v_to_list_def]
  \\ rename1 ‘Conv opt ws’ \\ Cases_on ‘opt’ \\ gs [v_to_list_def]
  \\ rename1 ‘Conv (SOME opt) ws’ \\ Cases_on ‘ws’ \\ gs [v_to_list_def]
  \\ rename1 ‘Conv (SOME opt) (w::ws)’ \\ Cases_on ‘ws’ \\ gs [v_to_list_def]
  \\ Cases_on ‘t’ \\ gvs [v_to_list_def, CaseEq "option"]
  \\ first_assum (irule_at Any) \\ gs [SF SFY_ss]
QED

Theorem v_rel_v_to_char_list:
  ∀x1 res1 x2 res2.
    v_rel fr ft fe x1 x2 ∧
    v_to_char_list x1 = res1 ∧
    v_to_char_list x2 = res2 ∧
    INJ ($' ft) (FDOM ft) (count ns) ∧
    FLOOKUP ft list_type_num = SOME list_type_num ∧
    list_type_num < ns ⇒
      res1 = res2
Proof
  ho_match_mp_tac v_to_char_list_ind \\ gs []
  \\ rw [] \\ gvs [v_rel_def, v_to_char_list_def]
  \\ TRY (gs[v_rel_cases] \\ NO_TAC)
  \\ gvs [CaseEq "bool", OPTREL_def, stamp_rel_cases]
  \\ gs [v_to_char_list_def]
  >- (
    Cases_on ‘m1 = list_type_num’ \\ gs []
    \\ rpt strip_tac \\ gvs []
    \\ gs [INJ_DEF, flookup_thm])
  \\ gs [CaseEq "option"]
  \\ Cases_on ‘m1 = list_type_num ∧ n = «::»’ \\ gvs []
  >- (
    first_x_assum (drule_all_then assume_tac)
    \\ simp[AllCaseEqs()]
    \\ metis_tac[option_nchotomy])
  \\ Cases_on ‘m1 = list_type_num’ \\ gs [] \\ rw []
  \\ gs [INJ_DEF, flookup_thm]
QED

Theorem v_to_list_list_to_v:
  ∀xs.
    v_to_list (list_to_v xs) = SOME xs
Proof
  Induct \\ rw [list_to_v_def, v_to_list_def]
QED

Theorem INJ_EQ_11_alt:
  ∀f s x y. INJ f s t ∧ x ∈ s ∧ y ∈ s ⇒ (f x = f y ⇔ x = y)
Proof
  rw[INJ_DEF]>>
  metis_tac[]
QED

Theorem v_rel_do_eq:
  (∀x1 y1 x2 y2.
     v_rel fr ft fe x1 x2 ∧
     v_rel fr ft fe y1 y2 ∧
     FLOOKUP ft bool_type_num = SOME bool_type_num ∧
     INJ ($' fr) (FDOM fr) (count rs) ∧
     INJ ($' ft) (FDOM ft) (count ns) ∧
     INJ ($' fe) (FDOM fe) (count ms) ⇒
     do_eq x1 y1 = do_eq x2 y2) ∧
  (∀x1 y1 x2 y2.
     LIST_REL (v_rel fr ft fe) x1 x2 ∧
     LIST_REL (v_rel fr ft fe) y1 y2 ∧
     FLOOKUP ft bool_type_num = SOME bool_type_num ∧
     INJ ($' fr) (FDOM fr) (count rs) ∧
     INJ ($' ft) (FDOM ft) (count ns) ∧
     INJ ($' fe) (FDOM fe) (count ms) ⇒
     do_eq_list x1 y1 = do_eq_list x2 y2)
Proof
  ho_match_mp_tac do_eq_ind \\ rw []
  \\ gvs [v_rel_def, do_eq_def, Boolv_def]
  \\ gvs [OPTREL_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ gs []
  \\ rw [EQ_IMP_THM] \\ gs []
  \\ gvs [ctor_same_type_def, same_type_def, stamp_rel_cases, flookup_thm]
  \\ rpt CASE_TAC \\ gvs[]
  \\ metis_tac[INJ_DEF]
QED

Theorem v_rel_IMP_check_type_eq[local]:
  state_rel l fr ft fe s t ⇒
  v_rel fr ft fe v1 w1 ⇒ (check_type ty v1 = check_type ty w1)
Proof
  simp [Once v_rel_cases] \\ rw [] \\ simp [check_type_def]
  \\ Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ gvs [check_type_def,Boolv_def]
  \\ eq_tac \\ rw [] \\ gvs [OPTREL_def,stamp_rel_cases]
  \\ gvs [state_rel_def]
  \\ rpt $ pop_assum mp_tac
  \\ once_rewrite_tac [INJ_DEF]
  \\ rewrite_tac [FLOOKUP_DEF,AllCaseEqs(),NOT_NONE_SOME,SOME_11]
  \\ metis_tac []
QED

Theorem v_rel_IMP_dest_Litv_eq[local]:
  v_rel fr ft fe v1 w1 ⇒ dest_Litv v1 = dest_Litv w1
Proof
  simp [Once v_rel_cases] \\ rw [] \\ simp [dest_Litv_def]
QED

Theorem do_test_thm[local]:
  do_test test ty v1 v2 = res ∧
  v_rel fr ft fe v1 w1 ∧
  v_rel fr ft fe v2 w2 ∧
  state_rel l fr ft fe s t ⇒
  do_test test ty w1 w2 = res
Proof
  rewrite_tac [oneline do_test_def,AllCaseEqs()]
  \\ strip_tac
  \\ imp_res_tac v_rel_IMP_check_type_eq \\ rw []
  \\ gvs []
  >-
   (gvs [check_type_def,the_Litv_Float64_def]
   \\ fs [Once v_rel_cases])
  >-
   (Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ gvs [check_type_def]
    \\ fs [do_eq_def,Boolv_def] \\ EVAL_TAC
    \\ rpt $ pop_assum mp_tac
    \\ once_rewrite_tac [v_rel_cases]
    \\ gvs [stamp_rel_cases])
  \\ imp_res_tac v_rel_IMP_dest_Litv_eq \\ fs []
QED

Theorem do_arith_update:
  state_rel l fr ft fe s t ∧
  LIST_REL (v_rel fr ft fe) vs ws ∧
  EVERY (check_type ty) vs
  ⇒
  OPTREL ((v_rel fr ft fe) +++ (v_rel fr ft fe))
    (do_arith a ty vs) (do_arith a ty ws)
Proof
  rw[LIST_REL_EL_EQN, EVERY_EL]
  \\ drule v_rel_IMP_check_type_eq
  \\ strip_tac
  \\ rw[OPTREL_def]
  \\ Cases_on ‘a’ \\ Cases_on ‘ty’ using semanticPrimitivesPropsTheory.prim_type_cases
  \\ rw[do_arith_def]
  \\ gvs[check_type_def, CaseEq"list", PULL_EXISTS]
  \\ simp[Once v_rel_cases]
  \\ Cases_on ‘vs’ \\ Cases_on ‘ws’ \\ gvs[PULL_EXISTS]
  \\ rpt (
    qmatch_assum_rename_tac‘LENGTH vs = LENGTH ws’
    \\ Cases_on ‘vs’ \\ Cases_on ‘ws’ \\ gvs[PULL_EXISTS])
  \\ gvs[NUMERAL_LESS_THM, SF DNF_ss, Boolv_def]
  \\ gvs[Once v_rel_cases]
  \\ gvs[Once v_rel_cases]
  \\ rw[]
  \\ TRY (
    rw[Once v_rel_cases, div_exn_v_def, stamp_rel_cases, div_stamp_def]
    \\ gvs[state_rel_def] \\ NO_TAC )
  \\ gvs[Once v_rel_cases]
  \\ gvs [optionTheory.OPTREL_SOME]
  \\ gvs [stamp_rel_cases]
  \\ gvs [state_rel_def]
QED

Theorem do_app_update:
  do_app (s.refs,s.ffi) op vs = res ∧
  state_rel l fr ft fe s t ∧
  LIST_REL (v_rel fr ft fe) vs ws ∧
  op ≠ Opapp ∧
  op ≠ Eval ⇒
    ∃fr1 ft1 fe1 res1.
      do_app (t.refs,t.ffi) op ws = res1 ∧
      fr ⊑ fr1 ∧
      ft ⊑ ft1 ∧
      fe ⊑ fe1 ∧
      OPTREL (λ((refs1,ffi1),res) ((refs1',ffi1'),res1).
                ∃s1 t1.
                  s1.refs = refs1 ∧ s1.ffi = ffi1 ∧
                  t1.refs = refs1' ∧ t1.ffi = ffi1' ∧
                  s1.next_exn_stamp = s.next_exn_stamp ∧
                  t1.next_exn_stamp = t.next_exn_stamp ∧
                  s1.next_type_stamp = s.next_type_stamp ∧
                  t1.next_type_stamp = t.next_type_stamp ∧
                  state_rel l fr1 ft1 fe1 s1 t1 ∧
                  res_rel (v_rel fr1 ft1 fe1) (v_rel fr1 ft1 fe1) res res1)
              res res1
Proof
  strip_tac
  \\ Cases_on ‘∃a ty. op = Arith a ty’ \\ gs []
  >- (
    gvs [do_app_def] \\ rpt $ irule_at Any SUBMAP_REFL
    \\ drule_then drule do_arith_update
    \\ drule v_rel_IMP_check_type_eq
    \\ reverse $ rw[]
    >- prove_tac[LIST_REL_EL_EQN, EVERY_EL]
    >- prove_tac[LIST_REL_EL_EQN, EVERY_EL]
    \\ first_x_assum $ drule_then(qspec_then‘a’mp_tac)
    \\ rw[OPTREL_def] \\ gvs[CaseEq"sum",PULL_EXISTS]
    \\ Cases_on‘x0’ \\ Cases_on‘y0’ \\ gvs[]
    \\ prove_tac[] )
  \\ Cases_on ‘∃ty1 ty2. op = FromTo ty1 ty2’ \\ gs []
  >- (
    gvs [do_app_def] \\ rpt $ irule_at Any SUBMAP_REFL
    \\ CASE_TAC \\ gvs[]
    \\ TOP_CASE_TAC \\ gvs[]
    \\ drule v_rel_IMP_check_type_eq
    \\ reverse $ rw[]
    >- prove_tac[]
    >- prove_tac[]
    \\ Cases_on‘ty1’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ Cases_on‘ty2’ using semanticPrimitivesPropsTheory.prim_type_cases
    \\ gvs[do_conversion_def] \\ rw []
    \\ gvs[check_type_def]
    \\ last_assum $ irule_at Any \\ gvs []
    \\ gvs [chr_exn_v_def, chr_stamp_def]
    \\ gvs[Once v_rel_cases]
    \\ simp [Once v_rel_cases]
    \\ simp [Once stamp_rel_cases]
    \\ gvs [state_rel_def])
  \\ Cases_on ‘∃test ty. op = Test test ty’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v", "word_size"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ gvs [CaseEqs ["eq_result"], EXISTS_PROD, PULL_EXISTS]
    \\ drule_all do_test_thm \\ fs [] \\ rw []
    \\ qpat_assum ‘state_rel l fr ft fe s t’ $ irule_at Any \\ fs []
    \\ Cases_on ‘b’ \\ gvs [Boolv_def]
    \\ simp [Once v_rel_cases,stamp_rel_cases]
    \\ gvs [state_rel_def])
  \\ Cases_on ‘op = Env_id’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, CaseEqs ["list", "v", "option", "prod"],
                           v_rel_def, OPTREL_def]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs [v_rel_def, nat_to_v_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘∃chn. op = FFI chn’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup
    \\ ‘t.ffi = s.ffi’
      by gs [state_rel_def]
    \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gvs [ref_rel_def]
    >- (
      gvs [CaseEqs ["ffi_result", "option", "bool", "oracle_result"],
              ffiTheory.call_FFI_def, PULL_EXISTS, state_rel_def]
      \\ gs [store_assign_def, store_lookup_def, v_rel_def])
    \\ gvs [CaseEqs ["ffi_result", "option", "bool", "oracle_result"],
            ffiTheory.call_FFI_def, PULL_EXISTS, EXISTS_PROD, v_rel_def,
            store_assign_def, store_lookup_def]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’ \\ rw [] \\ gs [ref_rel_def]
    \\ first_x_assum (qspec_then ‘n1’ assume_tac) \\ gs []
    \\ rw [] \\ gs []
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = ConfigGC’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = ListAppend’ \\ gs []
  >- (
    ‘FLOOKUP ft list_type_num = SOME list_type_num ∧
     INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
     list_type_num < t.next_type_stamp’
      by (gs [state_rel_def]
          \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
          \\ rpt (first_x_assum (qspec_then ‘list_type_num’ assume_tac))
          \\ gs [flookup_thm])
    \\ Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                              CaseEqs ["list", "v", "option", "prod", "lit"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ dxrule v_rel_v_to_list
    \\ rpt (disch_then drule) \\ gs []
    \\ disch_then drule \\ rw [OPTREL_def]
    \\ gs [option_nchotomy]
    \\ dxrule v_rel_v_to_list
    \\ rpt (disch_then drule) \\ gs []
    \\ disch_then drule \\ rw [OPTREL_def]
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule v_rel_list_to_v \\ gs []
    \\ irule_at Any v_to_list_list_to_v
    \\ irule_at Any v_to_list_list_to_v
    \\ gs [LIST_REL_EL_EQN, EL_APPEND_EQN]
    \\ rw [] \\ gs[])
  \\ Cases_on ‘op = Aw8sub_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gs []
    \\ first_assum (irule_at Any) \\ gs [v_rel_def])
  \\ Cases_on ‘op = Aw8update_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ gvs [store_assign_def, store_lookup_def]
    \\ rw [] \\ gs [v_rel_def]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = Aupdate_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ gvs [store_assign_def, store_lookup_def, store_v_same_type_def]
    \\ rw [] \\ gs [v_rel_def]
    \\ drule_then assume_tac LIST_REL_LENGTH \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ gvs [LIST_REL_EL_EQN, EL_LUPDATE]
    \\ rw [] \\ gs []
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = Asub_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gs []
    \\ gs [LIST_REL_EL_EQN]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Aupdate’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ gvs [store_assign_def, store_lookup_def, store_v_same_type_def]
    \\ rw [] \\ gs [v_rel_def]
    \\ drule_then assume_tac LIST_REL_LENGTH \\ gvs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE, sub_exn_v_def, v_rel_def, stamp_rel_cases,
           subscript_stamp_def]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ gvs [LIST_REL_EL_EQN, EL_LUPDATE]
    \\ rw [] \\ gs []
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = Alength’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def, v_rel_def]
    \\ gvs [store_assign_def, store_lookup_def, store_v_same_type_def]
    \\ drule_then assume_tac LIST_REL_LENGTH \\ gvs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def])
  \\ Cases_on ‘op = Asub’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gs []
    \\ gvs [LIST_REL_EL_EQN]
    \\ gs [state_rel_def, sub_exn_v_def, v_rel_def, stamp_rel_cases,
           subscript_stamp_def]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs [])
  \\ Cases_on ‘op = AallocEmpty’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS]
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ simp [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ simp [count_add1]
    \\ strip_tac
    >- (
      qx_gen_tac ‘n’
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n’
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ rw [] \\ gs [EL_LENGTH_APPEND, ref_rel_def]
    \\ gs [EL_APPEND_EQN]
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ Q.LIST_EXISTS_TAC [‘fe’,‘fr’,‘ft’] \\ gs [])
  \\ Cases_on ‘op = Aalloc’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS, CaseEqs ["bool", "option"],
            v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def]
    >- (
      rpt (irule_at Any SUBMAP_REFL \\ gs [])
      \\ first_assum (irule_at Any)
      \\ gs [state_rel_def])
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE, count_add1]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ simp [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ strip_tac
    >- (
      qx_gen_tac ‘n’
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n’
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ rw [] \\ gs [EL_APPEND_EQN, ref_rel_def, LIST_REL_REPLICATE_same]
    >- (
      rw []
      \\ irule v_rel_update
      \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs [])
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs [])
  \\ Cases_on ‘op = AallocFixed’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [state_rel_def, store_alloc_def] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS, CaseEqs ["bool", "option"],
            v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def]
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE, count_add1]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ simp [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ strip_tac
    >- (
      qx_gen_tac ‘n’
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n’
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ rw [] \\ gs [EL_APPEND_EQN, ref_rel_def, LIST_REL_REPLICATE_same]
    >- (
      qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
      \\ match_mp_tac LIST_REL_mono \\ rw []
      \\ irule v_rel_update
      \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs [])
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs [])
  \\ Cases_on ‘op = Vlength’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any)
    \\ gs [LIST_REL_EL_EQN])
  \\ Cases_on ‘op = Vsub’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rw [] \\ gvs [CaseEqs ["bool", "option"]]
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS, CaseEqs ["bool", "option"],
            v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def]
    \\ first_assum (irule_at Any)
    \\ gs [state_rel_def, LIST_REL_EL_EQN])
  \\ Cases_on ‘op = Vsub_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs [LIST_REL_EL_EQN]
    \\ first_assum (irule_at Any)
    \\ gs [state_rel_def, LIST_REL_EL_EQN])
  \\ Cases_on ‘op = VfromList’ \\ gs []
  >- (
    ‘FLOOKUP ft list_type_num = SOME list_type_num ∧
     INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
     list_type_num < t.next_type_stamp’
      by (gs [state_rel_def]
          \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
          \\ rpt (first_x_assum (qspec_then ‘list_type_num’ assume_tac))
          \\ gs [flookup_thm])
    \\ Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                              CaseEqs ["list", "v", "option", "prod", "lit",
                                       "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rename1 ‘v_rel _ _ _ x1 x2’
    \\ ‘∃res. v_to_list x2 = res’ by gs []
    \\ drule_all v_rel_v_to_list \\ rw [OPTREL_def]
    \\ first_assum (irule_at Any) \\ gs [v_rel_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Strcat’ \\ gs []
  >- (
    ‘FLOOKUP ft list_type_num = SOME list_type_num ∧
     INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
     list_type_num < t.next_type_stamp’
      by (gs [state_rel_def]
          \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
          \\ rpt (first_x_assum (qspec_then ‘list_type_num’ assume_tac))
          \\ gs [flookup_thm])
    \\ Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                              CaseEqs ["list", "v", "option", "prod", "lit",
                                       "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rename1 ‘v_rel _ _ _ x1 x2’
    \\ ‘∃res. v_to_list x2 = res’ by gs []
    \\ drule_all v_rel_v_to_list \\ rw [OPTREL_def]
    \\ gs [option_nchotomy]
    \\ rename1 ‘LIST_REL _ y1 y2’
    \\ ‘∃res. vs_to_string y2 = res’ by gs []
    \\ drule_all v_rel_vs_to_string \\ rw []
    \\ gs [v_rel_def]
    \\ first_assum (irule_at Any)
    \\ irule_at Any EQ_REFL \\ gs [])
  \\ Cases_on ‘op = Strlen’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Strsub’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rw [] \\ gvs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def,
           state_rel_def])
  \\ Cases_on ‘op = Explode’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ gs [v_rel_def]
    \\ first_assum (irule_at Any) \\ gs []
    \\ irule v_rel_list_to_v
    \\ irule_at Any v_to_list_list_to_v
    \\ irule_at Any v_to_list_list_to_v
    \\ gs [state_rel_def, EVERY2_MAP, LIST_REL_EL_EQN, v_rel_def])
  \\ Cases_on ‘op = Implode’ \\ gs []
  >- (
    ‘FLOOKUP ft list_type_num = SOME list_type_num ∧
     INJ ($' ft) (FDOM ft) (count t.next_type_stamp) ∧
     list_type_num < t.next_type_stamp’
      by (gs [state_rel_def]
          \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
          \\ rpt (first_x_assum (qspec_then ‘list_type_num’ assume_tac))
          \\ gs [flookup_thm])
    \\ Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                              CaseEqs ["list", "v", "option", "prod", "lit",
                                       "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ rename1 ‘v_rel _ _ _ x1 x2’
    \\ ‘∃res. v_to_char_list x2 = res’ by gs []
    \\ drule_all v_rel_v_to_char_list \\ rw []
    \\ first_assum (irule_at Any)
    \\ gs [v_rel_def] \\ metis_tac[])
  \\ Cases_on ‘op = XorAw8Str_unsafe’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ mp_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
    \\ rpt (qpat_x_assum ‘FLOOKUP _ _ = _’ mp_tac)
    \\ rw [flookup_thm, INJ_DEF] \\ gs [])
  \\ Cases_on ‘op = CopyAw8Aw8’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    >- (
      first_assum (irule_at Any)
      \\ gs [state_rel_def])
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ mp_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
    \\ rpt (qpat_x_assum ‘FLOOKUP _ _ = _’ mp_tac)
    \\ rw [flookup_thm, INJ_DEF] \\ gs [])
  \\ Cases_on ‘op = CopyAw8Str’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ rw [] \\ gs [ref_rel_def, v_rel_def, stamp_rel_cases])
  \\ Cases_on ‘op = CopyStrAw8’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ mp_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
    \\ rpt (qpat_x_assum ‘FLOOKUP _ _ = _’ mp_tac)
    \\ rw [flookup_thm, INJ_DEF] \\ gs [])
  \\ Cases_on ‘op = CopyStrStr’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"], PULL_EXISTS]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gs [])
    \\ imp_res_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rpt (rename [‘ref_rel _ (_ _) y0’] \\ Cases_on ‘y0’ \\ gvs [ref_rel_def])
    \\ gvs [store_assign_def, store_lookup_def, copy_array_def,
            v_rel_def, sub_exn_v_def, subscript_stamp_def, stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ rw [] \\ gs [ref_rel_def, v_rel_def, stamp_rel_cases])
  \\ Cases_on ‘op = Aw8update’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ gvs [store_assign_def, store_lookup_def]
    \\ rw [] \\ gvs [v_rel_def, sub_exn_v_def, subscript_stamp_def,
                     stamp_rel_cases]
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, EL_LUPDATE]
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [ref_rel_def]
    \\ rw [] \\ gs [ref_rel_def]
    \\ qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac \\ rw [INJ_DEF]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ qpat_x_assum ‘FLOOKUP fr _ = _’ mp_tac \\ rw [flookup_thm]
    \\ gs [])
  \\ Cases_on ‘op = Aw8sub’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gvs [LIST_REL_EL_EQN, v_rel_def, sub_exn_v_def,
                     subscript_stamp_def, stamp_rel_cases]
    \\ first_assum (irule_at Any) \\ gs [state_rel_def])
  \\ Cases_on ‘op = Aw8length’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ rw [] \\ gvs [LIST_REL_EL_EQN, v_rel_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Aw8alloc’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def, PULL_EXISTS, CaseEqs ["bool", "option"],
            v_rel_def, sub_exn_v_def, stamp_rel_cases, subscript_stamp_def]
    >- (
      rpt (irule_at Any SUBMAP_REFL \\ gs [])
      \\ first_assum (irule_at Any)
      \\ gs [state_rel_def])
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE, count_add1]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ simp [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ strip_tac
    >- (
      qx_gen_tac ‘n’
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n’
    \\ first_x_assum (qspec_then ‘n’ assume_tac)
    \\ rw [] \\ gs [EL_APPEND_EQN, ref_rel_def, LIST_REL_REPLICATE_same]
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs [])
  \\ Cases_on ‘∃sz sh n. op = Shift sz sh n’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v", "word_size"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Equality’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v", "word_size"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ gs [CaseEqs ["eq_result"], EXISTS_PROD, PULL_EXISTS]
    \\ gs [state_rel_def]
    \\ rename1 ‘v_rel _ _ _ x1 x2’ \\ rename1 ‘v_rel _ _ _ y1 y2’
    >- (
      qpat_assum ‘do_eq _ _ = _’ (SUBST1_TAC o SYM)
      \\ once_rewrite_tac [EQ_SYM_EQ]
      \\ irule (CONJUNCT1 v_rel_do_eq)
      \\ first_assum (irule_at Any) \\ gs []
      \\ first_assum (irule_at Any) \\ gs []
      \\ first_assum (irule_at Any) \\ gs []
      \\ first_assum (irule_at Any) \\ gs [])
    \\ qexists_tac ‘b’
    \\ qpat_assum ‘do_eq _ _ = _’ (SUBST1_TAC o SYM)
    \\ simp_tac std_ss [Once EQ_SYM_EQ]
    \\ irule_at Any (CONJUNCT1 v_rel_do_eq) \\ gvs []
    \\ first_assum (irule_at (Pat ‘v_rel’)) \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ rw [Boolv_def]
    \\ gs [v_rel_def, stamp_rel_cases, SF SFY_ss])
  \\ Cases_on ‘op = Opderef’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs []
    \\ drule_all_then assume_tac state_rel_store_lookup \\ gs [OPTREL_def]
    \\ rename1 ‘ref_rel _ _ y0’ \\ Cases_on ‘y0’ \\ gs [ref_rel_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Opassign’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs [v_rel_def]
    \\ rename1 ‘v_rel fr ft fe v w’
    \\ ‘ref_rel (v_rel fr ft fe) (Refv v) (Refv w)’
      by gs [ref_rel_def]
    \\ drule_all state_rel_store_assign \\ rw [OPTREL_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = Opref’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, v_rel_def, OPTREL_def,
                           CaseEqs ["list", "v", "option", "prod", "lit",
                                    "store_v"]]
    \\ TRY (rpt (irule_at Any SUBMAP_REFL) \\ gs [] \\ NO_TAC)
    \\ rpt (pairarg_tac \\ gs []) \\ gvs []
    \\ gvs [store_alloc_def, v_rel_def]
    \\ qexists_tac ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’
    \\ irule_at Any SUBMAP_REFL
    \\ irule_at Any SUBMAP_REFL
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r1; ffi := f1; clock := s.clock;
          next_type_stamp := nts1; next_exn_stamp := nes1;
          eval_state := NONE |>’ \\ gs []
    \\ Q.REFINE_EXISTS_TAC
      ‘<| refs := r2; ffi := f2; clock := t.clock;
          next_type_stamp := nts2; next_exn_stamp := nes2;
          eval_state := NONE |>’ \\ gs []
    \\ gs [state_rel_def, FLOOKUP_UPDATE, count_add1]
    \\ conj_tac
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ rw [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ conj_tac
    >- (
      qx_gen_tac ‘n1’
      \\ first_x_assum (qspec_then ‘n1’ assume_tac)
      \\ rw [] \\ gs []
      \\ first_x_assum drule \\ gs [])
    \\ qx_gen_tac ‘n1’
    \\ first_x_assum (qspec_then ‘n1’ assume_tac)
    \\ rw [] \\ gs [EL_LENGTH_APPEND, ref_rel_def, EL_APPEND_EQN]
    >- (
      irule v_rel_update
      \\ first_assum (irule_at (Pat ‘v_rel’))
      \\ gs [])
    \\ irule ref_rel_mono
    \\ first_assum (irule_at Any) \\ rw []
    \\ irule v_rel_update
    \\ first_assum (irule_at (Pat ‘v_rel’))
    \\ gs [])
  \\ Cases_on ‘∃m. op = ThunkOp (AllocThunk m)’ \\ gs[]
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, AllCaseEqs(), thunk_op_def]
    \\ rpt (pairarg_tac \\ gvs [])
    >- metis_tac [SUBMAP_REFL]
    >- metis_tac [SUBMAP_REFL]
    \\ qexists ‘fr |+ (LENGTH s.refs,LENGTH t.refs)’ \\ gvs []
    \\ rpt (irule_at Any SUBMAP_REFL \\ gvs [])
    \\ gvs [store_alloc_def]
    \\ rename1 ‘v_rel _ _ _ v y’
    \\ qexistsl [‘t with refs := t.refs ++ [Thunk m y]’,
                 ‘s with refs := s.refs ++ [Thunk m v]’]
    \\ gvs [state_rel_def]
    \\ rw []
    >- (
      qpat_x_assum ‘INJ ($' fr) _ _’ mp_tac
      \\ simp [INJ_DEF, FAPPLY_FUPDATE_THM]
      \\ rw [] \\ gvs []
      \\ ntac 2 (first_x_assum drule \\ gvs []))
    >- gvs [count_add1]
    >- (
      gvs [FLOOKUP_UPDATE] \\ rw []
      \\ first_x_assum drule \\ rw [])
    >- (first_x_assum drule \\ rw [])
    >- (
      gvs [FLOOKUP_UPDATE, EL_APPEND_EQN] \\ rw [] \\ gvs []
      >- (
        simp [oneline ref_rel_def]
        \\ irule v_rel_update \\ gvs []
        \\ first_x_assum $ irule_at Any \\ gvs [])
      >- (
        first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs []
        \\ irule ref_rel_mono \\ gvs []
        \\ first_x_assum $ irule_at Any \\ rw []
        \\ irule v_rel_update \\ gvs []
        \\ first_x_assum $ irule_at Any \\ gvs []))
    >- (
      gvs [FLOOKUP_UPDATE]
      \\ first_x_assum $ qspec_then ‘n’ assume_tac \\ gvs [])
    >- gvs [v_rel_def, FLOOKUP_UPDATE])
  \\ Cases_on ‘∃m. op = ThunkOp (UpdateThunk m)’ \\ gs[]
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, AllCaseEqs(), thunk_op_def, OPTREL_def]
    \\ rpt (irule_at Any SUBMAP_REFL) \\ gs [v_rel_def]
    \\ rename1 ‘v_rel fr ft fe v w’
    \\ ‘ref_rel (v_rel fr ft fe) (Thunk m v) (Thunk m w)’
      by gs [ref_rel_def]
    \\ drule_all state_rel_store_assign \\ rw [OPTREL_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = ThunkOp ForceThunk’ \\ gs []
  >- (
    Cases_on ‘res’ \\ gvs [do_app_def, AllCaseEqs(), thunk_op_def]
    \\ rpt (irule_at Any SUBMAP_REFL \\ gvs []))
  \\ Cases_on ‘op’ \\ gs []
  \\ Cases_on ‘t'’ \\ gs []
QED

(* TODO Move up *)
Theorem res_rel_list_result:
  res_rel R1 R2 x y ⇒
    res_rel (LIST_REL R1) R2 (list_result x) (list_result y)
Proof
  Cases_on ‘x’ \\ Cases_on ‘y’ \\ gs [list_result_def]
  \\ rename1 ‘_ _ (Rerr e1) (Rerr e2)’
  \\ Cases_on ‘e1’ \\ Cases_on ‘e2’ \\ gs []
QED

(* TODO Move up *)
Theorem res_rel_mono:
  res_rel R1 R2 x y ∧
  (∀x y. R1 x y ⇒ Q1 x y) ∧
  (∀x y. R2 x y ⇒ Q2 x y) ⇒
    res_rel Q1 Q2 x y
Proof
  rw []
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ gs []
  \\ rename1 ‘_ _ (Rerr e1) (Rerr e2)’
  \\ Cases_on ‘e1’ \\ Cases_on ‘e2’ \\ gs []
QED

Definition thunk_rel_def:
  thunk_rel f BadRef BadRef = T ∧
  thunk_rel f NotThunk NotThunk = T ∧
  thunk_rel f (IsThunk m1 v1) (IsThunk m2 v2) = (m1 = m2 ∧ f v1 v2) ∧
  thunk_rel _ _ _ = F
End

Theorem state_rel_dest_thunk:
  state_rel l fr ft fe s t ∧
  LIST_REL (v_rel fr ft fe) vs ws ∧
  dest_thunk vs s.refs = t1 ⇒
    ∃t2. dest_thunk ws t.refs = t2 ∧ thunk_rel (v_rel fr ft fe) t1 t2
Proof
  rw []
  \\ Cases_on ‘dest_thunk vs s.refs’
  \\ Cases_on ‘dest_thunk ws t.refs’
  \\ gvs [thunk_rel_def, oneline dest_thunk_def, AllCaseEqs(), v_rel_def]
  \\ drule_all state_rel_store_lookup \\ rw [OPTREL_def, ref_rel_def]
QED

Theorem state_rel_update_thunk_NONE:
  fr1 ⊑ fr2 ∧
  state_rel l fr2 ft2 fe2 s t ∧
  LIST_REL (v_rel fr1 ft1 fe1) vs1 ws1 ∧
  LIST_REL (v_rel fr2 ft2 fe2) vs2 ws2 ∧
  update_thunk vs1 s.refs vs2 = NONE ⇒
    update_thunk ws1 t.refs ws2 = NONE
Proof
  rw []
  \\ gvs [oneline update_thunk_def, AllCaseEqs(), v_rel_def]
  \\ ‘LIST_REL (v_rel fr2 ft2 fe2) [v] [y']’ by gvs []
  \\ drule_all state_rel_dest_thunk \\ rw [] \\ gvs []
  \\ Cases_on ‘dest_thunk [y'] t.refs’ \\ gvs [thunk_rel_def]
  \\ ‘FLOOKUP fr2 n = SOME l2’ by (drule_all FLOOKUP_SUBMAP \\ rw [])
  \\ ‘ref_rel (v_rel fr2 ft2 fe2) (Thunk Evaluated v) (Thunk Evaluated y')’
    by gvs [ref_rel_def]
  \\ drule_all state_rel_store_assign \\ rw [OPTREL_def]
QED

Theorem state_rel_update_thunk_SOME:
  fr1 ⊑ fr2 ∧
  state_rel l fr2 ft2 fe2 s t ∧
  update_thunk vs1 s.refs vs2 = SOME refs1 ∧
  LIST_REL (v_rel fr1 ft1 fe1) vs1 a1 ∧
  LIST_REL (v_rel fr2 ft2 fe2) vs2 a2 ⇒
    ∃refs2.
      (update_thunk a1 t.refs a2 = SOME refs2 ∧
       state_rel l fr2 ft2 fe2 (s with refs := refs1) (t with refs := refs2))
Proof
  rw []
  \\ gvs [oneline update_thunk_def, AllCaseEqs(), v_rel_def]
  \\ ‘LIST_REL (v_rel fr2 ft2 fe2) [v] [y']’ by gvs []
  \\ drule_all state_rel_dest_thunk \\ rw [] \\ gvs []
  \\ Cases_on ‘dest_thunk [y'] t.refs’ \\ gvs [thunk_rel_def]
  \\ ‘FLOOKUP fr2 n = SOME l2’ by (drule_all FLOOKUP_SUBMAP \\ rw [])
  \\ ‘ref_rel (v_rel fr2 ft2 fe2) (Thunk Evaluated v) (Thunk Evaluated y')’
    by gvs [ref_rel_def]
  \\ drule_all state_rel_store_assign \\ rw [OPTREL_def] \\ gvs []
QED

Theorem evaluate_update_Op:
  op ≠ Opapp ∧ op ≠ Eval ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def] \\ Cases_on ‘getOpClass op’
  >- (Cases_on ‘op’ \\ gs[] \\ Cases_on ‘t'’ \\ gs[])
  >- (Cases_on ‘op’ \\ gs[] \\ Cases_on ‘t'’ \\ gs[])
  >- (
    Cases_on ‘op’ \\ gvs [] \\ Cases_on ‘t'’ \\ gvs []
    \\ qpat_x_assum ‘_ = (s1,res)’ mp_tac
    \\ TOP_CASE_TAC \\ gvs []
    \\ reverse TOP_CASE_TAC \\ gvs []
    >- (
      strip_tac
      \\ first_x_assum drule_all \\ rw [] \\ gvs []
      \\ qpat_x_assum ‘res_rel _ _ (Rerr _) res1’ mp_tac
      \\ Cases_on ‘res1’ \\ rw [res_rel_def]
      \\ metis_tac [])
    \\ first_x_assum drule_all \\ strip_tac \\ gvs []
    \\ Cases_on ‘res1’ \\ gvs [res_rel_def]
    \\ TOP_CASE_TAC \\ gvs []
    \\ imp_res_tac EVERY2_REVERSE
    \\ drule_all state_rel_dest_thunk \\ simp [oneline thunk_rel_def]
    \\ TOP_CASE_TAC \\ gvs []
    >~ [‘BadRef’] >- metis_tac []
    >~ [‘NotThunk’] >- metis_tac []
    \\ strip_tac \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    >- (rw [] \\ gvs [] \\ metis_tac [])
    \\ TOP_CASE_TAC \\ gvs []
    >- (
      strip_tac \\ gvs []
      \\ qpat_x_assum ‘v_rel _ _ _ v v'’ mp_tac
      \\ gvs [do_opapp_def, AllCaseEqs(), PULL_EXISTS]
      \\ rw [Once v_rel_cases]
      \\ metis_tac [])
    \\ Cases_on ‘do_opapp [v'; Conv NONE []]’ \\ gvs []
    >- (
      CCONTR_TAC \\ gvs []
      \\ qpat_x_assum ‘v_rel _ _ _ v v'’ assume_tac
      \\ gvs [do_opapp_def, AllCaseEqs(), PULL_EXISTS]
      \\ rgs [Once v_rel_cases])
    \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\ gvs []
    \\ ‘q.clock = t1.clock’ by gvs [state_rel_def] \\ gvs []
    \\ TOP_CASE_TAC \\ gvs []
    >- (rw [] \\ gvs [] \\ metis_tac [])
    \\ TOP_CASE_TAC \\ gvs []
    \\ ‘state_rel l fr1 ft1 fe1 (dec_clock q) (dec_clock t1)’
      by gvs [dec_clock_def, state_rel_def]
    \\ first_x_assum drule
    \\ disch_then $ qspec_then ‘q''’ mp_tac
    \\ impl_tac \\ gvs []
    >- (
      qpat_x_assum ‘v_rel _ _ _ v v'’ assume_tac
      \\ gvs [do_opapp_def, AllCaseEqs()]
      \\ rgs [Once v_rel_cases] \\ gvs []
      \\ gvs [env_rel_def]
      \\ irule nsAll2_nsBind \\ gvs [v_rel_def]
      \\ gvs [semanticPrimitivesPropsTheory.build_rec_env_merge]
      \\ irule nsAll2_nsAppend \\ gs []
      \\ irule nsAll2_alist_to_ns
      \\ gs [EVERY2_MAP, LAMBDA_PROD, v_rel_def]
      \\ rw [LIST_REL_EL_EQN, ELIM_UNCURRY, env_rel_def])
    \\ strip_tac \\ gvs []
    \\ qpat_x_assum ‘v_rel _ _ _ v v'’ assume_tac
    \\ gvs [do_opapp_def]
    \\ gvs [CaseEq"v", CaseEq"option", CaseEq"prod"]
    \\ rgs [Once v_rel_cases] \\ gvs []
    \\ (
      reverse TOP_CASE_TAC \\ gvs []
      >- (
        rw [] \\ gvs []
        \\ TOP_CASE_TAC \\ gvs []
        \\ metis_tac [SUBMAP_TRANS])
      \\ TOP_CASE_TAC \\ gvs []
      >- (
        rw [] \\ gvs []
        \\ TOP_CASE_TAC \\ gvs []
        \\ imp_res_tac EVERY2_REVERSE
        \\ drule_all state_rel_update_thunk_NONE \\ rw [] \\ gvs []
        \\ metis_tac [SUBMAP_TRANS])
      \\ strip_tac \\ gvs []
      \\ TOP_CASE_TAC \\ gvs []
      \\ imp_res_tac EVERY2_REVERSE
      \\ drule_all state_rel_update_thunk_SOME \\ rw [] \\ gvs []
      \\ metis_tac [SUBMAP_TRANS]))
  >- (
    gvs [CaseEqs ["prod", "result", "option"], PULL_EXISTS]
    \\ first_x_assum (drule_all_then strip_assume_tac)
    \\ Cases_on ‘res1’ \\ gs []
    >~ [‘res_rel _ _ (Rerr err1) (Rerr err2)’] >- (
      first_assum (irule_at Any)
      \\ gs [])
    \\ dxrule_then assume_tac EVERY2_REVERSE
    \\ drule_all_then strip_assume_tac do_app_update \\ gs []
    \\ gs [OPTREL_def, SF SFY_ss]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ irule_at Any res_rel_list_result
    \\ first_assum (irule_at Any)
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
    \\ gs [state_rel_def])
QED

Theorem do_opapp_update:
  do_opapp vs = res1 ∧
  LIST_REL (v_rel fr ft fe) vs ws ⇒
    let res2 = do_opapp ws in
    OPTREL (λ(env1,x1) (env2,x2). env_rel fr ft fe env1 env2 ∧ x1 = x2)
           res1 res2
Proof
  rw [OPTREL_def]
  \\ Cases_on ‘do_opapp vs’ \\ Cases_on ‘do_opapp ws’ \\ gs []
  \\ PairCases_on ‘x’ \\ gs []
  \\ gvs [semanticPrimitivesPropsTheory.do_opapp_cases, v_rel_def]
  \\ gs [do_opapp_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ simp [env_rel_nsBind]
  \\ gs [semanticPrimitivesPropsTheory.build_rec_env_merge, env_rel_def]
  \\ irule nsAll2_nsBind \\ gs []
  \\ irule nsAll2_nsAppend \\ gs []
  \\ irule nsAll2_alist_to_ns
  \\ gs [EVERY2_MAP, LAMBDA_PROD, v_rel_def]
  \\ rw [LIST_REL_EL_EQN, ELIM_UNCURRY, env_rel_def]
QED

Theorem evaluate_update_Opapp:
  op = Opapp ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool"], PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘res_rel _ _ (Rerr err1) (Rerr err2)’] >- (
    first_assum (irule_at Any)
    \\ gs [])
  \\ dxrule_then assume_tac EVERY2_REVERSE
  \\ drule_all do_opapp_update \\ rw [OPTREL_def]
  \\ rpt (pairarg_tac \\ gvs [])
  >~ [‘do_opapp _ = NONE’] >- (
    first_assum (irule_at Any) \\ gs [])
  >- (
    first_assum (irule_at Any)
    \\ gs [state_rel_def])
  \\ rename [‘state_rel l fr1 ft1 fe1 s1 t1’]
  \\ ‘state_rel l fr1 ft1 fe1 (dec_clock s1) (dec_clock t1)’
    by gs [state_rel_def, dec_clock_def]
  \\ drule_all_then assume_tac env_rel_update
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at Any) \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ gs [state_rel_def]
QED

Theorem evaluate_update_App:
  ^(get_goal "App")
Proof
  Cases_on ‘op = Opapp’ >- (match_mp_tac evaluate_update_Opapp \\ gs [])
  \\ Cases_on ‘op = Eval’ >- (match_mp_tac evaluate_update_Eval \\ gs [])
  \\ match_mp_tac evaluate_update_Op \\ gs []
QED

Theorem v_rel_Boolv:
  state_rel l fr ft fe s t ∧
  v_rel fr ft fe v1 v2 ⇒
    ∀b. v1 = Boolv b ⇔ v2 = Boolv b
Proof
  rw [Boolv_def, state_rel_def] \\ rw [EQ_IMP_THM]
  \\ gvs [v_rel_def, OPTREL_def, Once stamp_rel_cases, flookup_thm]
  \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac \\ rw [INJ_DEF]
QED

Theorem v_rel_do_log:
  state_rel l fr ft fe s t ∧
  v_rel fr ft fe v1 v2 ∧
  do_log lop v1 x = res ⇒
    case res of
      SOME (Val v) =>
        ∃w. do_log lop v2 x = SOME (Val w) ∧
            v_rel fr ft fe v w
    | _ => do_log lop v2 x = res
Proof
  rw [] \\ gs []
  \\ drule_all_then assume_tac v_rel_Boolv \\ gs []
  \\ gs [do_log_def]
  \\ rw [] \\ gs []
QED

Theorem evaluate_update_Log:
  ^(get_goal "Log")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool", "exp_or_val"],
          PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘res_rel _ _ (Rerr err1) (Rerr err2)’] >- (
    Cases_on ‘err1’ \\ Cases_on ‘err2’ \\ gs []
    \\ gs [SF SFY_ss])
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ drule_all_then assume_tac v_rel_do_log \\ gs [SF SFY_ss]
  \\ drule_all_then assume_tac env_rel_update
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_update_If:
  ^(get_goal "If")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool", "exp_or_val"],
          PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘res_rel _ _ (Rerr err1) (Rerr err2)’] >- (
    Cases_on ‘err1’ \\ Cases_on ‘err2’ \\ gs []
    \\ gs [SF SFY_ss])
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ drule_all_then assume_tac v_rel_Boolv
  \\ gvs [do_if_def, CaseEqs ["option", "bool"], SF SFY_ss]
  \\ drule_all_then assume_tac env_rel_update
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_update_Mat:
  ^(get_goal "Mat")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool"], PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘res_rel _ _ (Rerr err1) (Rerr err2)’] >- (
    Cases_on ‘err1’ \\ Cases_on ‘err2’ \\ gs []
    \\ gs [SF SFY_ss])
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ drule_all_then assume_tac env_rel_update
  \\ ‘v_rel fr1 ft1 fe1 bind_exn_v bind_exn_v’
    by (rw [bind_exn_v_def, v_rel_def, Once stamp_rel_cases]
        \\ gs [state_rel_def, bind_stamp_def, SF SFY_ss])
  >- (
    first_x_assum (drule_all_then strip_assume_tac) \\ gs []
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [state_rel_def, env_rel_def]
    \\ qpat_x_assum ‘v_rel _ _ _ bind_exn_v _’ kall_tac
    \\ drule can_pmatch_all_thm \\ gs []
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then ‘MAP FST pes’ assume_tac) \\ gs []
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
    \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs [])
  \\ first_assum (irule_at Any)
  \\ gs [state_rel_def, env_rel_def]
  \\ qpat_x_assum ‘v_rel _ _ _ bind_exn_v _’ kall_tac
  \\ drule can_pmatch_all_thm \\ gs []
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then ‘MAP FST pes’ assume_tac) \\ gs []
QED

Theorem evaluate_update_Let:
  ^(get_goal "Let")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool"], PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘res_rel _ _ (Rerr err1) (Rerr err2)’] >- (
    Cases_on ‘err1’ \\ Cases_on ‘err2’ \\ gs []
    \\ gs [SF SFY_ss])
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ drule_all_then assume_tac env_rel_update
  \\ rename1 ‘v_rel fr1 ft1 fe1 v1 v2’
  \\ ‘env_rel fr1 ft1 fe1 (env with v := nsOptBind xo v1 env.v)
                          (env1 with v := nsOptBind xo v2 env1.v)’
    by (Cases_on ‘xo’ \\ gs [namespaceTheory.nsOptBind_def, env_rel_def]
        \\ irule nsAll2_nsBind \\ gs [])
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_update_Letrec:
  ^(get_goal "Letrec")
Proof
  rw [evaluate_def]
  >~ [‘¬ALL_DISTINCT _’] >- (
    first_assum (irule_at Any) \\ gs [])
  \\ ‘env_rel fr ft fe (env with v := build_rec_env funs env env.v)
                       (env1 with v := build_rec_env funs env1 env1.v)’
    suffices_by (
      strip_tac
      \\ first_x_assum (drule_all_then strip_assume_tac)
      \\ first_assum (irule_at Any) \\ gs [])
  \\ gs [env_rel_def]
  \\ simp [semanticPrimitivesPropsTheory.build_rec_env_merge]
  \\ irule nsAll2_nsAppend \\ gs []
  \\ irule nsAll2_alist_to_ns
  \\ rw [EVERY2_MAP, LAMBDA_PROD, LIST_REL_EL_EQN]
  \\ simp [ELIM_UNCURRY, v_rel_def, env_rel_def]
QED

Theorem evaluate_update_Tannot:
  ^(get_goal "Tannot")
Proof
  rw [evaluate_def]
QED

Theorem evaluate_update_Lannot:
  ^(get_goal "Lannot")
Proof
  rw [evaluate_def]
QED

Theorem evaluate_update_pmatch_Nil:
  ^(get_goal "[]:(pat # exp) list")
Proof
  rw [evaluate_def] \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_update_pmatch_Cons:
  ^(get_goal "_::_:(pat # exp) list")
Proof
  rw [evaluate_def]
  \\ gs [CaseEqs ["match_result"]]
  >~ [‘¬ALL_DISTINCT _’] >- (
    first_assum (irule_at Any) \\ gs [])
  >~ [‘res = Rerr (Rabort Rtype_error)’] >- (
    first_assum (irule_at Any) \\ gs []
    \\ gs [state_rel_def, env_rel_def]
    \\ drule (CONJUNCT1 pmatch_update)
    \\ rpt (disch_then drule) \\ simp []
    \\ rpt (disch_then drule) \\ rw []
    \\ Cases_on ‘pmatch env1.c t.refs p w []’ \\ gs [])
  >- (
    first_x_assum (drule_all_then strip_assume_tac) \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [state_rel_def, env_rel_def]
    \\ drule (CONJUNCT1 pmatch_update)
    \\ rpt (disch_then drule) \\ simp []
    \\ rpt (disch_then drule) \\ rw []
    \\ Cases_on ‘pmatch env1.c t.refs p w []’ \\ gs [])
  \\ qpat_assum ‘env_rel _ _ _ _ _’ mp_tac
  \\ qpat_assum ‘state_rel _ _ _ _ _ _’ mp_tac
  \\ simp_tac std_ss [Once env_rel_def, Once state_rel_def]
  \\ rpt strip_tac
  \\ drule (CONJUNCT1 pmatch_update)
  \\ rpt (disch_then drule) \\ simp []
  \\ rpt (disch_then drule) \\ rw []
  \\ Cases_on ‘pmatch env1.c t.refs p w []’ \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_rel_def]
  \\ irule nsAll2_nsAppend \\ gs []
  \\ irule nsAll2_alist_to_ns \\ gs []
QED

Theorem evaluate_update_decs_Nil:
  ^(get_goal "[]:dec list")
Proof
  rw [evaluate_decs_def, extend_dec_env_def]
  \\ first_assum (irule_at Any) \\ gs [SF SFY_ss]
  \\ simp [env_rel_def, ctor_rel_def]
QED

Theorem evaluate_update_decs_Cons:
  ^(get_goal "_::_::_:dec list")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["prod", "result"], PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘res_rel _ _ (Rerr _) (Rerr _)’] >- (
    first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ drule_all_then assume_tac env_rel_update
  \\ dxrule_then (drule_then assume_tac) env_rel_extend_dec_env
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at (Pat ‘state_rel’))
  \\ first_assum (irule_at Any)
  \\ irule_at Any EQ_REFL
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ gs [combine_dec_result_def]
  \\ rpt CASE_TAC \\ gs []
  \\ gs [extend_dec_env_def]
  \\ gs [env_rel_def, ctor_rel_def]
  \\ irule_at Any nsAll2_nsAppend
  \\ irule_at Any nsAll2_nsAppend \\ gs []
  \\ irule_at Any nsAll2_mono
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any nsAll2_mono
  \\ first_assum (irule_at Any) \\ gs []
  \\ simp [FORALL_PROD]
  \\ rw [] \\ (irule_at Any stamp_rel_update ORELSE irule_at Any v_rel_update)
  \\ gs [SF SFY_ss]
QED

Theorem env_rel_one_con_check:
  env_rel fr ft fe env env1 ⇒
  one_con_check env1.c = one_con_check env.c
Proof
  fs [one_con_check_def,FUN_EQ_THM]
  \\ strip_tac \\ Cases \\ fs [one_con_check_def]
  \\ rename [‘do_con_check _ a’] \\ Cases_on ‘a’ \\ fs [do_con_check_def]
  \\ fs [env_rel_def,ctor_rel_def]
  \\ pop_assum kall_tac
  \\ drule namespacePropsTheory.nsAll2_nsLookup_none
  \\ disch_then $ qspec_then ‘x’ assume_tac
  \\ rpt (CASE_TAC \\ fs [])
  \\ drule_all namespacePropsTheory.nsAll2_nsLookup2 \\ fs []
QED

Theorem evaluate_update_decs_Dlet:
  ^(get_goal "Dlet")
Proof
  reverse $ rw [evaluate_decs_def]
  >- (first_assum (irule_at Any) \\ gs [SF SFY_ss]
      \\ imp_res_tac env_rel_one_con_check \\ fs [])
  \\ imp_res_tac env_rel_one_con_check
  \\ gvs [CaseEqs ["prod", "result"], PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘res_rel _ _ (Rerr err1) (Rerr err2)’] >- (
    Cases_on ‘err1’ \\ Cases_on ‘err2’ \\ gs []
    \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ first_assum (irule_at Any) \\ gs [SF SFY_ss]
  \\ drule_then strip_assume_tac evaluate_sing \\ gvs []
  \\ ‘∃res. pmatch env.c s1.refs p x [] = res’ by gs []
  \\ drule_all_then assume_tac env_rel_update
  \\ gs [state_rel_def, env_rel_def]
  \\ drule (CONJUNCT1 pmatch_update)
  \\ rpt (disch_then drule) \\ simp []
  \\ rpt (disch_then drule) \\ rw []
  \\ rename1 ‘v_rel _ _ _ x y’
  \\ Cases_on ‘pmatch env.c s1.refs p x []’
  \\ Cases_on ‘pmatch env1.c t1.refs p y []’ \\ gs []
  \\ rw [v_rel_def, bind_exn_v_def, Once stamp_rel_cases, bind_stamp_def,
         ctor_rel_def]
  \\ irule nsAll2_alist_to_ns \\ gs []
QED

Theorem evaluate_update_decs_Dletrec:
  ^(get_goal "Dletrec")
Proof
  reverse $ rw [evaluate_decs_def]
  >- (first_assum (irule_at Any) \\ gs [SF SFY_ss])
  >- (CCONTR_TAC \\ fs []
      \\ imp_res_tac env_rel_one_con_check \\ fs []
      \\ gvs [EVERY_MEM,EXISTS_MEM] \\ res_tac \\ fs [])
  >- (imp_res_tac env_rel_one_con_check \\ fs []
      \\ gvs [EVERY_MEM,EXISTS_MEM] \\ res_tac \\ fs [])
  \\ gvs [CaseEqs ["prod", "result"], PULL_EXISTS]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_rel_def, ctor_rel_def, PULL_EXISTS, SF SFY_ss,
         semanticPrimitivesPropsTheory.build_rec_env_merge]
  \\ irule_at Any nsAll2_alist_to_ns
  \\ gs [EVERY2_MAP, LAMBDA_PROD]
  \\ rw [v_rel_def, LIST_REL_EL_EQN, ELIM_UNCURRY, env_rel_def, ctor_rel_def]
QED

Theorem state_rel_with_next_type_stamp:
  state_rel l fr ft fe s t ⇒
    state_rel l fr
      (ft ⊌ FUN_FMAP (λn. n - s.next_type_stamp + t.next_type_stamp)
                     (IMAGE ($+ s.next_type_stamp) (count extra))) fe
      (s with next_type_stamp := extra + s.next_type_stamp)
      (t with next_type_stamp := extra + t.next_type_stamp)
Proof
  simp [state_rel_def] \\ strip_tac
  \\ gs [flookup_thm, FUNION_DEF]
  \\ conj_tac
  >- (
    qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac
    \\ qpat_x_assum ‘FDOM ft = _’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ rw [INJ_IFF, FUNION_DEF]
    \\ rw [FUN_FMAP_DEF] \\ gs [CaseEq "bool"]
    \\ res_tac \\ fs [])
  \\ once_rewrite_tac [ADD_COMM] \\ simp [count_add]
  \\ qx_gen_tac ‘m’ \\ strip_tac
  \\ last_x_assum drule \\ rw []
  \\ irule ref_rel_mono
  \\ first_assum (irule_at Any) \\ rw []
  \\ irule v_rel_update
  \\ first_assum (irule_at (Pat ‘v_rel’))
  \\ gs [SUBMAP_FUNION_ID]
QED

Theorem state_rel_with_next_exn_stamp:
  state_rel l fr ft fe s t ⇒
    state_rel l fr ft
      (fe ⊌ FUN_FMAP (λn. n - s.next_exn_stamp + t.next_exn_stamp)
                     (IMAGE ($+ s.next_exn_stamp) (count extra)))
      (s with next_exn_stamp := extra + s.next_exn_stamp)
      (t with next_exn_stamp := extra + t.next_exn_stamp)
Proof
  simp [state_rel_def] \\ strip_tac
  \\ gs [flookup_thm, FUNION_DEF]
  \\ conj_tac
  >- (
    qpat_x_assum ‘INJ ($' fe) _ _’ mp_tac
    \\ qpat_x_assum ‘FDOM fe = _’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ rw [INJ_IFF, FUNION_DEF]
    \\ rw [FUN_FMAP_DEF] \\ gs [CaseEq "bool"]
    \\ res_tac \\ fs [])
  \\ once_rewrite_tac [ADD_COMM] \\ simp [count_add]
  \\ qx_gen_tac ‘m’ \\ strip_tac
  \\ last_x_assum drule \\ rw []
  \\ irule ref_rel_mono
  \\ first_assum (irule_at Any) \\ rw []
  \\ irule v_rel_update
  \\ first_assum (irule_at (Pat ‘v_rel’))
  \\ gs [SUBMAP_FUNION_ID]
QED

Theorem evaluate_update_decs_Dtype:
  ^(get_goal "Dtype")
Proof
  rw [evaluate_decs_def]
  >~ [‘¬EVERY check_dup_ctors _’] >- (
    first_assum (irule_at (Pat ‘state_rel’))
    \\ gs [])
  \\ drule_all_then (qspec_then ‘LENGTH tds’ assume_tac)
                    state_rel_with_next_type_stamp
  \\ rw []
  \\ first_assum (irule_at Any)
  \\ gs [SUBMAP_FUNION_ID]
  \\ gvs [env_rel_def, ctor_rel_def, state_rel_def]
  \\ qpat_x_assum ‘INJ ($' (FUNION _ _)) _ _’ mp_tac
  \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac
  \\ qpat_x_assum ‘FDOM ft = _’ mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ rename1 ‘_ _ (build_tdefs n _) (_ m _)’
  \\ qid_spec_tac ‘ft’
  \\ qid_spec_tac ‘m’
  \\ qid_spec_tac ‘tds’
  \\ qid_spec_tac ‘n’
  \\ ho_match_mp_tac build_tdefs_ind
  \\ rw [build_tdefs_def]
  \\ irule nsAll2_nsAppend \\ gs []
  \\ irule_at Any nsAll2_alist_to_ns \\ gs []
  \\ conj_tac
  >- (
    gs [build_constrs_def, EVERY2_MAP, LAMBDA_PROD, stamp_rel_cases]
    \\ gvs [LIST_REL_EL_EQN] \\ rw []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ gs [flookup_thm]
    \\ simp [FUNION_DEF]
    \\ qmatch_goalsub_abbrev_tac ‘FUN_FMAP f D’
    \\ ‘n ∈ D’
      by (gs [Abbr ‘D’] \\ qexists_tac ‘0’ \\ gs [])
    \\ ‘FINITE D’
      by gs [Abbr ‘D’]
    \\ drule_then (qspec_then ‘f’ mp_tac) FUN_FMAP_DEF \\ rw []
    \\ gs [Abbr ‘f’])
  \\ gs [ADD1]
  \\ ‘FDOM (ft |+ (n, m)) = count (n + 1)’
    by rw [EXTENSION]
  \\ ‘INJ ($' (ft |+ (n, m))) (count (n + 1)) (count (m + 1))’
    by (gs [INJ_IFF, FAPPLY_FUPDATE_THM]
        \\ rw [] \\ gs []
        \\ rename1 ‘x < n + 1’ \\ ‘x < n’ by gs []
        \\ res_tac \\ fs [])
  \\ ‘INJ ($' (FUNION (ft |+ (n,m)) (FUN_FMAP (λx. x - (n + 1) + (m + 1))
                                    (IMAGE ($+ (n + 1)) (count (LENGTH tds))))))
                                    (count (n + (LENGTH tds + 1)))
                                    (count (m + (LENGTH tds + 1)))’
    by (qmatch_goalsub_abbrev_tac ‘($' ft')’
        \\ ‘∀k. k < n + LENGTH tds + 1 ⇒
                if k < n then ft' ' k = ft ' k else
                if k = n then ft' ' k = m else
                ft' ' k = k + m - n’
          by (csimp [Abbr ‘ft'’, FUNION_DEF, FAPPLY_FUPDATE_THM]
              \\ rw [DISJ_EQ_IMP]
              \\ qmatch_goalsub_abbrev_tac ‘FUN_FMAP f D’
              \\ ‘k ∈ D’
                by (gs [Abbr ‘D’] \\ qexists_tac ‘k - n - 1’ \\ gs [])
              \\ ‘FINITE D’
                by gs [Abbr ‘D’]
              \\ drule_then (qspec_then ‘f’ mp_tac) FUN_FMAP_DEF \\ rw []
              \\ gs [Abbr ‘f’])
        \\ qpat_x_assum ‘INJ ($' ft) _ _’ mp_tac
        \\ rw [INJ_IFF]
        >- (
          gs [] \\ res_tac \\ fs [COND_EXPAND]
          \\ res_tac \\ fs [])
        \\ rw [EQ_IMP_THM] \\ gs []
        \\ first_assum drule_all
        \\ ntac 2 (pop_assum mp_tac)
        \\ first_x_assum drule_all
        \\ rw [] \\ gs []
        \\ res_tac \\ fs [])
  \\ first_x_assum (drule_then (qspec_then ‘m + 1’ mp_tac))
  \\ rw []
  \\ irule nsAll2_mono
  \\ first_assum (irule_at Any) \\ gs []
  \\ simp [FORALL_PROD]
  \\ rw [stamp_rel_cases]
  \\ gs [flookup_thm, FUN_FMAP_DEF, FUNION_DEF, FAPPLY_FUPDATE_THM, SF CONJ_ss]
  \\ Cases_on ‘m1 = n’ \\ gvs []
  \\ qmatch_goalsub_abbrev_tac ‘FUN_FMAP f D’
  \\ ‘m1 ∈ D’
    by (gs [Abbr ‘D’] \\ qexists_tac ‘0’ \\ gs [])
  \\ ‘FINITE D’
    by gs [Abbr ‘D’]
  \\ drule_then (qspec_then ‘f’ mp_tac) FUN_FMAP_DEF \\ rw []
  \\ gs [Abbr ‘f’]
QED

Theorem evaluate_update_decs_Dtabbrev:
  ^(get_goal "Dtabbrev")
Proof
  rw [evaluate_decs_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ simp [env_rel_def, ctor_rel_def]
QED

Theorem state_rel_declare_env[local]:
  state_rel l fr ft fe s t ⇒
    (∀env. declare_env s.eval_state env = NONE) ∧
    (∀env. declare_env t.eval_state env = NONE)
Proof
  rw [state_rel_def, declare_env_def]
QED

Theorem evaluate_update_decs_Denv:
  ^(get_goal "Denv")
Proof
  rw [evaluate_decs_def]
  \\ drule_then assume_tac state_rel_declare_env \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_update_decs_Dexn:
  ^(get_goal "Dexn")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"]]
  \\ drule_then (qspec_then ‘1’ assume_tac)
                state_rel_with_next_exn_stamp \\ gs []
  \\ first_assum (irule_at (Pat ‘state_rel’)) \\ gs []
  \\ simp [SUBMAP_FUNION_ID]
  \\ gs [env_rel_def, ctor_rel_def, stamp_rel_cases, flookup_thm,
         FUNION_DEF, state_rel_def, FUN_FMAP_DEF]
QED

Theorem evaluate_update_decs_Dmod:
  ^(get_goal "Dmod")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "result"]]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ Cases_on ‘res1’ \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_rel_def, ctor_rel_def]
QED

Theorem evaluate_update_decs_Dlocal:
  ^(get_goal "Dlocal")
Proof
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod", "result"]]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ drule_all_then assume_tac env_rel_update
  \\ Cases_on ‘res1’ \\ gs []
  >~ [‘res_rel _ _ (Rerr _) (Rerr _)’] >- (
    first_assum (irule_at Any)
    \\ gs [])
  \\ dxrule_then (drule_then assume_tac) env_rel_extend_dec_env
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
  \\ irule_at Any SUBMAP_TRANS \\ first_assum (irule_at Any) \\ gs []
QED

Theorem evaluate_update:
  ^(evaluate_update ())
Proof
  match_mp_tac (the_ind_thm ())
  \\ rpt conj_tac \\ rpt gen_tac
  \\ rewrite_tac [evaluate_update_Nil, evaluate_update_Cons,
                  evaluate_update_Lit, evaluate_update_Raise,
                  evaluate_update_Handle, evaluate_update_Con,
                  evaluate_update_Var, evaluate_update_Fun,
                  evaluate_update_App, evaluate_update_Log,
                  evaluate_update_If, evaluate_update_Mat,
                  evaluate_update_Let, evaluate_update_Letrec,
                  evaluate_update_Tannot, evaluate_update_Lannot,
                  evaluate_update_pmatch_Nil, evaluate_update_pmatch_Cons,
                  evaluate_update_decs_Nil, evaluate_update_decs_Cons,
                  evaluate_update_decs_Dlet, evaluate_update_decs_Dletrec,
                  evaluate_update_decs_Dtype,
                  evaluate_update_decs_Dtabbrev,
                  evaluate_update_decs_Denv, evaluate_update_decs_Dexn,
                  evaluate_update_decs_Dmod, evaluate_update_decs_Dlocal]
QED

(* --------------------------------------------------------------------------
 *  top-level theorem
 * -------------------------------------------------------------------------- *)

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
  rw []
  \\ drule_all_then strip_assume_tac (el 3 (CONJUNCTS evaluate_update))
  \\ first_assum (irule_at Any) \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ irule res_rel_mono
  \\ first_assum (irule_at Any) \\ rw []
  \\ irule env_rel_extend_dec_env \\ gs []
  \\ drule_all env_rel_update \\  gs []
QED

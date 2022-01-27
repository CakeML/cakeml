(*
  Lemmas used in repl_typesTheory. These lemmas show that a plain
  evaluate run can be replicated in a state with junk refs, extra type
  stamps and unused exception definitions.
*)

open preamble
open evaluateTheory semanticPrimitivesTheory evaluatePropsTheory
open namespacePropsTheory ml_progTheory
local open helperLib in end

val _ = new_theory "evaluate_skip";

val _ = numLib.prefer_num ();

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
   “v_rel fr ft fe (Loc loc) v”,
   “v_rel fr ft fe (Env env ns) v”,
   “v_rel fr ft fe v (Conv opt vs)”,
   “v_rel fr ft fe v (Closure env n x)”,
   “v_rel fr ft fe v (Recclosure env f n)”,
   “v_rel fr ft fe v (Vectorv vs)”,
   “v_rel fr ft fe v (Litv lit)”,
   “v_rel fr ft fe v (Loc loc)”,
   “v_rel fr ft fe v (Env env ns)”]
  |> map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
  |> LIST_CONJ;

Theorem env_rel_def =
  “env_rel fr ft fe env1 env2” |> SIMP_CONV std_ss [Once v_rel_cases];

Definition ref_rel_def:
  ref_rel f (Refv v)    (Refv w)    = f v w            ∧
  ref_rel f (Varray vs) (Varray ws) = LIST_REL f vs ws ∧
  ref_rel f (W8array a) (W8array b) = (a = b)          ∧
  ref_rel f _           _           = F
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

Theorem env_rel_update = CONJUNCT2 v_rel_update;

Theorem v_rel_update = CONJUNCT1 v_rel_update;

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
  cheat (* annoying *)
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
Proof
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

(* TODO this statement is wrong; fix later *)
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
                  state_rel l fr1 ft1 fe1 s1 t1 ∧
                  res_rel (v_rel fr1 ft1 fe1) (v_rel fr1 ft1 fe1) res res1)
              res res1
Proof
  cheat (*
  strip_tac
  \\ qpat_x_assum ‘do_app _ _ _ = _’ mp_tac
  \\ Cases_on ‘op = Env_id’ \\ gs []
  >- (
    rw [semanticPrimitivesPropsTheory.do_app_cases] \\ gs []
    \\ simp [Once v_rel_cases]
    v_rel
    gs [SF SFY_ss]
    \\ simp [v_ok_def, nat_to_v_def]
    \\ first_assum (irule_at Any) \\ gs [SF SFY_ss]
    )
  \\ Cases_on ‘∃chn. op = FFI chn’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ gvs [ffiTheory.call_FFI_def, store_lookup_def, store_assign_def,
            CaseEqs ["bool", "list", "option", "oracle_result",
                     "ffi$ffi_result"], EVERY_EL, EL_LUPDATE]
    \\ rw [v_ok_def, EL_APPEND_EQN]
    \\ first_assum (irule_at Any)
    \\ csimp [oEL_LUPDATE]
    \\ rw [] \\ gs [NOT_LESS, LESS_OR_EQ, ok_event_def, ref_ok_def, SF SFY_ss]
    \\ irule kernel_loc_ok_LUPDATE1 \\ gs []
    \\ strip_tac \\ gvs [v_ok_def])
  \\ Cases_on ‘op = ConfigGC’ \\ gs []
  >- (
    rw [do_app_cases, oEL_LUPDATE] \\ gs [SF SFY_ss]
    \\ simp [v_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ Cases_on ‘op = ListAppend’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ dxrule_all_then assume_tac v_ok_v_to_list
    \\ dxrule_all_then assume_tac v_ok_v_to_list
    \\ ‘EVERY (v_ok ctxt) (xs ++ ys)’
      by gs []
    \\ pop_assum mp_tac
    \\ rename1 ‘EVERY (v_ok ctxt) zs ⇒ _’
    \\ qid_spec_tac ‘zs’
    \\ Induct \\ simp [list_to_v_def, v_ok_def]
    \\ rw [] \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ Cases_on ‘op = Aw8sub_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs []
    \\ simp [v_ok_def]
    \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
  \\ Cases_on ‘op = Aw8update_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [SF CONJ_ss, oEL_LUPDATE] \\ gs [ref_ok_def, SF SFY_ss]
    \\ irule kernel_loc_ok_LUPDATE1 \\ gs []
    \\ strip_tac \\ gs [])
  \\ Cases_on ‘op = Aupdate_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ rw [] \\ gs [EVERY_EL, EL_LUPDATE, ref_ok_def]
    \\ first_assum (irule_at Any)
    \\ rw [] \\ gs []
    >- (
      irule kernel_loc_ok_LUPDATE1 \\ gs []
      \\ strip_tac \\ gvs [v_ok_def])
    \\ gvs [oEL_LUPDATE, CaseEq "bool", SF SFY_ss]
    \\ rw [ref_ok_def, EVERY_EL, EL_LUPDATE] \\ rw []
    \\ first_x_assum drule
    \\ gs [LLOOKUP_EQ_EL, ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Asub_unsafe’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [store_lookup_def, v_ok_def, LLOOKUP_EQ_EL, EVERY_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Aupdate’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ gvs [store_lookup_def, store_assign_def, EVERY_EL, EL_LUPDATE]
    \\ first_assum (irule_at Any) \\ gs [LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def, EVERY_EL, EL_LUPDATE] \\ rw []
    >- (
      irule kernel_loc_ok_LUPDATE1 \\ gs []
      \\ strip_tac \\ gvs [v_ok_def])
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = Alength’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Asub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [store_lookup_def, v_ok_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_x_assum drule_all
    \\ gs [ref_ok_def, EVERY_EL])
  \\ Cases_on ‘op = AallocEmpty’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘op = Aalloc’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘op = Vlength’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Vsub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gs [v_ok_def, EVERY_EL])
  \\ Cases_on ‘op = VfromList’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ drule_all v_ok_v_to_list
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strcat’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strlen’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Strsub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Explode’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ rename1 ‘MAP _ xs’
    \\ qid_spec_tac ‘xs’
    \\ Induct \\ simp [list_to_v_def, v_ok_def])
  \\ Cases_on ‘op = Implode’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃opb. op = Chopb opb’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘op = Chr’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Ord’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = CopyAw8Aw8’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any) \\ gs [LLOOKUP_EQ_EL]
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = CopyAw8Str’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = CopyStrAw8’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = CopyStrStr’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃n. op = WordToInt n’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃n. op = WordFromInt n’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8update’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [v_ok_def, SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [store_assign_def, EL_LUPDATE, EVERY_EL, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gvs [])
  \\ Cases_on ‘op = Aw8sub’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8length’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Aw8alloc’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ gvs [v_ok_def, store_alloc_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_assum (irule_at Any) \\ gs []
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ strip_tac
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘∃top. op = FP_top top’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃bop. op = FP_bop bop’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃uop. op = FP_uop uop’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃cmp. op = FP_cmp cmp’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘∃opn. op = Opn opn’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃opb. op = Opb opb’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘∃sz opw. op = Opw sz opw’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘∃sz sh n. op = Shift sz sh n’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [v_ok_def])
  \\ Cases_on ‘op = Equality’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ simp [Boolv_def]
    \\ rw [v_ok_def])
  \\ Cases_on ‘op = Opderef’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gs [v_ok_def, store_lookup_def, EVERY_EL, LLOOKUP_EQ_EL]
    \\ first_x_assum drule \\ gs [ref_ok_def])
  \\ Cases_on ‘op = Opassign’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [v_ok_def, store_assign_def, EVERY_EL, EL_LUPDATE, LLOOKUP_EQ_EL]
    \\ rw [ref_ok_def]
    \\ irule kernel_loc_ok_LUPDATE1
    \\ rpt strip_tac \\ gs [])
  \\ Cases_on ‘op = Opref’ \\ gs []
  >- (
    rw [do_app_cases] \\ gs [SF SFY_ss]
    \\ first_assum (irule_at Any)
    \\ gvs [v_ok_def, store_alloc_def, ref_ok_def, LLOOKUP_EQ_EL]
    \\ rw [DISJ_EQ_IMP] \\ rpt strip_tac
    >- (
      gs [kernel_loc_ok_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
      \\ first_x_assum (drule_then strip_assume_tac)
      \\ rw [] \\ gs [SF SFY_ss])
    \\ rw [EL_APPEND_EQN] \\ gs [NOT_LESS, LESS_OR_EQ, ref_ok_def]
    \\ first_x_assum (drule_then assume_tac)
    \\ drule kernel_loc_ok_LENGTH \\ gs [])
  \\ Cases_on ‘op’ \\ gs [] *)
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

Theorem evaluate_update_Op:
  op ≠ Opapp ∧ op ≠ Eval ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["prod", "result", "option"], PULL_EXISTS]
  \\ first_x_assum (drule_all_then strip_assume_tac)
  \\ Cases_on ‘res1’ \\ gs []
  \\ first_assum (irule_at Any) \\ gs []
  \\ dxrule_then assume_tac EVERY2_REVERSE
  \\ drule_all_then strip_assume_tac do_app_update
  \\ gs [OPTREL_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ first_assum (irule_at Any)
  \\ first_assum (irule_at Any)
  \\ irule_at Any res_rel_list_result
  \\ rename1 ‘res_rel _ _ r1 r2’
  \\ Cases_on ‘r1’ \\ Cases_on ‘r2’ \\ gs []
  \\ cheat (* fix later when do_app theorem is correct *)
QED

Theorem evaluate_update_Opapp:
  op = Opapp ⇒ ^(get_goal "App")
Proof
  rw [evaluate_def]
  \\ gvs [CaseEqs ["option", "prod", "result", "bool"], PULL_EXISTS]
  >~ [‘do_opapp _ = NONE’] >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ Cases_on ‘res1’ \\ gs []
    \\ cheat (* do_opapp *))
  >~ [‘s.clock = 0’] >- (
    first_x_assum (drule_all_then strip_assume_tac)
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs []
    \\ Cases_on ‘res1’ \\ gs []
    \\ cheat (* do_opapp *))
  \\ first_x_assum (drule_all_then strip_assume_tac) \\ gs []
  \\ Cases_on ‘res1’ \\ gs []
  \\ cheat (* do_opapp *)
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
  \\ simp [ELIM_UNCURRY, v_rel_def]
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

Theorem evaluate_update_decs_Dlet:
  ^(get_goal "Dlet")
Proof
  rw [evaluate_decs_def]
  >~ [‘¬ALL_DISTINCT _’] >- (
    first_assum (irule_at Any) \\ gs [SF SFY_ss])
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
  rw [evaluate_decs_def]
  >~ [‘¬ALL_DISTINCT _’] >- (
    first_assum (irule_at Any) \\ gs [])
  \\ gvs [CaseEqs ["prod", "result"], PULL_EXISTS]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_rel_def, ctor_rel_def, PULL_EXISTS, SF SFY_ss,
         semanticPrimitivesPropsTheory.build_rec_env_merge]
  \\ irule_at Any nsAll2_alist_to_ns
  \\ gs [EVERY2_MAP, LAMBDA_PROD]
  \\ rw [v_rel_def, LIST_REL_EL_EQN, ELIM_UNCURRY]
QED

Theorem evaluate_update_decs_Dtype:
  ^(get_goal "Dtype")
Proof
  cheat (*
  rw [evaluate_decs_def]
  >~ [‘¬EVERY check_dup_ctors _’] >- (
    gs [state_ok_def]
    \\ first_assum (irule_at Any) \\ gs [])
  \\ gvs [CaseEqs ["prod", "semanticPrimitives$result"], state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ conj_tac
  >- (
    rw []
    \\ first_x_assum drule \\ gs [])
  \\ gs [extend_dec_env_def, build_tdefs_def, env_ok_def,
         nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, SF SFY_ss]
  \\ rw [] \\ gs [SF SFY_ss]
  \\ ‘∀m tds n l t k.
        nsLookup (build_tdefs m tds) n = SOME (l, TypeStamp t k) ⇒
          m ≤ k’
    by (ho_match_mp_tac build_tdefs_ind
        \\ simp [build_tdefs_def, nsLookup_nsAppend_some,
                 nsLookup_alist_to_ns_some, SF SFY_ss]
        \\ rw [] \\ gs [SF SFY_ss]
        >- (
          first_x_assum drule
          \\ gs [])
        \\ drule_then assume_tac ALOOKUP_MEM
        \\ gs [build_constrs_def, MEM_MAP, EXISTS_PROD])
  \\ first_x_assum (drule_then assume_tac)
  \\ first_x_assum drule_all \\ gs [] *)
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
  cheat (*
  rw [evaluate_decs_def]
  \\ gvs [CaseEqs ["option", "prod"], state_ok_def]
  \\ first_assum (irule_at Any) \\ gs []
  \\ gs [env_ok_def, extend_dec_env_def, SF SFY_ss]
  \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
  \\ rw [] \\ gs [SF SFY_ss] *)
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
 *
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

Theorem evaluate_decs_init:
  evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,Rval env) ⇒
  ∃fr ft fe.
     fr = FUN_FMAP I (count (LENGTH s.refs)) ∧
     ft = FUN_FMAP I (count s.next_type_stamp) ∧
     fe = FUN_FMAP I (count s.next_exn_stamp) ∧
     state_rel (LENGTH s.refs) fr ft fe s s ∧
     env_rel fr ft fe (extend_dec_env env init_env)
                      (extend_dec_env env init_env)
Proof
  cheat (* deal with this separately *)
QED

val _ = export_theory();


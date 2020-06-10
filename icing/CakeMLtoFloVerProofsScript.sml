(*
  Central theorem about connection to FloVer
*)
(* HOL4 *)
open machine_ieeeTheory realTheory realLib RealArith;
(* CakeML *)
open semanticPrimitivesTheory terminationTheory compilerTheory;
(* FloVer *)
open ExpressionsTheory ExpressionSemanticsTheory CommandsTheory
     EnvironmentsTheory IEEE_connectionTheory
     FloverMapTheory TypeValidatorTheory;
(* Icing *)
open CakeMLtoFloVerTheory CakeMLtoFloVerLemsTheory;
open preamble;

val _ = new_theory "CakeMLtoFloVerProofs";

(* TODO: Move to HOL4 distrib *)
Theorem float_is_finite_sandwich:
  ∀ (w1:('a,'b) float) (w2:('a,'b) float) (w3:('a,'b) float).
  float_less_equal w1 w2 ∧
  float_less_equal w2 w3 ∧
  float_is_finite w1 ∧
  float_is_finite w3 ⇒
  float_is_finite w2
Proof
  rpt strip_tac
  \\ fs[binary_ieeeTheory.float_is_finite_def,
        binary_ieeeTheory.float_less_equal_def]
  \\ Cases_on ‘float_value w1’ \\ fs[]
  \\ Cases_on ‘float_value w3’ \\ fs[]
  \\ Cases_on ‘float_compare w1 w2’ \\ fs[]
  \\ Cases_on ‘float_compare w2 w3’ \\ rfs[binary_ieeeTheory.float_compare_def]
  \\ Cases_on ‘float_value w2’ \\ fs[]
  \\ Cases_on ‘w2.Sign = 1w’ \\ fs[]
QED

Theorem fp64_isFinite_sandwich:
  ∀ w1 w2 w3.
    fp64_lessEqual w1 w2 ∧
    fp64_lessEqual w2 w3 ∧
    fp64_isFinite w1 ∧
    fp64_isFinite w3 ⇒
    fp64_isFinite w2
Proof
  fs[fp64_lessEqual_def, fp64_isFinite_def]
  \\ rpt strip_tac
  \\ irule float_is_finite_sandwich
  \\ fsrw_tac [SATISFY_ss] []
QED

Theorem closest_such_0:
  ∀ (f:('a, 'b) float).
  closest_such (λ a. ~word_lsb a.Significand) float_is_finite 0 = f ⇒
  f = float_plus_zero (:'a # 'b) ∨ f = float_minus_zero (:'a # 'b)
Proof
  rpt strip_tac \\ rveq
  \\ fs[binary_ieeeTheory.closest_such_def]
  \\ SELECT_ELIM_TAC \\ rpt strip_tac
  >- (
    fs[binary_ieeeTheory.is_closest_def]
    \\ qexists_tac ‘float_plus_zero (:'a # 'b)’
    \\ fs[binary_ieeeTheory.float_is_finite, IN_DEF,
          binary_ieeeTheory.zero_properties, binary_ieeeTheory.zero_to_real,
          ABS_POS]
    \\ rpt strip_tac
    \\ fs[wordsTheory.word_lsb_def, binary_ieeeTheory.float_plus_zero_def]
    \\ pop_assum (fn thm => assume_tac (EVAL_RULE thm)) \\ fs[])
  \\ fs[binary_ieeeTheory.is_closest_def]
  \\ last_x_assum (qspec_then ‘float_plus_zero (:'a # 'b)’ mp_tac)
  \\ simp[binary_ieeeTheory.float_is_finite, IN_DEF,
          binary_ieeeTheory.zero_properties, binary_ieeeTheory.zero_to_real,
          ABS_POS]
  \\ rpt strip_tac
  \\ ‘float_is_zero x’ by (fs[binary_ieeeTheory.float_is_zero_to_real])
  \\ fs[binary_ieeeTheory.float_is_zero, binary_ieeeTheory.float_plus_zero_def,
        binary_ieeeTheory.float_minus_zero_def]
  \\ Cases_on ‘x’ \\ Cases_on ‘c’ \\ Cases_on ‘n’ \\ fs[]
  \\ TRY (rename1 ‘SUC n < 2’ \\ Cases_on ‘n’)
  \\ fs[binary_ieeeTheory.float_negate_def, binary_ieeeTheory.float_component_equality]
QED

Definition v_word_eq_def:
  v_word_eq (FP_WordTree fp) w = (compress_word fp = w) ∧
  v_word_eq (Litv (Word64 w1)) w2 = (w1 = w2) ∧
  v_word_eq _ _ = F
End

(**
  Relation: env_word_sim
  Arguments:
    The CakeML environment env, the FloVer environment E, and a set of pairs of
    CakeML * FloVer variables, and a type environment Gamma
  The environments env and E are in relation with each other for the set of
  variables fVars under the type assignment Gamma,
  if and only if for every pair of variables (cake_id, flover_id):
  if the CakeML environment binds cake_id, the FloVer environment must bind
  flover_id to a value r that is in relation with the CakeML value for the type
  in Gamma, and
  if the FloVer environment binds flover_id, and has a type in Gamma, the
  the CakeML environment binds the variable cake_id to a value that is in
  relation with the FloVer value under the type from Gamma **)
Definition env_word_sim_def:
  env_word_sim env (E:num -> word64 option) fVars =
    (∀ (cake_id:(string, string) id) (flover_id:num).
     (cake_id, flover_id) IN fVars ⇒
      (∀ v.
        nsLookup env cake_id = SOME v ⇒
        ∃ r. E flover_id = SOME r ∧ v_word_eq v r) ∧
      (∀ r.
       E flover_id = SOME r ⇒
        ∃ v. nsLookup env cake_id = SOME v ∧ v_word_eq v r))
End

Theorem env_word_sim_inhabited:
  (∀ x y. (x,y) IN fVars ⇒ lookupFloVerVar y ids = SOME (x,y)) ∧
  (∀ x y. (x,y) IN fVars ⇒
   ∃ fp. nsLookup env x = SOME (FP_WordTree fp) ∨ ∃ w. nsLookup env x = SOME (Litv (Word64 w)))⇒
  env_word_sim env
  (λ x. case lookupFloVerVar x ids of
   |NONE => NONE
   |SOME (cakeId, _) =>
   case nsLookup env cakeId of
   |SOME (Litv (Word64 w)) => SOME w
   |SOME (FP_WordTree fp) => SOME (compress_word fp)
   | _ => NONE) fVars
Proof
  rpt strip_tac \\ fs[env_word_sim_def]
  \\ rpt strip_tac \\ res_tac \\ fs[] \\ rveq \\ fs[option_case_eq, v_word_eq_def]
QED

(**
  Relation: v_eq
  Arguments:
    The CakeML value v, a real number r, and a FloVer type m.
  The predicate returns true, iff either m is REAL, and v represents exactly the
  real number r, or m is M64 for a 64-bit double number, v is a double value or
  a value tree, and r is the translation to reals of v. **)
Definition v_eq_def:
  v_eq (FP_WordTree fp) r M64 = (r = fp64_to_real (compress_word fp)) ∧
  v_eq (Litv (Word64 w)) r M64 = (r = fp64_to_real w) ∧
  v_eq (Real r1) r2 REAL = (r1 = r2) ∧
  v_eq _ _ _ = F
End

Triviality v_eq_float:
  v_eq (Litv (Word64 w)) r m ⇔ ((m = M64) ∧ r = fp64_to_real w)
Proof
  Cases_on ‘m’ \\ fs[v_eq_def]
QED

Triviality v_eq_valtree:
  v_eq (FP_WordTree fp) r m ⇔ ((m = M64) ∧ r = fp64_to_real (compress_word fp))
Proof
  Cases_on ‘m’ \\ fs[v_eq_def]
QED

Triviality v_eq_real:
  v_eq v r REAL ⇔ v = Real r
Proof
  Cases_on ‘v’ \\ fs[v_eq_def]
QED

(**
  Relation: env_sim
  Arguments:
    The CakeML environment env, the FloVer environment E, and a set of pairs of
    CakeML * FloVer variables, and a type environment Gamma
  The environments env and E are in relation with each other for the set of
  variables fVars under the type assignment Gamma,
  if and only if for every pair of variables (cake_id, flover_id):
  if the CakeML environment binds cake_id, the FloVer environment must bind
  flover_id to a value r that is in relation with the CakeML value for the type
  in Gamma, and
  if the FloVer environment binds flover_id, and has a type in Gamma, the
  the CakeML environment binds the variable cake_id to a value that is in
  relation with the FloVer value under the type from Gamma **)
Definition env_sim_def:
  env_sim env E fVars (Gamma:(real expr -> mType option)) =
    (∀ (cake_id:(string, string) id) (flover_id:num).
     (cake_id, flover_id) IN fVars ⇒
      (∀ v.
        nsLookup env cake_id = SOME v ⇒
        ∃ r m. E flover_id = SOME r ∧ Gamma (Var flover_id) = SOME m ∧ v_eq v r m) ∧
      (∀ r m.
       E flover_id = SOME r ∧
       Gamma (Var flover_id) = SOME m ⇒
        ∃ v. nsLookup env cake_id = SOME v ∧ v_eq v r m))
End

Definition type_correct_def:
  type_correct (Real r) REAL = T ∧
  type_correct (FP_WordTree fp) M64 = T ∧
  type_correct (Litv (Word64 w)) M64 = T ∧
  type_correct _ _ = F
End

(**
  Relation: env_sim_real
  Arguments:
    The CakeML environment env, the FloVer environment E, and a set of pairs of
    CakeML * FloVer variables, and a type environment Gamma
  The environments env and E are in relation with each other for the set of
  variables fVars under the type assignment Gamma,
  if and only if for every pair of variables (cake_id, flover_id):
  if the CakeML environment binds cake_id, the FloVer environment must bind
  flover_id to a value r that is in relation with the CakeML value for the type
  in Gamma, and
  if the FloVer environment binds flover_id, and has a type in Gamma, the
  the CakeML environment binds the variable cake_id to a value that is in
  relation with the FloVer value under the type from Gamma **)
Definition env_sim_real_def:
  env_sim_real env E fVars =
    (∀ (cake_id:(string, string) id) (flover_id:num).
     (cake_id, flover_id) IN fVars ⇒
      (∀ v.
        nsLookup env cake_id = SOME v ⇒
        ∃ r. E flover_id = SOME r ∧ v_eq v r REAL) ∧
      (∀ r.
       E flover_id = SOME r ⇒
        ∃ v. nsLookup env cake_id = SOME v ∧ v_eq v r REAL))
End

Definition toRspace_def:
  toRspace env =
  nsMap (λ (x:v). case x of
         |Litv (Word64 w) => Real (fp64_to_real w)
         | FP_WordTree fp => Real (fp64_to_real (compress_word fp))
         | _ => x) env
End

Theorem env_sim_real_from_word_sim:
  ∀ env Ed fVars.
  env_word_sim env Ed fVars ⇒
  env_sim_real (toRspace env)
          (λ x. case Ed x of SOME w => SOME (fp64_to_real w) | _ => NONE)
          fVars
Proof
  rpt strip_tac \\ fs[env_word_sim_def, env_sim_real_def, toRspace_def,
                     namespacePropsTheory.nsLookup_nsMap]
  \\ rpt strip_tac \\ res_tac \\ fs[type_correct_def] \\ rveq
  >- (
   rename1 ‘v_word_eq v r’ \\ Cases_on ‘v’
   \\ fs[v_word_eq_def, ExpressionAbbrevsTheory.toRTMap_def]
   \\ TRY (rename1 ‘v_word_eq (Litv l) r’ \\ Cases_on ‘l’ \\ fs[v_word_eq_def])
   \\ rveq \\ fs[type_correct_def, v_eq_def])
  \\ fs[option_case_eq] \\ rveq \\ res_tac
  \\ Cases_on ‘v’ \\ fs[v_word_eq_def]
   \\ TRY (rename1 ‘v_word_eq (Litv l) r’ \\ Cases_on ‘l’ \\ fs[v_word_eq_def])
   \\ rveq \\ fs[type_correct_def, v_eq_def]
QED

Theorem approxEnv_construct:
  ∀ E1 Gamma A fVars.
    (∀ x. ~ (x  IN domain fVars) ⇒ E1 x = NONE) ∧
    (∀ x. x IN domain fVars ⇒ Gamma (Var x) = SOME M64) ∧
    (∀ x. x IN domain fVars ⇒ ∃ v. E1 x = SOME v) ∧
    (∀ x v. E1 x = SOME v ⇒ (normalizes (:52 # 11) v ∨ v = 0)) ⇒
    approxEnv E1
              Gamma A fVars LN
              (toREnv
               (λ n. case E1 n of
                |NONE => NONE
                | SOME v => SOME (float_to_fp64 (round roundTiesToEven v))))
Proof
  fs[approxEnv_def] \\ rpt strip_tac
  >- (
    res_tac \\ fs[toREnv_def])
  \\ res_tac \\ fs[toREnv_def]
  \\ simp[fp64_to_float_float_to_fp64]
  \\ ‘normalizes (:52 # 11) v ∨ v = 0’
    by (first_x_assum irule \\ fsrw_tac [SATISFY_ss] [])
  >- (
    imp_res_tac lift_ieeeTheory.relative_error
    \\ simp[MachineTypeTheory.computeError_def, MachineTypeTheory.mTypeToR_def]
    \\ rewrite_tac [REAL_LDISTRIB, REAL_MUL_RID, real_sub, REAL_NEG_ADD,
                    REAL_ADD_ASSOC]
    \\ fs[ABS_NEG, ABS_MUL]
    \\ irule REAL_LE_RMUL_IMP \\ fs[ABS_POS])
  \\ rveq \\ fs[binary_ieeeTheory.round_def, binary_ieeeTheory.threshold]
  \\ Q.ISPEC_THEN ‘f:(52,11) float’
                  (assume_tac o SIMP_RULE std_ss [] o GEN_ALL) closest_such_0
  \\ fs[binary_ieeeTheory.zero_to_real, MachineTypeTheory.computeError_def]
QED

Theorem buildFloVerTypeMap_is_64Bit:
  ∀ floverVars. is64BitEnv (buildFloVerTypeMap floverVars)
Proof
  Induct_on ‘floverVars’
  \\ fs[buildFloVerTypeMap_def, is64BitEnv_def,
        FloverMapTree_empty_def, FloverMapTree_find_def, map_find_add]
  \\ rpt strip_tac \\ every_case_tac \\ rveq
  \\ fs[ExpressionAbbrevsTheory.toRExpMap_def, FloverMapTheory.map_find_add]
  \\ res_tac
QED

Theorem eval_expr_real:
  ∀ Gamma E e v m.
  (∀ x m. Gamma x = SOME m ⇒ m = REAL) ∧
  eval_expr E Gamma (toREval e) v m ⇒
  m = REAL
Proof
  Induct_on ‘e’ \\ rpt strip_tac
  \\ fs[Once toREval_def, Once eval_expr_cases] \\ rveq
  \\ res_tac
QED

Theorem CakeML_FloVer_real_sim_exp:
  ∀ varMap f theExp freshId E env fVars (st:'ffi semanticPrimitives$state) Gamma v.
    toFloVerExp varMap f = SOME theExp ∧
    ids_unique varMap freshId ∧
    st.fp_state.real_sem ∧
    env_sim_real env.v E fVars ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
    eval_expr E (toRTMap Gamma) (toREval (toRExp theExp)) v REAL ⇒
    evaluate st env [realify f] = (st, Rval [Real v])
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  \\ rveq \\ fs[realify_def, freevars_def]
  \\ rfs[] \\ rveq \\ fs [toRExp_def, toREval_def, eval_expr_cases]
  >- (
    fs[env_sim_real_def] \\ rveq
    \\ fs[ExpressionAbbrevsTheory.toRExpMap_def,
          ExpressionAbbrevsTheory.toRTMap_def, option_case_eq]
    \\ simp[evaluate_def] \\ res_tac \\ fs[v_eq_real])
  >- (
    simp[realify_def, evaluate_def, astTheory.getOpClass_def]
    \\ fs[MachineTypeTheory.mTypeToR_def, perturb_def] \\ rveq
    \\ simp[do_app_def, fp64_to_real_def, state_component_equality])
  >- (
    rveq \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[freevars_def]
    \\ Cases_on ‘m'’ \\ fs[MachineTypeTheory.isCompat_def]
    \\ ‘evaluate st env [realify e] = (st, Rval [Real v1])’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ fs[MachineTypeTheory.isCompat_def])
    \\ simp[realify_def, evaluate_def, astTheory.getOpClass_def,
            getRealUop_def]
    \\ fs[do_app_def] \\ EVAL_TAC \\ fs[state_component_equality])
  >- (
    rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[freevars_def]
    \\ ‘m1 = REAL ∧ m2 = REAL’
       by (
         conj_tac \\ irule eval_expr_real
         \\ once_rewrite_tac[CONJ_COMM] \\ asm_exists_tac \\ fs[]
         \\ rpt strip_tac
         \\ Cases_on ‘x’
         \\ fs[ExpressionAbbrevsTheory.toRTMap_def, option_case_eq])
    \\ rveq
    \\ ‘evaluate st env [realify e2] = (st, Rval [Real v2])’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspecl_then [‘Gamma’, ‘v2’] mp_tac) \\ impl_tac \\ fs[])
    \\ ‘evaluate st env [realify e1] = (st, Rval [Real v1])’
      by (
        last_x_assum kall_tac
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspecl_then [‘Gamma’, ‘v1’] mp_tac) \\ impl_tac \\ fs[])
    \\ simp[evaluate_def, astTheory.getOpClass_def, semanticPrimitivesTheory.do_app_def]
    \\ fs[MachineTypeTheory.mTypeToR_def, perturb_def]
    \\ Cases_on ‘bop’ \\ EVAL_TAC \\ fs[state_component_equality])
  >- (
    rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[freevars_def]
    \\ ‘m1 = REAL ∧ m2 = REAL ∧ m3 = REAL’
       by (
         rpt conj_tac \\ irule eval_expr_real
         \\ once_rewrite_tac[CONJ_COMM] \\ asm_exists_tac \\ fs[]
         \\ rpt strip_tac
         \\ Cases_on ‘x’
         \\ fs[ExpressionAbbrevsTheory.toRTMap_def, option_case_eq])
    \\ rveq
    \\ ‘∀ (st:'ffi semanticPrimitives$state). st.fp_state.real_sem ⇒
        evaluate st env [realify e3] = (st, Rval [Real v2])’
      by (
        rpt strip_tac
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspecl_then [‘Gamma’, ‘v2’] mp_tac)
        \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∀ (st:'ffi semanticPrimitives$state). st.fp_state.real_sem ⇒
        evaluate st env [realify e2] = (st, Rval [Real v1])’
      by (
        rpt strip_tac
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspecl_then [‘Gamma’, ‘v1’] mp_tac) \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∀ (st:'ffi semanticPrimitives$state). st.fp_state.real_sem ⇒
        evaluate st env [realify e1] = (st, Rval [Real v3])’
      by (
        rpt strip_tac
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspecl_then [‘Gamma’, ‘v3’] mp_tac) \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ first_x_assum (qspec_then ‘st’ mp_tac) \\ impl_tac \\ fs[]
    \\ strip_tac \\ fs[]
    \\ last_x_assum (qspec_then ‘st’ mp_tac) \\ impl_tac \\ fs[]
    \\ strip_tac \\ fs[]
    \\ last_x_assum (qspec_then ‘st’ mp_tac) \\ impl_tac \\ fs[]
    \\ strip_tac \\ fs[]
    \\ simp[evaluate_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ simp[semanticPrimitivesTheory.shift_fp_opts_def]
    \\ fs[MachineTypeTheory.mTypeToR_def, perturb_def]
    \\ EVAL_TAC \\ fs[state_component_equality])
  >- (
   simp[terminationTheory.evaluate_def]
   \\ qmatch_goalsub_abbrev_tac ‘evaluate stUpd env [realify f]’
   \\ ‘stUpd.fp_state.real_sem’
     by (unabbrev_all_tac \\ TOP_CASE_TAC
         \\ fs[state_component_equality, fpState_component_equality])
   \\ first_x_assum drule
   \\ rpt (disch_then drule)
   \\ strip_tac \\ unabbrev_all_tac
   \\ fs[do_fpoptimise_def, state_component_equality, fpState_component_equality]
   \\ TOP_CASE_TAC \\ fs[])
QED

Theorem CakeML_FloVer_real_sim:
  ∀ varMap freshId f theIds freshId2 theCmd E env fVars (st:'ffi semanticPrimitives$state) Gamma r.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
    ids_unique varMap freshId ∧
    st.fp_state.real_sem ∧
    env_sim_real env.v E fVars ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
    bstep (toREvalCmd (toRCmd theCmd)) E (toRTMap Gamma) r REAL ⇒
    evaluate st env [realify f] = (st, Rval [Real r])
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def]
  >- (
   fs[option_case_eq, pair_case_eq] \\ rveq
   \\ qpat_x_assum ‘bstep _ _ _ _ _’ mp_tac
   \\ simp[Once toRCmd_def, Once toREvalCmd_def, bstep_cases, freevars_def]
   \\ rpt strip_tac
   \\ drule CakeML_FloVer_real_sim_exp \\ rpt (disch_then drule)
   \\ disch_then (qspecl_then [‘Gamma’, ‘v’] mp_tac)
   \\ impl_tac \\ fs[freevars_def]
   \\ disch_then assume_tac \\ fs[]
   \\ qpat_assum ‘bstep _ _ _ _ _’
                   (fn thm => first_x_assum (fn ithm => mp_then Any mp_tac ithm thm))
   \\ disch_then
      (qspecl_then [‘env with v := (nsOptBind (SOME x) (Real v) env.v)’,
                    ‘fVars UNION { (Short x,freshId)}’,
                    ‘st’] mp_tac)
   \\ impl_tac
   >- (
     rpt conj_tac \\ fs[]
     >- (
       irule ids_unique_append \\ asm_exists_tac \\ fs[])
     >- (
       simp[env_sim_real_def] \\ rpt strip_tac \\ fs[namespaceTheory.nsOptBind_def]
       >- (
         ‘cake_id ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘flover_id ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ fs[env_sim_real_def] \\ res_tac
         \\ fsrw_tac [SATISFY_ss] []
         \\ res_tac \\ fs[])
       >- (
         ‘cake_id ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘flover_id ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ fs[ml_progTheory.nsLookup_nsBind_compute]
         \\ fs[env_sim_real_def] \\ res_tac
         \\ fsrw_tac [SATISFY_ss] []
         \\ res_tac \\ rfs[])
       >- (
         rveq \\ fs[ml_progTheory.nsLookup_nsBind_compute]
         \\ rveq  \\ fs[v_eq_def])
       \\ rveq \\ fs[] \\ rveq \\ fs[v_eq_def])
     >- (
      rpt strip_tac
      >- (
        fs[lookupCMLVar_appendCMLVar]
        \\ ‘x' ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘y ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ res_tac
         \\ fs[lookupCMLVar_def, updateTheory.FIND_def])
      \\ rveq \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def])
     >- (
       rpt strip_tac
       \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def]
       \\ TOP_CASE_TAC \\ fs[]
       \\ first_x_assum (qspec_then ‘x'’ mp_tac) \\ fs[]
       \\ disch_then assume_tac \\ fs[]
       \\ fs[]))
    \\ disch_then assume_tac \\ fs[]
    \\ simp[realify_def, evaluate_def])
  \\ TRY (
     fs[option_case_eq, pair_case_eq] \\ rveq
     \\ fs[Once toRCmd_def, Once toREvalCmd_def, bstep_cases] \\ rveq
     \\ drule CakeML_FloVer_real_sim_exp \\ fs[]
     \\ rpt (disch_then drule) \\ fs[])
  \\ simp[realify_def, terminationTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate stUpd env [realify f]’
  \\ ‘stUpd.fp_state.real_sem’ by (unabbrev_all_tac \\ TOP_CASE_TAC \\ fs[])
  \\ first_x_assum drule
  \\ fs[freevars_def]
  \\ rpt (disch_then drule)
  \\ strip_tac \\ unabbrev_all_tac
  \\ fs[do_fpoptimise_def, state_component_equality, fpState_component_equality]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem CakeML_FloVer_float_sim_exp:
  ∀ varMap f theExp freshId E env fVars (st:'ffi semanticPrimitives$state) vF.
    toFloVerExp varMap f = SOME theExp ∧
    st.fp_state.canOpt = FPScope NoOpt ∧
    ids_unique varMap freshId ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    env_word_sim env.v E fVars ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
    eval_expr_float theExp E = SOME vF ⇒
    ∃ vFC. evaluate st env [f] = (st, Rval [vFC]) ∧ v_word_eq vFC vF
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ fs[eval_expr_float_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[env_word_sim_def]
    \\ res_tac \\ rveq \\ fs[] \\ rveq
    \\ simp[evaluate_def])
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum `T` kall_tac)
    \\ fs[eval_expr_float_def] \\ rveq \\ fs[]
    \\ simp[evaluate_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def, fpSemTheory.compress_word_def,
            state_component_equality,
            v_word_eq_def])
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[eval_expr_float_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[]
    \\ ‘∃ vFC. evaluate st env [e] = (st, Rval [vFC]) ∧
        v_word_eq vFC v’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then assume_tac \\ fs[])
    \\ simp[evaluate_def, v_eq_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ Cases_on ‘vFC’
    \\ TRY (rename1 ‘v_word_eq (Litv l) v’ \\ Cases_on ‘l’)
    \\ fs[v_word_eq_def] \\ rveq
    \\ fs[v_word_eq_def, semanticPrimitivesTheory.fp_translate_def,
          astTheory.isFpBool_def, fpValTreeTheory.fp_uop_def,
          state_component_equality,
          fpSemTheory.compress_word_def]
    \\ EVAL_TAC)
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[eval_expr_float_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[]
    \\ ‘∃ vFC. evaluate st env [e2] = (st, Rval [vFC]) ∧
        v_word_eq vFC v2’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v2’ mp_tac) \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∃ vFC. evaluate st env [e1] = (st, Rval [vFC]) ∧
        v_word_eq vFC v1’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v1’ mp_tac) \\ impl_tac \\ fs[])
    \\ simp[evaluate_def, v_eq_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ Cases_on ‘vFC'’ \\ Cases_on ‘vFC’
    \\ TRY (rename1 ‘v_word_eq (Litv l1) v1’ \\ Cases_on ‘l1’)
    \\ TRY (rename1 ‘v_word_eq (Litv l2) v2’ \\ Cases_on ‘l2’)
    \\ fs[v_word_eq_def, semanticPrimitivesTheory.fp_translate_def,
          astTheory.isFpBool_def, fpValTreeTheory.fp_uop_def,
          state_component_equality,
          fpSemTheory.compress_word_def]
    \\ rveq \\ Cases_on ‘bop’ \\ fs[fpBopToFloVer_def, dmode_def] \\ rveq
    \\ fs[fpValTreeTheory.fp_bop_def, fpSemTheory.compress_word_def]
    \\ EVAL_TAC)
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[eval_expr_float_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[]
    \\ ‘∃ vFC. evaluate st env [e3] = (st, Rval [vFC]) ∧
        v_word_eq vFC v2’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v2’ mp_tac) \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∃ vFC. evaluate st env [e2] = (st, Rval [vFC]) ∧
        v_word_eq vFC v1’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v1’ mp_tac) \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∃ vFC. evaluate st env [e1] = (st, Rval [vFC]) ∧
        v_word_eq vFC v3’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v3’ mp_tac) \\ impl_tac \\ fs[])
    \\ simp[evaluate_def, v_eq_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ Cases_on ‘vFC'’ \\ Cases_on ‘vFC’ \\ Cases_on ‘vFC''’
    \\ TRY (rename1 ‘v_word_eq (Litv l1) v1’ \\ Cases_on ‘l1’)
    \\ TRY (rename1 ‘v_word_eq (Litv l2) v2’ \\ Cases_on ‘l2’)
    \\ TRY (rename1 ‘v_word_eq (Litv l3) v3’ \\ Cases_on ‘l3’)
    \\ fs[v_word_eq_def, semanticPrimitivesTheory.fp_translate_def,
          astTheory.isFpBool_def, fpValTreeTheory.fp_uop_def,
          state_component_equality,
          fpSemTheory.compress_word_def]
    \\ rveq
    \\ fs[fpValTreeTheory.fp_top_def, fpSemTheory.compress_word_def]
    \\ EVAL_TAC)
  >- (
   simp[terminationTheory.evaluate_def]
   \\ qmatch_goalsub_abbrev_tac ‘evaluate stUpd env [f]’
   \\ ‘stUpd.fp_state.canOpt = FPScope NoOpt’
      by (unabbrev_all_tac \\ fs[])
   \\ first_x_assum drule
   \\ rpt (disch_then drule)
   \\ disch_then (qspec_then ‘vF’ mp_tac)
   \\ impl_tac
   >- (fs[freevars_def])
   \\ strip_tac \\ fs[]
   \\ Cases_on ‘vFC’ \\ TRY (Cases_on ‘l’)
   \\ unabbrev_all_tac
   \\ fs[v_word_eq_def, do_fpoptimise_def, state_component_equality,
         fpState_component_equality, fpSemTheory.compress_word_def])
QED

Theorem CakeML_FloVer_float_sim:
  ∀ varMap freshId f theIds freshId2 theCmd E env fVars (st:'ffi semanticPrimitives$state) vF.
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
  st.fp_state.canOpt = FPScope NoOpt ∧
  ids_unique varMap freshId ∧
  (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
  env_word_sim env.v E fVars ∧
  (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
  bstep_float theCmd E = SOME vF ⇒
  ∃ vFC. evaluate st env [f] = (st, Rval [vFC]) ∧
    v_word_eq vFC vF
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def]
  >- (
   fs[option_case_eq, pair_case_eq, freevars_def] \\ rveq
   \\ fs[bstep_float_def]
   \\ Cases_on ‘eval_expr_float fexp1 E’ \\ fs[optionLift_def]
   \\ rename1 ‘eval_expr_float fexp1 E = SOME w1’
   \\ ‘∃vF1. evaluate st env [e1] = (st, Rval [vF1]) ∧ v_word_eq vF1 w1’
     by (drule CakeML_FloVer_float_sim_exp
         \\ rpt (disch_then drule)
         \\ disch_then (qspec_then ‘w1’ mp_tac) \\ impl_tac
         \\ rpt strip_tac \\ fs[])
   \\ simp[evaluate_def]
   \\ first_x_assum drule \\ rpt (disch_then drule)
   \\ disch_then (qspecl_then [‘updFlEnv freshId w1 E’,
                               ‘env with v := nsOptBind (SOME x) vF1 env.v’,
                               ‘fVars UNION { (Short x, freshId) }’,
                               ‘vF’] mp_tac)
   \\ reverse (impl_tac)
   >- (strip_tac \\ fsrw_tac [SATISFY_ss] [])
   \\ rpt conj_tac
   >- (
     irule ids_unique_append \\ fs[])
   >- (
     rpt strip_tac \\ fs[]
     >- (
       fs[lookupCMLVar_appendCMLVar]
        \\ ‘x' ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘y ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
       \\ res_tac
       \\ fs[lookupCMLVar_def, updateTheory.FIND_def])
     \\ rveq \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def])
   >- (
       simp[env_word_sim_def] \\ rpt strip_tac \\ fs[namespaceTheory.nsOptBind_def]
       >- (
         ‘cake_id ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘flover_id ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ fs[env_word_sim_def] \\ res_tac
         \\ fsrw_tac [SATISFY_ss] []
         \\ res_tac \\ fs[updFlEnv_def])
       >- (
         ‘cake_id ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘flover_id ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ fs[ml_progTheory.nsLookup_nsBind_compute]
         \\ fs[env_word_sim_def] \\ res_tac
         \\ fsrw_tac [SATISFY_ss] []
         \\ res_tac \\ rfs[updFlEnv_def] \\ fs[])
       >- (
         rveq \\ fs[ml_progTheory.nsLookup_nsBind_compute]
         \\ rveq \\ fs[v_word_eq_def, updFlEnv_def])
       \\ rveq \\ fs[updFlEnv_def] \\ rveq \\ fs[v_word_eq_def])
   >- (
     rpt strip_tac
     \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def]
     \\ TOP_CASE_TAC \\ fs[]
     \\ first_x_assum (qspec_then ‘x'’ mp_tac) \\ fs[]
     \\ disch_then assume_tac \\ fs[])
   \\ fs[])
  \\ TRY (
     fs[option_case_eq, pair_case_eq] \\ rveq
     \\ fs[bstep_float_def]
     \\ drule CakeML_FloVer_float_sim_exp \\ rpt (disch_then drule)
     \\ strip_tac \\ fs[])
  \\ simp[terminationTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate stUpd env _’
  \\ ‘stUpd.fp_state.canOpt = FPScope NoOpt’ by (unabbrev_all_tac \\ fs[])
  \\ fs[freevars_def]
  \\ first_x_assum drule
  \\ rpt (disch_then drule)
  \\ strip_tac \\ fs[]
  \\ Cases_on ‘vFC’ \\ TRY (Cases_on ‘l’) \\ fs[v_word_eq_def]
  \\ rveq \\ EVAL_TAC \\ fs[fpSemTheory.compress_word_def, v_word_eq_def]
  \\ unabbrev_all_tac \\ fs[state_component_equality, fpState_component_equality]
QED

Theorem CakeML_FloVer_float_sim_exp_strict:
  ∀ varMap f theExp freshId E env fVars (st:'ffi semanticPrimitives$state) vF.
    toFloVerExp varMap f = SOME theExp ∧
    st.fp_state.canOpt = Strict ∧
    ids_unique varMap freshId ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    env_word_sim env.v E fVars ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
    eval_expr_float theExp E = SOME vF ⇒
    ∃ vFC. evaluate st env [f] = (st, Rval [vFC]) ∧ v_word_eq vFC vF
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ fs[eval_expr_float_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[env_word_sim_def]
    \\ res_tac \\ rveq \\ fs[] \\ rveq
    \\ simp[evaluate_def])
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum `T` kall_tac)
    \\ fs[eval_expr_float_def] \\ rveq \\ fs[]
    \\ simp[evaluate_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def, fpSemTheory.compress_word_def,
            state_component_equality,
            v_word_eq_def])
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[eval_expr_float_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[]
    \\ ‘∃ vFC. evaluate st env [e] = (st, Rval [vFC]) ∧
        v_word_eq vFC v’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then assume_tac \\ fs[])
    \\ simp[evaluate_def, v_eq_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ Cases_on ‘vFC’
    \\ TRY (rename1 ‘v_word_eq (Litv l) v’ \\ Cases_on ‘l’)
    \\ fs[v_word_eq_def] \\ rveq
    \\ fs[v_word_eq_def, semanticPrimitivesTheory.fp_translate_def,
          astTheory.isFpBool_def, fpValTreeTheory.fp_uop_def,
          state_component_equality,
          fpSemTheory.compress_word_def]
    \\ EVAL_TAC)
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[eval_expr_float_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[]
    \\ ‘∃ vFC. evaluate st env [e2] = (st, Rval [vFC]) ∧
        v_word_eq vFC v2’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v2’ mp_tac) \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∃ vFC. evaluate st env [e1] = (st, Rval [vFC]) ∧
        v_word_eq vFC v1’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v1’ mp_tac) \\ impl_tac \\ fs[])
    \\ simp[evaluate_def, v_eq_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ Cases_on ‘vFC'’ \\ Cases_on ‘vFC’
    \\ TRY (rename1 ‘v_word_eq (Litv l1) v1’ \\ Cases_on ‘l1’)
    \\ TRY (rename1 ‘v_word_eq (Litv l2) v2’ \\ Cases_on ‘l2’)
    \\ fs[v_word_eq_def, semanticPrimitivesTheory.fp_translate_def,
          astTheory.isFpBool_def, fpValTreeTheory.fp_uop_def,
          state_component_equality,
          fpSemTheory.compress_word_def]
    \\ rveq \\ Cases_on ‘bop’ \\ fs[fpBopToFloVer_def, dmode_def] \\ rveq
    \\ fs[fpValTreeTheory.fp_bop_def, fpSemTheory.compress_word_def]
    \\ EVAL_TAC)
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[eval_expr_float_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[]
    \\ ‘∃ vFC. evaluate st env [e3] = (st, Rval [vFC]) ∧
        v_word_eq vFC v2’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v2’ mp_tac) \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∃ vFC. evaluate st env [e2] = (st, Rval [vFC]) ∧
        v_word_eq vFC v1’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v1’ mp_tac) \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∃ vFC. evaluate st env [e1] = (st, Rval [vFC]) ∧
        v_word_eq vFC v3’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v3’ mp_tac) \\ impl_tac \\ fs[])
    \\ simp[evaluate_def, v_eq_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ Cases_on ‘vFC'’ \\ Cases_on ‘vFC’ \\ Cases_on ‘vFC''’
    \\ TRY (rename1 ‘v_word_eq (Litv l1) v1’ \\ Cases_on ‘l1’)
    \\ TRY (rename1 ‘v_word_eq (Litv l2) v2’ \\ Cases_on ‘l2’)
    \\ TRY (rename1 ‘v_word_eq (Litv l3) v3’ \\ Cases_on ‘l3’)
    \\ fs[v_word_eq_def, semanticPrimitivesTheory.fp_translate_def,
          astTheory.isFpBool_def, fpValTreeTheory.fp_uop_def,
          state_component_equality,
          fpSemTheory.compress_word_def]
    \\ rveq
    \\ fs[fpValTreeTheory.fp_top_def, fpSemTheory.compress_word_def]
    \\ EVAL_TAC)
  >- (
   simp[terminationTheory.evaluate_def]
   \\ qmatch_goalsub_abbrev_tac ‘evaluate stUpd env [f]’
   \\ ‘stUpd.fp_state.canOpt = Strict’
      by (unabbrev_all_tac \\ fs[])
   \\ first_x_assum drule
   \\ rpt (disch_then drule)
   \\ disch_then (qspec_then ‘vF’ mp_tac)
   \\ impl_tac
   >- (fs[freevars_def])
   \\ strip_tac \\ fs[]
   \\ Cases_on ‘vFC’ \\ TRY (Cases_on ‘l’)
   \\ unabbrev_all_tac
   \\ fs[v_word_eq_def, do_fpoptimise_def, state_component_equality,
         fpState_component_equality, fpSemTheory.compress_word_def])
QED

Theorem CakeML_FloVer_float_sim_strict:
  ∀ varMap freshId f theIds freshId2 theCmd E env fVars
  (st:'ffi semanticPrimitives$state) vF.
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
  st.fp_state.canOpt = Strict ∧
  ids_unique varMap freshId ∧
  (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
  env_word_sim env.v E fVars ∧
  (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
  bstep_float theCmd E = SOME vF ⇒
  ∃ vFC. evaluate st env [f] = (st, Rval [vFC]) ∧
    v_word_eq vFC vF
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def]
  >- (
   fs[option_case_eq, pair_case_eq, freevars_def] \\ rveq
   \\ fs[bstep_float_def]
   \\ Cases_on ‘eval_expr_float fexp1 E’ \\ fs[optionLift_def]
   \\ rename1 ‘eval_expr_float fexp1 E = SOME w1’
   \\ ‘∃vF1. evaluate st env [e1] = (st, Rval [vF1]) ∧ v_word_eq vF1 w1’
     by (drule CakeML_FloVer_float_sim_exp_strict
         \\ rpt (disch_then drule)
         \\ disch_then (qspec_then ‘w1’ mp_tac) \\ impl_tac
         \\ rpt strip_tac \\ fs[])
   \\ simp[evaluate_def]
   \\ first_x_assum drule \\ rpt (disch_then drule)
   \\ disch_then (qspecl_then [‘updFlEnv freshId w1 E’,
                               ‘env with v := nsOptBind (SOME x) vF1 env.v’,
                               ‘fVars UNION { (Short x, freshId) }’,
                               ‘vF’] mp_tac)
   \\ reverse (impl_tac)
   >- (strip_tac \\ fsrw_tac [SATISFY_ss] [])
   \\ rpt conj_tac
   >- (
     irule ids_unique_append \\ fs[])
   >- (
     rpt strip_tac \\ fs[]
     >- (
       fs[lookupCMLVar_appendCMLVar]
        \\ ‘x' ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘y ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
       \\ res_tac
       \\ fs[lookupCMLVar_def, updateTheory.FIND_def])
     \\ rveq \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def])
   >- (
       simp[env_word_sim_def] \\ rpt strip_tac \\ fs[namespaceTheory.nsOptBind_def]
       >- (
         ‘cake_id ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘flover_id ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ fs[env_word_sim_def] \\ res_tac
         \\ fsrw_tac [SATISFY_ss] []
         \\ res_tac \\ fs[updFlEnv_def])
       >- (
         ‘cake_id ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘flover_id ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ fs[ml_progTheory.nsLookup_nsBind_compute]
         \\ fs[env_word_sim_def] \\ res_tac
         \\ fsrw_tac [SATISFY_ss] []
         \\ res_tac \\ rfs[updFlEnv_def] \\ fs[])
       >- (
         rveq \\ fs[ml_progTheory.nsLookup_nsBind_compute]
         \\ rveq \\ fs[v_word_eq_def, updFlEnv_def])
       \\ rveq \\ fs[updFlEnv_def] \\ rveq \\ fs[v_word_eq_def])
   >- (
     rpt strip_tac
     \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def]
     \\ TOP_CASE_TAC \\ fs[]
     \\ first_x_assum (qspec_then ‘x'’ mp_tac) \\ fs[]
     \\ disch_then assume_tac \\ fs[])
   \\ fs[])
  \\ TRY (
     fs[option_case_eq, pair_case_eq] \\ rveq
     \\ fs[bstep_float_def]
     \\ drule CakeML_FloVer_float_sim_exp_strict \\ rpt (disch_then drule)
     \\ strip_tac \\ fs[])
  \\ simp[terminationTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate stUpd env _’
  \\ ‘stUpd.fp_state.canOpt = Strict’ by (unabbrev_all_tac \\ fs[])
  \\ fs[freevars_def]
  \\ first_x_assum drule
  \\ rpt (disch_then drule)
  \\ strip_tac \\ fs[]
  \\ Cases_on ‘vFC’ \\ TRY (Cases_on ‘l’) \\ fs[v_word_eq_def]
  \\ rveq \\ EVAL_TAC \\ fs[fpSemTheory.compress_word_def, v_word_eq_def]
  \\ unabbrev_all_tac \\ fs[state_component_equality, fpState_component_equality]
QED

Triviality state_eq_fpstate:
  st with fp_state := st.fp_state = st
Proof
  fs[state_component_equality]
QED

Theorem CakeML_FloVer_float_sim_noopt:
  ∀ varMap freshId f theIds freshId2 theCmd E env fVars (st:'ffi semanticPrimitives$state) vF.
  toFloVerCmd varMap freshId (FpOptimise NoOpt f) = SOME (theIds, freshId2, theCmd) ∧
  ids_unique varMap freshId ∧
  (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
  env_word_sim env.v E fVars ∧
  (∀ x. x IN freevars [FpOptimise NoOpt f] ⇒
   ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
  bstep_float theCmd E = SOME vF ⇒
  ∃ vFC. evaluate st env [FpOptimise NoOpt f] = (st, Rval [vFC]) ∧
    v_word_eq vFC vF
Proof
  rpt strip_tac
  \\ fs[terminationTheory.evaluate_def, toFloVerCmd_def, freevars_def]
  \\ Cases_on ‘st.fp_state.canOpt = Strict’ \\ fs[]
  >- (
   drule CakeML_FloVer_float_sim_strict
   \\ rpt (disch_then drule)
   \\ strip_tac \\ fs[state_eq_fpstate]
   \\ Cases_on ‘vFC’ \\ TRY (Cases_on ‘l’)
   \\ fs[do_fpoptimise_def, v_word_eq_def, state_component_equality, fpState_component_equality, fpSemTheory.compress_word_def])
  \\ drule CakeML_FloVer_float_sim
  \\ ‘(st with fp_state := st.fp_state with canOpt := FPScope NoOpt).fp_state.canOpt = FPScope NoOpt’ by fs[]
   \\ rpt (disch_then drule)
   \\ strip_tac \\ fs[state_eq_fpstate]
   \\ Cases_on ‘vFC’ \\ TRY (Cases_on ‘l’)
   \\ fs[do_fpoptimise_def, v_word_eq_def, state_component_equality,
         fpState_component_equality, fpSemTheory.compress_word_def]
QED

Theorem FloVer_CakeML_float_sim_exp:
  ∀ varMap f theExp freshId E env fVars (st:'ffi semanticPrimitives$state) st2 vFC.
    toFloVerExp varMap f = SOME theExp ∧
    st.fp_state.canOpt = FPScope NoOpt ∧
    ids_unique varMap freshId ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    env_word_sim env.v E fVars ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
    evaluate st env [f] = (st2, Rval [vFC]) ⇒
    ∃ vF. eval_expr_float theExp E = SOME vF ∧ v_word_eq vFC vF
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ fs[evaluate_def, option_case_eq, freevars_def]
    \\ rveq \\ fs[env_word_sim_def]
    \\ res_tac \\ rveq \\ fs[] \\ rveq
    \\ simp[eval_expr_float_def])
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum `T` kall_tac)
    \\ fs[eval_expr_float_def] \\ rveq \\ fs[]
    \\ fs[evaluate_def, astTheory.getOpClass_def,
          semanticPrimitivesTheory.do_app_def]
    \\ rveq \\ simp[v_word_eq_def, fpSemTheory.compress_word_def])
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ qpat_x_assum `evaluate st env _ = _` mp_tac
    \\ simp[evaluate_def, option_case_eq, freevars_def,
          astTheory.getOpClass_def, semanticPrimitivesTheory.do_app_def]
    \\ ntac 5 (TOP_CASE_TAC \\ fs[])
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ rveq \\ fs[]
    \\ rename1 ‘evaluate st env [e] = (st1, Rval [v1])’
    \\ ‘st1.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ simp[astTheory.isFpBool_def] \\ strip_tac \\ fs[] \\ rveq
    \\ simp[eval_expr_float_def]
    \\ fs[freevars_def]
    \\ pop_assum kall_tac
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac \\ fs[]
    \\ every_case_tac \\ fs[] \\ rveq
    \\ TRY (Cases_on ‘l’ \\ fs[])
    \\ fs[v_word_eq_def, fpValTreeTheory.fp_uop_def, fp_translate_def,
          fpSemTheory.compress_word_def]
    \\ rveq
    \\ fs[fpSemTheory.compress_word_def, fpSemTheory.fp_uop_comp_def])
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ qpat_x_assum `evaluate st env _ = _` mp_tac
    \\ simp[evaluate_def, option_case_eq, freevars_def,
            astTheory.getOpClass_def, semanticPrimitivesTheory.do_app_def,
            astTheory.isFpBool_def]
    \\ Cases_on ‘evaluate st env [e2]’ \\ fs[]
    \\ Cases_on ‘r’ \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ rveq \\ fs[]
    \\ rename1 ‘evaluate st env [e2] = (st1, Rval [v2])’
    \\ Cases_on ‘evaluate st1 env [e1]’ \\ fs[]
    \\ Cases_on ‘r’ \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ rveq \\ fs[]
    \\ rename1 ‘evaluate st1 env [e1] = (st3, Rval [v1])’
    \\ ‘st3.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ pop_assum kall_tac
    \\ rveq \\ rename1 ‘evaluate st env [e2] = (st1, Rval [v2])’
    \\ Cases_on ‘fp_translate v1’ \\ fs[]
    \\ Cases_on ‘x’ \\ fs[]
    \\ Cases_on ‘fp_translate v2’ \\ fs[]
    \\ Cases_on ‘x’ \\ fs[]
    \\ strip_tac \\ rveq
    \\ fs[freevars_def]
    \\ ‘∃ vF2. eval_expr_float fexp2 E = SOME vF2 ∧ v_word_eq v2 vF2’
      by (
         last_x_assum drule
         \\ rpt (disch_then drule)
         \\ disch_then irule
         \\ rpt conj_tac \\ rpt strip_tac
         >- (first_x_assum (qspec_then ‘x’ mp_tac) \\ impl_tac \\ fs[])
         \\ asm_exists_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘st1.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ ‘∃ vF1. eval_expr_float fexp1 E = SOME vF1 ∧ v_word_eq v1 vF1’
      by (
         last_x_assum drule
         \\ rpt (disch_then drule)
         \\ disch_then irule
         \\ rpt conj_tac \\ rpt strip_tac
         >- (first_x_assum (qspec_then ‘x’ mp_tac) \\ impl_tac \\ fs[])
         \\ asm_exists_tac \\ fs[])
    \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ fs[] \\ rveq
    \\ TRY (rename1 ‘fp_translate (Litv l1) = SOME (FP_WordTree f)’ \\ Cases_on ‘l1’ \\ fs[])
    \\ TRY (rename1 ‘fp_translate (Litv l2) = SOME (FP_WordTree f2)’ \\ Cases_on ‘l2’ \\ fs[])
    \\ fs[v_word_eq_def, fpValTreeTheory.fp_bop_def, fp_translate_def,
          fpSemTheory.compress_word_def]
    \\ rveq \\ Cases_on ‘bop’ \\ EVAL_TAC
    \\ fs[fpSemTheory.compress_word_def, fpSemTheory.fp_bop_comp_def])
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ qpat_x_assum `evaluate st env _ = _` mp_tac
    \\ simp[evaluate_def, option_case_eq, freevars_def,
            astTheory.getOpClass_def, semanticPrimitivesTheory.do_app_def,
            astTheory.isFpBool_def]
    \\ Cases_on ‘evaluate st env [e3]’ \\ fs[]
    \\ Cases_on ‘r’ \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ rveq \\ fs[]
    \\ rename1 ‘evaluate st env [e3] = (stA, Rval [v3])’
    \\ Cases_on ‘evaluate stA env [e2]’ \\ fs[]
    \\ Cases_on ‘r’ \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ rveq \\ fs[]
    \\ rename1 ‘evaluate stA env [e2] = (stB, Rval [v2])’
    \\ Cases_on ‘evaluate stB env [e1]’ \\ fs[]
    \\ Cases_on ‘r’ \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ rveq \\ fs[]
    \\ rename1 ‘evaluate stB env [e1] = (stC, Rval [v1])’
    \\ ‘stC.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ rveq \\ fs[]
    \\ rename1 ‘evaluate stA env [e2] = (stB, Rval [v2])’
    \\ rename1 ‘evaluate st env [e3] = (stA, Rval [v3])’
    \\ pop_assum kall_tac
    \\ Cases_on ‘fp_translate v1’ \\ fs[]
    \\ Cases_on ‘x’ \\ fs[]
    \\ Cases_on ‘fp_translate v2’ \\ fs[]
    \\ Cases_on ‘x’ \\ fs[]
    \\ Cases_on ‘fp_translate v3’ \\ fs[]
    \\ Cases_on ‘x’ \\ fs[]
    \\ strip_tac \\ rveq
    \\ fs[freevars_def]
    \\ ‘∃ vF3. eval_expr_float fexp3 E = SOME vF3 ∧ v_word_eq v3 vF3’
      by (
         last_x_assum drule
         \\ rpt (disch_then drule)
         \\ disch_then irule
         \\ rpt conj_tac \\ rpt strip_tac
         >- (first_x_assum (qspec_then ‘x’ mp_tac) \\ impl_tac \\ fs[])
         \\ asm_exists_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘stA.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ ‘∃ vF2. eval_expr_float fexp2 E = SOME vF2 ∧ v_word_eq v2 vF2’
      by (
         last_x_assum drule
         \\ rpt (disch_then drule)
         \\ disch_then irule
         \\ rpt conj_tac \\ rpt strip_tac
         >- (first_x_assum (qspec_then ‘x’ mp_tac) \\ impl_tac \\ fs[])
         \\ asm_exists_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘stB.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ ‘∃ vF1. eval_expr_float fexp1 E = SOME vF1 ∧ v_word_eq v1 vF1’
      by (
         last_x_assum drule
         \\ rpt (disch_then drule)
         \\ disch_then irule
         \\ rpt conj_tac \\ rpt strip_tac
         >- (first_x_assum (qspec_then ‘x’ mp_tac) \\ impl_tac \\ fs[])
         \\ asm_exists_tac \\ fs[])
    \\ rename1 ‘fp_translate v1 = SOME (FP_WordTree f1)’
    \\ rename1 ‘fp_translate v2 = SOME (FP_WordTree f2)’
    \\ rename1 ‘fp_translate v3 = SOME (FP_WordTree f3)’
    \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ Cases_on ‘v3’ \\ fs[] \\ rveq
    \\ TRY (rename1 ‘fp_translate (Litv l1) = SOME (FP_WordTree f1)’ \\ Cases_on ‘l1’ \\ fs[])
    \\ TRY (rename1 ‘fp_translate (Litv l2) = SOME (FP_WordTree f2)’ \\ Cases_on ‘l2’ \\ fs[])
    \\ TRY (rename1 ‘fp_translate (Litv l3) = SOME (FP_WordTree f3)’ \\ Cases_on ‘l3’ \\ fs[])
    \\ fs[v_word_eq_def, fpValTreeTheory.fp_top_def, fp_translate_def,
          fpSemTheory.compress_word_def]
    \\ rveq \\ EVAL_TAC
    \\ fs[fpSemTheory.compress_word_def, fpSemTheory.fp_top_comp_def])
  >- (
   qpat_x_assum `evaluate _ _ _= _` mp_tac
   \\ simp[terminationTheory.evaluate_def]
   \\ rpt (TOP_CASE_TAC \\ fs[])
   \\ rpt strip_tac \\ fs[] \\ rveq
   \\ ‘(st with fp_state := st.fp_state with canOpt := FPScope NoOpt).fp_state.canOpt = FPScope NoOpt’
      by (fs[])
   \\ first_x_assum drule
   \\ rpt (disch_then drule)
   \\ imp_res_tac evaluatePropsTheory.evaluate_sing
   \\ rveq
   \\ disch_then (qspecl_then [‘q’,‘v’] mp_tac) \\ impl_tac
   \\ fs[freevars_def]
   \\ strip_tac \\ fs[]
   \\ Cases_on ‘v’ \\ TRY (Cases_on ‘l’) \\ fs[v_word_eq_def]
   \\ rveq \\ fs[do_fpoptimise_def] \\ rveq \\ fs[v_word_eq_def, fpSemTheory.compress_word_def])
QED

Theorem FloVer_CakeML_float_sim:
  ∀ varMap freshId f theIds freshId2 theCmd E env fVars (st:'ffi semanticPrimitives$state) st2 vFC.
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
  st.fp_state.canOpt = FPScope NoOpt ∧
  ids_unique varMap freshId ∧
  (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
  env_word_sim env.v E fVars ∧
  (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
  evaluate st env [f] = (st2, Rval [vFC]) ⇒
  ∃ vF. bstep_float theCmd E = SOME vF ∧
  v_word_eq vFC vF
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def]
  >- (
   fs[option_case_eq, pair_case_eq, freevars_def] \\ rveq
   \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
   \\ simp[evaluate_def]
   \\ ntac 2 (TOP_CASE_TAC \\ fs[])
   \\ strip_tac
   \\ imp_res_tac evaluatePropsTheory.evaluate_sing
   \\ fs[] \\ rveq
   \\ simp[bstep_float_def]
   \\ drule FloVer_CakeML_float_sim_exp
   \\ rpt (disch_then drule)
   \\ rename1 ‘evaluate st env [e1] = (stA, Rval [v1])’
   \\ disch_then (qspecl_then [‘stA’, ‘v1’] mp_tac)
   \\ impl_tac \\ fs[]
   \\ strip_tac \\ fs[]
   \\ simp[optionLift_def]
   \\ ‘stA.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
   \\ first_x_assum drule
   \\ rpt (disch_then drule)
   \\ disch_then irule
   \\ conj_tac
   >- (irule ids_unique_append \\ fs[])
   \\ qexists_tac ‘env with v := nsOptBind (SOME x) v1 env.v’
   \\ qexists_tac ‘fVars UNION { (Short x, freshId) }’
   \\ qexists_tac ‘st2’
   \\ rpt conj_tac \\ fs[]
   >- (
     rpt strip_tac \\ fs[]
     >- (
       fs[lookupCMLVar_appendCMLVar]
        \\ ‘x' ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
         \\ ‘y ≠ freshId’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
       \\ res_tac
       \\ fs[lookupCMLVar_def, updateTheory.FIND_def])
     \\ rveq \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def])
   >- (
     rpt strip_tac
     \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def]
     \\ TOP_CASE_TAC \\ fs[]
     \\ first_x_assum (qspec_then ‘x'’ mp_tac) \\ fs[]
     \\ disch_then assume_tac \\ fs[]
     \\ fs[])
   \\ simp[env_word_sim_def] \\ rpt strip_tac \\ fs[namespaceTheory.nsOptBind_def]
   >- (
     ‘cake_id ≠ Short x’
       by (CCONTR_TAC
           \\ fs[] \\ rveq \\ res_tac
           \\ fs[])
     \\ ‘flover_id ≠ freshId’
       by (CCONTR_TAC
           \\ fs[] \\ rveq \\ res_tac
           \\ fs[ids_unique_def] \\ res_tac
           \\ fs[])
     \\ fs[env_word_sim_def] \\ res_tac
     \\ fsrw_tac [SATISFY_ss] []
     \\ res_tac \\ fs[updFlEnv_def])
   >- (
     ‘cake_id ≠ Short x’
       by (CCONTR_TAC
           \\ fs[] \\ rveq \\ res_tac
           \\ fs[])
     \\ ‘flover_id ≠ freshId’
       by (CCONTR_TAC
           \\ fs[] \\ rveq \\ res_tac
           \\ fs[ids_unique_def] \\ res_tac
           \\ fs[])
     \\ fs[ml_progTheory.nsLookup_nsBind_compute]
     \\ fs[env_word_sim_def] \\ res_tac
     \\ fsrw_tac [SATISFY_ss] []
     \\ res_tac \\ rfs[updFlEnv_def] \\ fs[])
   >- (
     rveq \\ fs[ml_progTheory.nsLookup_nsBind_compute]
     \\ rveq \\ fs[v_word_eq_def, updFlEnv_def])
   \\ rveq \\ fs[updFlEnv_def] \\ rveq \\ fs[v_word_eq_def])
  \\ TRY (
     fs[option_case_eq, pair_case_eq] \\ rveq
     \\ fs[bstep_float_def]
     \\ drule FloVer_CakeML_float_sim_exp \\ rpt (disch_then drule)
     \\ strip_tac \\ fs[])
  \\ pop_assum mp_tac \\ simp[terminationTheory.evaluate_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate stUpd env _’
  \\ ‘stUpd.fp_state.canOpt = FPScope NoOpt’ by (unabbrev_all_tac \\ fs[])
  \\ rpt (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac \\ rveq
  \\ fs[freevars_def]
  \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ rveq
  \\ first_x_assum drule
  \\ rpt (disch_then drule)
  \\ strip_tac \\ Cases_on ‘v’ \\ TRY (Cases_on ‘l’) \\ fs[v_word_eq_def]
  \\ rveq \\ fs[do_fpoptimise_def]
  \\ rveq \\ fs[v_word_eq_def, fpSemTheory.compress_word_def]
QED

Definition fpNormalOrZero_def:
  fpNormalOrZero v =
  case v of
  | [FP_WordTree fp] => normal_or_zero (fp64_to_real (compress_word fp))
  | [Litv (Word64 w)] => normal_or_zero (fp64_to_real w)
  | _ => T
End

Triviality ast_exp6_size_APPEND:
  ast$exp6_size (es1 ++ es2) = exp6_size es1 + exp6_size es2
Proof
  Induct_on ‘es1’ \\ fs[astTheory.exp_size_def]
QED

Triviality ast_exp6_size_REVERSE:
  ast$exp6_size (REVERSE es) = exp6_size es
Proof
  Induct_on ‘es’ \\ fs[astTheory.exp_size_def, ast_exp6_size_APPEND]
QED

Definition evaluate_fine_def:
  evaluate_fine st env es =
  case es of
   | [] => T
   | [Lit l] => T
   | [Var x] => T
   | [App op es] =>
     (evaluate_fine st env (REVERSE es) ∧
      case op of
      | FP_uop uop => T
      | FP_bop bop =>
      (case es of
      | [e1; e2] =>
      (case evaluate st env [e2] of
       | (st2, Rval [v2]) =>
       (case evaluate st2 env [e1] of
        | (st3, Rval [v1]) =>
        (case (fp_translate v1, fp_translate v2) of
         | SOME (FP_WordTree fp1), SOME (FP_WordTree fp2) =>
          normal_or_zero (evalBinop (fpBopToFloVer bop) (fp64_to_real (compress_word fp1)) (fp64_to_real (compress_word fp2)))
         | _, _ => F)
        | _ => F)
       | _ => F)
      | _ => F)
      | FP_top op =>
      (case es of
      | [e1; e2; e3] =>
      (case evaluate st env [e3] of
       | (st2, Rval [v3]) =>
       (case evaluate st2 env [e2] of
        | (st3, Rval [v2]) =>
        (case evaluate st3 env [e1] of
         | (st4, Rval [v1]) =>
        (case (fp_translate v1, fp_translate v2, fp_translate v3) of
         | SOME (FP_WordTree fp1), SOME (FP_WordTree fp2), SOME (FP_WordTree fp3) =>
          normal_or_zero (evalFma (fp64_to_real (compress_word fp2)) (fp64_to_real (compress_word fp3)) (fp64_to_real (compress_word fp1)))
          | _, _ => F)
        | _ => F)
        | _ => F)
       | _ => F)
       | _ => F)
      | _ => F)
   | [Let (SOME x) e1 f] =>
     (evaluate_fine st env [e1] ∧
      (case evaluate st env [e1] of
       | (st2, Rval v) =>
         evaluate_fine st (env with v := nsOptBind (SOME x) (HD v) env.v) [f]
       | _ => F))
   | [FpOptimise NoOpt e] =>
     evaluate_fine (st with fp_state := st.fp_state with canOpt := FPScope NoOpt) env [e]
   | (e1 :: e2 :: es) =>
     (evaluate_fine st env [e1] ∧
     case evaluate st env [e1] of
      | (st2, Rval v1) =>
        evaluate_fine st2 env (e2::es)
      | _ => F)
   | _ => F
Termination
  wf_rel_tac ‘measure (λ (s,env, es). exp6_size es)’
  \\ fs[ast_exp6_size_REVERSE]
End

Theorem evaluate_fine_eval_expr_valid:
  ∀ varMap f theCmd freshId (st:'ffi semanticPrimitives$state) env E fVars.
    toFloVerExp varMap f = SOME theCmd ∧
    evaluate_fine st env [f] ∧
    st.fp_state.canOpt = FPScope NoOpt ∧
    ids_unique varMap freshId ∧
    env_word_sim env.v E fVars ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ⇒
    eval_expr_valid theCmd E
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  >- (
    fs[option_case_eq, pair_case_eq, evaluate_fine_def] \\ rveq
    \\ fs[option_case_eq, eval_expr_valid_def])
  >- (rveq \\ simp[eval_expr_valid_def])
  >- (
    rveq \\ fs[]
    \\ qpat_x_assum `evaluate_fine _ _ _` mp_tac \\ simp[Once evaluate_fine_def]
    \\ rpt (qpat_x_assum `T` kall_tac)
    \\ strip_tac \\ fs[eval_expr_valid_def, freevars_def]
    \\ first_x_assum irule \\ rpt (asm_exists_tac \\ fs[])
    \\ rpt conj_tac \\ rpt (asm_exists_tac \\ fs[]))
  >- (
    rveq \\ fs[]
    \\ qpat_x_assum `evaluate_fine _ _ _` mp_tac \\ simp[Once evaluate_fine_def]
    \\ rpt (qpat_x_assum `T` kall_tac)
    \\ simp[Once evaluate_fine_def]
    \\ Cases_on ‘evaluate st env [e2]’ \\ Cases_on ‘r’ \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ fs[] \\ rveq
    \\ rename1 ‘evaluate st env [e2] = (stA, Rval [v2])’
    \\ ntac 2 (TOP_CASE_TAC) \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ fs[] \\ rveq
    \\ rename1 ‘evaluate st env [e2] = (stA, Rval [v2])’
    \\ rename1 ‘evaluate stA env [e1] = (stB, Rval [v1])’
    \\ ntac 4 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ fs[freevars_def]
    \\ ‘eval_expr_valid fexp2 E’
      by (last_x_assum drule
          \\ rpt (disch_then drule)
          \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘stA.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ ‘eval_expr_valid fexp1 E’
      by (last_x_assum drule
          \\ rpt (disch_then drule)
          \\ impl_tac \\ fs[])
    \\ fs[eval_expr_valid_def]
    \\ ‘∃ vF1. eval_expr_float fexp1 E = SOME vF1 ∧ v_word_eq v1 vF1’
       by (
         irule FloVer_CakeML_float_sim_exp
         \\ rpt (asm_exists_tac \\ fs[])
         \\ rewrite_tac [CONJ_ASSOC]
         \\ once_rewrite_tac [CONJ_COMM]
         \\ rpt (asm_exists_tac \\ fs[] \\ once_rewrite_tac[CONJ_COMM]))
    \\ ‘∃ vF2. eval_expr_float fexp2 E = SOME vF2 ∧ v_word_eq v2 vF2’
       by (
         irule FloVer_CakeML_float_sim_exp
         \\ qpat_x_assum ‘stA.fp_state.canOpt = _’ kall_tac
         \\ qexists_tac ‘env’
         \\ qexists_tac ‘e2’ \\ qexists_tac ‘fVars’
         \\ qexists_tac ‘freshId’ \\ qexists_tac ‘st’ \\ qexists_tac ‘stA’ \\ fs[]
         \\ qexists_tac ‘varMap’ \\ fs[])
    \\ fs[optionLift_def]
    \\ fs[fp64_to_real_def]
    \\ rename1 ‘fp_translate v1 = SOME (FP_WordTree f1)’
    \\ rename1 ‘fp_translate v2 = SOME (FP_WordTree f2)’
    \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ fs[] \\ rveq
    \\ TRY (rename1 ‘fp_translate (Litv l1) = SOME (FP_WordTree f1)’ \\ Cases_on ‘l1’ \\ fs[])
    \\ TRY (rename1 ‘fp_translate (Litv l2) = SOME (FP_WordTree f2)’ \\ Cases_on ‘l2’ \\ fs[])
    \\ fs[v_word_eq_def, fpValTreeTheory.fp_top_def, fp_translate_def,
          fpSemTheory.compress_word_def]
    \\ rveq
    \\ fs[fpSemTheory.compress_word_def])
  >- (
    rveq \\ fs[]
    \\ qpat_x_assum `evaluate_fine _ _ _` mp_tac \\ simp[Once evaluate_fine_def]
    \\ rpt (qpat_x_assum `T` kall_tac)
    \\ simp[Once evaluate_fine_def]
    \\ ntac 2 (TOP_CASE_TAC) \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ fs[] \\ rveq
    \\ rename1 ‘evaluate st env [e3] = (stA, Rval [v3])’
    \\ ntac 2 (TOP_CASE_TAC) \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ fs[] \\ rveq
    \\ rename1 ‘evaluate stA env [e2] = (stB, Rval [v2])’
    \\ ntac 2 (TOP_CASE_TAC) \\ fs[]
    \\ imp_res_tac evaluatePropsTheory.evaluate_sing \\ fs[] \\ rveq
    \\ rename1 ‘evaluate st env [e3] = (stA, Rval [v3])’
    \\ rename1 ‘evaluate stA env [e2] = (stB, Rval [v2])’
    \\ rename1 ‘evaluate stB env [e1] = (stC, Rval [v1])’
    \\ ntac 6 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ fs[freevars_def]
    \\ ‘eval_expr_valid fexp3 E’
      by (last_x_assum drule
          \\ rpt (disch_then drule)
          \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘stA.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ qpat_x_assum ‘evaluate_fine _ _ [e2; e1]’ mp_tac
    \\ simp[Once evaluate_fine_def] \\ strip_tac
    \\ ‘eval_expr_valid fexp2 E’
      by (last_x_assum drule
          \\ rpt (disch_then drule)
          \\ impl_tac \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘stB.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ ‘eval_expr_valid fexp1 E’
      by (last_x_assum drule
          \\ rpt (disch_then drule)
          \\ impl_tac \\ fs[])
    \\ fs[eval_expr_valid_def]
    \\ ‘∃ vF1. eval_expr_float fexp1 E = SOME vF1 ∧ v_word_eq v1 vF1’
       by (
         irule FloVer_CakeML_float_sim_exp
         \\ rpt (asm_exists_tac \\ fs[])
         \\ rewrite_tac [CONJ_ASSOC]
         \\ once_rewrite_tac [CONJ_COMM]
         \\ rpt (asm_exists_tac \\ fs[] \\ once_rewrite_tac[CONJ_COMM]))
    \\ ‘∃ vF2. eval_expr_float fexp2 E = SOME vF2 ∧ v_word_eq v2 vF2’
       by (
         irule FloVer_CakeML_float_sim_exp
         \\ qpat_x_assum ‘stB.fp_state.canOpt = _’ kall_tac
         \\ qexists_tac ‘env’
         \\ qexists_tac ‘e2’ \\ qexists_tac ‘fVars’
         \\ qexists_tac ‘freshId’ \\ qexists_tac ‘stA’ \\ qexists_tac ‘stB’ \\ fs[]
         \\ qexists_tac ‘varMap’ \\ fs[])
    \\ ‘∃ vF3. eval_expr_float fexp3 E = SOME vF3 ∧ v_word_eq v3 vF3’
       by (
         irule FloVer_CakeML_float_sim_exp
         \\ qpat_x_assum ‘stB.fp_state.canOpt = _’ kall_tac
         \\ qpat_x_assum ‘stA.fp_state.canOpt = _’ kall_tac
         \\ qexists_tac ‘env’
         \\ qexists_tac ‘e3’ \\ qexists_tac ‘fVars’
         \\ qexists_tac ‘freshId’ \\ qexists_tac ‘st’ \\ qexists_tac ‘stA’ \\ fs[]
         \\ qexists_tac ‘varMap’ \\ fs[])
    \\ fs[optionLift_def]
    \\ fs[fp64_to_real_def]
    \\ rename1 ‘fp_translate v1 = SOME (FP_WordTree f1)’
    \\ rename1 ‘fp_translate v2 = SOME (FP_WordTree f2)’
    \\ rename1 ‘fp_translate v3 = SOME (FP_WordTree f3)’
    \\ Cases_on ‘v1’ \\ Cases_on ‘v2’ \\ Cases_on ‘v3’ \\ fs[] \\ rveq
    \\ TRY (rename1 ‘fp_translate (Litv l1) = SOME (FP_WordTree f1)’ \\ Cases_on ‘l1’ \\ fs[])
    \\ TRY (rename1 ‘fp_translate (Litv l2) = SOME (FP_WordTree f2)’ \\ Cases_on ‘l2’ \\ fs[])
    \\ TRY (rename1 ‘fp_translate (Litv l3) = SOME (FP_WordTree f3)’ \\ Cases_on ‘l3’ \\ fs[])
    \\ fs[v_word_eq_def, fpValTreeTheory.fp_top_def, fp_translate_def,
          fpSemTheory.compress_word_def]
    \\ rveq
    \\ fs[fpSemTheory.compress_word_def])
  >- (
   qpat_x_assum ‘evaluate_fine _ _ _’ mp_tac
   \\ simp[Once evaluate_fine_def]
   \\ strip_tac \\ first_x_assum drule
   \\ rpt (disch_then drule \\ fs[freevars_def]))
QED


Theorem evaluate_fine_bstep_valid:
  ∀ varMap freshId f theIds freshId2 theCmd (st:'ffi semanticPrimitives$state) env E fVars.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
    evaluate_fine st env [f] ∧
    st.fp_state.canOpt = FPScope NoOpt ∧
    ids_unique varMap freshId ∧
    env_word_sim env.v E fVars ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ⇒
    bstep_valid theCmd E
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac
  \\ fs[toFloVerCmd_def, option_case_eq, pair_case_eq] \\ rveq
  >- (
    fs[bstep_valid_def]
    \\ qpat_x_assum ‘evaluate_fine _ _ [Let _ _ _]’ mp_tac
    \\ simp[Once evaluate_fine_def]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ strip_tac
    \\ drule evaluate_fine_eval_expr_valid
    \\ rpt (disch_then drule)
    \\ impl_tac
    >- (fs[freevars_def])
   \\ strip_tac
   \\ fs[bstep_valid_def]
   \\ imp_res_tac evaluatePropsTheory.evaluate_sing
   \\ fs[] \\ rveq \\ fs[freevars_def]
   \\ rename1 ‘evaluate st env [e1] = (stA, Rval [v1])’
   \\ ‘∃ vF1. eval_expr_float fexp1 E = SOME vF1 ∧ v_word_eq v1 vF1’
     by (irule FloVer_CakeML_float_sim_exp
          \\ fs[] \\ rpt (asm_exists_tac \\ fs[])
          \\ qexists_tac ‘env’ \\ qexists_tac ‘e1’ \\ fs[]
          \\ qexists_tac ‘freshId’  \\ fs[])
   \\ fs[optionLift_def]
   \\ first_x_assum drule
   \\ disch_then irule \\ fs[] \\ conj_tac
   >- (irule ids_unique_append \\ fs[])
   \\ qexists_tac ‘fVars ∪ { (Short x, freshId) }’ \\ rpt conj_tac
   >- (
     rpt strip_tac \\ fs[]
     >- (
       fs[lookupCMLVar_appendCMLVar]
       \\ ‘x' ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ fs[])
       \\ ‘y ≠ freshId’
         by (CCONTR_TAC
             \\ fs[] \\ rveq \\ res_tac
             \\ fs[ids_unique_def] \\ res_tac
             \\ fs[])
       \\ res_tac
       \\ fs[lookupCMLVar_def, updateTheory.FIND_def])
     \\ rveq \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def])
   >- (
     rpt strip_tac
     \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def]
     \\ TOP_CASE_TAC \\ fs[]
     \\ first_x_assum (qspec_then ‘x'’ mp_tac) \\ fs[]
     \\ disch_then assume_tac \\ fs[]
     \\ fs[])
   \\ simp[env_word_sim_def] \\ rpt strip_tac \\ fs[namespaceTheory.nsOptBind_def]
   >- (
     ‘cake_id ≠ Short x’
      by (CCONTR_TAC
          \\ fs[] \\ rveq \\ res_tac
          \\ fs[])
     \\ ‘flover_id ≠ freshId’
       by (CCONTR_TAC
           \\ fs[] \\ rveq \\ res_tac
           \\ fs[ids_unique_def] \\ res_tac
           \\ fs[])
     \\ fs[env_word_sim_def] \\ res_tac
     \\ fsrw_tac [SATISFY_ss] []
     \\ res_tac \\ fs[updFlEnv_def])
   >- (
     ‘cake_id ≠ Short x’
      by (CCONTR_TAC
          \\ fs[] \\ rveq \\ res_tac
          \\ fs[])
     \\ ‘flover_id ≠ freshId’
       by (CCONTR_TAC
           \\ fs[] \\ rveq \\ res_tac
           \\ fs[ids_unique_def] \\ res_tac
           \\ fs[])
     \\ fs[ml_progTheory.nsLookup_nsBind_compute]
     \\ fs[env_word_sim_def] \\ res_tac
     \\ fsrw_tac [SATISFY_ss] []
     \\ res_tac \\ rfs[updFlEnv_def] \\ fs[])
   >- (
     rveq \\ fs[ml_progTheory.nsLookup_nsBind_compute]
     \\ rveq \\ fs[v_word_eq_def, updFlEnv_def])
   \\ rveq \\ fs[updFlEnv_def] \\ rveq \\ fs[v_word_eq_def])
  \\ TRY (
     drule evaluate_fine_eval_expr_valid
     \\ rpt (disch_then drule)
     \\ fs[bstep_valid_def])
  \\ qpat_x_assum `evaluate_fine _ _ _` mp_tac
  \\ simp[Once evaluate_fine_def]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate_fine stUpd _ _’
  \\ ‘stUpd.fp_state.canOpt = FPScope NoOpt’  by (unabbrev_all_tac \\ fs[])
  \\ strip_tac \\ fs[freevars_def]
  \\ first_x_assum drule
  \\ rpt (disch_then drule) \\ fs[]
QED

Theorem evaluate_fine_bstep_noopt:
  ∀ varMap freshId f theIds freshId2 theCmd (st:'ffi semanticPrimitives$state) env E fVars.
    toFloVerCmd varMap freshId (FpOptimise NoOpt f) = SOME (theIds, freshId2, theCmd) ∧
    evaluate_fine st env [FpOptimise NoOpt f] ∧
    ids_unique varMap freshId ∧
    env_word_sim env.v E fVars ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ⇒
    bstep_valid theCmd E
Proof
  rpt gen_tac \\ simp[Once evaluate_fine_def, toFloVerCmd_def]
  \\ rpt strip_tac
  \\ drule evaluate_fine_bstep_valid
  \\ rpt (disch_then drule \\ fs[state_component_equality, fpState_component_equality])
QED

Theorem buildFloVerTypeMap_correct:
  ∀ floverVars x.
  MEM x floverVars ⇒
  ∃ m. FloverMapTree_find (Var x) (buildFloVerTypeMap floverVars) = SOME m
Proof
  Induct_on ‘floverVars’ \\ fs[]
  \\ rpt strip_tac \\ fs[buildFloVerTypeMap_def]
  \\ rveq
  \\ res_tac \\ fs[map_find_add]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem buildFloVerTypeMap_binds_map:
  ∀ x y ids floverVars varMap freshId.
  lookupFloVerVar y varMap = SOME (x,y) ∧
  getFloVerVarMap ids = SOME (floverVars, varMap, freshId) ⇒
  toRExpMap (buildFloVerTypeMap floverVars) (Var y) = SOME M64
Proof
  rpt strip_tac
  \\ imp_res_tac getFloVerVarMap_agrees_FloVer
  \\ rveq \\ fs[ExpressionAbbrevsTheory.toRExpMap_def]
  \\ qspec_then ‘floverVars’ assume_tac buildFloVerTypeMap_is_64Bit
  \\ fs[is64BitEnv_def]
  \\ imp_res_tac buildFloVerTypeMap_correct
  \\ res_tac \\ fs[]
QED

Theorem env_sim_from_word_sim:
  ! env Ed fVars Gamma.
  env_word_sim env Ed fVars /\
  (! x y v. (x,y) IN fVars /\ nsLookup env x = SOME v ==>
   (? m. Gamma (Var y) = SOME m ∧ type_correct v m)) ==>
  env_sim env (\ x. case Ed x of SOME w => SOME (fp64_to_real w) | _ => NONE) fVars Gamma
Proof
  rpt strip_tac \\ fs[env_word_sim_def, env_sim_def]
  \\ rpt strip_tac \\ res_tac \\ fs[type_correct_def] \\ rveq
  >- (
   Cases_on ‘v’ \\ fs[v_word_eq_def]
   \\ TRY (rename1 ‘v_word_eq (Litv l) r’ \\ Cases_on ‘l’ \\ fs[v_word_eq_def])
   \\ rveq \\ Cases_on ‘m’ \\ fs[type_correct_def, v_eq_def])
  \\ fs[option_case_eq] \\ rveq \\ res_tac
  \\ Cases_on ‘v’ \\ fs[v_word_eq_def]
   \\ TRY (rename1 ‘v_word_eq (Litv l) r’ \\ Cases_on ‘l’ \\ fs[v_word_eq_def])
   \\ rveq \\ Cases_on ‘m’ \\ fs[type_correct_def, v_eq_def]
QED

Definition extend_env_with_vars_def:
  extend_env_with_vars [] [] env = env ∧
  extend_env_with_vars (Short x::xs) (v::vs) env =
    (nsBind x (FP_WordTree (Fp_const v)) (extend_env_with_vars xs vs env)) ∧
  extend_env_with_vars _ _ env = env
End

Definition is_precond_sound_def:
  is_precond_sound [] [] P = T ∧
  is_precond_sound (x::xs) (v::vs) P =
  (let (vlo,vhi) = P x in
   vlo ≤ (fp64_to_real v) ∧ (fp64_to_real v) ≤ vhi ∧
   is_precond_sound xs vs P) ∧
  is_precond_sound _ _ _ = F
End

Theorem getFloVerVarMap_MEM_eq:
  ∀ theVars floverVars varMap freshId x y.
    getFloVerVarMap theVars = SOME (floverVars, varMap, freshId) ⇒
    MEM (x,y) varMap ⇒
    MEM x theVars
Proof
  Induct_on ‘theVars’ \\ fs[getFloVerVarMap_def]
  \\ rpt strip_tac
  \\ fs[option_case_eq, pair_case_eq]
  \\ rveq \\ res_tac
  \\ Cases_on ‘h’ \\ fs[] \\ rveq
  \\ fs[appendCMLVar_def] \\ rfs[]
  \\ res_tac \\ fs[]
QED

Theorem is_precond_sound_length:
  ∀ xs vs P.
    is_precond_sound xs vs P ⇒
    LENGTH xs = LENGTH vs
Proof
  Induct_on ‘xs’ \\ rpt strip_tac \\ Cases_on ‘vs’ \\ fs[is_precond_sound_def]
  \\ Cases_on ‘P h’ \\ fs[]
  \\ res_tac
QED

Theorem extend_env_with_vars_app:
  ∀ vs1 xs1 vs2 xs2 (env:(string, string, v) namespace).
  LENGTH vs1 = LENGTH xs1 ∧
  LENGTH vs2 = LENGTH xs2 ∧
  (∀ x. MEM x (xs1 ++ xs2) ⇒ ∃ n. x = Short n)⇒
  extend_env_with_vars (xs1 ++ xs2) (vs1 ++ vs2) env =
  extend_env_with_vars xs1 vs1 (extend_env_with_vars xs2 vs2 env)
Proof
  Induct_on ‘xs1’ \\ fs[extend_env_with_vars_def]
  \\ rpt strip_tac \\ Cases_on ‘vs1’ \\ Cases_on ‘h’
  \\ fs[extend_env_with_vars_def]
  >- (first_x_assum drule
      \\ rpt (disch_then drule)
      \\ impl_tac \\ fs[]
      \\ rpt strip_tac \\ fs[])
  \\ first_x_assum (qspec_then ‘Long m i’ mp_tac) \\ fs[]
QED

Theorem extend_env_with_vars_lookup:
  ∀ xs x vs (env:(string, string, v) namespace).
  ~ MEM x xs ⇒
  nsLookup (extend_env_with_vars xs vs env) x  = nsLookup env x
Proof
  Induct_on ‘xs’ \\ Cases_on ‘vs’ \\ fs[extend_env_with_vars_def]
  \\ rpt strip_tac
  \\ Cases_on ‘h'’ \\ fs[extend_env_with_vars_def]
QED

Theorem extended_env_defined:
  ∀ theVars floverVars varMap freshId vs env x y.
    getFloVerVarMap theVars = SOME (floverVars, varMap, freshId) ∧
    LENGTH theVars = LENGTH vs ∧
    MEM (x,y) varMap ⇒
    (∃ fp.
    nsLookup (extend_env_with_vars (REVERSE theVars) (REVERSE vs) env.v) x = SOME (FP_WordTree fp))
Proof
  Induct_on ‘theVars’ >- fs[getFloVerVarMap_def]
  \\ rpt strip_tac
  \\ imp_res_tac getFloVerVarMap_is_unique
  \\ ‘MEM x (h::theVars)’ by (imp_res_tac getFloVerVarMap_MEM_eq)
  \\ fs[getFloVerVarMap_def, option_case_eq, pair_case_eq]
  >- (
  Cases_on ‘h’ \\ fs[] \\ rveq
  \\ fs[appendCMLVar_def] \\ rfs[] \\ rveq
  \\ TRY (
     imp_res_tac getFloVerVarMap_is_unique
     \\ fs[ids_unique_def] \\ res_tac \\ fs[] \\ NO_TAC)
  \\ Cases_on ‘vs’ \\ fs[extend_env_with_vars_def]
  \\ ‘LENGTH (REVERSE t) = LENGTH (REVERSE theVars) ∧ LENGTH [h] = LENGTH [Short n]’
     by (cheat)
  \\ ‘∀ x. MEM x (REVERSE theVars ++ [Short n]) ⇒ ∃n. x = Short n’ by (cheat)
  \\ first_x_assum (mp_then Any mp_tac extend_env_with_vars_app)
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [‘[h]’, ‘env.v’] mp_tac)
  \\ strip_tac \\ fs[]
  \\ ‘~ MEM (Short n) (REVERSE theVars)’ by (cheat)
  \\ fs[extend_env_with_vars_lookup, extend_env_with_vars_def])
  \\ Cases_on ‘h’ \\ fs[] \\ rveq
  \\ Cases_on ‘vs’ \\ fs[extend_env_with_vars_def]
  \\ ‘LENGTH (REVERSE t) = LENGTH (REVERSE theVars) ∧ LENGTH [h] = LENGTH [Short n]’
     by (cheat)
  \\ ‘∀ x. MEM x (REVERSE theVars ++ [Short n]) ⇒ ∃n. x = Short n’ by (cheat)
  \\ first_x_assum (mp_then Any mp_tac extend_env_with_vars_app)
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [‘[h]’, ‘env.v’] mp_tac)
  \\ strip_tac \\ fs[]
  \\ fs[appendCMLVar_def] \\ rfs[] \\ rveq
  >- (
   ‘∃ y. MEM (Short n, y) ids’ by (cheat)
   \\ imp_res_tac getFloVerVarMap_is_unique
   \\ fs[ids_unique_def] \\ res_tac \\ fs[])
  \\ first_x_assum
     (qspecl_then [‘t’, ‘env with v := extend_env_with_vars ([Short n]:(string,string) id list) [h] env.v’, ‘x’, ‘y’] mp_tac)
  \\ impl_tac \\ fs[]
QED

Theorem extended_env_defined_strong:
  ∀ theVars floverVars varMap freshId vs env P x y.
    getFloVerVarMap theVars = SOME (floverVars, varMap, freshId) ∧
    is_precond_sound theVars vs P ∧
    LENGTH theVars = LENGTH vs ∧
    MEM (x,y) varMap ⇒
    ∃ fp.
    nsLookup (extend_env_with_vars (REVERSE theVars) (REVERSE vs) env.v) x = SOME (FP_WordTree fp) ∧
    FST (P x) ≤ fp64_to_real (compress_word fp) ∧
    fp64_to_real (compress_word fp) ≤ SND (P x)
Proof
  Induct_on ‘theVars’ >- fs[getFloVerVarMap_def]
  \\ rpt strip_tac
  \\ imp_res_tac getFloVerVarMap_is_unique
  \\ ‘MEM x (h::theVars)’ by (imp_res_tac getFloVerVarMap_MEM_eq)
  \\ fs[getFloVerVarMap_def, option_case_eq, pair_case_eq]
  >- (
   Cases_on ‘h’ \\ fs[] \\ rveq
   \\ fs[appendCMLVar_def] \\ rfs[] \\ rveq
   \\ TRY (
      imp_res_tac getFloVerVarMap_is_unique
      \\ fs[ids_unique_def] \\ res_tac \\ fs[] \\ NO_TAC)
   \\ Cases_on ‘vs’ \\ fs[extend_env_with_vars_def, is_precond_sound_def]
   \\ ‘LENGTH (REVERSE t) = LENGTH (REVERSE theVars) ∧ LENGTH [h] = LENGTH [Short n]’
     by (cheat)
   \\ ‘∀ x. MEM x (REVERSE theVars ++ [Short n]) ⇒ ∃n. x = Short n’ by (cheat)
   \\ first_x_assum (mp_then Any mp_tac extend_env_with_vars_app)
   \\ rpt (disch_then drule)
   \\ disch_then (qspecl_then [‘[h]’, ‘env.v’] mp_tac)
   \\ strip_tac \\ fs[]
   \\ ‘~ MEM (Short n) (REVERSE theVars)’ by (cheat)
         \\ fs[extend_env_with_vars_lookup, extend_env_with_vars_def]
         \\ Cases_on ‘P (Short n)’ \\ fs[fpSemTheory.compress_word_def])
  \\ Cases_on ‘h’ \\ fs[] \\ rveq
  \\ Cases_on ‘vs’ \\ fs[extend_env_with_vars_def, is_precond_sound_def]
  \\ ‘LENGTH (REVERSE t) = LENGTH (REVERSE theVars) ∧ LENGTH [h] = LENGTH [Short n]’
     by (cheat)
  \\ ‘∀ x. MEM x (REVERSE theVars ++ [Short n]) ⇒ ∃n. x = Short n’ by (cheat)
  \\ first_x_assum (mp_then Any mp_tac extend_env_with_vars_app)
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [‘[h]’, ‘env.v’] mp_tac)
  \\ strip_tac \\ fs[]
  \\ fs[appendCMLVar_def] \\ rfs[] \\ rveq
  >- (
   ‘∃ y. MEM (Short n, y) ids’ by (cheat)
   \\ imp_res_tac getFloVerVarMap_is_unique
   \\ fs[ids_unique_def] \\ res_tac \\ fs[])
  \\ first_x_assum
     (qspecl_then [‘t’, ‘env with v := extend_env_with_vars ([Short n]:(string,string) id list) [h] env.v’, ‘P’, ‘x’, ‘y’] mp_tac)
  \\ Cases_on ‘P (Short n)’ \\ fs[]
QED

Theorem getFloVerVarMap_list_eq:
  ∀ theVars floverVars varMap freshId.
    getFloVerVarMap theVars = SOME (floverVars, varMap, freshId) ⇒
    MAP FST varMap = theVars
Proof
  Induct_on ‘theVars’ \\ fs[getFloVerVarMap_def, option_case_eq, pair_case_eq]
  \\ rpt strip_tac \\ rveq
  \\ Cases_on ‘h’ \\ fs[] \\ rveq
  \\ fs[appendCMLVar_def]
QED

Theorem CakeML_FloVer_infer_error:
  ∀ (st:'ffi semanticPrimitives$state) env theVars vs e body floverVars varMap
  freshId freshId2 Gamma theIds theCmd P theBounds.
    (* evaluation does not run into subnormal numbers *)
    evaluate_fine st (env with v := extend_env_with_vars (REVERSE theVars) (REVERSE vs) env.v) [body] ∧
    stripFuns e = (theVars, body) ∧
    (* no icing optimizations allowed *)
    (∃ body'. body = FpOptimise NoOpt body') ∧
    getFloVerVarMap theVars = SOME (floverVars, varMap, freshId) ∧
    checkFreevars theVars (freevars_list [body]) ∧
    buildFloVerTypeMap floverVars = Gamma ∧
    toFloVerCmd varMap freshId body = SOME (theIds, freshId2, theCmd) ∧
    computeErrorbounds theCmd (mkFloVerPre P varMap) Gamma = SOME theBounds ∧
    is_precond_sound theVars vs P ⇒
  ∃ ids iv err r vF.
    (* the analysis result returned contains an error bound *)
    FloverMapTree_find (getRetExp (toRCmd theCmd)) theBounds = SOME (iv,err) /\
    (* the CakeML code returns a valid floating-point word *)
    evaluate (st with fp_state := st.fp_state with real_sem := T)
      (env with v := toRspace (extend_env_with_vars (REVERSE theVars) (REVERSE vs) env.v))
      [realify body] =
      (st with fp_state := st.fp_state with real_sem := T, Rval [Real r]) /\
    (* the CakeML code returns a valid floating-point word *)
    evaluate st (env with v := extend_env_with_vars (REVERSE theVars) (REVERSE vs) env.v) [body] =
      (st, Rval [vF] ) /\
    (* the roundoff error is sound *)
    ((∃ w. vF = Litv (Word64 w) ∧ real$abs (fp64_to_real w - r) ≤ err) ∨
     (∃ fp. vF = FP_WordTree fp ∧ real$abs (fp64_to_real (compress_word fp) - r) ≤ err))
Proof
  rpt strip_tac \\ imp_res_tac getFloVerVarMap_is_unique
  \\ rename [‘stripFuns e = (theVars, noOptBody)’, ‘FpOptimise NoOpt body’]
  \\ qspecl_then
     [‘varMap’, ‘λ (x,y). MEM (x,y) varMap’,
      ‘extend_env_with_vars (REVERSE theVars) (REVERSE vs) env.v’]
     mp_tac (GEN_ALL env_word_sim_inhabited)
  \\ impl_tac
  >- (
    rpt conj_tac
    >- (
      rpt strip_tac \\ ‘MEM (x,y) varMap’ by (fs[IN_DEF])
      \\ imp_res_tac toFloVerCmd_ids_unique
      \\ fs[ids_unique_def] \\ res_tac)
    \\ rpt strip_tac \\ ‘MEM (x,y) varMap’ by (fs[IN_DEF])
    \\ drule extended_env_defined
    \\ imp_res_tac is_precond_sound_length
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then ‘env’ assume_tac)
    \\ fsrw_tac [SATISFY_ss] [])
  \\ qmatch_goalsub_abbrev_tac ‘env_word_sim ext_env Enew fVars’
  \\ strip_tac
  \\ imp_res_tac env_sim_from_word_sim
  \\ first_x_assum (Q.SPEC_THEN ‘toRExpMap Gamma’ mp_tac)
  \\ impl_tac
  >- (
    rpt strip_tac \\ rveq
    \\ qspec_then ‘floverVars’ assume_tac buildFloVerTypeMap_is_64Bit
    \\ ‘MEM (x,y) varMap’ by (unabbrev_all_tac \\ fs[IN_DEF])
    \\ ‘lookupFloVerVar y varMap = SOME (x,y)’
      by (imp_res_tac toFloVerCmd_ids_unique \\ fs[ids_unique_def] \\ res_tac)
    \\ imp_res_tac buildFloVerTypeMap_binds_map
    \\ fs[is64BitEnv_def, ExpressionAbbrevsTheory.toRExpMap_def]
    \\ ‘x IN freevars [FpOptimise NoOpt body]’
      by (
      drule freevars_agree_varMap
      \\ rpt (disch_then drule)
      \\ disch_then irule
      \\ ‘MAP FST varMap = theVars’ by (imp_res_tac getFloVerVarMap_list_eq)
      \\ fs[ids_unique_def] \\ res_tac \\ fs[])
    \\ drule extended_env_defined
    \\ imp_res_tac is_precond_sound_length
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then ‘env’ assume_tac)
    \\ unabbrev_all_tac
    \\ rfs[type_correct_def])
  \\ qmatch_goalsub_abbrev_tac ‘env_sim ext_env Enew_real fVars’ \\ strip_tac
  \\ imp_res_tac env_sim_real_from_word_sim
  \\ pop_assum mp_tac \\ rfs[]
  \\ qpat_x_assum ‘computeErrorbounds _ _ _ = _’ mp_tac
  \\ simp[computeErrorbounds_def]
  \\ ntac 4 (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ fs[] \\ rveq
  \\ imp_res_tac CertificateCheckerTheory.CertificateCheckerCmd_Gamma_is_getValidMapCmd
  \\ fs[] \\ rveq
  \\ imp_res_tac IEEE_connection_cmds
  \\ first_x_assum
     (qspecl_then [‘Enew’, ‘Enew_real’] mp_tac)
  \\ impl_tac
  >- (
    ‘toREnv Enew = Enew_real’
      by (fs[FUN_EQ_THM]
          \\ rpt strip_tac \\ unabbrev_all_tac \\ fs[toREnv_def]
          \\ once_rewrite_tac [fp64_to_real_def]
          \\ rpt (TOP_CASE_TAC \\ fs[]))
    \\ pop_assum (rewrite_tac o single)
    \\ irule approxEnv_refl \\ rpt conj_tac \\ fs[]
    >- (
      rpt strip_tac \\ fs[]
      \\ unabbrev_all_tac \\ simp[]
      \\ rename1 ‘y ∉ domain (freeVars (toRCmd theCmd))’
      \\ Cases_on ‘lookupFloVerVar y varMap’ \\ fs[]
      \\ rename1 ‘lookupFloVerVar y varMap = SOME varp’ \\ Cases_on ‘varp’ \\ fs[]
      \\ imp_res_tac lookupFloVerVar_id_r \\ rveq
      \\ rename1 ‘lookupFloVerVar y varMap = SOME (cake_id, y)’
      \\ ‘MEM (cake_id, y) varMap’ by (irule lookupFloVerVar_mem \\ fs[])
      \\ ‘y IN domain (freeVars theCmd)’
        by (irule freeVars_agree_varMap
            \\ rpt (asm_exists_tac \\ fs[])
            \\ ‘MAP FST varMap = theVars’ suffices_by fs[]
            \\ imp_res_tac getFloVerVarMap_list_eq)
      \\ fs[toRCmd_freeVars_agree])
    (* invariant of construction of Gamma *)
    >- (
      rpt strip_tac \\ fs[]
      \\ rename1 ‘y IN domain (freeVars (toRCmd theCmd))’
      \\ ‘y IN domain (freeVars theCmd)’ by fs[toRCmd_freeVars_agree]
      \\ ‘∃ x. lookupFloVerVar y varMap = SOME (x,y)’
        by (imp_res_tac toFloVerCmd_freevars_freeVars \\ fs[])
      \\ imp_res_tac buildFloVerTypeMap_binds_map
      \\ fs[ExpressionAbbrevsTheory.toRExpMap_def]
      \\ ‘validTypesCmd (toRCmd theCmd) a’
         by (imp_res_tac getValidMapCmd_correct
             \\ first_x_assum irule  \\ EVAL_TAC \\ fs[])
      \\ imp_res_tac validTypesCmd_freevars
      \\ imp_res_tac getValidMapCmd_preserving
      \\ first_x_assum mp_tac  \\ impl_tac
      >- (qspec_then ‘floverVars’ assume_tac buildFloVerTypeMap_is_64Bit
          \\ rpt strip_tac \\ fs[is64BitEnv_def] \\ res_tac)
      \\ impl_tac
      >- (
       irule toFloVerCmd_is64BitBstep
       \\ asm_exists_tac \\ fs[])
      \\ impl_tac >- (EVAL_TAC \\ fs[])
      \\ strip_tac \\ res_tac \\ fs[])
    (* assumption from env simulation *)
    \\ rpt strip_tac \\ fs[] \\ unabbrev_all_tac
    \\ rename1 ‘y IN domain (freeVars (toRCmd theCmd))’
    \\ ‘y IN domain (freeVars theCmd)’ by fs[toRCmd_freeVars_agree]
    \\ simp[]
    \\ ‘∃ cake_id. lookupFloVerVar y varMap = SOME (cake_id, y)’
        by (imp_res_tac toFloVerCmd_freevars_freeVars \\ fs[])
    \\ simp[]
    \\ ‘lookupCMLVar cake_id varMap = SOME (cake_id, y)’
      by (fs[ids_unique_def])
    \\ ‘cake_id IN freevars [FpOptimise NoOpt body]’
      by (irule freevars_agree_varMap \\ rpt (asm_exists_tac \\ fs[])
          \\ ‘MAP FST varMap = theVars’ suffices_by fs[]
          \\ imp_res_tac getFloVerVarMap_list_eq)
    \\ drule extended_env_defined
    \\ imp_res_tac is_precond_sound_length
    \\ ‘MEM (cake_id, y) varMap’
       by (irule lookupCMLVar_mem \\ fs[])
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then ‘env’ assume_tac)
    \\ fsrw_tac [SATISFY_ss] [])
  \\ disch_then (qspec_then ‘freeVars (toRCmd theCmd)’ mp_tac)
  \\ impl_tac \\ fs[]
  \\ impl_tac
  >- (
   fs[RealRangeArithTheory.fVars_P_sound_def]
   \\ unabbrev_all_tac
   \\ ntac 7 (pop_assum kall_tac)
   \\ rpt strip_tac
   \\ rename1 ‘y IN domain (freeVars (toRCmd theCmd))’
   \\ ‘y IN domain (freeVars theCmd)’
      by (fs[toRCmd_freeVars_agree])
   \\ ‘∃ x. lookupFloVerVar y varMap = SOME (x,y) ∧
       x IN freevars [FpOptimise NoOpt body]’
      by (drule toFloVerCmd_freevars_freeVars
          \\ rpt (disch_then drule)
          \\ fs[])
   \\ fs[]
   \\ ‘MEM (x,y) varMap’
      by (imp_res_tac lookupFloVerVar_mem \\ fs[])
   \\ ‘MEM x theVars’
      by (imp_res_tac getFloVerVarMap_MEM_eq)
   \\ drule extended_env_defined_strong
   \\ imp_res_tac is_precond_sound_length
   \\ rpt (disch_then drule)
   \\ disch_then (qspec_then ‘env’ assume_tac)
   \\ fs[mkFloVerPre_def])
  \\ impl_tac
  >- (
    drule evaluate_fine_bstep_noopt
    \\ rpt (disch_then drule)
    \\ disch_then irule
    \\ qexists_tac ‘λ (x,y). MEM (x,y) varMap’ \\ rpt conj_tac
    >- (rpt strip_tac \\ ‘MEM (x',y) varMap’ by fs[IN_DEF] \\ res_tac \\ fs[ids_unique_def])
    >- (
     rpt strip_tac
     \\ ‘∃ y. MEM (x',y) varMap’
      by (imp_res_tac toFloVerCmd_freeVars_freevars
          \\ fs[freevars_def]
          \\ pop_assum imp_res_tac
          \\ fs[ids_unique_def]
          \\ res_tac \\ fs[] \\ rveq
          \\ imp_res_tac lookupCMLVar_mem
          \\ fsrw_tac [SATISFY_ss] [])
      \\ fs[ids_unique_def] \\ res_tac
      \\ unabbrev_all_tac \\ rveq \\ fs[IN_DEF] \\ rveq \\ fs[])
    \\ unabbrev_all_tac \\ fs[sem_env_component_equality])
  \\ impl_tac
  (* invariant of the translation to FloVer: noDowncastFun is true *)
  >- (
    irule toFloVerCmd_noDowncastFun
    \\ asm_exists_tac \\ fs[])
  \\ impl_tac
  (* invariant of getFloVerVarMap: is64BitEnv (buildFloVerTypeMap floverVars) *)
  >- (irule is64BitEnv_buildFloVerTypeMap)
  \\ impl_tac
  (* invariant of translation to FloVer: is64BitBstep (toRCmd theCmd) *)
  >- (
    irule toFloVerCmd_is64BitBstep
    \\ asm_exists_tac \\ fs[])
  \\ disch_then assume_tac \\ fs[]
  \\ ‘(st with fp_state := st.fp_state with real_sem := T).fp_state.real_sem’
    by (fs[])
  (* Simulation 1: We can get the same result as the FloVer reals from CakeML reals *)
  \\ first_x_assum (mp_then Any mp_tac CakeML_FloVer_real_sim)
  \\ rpt (disch_then drule)
  \\ disch_then
     (qspecl_then
      [‘Enew_real’, ‘env with v := toRspace ext_env’, ‘fVars’, ‘toRExpMap a’, ‘vR'’] mp_tac)
  \\ impl_tac \\ fs[]
  >- (
   rpt conj_tac \\ fs[ExpressionAbbrevsTheory.toRExpMap_def]
   >- (
    rpt strip_tac
    \\ ‘MEM (x', y) varMap’ by (unabbrev_all_tac \\ fs[IN_DEF])
    \\ fs[ids_unique_def] \\ res_tac)
   \\ rpt strip_tac
   \\ ‘∃y. MEM (x', y) varMap’
     by (imp_res_tac toFloVerCmd_freeVars_freevars
         \\ imp_res_tac lookupCMLVar_mem
         \\ unabbrev_all_tac
         \\ fsrw_tac [SATISFY_ss] [IN_DEF])
   \\ fs[ids_unique_def] \\ res_tac \\ unabbrev_all_tac \\ fs[IN_DEF])
  \\ disch_then assume_tac \\ fs[]
  (* Simulation 2: We can get the same result as FloVer floats for CakeML *)
  \\ first_x_assum (mp_then Any mp_tac CakeML_FloVer_float_sim_noopt)
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [‘env with v := ext_env’, ‘fVars’] mp_tac)
  \\ impl_tac
  >- (
    rpt conj_tac \\ fs[]
    \\ rpt strip_tac
    \\ res_tac \\ fs[ids_unique_def]
    >- (
     ‘MEM (x',y) varMap’ by (unabbrev_all_tac \\ fs[IN_DEF])
     \\ res_tac \\ fs[])
    \\ ‘∃ y. MEM (x', y) varMap’
      by (imp_res_tac toFloVerCmd_freeVars_freevars
          \\ pop_assum mp_tac
          \\ impl_tac \\ fs[ids_unique_def]
          >- (rpt strip_tac \\ res_tac \\ fs[])
          \\ strip_tac
          \\ ‘∃ y. lookupCMLVar x' varMap = SOME (x',y)’
             by (res_tac \\ fs[])
          \\ imp_res_tac lookupCMLVar_mem
          \\ fsrw_tac [SATISFY_ss] [])
    \\ res_tac \\ unabbrev_all_tac \\ fs[IN_DEF])
  \\ disch_then (qspec_then ‘st’ assume_tac) \\ fs[]
  \\ Cases_on ‘vFC’ \\ fs[v_word_eq_def]
  \\ TRY (Cases_on ‘l’ \\ fs[v_word_eq_def])
  \\ rveq
  \\ fsrw_tac [SATISFY_ss] [fpSemTheory.compress_word_def]
  \\ once_rewrite_tac [ABS_SUB]
  \\ simp[fp64_to_real_def]
QED

val _ = export_theory ();

(*
Theorem isFloVerExps_toFloVerExp_succeeds:
  ∀ es.
    isFloVerExps es ⇒
    ∀ e. MEM e es ⇒
      ∀ ids freshId.
        ∃ ids2 freshId2 fexp.
        toFloVerExp ids freshId e = SOME (ids2, freshId2, fexp)
Proof
  ho_match_mp_tac isFloVerExps_ind
  \\ rpt strip_tac \\ rfs [] \\ rveq \\ TRY (fs[isFloVerExps_def]\\ NO_TAC)
  >- (fs[isFloVerExps_def, toFloVerExp_def, lookupCMLVar_def]
      \\ rpt (TOP_CASE_TAC \\ fs[]))
  \\ Cases_on ‘op’ \\ fs[isFloVerExps_def, quantHeuristicsTheory.LIST_LENGTH_3]
  \\ rveq \\ fs[]
  >- (
    Cases_on ‘f’ \\ fs[] \\ rveq \\ fs[]
    \\ simp[toFloVerExp_def]
    \\ first_x_assum (qspecl_then [‘ids’,‘freshId’] assume_tac) \\ fs[])
  >- (
     simp[toFloVerExp_def]
     \\ first_assum (qspec_then ‘e1’ assume_tac)
     \\ first_x_assum (qspec_then ‘e2’ assume_tac)
     \\ fs[]
     \\ last_x_assum (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
     \\ last_x_assum (qspecl_then [‘ids2’, ‘freshId2’] assume_tac) \\ fs[])
  \\ simp[toFloVerExp_def]
  \\ first_assum (qspec_then ‘e1’ assume_tac)
  \\ first_assum (qspec_then ‘e2’ assume_tac)
  \\ first_x_assum (qspec_then ‘e3’ assume_tac)
  \\ fs[]
  \\ last_x_assum (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
  \\ last_x_assum (qspecl_then [‘ids2’, ‘freshId2’] assume_tac) \\ fs[]
  \\ rename1 ‘toFloVerExp ids2 freshId2 e2 = SOME (ids3, freshId3, fexp2)’
  \\ last_x_assum (qspecl_then [‘ids3’, ‘freshId3’] assume_tac) \\ fs[]
QED
*)

(*
Theorem isFloVerCmd_toFloVerCmd_succeeds:
  ∀ e ids freshId.
    isFloVerCmd e ⇒
    ∃ ids2 freshId2 f.
      toFloVerCmd ids freshId e = SOME (ids2, freshId2, f)
Proof
  ho_match_mp_tac isFloVerCmd_ind
  \\ rpt strip_tac \\ fs[isFloVerCmd_def, toFloVerCmd_def]
  >- (
   Cases_on ‘so’ \\ fs[lookupCMLVar_def, updateTheory.FIND_def]
   \\ drule isFloVerExps_toFloVerExp_succeeds \\ fs[]
   \\ disch_then (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
   \\ first_x_assum (qspecl_then [‘appendCMLVar (Short x) freshId2 ids2’, ‘freshId2 + 1’] assume_tac)
   \\ fs[])
  >- (
   drule isFloVerExps_toFloVerExp_succeeds
    \\ disch_then (qspecl_then [‘App op exps’,‘ids’, ‘freshId’] assume_tac) \\ fs[])
  \\ fs[toFloVerExp_def]
  \\ Cases_on ‘lookupCMLVar x ids’ \\ fs[]
  \\ rename1 ‘lookupCMLVar x ids = SOME v’
  \\ Cases_on ‘v’ \\ fs[]
QED

(**
  If toFloVerPre constructs a precondition from a CakeML precondition
  with multiple constraints it cannot overwrite bound variables *)
Theorem toFloVerPre_bind_single:
  ∀ e1 e2 ids floverP dVars floverP2 dVars2 x lo hi n.
    toFloVerPre [Log And e1 e2] (ids:((string, string) id # num) list) =
      SOME (floverP,dVars) ⇒
    getInterval (Log And e1 e2) = NONE (* compound case *) ∧
    getInterval e1 = SOME (x, lo, hi) ∧
    toFloVerPre [e2] ids = SOME (floverP2, dVars2) ∧
    lookupCMLVar (Short x) ids = SOME (Short x,n) ⇒
    ~ (Short x IN freevars [e2])
Proof
  rpt strip_tac \\ fs[toFloVerPre_def]
  \\ Cases_on ‘FIND (λ m. n = m) dVars2’ \\ fs[] \\ rveq
  \\ imp_res_tac toFloVerPre_freevar_FIND \\ fs[] \\ rveq \\ fs[]
QED

Theorem getInterval_preserves_bounds:
  ∀ e lo hi (st:α semanticPrimitives$state) env st2 E ids
    freshId fVars x y z Gamma.
    getInterval e = SOME (x, lo, hi) ∧
    st.fp_state.canOpt = FPScope NoOpt ∧
    evaluate st env [e] = (st2, Rval [Boolv T]) ∧
    env_sim env.v E fVars Gamma ∧
    ids_unique ids freshId ∧
    (∀ x. x IN freevars [e] ⇒ ∃ y. lookupCMLVar x ids = SOME (x,y) ∧ (x,y) IN fVars) ∧
    lookupFloVerVar y ids = SOME (Short x, y) ∧
    lookupCMLVar (Short x) ids = SOME (Short x, z) ⇒
    ∃ v.
      E y = SOME v ∧
      FST ((λ n. if n = z then (lo,hi) else (0,0)) y) ≤ v ∧
      v ≤ SND ((λ n. if n = z then (lo,hi) else (0,0)) y)
Proof
  rpt strip_tac
  \\ first_assum (mp_then Any assume_tac getInterval_inv)
  \\ fs[] \\ rveq
  \\ ‘y = z’ by (fs[ids_unique_def])
  \\ rveq \\ fs[]
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[evaluate_def]
  \\ Cases_on ‘nsLookup env.v (Short x)’
  \\ simp[astTheory.getOpClass_def, astTheory.isFpBool_def, do_app_def,
          fp_translate_def]
  \\ rename1 ‘nsLookup env.v (Short x) = SOME v’
  \\ fs[env_sim_def] \\ first_x_assum (qspecl_then [‘Short x’, ‘y’] assume_tac)
  \\ rfs[]
  \\ Cases_on ‘v’ \\ simp[fp_translate_def]
  THENL [rename1 ‘Litv l’ \\ Cases_on ‘l’
         \\ simp [fp_translate_def],
         ALL_TAC]
  \\ simp [do_log_def, fpValTreeTheory.fp_cmp_def, fpSemTheory.fp_cmp_comp_def,
           fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  THENL [
    Cases_on ‘fp64_lessEqual w1 c’,
    Cases_on ‘fp64_lessEqual w1 (compress_word f)’]
  \\ simp[evaluate_def, astTheory.getOpClass_def,
          astTheory.isFpBool_def, do_app_def, fp_translate_def]
  \\ simp[fpValTreeTheory.fp_cmp_def, fpSemTheory.fp_cmp_comp_def,
          fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  \\ rpt strip_tac \\ rveq
  \\ first_x_assum (qspec_then ‘r’ assume_tac)
  \\ fs[v_eq_def, fp64_to_real_def, fp64_isFinite_def, fp64_lessEqual_def]
  THENL [
    ‘float_is_finite (fp64_to_float c)’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] []),
    ‘float_is_finite (fp64_to_float c)’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] []),
    ‘float_is_finite (fp64_to_float (compress_word f))’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] []),
    ‘float_is_finite (fp64_to_float (compress_word f))’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] [])]
  \\ res_tac
  \\ fs[v_eq_float, v_eq_valtree] \\ rveq \\ simp[fp64_to_real_def]
  \\ metis_tac [lift_ieeeTheory.float_le]
QED

(**
  Prove a relation between the CakeML precondition and the translated
  FloVer precondition.
  If the CakeML precondition is true (i.e. evaluate terminates with Boolv True)
  and the FloVer and CakeML environments agree on the values for the variables
  of the precondition, then the FloVer environment must respect the precondition
  too **)
Theorem toFloVerPre_preserves_bounds:
  ∀ cake_P ids floverP dVars Gamma.
    (* We can extract a precondition *)
    toFloVerPre cake_P (ids:((string, string) id # num) list) = SOME (floverP,dVars) ⇒
    ∀ st (st2:α semanticPrimitives$state) env E fVars freshId.
      st.fp_state.canOpt = FPScope NoOpt ∧
      (* the free variables are paired up in the id list, and defined *)
      env_sim env.v E fVars Gamma ∧
      ids_unique ids freshId ∧
      (∀ x. x IN freevars cake_P ⇒ ∃ y. lookupCMLVar x ids = SOME (x,y) ∧ (x,y) IN fVars) ∧
      (* the precondition can be evaluated to True *)
      evaluate st env cake_P = (st2, Rval ([Boolv T])) ⇒
      ∀ n x.
        lookupFloVerVar n ids = SOME (x,n) ∧
        x IN freevars cake_P ⇒
      ∃ v. E n = SOME v ∧
      IVlo (floverP n) ≤ v ∧
      v ≤ IVhi (floverP n)
Proof
  ho_match_mp_tac toFloVerPre_ind
  \\ rpt strip_tac \\ fs[toFloVerPre_def]
  \\ qpat_x_assum ‘_ = SOME (floverP, _)’ mp_tac
  \\ reverse TOP_CASE_TAC \\ fs[]
  (* Base case: top expression is an interval constraint *)
  >- (
    rpt (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ imp_res_tac getInterval_inv \\ rveq \\ fs[] \\ rveq
    \\ drule getInterval_preserves_bounds
    \\ rpt (disch_then drule)
    \\ disch_then (qspecl_then [‘n’, ‘r’] mp_tac) \\ impl_tac
    \\ fs[])
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[evaluate_def]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ simp[do_log_def]
  \\ rename1 ‘evaluate st env [e1] = (st1, Rval v)’
  \\ reverse (Cases_on ‘HD v = Boolv T’) \\ fs[]
  >- (Cases_on ‘HD v = Boolv F’ \\ fs[])
  \\ strip_tac \\ fs[]
  \\ first_x_assum (qspecl_then [‘Gamma’,‘st1’, ‘st2’, ‘env’, ‘E’, ‘fVars’, ‘freshId’] mp_tac)
  \\ impl_tac \\ fs[]
  >- (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[freevars_def])
  \\ rpt strip_tac \\ imp_res_tac evaluatePropsTheory.evaluate_sing
  \\ fs[] \\ rveq \\ fs[freevars_def]
  (* Base case again *)
  >- (
    imp_res_tac getInterval_inv \\ rveq \\ fs[] \\ rveq
    \\ drule getInterval_preserves_bounds
    \\ rpt (disch_then drule)
    \\ imp_res_tac lookupCMLVar_id_l \\ rveq
    \\ disch_then (qspecl_then [‘n’, ‘r’] mp_tac) \\ impl_tac
    \\ fs[]
    \\ ‘n = r’ by (fs[ids_unique_def])
    \\ rveq \\ fs[])
  \\ res_tac \\ qexists_tac ‘v’
  \\ fs[] \\ rveq
  \\ ‘n ≠ r’ suffices_by (fs[])
  \\ CCONTR_TAC \\ fs[] \\ rveq
  \\ imp_res_tac lookupCMLVar_id_l \\ rveq
  \\ ‘n = y’ by (fs[ids_unique_def])
  \\ rveq \\ fs[]
  \\ ‘x = Short q’ by (fs[ids_unique_def])
  \\ rveq \\ fs[]
  \\ imp_res_tac getInterval_inv
  \\ rename1 ‘toFloVerPre [e2] ids = SOME (flover_P, ids2)’
  \\ qspecl_then [‘e1’, ‘e2’, ‘ids’] mp_tac toFloVerPre_bind_single
  \\ simp[toFloVerPre_def] \\ rveq \\ fs[]
QED

*)

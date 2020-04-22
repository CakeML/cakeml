(* HOL4 *)
open machine_ieeeTheory realTheory realLib RealArith;
(* CakeML *)
open compilerTheory;
(* FloVer *)
open ExpressionsTheory CommandsTheory IEEE_connectionTheory;
(* Icing *)
open CakeMLtoFloVerTheory;
open preamble;

val _ = new_theory "CakeMLtoFloVerProofs";

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

Theorem toFloVerExp_usedVars:
  ∀ ids freshId e ids2 freshId2 fexp.
    toFloVerExp ids freshId e = SOME (ids2, freshId2, fexp) ⇒
    ∀ n. freshId ≤ n ∧ n < freshId2 ⇒
      n IN domain (usedVars (fexp))
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac \\ fs[toFloVerExp_def]
  >- (
   qpat_x_assum ‘_ = SOME _’ mp_tac
   \\ rpt (TOP_CASE_TAC \\ fs[])
   \\ rpt strip_tac \\ rveq \\ fs[usedVars_def])
  \\ qpat_x_assum ‘_ = SOME _’ mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq \\ simp[Once usedVars_def, domain_union]
  \\ TRY (metis_tac[])
  \\ TRY (Cases_on ‘n < q'’\\ fs[] \\ metis_tac[])
  \\ TRY (Cases_on ‘n < q'’\\ fs[] \\ TRY (metis_tac[])
          \\ Cases_on ‘n < q'3'’ \\ fs[] \\ metis_tac[])
QED

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

Definition freevars_def:
  freevars [] = EMPTY ∧
  freevars [ast$Var n] = { n } ∧
  freevars [Lit l] = EMPTY ∧
  freevars [Raise e] = freevars [e] ∧
  freevars [Handle e pes] =
    FOLDL (λ vars. λ (p,e). (freevars [e]) ∪ vars) (freevars [e]) pes ∧
  freevars [Con id es] = freevars es ∧
  freevars [Fun s e] = freevars [e] DIFF { Short s } ∧
  freevars [App op es] = freevars es ∧
  freevars [Log lop e1 e2] = (freevars [e1] ∪ freevars [e2]) ∧
  freevars [If e1 e2 e3] = (freevars [e1] ∪ freevars [e2] ∪ freevars [e3]) ∧
  freevars [Mat e pes] =
    FOLDL (λ vars. λ (p,e). (freevars [e]) ∪ vars) (freevars [e]) pes ∧
  freevars [Let x e1 e2] =
    freevars [e1] ∪
    (freevars [e2] DIFF (case x of | NONE => EMPTY | SOME s => { Short s })) ∧
  freevars [Letrec fs e] = EMPTY (* TODO *) ∧
  freevars [Tannot e t] = freevars [e] ∧
  freevars [Lannot e l] = freevars [e] ∧
  freevars [FpOptimise opt e] = freevars [e] ∧
  freevars (e1::es) =
    freevars [e1] ∪ freevars es
Termination
  wf_rel_tac ‘measure exp6_size’ \\ fs[]
  \\ Induct_on ‘pes’ \\ fs[]
  \\ rpt strip_tac \\ simp[astTheory.exp_size_def]  \\ rveq
  \\ res_tac
  >- (simp[astTheory.exp_size_def])
  \\ first_x_assum (qspec_then ‘e’ assume_tac) \\ fs[]
End

Theorem lookupCMLVar_id_l:
  lookupCMLVar x ids = SOME (y, n) ⇒
  x = y
Proof
  Induct_on ‘ids’ \\ fs[lookupCMLVar_def, updateTheory.FIND_def]
  \\ strip_tac \\ rename1 ‘(λ (m,i). x = m) h’ \\ Cases_on ‘h’ \\  fs[]
  \\ TOP_CASE_TAC \\ fs[]
QED

Theorem getInterval_inv:
  getInterval e = SOME (x,lo,hi) ⇒
  freevars [e] = { Short x } ∧
  ∃ w1 w2.
  e = Log And (App (FP_cmp FP_LessEqual) [Lit (Word64 w1); Var (Short x)])
  (App (FP_cmp FP_LessEqual) [Var (Short x); Lit (Word64 w2)]) ∧
  lo = fp64_to_real w1 ∧
  hi = fp64_to_real w2 ∧
  fp64_isFinite w1 ∧
  fp64_isFinite w2
Proof
  Cases_on ‘e’ \\ simp[getInterval_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq \\ fs[freevars_def]
QED

Theorem toFloVerPre_freevar_FIND:
  ∀ cake_P ids floverP dVars.
  toFloVerPre cake_P ids = SOME (floverP, dVars) ⇒
  ∀ x. x IN freevars cake_P ⇒
  ∃ n m. lookupCMLVar x ids = SOME (x, n) ∧
  FIND (λ m. n = m) dVars = SOME m
Proof
  ho_match_mp_tac toFloVerPre_ind
  \\ rpt strip_tac \\ fs[toFloVerPre_def]
  \\ qpat_x_assum ‘_ = SOME (_, _)’ mp_tac
  \\ reverse TOP_CASE_TAC \\ fs[]
  >- (
    rpt (TOP_CASE_TAC \\ fs[])
    \\ first_assum (mp_then Any assume_tac getInterval_inv)
    \\ rpt strip_tac \\ fs[] \\ rveq
    \\ first_assum (mp_then Any assume_tac lookupCMLVar_id_l)
    \\ rveq \\ fsrw_tac [SATISFY_ss] [updateTheory.FIND_def])
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ fs[freevars_def]
  >- (
    first_assum (mp_then Any assume_tac getInterval_inv)
    \\ first_assum (mp_then Any assume_tac lookupCMLVar_id_l)
    \\ fs[] \\ rveq
    \\ fsrw_tac [SATISFY_ss] [updateTheory.FIND_def])
  \\ res_tac
  \\ imp_res_tac lookupCMLVar_id_l \\ rveq
  \\ fsrw_tac [SATISFY_ss] [updateTheory.FIND_def]
  \\ TOP_CASE_TAC \\ fs[]
QED

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

Definition v_eq_def:
  v_eq (FP_WordTree fp) r = (r = fp64_to_real (compress_word fp)) ∧
  v_eq (Litv (Word64 w)) r = (r = fp64_to_real w) ∧
  v_eq _ _ = F
End

(**
  Relation: env_sim
  Arguments:
    The CakeML environment env, the FloVer environment E, and a set of pairs of
    CakeML * FloVer variables
  The environments env and E are in relation with each other for the set of
  variables fVars, if and only if the for every pair of variables
  (cake_id, flover_id):
  whenever the CakeML environment binds the the variable cake_id to a 64-bit
  word, the FloVer environment binds flover_id to the words real equivalent, and
  whenever the CakeM environment binds the variable to a value tree,
  the FloVer environment binds flover_id to the real equivalent of the
  compressed tree **)
Definition env_sim_def:
  env_sim env E fVars =
    (∀ (cake_id:(string, string) id) (flover_id:num).
      (cake_id, flover_id) IN fVars ⇒
      (∀ v. ∃ r.
      nsLookup env cake_id = SOME v ⇒
      E flover_id = SOME r ∧ v_eq v r) ∧
      (∀ r. ∃ v.
      E flover_id = SOME r ⇒
      nsLookup env cake_id = SOME v ∧ v_eq v r))
End

Definition ids_unique_def:
  ids_unique ids =
  ((∀ x y z.
    lookupCMLVar x ids = SOME (x, y) ∧
    lookupFloVerVar z ids = SOME (x, z) ⇒
    z = y) ∧
  (∀ x y z.
    lookupCMLVar (Short x) ids = SOME (Short x, z) ∧
    lookupFloVerVar z ids = SOME (Short y, z) ⇒
    x = y) ∧
  (∀ x y z.
    lookupCMLVar x ids = SOME (x,z) ∧
    lookupCMLVar y ids = SOME (y,z) ⇒
    x = y) ∧
  (∀ x y z.
    lookupFloVerVar x ids = SOME (z,x) ∧
    lookupFloVerVar y ids = SOME (z,y) ⇒
    x = y) ∧
  (∀ x y.
    lookupFloVerVar x ids = SOME (y, x) ⇒
    lookupCMLVar y ids = SOME (y,x)) ∧
  (∀ x y.
    lookupCMLVar y ids = SOME (y,x) ⇒
    lookupFloVerVar x ids = SOME (y, x)))
End

Theorem getInterval_preserves_bounds:
  ∀ e lo hi (st:α semanticPrimitives$state) env st2 E ids fVars x y z.
    getInterval e = SOME (x, lo, hi) ∧
    st.fp_state.canOpt = FPScope NoOpt ∧
    evaluate st env [e] = (st2, Rval [Boolv T]) ∧
    env_sim env.v E fVars ∧
    ids_unique ids ∧
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
  \\ simp[terminationTheory.evaluate_def]
  \\ Cases_on ‘nsLookup env.v (Short x)’
  \\ simp[astTheory.getOpClass_def, astTheory.isFpBool_def,
          semanticPrimitivesTheory.do_app_def,
          semanticPrimitivesTheory.fp_translate_def]
  \\ rename1 ‘nsLookup env.v (Short x) = SOME v’
  \\ fs[env_sim_def] \\ first_x_assum (qspecl_then [‘Short x’, ‘y’] assume_tac)
  \\ rfs[]
  \\ Cases_on ‘v’ \\ simp[semanticPrimitivesTheory.fp_translate_def]
  THENL [rename1 ‘Litv l’ \\ Cases_on ‘l’
         \\ simp [semanticPrimitivesTheory.fp_translate_def],
         ALL_TAC]
  \\ simp [semanticPrimitivesTheory.do_log_def,
           fpValTreeTheory.fp_cmp_def, fpSemTheory.fp_cmp_comp_def,
           fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  THENL [
    Cases_on ‘fp64_lessEqual w1 c’,
    Cases_on ‘fp64_lessEqual w1 (compress_word f)’]
  \\ simp[terminationTheory.evaluate_def, astTheory.getOpClass_def,
          astTheory.isFpBool_def, semanticPrimitivesTheory.do_app_def,
          semanticPrimitivesTheory.fp_translate_def]
  \\ simp[fpValTreeTheory.fp_cmp_def, fpSemTheory.fp_cmp_comp_def,
          fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  \\ rpt strip_tac \\ rveq
  THENL [
     first_x_assum (qspec_then ‘Litv (Word64 c)’ assume_tac),
     first_x_assum (qspec_then ‘FP_WordTree f’ assume_tac)]
  \\ fs[v_eq_def]
  \\ fs[fp64_to_real_def, fp64_isFinite_def, fp64_lessEqual_def]
  THENL [
    ‘float_is_finite (fp64_to_float c)’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] []),
    ‘float_is_finite (fp64_to_float (compress_word f))’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] [])]
  \\ conj_tac \\ metis_tac [lift_ieeeTheory.float_le]
QED

(**
  Prove a relation between the CakeML precondition and the translated
  FloVer precondition.
  If the CakeML precondition is true (i.e. evaluate terminates with Boolv True)
  and the FloVer and CakeML environments agree on the values for the variables
  of the precondition, then the FloVer environment must respect the precondition
  too **)
Theorem toFloVerPre_preserves_bounds:
  ∀ cake_P ids floverP dVars.
    (* We can extract a precondition *)
    toFloVerPre cake_P (ids:((string, string) id # num) list) = SOME (floverP,dVars) ⇒
    ∀ st (st2:α semanticPrimitives$state) env E fVars.
      st.fp_state.canOpt = FPScope NoOpt ∧
      (* the free variables are paired up in the id list, and defined *)
      env_sim env.v E fVars ∧
      ids_unique ids ∧
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
  \\ simp[terminationTheory.evaluate_def]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ simp[semanticPrimitivesTheory.do_log_def]
  \\ rename1 ‘evaluate st env [e1] = (st1, Rval v)’
  \\ reverse (Cases_on ‘HD v = Boolv T’) \\ fs[]
  >- (Cases_on ‘HD v = Boolv F’ \\ fs[])
  \\ strip_tac \\ fs[]
  \\ first_x_assum (qspecl_then [‘st1’, ‘st2’, ‘env’, ‘E’, ‘fVars’] mp_tac)
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

Theorem prepareVars_is_unique:
  ∀ ids floverVars varMap freshId.
    prepareVars ids = (floverVars, varMap, freshId) ⇒
    ids_unique varMap ∧
    (∀ id. freshId ≤ id ⇒ lookupFloVerVar id varMap = NONE) ∧
    (∀ x y. lookupCMLVar x varMap = SOME (x, y) ⇒
     y < freshId)
Proof
  Induct_on ‘ids’ \\ fs[prepareVars_def]
  >- (
    rpt strip_tac \\ fs[] \\ rveq
    \\ fs[ids_unique_def, lookupCMLVar_def, lookupFloVerVar_def,
          updateTheory.FIND_def])
  \\ Cases_on ‘prepareVars ids’ \\ rename1 ‘prepareVars ids = (floverVars, p)’
  \\ Cases_on ‘p’ \\ rename1 ‘prepareVars ids = (floverVars, varMap, freshId)’
  \\ fs[ids_unique_def] \\ rpt strip_tac \\ rpt conj_tac
  \\ fs[appendCMLVar_def]
  \\ Cases_on ‘lookupCMLVar (Short h) varMap’
  \\ fs[lookupCMLVar_def, lookupFloVerVar_def, updateTheory.FIND_def]
  \\ every_case_tac \\ rveq \\ fs[]
  \\ res_tac \\ rveq \\ fs[]
QED

Theorem toFloVerExp_noDowncast:
  ∀ varMap freshId e theIds freshId2 theExp.
    toFloVerExp varMap freshId e = SOME (theIds, freshId2, theExp) ⇒
    noDowncast (toRExp theExp)
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac \\ fs[toFloVerExp_def, toRExp_def, noDowncast_def]
  \\ rveq \\ fs[toRExp_def, noDowncast_def]
  \\ every_case_tac \\ fs[] \\ rveq
  \\ fs[toRExp_def, noDowncast_def]
QED

Theorem toFloVerCmd_noDowncastFun:
  ∀ varMap freshId f theIds freshId2 theCmd.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ⇒
    noDowncastFun (toRCmd theCmd)
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def, toRCmd_def, noDowncastFun_def]
  \\ every_case_tac \\ fs[toRCmd_def, noDowncastFun_def] \\ rveq
  \\ fs[toRCmd_def, noDowncastFun_def]
  \\ irule toFloVerExp_noDowncast \\ asm_exists_tac \\ fs[]
QED

Theorem is64BitEnv_prepareGamma:
  ∀ floverVars. is64BitEnv (prepareGamma floverVars)
Proof
  Induct_on ‘floverVars’ \\ fs[is64BitEnv_def, prepareGamma_def]
  >- (
   rpt strip_tac
   \\ fs[FloverMapTheory.FloverMapTree_find_def,
         FloverMapTheory.FloverMapTree_empty_def])
  \\ rpt strip_tac \\ fs[FloverMapTheory.map_find_add]
  \\ every_case_tac \\ fs[] \\ res_tac
QED

Theorem toFloVerExp_is64BitEval:
  ∀ varMap freshId e theIds freshId2 theExp.
    toFloVerExp varMap freshId e = SOME (theIds, freshId2, theExp) ⇒
    is64BitEval (toRExp theExp)
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac \\ fs[toFloVerExp_def, toRExp_def, is64BitEval_def]
  \\ rveq \\ fs[toRExp_def, is64BitEval_def]
  \\ every_case_tac \\ fs[] \\ rveq
  \\ fs[toRExp_def, is64BitEval_def]
QED

Theorem toFloVerCmd_is64BitBstep:
  ∀ varMap freshId f theIds freshId2 theCmd.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ⇒
    is64BitBstep (toRCmd theCmd)
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def, toRCmd_def, is64BitBstep_def]
  \\ every_case_tac \\ fs[toRCmd_def, is64BitBstep_def] \\ rveq
  \\ fs[toRCmd_def, is64BitBstep_def]
  \\ irule toFloVerExp_is64BitEval \\ asm_exists_tac \\ fs[]
QED

Theorem CakeML_FloVer_infer_error:
  ∀ (st st2:'a semanticPrimitives$state) env Gamma P analysisResult
    decl ids cake_P f floverVars varMap freshId freshId2 theIds theCmd dVars E fVars.
  (* the CakeML code can be translated into FloVer input *)
  prepareKernel (getFunctions decl) = SOME (ids, cake_P, f) ∧
  prepareVars ids = (floverVars, varMap, freshId) ∧
  Gamma = prepareGamma floverVars ∧
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
  toFloVerPre [cake_P] varMap = SOME (P, dVars) ∧
  computeErrorbounds theCmd P Gamma = SOME analysisResult ∧
  evaluate st env [cake_P] = (st2, Rval [Boolv T]) ∧
  (∀ x. x IN freevars [f] ⇒ x IN freevars [cake_P]) ∧
  st.fp_state.canOpt = FPScope NoOpt ∧
  (* the free variables are paired up in the id list, and defined *)
  env_sim env.v E fVars ∧
  (∀ x. x IN freevars [cake_P] ⇔ x IN freevars [f]) (* TODO: Should this be checked? *) ∧
  (∀ x. x IN freevars [cake_P] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ==>
  ? ids iv err w r.
    (* the analysis result returned contains an error bound *)
    FloverMapTree_find (getRetExp (toRCmd theCmd)) analysisResult = SOME (iv,err) /\
    (* we can evaluate with a real-valued semantics *)
    evaluate st env [toRealExp f] = (st2, Rval [Real r]) /\
    (* the CakeML code returns a valid floating-point word *)
    evaluate st env [f] = (st2, Rval [FP_WordTree w]) /\
    (* the roundoff error is sound *)
    real$abs (fp64_to_real (compress_word w) - r)
      <= err
Proof
  rpt strip_tac \\ imp_res_tac prepareVars_is_unique
  \\ rveq
  \\ first_assum (mp_then Any assume_tac toFloVerPre_preserves_bounds)
  (* the free variables of the program are bound and sound with respect to P *)
  \\ qpat_x_assum ‘computeErrorbounds _ _ _ = _’ mp_tac
  \\ simp[computeErrorbounds_def]
  \\ ntac 4 (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ fs[] \\ rveq
  \\ imp_res_tac IEEE_connectionTheory.IEEE_connection_cmds
  (* Issue 1: We need to somehow disallow underflow here... *)
  \\ first_x_assum
     (qspecl_then
      [ ‘λ x. case E x of |SOME v => SOME (real_to_fp64 roundTiesToEven v) | NONE => NONE’,
        ‘E’]
      mp_tac)
  \\ impl_tac
  >- (cheat)
  (* TODO: Should this be free vars + domain of Precondition/function parameters? *)
  \\ disch_then (qspec_then ‘freeVars (toRCmd theCmd)’ mp_tac)
  \\ impl_tac \\ fs[]
  \\ impl_tac
  >- (
    simp[RealRangeArithTheory.fVars_P_sound_def]
    \\ rpt strip_tac
    \\ first_x_assum irule \\ fs[PULL_EXISTS]
    \\ qexists_tac ‘[cake_P]’ \\ fs[]
    \\ qexists_tac ‘env’ \\ rewrite_tac [CONJ_ASSOC]
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs[]
    \\ qexists_tac ‘st’ \\ qexists_tac ‘st2’ \\ fs[]
    (* Connection between freeVars theCmd and freeVars toRCmd *)
    \\ ‘v IN domain (freeVars theCmd)’ by (cheat)
    (* Conclusion: Follows because freevars of CakeML and FloVer program must agree!*)
    \\ cheat)
  \\ impl_tac
  (* Can only be done once we know which environment to pick for the subnormal evaluation*)
  >- (cheat) (* TODO: bstep_valid *)
  \\ impl_tac
  (* invariant of the translation to FloVer: noDowncastFun is true *)
  >- (
    irule toFloVerCmd_noDowncastFun
    \\ asm_exists_tac \\ fs[])
  \\ impl_tac
  (* invariant of prepareVars: is64BitEnv (prepareGamma floverVars) *)
  >- (irule is64BitEnv_prepareGamma)
  \\ impl_tac
  (* invariant of translation to FloVer: is64BitBstep (toRCmd theCmd) *)
  >- (
    irule toFloVerCmd_is64BitBstep
    \\ asm_exists_tac \\ fs[])
  \\ disch_then assume_tac \\ fs[]
  (* Simulation 1: We can get the same result as the FloVer reals from CakeML reals *)
  \\ ‘evaluate st env [toRealExp f] = (st2, Rval [Real vR'])’
     by (cheat)
  (* Simulation 2: We can get the same result as FloVer floats for CakeML *)
  \\ ‘evaluate st env [f] = (st2, Rval [FP_WordTree (Fp_const vF)])’
     by (cheat)
  \\ fsrw_tac [SATISFY_ss] [fpSemTheory.compress_word_def]
  \\ once_rewrite_tac [ABS_SUB]
  \\ simp[fp64_to_real_def]
QED

val _ = export_theory ();

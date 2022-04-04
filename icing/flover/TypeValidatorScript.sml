(**
  Simple Type Inference algorithm with correctness proof to infer machine type
  assignments for FloVer's input expressions
**)
open realTheory realLib sptreeTheory;
open ExpressionsTheory MachineTypeTheory FloverTactics ExpressionAbbrevsTheory
     ExpressionSemanticsTheory CommandsTheory FloverMapTheory ResultsTheory;
open ResultsLib;
open preambleFloVer;

val _ = new_theory "TypeValidator";

Definition validTypes_def:
  validTypes e Gamma =
    ∃ mG. FloverMapTree_find e Gamma = SOME mG ∧
    (case e of
    | Var x => T
    | Const m v => m = mG
    | Unop u e1 =>
        validTypes e1 Gamma ∧
        (? me. FloverMapTree_find e1 Gamma = SOME me ∧ isCompat me mG)
    | Binop b e1 e2 =>
        validTypes e1 Gamma ∧
        validTypes e2 Gamma ∧
        (?m1 m2. FloverMapTree_find e1 Gamma = SOME m1 ∧
                 FloverMapTree_find e2 Gamma = SOME m2 ∧
                 isJoin m1 m2 mG)
    | Fma e1 e2 e3 =>
        validTypes e1 Gamma ∧
        validTypes e2 Gamma ∧
        validTypes e3 Gamma ∧
        (?m1 m2 m3. FloverMapTree_find e1 Gamma = SOME m1 ∧
                    FloverMapTree_find e2 Gamma = SOME m2 ∧
                    FloverMapTree_find e3 Gamma = SOME m3 ∧
                    isJoin3 m1 m2 m3 mG)
    | Downcast m e1 =>
        validTypes e1 Gamma ∧
        m = mG ∧
        (? m1. FloverMapTree_find e1 Gamma = SOME m1 ∧
               isMorePrecise m1 mG)) ∧
    (! E Gamma2 v m.
      (! e m. FloverMapTree_find e Gamma = SOME m ==>
              FloverMapTree_find e Gamma2 = SOME m) ∧
      eval_expr E (toRExpMap Gamma2) e v m ==>
      m = mG)
End

Theorem validTypes_single:
  ∀ e Gamma.
    validTypes e Gamma ==>
    ∃ mG.
      FloverMapTree_find e Gamma = SOME mG /\
      (!E v m Gamma2.
        (! e m. FloverMapTree_find e Gamma = SOME m ==>
                FloverMapTree_find e Gamma2 = SOME m) /\
        eval_expr E (toRExpMap Gamma2) e v m ==>
        m = mG)
Proof
  Cases_on `e` \\ rpt strip_tac \\ fs[Once validTypes_def] \\ rpt strip_tac
  \\ first_x_assum irule \\ fs[]
  \\ rpt (asm_exists_tac \\ fs[])
QED

Theorem validTypes_exec:
  ! e Gamma m.
      validTypes e Gamma /\
      FloverMapTree_find e Gamma = SOME m ==>
      ! E v mG.
        eval_expr E (toRExpMap Gamma) e v mG ==>
        mG = m
Proof
  rpt strip_tac \\ IMP_RES_TAC validTypes_single
  \\ rename1 `FloverMapTree_find e Gamma = SOME mG2`
  \\ `m = mG2`  by (fs[])
  \\ rveq
  \\ first_x_assum irule
  \\ qexistsl_tac [`E`, `Gamma`, `v`] \\ fs[]
QED

Definition isMonotone_def:
  isMonotone NONE mNew = T /\
  isMonotone (SOME mOld) mNew = (mOld = mNew)
End

Definition addMono_def:
  addMono e m map =
    case FloverMapTree_find e map of
    | SOME mOld => Fail "Nonmonotonic map update"
    | NONE => Succes (FloverMapTree_insert e m map)
End

Overload insert[local] = “FloverMapTree_insert”

Definition getValidMap_def:
  getValidMap Gamma e akk =
  if (FloverMapTree_mem e akk)
  then Succes akk
  else
    let mOldO = FloverMapTree_find e Gamma in
    case e of
    | Var x =>
      (case mOldO of
      | SOME m => Succes (insert e m akk)
      | NONE => Fail "Undefined variable")
    | Const m n =>
      if (isMonotone mOldO m)
      then Succes (insert e m akk)
      else Fail "Wrong type annotation for Constant"
    | Unop u e1 =>
    do
      akk_new <- getValidMap Gamma e1 akk;
      case FloverMapTree_find e1 akk_new of
      | NONE => Fail "Cannot typecheck unary op"
      | SOME m_e1 =>
        if (isFixedPoint m_e1)
          then
            case mOldO of
            | NONE => Fail "Undefined fixed-point type"
            | SOME mFix =>
              if (isCompat m_e1 mFix)
              then addMono e mFix akk_new
              else Fail "Incompatible type assignment"
          else
            if (isMonotone mOldO m_e1)
            then addMono e m_e1 akk_new
            else Fail "Wront type annotation for unary constant"
    od
    | Binop b e1 e2 =>
    do
      akk1_map <- getValidMap Gamma e1 akk;
      akk2_map <- getValidMap Gamma e2 akk1_map;
      let m1 = FloverMapTree_find e1 akk2_map;
          m2 = FloverMapTree_find e2 akk2_map in
      case m1, m2 of
      | SOME t1, SOME t2 =>
        if (isFixedPoint t1 /\ isFixedPoint t2)
        then
          case mOldO of
          | NONE => Fail "Undefined fixed-point type"
          | SOME mj =>
            if (morePrecise t1 mj /\ morePrecise t2 mj)
            then addMono e mj akk2_map
            else Fail "Incorrect fixed-point type"
        else
          if (t1 = REAL ∨ t2 = REAL)
          then if (t1 = REAL ∧ t2 = REAL)
               then if (isMonotone mOldO REAL)
                    then addMono e REAL akk2_map
                    else Fail "Wrong type annotation for binary operator"
               else Fail "Both arguments must be REAL if one is REAL"
          else
          (case join_fl t1 t2 of
          | NONE => Fail "Could not compute join for arguments"
          | SOME m =>
            if (isMonotone mOldO m)
            then addMono e m akk2_map
            else Fail "Wrong type annotation for binary operator")
      | _, _ => Fail "Could not compute type for arguments"
    od
    | Fma e1 e2 e3 =>
    do
      akk1_map <- getValidMap Gamma e1 akk;
      akk2_map <- getValidMap Gamma e2 akk1_map;
      akk3_map <- getValidMap Gamma e3 akk2_map;
      let m1 = FloverMapTree_find e1 akk3_map;
          m2 = FloverMapTree_find e2 akk3_map;
          m3 = FloverMapTree_find e3 akk3_map in
      case m1, m2, m3 of
      | SOME t1, SOME t2, SOME t3=>
        if (isFixedPoint t1 /\ isFixedPoint t2 /\ isFixedPoint t3)
        then
          case mOldO of
          | NONE => Fail "Undefined fixed-point type"
          | SOME mj =>
            if (morePrecise t1 mj /\ morePrecise t2 mj /\ morePrecise t3 mj)
            then addMono e mj akk3_map
            else Fail "Incorrect fixed-point type"
        else if (t1 = REAL ∨ t2 = REAL ∨ t3 = REAL)
          then if (t1 = REAL ∧ t2 = REAL ∧ t3 = REAL)
               then if (isMonotone mOldO REAL)
                    then addMono e REAL akk3_map
                    else Fail "Wrong type annotation for binary operator"
               else Fail "Both arguments must be REAL if one is REAL"
          else
          (case join_fl3 t1 t2 t3 of
          | NONE => Fail "Could not compute join for arguments"
          | SOME m =>
            if (isMonotone mOldO m)
            then addMono e m akk3_map
            else Fail "Wrong type annotation for FMA")
      | _, _ => Fail "Could not compute type for arguments"
    od
    | Downcast m e1 =>
    do
      akk_new <- getValidMap Gamma e1 akk;
      case FloverMapTree_find e1 akk_new of
      | NONE => Fail "Could not find cast argument type"
      | SOME t1 =>
        if (isFixedPoint t1)
        then
          case mOldO of
          | NONE => Fail "Could not find fixed_point type for cast"
          | SOME mFix =>
            if (m = mFix /\ morePrecise t1 mFix)
            then addMono e mFix akk_new
            else Fail "Incorrect fixed-point type"
        else
          if (morePrecise t1 m /\ isMonotone mOldO m)
          then addMono e m akk_new
          else Fail "Cannot cast down to lower precision"
    od
End

val tMap_def = FloverMapTree_correct;

Theorem toRExpMap_char:
  !e m akk. toRExpMap (FloverMapTree_insert e m akk) e = SOME m
Proof
  fs[toRExpMap_def, tMap_def]
QED

val by_monotonicity =
  once_rewrite_tac [map_find_add]
  \\ COND_CASES_TAC \\ fs[]
  \\ rveq
  \\ fs[FloverMapTree_mem_def]
  \\ EVERY_CASE_TAC \\ fs[];

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

Theorem getValidMap_mono:
  ∀ e Gamma akk res.
    getValidMap Gamma e akk = Succes res ⇒
    ∀ e m. FloverMapTree_find e akk = SOME m ⇒
           FloverMapTree_find e res = SOME m
Proof
  Induct_on  `e`
  \\ once_rewrite_tac [getValidMap_def] \\ fs[]
  \\ rpt strip_tac
  >- (Cases_on `FloverMapTree_mem (Var n) akk`
      \\ fs[option_case_eq] \\ rveq \\ fs[]
      \\ by_monotonicity)
  >- (Cases_on `FloverMapTree_mem (Const m v) akk`
      \\ fs[option_case_eq] \\ rveq \\ fs[]
      \\ Cases_on `isMonotone (FloverMapTree_find (Const m v) Gamma) m`
      \\ fs[]
      \\ rveq \\ by_monotonicity)
  >- (Cases_on `FloverMapTree_mem (Unop u e) akk`
      \\ fs[] \\ rveq \\ fs[]
      \\ Cases_on `getValidMap Gamma e akk` \\ fs[option_case_eq]
      \\ Cases_on `isFixedPoint m_e1` \\ fs[option_case_eq]
      >- (Cases_on `isCompat m_e1 mFix` \\ fs[addMono_def, option_case_eq]
          \\ rveq \\ res_tac
          \\ by_monotonicity)
      \\ Cases_on `isMonotone (FloverMapTree_find (Unop u e) Gamma) m_e1`
      \\ fs[addMono_def, option_case_eq] \\ rveq
      \\ res_tac
      \\ by_monotonicity)
  >- (rename1 `Binop b e1 e2` \\ Cases_on `FloverMapTree_mem (Binop b e1 e2) akk`
      \\ fs[] \\ rveq \\ fs[]
      \\ Cases_on `getValidMap Gamma e1 akk` \\ fs[result_bind_def]
      \\ Cases_on `getValidMap Gamma e2 a` \\ fs[option_case_eq]
      \\ Cases_on `isFixedPoint t1` \\ Cases_on `isFixedPoint t2` \\ fs[option_case_eq]
      >- (Cases_on `morePrecise t1 mj` \\ Cases_on `morePrecise t2 mj`
          \\ fs[addMono_def, option_case_eq]
          \\ rveq \\ res_tac
          \\ by_monotonicity)
      \\ Cases_on ‘t1 = REAL ∨ t2 = REAL’ \\ fs[]
      \\ TRY (rename1 ‘t1 = REAL ∧ t2 = REAL’ \\ Cases_on ‘t1 = REAL ∧ t2 = REAL’ \\ fs[] \\ fs[])
      \\ TRY (fs[option_case_eq] \\ rename1 `join_fl t1 t2 = SOME mj`
          \\ Cases_on `isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) mj`
          \\ fs[addMono_def, option_case_eq] \\ rveq \\ res_tac
          \\ by_monotonicity)
      \\ rveq \\ fs[]
      \\ Cases_on `isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) REAL`
      \\ fs[addMono_def, option_case_eq] \\ rveq \\ res_tac
      \\ by_monotonicity)
  >- (rename1 `Fma e1 e2 e3` \\ Cases_on `FloverMapTree_mem (Fma e1 e2 e3) akk`
      \\ fs[] \\ rveq \\ fs[]
      \\ Cases_on `getValidMap Gamma e1 akk` \\ fs[result_bind_def]
      \\ Cases_on `getValidMap Gamma e2 a` \\ fs[result_bind_def]
      \\ Cases_on `getValidMap Gamma e3 a'` \\ fs[option_case_eq]
      \\ Cases_on `isFixedPoint t1`
      \\ Cases_on `isFixedPoint t2`
      \\ Cases_on `isFixedPoint t3`
      \\ fs[option_case_eq]
      >- (Cases_on `morePrecise t1 mj`
          \\ Cases_on `morePrecise t2 mj`
          \\ Cases_on `morePrecise t3 mj`
          \\ fs[addMono_def, option_case_eq]
          \\ rveq \\ res_tac
          \\ by_monotonicity)
      \\ Cases_on ‘t1 = REAL ∨ t2 = REAL ∨ t3 = REAL’ \\ fs[]
      \\ TRY (rename1 ‘t1 = REAL ∧ t2 = REAL ∧ t3 = REAL’
              \\ Cases_on ‘t1 = REAL ∧ t2 = REAL ∧ t3 = REAL’ \\ fs[] \\ fs[])
      \\ TRY (fs[option_case_eq]
              \\ rename1 `join_fl3 t1 t2 t3 = SOME mj`
              \\ Cases_on `isMonotone (FloverMapTree_find (Fma e1 e2 e3) Gamma) mj`
              \\ fs[addMono_def, option_case_eq] \\ rveq \\ res_tac
              \\ by_monotonicity)
      \\ rveq \\ fs[]
      \\ Cases_on `isMonotone (FloverMapTree_find (Fma e1 e2 e3) Gamma) REAL`
      \\ fs[addMono_def, option_case_eq] \\ rveq \\ res_tac
      \\ by_monotonicity)
  \\ Cases_on `FloverMapTree_mem (Downcast m e) akk`
  \\ fs[] \\ rveq \\ fs[]
  \\ Cases_on `getValidMap Gamma e akk` \\ fs[option_case_eq]
  \\ Cases_on `isFixedPoint t1` \\ fs[option_case_eq]
  >- (Cases_on `m = mFix` \\ Cases_on `morePrecise t1 mFix`
      \\ fs[addMono_def, option_case_eq]
      \\ rveq \\ res_tac
      \\ by_monotonicity)
  \\ Cases_on `morePrecise t1 m`
  \\ Cases_on `isMonotone (FloverMapTree_find (Downcast m e) Gamma) m`
  \\ fs[addMono_def, option_case_eq] \\ rveq
  \\ res_tac
  \\ by_monotonicity
QED

Theorem validTypes_mono:
  ! e map1 map2.
      (! e m. FloverMapTree_find e map1 = SOME m ==>
              FloverMapTree_find e map2 = SOME m) /\
      validTypes e map1 ==>
      validTypes e map2
Proof
  Induct_on `e` \\ fs[Once validTypes_def]
  \\ rpt strip_tac
  \\ simp [Once validTypes_def]
  >- (qexists_tac `mG` \\ fs[]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ qexistsl_tac [`E`, `Gamma2`, `v`]
      \\ fs[])
  >- (rpt strip_tac \\ first_x_assum irule
      \\ qexistsl_tac [`E`, `Gamma2`, `v'`] \\ fs[])
  >- (qexists_tac `mG` \\ fs[]
      \\ rpt conj_tac
      >- (first_x_assum irule
          \\ qexists_tac `map1` \\ simp[GSYM validTypes_def])
      >- (qexists_tac `me` \\ fs[])
      \\ rpt strip_tac \\ first_x_assum irule
      \\ qexistsl_tac [`E`, `Gamma2`, `v`] \\ fs[])
  >- (qexists_tac `mG` \\ fs[]
      \\ rpt conj_tac
      >- (first_x_assum irule
          \\ qexists_tac `map1` \\ simp[GSYM validTypes_def])
      >- (first_x_assum irule
          \\ qexists_tac `map1` \\ simp[GSYM validTypes_def])
      >- (qexistsl_tac [`m1`, `m2`] \\ fs[])
      \\ rpt strip_tac \\ first_x_assum irule
      \\ qexistsl_tac [`E`, `Gamma2`, `v`] \\ fs[])
  >- (qexists_tac `mG` \\ fs[]
      \\ rpt conj_tac
      >- (first_x_assum irule
          \\ qexists_tac `map1` \\ simp[GSYM validTypes_def])
      >- (first_x_assum irule
          \\ qexists_tac `map1` \\ simp[GSYM validTypes_def])
      >- (first_x_assum irule
          \\ qexists_tac `map1` \\ simp[GSYM validTypes_def])
      >- (qexistsl_tac [`m1`, `m2`, `m3`] \\ fs[])
      \\ rpt strip_tac \\ first_x_assum irule
      \\ qexistsl_tac [`E`, `Gamma2`, `v`] \\ fs[])
  \\ rpt conj_tac
  >- (first_x_assum irule
      \\ qexists_tac `map1` \\ simp[GSYM validTypes_def])
  >- (qexists_tac `m1` \\ fs[])
  \\ rpt strip_tac \\ first_x_assum irule
  \\ qexistsl_tac [`E`, `Gamma2`, `v`] \\ fs[]
QED

Theorem map_find_mono:
  ! e1 e2 m1 m2 Gamma.
    FloverMapTree_mem e2 Gamma = F /\
    FloverMapTree_find e1 Gamma = SOME m1 ==>
    FloverMapTree_find e1 (FloverMapTree_insert e2 m2 Gamma) = SOME m1
Proof
  rpt strip_tac \\ fs[map_find_add]
  \\ Cases_on `e1 = e2` \\ fs[FloverMapTree_mem_def]
QED

Theorem getValidMap_correct:
  ∀ e Gamma akk res.
    (∀ e.
       FloverMapTree_mem e akk ⇒
       validTypes e akk) ∧
    getValidMap Gamma e akk = Succes res ⇒
    ∀ e.
      FloverMapTree_mem e res ⇒
      validTypes e res
Proof
  Induct_on `e` \\ simp[Once getValidMap_def] \\ rpt strip_tac
  >- (Cases_on `FloverMapTree_mem (Var n) akk`
      \\ fs[] \\ rveq \\ fs[option_case_eq]
      \\ rveq
      \\ fs[FloverMapTree_mem_def]
      \\ Cases_on `FloverMapTree_find e (insert (Var n) m akk)`
      \\ fs[map_find_add]
      \\ Cases_on `e = Var n` \\ fs[]
      >- (rveq \\ simp[Once validTypes_def]
          \\ qexists_tac `m` \\ fs[map_find_add]
          \\ rpt strip_tac
          \\ first_x_assum (qspecl_then [`Var n`, `m`] assume_tac)
          \\ fs[eval_expr_cases, toRExpMap_def])
      \\ `validTypes e akk`
        by (first_x_assum irule \\ fs[])
      \\ irule validTypes_mono \\ find_exists_tac \\ fs[]
      \\ rpt strip_tac \\ fs[map_find_add]
      \\ COND_CASES_TAC \\ fs[])
  >- (Cases_on `FloverMapTree_mem (Const m v) akk`
      \\ fs[] \\ rveq \\ fs[]
      \\ Cases_on `isMonotone (FloverMapTree_find (Const m v) Gamma) m`
      \\ fs[] \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
      \\ reverse (Cases_on `e = Const m v`) \\ fs[]
      >- (irule validTypes_mono
          \\ qexists_tac `akk` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      \\ simp[Once validTypes_def]
      \\ fs[map_find_add]
      \\ rpt strip_tac \\ rveq
      \\ first_x_assum (qspecl_then [`Const m v`, `m`] assume_tac)
      \\ fs[eval_expr_cases, toRExpMap_def])
  >- (qpat_x_assum `getValidMap _ _ _ = _`
        (fn thm => assume_tac (ONCE_REWRITE_RULE [getValidMap_def] thm))
      \\ Cases_on `FloverMapTree_mem (Unop u e) akk` \\ fs[]
      \\ Cases_on `getValidMap Gamma e akk` \\ fs[]
      \\ Cases_on `FloverMapTree_find e a` \\ fs[]
      \\ `! e. FloverMapTree_mem e a  ==> validTypes e a`
        by (rpt strip_tac \\ first_x_assum irule \\ fs[]
            \\ qexistsl_tac [`Gamma`, `akk`] \\ fs[])
      \\ Cases_on `isFixedPoint x` \\ fs[option_case_eq]
      >- (Cases_on `isCompat x mFix` \\ fs[addMono_def, option_case_eq]
          \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
          \\ reverse (Cases_on `e' = Unop u e`) \\ fs[]
          >- (irule validTypes_mono
              \\ qexists_tac `a` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              >- (COND_CASES_TAC \\ fs[])
              \\ first_x_assum irule \\ fs[])
          \\ rveq \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `mFix` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `a` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (fs[no_cycle_unop])
          \\ rpt strip_tac
          \\ first_x_assum (qspecl_then [`Unop u e`, `mFix`] assume_tac)
          \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
      \\ Cases_on `isMonotone (FloverMapTree_find (Unop u e) Gamma) x`
      \\ fs[addMono_def, option_case_eq]
      \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
      \\ reverse (Cases_on `e' = Unop u e`) \\ fs[]
      >- (irule validTypes_mono
          \\ qexists_tac `a` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          >- (COND_CASES_TAC \\ fs[])
          \\ first_x_assum irule \\ fs[])
      \\ rveq \\ once_rewrite_tac[validTypes_def]
      \\ qexists_tac `x` \\ fs[map_find_add]
      \\ rpt conj_tac
      >- (irule validTypes_mono
          \\ qexists_tac `a` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      >- (Cases_on `x` \\ fs[isCompat_def, morePrecise_def])
      \\ rpt strip_tac
      \\ first_x_assum (qspecl_then [`Unop u e`, `x`] assume_tac)
      \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
  >- (qpat_x_assum `getValidMap _ _ _ = _`
        (fn thm => assume_tac (ONCE_REWRITE_RULE [getValidMap_def] thm))
      \\ rename1 `Binop b e1 e2`
      \\ Cases_on `FloverMapTree_mem (Binop b e1 e2) akk` \\ fs[]
      \\ Cases_on `getValidMap Gamma e1 akk` \\ fs[]
      \\ Cases_on `getValidMap Gamma e2 a` \\ fs[]
      \\ rename1 `getValidMap Gamma e2 a = Succes map2`
      \\ Cases_on `FloverMapTree_find e1 map2` \\ fs[]
      \\ Cases_on `FloverMapTree_find e2 map2` \\ fs[]
      \\ ‘∀ e. FloverMapTree_mem e a ⇒ validTypes e a’
        by (rpt strip_tac \\ last_x_assum irule \\ fs[]
            \\ qexistsl_tac [`Gamma`, `akk`] \\ fs[])
      \\ ‘∀ e. FloverMapTree_mem e map2 ⇒ validTypes e map2’
        by (rpt strip_tac \\ first_x_assum irule \\ fs[]
            \\ qexistsl_tac [`Gamma`, `a`] \\ fs[])
      \\ Cases_on ‘isFixedPoint x ∧ isFixedPoint x'’
      >- (fs[option_case_eq] \\ Cases_on `morePrecise x mj` \\ Cases_on `morePrecise x' mj`
          \\ fs[addMono_def, option_case_eq]
          \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
          \\ reverse (Cases_on `e'' = Binop b e1 e2`) \\ fs[]
          >- (irule validTypes_mono
              \\ qexists_tac `map2` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              >- (COND_CASES_TAC \\ fs[]))
          \\ rveq \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `mj` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `map2` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map2` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (fs[no_cycle_binop_left, no_cycle_binop_right, isJoin_def]
              \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\ fs[isFixedPoint_def]
              \\ fs[join_fl_def]
              \\ Cases_on ‘mj’ \\ fs[morePrecise_def])
          \\ rpt strip_tac
          \\ first_x_assum (qspecl_then [`Binop b e1 e2`, `mj`] assume_tac)
          \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
      \\ pop_assum (fn thm => fs[thm, option_case_eq])
      \\ rename1 ‘m1 = REAL ∨ m2 = REAL’
      \\ Cases_on ‘m1 = REAL ∨ m2 = REAL’ \\ fs[] \\ fs[]
      \\ TRY (rename1 ‘(if m2 = REAL then _ else _) = _’ \\ Cases_on ‘m2 = REAL’ \\ fs[]
              \\ Cases_on `isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) REAL`)
      ORELSE (TRY (rename1 ‘(if m1 = REAL then _ else _) = _’ \\ Cases_on ‘m1 = REAL’ \\ fs[]
              \\ Cases_on `isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) REAL`))
      ORELSE (Cases_on `isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) m`)
      \\ fs[addMono_def, option_case_eq]
      \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
      \\ reverse (Cases_on `e'' = Binop b e1 e2`) \\ fs[]
      \\ TRY (irule validTypes_mono
          \\ qexists_tac `map2` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[] \\ FAIL_TAC "NOT FINISHED")
      >- (rveq \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `REAL` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `map2` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map2` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- fs[isJoin_def, isFixedPoint_def, join_fl_def]
          \\ rpt strip_tac \\ fs[eval_expr_cases, toRExpMap_def]
          \\ first_x_assum (qspecl_then [‘Binop b e1 e2’, ‘REAL’] assume_tac) \\ fs[])
      >- (Cases_on ‘FloverMapTree_find (Binop b e1 e2) akk’ \\ fs[]
          \\ Cases_on ‘m1 = REAL’ \\ fs[]
          \\ Cases_on ‘isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) REAL’
          \\ fs[option_case_eq] \\ rveq
          \\ irule validTypes_mono \\ qexists_tac ‘map2’ \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ TOP_CASE_TAC \\ fs[])
      >- (rveq
          \\ Cases_on ‘FloverMapTree_find (Binop b e1 e2) akk’ \\ fs[]
          \\ Cases_on ‘m1 = REAL’ \\ fs[]
          \\ Cases_on ‘isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) REAL’
          \\ fs[option_case_eq] \\ rveq
          \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `REAL` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `map2` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map2` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- fs[isJoin_def, isFixedPoint_def, join_fl_def]
          \\ rpt strip_tac \\ fs[eval_expr_cases, toRExpMap_def]
          \\ first_x_assum (qspecl_then [‘Binop b e1 e2’, ‘REAL’] assume_tac) \\ fs[])
      >- (Cases_on ‘isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) m’
          \\ fs[option_case_eq] \\ rveq
          \\ irule validTypes_mono \\ qexists_tac ‘map2’ \\ fs[map_find_add]
          \\ rpt strip_tac \\ TOP_CASE_TAC \\ fs[])
      \\ rveq \\ fs[]
      \\ Cases_on ‘isMonotone (FloverMapTree_find (Binop b e1 e2) Gamma) m’
      \\ fs[option_case_eq] \\ rveq
      \\ rveq \\ once_rewrite_tac[validTypes_def]
      \\ qexists_tac ‘m’ \\ fs[] \\ rpt conj_tac \\ fs[map_find_add]
      >- (irule validTypes_mono
          \\ qexists_tac `map2` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      >- (irule validTypes_mono
          \\ qexists_tac `map2` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      >- (fs[no_cycle_binop_left, no_cycle_binop_right, isJoin_def]
          \\ Cases_on ‘m1’ \\ Cases_on ‘m2’ \\ fs[join_fl_def, morePrecise_def]
          \\ rveq \\ EVAL_TAC)
      \\ rpt strip_tac
      \\ first_x_assum (qspecl_then [`Binop b e1 e2`, `m`] assume_tac)
      \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
  >- (qpat_x_assum `getValidMap _ _ _ = _`
        (fn thm => assume_tac (ONCE_REWRITE_RULE [getValidMap_def] thm))
      \\ rename1 `Fma e1 e2 e3` \\ fs[]
      \\ Cases_on `FloverMapTree_mem (Fma e1 e2 e3) akk` \\ fs[]
      \\ Cases_on `getValidMap Gamma e1 akk` \\ fs[]
      \\ Cases_on `getValidMap Gamma e2 a` \\ fs[]
      \\ rename1 `getValidMap Gamma e2 a = Succes map2`
      \\ Cases_on `getValidMap Gamma e3 map2` \\ fs[]
      \\ rename1 `getValidMap Gamma e3 map2 = Succes map3`
      \\ Cases_on `FloverMapTree_find e1 map3` \\ fs[]
      \\ Cases_on `FloverMapTree_find e2 map3` \\ fs[]
      \\ Cases_on `FloverMapTree_find e3 map3` \\ fs[]
      \\ `! e. FloverMapTree_mem e a  ==> validTypes e a`
        by (rpt strip_tac \\ last_x_assum irule \\ fs[]
            \\ qexistsl_tac [`Gamma`, `akk`] \\ fs[])
      \\ `! e. FloverMapTree_mem e map2 ==> validTypes e map2`
        by (rpt strip_tac
            \\ qpat_x_assum `!Gamma akk res. _ /\ getValidMap _ e3 _ = _ ==> _` kall_tac
            \\ first_x_assum irule \\ fs[]
            \\ qexistsl_tac [`Gamma`, `a`] \\ fs[])
      \\ `! e. FloverMapTree_mem e map3  ==> validTypes e map3`
        by (rpt strip_tac \\ first_x_assum irule \\ fs[]
            \\ qexistsl_tac [`Gamma`, `map2`] \\ fs[])
      \\ Cases_on `isFixedPoint x /\ isFixedPoint x' /\ isFixedPoint x''`
      >- (fs[option_case_eq]
          \\ Cases_on `morePrecise x mj` \\ Cases_on `morePrecise x' mj`
          \\ Cases_on `morePrecise x'' mj`
          \\ fs[addMono_def, option_case_eq]
          \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
          \\ rename1 `if eNew = Fma e1 e2 e3 then SOME mj else _`
          \\ reverse (Cases_on `eNew = Fma e1 e2 e3`) \\ fs[]
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          \\ rveq \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `mj` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (fs[no_cycle_fma_left, no_cycle_fma_center, no_cycle_fma_right,
                 isJoin3_def]
              \\ Cases_on ‘x’ \\ Cases_on ‘x'’ \\ Cases_on ‘x''’ \\ fs[isFixedPoint_def]
              \\ Cases_on ‘mj’ \\ fs[morePrecise_def])
          \\ rpt strip_tac
          \\ first_x_assum (qspecl_then [`Fma e1 e2 e3`, `mj`] assume_tac)
          \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
      \\ pop_assum (fn thm => fs[thm, option_case_eq])
      \\ rename1 ‘m1 = REAL ∨ m2 = REAL ∨ m3 = REAL’
      \\ Cases_on ‘m1 = REAL ∨ m2 = REAL ∨ m3 = REAL’ \\ fs[] \\ fs[]
      \\ ((rename1 ‘(if m2 = REAL ∧ m3 = REAL then _ else _) = _’
              \\ Cases_on ‘m2 = REAL ∧ m3 = REAL’ \\ fs[]
              \\ Cases_on `isMonotone (FloverMapTree_find (Fma e1 e2 e3) Gamma) REAL`)
       ORELSE (rename1 ‘(if m1 = REAL ∧ m3 = REAL then _ else _) = _’
                    \\ Cases_on ‘m1 = REAL ∧ m3 = REAL’ \\ fs[]
                    \\ Cases_on `isMonotone (FloverMapTree_find (Fma e1 e2 e3) Gamma) REAL`)
       ORELSE (rename1 ‘(if m1 = REAL ∧ m2 = REAL then _ else _) = _’
                    \\ Cases_on ‘m1 = REAL ∧ m2 = REAL’ \\ fs[]
                    \\ Cases_on `isMonotone (FloverMapTree_find (Fma e1 e2 e3) Gamma) REAL`)
       ORELSE (fs[option_case_eq] \\ Cases_on `isMonotone (FloverMapTree_find (Fma e1 e2 e3) Gamma) m`))
      \\ fs[addMono_def, option_case_eq]
      \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
      \\ rename1 `eNew = Fma e1 e2 e3`
      \\ reverse (Cases_on `eNew = Fma e1 e2 e3`) \\ fs[]
      >- (irule validTypes_mono
          \\ qexists_tac `map3` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      >- (rveq \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `REAL` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- EVAL_TAC
          \\ rpt strip_tac
          \\ first_x_assum (qspecl_then [`Fma e1 e2 e3`, `REAL`] assume_tac)
          \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
      >- (irule validTypes_mono
          \\ qexists_tac `map3` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      >- (rveq \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `REAL` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- EVAL_TAC
          \\ rpt strip_tac
          \\ first_x_assum (qspecl_then [`Fma e1 e2 e3`, `REAL`] assume_tac)
          \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
      >- (irule validTypes_mono
          \\ qexists_tac `map3` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      >- (rveq \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `REAL` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- EVAL_TAC
          \\ rpt strip_tac
          \\ first_x_assum (qspecl_then [`Fma e1 e2 e3`, `REAL`] assume_tac)
          \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
         >- (irule validTypes_mono
             \\ qexists_tac `map3` \\ fs[]
             \\ rpt strip_tac \\ fs[map_find_add]
             \\ COND_CASES_TAC \\ fs[])
      >- (rveq \\ once_rewrite_tac[validTypes_def]
          \\ qexists_tac `m` \\ fs[map_find_add]
          \\ rpt conj_tac
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (irule validTypes_mono
              \\ qexists_tac `map3` \\ fs[]
              \\ rpt strip_tac \\ fs[map_find_add]
              \\ COND_CASES_TAC \\ fs[])
          >- (fs[no_cycle_fma_left, no_cycle_fma_center, no_cycle_fma_right,
                 isJoin3_def]
              \\ Cases_on ‘m1’ \\ Cases_on ‘m2’ \\ Cases_on ‘m3’
              \\ fs[join_fl3_def, join_fl_def, morePrecise_def, isFixedPoint_def]
              \\ rveq \\ fs[])
          \\ rpt strip_tac
          \\ first_x_assum (qspecl_then [`Fma e1 e2 e3`, `m`] assume_tac)
          \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[]))
  \\ qpat_x_assum `getValidMap _ _ _ = _`
    (fn thm => assume_tac (ONCE_REWRITE_RULE [getValidMap_def] thm))
  \\ Cases_on `FloverMapTree_mem (Downcast m e) akk` \\ fs[]
  \\ Cases_on `getValidMap Gamma e akk` \\ fs[]
  \\ Cases_on `FloverMapTree_find e a` \\ fs[]
  \\ `! e. FloverMapTree_mem e a  ==> validTypes e a`
    by (rpt strip_tac \\ first_x_assum irule \\ fs[]
        \\ qexistsl_tac [`Gamma`, `akk`] \\ fs[])
  \\ Cases_on `isFixedPoint x` \\ fs[option_case_eq]
  >- (Cases_on `m = mFix` \\ Cases_on `morePrecise x mFix`
      \\ fs[addMono_def, option_case_eq]
      \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
      \\ reverse (Cases_on `e' = Downcast m e`) \\ fs[]
      >- (irule validTypes_mono
          \\ qexists_tac `a` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      \\ rveq \\ once_rewrite_tac[validTypes_def]
      \\ qexists_tac `m` \\ fs[map_find_add]
      \\ rpt conj_tac
      >- (irule validTypes_mono
          \\ qexists_tac `a` \\ fs[]
          \\ rpt strip_tac \\ fs[map_find_add]
          \\ COND_CASES_TAC \\ fs[])
      >- (fs[no_cycle_cast, isMorePrecise_morePrecise])
      \\ rpt strip_tac
      \\ first_x_assum (qspecl_then [`Downcast m e`, `mFix`] assume_tac)
      \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[])
  \\ Cases_on `morePrecise x m`
  \\ Cases_on `isMonotone (FloverMapTree_find (Downcast m e) Gamma) m`
  \\ fs[addMono_def, option_case_eq]
  \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
  \\ reverse (Cases_on `e' = Downcast m e`) \\ fs[]
  >- (irule validTypes_mono
      \\ qexists_tac `a` \\ fs[]
      \\ rpt strip_tac \\ fs[map_find_add]
      \\ COND_CASES_TAC \\ fs[])
  \\ rveq \\ once_rewrite_tac[validTypes_def]
  \\ qexists_tac `m` \\ fs[map_find_add]
  \\ rpt conj_tac
  >- (irule validTypes_mono
      \\ qexists_tac `a` \\ fs[]
      \\ rpt strip_tac \\ fs[map_find_add]
      \\ COND_CASES_TAC \\ fs[])
  >- (fs[no_cycle_cast, isMorePrecise_morePrecise])
  \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [`Downcast m e`, `m`] assume_tac)
  \\ fs[eval_expr_cases, toRExpMap_def] \\ rveq \\ fs[]
QED

Theorem getValidMap_top_contained:
  ! e akk Gamma res.
      getValidMap Gamma e akk = Succes res ==>
      FloverMapTree_mem e res
Proof
  Induct_on `e` \\ simp[Once getValidMap_def] \\ rpt strip_tac
  >- (EVERY_CASE_TAC \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add])
  >- (EVERY_CASE_TAC \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add])
  >- (Cases_on `getValidMap Gamma e akk` \\ fs[]
      \\ res_tac
      \\ fs[addMono_def]
      \\ EVERY_CASE_TAC \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add])
  >- (Cases_on `FloverMapTree_mem (Binop b e e') akk` \\ fs[] \\ rveq \\ fs[]
      \\ Cases_on `getValidMap Gamma e akk` \\ fs[]
      \\ Cases_on `getValidMap Gamma e' a` \\ fs[]
      \\ res_tac \\ fs[addMono_def]
      \\ EVERY_CASE_TAC \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add])
  >- (rename1 `Fma e1 e2 e3`
      \\ Cases_on `FloverMapTree_mem (Fma e1 e2 e3) akk` \\ fs[] \\ rveq \\ fs[]
      \\ Cases_on `getValidMap Gamma e1 akk` \\ fs[]
      \\ Cases_on `getValidMap Gamma e2 a` \\ fs[]
      \\ Cases_on `getValidMap Gamma e3 a'` \\ fs[]
      \\ res_tac \\ fs[addMono_def]
      \\ EVERY_CASE_TAC \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add])
  \\ Cases_on `getValidMap Gamma e akk` \\ fs[]
  \\ res_tac
  \\ fs[addMono_def]
  \\ EVERY_CASE_TAC \\ rveq \\ fs[FloverMapTree_mem_def, map_find_add]
QED

Theorem getValidMap_top_correct:
  ! e akk Gamma res.
      (! e. FloverMapTree_mem e akk ==> validTypes e akk) /\
      getValidMap Gamma e akk = Succes res ==>
      validTypes e res
Proof
  metis_tac[getValidMap_correct, getValidMap_top_contained]
QED

Definition validTypesCmd_def:
  validTypesCmd f Gamma =
    ((case f of
    | Let m x e g =>
      ? mG.
      FloverMapTree_find e Gamma = SOME mG /\
      FloverMapTree_find (Var x) Gamma = SOME m /\
      m = mG /\
      validTypes e Gamma /\
      validTypesCmd g Gamma
    | Ret e => validTypes e Gamma) /\
    ? mT.
      FloverMapTree_find (getRetExp f) Gamma = SOME mT /\
      (! E Gamma2 v m.
        (! e m. FloverMapTree_find e Gamma = SOME m ==>
                FloverMapTree_find e Gamma2 = SOME m) /\
        bstep f E (toRExpMap Gamma2) v m ==>
        m = mT))
End

Theorem validTypesCmd_single:
  ! f Gamma.
      validTypesCmd f Gamma ==>
      ? mT.
        FloverMapTree_find (getRetExp f) Gamma = SOME mT /\
        ! E Gamma2 v m.
          (! e m. FloverMapTree_find e Gamma = SOME m ==>
                  FloverMapTree_find e Gamma2 = SOME m) /\
          bstep f E (toRExpMap Gamma2) v m ==>
          m = mT
Proof
  Cases_on `f` \\ simp[Once validTypesCmd_def] \\ rpt strip_tac \\ metis_tac[]
QED

Definition getValidMapCmd_def:
  getValidMapCmd Gamma (Let m x e g) akk =
    do
      res_e <- getValidMap Gamma e akk;
      case FloverMapTree_find e res_e of
      | NONE => Fail "No type computed for argument"
      | SOME m_e =>
        if (m = m_e)
        then
          do
            newMap <- addMono (Var x) m res_e;
            getValidMapCmd Gamma g newMap;
          od
        else Fail "Incorrect type for let-bound variable"
    od /\
  getValidMapCmd Gamma (Ret e) akk = getValidMap Gamma e akk
End

Theorem getValidMapCmd_mono:
  ! f Gamma akk res.
      getValidMapCmd Gamma f akk = Succes res ==>
      ! e m. FloverMapTree_find e akk = SOME m ==>
             FloverMapTree_find e res = SOME m
Proof
  Induct_on `f` \\ simp[Once getValidMapCmd_def]
  THENL [ ALL_TAC , MATCH_ACCEPT_TAC getValidMap_mono]
  \\ rpt strip_tac
  \\ Cases_on `getValidMap Gamma e akk` \\ fs[option_case_eq]
  \\ Cases_on `m = m_e` \\ fs[] \\ rveq
  \\ Cases_on `addMono (Var n) m a` \\ fs[addMono_def, option_case_eq]
  \\ rveq
  \\ res_tac
  \\ first_x_assum irule
  \\ fs[map_find_add]
  \\ COND_CASES_TAC \\ fs[]
  >- (rveq
      \\ `FloverMapTree_find (Var n) a = SOME m'`
        by (irule getValidMap_mono \\ qexistsl_tac [`Gamma`, `akk`, `e`]
            \\ fs[])
      \\ fs[])
  \\ irule getValidMap_mono \\ ntac 2 (find_exists_tac \\ fs[])
QED

Theorem getValidMapCmd_correct:
  ! f Gamma akk res.
      (! e. FloverMapTree_mem e akk ==>
            validTypes e akk) /\
      getValidMapCmd Gamma f akk = Succes res ==>
      validTypesCmd f res /\
      (! e. FloverMapTree_mem e res ==>
            validTypes e res)
Proof
  Induct_on `f` \\ simp[getValidMapCmd_def]
  \\ rpt gen_tac \\ rpt (disch_then assume_tac) \\ fs[]
  >- (Cases_on `getValidMap Gamma e akk` \\ fs[option_case_eq]
      \\ Cases_on `m = m_e` \\ fs[] \\ rveq
      \\ Cases_on `addMono (Var n) m a` \\ fs[addMono_def, option_case_eq]
      \\ rveq
      \\ `validTypesCmd f res /\
          ! e. FloverMapTree_mem e res ==> validTypes e res`
        by (first_x_assum irule \\ qexistsl_tac [`Gamma`, `insert (Var n) m a`]
            \\ fs[] \\ rpt strip_tac \\ fs[FloverMapTree_mem_def, map_find_add]
            \\ Cases_on `e' = Var n`
            >- (rveq \\ simp[validTypes_def]
                \\ qexists_tac `m` \\ fs[map_find_add]
                \\ rpt strip_tac
                \\ first_x_assum (qspecl_then [`Var n`, `m`] assume_tac)
                \\ fs[eval_expr_cases, toRExpMap_def])
            \\ fs[] \\ irule validTypes_mono
            \\ qexists_tac `a` \\ conj_tac
            >- (rpt strip_tac \\ irule map_find_mono
                \\ fs[FloverMapTree_mem_def])
            \\ irule getValidMap_correct
            \\ conj_tac \\ fs[FloverMapTree_mem_def]
            \\ qexistsl_tac [`Gamma`, `akk`, `e`] \\ fs[])
      \\ simp[Once validTypesCmd_def, getRetExp_def]
      \\ IMP_RES_TAC validTypesCmd_single
      \\ rpt conj_tac
      >- (irule getValidMapCmd_mono
          \\ qexistsl_tac [`Gamma`, `insert (Var n) m a`, `f`] \\ fs[]
          \\ fs[map_find_add] \\ Cases_on `e = Var n` \\ fs[])
      >- (irule getValidMapCmd_mono
          \\ qexistsl_tac [`Gamma`, `insert (Var n) m a`, `f`] \\ fs[]
          \\ fs[map_find_add])
      >- (`? m. FloverMapTree_find e res = SOME m`
          by (qexists_tac `m` \\ irule getValidMapCmd_mono
              \\ qexistsl_tac [`Gamma`, `insert (Var n) m a`, `f`] \\ fs[]
              \\ fs[map_find_add] \\ COND_CASES_TAC \\ fs[])
          \\ first_x_assum irule \\ fs[FloverMapTree_mem_def])
      \\ qexists_tac `mT` \\ fs[]
      \\ rpt strip_tac \\ fs[bstep_cases]
      \\ first_x_assum irule
      \\ ntac 2 (find_exists_tac \\ fs[]))
  \\ simp[Once validTypesCmd_def]
  \\ IMP_RES_TAC getValidMap_correct
  \\ IMP_RES_TAC getValidMap_top_correct
  \\ rpt conj_tac \\ fs[]
  \\ IMP_RES_TAC validTypes_single
  \\ qexists_tac `mG` \\ fs[getRetExp_def]
  \\ rpt strip_tac \\ fs[bstep_cases]
  \\ first_x_assum irule \\ ntac 2 (find_exists_tac \\ fs[])
QED

Theorem validTypes_defined_usedVars:
  ∀ e Gamma.
  validTypes e Gamma ⇒
  ∀ x. x IN domain (usedVars e) ⇒
  ∃ m. FloverMapTree_find (Var x) Gamma = SOME m
Proof
  ho_match_mp_tac (fetch "-" "validTypes_ind")
  \\ rpt strip_tac
  \\ qpat_x_assum ‘validTypes _ _’ mp_tac \\ simp[Once validTypes_def]
  \\ every_case_tac
  \\ qpat_x_assum ‘_ IN domain (usedVars _)’ mp_tac
  \\ simp[Once usedVars_def]
  \\ rpt strip_tac \\ rveq \\ fs[domain_union]
QED

Theorem validTypesCmd_freevars:
  ∀ e Gamma.
  validTypesCmd e Gamma ⇒
  ∀ x. x IN domain (freeVars e) ⇒
  ∃ m. FloverMapTree_find (Var x) Gamma = SOME m
Proof
  ho_match_mp_tac (fetch "-" "validTypesCmd_ind")
  \\ rpt strip_tac
  \\ qpat_x_assum ‘validTypesCmd _ _’ mp_tac \\ simp[Once validTypesCmd_def]
  \\ every_case_tac
  \\ qpat_x_assum ‘_ IN domain (freeVars _)’ mp_tac
  \\ simp[Once freeVars_def, domain_union]
  \\ rpt strip_tac \\ rveq \\ fs[domain_union]
  \\ imp_res_tac validTypes_defined_usedVars \\ fs[]
QED

val _ = export_theory();

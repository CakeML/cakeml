open FloverTactics AbbrevsTheory RealSimpsTheory TypeValidatorTheory
     ExpressionSemanticsTheory ssaPrgsTheory IntervalArithTheory CommandsTheory;
open preambleFloVer;

val _ = new_theory "RealRangeArith";

val dVars_range_valid_def = Define `
  dVars_range_valid (dVars:num_set) (E:num -> real option) (A:analysisResult) =
    !(v:num). v IN domain dVars ==>
       ?vR iv err.
         E v = SOME vR /\
         (FloverMapTree_find ((Var v):real expr) A = SOME (iv, err)) /\
         (FST iv) <= vR /\ vR <= (SND iv)`;

val fVars_P_sound_def = Define `
  fVars_P_sound (fVars:num_set) (E:env) (P:precond) =
    !(v:num).
      v IN domain fVars ==>
      ?vR. E v = SOME vR /\
        FST (P v) <= vR /\ vR <= SND (P v)`;

val validRanges_def = Define `
  validRanges e A E Gamma =
  ((case e of
      | Var x => T
      | Const m v => T
      | Unop u e1 =>
        (u = Sqrt ==>
          (! iv1 err.
            FloverMapTree_find e1 A = SOME (iv1, err) ==>
            (0 < IVlo iv1))) /\
        validRanges e1 A E Gamma
      | Binop b e1 e2 =>
        (b = Div ==>
          (! iv2 err.
            FloverMapTree_find e2 A = SOME (iv2, err) ==>
             (IVhi iv2 < 0 \/ 0 < IVlo iv2))) /\
         validRanges e1 A E Gamma  /\ validRanges e2 A E Gamma
      | Fma e1 e2 e3 =>
        validRanges e1 A E Gamma /\ validRanges e2 A E Gamma /\
        validRanges e3 A E Gamma
      | Downcast m e1 =>
        validRanges e1 A E Gamma)
  /\
  (? iv err vR.
    FloverMapTree_find e A = SOME (iv, err) /\
    eval_expr E Gamma (toREval e) vR REAL /\
    (IVlo iv <= vR /\ vR <= IVhi iv)))`;

val validRanges_single = store_thm (
  "validRanges_single",
  ``! e A E Gamma.
      validRanges e A E Gamma ==>
      ? iv err vR.
        FloverMapTree_find e A = SOME (iv, err) /\
        eval_expr E Gamma (toREval e) vR REAL /\
        (IVlo iv <= vR /\ vR <= IVhi iv)``,
  rpt strip_tac \\ Cases_on `e` \\ fs[Once validRanges_def]
  \\ find_exists_tac \\ fs[]);

val validRanges_swap = store_thm (
  "validRanges_swap",
  ``! Gamma1 Gamma2 e A E.
      (! n. Gamma1 n = Gamma2 n) /\
      validRanges e A E Gamma1 ==>
      validRanges e A E Gamma2``,
  Induct_on `e` \\ simp[Once validRanges_def] \\ rpt strip_tac
  \\ simp[Once validRanges_def]
  \\ rpt conj_tac \\ metis_tac []);

val validRangesCmd_def = Define `
  validRangesCmd f A E Gamma =
  ((case f of
      | Let m x e g =>
        validRanges e A E Gamma /\
        (! vR. eval_expr E Gamma (toREval e) vR REAL ==>
               validRangesCmd g A (updEnv x vR E) Gamma)
      | Ret e => validRanges e A E Gamma) /\
  ? iv_e err_e vR.
    FloverMapTree_find (getRetExp f) A = SOME (iv_e, err_e) /\
    bstep (toREvalCmd f) E Gamma vR REAL /\
    (IVlo iv_e <= vR /\ vR <= IVhi iv_e))`;

val validRangesCmd_single = store_thm (
  "validRangesCmd_single",
  ``! f A E Gamma.
      validRangesCmd f A E Gamma ==>
      ? iv_e err_e vR.
        FloverMapTree_find (getRetExp f) A = SOME (iv_e, err_e) /\
        bstep (toREvalCmd f) E Gamma vR REAL /\
        (IVlo iv_e <= vR /\ vR <= IVhi iv_e)``,
  Cases_on `f` \\ simp[Once validRangesCmd_def] \\ metis_tac[]);

val validRangesCmd_swap = store_thm (
  "validRangesCmd_swap",
  ``! f A E Gamma1 Gamma2.
      (! n. Gamma1 n = Gamma2 n) /\
      validRangesCmd f A E Gamma1 ==>
      validRangesCmd f A E Gamma2``,
  Induct_on `f` \\ simp[Once validRangesCmd_def] \\ rpt strip_tac
  \\ simp[Once validRangesCmd_def] \\ rpt conj_tac \\ metis_tac[]);

val _ = export_theory();

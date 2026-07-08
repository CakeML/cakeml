(**
   This file contains the HOL4 implementation of the error bound validator as well
   as its soundness proof. The function validErrorbound is the Error bound
   validator from the certificate checking process. Under the assumption that a
   valid range arithmetic result has been computed, it can validate error bounds
   encoded in the analysis result. The validator is used in the file
   CertificateCheckerScript.sml to build the complete checker.
 **)
Theory ErrorIntervalInference
Ancestors
  real pred_set Abbrevs Expressions ExpressionSemantics RealSimps
  RealRangeArith MachineType ExpressionAbbrevs ErrorBounds
  IntervalArith TypeValidator IntervalValidation Environments
  RealIntervalInference Commands ssaPrgs FloverMap
Libs
  simpLib realLib RealArith FloverTactics preambleFloVer

Definition inferErrorbound_def:
  inferErrorbound e (typeMap: typeMap) (I:ivMap) (akk:analysisResult) :analysisResult option=
  (case (FloverMapTree_find e akk) of
  | SOME _ => SOME akk
  | NONE =>
    do
      iv_f <- FloverMapTree_find e I;
      m <- FloverMapTree_find e typeMap;
      (case e of
      | Var v =>
        SOME (FloverMapTree_insert e (iv_f, computeError (maxAbs iv_f) m) akk)
      | Const _ n =>
        SOME (FloverMapTree_insert e (iv_f, computeError (maxAbs iv_f) m) akk)
      | Unop Neg e1 =>
        do
        recRes <- inferErrorbound e1 typeMap I akk;
        (iv, err1) <- FloverMapTree_find e1 recRes;
        SOME (FloverMapTree_insert e (iv_f, err1) recRes);
        od
      | Unop Inv e1 => NONE
      | Unop Sqrt e1 =>
        do
        recRes <- inferErrorbound e1 typeMap I akk;
        (iv1, err1) <- FloverMapTree_find e1 recRes;
        let errIve1 = widenInterval iv1 err1;
            sqrtRealLo = newton ITERCOUNT (IVlo iv1 * 0.99) (IVlo iv1 * 0.99);
            sqrtRealHi = newton ITERCOUNT (IVhi iv1 * 1.01) (IVhi iv1 * 1.01);
            sqrtRealIv = (sqrtRealLo, sqrtRealHi);
            sqrtFinLo= newton ITERCOUNT (IVlo errIve1 * 0.99) (IVlo errIve1 * 0.99);
            sqrtFinHi = newton ITERCOUNT (IVhi errIve1 * 1.01) (IVhi errIve1 * 1.01);
            sqrtFinIv = (sqrtFinLo, sqrtFinHi);
            propError = err1 * sqrtFinHi * inv ((IVlo iv1 - err1) * 2);
            mAbs = maxAbs sqrtFinIv
        in
          SOME (FloverMapTree_insert e (iv_f, propError + computeError mAbs m) recRes);
        od
      | Binop op e1 e2 =>
        do
        recRes1 <- inferErrorbound e1 typeMap I akk;
        recRes2 <- inferErrorbound e2 typeMap I recRes1;
        (ive1, err1) <- FloverMapTree_find e1 recRes2;
        (ive2, err2) <- FloverMapTree_find e2 recRes2;
          let errIve1 = widenInterval ive1 err1 in
          let errIve2 = widenInterval ive2 err2 in
          let upperBoundE1 = maxAbs ive1 in
          let upperBoundE2 = maxAbs ive2 in
          if ((op = Div /\ noDivzero (IVhi errIve2) (IVlo errIve2) \/ op <> Div))
          then
            let eNew =
              (case op of
               | Plus =>
                 let mAbs = maxAbs (addInterval errIve1 errIve2) in
                   err1 + err2 + computeError mAbs m
               | Sub =>
                 let mAbs = maxAbs (subtractInterval errIve1 errIve2) in
                   err1 + err2 + computeError mAbs m
               | Mult =>
                 let mAbs = maxAbs (multInterval errIve1 errIve2);
                     eProp = upperBoundE1 * err2 + upperBoundE2 * err1 + err1 * err2 in
                   eProp + computeError mAbs m
               | Div =>
                 let upperBoundInvE2 = maxAbs (invertInterval ive2);
                  minAbsIve2 = minAbsFun (errIve2);
                  errInv = (1 / (minAbsIve2 * minAbsIve2)) * err2;
                  mAbs = maxAbs (divideInterval errIve1 errIve2);
                  eProp = upperBoundE1 * errInv + upperBoundInvE2 * err1 + err1 * errInv in
                  eProp + computeError mAbs m)
            in
            SOME (FloverMapTree_insert e (iv_f, eNew) recRes2)
          else NONE;
        od
      | Fma e1 e2 e3 =>
        do
        recRes1 <- inferErrorbound e1 typeMap I akk;
        recRes2 <- inferErrorbound e2 typeMap I recRes1;
        recRes3 <- inferErrorbound e3 typeMap I recRes2;
        (ive1, err1) <- FloverMapTree_find e1 recRes3;
        (ive2, err2) <- FloverMapTree_find e2 recRes3;
        (ive3, err3) <- FloverMapTree_find e3 recRes3;
          let errIve1 = widenInterval ive1 err1;
              errIve2 = widenInterval ive2 err2;
              errIve3 = widenInterval ive3 err3;
              upperBoundE1 = maxAbs ive1;
              upperBoundE2 = maxAbs ive2;
              upperBoundE3 = maxAbs ive3;
              errIntv_prod = multInterval errIve1 errIve2;
              mult_error_bound = (upperBoundE1 * err2 + upperBoundE2 * err1 + err1 * err2);
              mAbs = maxAbs (addInterval errIntv_prod errIve3);
              eNew = mult_error_bound + err3 + computeError mAbs m
          in
          SOME (FloverMapTree_insert e (iv_f, eNew) recRes3);
        od
      | Downcast m1 e1 =>
        do
        recRes <- inferErrorbound e1 typeMap I akk;
        (ive1, err1) <- FloverMapTree_find e1 recRes;
          let errIve1 = widenInterval ive1 err1;
              mAbs = maxAbs errIve1;
              eNew = err1 + computeError mAbs m1;
          in
          SOME (FloverMapTree_insert e (iv_f, eNew) recRes)
        od)
      od)
End

Definition inferErrorboundCmd_def:
  inferErrorboundCmd (f:real cmd) (typeMap: (real expr # mType) binTree)
                    (I:ivMap) (akk:analysisResult) =
    case f of
      | Let m x e g  =>
        do
          recRes <- inferErrorbound e typeMap I akk;
          (ive, erre) <- FloverMapTree_find e recRes;
          inferErrorboundCmd g typeMap I (FloverMapTree_insert (Var x) (ive, erre) recRes);
        od
      | Ret e =>
      inferErrorbound e typeMap I akk
End


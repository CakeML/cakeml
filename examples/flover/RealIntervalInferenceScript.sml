(**
  Implement  a trusted, unverified inferencer for real range intervals.
  The inferred, returned maps should be run through the certificate checker
**)
Theory RealIntervalInference
Ancestors
  real Abbrevs Expressions RealSimps ExpressionAbbrevs
  IntervalArith Commands ssaPrgs MachineType FloverMap
  TypeValidator RealRangeArith ExpressionSemantics sqrtApprox
Libs
  simpLib realLib RealArith FloverTactics preambleFloVer

val _ = monadsyntax.enable_monadsyntax();
val _ = List.app monadsyntax.enable_monad ["option"];

Type ivMap = “:(real#real) fMap”;

Definition ITERCOUNT_def:
  ITERCOUNT = 4:num
End

(** Unverified, trusted inferencer for interval bounds on expressions **)
Definition inferIntervalbounds_def:
  inferIntervalbounds e (P:precond) (akk:ivMap) :ivMap option =
  (case (FloverMapTree_find e akk) of
    | SOME intv => SOME akk
    | NONE =>
      (case e of
       | Var v =>
         SOME (FloverMapTree_insert e (P v) akk)
       | Const m n =>
        SOME (FloverMapTree_insert e (n,n) akk)
        | Unop op e1 =>
          do
            recRes <- inferIntervalbounds e1 P akk;
            iv_e1 <- FloverMapTree_find e1 recRes;
              case op of
                | Neg =>
                  SOME (FloverMapTree_insert e (negateInterval iv_e1) recRes)
                | Sqrt =>
                    let sqrtLo = newton ITERCOUNT (IVlo iv_e1 * 0.99) (IVlo iv_e1 * 0.99);
                        sqrtHi = newton ITERCOUNT (IVhi iv_e1 * 1.01) (IVhi iv_e1 * 1.01);
                        new_iv = (sqrtLo, sqrtHi);
                    in
                      SOME (FloverMapTree_insert e new_iv recRes)
                | _ => NONE
          od
        | Downcast m e1 =>
          do
            recRes <- inferIntervalbounds e1 P akk;
            iv_e1 <- FloverMapTree_find e1 recRes;
            SOME (FloverMapTree_insert e iv_e1 recRes);
          od
        | Binop op e1 e2 =>
          do
            recRes1 <- inferIntervalbounds e1 P akk;
            recRes2 <- inferIntervalbounds e2 P recRes1;
            iv_e1 <- FloverMapTree_find e1 recRes2;
            iv_e2 <- FloverMapTree_find e2 recRes2;
            if (op = Div /\ (IVlo iv_e2 <= 0 /\ 0 <= IVhi iv_e2))
            then NONE
            else
              SOME
                (let new_iv =
                  (case op of
                    | Plus => addInterval iv_e1 iv_e2
                    | Sub => subtractInterval iv_e1 iv_e2
                    | Mult => multInterval iv_e1 iv_e2
                    | Div => divideInterval iv_e1 iv_e2)
                  in FloverMapTree_insert e new_iv recRes2);
            od
        | Fma e1 e2 e3 =>
          do
            recRes1 <- inferIntervalbounds e1 P akk;
            recRes2 <- inferIntervalbounds e2 P recRes1;
            recRes3 <- inferIntervalbounds e3 P recRes2;
            iv_e1 <- FloverMapTree_find e1 recRes3;
            iv_e2 <- FloverMapTree_find e2 recRes3;
            iv_e3 <- FloverMapTree_find e3 recRes3;
            SOME (FloverMapTree_insert e (addInterval (multInterval iv_e1 iv_e2) iv_e3) recRes3);
            od))
End

Definition inferIntervalboundsCmd_def:
  inferIntervalboundsCmd (f:real cmd) (P:precond) (akk:ivMap) :ivMap option =
    case f of
     | Let m x e g =>
      do
        recRes <- inferIntervalbounds e P akk;
        iv_x <- FloverMapTree_find e recRes;
        inferIntervalboundsCmd g P (FloverMapTree_insert (Var x) iv_x recRes);
      od
      | Ret e => inferIntervalbounds e P akk
End


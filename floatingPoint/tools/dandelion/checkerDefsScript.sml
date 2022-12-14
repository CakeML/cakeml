(**
  Basic definitions used by Dandelion
**)
open realTheory realLib RealArith stringTheory;
open renameTheory realPolyTheory transcLangTheory;
open preambleDandelion;

val _ = new_theory"checkerDefs";

Datatype:
  certificate =
  <|
    transc : transc;                  (* transcendental function to be approximated *)
    poly : poly;                      (* real-number polynomial approximation *)
    eps : real;                       (* approximation error *)
    iv: ((string#(real#real)) list);  (* the interval on which the function is approximated *)
   |>
End

Datatype:
  result = Valid          (* the checker succeeded *)
         | Invalid string (* the checker failed with an error message *)
End

Definition isValid_def:
  isValid b err = if b then Valid else Invalid err
End

Definition interpResult_def:
  interpResult (Valid) = T ∧
  interpResult _ = F
End

Datatype:
  transcCertAnn =
    Cert certificate
    | PolyCert poly transcCertAnn
    | BopCert binop transcCertAnn transcCertAnn
    | UopCert unop transcCertAnn
    | CstCert real
    | VarCert string
End

Definition interpCertAnn_def:
  interpCertAnn (VarCert x) env =
    do v <- FIND (λ (y,r). y = x) env;
    return (SND v);
    od ∧
  interpCertAnn (CstCert c) env = SOME c ∧
  interpCertAnn (UopCert uop t) env =
    do
      r <- interpCertAnn t env;
      assert (uop = Inv ⇒ r ≠ 0);
      return (appUop uop r)
    od ∧
  interpCertAnn (BopCert bop t1 t2) env =
    do
      r1 <- interpCertAnn t1 env;
      r2 <- interpCertAnn t2 env;
      assert (bop = Div ⇒ r2 ≠ 0);
      return (appBop bop r1 r2);
    od ∧
  interpCertAnn (Cert c) env =
    do
      r <- interp c.transc env;
      return r;
    od ∧
  interpCertAnn (PolyCert p t) env =
    do
      r <- interpCertAnn t env;
      return (evalPoly p r)
    od
End

Datatype:
  transcCertProg =
    Let string transcCertAnn transcCertAnn
    | Ret transcCertAnn
End

val _ = export_theory();

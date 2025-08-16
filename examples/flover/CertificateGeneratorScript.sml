(**
  A simple, unverified generator for certificates.
  To be used in conjunction with the certificate checker to first analyze
  a kernel and then validate the analysis result
**)
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory ExpressionsTheory
     FloverMapTheory TypeValidatorTheory CommandsTheory AbbrevsTheory
     ExpressionAbbrevsTheory;
open preambleFloVer;

val _ = new_theory "CertificateGenerator";

Definition CertificateGeneratorExp_def:
  CertificateGeneratorExp (f:real expr) (P:precond) (Gamma:typeMap)
    :(real expr # precond # typeMap # analysisResult) option =
    let
      ivMap = inferIntervalbounds f P FloverMapTree_empty;
      fullTMap = getValidMap Gamma f FloverMapTree_empty;
    in
      case ivMap, fullTMap of
      | SOME ivMap, Succes tMap =>
        (case inferErrorbound f tMap ivMap FloverMapTree_empty of
        | SOME errMap => SOME (f,P,Gamma,errMap)
        | NONE => NONE)
                    | _, _ => NONE
End

Definition getExp_def:
  getExp (f, P, Gamma, errMap) = f
End

Definition getError_def:
  getError (f, P, Gamma, errMap) = FloverMapTree_find f errMap
End

Definition CertificateGeneratorCmd_def:
  CertificateGeneratorCmd (f:real cmd) (P:precond) (Gamma:typeMap)
    :(real cmd # precond # typeMap # analysisResult) option =
    let
      ivMap = inferIntervalboundsCmd f P FloverMapTree_empty;
      fullTMap = getValidMapCmd Gamma f FloverMapTree_empty;
    in
      case ivMap, fullTMap of
      | SOME ivMap, Succes tMap =>
        (case inferErrorboundCmd f tMap ivMap FloverMapTree_empty of
        | SOME errMap => SOME (f,P,Gamma,errMap)
        | NONE => NONE)
                    | _, _ => NONE
End

Definition getCmd_def:
  getCmd (f, P, Gamma, errMap) = f
End

val _ = export_theory ();

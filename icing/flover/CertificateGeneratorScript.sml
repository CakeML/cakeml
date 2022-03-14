open RealIntervalInferenceTheory ErrorIntervalInferenceTheory ExpressionsTheory
     FloverMapTheory TypeValidatorTheory CommandsTheory AbbrevsTheory
     ExpressionAbbrevsTheory;
open preambleFloVer;

val _ = new_theory "CertificateGenerator";

val CertificateGeneratorExp_def = Define `
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
      | _, _ => NONE`;

val getExp_def = Define `
  getExp (f, P, Gamma, errMap) = f`;

val getError_def = Define `
  getError (f, P, Gamma, errMap) = FloverMapTree_find f errMap`;

val CertificateGeneratorCmd_def = Define `
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
      | _, _ => NONE`;

val getCmd_def = Define `
  getCmd (f, P, Gamma, errMap) = f`;

val getError_def = Define `
  getError (f, P, Gamma, errMap) = FloverMapTree_find (getRetExp f) errMap`;

val _ = export_theory ();

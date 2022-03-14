open preamble FloverTactics AbbrevsTheory MachineTypeTheory CertificateCheckerTheory FloverMapTheory;
open simpLib realTheory realLib RealArith;

val _ = new_theory "certificate_Doppler";


val C12_def = Define `C12:(real expr) = Const (F 32 22) ((1657)/(5))`;
val C34_def = Define `C34:(real expr) = Const (F 32 31) ((3)/(5))`;
val T2_def = Define `T2:(real expr) = Var 2`;
val MultC34T2 = Define `MultC34T2:(real expr) = Binop Mult C34 T2`;;
val PlusC12MultC34T2 = Define `PlusC12MultC34T2:(real expr) = Binop Plus C12 MultC34T2`;;
val t15_def = Define `t15:(real expr) = Var 5`;
val UMint15 = Define `UMint15:(real expr) = Unop Neg t15`;
val v1_def = Define `v1:(real expr) = Var 1`;
val MultUMint15v1 = Define `MultUMint15v1:(real expr) = Binop Mult UMint15 v1`;;
val u0_def = Define `u0:(real expr) = Var 0`;
val Plust15u0 = Define `Plust15u0:(real expr) = Binop Plus t15 u0`;;
val MultPlust15u0Plust15u0 = Define `MultPlust15u0Plust15u0:(real expr) = Binop Mult Plust15u0 Plust15u0`;;
val DivMultUMint15v1MultPlust15u0Plust15u0 = Define `DivMultUMint15v1MultPlust15u0Plust15u0:(real expr) = Binop Div MultUMint15v1 MultPlust15u0Plust15u0`;;
val RetDivMultUMint15v1MultPlust15u0Plust15u0_def = Define `RetDivMultUMint15v1MultPlust15u0Plust15u0 = Ret DivMultUMint15v1MultPlust15u0Plust15u0`;
val Lett15PlusC12MultC34T2RetDivMultUMint15v1MultPlust15u0Plust15u0_def = Define `Lett15PlusC12MultC34T2RetDivMultUMint15v1MultPlust15u0Plust15u0 = Let (F 32 22) 5 PlusC12MultC34T2 RetDivMultUMint15v1MultPlust15u0Plust15u0`;


val defVars_doppler_def = Define `
 defVars_doppler (n:num) : mType option = 
if (n = 2) then SOME (F 32 25) else if (n = 5) then SOME (F 32 22) else if (n = 1) then SOME (F 32 16) else if (n = 0) then SOME (F 32 24) else NONE`;

val thePrecondition_doppler_def = Define ` 
 thePreconditiondoppler (n:num):interval = 
if n = 0 then ( (-100)/(1), (100)/(1)) else if n = 1 then ( (20)/(1), (20000)/(1)) else if n = 2 then ( (-30)/(1), (50)/(1)) else (0,1)`;

val absenv_doppler_def = RIGHT_CONV_RULE EVAL (Define `
  absenv_doppler:analysisResult = 
FloverMapTree_insert (Var 5) (( (1567)/(5), (1807)/(5)) , (191998459909)/(360287970189639680)) (FloverMapTree_insert DivMultUMint15v1MultPlust15u0Plust15u0 (( (-180700000)/(1138489), (-156700)/(5322249)), (687245686953077470048979305110968647520377206972059587321240717242952012043403992684315145245537877257)/(187873365883518886636153423154365518195667220347687807938599634639865414791217046800943848304672092482174976)) (FloverMapTree_insert MultPlust15u0Plust15u0 (( (1138489)/(25), (5322249)/(25)), (115379174302627901148046863368217)/(129807421463370690713262408230502400)) (FloverMapTree_insert Plust15u0 (( (1067)/(5), (2307)/(5)), (299372642309)/(360287970189639680)) (FloverMapTree_insert u0 (( (-100)/(1), (100)/(1)), (1)/(16777216)) (FloverMapTree_insert t15 (( (1567)/(5), (1807)/(5)), (191998459909)/(360287970189639680)) (FloverMapTree_insert Plust15u0 (( (1067)/(5), (2307)/(5)), (299372642309)/(360287970189639680)) (FloverMapTree_insert u0 (( (-100)/(1), (100)/(1)), (1)/(16777216)) (FloverMapTree_insert t15 (( (1567)/(5), (1807)/(5)), (191998459909)/(360287970189639680)) (FloverMapTree_insert MultUMint15v1 (( (-7228000)/(1), (-6268)/(1)), (474098014359006478341)/(23611832414348226068480)) (FloverMapTree_insert v1 (( (20)/(1), (20000)/(1)), (1)/(65536)) (FloverMapTree_insert UMint15 (( (-1807)/(5), (-1567)/(5)), (191998459909)/(360287970189639680)) (FloverMapTree_insert t15 (( (1567)/(5), (1807)/(5)), (191998459909)/(360287970189639680)) (FloverMapTree_insert PlusC12MultC34T2 (( (1567)/(5), (1807)/(5)), (191998459909)/(360287970189639680)) (FloverMapTree_insert MultC34T2 (( (-18)/(1), (30)/(1)), (20199768069)/(360287970189639680)) (FloverMapTree_insert T2 (( (-30)/(1), (50)/(1)), (1)/(33554432)) (FloverMapTree_insert C34 (( (3)/(5), (3)/(5)), (1)/(2147483648)) (FloverMapTree_insert C12 (( (1657)/(5), (1657)/(5)), (1)/(4194304)) (FloverMapTree_empty))))))))))))))))))`);

val fBitsdoppler_def = Define `
 fBitsdoppler:bitMap = FloverMapTree_insert DivMultUMint15v1MultPlust15u0Plust15u0 23 (FloverMapTree_insert MultPlust15u0Plust15u0 13 (FloverMapTree_insert Plust15u0 22 (FloverMapTree_insert Plust15u0 22 (FloverMapTree_insert MultUMint15v1 8 (FloverMapTree_insert PlusC12MultC34T2 22 (FloverMapTree_insert MultC34T2 26 (FloverMapTree_empty))))))) `;

val _ = store_thm ("ErrorBound_doppler_Sound",
``CertificateCheckerCmd Lett15PlusC12MultC34T2RetDivMultUMint15v1MultPlust15u0Plust15u0 absenv_doppler thePreconditiondoppler defVars_doppler fBitsdoppler``,
 flover_eval_tac \\ fs[REAL_INV_1OVER]);


 val _ = export_theory();
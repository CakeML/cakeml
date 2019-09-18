(*
  Compiles the divergent examples down to dataLang
*)

open preamble compilationLib dataLangLib

val _ = new_theory "divCompile"

val pureLoop =
  `fun pureLoop x = pureLoop x;`

val condLoop =
  `fun condLoop x = if x = 0 then 0 else condLoop (x - 1);`

val oddLoop =
  `fun oddLoop x = if x = 0 then () else oddLoop(x-2);`


val outerLoop =
  `fun pureLoop x = pureLoop x;
   fun outerLoop x = if x = 5000 then pureLoop () else outerLoop (x + 1);`


val (pureLoop_call_def,pureLoop_code_def) =
  to_data_x64 pureLoop "pureLoop"

val (condLoop_call_def,condLoop_code_def) =
  to_data_x64 condLoop "condLoop"

val (oddLoop_call_def,oddLoop_code_def) =
  to_data_x64 oddLoop "oddLoop"

val (outerLoop_call_def,outerLoop_code_def) =
  to_data_x64 outerLoop "outerLoop"

val _ = export_theory();

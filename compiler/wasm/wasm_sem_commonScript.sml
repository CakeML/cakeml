(*
  CWasm semantic components common to both the Big- & small- step semantics
  (wasmSem & wasm_smallstep resp.)
*)

Theory      wasm_sem_common
Ancestors   wasmLang ancillaryOps option arithmetic
Libs        wordsLib

Datatype: value
  = I32 word32
  | I64 word64
End

Overload b2w32 = “(λ b. if b then I32 1w else I32 0w) : bool -> value”
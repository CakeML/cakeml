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

Overload b2v = “(λ b. if b then I32 1w else I32 0w) : bool -> value”

Datatype: result
  = RInvalid
  (* RInvalid represents cases of going wrong
     that shouldn't happen in validated modules.
     ie, any "valid" CWasm module should never
     be evaluated to RInvalid *)
  | RBreak num
  | RReturn
  | RTrap
  | RNormal
  | RTimeout
End
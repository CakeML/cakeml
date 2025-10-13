WebAssembly backend for CakeML

[ancillaryOpsScript.sml](ancillaryOpsScript.sml):
Some supporting operations

[end-to-end](end-to-end):
Connect stackLang-to-WASM to rest of CakeML compiler

[futureDev](futureDev):
Future CWasm IR Dev

[leb128Script.sml](leb128Script.sml):
A foramlisation of LEB128

[shLib.sml](shLib.sml):
Shuhan's lib for misc utilities

[stack_to_wasmProofScript.sml](stack_to_wasmProofScript.sml):
Correctness proof for compilation from stackLang to CWasm

[stack_to_wasmScript.sml](stack_to_wasmScript.sml):
Compilation from stackLang to wasmLang

[wasmLangScript.sml](wasmLangScript.sml):
CWasm AST modelling Wasm 1.0 (+ tail calls)
Imprecisions:
  HOL lists encode Wasm vectors; latter has max length of 2^32

[wasmSemScript.sml](wasmSemScript.sml):
CWasm Functional Bigstep semantics

[wasm_notationsScript.sml](wasm_notationsScript.sml):
Notations for cake's Wasm 1.0 AST
Separated from wasmLangScript for ergonomics/build efficency

[wasm_sem_commonScript.sml](wasm_sem_commonScript.sml):
CWasm semantic components common to both the Big- & small- step semantics
(wasmSem & wasm_smallstep resp.)

[wasm_smallstepScript.sml](wasm_smallstepScript.sml):
Wasm smallstep semantics

[wbfScript.sml](wbfScript.sml):
En- & De- coding between CWasm 1.0 AST & Wasm's binary format

[wbf_prelimScript.sml](wbf_prelimScript.sml):
Preliminaries for En- & De- coding between CWasm 1.ε AST & Wasm binary format
such as:
- Types
- General (leb128) en-/de- coders
- Helpful Corollaries

[wbf_thmsScript.sml](wbf_thmsScript.sml):
CWasm 1.ε AST ⇔ Wasm binary format En- & De- coder theorems

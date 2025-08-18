WebAssembly backend for CakeML

[ancillaryOpsScript.sml](ancillaryOpsScript.sml):
Some supporting operations

[end-to-end](end-to-end):
Connect stackLang-to-WASM to rest of CakeML compiler

[leb128Script.sml](leb128Script.sml):
A foramlisation of LEB128

[stack_to_wasmProofScript.sml](stack_to_wasmProofScript.sml):
Correctness proof for compilation from stackLang to wasmLang

[stack_to_wasmScript.sml](stack_to_wasmScript.sml):
Compilation from stackLang to wasmLang

[wasm2LangScript.sml](wasm2LangScript.sml):
CWasm AST modelling Wasm 2.0 (+ tail calls)
Imprecisions:
  HOL lists encode Wasm vectors; latter has max length of 2^32

[wasm2_binary_formatScript.sml](wasm2_binary_formatScript.sml):
En- & De- coding between CWasm 2.0 AST & Wasm's binary format

[wasm2_notationsScript.sml](wasm2_notationsScript.sml):
Notations (HOL Overloads) for cake's Wasm 2.0 AST
Separated from wasm2LangScript for ergonomics/build efficency
We have over 400 instructions

[wasmLangScript.sml](wasmLangScript.sml):
CWasm AST modelling Wasm 1.0 (+ tail calls)
Imprecisions:
  HOL lists encode Wasm vectors; latter has max length of 2^32

[wasmSemScript.sml](wasmSemScript.sml):
WebAssembly (Wasm) semantics

[wasm_binary_formatScript.sml](wasm_binary_formatScript.sml):
En- & De- coding between CWasm 1.0 AST & Wasm's binary format
9 cheats

[wasm_notationsScript.sml](wasm_notationsScript.sml):
Notations for cake's Wasm 1.0 AST
Separated from wasmLangScript for ergonomics/build efficency

WebAssembly backend for CakeML
Defines the Cwasm IR that models Wasm (largely faithfully)

[leb128Script.sml](leb128Script.sml):
A foramlisation of LEB128

[miscOpsScript.sml](miscOpsScript.sml):
Some extra operations
No specs yet

[wasm2LangScript.sml](wasm2LangScript.sml):
CWasm AST modelling Wasm 2.0 (+ tail calls)
Present here are
  + control flow instructions
  + all numeric (stack) instructions
  + all vector (stack) instructions
  + all (incl num&vec) memory operations -- factored into their own datatype
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
Present here are
  + control flow instructions
  + int numeric instructions (ie, those not involving floats)
  + int memory operations    (not involving floats/vecs)
Imprecisions:
  HOL lists encode Wasm vectors; latter has max length of 2^32

[wasmSemScript.sml](wasmSemScript.sml):
WebAssembly (Wasm) semantics

[wasm_binary_formatScript.sml](wasm_binary_formatScript.sml):
En- & De- coding between CWasm 1.0 AST & Wasm's binary format

[wasm_notationsScript.sml](wasm_notationsScript.sml):
Notations for cake's Wasm 1.0 AST
Separated from wasmLangScript for ergonomics/build efficency

[wasm_parseScript.sml](wasm_parseScript.sml):
To deprecate/delete
WASM parser -- supports part of WASM text format

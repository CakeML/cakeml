# CHRC
**1Sep'25 Current status:**
- Finishing binary format
  + list dec-enc is a little more intricate that I expected (or possibly not, let me study it a while)
  +
- Starting small step
---
Resposible for the following files:
- wasmLang
- wasm_binary_format/_proofs
- wasm_smallstep
- wasmSem (partially)
---
### File status:
#### Binary Format encoder/decoder - wasm_binary_formatScript.sml
✓ Encode for Wasm 1.0 + ε (conversions) + tailcalls modules
- ❌ names section encoder
- ❌ some decoders
- ❌ some dec enc thms
- ❌ shortening thms


#### Semantics, Big step, functional - wasmSemScript.sml
✓ instruction semantics
+ ❌ whole program (modules) semantics
+ ❌ initialization
+ ? start and end states?


#### AST - wasmLangScript.sml
Wasm 1.0 + ε (conversions) + tailcalls
- Done
- ✓ Instructions
  + num/value types SANS FLOATS
  + numeric (intruction)s
  + parametrics
  + variables
  + memories
  + controls
- ✓ Modules
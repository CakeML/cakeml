### AST - wasmLangScript.sml
Wasm 1.0 + ε (conversions) + tailcalls
- ✓ Instructions
  + num/value types SANS FLOATS
  + numeric (intruction)s
  + parametrics
  + variables
  + memories
  + controls
- ✓ Modules

### Binary Format encoder/decoder - wasm_binary_formatScript.sml
✓ Wasm 1.0 + ε (conversions) + tailcalls encode
- ❌ names section encoder
- ❌ multiple decoders
- ❌ multiple dec_enc_thms


### Semantics, Big step, functional - wasmSemScript.sml
✓ instruction semantics
+ ❌ whole program (modules) semantics
+ ❌ initialization
+ ? start and end states?

### Compiler
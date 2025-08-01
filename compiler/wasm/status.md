AST - wasmLangScript.sml
    Milestone/Goal: Wasm 1.0 + tailcalls
                num/value types SANS FLOATS
                numeric (intruction)s
                parametrics
                variables
                memories
                controls
                modules

    Missing
        Functions
        Modules
        and supporting/types eg blocktypes

    Completed
        basic types
        all desired instructions in a rather hierachical encoding (all numerics/mem are factored together and the overall instruction encoding is a tagged union of )


Binary Format encoder/decoder - wasm_binary_formatScript.sml
    Milestone: Wasm 3.0 (for tailcalls) compliant encoder & decoder

    Missing
    dec_enc thms - stating that if we encode then decode a part of the AST, we get back the same thing

    Completed
    enc/dec pairs factored by instruction (AST) type

Semantics, Big step, functional - wasmSemScript.sml



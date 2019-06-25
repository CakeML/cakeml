This directory applies the translator to the compiler in order to
produce a deep embedding of the entire shallowly embedded compiler.
The translator is proof-producing. This means that each deep embedding
comes with a certificate theorem that relates the deep embedding to
the original shallow embedding.

[ag32ProgScript.sml](ag32ProgScript.sml):
Translate the ag32 instruction encoder and ag32-specific config.

[arm7ProgScript.sml](arm7ProgScript.sml):
Translate the ARMv7 instruction encoder and ARMv7-specific config.

[arm8ProgScript.sml](arm8ProgScript.sml):
Translate the ARMv8 instruction encoder and ARMv8-specific config.

[compiler32ProgScript.sml](compiler32ProgScript.sml):
Finish translation of the 32-bit version of the compiler.

[compiler64ProgScript.sml](compiler64ProgScript.sml):
Finish translation of the 64-bit version of the compiler.

[explorerProgScript.sml](explorerProgScript.sml):
Translate the compiler explorer parts of the compiler.

[inferProgScript.sml](inferProgScript.sml):
Translate the compiler's type inferencer.

[inliningLib.sml](inliningLib.sml):
Stuff used for manual inlining of encoders

[lexerProgScript.sml](lexerProgScript.sml):
Translate the compiler's lexer.

[mipsProgScript.sml](mipsProgScript.sml):
Translate the MIPS instruction encoder and MIPS-specific config.

[parserProgScript.sml](parserProgScript.sml):
Translate the compiler's parser.

[reg_allocProgScript.sml](reg_allocProgScript.sml):
Translate the compiler's register allocator.

[riscvProgScript.sml](riscvProgScript.sml):
Translate the RISC-V instruction encoder and RISC-V-specific config.

[sexp_parserProgScript.sml](sexp_parserProgScript.sml):
Translate the alternative s-expression parser.

[to_bviProgScript.sml](to_bviProgScript.sml):
Translate the backend phase from BVL to BVI.

[to_bvlProgScript.sml](to_bvlProgScript.sml):
Translate the backend phase from closLang to BVL.

[to_closProgScript.sml](to_closProgScript.sml):
Translate the backend phase from patLang to closLang.

[to_dataProgScript.sml](to_dataProgScript.sml):
Translate the backend phase from BVI to dataLang.

[to_flatProgScript.sml](to_flatProgScript.sml):
Translate backend phases up to and including flatLang.

[to_patProgScript.sml](to_patProgScript.sml):
Translate the backend phase from flatLang to patLang.

[to_target32ProgScript.sml](to_target32ProgScript.sml):
Translate the final part of the compiler backend for 32-bit targets.

[to_target64ProgScript.sml](to_target64ProgScript.sml):
Translate the final part of the compiler backend for 64-bit targets.

[to_word32ProgScript.sml](to_word32ProgScript.sml):
Translate the data_to_word part of the 32-bit compiler.

[to_word64ProgScript.sml](to_word64ProgScript.sml):
Translate the data_to_word part of the 64-bit compiler.

[x64ProgScript.sml](x64ProgScript.sml):
Translate the x64 instruction encoder and x64-specific config.

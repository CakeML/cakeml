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

[basis_defProgScript.sml](basis_defProgScript.sml):
Translate the basis library term.

[compiler_ag32ProgScript.sml](compiler_ag32ProgScript.sml):
Native AG32 batch entry point for the compiler.

[compiler_arm8ProgScript.sml](compiler_arm8ProgScript.sml):
Native ARM8 entry point for the compiler.

[compiler_commonProgScript.sml](compiler_commonProgScript.sml):
Shared CakeML compiler translation for the native entry points.

[compiler_mainProgScript.sml](compiler_mainProgScript.sml):
Shared host selection, REPL and entry points for the native compiler programs.

[compiler_x64ProgScript.sml](compiler_x64ProgScript.sml):
Native x64 entry point for the compiler.

[decProgScript.sml](decProgScript.sml):
Translation of CakeML source AST

[decodeProgScript.sml](decodeProgScript.sml):
Translate the compiler's state decoder.

[explorerProgScript.sml](explorerProgScript.sml):
Translate the compiler explorer parts of the compiler.

[from_bviProgScript.sml](from_bviProgScript.sml):
Translate the backend from BVI to target code.

[from_bvlProgScript.sml](from_bvlProgScript.sml):
Translate the backend from BVL to target code.

[from_cakeProgScript.sml](from_cakeProgScript.sml):
Translate the complete CakeML compiler backend.

[from_closProgScript.sml](from_closProgScript.sml):
Translate the backend from closLang to target code.

[from_dataProgScript.sml](from_dataProgScript.sml):
Translate the backend from dataLang to target code.

[from_flatProgScript.sml](from_flatProgScript.sml):
Translate the backend from flatLang to target code.

[from_labProgScript.sml](from_labProgScript.sml):
Translate the backend from labelled assembly to target code.

[from_stackProgScript.sml](from_stackProgScript.sml):
Translate the backend from stackLang to target code.

[from_wordProgScript.sml](from_wordProgScript.sml):
Translate the wordLang backend and shared compiler interface.

[hol_baseProgScript.sml](hol_baseProgScript.sml):
Translation of standard library functions

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

[printingProgScript.sml](printingProgScript.sml):
Translate the pretty printing functions for the REPL

[reg_allocProgScript.sml](reg_allocProgScript.sml):
Translate the compiler's register allocator.

[riscvProgScript.sml](riscvProgScript.sml):
Translate the RISC-V instruction encoder and RISC-V-specific config.

[x64ProgScript.sml](x64ProgScript.sml):
Translate the x64 instruction encoder and x64-specific config.

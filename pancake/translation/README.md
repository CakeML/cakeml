Translations for the standalone Pancake compiler. The translation branches
from the CakeML compiler at from_wordProg. All native entry points extend
pancake_compilerProg.

[from_pancakeProgScript.sml](from_pancakeProgScript.sml):
Translate the pan_to_target part of the compiler for all targets.

[pancake_compilerProgScript.sml](pancake_compilerProgScript.sml):
Shared command-line entry point for the Pancake compiler.

[pancake_compiler_arm8ProgScript.sml](pancake_compiler_arm8ProgScript.sml):
Native ARM8 entry point for the Pancake compiler.

[pancake_compiler_riscvProgScript.sml](pancake_compiler_riscvProgScript.sml):
Native RISC-V64 entry point for the Pancake compiler.

[pancake_compiler_x64ProgScript.sml](pancake_compiler_x64ProgScript.sml):
Native x64 entry point for the Pancake compiler.

[pancake_lexProgScript.sml](pancake_lexProgScript.sml):
Translate pancake's lexer

[pancake_parseProgScript.sml](pancake_parseProgScript.sml):
Translate pancake's parser

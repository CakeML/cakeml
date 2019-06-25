This directory contains the Silver-specific part of the compiler
backend and associated proofs.

[ag32_compileLib.sml](ag32_compileLib.sml):
Provides a compset for the ag32-specific parts of the backend

[ag32_configScript.sml](ag32_configScript.sml):
Define the compiler configuration for ag32

[ag32_memoryScript.sml](ag32_memoryScript.sml):
Define the memory layout for running CakeML programs on Silver, and implement
the startup code, the FFI jumps, and the CakeML basis's primitive FFI calls
in Silver machine code. Also define shallow embeddings of the FFI primitives
and prove theorems summarising their effects.

[export_ag32Script.sml](export_ag32Script.sml):
Define the format of the compiler-generated output file for ag32

[proofs](proofs):
This directory contains the Silver-specific proofs.

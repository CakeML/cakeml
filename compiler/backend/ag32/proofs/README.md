This directory contains the Silver-specific proofs.

[ag32_basis_ffiProofScript.sml](ag32_basis_ffiProofScript.sml):
Verify that the ag32 implementation of the FFI primitives satisfies
interference_implemented.

[ag32_configProofScript.sml](ag32_configProofScript.sml):
For ag32, prove that the compiler configuration is well formed, and
instantiate the compiler correctness theorem.

[ag32_decompilerLib.sml](ag32_decompilerLib.sml):
A decompiler that extracts a low-level shallow embedding from
deeply embedded ag32 code.

[ag32_ffi_codeProofScript.sml](ag32_ffi_codeProofScript.sml):
Verify the deep embeddings of the ag32 implementation of the CakeML
basis FFI primitives.

[ag32_machine_configScript.sml](ag32_machine_configScript.sml):
Define the Sliver machine configuration.
This includes the FFI interference oracle.

[ag32_memoryProofScript.sml](ag32_memoryProofScript.sml):
Prove some properties about the ag32 memory layout including
correctness of the startup code and length and lookup theorems for
other parts of memory.

[ag32_progScript.sml](ag32_progScript.sml):
Defines an ag32 instantiation of the machine-code Hoare triple for
the decompiler.

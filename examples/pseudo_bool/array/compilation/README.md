Compiling the pseudo-boolean constraints checker.

[npbc_compile_configProofScript.sml](npbc_compile_configProofScript.sml):
The compiler configurations of the CakePB executables satisfy the
assumptions of the compiler correctness theorem: each is the default
configuration with only clos_conf.max_app changed

[npbc_compile_configScript.sml](npbc_compile_configScript.sml):
The compiler configurations of the CakePB executables: the default x64
and arm8 configurations with clos_conf.max_app raised to 20

[npbc_fullCompileScript.sml](npbc_fullCompileScript.sml):
Compiles the PB checker example by evaluation inside the logic of HOL

[proofs](proofs):
Prove end-to-end correctness theorem for PB checker with arrays.

[proofsARM8](proofsARM8):
Prove end-to-end correctness theorem for PB checker with arrays
against the ARMv8 model.

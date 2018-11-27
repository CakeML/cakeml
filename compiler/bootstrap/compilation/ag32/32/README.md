This directory contains scripts that compile the CakeML compiler
inside the logic to produce the verified machine code version of the
32-bit compiler.

[ag32BootstrapScript.sml](ag32BootstrapScript.sml):
Evaluate the final part of the 32-bit version of the compiler
into machine code for ag32, i.e. the Silver ISA.

[proofs](proofs):
This directory contains the end-to-end correctness theorem for the
32-bit version of the CakeML compiler.

[to_dataBootstrapScript.sml](to_dataBootstrapScript.sml):
Evaluate the 32-bit version of the compiler down to a DataLang
program.

[to_lab_ag32BootstrapScript.sml](to_lab_ag32BootstrapScript.sml):
Evaluate the 32-bit version of the compiler down to a LabLang
program (an assembly program).

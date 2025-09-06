Proof of soundness for the Candle theorem prover.

[ast_extrasScript.sml](ast_extrasScript.sml):
Useful predicates on the CakeML ast.

[candle_basis_evaluateScript.sml](candle_basis_evaluateScript.sml):
Proving that the basis program only produces v_ok values.

[candle_kernelProgScript.sml](candle_kernelProgScript.sml):
Adds Candle specific functions to the kernel module from ml_hol_kernel_funsProg

[candle_kernel_funsScript.sml](candle_kernel_funsScript.sml):
Prove that kernel functions maintain Candle prover's invariants

[candle_kernel_permsScript.sml](candle_kernel_permsScript.sml):
Prove perms theorems for kernel functions

[candle_kernel_valsScript.sml](candle_kernel_valsScript.sml):
Theorems about values from the Candle kernel program

[candle_prover_evaluateScript.sml](candle_prover_evaluateScript.sml):
Proving that Candle prover maintains its invariants (i.e. v_ok)

[candle_prover_invScript.sml](candle_prover_invScript.sml):
Definitions of invariants that are to be maintained during
evaluate of Candle prover

[candle_prover_semanticsScript.sml](candle_prover_semanticsScript.sml):
Top-level soundness theorem for the Candle theorem prover.

[compute](compute):
A verified Candle compute primitive.

[permsScript.sml](permsScript.sml):
Permissions for CakeML values.

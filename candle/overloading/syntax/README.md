Syntax of the HOL inference system.

[holAxiomsSyntaxScript.sml](holAxiomsSyntaxScript.sml):
Context extensions for asserting the mathematical axioms.

[holBoolSyntaxScript.sml](holBoolSyntaxScript.sml):
Definitions to extend a theory context to include the theory of
Booleans, and some basic syntactic properties about these
extensions.

[holConservativeScript.sml](holConservativeScript.sml):
Functions and proofs about expanding constant definitions.

[holSyntaxCyclicityScript.sml](holSyntaxCyclicityScript.sml):
Implementation of cyclicity check for function definitions

[holSyntaxExtraScript.sml](holSyntaxExtraScript.sml):
Some lemmas about the syntactic functions.

[holSyntaxRenamingScript.sml](holSyntaxRenamingScript.sml):
Verification of `rename_apart`:
`rename_apart r c` gives a function f, such that
f(r) ∩ c = ∅ ,  f(r) ∩ r = ∅  and dom(f) = r ∩ c.

[holSyntaxScript.sml](holSyntaxScript.sml):
Defines the HOL inference system.

[holSyntaxSyntax.sml](holSyntaxSyntax.sml):
ML functions for constructing and picking apart terms arising from
holSyntaxTheory.

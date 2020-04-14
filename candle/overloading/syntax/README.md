Syntax of the HOL inference system with ad-hoc overloading.

[holAxiomsSyntaxScript.sml](holAxiomsSyntaxScript.sml):
Context extensions for asserting the mathematical axioms.

[holBoolSyntaxScript.sml](holBoolSyntaxScript.sml):
Definitions to extend a theory context to include the theory of
Booleans, and some basic syntactic properties about these
extensions.

[holSyntaxCyclicityScript.sml](holSyntaxCyclicityScript.sml):
Implementation of cyclicity check for function definitions

[holSyntaxExtraScript.sml](holSyntaxExtraScript.sml):
Some lemmas about the syntactic functions.

[holSyntaxRenamingScript.sml](holSyntaxRenamingScript.sml):
Verification of `rename_apart`:
`rename_apart r c` gives a function f, such that
f(r) ∩ c = ∅ ,  f(r) ∩ r = ∅  and dom(f) = r ∩ c.

[holSyntaxRenamingTyvarScript.sml](holSyntaxRenamingTyvarScript.sml):
* Properties of RenamingTheory for our syntax

[holSyntaxScript.sml](holSyntaxScript.sml):
Defines the HOL inference system.

[holSyntaxSyntax.sml](holSyntaxSyntax.sml):
ML functions for constructing and picking apart terms arising from
holSyntaxTheory.

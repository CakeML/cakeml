Theorems about CakeML's syntax and semantics.

[astPropsScript.sml](astPropsScript.sml):
Basic properties of the AST.
TODO: delete this theory (it has no content)

[cmlPtreeConversionPropsScript.sml](cmlPtreeConversionPropsScript.sml):
Definition of a function for mapping types back to ASTs, and proofs that
check that the conversion functions are doing something reasonable.
TODO: check this description is correct

[evaluateComputeLib.sml](evaluateComputeLib.sml):
compset for the operational semantics.

[evaluatePropsScript.sml](evaluatePropsScript.sml):
Properties of the operational semantics.

[gramPropsScript.sml](gramPropsScript.sml):
Properties of the CakeML CFG, including automatically derived
nullability results for various non-terminals, and results about
the grammar’s rules finite map.

[namespacePropsScript.sml](namespacePropsScript.sml):
Proofs about the namespace datatype.

[primSemEnvScript.sml](primSemEnvScript.sml):
TODO: document

[semanticPrimitivesPropsScript.sml](semanticPrimitivesPropsScript.sml):
Various basic properties of the semantic primitives.

[semanticsComputeLib.sml](semanticsComputeLib.sml):
compset for parts of the semantics, including the lexer.

[semanticsPropsScript.sml](semanticsPropsScript.sml):
Theorems about the top-level semantics, including totality and determinism.

[typeIdRenamingScript.sml](typeIdRenamingScript.sml):
Theorems about switching type identifiers used in checking expressions and
definitions.

[typeSoundInvariantsScript.sml](typeSoundInvariantsScript.sml):
A type system for values, and
the invariants that are used for type soundness.

[typeSoundScript.sml](typeSoundScript.sml):
Proof of type soundness: a type-correct program does not crash.

[typeSysPropsScript.sml](typeSysPropsScript.sml):
Theorems about the type system.

[weakeningScript.sml](weakeningScript.sml):
Weakening lemmas used in type soundness

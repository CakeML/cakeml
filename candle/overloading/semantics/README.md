Semantics, soundness, and consistency for the HOL inference system
with ad-hoc overloading of constant definitions.

[holBoolScript.sml](holBoolScript.sml):
Define semantics for the Boolean operations and show the definitions are
correct.

[holConsistencyScript.sml](holConsistencyScript.sml):
Proves consistency of the inference system: starting from any context with a
model, any context reached by non-axiomatic extensions has both provable and
unprovable sequents. And the base case: the HOL contexts (initial context
with no axioms, with all but infinity axiom, with all three axioms) have
models (under suitable assumptions).

[holExtensionScript.sml](holExtensionScript.sml):
Proves soundness of the context extension rules: any model of a context can
be extended to a model of the context obtained by applying one of the
non-axiomatic context updates.

[holModelConservativityScript.sml](holModelConservativityScript.sml):
Proves [model-theoretic conservative extension of
HOL](https://doi.org/10.1016/j.entcs.2018.10.009), extending a model of a
theory wrt a theory update. The model extension keeps those interpretations of
the smaller model, for types and constants from the so-called *independent
fragment*. In the independent fragment are all types and constants that are
not depending on what is introduced by the update.

[holSemanticsExtraScript.sml](holSemanticsExtraScript.sml):
Some lemmas about the semantics.

[holSemanticsScript.sml](holSemanticsScript.sml):
Define semantics for HOL sequents, in particular the notion of entailment
i.e. valid sequents, which are those that are satisfied by any model of the
theory context.

[holSoundnessScript.sml](holSoundnessScript.sml):
Proves soundness of the inference system: any provable sequent is valid.

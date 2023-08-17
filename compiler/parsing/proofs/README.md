Soundness and completeness proofs for the CakeML PEG.

[cmlNTPropsScript.sml](cmlNTPropsScript.sml):
Properties (first sets etc) for non-terminals in the CakeML grammar

[parserProofScript.sml](parserProofScript.sml):
Correctness proof for the parser; showing that the parse_prog implementation
conforms to the specification (semantics$parse).

[pegCompleteScript.sml](pegCompleteScript.sml):
Completeness proof for the parser. If a successful parse exists,
then the parser will find one.

[pegSoundScript.sml](pegSoundScript.sml):
Soundness proof for the parser. If the parser returns a parse tree,
then it is valid w.r.t. the specification grammar.

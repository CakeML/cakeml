Soundness and completeness proofs for the CakeML PEG.

[pegCompleteScript.sml](pegCompleteScript.sml):
Completeness proof for the parser. If a successful parse exists,
then the parser will find one.

[pegSoundScript.sml](pegSoundScript.sml):
Soundness proof for the parser. If the parser returns a parse tree,
then it is valid w.r.t. the specification grammar.

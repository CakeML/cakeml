Implementation of an OpenTheory reader based on the Candle kernel.

[compilation](compilation):
This directory contains the script that does in-logic compilation of
the OpenTheory article checker.

[monadIO](monadIO):
This directory contains a version of the OpenTheory article checker
where the I/O part is built using the monadic translator.

[prettyScript.sml](prettyScript.sml):
A pretty printer producing strings.
Based on the pretty printer from "ML from the working programmer".

[readerProgScript.sml](readerProgScript.sml):
Deeply embedded CakeML program that implements an OpenTheory article
checker.

[readerProofScript.sml](readerProofScript.sml):
Correctness proofs about the OpenTheory article checker's CakeML
implementation. In particular, anything the article checker proves
follows by logical inference in Candle's version of the HOL logic.

[readerScript.sml](readerScript.sml):
Shallowly embedded (monadic) functions that implement the OpenTheory
article checker.

[readerSoundnessScript.sml](readerSoundnessScript.sml):
Proves soundness of the OpenTheory article checker. The soundness
theorem makes the connection to the semantics of HOL explicit.

[reader_commonProgScript.sml](reader_commonProgScript.sml):
There are two 'frontends' to the OpenTheory reader. This theory contains
translations of the functions which are used by both versions so that we
do not translate more than once.

[reader_initScript.sml](reader_initScript.sml):
Kernel initialisation

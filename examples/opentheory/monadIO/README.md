This directory contains a version of the OpenTheory article checker
where the I/O part is built using the monadic translator.

[compilation](compilation):
This directory contains scripts that compile th OpenTheory article
checker by evaluation in the logic of HOL.

[readerIOProgScript.sml](readerIOProgScript.sml):
Applying the monadic translator to OpenTheory article reader
expressed using a basis-compatible IO monad.

[readerIOProofScript.sml](readerIOProofScript.sml):
Verification of the OpenTheory article checker expressed using an IO
monad for the basis.

[readerIOScript.sml](readerIOScript.sml):
The OpenTheory article reader defined using an IO monad for the
basis library.

This directory contains solutions for the tutorial.

[simple_bstScript.sml](simple_bstScript.sml):
Simple binary search tree.

[splitwordsScript.sml](splitwordsScript.sml):
A high-level specification of words and frequencies

[wordfreqCompileScript.sml](wordfreqCompileScript.sml):
Compile the wordfreq program to machine code by evaluation of the compiler in
the logic.

[wordfreqProgScript.sml](wordfreqProgScript.sml):
The CakeML program implementing the word frequency application.
This is produced by a combination of translation and CF verification.

[wordfreqProofScript.sml](wordfreqProofScript.sml):
Constructs the end-to-end correctness theorem for wordfreq example
by composing the application-specific correctness theorem, the
compiler evaluation theorem and the compiler correctness theorem.

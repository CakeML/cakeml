An extended worked example on using HOL and CakeML to write verified programs,
that was presented as a tutorial on CakeML at PLDI and ICFP in 2017.

[arith_exp_demoScript.sml](arith_exp_demoScript.sml):
A demonstration of interaction with HOL: a simple datatype for arithmetic
expressions.

[simple_bstProgScript.sml](simple_bstProgScript.sml):
Using the CakeML translator to produce a verified deep embedding of the
simple BST implementation.

[simple_bstScript.sml](simple_bstScript.sml):
Simple binary search tree.

[solutions](solutions):
This directory contains solutions for the tutorial.

[splitwordsScript.sml](splitwordsScript.sml):
A high-level specification of words and frequencies

[wordcountCompileScript.sml](wordcountCompileScript.sml):
Compile the wordcount program to machine code by evaluation of the compiler
in the logic.

[wordcountProgScript.sml](wordcountProgScript.sml):
Simple wordcount program, to demonstrate use of CF.

[wordcountProofScript.sml](wordcountProofScript.sml):
Constructs the end-to-end correctness theorem for wordcount example
by composing the application-specific correctness theorem, the
compiler evaluation theorem and the compiler correctness theorem.

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

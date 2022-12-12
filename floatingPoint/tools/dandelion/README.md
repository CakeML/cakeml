# Dandelion

A certificate checker for approximations of elementary functions.

## Building Dandelion

Dandelion relies on a copy of sollya (sollya.org). Therefore it is
necessary to run `Holmake` in this directory to execute the code
in `.hol_preexec`.

## Key theorems and definitions relating to the original ITP'22 paper

The first phase is defined across the files `transcApproxSemScript.sml` and
`approxPolyScript.sml`. The first file defines the overall approximation
function `approxAsPoly` and gives its soundness proof, and
`approxPolyScript.sml` defines the low-level approximation function for
approximating a single elementary function with a single polynomial and proves
soundness of this function.

Theorem 4 (First Phase Soundness) from section 3 is proven in file
`transcApproxSemScript.sml` as `approxTransc_sound`.
Variants of Theorem 5 are proven for the supported elementary function in file
`mcLaurinApproxScript.sml` if they are not provided by HOL4.
Variants of Theorem 6 are proven for the supported elementary functions in file
`approxPolyScript.sml`.

The second phase is implemented and proven sound in the file
`checkerScript.sml`.
It relies on the implementation of computable Sturm sequences in
`sturmComputeScript.sml` and computable polynomial division in
`euclidDivScript.sml`.

Theorem 7 (Second Phase Soundness) from section 4 is proven in file
`checkerScript.sml` as the combination of `numZeros_sound`,
`validBounds_is_valid`, and `validateZerosLeqErr_sound`.

Theorem 8 was ported from Harrison's HOL-Light proofs in file `drangScript.sml`
and is called `BOUND_THEOREM_INEXACT`.

Theorem 9 (Dandelion soundness) is called `checker_soundness` in file
`checkerScript.sml`.

The extracted binary is created in the directory `binary`.
File `translateScript.sml` sets up the CakeML translation of the definitions of
Dandelion, file `certParserScript.sml` defines our (unverified) parser and
lexer, file `sturmMainCakeScript.sml` proves the CakeML specification for the
binary, and file `sturmMainCakeCompileScript.sml` compiles the binary for the
second phase by running the CakeML compiler in-logic on the translated
definitions.

[approxCompErrScript.sml](approxCompErrScript.sml):
Theorems about how to compose errors from truncated Taylor series
for each supported elementary function

[approxPolyScript.sml](approxPolyScript.sml):
Function that computes a polynomial approximation for a single elementary
function on a fixed interval, and its soundness proof.
Function approxPoly is reused in transcApproxSemScript.sml to build the overall
function implementing the first phase of Dandelion

[checkerDefsScript.sml](checkerDefsScript.sml):
Basic definitions used by Dandelion

[checkerScript.sml](checkerScript.sml):
Define high-level functions used by Dandelion and prove their
soundness by composing soundness proofs from the included files

[cosDeg3Script.sml](cosDeg3Script.sml):
Simple cosine of degree 3

[drangScript.sml](drangScript.sml):
Proofs ported about extrema of real-valued, univariate functions,
ported from the work by Harrison

[euclidDivScript.sml](euclidDivScript.sml):
Computable version of polynomial division and a correctness proof.
Inspired by the implementation in Isabelle/HOL
isabelle.in.tum.de/library/HOL/HOL-Computational_Algebra/Polynomial.html
used to implement a computable version of Sturm sequences

[floverConnScript.sml](floverConnScript.sml):
Connection to FloVer roundoff error analyzer, currently unused

[mcLaurinApproxScript.sml](mcLaurinApproxScript.sml):
Proofs of McLaurin series for the supported elementary functions
described in transcLang file

[moreRealScript.sml](moreRealScript.sml):
small theorems extending HOL4's realTheory
used throughout the development

[pointCheckerProofsScript.sml](pointCheckerProofsScript.sml):
Soundness theorem of the point-wise equivalence checker
Currently unused

[pointCheckerScript.sml](pointCheckerScript.sml):
A simple checker for polynomial evaluation
Part one of the soundness proof requires showing that the approximated
polynomial agrees with what Remez thought the trancendental function behaves
like on the set of points Ω

[realPolyProofsScript.sml](realPolyProofsScript.sml):
Some simple properties of polynomials on reals

[realPolyScript.sml](realPolyScript.sml):
Definition of datatype for real-valued polynomials

[realZeroLib.sml](realZeroLib.sml):
Library implementing the automatic computations
done by Dandelion

[renameScript.sml](renameScript.sml):
renaming theory to unify naming of theorems

[sinDeg3Script.sml](sinDeg3Script.sml):
Simple approximation of sine of degree 3

[sollya-8.0](sollya-8.0):
Dependency to generate unverified guesses

[sturmComputeScript.sml](sturmComputeScript.sml):
Define a computable version of the sturm sequence and
prove its equivalence with the non-computable version
of John Harrison

[sturmScript.sml](sturmScript.sml):
Proof of Sturm's theorem, ported from Harrison material

[transcApproxSemScript.sml](transcApproxSemScript.sml):
Define an "approximating" semantics on the elementary functions
of Dandelion. The function approxTransc corresponds to the
function "approxAsPoly" in the paper

[transcIntvSemScript.sml](transcIntvSemScript.sml):
Define an interval semantics on the elementary functions
of Dandelion. The function borrows the definitions and soundness
proof of basic arithmetic from FloVer

[transcLangScript.sml](transcLangScript.sml):
Define a simple "language" for describing elementary
functions. For now we only allow combinations, i.e.
exp (sin (cos ...) but no additional operators like +,-,*,/

[transcReflectScript.sml](transcReflectScript.sml):
Simple reflection function translating elements of the deeply
embedded transc datatype into the polynomials defined in
realPolyScript.sml

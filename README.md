The CakeML project: https://cakeml.org
======================================

CakeML is a verified implementation of a significant subset of
Standard ML.

The source and proofs for CakeML are developed in the [HOL4 theorem
prover](http://hol-theorem-prover.org). We use the latest development
version of [HOL4](https://github.com/HOL-Theorem-Prover/HOL), which we
build on [PolyML 5.7](http://www.polyml.org).
Example build instructions can be found in
[build-instructions.sh](build-instructions.sh).

Building all of CakeML (including the bootstrapped compiler and its proofs)
requires significant resources. [Built copies](https://cakeml.org/download) of
the compiler and resource usage for our
[regression tests](https://cakeml.org/regression.cgi) are online.

The [master](../../tree/master) branch contains the latest development
version of CakeML. See the [version2](../../tree/version2) or
[version1](../../tree/version1) branch for previous versions.

Directory structure
-------------------

[COPYING](COPYING):
CakeML Copyright Notice, License, and Disclaimer.

[basis](basis):
Contains the beginnings of a standard basis library for CakeML,
similar to the standard basis library of SML.

[build-instructions.sh](build-instructions.sh):
This file describes how to install Poly/ML, HOL and CakeML.

[candle](candle):
Verification of a HOL theorem prover, based on HOL Light
(http://www.cl.cam.ac.uk/~jrh13/hol-light/), implemented in CakeML.

[characteristic](characteristic):
A verified CakeML adaption of Arthur Charguéraud's "Characteristic
Formulae for the Verification of Imperative Programs"

[compiler](compiler):
A verified compiler for CakeML, including:
 - parsing: lexer and PEG parser
 - inference: type inferencer
 - backend: compilation to ASM assembly language
 - targets: code generation to x86, ARM, and more

[developers](developers):
This directory contains scripts for automating routine tasks, e.g., for
generating README.md files.

[documentation](documentation):
Work-in-progress documentation regarding the CakeML language.

[examples](examples):
Examples of verified programs built using CakeML infrastructure.

[misc](misc):
Auxiliary files providing glue between a standard HOL installation
and what we want to use for CakeML development.

[semantics](semantics):
The definition of the CakeML language. The definition is (mostly)
expressed in Lem (http://www.cs.kent.ac.uk/~sao/lem), but the
generated HOL is also included. The directory includes definitions of:
 - the concrete syntax
 - the abstract syntax
 - small step semantics
 - big step semantics (both functional and relational)
 - semantics of FFI calls
 - a type system

[translator](translator):
A proof-producing translator from HOL functions to CakeML.

[tutorial](tutorial):
An extended worked example on using HOL and CakeML to write verified programs,
to be presented as a tutorial on CakeML at PLDI and ICFP in 2017.

[unverified](unverified):
Various unverified tools, e.g. tools for converting OCaml to CakeML
and an SML version of the CakeML register allocator.

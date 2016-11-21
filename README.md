The CakeML project: https://cakeml.org
======================================

CakeML is a verified implementation of a significant subset of
Standard ML.

The source and proofs for CakeML are developed in the [HOL4 theorem
prover](http://hol-theorem-prover.org).  We use the latest development
version of [HOL4](https://github.com/HOL-Theorem-Prover/HOL), which we
build on [PolyML 5.6](http://www.polyml.org).
Example build instructions can be found in
[build-instructions.sh](build-instructions.sh).

The [master](../../tree/master) branch contains the latest development
version of CakeML.  See the [version1](../../tree/version1) branch for
the previous version.

Directory structure
-------------------

[COPYING](COPYING):
CakeML Copyright Notice, License, and Disclaimer.

[basis](basis):
Contains the beginnings of a standard basis library for CakeML,
similar to the standard basis library of SML.

[build-instructions.sh](build-instructions.sh):
This script installs Poly/ML, HOL and CakeML.

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
This directory contains scripts for automating routine tasks, e.g. for
running regression tests.

[documentation](documentation):
Work-in-progress documentation regarding the CakeML language.

[explorer](explorer):
Tools for stepping through execution of the compiler from one
intermediate language to the next, and pretty-printing the
intermediate results. An instance is available on the CakeML website.

[flame](flame):
The start of a set theory formalisation that has net yet been used.

[lem_lib_stub](lem_lib_stub):
Empty versions of the Lem libraries (which we don't use, but building
with Lem requires)

[lib.lem](lib.lem):
Extensions to Lem's built-in library to target things we need in HOL.

[miscScript.sml](miscScript.sml):
Miscellaneous definitions and minor lemmas used throughout the
development.

[mlstringScript.sml](mlstringScript.sml):
Small theory of wrapped strings, so the translator can distinguish
them from char lists and can target CakeML strings directly.

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

[unverified](unverified):
Various unverified tools, e.g. tools for converting OCaml to CakeML
and an SML version of the CakeML register allocator.

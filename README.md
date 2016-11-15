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

[build-instructions.sh](build-instructions.sh):
This script installs Poly/ML, HOL and CakeML.

[developers](developers):
This directory contains scripts for automating routine tasks, e.g. for
running regression tests.

[miscScript.sml](miscScript.sml):
Miscellaneous definitions and minor lemmas used throughout the
development.

[mlstringScript.sml](mlstringScript.sml):
Small theory of wrapped strings, so the translator can distinguish
them from char lists and can target CakeML strings directly.

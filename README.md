The CakeML project: https://cakeml.org
======================================

CakeML is a verified implementation of a significant subset of
Standard ML in the [HOL4 theorem prover](http://hol-theorem-prover.org).

We build the CakeML sources using the latest development version of
[HOL4](https://github.com/HOL-Theorem-Prover/HOL).  We build HOL on
[PolyML 5.6](http://www.polyml.org).  Example build instructions can
be found in [build-instructions.sh].

The `master` branch contains the latest development version of CakeML.
See the `version1` branch for the previous version.

Directory structure
-------------------

[](COPYING):
CakeML Copyright Notice, License, and Disclaimer.

[](build-instructions.sh):
This script installs Poly/ML, HOL and CakeML.

[](developers):
This directory contains scripts for automating routine tasks, e.g. for
running regression tests.

[](miscScript.sml):
Miscellaneous definitions and minor lemmas used throughout the
development.

[](mlstringScript.sml):
Small theory of wrapped strings, so the translator can distinguish
them from char lists and can target CakeML strings directly.

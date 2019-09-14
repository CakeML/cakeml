Contains the beginnings of a standard basis library for CakeML,
similar to the standard basis library of SML.

[ArrayProgScript.sml](ArrayProgScript.sml):
A module about Arrays for the CakeML standard basis library.

[ArrayProofScript.sml](ArrayProofScript.sml):
Proofs about the Array module.

[CharProgScript.sml](CharProgScript.sml):
A module about the char type for the CakeML standard basis library.

[CommandLineProgScript.sml](CommandLineProgScript.sml):
A module about command-line arguments for the CakeML standard basis
library.

[CommandLineProofScript.sml](CommandLineProofScript.sml):
Proof about the command-line module of the CakeML standard basis library.

[DoubleFFIScript.sml](DoubleFFIScript.sml):
Logical model of the FFI calls for functions to-/fromString in
the Double module.

[DoubleProgScript.sml](DoubleProgScript.sml):
Module for the built-in double floating-point type.
Defines basic arithmetic operations like +,-,*,/, and FMA,
logical operations <, <=, >, >=, and =
and to-/fromString functions for parsing and pretty-printing constants

[DoubleProofScript.sml](DoubleProofScript.sml):
Proofs that the to-/fromString functions in the Double
module correctly produce a string representation from a double,
and vice versa assuming that the FFI is implemented correctly.

[HashtableProgScript.sml](HashtableProgScript.sml):
A module about hash tables for the CakeML standard basis library.

[HashtableProofScript.sml](HashtableProofScript.sml):
Proof of the hashtable module

[IntProgScript.sml](IntProgScript.sml):
Module about the built-in integer type. Note that CakeML uses
arbitrary precision integers (the mathematical intergers).

[ListProgScript.sml](ListProgScript.sml):
Module about the built-in list tyoe.

[ListProofScript.sml](ListProofScript.sml):
Proofs about the module about the list tyoe.

[MapProgScript.sml](MapProgScript.sml):
This module contains CakeML code implementing a functional map type
using a self-balancing binary tree.

[MarshallingProgScript.sml](MarshallingProgScript.sml):
Module with functions that aid converting to and from the byte
arrays that CakeML foreign-function interface (FFI) uses.

[MarshallingScript.sml](MarshallingScript.sml):
HOL functions that aid converting to and from the byte arrays that
CakeML foreign-function interface (FFI) uses.

[OptionProgScript.sml](OptionProgScript.sml):
Module about the option tyoe.

[PrettyPrinterProgScript.sml](PrettyPrinterProgScript.sml):
Module providing various functions that can be used to efficiently
pretty-print values of different types.

[RatProgScript.sml](RatProgScript.sml):
Module for computing over the rational numbers.

[RuntimeProgScript.sml](RuntimeProgScript.sml):
Module that contains a few special functions, e.g. a function for
forcing a full GC to run, a function for producing debug output.

[RuntimeProofScript.sml](RuntimeProofScript.sml):
Proof about the exit function in the Runtime module.

[StringProgScript.sml](StringProgScript.sml):
Module about the built-in string tyoe.

[TextIOProgScript.sml](TextIOProgScript.sml):
Module for text-based I/O with the underlying file system.

[TextIOProofScript.sml](TextIOProofScript.sml):
Proofs about the code in the TextIO module.
load "cfLib";
load "cfMonadLib";
load "ArrayProofTheory";
load "basisFunctionsLib";
load "fsFFITheory";
load "fsFFIPropsTheory";
load "Word8ArrayProofTheory";
load "TextIOProgTheory";
load "MarshallingProgTheory";

[VectorProgScript.sml](VectorProgScript.sml):
Module about the built-in 'a vector.

[Word64ProgScript.sml](Word64ProgScript.sml):
Module about the built-in word64 type.

[Word8ArrayProgScript.sml](Word8ArrayProgScript.sml):
Module about the built-in byte-array type.

[Word8ArrayProofScript.sml](Word8ArrayProofScript.sml):
Proof about the code in the byte-array module Word8Array.

[Word8ProgScript.sml](Word8ProgScript.sml):
Module about the built-in word8 type.

[basisFunctionsLib.sml](basisFunctionsLib.sml):
Functions that aid building the CakeML code for the basis library.

[basisProgScript.sml](basisProgScript.sml):
Contains the code for the entire CakeML basis library in basis_def.

[basis_ffi.c](basis_ffi.c):
Implements the foreign function interface (FFI) used in the CakeML basis
library, as a thin wrapper around the relevant system calls.

[basis_ffiLib.sml](basis_ffiLib.sml):
Automation for instantiating the FFI oracle with the
basis library functions, and removing CF separation logic.

[basis_ffiScript.sml](basis_ffiScript.sml):
Instantiate the CakeML FFI oracle for the oracle of the basis library.

[clFFIScript.sml](clFFIScript.sml):
Logical model of the commandline state: simply a list of mlstrings

[dependency-order](dependency-order):
This file records the current, linear dependency order between the
translation/CF theories making up the basis library verification.

[fsFFIPropsScript.sml](fsFFIPropsScript.sml):
Lemmas about the file system model used by the proof about TextIO.

[fsFFIScript.sml](fsFFIScript.sml):
Logical model of filesystem and I/O streams

[mlbasicsProgScript.sml](mlbasicsProgScript.sml):
Bind various built-in functions to function names that the parser
expects, e.g. the parser generates a call to a function called "+"
when it parses 1+2.

[pure](pure):
HOL definitions of the pure functions used in the CakeML basis.

[runtimeFFIScript.sml](runtimeFFIScript.sml):
Logical model of the Runtime module's exit function calls.

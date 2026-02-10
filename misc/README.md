Auxiliary files providing glue between a standard HOL installation
and what we want to use for CakeML development.

[arithLemmasScript.sml](arithLemmasScript.sml):
General-purpose arithmetic lemmas (DIV, MOD, EXP, LOG, FUNPOW, etc.)
used throughout the CakeML development.

[basicComputeLib.sml](basicComputeLib.sml):
Build a basic compset for evaluation in the logic.

[induct_tweakLib.sml](induct_tweakLib.sml):
Code for adjusting and improving induction theorems.

[listLemmasScript.sml](listLemmasScript.sml):
General-purpose list lemmas (LIST_REL, EVERY, ALOOKUP, MAP, FILTER,
GENLIST, ZIP, LUPDATE, DROP/TAKE, SNOC, FLAT, REPLICATE, SORTED,
PERM, enumerate, find_index, etc.) used throughout the CakeML development.

[miscScript.sml](miscScript.sml):
Miscellaneous definitions and minor lemmas used throughout the
development.

[optionLemmasScript.sml](optionLemmasScript.sml):
General-purpose option lemmas (OPTION_MAP, OPTION_BIND, option_le,
OPT_MMAP, option_fold, etc.) used throughout the CakeML development.

[packLib.sml](packLib.sml):
A library for packing theorems, terms, and types as theorems (which can
thereby be saved in theories).

[preamble.sml](preamble.sml):
Proof tools (e.g. tactics) used throughout the development.

[setLemmasScript.sml](setLemmasScript.sml):
General-purpose set and finite map lemmas (INJ, BIJ, SURJ, SUBSET,
DISJOINT, IMAGE, FUPDATE_LIST, FLOOKUP, FDOM, etc.)
used throughout the CakeML development.

[sptreeLemmasScript.sml](sptreeLemmasScript.sml):
General-purpose sptree lemmas (lookup, insert, delete, domain,
toAList, fromAList, subspt, eq_shape, copy_shape, range, etc.)
used throughout the CakeML development.

[wordLemmasScript.sml](wordLemmasScript.sml):
General-purpose word lemmas (bit operations, shifts, alignment,
bytes_in_memory, good_dimindex, n2w/w2n, etc.)
used throughout the CakeML development.

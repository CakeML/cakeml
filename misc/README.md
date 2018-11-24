Auxiliary files providing glue between a standard HOL installation
and what we want to use for CakeML development.

[alist_treeLib.sml](alist_treeLib.sml):
Code to recall that some partial functions (of type 'a -> 'b option)
can be represented as sorted alists, and derive a fast conversion on
applications of those functions.

[alist_treeScript.sml](alist_treeScript.sml):
Definitions and theorems that support automation (the Lib file) for
fast insertion and lookup into association lists (alists).

[basicComputeLib.sml](basicComputeLib.sml):
Build a basic compset for evaluation in the logic.

[lem_lib_stub](lem_lib_stub):
Empty versions of the Lem libraries (which we don't use, but building
with Lem requires)

[miscScript.sml](miscScript.sml):
Miscellaneous definitions and minor lemmas used throughout the
development.

[packLib.sml](packLib.sml):
A library for packing theorems, terms, and types as theorems (which can
thereby be saved in theories).

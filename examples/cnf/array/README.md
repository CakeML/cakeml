Refinement of generic CNF functions to use arrays

[ccnf_arithScript.sml](ccnf_arithScript.sml):
Specifications of the witnessed small-integer operations of Unsafe.Arith
at the types the checkers use: nums, and ints bounded by a witness

[ccnf_arrayProgScript.sml](ccnf_arrayProgScript.sml):
This refines ccnf_list to use arrays

[ccnf_listScript.sml](ccnf_listScript.sml):
This refines the CCNF functions to a fixed-size, list-based implementation.

[ccnf_parseProgScript.sml](ccnf_parseProgScript.sml):
Adds file-level parsing and formula construction to ccnf_arrayProg

Example applications of the monadic translator on in-array sort functions.

These sort functions generally have a pure (datatype recursive) instance, a
monadic theory that provides an in-array version and proves that it simulates
the pure computation, and finally a translation theory that translates the
monadic code to CakeML AST.

[heap_list_sortScript.sml](heap_list_sortScript.sml):
A heap-sort variant that builds a list of exactly-balanced heaps.

[heap_list_sort_monadicScript.sml](heap_list_sort_monadicScript.sml):
Monadic variants of the heap-list sort functions, and proofs of equivalence.

[heap_list_sort_translationScript.sml](heap_list_sort_translationScript.sml):
Post-translation of heap_list_sort

[merge_run_sortScript.sml](merge_run_sortScript.sml):
Verified run-finding (natural) merge sort.

[merge_run_sort_monadicScript.sml](merge_run_sort_monadicScript.sml):
Monadic variants of the merge-run-sort functions, and proofs of equivalence.

[merge_run_sort_translationScript.sml](merge_run_sort_translationScript.sml):
Post-translation of merge_run_sort

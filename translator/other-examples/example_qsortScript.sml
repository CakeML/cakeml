(*
  This is a simple example of applying the translator to a
  functional version of quick sort.
*)
Theory example_qsort
Ancestors
  ninetyOne arithmetic list sorting regexpMatch
Libs
  ml_translatorLib

(* qsort *)

val res = translate APPEND;
val res = translate PART_DEF;
val res = translate PARTITION_DEF;
val res = translate QSORT_DEF;


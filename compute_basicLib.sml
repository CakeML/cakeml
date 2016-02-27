structure compute_basicLib :> compute_basicLib =
struct

open HolKernel boolLib bossLib lcsymtacs
(*
open miscTheory intReduce stringLib optionLib combinLib finite_mapLib wordsLib
     spteeLib pegLib sortingTheory
*)

fun add_datatype compset tm =
  (computeLib.add_datatype_info compset o valOf o TypeBase.fetch) tm

(* compset needs to have at least wordsLib.words_compset in it *)
fun add_basic_compset compset =
  (
  (* included in words_compset
    listLib.list_rws compset
  ; numposrepLib.add_numposrep_compset compset
  ; ASCIInumbersLib.add_ASCIInumbers_compset compset
  *)
  (* HOL libraries provide compsets :) *)
    listLib.add_rich_list_compset compset
  ; listLib.add_indexedLists_compset compset
  ; intReduce.add_int_compset compset
  ; stringLib.add_string_compset compset
  ; sumSimps.SUM_rws compset
  ; optionLib.OPTION_rws compset
  ; pred_setLib.add_pred_set_compset compset
  ; combinLib.add_combin_compset compset
  ; pairLib.add_pair_compset compset
  ; finite_mapLib.add_finite_map_compset compset
  ; sptreeLib.add_sptree_compset compset
  ; pegLib.add_peg_compset compset
    (*Missing from lists*)
  ; computeLib.add_thms
    [listTheory.splitAtPki_DEF] compset
    (*sorting*)
  ; computeLib.add_thms
    [sortingTheory.PARTITION_DEF
    ,sortingTheory.PART_DEF
    ,sortingTheory.QSORT_DEF
    ] compset
  (*monadic*)
  ; computeLib.add_thms
    [state_transformerTheory.MWHILE_DEF
    ,state_transformerTheory.BIND_DEF
    ,state_transformerTheory.UNIT_DEF
    ,state_transformerTheory.FOREACH_def
    ,pairTheory.UNCURRY_DEF
    ,state_transformerTheory.IGNORE_BIND_DEF
    ]
  (* From misc *)
  ; computeLib.add_thms
      [miscTheory.find_index_def,
       miscTheory.LEAST_thm,
       miscTheory.least_from_thm,
       miscTheory.lookup_any_def,
       miscTheory.list_insert_def,
       miscTheory.list_to_num_set_def,
       miscTheory.bytes_in_word_def,
       miscTheory.UPDATE_LIST_THM,
       miscTheory.list_max_def
      ] compset
  )

val the_basic_compset =
  let
    val c = wordsLib.words_compset ()
  in
    add_basic_compset c; c
  end

end


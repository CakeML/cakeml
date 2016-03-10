structure basicComputeLib :> basicComputeLib =
struct

open HolKernel boolLib bossLib
(*
open miscTheory intReduce stringLib optionLib combinLib finite_mapLib wordsLib
     spteeLib pegLib sortingTheory
*)

fun add_datatype compset tm =
  (computeLib.add_datatype_info compset o valOf o TypeBase.fetch) tm

(* compset needs to have at least wordsLib.words_compset in it *)
fun add_basic_compset compset =
  List.app (fn f => f compset)
  [
  (* included in words_compset
    listLib.list_rws
  , numposrepLib.add_numposrep_compset
  , ASCIInumbersLib.add_ASCIInumbers_compset
  *)
  (* HOL libraries compsets *)
    listLib.add_rich_list_compset
  , listLib.add_indexedLists_compset
  , intReduce.add_int_compset
  , stringLib.add_string_compset
  , sumSimps.SUM_rws
  , optionLib.OPTION_rws
  , pred_setLib.add_pred_set_compset
  , combinLib.add_combin_compset
  , pairLib.add_pair_compset
  , finite_mapLib.add_finite_map_compset
  , sptreeLib.add_sptree_compset
  , pegLib.add_peg_compset
  , state_monadLib.add_state_monad_compset
  (* sorting *)
  , computeLib.add_thms
    [sortingTheory.PARTITION_DEF
    ,sortingTheory.PART_DEF
    ,sortingTheory.QSORT_DEF
    ]
  (* From misc *)
  , computeLib.add_thms
      [miscTheory.find_index_def,
       miscTheory.LEAST_thm,
       miscTheory.least_from_thm,
       miscTheory.lookup_any_def,
       miscTheory.list_insert_def,
       miscTheory.list_to_num_set_def,
       miscTheory.bytes_in_word_def,
       miscTheory.UPDATE_LIST_THM,
       miscTheory.list_max_def
      ]
  ]

val the_basic_compset =
  let
    val c = wordsLib.words_compset ()
  in
    add_basic_compset c; c
  end

end


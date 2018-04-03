(*
   Build a basic compset for evaluation in the logic.
*)
structure basicComputeLib :> basicComputeLib =
struct

open HolKernel boolLib bossLib
(*
open miscTheory intReduce stringLib optionLib combinLib finite_mapLib wordsLib
     sptreeLib pegLib listLib state_monadLib sortingTheory
*)

(*
  The following is designed to extend wordsLib.words_compset, which already
  includes:
  listLib.list_rws, numposrepLib.add_numposrep_compset and
  ASCIInumbersLib.add_ASCIInumbers_compset
*)

val add_basic_compset =
  computeLib.extend_compset
  [computeLib.Extenders
   [ (* HOL library compsets *)
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
   , state_monadLib.add_state_monad_compset],
   computeLib.Tys
   [ (* misc *)
     ``:α app_list``
    ,``:location$locn``
    ],
   computeLib.Defs
   [ (* misc *)
     miscTheory.find_index_def
   , miscTheory.max3_def
   , miscTheory.LEAST_thm
   , miscTheory.least_from_thm
   , miscTheory.lookup_any_def
   , miscTheory.list_insert_def
   , miscTheory.list_to_num_set_def
   , miscTheory.bytes_in_word_def
   , miscTheory.UPDATE_LIST_THM
   , miscTheory.list_max_def
   , miscTheory.anub_def
   , miscTheory.safeTL_def
   , miscTheory.zlookup_def
   , miscTheory.tlookup_def
   , miscTheory.any_el_def
   , miscTheory.append_aux_def
   , miscTheory.append_def
   , miscTheory.SmartAppend_thm
   , miscTheory.option_fold_def
   , miscTheory.list_subset_def
   , miscTheory.list_set_eq_def
   , listTheory.LIST_REL_def
   , libTheory.the_def
   (* TODO: should be in HOL *)
   ,optionTheory.OPTION_MAP2_DEF
   ,optionTheory.OPTION_JOIN_DEF
   ,alistTheory.alist_to_fmap_def
   ,alistTheory.ALOOKUP_def
   ,sortingTheory.PARTITION_DEF
   ,sortingTheory.PART_DEF
   ,sortingTheory.QSORT_DEF
   ,sptreeTheory.inter_eq_def
   ,sptreeTheory.filter_v_def] ]
end

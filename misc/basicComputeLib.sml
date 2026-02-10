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
   , state_monadLib.add_state_monad_compset
   , alistLib.add_alist_compset
   , sortingLib.add_sorting_compset],
   computeLib.Tys
   [ (* misc *)
     ``:α app_list``
    ,``:location$locn``
    ],
   computeLib.Defs
   [ (* listLemmas *)
     listLemmasTheory.find_index_def
   , listLemmasTheory.UPDATE_LIST_THM
   , listLemmasTheory.anub_def
   , listLemmasTheory.list_subset_def
   , listLemmasTheory.list_set_eq_def
     (* arithLemmas *)
   , arithLemmasTheory.LEAST_thm
   , arithLemmasTheory.least_from_thm
     (* sptreeLemmas *)
   , sptreeLemmasTheory.lookup_any_def
     (* misc *)
   , miscTheory.max3_def
   , rich_listTheory.MAX_LIST_def
   , miscTheory.zlookup_def
   , miscTheory.tlookup_def
   , miscTheory.any_el_def
   , miscTheory.append_aux_def
   , miscTheory.append_def
   , miscTheory.SmartAppend_thm
   , miscTheory.option_fold_def
   , miscTheory.the_def
   (* TODO: move to HOL *)
   , listTheory.LIST_REL_def
   , byteTheory.bytes_in_word_def
   ]
  ]
end

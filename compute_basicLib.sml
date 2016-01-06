structure compute_basicLib :> compute_basicLib =
struct

open HolKernel boolLib bossLib lcsymtacs

(*
open miscTheory intReduce stringLib optionLib combinLib finite_mapLib wordsLib
     spteeLib pegLib
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
  ; computeLib.add_thms
      [miscTheory.find_index_def,
       miscTheory.LEAST_thm,
       miscTheory.least_from_thm,
       miscTheory.lookup_any_def,
       miscTheory.list_insert_def,
       miscTheory.list_to_num_set_def
      ] compset
  )

val the_basic_compset =
  let
    val c = wordsLib.words_compset ()
  in
    add_basic_compset c; c
  end

end


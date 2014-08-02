structure compute_basicLib = struct
open HolKernel boolLib bossLib lcsymtacs

fun add_datatype tm compset =
  (computeLib.add_datatype_info compset o valOf o TypeBase.fetch) tm

(* compset needs to have at least wordsLib.words_compset in it *)
fun add_basic_compset compset =
let
  (* good libraries which provide compsets :) *)
  val () = intReduce.add_int_compset compset
  (* included in words_compset
  val () = listLib.list_rws compset
  val () = numposrepLib.add_numposrep_compset compset
  val () = ASCIInumbersLib.add_ASCIInumbers_compset compset
  *)
  val () = stringLib.add_string_compset compset
  val () = sumSimps.SUM_rws compset
  val () = optionLib.OPTION_rws compset
  val () = pred_setLib.add_pred_set_compset compset
  val () = combinLib.add_combin_compset compset
  val () = pairLib.add_pair_compset compset
  val () = finite_mapLib.add_finite_map_compset compset
  val () = pegLib.add_peg_compset compset
(* rich_list doesnt' provide a compset :( *)
  val () = computeLib.add_thms
  [rich_listTheory.SPLITP_compute
  ,rich_listTheory.SPLITP_AUX_def
  ] compset
(* sptree doesn't provide a compset :( *)
  val () = computeLib.add_thms
  [sptreeTheory.lookup_compute
  ,sptreeTheory.insert_compute
  ,sptreeTheory.delete_compute
  ,sptreeTheory.lrnext_thm
  ,sptreeTheory.wf_def
  ,sptreeTheory.mk_BN_def
  ,sptreeTheory.mk_BS_def
  ,sptreeTheory.fromList_def
  ,sptreeTheory.size_def
  ,sptreeTheory.union_def
  ,sptreeTheory.inter_def
  ,sptreeTheory.domain_def
  ,sptreeTheory.foldi_def
  ,sptreeTheory.toListA_def
  ,sptreeTheory.toList_def
  ,sptreeTheory.mk_wf_def
  ] compset
  val () = computeLib.add_thms 
  [miscTheory.find_index_def
  ,miscTheory.LEAST_thm
  ,miscTheory.least_from_thm
  ] compset
  val () = add_datatype ``:'a spt`` compset
in
  ()
end

  val the_basic_compset = 
    let
      val c = wordsLib.words_compset ()
      val () = add_basic_compset c
    in
      c
    end

end


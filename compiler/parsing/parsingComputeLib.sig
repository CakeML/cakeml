signature parsingComputeLib =
sig

  include Abbrev
  val add_parsing_compset : computeLib.compset -> unit
    (* start with listLib.list_compset and add

          List.app (fn f => f cs) [
            combinLib.add_combin_compset,
            stringLib.add_string_compset,
            optionLib.OPTION_rws,
            pairLib.add_pair_compset,
            computeLib.extend_compset [
              computeLib.Tys [“:tokens$token”]
            ],
            computeLib.add_thms
              [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY],
            computeLib.add_thms [
              grammarTheory.ptree_list_loc_def,
              grammarTheory.ptree_loc_def,
              locationTheory.merge_list_locs_def,
              locationTheory.merge_locs_def,
              locationTheory.unknown_loc_def
            ],
            semanticsComputeLib.add_tokenUtils_compset,
            add_parsing_compset
          ]
    *)
  val parsing_compset : unit -> computeLib.compset

  val parse : term -> term -> string quotation -> term
  val parse_exp : string quotation -> term
  val parse_decl : string quotation -> term
  val parse_topdecs : string quotation -> term


end

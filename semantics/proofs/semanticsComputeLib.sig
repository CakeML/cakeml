signature semanticsComputeLib =
sig

val add_ast_compset : computeLib.compset -> unit
val add_namespace_compset : computeLib.compset -> unit
val add_lexer_fun_compset : computeLib.compset -> unit
  (* requires base of listLib.list_compset()
     and addition of:
       stringLib.add_string_compset cs;
       pairLib.add_pair_compset cs;
       optionLib.OPTION_rws cs;
       combinLib.add_combin_compset cs;
       computeLib.add_thms
         [pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] cs;
       numposrepLib.add_numposrep_compset cs;
       bitLib.add_bit_compset cs;
       ASCIInumbersLib.add_ASCIInumbers_compset cs;
       intReduce.add_int_compset cs;
  *)
val add_gram_compset : computeLib.compset -> unit
val add_tokenUtils_compset : computeLib.compset -> unit
val add_cmlPtreeConversion_compset : computeLib.compset -> unit
  (* requires base of listLib.list_compset()
     and addition of
       stringLib.add_string_compset cs;
       pairLib.add_pair_compset cs;
       optionLib.OPTION_rws cs;
       combinLib.add_combin_compset cs;
       computeLib.extend_compset [
         computeLib.Tys [“:(α,β,γ) grammar$parsetree”]
       ] cs;
       gramLib.add_gram_compset cs;
       add_tokenUtils_compset cs;
  *)

val add_semantics_compset : computeLib.compset -> unit

end

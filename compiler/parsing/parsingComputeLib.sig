signature parsingComputeLib =
sig

  val add_parsing_compset : computeLib.compset -> unit
  val parsing_compset : computeLib.compset

  val parse : term -> term -> string quotation -> term
  val parse_exp : string quotation -> term
  val parse_decl : string quotation -> term
  val parse_topdecs : string quotation -> term


end

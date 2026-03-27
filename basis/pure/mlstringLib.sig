signature mlstringLib = sig

  include Abbrev

  val smart_dest_mlstring_case : term -> term * (term * term) list * term

  val mlstring_case_conv : conv

  val add_mlstring_compset : computeLib.compset -> computeLib.compset
end

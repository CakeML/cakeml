signature mlvectorSyntax =
sig
  include Abbrev

  val mk_vector_type   : hol_type -> hol_type
  val dest_vector_type : hol_type -> hol_type
  val is_vector_type   : hol_type -> bool
end

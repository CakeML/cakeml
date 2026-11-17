signature runtime_checkLib = sig

  include Abbrev

  val shape_of_type : hol_type -> term
  val assert_check : term quotation list -> thm -> thm

end

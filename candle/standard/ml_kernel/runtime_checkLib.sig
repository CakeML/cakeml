signature runtime_checkLib = sig

  include Abbrev

  val check : term quotation list -> thm -> thm

end

signature cfAppLib = sig
  include Abbrev

  val app_of_Arrow_rule : Context.t -> hol_type -> thm -> thm
end

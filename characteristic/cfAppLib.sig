signature cfAppLib = sig
  include Abbrev

  val app_of_Arrow_rule : hol_type -> thm -> thm
end

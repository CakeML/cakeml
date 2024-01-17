signature cv_typeLib =
sig
  include Abbrev

  (* --- main entry points --- *)

  (* ask for from_to info (derives missing info automatically) *)
  val from_to_thm_for    : hol_type -> thm
  val from_term_for      : hol_type -> term
  val to_term_for        : hol_type -> term

  (* --- less useful entry points --- *)

  (* automatically define new from/to functions for a user-defined datatype *)
  val define_from_to     : hol_type -> thm * thm * thm list
  val rec_define_from_to : hol_type -> thm list

  (* define_from_to can raise this *)
  exception Missing_from_to of hol_type

end

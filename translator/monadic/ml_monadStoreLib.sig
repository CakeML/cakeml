(*
  The signature for ml_monadStoreLib
*)
signature ml_monadStoreLib =
sig
  include ml_translatorLib

  type monadic_translation_parameters = {
    store_pred_def : thm,
    refs_specs     : (thm * thm) list,
    rarrays_specs  : (thm * thm * thm * thm) list,
    farrays_specs  : (thm * thm * thm) list
  };

  type store_translation_result = {
      refs_init_values      : thm list,
      refs_locations        : thm list,
      rarrays_init_values   : thm list,
      farrays_init_values   : thm list,
      rarrays_locations     : thm list,
      farrays_locations     : thm list,
      store_pred_validity   : thm,
      store_pred_exists_thm : thm
    };

  val translate_dynamic_init_fixed_store  :
      (string * thm * thm) list ->
      (string * thm * thm * thm * thm * thm * thm) list ->
      (string * thm * thm * thm * thm * thm) list -> string ->
      hol_type -> thm -> thm option -> monadic_translation_parameters

   val translate_static_init_fixed_store :
       (string * thm * thm * thm) list ->
       (string * thm * thm * thm * thm * thm * thm * thm) list ->
       (string * (int * thm) * thm * thm * thm * thm * thm) list ->
       string -> hol_type -> thm -> (thm * thm) option -> term option ->
       monadic_translation_parameters * store_translation_result
end

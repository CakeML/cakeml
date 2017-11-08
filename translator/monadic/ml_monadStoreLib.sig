signature ml_monadStoreLib =
sig
    include ml_translatorLib

    type monadic_translation_parameters =
    {store_pred_def : thm,
     refs_specs : (thm * thm) list,
     arrays_specs : (thm * thm * thm * thm) list};

    type store_translation_result =
    {refs_init_values : thm list,
     refs_locations  : thm list,
     arrays_init_values : thm list,
     arrays_locations : thm list,
     store_pred_validity : thm,
     store_pred_exists_thm : thm};

  val translate_dynamic_init_fixed_store  : (string * thm * thm) list ->
       (string * thm * thm * thm * thm * thm * thm) list ->
       string -> hol_type -> thm -> thm option -> monadic_translation_parameters

   val translate_static_init_fixed_store :
       (string * thm * thm * thm) list ->
       (string * thm * thm * thm * thm * thm * thm * thm) list ->
       string -> hol_type -> thm -> (thm * thm) option ->
       monadic_translation_parameters * store_translation_result
end

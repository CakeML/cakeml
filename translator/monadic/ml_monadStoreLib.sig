signature ml_monadStoreLib =
sig
    type thm = Thm.thm
    type term = Term.term

    type store_translation_result =
    {init_values_thms : thm list,
     locations_thms  : thm list,
     store_pred_def : thm,
     store_pred_validity : thm,
     store_pred_exists_thm : thm,
     get_specs : thm list,
     set_specs : thm list};

   val mk_store_translation_result :
       thm list -> thm list -> thm -> thm -> thm -> thm list -> thm list -> store_translation_result

   val translate_fixed_store :
       (string * thm * thm * thm) list -> string -> term -> store_translation_result
end

signature ml_translatorLib =
sig

    include Abbrev

    (* main functionality *)

    val translate  : thm -> thm    (* e.g. try translate listTheory.MAP *)
    val hol2deep   : term -> thm   (* e.g. try hol2deep ``\x.x`` *)
    val hol2val    : term -> term  (* e.g. try hol2val ``5:num`` *)

    (* wrapper functions *)

    val mlDefine   : term quotation -> thm
    val mltDefine  : string -> term quotation -> tactic -> thm

    (* interface for teaching the translator about new types *)

    val add_type_inv   : term -> hol_type -> unit
    val get_type_inv   : hol_type -> term
    val store_eval_thm : thm -> thm
    val store_eq_thm   : thm -> thm
    val register_type  : hol_type -> unit
    val store_cert     : thm -> thm list -> thm -> thm
    val get_DeclAssum  : unit -> term

    val register_exn_type   : hol_type -> unit
    val full_name_of_type   : hol_type -> string
    val case_of             : hol_type -> thm
    val get_DeclAssumExists : unit -> thm
    val get_cenv_eq_thm     : unit -> thm
    val eq_lemmas           : unit -> thm list
    val clean_lookup_cons   : thm -> thm

    (* loading / storing state of translator *)

    val translation_extends   : string -> unit
    val reset_translation     : unit -> unit   (* bring back to initial state *)
    val finalise_translation  : unit -> unit   (* happens automatically at export *)
    val get_cert              : string -> thm * thm
    val get_decls             : unit -> term

    val translate_into_module       : string -> unit
    val finalise_module_translation : unit -> thm

    (* simplification of preconditions / sideconditions *)

    val update_precondition  : thm -> thm

    (* configuration *)

    val print_asts           : bool ref
    val use_full_type_names  : bool ref
    val add_preferred_thy    : string -> unit
    val find_def_for_const   : (term -> thm) ref

    (* internals, for ml_hol_kernel *)

    val lookup_cert              : term -> thm
    val match_rec_pattern        : term -> term * string * term
    val install_rec_pattern      : term -> string -> term
    val uninstall_rec_patterns   : unit -> unit
    val preprocess_def           : thm -> bool * thm list * thm option
    val get_unique_name          : string -> string
    val get_nchotomy_of          : hol_type -> thm
    val sat_hyp_lemma            : thm
    val print_fname              : string -> thm -> unit
    val last_fail                : term ref
    val check_inv                : string -> term -> thm -> thm
    val remove_primes            : thm -> thm
    val clean_assumptions        : thm -> thm
    val SIMP_EqualityType_ASSUMS : thm -> thm
    val FORCE_GEN                : term -> thm -> thm
    val rename_bound_vars_rule   : string -> thm -> thm
    val clean_uppercase          : string -> string
    exception UnableToTranslate of term

end

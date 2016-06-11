signature ml_translatorLib =
sig

    include Abbrev

    (* main functionality *)

    val translate  : thm -> thm    (* e.g. try translate listTheory.MAP *)
    val hol2deep   : term -> thm   (* e.g. try hol2deep ``\x.x`` *)
    val hol2val    : term -> term  (* e.g. try hol2val ``5:num`` *)

    val ml_prog_update : (ml_progLib.ml_prog_state ->
                          ml_progLib.ml_prog_state) -> unit

    (* wrapper functions *)

    val mlDefine   : term quotation -> thm
    val mltDefine  : string -> term quotation -> tactic -> thm

    (* interface for teaching the translator about new types *)

    val add_type_inv   : term -> hol_type -> unit
    val get_type_inv   : hol_type -> term

    val add_eval_thm   : thm -> thm
    val add_user_proved_v_thm : thm -> thm

    val store_eq_thm   : thm -> thm
    val register_type  : hol_type -> unit

    val register_exn_type   : hol_type -> unit
    val full_name_of_type   : hol_type -> string
    val case_of             : hol_type -> thm
    val eq_lemmas           : unit -> thm list

    (* loading / storing state of translator *)

    val translation_extends   : string -> unit
    val reset_translation     : unit -> unit   (* bring back to initial state *)
    val finalise_translation  : unit -> unit   (* happens automatically at export *)

    (* simplification of preconditions / sideconditions *)

    val update_precondition  : thm -> thm

    (* configuration *)

    val print_asts           : bool ref
    val use_full_type_names  : bool ref
    val add_preferred_thy    : string -> unit
    val find_def_for_const   : (term -> thm) ref

    (* internals, for ml_hol_kernel *)

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
    val prove_EvalPatRel         : term -> (term -> thm) -> thm
    val dest_pmatch_K_T          : term -> term * (term * term) list
    val dest_pmatch_row_K_T      : term -> term * term
    val is_pmatch                : term -> bool
    val to_pattern               : term -> term
    val pmatch_preprocess_conv   : term -> thm
    exception UnableToTranslate of term

end

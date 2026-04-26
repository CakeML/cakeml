signature ml_progLib =
sig

  include Abbrev

  datatype ml_prog_state = ML_code of (thm list) (* state const definitions *) *
                                      (thm list) (* env const definitions *) *
                                      (thm list) (* v const definitions *) *
                                      thm (* ML_code thm *);

  val init_state   : ml_prog_state

  val open_module  : string (* module name *) ->
                     ml_prog_state -> ml_prog_state

  val close_module : term option (* optional signature *) ->
                     ml_prog_state -> ml_prog_state

  (* names of (nested) opened modules, outermost first *)
  val get_open_modules : ml_prog_state -> string list

  (* use of local/in/end blocks, by calling these three functions in order *)
  val open_local_block    : ml_prog_state -> ml_prog_state
  val open_local_in_block : ml_prog_state -> ml_prog_state
  val close_local_block   : ml_prog_state -> ml_prog_state

  (* close all local blocks up to the module/global scope *)
  val close_local_blocks  : ml_prog_state -> ml_prog_state

  val add_Dtype    : term (* loc *) -> term (* tds *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dexn     : term (* loc *) -> term -> term (* Dexn args *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dtabbrev : term (* loc *) ->
                     term -> term -> term -> (* Dtabbrev args *)
                     ml_prog_state -> ml_prog_state

  val add_Dlet     : thm (* evaluate thm *) ->
                     string (* var name *) ->
                     ml_prog_state -> ml_prog_state

  val add_Denv     : thm (* declare_env thm *) ->
                     string (* var name *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dlet_Fun : term (* loc *) -> term -> term -> term (* terms of Dlet (Pvar _) (Fun _ _) *) ->
                     string (* v const name *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dlet_Var_Ref_Var : term -> term -> term -> string -> ml_prog_state -> ml_prog_state

  val add_Dlet_Var_Var : term -> term -> term -> ml_prog_state -> ml_prog_state

  val add_Dletrec  : term (* loc *) -> term (* funs *) ->
                     string list (* names of v consts *) ->
                     ml_prog_state -> ml_prog_state

  val add_dec      : term (* dec *) ->
                     (string -> string) (* pick name for v abbrev const *) ->
                     ml_prog_state -> ml_prog_state

  val add_prog     : term (* prog i.e. list of top *) ->
                     (string -> string) (* pick name for v abbrev const *) ->
                     ml_prog_state -> ml_prog_state

  val set_eval_state : term (* new eval_state *) -> ml_prog_state -> ml_prog_state

  val nsLookup_conv : conv

  (* New env_tree infrastructure.
     derive_nsLookup_tree produces  |- !k. nsLookup_all env = tree_lookup T
     and registers (env, T, equiv) in the internal map. Raises HOL_ERR if the
     def's shape is unsupported or the base env hasn't been registered. *)
  val derive_nsLookup_tree : thm -> thm

  (* Tree-backed lookup conv, fires on
       nsLookup_Short env.v k / env.c k / nsLookup_Mod1 env.v k / env.c k
     for env registered by derive_nsLookup_tree and concrete strlit key. *)
  val nsLookup_tree_conv : conv

  (* Test hook: check whether env_tree_map has an entry for env_const,
     triggering lazy-load from saved theorems if needed. *)
  val env_tree_has : term -> bool

  val remove_snocs : ml_prog_state -> ml_prog_state
  val clean_state  : ml_prog_state -> ml_prog_state

  val get_thm      : ml_prog_state -> thm (* ML_code thm *)
  val get_env      : ml_prog_state -> term (* env in ML_code thm *)
  val get_state    : ml_prog_state -> term (* state in ML_code thm *)
  val get_v_defs   : ml_prog_state -> thm list (* v abbrev defs *)

  val get_Decls_thm : ml_prog_state -> thm (* Decls thm at top level *)
  val get_prog      : ml_prog_state -> term (* program at top level *)

  val get_next_exn_stamp  : ml_prog_state -> int
  val get_next_type_stamp : ml_prog_state -> int

  val pack_ml_prog_state   : ml_prog_state -> ThyDataSexp.t
  val unpack_ml_prog_state : ThyDataSexp.t -> ml_prog_state

  val define_abbrev : bool -> string -> term -> thm

  val pick_name : string -> string

  (* Profiling: per-phase wall time for let_env_abbrev and nsLookup_conv. *)
  val print_let_env_profile : unit -> unit

  (* Debug-only accessors for live counters. *)
  val get_nslookup_conv_calls : unit -> int
  val get_nslookup_conv_time  : unit -> real
  val reset_nslookup_conv_counters : unit -> unit

  (* Runtime toggle: when true, nsLookup_conv uses the legacy alist
     (orig HEAD) path; when false (default), the new env_tree path. *)
  val use_alist_conv : bool ref
end

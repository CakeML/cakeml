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
                     thm list (* v const thms *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dlet_Fun : term (* loc *) -> term -> term -> term (* terms of Dlet (Pvar _) (Fun _ _) *) ->
                     string (* v const name *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dletrec  : term (* loc *) -> term (* funs *) ->
                     string list (* names of v consts *) ->
                     ml_prog_state -> ml_prog_state

  val add_dec      : term (* dec *) ->
                     (string -> string) (* pick name for v abbrev const *) ->
                     ml_prog_state -> ml_prog_state

  val add_prog     : term (* prog i.e. list of top *) ->
                     (string -> string) (* pick name for v abbrev const *) ->
                     ml_prog_state -> ml_prog_state

  val nsLookup_conv : conv
  val nsLookup_pf_conv : conv

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
end

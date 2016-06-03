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

  val add_Dtype    : term (* tds *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dexn     : term -> term (* Dexn args *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dtabbrev : term -> term -> term -> (* Dtabbrev args *)
                     ml_prog_state -> ml_prog_state

  val add_Dlet     : thm (* evaluate thm *) ->
                     string (* var name *) ->
                     thm list (* v const thms *) ->
                     ml_prog_state -> ml_prog_state

  val add_Dletrec  : term (* funs *) ->
                     string list (* names of v consts *) ->
                     ml_prog_state -> ml_prog_state

  val add_prog     : term (* prog i.e. list of top *) ->
                     (string -> string) (* pick name for v abbrev const *) ->
                     ml_prog_state -> ml_prog_state

  val remove_snocs : ml_prog_state -> ml_prog_state

  val get_thm      : ml_prog_state -> thm (* ML_code thm *)

end

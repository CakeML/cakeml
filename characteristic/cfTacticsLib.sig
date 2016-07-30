signature cfTacticsLib =
sig
  include Abbrev

  (* [xcf name prog_state] is usually the first tactic to call when
     proving a specification.

     It turns a goal corresponding to a specification of a function
     named [name] in [prog_state], which is of of the form [app ...],
     into a characteristic formula.
  *)
  val xcf : string -> ml_progLib.ml_prog_state -> tactic

  (* [xpull] must be called whenever the goal is a cf which
     precondition contains pure facts ([& H]); [xpull] then
     extracts them and put them in the context.
  *)
  val xpull : tactic

  (* [xsimpl] applies on goals containing heap implications
     [H ==>> Q], and tries to simplify them
  *)
  val xsimpl : tactic

  (* [xlet] applies on characteristic formulae for let, of the form
     [cf_let ...].

     It must be provided the post-condition for the expression bound
     to the value, and a name for the corresponding value.

     Example: [xlet `\v. & INT 3 v` `i`]
  *)
  val xlet : term quotation -> term quotation -> tactic

  (* [xlet_seq] applies on characteristic formulae for let that result
     from a sequence. Only the post-condition needs to be provided.
  *)
  val xlet_seq : term quotation -> tactic

  (* [xapp] and [xapp_spec] apply on characteristic fomulae for
     function application, of the form [cf_app ...].

     [xapp] tries to fetch a specification for the applied function
     from the currently loaded theories. [xapp_spec] allows to
     explicitly provide a specification for the applied function.
  *)
  val xapp : tactic
  val xapp_spec : thm -> tactic

  (* [xret] applies on characteristic formulae of the form
     [cf_lit ...], [cf_con ...], [cf_var ...].
   *)
  val xret : tactic

  (* [xlog] applies on characteristic formulae for logical operations
     (produced by [andalso] or [orelse] at source level), which are of
     the form [cf_log ...].
  *)
  val xlog : tactic

  (* [xif] applies on characteristic formulae for if..then..else, of
     the form [cf_if ...].

     It usually produces two subgoals, one for each branch.
  *)
  val xif : tactic

  (* [xmatch] applies to characteristic formulae for pattern matching,
     of the form [cf_match ...].

     [xmatch] is expected to be called after case analysis on the
     matched value has been performed in the logic, in order to
     simplify the goal and reduce it to the cf of the matching branch.
  *)
  val xmatch : tactic

  (* low level / debugging *)
  val xlocal : tactic
  val xapply : thm -> tactic
  val xapp_prepare_goal : tactic
  val reduce_tac : tactic

  val hide_environments : bool -> unit
end

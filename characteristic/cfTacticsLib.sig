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

  (* [xlet] applies on characteristic formulae for let and sequences,
     of the form [cf_let ...].

     It must be provided the post-condition for the expression bound
     to the value; the introduced name will be deduced from the
     variable of the lambda.

     Example: [xlet `\i. & INT 3 i`]
  *)
  val xlet : term quotation -> tactic

  (* [xfun] applies on characteristic formulae for function
     declaration, of the form [cf_fundecl ...] or
     [cf_fundecl_rec ...].

     It must be provided with a name for the closure corresponding to
     the function. It then adds to the context the most general
     specification for the new function, that will be used by later
     calls to [xapp].
  *)
  val xfun : term quotation -> tactic

  (* [xfun_spec] is a variant of [xfun] which allows providing
     explicitly a specification for the introduced function. This
     produces a subgoal for proving the asserted spec, knowing the
     most-general specification, as [xfun] would produce.

     This is mostly useful for recursive functions, where the general
     specification is generally not useful as-is.

     The first argument is a name for the introduced closure, and the
     second argument is the provided specification (of the form
     [app p f args H Q]).
  *)
  val xfun_spec : term quotation -> term quotation -> tactic

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

     [xlit], [xcon] and [xvar] are aliases of [xret].
   *)
  val xret : tactic
  val xlit : tactic
  val xcon : tactic
  val xvar : tactic

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

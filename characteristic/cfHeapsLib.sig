signature cfHeapsLib =
sig
  include Abbrev

  (* Prove an "easy" goal about sets, involving UNION, DISJOINT,... Useful
    after unfolding the definitions of heap predicates. *)
  val SPLIT_TAC : tactic


  (** Normalization of STAR *)

  (* Normalize modulo AC of STAR *)
  val rew_heap_AC : tactic

  (* Normalize using AC, but also pull exists, remove emp, etc. *)
  val rew_heap : tactic


  (** Making progress on goals of the form [SEP_IMP H1 H2].

      The main tactic one wants to use faced with such a goal is [hsimpl].

      It will normalize both heaps, extract pure formulæ ([cond]), extract and
      instantiate existential quantifications from H1 and H2, and remove
      subheaps present both in H1 and H2.

      [hsimpl] is defined using auxiliary tactics, that are also exported here,
      in case one wants to do some more fine grained manipulations.
   *)
  val hsimpl : tactic


  (** Auxiliary tactics *)

  (* [hpull]: extract pure facts and existential quantifications from the left
     heap (H1).

     For example:

      A ?- SEP_IMP (A * cond P) B
     =============================  hpull
        A ?- P ==> SEP_IMP A B

      SEP_IMP (SEP_EXISTS x. A x * B) C
     ===================================  hpull
        A ?- !x. SEP_IMP (A x * B) C
     
     [hpull] fails (raising HOL_ERR) if it cannot do anything on the goal.
   *)
  val hpull : tactic
                 
  (* [hsimpl_cancel]: on a goal of the form [SEP_IMP H1 H2], [hsimpl_cancel]
     tries to remove subheaps present both in H1 and H2. Moreover, if
     [one (loc, v)] is in H1 and [one (loc, v')] is in H2, [hsimpl_cancel] will
     remove both, and produce a subgoal [v = v'].

     For example:

      A ?- SEP_IMP (A * B * one (l, v)) (B * one (l, v'))
     =====================================================  hsimpl_cancel
          A ?- v = v'              A ?- SEP_IMP A emp

     [hsimpl_cancel] fails (raising HOL_ERR) if it cannot do anything on the goal.
   *)
  val hsimpl_cancel : tactic

  (* [hsimpl_steps]: extract pure facts and existential quantifications from the
     right heap (H2).

     For example:

      A ?- SEP_IMP A (B * cond P)
     =============================  hsimpl_steps
         A ?- P /\ SEP_IMP A B
   *)
  val hsimpl_steps : tactic
end

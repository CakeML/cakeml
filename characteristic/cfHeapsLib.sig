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

  (* hpull: extract pure facts and existential quantifications from the left
     heap (H1).

     For example:

      A ?- SEP_IMP (A * cond P) B
     =============================  hpull
          P ==> SEP_IMP A B

      SEP_IMP (SEP_EXISTS x. A x * B) C
     ===================================  hpull
           !x. SEP_IMP (A x * B) C
     
     hpull fails (raises an exception) if it cannot do anything on the goal.
   *)
  val hpull : tactic
                 
  (* hsimpl_cancel:  *)
  val 

end

(*
  A small tutorial on how to do proofs in CF using the tools provided
  by CakeML's support for CF reasoning.
*)

(* Perform the same opens as in cf_examplesScript.sml

   - ml_translatorTheory for the various predicates relating
     deep-embedded values to values of the logic, predicates that we
     will also use in specifications;
   - cfTacticsBaseLib and cfTacticsLib contain the automation to deal
     with characteristic formulae, so we open them aswell.
*)
open preamble
open ml_translatorTheory cfTacticsBaseLib cfTacticsLib
local open ml_progLib basisProgTheory in end

val _ = new_theory "cf_tutorial";

(* We use translator/ml_progLib for managing the state resulting from
   the evaluation of several toplevel declarations.

   Let's first fetch the state (of type ml_progLib.ml_prog_state)
   corresponding to the base definitions (the ones in
   basis/basisProgScript.sml). It is defined in
   basisProgTheory, and comes with specifications for the
   functions it defines.
*)
val basis_st = ml_translatorLib.get_ml_prog_state();

(* Then, write the code for the programs we want to specify.

   We define first a length function on lists, then the fromList
   function we want to specify (it takes a list of bytes, and returns
   a new bytearray containing those bytes).
*)
val bytearray_fromlist = process_topdecs
  `fun length l =
     case l of
         [] => 0
       | x::xs => (length xs) + 1

   fun fromList ls =
     let val a = Word8Array.array (length ls) (Word8.fromInt 0)
         fun f ls i =
           case ls of
               [] => a
             | h::t => (Word8Array.update a i h; f t (i+1))
     in f ls 0 end`

(* Now add these definitions to the basis ml_prog_state.
*)
val st = ml_progLib.add_prog bytearray_fromlist ml_progLib.pick_name basis_st

(* We can start proving a specification for length.

   The tactic that handles function application in characteristic
   formulae is able to fetch specifications from the assumptions, and
   from the exported theorems of the current theories.
   As we want to use length in fromList, we store its specification.
*)
Theorem list_length_spec:

(* Toplevel specifications are of the form:
   !x1..xn argv1.. argvm.
     facts_about_xi_argvj x1 .. xn .. argv1 .. argvm ==>
     app (p:'ffi ffi_proj) ^(fetch_v "name" st) [argv1, argv2,...]
       precondition postcondition

   where:

   - [name] is the name of the function in the toplevel declaration we
     added to the ml_prog_state;

   - [st] is the ml_prog_state containing the function;

   - [argv1, ..., argvm] are the arguments of the function, as values
     of the deep embedding;

   - [facts_about_xi_argvj] usually relate the argvi to values of the
     logic, using the predicates defined in ml_translatorTheory,
     and/or contain any necessary logical preconditions;

   - [precondition] is a heap predicate (of type [hprop]), and describe
     the memory heap before the execution of the function.
     The syntax for heap predicates includes:
     - [emp]: the empty heap
     - [H1 * H2]: separating conjunction (H1, H2: hprop)
     - [& P]: a pure fact (P: bool)
     - [H1 ==>> H2]: heap implication (H1, H2: hprop)
     - [REF r v]: a reference cell
     - [ARRAY r lv]: an array

     NB: it is always better to put pure preconditions as logical
     preconditions (in [facts_about_xi_argvj]) than in the
     precondition heap.

   - [postcondition] describes the state of the heap after the
     execution of the function.

     As the function may either return, producing a value, or raise an
     exception, several helper functions are provided for writing
     post-conditions:

     - [POSTv v. Q] is a post-condition that asserts that the function
       will always reduce to a value, here bound to [v], and that the
       heap predicate [Q] (of type [hprop]) must be satisfied;
     - [POSTe v. Q] is similar, but for functions that always raise an
       exception;
     - [POST Qv Qe] is the general case: [Qv] of type [v -> hprop] is
       the post-condition for when the function returns a value, and
       [Qe] (also of type [v -> hprop]) is the post-condition for when
       the function raises an exception.
*)
   !a l lv.
     LIST_TYPE a l lv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "length" st) [lv]
       emp (POSTv v. & NUM (LENGTH l) v)

Proof
  (* Let's reason by induction on [l].
  *)
  Induct_on `l`
  THEN1 ((** Base case *)
    (* The first tactic to call when proving a specification is xcf,
       which turns an [app...] goal into a goal about the
       characteristic formula of the function body.
    *)
    xcf "length" st \\ fs [LIST_TYPE_def] \\

    (* Now, the general method is to look at the head constructor, and
       call the corresponding xtactic. Here, we have a [cf_match...]
       goal, which can be simplified as we know the match case we're
       in, so we call [xmatch], which does exactly that.
    *)
    xmatch \\

    (* We get a [cf_lit...] goal, handled by [xlit]. [xlit] is
       actually an alias for [xret], which also takes care of
       [cf_con...] and [cf_var...] goals.
    *)
    xlit \\

    (* We finally get a goal containing heap implications. These goals
       are handled by [xsimpl]. As our goal is quite simple, [xsimpl]
       is able to finish the proof.
    *)
    xsimpl
  )
  THEN1 ((** Induction *)
    xcf "length" st \\ fs [LIST_TYPE_def] \\
    rename1 `a x xv` \\ rename1 `LIST_TYPE a xs xvs` \\
    xmatch \\

    (* [cf_let...] goal: the corresponding tactic is [xlet].

       As of now, [xlet] has one major limitation: the post-condition
       for computing the expression that is bound must be provided
       explicitely beforehand.

       As it is a post-condition, it must be of type [v -> hprop],
       where the input value corresponds to what the bound expression
       reduces.

       We get two subgoals, one for proving that this intermediate
       post-condition holds, and one for the rest of the proof.
    *)
    xlet `POSTv xs_len. & NUM (LENGTH xs) xs_len`
    THEN1 (

      (* [cf_app...] goal: we use [xapp].

         This goal corresponds to a function application. Therefore,
         [xapp] needs to fetch a specification for the applied
         function. Here, one can be found in the assumptions: it is
         the induction hypothesis.
      *)
      xapp \\ metis_tac []
    ) \\

    (* In that case, [xapp] fetches the specification from the
       exported theorems of currently loaded theories: more precisely,
       the specification for "op +" proven in cf_initialProgramTheory
    *)
    xapp \\ xsimpl \\ fs [NUM_def] \\ asm_exists_tac \\ fs [] \\

    (* This is a bit tedious, I don't know if it's possible to have
       something better
    *)
    fs [INT_def] \\ intLib.ARITH_TAC
    (* RK suggests one alternative:
    fs [ADD1,integerTheory.INT_ADD]
    *)
  )
QED


(* Now, the specification of fromList.
*)
val bytearray_fromlist_spec = Q.prove (
  `!l lv.
     LIST_TYPE WORD l lv ==>
     app (p:'ffi ffi_proj) ^(fetch_v "fromList" st) [lv]
       emp (POSTv av. W8ARRAY av l)`,
  xcf "fromList" st \\
  xlet `POSTv w8z. & WORD (n2w 0: word8) w8z` THEN1 (xapp \\ fs []) \\
  xlet `POSTv len_v. & NUM (LENGTH l) len_v` THEN1 (xapp \\ metis_tac []) \\
  xlet `POSTv av. W8ARRAY av (REPLICATE (LENGTH l) 0w)`
    THEN1 (xapp \\ fs []) \\

  (* [cf_fun] and [cf_fun_rec] goals are handled by [xfun] and
     [xfun_spec].

     [xfun] only needs a new name for the function, and adds to the
     context the most general specification for it. However, for a
     recursive function, this specification is generally not super
     useful as-is.

     Because of that, we use [xfun_spec], to which we can provide
     explicitely a specification for the function, that we prove by
     induction using the most general specification.

     This specification looks like the toplevel specifications, except
     that we do not need to use [fetch_v] to query the identifier of
     the function, and can simply used the name provided to
     [xfun_spec].
  *)
  xfun_spec `f`
    `!ls lvs i iv l_pre rest.
       NUM i iv /\ LIST_TYPE WORD ls lvs /\
       LENGTH rest = LENGTH ls /\ i = LENGTH l_pre
        ==>
       app p f [lvs; iv]
         (W8ARRAY av (l_pre ++ rest))
         (POSTv ret. & (ret = av) * W8ARRAY av (l_pre ++ ls))`
  THEN1 (
    (* We get the specification to prove as a first subgoal
    *)
    Induct_on `ls` \\ fs [LIST_TYPE_def, LENGTH_NIL] \\ rpt strip_tac
    THEN1 (xapp \\ xmatch \\ xret \\ xsimpl)
    THEN1 (
      (* Now this is a bit awkward: we have two specifications for [f]
         in the assumptions: the most general one, and the induction
         hypothesis.

         In that case we can use [xapp_spec], a variant of [xapp]
         where the specification to use is provided explicitely.

         We first use the general specification to do some progress,
         before using the induction hypothesis.
      *)
      fs [] \\ last_assum xapp_spec \\ xmatch \\ fs [LENGTH_CONS] \\
      rename1 `rest = rest_h :: rest_t` \\ rw [] \\

      (* Sequences are encoded as lets, so we can just use [xlet] here *)
      xlet `POSTv _. W8ARRAY av (l_pre ++ h :: rest_t)` THEN1 (
        xapp \\ xsimpl \\ fs [UNIT_TYPE_def] \\ instantiate \\
        fs [lupdate_append]
      ) \\
      xlet `POSTv ippv. & NUM (LENGTH l_pre + 1) ippv * W8ARRAY av (l_pre ++ h::rest_t)`
      THEN1 (
        xapp \\ xsimpl \\ fs [NUM_def] \\ instantiate \\
        (* tedious? *) fs [INT_def] \\ intLib.ARITH_TAC
      ) \\
      once_rewrite_tac [
        Q.prove(`l_pre ++ h::ls = (l_pre ++ [h]) ++ ls`, fs [])
      ] \\

      (* Finally use the induction hypothesis (by default [xapp] uses
         the first assumption that can is a valid specification).
      *)
      xapp \\ fs []
    )
  ) \\
  xapp \\ fs [] \\ xsimpl \\
  fs[LENGTH_NIL_SYM,LENGTH_REPLICATE]
  (* Done! *)
)

(* Some more documentation can be found:
   - in cfTacticsLib.sig, for documentation about the tactics to deal
     with characteristic formulae;
   - through examples, looking in cf_examplesScript.sml
*)

val _ = export_theory();

(*

An example of a queue data structure implemented using CakeML arrays, verified
using CF.

*)

open  preamble ml_progLib ioProgLib ml_translatorLib
	       cfTacticsLib basisFunctionsLib ml_translatorTheory
	       cfLetAutoLib
	       (* AssumSimpLib IntroRewriteLib *)

val _ = new_theory "queueProg";

val _ = translation_extends"ioProg";

val queue_decls = process_topdecs
    `fun empty_queue u = ref (Array.arrayEmpty (), 0)

    fun push q e =
    	case !q of (a,i) =>
      let val l = Array.length a in
        if i >= l then
          let val a' = Array.array (2*l+1) e in
            (Array.copy a a' 0;
             q := (a', i+1))
          end
      	else
          (Array.update a i e;
           q := (a,i+1))
      end

    exception EmptyQueue

    fun pop q =
    	case !q of (a,i) =>
      	if i = 0 then raise EmptyQueue
      	else let val x = Array.sub a (i-1) in (q := (a, i-1); x) end`;

val _ = append_prog queue_decls;

val EmptyQueue_exn_def = Define`
  EmptyQueue_exn v = (v = Conv (SOME ("EmptyQueue", TypeExn (Short "EmptyQueue"))) [])`;

(* Heap predicate for queues:
   QUEUE A vs qv means qv is a reference to a queue of
   elements vs, with A the refinement invariant satsfied by the elements of the queue *)
val QUEUE_def  = Define `
  QUEUE A vs qv =
  SEP_EXISTS av iv vvs junk.
    REF qv (Conv NONE [av;iv]) *
    & NUM (LENGTH vs) iv *
    ARRAY av (vvs ++ junk) *
    & LIST_REL A vs vvs`;

(* Some simple auto tactics *)
val xsimpl_tac = rpt(FIRST [xcon, (CHANGED_TAC xsimpl), xif, xmatch, xapp]);
val xs_auto_tac = rpt (FIRST [xcon, (CHANGED_TAC xsimpl), xif, xmatch, xapp, xlet_auto]);

val st = get_ml_prog_state ();

val empty_queue_spec = Q.store_thm ("empty_queue_spec",
    `!uv. app (p:'ffi ffi_proj) ^(fetch_v "empty_queue" st) [uv]
          emp (POSTv qv. QUEUE A [] qv)`,
    xcf "empty_queue" st \\
    xlet `POSTv v. &UNIT_TYPE () v` THEN1(xcon \\ xsimpl) \\
    xlet `POSTv av. ARRAY av []` THEN1(xapp \\ fs[]) \\
    xlet `POSTv pv. SEP_EXISTS av iv.
      &(pv = Conv NONE [av; iv]) * ARRAY av [] * &NUM 0 iv`
    THEN1(xcon \\ xsimpl) \\
    xapp \\ xsimpl \\ simp[QUEUE_def] \\ xsimpl
);

val empty_queue_spec = Q.store_thm ("empty_queue_spec",
    `!uv. app (p:'ffi ffi_proj) ^(fetch_v "empty_queue" st) [uv]
          emp (POSTv qv. QUEUE A [] qv)`,
    xcf "empty_queue" st >> simp[QUEUE_def] >> xs_auto_tac
);

val push_spec = Q.store_thm ("push_spec",
    `!qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (QUEUE A vs qv * & A x xv)
	  (POSTv uv. QUEUE A (vs ++ [x]) qv)`,
    xcf "push" st >>
    simp[QUEUE_def] >>
    xpull >>
    xlet_auto >-(xsimpl)>>
    xmatch >> rw[]
    >-(
	xlet_auto >-(xsimpl) >>
	xlet_auto >-(xsimpl) >>
	xif
	>-(
	    xlet_auto >-(xsimpl) >>
	    xlet_auto >-(xsimpl) >>
	    xlet_auto >-(xsimpl) >>
	    xlet_auto >-(xsimpl >> fs[REPLICATE, REPLICATE_APPEND_DECOMPOSE_SYM, LENGTH_REPLICATE]) >>	    
	    xlet_auto >-(xsimpl) >>
	    xlet_auto >-(xcon >> xsimpl) >>
	    xapp >>
	    xsimpl >>
	    fs[UNIT_TYPE_def] >>
	    (* Should be partially automatized *)
	    qexists_tac `vvs ++ [xv]` >>
            `LENGTH junk = 0` by rw[]
	    >-(
                `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
	        bossLib.DECIDE_TAC
	    ) >>
	    fs[LENGTH_NIL] >>
	    fs[REPLICATE, REPLICATE_PLUS_ONE] >>
	    fs refin_inv_rewrite_thms
	    (*---------------------------------*)
	) >>
	xlet_auto >-(xsimpl) >>
	xlet_auto >-(xsimpl) >>
	xlet_auto >-(xcon >> xsimpl) >>
	xapp >>
	xsimpl >>
	(* Should be partially automatized *)
	fs[UNIT_TYPE_def] >>
	qexists_tac `vvs ++ [xv]` >>
	qexists_tac `TL junk` >>
	fs refin_inv_rewrite_thms >>
        `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
	Cases_on `junk:v list` >-(fs[LENGTH_NIL]) >>
        `vvs++[h]++t = vvs++h::t` by rw[] >>
	POP_ASSUM (fn x => fs[x, LUPDATE_LENGTH])
    ) >>
    computeLib.EVAL_TAC);

val push_spec = Q.store_thm ("push_spec",
    `!qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (QUEUE A vs qv * & A x xv)
	  (POSTv uv. QUEUE A (vs ++ [x]) qv)`,
    xcf "push" st >>
    simp[QUEUE_def] >>
    xpull >>
    xs_auto_tac >>
    rw[]
    >-(
	xs_auto_tac
	(* 3 subgoals *)
	>-(fs[REPLICATE, REPLICATE_APPEND_DECOMPOSE_SYM, LENGTH_REPLICATE])
	>-(
	    fs[UNIT_TYPE_def] >>
	    qexists_tac `vvs ++ [xv]` >>
            `LENGTH junk = 0` by rw[]
	    >-(
                `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
	        bossLib.DECIDE_TAC
	    ) >>
	    fs[LENGTH_NIL] >>
	    fs[REPLICATE, REPLICATE_PLUS_ONE] >>
	    fs refin_inv_rewrite_thms
	) >>
	fs[UNIT_TYPE_def] >>
	qexists_tac `vvs ++ [xv]` >>
	qexists_tac `TL junk` >>
	fs refin_inv_rewrite_thms >>
        `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
	Cases_on `junk:v list` >-(fs[LENGTH_NIL]) >>
        `vvs++[h]++t = vvs++h::t` by rw[] >>
	POP_ASSUM (fn x => fs[x, LUPDATE_LENGTH])
    ) >>
    computeLib.EVAL_TAC);

val eq_num_v_thm =
  mlbasicsProgTheory.eq_v_thm
  |> DISCH_ALL
  |> C MATCH_MP (EqualityType_NUM_BOOL |> CONJUNCT1);

(*val pop_spec = Q.store_thm("pop_spec",
  `!qv.
   EqualityType A ==>
   app (p:'ffi ffi_proj) ^(fetch_v "pop" st) [qv]
   (QUEUE A vs qv)
   (POST (\v. &(not(NULL vs) /\ A (LAST vs) v) * QUEUE A (FRONT vs) qv)
	 (\e. &(NULL vs /\ EmptyQueue_exn e) * QUEUE A vs qv))`
   xcf "pop" st >>
   simp[QUEUE_def] >>
   xpull >>

   xlet_auto >-(xsimpl)>>
   xmatch >>
   rw[]
   >-(
      xlet_auto >-(xsimpl)>>
      xlet_auto >-(xsimpl) >>
      xif
      >-(
	  xlet_auto >-(xcon >> xsimpl) >>
	  xraise >>
	  xsimpl >>
	  fs[EmptyQueue_exn_def] >>
	  rw[] >>
	  irule FALSITY >>
	  fs[computeLib.EVAL_CONV ``not T``]
      ) >>
      xlet_auto >-(xsimpl) >>
      xlet_auto
      >-(
	  xsimpl >>
          `vvs <> []` by metis_tac[LIST_REL_LENGTH, LENGTH_NIL] >>
          `LENGTH vs <> 0 /\ LENGTH vvs <> 0` by metis_tac[LENGTH_NIL] >>
	  `LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>
	  bossLib.DECIDE_TAC
      ) >>
      xlet_auto >-(xsimpl) >>
      xlet_auto >-(xcon >> xsimpl) >>
      xlet_auto >-(xsimpl) >> *)

val _ = export_theory ()

(*

An example of a queue data structure implemented using CakeML arrays, verified
using CF.

*)

open  preamble ml_progLib ml_translatorLib
      cfTacticsLib basisFunctionsLib ml_translatorTheory

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
   elements vs which satisfy A *)
val QUEUE_def  = Define `
  QUEUE A vs qv =
  SEP_EXISTS av iv vvs junk.
    REF qv (Conv NONE [av;iv]) *
    & NUM (LENGTH vs) iv *
    ARRAY av (vvs ++ junk) *
    & LIST_REL A vs vvs`;

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

val push_spec = Q.store_thm ("push_spec",
    `!qv xv vs x. app (p:'ffi ffi_proj) ^(fetch_v "push" st) [qv; xv]
          (QUEUE A vs qv * & A x xv)
	  (POSTv uv. QUEUE A (vs ++ [x]) qv)`,
    xcf "push" st >>
    simp[QUEUE_def] >> xpull >>
    xlet `POSTv qr. & (qr = (Conv NONE [av; iv])) * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
    >- (xapp >> xsimpl) >>
    xmatch >> xlet `POSTv v. &NUM (LENGTH (vvs ++ junk)) v * qv ~~> Conv NONE [av; iv]  * ARRAY av (vvs ++ junk)`
    >- (xapp >> xsimpl)
    >> xlet `POSTv cb. &BOOL ((LENGTH vs) >= (LENGTH junk + LENGTH vvs)) cb * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
    >- (xapp >> xsimpl >> fs[NUM_def] >> instantiate >> rw[BOOL_def] >> intLib.COOPER_TAC)
    >> xif
    >- (
       imp_res_tac LIST_REL_LENGTH >> fs[]
       >> `LENGTH junk = 0` by decide_tac >>
       xlet `POSTv nlv. & NUM (2* (LENGTH vs)) nlv * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >- (xapp >> xsimpl >> fs[NUM_def] >> instantiate) >>
       xlet `POSTv nlv. & NUM (2* (LENGTH vs) + 1) nlv * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >- (xapp >> xsimpl >> fs[NUM_def] >> instantiate >> fs[integerTheory.INT_ADD]) >>
       xlet `POSTv nav. ARRAY nav (REPLICATE (2 * LENGTH vvs + 1) xv) * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >-(xapp >> xsimpl >> instantiate) >>
       xlet `POSTv uv. ARRAY nav (vvs ++ (REPLICATE (LENGTH vvs + 1) xv)) * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >-(
	  xapp >> xsimpl >> fs[LENGTH_NIL, LENGTH_NIL_SYM] >>
	  `2 * LENGTH vvs = LENGTH vvs + LENGTH vvs` by simp[] >>
	  pop_assum SUBST1_TAC >>
	  fs[GSYM REPLICATE_APPEND] >> fs[LENGTH_REPLICATE]
	  ) >>
       xlet `POSTv niv. &NUM ((LENGTH vvs)+1) niv * ARRAY nav (vvs ++ REPLICATE (LENGTH vvs + 1) xv) * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
       >-(
		xapp >> xsimpl >> fs[NUM_def] >> instantiate >> fs[integerTheory.INT_ADD]
	) >>
	xlet `POSTv ftv. ARRAY nav (vvs ++ REPLICATE (LENGTH vvs + 1) xv) * &(ftv = (Conv NONE [nav;niv])) *  qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ junk)`
	>-(
		xcon >> xsimpl
	) >>
	xapp >> xsimpl >> fs[NUM_def] >>
	rpt strip_tac >>
	qexists_tac `vvs ++ [xv]` >>
	fs[LIST_REL_def] >>
	qexists_tac `REPLICATE (LENGTH vvs) xv` >>
	`LENGTH vvs + 1 = (SUC (LENGTH vvs))`by intLib.ARITH_TAC >>
	pop_assum SUBST1_TAC >>
	fs[REPLICATE]
	) >>
	xlet `POSTv uv. SEP_EXISTS junk'. qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ [xv] ++ junk')`
	>-(
		xapp >> xsimpl >> instantiate >> rpt strip_tac >>
		`(LENGTH junk) > 0` by rw[]
		>-(`LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >>intLib.ARITH_TAC) >>
		Cases_on `junk`
		>-(irule FALSITY >> fs[LENGTH]) >>
		qexists_tac `t` >>
		`LENGTH vs = LENGTH vvs` by metis_tac[LIST_REL_LENGTH] >> pop_assum SUBST1_TAC >>
		rw[lupdate_append2]
	) >>
	xlet `POSTv niv. &NUM (LENGTH vs + 1) niv * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ [xv] ++ junk')`
	>-(
		xapp >> xsimpl >> fs[NUM_def] >> instantiate >> fs[integerTheory.INT_ADD]
	) >>
	xlet `POSTv np. &(np = Conv NONE [av; niv]) * qv ~~> Conv NONE [av; iv] * ARRAY av (vvs ++ [xv] ++ junk')`
	>-(
		xcon >> xsimpl
	) >>
	xapp >> xsimpl >> rpt strip_tac >>
	qexists_tac `vvs ++ [xv]` >> qexists_tac `junk'` >>
	fs[APPEND]
);

val eq_num_v_thm =
  mlbasicsProgTheory.eq_v_thm
  |> DISCH_ALL
  |> C MATCH_MP (EqualityType_NUM_BOOL |> CONJUNCT1);

val pop_spec = Q.store_thm("pop_spec",
  `∀qv.
   app (p:'ffi ffi_proj) ^(fetch_v "pop" st) [qv]
     (QUEUE A vs qv)
     (POST (λv. &(¬NULL vs ∧ A (LAST vs) v) * QUEUE A (FRONT vs) qv)
           (λe. &(NULL vs ∧ EmptyQueue_exn e) * QUEUE A vs qv))`,
  xcf "pop" st \\
  simp[QUEUE_def] >> xpull >>
  qmatch_abbrev_tac`_ _ frame _` \\
  xlet `POSTv qr. & (qr = (Conv NONE [av; iv])) * frame`
  >- ( xapp \\ simp[Abbr`frame`] \\ xsimpl ) \\
  xmatch \\
  xlet `POSTv bv. &(BOOL (LENGTH vs = 0) bv) * frame`
  >- (
    xapp_spec eq_num_v_thm \\
    xsimpl \\
    instantiate ) \\
  xif
  >- (
    xlet `POSTv ev. &EmptyQueue_exn ev * frame`
    >- (
      xcon
      \\ xsimpl
      \\ simp[EmptyQueue_exn_def] ) \\
    xraise \\
    xsimpl \\
    fs[LENGTH_NIL,NULL_EQ,Abbr`frame`] \\
    xsimpl) \\
  xlet `POSTv niv. &(NUM (LENGTH vs - 1) niv) * frame`
  >- (
    xapp
    \\ xsimpl
    \\ fs[NUM_def]
    \\ instantiate
    \\ simp[integerTheory.INT_SUB] )
  \\ xlet `POSTv xv. &(A (LAST vs) xv) * frame`
  >- (
    xapp
    \\ xsimpl
    \\ simp[Abbr`frame`]
    \\ xsimpl
    \\ instantiate
    \\ imp_res_tac LIST_REL_LENGTH
    \\ simp[]
    \\ `vs ≠ [] ∧ vvs ≠ []` by (rpt strip_tac \\ fs[])
    \\ `vvs = FRONT vvs ++ [LAST vvs]` by simp[APPEND_FRONT_LAST]
    \\ pop_assum SUBST1_TAC
    \\ simp[EL_APPEND1,EL_APPEND2]
    \\ imp_res_tac list_rel_lastn
    \\ pop_assum(qspec_then`1`mp_tac)
    \\ simp[LASTN_1] ) \\
  xlet `POSTv niv2. &(NUM (LENGTH vs - 1) niv2) * frame`
  >- (
    xapp
    \\ xsimpl
    \\ fs[NUM_def]
    \\ instantiate
    \\ simp[integerTheory.INT_SUB] ) \\
  xlet `POSTv pv. &(pv = Conv NONE [av; niv2]) * frame`
  >- ( xcon \\ xsimpl ) \\
  xlet `POSTv uv. qv ~~> pv * ARRAY av (vvs ++ junk)`
  >- (
    xapp
    \\ simp[Abbr`frame`]
    \\ xsimpl ) \\
  xvar
  >- (
    xsimpl
    \\ fs[NULL_EQ,LENGTH_NIL,LENGTH_FRONT,PRE_SUB1]
    \\ qexists_tac`FRONT vvs`
    \\ qexists_tac`[LAST vvs] ++ junk`
    \\ `vvs ≠ []` by (rpt strip_tac \\ fs[])
    \\ simp[APPEND_FRONT_LAST]
    \\ fs[LIST_REL_FRONT_LAST] )
  \\ fs[NULL_EQ,LENGTH_NIL]
  \\ xsimpl);

val _ = export_theory ()

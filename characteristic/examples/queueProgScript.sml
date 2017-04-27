open  preamble ml_progLib ioProgLib ml_translatorLib
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
	   (Array.update a i e; q := (a,i+1))
	end

    exception EmptyQueue
  
    fun pop q =
    	case !q of (a,i) =>
      	if i = 0 then raise EmptyQueue
      	else let val e = Array.sub a (i-1) in (q := (a, i-1); e) end`
	
val _ = append_prog queue_decls

val QUEUE_def  = Define `
  QUEUE A vs qv =
  SEP_EXISTS av iv vvs junk. REF qv (Conv NONE [av;iv]) * & NUM (LENGTH vs) iv * ARRAY av (vvs ++ junk) * & LIST_REL A vs vvs`

val st = get_ml_prog_state ()

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
)


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
)







(*DB.find "APPEND" |> DB.find_in "LIST" 
dest cons
overload_info_for"++"
DB.find "LUPDATE" |> DB.find_in "APPEND"
DB.find "REPLICATE"
DB.find "LIST_REL" |> DB.find_in "length"

REPLICATE
	  

DB.find "REPLICATE" |> DB.find_in "LENGTH"
      DB.find "INT_ADD"*)

val _ = export_theory ()
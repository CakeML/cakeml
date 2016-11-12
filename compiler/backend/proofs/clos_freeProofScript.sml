open preamble
     db_varsTheory clos_freeTheory
     closPropsTheory;

val _ = new_theory"clos_freeProof";

val IMP_EXISTS_IFF = Q.prove(
  `!xs. (!x. MEM x xs ==> (P x <=> Q x)) ==>
         (EXISTS P xs <=> EXISTS Q xs)`,
  Induct \\ fs []);

val free_thm = Q.store_thm("free_thm",
  `!xs.
     let (ys,l) = free xs in
       !n. (fv n ys = has_var n l) /\
           (fv n xs = has_var n l)`,
  recInduct free_ind \\ REPEAT STRIP_TAC \\ fs [free_def,LET_DEF]
  \\ TRY (fs [has_var_def,fv_def,fv1_thm] \\ NO_TAC)
  THEN1 (* cons *)
   (`?y1 l1. free [x] = ([y1],l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
    \\ `?y2 l2. free (y::xs) = (y2,l2)` by METIS_TAC [PAIR] \\ fs []
    \\ IMP_RES_TAC evaluate_const \\ rfs [] \\ RES_TAC
    \\ IMP_RES_TAC free_LENGTH
    \\ Cases_on `y2` \\ fs [has_var_def,fv_def,fv1_thm])
  \\ `?y1 l1. free (MAP SND fns) = (y1,l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y1 l1. free [x1] = ([y1],l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y1 l1. free xs = (y1,l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y1 l1. free xs2 = (y1,l1)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y2 l2. free [x2] = ([y2],l2)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ `?y3 l3. free [x3] = ([y3],l3)` by METIS_TAC [PAIR,free_SING] \\ fs []
  \\ rfs [] \\ RES_TAC \\ IMP_RES_TAC free_LENGTH \\ fs []
  \\ fs [has_var_def,fv_def,fv1_thm,MEM_vars_to_list]
  \\ fs [AC ADD_ASSOC ADD_COMM, MAP_ZIP]
  \\ fs [MAP_MAP_o,o_DEF]
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) \\ fs []
  \\ STRIP_TAC \\ Cases_on `has_var (n + LENGTH fns) l1'` \\ fs []
  \\ fs [EXISTS_MAP]
  \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC IMP_EXISTS_IFF \\ fs [FORALL_PROD]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ Cases_on `free [p_2]` \\ fs []
  \\ IMP_RES_TAC free_SING \\ fs [])
  |> SPEC_ALL;

val _ = export_theory()

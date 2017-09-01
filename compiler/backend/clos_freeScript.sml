open preamble db_varsTheory closLangTheory;

(* annotate Fn and Letrec with free variables, no semantic change *)

val _ = new_theory"clos_free";

val free_def = tDefine "free" `
  (free [] = ([],Empty)) /\
  (free ((x:closLang$exp)::y::xs) =
     let (c1,l1) = free [x] in
     let (c2,l2) = free (y::xs) in
       (c1 ++ c2,mk_Union l1 l2)) /\
  (free [Var t v] = ([Var t v], Var v)) /\
  (free [If t x1 x2 x3] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free [x2] in
     let (c3,l3) = free [x3] in
       ([If t (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union l2 l3))) /\
  (free [Let t xs x2] =
     let (c1,l1) = free xs in
     let (c2,l2) = free [x2] in
       ([Let t c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs) l2))) /\
  (free [Raise t x1] =
     let (c1,l1) = free [x1] in
       ([Raise t (HD c1)],l1)) /\
  (free [Tick t x1] =
     let (c1,l1) = free [x1] in
       ([Tick t (HD c1)],l1)) /\
  (free [Op t op xs] =
     let (c1,l1) = free xs in
       ([Op t op c1],l1)) /\
  (free [App t loc_opt x1 xs2] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free xs2 in
       ([App t loc_opt (HD c1) c2],mk_Union l1 l2)) /\
  (free [Fn t loc _ num_args x1] =
     let (c1,l1) = free [x1] in
     let l2 = Shift num_args l1 in
       ([Fn t loc (SOME (vars_to_list l2)) num_args (HD c1)],l2)) /\
  (free [Letrec t loc _ fns x1] =
     let m = LENGTH fns in
     let res = MAP (\(n,x). let (c,l) = free [x] in
                              ((n,HD c),Shift (n + m) l)) fns in
     let c1 = MAP FST res in
     let l1 = list_mk_Union (MAP SND res) in
     let (c2,l2) = free [x1] in
       ([Letrec t loc (SOME (vars_to_list l1)) c1 (HD c2)],
        mk_Union l1 (Shift (LENGTH fns) l2))) /\
  (free [Handle t x1 x2] =
     let (c1,l1) = free [x1] in
     let (c2,l2) = free [x2] in
       ([Handle t (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2))) /\
  (free [Call t ticks dest xs] =
     let (c1,l1) = free xs in
       ([Call t ticks dest c1],l1))`
 (WF_REL_TAC `measure exp3_size`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC exp1_size_lemma \\ DECIDE_TAC);

val free_ind = theorem "free_ind";

val free_LENGTH_LEMMA = Q.prove(
  `!xs. (case free xs of (ys,s1) => (LENGTH xs = LENGTH ys))`,
  recInduct free_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [free_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

val free_LENGTH = Q.store_thm("free_LENGTH",
  `!xs ys l. (free xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)`,
  REPEAT STRIP_TAC \\ MP_TAC free_LENGTH_LEMMA \\ fs []);

val free_SING = Q.store_thm("free_SING",
  `(free [x] = (ys,l)) ==> ?y. ys = [y]`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC free_LENGTH
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]);

val LENGTH_FST_free = Q.store_thm("LENGTH_FST_free",
  `LENGTH (FST (free fns)) = LENGTH fns`,
  Cases_on `free fns` \\ fs [] \\ IMP_RES_TAC free_LENGTH);

val HD_FST_free = Q.store_thm("HD_FST_free",
  `[HD (FST (free [x1]))] = FST (free [x1])`,
  Cases_on `free [x1]` \\ fs []
  \\ imp_res_tac free_SING \\ fs[]);

val free_CONS = Q.store_thm("free_CONS",
  `FST (free (x::xs)) = HD (FST (free [x])) :: FST (free xs)`,
  Cases_on `xs` \\ fs [free_def,SING_HD,LENGTH_FST_free,LET_DEF]
  \\ Cases_on `free [x]` \\ fs []
  \\ Cases_on `free (h::t)` \\ fs [SING_HD]
  \\ IMP_RES_TAC free_SING \\ fs []);

val _ = export_theory()

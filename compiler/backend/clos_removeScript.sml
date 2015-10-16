open preamble db_varsTheory closLangTheory;

(* This transformation replaces dead assignments (i.e. unused Lets and
   Letrecs) with dummmy assignments. The assignments aren't removed
   here because removing them would require shifting the De Bruijn
   indexes. The dummy assignments will be removed at the latest by
   BVP's dead-code elimination pass. *)

val _ = new_theory"clos_remove";

val no_overlap_def = Define `
  (no_overlap 0 l <=> T) /\
  (no_overlap (SUC n) l <=>
     if has_var n l then F else no_overlap n l)`

val const_0_def = Define `
  const_0 = Op (Const 0) []`;

val remove_def = tDefine "remove" `
  (remove [] = ([],Empty)) /\
  (remove ((x:closLang$exp)::y::xs) =
     let (c1,l1) = remove [x] in
     let (c2,l2) = remove (y::xs) in
       (c1 ++ c2,mk_Union l1 l2)) /\
  (remove [Var v] = ([Var v], Var v)) /\
  (remove [If x1 x2 x3] =
     let (c1,l1) = remove [x1] in
     let (c2,l2) = remove [x2] in
     let (c3,l3) = remove [x3] in
       ([If (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union l2 l3))) /\
  (remove [Let xs x2] =
     let n = LENGTH xs in
     let (c2,l2) = remove [x2] in
       if no_overlap n l2 then
         ([Let (REPLICATE n const_0) (HD c2)], Shift n l2)
       else
         let (c1,l1) = remove xs in
           ([Let c1 (HD c2)],mk_Union l1 (Shift n l2))) /\
  (remove [Raise x1] =
     let (c1,l1) = remove [x1] in
       ([Raise (HD c1)],l1)) /\
  (remove [Tick x1] =
     let (c1,l1) = remove [x1] in
       ([Tick (HD c1)],l1)) /\
  (remove [Op op xs] =
     let (c1,l1) = remove xs in
       ([Op op c1],l1)) /\
  (remove [App loc_opt x1 xs2] =
     let (c1,l1) = remove [x1] in
     let (c2,l2) = remove xs2 in
       ([App loc_opt (HD c1) c2],mk_Union l1 l2)) /\
  (remove [Fn loc vs_opt num_args x1] =
     let (c1,l1) = remove [x1] in
     let l2 = Shift num_args l1 in
       ([Fn loc (SOME (vars_to_list l2)) num_args (HD c1)],l2)) /\
  (remove [Letrec loc _ fns x1] =
     let m = LENGTH fns in
     let (c2,l2) = remove [x1] in
       if no_overlap m l2 then
         ([Let (REPLICATE m const_0) (HD c2)], Shift m l2)
       else
         let res = MAP (\(n,x). let (c,l) = remove [x] in
                                  ((n,HD c),Shift (n + m) l)) fns in
         let c1 = MAP FST res in
         let l1 = list_mk_Union (MAP SND res) in
           ([Letrec loc (SOME (vars_to_list l1)) c1 (HD c2)],
            mk_Union l1 (Shift (LENGTH fns) l2))) /\
  (remove [Handle x1 x2] =
     let (c1,l1) = remove [x1] in
     let (c2,l2) = remove [x2] in
       ([Handle (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2))) /\
  (remove [Call dest xs] =
     let (c1,l1) = remove xs in
       ([Call dest c1],l1))`
 (WF_REL_TAC `measure exp3_size`
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC exp1_size_lemma \\ DECIDE_TAC);

val remove_ind = theorem "remove_ind";

val remove_LENGTH_LEMMA = prove(
  ``!xs. (case remove xs of (ys,s1) => (LENGTH xs = LENGTH ys))``,
  recInduct remove_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [remove_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

val remove_LENGTH = store_thm("remove_LENGTH",
  ``!xs ys l. (remove xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC remove_LENGTH_LEMMA \\ fs []);

val remove_SING = store_thm("remove_SING",
  ``(remove [x] = (ys,l)) ==> ?y. ys = [y]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC remove_LENGTH
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]);

val LENGTH_FST_remove = store_thm("LENGTH_FST_remove",
  ``LENGTH (FST (remove fns)) = LENGTH fns``,
  Cases_on `remove fns` \\ fs [] \\ IMP_RES_TAC remove_LENGTH);

val HD_FST_remove = store_thm("HD_FST_remove",
  ``[HD (FST (remove [x1]))] = FST (remove [x1])``,
  Cases_on `remove [x1]` \\ fs []
  \\ imp_res_tac remove_SING \\ fs[]);

val remove_CONS = store_thm("remove_CONS",
  ``FST (remove (x::xs)) = HD (FST (remove [x])) :: FST (remove xs)``,
  Cases_on `xs` \\ fs [remove_def,SING_HD,LENGTH_FST_remove,LET_DEF]
  \\ Cases_on `remove [x]` \\ fs []
  \\ Cases_on `remove (h::t)` \\ fs [SING_HD]
  \\ IMP_RES_TAC remove_SING \\ fs []);

val _ = export_theory()

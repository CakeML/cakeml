open HolKernel Parse boolLib bossLib; val _ = new_theory "clos_annotate";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory sptreeTheory db_varsTheory;

(* what is a free variable in clos_exp *)

val clos_free_def = tDefine "clos_free" `
  (clos_free n [] <=> F) /\
  (clos_free n ((x:clos_exp)::y::xs) <=>
     clos_free n [x] \/ clos_free n (y::xs)) /\
  (clos_free n [Var v] <=> (n = v)) /\
  (clos_free n [If x1 x2 x3] <=>
     clos_free n [x1] \/ clos_free n [x2] \/ clos_free n [x3]) /\
  (clos_free n [Let xs x2] <=>
     clos_free n xs \/ clos_free (n + LENGTH xs) [x2]) /\
  (clos_free n [Raise x1] <=> clos_free n [x1]) /\
  (clos_free n [Tick x1] <=> clos_free n [x1]) /\
  (clos_free n [Op op xs] <=> clos_free n xs) /\
  (clos_free n [App loc_opt x1 x2] <=>
     clos_free n [x1] \/ clos_free n [x2]) /\
  (clos_free n [Fn loc vs x1] <=>
     clos_free (n + 1) [x1]) /\
  (clos_free n [Letrec loc vs fns x1] <=>
     clos_free (n + 1) fns \/ clos_free (n + LENGTH fns) [x1]) /\
  (clos_free n [Handle x1 x2] <=>
     clos_free n [x1] \/ clos_free n [x2]) /\
  (clos_free n [Call dest xs] <=> clos_free n xs)`
 (WF_REL_TAC `measure (clos_exp1_size o SND)`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

(* specify when the annotations are good *)

val clos_ann_ok_def = tDefine "clos_ann_ok" `
  (clos_ann_ok [] <=> T) /\
  (clos_ann_ok ((x:clos_exp)::y::xs) <=>
     clos_ann_ok [x] /\ clos_ann_ok (y::xs)) /\
  (clos_ann_ok [Var v] <=> T) /\
  (clos_ann_ok [If x1 x2 x3] <=>
     clos_ann_ok [x1] /\ clos_ann_ok [x2] /\ clos_ann_ok [x3]) /\
  (clos_ann_ok [Let xs x2] <=>
     clos_ann_ok xs /\ clos_ann_ok [x2]) /\
  (clos_ann_ok [Raise x1] <=> clos_ann_ok [x1]) /\
  (clos_ann_ok [Tick x1] <=> clos_ann_ok [x1]) /\
  (clos_ann_ok [Op op xs] <=> clos_ann_ok xs) /\
  (clos_ann_ok [App loc_opt x1 x2] <=>
     clos_ann_ok [x1] /\ clos_ann_ok [x2]) /\
  (clos_ann_ok [Fn loc vs x1] <=>
     (!n. clos_free n [Fn loc vs x1] <=> MEM n vs) /\
     clos_ann_ok [x1]) /\
  (clos_ann_ok [Letrec loc vs fns x1] <=>
     (!n. clos_free n [Letrec loc vs fns (Op (Const 0) [])] <=> MEM n vs) /\
     clos_ann_ok fns /\ clos_ann_ok [x1]) /\
  (clos_ann_ok [Handle x1 x2] <=>
     clos_ann_ok [x1] /\ clos_ann_ok [x2]) /\
  (clos_ann_ok [Call dest xs] <=> clos_ann_ok xs)`
 (WF_REL_TAC `measure (clos_exp1_size)`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

(* annotate clos_exp Fn and Letrec with free variables, no sem change *)

val cFree_def = tDefine "cFree" `
  (cFree [] = ([],Empty)) /\
  (cFree ((x:clos_exp)::y::xs) =
     let (c1,l1) = cFree [x] in
     let (c2,l2) = cFree (y::xs) in
       (c1 ++ c2,mk_Union l1 l2)) /\
  (cFree [Var v] = ([Var v], Var v)) /\
  (cFree [If x1 x2 x3] =
     let (c1,l1) = cFree [x1] in
     let (c2,l2) = cFree [x2] in
     let (c3,l3) = cFree [x3] in
       ([If (HD c1) (HD c2) (HD c3)],mk_Union l1 (mk_Union l2 l3))) /\
  (cFree [Let xs x2] =
     let (c1,l1) = cFree xs in
     let (c2,l2) = cFree [x2] in
       ([Let c1 (HD c2)],mk_Union l1 (Shift (LENGTH xs) l2))) /\
  (cFree [Raise x1] =
     let (c1,l1) = cFree [x1] in
       ([Raise (HD c1)],l1)) /\
  (cFree [Tick x1] =
     let (c1,l1) = cFree [x1] in
       ([Tick (HD c1)],l1)) /\
  (cFree [Op op xs] =
     let (c1,l1) = cFree xs in
       ([Op op c1],l1)) /\
  (cFree [App loc_opt x1 x2] =
     let (c1,l1) = cFree [x1] in
     let (c2,l2) = cFree [x2] in
       ([App loc_opt (HD c1) (HD c2)],mk_Union l1 l2)) /\
  (cFree [Fn loc vs x1] =
     let (c1,l1) = cFree [x1] in
     let l2 = Shift 1 l1 in
       ([Fn loc (vars_to_list l2) (HD c1)],l2)) /\
  (cFree [Letrec loc vs fns x1] =
     let (c1,l1) = cFree fns in
     let l3 = Shift 1 l1 in
     let (c2,l2) = cFree [x1] in
       ([Letrec loc (vars_to_list l3) c1 (HD c2)],
        mk_Union l3 (Shift (LENGTH fns) l2))) /\
  (cFree [Handle x1 x2] =
     let (c1,l1) = cFree [x1] in
     let (c2,l2) = cFree [x2] in
       ([Handle (HD c1) (HD c2)],mk_Union l1 l2)) /\
  (cFree [Call dest xs] =
     let (c1,l1) = cFree xs in
       ([Call dest c1],l1))`
 (WF_REL_TAC `measure clos_exp1_size`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

val cFree_ind = fetch "-" "cFree_ind";

val cFree_LENGTH_LEMMA = prove(
  ``!xs. (case cFree xs of (ys,s1) => (LENGTH xs = LENGTH ys))``,
  recInduct cFree_ind \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [cFree_def]
  \\ SRW_TAC [] [] \\ SRW_TAC [] []
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ FULL_SIMP_TAC (srw_ss()) []
  \\ REV_FULL_SIMP_TAC std_ss [] \\ FULL_SIMP_TAC (srw_ss()) []
  \\ SRW_TAC [] [] \\ DECIDE_TAC)
  |> SIMP_RULE std_ss [] |> SPEC_ALL;

val cFree_LENGTH = prove(
  ``!xs ys l. (cFree xs = (ys,l)) ==> (LENGTH ys = LENGTH xs)``,
  REPEAT STRIP_TAC \\ MP_TAC cFree_LENGTH_LEMMA \\ fs []);

val cFree_SING = prove(
  ``(cFree [x] = (ys,l)) ==> ?y. ys = [y]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC cFree_LENGTH
  \\ Cases_on `ys` \\ fs [LENGTH_NIL]);

val has_var_mk_Union = prove(
  ``has_var n (mk_Union l1 l2) <=> has_var n l1 \/ has_var n l2``,
  SRW_TAC [] [mk_Union_def,has_var_def]);

val _ = augment_srw_ss [rewrites [has_var_mk_Union, has_var_def]];

val cFree_clos_ann_ok_lemma = prove(
  ``!xs.
      let (ys,l) = cFree xs in
        clos_ann_ok ys /\ !n. has_var n l = clos_free n ys``,
  recInduct cFree_ind \\ REPEAT STRIP_TAC \\ fs [cFree_def,LET_DEF]
  \\ TRY (fs [clos_ann_ok_def,has_var_def,clos_free_def] \\ NO_TAC)
  THEN1 (* cons *)
   (`?y1 l1. cFree [x] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
    \\ `?y2 l2. cFree (y::xs) = (y2,l2)` by METIS_TAC [PAIR] \\ fs []
    \\ IMP_RES_TAC cEval_const \\ rfs [] \\ RES_TAC
    \\ IMP_RES_TAC cFree_LENGTH
    \\ Cases_on `y2` \\ fs [clos_ann_ok_def,has_var_def,clos_free_def])
  \\ `?y1 l1. cFree fns = (y1,l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y1 l1. cFree [x1] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y1 l1. cFree xs = (y1,l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y2 l2. cFree [x2] = ([y2],l2)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y3 l3. cFree [x3] = ([y3],l3)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ rfs [] \\ RES_TAC \\ IMP_RES_TAC cFree_LENGTH \\ fs []
  \\ fs [clos_ann_ok_def,has_var_def,clos_free_def,MEM_vars_to_list])
  |> SPEC_ALL;

val cFree_IMP_clos_ann_ok = prove(
  ``(cFree xs = (ys,l)) ==> clos_ann_ok ys``,
  REPEAT STRIP_TAC \\ MP_TAC cFree_clos_ann_ok_lemma \\ fs [LET_DEF]);

(* cShift renames variables to use only those in the annotations *)

val tlookup_def = Define `
  tlookup m k = case lookup m k of NONE => 0:num | SOME k => k`;

val get_var_def = Define `
  get_var m l i v =
    if v < l then v else l + tlookup (v - l) i`;

val cShift_def = tDefine "cShift" `
  (cShift [] (m:num) (l:num) (i:num num_map) = []) /\
  (cShift ((x:clos_exp)::y::xs) m l i =
     let c1 = cShift [x] m l i in
     let c2 = cShift (y::xs) m l i in
       (c1 ++ c2:clos_exp list)) /\
  (cShift [Var v] m l i =
     [Var (get_var m l i v)]) /\
  (cShift [If x1 x2 x3] m l i =
     let c1 = cShift [x1] m l i in
     let c2 = cShift [x2] m l i in
     let c3 = cShift [x3] m l i in
       ([If (HD c1) (HD c2) (HD c3)])) /\
  (cShift [Let xs x2] m l i =
     let c1 = cShift xs m l i in
     let c2 = cShift [x2] m (l + LENGTH xs) i in
       ([Let c1 (HD c2)])) /\
  (cShift [Raise x1] m l i =
     let (c1) = cShift [x1] m l i in
       ([Raise (HD c1)])) /\
  (cShift [Tick x1] m l i =
     let c1 = cShift [x1] m l i in
       ([Tick (HD c1)])) /\
  (cShift [Op op xs] m l i =
     let c1 = cShift xs m l i in
       ([Op op c1])) /\
  (cShift [App loc_opt x1 x2] m l i =
     let c1 = cShift [x1] m l i in
     let c2 = cShift [x2] m l i in
       ([App loc_opt (HD c1) (HD c2)])) /\
  (cShift [Fn loc vs x1] m l i =
     let k = m + l in
     let vs = FILTER (\n. n < k) vs in
     let vars = MAP (\n. (n, get_var m l i n)) vs in
     let c1 = cShift [x1] (LENGTH vars) 1 (fromAList vars) in
       ([Fn loc (MAP FST vars) (HD c1)])) /\
  (cShift [Letrec loc vs fns x1] m l i =
     let k = m + l in
     let vs = FILTER (\n. n < k) vs in
     let vars = MAP (\n. (n, get_var m l i n)) vs in
     let cs = cShift fns (LENGTH vars) 1 (fromAList vars) in
     let c1 = cShift [x1] m l i in
       ([Letrec loc (MAP FST vars) cs (HD c1)])) /\
  (cShift [Handle x1 x2] m l i =
     let c1 = cShift [x1] m l i in
     let c2 = cShift [x2] m l i in
       ([Handle (HD c1) (HD c2)])) /\
  (cShift [Call dest xs] m l i =
     let c1 = cShift xs m l i in
       ([Call dest c1]))`
 (WF_REL_TAC `measure (clos_exp1_size o FST)`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

(* main function *)

val cAnnotate_def = Define `
  cAnnotate xs = cShift (FST (cFree xs)) 0 0 LN`;

val _ = export_theory();

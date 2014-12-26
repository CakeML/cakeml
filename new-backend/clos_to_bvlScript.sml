open HolKernel Parse boolLib bossLib; val _ = new_theory "clos_to_bvl";

open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory bvlTheory;
open sptreeTheory

(* compiler definition *)

val free_let_def = Define `
  free_let n = (GENLIST (\n. Op (El (n+1)) [Var 1]) n) : bvl_exp list`;

val closure_tag_def = Define `
  closure_tag = 0:num`;

val code_for_recc_case_def = Define `
  code_for_recc_case n (c:bvl_exp) =
    Let [Op (El 1) [Var 1]]
      (Let (Var 1::GENLIST (\i. Op (Deref) [Var 0; Op (Const (& i)) []]) n) c)`

val build_aux_def = Define `
  (build_aux i [] aux = (i:num,aux)) /\
  (build_aux i ((x:bvl_exp)::xs) aux = build_aux (i+1) xs ((i,x) :: aux))`;

val recc_Let_def = Define `
  recc_Let n hole =
    Let [Op (Cons closure_tag) [Op (Label n) []; Var 0]]
      (Let [Op Update [hole; Var 0]] (Var 1 : bvl_exp))`;

val recc_Lets_def = Define `
  recc_Lets n k rest =
    if k = 0:num then rest else
      Let [recc_Let n (Op (El 1) [Var 1])]
        (recc_Lets (n+1) (k-1) rest)`;

val build_recc_lets_def = Define `
  build_recc_lets (fns:clos_exp list) vs n1 fns_l (c3:bvl_exp) =
    Let [Let [Op Ref (MAP (K (Op (Const 0) [])) fns ++ MAP Var vs)]
           (recc_Let n1 (Var 1))]
      (recc_Lets (n1+1) (fns_l - 1) c3)`;

val cComp_def = tDefine "cComp" `
  (cComp (n:num) [] aux = ([],aux,n)) /\
  (cComp n ((x:clos_exp)::y::xs) aux =
     let (c1,aux1,n1) = cComp n [x] aux in
     let (c2,aux2,n2) = cComp n1 (y::xs) aux1 in
       (c1 ++ c2, aux2, n2)) /\
  (cComp n [Var v] aux = ([(Var v):bvl_exp], aux, n)) /\
  (cComp n [If x1 x2 x3] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
     let (c2,aux2,n2) = cComp n1 [x2] aux1 in
     let (c3,aux3,n3) = cComp n2 [x3] aux2 in
       ([If (HD c1) (HD c2) (HD c3)],aux3,n3)) /\
  (cComp n [Let xs x2] aux =
     let (c1,aux1,n1) = cComp n xs aux in
     let (c2,aux2,n2) = cComp n1 [x2] aux1 in
       ([Let c1 (HD c2)], aux2, n2)) /\
  (cComp n [Raise x1] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
       ([Raise (HD c1)], aux1, n1)) /\
  (cComp n [Tick x1] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
       ([Tick (HD c1)], aux1, n1)) /\
  (cComp n [Op op xs] aux =
     let (c1,aux1,n1) = cComp n xs aux in
       ([Op op c1],aux1,n1)) /\
  (cComp n [App x1 x2] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
     let (c2,aux2,n2) = cComp n1 [x2] aux1 in
       ([Let (c1++c2)
           (Call NONE ((Var 1) ::          (* argument *)
                       (Var 0) ::          (* closure itself *)
                       [Op (El 0) [Var 0]] (* code pointer *)))],
        aux2, n2)) /\
  (cComp n [Fn vs x1] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
     let c2 = Let ((Var 0:bvl_exp) :: free_let (LENGTH vs)) (HD c1) in
       ([Op (Cons closure_tag) (Op (Label n1) [] :: MAP Var vs)],
        (n1,c2) :: aux1, n1+1)) /\
  (cComp n [Letrec vs fns x1] aux =
     case fns of
     | [] => cComp n [x1] aux
     | [exp] =>
         let (c1,aux1,n1) = cComp n [exp] aux in
         let (c2,aux2,n2) = cComp (n1+1) [x1] aux1 in
         let c3 = Let (Var 0 :: Var 1 :: free_let (LENGTH vs)) (HD c1) in
         let c4 = Op (Cons closure_tag) (Op (Label n1) [] :: MAP Var vs) in
           ([Let [c4] (HD c2)], (n1,c3) :: aux2, n2)
     | _ =>
         let fns_l = LENGTH fns in
         let l = fns_l + LENGTH vs in
         let (cs,aux1,n1) = cComp n fns aux in
         let cs1 = MAP (code_for_recc_case l) cs in
         let (n2,aux2) = build_aux n1 cs1 aux in
         let (c3,aux3,n3) = cComp n2 [x1] aux2 in
         let c4 = build_recc_lets fns vs n1 fns_l (HD c3) in
           ([c4],aux3,n3)) /\
  (cComp n [Handle x1 x2] aux =
     let (c1,aux1,n1) = cComp n [x1] aux in
     let (c2,aux2,n2) = cComp n1 [x2] aux1 in
       ([Handle (HD c1) (HD c2)], aux2, n2)) /\
  (cComp n [Call dest xs] aux =
     let (c1,aux1,n1) = cComp n xs aux in
       ([Call (SOME dest) c1],aux1,n1))`
 (WF_REL_TAC `measure (clos_exp1_size o FST o SND)`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

(* correctness proof *)

val code_installed_def = Define `
  code_installed aux code =
    EVERY (\(n,exp). lookup n code = SOME (2:num,exp)) aux`;

val closure_code_installed_def = Define `
  closure_code_installed code exps_ps (env:clos_val list) =
    EVERY (\(exp,p).
      ?n aux c aux1 n1.
        (cComp n [exp] aux = ([c],aux1,n1)) /\
        (lookup p code = SOME (2:num,code_for_recc_case
              (LENGTH env + LENGTH exps_ps) c)) /\
        code_installed aux1 code) exps_ps`

val (val_rel_rules,val_rel_ind,val_rel_cases) = Hol_reln `
  (val_rel f refs code (Number n) (Number n))
  /\
  (EVERY2 (val_rel f refs code) xs (ys:bc_value list) ==>
   val_rel f refs code (Block t xs) (Block t ys))
  /\
  ((FLOOKUP f r1 = SOME r2) ==>
   val_rel f refs code (RefPtr r1) (RefPtr r2))
  /\
  (EVERY2 (val_rel f refs code) env ys /\
   (cComp n' [x] aux = ([c],aux1,n1)) /\
   code_installed aux1 code /\
   (lookup p code = SOME (2:num,Let (Var 0::free_let (LENGTH env)) c)) ==>
   val_rel f refs code (Closure env x) (Block closure_tag (CodePtr p :: ys)))
  /\
  (EVERY2 (val_rel f refs code) env ys /\
   (cComp n' [x] aux = ([c],aux1,n1)) /\
   code_installed aux1 code /\
   (lookup p code = SOME (2:num,Let (Var 0::Var 1::free_let (LENGTH env)) c)) ==>
   val_rel f refs code (Recclosure env [x] 0) (Block closure_tag (CodePtr p :: ys)))
  /\
  ((exps = MAP FST exps_ps) /\
   (ps = MAP SND exps_ps) /\
   (rs = MAP (\p. Block closure_tag [CodePtr p; RefPtr r]) ps) /\
   ~(r IN FRANGE f) /\
   (FLOOKUP refs r = SOME (ValueArray (rs ++ ys))) /\
   EVERY2 (val_rel f refs code) env ys /\
   1 < LENGTH exps /\ k < LENGTH exps /\ (p = EL k ps) /\
   closure_code_installed code exps_ps env ==>
   val_rel f refs code (Recclosure env exps k) (EL k rs))`

val opt_val_rel_def = Define `
  (opt_val_rel f refs code NONE NONE = T) /\
  (opt_val_rel f refs code (SOME x) (SOME y) = val_rel f refs code x y) /\
  (opt_val_rel f refs code _ _ = F)`;

val (res_rel_rules,res_rel_ind,res_rel_cases) = Hol_reln `
  (EVERY2 (val_rel f refs code) xs (ys:bc_value list) ==>
   res_rel f refs code (Result xs) (Result ys)) /\
  (val_rel f refs code x y ==>
   res_rel f refs code (Exception x) (Exception y)) /\
  (res_rel f refs code TimeOut TimeOut) /\
  (res_rel f refs code Error Error)`

val env_rel_def = Define `
  (env_rel f refs code [] [] = T) /\
  (env_rel f refs code [] ys = T) /\   (* bvl env allowed to contain extra stuff *)
  (env_rel f refs code (x::xs) [] = F) /\
  (env_rel f refs code (x::xs) (y::ys) <=>
     val_rel f refs code x y /\ env_rel f refs code xs ys)`;

val (ref_rel_rules,ref_rel_ind,ref_rel_cases) = Hol_reln `
  (EVERY2 (val_rel f refs code) [x] ys ==>
   ref_rel f refs code x (ValueArray ys))` (* TODO: needs fixing *)

val state_rel_def = Define `
  state_rel f (s:clos_state) (t:bvl_state) <=>
    (s.clock = t.clock) /\
    (s.output = t.output) /\
    (EVERY2 (opt_val_rel f t.refs t.code) s.globals t.globals /\
    INJ ($' f) (FDOM f) (FRANGE f) /\
    (FDOM f = FDOM s.refs) /\
    (!n x. (FLOOKUP s.refs n = SOME x) ==>
           ?y m. (FLOOKUP f n = SOME m) /\
                 (FLOOKUP t.refs m = SOME y) /\
                 ref_rel f t.refs t.code x y) /\
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?n1 aux1 n2 c2 aux2.
        (cComp n1 [c] aux1 = ([c2],aux2,n2)) /\
        (lookup name t.code = SOME (arity,c2)) /\
        code_installed aux2 t.code))`

val FDIFF_def = Define `
  FDIFF f1 f2 = DRESTRICT f1 (COMPL (FRANGE f2))`;

val val_rel_SUBMAP = prove(
  ``!x y. val_rel f1 refs1 code x y ==>
      f1 SUBMAP f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
      val_rel f2 refs2 code x y``,
  HO_MATCH_MP_TAC val_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (fs [SUBMAP_DEF,FLOOKUP_DEF])
  THEN1 (Q.LIST_EXISTS_TAC [`aux`,`aux1`,`n'`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`,`n'`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`,`ys`] \\ fs []
  \\ rfs [] \\ Q.PAT_ASSUM `LIST_REL pppat env ys` MP_TAC
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r`) \\ fs [])
  |> SPEC_ALL |> MP_CANON;

val env_rel_SUBMAP = prove(
  ``!env1 env2.
      env_rel f1 refs1 code env1 env2 /\
      f1 SUBMAP f2 /\ FDIFF refs1 f1 SUBMAP FDIFF refs2 f2 ==>
      env_rel f2 refs2 code env1 env2``,
  Induct \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ REPEAT STRIP_TAC \\ IMP_RES_TAC val_rel_SUBMAP) |> GEN_ALL;

val LESS_LENGTH_env_rel_IMP = prove(
  ``!env env2 n.
      n < LENGTH env /\ env_rel f refs code env env2 ==>
      n < LENGTH env2 /\ val_rel f refs code (EL n env) (EL n env2)``,
  Induct \\ fs [LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases_on `n` \\ fs []);

val lookup_vars_IMP = prove(
  ``!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel f refs code env env2 ==>
      ?ys. (bEval (MAP Var vs,env2,t1) = (Result ys,t1)) /\
           EVERY2 (val_rel f refs code) xs ys /\
           (LENGTH vs = LENGTH xs)``,
  Induct \\ fs [lookup_vars_def,bEval_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ fs [] \\ SRW_TAC [] []
  \\ ONCE_REWRITE_TAC [bEval_CONS]
  \\ fs [bEval_def]
  \\ RES_TAC \\ IMP_RES_TAC LESS_LENGTH_env_rel_IMP \\ fs []);

val build_aux_lemma = prove(
  ``!k n aux. ?aux1. SND (build_aux n k aux) = aux1 ++ aux``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPECL [`n+1`,`(n,h)::aux`]) \\ fs []);

val cComp_lemma = prove(
  ``!n xs aux.
      let (c,aux1,n1) = cComp n xs aux in
        (LENGTH c = LENGTH xs) /\ ?ys. aux1 = ys ++ aux``,
  recInduct (fetch "-" "cComp_ind") \\ REPEAT STRIP_TAC
  \\ fs [cComp_def] \\ SRW_TAC [] [] \\ fs [LET_DEF,ADD1]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ rfs [] \\ fs []
  \\ Cases_on `cComp n [r] aux` \\ fs []
  \\ Cases_on `r'` \\ fs [] \\ TRY DECIDE_TAC
  \\ Q.PAT_ASSUM `xxx = (c,aux1,n1)` MP_TAC
  \\ Cases_on `t` \\ fs []
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ `?tt. cComp n [h] aux = tt` by fs [] \\ PairCases_on `tt` \\ fs []
  \\ `?t1. cComp (tt2 + 1) [x1] (ys ++ aux) = t1` by fs []
  \\ PairCases_on `t1` \\ fs [] \\ rfs [] \\ fs []
  \\ `?t0. cComp n (h::h'::t') aux = t0` by fs []
  \\ PairCases_on `t0` \\ fs []
  \\ Q.ABBREV_TAC `m = (MAP (code_for_recc_case
           (SUC (SUC (LENGTH t')) + LENGTH vs)) t00)`
  \\ Cases_on `build_aux t02 m aux` \\ fs []
  \\ `?t1. cComp q'' [x1] r' = t1` by fs []
  \\ PairCases_on `t1` \\ fs []
  \\ ASSUME_TAC (Q.SPECL [`m`,`t02`,`aux`] build_aux_lemma) \\ rfs []);

val cComp_SING = prove(
  ``(cComp n [x] aux = (c,aux1,n1)) ==> ?d. c = [d]``,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`n`,`[x]`,`aux`] cComp_lemma) \\ rfs [LET_DEF]
  \\ Cases_on `c` \\ fs [] \\ Cases_on `t` \\ fs []);

val res_rel_Result =
  ``res_rel f refs code (Result x) (Result y)``
  |> SIMP_CONV (srw_ss()) [res_rel_cases]

val val_rel_Closure =
  ``val_rel f refs code (Closure env exp) y``
  |> SIMP_CONV (srw_ss()) [val_rel_cases]

val bEval_free_let_Block = prove(
  ``!ys zs s.
      bEval (free_let (LENGTH ys),[x; Block n (y::ys ++ zs)],s) =
        (Result ys,s)``,
  recInduct SNOC_INDUCT \\ REPEAT STRIP_TAC THEN1 EVAL_TAC
  \\ fs [free_let_def,GENLIST,bEval_SNOC]
  \\ fs [SNOC_APPEND] \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC] \\ fs []
  \\ fs [bEval_def,bEvalOp_def]
  \\ SRW_TAC [] [] \\ TRY (`F` by DECIDE_TAC)
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND,GSYM APPEND_ASSOC]
  \\ `LENGTH l + 1 = LENGTH (y::l)` by fs [ADD1]
  \\ FULL_SIMP_TAC std_ss [EVAL ``[x] ++ l``]
  \\ fs [rich_listTheory.EL_LENGTH_APPEND])
  |> Q.SPECL [`ys`,`[]`,`s`] |> SIMP_RULE std_ss [APPEND_NIL];

val list_rel_IMP_env_rel = prove(
  ``!xs ys.
      LIST_REL (val_rel f refs code) xs ys ==>
      env_rel f refs code xs (ys ++ ts)``,
  Induct \\ Cases_on `ys` \\ fs [env_rel_def]
  \\ Cases_on `ts` \\ fs [env_rel_def]);

val cComp_IMP_code_installed = prove(
  ``(cComp n xs aux = (c,aux1,n1)) /\
    code_installed aux1 code ==>
    code_installed aux code``,
  REPEAT STRIP_TAC
  \\ MP_TAC (SPEC_ALL cComp_lemma) \\ fs [LET_DEF]
  \\ REPEAT STRIP_TAC \\ fs [code_installed_def]);

val IMP_IMP = save_thm("IMP_IMP",
  METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``);

val FLOOKUP_SUBMAP_IMP = prove(
  ``(FLOOKUP refs2 r = SOME x) /\ r NOTIN FRANGE f2 /\
    FDIFF refs2 f2 SUBMAP FDIFF refs6 f6 ==>
    (FLOOKUP refs6 r = SOME x) /\ r NOTIN FRANGE f6``,
  fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF] \\ METIS_TAC []);

val bEval_ValueArray_lemma = prove(
  ``!zs s r ts.
      (FLOOKUP s.refs r = SOME (ValueArray (zs ++ ts))) ==>
      (bEval
        (GENLIST (\i. Op Deref [Var 0; Op (Const (&i)) []]) (LENGTH zs),
         RefPtr r::env,s) = (Result zs,s))``,
  recInduct SNOC_INDUCT \\ REPEAT STRIP_TAC \\ fs [bEval_def,GENLIST]
  \\ fs [bEval_SNOC] \\ fs [bEval_def,bEvalOp_def]
  \\ fs [DECIDE ``n < SUC n + m:num``,SNOC_APPEND]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [rich_listTheory.EL_LENGTH_APPEND]);

val bEval_ValueArray = prove(
  ``(FLOOKUP s.refs r = SOME (ValueArray zs)) /\ (n = LENGTH zs) ==>
    (bEval
      (GENLIST (\i. Op Deref [Var 0; Op (Const (&i)) []]) n,
       RefPtr r::env,s) = (Result zs,s))``,
  REPEAT STRIP_TAC \\ fs []
  \\ MATCH_MP_TAC bEval_ValueArray_lemma
  \\ Q.EXISTS_TAC `[]` \\ fs []);

val cComp_correct = prove(
  ``!xs env s1 n aux1 t1 env' f1 res s2 n2 ys aux2.
      (cEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      (cComp n xs aux1 = (ys,aux2,n2)) /\
      code_installed aux2 t1.code /\
      env_rel f1 t1.refs t1.code env env' /\
      state_rel f1 s1 t1 ==>
      ?res' t2 f2.
         (bEval (ys,env',t1) = (res',t2)) /\
         res_rel f2 t2.refs t2.code res res' /\
         state_rel f2 s2 t2 /\
         f1 SUBMAP f2 /\
         (FDIFF t1.refs f1) SUBMAP (FDIFF t2.refs f2)``,

  recInduct cEval_ind \\ REPEAT STRIP_TAC
  THEN1 (* NIL *) cheat
  THEN1 (* CONS *) cheat
  THEN1 (* Var *) cheat
  THEN1 (* If *) cheat
  THEN1 (* Let *) cheat
  THEN1 (* Raise *) cheat
  THEN1 (* Handle *) cheat
  THEN1 (* Op *) cheat
  THEN1 (* Fn *)
   (fs [cEval_def] \\ BasicProvers.FULL_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [cComp_def]
    \\ `?c2 aux3 n3. cComp n [exp] aux1 = (c2,aux3,n3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ fs [code_installed_def]
    \\ fs [bEval_def,bEval_CONS,bEvalOp_def,domain_lookup]
    \\ IMP_RES_TAC lookup_vars_IMP
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `t1`)
    \\ fs [res_rel_cases,val_rel_cases]
    \\ Q.EXISTS_TAC `f1` \\ fs []
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
    \\ Q.LIST_EXISTS_TAC [`aux1`,`aux3`,`n`] \\ fs []
    \\ IMP_RES_TAC cComp_SING \\ fs [code_installed_def])
  THEN1 (* Letrec *)

   (fs [cEval_def] \\ BasicProvers.FULL_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [cComp_def]
    \\ fs [build_recc_def]
    \\ Cases_on `lookup_vars names env` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `fns` \\ fs []
    THEN1 (rfs [] \\ FIRST_X_ASSUM MATCH_MP_TAC
           \\ Q.LIST_EXISTS_TAC [`n`,`aux1`] \\ fs [])
    \\ Cases_on `t` \\ fs [] \\ rfs []
    THEN1 (* special case for singly-recursive closure *)
     (`?c2 aux3 n3. cComp n [h] aux1 = ([c2],aux3,n3)` by
              METIS_TAC [PAIR,cComp_SING]
      \\ `?c3 aux4 n4. cComp (n3+1) [exp] aux3 = ([c3],aux4,n4)` by
              METIS_TAC [PAIR,cComp_SING]
      \\ fs [LET_DEF] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n3+1`,`aux3`,`t1`]) \\ fs []
      \\ fs [code_installed_def] \\ REPEAT STRIP_TAC
      \\ fs [bEval_def,bEvalOp_def,domain_lookup]
      \\ ONCE_REWRITE_TAC [bEval_CONS]
      \\ fs [bEval_def,bEvalOp_def,domain_lookup]
      \\ IMP_RES_TAC lookup_vars_IMP \\ fs []
      \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `t1`) \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
           [`Block closure_tag (CodePtr n3::ys)::env'`,`f1`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (fs [env_rel_def] \\ fs [val_rel_cases] \\ DISJ1_TAC
        \\ Q.LIST_EXISTS_TAC [`aux1`,`aux3`,`n`] \\ fs []
        \\ IMP_RES_TAC cComp_IMP_code_installed
        \\ fs [GSYM code_installed_def])
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.LIST_EXISTS_TAC [`res'`,`t2`,`f2`] \\ fs []
      \\ Cases_on `res'` \\ fs []
      \\ IMP_RES_TAC bEval_IMP_LENGTH
      \\ Cases_on `a` \\ fs [] \\ Cases_on `t` \\ fs [LENGTH_NIL])
    (* general case for mutually recursive closures *)
    \\ cheat)

  THEN1 (* App *)
   (fs [cEval_def,cComp_def]
    \\ `?res5 s5. cEval ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. cEval ([x2],env,s5) = (res6,s6)` by METIS_TAC [PAIR]
    \\ `?c7 aux7 n7. cComp n [x1] aux1 = ([c7],aux7,n7)` by
          METIS_TAC [PAIR,cComp_SING]
    \\ `?c8 aux8 n8. cComp n7 [x2] aux7 = ([c8],aux8,n8)` by
          METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ ONCE_REWRITE_TAC [bEval_def]
    \\ SIMP_TAC std_ss [Once bEval_def]
    \\ REVERSE (Cases_on `res5`) \\ fs []
    \\ SRW_TAC [] []
    \\ `code_installed aux7 t1.code` by IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n`,`aux1`,`t1`,`env'`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ POP_ASSUM (MP_TAC o Q.SPEC `f1`) \\ fs [] \\ REPEAT STRIP_TAC
    \\ Cases_on `res'`
    \\ TRY (fs [res_rel_cases]
         \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC) \\ fs []
    \\ `t2.code = t1.code` by IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ `code_installed aux2 t2.code` by fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n7`,`aux7`,`t2`,`env'`,`f2`]) \\ fs []
    \\ `env_rel f2 t2.refs t1.code env env'` by
          (MATCH_MP_TAC env_rel_SUBMAP \\ METIS_TAC []) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ REVERSE (Cases_on `res6`) \\ fs []
    \\ Cases_on `res'`
    \\ TRY (fs [res_rel_cases] \\ SRW_TAC [] []
            \\ Q.EXISTS_TAC `f2'` \\ IMP_RES_TAC SUBMAP_TRANS
            \\ fs [] \\ NO_TAC) \\ fs []
    \\ `?g1 y1 c1. (a = [g1]) /\ (a'' = [y1])` by METIS_TAC [cEval_SING]
    \\ fs [] \\ Cases_on `dest_closure g1 y1` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `x` \\ fs []
    \\ fs [bEval_def]
    \\ fs [res_rel_Result,DECIDE ``1 < SUC (1 + n:num)``]
    \\ Cases_on `g1` \\ fs [dest_closure_def] \\ SRW_TAC [] []
    THEN1 (* Closure case *)
     (fs [val_rel_Closure] \\ SRW_TAC [] []
      \\ fs [bEvalOp_def,find_code_def]
      \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel f6 s6 t6` []
      \\ `t6.code = t2.code` by IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ `t6.clock = s6.clock` by fs [state_rel_def] \\ fs []
      \\ Cases_on `s6.clock = 0` \\ fs []
      THEN1 (Q.EXISTS_TAC `f6` \\ SRW_TAC [] [res_rel_cases]
             \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
      \\ SIMP_TAC std_ss [bEval_def]
      \\ SIMP_TAC std_ss [Once bEval_CONS]
      \\ fs [bEval_def]
      \\ IMP_RES_TAC EVERY2_LENGTH
      \\ fs [bEval_free_let_Block]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n'`,`aux`,`dec_clock t6`])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `(dec_clock t6).code = t1.code` by (fs [dec_clock_def]) \\ fs []
      \\ `(dec_clock t6).refs = t6.refs` by (fs [dec_clock_def]) \\ fs []
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
      \\ POP_ASSUM (MP_TAC o Q.SPECL
           [`y'::(ys ++ [y'; Block closure_tag (CodePtr p::ys)])`,`f6`])
      \\ MATCH_MP_TAC IMP_IMP \\ REVERSE STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ fs [] \\ Q.EXISTS_TAC `f2'` \\ fs []
        \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [dec_clock_def])
      \\ fs [env_rel_def]
      \\ IMP_RES_TAC list_rel_IMP_env_rel \\ fs []
      \\ fs [state_rel_def,closLangTheory.dec_clock_def,bvlTheory.dec_clock_def]
      \\ rfs [] \\ MATCH_MP_TAC env_rel_SUBMAP \\ METIS_TAC [])
    (* Recclosure case *)
    \\ fs [GSYM NOT_LESS]
    \\ Q.MATCH_ASSUM_RENAME_TAC `index < LENGTH exps` []
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ Q.ABBREV_TAC `cl_env = l` \\ POP_ASSUM (K ALL_TAC)
    \\ Cases_on `LENGTH exps = 0` \\ fs []
    \\ Cases_on `LENGTH exps = 1` \\ fs []
    THEN1 (* special case for singly-recursive closure *)
     (`?exp. exps = [exp]` by (Cases_on `exps` \\ fs [LENGTH_NIL])
      \\ SRW_TAC [] [] \\ POP_ASSUM (K ALL_TAC)
      \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel f6 s6 t6` []
      \\ Q.PAT_ASSUM `val_rel f2 t2.refs t1.code (Recclosure cl_env [exp] 0) y` MP_TAC
      \\ REVERSE (ONCE_REWRITE_TAC [val_rel_cases] \\ fs [] \\ SRW_TAC [] [])
      THEN1 (Cases_on `exps_ps` \\ fs [] \\ Cases_on `t` \\ fs [])
      \\ fs [bEvalOp_def,find_code_def]
      \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ `t6.clock = s6.clock` by fs [state_rel_def] \\ fs []
      \\ Cases_on `s6.clock = 0` \\ fs []
      THEN1 (Q.EXISTS_TAC `f6` \\ IMP_RES_TAC SUBMAP_TRANS
             \\ SRW_TAC [] [res_rel_cases])
      \\ SIMP_TAC std_ss [bEval_def] \\ fs []
      \\ SIMP_TAC std_ss [Once bEval_CONS]
      \\ fs [bEval_def]
      \\ IMP_RES_TAC EVERY2_LENGTH
      \\ fs [bEval_free_let_Block]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n'`,`aux`,`dec_clock t6`])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `(dec_clock t6).code = t1.code` by (fs [dec_clock_def]) \\ fs []
      \\ Q.ABBREV_TAC `bb = Block closure_tag (CodePtr p::ys)`
      \\ Q.PAT_ASSUM `!xx.bbb` (MP_TAC o Q.SPECL [`y'::bb::(ys ++ [y'; bb])`,`f6`])
      \\ MATCH_MP_TAC IMP_IMP \\ REVERSE STRIP_TAC THEN1
       (REPEAT STRIP_TAC \\ fs [] \\ Q.EXISTS_TAC `f2'` \\ fs []
        \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [dec_clock_def])
      \\ fs [state_rel_def,closLangTheory.dec_clock_def,bvlTheory.dec_clock_def]
      \\ `y'::bb::(ys ++ [y'; bb]) = y'::bb::ys ++ [y'; bb]` by fs []
      \\ ASM_SIMP_TAC std_ss []
      \\ MATCH_MP_TAC list_rel_IMP_env_rel \\ fs []
      \\ `LIST_REL (val_rel f6 t6.refs t2.code) cl_env ys` by
       (Q.PAT_ASSUM `LIST_REL vvv cl_env ys` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ METIS_TAC [val_rel_SUBMAP])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs [] \\ DISJ1_TAC
      \\ Q.UNABBREV_TAC `bb` \\ fs [] \\ METIS_TAC [])
    (* general case for mutually recursive closures *)
    \\ Q.PAT_ASSUM `val_rel f2 t2.refs t1.code xxx y` MP_TAC
    \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
    \\ REPEAT STRIP_TAC THEN1 (SRW_TAC [] [] \\ fs [])
    \\ SRW_TAC [] [] \\ fs []
    \\ fs [MAP_MAP_o,EL_MAP]
    \\ SIMP_TAC std_ss [Once bEvalOp_def] \\ fs [find_code_def]
    \\ POP_ASSUM (fn th => ASSUME_TAC th THEN
         ASSUME_TAC (RW [closure_code_installed_def] th))
    \\ fs [EVERY_MEM]
    \\ `MEM (EL index exps_ps) exps_ps` by METIS_TAC [MEM_EL]
    \\ FIRST_ASSUM (MP_TAC o Q.SPEC `EL index exps_ps`)
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
    \\ `?exp p. EL index exps_ps = (exp,p)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel f6 s6 t6` []
    \\ `t6.clock = s6.clock` by fs [state_rel_def]
    \\ Cases_on `t6.clock = 0` \\ fs []
    THEN1 (Q.EXISTS_TAC `f6` \\ IMP_RES_TAC SUBMAP_TRANS
           \\ SRW_TAC [] [res_rel_cases])
    \\ rfs [] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n'`,`aux`,`dec_clock t6`]) \\ fs []
    \\ `state_rel f6 (dec_clock s6) (dec_clock t6)` by ALL_TAC THEN1
      (fs [state_rel_def,closLangTheory.dec_clock_def,bvlTheory.dec_clock_def])
    \\ `code_installed aux1' (dec_clock t6).code` by ALL_TAC THEN1
      (fs [bvlTheory.dec_clock_def]) \\ fs [] \\ STRIP_TAC
    \\ SIMP_TAC std_ss [code_for_recc_case_def]
    \\ fs [bEval_def,bEvalOp_def]
    \\ ONCE_REWRITE_TAC [bEval_CONS]
    \\ fs [bEval_def,o_DEF]
    \\ Q.ABBREV_TAC `zs = (MAP (\x. Block closure_tag [CodePtr (SND x); RefPtr r])
               exps_ps ++ ys)`
    \\ `bEval
         (GENLIST (\i. Op Deref [Var 0; Op (Const (&i)) []])
            (LENGTH cl_env + LENGTH exps_ps),
          [RefPtr r; y'; Block closure_tag [CodePtr p; RefPtr r]],
          dec_clock t6) = (Result zs,dec_clock t6)` by ALL_TAC THEN1
     (MATCH_MP_TAC bEval_ValueArray
      \\ UNABBREV_ALL_TAC \\ IMP_RES_TAC EVERY2_LENGTH
      \\ fs [dec_clock_def,AC ADD_COMM ADD_ASSOC]
      \\ IMP_RES_TAC FLOOKUP_SUBMAP_IMP) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`y':: (zs ++ [RefPtr r] ++
             [y'; Block closure_tag [CodePtr p; RefPtr r]])`,`f6`])
    \\ fs [] \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [env_rel_def,dec_clock_def]
      \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC]
      \\ MATCH_MP_TAC list_rel_IMP_env_rel
      \\ UNABBREV_ALL_TAC
      \\ MATCH_MP_TAC rich_listTheory.EVERY2_APPEND_suff
      \\ REVERSE (REPEAT STRIP_TAC) THEN1
       (Q.PAT_ASSUM `LIST_REL xxx cl_env ys` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ METIS_TAC [val_rel_SUBMAP])
      \\ SIMP_TAC std_ss [listTheory.LIST_REL_EL_EQN]
      \\ fs [LENGTH_MAP,LENGTH_GENLIST,EL_MAP]
      \\ REPEAT STRIP_TAC
      \\ Q.MATCH_ASSUM_RENAME_TAC `k7 < LENGTH exps_ps` []
      \\ SIMP_TAC std_ss [Once val_rel_cases] \\ fs [] \\ DISJ2_TAC
      \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`,`ys`]
      \\ fs [EL_MAP] \\ IMP_RES_TAC FLOOKUP_SUBMAP_IMP \\ fs []
      \\ fs [MAP_MAP_o,o_DEF]
      \\ Q.PAT_ASSUM `LIST_REL xxx cl_env ys` MP_TAC
      \\ MATCH_MP_TAC listTheory.LIST_REL_mono
      \\ METIS_TAC [val_rel_SUBMAP])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `res'` \\ fs []
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ fs [dec_clock_def]
    \\ IMP_RES_TAC SUBMAP_TRANS
    \\ ASM_SIMP_TAC std_ss []
    \\ `[HD a] = a` by ALL_TAC \\ fs []
    \\ IMP_RES_TAC bEval_IMP_LENGTH
    \\ Cases_on `a` \\ fs [LENGTH_NIL])
  THEN1 (* Tick *) cheat
  THEN1 (* Call *) cheat);


(*
val _ = PolyML.SaveState.saveState "heap_state";
val _ = PolyML.SaveState.loadState "heap_state";
*)

val _ = export_theory();

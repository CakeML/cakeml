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
    Let [Op (El 1) [Var 0]]
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
  (cComp n [] aux = ([],aux,n)) /\
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

val (val_rel_rules,val_rel_ind,val_rel_cases) = Hol_reln `
  (val_rel code (Number i) (Number i))
  /\
  (EVERY2 (val_rel code) xs (ys:bc_value list) ==>
   val_rel code (Block t xs) (Block t ys))
  /\
  (val_rel code (RefPtr p1) (RefPtr p1)) (* <-- needs changing *)
  /\
  (EVERY2 (val_rel code) env ys /\
   (cComp n [x] aux = ([c],aux1,n1)) /\
   code_installed aux1 code /\
   (lookup p code = SOME (2:num,Let (Var 0::free_let (LENGTH env)) c)) ==>
   val_rel code (Closure env x) (Block closure_tag (CodePtr p :: ys)))
  /\
  (EVERY2 (val_rel code) env ys /\
   (cComp n [x] aux = ([c],aux1,n1)) /\
   code_installed aux1 code /\
   (lookup p code = SOME (2:num,Let (Var 0::Var 1::free_let (LENGTH env)) c)) ==>
   val_rel code (Recclosure env [x] 0) (Block closure_tag (CodePtr p :: ys)))`

val opt_val_rel_def = Define `
  (opt_val_rel code NONE NONE = T) /\
  (opt_val_rel code (SOME x) (SOME y) = val_rel code x y) /\
  (opt_val_rel code _ _ = F)`;

val (res_rel_rules,res_rel_ind,res_rel_cases) = Hol_reln `
  (EVERY2 (val_rel code) xs (ys:bc_value list) ==>
   res_rel code (Result xs) (Result ys)) /\
  (val_rel code x y ==>
   res_rel code (Exception x) (Exception y)) /\
  (res_rel code TimeOut TimeOut) /\
  (res_rel code Error Error)`

val env_rel_def = Define `
  (env_rel code [] [] = T) /\
  (env_rel code [] ys = T) /\   (* bvl env allowed to contain extra stuff *)
  (env_rel code (x::xs) [] = F) /\
  (env_rel code (x::xs) (y::ys) <=> val_rel code x y /\ env_rel code xs ys)`;

val state_rel_def = Define `
  state_rel (s:clos_state) (t:bvl_state) <=>
    (s.clock = t.clock) /\
    (s.output = t.output) /\
    (EVERY2 (opt_val_rel t.code) s.globals t.globals /\
    (* TODO: refs need relating too *)
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?n1 aux1 n2 c2 aux2.
        (cComp n1 [c] aux1 = ([c2],aux2,n2)) /\
        (lookup name t.code = SOME (arity,c2)) /\
        code_installed aux2 t.code))`

val LESS_LENGTH_env_rel_IMP = prove(
  ``!env env2 n.
      n < LENGTH env /\ env_rel t1.code env env2 ==>
      n < LENGTH env2 /\ val_rel t1.code (EL n env) (EL n env2)``,
  Induct \\ fs [LENGTH] \\ REPEAT STRIP_TAC
  \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ Cases_on `n` \\ fs []);

val lookup_vars_IMP = prove(
  ``!vs env xs env2.
      (lookup_vars vs env = SOME xs) /\
      env_rel t1.code env env2 ==>
      ?ys. (bEval (MAP Var vs,env2,t1) = (Result ys,t1)) /\
           EVERY2 (val_rel t1.code) xs ys /\
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
  ``res_rel code (Result x) (Result y)``
  |> SIMP_CONV (srw_ss()) [res_rel_cases]

val val_rel_Closure =
  ``val_rel code (Closure env exp) y``
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
      LIST_REL (val_rel code) xs ys ==>
      env_rel code xs (ys ++ ts)``,
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

val cComp_correct = prove(
  ``!xs env s1 n aux1 t1 env' res s2 n2 ys aux2.
      (cEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      (cComp n xs aux1 = (ys,aux2,n2)) /\
      code_installed aux2 t1.code /\
      env_rel t1.code env env' /\
      state_rel s1 t1 ==>
      ?res' t2.
         (bEval (ys,env',t1) = (res',t2)) /\
         res_rel t1.code res res' /\
         state_rel s2 t2``,

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
    \\ fs [res_rel_cases,val_rel_cases]
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
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `Block closure_tag (CodePtr n3::ys)::env'`)
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (fs [env_rel_def] \\ fs [val_rel_cases]
        \\ Q.LIST_EXISTS_TAC [`aux1`,`aux3`,`n`] \\ fs []
        \\ IMP_RES_TAC cComp_IMP_code_installed
        \\ fs [GSYM code_installed_def])
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.LIST_EXISTS_TAC [`res'`,`t2`] \\ fs []
      \\ Cases_on `res'` \\ fs []
      \\ IMP_RES_TAC bEval_IMP_LENGTH
      \\ Cases_on `a` \\ fs [] \\ Cases_on `t` \\ fs [LENGTH_NIL])
    (* general case for mutually recursive closures *)
    \\ cheat)

  THEN1 (* App *)
   (

    fs [cEval_def,cComp_def]
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
    \\ Cases_on `res'` \\ TRY (fs [res_rel_cases] \\ NO_TAC) \\ fs []
    \\ `t2.code = t1.code` by IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ `code_installed aux2 t2.code` by fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n7`,`aux7`,`t2`,`env'`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ REVERSE (Cases_on `res6`) \\ fs []
    \\ Cases_on `res'`
    \\ TRY (fs [res_rel_cases] \\ SRW_TAC [] [] \\ NO_TAC) \\ fs []
    \\ `?f1 y1 c1. (a = [f1]) /\ (a'' = [y1])` by METIS_TAC [cEval_SING]
    \\ fs [] \\ Cases_on `dest_closure f1 y1` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `x` \\ fs []
    \\ fs [bEval_def]
    \\ fs [res_rel_Result,DECIDE ``1 < SUC (1 + n:num)``]
    \\ Cases_on `f1` \\ fs [dest_closure_def] \\ SRW_TAC [] []
    THEN1 (* Closure case *)
     (fs [val_rel_Closure] \\ SRW_TAC [] []
      \\ fs [bEvalOp_def,find_code_def]
      \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel s6 t6` []
      \\ `t6.code = t2.code` by IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ `t6.clock = s6.clock` by fs [state_rel_def] \\ fs []
      \\ Cases_on `s6.clock = 0` \\ fs []
      THEN1 (SRW_TAC [] [res_rel_cases])
      \\ SIMP_TAC std_ss [bEval_def]
      \\ SIMP_TAC std_ss [Once bEval_CONS]
      \\ fs [bEval_def]
      \\ IMP_RES_TAC EVERY2_LENGTH
      \\ fs [bEval_free_let_Block]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n'`,`aux`,`dec_clock t6`])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `(dec_clock t6).code = t1.code` by (fs [dec_clock_def]) \\ fs []
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MATCH_MP_TAC
      \\ fs [env_rel_def]
      \\ IMP_RES_TAC list_rel_IMP_env_rel \\ fs []
      \\ fs [state_rel_def,closLangTheory.dec_clock_def,bvlTheory.dec_clock_def]
      \\ rfs [])
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
      \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel s6 t6` []
      \\ Q.PAT_ASSUM `val_rel t1.code (Recclosure cl_env [exp] 0) y` MP_TAC
      \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs [] \\ SRW_TAC [] []
      \\ fs [bEvalOp_def,find_code_def]
      \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ `t6.clock = s6.clock` by fs [state_rel_def] \\ fs []
      \\ Cases_on `s6.clock = 0` \\ fs []
      THEN1 SRW_TAC [] [res_rel_cases]
      \\ SIMP_TAC std_ss [bEval_def] \\ fs []
      \\ SIMP_TAC std_ss [Once bEval_CONS]
      \\ fs [bEval_def]
      \\ IMP_RES_TAC EVERY2_LENGTH
      \\ fs [bEval_free_let_Block]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n'`,`aux`,`dec_clock t6`])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `(dec_clock t6).code = t1.code` by (fs [dec_clock_def]) \\ fs []
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM MATCH_MP_TAC
      \\ fs [env_rel_def]
      \\ IMP_RES_TAC list_rel_IMP_env_rel \\ fs []
      \\ fs [state_rel_def,closLangTheory.dec_clock_def,bvlTheory.dec_clock_def]
      \\ rfs [] \\ fs [val_rel_cases] \\ METIS_TAC [])

    (* general case for mutually recursive closures *)
    \\ cheat)
  THEN1 (* Tick *) cheat
  THEN1 (* Call *) cheat);


(*
val _ = PolyML.SaveState.saveState "heap_state";
val _ = PolyML.SaveState.loadState "heap_state";
*)

val _ = export_theory();

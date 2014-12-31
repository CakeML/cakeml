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
  recc_Let n i =
    Let [Op (El 1) [Var 0]]
     (Let [Op (Cons closure_tag) [Op (Label n) []; Var 0]]
       (Let [Op Update [Var 1; Op (Const (&i)) []; Var 0]]
         (Var 1 : bvl_exp)))`;

val recc_Lets_def = Define `
  recc_Lets n k rest =
    if k = 0:num then rest else
      let k = k - 1 in
        Let [recc_Let (n + k) k] (recc_Lets n k rest)`;

val recc_Let0_def = Define `
  recc_Let0 n i =
    Let [Op (Cons closure_tag) [Op (Label n) []; Var 0]]
      (Let [Op Update [Var 1; Op (Const (&i)) []; Var 0]] (Var 1 : bvl_exp))`;

val build_recc_lets_def = Define `
  build_recc_lets (fns:clos_exp list) vs n1 fns_l (c3:bvl_exp) =
    Let [Let [Op Ref (MAP (K (Op (Const 0) [])) fns ++ MAP Var vs)]
           (recc_Let0 (n1 + (fns_l - 1)) (fns_l - 1))]
      (recc_Lets n1 (fns_l - 1) c3)`;

val cComp_def = tDefine "cComp" `
  (cComp [] aux = ([],aux)) /\
  (cComp ((x:clos_exp)::y::xs) aux =
     let (c1,aux1) = cComp [x] aux in
     let (c2,aux2) = cComp (y::xs) aux1 in
       (c1 ++ c2, aux2)) /\
  (cComp [Var v] aux = ([(Var v):bvl_exp], aux)) /\
  (cComp [If x1 x2 x3] aux =
     let (c1,aux1) = cComp [x1] aux in
     let (c2,aux2) = cComp [x2] aux1 in
     let (c3,aux3) = cComp [x3] aux2 in
       ([If (HD c1) (HD c2) (HD c3)],aux3)) /\
  (cComp [Let xs x2] aux =
     let (c1,aux1) = cComp xs aux in
     let (c2,aux2) = cComp [x2] aux1 in
       ([Let c1 (HD c2)], aux2)) /\
  (cComp [Raise x1] aux =
     let (c1,aux1) = cComp [x1] aux in
       ([Raise (HD c1)], aux1)) /\
  (cComp [Tick x1] aux =
     let (c1,aux1) = cComp [x1] aux in
       ([Tick (HD c1)], aux1)) /\
  (cComp [Op op xs] aux =
     let (c1,aux1) = cComp xs aux in
       ([Op op c1],aux1)) /\
  (cComp [App _ x1 x2] aux =
     let (c1,aux1) = cComp [x1] aux in
     let (c2,aux2) = cComp [x2] aux1 in
       ([Let (c1++c2)
           (Call NONE ((Var 1) ::          (* argument *)
                       (Var 0) ::          (* closure itself *)
                       [Op (El 0) [Var 0]] (* code pointer *)))],
        aux2)) /\
  (cComp [Fn loc vs x1] aux =
     let (c1,aux1) = cComp [x1] aux in
     let c2 = Let ((Var 0:bvl_exp) :: free_let (LENGTH vs)) (HD c1) in
       ([Op (Cons closure_tag) (Op (Label loc) [] :: MAP Var vs)],
        (loc,c2) :: aux1)) /\
  (cComp [Letrec loc vs fns x1] aux =
     case fns of
     | [] => cComp [x1] aux
     | [exp] =>
         let (c1,aux1) = cComp [exp] aux in
         let (c2,aux2) = cComp [x1] aux1 in
         let c3 = Let (Var 0 :: Var 1 :: free_let (LENGTH vs)) (HD c1) in
         let c4 = Op (Cons closure_tag) (Op (Label loc) [] :: MAP Var vs) in
           ([Let [c4] (HD c2)], (loc,c3) :: aux2)
     | _ =>
         let fns_l = LENGTH fns in
         let l = fns_l + LENGTH vs in
         let (cs,aux1) = cComp fns aux in
         let cs1 = MAP (code_for_recc_case l) cs in
         let (n2,aux2) = build_aux loc cs1 aux1 in
         let (c3,aux3) = cComp [x1] aux2 in
         let c4 = build_recc_lets fns vs loc fns_l (HD c3) in
           ([c4],aux3)) /\
  (cComp [Handle x1 x2] aux =
     let (c1,aux1) = cComp [x1] aux in
     let (c2,aux2) = cComp [x2] aux1 in
       ([Handle (HD c1) (HD c2)], aux2)) /\
  (cComp [Call dest xs] aux =
     let (c1,aux1) = cComp xs aux in
       ([Call (SOME dest) c1],aux1))`
 (WF_REL_TAC `measure (clos_exp1_size o FST)`
  \\ REPEAT STRIP_TAC \\ DECIDE_TAC);

(* correctness proof *)

val code_installed_def = Define `
  code_installed aux code =
    EVERY (\(n,exp). lookup n code = SOME (2:num,exp)) aux`;

val closure_code_installed_def = Define `
  closure_code_installed code exps_ps (env:clos_val list) =
    EVERY (\(exp,p).
      ?aux c aux1.
        (cComp [exp] aux = ([c],aux1)) /\
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
   (cComp [x] aux = ([c],aux1)) /\
   code_installed aux1 code /\
   (lookup p code = SOME (2:num,Let (Var 0::free_let (LENGTH env)) c)) ==>
   val_rel f refs code (Closure p env x) (Block closure_tag (CodePtr p :: ys)))
  /\
  (EVERY2 (val_rel f refs code) env ys /\
   (cComp [x] aux = ([c],aux1)) /\
   code_installed aux1 code /\
   (lookup p code = SOME (2:num,Let (Var 0::Var 1::free_let (LENGTH env)) c)) ==>
   val_rel f refs code (Recclosure p env [x] 0) (Block closure_tag (CodePtr p :: ys)))
  /\
  ((exps = MAP FST exps_ps) /\
   (ps = MAP SND exps_ps) /\ (ps = GENLIST (\n. loc + n) (LENGTH exps_ps)) /\
   (rs = MAP (\p. Block closure_tag [CodePtr p; RefPtr r]) ps) /\
   ~(r IN FRANGE f) /\
   (FLOOKUP refs r = SOME (ValueArray (rs ++ ys))) /\
   EVERY2 (val_rel f refs code) env ys /\
   1 < LENGTH exps /\ k < LENGTH exps /\
   closure_code_installed code exps_ps env ==>
   val_rel f refs code (Recclosure loc env exps k) (EL k rs))`

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
  (EVERY2 (val_rel f refs code) xs ys ==>
   ref_rel f refs code (ValueArray xs) (ValueArray ys))`

val state_rel_def = Define `
  state_rel f (s:clos_state) (t:bvl_state) <=>
    (s.clock = t.clock) /\
    (s.output = t.output) /\
    (EVERY2 (opt_val_rel f t.refs t.code) s.globals t.globals /\
    INJ ($' f) (FDOM f) (FRANGE f) /\
    (FDOM f = FDOM s.refs) /\
    (FRANGE f SUBSET FDOM t.refs) /\
    (!n x. (FLOOKUP s.refs n = SOME x) ==>
           ?y m. (FLOOKUP f n = SOME m) /\
                 (FLOOKUP t.refs m = SOME y) /\
                 ref_rel f t.refs t.code x y) /\
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?aux1 c2 aux2.
        (cComp [c] aux1 = ([c2],aux2)) /\
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
  THEN1 (Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
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

val val_rel_NEW_REF = prove(
  ``!x y. val_rel f1 refs1 code x y ==> ~(r IN FDOM refs1) ==>
          val_rel f1 (refs1 |+ (r,t)) code x y``,
  HO_MATCH_MP_TAC val_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`,`ys`] \\ fs []
  \\ rfs [] \\ Q.PAT_ASSUM `LIST_REL pppat env ys` MP_TAC
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ fs [FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ fs [])
  |> SPEC_ALL |> MP_CANON;

val val_rel_UPDATE_REF = prove(
  ``!x y. val_rel f1 refs1 code x y ==>
          (r IN FRANGE f1) ==>
          val_rel f1 (refs1 |+ (r,t)) code x y``,
  HO_MATCH_MP_TAC val_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r'`,`ys`] \\ fs []
  \\ rfs [] \\ Q.PAT_ASSUM `LIST_REL pppat env ys` MP_TAC
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ fs [FDIFF_def,SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ fs [FAPPLY_FUPDATE_THM] \\ SRW_TAC [] []
  \\ fs [FRANGE_DEF] \\ METIS_TAC [])
  |> SPEC_ALL |> MP_CANON;

val opt_val_rel_NEW_REF = prove(
  ``opt_val_rel f1 refs1 code x y /\ ~(r IN FDOM refs1) ==>
    opt_val_rel f1 (refs1 |+ (r,t)) code x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [opt_val_rel_def,val_rel_NEW_REF]);

val opt_val_rel_UPDATE_REF = prove(
  ``opt_val_rel f1 refs1 code x y /\ r IN FRANGE f1 ==>
    opt_val_rel f1 (refs1 |+ (r,t)) code x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [opt_val_rel_def,val_rel_UPDATE_REF]);

val env_rel_NEW_REF = prove(
  ``!x y.
      env_rel f1 refs1 code x y /\ ~(r IN FDOM refs1) ==>
      env_rel f1 (refs1 |+ (r,t)) code x y``,
  Induct \\ Cases_on `y` \\ fs [env_rel_def] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC val_rel_NEW_REF \\ fs []);

val FLOOKUP_FAPPLY = prove(
  ``FLOOKUP (f |+ (x,y)) n = if n = x then SOME y else FLOOKUP f n``,
  fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ fs []);

val val_rel_NEW_F = prove(
  ``!x y.
      val_rel f2 t2.refs t2.code x y ==>
      ~(pp IN FDOM f2) ==>
      ~(qq IN FDOM t2.refs) ==>
      val_rel (f2 |+ (pp,qq)) t2.refs t2.code x y``,
  HO_MATCH_MP_TAC val_rel_ind \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs []
  THEN1 (REPEAT (POP_ASSUM MP_TAC) \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (fs [FLOOKUP_FAPPLY] \\ SRW_TAC [] [] \\ fs [FLOOKUP_DEF])
  THEN1 (Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  THEN1 (DISJ1_TAC \\ Q.LIST_EXISTS_TAC [`aux`,`aux1`] \\ fs []
         \\ REPEAT (POP_ASSUM MP_TAC)
         \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ DISJ2_TAC \\ Q.LIST_EXISTS_TAC [`exps_ps`,`r`,`ys`] \\ fs []
  \\ rfs [] \\ Q.PAT_ASSUM `LIST_REL pppat env ys` MP_TAC
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [] \\ STRIP_TAC
  \\ REPEAT STRIP_TAC \\ fs [] \\ SRW_TAC [] []
  \\ fs [FLOOKUP_DEF]
  \\ fs [FRANGE_DEF,DOMSUB_FAPPLY_THM] \\ rfs []
  \\ METIS_TAC [])
  |> SPEC_ALL |> MP_CANON;

val opt_val_rel_NEW_F = prove(
  ``opt_val_rel f2 t2.refs t2.code x y ==>
    ~(pp IN FDOM f2) ==>
    ~(qq IN FDOM t2.refs) ==>
    opt_val_rel (f2 |+ (pp,qq)) t2.refs t2.code x y``,
  Cases_on `x` \\ Cases_on `y` \\ fs [opt_val_rel_def]
  \\ METIS_TAC [val_rel_NEW_F]) |> MP_CANON

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
  ``!xs aux.
      let (c,aux1) = cComp xs aux in
        (LENGTH c = LENGTH xs) /\ ?ys. aux1 = ys ++ aux``,
  recInduct (fetch "-" "cComp_ind") \\ REPEAT STRIP_TAC
  \\ fs [cComp_def] \\ SRW_TAC [] [] \\ fs [LET_DEF,ADD1]
  \\ REPEAT BasicProvers.FULL_CASE_TAC \\ rfs [] \\ fs []
  \\ fs [AC ADD_COMM ADD_ASSOC]
  \\ Cases_on `cComp [x] aux` \\ fs []
  \\ Cases_on `r` \\ fs [] \\ TRY DECIDE_TAC
  \\ Q.PAT_ASSUM `xxx = (c,aux1)` MP_TAC
  \\ Cases_on `t` \\ fs []
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  THEN1
   (`?tt. cComp [h] aux = tt` by fs [] \\ PairCases_on `tt` \\ fs []
    \\ `?t1. cComp [x1] (ys ++ aux) = t1` by fs []
    \\ PairCases_on `t1` \\ fs [] \\ rfs [] \\ fs [])
  \\ TRY
   (`?tt. cComp [h] aux = tt` by fs [] \\ PairCases_on `tt` \\ fs []
    \\ `?tu. cComp [x1] tt1 = tu` by fs [] \\ PairCases_on `tu` \\ fs []
    \\ SRW_TAC [] [] \\ NO_TAC)
  THEN1
   (`?tt. cComp [h] aux = tt` by fs [] \\ PairCases_on `tt` \\ fs []
    \\ `?t0. cComp (h'::t') tt1 = t0` by fs []
    \\ PairCases_on `t0` \\ fs []
    \\ `?t0. cComp (h::h'::t') aux = t0` by fs []
    \\ PairCases_on `t0` \\ fs []
    \\ Q.ABBREV_TAC `m = (MAP (code_for_recc_case
           (LENGTH vs + SUC (SUC (LENGTH t')))) t00')`
    \\ Cases_on `build_aux loc m t01'` \\ fs []
    \\ `?t2. cComp [x1] r = t2` by fs []
    \\ PairCases_on `t2` \\ fs []
    \\ ASSUME_TAC (Q.SPECL [`m`,`loc`,`t01'`] build_aux_lemma)
    \\ rfs [] \\ SRW_TAC [] []
    \\ rfs [] \\ SRW_TAC [] []
    \\ fs [cComp_def,LET_DEF] \\ SRW_TAC [] []
    \\ rfs [] \\ SRW_TAC [] []
    \\ fs [cComp_def,LET_DEF] \\ SRW_TAC [] [])
  THEN1
   (`?tt. cComp [h] aux = tt` by fs [] \\ PairCases_on `tt` \\ fs []
    \\ `?t0. cComp (h''::t'') tt1 = t0` by fs []
    \\ PairCases_on `t0` \\ fs []
    \\ `?t0. cComp (h::h''::t'') aux = t0` by fs []
    \\ PairCases_on `t0` \\ fs []
    \\ Q.ABBREV_TAC `m = (MAP (code_for_recc_case
           (LENGTH vs + SUC (SUC (LENGTH t'')))) t00')`
    \\ Cases_on `build_aux loc m t01'` \\ fs []
    \\ `?t2. cComp [x1] r = t2` by fs []
    \\ PairCases_on `t2` \\ fs []
    \\ ASSUME_TAC (Q.SPECL [`m`,`loc`,`t01'`] build_aux_lemma)
    \\ rfs [] \\ SRW_TAC [] []
    \\ rfs [] \\ SRW_TAC [] []
    \\ fs [cComp_def,LET_DEF] \\ SRW_TAC [] []
    \\ rfs [] \\ SRW_TAC [] []
    \\ fs [cComp_def,LET_DEF] \\ SRW_TAC [] []));

val cComp_LENGTH = prove(
  ``(cComp xs aux = (c,aux1)) ==> (LENGTH c = LENGTH xs)``,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`xs`,`aux`] cComp_lemma)
  \\ rfs [LET_DEF]);

val cComp_SING = prove(
  ``(cComp [x] aux = (c,aux1)) ==> ?d. c = [d]``,
  REPEAT STRIP_TAC
  \\ ASSUME_TAC (Q.SPECL [`[x]`,`aux`] cComp_lemma) \\ rfs [LET_DEF]
  \\ Cases_on `c` \\ fs [] \\ Cases_on `t` \\ fs []);

val res_rel_Result =
  ``res_rel f refs code (Result x) (Result y)``
  |> SIMP_CONV (srw_ss()) [res_rel_cases]

val res_rel_Result1 =
  ``res_rel f refs code (Result x) y``
  |> SIMP_CONV (srw_ss()) [res_rel_cases]

val res_rel_Ex =
  ``res_rel f refs code (Exception x) y``
  |> SIMP_CONV (srw_ss()) [res_rel_cases]

val val_rel_Closure =
  ``val_rel f refs code (Closure loc env exp) y``
  |> SIMP_CONV (srw_ss()) [val_rel_cases]

val val_rel_SIMP = LIST_CONJ
  [``val_rel f refs code (RefPtr p) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases],
   ``val_rel f refs code (Number i) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases],
   ``val_rel f refs code (Closure loc env exp) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases],
   ``val_rel f refs code (Recclosure loc env exp k) y``
   |> SIMP_CONV (srw_ss()) [val_rel_cases]]

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
  ``(cComp xs aux = (c,aux1)) /\
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

val bEval_MAP_Const = prove(
  ``!exps.
      bEval (MAP (K (Op (Const 0) [])) (exps:'a list),env,t1) =
        (Result (MAP (K (Number 0)) exps),t1)``,
  Induct \\ fs [bEval_def,bEval_CONS,bEvalOp_def]);

val bEval_recc_Lets = prove(
  ``!ll n n7 rr env' t1 ys c8.
     EVERY (\n. n7 + n IN domain t1.code) (GENLIST I (LENGTH ll)) ==>
     (bEval
       ([recc_Lets n7 (LENGTH ll) (HD c8)],
        Block closure_tag [CodePtr (n7 + LENGTH ll); RefPtr rr]::env',
        t1 with refs := t1.refs |+ (rr,
               ValueArray
               (MAP (K (Number 0)) ll ++
                Block closure_tag [CodePtr (n7 + LENGTH ll); RefPtr rr]::ys))) =
      bEval
       ([HD c8],
        GENLIST (\n. Block closure_tag [CodePtr (n7 + n); RefPtr rr])
                  (LENGTH ll + 1) ++ env',
        t1 with refs := t1.refs |+ (rr,
               ValueArray
               (GENLIST (\n. Block closure_tag [CodePtr (n7 + n); RefPtr rr])
                  (LENGTH ll + 1) ++ ys))))``,
  recInduct SNOC_INDUCT \\ fs [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [recc_Lets_def] \\ fs [LET_DEF]
  \\ fs [bEval_def,recc_Let_def,bEvalOp_def]
  \\ fs [DECIDE ``0 < k + SUC n:num``,EVERY_SNOC,GENLIST]
  \\ fs [FLOOKUP_FAPPLY,DECIDE ``n < SUC n + m``,DECIDE ``0 < 1 + SUC n``,
         DECIDE ``0 < 1 + n:num``,DECIDE ``2 < 1 + (1 + (1 + n:num))``]
  \\ FULL_SIMP_TAC std_ss [SNOC_APPEND,MAP_APPEND,MAP]
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ `LENGTH l = LENGTH ((MAP (K (Number 0)) l) : bc_value list)` by fs []
  \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
  \\ SIMP_TAC std_ss [LUPDATE_LENGTH] \\ fs []
  \\ FULL_SIMP_TAC std_ss [DECIDE ``SUC n + 1 = SUC (n+1)``,GENLIST]
  \\ FULL_SIMP_TAC std_ss [ADD1,SNOC_APPEND]
  \\ SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]) |> SPEC_ALL;

val NUM_NOT_IN_FDOM =
  MATCH_MP IN_INFINITE_NOT_FINITE (CONJ INFINITE_NUM_UNIV
    (Q.ISPEC `f:num|->'a` FDOM_FINITE))
  |> SIMP_RULE std_ss [IN_UNIV]

val EXISTS_NOT_IN_refs = prove(
  ``?x. ~(x IN FDOM (t1:bvl_state).refs)``,
  METIS_TAC [NUM_NOT_IN_FDOM])

val env_rel_APPEND = prove(
  ``!xs1 xs2.
      EVERY2 (val_rel f1 refs code) xs1 xs2 /\
      env_rel f1 refs code ys1 ys2 ==>
      env_rel f1 refs code (xs1 ++ ys1) (xs2 ++ ys2)``,
  Induct \\ Cases_on `xs2` \\ fs [env_rel_def]);

val EVERY2_GENLIST = prove(
  ``!n.
      (!k. k < n ==> P (f k) (g k)) ==>
      EVERY2 P (GENLIST f n) (GENLIST g n)``,
  Induct \\ fs [GENLIST] \\ REPEAT STRIP_TAC
  \\ fs [rich_listTheory.LIST_REL_APPEND_SING,SNOC_APPEND]
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ DECIDE_TAC);

val MAP_FST_ZIP = prove(
  ``!xs ys.
      (LENGTH xs = LENGTH ys) ==>
      (MAP FST (ZIP (xs,ys)) = xs) /\
      (MAP SND (ZIP (xs,ys)) = ys)``,
  Induct \\ Cases_on `ys` \\ fs []);

val EVERY_ZIP_GENLIST = prove(
  ``!xs.
      (!i. i < LENGTH xs ==> P (EL i xs,f i)) ==>
      EVERY P (ZIP (xs,GENLIST f (LENGTH xs)))``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ fs [GENLIST] \\ REPEAT STRIP_TAC
  \\ fs [rich_listTheory.ZIP_SNOC,EVERY_SNOC] \\ REPEAT STRIP_TAC
  THEN1
   (FIRST_X_ASSUM MATCH_MP_TAC \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EL_SNOC \\ fs []
    \\ `i < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC \\ METIS_TAC [])
  \\ `LENGTH xs < SUC (LENGTH xs)` by DECIDE_TAC \\ RES_TAC
  \\ fs [SNOC_APPEND,rich_listTheory.EL_LENGTH_APPEND]);

val build_aux_MEM = prove(
  ``!c n aux n7 aux7.
       (build_aux n c aux = (n7,aux7)) ==>
       !k. k < LENGTH c ==> ?d. MEM (n + k,d) aux7``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+1`,`(n,h)::aux`]) \\ fs []
  \\ REPEAT STRIP_TAC
  \\ Cases_on `k` \\ fs []
  THEN1 (MP_TAC (Q.SPECL [`c`,`n+1`,`(n,h)::aux`] build_aux_lemma) \\ fs []
         \\ REPEAT STRIP_TAC \\ fs [] \\ METIS_TAC [])
  \\ RES_TAC \\ fs [ADD1,AC ADD_COMM ADD_ASSOC] \\ METIS_TAC []);

val cComp_CONS = store_thm("cComp_CONS",
  ``!xs x aux.
      cComp (x::xs) aux =
      (let (c1,aux1) = cComp [x] aux in
       let (c2,aux2) = cComp xs aux1 in
         (c1 ++ c2,aux2))``,
  Cases_on `xs` \\ fs[cComp_def] \\ fs [LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val cComp_SNOC = store_thm("cComp_SNOC",
  ``!xs x aux.
      cComp (SNOC x xs) aux =
      (let (c1,aux1) = cComp xs aux in
       let (c2,aux2) = cComp [x] aux1 in
         (c1 ++ c2,aux2))``,
  Induct THEN1
   (fs [cComp_def,LET_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [])
  \\ fs [SNOC_APPEND]
  \\ ONCE_REWRITE_TAC [cComp_CONS]
  \\ ASM_SIMP_TAC std_ss [cComp_def,LET_DEF,APPEND_NIL]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs []);

val build_aux_APPEND = prove(
  ``!xs x n aux.
      build_aux n (xs ++ [x]) aux =
        let (n1,aux1) = build_aux n xs aux in
          (n1+1,(n1,x)::aux1)``,
  Induct \\ fs [build_aux_def,LET_DEF]);

val build_aux_MOVE = prove(
  ``!xs n aux n1 aux1.
      (build_aux n xs aux = (n1,aux1)) <=>
      ?aux2. (build_aux n xs [] = (n1,aux2)) /\ (aux1 = aux2 ++ aux)``,
  Induct THEN1 (fs [build_aux_def] \\ METIS_TAC [])
  \\ ONCE_REWRITE_TAC [build_aux_def]
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ fs [PULL_EXISTS]);

val build_aux_LENGTH = prove(
  ``!l n aux n1 t.
      (build_aux n l aux = (n1,t)) ==> (n1 = n + LENGTH l)``,
  Induct \\ fs [build_aux_def] \\ REPEAT STRIP_TAC \\ RES_TAC \\ DECIDE_TAC);

val cComp_LIST_IMP_cComp_EL = prove(
  ``!exps aux1 c7 aux7 i n8 n4 aux5.
      (cComp exps aux1 = (c7,aux7)) /\ i < LENGTH exps /\
      (build_aux n8 (MAP (code_for_recc_case k) c7) aux7 = (n4,aux5)) /\
      code_installed aux5 t1.code ==>
      ?aux c aux1'.
        cComp [EL i exps] aux = ([c],aux1') /\
        lookup (i + n8) t1.code =
        SOME (2,code_for_recc_case k c) /\
        code_installed aux1' t1.code``,
  HO_MATCH_MP_TAC SNOC_INDUCT \\ fs [] \\ REPEAT STRIP_TAC
  \\ Cases_on `i = LENGTH exps` \\ fs [] THEN1
   (fs [SNOC_APPEND,rich_listTheory.EL_LENGTH_APPEND]
    \\ fs [GSYM SNOC_APPEND,cComp_SNOC]
    \\ `?c1 aux2. cComp exps aux1 = (c1,aux2)` by METIS_TAC [PAIR]
    \\ `?c3 aux3. cComp [x] aux2 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ Q.LIST_EXISTS_TAC [`aux2`] \\ fs []
    \\ IMP_RES_TAC cComp_SING \\ fs []
    \\ fs [build_aux_APPEND]
    \\ IMP_RES_TAC cComp_LENGTH \\ fs []
    \\ Cases_on `build_aux n8 (MAP (code_for_recc_case k) c1) aux3`
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ fs [code_installed_def]
    \\ IMP_RES_TAC build_aux_LENGTH
    \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ MP_TAC (Q.SPECL [`MAP (code_for_recc_case k) c1`,`n8`,`aux3`]
           build_aux_lemma) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs [])
  \\ `i < LENGTH exps` by DECIDE_TAC
  \\ fs [EL_SNOC]
  \\ fs [cComp_SNOC]
  \\ `?c1 aux2. cComp exps aux1 = (c1,aux2)` by METIS_TAC [PAIR]
  \\ `?c3 aux3. cComp [x] aux2 = (c3,aux3)` by METIS_TAC [PAIR]
  \\ fs [LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
  \\ SRW_TAC [] [] \\ POP_ASSUM (MP_TAC o Q.SPECL [`i`,`n8`])
  \\ fs [] \\ REPEAT STRIP_TAC
  \\ IMP_RES_TAC cComp_SING \\ SRW_TAC [] []
  \\ fs [MAP,build_aux_APPEND]
  \\ Cases_on `build_aux n8 (MAP (code_for_recc_case k) c1) aux3`
  \\ fs [LET_DEF] \\ NTAC 2 (POP_ASSUM MP_TAC)
  \\ MP_TAC (Q.SPECL [`[x]`,`aux2`] cComp_lemma)
  \\ fs [LET_DEF] \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ POP_ASSUM MP_TAC
  \\ ONCE_REWRITE_TAC [build_aux_MOVE]
  \\ REPEAT STRIP_TAC \\ fs []
  \\ fs [code_installed_def]) |> SPEC_ALL;

val bEval_SING = prove(
  ``(bEval ([x],env,s) = (Result a,p1)) ==> ?d1. a = [d1]``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC bEval_IMP_LENGTH
  \\ Cases_on `a` \\ fs [LENGTH_NIL]);

val env_rel_IMP_LENGTH = prove(
  ``!env1 env2.
      env_rel f refs code env1 env2 ==>
      LENGTH env1 <= LENGTH env2``,
  Induct \\ Cases_on `env2` \\ fs [env_rel_def]);

val env_rel_IMP_EL = prove(
  ``!env1 env2 n.
      env_rel f refs code env1 env2 /\ n < LENGTH env1 ==>
      val_rel f refs code (EL n env1) (EL n env2)``,
  Induct \\ Cases_on `env2` \\ fs [env_rel_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ fs []);

val FDOM_FDIFF = prove(
  ``x IN FDOM (FDIFF refs f2) <=> x IN FDOM refs /\ ~(x IN FRANGE f2)``,
  fs [FDIFF_def,DRESTRICT_DEF]);

val EXISTS_NOT_IN_FDOM_LEMMA = prove(
  ``?x. ~(x IN FDOM (refs:num|->'a))``,
  METIS_TAC [NUM_NOT_IN_FDOM]);

val LEAST_NO_IN_FDOM = prove(
  ``(LEAST ptr. ptr NOTIN FDOM (refs:num|->'a)) NOTIN FDOM refs``,
  ASSUME_TAC (EXISTS_NOT_IN_FDOM_LEMMA |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs []);

val EVERY2_LUPDATE = prove(
  ``!xs ys P x y n.
      P x y /\ EVERY2 P xs ys ==>
      EVERY2 P (LUPDATE x n xs) (LUPDATE y n ys)``,
  Induct \\ Cases_on `ys` \\ fs [LUPDATE_def]
  \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ fs [LUPDATE_def]);

val EL_index_ps = prove(
  ``!exps_ps index exp p.
      (MAP SND exps_ps = GENLIST (\n. n0 + n) (LENGTH exps_ps)) /\
      index < LENGTH exps_ps /\ (EL index exps_ps = (exp,p)) ==>
      n0 + index = p``,
  recInduct SNOC_INDUCT \\ fs [] \\ REPEAT STRIP_TAC
  \\ fs [GENLIST,GSYM ADD1]
  \\ Cases_on `index = LENGTH l` \\ fs [EL_LENGTH_SNOC]
  \\ `index < LENGTH l` by DECIDE_TAC \\ fs []
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
  \\ fs [SNOC_APPEND,rich_listTheory.EL_APPEND1]);

val cEvalOp_correct = prove(
  ``(cEvalOp op xs s1 = SOME (v,s2)) /\
    state_rel f s1 t1 /\
    (op <> Ref) /\ (op <> Update) ==>
    ?w t2.
      (bEvalOp op ys t1 = SOME (w,t2)) /\
      val_rel f t1.refs t1.code v w /\
      state_rel f s2 t2 /\
      (t1.refs = t2.refs) /\ (t1.code = t2.code)``,
  cheat);

val cComp_correct = prove(
  ``!xs env s1 aux1 t1 env' f1 res s2 ys aux2.
      (cEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      (cComp xs aux1 = (ys,aux2)) /\
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
  THEN1 (* NIL *)
   (fs [cEval_def,cComp_def] \\ SRW_TAC [] [bEval_def]
    \\ Q.EXISTS_TAC `f1` \\ fs [res_rel_Result])
  THEN1 (* CONS *)
   (fs [cEval_def,cComp_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. cEval ([x],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?q. cEval (y::xs,env,p1) = q` by fs [] \\ PairCases_on `q` \\ fs []
    \\ `?cc. cComp [x] aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ `?dd. cComp (y::xs) cc1 = dd` by fs [] \\ PairCases_on `dd` \\ fs []
    \\ fs [LET_DEF,PULL_FORALL]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ SRW_TAC [] []
    \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ Q.PAT_ASSUM `!xx yy zz. bbb ==> b` (MP_TAC o Q.SPECL [`t1`,`env'`,`f1`])
    \\ IMP_RES_TAC cComp_SING \\ fs [] \\ REPEAT STRIP_TAC
    \\ ONCE_REWRITE_TAC [bEval_CONS]
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`cc1`]) \\ fs []
    \\ fs [res_rel_Result1] \\ SRW_TAC [] []
    \\ `q0 <> Error` by (Cases_on `q0` \\ fs []) \\ fs []
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t2`,`env'`,`f2`]) \\ fs []
    \\ IMP_RES_TAC env_rel_SUBMAP \\ fs [] \\ REPEAT STRIP_TAC
    \\ fs [] \\ IMP_RES_TAC bEval_SING \\ fs []
    \\ Cases_on `q0` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_cases] \\ Q.EXISTS_TAC `f2'`
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ IMP_RES_TAC val_rel_SUBMAP \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs []
    \\ Q.PAT_ASSUM `LIST_REL ppp yy tt` MP_TAC
    \\ MATCH_MP_TAC listTheory.LIST_REL_mono
    \\ METIS_TAC [val_rel_SUBMAP])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env` \\ fs [cComp_def,cEval_def]
    \\ IMP_RES_TAC env_rel_IMP_LENGTH
    \\ `n < LENGTH env'` by DECIDE_TAC
    \\ SRW_TAC [] [bEval_def,res_rel_cases]
    \\ Q.EXISTS_TAC `f1` \\ fs [SUBMAP_REFL]
    \\ MATCH_MP_TAC env_rel_IMP_EL \\ fs [])
  THEN1 (* If *)
   (fs [cComp_def,cEval_def]
    \\ `?c3 aux3. cComp [x1] aux1 = ([c3],aux3)` by
              METIS_TAC [PAIR,cComp_SING]
    \\ `?c4 aux4. cComp [x2] aux3 = ([c4],aux4)` by
              METIS_TAC [PAIR,cComp_SING]
    \\ `?c5 aux5. cComp [x3] aux4 = ([c5],aux5)` by
              METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. cEval ([x1],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env'`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ IMP_RES_TAC cEval_SING \\ SRW_TAC [] []
    \\ fs [res_rel_Result1]
    \\ Cases_on `Block 1 [] = r1` \\ fs [] THEN1
     (`Block 1 [] = y` by (SRW_TAC [] [] \\ fs [val_rel_cases] \\ NO_TAC)
      \\ fs [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`]) \\ fs []
      \\ REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`env'`,`f2`]) \\ fs []
      \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs []
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.EXISTS_TAC `f2'` \\ fs []
      \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
    \\ Cases_on `Block 0 [] = r1` \\ fs [] THEN1
     (`Block 0 [] = y` by (SRW_TAC [] [] \\ fs [val_rel_cases] \\ NO_TAC)
      \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux4`]) \\ fs []
      \\ REPEAT STRIP_TAC
      \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`env'`,`f2`]) \\ fs []
      \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs []
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.EXISTS_TAC `f2'` \\ fs []
      \\ IMP_RES_TAC SUBMAP_TRANS \\ fs []))
  THEN1 (* Let *)
   (fs [cComp_def,cEval_def]
    \\ `?c3 aux3. cComp xs aux1 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ `?c4 aux4. cComp [x2] aux3 = ([c4],aux4)` by
              METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. cEval (xs,env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env'`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`ys ++ env'`,`f2`]) \\ fs []
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (MATCH_MP_TAC env_rel_APPEND \\ fs []
      \\ IMP_RES_TAC env_rel_SUBMAP \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
  THEN1 (* Raise *)
   (fs [cEval_def,cComp_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. cEval ([x1],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?cc. cComp [x1] aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ fs [LET_DEF,PULL_FORALL] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ IMP_RES_TAC cComp_IMP_code_installed \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`env'`,`f1`])
    \\ IMP_RES_TAC cComp_SING \\ fs [] \\ SRW_TAC [] []
    \\ fs [bEval_def]
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1] \\ SRW_TAC [] []
    \\ IMP_RES_TAC cEval_SING \\ fs []
    \\ IMP_RES_TAC bEval_SING \\ fs [] \\ SRW_TAC [] []
    \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_cases])
  THEN1 (* Handle *)
   (fs [cComp_def,cEval_def]
    \\ `?c3 aux3. cComp [x1] aux1 = ([c3],aux3)` by METIS_TAC [PAIR,cComp_SING]
    \\ `?c4 aux4. cComp [x2] aux3 = ([c4],aux4)` by METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. cEval ([x1],env,s1) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env'`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Ex] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`t2`,`y'::env'`,`f2`]) \\ fs []
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
      (fs [env_rel_def] \\ IMP_RES_TAC env_rel_SUBMAP \\ fs [])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [])
  THEN1 (* Op *)
   (fs [cEval_def,cComp_def] \\ SRW_TAC [] [bEval_def]
    \\ `?p. cEval (xs,env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?cc. cComp xs aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ fs [LET_DEF,PULL_FORALL] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ IMP_RES_TAC cComp_IMP_code_installed \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1`,`env'`,`f1`])
    \\ IMP_RES_TAC cComp_SING \\ fs [] \\ SRW_TAC [] []
    \\ fs [bEval_def]
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1] \\ SRW_TAC [] []
    \\ Cases_on `cEvalOp op a p1` \\ fs []
    \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `op = Ref` \\ fs []
    THEN1
     (fs [cEvalOp_def,LET_DEF] \\ SRW_TAC [] [res_rel_Result1]
      \\ fs [PULL_EXISTS]
      \\ Q.ABBREV_TAC `pp = LEAST ptr. ptr NOTIN FDOM p1.refs`
      \\ Q.ABBREV_TAC `qq = LEAST ptr. ptr NOTIN FDOM t2.refs`
      \\ fs [bEvalOp_def,LET_DEF]
      \\ Q.EXISTS_TAC `f2 |+ (pp,qq)` \\ fs []
      \\ `~(pp IN FDOM p1.refs)` by
           (UNABBREV_ALL_TAC \\ fs [LEAST_NO_IN_FDOM] \\ NO_TAC)
      \\ `~(qq IN FDOM t2.refs)` by
           (UNABBREV_ALL_TAC \\ fs [LEAST_NO_IN_FDOM] \\ NO_TAC)
      \\ `~(pp IN FDOM f2)` by fs [state_rel_def]
      \\ `~(qq IN FRANGE f2)` by
        (REPEAT STRIP_TAC \\ fs [state_rel_def,SUBSET_DEF] \\ RES_TAC \\ NO_TAC)
      \\ `FRANGE (f2 \\ pp) = FRANGE f2` by ALL_TAC THEN1
       (fs [FRANGE_DEF,finite_mapTheory.DOMSUB_FAPPLY_THM,EXTENSION]
        \\ METIS_TAC []) \\ fs []
      \\ REPEAT STRIP_TAC
      THEN1 (fs [val_rel_cases,FLOOKUP_FAPPLY])
      THEN1
       (fs [state_rel_def,FLOOKUP_FAPPLY]
        \\ REPEAT STRIP_TAC THEN1
         (Q.PAT_ASSUM `LIST_REL ppp qqq rrr` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC opt_val_rel_NEW_REF \\ fs []
          \\ MATCH_MP_TAC opt_val_rel_NEW_F \\ fs [])
        THEN1
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM f2) (FRANGE f2)` MP_TAC
          \\ REPEAT (Q.PAT_ASSUM `INJ xx yy zz` (K ALL_TAC))
          \\ fs [INJ_DEF,FAPPLY_FUPDATE_THM,FRANGE_DEF]
          \\ REPEAT STRIP_TAC \\ METIS_TAC [])
        \\ Cases_on `n = pp` \\ fs [] THEN1
         (SRW_TAC [] [ref_rel_cases]
          \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) a ys` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC val_rel_NEW_REF \\ fs []
          \\ MATCH_MP_TAC val_rel_NEW_F \\ fs [])
        \\ RES_TAC \\ fs []
        \\ `qq <> m` by (REPEAT STRIP_TAC \\ fs [FLOOKUP_DEF] \\ SRW_TAC [] [])
        \\ fs [ref_rel_cases]
        \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) xs' ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC val_rel_NEW_REF \\ fs []
        \\ MATCH_MP_TAC val_rel_NEW_F \\ fs [])
      THEN1
       (fs [SUBMAP_DEF,FAPPLY_FUPDATE_THM] \\ SRW_TAC [] [] \\ METIS_TAC [])
      \\ MATCH_MP_TAC SUBMAP_TRANS
      \\ Q.EXISTS_TAC `FDIFF t2.refs f2` \\ fs []
      \\ fs [SUBMAP_DEF,FDOM_FDIFF]
      \\ REPEAT STRIP_TAC
      \\ fs [FDIFF_def,DRESTRICT_DEF]
      \\ SRW_TAC [] [] \\ fs [state_rel_def,SUBSET_DEF])
    \\ Cases_on `op = Update` \\ fs [] THEN1
     (fs [cEvalOp_def,bEvalOp_def]
      \\ Cases_on `a` \\ fs []
      \\ Cases_on `t` \\ fs []
      \\ Cases_on `t'` \\ fs []
      \\ Cases_on `t` \\ fs []
      \\ Cases_on `h` \\ fs []
      \\ Cases_on `h'` \\ fs []
      \\ Cases_on `FLOOKUP p1.refs n` \\ fs []
      \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
      \\ fs [val_rel_SIMP] \\ SRW_TAC [] []
      \\ `?y m.
            FLOOKUP f2 n = SOME m /\ FLOOKUP t2.refs m = SOME y /\
            ref_rel f2 t2.refs t2.code (ValueArray l) y` by
              METIS_TAC [state_rel_def]
      \\ fs [] \\ SRW_TAC [] []
      \\ fs [ref_rel_cases] \\ SRW_TAC [] []
      \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_cases] \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
      THEN1
       (MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
        \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      THEN1
       (fs [state_rel_def,FLOOKUP_FAPPLY] \\ REPEAT STRIP_TAC
        THEN1
         (Q.PAT_ASSUM `LIST_REL tt yy t2.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC opt_val_rel_UPDATE_REF \\ fs []
          \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        THEN1 (fs [EXTENSION,FLOOKUP_DEF] \\ METIS_TAC [])
        THEN1
         (`m IN FRANGE f2` by (fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ fs [SUBSET_DEF] \\ METIS_TAC [])
        \\ SRW_TAC [] [] \\ Cases_on `n' = n` \\ fs [] \\ SRW_TAC [] []
        THEN1
         (fs [ref_rel_cases]
          \\ MATCH_MP_TAC EVERY2_LUPDATE
          \\ REPEAT STRIP_TAC THEN1
           (MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
            \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
          \\ Q.PAT_ASSUM `LIST_REL (val_rel f2 t2.refs t2.code) l ys` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ REPEAT STRIP_TAC
          \\ MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
          \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
        \\ RES_TAC \\ fs []
        \\ `m' <> m''` by
         (Q.PAT_ASSUM `INJ ($' f2) (FDOM p1.refs) (FRANGE f2)` MP_TAC
          \\ SIMP_TAC std_ss [INJ_DEF,FRANGE_DEF] \\ fs [FLOOKUP_DEF]
          \\ METIS_TAC [])
        \\ fs [] \\ SRW_TAC [] [] \\ fs [ref_rel_cases] \\ SRW_TAC [] []
        \\ Q.PAT_ASSUM `LIST_REL pp xs' ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ REPEAT STRIP_TAC
        \\ MATCH_MP_TAC val_rel_UPDATE_REF \\ fs []
        \\ fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ `m IN FRANGE f2` by (fs [FLOOKUP_DEF,FRANGE_DEF] \\ METIS_TAC [])
      \\ fs [SUBMAP_DEF,FDIFF_def,DRESTRICT_DEF,FAPPLY_FUPDATE_THM])
    \\ IMP_RES_TAC cEvalOp_correct \\ POP_ASSUM (K ALL_TAC)
    \\ POP_ASSUM (MP_TAC o Q.SPEC `ys`) \\ SRW_TAC [] [] \\ fs []
    \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_Result])
  THEN1 (* Fn *)
   (fs [cEval_def] \\ BasicProvers.FULL_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [cComp_def]
    \\ `?c2 aux3. cComp [exp] aux1 = (c2,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ fs [code_installed_def]
    \\ fs [bEval_def,bEval_CONS,bEvalOp_def,domain_lookup]
    \\ IMP_RES_TAC lookup_vars_IMP
    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `t1`)
    \\ fs [res_rel_cases,val_rel_cases]
    \\ Q.EXISTS_TAC `f1` \\ fs []
    \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
    \\ Q.LIST_EXISTS_TAC [`aux1`,`aux3`] \\ fs []
    \\ IMP_RES_TAC cComp_SING \\ fs [code_installed_def])
  THEN1 (* Letrec *)
   (fs [cEval_def] \\ BasicProvers.FULL_CASE_TAC
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [cComp_def]
    \\ fs [build_recc_def]
    \\ Cases_on `lookup_vars names env` \\ fs [] \\ SRW_TAC [] []
    \\ Cases_on `fns` \\ fs []
    THEN1 (rfs [] \\ FIRST_X_ASSUM MATCH_MP_TAC
           \\ Q.LIST_EXISTS_TAC [`aux1`] \\ fs [])
    \\ Cases_on `t` \\ fs [] \\ rfs []
    THEN1 (* special case for singly-recursive closure *)
     (`?c2 aux3. cComp [h] aux1 = ([c2],aux3)` by
              METIS_TAC [PAIR,cComp_SING]
      \\ `?c3 aux4. cComp [exp] aux3 = ([c3],aux4)` by
              METIS_TAC [PAIR,cComp_SING]
      \\ fs [LET_DEF] \\ SRW_TAC [] []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux3`,`t1`]) \\ fs []
      \\ fs [code_installed_def] \\ REPEAT STRIP_TAC
      \\ fs [bEval_def,bEvalOp_def,domain_lookup]
      \\ ONCE_REWRITE_TAC [bEval_CONS]
      \\ fs [bEval_def,bEvalOp_def,domain_lookup]
      \\ IMP_RES_TAC lookup_vars_IMP \\ fs []
      \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `t1`) \\ fs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL
           [`Block closure_tag (CodePtr loc::ys)::env'`,`f1`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (fs [env_rel_def] \\ fs [val_rel_cases] \\ DISJ1_TAC
        \\ Q.LIST_EXISTS_TAC [`aux1`,`aux3`] \\ fs []
        \\ IMP_RES_TAC cComp_IMP_code_installed
        \\ fs [GSYM code_installed_def])
      \\ REPEAT STRIP_TAC \\ fs []
      \\ Q.LIST_EXISTS_TAC [`res'`,`t2`,`f2`] \\ fs []
      \\ Cases_on `res'` \\ fs []
      \\ IMP_RES_TAC bEval_IMP_LENGTH
      \\ Cases_on `a` \\ fs [] \\ Cases_on `t` \\ fs [LENGTH_NIL])
    (* general case for mutually recursive closures *)
    \\ `0 < LENGTH (h::h'::t') /\ 1 < LENGTH (h::h'::t')` by (fs [] \\ DECIDE_TAC)
    \\ `SUC (SUC (LENGTH t')) = LENGTH (h::h'::t')` by fs []
    \\ Q.ABBREV_TAC `exps = h::h'::t'` \\ fs []
    \\ NTAC 2 (POP_ASSUM (K ALL_TAC)) \\ fs [LET_DEF]
    \\ `?c7 aux7. cComp exps aux1 = (c7,aux7)` by METIS_TAC [PAIR]
    \\ `?n4 aux5. build_aux loc
           (MAP (code_for_recc_case (LENGTH exps + LENGTH names)) c7)
           aux7 = (n4,aux5)` by METIS_TAC [PAIR]
    \\ `?c8 aux8. cComp [exp] aux5 = (c8,aux8)` by METIS_TAC [PAIR]
    \\ fs [] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux5`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ fs [build_recc_lets_def]
    \\ fs [bEvalOp_def,bEval_def,LET_DEF]
    \\ fs [bEval_APPEND,bEval_MAP_Const]
    \\ IMP_RES_TAC lookup_vars_IMP
    \\ POP_ASSUM (MP_TAC o Q.SPEC `t1`) \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.ABBREV_TAC `rr = LEAST ptr. ptr NOTIN FDOM t1.refs`
    \\ fs [recc_Let0_def]
    \\ `loc + (LENGTH exps - 1) IN domain t1.code` by
     (IMP_RES_TAC cComp_IMP_code_installed
      \\ IMP_RES_TAC cComp_LENGTH
      \\ POP_ASSUM (fn th => fs [GSYM th])
      \\ fs [domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ fs []
      \\ `LENGTH c7 - 1 < LENGTH c7` by DECIDE_TAC
      \\ RES_TAC
      \\ fs [code_installed_def,EVERY_MEM] \\ fs []
      \\ RES_TAC \\ fs [])
    \\ fs [bEval_def,bEvalOp_def,DECIDE ``1 < m + 1 + SUC n``,
           DECIDE ``0 < 1 + SUC n``, DECIDE ``1 < n + (1 + SUC m)``,
           DECIDE ``m < 1 + (m + n):num``]
    \\ `0 < LENGTH exps + LENGTH ys` by DECIDE_TAC
    \\ ASM_SIMP_TAC (srw_ss()) [FLOOKUP_DEF, DECIDE ``n < 1 + (n + m):num``]
    \\ `exps <> []` by (fs [GSYM LENGTH_NIL] \\ DECIDE_TAC)
    \\ `?ll x. exps = SNOC x ll` by METIS_TAC [SNOC_CASES] \\ fs []
    \\ `LENGTH ll = LENGTH ((MAP (K (Number 0)) ll) : bc_value list)`
         by fs [LENGTH_MAP]
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ SIMP_TAC std_ss [APPEND,GSYM APPEND_ASSOC,LUPDATE_LENGTH]
    \\ `EVERY (\n. loc + n IN domain t1.code) (GENLIST I (LENGTH ll))` by
     (fs [EVERY_GENLIST]
      \\ IMP_RES_TAC cComp_IMP_code_installed
      \\ IMP_RES_TAC cComp_LENGTH
      \\ POP_ASSUM (fn th => fs [GSYM th])
      \\ fs [domain_lookup,code_installed_def]
      \\ IMP_RES_TAC build_aux_MEM \\ fs []
      \\ REPEAT STRIP_TAC
      \\ `i < LENGTH c7` by ALL_TAC THEN1
       (`LENGTH ll <= LENGTH c7` by ALL_TAC
        \\ IMP_RES_TAC cComp_LENGTH \\ fs [LENGTH_APPEND]
        \\ DECIDE_TAC)
      \\ RES_TAC
      \\ fs [code_installed_def,EVERY_MEM] \\ fs []
      \\ RES_TAC \\ fs [])
    \\ fs [bEval_recc_Lets]
    \\ Q.PAT_ABBREV_TAC `t1_refs  = t1 with refs := t1.refs |+ xxx`
    \\ `[HD c8] = c8` by (IMP_RES_TAC cComp_SING \\ fs []) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t1_refs`,
       `GENLIST (\n. Block closure_tag [CodePtr (loc + n); RefPtr rr])
          (LENGTH (ll:clos_exp list) + 1) ++ env'`,`f1`])
    \\ `~(rr IN FDOM t1.refs)` by ALL_TAC THEN1
     (UNABBREV_ALL_TAC
      \\ SIMP_TAC std_ss [FDIFF_def,SUBMAP_DEF]
      \\ fs [DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
      \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
      \\ ASSUME_TAC (EXISTS_NOT_IN_refs |>
           SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs [])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    THEN1
     (`t1_refs.code = t1.code` by fs [Abbr`t1_refs`] \\ fs []
      \\ REVERSE (REPEAT STRIP_TAC) THEN1
       (fs [state_rel_def,Abbr`t1_refs`] \\ STRIP_TAC THEN1
         (Q.PAT_ASSUM `LIST_REL ppp s.globals t1.globals` MP_TAC
          \\ MATCH_MP_TAC listTheory.LIST_REL_mono
          \\ METIS_TAC [opt_val_rel_NEW_REF])
        \\ STRIP_TAC THEN1 fs [SUBSET_DEF]
        \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs [FLOOKUP_FAPPLY]
        \\ `m <> rr` by (REPEAT STRIP_TAC \\ fs [FLOOKUP_DEF]) \\ fs []
        \\ fs [ref_rel_cases]
        \\ Q.PAT_ASSUM `LIST_REL ppp xs ys'` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ IMP_RES_TAC val_rel_NEW_REF \\ fs [])
      \\ `LENGTH ll + 1 = LENGTH exps` by fs []
      \\ POP_ASSUM (fn th => FULL_SIMP_TAC std_ss [th])
      \\ `1 < LENGTH exps` by (fs [] \\ DECIDE_TAC)
      \\ Q.PAT_ASSUM `exps = ll ++ [x]` (fn th => FULL_SIMP_TAC std_ss [GSYM th])
      \\ MATCH_MP_TAC env_rel_APPEND
      \\ REVERSE STRIP_TAC THEN1
       (UNABBREV_ALL_TAC \\ fs []
        \\ MATCH_MP_TAC (env_rel_NEW_REF |> GEN_ALL) \\ fs [])
      \\ MATCH_MP_TAC EVERY2_GENLIST \\ REPEAT STRIP_TAC \\ fs []
      \\ ONCE_REWRITE_TAC [val_rel_cases] \\ fs [] \\ DISJ2_TAC
      \\ Q.EXISTS_TAC `ZIP (exps,GENLIST (\i.loc+i) (LENGTH exps))`
      \\ fs [LENGTH_ZIP]
      \\ Q.LIST_EXISTS_TAC [`rr`,`ys`] \\ fs [Abbr `t1_refs`,FLOOKUP_FAPPLY]
      \\ fs [MAP_FST_ZIP] \\ fs [MAP_GENLIST,o_DEF]
      \\ REPEAT STRIP_TAC
      THEN1 (fs [state_rel_def,SUBSET_DEF] \\ RES_TAC)
      THEN1
       (Q.PAT_ASSUM `LIST_REL (val_rel f1 t1.refs t1.code) x' ys` MP_TAC
        \\ MATCH_MP_TAC listTheory.LIST_REL_mono
        \\ METIS_TAC [val_rel_NEW_REF])
      \\ fs [closure_code_installed_def]
      \\ MATCH_MP_TAC EVERY_ZIP_GENLIST \\ fs [AC ADD_ASSOC ADD_COMM]
      \\ REPEAT STRIP_TAC
      \\ IMP_RES_TAC cComp_IMP_code_installed
      \\ MATCH_MP_TAC cComp_LIST_IMP_cComp_EL \\ fs [])
    \\ REPEAT STRIP_TAC
    \\ fs [] \\ Q.EXISTS_TAC `f2` \\ IMP_RES_TAC SUBMAP_TRANS
    \\ ASM_SIMP_TAC std_ss []
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ UNABBREV_ALL_TAC
    \\ SIMP_TAC std_ss [FDIFF_def,SUBMAP_DEF]
    \\ fs [DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
    \\ REPEAT STRIP_TAC \\ SRW_TAC [] []
    \\ ASSUME_TAC (EXISTS_NOT_IN_refs |>
         SIMP_RULE std_ss [whileTheory.LEAST_EXISTS]) \\ fs [])
  THEN1 (* App *)
   (fs [cEval_def,cComp_def]
    \\ `?res5 s5. cEval ([x1],env,s) = (res5,s5)` by METIS_TAC [PAIR]
    \\ `?res6 s6. cEval ([x2],env,s5) = (res6,s6)` by METIS_TAC [PAIR]
    \\ `?c7 aux7. cComp [x1] aux1 = ([c7],aux7)` by
          METIS_TAC [PAIR,cComp_SING]
    \\ `?c8 aux8. cComp [x2] aux7 = ([c8],aux8)` by
          METIS_TAC [PAIR,cComp_SING]
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ ONCE_REWRITE_TAC [bEval_def]
    \\ SIMP_TAC std_ss [Once bEval_def]
    \\ REVERSE (Cases_on `res5`) \\ fs []
    \\ SRW_TAC [] []
    \\ `code_installed aux7 t1.code` by IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`,`env'`,`f1`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `res'`
    \\ TRY (fs [res_rel_cases]
         \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC) \\ fs []
    \\ `t2.code = t1.code` by IMP_RES_TAC bvl_inlineTheory.bEval_code
    \\ `code_installed aux2 t2.code` by fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux7`,`t2`,`env'`,`f2`]) \\ fs []
    \\ `env_rel f2 t2.refs t1.code env env'` by
          (MATCH_MP_TAC env_rel_SUBMAP \\ METIS_TAC []) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ REVERSE (Cases_on `res6`) \\ fs []
    \\ Cases_on `res'`
    \\ TRY (fs [res_rel_cases] \\ SRW_TAC [] []
            \\ Q.EXISTS_TAC `f2'` \\ IMP_RES_TAC SUBMAP_TRANS
            \\ fs [] \\ NO_TAC) \\ fs []
    \\ `?g1 y1 c1. (a = [g1]) /\ (a'' = [y1])` by METIS_TAC [cEval_SING]
    \\ fs [] \\ Cases_on `dest_closure loc_opt g1 y1` \\ fs [] \\ SRW_TAC [] []
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
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux`,`dec_clock t6`])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `(dec_clock t6).code = t1.code` by (fs [dec_clock_def]) \\ fs []
      \\ `(dec_clock t6).refs = t6.refs` by (fs [dec_clock_def]) \\ fs []
      \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
      \\ POP_ASSUM (MP_TAC o Q.SPECL
           [`y'::(ys ++ [y'; Block closure_tag (CodePtr n::ys)])`,`f6`])
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
      \\ Q.PAT_ASSUM `val_rel f2 t2.refs t1.code
           (Recclosure n0 cl_env [exp] 0) y` MP_TAC
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
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux`,`dec_clock t6`])
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ `(dec_clock t6).code = t1.code` by (fs [dec_clock_def]) \\ fs []
      \\ Q.ABBREV_TAC `bb = Block closure_tag (CodePtr n0::ys)`
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
         ASSUME_TAC (REWRITE_RULE [closure_code_installed_def] th))
    \\ fs [EVERY_MEM]
    \\ `MEM (EL index exps_ps) exps_ps` by METIS_TAC [MEM_EL]
    \\ FIRST_ASSUM (MP_TAC o Q.SPEC `EL index exps_ps`)
    \\ POP_ASSUM (fn th => SIMP_TAC std_ss [th])
    \\ `?exp p. EL index exps_ps = (exp,p)` by METIS_TAC [PAIR]
    \\ ASM_SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `state_rel f6 s6 t6` []
    \\ `t6.clock = s6.clock` by fs [state_rel_def]
    \\ `n0 + index = p` by METIS_TAC [EL_index_ps]
    \\ Cases_on `t6.clock = 0` \\ fs []
    THEN1 (Q.EXISTS_TAC `f6` \\ IMP_RES_TAC SUBMAP_TRANS
           \\ SRW_TAC [] [res_rel_cases])
    \\ rfs [] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux`,`dec_clock t6`]) \\ fs []
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
      \\ `MAP (\x. Block closure_tag [CodePtr (SND x); RefPtr r]) exps_ps =
          MAP (\x. Block closure_tag [CodePtr x; RefPtr r]) (MAP SND exps_ps)`
           by (fs [MAP_MAP_o,o_DEF]) \\ fs []
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
  THEN1 (* Tick *)
   (fs [cComp_def]
    \\ `?p. cEval ([x],env,s) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ `?cc. cComp [x] aux1 = cc` by fs [] \\ PairCases_on `cc` \\ fs []
    \\ fs [LET_DEF] \\ SRW_TAC [] []
    \\ IMP_RES_TAC cComp_SING \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `t1.clock = s.clock` by fs [state_rel_def] \\ fs []
    \\ Cases_on `s.clock = 0` \\ fs [] THEN1
     (fs [cEval_def] \\ SRW_TAC [] [res_rel_cases]
      \\ Q.EXISTS_TAC `f1` \\ fs [SUBMAP_REFL])
    \\ fs [cEval_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`dec_clock t1`,`env'`,`f1`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
      (fs [dec_clock_def,state_rel_def,closLangTheory.dec_clock_def])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.EXISTS_TAC `f2` \\ fs [dec_clock_def])
  THEN1 (* Call *)
   (fs [cComp_def,cEval_def]
    \\ `?c3 aux3. cComp xs aux1 = (c3,aux3)` by METIS_TAC [PAIR]
    \\ fs [LET_DEF] \\ SRW_TAC [] [] \\ fs [bEval_def]
    \\ `?p. cEval (xs,env,s1) = p` by fs [] \\ PairCases_on `p` \\ fs []
    \\ SRW_TAC [] [] \\ IMP_RES_TAC cComp_IMP_code_installed
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1`,`t1`])
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`env'`,`f1`]) \\ fs []
    \\ REVERSE (Cases_on `p0`) \\ fs [] \\ SRW_TAC [] []
    \\ TRY (fs [res_rel_cases] \\ Q.EXISTS_TAC `f2` \\ fs [] \\ NO_TAC)
    \\ fs [res_rel_Result1]
    \\ fs [closLangTheory.find_code_def,bvlTheory.find_code_def]
    \\ Cases_on `FLOOKUP p1.code dest` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ Cases_on `q = LENGTH a` \\ fs []
    \\ `?aux1 c2 aux2.
          cComp [r] aux1 = ([c2],aux2) /\
          lookup dest t2.code = SOME (LENGTH a,c2) /\
          code_installed aux2 t2.code` by METIS_TAC [state_rel_def]
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ `t2.clock = p1.clock` by fs [state_rel_def]
    \\ Cases_on `t2.clock = 0` \\ fs []
    THEN1 (SRW_TAC [] [] \\ Q.EXISTS_TAC `f2` \\ fs [res_rel_cases])
    \\ fs [] \\ rfs [] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`aux1'`]) \\ fs []
    \\ REPEAT STRIP_TAC
    \\ POP_ASSUM (MP_TAC o Q.SPECL [`dec_clock t2`,`ys`,`f2`]) \\ fs []
    \\ IMP_RES_TAC bvl_inlineTheory.bEval_code \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [closLangTheory.dec_clock_def,state_rel_def,bvlTheory.dec_clock_def]
      \\ IMP_RES_TAC list_rel_IMP_env_rel \\ METIS_TAC [APPEND_NIL])
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Q.EXISTS_TAC `f2'` \\ fs []
    \\ IMP_RES_TAC SUBMAP_TRANS \\ fs [dec_clock_def]));

val _ = export_theory();

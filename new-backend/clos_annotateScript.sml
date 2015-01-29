open HolKernel Parse boolLib bossLib;
open pred_setTheory arithmeticTheory pairTheory listTheory combinTheory;
open finite_mapTheory sumTheory relationTheory stringTheory optionTheory;
open lcsymtacs closLangTheory sptreeTheory db_varsTheory;
open clos_numberTheory;

val _ = new_theory "clos_annotate";

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
     clos_free n [x1] \/ clos_free n x2) /\
  (clos_free n [Fn loc vs num_args x1] <=>
     clos_free (n + num_args) [x1]) /\
  (clos_free n [Letrec loc vs fns x1] <=>
     EXISTS (\(num_args, x). clos_free (n + num_args + LENGTH fns) [x]) fns \/ clos_free (n + LENGTH fns) [x1]) /\
  (clos_free n [Handle x1 x2] <=>
     clos_free n [x1] \/ clos_free (n+1) [x2]) /\
  (clos_free n [Call dest xs] <=> clos_free n xs)`
 (WF_REL_TAC `measure (clos_exp3_size o SND)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC \\
  Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  res_tac >>
  srw_tac [ARITH_ss] [clos_exp_size_def]);

val clos_exp_ind =
  theorem "clos_free_ind" |> Q.SPEC `K P` |> SIMP_RULE std_ss []

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
  (cFree [App loc_opt x1 xs2] =
     let (c1,l1) = cFree [x1] in
     let (c2,l2) = cFree xs2 in
       ([App loc_opt (HD c1) c2],mk_Union l1 l2)) /\
  (cFree [Fn loc vs num_args x1] =
     let (c1,l1) = cFree [x1] in
     let l2 = Shift num_args l1 in
       ([Fn loc (vars_to_list l2) num_args (HD c1)],l2)) /\
  (cFree [Letrec loc vs fns x1] =
     let (c1,l1) = cFree (MAP SND fns) in
     let l3 = Shift (1 + LENGTH fns) l1 in
     let (c2,l2) = cFree [x1] in
       ([Letrec loc (vars_to_list l3) (ZIP (MAP FST fns, c1)) (HD c2)],
        mk_Union l3 (Shift (LENGTH fns) l2))) /\
  (cFree [Handle x1 x2] =
     let (c1,l1) = cFree [x1] in
     let (c2,l2) = cFree [x2] in
       ([Handle (HD c1) (HD c2)],mk_Union l1 (Shift 1 l2))) /\
  (cFree [Call dest xs] =
     let (c1,l1) = cFree xs in
       ([Call dest c1],l1))`
 (WF_REL_TAC `measure clos_exp3_size`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC \\
  Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  Cases_on `h` >>
  srw_tac [ARITH_ss] [clos_exp_size_def]);

  

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

val SING_HD = store_thm("SING_HD",
  ``(([HD xs] = xs) <=> (LENGTH xs = 1)) /\
    ((xs = [HD xs]) <=> (LENGTH xs = 1))``,
  Cases_on `xs` \\ fs [LENGTH_NIL] \\ METIS_TAC []);

val LENGTH_FST_cFree = store_thm("LENGTH_FST_cFree",
  ``LENGTH (FST (cFree fns)) = LENGTH fns``,
  Cases_on `cFree fns` \\ fs [] \\ IMP_RES_TAC cFree_LENGTH);

val cFree_CONS = prove(
  ``FST (cFree (x::xs)) = HD (FST (cFree [x])) :: FST (cFree xs)``,
  Cases_on `xs` \\ fs [cFree_def,SING_HD,LENGTH_FST_cFree,LET_DEF]
  \\ Cases_on `cFree [x]` \\ fs []
  \\ Cases_on `cFree (h::t)` \\ fs [SING_HD]
  \\ IMP_RES_TAC cFree_SING \\ fs []);

val has_var_mk_Union = prove(
  ``has_var n (mk_Union l1 l2) <=> has_var n l1 \/ has_var n l2``,
  SRW_TAC [] [mk_Union_def,has_var_def]);

val _ = augment_srw_ss [rewrites [has_var_mk_Union, has_var_def]];

val cFree_thm = prove(
  ``!xs.
      let (ys,l) = cFree xs in
        !n. (clos_free n ys = has_var n l) /\
            (clos_free n xs = has_var n l)``,
  recInduct cFree_ind \\ REPEAT STRIP_TAC \\ fs [cFree_def,LET_DEF]
  \\ TRY (fs [has_var_def,clos_free_def] \\ NO_TAC)
  THEN1 (* cons *)
   (`?y1 l1. cFree [x] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
    \\ `?y2 l2. cFree (y::xs) = (y2,l2)` by METIS_TAC [PAIR] \\ fs []
    \\ IMP_RES_TAC cEval_const \\ rfs [] \\ RES_TAC
    \\ IMP_RES_TAC cFree_LENGTH
    \\ Cases_on `y2` \\ fs [has_var_def,clos_free_def])
  \\ `?y1 l1. cFree (MAP SND fns) = (y1,l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y1 l1. cFree [x1] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y1 l1. cFree xs = (y1,l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y1 l1. cFree xs2 = (y1,l1)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y2 l2. cFree [x2] = ([y2],l2)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ `?y3 l3. cFree [x3] = ([y3],l3)` by METIS_TAC [PAIR,cFree_SING] \\ fs []
  \\ rfs [] \\ RES_TAC \\ IMP_RES_TAC cFree_LENGTH \\ fs []
  \\ fs [has_var_def,clos_free_def,MEM_vars_to_list]
  \\ fs [AC ADD_ASSOC ADD_COMM, MAP_ZIP])
  |> SPEC_ALL;

(* cShift renames variables to use only those in the annotations *)

val tlookup_def = Define `
  tlookup m k = case lookup m k of NONE => 0:num | SOME k => k`;

val get_var_def = Define `
  get_var m l i v =
    if v < l then v else l + tlookup (v - l) i`;

val index_of_def = Define `
  (index_of x [] = 0:num) /\
  (index_of x (y::ys) = if x = y then 0 else 1 + index_of x ys)`;

val new_env_def = Define `
  (new_env n [] = LN) /\
  (new_env n (x::xs) = insert x (n:num) (new_env (n+1) xs))`;

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
  (cShift [App loc_opt x1 xs2] m l i =
     let c1 = cShift [x1] m l i in
     let c2 = cShift xs2 m l i in
       ([App loc_opt (HD c1) c2])) /\
  (cShift [Fn loc vs num_args x1] m l i =
     let k = m + l in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let c1 = cShift [x1] (m + l) 1 (new_env 0 live) in
       ([Fn loc vars num_args (HD c1)])) /\
  (cShift [Letrec loc vs fns x1] m l i =
     let k = m + l in
     let live = FILTER (\n. n < k) vs in
     let vars = MAP (get_var m l i) live in
     let cs = cShift (MAP SND fns) (m + l) (1 + LENGTH fns) (new_env 0 live) in
     let c1 = cShift [x1] m (l + LENGTH fns) i in
       ([Letrec loc vars (ZIP (MAP FST fns, cs)) (HD c1)])) /\
  (cShift [Handle x1 x2] m l i =
     let c1 = cShift [x1] m l i in
     let c2 = cShift [x2] m (l+1) i in
       ([Handle (HD c1) (HD c2)])) /\
  (cShift [Call dest xs] m l i =
     let c1 = cShift xs m l i in
       ([Call dest c1]))`
 (WF_REL_TAC `measure (clos_exp3_size o FST)`
  \\ REPEAT STRIP_TAC \\ TRY DECIDE_TAC \\
  Induct_on `fns` >>
  srw_tac [ARITH_ss] [clos_exp_size_def] >>
  Cases_on `h` >>
  srw_tac [ARITH_ss] [clos_exp_size_def]);

val cShift_ind = fetch "-" "cShift_ind";

val cShift_LENGTH_LEMMA = store_thm("cShift_LENGTH_LEMMA",
  ``!xs m l i. LENGTH (cShift xs m l i) = LENGTH xs``,
  recInduct cShift_ind \\ REPEAT STRIP_TAC
  \\ fs [cShift_def,LET_DEF,ADD1,AC ADD_COMM ADD_ASSOC])

val cShift_SING = prove(
  ``!ys. (cShift [x] m l i = ys) ==> ?y. ys = [y]``,
  fs [] \\ MP_TAC (Q.SPEC `[x]` cShift_LENGTH_LEMMA |> SPEC_ALL)
  \\ Cases_on `cShift [x] m l i` \\ fs [LENGTH_NIL])
  |> SIMP_RULE std_ss [];

val cShift_CONS = store_thm("cEval_CONS",
  ``cShift ((x:clos_exp)::xs) m l i =
      let c1 = cShift [x] m l i in
      let c2 = cShift xs m l i in
        (HD c1 :: c2:clos_exp list)``,
  Cases_on `xs` \\ fs [cShift_def,LET_DEF,SING_HD,cShift_LENGTH_LEMMA]);

(* main function *)

val cAnnotate_def = Define `
  cAnnotate env_size xs = cShift (FST (cFree xs)) 0 env_size LN`;

(* correctness theorem *)

val clos_free_set_def = Define `
  clos_free_set x y = clos_free y x`;

val (val_rel_rules,val_rel_ind,val_rel_cases) = Hol_reln `
  (val_rel (Number j) (Number j))
  /\
  (EVERY2 val_rel (xs:clos_val list) (ys:clos_val list) ==>
   val_rel (Block t xs) (Block t ys))
  /\
  (val_rel (RefPtr r1) (RefPtr r1))
  /\
  ((cShift (FST (cFree [c])) m 1 i = [c']) /\
   (!n. clos_free_set [c] n /\ 1 <= n ==> env_ok m 0 i env env' (n - 1)) /\
   (LENGTH env = m) ==>
   val_rel (Closure p env c) (Closure p env' c'))
  /\
  ((cShift (FST (cFree cs)) m (LENGTH cs + 1) i = cs') /\
   (!n. clos_free_set cs n /\ 1 + LENGTH cs <= n ==>
        env_ok m 0 i env env' (n - (1 + LENGTH cs))) /\
   (LENGTH env = m) ==>
   val_rel (Recclosure p env cs index) (Recclosure p env' cs' index))
  /\
  (l + m <= n ==>
   env_ok m l i (env2:clos_val list) (env2':clos_val list) n)
  /\
  (n < l /\ val_rel (EL n env2) (EL n env2') /\
   n < LENGTH env2 /\ n < LENGTH env2' ==>
   env_ok m l i env2 env2' n)
  /\
  (l <= n /\ n < l + m /\
   n < l + m /\ (lookup (n - l) i = SOME v) /\
   n < LENGTH env2 /\
   l + v < LENGTH env2' /\
   val_rel (EL n env2) (EL (l + v) env2') ==>
   env_ok m l i env2 env2' n)`

val env_ok_def = val_rel_cases |> CONJUNCT2

val (res_rel_rules,res_rel_ind,res_rel_cases) = Hol_reln `
  (EVERY2 val_rel xs ys ==>
   res_rel (Result xs) (Result ys)) /\
  (val_rel x y ==>
   res_rel (Exception x) (Exception y)) /\
  (res_rel TimeOut TimeOut) /\
  (res_rel Error Error)`

val (ref_rel_rules,ref_rel_ind,ref_rel_cases) = Hol_reln `
  (EVERY2 val_rel xs ys ==>
   ref_rel (ValueArray xs) (ValueArray ys)) /\
  (ref_rel (ByteArray b) (ByteArray b))`

val state_rel_def = Define `
  state_rel (s:clos_state) (t:clos_state) <=>
    (s.clock = t.clock) /\
    (s.output = t.output) /\
    ~s.restrict_envs /\ t.restrict_envs /\
    EVERY2 (OPTREL val_rel) s.globals t.globals /\
    (FDOM s.refs = FDOM t.refs) /\
    (!n r1.
      (FLOOKUP s.refs n = SOME r1) ==>
      ?r2. (FLOOKUP t.refs n = SOME r2) /\ ref_rel r1 r2) /\
    (!name arity c.
      (FLOOKUP s.code name = SOME (arity,c)) ==>
      ?c2.
        (cShift (FST (cFree [c])) 0 arity LN = [c2]) /\
        (FLOOKUP t.code name = SOME (arity,c2)))`

val val_rel_simp = let
  val f = SIMP_CONV (srw_ss()) [Once val_rel_cases]
  in map f [``val_rel (Number x) y``,
            ``val_rel (Block n l) y``,
            ``val_rel (RefPtr x) y``,
            ``val_rel (Closure n l x) y``,
            ``val_rel (Recclosure x1 x2 x3 x4) y``,
            ``val_rel y (Number x)``,
            ``val_rel y (Block n l)``,
            ``val_rel y (RefPtr x)``,
            ``val_rel y (Closure n l x)``,
            ``val_rel y (Recclosure x1 x2 x3 x4)``] |> LIST_CONJ end
  |> curry save_thm "val_rel_simp"

val res_rel_simp = let
  val f = SIMP_CONV (srw_ss()) [res_rel_cases]
  in map f [``res_rel (Result x) y``,
            ``res_rel (Exception x) y``,
            ``res_rel Error y``,
            ``res_rel TimeOut y``] |> LIST_CONJ end
val _ = save_thm("res_rel_simp",res_rel_simp)

val HD_cShift = prove(
  ``[HD (cShift [x] m l i)] = cShift [x] m l i``,
  STRIP_ASSUME_TAC cShift_SING \\ fs [])

val _ = augment_srw_ss [rewrites [HD_cShift]];

val IMP_IMP = save_thm("IMP_IMP",
  METIS_PROVE [] ``b1 /\ (b2 ==> b3) ==> ((b1 ==> b2) ==> b3)``);

val EVERY2_EL = prove(
  ``!xs ys P. EVERY2 P xs ys ==> !n. n < LENGTH xs ==> P (EL n xs) (EL n ys)``,
  Induct \\ Cases_on `ys` \\ fs [EL] \\ REPEAT STRIP_TAC
  \\ Cases_on `n` \\ fs []);

val env_ok_EXTEND = prove(
  ``EVERY2 val_rel env1 env2 /\ (l1 = LENGTH env1) /\
    (l1 <= n ==> env_ok m l i env1' env2' (n - l1)) ==>
    env_ok m (l + l1) i (env1 ++ env1') (env2 ++ env2') n``,
  SRW_TAC [] [] \\ SIMP_TAC std_ss [env_ok_def]
  \\ Cases_on `n < LENGTH env1` \\ fs [] THEN1
   (DISJ2_TAC \\ DISJ1_TAC \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ fs [rich_listTheory.EL_APPEND1]
    \\ IMP_RES_TAC EVERY2_EL \\ fs [] \\ DECIDE_TAC)
  \\ fs [NOT_LESS]
  \\ fs [env_ok_def]
  THEN1 (DISJ1_TAC \\ DECIDE_TAC)
  THEN1
   (DISJ2_TAC \\ DISJ1_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ fs [rich_listTheory.EL_APPEND2]
    \\ DECIDE_TAC)
  \\ DISJ2_TAC \\ DISJ2_TAC \\ Q.EXISTS_TAC `v` \\ fs []
  \\ IMP_RES_TAC EVERY2_LENGTH
  \\ fs [rich_listTheory.EL_APPEND2]
  \\ `n - (l + LENGTH env2) = n - LENGTH env2 - l` by DECIDE_TAC \\ fs []
  \\ `LENGTH env2 <= l + LENGTH env2 + v` by DECIDE_TAC
  \\ fs [rich_listTheory.EL_APPEND2]
  \\ `l + LENGTH env2 + v - LENGTH env2 = l + v` by DECIDE_TAC \\ fs []
  \\ DECIDE_TAC);

val env_ok_cons = env_ok_EXTEND
  |> Q.INST [`env1`|->`[v1]`,`env2`|->`[v2]`] |> Q.GEN `l1`
  |> SIMP_RULE (srw_ss()) []

val env_ok_1 = env_ok_EXTEND
  |> Q.INST [`env1`|->`[v1]`,`env2`|->`[v2]`,`l`|->`0`] |> Q.GEN `l1`
  |> SIMP_RULE (srw_ss()) []

val env_ok_append = env_ok_EXTEND
  |> GSYM |> Q.INST [`l`|->`0`]
  |> SIMP_RULE (srw_ss()) []

val lookup_vars_NONE = prove(
  ``!vs. (lookup_vars vs env = NONE) <=> ?v. MEM v vs /\ LENGTH env <= v``,
  Induct \\ fs [lookup_vars_def]
  \\ REPEAT STRIP_TAC \\ fs []
  \\ Cases_on `h < LENGTH env` \\ fs [NOT_LESS]
  \\ Cases_on `lookup_vars vs env` \\ fs []
  THEN1 METIS_TAC []
  \\ CCONTR_TAC \\ fs [] \\ METIS_TAC [NOT_LESS])

val lookup_vars_SOME = prove(
  ``!vs env xs.
      (lookup_vars vs env = SOME xs) ==>
      (LENGTH vs = LENGTH xs)``,
  Induct \\ fs [lookup_vars_def] \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup_vars vs env` \\ fs [] \\ SRW_TAC [] [] \\ RES_TAC);

val lookup_vars_MEM = prove(
  ``!ys n x (env2:clos_val list).
      (lookup_vars ys env2 = SOME x) /\ n < LENGTH ys ==>
      (EL n ys) < LENGTH env2 /\
      (EL n x = EL (EL n ys) env2)``,
  Induct \\ fs [lookup_vars_def] \\ NTAC 5 STRIP_TAC
  \\ Cases_on `lookup_vars ys env2` \\ fs []
  \\ Cases_on `n` \\ fs [] \\ SRW_TAC [] [] \\ fs []) |> SPEC_ALL;

val lookup_EL_new_env = prove(
  ``!y n k. n < LENGTH y /\ ALL_DISTINCT y ==>
            (lookup (EL n y) (new_env k y) = SOME (k + n))``,
  Induct \\ fs [] \\ Cases_on `n` \\ fs [new_env_def,lookup_insert]
  \\ SRW_TAC [] [ADD1,AC ADD_COMM ADD_ASSOC]
  \\ fs [MEM_EL] \\ METIS_TAC []);

val env_ok_new_env = prove(
  ``env_ok m l i env env2 k /\ MEM k live /\ ALL_DISTINCT live /\
    (lookup_vars (MAP (get_var m l i) (FILTER (\n. n < m + l) live)) env2 =
      SOME x) ==>
    env_ok (m + l) 0 (new_env 0 (FILTER (\n. n < m + l) live)) env x k``,
  REPEAT STRIP_TAC
  \\ Q.ABBREV_TAC `y = FILTER (\n. n < m + l) live`
  \\ `ALL_DISTINCT y` by
       (UNABBREV_ALL_TAC \\ MATCH_MP_TAC FILTER_ALL_DISTINCT \\ fs [])
  \\ Cases_on `~(k < m + l)` THEN1 (fs [env_ok_def,NOT_LESS] \\ DECIDE_TAC)
  \\ fs []
  \\ `MEM k y` by (UNABBREV_ALL_TAC \\ fs [MEM_FILTER])
  \\ POP_ASSUM MP_TAC
  \\ simp [MEM_EL] \\ STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o GSYM)
  \\ Q.PAT_ASSUM `MEM k live` (K ALL_TAC)
  \\ Q.PAT_ASSUM `Abbrev vvv` (K ALL_TAC)
  \\ `(EL n (MAP (get_var m l i) y) = get_var m l i k) /\
      n < LENGTH (MAP (get_var m l i) y)` by fs [EL_MAP]
  \\ Q.ABBREV_TAC `ys = (MAP (get_var m l i) y)`
  \\ MP_TAC lookup_vars_MEM \\ fs [] \\ STRIP_TAC
  \\ `val_rel (EL k env) (EL (get_var m l i k) env2)` by
   (fs [env_ok_def] THEN1 (`F` by DECIDE_TAC) \\ fs [get_var_def]
    \\ `~(k < l)` by DECIDE_TAC \\ fs [tlookup_def])
  \\ Q.PAT_ASSUM `EL n x = yy` (ASSUME_TAC o GSYM) \\ fs []
  \\ fs [env_ok_def] \\ DISJ2_TAC
  \\ TRY (`k < l + m` by DECIDE_TAC) \\ fs []
  \\ SRW_TAC [] [] \\ fs [lookup_EL_new_env]
  \\ IMP_RES_TAC lookup_vars_SOME \\ fs []);

val EL_cShift_cFree = prove(
  ``!fns index.
     index < LENGTH fns ==>
     ([EL index (cShift (FST (cFree fns)) l m i)] =
      (cShift (FST (cFree [EL index fns])) l m i))``,
  Induct \\ fs [] \\ REPEAT STRIP_TAC
  \\ ONCE_REWRITE_TAC [cFree_CONS]
  \\ SIMP_TAC std_ss [Once cShift_CONS]
  \\ Cases_on `index` \\ fs []
  \\ fs [LET_DEF,cFree_def]
  \\ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ fs [SING_HD,LENGTH_FST_cFree]);

val clos_free_EL_IMP = prove(
  ``!fns n index.
      clos_free n [EL index fns] /\ index < LENGTH fns ==>
      clos_free n fns``,
  Induct \\ fs [] \\ REPEAT STRIP_TAC
  \\ Cases_on `index` \\ fs [EL]
  \\ Cases_on `fns` \\ fs [clos_free_def] \\ RES_TAC \\ fs []);

val EVERY2_GENLIST = prove(
  ``EVERY2 P (GENLIST f l) (GENLIST g l) <=>
    !i. i < l ==> P (f i) (g i)``,
  Induct_on `l`
  \\ fs [GENLIST,rich_listTheory.LIST_REL_APPEND_SING,SNOC_APPEND]
  \\ fs [DECIDE ``i < SUC n <=> i < n \/ (i = n)``] \\ METIS_TAC []);

val val_rel_IMP_clos_to_chars = prove(
  ``!xs ys aux.
      EVERY2 val_rel xs ys ==>
      (clos_to_chars xs aux = clos_to_chars ys aux)``,
  Induct \\ Cases_on `ys` \\ fs []
  \\ Cases_on `h` \\ fs [val_rel_simp,clos_to_chars_def,PULL_EXISTS]
  \\ SRW_TAC [] [] \\ fs []);

val val_rel_IMP_clos_to_string = prove(
  ``!h1 h2. val_rel h1 h2 ==> (clos_to_string h1 = clos_to_string h2)``,
  Induct \\ fs [val_rel_simp,clos_to_string_def,PULL_EXISTS]
  \\ SRW_TAC [] [] \\ IMP_RES_TAC val_rel_IMP_clos_to_chars \\ fs []);

val EVERY2_LUPDATE = prove(
  ``!xs ys n.
      P x y /\ EVERY2 P xs ys ==> EVERY2 P (LUPDATE x n xs) (LUPDATE y n ys)``,
  Induct \\ Cases_on `ys` \\ Cases_on `n` \\ fs [LUPDATE_def]);

val cEvalOp_thm = prove(
  ``state_rel s1 t1 /\ EVERY2 val_rel xs ys /\
    (cEvalOp op xs s1 = SOME (v,s2)) ==>
    ?w t2. (cEvalOp op ys t1 = SOME (w,t2)) /\
           val_rel v w /\ state_rel s2 t2``,

  REVERSE (Cases_on `op`) \\ REPEAT STRIP_TAC
  THEN1 (* Less *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [val_rel_simp] \\ SRW_TAC [] []
    \\ Cases_on `i < i'` \\ fs [bool_to_val_def,val_rel_simp])
  THEN1 (* Mod *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [val_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Div *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [val_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Mult *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [val_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Sub *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [val_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* Add *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [val_rel_simp] \\ SRW_TAC [] [])
  THEN1 (* PrintC *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [val_rel_simp] \\ SRW_TAC [] []
    \\ fs [state_rel_def])
  THEN1 (* Print *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ SRW_TAC [] [] \\ fs [val_rel_simp] \\ SRW_TAC [] []
    \\ fs [state_rel_def] \\ IMP_RES_TAC val_rel_IMP_clos_to_string \\ fs [])
  THEN1 (* Label *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs [])
  THEN1 (* Update *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [val_rel_simp] \\ SRW_TAC [] []
    \\ fs [state_rel_def,FLOOKUP_DEF]
    \\ rfs [] \\ fs []
    \\ TRY (Q.PAT_ASSUM `!x. bb ==> bbb` IMP_RES_TAC
            \\ rfs [] \\ POP_ASSUM MP_TAC
            \\ fs [ref_rel_cases]
            \\ REPEAT STRIP_TAC
            \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [] \\ NO_TAC)
    \\ STRIP_TAC \\ Cases_on `n' = n` \\ fs []
    \\ fs [FAPPLY_FUPDATE_THM] \\ fs [ref_rel_cases]
    \\ MATCH_MP_TAC EVERY2_LUPDATE \\ fs []
    \\ RES_TAC \\ rfs []
    \\ fs [FAPPLY_FUPDATE_THM])
  THEN1 (* Deref *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [val_rel_simp] \\ SRW_TAC [] []
    \\ fs [state_rel_def,FLOOKUP_DEF]
    \\ rfs [] \\ fs []
    \\ TRY (Q.PAT_ASSUM `!x. bb ==> bbb` IMP_RES_TAC
            \\ rfs [] \\ POP_ASSUM MP_TAC
            \\ fs [ref_rel_cases]
            \\ REPEAT STRIP_TAC
            \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [] \\ NO_TAC)
    \\ Q.PAT_ASSUM `!x. bb ==> bbb` IMP_RES_TAC
    \\ rfs [] \\ POP_ASSUM MP_TAC
    \\ ONCE_REWRITE_TAC [ref_rel_cases]
    \\ fs [] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC EVERY2_EL
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ `Num i < LENGTH l` by intLib.COOPER_TAC
    \\ RES_TAC)
  THEN1 (* Ref *) cheat
  THEN1 (* Equal *) cheat
  THEN1 (* IsBlock *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [val_rel_simp] \\ SRW_TAC [] []
    \\ EVAL_TAC \\ fs [val_rel_simp])
  THEN1 (* TagEq *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC \\ fs []
    \\ fs [val_rel_simp] \\ SRW_TAC [] []
    \\ Cases_on `n' = n` \\ fs [] \\ EVAL_TAC
    \\ fs [val_rel_simp])
  THEN1 (* Const *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [val_rel_simp] \\ fs [])
  THEN1 (* ToList *) cheat
  THEN1 (* FromList *) cheat
  THEN1 (* UpdateByte *) cheat
  THEN1 (* DerefByte *) cheat
  THEN1 (* RefArray *) cheat
  THEN1 (* RefByte *) cheat
  THEN1 (* LengthByte *) cheat
  THEN1 (* Length *) cheat
  THEN1 (* LengthBlock *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [val_rel_simp] \\ fs []
    \\ fs [val_rel_simp] \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [])
  THEN1 (* El *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [val_rel_simp] \\ fs []
    \\ fs [val_rel_simp] \\ fs [] \\ SRW_TAC [] []
    \\ IMP_RES_TAC EVERY2_EL
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs [])
  THEN1 (* Cons *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [val_rel_simp] \\ fs [])
  THEN1 (* SetGlobal *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [val_rel_simp] \\ fs []
    \\ fs [state_rel_def,get_global_def] \\ RES_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ IMP_RES_TAC EVERY2_EL
    \\ rfs [] \\ POP_ASSUM IMP_RES_TAC
    \\ rfs [quotient_optionTheory.OPTION_REL_def]
    \\ MATCH_MP_TAC EVERY2_LUPDATE
    \\ fs [quotient_optionTheory.OPTION_REL_def])
  THEN1 (* AllocGlobal *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [val_rel_simp] \\ fs []
    \\ fs [state_rel_def,get_global_def] \\ RES_TAC
    \\ fs [quotient_optionTheory.OPTION_REL_def])
  THEN1 (* Global *)
   (fs [cEvalOp_def] \\ BasicProvers.EVERY_CASE_TAC
    \\ SRW_TAC [] [val_rel_simp] \\ fs []
    \\ fs [state_rel_def,get_global_def] \\ RES_TAC
    \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ IMP_RES_TAC EVERY2_EL
    \\ rfs [] \\ POP_ASSUM IMP_RES_TAC
    \\ rfs [quotient_optionTheory.OPTION_REL_def]));

val cShift_correct = prove(
  ``!xs env s1 env' t1 res s2 m l i.
      (cEval (xs,env,s1) = (res,s2)) /\ res <> Error /\
      (LENGTH env = m + l) /\
      clos_free_set xs SUBSET env_ok m l i env env' /\
      state_rel s1 t1 ==>
      ?res' t2.
         (cEval (cShift (FST (cFree xs)) m l i,env',t1) = (res',t2)) /\
         res_rel res res' /\
         state_rel s2 t2 ``,
  recInduct cEval_ind \\ REPEAT STRIP_TAC
  THEN1 (* NIL *)
   (fs [cFree_def,cShift_def,cEval_def]
    \\ SRW_TAC [] [res_rel_cases])
  THEN1 (* CONS *)
   (fs [cFree_def,cEval_def]
    \\ `?y1 l1. cFree [x] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ `?y2 l2. cFree (y::xs) = (y2,l2)` by METIS_TAC [PAIR] \\ fs []
    \\ fs [LET_DEF]
    \\ `?r1 s1. cEval ([x],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs []
    \\ `?y3 y4. y2 = y3::y4` by
     (IMP_RES_TAC cFree_LENGTH
      \\ Cases_on `y2` \\ fs [has_var_def,clos_free_def])
    \\ fs [cShift_def]
    \\ Cases_on `r1` \\ fs []
    \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?t. cShift [y1] m l i = [t]` by METIS_TAC [cShift_SING]
    \\ fs [] \\ ONCE_REWRITE_TAC [cEval_CONS]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`])
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`m`,`l`,`i`])
    \\ `clos_free_set [x] SUBSET env_ok m l i env env' /\
        clos_free_set (y::xs) SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ fs [] \\ REPEAT STRIP_TAC \\ fs [res_rel_simp]
    \\ `?r2 s2. cEval (y::xs,env,s1) = (r2,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t2`])
    \\ Cases_on `r2` \\ fs []
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPECL [`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs [] \\ SRW_TAC [] [] \\ fs [res_rel_simp]
    \\ IMP_RES_TAC cEval_SING \\ fs [])
  THEN1 (* Var *)
   (Cases_on `n < LENGTH env`
    \\ fs [cFree_def,cEval_def,cShift_def]
    \\ fs [clos_free_set_def,SUBSET_DEF,IN_DEF,clos_free_def]
    \\ Cases_on `l + m <= n`
    THEN1 (fs [env_ok_def] \\ rfs [] \\ `F` by DECIDE_TAC)
    \\ REVERSE (`get_var m l i n < LENGTH env' /\
        val_rel (EL n env) (EL (get_var m l i n) env')` by ALL_TAC)
    THEN1 (fs [] \\ SRW_TAC [] [] \\ fs [res_rel_cases])
    \\ fs [get_var_def,env_ok_def]
    \\ Cases_on `n < l` \\ fs [tlookup_def]
    \\ `F` by DECIDE_TAC)
  THEN1 (* If *)
   (fs [cFree_def]
    \\ `?y1 l1. cFree [x1] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ `?y2 l2. cFree [x2] = ([y2],l2)` by METIS_TAC [PAIR,cFree_SING]
    \\ `?y3 l3. cFree [x3] = ([y3],l3)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [LET_DEF,cShift_def,cEval_def]
    \\ `?r1 s1. cEval ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs []
    \\ `clos_free_set [x1] SUBSET env_ok m l i env env' /\
        clos_free_set [x2] SUBSET env_ok m l i env env' /\
        clos_free_set [x3] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ `r1 <> Error` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC cEval_SING \\ fs [] \\ SRW_TAC [] []
    \\ fs [] \\ SRW_TAC [] []
    \\ fs [val_rel_simp] \\ SRW_TAC [] []
    \\ Cases_on `r1 = Block 1 []` \\ fs [val_rel_simp]
    \\ Cases_on `r1 = Block 0 []` \\ fs [val_rel_simp])
  THEN1 (* Let *)
   (fs [cFree_def]
    \\ `?y1 l1. cFree xs = (y1,l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ `?y2 l2. cFree [x2] = ([y2],l2)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [LET_DEF,cShift_def,cEval_def]
    \\ `?r1 s1. cEval (xs,env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs []
    \\ `clos_free_set xs SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ `r1 <> Error` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_simp] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`ys++env'`,`t2`,
         `m`,`l + LENGTH (y1:clos_exp list)`,`i`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC
    \\ REPEAT STRIP_TAC \\ fs []
    \\ fs [] \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
    \\ IMP_RES_TAC cFree_LENGTH
    \\ IMP_RES_TAC EVERY2_LENGTH
    \\ IMP_RES_TAC cEval_IMP_LENGTH
    \\ fs [cShift_LENGTH_LEMMA,AC ADD_COMM ADD_ASSOC]
    \\ MATCH_MP_TAC env_ok_EXTEND \\ fs []
    \\ fs [clos_free_set_def,clos_free_def]
    \\ REPEAT STRIP_TAC
    \\ Q.PAT_ASSUM `!x.bbb` (K ALL_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ `x - LENGTH ys + LENGTH ys = x` by DECIDE_TAC \\ fs [])
  THEN1 (* Raise *)
   (fs [cFree_def]
    \\ `?y1 l1. cFree [x1] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [LET_DEF,cShift_def,cEval_def]
    \\ `?r1 s1. cEval ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs []
    \\ `clos_free_set [x1] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ `r1 <> Error` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC cEval_SING \\ fs [])
  THEN1 (* Handle *)
   (fs [cFree_def]
    \\ `?y1 l1. cFree [x1] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ `?y2 l2. cFree [x2] = ([y2],l2)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [LET_DEF,cShift_def,cEval_def]
    \\ `?r1 s2. cEval ([x1],env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `clos_free_set [x1] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ `r1 <> Error` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_simp] \\ SRW_TAC [] []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`y'::env'`,`t2`,`m`,`l+1`,`i`]) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC \\ fs []
    \\ fs [AC ADD_ASSOC ADD_COMM,ADD1]
    \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC env_ok_cons \\ fs []
    \\ RES_TAC \\ REPEAT STRIP_TAC
    \\ fs [clos_free_set_def,clos_free_def]
    \\ Cases_on `x` \\ fs []
    \\ Q.PAT_ASSUM `!x.bbb` (K ALL_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [ADD1])
  THEN1 (* Op *)
   (fs [cFree_def]
    \\ `?y1 l1. cFree xs = (y1,l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [LET_DEF,cShift_def,cEval_def]
    \\ `?r1 s1. cEval (xs,env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs []
    \\ `clos_free_set xs SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ `r1 <> Error` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_simp] \\ SRW_TAC [] []
    \\ Cases_on `cEvalOp op a s1` \\ fs []
    \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] [res_rel_simp,PULL_EXISTS]
    \\ IMP_RES_TAC cEvalOp_thm \\ fs [])
  THEN1 (* Fn *)
   (fs [cFree_def,cEval_def]
    \\ `~s.restrict_envs /\ t1.restrict_envs` by fs [state_rel_def]
    \\ fs [clos_env_def]
    \\ SRW_TAC [] [] \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?y1 l1. cFree [exp] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [cShift_def,LET_DEF,cEval_def,clos_env_def,res_rel_simp,PULL_EXISTS,
           val_rel_simp]
    \\ Q.ABBREV_TAC `live = FILTER (\n. n < m + l) (vars_to_list (Shift 1 l1))`
    \\ fs [MAP_MAP_o,o_DEF]
    \\ Cases_on `lookup_vars (MAP (get_var m l i) live) env'`
    \\ fs [] THEN1
     (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def]
      \\ fs [lookup_vars_NONE] \\ UNABBREV_ALL_TAC
      \\ fs [MEM_FILTER,MEM_vars_to_list,MEM_MAP]
      \\ MP_TAC (Q.INST [`xs`|->`[exp]`] cFree_thm)
      \\ fs [LET_DEF] \\ CCONTR_TAC \\ fs [] \\ RES_TAC
      \\ SRW_TAC [] []
      \\ fs [env_ok_def] \\ rfs []
      \\ fs [get_var_def,tlookup_def]
      \\ DECIDE_TAC)
    \\ Q.EXISTS_TAC `new_env 0 live` \\ fs []
    \\ REPEAT STRIP_TAC \\ Cases_on `n` \\ fs []
    \\ MP_TAC (Q.INST [`xs`|->`[exp]`] cFree_thm)
    \\ fs [LET_DEF] \\ STRIP_TAC
    \\ fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def]
    \\ fs [ADD1] \\ RES_TAC \\ UNABBREV_ALL_TAC
    \\ Q.ABBREV_TAC `live = vars_to_list (Shift 1 l1)`
    \\ `MEM n' live` by (UNABBREV_ALL_TAC \\ fs [MEM_vars_to_list])
    \\ Q.ABBREV_TAC `k = n'`
    \\ Q.ABBREV_TAC `env2 = env'`
    \\ `ALL_DISTINCT live` by
      (UNABBREV_ALL_TAC \\ fs [ALL_DISTINCT_vars_to_list])
    \\ IMP_RES_TAC env_ok_new_env)
  THEN1 (* Letrec *)
   (fs [cFree_def,cEval_def]
    \\ `~s.restrict_envs /\ t1.restrict_envs` by fs [state_rel_def]
    \\ fs [clos_env_def]
    \\ SRW_TAC [] [] \\ SRW_TAC [] [markerTheory.Abbrev_def]
    \\ `?y1 l1. cFree fns = (y1,l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ `?y2 l2. cFree [exp] = ([y2],l2)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [cShift_def,LET_DEF,cEval_def,build_recc_def,clos_env_def,
           cShift_LENGTH_LEMMA]
    \\ Q.ABBREV_TAC `live = FILTER (\n. n < m + l)
          (vars_to_list (Shift (1 + LENGTH fns) l1))`
    \\ Cases_on `lookup_vars (MAP (get_var m l i) live) env'`
    \\ fs [] THEN1
     (`F` by ALL_TAC \\ fs []
      \\ fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def]
      \\ fs [lookup_vars_NONE] \\ UNABBREV_ALL_TAC
      \\ fs [MEM_FILTER,MEM_vars_to_list,MEM_MAP]
      \\ MP_TAC (Q.INST [`xs`|->`fns`] cFree_thm)
      \\ fs [LET_DEF] \\ CCONTR_TAC
      \\ fs [AC ADD_ASSOC ADD_COMM] \\ RES_TAC
      \\ SRW_TAC [] [] \\ fs []
      \\ fs [env_ok_def] \\ rfs []
      \\ fs [get_var_def,tlookup_def]
      \\ DECIDE_TAC)
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ IMP_RES_TAC cFree_LENGTH \\ fs []
    \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def]
    \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC (env_ok_EXTEND |> GEN_ALL)
    \\ fs [LENGTH_GENLIST]
    \\ REVERSE (REPEAT STRIP_TAC) THEN1
     (FIRST_X_ASSUM MATCH_MP_TAC
      \\ IMP_RES_TAC (DECIDE ``n <= m:num <=> (m - n + n = m)``) \\ fs [])
    \\ fs [EVERY2_GENLIST] \\ REPEAT STRIP_TAC
    \\ fs [val_rel_simp]
    \\ Q.EXISTS_TAC `new_env 0 live` \\ fs []
    \\ REPEAT STRIP_TAC
    \\ UNABBREV_ALL_TAC
    \\ ONCE_REWRITE_TAC [ADD_COMM]
    \\ MATCH_MP_TAC (GEN_ALL env_ok_new_env)
    \\ Q.LIST_EXISTS_TAC [`i`,`env'`] \\ fs []
    \\ fs [AC ADD_COMM ADD_ASSOC,ALL_DISTINCT_vars_to_list]
    \\ fs [MEM_vars_to_list]
    \\ MP_TAC (Q.INST [`xs`|->`fns`] cFree_thm)
    \\ fs [LET_DEF] \\ STRIP_TAC \\ fs []
    \\ IMP_RES_TAC (DECIDE ``n <= m:num <=> (m - n + n = m)``)
    \\ fs [clos_free_set_def]
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ fs [clos_free_set_def])
  THEN1 (* App *)
   (fs [cFree_def]
    \\ `?y1 l1. cFree [x1] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ `?y2 l2. cFree [x2] = ([y2],l2)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [LET_DEF,cShift_def,cEval_def]
    \\ `?r1 s1. cEval ([x1],env,s) = (r1,s1)` by METIS_TAC [PAIR] \\ fs []
    \\ `clos_free_set [x1] SUBSET env_ok m l i env env' /\
        clos_free_set [x2] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ `r1 <> Error` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_simp] \\ SRW_TAC [] []
    \\ `?r2 s2. cEval ([x2],env,s1) = (r2,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `r2 <> Error` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t2`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r2` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_simp] \\ SRW_TAC [] []
    \\ IMP_RES_TAC cEval_SING \\ fs [] \\ SRW_TAC [] []
    \\ fs [closLangTheory.dest_closure_def]
    \\ Cases_on `r1'` \\ fs []
    THEN1 (* Closure case *)
     (Cases_on `check_loc loc_opt n`
      \\ fs [val_rel_simp]
      \\ `t2'.clock = s2'.clock` by fs [state_rel_def] \\ fs []
      \\ Cases_on `s2'.clock = 0` \\ fs [] \\ SRW_TAC [] [res_rel_simp]
      \\ Q.PAT_ASSUM `xx = [c']` (fn th => fs [GSYM th])
      \\ fs [SUBSET_DEF,IN_DEF]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`y'::env''`,`dec_clock t2'`,
           `LENGTH (l':clos_val list)`,`1`,`i'`])
      \\ MATCH_MP_TAC IMP_IMP \\ REPEAT STRIP_TAC \\ fs []
      \\ REPEAT STRIP_TAC \\ fs [ADD1]
      THEN1 (MATCH_MP_TAC env_ok_1 \\ fs [])
      \\ fs [state_rel_def,closLangTheory.dec_clock_def])
    (* Recclosure case *)
    \\ Q.MATCH_ASSUM_RENAME_TAC `val_rel (Recclosure dest env3 fns index) y`
    \\ Cases_on `LENGTH fns <= index` \\ fs []
    \\ Cases_on `check_loc loc_opt (dest + index)` \\ fs [LET_DEF]
    \\ fs [val_rel_simp,cShift_LENGTH_LEMMA,LENGTH_FST_cFree]
    \\ `t2'.clock = s2'.clock` by fs [state_rel_def] \\ fs []
    \\ Cases_on `s2'.clock = 0` \\ fs [] \\ SRW_TAC [] [res_rel_simp]
    \\ `index < LENGTH fns` by DECIDE_TAC
    \\ fs [EL_cShift_cFree]
    \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ simp [AC ADD_ASSOC ADD_COMM,ADD1]
    \\ REVERSE (REPEAT STRIP_TAC)
    THEN1 (fs [state_rel_def,closLangTheory.dec_clock_def])
    \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
    \\ MATCH_MP_TAC env_ok_cons \\ fs []
    \\ REPEAT STRIP_TAC
    \\ Cases_on `x` \\ fs [ADD1]
    \\ fs [clos_free_set_def,clos_free_def]
    \\ MATCH_MP_TAC env_ok_append \\ fs [LENGTH_GENLIST]
    \\ REVERSE (REPEAT STRIP_TAC) THEN1
     (FIRST_X_ASSUM (MP_TAC o Q.SPEC `n + 1`)
      \\ fs [SUB_PLUS] \\ REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC
      \\ IMP_RES_TAC clos_free_EL_IMP \\ fs [AC ADD_COMM ADD_ASSOC])
    \\ fs [EVERY2_GENLIST]
    \\ REPEAT STRIP_TAC
    \\ fs [val_rel_simp]
    \\ Q.EXISTS_TAC `i'` \\ fs []
    \\ REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC
    \\ fs [clos_free_set_def])
  THEN1 (* Tick *)
   (fs [cFree_def,cEval_def]
    \\ `?y1 l1. cFree [x] = ([y1],l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [LET_DEF,cShift_def,cEval_def]
    \\ `t1.clock = s.clock` by fs [state_rel_def] \\ fs []
    \\ Cases_on `s.clock = 0` \\ fs []
    \\ SRW_TAC [] [res_rel_simp]
    \\ `clos_free_set [x] SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ `state_rel (dec_clock s) (dec_clock t1)` by
          fs [state_rel_def,closLangTheory.dec_clock_def] \\ RES_TAC
    \\ STRIP_ASSUME_TAC (cShift_SING |> Q.INST [`x`|->`y1`]) \\ fs [])
  THEN1 (* Call *)
   (fs [cFree_def]
    \\ `?y1 l1. cFree xs = (y1,l1)` by METIS_TAC [PAIR,cFree_SING]
    \\ fs [LET_DEF,cShift_def,cEval_def]
    \\ `?r1 s2. cEval (xs,env,s1) = (r1,s2)` by METIS_TAC [PAIR] \\ fs []
    \\ `clos_free_set xs SUBSET env_ok m l i env env'` by
      (fs [SUBSET_DEF,IN_DEF,clos_free_set_def,clos_free_def])
    \\ `r1 <> Error` by (REPEAT STRIP_TAC \\ fs [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env'`,`t1`,`m`,`l`,`i`]) \\ fs []
    \\ REPEAT STRIP_TAC \\ fs []
    \\ Cases_on `r1` \\ fs [] \\ SRW_TAC [] []
    \\ fs [res_rel_simp] \\ SRW_TAC [] []
    \\ Cases_on `find_code dest a s2'.code` \\ fs []
    \\ Cases_on `x` \\ fs []
    \\ fs [find_code_def]
    \\ Cases_on `FLOOKUP s2'.code dest` \\ fs []
    \\ Cases_on `x` \\ fs [] \\ SRW_TAC [] []
    \\ `?c2. cShift (FST (cFree [r])) 0 (LENGTH a) LN = [c2] /\
             FLOOKUP t2.code dest = SOME (LENGTH a,c2)` by
         (fs [state_rel_def] \\ RES_TAC \\ NO_TAC)
    \\ fs [] \\ IMP_RES_TAC EVERY2_LENGTH \\ fs []
    \\ `s2'.clock = t2.clock` by fs [state_rel_def] \\ fs []
    \\ Cases_on `t2.clock = 0` \\ fs []
    THEN1 (SRW_TAC [] [res_rel_simp])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`ys`,`dec_clock t2`,`0`,
         `LENGTH (ys:clos_val list)`,`LN`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [] \\ REVERSE (REPEAT STRIP_TAC)
      THEN1 (fs [state_rel_def,closLangTheory.dec_clock_def])
      \\ fs [SUBSET_DEF,IN_DEF] \\ REPEAT STRIP_TAC
      \\ SIMP_TAC std_ss [env_ok_def]
      \\ REVERSE (Cases_on `x < LENGTH ys`) \\ fs [] THEN1 DECIDE_TAC
      \\ IMP_RES_TAC EVERY2_EL \\ METIS_TAC [])
    \\ REPEAT STRIP_TAC \\ fs [] \\ rfs []));

val env_set_default = prove(
  ``x SUBSET env_ok 0 0 LN [] env'``,
  fs [SUBSET_DEF,IN_DEF,env_ok_def]);

val cAnnotate_correct = save_thm("cAnnotate_correct",
  cShift_correct
  |> SPEC_ALL |> Q.INST [`m`|->`0`,`l`|->`0`,`i`|->`LN`,`env`|->`[]`]
  |> REWRITE_RULE [GSYM cAnnotate_def,env_set_default,LENGTH,ADD_0]);

val code_locs_append = store_thm("code_locs_append",
  ``∀l1 l2. code_locs (l1 ++ l2) = code_locs l1 ++ code_locs l2``,
  Induct >> simp[code_locs_def] >>
  simp[Once code_locs_cons] >>
  simp[Once code_locs_cons,SimpRHS])

val cShift_code_locs = prove(
  ``∀xs env s1 env'. code_locs (cShift xs env s1 env') = code_locs xs``,
  ho_match_mp_tac cShift_ind >>
  simp[cShift_def,code_locs_def,cShift_LENGTH_LEMMA] >>
  rw[code_locs_append])

fun tac (g as (asl,w)) =
  let
    fun finder tm =
      let
        val (f,lss) = strip_comb tm
        val _ = assert (equal 1) (length lss)
        val (xs,_) = listSyntax.dest_list (hd lss)
      in
        same_const``cFree`` f andalso
        length xs > 0 andalso
        all is_var xs
      end
    fun f tm = case total finder tm of NONE => false | SOME x => x
    val tm = find_term f w
  in
    Cases_on[ANTIQUOTE tm] g
  end

val cFree_code_locs = prove(
  ``∀xs. code_locs (FST (cFree xs)) = code_locs xs``,
  ho_match_mp_tac cFree_ind >>
  simp[cFree_def,code_locs_def,UNCURRY] >> rw[] >>
  rpt(tac >> fs[code_locs_append]) >>
  imp_res_tac cFree_SING >> fs[] >> rw[] >>
  Cases_on`cFree xs`>>fs[] >>
  assume_tac cFree_LENGTH_LEMMA >> rfs[])

val cAnnotate_code_locs = store_thm("cAnnotate_code_locs",
  ``∀n ls. code_locs (cAnnotate n ls) = code_locs ls``,
  rw[cAnnotate_def,cShift_code_locs,cFree_code_locs])

val _ = export_theory();

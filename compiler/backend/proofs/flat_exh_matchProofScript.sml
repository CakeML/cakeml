open semanticPrimitivesTheory
open semanticPrimitivesPropsTheory
open preamble flatPropsTheory flatSemTheory flat_exh_matchTheory

val _ = new_theory "flat_exh_matchProof"

(* ------------------------------------------------------------------------- *)
(* Compile lemmas                                                            *)
(* ------------------------------------------------------------------------- *)

val compile_exps_SING_HD = Q.store_thm("compile_exps_SING_HD[simp]",
  `[HD (compile_exps exh [x])] = compile_exps exh [x]`,
  Cases_on `compile_exps exh [x]`
  \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`) \\ fs [compile_exps_LENGTH]);

val compile_exps_CONS = Q.store_thm("compile_exps_CONS",
  `compile_exps exh (x::xs) = compile_exps exh [x] ++ compile_exps exh xs`,
  qid_spec_tac `x` \\ Induct_on `xs` \\ rw [compile_exps_def]);

val compile_exps_APPEND = Q.store_thm("compile_exps_APPEND",
  `compile_exps exh (xs ++ ys) = compile_exps exh xs ++ compile_exps exh ys`,
  map_every qid_spec_tac [`ys`,`xs`] \\ Induct \\ rw [compile_exps_def]
  \\ rw [Once compile_exps_CONS]
  \\ rw [Once (GSYM compile_exps_CONS)]);

val compile_exps_REVERSE = Q.store_thm("compile_exps_REVERSE[simp]",
  `REVERSE (compile_exps exh xs) = compile_exps exh (REVERSE xs)`,
  Induct_on `xs` \\ rw [compile_exps_def]
  \\ rw [Once compile_exps_CONS, Once compile_exps_APPEND]
  \\ `LENGTH (compile_exps exh [h]) = LENGTH [h]`
    by fs [compile_exps_LENGTH]
  \\ fs [LENGTH_EQ_NUM_compute]);

val compile_exps_MAP_FST = Q.store_thm("compile_exps_MAP_FST",
  `MAP FST funs =
   MAP FST (MAP (\(a,b,c). (a,b,HD (compile_exps ctors [c]))) funs)`,
  Induct_on `funs` \\ rw []
  \\ PairCases_on `h` \\ fs []);

val compile_exps_find_recfun = Q.store_thm("compile_exps_find_recfun",
  `!ls f exh.
     find_recfun f (MAP (\(a,b,c). (a, b, HD (compile_exps exh [c]))) ls) =
     OPTION_MAP (\(x,y). (x, HD (compile_exps exh [y]))) (find_recfun f ls)`,
  Induct \\ rw []
  >- fs [semanticPrimitivesTheory.find_recfun_def]
  \\ simp [Once semanticPrimitivesTheory.find_recfun_def]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once semanticPrimitivesTheory.find_recfun_def]
  \\ every_case_tac \\ fs [])

val exhaustive_SUBMAP = Q.store_thm("exhaustive_SUBMAP",
  `!ps ctors ctors_pre.
     exhaustive_match ctors_pre ps /\
     ctors_pre SUBMAP ctors
     ==>
     exhaustive_match ctors ps`,
  Induct \\ rw [exhaustive_match_def] \\ fs []
  \\ every_case_tac \\ fs [is_unconditional_def]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs [] \\ rw []);

(* ------------------------------------------------------------------------- *)
(* Value relations                                                           *)
(* ------------------------------------------------------------------------- *)

(* The submap is to push env-rel forward in the proofs after adding things to
   the environment. *)
val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!ctors v. v_rel ctors (Litv v) (Litv v)) /\
  (!ctors n. v_rel ctors (Loc n) (Loc n)) /\
  (!ctors vs1 vs2.
     LIST_REL (v_rel ctors) vs1 vs2
     ==>
     v_rel ctors (Vectorv vs1) (Vectorv vs2)) /\
  (!ctors t v1 v2.
     LIST_REL (v_rel ctors) v1 v2
     ==>
     v_rel ctors (Conv t v1) (Conv t v2)) /\
  (!ctors vs1 n x vs2 ctors_pre.
     nv_rel ctors vs1 vs2 /\
     ctors_pre SUBMAP ctors
     ==>
     v_rel ctors (Closure vs1 n x)
                 (Closure vs2 n (HD (compile_exps ctors_pre [x])))) /\
  (!ctors vs1 fs x vs2 ctors_pre.
     nv_rel ctors vs1 vs2 /\
     ctors_pre SUBMAP ctors
     ==>
     v_rel ctors
       (Recclosure vs1 fs x)
       (Recclosure vs2
         (MAP (\(n,m,e). (n,m,HD (compile_exps ctors_pre [e]))) fs) x)) /\
  (!ctors. nv_rel ctors [] []) /\
  (!ctors n v1 v2 vs1 vs2.
     v_rel ctors v1 v2 /\
     nv_rel ctors vs1 vs2
     ==>
     nv_rel ctors ((n,v1)::vs1) ((n,v2)::vs2))`

val v_rel_thms = Q.store_thm("v_rel_thms[simp]",
  `(v_rel ctors (Litv l) v <=> v = Litv l) /\
   (v_rel ctors v (Litv l) <=> v = Litv l) /\
   (v_rel ctors (Loc n) v  <=> v = Loc n) /\
   (v_rel ctors v (Loc n)  <=> v = Loc n) /\
   (v_rel ctors (Conv t x) v <=>
     ?y. v = Conv t y /\ LIST_REL (v_rel ctors) x y) /\
   (v_rel ctors v (Conv t x) <=>
     ?y. v = Conv t y /\ LIST_REL (v_rel ctors) y x) /\
   (v_rel ctors (Vectorv x) v <=>
     ?y. v = Vectorv y /\ LIST_REL (v_rel ctors) x y) /\
   (v_rel ctors v (Vectorv x) <=>
     ?y. v = Vectorv y /\ LIST_REL (v_rel ctors) y x)`,
   rw [] \\ Cases_on `v` \\ rw [Once v_rel_cases, EQ_SYM_EQ])

val nv_rel_LIST_REL = Q.store_thm("nv_rel_LIST_REL",
  `!xs ys ctors.
     nv_rel ctors xs ys <=>
     LIST_REL (\(n1, v1) (n2, v2). n1 = n2 /\ v_rel ctors v1 v2) xs ys`,
  Induct \\ rw [Once (CONJUNCT2 v_rel_cases)]
  \\ PairCases_on `h` \\ Cases_on `ys` \\ fs []
  \\ PairCases_on `h` \\ fs [] \\ metis_tac []);

(* This needs to be removed from the proofs outside of this theory
   (something needs to be proven in source_to_flat) *)
val ctor_rel_def = Define `
  ctor_rel ctors (c : ((ctor_id # type_id) # num) set) <=>
    !tyid.
      case FLOOKUP ctors tyid of
        NONE      => !cid arity. ((cid, tyid), arity) NOTIN c
      | SOME dtys =>
          (tyid = NONE <=> (* exn *)
            !cid arity.
              lookup cid dtys = SOME arity <=> ((cid, tyid), arity) IN c) /\
          (IS_SOME tyid <=> (* dty *)
            !arity max.
              lookup arity dtys = SOME max <=>
                (!cid. cid < max ==> ((cid, tyid), arity) IN c))`;

val env_rel_def = Define `
  env_rel ctors env1 env2 <=>
    ctor_rel ctors env1.c /\
    env1.check_ctor /\
    env2.check_ctor /\
    env1.c = env2.c /\
    ~env1.exh_pat /\
    env2.exh_pat /\
    nv_rel ctors env1.v env2.v`;

(* TODO code, oracle, compiler *)
val state_rel_def = Define `
  state_rel ctors s1 s2 <=>
    s1.clock = s2.clock /\
    LIST_REL (sv_rel (v_rel ctors)) s1.refs s2.refs /\
    s1.ffi = s2.ffi /\
    LIST_REL (OPTION_REL (v_rel ctors)) s1.globals s2.globals`;

val result_rel_def = Define `
  (result_rel R ctors (Rval v1) (Rval v2) <=>
    R ctors v1 v2) /\
  (result_rel R ctors (Rerr (Rraise v1)) (Rerr (Rraise v2)) <=>
    v_rel ctors v1 v2) /\
  (result_rel R ctors (Rerr (Rabort e1)) (Rerr (Rabort e2)) <=>
    e1 = e2) /\
  (result_rel R ctors res1 res2 <=> F)`

val result_rel_thms = Q.store_thm("result_rel_thms[simp]",
  `(!ctors v1 r.
     result_rel R ctors (Rval v1) r <=>
     ?v2. r = Rval v2 /\ R ctors v1 v2) /\
   (!ctors v2 r.
     result_rel R ctors r (Rval v2) <=>
     ?v1. r = Rval v1 /\ R ctors v1 v2) /\
   (!ctors v1 r.
     result_rel R ctors (Rerr (Rraise v1)) r <=>
     ?v2. r = Rerr (Rraise v2) /\ v_rel ctors v1 v2) /\
   (!ctors v2 r.
      result_rel R ctors r (Rerr (Rraise v2)) <=>
      ?v1. r = Rerr (Rraise v1) /\ v_rel ctors v1 v2) /\
   (!ctors a r.
      result_rel R ctors (Rerr (Rabort a)) r <=>
      r = Rerr (Rabort a)) /\
   (!ctors a r.
      result_rel R ctors r (Rerr (Rabort a)) <=>
      r = Rerr (Rabort a))`,
  rpt conj_tac \\ ntac 2 gen_tac \\ Cases \\ rw [result_rel_def]
  \\ Cases_on `e` \\ rw [result_rel_def, EQ_SYM_EQ]);

val match_rel_def = Define `
  (match_rel ctors (Match env1) (Match env2) <=> nv_rel ctors env1 env2) /\
  (match_rel ctors No_match No_match <=> T) /\
  (match_rel ctors Match_type_error Match_type_error <=> T) /\
  (match_rel ctors _ _ <=> F)`

val match_rel_thms = Q.store_thm("match_rel_thms[simp]",
  `(match_rel ctors Match_type_error e <=> e = Match_type_error) /\
   (match_rel ctors e Match_type_error <=> e = Match_type_error) /\
   (match_rel ctors No_match e <=> e = No_match) /\
   (match_rel ctors e No_match <=> e = No_match)`,
  Cases_on `e` \\ rw [match_rel_def]);

val v_rel_v_to_char_list = Q.store_thm("v_rel_v_to_char_list",
  `!v1 v2 xs ctors.
     v_to_char_list v1 = SOME xs /\
     v_rel ctors v1 v2
     ==>
     v_to_char_list v2 = SOME xs`,
  ho_match_mp_tac v_to_char_list_ind \\ rw []
  \\ fs [v_to_char_list_def, case_eq_thms]
  \\ metis_tac []);

val v_rel_v_to_list = Q.store_thm("v_rel_v_to_list",
  `!v1 v2 xs ctors.
     v_to_list v1 = SOME xs /\
     v_rel ctors v1 v2
     ==>
     ?ys. v_to_list v2 = SOME ys /\
          LIST_REL (v_rel ctors) xs ys`,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def, case_eq_thms] \\ rw []
  \\ metis_tac []);

val v_rel_vs_to_string = Q.store_thm("v_rel_vs_to_string",
  `!v1 v2 xs ctors.
     vs_to_string v1 = SOME xs /\
     LIST_REL (v_rel ctors) v1 v2
     ==>
     vs_to_string v2 = SOME xs`,
  ho_match_mp_tac vs_to_string_ind \\ rw []
  \\ fs [vs_to_string_def, case_eq_thms] \\ rw []
  \\ metis_tac []);

val v_rel_list_to_v_APPEND = Q.store_thm("v_rel_list_to_v_APPEND",
  `!xs1 xs2 ctors ys1 ys2.
     v_rel ctors (list_to_v xs1) (list_to_v xs2) /\
     v_rel ctors (list_to_v ys1) (list_to_v ys2)
     ==>
     v_rel ctors (list_to_v (xs1 ++ ys1)) (list_to_v (xs2 ++ ys2))`,
  Induct \\ rw [] \\ fs [list_to_v_def]
  \\ Cases_on `xs2` \\ fs [list_to_v_def]);

val v_rel_list_to_v = Q.store_thm("v_rel_list_to_v",
  `!v1 v2 xs ys ctors.
   v_to_list v1 = SOME xs /\
   v_to_list v2 = SOME ys /\
   v_rel ctors v1 v2
   ==>
   v_rel ctors (list_to_v xs) (list_to_v ys)`,
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def, case_eq_thms] \\ rw []
  \\ fs [list_to_v_def]
  \\ metis_tac []);

val nv_rel_ALOOKUP_v_rel = Q.store_thm("nv_rel_ALOOKUP_v_rel",
  `!xs ys ctors n x.
     nv_rel ctors xs ys /\
     ALOOKUP xs n = SOME x
     ==>
     ?y.
     ALOOKUP ys n = SOME y /\ v_rel ctors x y`,
  Induct \\ rw []
  \\ qhdtm_x_assum `nv_rel` mp_tac
  \\ rw [Once (CONJUNCT2 v_rel_cases)]
  \\ fs [ALOOKUP_def, bool_case_eq]);

(* ------------------------------------------------------------------------- *)
(* Various semantics preservation theorems                                   *)
(* ------------------------------------------------------------------------- *)

val do_eq_thm = Q.store_thm("do_eq_thm",
  `(!v1 v2 r ctors v1' v2'.
     do_eq v1 v2 = r /\
     r <> Eq_type_error /\
     v_rel ctors v1 v1' /\
     v_rel ctors v2 v2'
     ==>
     do_eq v1' v2' = r) /\
   (!vs1 vs2 r ctors vs1' vs2'.
     do_eq_list vs1 vs2 = r /\
     r <> Eq_type_error /\
     LIST_REL (v_rel ctors) vs1 vs1' /\
     LIST_REL (v_rel ctors) vs2 vs2'
     ==>
     do_eq_list vs1' vs2' = r)`,
  ho_match_mp_tac do_eq_ind \\ reverse (rw [do_eq_def]) \\ fs [] \\ rw [do_eq_def]
  \\ TRY (metis_tac [LIST_REL_LENGTH])
  >-
   (qpat_x_assum `_ <> Eq_type_error` mp_tac
    \\ rw [case_eq_thms, pair_case_eq, bool_case_eq] \\ fs [PULL_EXISTS]
    \\ fsrw_tac [DNF_ss] []
    \\ res_tac \\ fs []
    \\ Cases_on `do_eq v1 v2` \\ fs []
    \\ Cases_on `b` \\ fs []
    \\ res_tac \\ fs [])
  \\ fs [Once v_rel_cases] \\ rw [] \\ fs [do_eq_def]);

val pmatch_thm = Q.store_thm("pmatch_thm",
  `(!env refs p v vs r ctors refs1 v1 env1 vs1.
     pmatch env refs p v vs = r /\
     r <> Match_type_error /\
     LIST_REL (sv_rel (v_rel ctors)) refs refs1 /\
     v_rel ctors v v1 /\
     nv_rel ctors vs vs1 /\
     env_rel ctors env env1
     ==>
     ?r1.
       pmatch env1 refs1 p v1 vs1 = r1 /\
       match_rel ctors r r1) /\
  (!env refs ps v vs r ctors refs1 v1 env1 vs1.
     pmatch_list env refs ps v vs = r /\
     r <> Match_type_error /\
     LIST_REL (sv_rel (v_rel ctors)) refs refs1 /\
     LIST_REL (v_rel ctors) v v1 /\
     nv_rel ctors vs vs1 /\
     env_rel ctors env env1
     ==>
     ?r1.
       pmatch_list env1 refs1 ps v1 vs1 = r1 /\
       match_rel ctors r r1)`,
  ho_match_mp_tac pmatch_ind \\ rw [pmatch_def]
  \\ rw [match_rel_def, Once v_rel_cases]
  \\ fsrw_tac [DNF_ss] [] \\ rfs [] \\ rw [pmatch_def]
  \\ rfs [] \\ fs []
  \\ TRY (metis_tac [env_rel_def, same_ctor_def, ctor_same_type_def])
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  >-
   (every_case_tac \\ fs [store_lookup_def]
    \\ fs [LIST_REL_EL_EQN]
    \\ metis_tac [sv_rel_def])
  \\ every_case_tac \\ fs [] \\ rfs []
  \\ last_x_assum drule \\ rpt (disch_then drule) \\ rw [] \\ fs []
  \\ metis_tac [match_rel_def]);

val do_opapp_thm = Q.store_thm("do_opapp_thm",
  `do_opapp vs1 = SOME (nvs1, e) /\
   LIST_REL (v_rel ctors) vs1 vs2
   ==>
   ?ctors_pre nvs2.
     nv_rel ctors nvs1 nvs2 /\
     ctors_pre SUBMAP ctors /\
     do_opapp vs2 = SOME (nvs2, HD (compile_exps ctors_pre [e]))`,
  simp [do_opapp_def, pair_case_eq, case_eq_thms, PULL_EXISTS]
  \\ rw [] \\ fs [PULL_EXISTS] \\ rw [] \\ fs []
  \\ fs [Once v_rel_cases] \\ rw [] \\ fs [PULL_EXISTS]
  \\ TRY (metis_tac [])
  \\ TRY (simp [Once v_rel_cases] \\ metis_tac [])
  \\ simp [compile_exps_find_recfun]
  \\ simp [AC CONJ_ASSOC CONJ_COMM]
  \\ fs [FST_triple, MAP_MAP_o, ETA_THM, o_DEF, LAMBDA_PROD, UNCURRY]
  \\ fs [build_rec_env_merge, nv_rel_LIST_REL]
  \\ qexists_tac `ctors_pre` \\ fs []
  \\ TRY
   (match_mp_tac EVERY2_APPEND_suff \\ fs [EVERY2_MAP]
    \\ match_mp_tac EVERY2_refl \\ rw [UNCURRY]
    \\ simp [Once v_rel_cases, nv_rel_LIST_REL]
    \\ metis_tac [])
  \\ fs [AC CONJ_ASSOC CONJ_COMM]
  \\ (conj_tac >- (simp [Once v_rel_cases, nv_rel_LIST_REL] \\ metis_tac []))
  \\ match_mp_tac EVERY2_APPEND_suff \\ fs [EVERY2_MAP]
  \\ match_mp_tac EVERY2_refl \\ rw [UNCURRY]
  \\ simp [Once v_rel_cases, nv_rel_LIST_REL] \\ metis_tac []);

val store_v_same_type_cases = Q.prove (
  `(!v r. store_v_same_type (Refv v) r <=> ?v1. r = Refv v1) /\
   (!v r. store_v_same_type r (Refv v) <=> ?v1. r = Refv v1) /\
   (!v r. store_v_same_type (Varray v) r <=> ?v1. r = Varray v1) /\
   (!v r. store_v_same_type r (Varray v) <=> ?v1. r = Varray v1) /\
   (!v r. store_v_same_type (W8array v) r <=> ?v1. r = W8array v1) /\
   (!v r. store_v_same_type r (W8array v) <=> ?v1. r = W8array v1)`,
  rpt conj_tac \\ gen_tac \\ Cases \\ rw [store_v_same_type_def]);

(* TODO this is in bad shape *)
val do_app_thm = Q.store_thm("do_app_thm",
  `do_app s1 op vs1 = SOME (t1, r1) /\
   state_rel ctors s1 s2 /\
   LIST_REL (v_rel ctors) vs1 vs2
   ==>
   ?t2 r2.
     result_rel v_rel ctors r1 r2 /\
     state_rel ctors t1 t2 /\
     do_app s2 op vs2 = SOME (t2, r2)`,
  rw [do_app_cases, case_eq_thms, PULL_EXISTS, bool_case_eq, COND_RATOR,
      div_exn_v_def, subscript_exn_v_def, chr_exn_v_def]
  \\ rw [] \\ fs [] \\ rw [] \\ fs [] \\ rfs [IS_SOME_EXISTS]
  \\ TRY
   (rename1 `Boolv xyz` \\ fs [Boolv_def]
    \\ imp_res_tac do_eq_thm \\ fs []
    \\ NO_TAC)
  \\ TRY
   (rename1 `store_alloc _ _.refs`
    \\ fs [store_alloc_def, state_rel_def] \\ rveq \\ fs []
    \\ metis_tac [LIST_REL_LENGTH])
  \\ TRY
   (asm_exists_tac \\ fs []
    \\ fs [state_rel_def, store_lookup_def, LIST_REL_EL_EQN]
    \\ rename1 `EL xx s1.refs`
    \\ last_assum (qspec_then `xx` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [sv_rel_cases] \\ rw [])
  \\ TRY
   (rename1 `store_lookup nn _.refs`
    \\ fs [store_lookup_def, state_rel_def, LIST_REL_EL_EQN] \\ rw [] \\ fs []
    \\ last_x_assum (qspec_then `nn` assume_tac) \\ fs []
    \\ rfs [] \\ fs [sv_rel_cases]
    \\ NO_TAC)
  \\ TRY
   (rename1 `store_assign nn _`
    \\ fs [store_assign_def, store_v_same_type_cases, store_lookup_def] \\ rveq
    \\ fs [] \\ rw []
    \\ fs [state_rel_def, LIST_REL_EL_EQN, EL_LUPDATE] \\ rw []
    \\ last_assum (qspec_then `nn` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [sv_rel_cases] \\ rw [] \\ fs [] \\ rw [EL_LUPDATE]
    \\ last_x_assum (qspec_then `n` assume_tac)
    \\ rfs [] \\ fs [sv_rel_cases]
    \\ NO_TAC)
  \\ TRY
   (rename1 `copy_array (_,_) _ _ = _`
    \\ fs [store_lookup_def, state_rel_def, LIST_REL_EL_EQN]
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ rename1 `EL src _`
    \\ rename1 `dst < _`
    \\ first_assum (qspec_then `src` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [sv_rel_cases] \\ rw []
    \\ first_assum (qspec_then `dst` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [sv_rel_cases] \\ rw []
    \\ fs [store_assign_def, store_v_same_type_cases] \\ rveq
    \\ rw [LUPDATE_LENGTH, EL_LUPDATE]
    \\ first_x_assum (qspec_then `n` mp_tac)
    \\ simp [sv_rel_cases]
    \\ NO_TAC)
  \\ TRY
   (fs [LIST_REL_EL_EQN]
    \\ asm_exists_tac \\ fs []
    \\ NO_TAC)
  \\ TRY
   (fs [store_alloc_def] \\ rveq
    \\ fs [state_rel_def, LIST_REL_EL_EQN] \\ rw []
    \\ rw [EL_APPEND_EQN]
    \\ `n - LENGTH s2.refs = 0` by fs []
    \\ pop_assum (fn th => once_rewrite_tac [th]) \\ fs []
    \\ rw [LIST_REL_EL_EQN, EL_REPLICATE]
    \\ NO_TAC)
  \\ TRY
   (fs [store_lookup_def, state_rel_def, LIST_REL_EL_EQN]
    \\ rename1 `EL nnn _ = Varray _`
    \\ last_assum (qspec_then `nnn` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [sv_rel_cases] \\ rw [] \\ fs []
    \\ fs [LIST_REL_EL_EQN] \\ rw [])
  \\ TRY
   (fs [store_lookup_def, store_assign_def, store_v_same_type_cases] \\ rveq
    \\ fs [state_rel_def, LIST_REL_EL_EQN] \\ rveq \\ fs []
    \\ rename1 `EL nnn _`
    \\ last_assum (qspec_then `nnn` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [sv_rel_cases] \\ rw [] \\ fs []
    \\ fs [LIST_REL_EL_EQN, EL_LUPDATE] \\ rw []
    \\ last_x_assum (qspec_then `n` mp_tac)
    \\ simp [sv_rel_cases] \\ rw [] \\ fs []
    \\ fs [LIST_REL_EL_EQN, EL_LUPDATE]
    \\ rw [])
  \\ TRY
   (fs [store_lookup_def, state_rel_def, LIST_REL_EL_EQN]
    \\ rename1 `EL nnn _ = Varray _`
    \\ last_assum (qspec_then `nnn` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [sv_rel_cases] \\ rw [] \\ fs []
    \\ fs [LIST_REL_EL_EQN] \\ rw []
    \\ last_assum (qspec_then `n` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [sv_rel_cases] \\ rw [] \\ fs []
    \\ fs [LIST_REL_EL_EQN])
  \\ TRY
   (fs [state_rel_def, LIST_REL_EL_EQN, OPTREL_def] \\ rw []
    \\ fs [EL_APPEND_EQN] \\ rw [] \\ fs [EL_REPLICATE, PULL_EXISTS]
    \\ rename1 `EL nnn _.globals`
    \\ first_assum (qspec_then `nnn` mp_tac)
    \\ impl_tac >- fs []
    \\ strip_tac \\ fs []
    \\ fs [EL_LUPDATE] \\ rw [] \\ fs []
    \\ NO_TAC)
  \\ TRY
   (fs [state_rel_def, LIST_REL_EL_EQN, OPTREL_def] \\  rw []
    \\ fs [EL_APPEND_EQN]
    \\ rw [] \\ fs [EL_REPLICATE]
    \\ NO_TAC)
  \\ map_every imp_res_tac [v_rel_v_to_char_list, v_rel_v_to_list,
                            v_rel_vs_to_string, v_rel_list_to_v] \\ fs []
  \\ irule v_rel_list_to_v_APPEND \\ fs []
  \\ rw [] \\ rfs [] \\ fs []);

(* ------------------------------------------------------------------------- *)
(* Compile expressions                                                       *)
(* ------------------------------------------------------------------------- *)

val is_unconditional_thm = Q.store_thm("is_unconditional_thm",
  `!p env refs v vs.
     is_unconditional p
     ==>
     pmatch env refs p v vs <> No_match`,
  ho_match_mp_tac is_unconditional_ind \\ rw []
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [is_unconditional_def]
  \\ CASE_TAC \\ fs [pmatch_def]
  \\ TRY CASE_TAC \\ fs [] \\ rw []
  \\ Cases_on `v` \\ fs [pmatch_def]
  \\ rpt CASE_TAC \\ fs []
  \\ rename1 `Conv t ls`
  \\ Cases_on `t` \\ rw [pmatch_def]
  \\ rpt (pop_assum mp_tac)
  \\ map_every qid_spec_tac [`env`,`refs`,`ls`,`vs`,`l`]
  \\ Induct \\ rw [pmatch_def]
  \\ fsrw_tac [DNF_ss] []
  \\ Cases_on `ls` \\ fs [pmatch_def]
  \\ CASE_TAC \\ fs []
  \\ res_tac \\ fs []);

val is_unconditional_list_thm = Q.store_thm("is_unconditional_list_thm",
  `!vs1 vs2 a b c.
   EVERY is_unconditional vs1
   ==>
   pmatch_list a b vs1 vs2 c <> No_match`,
  Induct >- (Cases \\ rw [pmatch_def])
  \\ gen_tac \\ Cases \\ rw [pmatch_def]
  \\ every_case_tac \\ fs []
  \\ metis_tac [is_unconditional_thm])

val exists_match_def = Define `
  exists_match env refs ps v <=>
    !vs. ?p. MEM p ps /\ pmatch env refs p v vs <> No_match`

val get_exn_tags_thm = Q.store_thm("get_exn_tags_thm",
  `!pats exns res.
     get_exn_tags pats exns = SOME res
     ==>
       (!pat.
         MEM pat pats ==>
           ?cid ps.
             pat = Pcon (SOME (cid, NONE)) ps /\
             EVERY is_unconditional ps /\
             lookup cid res = NONE) /\
       (!cid arity.
         (lookup cid exns = NONE ==> lookup cid res = NONE) /\
         (lookup cid exns = SOME arity /\
          lookup cid res = NONE ==>
           ?ps'.
             MEM (Pcon (SOME (cid, NONE)) ps') pats /\
             EVERY is_unconditional ps' /\
             LENGTH ps' = arity))`,
  Induct \\ simp [get_exn_tags_def]
  >- (rw [] \\ CCONTR_TAC \\ fs [] \\ fs [])
  \\ Cases \\ fs []
  \\ ntac 3 (PURE_TOP_CASE_TAC \\ fs [])
  \\ rpt gen_tac
  \\ rw [] \\ fs [case_eq_thms] \\ first_x_assum drule \\ rw []
  \\ TRY (Cases_on `q = cid` \\ fs [])
  \\ metis_tac [lookup_delete]);

val get_dty_tags_thm = Q.store_thm("get_dty_tags_thm",
  `!pats tags res.
     get_dty_tags pats tags = SOME res
     ==>
       (!pat.
         MEM pat pats ==>
           ?cid tyid ps left.
             pat = Pcon (SOME (cid, SOME tyid)) ps /\
             EVERY is_unconditional ps /\
             lookup (LENGTH ps) res = SOME left /\
             cid NOTIN domain left) /\
       (!arity ts.
         lookup arity tags = SOME ts ==>
           ?left.
             lookup arity res = SOME left /\
             domain left SUBSET domain ts /\
             (!tag.
               tag IN domain ts /\
               tag NOTIN domain left ==>
                 ?ps' tyid'.
                   MEM (Pcon (SOME (tag, SOME tyid')) ps') pats /\
                   EVERY is_unconditional ps' /\
                   LENGTH ps' = arity))`,
  Induct \\ simp [get_dty_tags_def]
  \\ Cases \\ fs []
  \\ ntac 3 (PURE_TOP_CASE_TAC \\ fs [])
  \\ rpt gen_tac
  \\ rw [] \\ fs [case_eq_thms] \\ first_x_assum drule \\ rw []
  >-
   (first_x_assum (qspec_then `LENGTH l` mp_tac)
    \\ simp [lookup_insert]
    \\ rw [SUBSET_DEF]
    \\ metis_tac [])
  \\ first_x_assum (qspec_then `arity` mp_tac)
  \\ simp [lookup_insert]
  \\ rw [] \\ fs [SUBSET_DEF] \\ rw []
  \\ metis_tac []);

val pmatch_Pcon_No_match = Q.store_thm("pmatch_Pcon_No_match",
  `env.check_ctor /\
   EVERY is_unconditional ps
   ==>
   ((pmatch env s (Pcon (SOME (c1,t)) ps) v bindings = No_match) <=>
     ?c2 vs.
       v = Conv (SOME (c2,t)) vs /\
       ((c1,t), LENGTH ps) IN env.c /\
       (LENGTH ps = LENGTH vs ==> c1 <> c2))`,
  Cases_on `v` \\ fs [pmatch_def]
  \\ Cases_on `o'` \\ fs [pmatch_def]
  \\ PairCases_on `x` \\ fs [pmatch_def]
  \\ rw [ctor_same_type_def, same_ctor_def] \\ fs []
  \\ metis_tac [is_unconditional_list_thm]);

val exhaustive_exists_match = Q.store_thm("exhaustive_exists_match",
  `!ctors ps env.
     exhaustive_match ctors ps /\
     env.check_ctor /\
     ctor_rel ctors env.c
     ==>
     !refs v. exists_match env refs ps v`,
  rw [exhaustive_match_def, exists_match_def]
  >- (fs [EXISTS_MEM] \\ metis_tac [is_unconditional_thm])
  \\ every_case_tac \\ fs []
  >- (* exn *) cheat (* TODO *)
  \\ (* dty *) cheat (* TODO *)
  );

(* TODO move to flatProps *)
val pmatch_any_match = Q.store_thm ("pmatch_any_match",
  `(∀env s p v vs vs'. pmatch env s p v vs = Match vs' ⇒
       ∀vs. ∃vs'. pmatch env s p v vs = Match vs') ∧
    (∀env s ps vs ws ws'. pmatch_list env s ps vs ws = Match ws' ⇒
       ∀ws. ∃ws'. pmatch_list env s ps vs ws = Match ws')`,
  ho_match_mp_tac pmatch_ind
  \\ rw [pmatch_def] \\ fs []
  \\ pop_assum mp_tac
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ metis_tac [semanticPrimitivesTheory.match_result_distinct]);

(* TODO move to flatProps *)
val pmatch_any_no_match = Q.store_thm("pmatch_any_no_match",
  `(∀env s p v vs . pmatch env s p v vs = No_match ⇒
       ∀vs. pmatch env s p v vs = No_match) ∧
    (∀env s ps vs ws. pmatch_list env s ps vs ws = No_match ⇒
       ∀ws. pmatch_list env s ps vs ws = No_match)`,
  ho_match_mp_tac pmatch_ind
  \\ rw [pmatch_def] \\ fs []
  \\ pop_assum mp_tac
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ metis_tac [semanticPrimitivesTheory.match_result_distinct,
                pmatch_any_match]);

val s1 = mk_var ("s1",
  ``flatSem$evaluate`` |> type_of |> strip_fun |> snd
  |> dest_prod |> fst)

(* TODO simplification to avoid Cases_on `Rerr...` *)
val compile_exps_evaluate = Q.store_thm("compile_exps_evaluate",
  `(!env1 ^s1 xs t1 r1.
      evaluate env1 s1 xs = (t1, r1) /\
      r1 <> Rerr (Rabort Rtype_error)
      ==>
      !ctors env2 s2 ctors_pre.
        env_rel ctors env1 env2 /\
        state_rel ctors s1 s2 /\
        ctors_pre SUBMAP ctors
        ==>
        ?t2 r2.
          result_rel (LIST_REL o v_rel) ctors r1 r2 /\
          state_rel ctors t1 t2 /\
          evaluate env2 s2 (compile_exps ctors_pre xs) = (t2, r2)) /\
   (!env1 ^s1 v ps err_v t1 r1.
     evaluate_match env1 s1 v ps err_v = (t1, r1) /\
     r1 <> Rerr (Rabort Rtype_error)
     ==>
     !ps2 is_handle ctors env2 s2 v2 tr err_v2 ctors_pre.
       env_rel ctors env1 env2 /\
       state_rel ctors s1 s2 /\
       ctors_pre SUBMAP ctors /\
       v_rel ctors v v2 /\
       v_rel ctors err_v err_v2 /\
       (is_handle  ==> err_v = v) /\
       (~is_handle ==> err_v = bind_exn_v) /\
       (ps2 = add_default tr is_handle F ps \/
        exists_match env1 s1.refs (MAP FST ps) v /\
        ps2 = add_default tr is_handle T ps)
       ==>
       ?t2 r2.
         result_rel (LIST_REL o v_rel) ctors r1 r2 /\
         state_rel ctors t1 t2 /\
         evaluate_match env2 s2 v2
           (MAP (\(p,e). (p, HD (compile_exps ctors_pre [e]))) ps2)
           err_v2 = (t2, r2))`,
  ho_match_mp_tac evaluate_ind
  \\ rw [compile_exps_def, evaluate_def] \\ fs [result_rel_def]
  >-
   (simp [Once evaluate_cons]
    \\ fs [case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs [PULL_EXISTS]
    \\ rpt (first_x_assum drule \\ rpt (disch_then drule) \\ rw [])
    \\ fs [result_rel_thms]
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rw []
    \\ rename1 `Rerr rrr` \\ Cases_on `rrr` \\ fs [result_rel_thms])
  >-
   (fs [case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs [PULL_EXISTS]
    \\ rpt (first_x_assum drule \\ rpt (disch_then drule) \\ rw [])
    \\ fs [result_rel_thms]
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rw []
    \\ rename1 `Rerr rrr` \\ Cases_on `rrr` \\ fs [result_rel_thms])
  >- (* Handle *)
   (fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ last_x_assum match_mp_tac \\ fs [add_default_def, env_rel_def]
    \\ qexists_tac `T` \\ rw []
    \\ metis_tac [exhaustive_exists_match, exhaustive_SUBMAP])
  >-
   (fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ fs [case_eq_thms, pair_case_eq, PULL_EXISTS]
    \\ first_x_assum drule
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ fsrw_tac [DNF_ss] [env_rel_def]
    \\ rename1 `Rerr rrr` \\ Cases_on `rrr` \\ fs [])
  >- fs [env_rel_def]
  >-
   (fs [case_eq_thms, pair_case_eq, bool_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ qpat_x_assum `_ ==> _` mp_tac
    \\ impl_keep_tac >- fs [env_rel_def]
    \\ rpt (disch_then drule) \\ rfs [] \\ fs [compile_exps_LENGTH]
    \\ fsrw_tac [DNF_ss] [env_rel_def] \\ rw []
    \\ rename1 `Rerr rrr` \\ Cases_on `rrr` \\ fs [])
  >-
   (every_case_tac \\ fs [] \\ rw [] \\ fs [env_rel_def]
    \\ map_every imp_res_tac [nv_rel_ALOOKUP_v_rel, MEM_LIST_REL] \\ rfs [])
  >- (simp [Once v_rel_cases] \\ metis_tac [env_rel_def])
  >- (* App *)
   (fs [case_eq_thms, pair_case_eq, bool_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ last_x_assum drule
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ rpt (qpat_x_assum `(_,_) = _` (assume_tac o GSYM)) \\ fs []
    \\ imp_res_tac EVERY2_REVERSE
    >- metis_tac [do_opapp_thm, state_rel_def]
    >-
     (
      drule (GEN_ALL do_opapp_thm) \\ disch_then drule \\ rw [] \\ fs []
      \\ sg `env_rel ctors (env1 with v := env') (env2 with v := nvs2)`
      >- (fs [env_rel_def] \\ rfs [] \\ fs [])
      \\ sg `state_rel ctors (dec_clock s') (dec_clock t2)`
      >- fs [state_rel_def, dec_clock_def]
      \\ first_x_assum drule
      \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ fs [state_rel_def])
    >-
     (drule (GEN_ALL do_app_thm) \\ rpt (disch_then drule) \\ rw [] \\ fs []
      \\ Cases_on `r` \\ Cases_on `r2` \\ fs [evaluateTheory.list_result_def]
      \\ Cases_on `e` \\ fs [])
    \\ rename1 `Rerr rrr` \\ Cases_on `rrr` \\ fs [])
  >- (* If *)
   (fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ TRY (rename1 `Rerr rrr` \\ Cases_on `rrr` \\ fs [] \\ NO_TAC)
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ fs [do_if_def, bool_case_eq, Boolv_def] \\ rw [] \\ fs [])
  >- (* Mat *)
   (fs [case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ rw []
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rw []
    >-
     (last_x_assum drule \\ rpt (disch_then drule)
      \\ disch_then match_mp_tac
      \\ qexists_tac `F` \\ rw [add_default_def] \\ fs [bind_exn_v_def]
      \\ metis_tac [exhaustive_exists_match, env_rel_def, exhaustive_SUBMAP])
    \\ rename1 `Rerr rrr` \\ Cases_on `rrr` \\ fs [])
  >- (* Let *)
   (fs [case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ rw [] \\ fs [PULL_EXISTS]
    \\ TRY (rename1 `Rerr rrr` \\ Cases_on `rrr` \\ fs [] \\ NO_TAC)
    \\ last_x_assum match_mp_tac
    \\ fs [env_rel_def]
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rw [] \\ fs []
    \\ fs [libTheory.opt_bind_def] \\ CASE_TAC \\ fs []
    \\ simp [Once v_rel_cases])
  >- (* Letrec *)
   (rw [] \\ TRY (metis_tac [compile_exps_MAP_FST])
    \\ first_x_assum match_mp_tac \\ fs [env_rel_def]
    \\ simp [nv_rel_LIST_REL, LIST_REL_EL_EQN]
    \\ fs [build_rec_env_merge]
    \\ conj_asm1_tac >- fs [env_rel_def, LIST_REL_EL_EQN, nv_rel_LIST_REL]
    \\ fs [EL_APPEND_EQN] \\ rw [] \\ fs [EL_MAP] \\ fs [ELIM_UNCURRY]
    >- (simp [Once v_rel_cases, MAP_EQ_f, ELIM_UNCURRY] \\ metis_tac [])
    \\ fs [env_rel_def, nv_rel_LIST_REL, LIST_REL_EL_EQN, ELIM_UNCURRY])
  >-
   (fs [add_default_def] \\ fs [PULL_EXISTS]
    \\ rw [evaluate_def, pat_bindings_def, pmatch_def, compile_exps_def,
           exists_match_def] \\ fs [env_rel_def]
    \\ rw [] \\ fs [] \\ EVAL_TAC
    \\ cheat (* TODO bind_tag,NONE not there *))
  >- fs [exists_match_def]
  >-
   (`LIST_REL (sv_rel (v_rel ctors)) s1.refs s2.refs` by fs [state_rel_def]
    \\ reverse every_case_tac \\ fs []
    \\ drule (CONJUNCT1 pmatch_thm) \\ fs []
    \\ rpt (disch_then drule)
    \\ disch_then (qspecl_then [`env2`, `[]`] mp_tac)
    \\ (impl_tac >- simp [Once v_rel_cases])
    \\ rw []
    >-
     (Cases_on `pmatch env2 s2.refs p v2 []` \\ fs [match_rel_def]
      \\ `env_rel ctors (env1 with v := a ++ env1.v)
                        (env2 with v := a' ++ env2.v)` by
       (fs [env_rel_def, nv_rel_LIST_REL]
        \\ conj_tac >- metis_tac []
        \\ match_mp_tac EVERY2_APPEND_suff \\ fs [])
      \\ first_x_assum drule
      \\ rpt (disch_then drule)
      \\ rw [] \\ fs []
      \\ rw [add_default_def] \\ fs [compile_exps_def, evaluate_def])
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ disch_then (qspec_then `tr` mp_tac o CONV_RULE SWAP_FORALL_CONV) \\ fs []
    \\ qpat_abbrev_tac `ps2 = add_default X Y F ps`
    \\ qpat_abbrev_tac `ps3 = add_default X Y T ps`
    \\ strip_tac
    \\ first_assum (qspec_then `ps2` mp_tac)
    \\ simp_tac std_ss []
    \\ strip_tac \\ fs []
    \\ first_x_assum (qspec_then `ps3` mp_tac)
    \\ rw [] \\ fs [Abbr`ps2`, Abbr`ps3`]
    \\ rfs [add_default_def] \\ rw [] \\ fs [evaluate_def])
  \\ `LIST_REL (sv_rel (v_rel ctors)) s1.refs s2.refs` by fs [state_rel_def]
  \\ reverse every_case_tac \\ fs []
  \\ drule (CONJUNCT1 pmatch_thm) \\ fs []
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`env2`, `[]`] mp_tac)
  \\ (impl_tac >- simp [Once v_rel_cases])
  \\ rw []
  >-
   (Cases_on `pmatch env2 s2.refs p v2 []` \\ fs [match_rel_def]
    \\ `env_rel ctors (env1 with v := a ++ env1.v)
                      (env2 with v := a' ++ env2.v)` by
     (fs [env_rel_def, nv_rel_LIST_REL]
      \\ conj_tac >- metis_tac []
      \\ match_mp_tac EVERY2_APPEND_suff \\ fs [])
    \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ rw [] \\ fs []
    \\ rw [add_default_def] \\ fs [compile_exps_def, evaluate_def])
  \\ first_x_assum drule
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then `tr` mp_tac o CONV_RULE SWAP_FORALL_CONV) \\ fs []
  \\ qpat_abbrev_tac `ps2 = add_default X Y F ps`
  \\ qpat_abbrev_tac `ps3 = add_default X Y T ps`
  \\ strip_tac
  \\ first_assum (qspec_then `ps2` mp_tac)
  \\ simp_tac std_ss []
  \\ strip_tac \\ fs []
  \\ first_x_assum (qspec_then `ps3` mp_tac)
  \\ fs [Abbr`ps2`,Abbr`ps3`, add_default_def] \\ rw [] \\ fs []
  \\ fs [evaluate_def, compile_exps_def] \\ rw [] \\ fs []
  \\ fs [exists_match_def, PULL_EXISTS]
  \\ rw [] \\ fsrw_tac [DNF_ss] []
  \\ metis_tac [pmatch_any_no_match]);

(* ------------------------------------------------------------------------- *)
(* Compile declarations                                                      *)
(* ------------------------------------------------------------------------- *)

val evaluate_compile_dec = Q.store_thm("evaluate_compile_dec",
  `T`,
  cheat (* TODO *)
  );

val evaluate_compile_decs = Q.store_thm("evaluate_compile_decs",
  `T`,
  cheat (* TODO *)
  );

val _ = export_theory();

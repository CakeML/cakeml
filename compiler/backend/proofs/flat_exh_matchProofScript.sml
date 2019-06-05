(*
  Correctness proof for flat_exh_match
*)

open semanticPrimitivesTheory semanticPrimitivesPropsTheory;
open preamble flatPropsTheory flatSemTheory flat_exh_matchTheory
(* TODO: fix grammar ancestry problems when these opens are combined *)

val _ = new_theory "flat_exh_matchProof"

(* ------------------------------------------------------------------------- *)
(* Compile lemmas                                                            *)
(* ------------------------------------------------------------------------- *)

val _ = set_grammar_ancestry["flat_exh_match","flatSem","flatProps","ffi","misc"];

Theorem compile_exps_SING_HD[simp]:
  LENGTH (compile_exps exh [x]) = 1 ∧
  [HD (compile_exps exh [x])] = compile_exps exh [x]
Proof
  Cases_on `compile_exps exh [x]`
  \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`) \\ fs [compile_exps_LENGTH]
QED

Theorem compile_exps_CONS:
  compile_exps exh (x::xs) = compile_exps exh [x] ++ compile_exps exh xs
Proof qid_spec_tac `x` \\ Induct_on `xs` \\ rw [compile_exps_def]
QED

Theorem compile_exps_APPEND:
   compile_exps exh (xs ++ ys) = compile_exps exh xs ++ compile_exps exh ys
Proof
  map_every qid_spec_tac [`ys`,`xs`] \\ Induct \\ rw [compile_exps_def]
  \\ rw [Once compile_exps_CONS]
  \\ rw [Once (GSYM compile_exps_CONS)]
QED

Theorem compile_exps_REVERSE[simp]:
  REVERSE (compile_exps exh xs) = compile_exps exh (REVERSE xs)
Proof
  Induct_on `xs` \\ rw [compile_exps_def]
  \\ rw [Once compile_exps_CONS, Once compile_exps_APPEND]
  \\ `LENGTH (compile_exps exh [h]) = 1`
    by fs [compile_exps_LENGTH]
  \\ fs [LENGTH_EQ_NUM_compute]
QED

Theorem compile_exps_MAP_FST:
   MAP FST funs =
   MAP FST (MAP (\(a,b,c). (a,b,HD (compile_exps ctors [c]))) funs)
Proof
  Induct_on `funs` \\ rw []
  \\ PairCases_on `h` \\ fs []
QED

Theorem compile_exps_find_recfun:
   !ls f exh.
     find_recfun f (MAP (\(a,b,c). (a, b, HD (compile_exps exh [c]))) ls) =
     OPTION_MAP (\(x,y). (x, HD (compile_exps exh [y]))) (find_recfun f ls)
Proof
  Induct \\ rw []
  >- fs [semanticPrimitivesTheory.find_recfun_def]
  \\ simp [Once semanticPrimitivesTheory.find_recfun_def]
  \\ once_rewrite_tac [EQ_SYM_EQ]
  \\ simp [Once semanticPrimitivesTheory.find_recfun_def]
  \\ every_case_tac \\ fs []
QED

Theorem exhaustive_SUBMAP:
   !ps ctors ctors_pre.
     exhaustive_match ctors_pre ps /\
     ctors_pre SUBMAP ctors
     ==>
     exhaustive_match ctors ps
Proof
  Induct \\ rw [exhaustive_match_def] \\ fs []
  \\ every_case_tac \\ fs [is_unconditional_def]
  \\ imp_res_tac FLOOKUP_SUBMAP \\ fs [] \\ rw []
QED

(* ------------------------------------------------------------------------- *)
(* Value relations                                                           *)
(* ------------------------------------------------------------------------- *)

val ok_ctor_def = Define `
  (ok_ctor ctors (Conv x ps) <=>
    !id tid.
      x = SOME (id, SOME tid) ==>
      ?ars max.
        FLOOKUP ctors tid = SOME ars /\
        lookup (LENGTH ps) ars = SOME max /\
        id < max) /\
  (ok_ctor ctors v <=> T)`

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!ctors v. v_rel ctors (Litv v) (Litv v)) /\
  (!ctors n. v_rel ctors (Loc n) (Loc n)) /\
  (!ctors vs1 vs2.
     LIST_REL (v_rel ctors) vs1 vs2
     ==>
     v_rel ctors (Vectorv vs1) (Vectorv vs2)) /\
  (!ctors t v1 v2 ctors_pre.
     LIST_REL (v_rel ctors) v1 v2 /\
     ctors_pre SUBMAP ctors /\
     ok_ctor ctors_pre (Conv t v1)
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

Theorem v_rel_thms[simp]:
   (v_rel ctors (Litv l) v <=> v = Litv l) /\
   (v_rel ctors v (Litv l) <=> v = Litv l) /\
   (v_rel ctors (Loc n) v  <=> v = Loc n) /\
   (v_rel ctors v (Loc n)  <=> v = Loc n) /\
   (v_rel ctors (Conv t x) v <=>
     ?y. v = Conv t y /\ LIST_REL (v_rel ctors) x y /\
     ok_ctor ctors v) /\
   (v_rel ctors v (Conv t x) <=>
     ?y. v = Conv t y /\ LIST_REL (v_rel ctors) y x /\
     ok_ctor ctors v) /\
   (v_rel ctors (Vectorv x) v <=>
     ?y. v = Vectorv y /\ LIST_REL (v_rel ctors) x y) /\
   (v_rel ctors v (Vectorv x) <=>
     ?y. v = Vectorv y /\ LIST_REL (v_rel ctors) y x)
Proof
   rw [] \\ Cases_on `v` \\ rw [Once v_rel_cases, EQ_SYM_EQ, ok_ctor_def]
   \\ Cases_on `t` \\ Cases_on `o'` \\ fs []
   \\ every_case_tac \\ fs []
   \\ metis_tac [SUBMAP_REFL, LIST_REL_EL_EQN, FLOOKUP_SUBMAP]
QED

Theorem v_rel_Boolv:
  init_ctors SUBMAP ctors ==>
  v_rel ctors (Boolv x) (Boolv x)
Proof
  Cases_on `x` \\ fs [Once v_rel_cases, Boolv_def] \\ rw []
  \\ asm_exists_tac \\ fs [ok_ctor_def]
  \\ EVAL_TAC \\ rw [lookup_def]
QED

Theorem nv_rel_LIST_REL:
   !xs ys ctors.
     nv_rel ctors xs ys <=>
     LIST_REL (\(n1, v1) (n2, v2). n1 = n2 /\ v_rel ctors v1 v2) xs ys
Proof
  Induct \\ rw [Once (CONJUNCT2 v_rel_cases)]
  \\ PairCases_on `h` \\ Cases_on `ys` \\ fs []
  \\ PairCases_on `h` \\ fs [] \\ metis_tac []
QED

Theorem nv_rel_NIL[simp]:
   nv_rel ctors [] []
Proof
rw [Once v_rel_cases]
QED

val ctor_rel_def = Define `
  ctor_rel ctors (c : ((ctor_id # type_id) # num) set) <=>
  !ty id arity.
    ((id, SOME ty), arity) IN c <=>
      ?ars max.
        FLOOKUP ctors ty = SOME ars /\
        lookup arity ars = SOME max /\
        id < max`

val env_rel_def = Define `
  env_rel ctors env1 env2 <=>
    (* Constructors *)
    initial_ctors SUBSET env1.c /\
    init_ctors SUBMAP ctors /\
    ctor_rel ctors env1.c /\
    (* Flags *)
    env1.check_ctor /\
    env2.check_ctor /\
    env1.c = env2.c /\
    ~env1.exh_pat /\
    env2.exh_pat /\
    (* Value relation *)
    nv_rel ctors env1.v env2.v`;

val state_rel_def = Define `
  state_rel ctors s1 s2 <=>
    s1.clock = s2.clock /\
    LIST_REL (sv_rel (v_rel ctors)) s1.refs s2.refs /\
    s1.ffi = s2.ffi /\
    LIST_REL (OPTREL (v_rel ctors)) s1.globals s2.globals`;

val result_rel_def = Define `
  (result_rel R ctors (Rval v1) (Rval v2) <=>
    R ctors v1 v2) /\
  (result_rel R ctors (Rerr (Rraise v1)) (Rerr (Rraise v2)) <=>
    v_rel ctors v1 v2) /\
  (result_rel R ctors (Rerr (Rabort e1)) (Rerr (Rabort e2)) <=>
    e1 = e2) /\
  (result_rel R ctors res1 res2 <=> F)`

Theorem result_rel_thms[simp]:
   (!ctors v1 r.
     result_rel R ctors (Rval v1) r <=>
     ?v2. r = Rval v2 /\ R ctors v1 v2) /\
   (!ctors v2 r.
     result_rel R ctors r (Rval v2) <=>
     ?v1. r = Rval v1 /\ R ctors v1 v2) /\
   (!ctors err r.
     result_rel R ctors (Rerr err) r <=>
       (?v1 v2.
         err = Rraise v1 /\ r = Rerr (Rraise v2) /\
         v_rel ctors v1 v2) \/
       (?a.  err = Rabort a /\ r = Rerr (Rabort a))) /\
   (!ctors err r.
     result_rel R ctors r (Rerr err) <=>
       (?v1 v2.
         err = Rraise v2 /\ r = Rerr (Rraise v1) /\
         v_rel ctors v1 v2) \/
       (?a.  err = Rabort a /\ r = Rerr (Rabort a)))
Proof
  rpt conj_tac \\ ntac 2 gen_tac \\ Cases \\ rw [result_rel_def]
  \\ Cases_on `e` \\ rw [result_rel_def]
  \\ Cases_on `err` \\ fs [result_rel_def, EQ_SYM_EQ]
QED

val match_rel_def = Define `
  (match_rel ctors (Match env1) (Match env2) <=> nv_rel ctors env1 env2) /\
  (match_rel ctors No_match No_match <=> T) /\
  (match_rel ctors Match_type_error Match_type_error <=> T) /\
  (match_rel ctors _ _ <=> F)`

Theorem match_rel_thms[simp]:
   (match_rel ctors Match_type_error e <=> e = Match_type_error) /\
   (match_rel ctors e Match_type_error <=> e = Match_type_error) /\
   (match_rel ctors No_match e <=> e = No_match) /\
   (match_rel ctors e No_match <=> e = No_match)
Proof
  Cases_on `e` \\ rw [match_rel_def]
QED

Theorem v_rel_v_to_char_list:
   !v1 v2 xs ctors.
     v_to_char_list v1 = SOME xs /\
     v_rel ctors v1 v2
     ==>
     v_to_char_list v2 = SOME xs
Proof
  ho_match_mp_tac v_to_char_list_ind \\ rw []
  \\ fs [v_to_char_list_def, case_eq_thms]
  \\ rw [] \\ metis_tac []
QED

Theorem v_rel_v_to_list:
   !v1 v2 xs ctors.
     v_to_list v1 = SOME xs /\
     v_rel ctors v1 v2
     ==>
     ?ys. v_to_list v2 = SOME ys /\
          LIST_REL (v_rel ctors) xs ys
Proof
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def, case_eq_thms] \\ rw []
  \\ metis_tac []
QED

Theorem v_rel_vs_to_string:
   !v1 v2 xs ctors.
     vs_to_string v1 = SOME xs /\
     LIST_REL (v_rel ctors) v1 v2
     ==>
     vs_to_string v2 = SOME xs
Proof
  ho_match_mp_tac vs_to_string_ind \\ rw []
  \\ fs [vs_to_string_def, case_eq_thms] \\ rw []
  \\ metis_tac []
QED

Theorem v_rel_list_to_v_APPEND:
   !xs1 xs2 ctors ys1 ys2.
     v_rel ctors (list_to_v xs1) (list_to_v xs2) /\
     v_rel ctors (list_to_v ys1) (list_to_v ys2)
     ==>
     v_rel ctors (list_to_v (xs1 ++ ys1)) (list_to_v (xs2 ++ ys2))
Proof
  Induct \\ rw [] \\ fs [list_to_v_def]
  \\ Cases_on `xs2` \\ fs [list_to_v_def, ok_ctor_def]
QED

Theorem v_rel_list_to_v:
   !v1 v2 xs ys ctors.
   v_to_list v1 = SOME xs /\
   v_to_list v2 = SOME ys /\
   v_rel ctors v1 v2
   ==>
   v_rel ctors (list_to_v xs) (list_to_v ys)
Proof
  ho_match_mp_tac v_to_list_ind \\ rw []
  \\ fs [v_to_list_def, case_eq_thms] \\ rw []
  \\ fs [list_to_v_def, ok_ctor_def]
  \\ metis_tac []
QED

Theorem v_rel_Unitv[simp]:
   v_rel ctors (Unitv cc) (Unitv cc)
Proof
  EVAL_TAC
  \\ rw[v_rel_cases]
  \\ EVAL_TAC
  \\ rw[]
QED

Theorem nv_rel_ALOOKUP_v_rel:
   !xs ys ctors n x.
     nv_rel ctors xs ys /\
     ALOOKUP xs n = SOME x
     ==>
     ?y.
     ALOOKUP ys n = SOME y /\ v_rel ctors x y
Proof
  Induct \\ rw []
  \\ qhdtm_x_assum `nv_rel` mp_tac
  \\ rw [Once (CONJUNCT2 v_rel_cases)]
  \\ fs [ALOOKUP_def, bool_case_eq]
QED

(* ------------------------------------------------------------------------- *)
(* Various semantics preservation theorems                                   *)
(* ------------------------------------------------------------------------- *)

Theorem do_eq_thm:
   (!v1 v2 r ctors v1' v2'.
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
     do_eq_list vs1' vs2' = r)
Proof
  ho_match_mp_tac do_eq_ind \\ rw [do_eq_def] \\ fs [] \\ rw [do_eq_def]
  \\ TRY (metis_tac [LIST_REL_LENGTH])
  \\ TRY
   (rpt (qhdtm_x_assum `v_rel` mp_tac \\ rw [Once v_rel_cases])
    \\ rw [do_eq_def] \\ NO_TAC)
  \\ every_case_tac \\ fs [] \\ res_tac \\ fs []
QED

Theorem pmatch_thm:
   (!env refs p v vs r ctors refs1 v1 env1 vs1.
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
       match_rel ctors r r1)
Proof
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
  \\ metis_tac [match_rel_def]
QED

Theorem do_opapp_thm:
   do_opapp vs1 = SOME (nvs1, e) /\
   LIST_REL (v_rel ctors) vs1 vs2
   ==>
   ?ctors_pre nvs2.
     nv_rel ctors nvs1 nvs2 /\
     ctors_pre SUBMAP ctors /\
     do_opapp vs2 = SOME (nvs2, HD (compile_exps ctors_pre [e]))
Proof
  simp [do_opapp_def, pair_case_eq, case_eq_thms, PULL_EXISTS]
  \\ rw [] \\ fs [PULL_EXISTS] \\ rw [] \\ fs []
  \\ fs [Once v_rel_cases] \\ rw [] \\ fs [PULL_EXISTS]
  \\ TRY
   (qpat_x_assum `ok_ctor _ (Conv t v1)` mp_tac
    \\ Cases_on `t` \\ fs [ok_ctor_def]
    >- metis_tac []
    \\ PairCases_on `x` \\ fs []
    \\ Cases_on `x1` \\ fs [] \\ rw []
    \\ metis_tac [LIST_REL_LENGTH, flookup_thm, FLOOKUP_SUBMAP])
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
  \\ TRY
   (qpat_x_assum `ok_ctor _ (Conv t _)` mp_tac
    \\ simp [ok_ctor_def]
    \\ fs [ok_ctor_def] \\ rw []
    >- metis_tac [FLOOKUP_SUBMAP, LIST_REL_LENGTH])
  \\ TRY (conj_tac >- (simp [Once v_rel_cases, nv_rel_LIST_REL] \\ metis_tac []))
  \\ match_mp_tac EVERY2_APPEND_suff \\ fs [EVERY2_MAP]
  \\ match_mp_tac EVERY2_refl \\ rw [UNCURRY]
  \\ simp [Once v_rel_cases, nv_rel_LIST_REL] \\ metis_tac []
QED

val store_v_same_type_cases = Q.prove (
  `(!v r. store_v_same_type (Refv v) r <=> ?v1. r = Refv v1) /\
   (!v r. store_v_same_type r (Refv v) <=> ?v1. r = Refv v1) /\
   (!v r. store_v_same_type (Varray v) r <=> ?v1. r = Varray v1) /\
   (!v r. store_v_same_type r (Varray v) <=> ?v1. r = Varray v1) /\
   (!v r. store_v_same_type (W8array v) r <=> ?v1. r = W8array v1) /\
   (!v r. store_v_same_type r (W8array v) <=> ?v1. r = W8array v1)`,
  rpt conj_tac \\ gen_tac \\ Cases \\ rw [store_v_same_type_def]);

Theorem do_app_thm:
   do_app cc s1 op vs1 = SOME (t1, r1) /\
   init_ctors SUBMAP ctors /\
   state_rel ctors s1 s2 /\
   LIST_REL (v_rel ctors) vs1 vs2
   ==>
   ?t2 r2.
     result_rel v_rel ctors r1 r2 /\
     state_rel ctors t1 t2 /\
     do_app cc s2 op vs2 = SOME (t2, r2)
Proof
  rpt strip_tac \\ qhdtm_x_assum `do_app` mp_tac
  \\ Cases_on `op = Opb Lt \/ op = Opb Gt \/ op = Opb Leq \/ op = Opb Geq \/
               op = Opn Plus \/ op = Opn Minus \/ op = Opn Times \/
               op = Opn Divide \/ op = Opn Modulo`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ fs [opb_lookup_def, v_rel_Boolv]
    \\ rw [div_exn_v_def, Once v_rel_cases, ok_ctor_def] \\ metis_tac [])
  \\ Cases_on `(?sz. op = Opw sz Andw \/ op = Opw sz Orw \/ op = Opw sz Xor \/
                     op = Opw sz Add \/ op = Opw sz Sub) \/
               (?sz s k. op = Shift sz s k)`
  >-
   (fs [] \\ fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS]
    \\ rw [] \\ fs [])
  \\ Cases_on `op = Equality`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ imp_res_tac do_eq_thm \\ fs [v_rel_Boolv])
  \\ Cases_on `(?f. op = FP_cmp f) \/ (?f. op = FP_bop f) \/
               (?f. op = FP_uop f)`
  >-
   (fs [] \\ fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS]
    \\ rw [] \\ fs [v_rel_Boolv])
  \\ Cases_on `op = Opapp`
  >- (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS])
  \\ Cases_on `op = Opassign \/ op = Opderef`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS]
    \\ rw [] \\ fs [] \\ rw []
    \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
    \\ fs [store_alloc_def, store_lookup_def, store_assign_def, state_rel_def,
           LIST_REL_EL_EQN, store_v_same_type_cases] \\ rw []
    \\ fs [EL_LUPDATE] \\ rw [] \\ fs []
    \\ rename1 `nnn < LENGTH _.refs`
    \\ last_x_assum (qspec_then `nnn` mp_tac) \\ fs []
    \\ rw [Once sv_rel_cases] \\ fs [ok_ctor_def])
  \\ Cases_on `op = Opref`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [store_alloc_def, state_rel_def, LIST_REL_EL_EQN]
    \\ rw [] \\ fs []
    \\ rename1 `nnn < _`
    \\ rw [EL_APPEND_EQN]
    \\ qmatch_goalsub_abbrev_tac `EL x [_]`
    \\ `x = 0` by fs [Abbr`x`] \\ fs [])
  \\ Cases_on `op = Aw8alloc`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    >- (rw [Once v_rel_cases, subscript_exn_v_def, ok_ctor_def] \\ metis_tac [])
    \\ rpt (pairarg_tac \\ fs []) \\ rveq
    \\ fs [store_alloc_def, state_rel_def, LIST_REL_EL_EQN] \\ rveq \\ fs []
    \\ rw [EL_APPEND_EQN]
    \\ qmatch_goalsub_abbrev_tac `EL x _`
    \\ `x = 0` by fs [Abbr`x`] \\ fs [])
  \\ Cases_on `op = Aw8sub \/ op = Aw8length \/ op = Aw8update`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ rw [Once v_rel_cases, subscript_exn_v_def]
    \\ fs [store_lookup_def, state_rel_def, LIST_REL_EL_EQN] \\ rveq \\ fs []
    \\ rename1 `EL n _ = _`
    \\ last_assum (qspec_then `n` mp_tac)
    \\ (impl_tac >- fs [])
    \\ simp_tac std_ss [Once sv_rel_cases] \\ rw []
    \\ fs [store_assign_def, store_v_same_type_cases]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ rw [EL_LUPDATE, ok_ctor_def]
    \\ metis_tac [])
  \\ Cases_on `(?sz. op = WordFromInt sz) \/ (?sz. op = WordToInt sz)`
  >- (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs [])
  \\ Cases_on `op = CopyStrStr`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ rw [Once v_rel_cases, subscript_exn_v_def, ok_ctor_def]
    \\ metis_tac [])
  \\ Cases_on `op = CopyStrAw8`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ fs [store_lookup_def, store_assign_def, store_v_same_type_cases,
           state_rel_def, LIST_REL_EL_EQN] \\ rw [] \\ fs [PULL_EXISTS]
    \\ rw [Once v_rel_cases, subscript_exn_v_def, ok_ctor_def]
    \\ last_assum (qspec_then `dst` mp_tac)
    \\ (impl_tac >- fs [])
    \\ simp_tac std_ss [Once sv_rel_cases] \\ rw [EL_LUPDATE] \\ rw []
    \\ metis_tac [])
  \\ Cases_on `op = CopyAw8Str`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ fs [store_lookup_def, state_rel_def, LIST_REL_EL_EQN] \\ rw []
    \\ fs [PULL_EXISTS] \\ rw [Once v_rel_cases, subscript_exn_v_def]
    \\ last_assum (qspec_then `src` mp_tac)
    \\ (impl_tac >- fs [])
    \\ simp_tac std_ss [Once sv_rel_cases] \\ rw []
    \\ rw [ok_ctor_def] \\ metis_tac [])
  \\ Cases_on `op = CopyAw8Aw8`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ fs [store_lookup_def, state_rel_def, store_assign_def,
           store_v_same_type_cases, LIST_REL_EL_EQN] \\ rw []
    \\ fs [PULL_EXISTS] \\ rw [Once v_rel_cases, subscript_exn_v_def]
    \\ rename1 `EL src _ = _ ws` \\ rename1 `EL dst _ = _ ds`
    \\ last_assum (qspec_then `dst` mp_tac)
    \\ (impl_tac >- fs [])
    \\ simp_tac std_ss [Once sv_rel_cases] \\ rw []
    \\ last_assum (qspec_then `src` mp_tac)
    \\ (impl_tac >- fs [])
    \\ simp_tac std_ss [Once sv_rel_cases] \\ rw []
    \\ rw [EL_LUPDATE]
    \\ rw [ok_ctor_def] \\ metis_tac [])
  \\ Cases_on `op = Ord \/ op = Chr \/ op = Chopb Lt \/ op = Chopb Gt \/
               op = Chopb Leq \/ op = Chopb Geq`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ fs [opb_lookup_def, v_rel_Boolv]
    \\ rw [Once v_rel_cases, chr_exn_v_def, ok_ctor_def]
    \\ metis_tac [])
  \\ Cases_on `op = Implode \/ op = Strsub \/ op = Strlen \/ op = Strcat`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ rw [Once v_rel_cases, subscript_exn_v_def, ok_ctor_def]
    \\ metis_tac [v_rel_v_to_char_list, v_rel_vs_to_string, v_rel_v_to_list])
  \\ Cases_on `op = VfromList \/ op = Vsub \/ op = Vlength`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ rw [subscript_exn_v_def, ok_ctor_def] \\ fs [LIST_REL_EL_EQN]
    \\ metis_tac [v_rel_v_to_list, LIST_REL_EL_EQN])
  \\ Cases_on `op = Aalloc`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ rw [subscript_exn_v_def, ok_ctor_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ fs [store_alloc_def, store_v_same_type_cases, state_rel_def,
           LIST_REL_EL_EQN] \\ rw [] \\ fs []
    \\ rw [EL_APPEND_EQN]
    \\ qmatch_goalsub_abbrev_tac `EL x _`
    \\ `x = 0` by fs [Abbr`x`] \\ fs []
    \\ rw [LIST_REL_REPLICATE_same])
  \\ Cases_on `op = Asub \/ op = Alength`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ rw [subscript_exn_v_def, ok_ctor_def]
    \\ fs [store_lookup_def, state_rel_def, LIST_REL_EL_EQN] \\ rw [] \\ fs []
    \\ fs [PULL_EXISTS]
    \\ rename1 `EL nnn _ = _`
    \\ last_assum (qspec_then `nnn` mp_tac)
    \\ (impl_tac >- fs [])
    \\ simp_tac std_ss [Once sv_rel_cases] \\ rw [] \\ fs []
    \\ fs [LIST_REL_EL_EQN])
  \\ Cases_on `op = Aupdate`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ rw [subscript_exn_v_def, ok_ctor_def]
    \\ fs [store_lookup_def, store_assign_def, store_v_same_type_cases,
           state_rel_def, LIST_REL_EL_EQN] \\ rw [] \\ fs []
    \\ fs [PULL_EXISTS]
    \\ rename1 `EL nnn _ = _`
    \\ last_assum (qspec_then `nnn` mp_tac)
    \\ (impl_tac >- fs [])
    \\ simp_tac std_ss [Once sv_rel_cases] \\ rw [] \\ fs []
    \\ fs [LIST_REL_EL_EQN]
    \\ rfs [] \\ rveq \\ fs []
    \\ rw [EL_LUPDATE] \\ fs [LIST_REL_EL_EQN] \\ rw []
    \\ rw [EL_LUPDATE] \\ rw [ok_ctor_def])
  \\ Cases_on `op = ConfigGC`
  >- (fs [do_app_def, case_eq_thms, pair_case_eq] \\ rw [] \\ fs [ok_ctor_def])
  \\ Cases_on `?s. op = FFI s`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ fs [store_lookup_def, store_assign_def, store_v_same_type_cases,
           state_rel_def, LIST_REL_EL_EQN] \\ rw [] \\ fs [] \\ rw [] \\ fs []
    \\ rename1 `EL nnn _ = _`
    \\ last_assum (qspec_then `nnn` mp_tac)
    \\ impl_tac >- fs []
    \\ simp_tac std_ss [Once sv_rel_cases] \\ rw []
    \\ rfs [] \\ rw []
    \\ rw [EL_LUPDATE] \\ rw [ok_ctor_def])
  \\ Cases_on `op = ListAppend`
  >-
   (fs [do_app_def, case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ rw []
    \\ imp_res_tac v_rel_v_to_list \\ fs []
    \\ metis_tac [v_rel_list_to_v, v_rel_list_to_v_APPEND])
  \\ Cases_on `?opn. op = Opn opn` >- (fs [] \\ Cases_on `opn` \\ fs [])
  \\ Cases_on `?opb. op = Opb opb` >- (fs [] \\ Cases_on `opb` \\ fs [])
  \\ Cases_on `?s opw. op = Opw s opw` >- (fs [] \\ Cases_on `opw` \\ fs [])
  \\ Cases_on `?opb. op = Chopb opb` >- (fs [] \\ Cases_on `opb` \\ fs [])
  \\ Cases_on `op` \\ fs [] \\ rw []
  \\ fs [do_app_def, pair_case_eq, case_eq_thms] \\ rw [] \\ fs []
  \\ fs [state_rel_def, LIST_REL_EL_EQN] \\ rw [] \\ fs []
  \\ fs [OPTREL_def, EL_LUPDATE, EL_APPEND_EQN] \\ rw [] \\ fs [EL_REPLICATE]
  \\ first_x_assum (qspec_then `n` mp_tac) \\ rw [] \\ fs []
  \\ rw [ok_ctor_def]
QED

(* ------------------------------------------------------------------------- *)
(* Compile expressions                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem is_unconditional_thm:
   !p env refs v vs.
     is_unconditional p
     ==>
     pmatch env refs p v vs <> No_match
Proof
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
  \\ res_tac \\ fs []
QED

Theorem is_unconditional_list_thm:
   !vs1 vs2 a b c.
   EVERY is_unconditional vs1
   ==>
   pmatch_list a b vs1 vs2 c <> No_match
Proof
  Induct >- (Cases \\ rw [pmatch_def])
  \\ gen_tac \\ Cases \\ rw [pmatch_def]
  \\ every_case_tac \\ fs []
  \\ metis_tac [is_unconditional_thm]
QED

val exists_match_def = Define `
  exists_match env refs ps v <=>
    !vs. ?p. MEM p ps /\ pmatch env refs p v vs <> No_match`

Theorem get_dty_tags_thm:
   !pats tags res.
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
                   LENGTH ps' = arity))
Proof
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
  \\ metis_tac []
QED

val pmatch_Pcon_No_match = Q.prove(
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

Theorem exhaustive_exists_match:
   !ctors ps env.
     exhaustive_match ctors ps /\
     env.check_ctor /\
     ctor_rel ctors env.c
     ==>
     !refs v. ok_ctor ctors v ==> exists_match env refs ps v
Proof
  rw [exhaustive_match_def, exists_match_def]
  >- (fs [EXISTS_MEM] \\ metis_tac [is_unconditional_thm])
  \\ every_case_tac \\ fs [get_dty_tags_def, case_eq_thms]
  \\ rfs [lookup_map] \\ rveq
  \\ qpat_abbrev_tac `pp = Pcon X l`
  \\ Cases_on `v`
  \\ TRY (qexists_tac `pp` \\ fs [Abbr`pp`, pmatch_def] \\ NO_TAC)
  \\ rename1 `Conv c1 l1`
  \\ fsrw_tac [DNF_ss] []
  \\ simp [METIS_PROVE [] ``a \/ b <=> ~a ==> b``]
  \\ rw [Abbr`pp`, pmatch_Pcon_No_match]
  \\ rename1 `FLOOKUP _ _ = SOME ars`
  \\ rename1 `get_dty_tags _ _ = SOME res` \\ fs []
  \\ imp_res_tac get_dty_tags_thm
  \\ first_x_assum (qspec_then `LENGTH l1` mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ fs [ctor_rel_def]
  \\ last_x_assum (qspec_then `x` assume_tac) \\ rfs []
  \\ fs [ok_ctor_def] \\ rw [lookup_insert]
  \\ fs [domain_fromList, lookup_map, SUBSET_DEF, PULL_EXISTS] \\ rfs []
  \\ fs [EVERY_MEM, MEM_toList, PULL_EXISTS] \\ rveq
  \\ first_x_assum (qspec_then `c2` mp_tac o PURE_ONCE_REWRITE_RULE [EQ_SYM_EQ])
  \\ res_tac \\ fs [] \\ rw [] \\ res_tac
  \\ asm_exists_tac
  \\ rw [pmatch_def, same_ctor_def, ctor_same_type_def]
  \\ metis_tac [EVERY_MEM, is_unconditional_list_thm]
QED

Theorem v_rel_ok_ctor:
   v_rel ctors v1 v2
   ==>
   ok_ctor ctors v1 /\ ok_ctor ctors v2
Proof
  Cases_on `v1` \\ Cases_on `v2` \\ rw [ok_ctor_def]
  \\ metis_tac [LIST_REL_LENGTH]
QED

val s1 = mk_var ("s1",
  ``flatSem$evaluate`` |> type_of |> strip_fun |> snd
  |> dest_prod |> fst);

Theorem compile_exps_evaluate:
  (!env1 ^s1 xs t1 r1.
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
          err_v2 = (t2, r2))
Proof
  ho_match_mp_tac evaluate_ind
  \\ rw [compile_exps_def, evaluate_def] \\ fs [result_rel_def]
  >-
   (simp [Once evaluate_cons]
    \\ fs [case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs [PULL_EXISTS]
    \\ rpt (first_x_assum drule \\ rpt (disch_then drule) \\ rw [])
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rw [])
  >-
   (fs [case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs [PULL_EXISTS]
    \\ rpt (first_x_assum drule \\ rpt (disch_then drule) \\ rw [])
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rw [])
  >- (* Handle *)
   (fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ last_x_assum match_mp_tac \\ fs [add_default_def, env_rel_def]
    \\ qexists_tac `T` \\ rw []
    \\ metis_tac [exhaustive_exists_match, exhaustive_SUBMAP, v_rel_ok_ctor])
  >-
   (fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ fs [case_eq_thms, pair_case_eq, PULL_EXISTS]
    \\ first_x_assum drule
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ fsrw_tac [DNF_ss] [env_rel_def, ok_ctor_def])
  >- fs [env_rel_def]
  >- (* Con *)
   (fs [case_eq_thms, pair_case_eq, bool_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ qpat_x_assum `_ ==> _` mp_tac
    \\ (impl_keep_tac >- fs [env_rel_def])
    \\ rpt (disch_then drule) \\ rfs [] \\ fs [compile_exps_LENGTH]
    \\ fsrw_tac [DNF_ss] [env_rel_def] \\ rw []
    \\ rw [ok_ctor_def]
    \\ metis_tac [LIST_REL_LENGTH, evaluate_length, LENGTH_REVERSE, ctor_rel_def])
  >-
   (every_case_tac \\ fs [] \\ rw [] \\ fs [env_rel_def]
    \\ map_every imp_res_tac [nv_rel_ALOOKUP_v_rel, LIST_REL_MEM_IMP] \\ rfs [])
  >- (simp [Once v_rel_cases] \\ metis_tac [env_rel_def])
  >- (* App *)
   (fs [case_eq_thms, pair_case_eq, bool_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ last_x_assum drule
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ rpt (qpat_x_assum `(_,_) = _` (assume_tac o GSYM)) \\ fs []
    \\ imp_res_tac EVERY2_REVERSE
    >- metis_tac [do_opapp_thm, state_rel_def]
    >-
     (drule (GEN_ALL do_opapp_thm) \\ disch_then drule \\ rw [] \\ fs []
      \\ sg `env_rel ctors (env1 with v := env') (env2 with v := nvs2)`
      >- (fs [env_rel_def] \\ rfs [] \\ fs [])
      \\ sg `state_rel ctors (dec_clock s') (dec_clock t2)`
      >- fs [state_rel_def, dec_clock_def]
      \\ first_x_assum drule \\ rpt (disch_then drule) \\ fs [] \\ rw []
      \\ fs [state_rel_def])
    \\ drule (GEN_ALL do_app_thm)
    \\ disch_then (qspecl_then [`REVERSE v2`,`t2`,`ctors`] mp_tac)
    \\ fs [env_rel_def] \\ rw [] \\ fs []
    \\ Cases_on `r` \\ Cases_on `r2` \\ fs [evaluateTheory.list_result_def])
  >- (* If *)
   (fs [case_eq_thms, pair_case_eq] \\ rw [] \\ fs [PULL_EXISTS]
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rveq \\ fs []
    \\ rpt (disch_then drule) \\ rw [] \\ fs []
    \\ fs [do_if_def, bool_case_eq, Boolv_def] \\ rw [] \\ fs [])
  >- (* Mat *)
   (fs [case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ rw []
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rw []
    \\ last_x_assum drule \\ rpt (disch_then drule)
    \\ disch_then match_mp_tac
    \\ qexists_tac `F` \\ rw [add_default_def] \\ fs [bind_exn_v_def]
    \\ rw [ok_ctor_def]
    \\ metis_tac [exhaustive_exists_match, env_rel_def, exhaustive_SUBMAP,
                  v_rel_ok_ctor])
  >- (* Let *)
   (fs [case_eq_thms, pair_case_eq, PULL_EXISTS] \\ rw [] \\ fs []
    \\ first_x_assum drule \\ rpt (disch_then drule) \\ rw [] \\ fs [PULL_EXISTS]
    \\ last_x_assum match_mp_tac
    \\ fs [env_rel_def]
    \\ imp_res_tac evaluate_sing \\ fs [] \\ rw [] \\ fs []
    \\ fs [libTheory.opt_bind_def] \\ PURE_CASE_TAC \\ fs []
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
    \\ fs [initial_ctors_def, SUBSET_DEF] \\ rfs [])
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
  \\ metis_tac [pmatch_any_no_match]
QED

(* ------------------------------------------------------------------------- *)
(* Compile declarations                                                      *)
(* ------------------------------------------------------------------------- *)

val v_rel_SUBMAP = Q.prove (
  `(!pre v1 v2.
    v_rel pre v1 v2 ==>
    !post.
    pre SUBMAP post ==>
    v_rel post v1 v2) /\
   (!pre vs1 vs2.
    nv_rel pre vs1 vs2 ==>
    !post.
    pre SUBMAP post ==>
    nv_rel post vs1 vs2)`,
  ho_match_mp_tac v_rel_ind \\ rw [] \\ fs [LIST_REL_EL_EQN]
  \\ fs [ok_ctor_def] \\ every_case_tac \\ fs []
  \\ rw [Once v_rel_cases] \\ metis_tac [SUBMAP_TRANS, FLOOKUP_SUBMAP]);

val sv_rel_lemma = Q.prove (
  `!R x y. (!x y. R x y ==> Q ==> P x y) ==> sv_rel R x y ==> Q ==> sv_rel P x y`,
  ho_match_mp_tac sv_rel_ind
  \\ rw [] \\ fs [LIST_REL_EL_EQN]);

val sv_rel_v_rel_SUBMAP = Q.prove (
  `sv_rel (v_rel pre) v1 v2 /\
   pre SUBMAP post
   ==>
   sv_rel (v_rel post) v1 v2`,
  rw [] \\ ho_match_mp_tac (GEN_ALL (MP_CANON sv_rel_lemma))
  \\ qexists_tac `pre SUBMAP post` \\ fs []
  \\ qexists_tac `v_rel pre` \\ rw []
  \\ imp_res_tac v_rel_SUBMAP);

val state_rel_SUBMAP = Q.prove (
  `state_rel pre s1 s2 /\
   pre SUBMAP post
   ==>
   state_rel post s1 s2`,
  rw [state_rel_def, LIST_REL_EL_EQN]
  >- metis_tac [sv_rel_v_rel_SUBMAP]
  \\ first_x_assum (qspec_then `n` mp_tac)
  \\ rw [OPTREL_def] \\ fs []
  \\ metis_tac [v_rel_SUBMAP]);

val dec_res_rel_def = Define `
  (dec_res_rel ctors NONE NONE <=> T) /\
  (dec_res_rel ctors (SOME r1) (SOME r2) <=>
     result_rel (LIST_REL o v_rel) ctors (Rerr r1) (Rerr r2)) /\
  (dec_res_rel _ _ _ <=> F)`;

Theorem dec_res_rel_thms[simp]:
   (!ctors r. dec_res_rel ctors NONE r <=> r = NONE) /\
   (!ctors r. dec_res_rel ctors r NONE <=> r = NONE) /\
   (!ctors e r. dec_res_rel ctors (SOME e) r <=>
      ?e1. r = SOME e1 /\
           result_rel (LIST_REL o v_rel) ctors (Rerr e) (Rerr e1)) /\
   (!ctors e r. dec_res_rel ctors r (SOME e) <=>
      ?e1. r = SOME e1 /\
           result_rel (LIST_REL o v_rel) ctors (Rerr e1) (Rerr e))
Proof
  rw [] \\ Cases_on `r` \\ rw [dec_res_rel_def]
QED

val compile_exps_lemma =
  CONJUNCT1 compile_exps_evaluate
  |> SPEC_ALL |> UNDISCH |> SPEC_ALL
  |> Q.GENL [`ctors_pre`,`ctors`]
  |> Q.SPECL [`ctors`,`ctors`]
  |> SIMP_RULE (srw_ss()) []
  |> DISCH_ALL |> GEN_ALL;

val get_tdecs_def = Define `
  get_tdecs xs =
    MAP (\d. case d of Dtype t s => t)
      (FILTER (\d. ?t s. d = Dtype t s) xs)`;

Theorem get_tdecs_APPEND:
   get_tdecs (xs ++ ys) = get_tdecs xs ++ get_tdecs ys
Proof
  rw [get_tdecs_def, FILTER_APPEND]
QED

Theorem get_tdecs_MEM:
   MEM t (get_tdecs xs) <=> ?s. MEM (Dtype t s) xs
Proof
  rw [get_tdecs_def, MEM_MAP, MEM_FILTER, PULL_EXISTS]
QED

val is_new_type_def = Define `
  is_new_type ctors decl <=>
    !tid s. decl = Dtype tid s ==> tid NOTIN FDOM ctors`;

val compile_decs_SUBMAP = Q.prove (
  `!decs ctors_pre ctors_post decs2.
     EVERY (is_new_type ctors_pre) decs /\
     ALL_DISTINCT (get_tdecs decs) /\
     compile_decs ctors_pre decs = (ctors_post, decs2)
     ==>
     ctors_pre SUBMAP ctors_post`,
  Induct \\ rw [compile_decs_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ `ALL_DISTINCT (get_tdecs decs) /\
      ctors_pre SUBMAP ctor1 /\
      EVERY (is_new_type ctor1) decs`
    by (rename1 `compile_dec _ dec`
        \\ Cases_on `dec` \\ fs [compile_dec_def] \\ rw []
        \\ fs [is_new_type_def, EVERY_MEM] \\ rw []
        \\ imp_res_tac get_tdecs_MEM
        \\ fs [get_tdecs_def]
        \\ every_case_tac \\ fs []
        \\ strip_tac \\ fs []
        \\ metis_tac [])
  \\ metis_tac [SUBMAP_TRANS]);

Theorem compile_dec_ctor_rel:
   evaluate_dec env s d1 = (t, c1, r) /\
   r <> SOME (Rabort Rtype_error) /\
   env.check_ctor /\
   ctor_rel ctors_pre env.c /\
   compile_dec ctors_pre d1 = (ctors, d2) /\
   is_new_type ctors_pre d1
   ==>
   ctors_pre SUBMAP ctors /\
   ctor_rel ctors (env.c UNION c1)
Proof
  Cases_on `d1` \\ simp [evaluate_dec_def]
  >- (fs [compile_dec_def] \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
  >-
   (rw [compile_dec_def, is_fresh_type_def, FORALL_PROD, is_new_type_def]
    >- fs [SUBMAP_FUPDATE]
    \\ fs [ctor_rel_def] \\ rw [] \\ fs [flookup_thm]
    \\ eq_tac \\ rw [] \\ fs []
    \\ `ty <> n` by metis_tac [flookup_thm] \\ fs [NOT_EQ_FAPPLY])
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ fs [compile_dec_def, is_fresh_exn_def, ctor_rel_def]
QED

val env_updated_by_UNION = Q.prove (
  `env with c updated_by $UNION c1 = env with c := env.c UNION c1 /\
   env with c updated_by $UNION c1 o $UNION c2 =
   env with c := env.c UNION c1 UNION c2`,
  fs [environment_component_equality, AC UNION_COMM UNION_ASSOC]);

Theorem compile_dec_evaluate:
   !d1 env1 s1 t1 c1 r1.
     evaluate_dec env1 s1 d1 = (t1, c1, r1) /\
     r1 <> SOME (Rabort Rtype_error)
     ==>
     !ctors env2 s2.
       env_rel ctors env1 env2 /\
       state_rel ctors s1 s2 /\
       is_new_type ctors d1
       ==>
       ?t2 r2 d2 ctors_post c2.
         ctors SUBMAP ctors_post /\
         compile_dec ctors d1 = (ctors_post, d2) /\
         env_rel ctors_post (env1 with c updated_by $UNION c1)
                            (env2 with c updated_by $UNION c2) /\
         state_rel ctors_post t1 t2 /\
         dec_res_rel ctors_post r1 r2 /\
         evaluate_dec env2 s2 d2 = (t2, c2, r2) /\
         c1 = c2
Proof
  Cases \\ rw []
  >- (* Dlet *)
   (`env_rel ctors (env1 with v := []) (env2 with v := [])`
      by (fs [env_rel_def] \\ metis_tac [])
    \\ fs [compile_dec_def, evaluate_dec_def, pair_case_eq, case_eq_thms]
    \\ rveq \\ fs [PULL_EXISTS]
    \\ drule compile_exps_lemma \\ fs []
    \\ rpt (disch_then drule) \\ rw []
    \\ fs [compile_exp_def, env_rel_def]
    \\ every_case_tac \\ fs [] \\ rw []
    \\ metis_tac [])
  >- (* Dtype *)
   (`env1.check_ctor /\ ctor_rel ctors env1.c` by fs [env_rel_def]
    \\ Cases_on `compile_dec ctors (Dtype n s)`
    \\ drule (GEN_ALL compile_dec_ctor_rel)
    \\ rpt (disch_then drule) \\ strip_tac
    \\ `init_ctors SUBMAP q` by metis_tac [SUBMAP_TRANS, env_rel_def]
    \\ fs [env_updated_by_UNION] \\ fs [env_rel_def]
    \\ fs [SUBSET_DEF]
    \\ simp [RIGHT_EXISTS_AND_THM]
    \\ conj_tac >- metis_tac [v_rel_SUBMAP]
    \\ qhdtm_x_assum `compile_dec` mp_tac \\ simp [compile_dec_def]
    \\ strip_tac \\ rveq
    \\ qmatch_asmsub_abbrev_tac `ctors |+ new`
    \\ fs [evaluate_dec_def, env_rel_def, is_fresh_type_def]
    \\ every_case_tac \\ fs []
    \\ metis_tac [state_rel_SUBMAP])
     (* Dexn *)
  \\ fs [evaluate_dec_def, env_rel_def, is_fresh_exn_def, compile_dec_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs [ctor_rel_def, FORALL_PROD]
  \\ metis_tac [SUBSET_DEF, SUBSET_UNION]
QED

Theorem compile_decs_evaluate:
   !ds1 env1 s1 t1 c1 r1.
     evaluate_decs env1 s1 ds1 = (t1, c1, r1) /\
     r1 <> SOME (Rabort Rtype_error)
     ==>
     !ctors env2 s2 ds2 ctors_post.
       compile_decs ctors ds1 = (ctors_post, ds2) /\
       env_rel ctors env1 env2 /\
       state_rel ctors s1 s2 /\
       EVERY (is_new_type ctors) ds1 /\
       ALL_DISTINCT (get_tdecs ds1)
       ==>
       ?t2 r2 c2.
         ctors SUBMAP ctors_post /\
         (r1 = NONE ==>
           env_rel ctors_post (env1 with c updated_by $UNION c1)
                              (env2 with c updated_by $UNION c2)) /\
         state_rel ctors_post t1 t2 /\
         dec_res_rel ctors_post r1 r2 /\
         evaluate_decs env2 s2 ds2 = (t2, c2, r2) /\
         c1 = c2
Proof
  Induct \\ rw []
  >-
   (fs [evaluate_decs_def, compile_decs_def, env_rel_def, get_tdecs_def,
        environment_component_equality] \\ rw []
    \\ fs [get_tdecs_def, evaluate_decs_def])
  \\ fs [evaluate_decs_def, compile_decs_def, case_eq_thms, pair_case_eq]
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ drule compile_dec_evaluate \\ fs []
  \\ rpt (disch_then drule) \\ rw []
  \\ `EVERY (is_new_type ctor1) ds1`
    by (fs [EVERY_MEM] \\ rw []
        \\ first_x_assum drule \\ fs [is_new_type_def] \\ rw []
        \\ fs [get_tdecs_def]
        \\ Cases_on `h` \\ fs [compile_dec_def] \\ rw [] \\ fs []
        \\ metis_tac [get_tdecs_MEM, get_tdecs_def])
  \\ `ALL_DISTINCT (get_tdecs ds1)` by (Cases_on `h` \\ fs [get_tdecs_def])
  >-
   (last_x_assum drule
    \\ rpt (disch_then drule) \\ rw []
    \\ simp [RIGHT_EXISTS_AND_THM]
    \\ conj_tac >- metis_tac [SUBMAP_TRANS]
    \\ fs [env_updated_by_UNION, AC UNION_ASSOC UNION_COMM, evaluate_decs_def])
  \\ fs [env_updated_by_UNION] \\ rw [] \\ fs [evaluate_decs_def]
  \\ metis_tac [v_rel_SUBMAP, state_rel_SUBMAP, SUBMAP_TRANS, compile_decs_SUBMAP]
QED

(* ------------------------------------------------------------------------- *)
(* Top-level semantics theorem                                               *)
(* ------------------------------------------------------------------------- *)

val ctor_rel_initial_ctor = Q.prove (
  `ctor_rel init_ctors (initial_env exh ctors).c`,
  rw [ctor_rel_def, init_ctors_def, initial_env_def, flookup_fupdate_list] \\ rw []
  \\ fs [lookup_insert] \\ every_case_tac \\ fs [lookup_def] \\ EVAL_TAC \\ rw []);

Theorem compile_decs_eval_sim:
   EVERY (is_new_type init_ctors) ds1 /\
   ALL_DISTINCT (get_tdecs ds1)
   ==>
   eval_sim
     (ffi:'ffi ffi_state) F T ds1 T T
     (SND (compile ds1))
     (\p1 p2. p2 = SND (compile p1)) F
Proof
  rw [eval_sim_def] \\ qexists_tac `0` \\ fs []
  \\ Cases_on `compile ds1` \\ fs [compile_def]
  \\ `env_rel init_ctors (initial_env F T) (initial_env T T)`
    by (rw [env_rel_def, ctor_rel_initial_ctor]
        \\ EVAL_TAC \\ fs []
        \\ fs [lookup_def] \\ rw [])
  \\ `state_rel init_ctors (initial_state ffi k) (initial_state ffi k)`
    by (EVAL_TAC \\ fs [])
  \\ drule compile_decs_evaluate \\ fs []
  \\ rpt (disch_then drule) \\ rw []
  \\ fs [state_rel_def] \\ rw [dec_res_rel_def] \\ fs []
QED

val compile_decs_semantics = save_thm ("compile_decs_semantics",
  MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] IMP_semantics_eq)
           (UNDISCH compile_decs_eval_sim)
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO]);

(* ------------------------------------------------------------------------- *)
(* Syntactic results for expressions                                         *)
(* ------------------------------------------------------------------------- *)

val compile_exps_sing = Q.prove (
  `!e. ?e2. compile_exps ctors [e] = [e2]`,
  rw []
  \\ qspecl_then [`ctors`,`[e]`] mp_tac compile_exps_LENGTH
  \\ simp_tac(std_ss++listSimps.LIST_ss)[LENGTH_EQ_NUM_compute]);

Theorem compile_exps_elist_globals_eq_empty:
   !ctors es.
     elist_globals es = {||}
     ==>
     elist_globals (compile_exps ctors es) = {||}
Proof
  ho_match_mp_tac compile_exps_ind
  \\ rw [compile_exps_def]
  \\ TRY
    (rename1 `HD (compile_exps ctors [e])`
     \\ qspec_then `e` assume_tac compile_exps_sing \\ fs [] \\ fs [])
  \\ fs [MAP_MAP_o, o_DEF, UNCURRY]
  \\ fs [add_default_def] \\ rw [] \\ fs []
  \\ TRY
   (pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ ntac 2 (pop_assum kall_tac)
    \\ pop_assum mp_tac
    \\ rename1 `MAP _ ps`
    \\ qid_spec_tac `ps`
    \\ Induct \\ fs [FORALL_PROD] \\ rw []
    \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- METIS_TAC[])
    \\ fsrw_tac [DNF_ss] [SUB_BAG_UNION] \\ rw []
    \\ rename1 `compile_exps ctors [e]`
    \\ Cases_on `compile_exps ctors [e]` \\ fs [])
  \\ pop_assum mp_tac
  \\ ntac 2 (pop_assum kall_tac)
  \\ pop_assum mp_tac
  \\ rename1 `MAP _ ps`
  \\ qid_spec_tac `ps`
  \\ Induct \\ fs [FORALL_PROD] \\ rw []
  \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- METIS_TAC[])
  \\ fsrw_tac [DNF_ss] [SUB_BAG_UNION] \\ rw []
  \\ rename1 `compile_exps ctors [e]`
  \\ Cases_on `compile_exps ctors [e]` \\ fs []
QED

Theorem compile_exps_set_globals_eq_empty:
   set_globals e = {||} ==> set_globals (HD (compile_exps ctors [e])) = {||}
Proof
  qspecl_then [`ctors`,`[e]`] mp_tac compile_exps_elist_globals_eq_empty
  \\ rw[] \\ fs[] \\ Cases_on `compile_exps ctors [e]` \\ fs []
QED

Theorem compile_exps_esgc_free:
   !ctors es.
     EVERY esgc_free es
     ==>
     EVERY esgc_free (compile_exps ctors es)
Proof
  ho_match_mp_tac compile_exps_ind
  \\ rw [compile_exps_def]
  \\ fs [compile_exps_set_globals_eq_empty]
  \\ TRY
    (rename1 `HD (compile_exps ctors [e])`
     \\ qspec_then `e` assume_tac compile_exps_sing \\ fs [] \\ fs []
     \\ NO_TAC)
  \\ fs [EVERY_MAP, EVERY_MEM, FORALL_PROD, elist_globals_eq_empty]
  \\ fs [MEM_MAP, MAP_MAP_o, PULL_EXISTS, FORALL_PROD]
  \\ fs [add_default_def] \\ rw [] \\ fs []
  \\ TRY (
    match_mp_tac compile_exps_set_globals_eq_empty
    \\ res_tac)
  \\ fs [compile_exps_def]
  \\ rename1 `HD (compile_exps ctors [p])`
  \\ qspec_then `p` assume_tac compile_exps_sing \\ fs []
  \\ res_tac \\ fs []
QED

Theorem compile_exps_sub_bag:
   !ctors es. elist_globals (compile_exps ctors es) ≤ elist_globals es
Proof
  ho_match_mp_tac compile_exps_ind
  \\ rw [compile_exps_def]
  \\ TRY
   (rename1 `HD (compile_exps ctors [x])`
    \\ qspec_then `x` assume_tac compile_exps_sing \\ fs [SUB_BAG_UNION]
    \\ fs [elist_globals_append, SUB_BAG_UNION])
  \\ fs [MAP_MAP_o, o_DEF, UNCURRY]
  \\ fs [add_default_def] \\ rw [] \\ fs []
  \\ simp [compile_exps_def, elist_globals_append]
  \\ TRY
   (rename1 `HD (compile_exps ctors [x1])`
    \\ qspec_then `x1` assume_tac compile_exps_sing \\ fs [SUB_BAG_UNION]
    \\ fs [elist_globals_append, SUB_BAG_UNION])
  \\ TRY
   (rename1 `HD (compile_exps ctors [x2])`
    \\ qspec_then `x2` assume_tac compile_exps_sing \\ fs [SUB_BAG_UNION]
    \\ fs [elist_globals_append, SUB_BAG_UNION])
  \\ (FIRST
    (map (fn th => match_mp_tac (MP_CANON th) \\ conj_tac >- simp[])
         (CONJUNCTS SUB_BAG_UNION)))
  \\ last_x_assum mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ rename1 `MAP _ xs`
  \\ Induct_on `xs` \\ fs [FORALL_PROD] \\ rw []
  \\ last_x_assum mp_tac
  \\ (impl_tac >- (rw [] \\ metis_tac [])) \\ rw []
  \\ rename1 `HD (compile_exps ctors [p])`
  \\ qspec_then `p` assume_tac compile_exps_sing \\ fs [SUB_BAG_UNION]
  \\ fsrw_tac [DNF_ss] [SUB_BAG_UNION] \\ rw []
QED

Theorem compile_exps_distinct_globals:
   BAG_ALL_DISTINCT (elist_globals es)
   ==>
   BAG_ALL_DISTINCT (elist_globals (compile_exps ctors es))
Proof
  metis_tac [compile_exps_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]
QED

(* ------------------------------------------------------------------------- *)
(* Syntactic results for declarations                                        *)
(* ------------------------------------------------------------------------- *)

Theorem compile_decs_elist_globals_eq_empty:
   !ds ctors.
     elist_globals
       (MAP dest_Dlet (FILTER is_Dlet ds)) = {||}
     ==>
     elist_globals
       (MAP dest_Dlet (FILTER is_Dlet (SND (compile_decs ctors ds)))) = {||}
Proof
  Induct \\ rw [compile_decs_def]
  \\ fs [UNCURRY] \\ rw []
  \\ Cases_on `h` \\ fs [compile_dec_def] \\ rw [compile_exp_def]
  \\ metis_tac [compile_exps_set_globals_eq_empty]
QED

Theorem compile_decs_esgc_free:
   !ds ctors.
     EVERY esgc_free (MAP dest_Dlet (FILTER is_Dlet ds))
     ==>
     EVERY esgc_free (MAP dest_Dlet
       (FILTER is_Dlet (SND (compile_decs ctors ds))))
Proof
  Induct \\ rw [compile_decs_def]
  \\ fs [UNCURRY] \\ rw []
  \\ Cases_on `h` \\ fs [compile_dec_def, compile_exp_def]
  \\ qspec_then `e` assume_tac compile_exps_sing \\ fs []
  \\ metis_tac [compile_exps_esgc_free, EVERY_DEF]
QED

Theorem compile_decs_sub_bag:
   !ds ctors.
    elist_globals (MAP dest_Dlet
      (FILTER is_Dlet (SND (compile_decs ctors ds)))) ≤
    elist_globals (MAP dest_Dlet (FILTER is_Dlet ds))
Proof
  Induct \\ rw [compile_decs_def]
  \\ fs [UNCURRY] \\ rw []
  \\ Cases_on `h` \\ fs [compile_dec_def, compile_exp_def]
  \\ qspec_then `e` assume_tac compile_exps_sing \\ fs []
  \\ last_x_assum (qspec_then `ctors` assume_tac)
  \\ `elist_globals [e2] <= elist_globals [e]`
    by metis_tac [compile_exps_sub_bag]
  \\ fs [SUB_BAG_UNION]
QED

Theorem compile_exps_distinct_globals:
   BAG_ALL_DISTINCT (elist_globals (MAP dest_Dlet (FILTER is_Dlet ds)))
   ==>
   BAG_ALL_DISTINCT
     (elist_globals
       (MAP dest_Dlet (FILTER is_Dlet (SND (compile_decs ctors ds)))))
Proof
  metis_tac [compile_decs_sub_bag, BAG_ALL_DISTINCT_SUB_BAG]
QED

val _ = export_theory();

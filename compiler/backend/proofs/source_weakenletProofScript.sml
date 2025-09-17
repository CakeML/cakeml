(*source_weakenletTheory
  Correctness proof for the source_letweaken pass.
 *)
Theory source_weakenletProof
Ancestors
  source_weakenlet evaluate evaluateProps namespaceProps
  semanticPrimitives semanticPrimitivesProps misc[qualified] semantics ast
Libs
  preamble

(*TODO this is may appear stronger than
env_rel defined in source_eval but their equivalent *)
Definition env_rel_def:
  env_rel rel (envx: 'a sem_env) envy =
  (nsDom envx.v = nsDom envy.v /\
  nsDomMod envx.v = nsDomMod envy.v /\
  (!n. OPTREL rel (nsLookup envx.v n) (nsLookup envy.v n))
                          /\ envx.c = envy.c)
End

Theorem env_rel_mono[mono]:
  (!x y. R1 x y ==> R2 x y) ==> env_rel R1 x y ==> env_rel R2 x y
Proof
  fs[env_rel_def] >> srw_tac[][] >>
  irule OPTREL_MONO >>
  first_x_assum (irule_at (Pos $ el 2)) >>
  simp[]
QED

Theorem env_rel_add_nsBind:
  env_rel R (env with v := ev) (env' with v := ev') /\ R x y ==>
  env_rel R (env with v := nsBind n x ev) (env' with v := nsBind n y ev')
Proof
  rw [env_rel_def]
  \\ Cases_on `n' = Short n`
  \\ fs [nsLookup_nsBind]
  \\ res_tac
QED

Theorem env_rel_add_nsBindList:
  !xs ys. env_rel R (env with v := ev) (env' with v := ev') /\
  LIST_REL ((=) ### R) xs ys ==>
  env_rel R (env with v := nsBindList xs ev) (env' with v := nsBindList ys ev')
Proof
  Induct
  \\ simp [FORALL_PROD, EXISTS_PROD]
  \\ rw []
  \\ fs [namespaceTheory.nsBindList_def]
  \\ irule env_rel_add_nsBind
  \\ simp []
QED

Theorem env_rel_nsLift:
  env_rel R (env with <| v := v; c := c |>)
    (env' with <| v := v'; c := c' |>) ==>
  env_rel R (env with <| v := nsLift mn v; c := nsLift mn c |>)
    (env' with <| v := nsLift mn v'; c := nsLift mn c' |>)
Proof
  rw [] \\ fs [env_rel_def, nsDom_nsLift, nsDomMod_nsLift]
  \\ rw [namespacePropsTheory.nsLookup_nsLift]
  \\ every_case_tac
  \\ fs []
  \\ res_tac
QED

Theorem env_rel_nsEmpty = LIST_CONJ
  [Q.SPECL [`R`, `x with <| v := nsEmpty |>`] env_rel_def,
    Q.SPECL [`R`, `x`, `y with <| v := nsEmpty |>`] env_rel_def]
  |> SIMP_RULE (std_ss ++ simpLib.type_ssfrag ``: 'a sem_env``)
        [nsLookup_nsEmpty]

val _ = bossLib.augment_srw_ss [rewrites (CONJUNCTS env_rel_nsEmpty)];

Theorem env_rel_nsAppend:
  env_rel R (env with v := a) (env' with v := c) /\
  env_rel R (env with v := b) (env' with v := d) ==>
  env_rel R (env with <| v := nsAppend a b |>)
    (env' with <| v := nsAppend c d |>)
Proof
  rw [env_rel_def, namespacePropsTheory.nsDom_nsAppend_equal]
  \\ rpt (first_x_assum (qspec_then `n` assume_tac))
  \\ fs [Q.ISPEC `nsDom n'` EXTENSION, nsLookup_nsDom]
  \\ Cases_on `nsLookup (nsAppend a b) n` \\ fs[OPTREL_SOME]
  \\ fs[ nsLookup_nsAppend_some,nsLookup_nsAppend_none]
  \\ gvs[]
  \\ fs[oneline OPTREL_THM,AllCasePreds()]
  \\ fs[namespaceTheory.nsDomMod_def,EXTENSION]
  \\ fs[GSPECIFICATION,UNCURRY_EQ]
  \\ res_tac
  \\ gvs[]
  >- metis_tac[]
  \\ rw[]
  \\ first_x_assum drule
  \\ fs[]
  \\ metis_tac[option_CLAUSES]
QED

Theorem env_rel_extend_dec_env:
  env_rel R env1 env2 /\ env_rel R env3 env4 ==>
  env_rel R (extend_dec_env env1 env3) (extend_dec_env env2 env4)
Proof
  rw [extend_dec_env_def]
  \\ irule env_rel_nsAppend
  \\ fs [env_rel_def]
  \\ rw [] \\ res_tac
QED

Theorem env_rel_nsLookup_v:
  env_rel R env env' /\ nsLookup env.v id = SOME v ==>
  ?v'. nsLookup env'.v id = SOME v' /\ R v v'
Proof
  rw [env_rel_def]
  \\ fs [Q.ISPEC `nsDom n'` EXTENSION, nsLookup_nsDom]
  \\ res_tac
  \\ fs []
  \\ first_x_assum (qspec_then `id` mp_tac)
  \\ fs[]
QED

Triviality env_rel_nsLookup_c:
  env_rel R env env' /\ nsLookup env.c id = r ==>
  env'.c = env.c
Proof
  rw [env_rel_def]
QED

Theorem nsLookup_alist_to_ns:
  nsLookup (alist_to_ns l) id =
  (case id of
    Short x => ALOOKUP l x
  | Long _ _ => NONE)
Proof
  TOP_CASE_TAC >>
  fs[namespaceTheory.alist_to_ns_def] >>
  fs[namespaceTheory.nsLookup_def]
QED

Theorem LIST_REL_PAIR_REL:
   LIST_REL (R1 ### R2) xs ys <=>
   (LIST_REL R1 (MAP FST xs) (MAP FST ys) /\
   LIST_REL R2 (MAP SND xs) (MAP SND ys))
Proof
  qid_spec_tac `ys` >>
  Induct_on `xs` >> fs[MAP_EQ_CONS,SF CONJ_ss,PULL_EXISTS]
  >> fs[PAIR_REL ,ELIM_UNCURRY]
  >> metis_tac[]
QED

Triviality env_rel_alist_to_ns:
   LIST_REL ((=) ### R) xs ys ==>
  env_rel R <|v := alist_to_ns xs; c := envC |>
          <|v := alist_to_ns ys; c := envC|>
Proof
  strip_tac >>
  fs[env_rel_def,nsLookup_alist_to_ns]
  \\ simp[TypeBase.case_rand_of ``:('a, 'b) id``,
   Cong $ TypeBase.case_cong_of ``:('a, 'b) id``]
  \\ CONJ_TAC >-
   (drule_then strip_assume_tac $ iffLR LIST_REL_PAIR_REL
    \\ fs[GSYM MAP_MAP_o])
  \\ rw[] >> TOP_CASE_TAC
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac `ys`
  \\ Induct_on `xs` \\ fs[PULL_EXISTS]
  \\ Ho_Rewrite.PURE_REWRITE_TAC [FORALL_PROD]
  \\ fs[COND_RAND]
QED

Theorem env_rel_nsOptBind:
  env_rel R envx envy /\
  R v''' v'' ==>
  env_rel R (envx with v := nsOptBind xo v'³' envx.v)
            (envy with v := nsOptBind xo v'' envy.v)
Proof
  fs[namespaceTheory.nsOptBind_def] >>
  TOP_CASE_TAC >>
  fs[env_rel_add_nsBind]
QED

(*TODO use modern Inductive syntax*)
Inductive v_rel:
   (v_rel (Litv v) (Litv v))
   /\
   (LIST_REL v_rel xs ys ==>
   (v_rel (Conv stamp xs) (Conv stamp ys)))
   /\
   (env_rel v_rel envx envy ==>
   (v_rel (Closure envx var exp) (Closure envy var exp)))
   /\
   (env_rel v_rel envx envy ==>
   (v_rel (Recclosure envx funs fun_name) (Recclosure envy funs fun_name)))
   /\
   (env_rel v_rel envx envy /\
   ALL_DISTINCT (MAP (λ(f,x,e). f) funs) /\
   find_recfun fun_name funs = SOME (var,exp) /\
   ~ EXISTS (\fun_name. exists_call fun_name exp) (MAP FST funs) ==>
   (v_rel (Closure envx var exp) (Recclosure envy funs fun_name)))
   /\
   (env_rel v_rel envx envy /\
   ALL_DISTINCT (MAP (λ(f,x,e). f) funs) /\
   find_recfun fun_name funs = SOME (var,exp) /\
   ~ EXISTS (\fun_name. exists_call fun_name exp) (MAP FST funs) ==>
   (v_rel (Recclosure envx funs fun_name) (Closure envy var exp)))
   /\
   (v_rel (Loc b addr) (Loc b addr))
   /\
   (LIST_REL v_rel xs ys ==>
   (v_rel (Vectorv xs) (Vectorv ys)))
   /\
   (env_rel v_rel envx envy ==>
   (v_rel (Env envx nid) (Env envy nid)))
End

Theorem v_rel_simp[simp] =
  map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
      [``v_rel (Litv v) y``,
       ``v_rel (Conv stamp xs) y``,
       ``v_rel (Loc b addr) y``,
       ``v_rel (Vectorv xs) y``,
       ``v_rel (Env env nid) y``,
       ``v_rel y (Litv v)``,
       ``v_rel y (Conv stamp xs)``,
       ``v_rel y (Loc b addr)``,
       ``v_rel y (Vectorv xs)``,
       ``v_rel y (Env env nid)``]
    |> LIST_CONJ

Theorem v_rel_Closure =
  map (SIMP_CONV (srw_ss()) [Once v_rel_cases])
      [``v_rel (Closure env var exp) y``,
       ``v_rel (Recclosure env funs fun_name) y``,
       ``v_rel y (Closure env var exp)``,
       ``v_rel y (Recclosure env funs fun_name)``]
    |> LIST_CONJ

Theorem v_rel_Boolv[simp]:
  (v_rel v (Boolv b) <=> v = Boolv b) /\
  (v_rel (Boolv b) v <=> v = Boolv b)
Proof
rw[Boolv_def]
QED

Theorem v_rel_bind_exn_v[simp]:
  ((v_rel v bind_exn_v) <=> v = bind_exn_v) /\
  ((v_rel bind_exn_v v) <=> v = bind_exn_v)
Proof
  fs[bind_exn_v_def]
QED

Theorem v_rel_div_exn_v[simp]:
  ((v_rel v div_exn_v) <=> v = div_exn_v) /\
  ((v_rel div_exn_v v) <=> v = div_exn_v)
Proof
  fs[div_exn_v_def]
QED

Theorem v_rel_sub_exn_v[simp]:
  ((v_rel v sub_exn_v) <=> v = sub_exn_v) /\
  ((v_rel sub_exn_v v) <=> v = sub_exn_v)
Proof
  fs[sub_exn_v_def]
QED
(*TODO maybe don't shadow existing OPTREL_refl binding*)
Triviality OPTREL_refl:
   (!x. opt = SOME x ==> R x x)  ==> OPTREL R opt opt
Proof
  Cases_on `opt`  >> fs[]
QED

Triviality nsLookup_size:
   nsLookup s.v n = SOME x ==>
   v_size x < sem_env_size v_size s
Proof
  Cases_on `s` >> fs[] >>
  rename1 `nsLookup n' n` >>
  Cases_on `n'` >> fs[] >>
  MAP_EVERY qid_spec_tac $ List.rev [`l0`,`l`] >>
  Induct_on `n` >> fs[namespaceTheory.nsLookup_def]
  >- (
  rw[] >>
  drule_then strip_assume_tac ALOOKUP_MEM >>
  fs[MEM_SPLIT,list_size_append])
  >- (
  simp[AllCaseEqs()] >> rpt strip_tac >>
  drule_then strip_assume_tac ALOOKUP_MEM >>
  fs[MEM_SPLIT,list_size_append] >> Cases_on `env` >>
  first_x_assum drule >> fs[])
QED

Theorem v_rel_refl:
 !x.
   v_rel x x
Proof
  completeInduct_on `v_size x` >>
  Cases_on `x` >> fs[] >> rpt strip_tac
  >- (irule EVERY2_refl >> rpt strip_tac >>
      first_x_assum irule >> fs[MEM_SPLIT,list_size_append])
  >~ [`Closure`]
  >- (simp[Once v_rel_cases] >>
     simp[env_rel_def] >> gen_tac >>
     irule OPTREL_refl >> rpt strip_tac >>
     first_x_assum irule >> fs[] >>
     drule nsLookup_size >> fs[])
  >~ [`Recclosure`]
  >- (simp[Once v_rel_cases] >>
     simp[env_rel_def] >> gen_tac >>
     irule OPTREL_refl >> rpt strip_tac >>
     first_x_assum irule >> fs[] >>
     drule nsLookup_size >> fs[])
  >- (irule EVERY2_refl >> rpt strip_tac >>
      first_x_assum irule >> fs[MEM_SPLIT,list_size_append])
  >- (simp[env_rel_def] >> gen_tac >>
     irule OPTREL_refl >> rpt strip_tac >>
     first_x_assum irule >> fs[] >>
     drule nsLookup_size >> fs[])
QED

Definition match_result_rel_def[simp]:
  match_result_rel R (Match m) (Match m') = R m m' /\
  match_result_rel R Match_type_error Match_type_error = T /\
  match_result_rel R No_match No_match = T /\
  match_result_rel R _ _ = F
End

Theorem match_result_rel_simp[simp]:
   ((match_result_rel R Match_type_error mres) <=> (mres = Match_type_error)) /\
   ((match_result_rel R No_match mres) <=> (mres = No_match)) /\
   ((match_result_rel R (Match m) mres) <=> (?m'. R m m' /\ mres = Match m'))
Proof
  Cases_on `mres` >> fs[]
QED

Definition store_v_rel_def[simp]:
  store_v_rel R (Refv v) (Refv v') = R v v' /\
  store_v_rel R (W8array a) (W8array a') = (a = a') /\
  store_v_rel R (Varray va) (Varray va') = LIST_REL R va va' /\
  store_v_rel R _ _ = F
End

Theorem store_v_rel_simps[simp]:
  (store_v_rel R (Refv v) store_v <=> (?v'. store_v = Refv v' /\ R v v') )/\
  (store_v_rel R store_v (Refv v) <=> (?v'. store_v = Refv v' /\ R v' v)) /\
  (store_v_rel R (W8array a) store_v <=> (store_v = W8array a)) /\
  (store_v_rel R (W8array a) store_v <=> (store_v = W8array a)) /\
  (store_v_rel R (Varray va) store_v <=> (?va'. store_v = Varray va' /\
                                         LIST_REL R va va')) /\
  (store_v_rel R store_v (Varray va) <=> (?va'. store_v = Varray va' /\
                                         LIST_REL R va' va))
Proof
  Cases_on `store_v` >> simp[] >> metis_tac[]
QED

Theorem store_v_rel_refl:
 (!x. store_v = Refv x ==> R x x) /\
 (!x. store_v = Varray x ==> LIST_REL R x x) ==>
 (store_v_rel R store_v store_v)
Proof
 Cases_on `store_v` >> fs[]
QED

Triviality v_rel_pmatch:
 (!envC refs p v env res v' refs' env'.
   v_rel v v' /\
   LIST_REL (store_v_rel v_rel) refs refs' /\
   LIST_REL ((=) ### v_rel) env env' /\
   pmatch envC refs p v env = res ==>
   ?res'.
   pmatch envC refs' p v' env' = res' /\
   match_result_rel (LIST_REL ((=) ### v_rel)) res res') /\
  (!envC refs ps vs envs res vs' refs' envs'.
   LIST_REL v_rel vs vs' /\
   LIST_REL (store_v_rel v_rel) refs refs' /\
   LIST_REL ((=) ### v_rel) envs envs' /\
   pmatch_list envC refs (ps) (vs) envs = res ==>
   ?res'.
   pmatch_list envC refs' (ps) (vs') envs' = res' /\
   match_result_rel (LIST_REL ((=) ### v_rel)) res res')
Proof
  ho_match_mp_tac pmatch_ind >> rpt strip_tac
  >> gvs[pmatch_def]
  >- (rpt TOP_CASE_TAC >> fs[] >>
     simp[EVERY2_refl,PAIR_REL_REFL,v_rel_refl])
  >- (rpt TOP_CASE_TAC >> gvs[] >>
      TRY (every_drule LIST_REL_LENGTH >> fs[]))
  >- (every_drule_then assume_tac LIST_REL_LENGTH >>
      rpt TOP_CASE_TAC >> gvs[])
  >- (`OPTREL (store_v_rel v_rel)
        (store_lookup lnum refs)
         (store_lookup lnum refs')`
         by (srw_tac[][store_lookup_def] >>fs[LIST_REL_EL_EQN]) >>
      rpt TOP_CASE_TAC >> fs[OPTREL_SOME])
  >>~- ([`Closure`],fs[Once v_rel_cases,pmatch_def])
  >>~- ([`Recclosure`],fs[Once v_rel_cases,pmatch_def])
  >- (
     Cases_on `pmatch envC refs p v envs` >> fs[] >>
     Cases_on `pmatch_list envC refs ps vs envs` >> fs[] >>
     res_tac >> fs[])
QED

Triviality v_rel_can_pmatch_all:
  v_rel v v' /\
  LIST_REL (store_v_rel v_rel) refs refs' ==>
  (can_pmatch_all envC refs' ps v' =
  can_pmatch_all envC refs ps v)
Proof
 rw[] >>
 Cases_on `can_pmatch_all envC refs ps v` >>
 fs[]
 >-(
   fs[can_pmatch_all_EVERY] >> fs[EVERY_MEM] >>
   rw[] >> first_x_assum $ drule_then assume_tac >>
   Cases_on `pmatch envC refs p v []` >> fs[] >>
   drule_at(Pos $ el 4) $ CONJUNCT1 v_rel_pmatch >>
   fs[] >> disch_then drule_all >> rw[] >> fs[])
 >-(
   fs[can_pmatch_all_EVERY] >> fs[EXISTS_MEM] >>
   rw[] >>
   drule_at(Pos $ el 4) $ CONJUNCT1 v_rel_pmatch >>
   fs[] >> disch_then drule_all >> rw[] >> fs[] >>
   metis_tac[])
QED

Triviality v_rel_build_conv:
  LIST_REL v_rel xs ys ==>
  OPTREL v_rel (build_conv envC cn xs) (build_conv envC cn ys)
Proof
  fs[build_conv_def] >> rpt TOP_CASE_TAC >> fs[]
QED

Theorem PAIR_REL_eq_PAIR:
  (R1 ### R2) (a,b) c <=> (?x y. c = (x,y) /\ R1 a x /\ R2 b y)
Proof
  Cases_on `c` >> fs[]
QED

(*
Triviality v_rel_do_eval_res:
  LIST_REL v_rel xs ys ==>
  ((=) ### result_rel ((env_rel v_rel) ### (=)) v_rel)
   (do_eval_res xs s) (do_eval_res ys s)
Proof
 cheat
QED
*)

Triviality v_rel_do_opapp:
   LIST_REL v_rel xs ys ==>
   OPTREL (env_rel v_rel ### (=)) (do_opapp xs) (do_opapp ys)
Proof
   strip_tac >>
   fs[do_opapp_def] >>
   rpt (PURE_TOP_CASE_TAC >> fs[]) >>
   gvs[v_rel_Closure]
   >- cheat
   >- cheat
   >- cheat
   >- cheat
QED

Triviality v_rel_v_to_list:
  !v v'.
  v_rel v v' ==>
  OPTREL (LIST_REL v_rel) (v_to_list v) (v_to_list v')
Proof
  ho_match_mp_tac v_to_list_ind >> rpt strip_tac >>
  fs[v_to_list_def,v_rel_Closure] >>
  TOP_CASE_TAC >> fs[] >>
  first_x_assum every_drule >>
  TOP_CASE_TAC >> fs[OPTREL_SOME] >>
  TOP_CASE_TAC >> fs[OPTREL_SOME]
QED

Triviality v_rel_list_to_v:
  !xs ys.
  v_rel (list_to_v xs) (list_to_v ys) = LIST_REL v_rel xs ys
Proof
  Induct >> fs[list_to_v_def]
  >- (Cases >> fs[list_to_v_def])
  >- (GEN_TAC >> Cases >> fs[list_to_v_def])
QED

Triviality v_rel_vs_to_string:
   !xs ys.
   LIST_REL v_rel xs ys ==>
   (vs_to_string xs) = (vs_to_string ys)
Proof
  ho_match_mp_tac vs_to_string_ind >> rpt strip_tac >>
  fs[vs_to_string_def,v_rel_Closure] >>
  TOP_CASE_TAC >> fs[] >>
  first_x_assum every_drule >>
  disch_then (assume_tac o GSYM) >>
  fs[]
QED

Triviality v_rel_v_to_char_list:
   !v v'.
   v_rel v v'==>
   (v_to_char_list v) = (v_to_char_list v')
Proof
  ho_match_mp_tac v_to_char_list_ind >> rpt strip_tac >>
  fs[v_to_char_list_def,v_rel_Closure] >>
  ntac 2 TOP_CASE_TAC >> fs[] >>
  first_x_assum every_drule >>
  disch_then (assume_tac o GSYM) >>
  fs[]
QED

Triviality v_rel_do_eq:
   (!a x b y.v_rel a b /\
   v_rel x y ==>
   (do_eq a x) =  (do_eq b y)) /\
   (!as xs bs ys.
   LIST_REL v_rel as bs /\
   LIST_REL v_rel xs ys ==>
   (do_eq_list as xs) = (do_eq_list bs ys))
Proof
  ho_match_mp_tac do_eq_ind >> rpt strip_tac >>
  fs[do_eq_def,v_rel_Closure] >>
  rpt TOP_CASE_TAC >> fs[] >>
  every_drule LIST_REL_LENGTH >> fs[]
  >- (first_x_assum drule_all >> fs[])
  >- (first_x_assum drule_all >> fs[])
  >- (first_x_assum drule_all >> fs[] >>
     first_x_assum drule_all >> fs[])
  >- (first_x_assum drule_all >> fs[] >>
     first_x_assum drule_all >> fs[])
  >- (first_x_assum drule_all >> fs[])
  >- (first_x_assum drule_all >> fs[])
QED

val state_component_equality = semanticPrimitivesTheory.state_component_equality

Triviality s_with_refs[simp]:
   (s with refs := refs) = (s with refs := refs') <=>
   refs = refs'
Proof
  simp[state_component_equality]
QED

(*TODO move*)
Triviality dec_clock_const[simp]:
 (dec_clock s).refs = s.refs
Proof
 EVAL_TAC
QED

Triviality dec_clock_with_const[simp]:
 (dec_clock (s with refs := refs)) = (dec_clock s with refs := refs)
Proof
 EVAL_TAC
QED

Triviality v_rel_store_lookup:
  LIST_REL (store_v_rel v_rel) refs refs' ==>
  OPTREL (store_v_rel v_rel) (store_lookup n refs) (store_lookup n refs')
Proof
  rw[] >> drule_then assume_tac LIST_REL_LENGTH >>
  fs[store_lookup_def] >> TOP_CASE_TAC >> fs[] >>
  fs[LIST_REL_EL_EQN]
QED

Triviality v_rel_store_assign:
  LIST_REL (store_v_rel v_rel) refs refs' /\
  store_v_rel v_rel v v' ==>
  OPTREL (LIST_REL (store_v_rel v_rel))
     (store_assign n v refs) (store_assign n v' refs')
Proof
  rw[] >> drule_then assume_tac LIST_REL_LENGTH >>
  fs[store_assign_def,store_v_same_type_def] >>
  TOP_CASE_TAC >> fs[AllCasePreds()] >>
  IMP_RES_TAC LIST_REL_EL_EQN >>
  gvs[] >>
  TRY (first_x_assum every_drule) >>
  rw[] >>fs[] >>
  res_tac >> fs[] >>
  rpt (irule EVERY2_LUPDATE_same >> fs[EVERY2_refl,store_v_rel_refl,v_rel_refl]) >>
  Cases_on `n < LENGTH refs'` >> fs[] >>
  res_tac >> fs[] >>
 Cases_on `EL n refs` >> fs[] >>
  Cases_on `v` >> fs[]
QED

Triviality v_rel_store_alloc:
  LIST_REL (store_v_rel v_rel) refs refs' ==>
  store_v_rel v_rel v v' ==>
  (LIST_REL (store_v_rel v_rel) ### (=))
     (store_alloc v refs) (store_alloc v' refs')
Proof
  rw[] >> drule_then assume_tac LIST_REL_LENGTH >>
  fs[store_alloc_def]
QED

Triviality v_rel_do_app:
   LIST_REL v_rel xs ys /\
   LIST_REL (store_v_rel v_rel) refs refs' ==>
   OPTREL ((LIST_REL (store_v_rel v_rel) ### (=)) ### result_rel v_rel v_rel)
     (do_app (refs,t) op xs) (do_app (refs',t) op ys)
Proof
   strip_tac >>
   Cases_on `op`
   >~ [`Equality`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     imp_res_tac $ CONJUNCT1 v_rel_do_eq >>
     rfs[] >> fs[] >>
     qpat_x_assum `Eq_val _ = _` (mp_tac o GSYM) >>
     fs[])
   >~ [`Opassign`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V'  _` >>
     (drule_then THEN_TCL qspecl_then [`V'`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,Abbr`V'`,OPTREL_SOME])
   >~ [`Opref`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_asmsub_abbrev_tac `store_alloc V  _` >>
     qmatch_goalsub_abbrev_tac `store_alloc V'  _` >>
     (drule_then THEN_TCL qspecl_then[`V'`,`V`]) assume_tac v_rel_store_alloc >>
     rfs[Abbr`V`,Abbr`V'`,OPTREL_SOME,PAIR_REL_eq_PAIR])
   >~ [`Opderef`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME])
   >~ [`Aw8alloc`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[] >>
     qmatch_asmsub_abbrev_tac `store_alloc V  _` >>
     (drule_then THEN_TCL qspecl_then[`V`,`V`]) assume_tac v_rel_store_alloc >>
     rfs[Abbr`V`,OPTREL_SOME,PAIR_REL_eq_PAIR])
   >~ [`Aw8sub`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME])
   >~ [`Aw8length`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME])
   >~ [`Aw8update`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V  _` >>
     (drule_then THEN_TCL qspecl_then [`V`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,OPTREL_SOME])
   >~ [`CopyStrAw8`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V  _` >>
     (drule_then THEN_TCL qspecl_then [`V`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,OPTREL_SOME])
   >~ [`CopyAw8Str`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     TOP_CASE_TAC >> fs[])
   >~ [`CopyAw8Aw8`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     qmatch_goalsub_abbrev_tac `store_lookup n' _`  >>
     (drule_then THEN_TCL qspec_then `n'`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V  _` >>
     (drule_then THEN_TCL qspecl_then [`V`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,OPTREL_SOME])
   >~ [`XorAw8Str_unsafe`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V  _` >>
     (drule_then THEN_TCL qspecl_then [`V`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,OPTREL_SOME])
   >~ [`Implode`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     drule_then mp_tac v_rel_v_to_char_list >>
     fs[] >> disch_then (assume_tac o GSYM) >>
     fs[])
   >~ [`Strcat`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     drule_then strip_assume_tac v_rel_v_to_list >>
     rfs[OPTREL_SOME] >>
     drule_then strip_assume_tac v_rel_vs_to_string >>
     fs[] >> fs[store_v_rel_refl,EVERY2_refl,v_rel_refl])
   >~ [`VfromList`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     drule_then strip_assume_tac v_rel_v_to_list >>
     rfs[OPTREL_SOME])
   >~ [`Vsub`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[] >>
     every_drule_then assume_tac LIST_REL_LENGTH >>
     fs[] >>
     fs[LIST_REL_EL_EQN])
   >~ [`Vlength`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     every_drule_then assume_tac LIST_REL_LENGTH >>
     fs[])
   >~ [`Aalloc`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[] >>
     qmatch_asmsub_abbrev_tac `store_alloc V'  _` >>
     qmatch_goalsub_abbrev_tac `store_alloc V  _` >>
     (drule_then THEN_TCL qspecl_then[`V`,`V'`]) assume_tac v_rel_store_alloc >>
     rfs[Abbr`V`,Abbr`V'`,OPTREL_SOME,PAIR_REL_eq_PAIR,LIST_REL_REPLICATE_same])
   >~ [`AallocEmpty`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[] >>
     qmatch_asmsub_abbrev_tac `store_alloc V  _` >>
     qmatch_goalsub_abbrev_tac `store_alloc V  _` >>
     (drule_then THEN_TCL qspecl_then[`V`,`V`]) assume_tac v_rel_store_alloc >>
     rfs[Abbr`V`,OPTREL_SOME,PAIR_REL_eq_PAIR,LIST_REL_REPLICATE_same])
   >~ [`AallocFixed`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[] >>
     qmatch_asmsub_abbrev_tac `store_alloc V  _` >>
     qmatch_goalsub_abbrev_tac `store_alloc V'  _` >>
     (drule_then THEN_TCL qspecl_then[`V'`,`V`]) assume_tac v_rel_store_alloc >>
     rfs[Abbr`V`,Abbr`V'`,OPTREL_SOME,PAIR_REL_eq_PAIR,LIST_REL_REPLICATE_same])
   >~ [`Asub`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     every_drule_then assume_tac LIST_REL_LENGTH >>
     fs[] >> fs[LIST_REL_EL_EQN])
   >~ [`Alength`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     every_drule_then assume_tac LIST_REL_LENGTH >> fs[])
   >~ [`Aupdate`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     every_drule_then assume_tac LIST_REL_LENGTH >> fs[] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V'  _` >>
     (drule_then THEN_TCL qspecl_then [`V'`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,Abbr`V'`,OPTREL_SOME] >>
     gvs[EVERY2_LUPDATE_same])
   >~ [`Asub_unsafe`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     every_drule_then assume_tac LIST_REL_LENGTH >> fs[] >>
     fs[LIST_REL_EL_EQN])
   >~ [`Aupdate_unsafe`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     every_drule_then assume_tac LIST_REL_LENGTH >> fs[] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V'  _` >>
     (drule_then THEN_TCL qspecl_then [`V'`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,Abbr`V'`,OPTREL_SOME] >>
     gvs[EVERY2_LUPDATE_same])
   >~ [`Aw8sub_unsafe`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME])
   >~ [`Aw8update_unsafe`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V  _` >>
     (drule_then THEN_TCL qspecl_then [`V`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,OPTREL_SOME])
   >~ [`ListAppend`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     every_drule_then assume_tac  v_rel_v_to_list >>
     rfs[OPTREL_SOME] >> fs[store_v_rel_refl,EVERY2_refl,v_rel_refl] >>
     fs[v_rel_list_to_v] >>
     fs[LIST_REL_APPEND_suff])
   >~ [`FFI`]
   >- (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     qmatch_goalsub_abbrev_tac `store_lookup n _`  >>
     (drule_then THEN_TCL qspec_then `n`) assume_tac v_rel_store_lookup >>
     rfs[OPTREL_SOME] >>
     qmatch_asmsub_abbrev_tac `store_assign lnum V  _` >>
     qmatch_goalsub_abbrev_tac `store_assign lnum V  _` >>
     (drule_then THEN_TCL qspecl_then [`V`,`V`,`lnum`]) assume_tac v_rel_store_assign >>
     rfs[Abbr`V`,OPTREL_SOME])
   >> TRY (
     qmatch_goalsub_abbrev_tac `do_app _ op _` >>
     Cases_on `do_app (refs,t) op xs` >>
     qunabbrev_tac `op` >>
     qpat_x_assum  `do_app _ _ _ = _`
       (strip_assume_tac o SRULE[SF LET_ss,do_app_def,AllCaseEqs(),UNCURRY_EQ]) >>
     rveq >> fs[v_rel_Closure] >> rveq >>
     simp_tac(srw_ss()) [do_app_def] >>
     fs[EVERY2_refl,store_v_rel_refl,v_rel_refl] >>
     rpt TOP_CASE_TAC >> gs[] >> NO_TAC)
QED


Theorem env_rel_build_rec_env:
  env_rel v_rel envx envy /\
  env_rel v_rel enva envb ==>
  env_rel v_rel <|v := build_rec_env funs envx enva.v; c := envxC|>
          <|v := build_rec_env funs envy envb.v; c := envxC|>
Proof
  strip_tac >> fs[build_rec_env_merge] >>
  irule env_rel_nsAppend >> fs[] >>
  REVERSE CONJ_TAC >- fs[env_rel_def] >>
  irule  env_rel_alist_to_ns >>
  fs[EVERY2_MAP ] >>
  fs[ELIM_UNCURRY,v_rel_Closure] >>
  fs[ EVERY2_refl]
QED

Theorem env_rel_build_rec_env2:
  env_rel v_rel envx envy ==>
  env_rel v_rel <|v := build_rec_env funs envx nsEmpty; c := envxC|>
          <|v := build_rec_env funs envy nsEmpty; c := envxC|>
Proof
  strip_tac >> fs[build_rec_env_merge] >>
  irule  env_rel_alist_to_ns >>
  fs[EVERY2_MAP ] >>
  fs[ELIM_UNCURRY,v_rel_Closure] >>
  fs[ EVERY2_refl]
QED

val s = mk_var ("s", ``: 'ffi semanticPrimitives$state``);
Triviality sem_env_elim:
   !env envV. (env: v sem_env) with v := envV = <|v := envV; c := env.c|>
Proof
fs[ semanticPrimitivesTheory.sem_env_component_equality]
QED

Theorem v_rel_evaluate:
  (!s envx es s' res envy refs.
  env_rel v_rel envx envy /\
  LIST_REL (store_v_rel v_rel) s.refs refs /\
  evaluate ^s envx es = (s',res) ==>
  ?res' t refs'.
  evaluate (s with refs := refs) envy es = (t,res') /\
  t = (s' with refs := refs') /\
  LIST_REL (store_v_rel v_rel) s'.refs refs' /\
  result_rel (LIST_REL v_rel) v_rel res res') /\
  (!s envx v pes err_v s' res envy v' err_v' refs.
   env_rel v_rel envx envy /\
   LIST_REL (store_v_rel v_rel) s.refs refs /\
   v_rel v v' /\ v_rel err_v err_v'  ==>
   evaluate_match ^s envx v pes err_v = (s',res) ==>
   ?res' t refs'.
   evaluate_match (s with refs := refs) envy v' pes err_v' = (t,res') /\
   t = (s' with refs := refs') /\
   LIST_REL (store_v_rel v_rel) s'.refs refs' /\
   result_rel (LIST_REL v_rel) v_rel res res')
Proof
  ho_match_mp_tac evaluate_ind >>
  rpt strip_tac
  >- (fs[evaluate_def])
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    gvs[] >> simp[evaluate_def] >> gvs[]
    >-(
      first_x_assum $ drule_all_then strip_assume_tac >> fs[] >>
      first_x_assum $ drule_all_then strip_assume_tac >> fs[] >>
      every_drule_then strip_assume_tac evaluate_sing >> fs[])
    >-(
      first_x_assum $ drule_all_then strip_assume_tac >> fs[] >>
      first_x_assum $ drule_all_then strip_assume_tac >> fs[]
      )
    >-(
      first_x_assum $ drule_all_then strip_assume_tac >> fs[])
      )
  (* Lit *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[])
  (* Raise *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >> fs[] >>
    every_drule_then strip_assume_tac evaluate_sing >> fs[])
  (* Handle *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >> fs[]
    >- (
    `envx.c = envy.c` by fs[env_rel_def] >>
   drule_all_then (fs o single) v_rel_can_pmatch_all)
    >- (
    `envx.c = envy.c` by fs[env_rel_def] >>
    drule_all_then (fs o single) v_rel_can_pmatch_all))
  (* Con *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    fs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >> fs[]
    >- (
      qspecl_then [`REVERSE v'`,`REVERSE vs`,`envy.c`,`cn`] mp_tac $ GEN_ALL  v_rel_build_conv >>
      impl_tac >- fs[]>>
      fs[])
    >- (
      qspecl_then [`REVERSE v'`,`REVERSE vs`,`envy.c`,`cn`] mp_tac $ GEN_ALL  v_rel_build_conv >>
      impl_tac >- fs[]>>
      fs[OPTREL_SOME] >> strip_tac >>
      fs[]))
  (* Var *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[] >>
    fs[env_rel_def] >>
    first_x_assum (qspec_then `n` mp_tac) >>
    fs[OPTREL_SOME] >> rw[] >> fs[])
  (* Fun *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    simp[Once v_rel_cases])
  (* App *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (mp_tac o SRULE[Once evaluate_def,Excl "getOpClass_def"]) >>
    Cases_on `getOpClass op` >> fs[] >>
    simp[evaluate_def]
    >- (cheat)
    >- (
      disch_then (strip_assume_tac o SRULE[AllCaseEqs()]) >>
      gvs[] >>
      first_x_assum $ drule_all_then strip_assume_tac >>
      gvs[] >>
      (qspecl_then [`REVERSE v'`,`REVERSE vs`] mp_tac $ GEN_ALL v_rel_do_opapp >>
      impl_tac >- fs[]) >>
      fs[OPTREL_SOME,PAIR_REL_eq_PAIR,PULL_EXISTS])
    >- (
      disch_then (strip_assume_tac o SRULE[AllCaseEqs()]) >>
      gvs[] >>
      first_x_assum $ drule_all_then strip_assume_tac >>
      gvs[] >>
      rename1`do_app (refs'',s'.ffi) op (REVERSE v')` >>
      (qspecl_then [`REVERSE v'`,`REVERSE vs`,`s'.ffi`,`refs''`,`s'.refs`,`op`] mp_tac
         $ GEN_ALL v_rel_do_app >>
      impl_tac >- fs[]) >>
      fs[] >> strip_tac >> fs[OPTREL_SOME,PAIR_REL_eq_PAIR]))
  (* Log *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    gvs[] >>
    qpat_x_assum `do_log _ _ _ = _`
       (strip_assume_tac o SRULE[do_log_def,AllCaseEqs()]) >>
    every_drule_then strip_assume_tac evaluate_sing >> gvs[] >>
    TOP_CASE_TAC >>
    qpat_x_assum `do_log _ _ _ = _`
       (strip_assume_tac o SRULE[do_log_def,AllCaseEqs()]) >>
    gvs[])
  (* If *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    gvs[] >>
    qpat_x_assum `do_if _ _ _ = _`
       (strip_assume_tac o SRULE[do_if_def,AllCaseEqs()]) >>
    every_drule_then strip_assume_tac evaluate_sing >> gvs[] >>
    TOP_CASE_TAC >>
    qpat_x_assum `do_if _ _ _ = _`
       (strip_assume_tac o SRULE[do_if_def,AllCaseEqs()]) >>
    gvs[])
  (* Mat *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    gvs[] >>
    every_drule_then strip_assume_tac evaluate_sing >> gvs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    drule_all_then (fs o single) v_rel_can_pmatch_all)
  (* Let *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    gvs[] >>
    every_drule_then strip_assume_tac evaluate_sing >> gvs[] >>
    qmatch_goalsub_abbrev_tac `evaluate _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    disch_then (drule_at (Pos $ el 2)) >>
    qunabbrev_tac `envy'` >>
    impl_tac >- fs[ env_rel_nsOptBind] >>
    strip_tac >> fs[])
  (* Letrec *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    qmatch_goalsub_abbrev_tac `evaluate _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    disch_then (drule_at (Pos $ el 2)) >>
    qunabbrev_tac `envy'` >>
    impl_tac >-
      (`envx.c = envy.c` by fs[env_rel_def] >>
      PURE_ONCE_REWRITE_TAC[sem_env_elim] >>
      fs[] >>
      irule env_rel_build_rec_env >>
      fs[])>>
    strip_tac >> fs[])
  (* Tannot *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    fs[])
  (* Lannot *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    fs[])
  (* evaluate_match single*)
  >- (gvs[evaluate_match_def])
  (* evaluate_match Cons *)
  >- (
    qpat_x_assum `evaluate_match  _ _ _ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_match_def ,AllCaseEqs()]) >>
    simp[evaluate_match_def] >> gvs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    drule_at (Pos $ el 4) $ CONJUNCT1 v_rel_pmatch >>
    fs[] >> disch_then $ drule_all_then strip_assume_tac >>
    fs[] >>
    qmatch_goalsub_abbrev_tac `evaluate _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    disch_then (drule_at (Pos $ el 2)) >>
    qunabbrev_tac `envy'` >>
    impl_tac >-
      (irule env_rel_nsAppend >>
       CONJ_TAC >-
        (PURE_ONCE_REWRITE_TAC[sem_env_elim] >>
        fs[] >>
        irule env_rel_alist_to_ns >>
        fs[])
        >- (fs[env_rel_def])) >>
    strip_tac >> fs[])
QED

Theorem v_rel_evaluate_decs:
  !s envx ds s' res envy refs.
   evaluate_decs s envx ds = (s', res) ∧
   env_rel v_rel envx envy /\
   LIST_REL (store_v_rel v_rel) s.refs refs ==>
   ? res' t refs'.
   evaluate_decs (s with refs := refs) envy ds = (t,res') /\
   t = s' with refs := refs' /\
   LIST_REL (store_v_rel v_rel) s'.refs refs' /\
   result_rel (env_rel v_rel) v_rel res res'
Proof
  ho_match_mp_tac evaluate_decs_ind >> rpt strip_tac
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> fs[env_rel_def,v_rel_refl])
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `evaluate_decs _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    disch_then $ drule_at (Pos $ el 2) >>
    qunabbrev_tac `envy'` >>
    impl_tac >- simp[env_rel_extend_dec_env]>>
    strip_tac  >> fs[] >>
    fs[combine_dec_result_def] >>
    TOP_CASE_TAC >> fs[] >>
    simp[SRULE []$ GSYM extend_dec_env_def] >>
    simp[env_rel_extend_dec_env])
  (* Dlet *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    fs[] >>
    drule_all $ CONJUNCT1  v_rel_evaluate >>
    strip_tac >> fs[] >>
    every_drule_then strip_assume_tac evaluate_sing >> gvs[] >>
    drule_at (Pos $ el 4) $ CONJUNCT1 v_rel_pmatch >>
    fs[] >> disch_then drule_all >> strip_tac >> fs[] >>
    fs[env_rel_alist_to_ns])
  (* Dletrec *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    fs[]
    >- fs[env_rel_build_rec_env2]
    >- (drule_then (SUBST_ALL_TAC o EQF_INTRO) (iffRL NOT_EVERY) >>
       fs[])
     )
  (* Dtype *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[]
    >> (drule_then (SUBST_ALL_TAC o EQF_INTRO) (iffRL NOT_EVERY) >>
        fs[])
    )
  (* Dtabbrev *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[]
    )
  (* Denv *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[]
    >> cheat)
  (* Dexn *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[]
    >> simp[env_rel_def])
  (* Dmod *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    gvs[] >>
    fs[env_rel_nsLift])
  (* Dlocal *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `evaluate_decs _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    disch_then $ drule_at (Pos $ el 2) >>
    qunabbrev_tac `envy'` >>
    impl_tac >- fs[env_rel_extend_dec_env]>>
    strip_tac >> fs[])
QED

Triviality compile_decs_cons:
 !d ds.compile_decs (d ::ds) = HD (compile_decs [d]) :: compile_decs ds
Proof
  Induct_on `ds` >> rw[compile_decs_def] >>
  rpt (TOP_CASE_TAC >> simp[])
QED

Triviality compile_decs_sing_HD:
  !ds. [HD (compile_decs [ds])] = compile_decs [ds]
Proof
  Induct_on `ds`  >> rw[compile_decs_def] >>
  rpt (TOP_CASE_TAC >> simp[])
QED

(*TODO this is false the results needs to be weakened to an
  equivalence relation*)
Theorem compile_decs_correct:
  ∀s env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate_decs s env (compile_decs ds) = (s', res)
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rw [Once compile_decs_def]
  >~ [‘d1::d2::ds’] >- (
    qpat_x_assum ‘evaluate_decs _ _ _ = _’ mp_tac
    \\ simp [Once evaluate_decs_def]
    \\ disch_then (strip_assume_tac o SRULE[AllCaseEqs()])
    \\ gvs[]
    \\ simp[Once compile_decs_cons,compile_decs_sing_HD]
    \\ simp[Once evaluate_decs_cons,compile_decs_sing_HD]
    \\ fs[ combine_dec_result_eq_Rerr])
  >~ [‘[Dmod _ _]’] >- (
    gvs [compile_decs_def,evaluate_decs_def,AllCaseEqs()])
  >~ [‘[Dlocal _ _]’] >- (
    gvs [compile_decs_def,evaluate_decs_def,AllCaseEqs()])
  >~ [‘[Dletrec _ _]’] >- (
    gvs [compile_decs_def] >>
    TOP_CASE_TAC  >- fs[] >>
    reverse TOP_CASE_TAC  >- fs[] >>
    `? fun_name first_arg exp.h = (fun_name,first_arg,exp)`
       by (PairCases_on `h` >> simp_tac(srw_ss())[]) >>
     POP_ASSUM SUBST_ALL_TAC >> simp[] >>
     TOP_CASE_TAC >> cheat)
  >> fs[compile_decs_def]
QED

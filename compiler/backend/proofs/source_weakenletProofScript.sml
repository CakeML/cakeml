(*source_weakenletTheory
  Correctness for the source_letweaken pass.
 *)
Theory source_weakenletProof
Ancestors
  source_weakenlet evaluate evaluateProps semanticPrimitives
  semanticPrimitivesProps misc[qualified] semantics ast
Libs
  preamble

Definition env_rel_def:
  env_rel rel (envx: 'a sem_env) envy = ((!n. OPTREL rel (nsLookup envx.v n) (nsLookup envy.v n))
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
   find_recfun fun_name funs = SOME (var,exp) /\
   ~ EXISTS (\fun_name. exists_call fun_name exp) (MAP FST funs) ==>
   (v_rel (Closure envx var exp) (Recclosure envy funs fun_name)))
   /\
   (env_rel v_rel envx envy /\
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

Theorem env_rel_extend_dec_env:
  env_rel v_rel enva envb ==>
  env_rel v_rel envx envy ==>
  env_rel v_rel (enva +++ envx) (envb +++ envy)
Proof
  cheat
  (* TODO currently unprovable env_rel needs to be changed
  rpt strip_tac >> fs[env_rel_def,extend_dec_env_def] >>
  qx_gen_tac `n` >>
  first_x_assum (fn x => qspec_then `n` assume_tac x >> mp_tac x) >>
  first_x_assum (fn x => qspec_then `n` assume_tac x >> mp_tac x) >>
  rpt (disch_then last_assume_tac) >>
  Cases_on `nsLookup (nsAppend enva.v envx.v) n` >>
  >- (
    fs[namespacePropsTheory.nsLookup_nsAppend_none] >>
    Cases_on `nsLookup envy.v n` >> fs[OPTREL_SOME] >>
    every_drule_then strip_assume_tac
      namespacePropsTheory.nsLookup_to_nsLookupMod >>
  *)
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

Triviality v_rel_pmatch:
 (!envC refs p v env res v' env'.
   v_rel v v' /\
   LIST_REL ((=) ### v_rel) env env' /\
   pmatch envC refs p v env = res ==>
   ?res'.
   pmatch envC refs p v' env' = res' /\
   match_result_rel (LIST_REL ((=) ### v_rel)) res res') /\
  (!envC s ps vs envs res vs' envs'.
   LIST_REL v_rel vs vs' /\
   LIST_REL ((=) ### v_rel) envs envs' /\
   pmatch_list envC s (ps) (vs) envs = res ==>
   ?res'.
   pmatch_list envC s (ps) (vs') envs' = res' /\
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
  >- (rpt TOP_CASE_TAC >> gvs[] >>
     first_x_assum irule >> fs[v_rel_refl])
  >>~- ([`Closure`],fs[Once v_rel_cases,pmatch_def])
  >>~- ([`Recclosure`],fs[Once v_rel_cases,pmatch_def])
  >- (
     Cases_on `pmatch envC s p v envs` >> fs[] >>
     Cases_on `pmatch_list envC s ps vs envs` >> fs[] >>
     res_tac >> fs[])
QED

Triviality v_rel_can_pmatch_all:
  v_rel v v' ==>
  (can_pmatch_all envC refs ps v' =
  can_pmatch_all envC refs ps v)
Proof
 rw[] >>
 Cases_on `can_pmatch_all envC refs ps v` >>
 fs[]
 >-(
   fs[can_pmatch_all_EVERY] >> fs[EVERY_MEM] >>
   rw[] >> first_x_assum $ drule_then assume_tac >>
   Cases_on `pmatch envC refs p v []` >> fs[] >>
   drule_at(Pos $ el 3) $ CONJUNCT1 v_rel_pmatch >>
   fs[] >> disch_then drule >> rw[] >> fs[])
 >-(
   fs[can_pmatch_all_EVERY] >> fs[EXISTS_MEM] >>
   rw[] >>
   drule_at(Pos $ el 3) $ CONJUNCT1 v_rel_pmatch >>
   fs[] >> disch_then drule >> rw[] >> fs[] >>
   metis_tac[])
QED

Triviality v_rel_build_conv:
  LIST_REL v_rel xs ys ==>
  OPTREL v_rel (build_conv envC cn xs) (build_conv envC cn ys)
Proof
  fs[build_conv_def] >> rpt TOP_CASE_TAC >> fs[]
QED

val s = mk_var ("s", ``: 'ffi semanticPrimitives$state``);
val st = mk_var ("st", ``: 'ffi semanticPrimitives$state``);

Theorem v_rel_evaluate:
  (!s envx es s' res envy.
  env_rel v_rel envx envy /\
  evaluate ^s envx es = (s',res) ==>
  ?res'.
  evaluate s envy es = (s',res') /\
  result_rel (LIST_REL v_rel) v_rel res res') /\
  (!st envx v pes err_v s' res envy v' err_v'.
   env_rel v_rel envx envy /\
   v_rel v v' /\ v_rel err_v err_v'  ==>
   evaluate_match ^st envx v pes err_v = (s',res) ==>
   ?res'.
   evaluate_match st envy v' pes err_v' = (s',res') /\
   result_rel (LIST_REL v_rel) v_rel res res')
Proof
  ho_match_mp_tac evaluate_ind >>
  rpt strip_tac
  >- (fs[evaluate_def])
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    gvs[] >> simp[evaluate_def] >> gvs[]
    >-
      (first_x_assum $ drule_then assume_tac >>
      first_x_assum $ drule_then strip_assume_tac >>
      gvs[] >>
      every_drule_then strip_assume_tac evaluate_sing >> fs[]
      )
    >- (first_x_assum $ drule_then assume_tac >>
      first_x_assum $ drule_then strip_assume_tac >>
      gvs[] >>
      every_drule_then strip_assume_tac evaluate_sing >> fs[]
      )
    >-(first_x_assum $ drule_then strip_assume_tac >>
      fs[]))
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[])
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl]
    >-(first_x_assum $ drule_then strip_assume_tac >>
      gvs[] >>
      every_drule_then strip_assume_tac evaluate_sing >> fs[]
      )
    >-(first_x_assum $ drule_then strip_assume_tac >>
      gvs[] >>
      every_drule_then strip_assume_tac evaluate_sing >> fs[]
      )
     )
  (* Handle *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    first_x_assum $ drule_then strip_assume_tac >>
    fs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    drule_then (fs o single) v_rel_can_pmatch_all)
  (* Con *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    fs[] >>
    first_x_assum $ drule_then strip_assume_tac >>
    gvs[]
    >- (
      qspecl_then [`REVERSE v'`,`REVERSE vs`,`envy.c`,`cn`] mp_tac $ GEN_ALL  v_rel_build_conv >>
      impl_tac >- fs[]>>
      fs[])
    >- (
      qspecl_then [`REVERSE v'`,`REVERSE vs`,`envy.c`,`cn`] mp_tac $ GEN_ALL  v_rel_build_conv >>
      impl_tac >- fs[]>>
      fs[OPTREL_SOME] >> strip_tac >>
      fs[]))
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
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
  >- ( cheat)
  (* Log *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    first_x_assum $ drule_then strip_assume_tac >>
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
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    first_x_assum $ drule_then strip_assume_tac >>
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
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    first_x_assum $ drule_then strip_assume_tac >>
    gvs[] >>
    every_drule_then strip_assume_tac evaluate_sing >> gvs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    drule_then (fs o single) v_rel_can_pmatch_all)
  (* Let *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    first_x_assum $ drule_then strip_assume_tac >>
    gvs[] >>
    every_drule_then strip_assume_tac evaluate_sing >> gvs[] >>
    qmatch_goalsub_abbrev_tac `evaluate _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    qunabbrev_tac `envy'` >>
    impl_tac >- cheat >>
    strip_tac >> fs[])
  (* Letrec *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def] >> gvs[v_rel_refl] >>
    qmatch_goalsub_abbrev_tac `evaluate _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    qunabbrev_tac `envy'` >>
    impl_tac >- cheat >>
    strip_tac >> fs[])
  (* Tannot *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def])
  (* Lannot *)
  >- (
    qpat_x_assum `evaluate_ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_def,AllCaseEqs()]) >>
    simp[evaluate_def])
  (* evaluate_match single*)
  >- (gvs[evaluate_match_def])
  (* evaluate_match Cons *)
  >- (
    qpat_x_assum `evaluate_match  _ _ _ _ _ = (s',res)`
       (strip_assume_tac o SRULE[Once evaluate_match_def ,AllCaseEqs()]) >>
    simp[evaluate_match_def] >> gvs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    drule_at (Pos $ el 3) $ CONJUNCT1 v_rel_pmatch >>
    fs[] >> disch_then $ drule_then strip_assume_tac >>
    fs[] >>
    qmatch_goalsub_abbrev_tac `evaluate _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    qunabbrev_tac `envy'` >>
    impl_tac >- cheat >>
    strip_tac >> fs[])
QED

Theorem v_rel_evaluate_decs:
  !s envx ds s' res envy.
   evaluate_decs s envx ds = (s', res) ∧
   env_rel v_rel envx envy ==>
   ? res'.
   evaluate_decs s envy ds = (s',res') /\
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
    first_x_assum $ drule_then strip_assume_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `evaluate_decs _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    qunabbrev_tac `envy'` >>
    impl_tac >- cheat >>
    strip_tac  >> fs[] >>
    fs[combine_dec_result_def] >>
    TOP_CASE_TAC >> fs[] >>
    cheat)
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
    drule_at (Pos $ el 3) $ CONJUNCT1 v_rel_pmatch >>
    fs[] >> disch_then drule >> strip_tac >> fs[] >>
    cheat)
  (* Dletrec *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[] >>
    `envx.c = envy.c` by fs[env_rel_def] >>
    fs[]
    >- cheat
    >- (drule_then (SUBST_ALL_TAC o EQF_INTRO) (iffRL NOT_EVERY) >>
       fs[])
     )
  (* Dtype *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[]
    >- simp[env_rel_def]
    >- (drule_then (SUBST_ALL_TAC o EQF_INTRO) (iffRL NOT_EVERY) >>
        fs[])
    )
  (* Dtabbrev *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[]
    >- simp[env_rel_def])
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
    first_x_assum $ drule_then strip_assume_tac >>
    gvs[] >> cheat)
  (* Dlocal *)
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _`
       (strip_assume_tac o SRULE[evaluate_decs_def,AllCaseEqs()]) >>
    fs[evaluate_decs_def] >> gvs[] >>
    first_x_assum $ drule_then strip_assume_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `evaluate_decs _ envy' _` >>
    first_x_assum (qspec_then `envy'` mp_tac) >>
    qunabbrev_tac `envy'` >>
    impl_tac >- cheat >>
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
     POP_ASSUM SUBST_ALL_TAC >> simp[]
     TOP_CASE_TAC >> cheat)
  >> fs[compile_decs_def]
QED

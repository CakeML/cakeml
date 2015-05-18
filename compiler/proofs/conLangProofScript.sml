open preamble;
open alistTheory optionTheory rich_listTheory;
open miscTheory;
open astTheory;
open semanticPrimitivesTheory;
open libTheory;
open modLangTheory;
open conLangTheory;
open modLangProofTheory;
open evalPropsTheory;
open terminationTheory;
open free_varsTheory compilerTerminationTheory;
open miscLib;

val _ = new_theory "conLangProof";

val merge_alist_mod_env_empty = Q.prove (
`!mod_env. merge_alist_mod_env ([],[]) mod_env = mod_env`,
rw [] >>
PairCases_on `mod_env` >>
rw [merge_alist_mod_env_def]);

val no_dup_types_i1_cons_imp = prove(
  ``no_dup_types_i1 (d::ds) ⇒ no_dup_types_i1 ds``,
  rw[decs_to_types_i1_def,no_dup_types_i1_def,ALL_DISTINCT_APPEND]);

val same_tid_refl = store_thm("same_tid_refl",
  ``same_tid t t``,
  Cases_on`t`>>EVAL_TAC)

val same_tid_diff_ctor = Q.prove (
`!cn1 cn2 t1 t2.
  same_tid t1 t2 ∧ ~same_ctor (cn1, t1) (cn2, t2)
  ⇒
  (cn1 ≠ cn2) ∨ (cn1 = cn2 ∧ ?mn1 mn2. t1 = TypeExn mn1 ∧ t2 = TypeExn mn2 ∧ mn1 ≠ mn2)`,
rw [] >>
cases_on `t1` >>
cases_on `t2` >>
fs [same_tid_def, same_ctor_def]);

val build_rec_env_i2_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. ((f, Recclosure_i2 env funs' f) :: env')) env' funs =
MAP (λ(fn,n,e). (fn, Recclosure_i2 env funs' fn)) funs ++ env'`,
Induct >>
rw [] >>
PairCases_on `h` >>
rw []);

val build_rec_env_i2_merge = Q.store_thm ("build_rec_env_i2_merge",
`∀funs funs' env env'.
  build_rec_env_i2 funs env env' =
  MAP (λ(fn,n,e). (fn, Recclosure_i2 env funs fn)) funs ++ env'`,
rw [build_rec_env_i2_def, build_rec_env_i2_help_lem]);

val funs_to_i2_map = Q.prove (
`!funs.
  funs_to_i2 cenv funs = MAP (\(f,x,e). (f,x,exp_to_i2 cenv e)) funs`,
 induct_on `funs` >>
 rw [exp_to_i2_def] >>
 PairCases_on `h` >>
 rw [exp_to_i2_def]);

val _ = type_abbrev("gtagenv",``:conN # tid_or_exn |-> num # num``)

val has_exns_def = Define `
has_exns gtagenv ⇔
  FLOOKUP gtagenv ("Subscript", TypeExn (Short "Subscript")) = SOME (subscript_tag,0:num) ∧
  FLOOKUP gtagenv ("Bind", TypeExn (Short "Bind")) = SOME (bind_tag,0) ∧
  FLOOKUP gtagenv ("Chr", TypeExn (Short "Chr")) = SOME (chr_tag,0) ∧
  FLOOKUP gtagenv ("Div", TypeExn (Short "Div")) = SOME (div_tag,0) ∧
  FLOOKUP gtagenv ("Eq", TypeExn (Short "Eq")) = SOME (eq_tag,0)`;

val has_lists_def = Define `
has_lists gtagenv ⇔
  FLOOKUP gtagenv ("nil", TypeId (Short "list")) = SOME (nil_tag,0:num) ∧
  FLOOKUP gtagenv ("::", TypeId (Short "list")) = SOME (cons_tag,2)`;

val has_bools_def = Define`
  has_bools gtagenv ⇔
  FLOOKUP gtagenv ("true", TypeId(Short"bool")) = SOME (true_tag,0:num) ∧
  FLOOKUP gtagenv ("false", TypeId(Short"bool")) = SOME (false_tag,0:num)`

val gtagenv_wf_def = Define `
gtagenv_wf gtagenv ⇔
  has_exns gtagenv ∧
  has_bools gtagenv ∧
  has_lists gtagenv ∧
  (∀t1 t2 tag l cn cn'.
    same_tid t1 t2 ∧
    FLOOKUP gtagenv (cn,t1) = SOME (tag,l) ∧
    FLOOKUP gtagenv (cn',t2) = SOME (tag,l) ⇒
    cn = cn' ∧ t1 = t2)`;

val envC_tagged_def = Define `
envC_tagged (envC:envC) (tagenv:tag_env) gtagenv =
  (!cn num_args t.
    lookup_alist_mod_env cn envC = SOME (num_args, t)
    ⇒
    ?tag.
      lookup_tag_env (SOME cn) tagenv = SOME (tag, t) ∧
      FLOOKUP gtagenv (id_to_n cn, t) = SOME (tag,num_args))`;

val exhaustive_env_correct_def = Define `
exhaustive_env_correct (exh:exh_ctors_env) (gtagenv:gtagenv) ⇔
  (∀t. t ∈ FRANGE exh ⇒ wf t) ∧
  (* (FDOM exh ⊆ { t | TypeId t ∈ IMAGE SND (FDOM gtagenv) }) ∧ *)
  (!t.
     (?cn. (cn, TypeId t) ∈ FDOM gtagenv)
     ⇒
     ?tags.
       FLOOKUP exh t = SOME tags ∧
       (!cn tag l. FLOOKUP gtagenv (cn,TypeId t) = SOME (tag,l)
         ⇒
         ∃max. lookup l tags = SOME max ∧ tag < max))`;

(* this probably doesn't work because of the accumulator inside a module...?
val same_mod_def = Define`
  (same_mod (Long x _) (TypeId (Long x' _)) ⇔ x = x') ∧
  (same_mod (Long x y) (TypeExn (Long x' y')) ⇔ x = x' ∧ y = y') ∧
  (same_mod (Short _) (TypeId (Short _)) ⇔ T) ∧
  (same_mod (Short x) (TypeExn (Short x')) ⇔ x = x') ∧
  (same_mod _ _ = F)`

val envC_wf_def = Define`
  envC_wf envC ⇔
    ∀cn a t. lookup_alist_mod_env cn envC = SOME (a,t) ⇒
             same_mod cn t`
*)

val cenv_inv_def = Define `
cenv_inv envC exh tagenv gtagenv ⇔
 (* envC_wf envC ∧ *)
 envC_tagged envC tagenv gtagenv ∧
 exhaustive_env_correct exh gtagenv ∧
 gtagenv_wf gtagenv`;

val (v_to_i2_rules, v_to_i2_ind, v_to_i2_cases) = Hol_reln `
(!gtagenv lit.
  v_to_i2 gtagenv (Litv_i1 lit) (Litv_i2 lit)) ∧
(!gtagenv vs vs'.
  vs_to_i2 gtagenv vs vs'
  ⇒
  v_to_i2 gtagenv (Conv_i1 NONE vs) (Conv_i2 NONE vs')) ∧
(!gtagenv cn tn tag vs vs'.
  FLOOKUP gtagenv (cn,tn) = SOME (tag, LENGTH vs) ∧
  vs_to_i2 gtagenv vs vs'
  ⇒
  v_to_i2 gtagenv (Conv_i1 (SOME (cn,tn)) vs) (Conv_i2 (SOME (tag,tn)) vs')) ∧
(!gtagenv env x e env_i2 envC exh tagenv.
  env_to_i2 gtagenv env env_i2 ∧
  cenv_inv envC exh tagenv gtagenv
  ⇒
  v_to_i2 gtagenv (Closure_i1 (envC,env) x e) (Closure_i2 env_i2 x (exp_to_i2 tagenv e))) ∧
(!gtagenv env funs x envC env_i2 exh tagenv.
  env_to_i2 gtagenv env env_i2 ∧
  cenv_inv envC exh tagenv gtagenv
  ⇒
  v_to_i2 gtagenv (Recclosure_i1 (envC,env) funs x) (Recclosure_i2 env_i2 (funs_to_i2 tagenv funs) x)) ∧
(!gtagenv loc.
  v_to_i2 gtagenv (Loc_i1 loc) (Loc_i2 loc)) ∧
(!gtagenv vs vs'.
  vs_to_i2 gtagenv vs vs'
  ⇒
  v_to_i2 gtagenv (Vectorv_i1 vs) (Vectorv_i2 vs')) ∧
(!gtagenv.
  vs_to_i2 gtagenv [] []) ∧
(!gtagenv v vs v' vs'.
  v_to_i2 gtagenv v v' ∧
  vs_to_i2 gtagenv vs vs'
  ⇒
  vs_to_i2 gtagenv (v::vs) (v'::vs')) ∧
(!gtagenv.
  env_to_i2 gtagenv [] []) ∧
(!gtagenv x v env env' v'.
  env_to_i2 gtagenv env env' ∧
  v_to_i2 gtagenv v v'
  ⇒
  env_to_i2 gtagenv ((x,v)::env) ((x,v')::env'))`;

val v_to_i2_eqns = Q.store_thm ("v_to_i2_eqns",
`(!gtagenv l v.
  v_to_i2 gtagenv (Litv_i1 l) v ⇔
    (v = Litv_i2 l)) ∧
 (!gtagenv cn vs v.
  v_to_i2 gtagenv (Conv_i1 cn vs) v ⇔
    (?vs' otag gtagenv'.
       vs_to_i2 gtagenv vs vs' ∧ (v = Conv_i2 otag vs') ∧
       (cn = NONE ∧ otag = NONE ∨
        ?cn' tn tag.
          otag = SOME (tag,tn) ∧
          FLOOKUP gtagenv (cn',tn) = SOME (tag,LENGTH vs) ∧
          cn = SOME (cn',tn)))) ∧
 (!gtagenv l v.
  v_to_i2 gtagenv (Loc_i1 l) v ⇔
    (v = Loc_i2 l)) ∧
 (!gtagenv cn vs v.
  v_to_i2 gtagenv (Vectorv_i1 vs) v ⇔
    (?vs'. vs_to_i2 gtagenv vs vs' ∧ (v = Vectorv_i2 vs'))) ∧
 (!gtagenv vs.
  vs_to_i2 gtagenv [] vs ⇔
    (vs = [])) ∧
 (!gtagenv l v vs vs'.
  vs_to_i2 gtagenv (v::vs) vs' ⇔
    ?v' vs''. v_to_i2 gtagenv v v' ∧ vs_to_i2 gtagenv vs vs'' ∧ vs' = v'::vs'') ∧
 (!gtagenv env'.
  env_to_i2 gtagenv [] env' ⇔
    env' = []) ∧
 (!gtagenv x v env env'.
  env_to_i2 gtagenv ((x,v)::env) env' ⇔
    ?v' env''. v_to_i2 gtagenv v v' ∧ env_to_i2 gtagenv env env'' ∧ env' = ((x,v')::env''))`,
rw [] >>
rw [Once v_to_i2_cases] >>
metis_tac []);

val vs_to_i2_list_rel = Q.prove (
`!gtagenv vs vs'. vs_to_i2 gtagenv vs vs' = LIST_REL (v_to_i2 gtagenv) vs vs'`,
 induct_on `vs` >>
 rw [v_to_i2_eqns] >>
 metis_tac []);

val gtagenv_weak_def = Define `
gtagenv_weak gtagenv1 gtagenv2 ⇔
  gtagenv1 SUBMAP gtagenv2 ∧
  (* Don't weaken by adding a constructor to an existing type. This is necessary for pattern exhaustiveness checking. *)
  (!t. (?cn. (cn,t) ∈ FDOM gtagenv1) ⇒ !cn. (cn,t) ∈ FDOM gtagenv2 ⇒ (cn,t) ∈ FDOM gtagenv1) ∧
  (!t1 t2 tag cn cn' l.
     same_tid t1 t2 ∧
     FLOOKUP gtagenv2 (cn,t1) = SOME (tag,l) ∧
     FLOOKUP gtagenv2 (cn',t2) = SOME (tag,l)
     ⇒
     cn = cn' ∧ t1 = t2)`;

val gtagenv_weak_refl = Q.prove (
`!gtagenv envC tagenv.
  gtagenv_wf gtagenv
  ⇒
  gtagenv_weak gtagenv gtagenv`,
 rw [gtagenv_weak_def] >>
 metis_tac [SUBMAP_REFL, gtagenv_wf_def]);

val gtagenv_weak_trans = Q.prove (
`!gtagenv1 gtagenv2 gtagenv3.
  gtagenv_weak gtagenv1 gtagenv2 ∧
  gtagenv_weak gtagenv2 gtagenv3
  ⇒
  gtagenv_weak gtagenv1 gtagenv3`,
 rw [gtagenv_weak_def] >>
 fs [FLOOKUP_DEF, SUBMAP_DEF] >>
 metis_tac []);

val gtagenv' = ``(gtagenv':gtagenv)``

val weakened_exh_def = Define`
  ((weakened_exh ^gtagenv' (exh:exh_ctors_env)):exh_ctors_env) =
    FUN_FMAP (λt.
      union
      (fromAList (SET_TO_LIST ({(l,1+(MAX_SET {tag | ∃cn. FLOOKUP ^gtagenv' (cn, TypeId t) = SOME (tag,l)}))
                               | l | ∃cn tag. FLOOKUP ^gtagenv' (cn, TypeId t) = SOME (tag,l)})))
      (case FLOOKUP exh t of NONE => LN | SOME tags => tags))
      { t | ∃cn. (cn, TypeId t) ∈ FDOM gtagenv' }`

val FINITE_weakened_exh_dom = prove(
  ``FINITE {t | ∃cn. (cn,TypeId t) ∈ FDOM ^gtagenv'}``,
  qmatch_abbrev_tac`FINITE P` >>
  qsuff_tac`∃f. P ⊆ IMAGE f (FDOM gtagenv')` >-
    metis_tac[IMAGE_FINITE,SUBSET_FINITE,FDOM_FINITE] >>
  simp[Abbr`P`,SUBSET_DEF] >>
  qexists_tac`λx. @y. SND x = TypeId y` >>
  rw[EXISTS_PROD] >> metis_tac[tid_or_exn_11]);

val FDOM_weakened_exh = prove(
  ``FDOM (weakened_exh ^gtagenv' exh) = { t | ∃cn. (cn, TypeId t) ∈ FDOM gtagenv' }``,
  rw[weakened_exh_def] >>
  (FUN_FMAP_DEF |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL |> match_mp_tac) >>
  rw[FINITE_weakened_exh_dom]);

val FLOOKUP_weakened_exh_imp = prove(
  ``(∀tags. tags ∈ FRANGE exh ⇒ wf tags) ∧
    (FLOOKUP (weakened_exh ^gtagenv' exh) t = SOME tags) ⇒
    wf tags ∧
    (∀a max. lookup a tags = SOME max ⇒
             (∃cn tag. FLOOKUP gtagenv' (cn, TypeId t) = SOME (tag,a) ∧ tag < max) ∨
             (∃tags'. FLOOKUP exh t = SOME tags'  ∧ lookup a tags' = SOME max)) ∧
    (∀cn tag a.
      FLOOKUP gtagenv' (cn, TypeId t) = SOME (tag,a) ⇒
      ∃max. lookup a tags = SOME max ∧ tag < max)``,
  simp[Once FLOOKUP_DEF,FDOM_weakened_exh] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  simp[weakened_exh_def] >>
  qmatch_abbrev_tac`wf (FUN_FMAP f X ' t) ∧ Z` >>
  strip_assume_tac(
    Q.ISPEC`f:string id -> num spt`(MATCH_MP FUN_FMAP_DEF FINITE_weakened_exh_dom)) >>
  fs[Abbr`X`,PULL_EXISTS,Abbr`Z`] >>
  res_tac >>
  pop_assum (SUBST1_TAC) >>
  simp[Abbr`f`] >>
  conj_tac >- (
    match_mp_tac sptreeTheory.wf_union >>
    conj_tac >- rw[sptreeTheory.wf_fromAList] >>
    BasicProvers.CASE_TAC >-
      rw[sptreeTheory.wf_def] >>
    fs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
    PROVE_TAC[]) >>
  simp[sptreeTheory.lookup_union,sptreeTheory.lookup_fromAList] >>
  qpat_abbrev_tac `s:(num#num) set = X` >>
  `FINITE s` by (
    simp[Abbr`s`,FLOOKUP_DEF] >>
    qmatch_abbrev_tac`FINITE P` >>
    qsuff_tac`∃f. P ⊆ IMAGE f (FDOM gtagenv')` >-
      metis_tac[IMAGE_FINITE,SUBSET_FINITE,FDOM_FINITE] >>
    `∃f. ∀x. x ∈ P ⇒ ∃y. y ∈ FDOM gtagenv' ∧ f y = x` by (
      simp[Abbr`P`,PULL_EXISTS] >>
      qho_match_abbrev_tac`∃f. ∀l cn' tag. Y cn' ∈ FDOM gtagenv' ∧ Z cn' tag l ⇒ ∃y. A y ∧ f y = X l cn' tag` >>
      qexists_tac`λp. X (SND (gtagenv' ' p)) (FST p) (FST (gtagenv' ' p))` >>
      simp[EXISTS_PROD,Abbr`Y`,Abbr`Z`] >>
      metis_tac[FST,SND] ) >>
    qexists_tac`f` >>
    simp[SUBSET_DEF] >>
    metis_tac[]) >>
  pop_assum(strip_assume_tac o MATCH_MP (GSYM SET_TO_LIST_IN_MEM)) >>
  conj_tac >- (
    rpt gen_tac >>
    rpt BasicProvers.CASE_TAC >> simp[CONJUNCT1 sptreeTheory.lookup_def] >>
    imp_res_tac ALOOKUP_MEM >>
    rfs[Abbr`s`] >> rw[] >>
    TRY disj1_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    qho_match_abbrev_tac`tag < (MAX_SET P) + 1` >>
    qho_match_abbrev_tac`Q (MAX_SET P)` >>
    match_mp_tac MAX_SET_ELIM >>
    `P ⊆ IMAGE FST (FRANGE gtagenv')` by (
      simp[Abbr`P`,SUBSET_DEF,IN_FRANGE_FLOOKUP,EXISTS_PROD] >>
      metis_tac[] ) >>
    (conj_tac >- metis_tac[FINITE_FRANGE,SUBSET_FINITE,IMAGE_FINITE]) >>
    (conj_tac >- ( simp[Abbr`P`,EXTENSION] >> metis_tac[] )) >>
    simp[Abbr`P`,Abbr`Q`,PULL_EXISTS] >>
    rw[] >> res_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  rpt BasicProvers.CASE_TAC >> simp[CONJUNCT1 sptreeTheory.lookup_def] >>
  TRY(
    CHANGED_TAC(imp_res_tac ALOOKUP_FAILS) >>
    rfs[Abbr`s`] >>
    metis_tac[]) >>
  imp_res_tac ALOOKUP_MEM >> rfs[Abbr`s`] >>
  qho_match_abbrev_tac`tag < (MAX_SET P) + 1` >>
  qho_match_abbrev_tac`Q (MAX_SET P)` >>
  match_mp_tac MAX_SET_ELIM >>
  `P ⊆ IMAGE FST (FRANGE gtagenv')` by (
    simp[Abbr`P`,SUBSET_DEF,IN_FRANGE_FLOOKUP,EXISTS_PROD] >>
    metis_tac[] ) >>
  (conj_tac >- metis_tac[FINITE_FRANGE,SUBSET_FINITE,IMAGE_FINITE]) >>
  (conj_tac >- ( simp[Abbr`P`,EXTENSION] >> metis_tac[] )) >>
  simp[Abbr`P`,Abbr`Q`,PULL_EXISTS] >>
  rw[] >> res_tac >> simp[])

val exhaustive_env_weak = Q.prove (
`!gtagenv gtagenv' exh.
    exhaustive_env_correct exh gtagenv ∧
    gtagenv_weak gtagenv ^gtagenv'
    ⇒
    ?exh'.
      exhaustive_env_correct exh' gtagenv'`,
 rw [gtagenv_weak_def, exhaustive_env_correct_def] >>
 qexists_tac `weakened_exh gtagenv' exh ⊌ exh` >>
 conj_tac >- (
   ho_match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
   rw[IN_FRANGE_FLOOKUP] >> imp_res_tac FLOOKUP_weakened_exh_imp) >>
 (*
 conj_tac >- (
   fs[FDOM_weakened_exh,EXISTS_PROD] >>
   fs[SUBMAP_DEF,SUBSET_DEF] >>
   metis_tac[] ) >>
 *)
 rw [] >>
 cases_on `?cn. (cn,TypeId t) ∈ FDOM gtagenv` >>
 res_tac >>
 fs [] >>
 rw []
 >- (`(cn,TypeId t) ∈ FDOM gtagenv` by metis_tac [] >>
     `?tags. FLOOKUP exh t = SOME tags ∧
             ∀cn tag l. FLOOKUP gtagenv (cn,TypeId t) = SOME (tag,l) ⇒
             ∃max. lookup l tags = SOME max ∧ tag < max` by metis_tac [] >>
     fs [FLOOKUP_FUNION] >>
     Cases_on `FLOOKUP (weakened_exh gtagenv' exh) t` >> simp[] >- (
       fs[FLOOKUP_DEF,FDOM_weakened_exh,PULL_EXISTS] ) >>
     imp_res_tac FLOOKUP_weakened_exh_imp >>
     rw [] >>
     metis_tac[]) >>
  simp[FLOOKUP_FUNION] >>
  BasicProvers.CASE_TAC >- (
    fs[FLOOKUP_DEF,FDOM_weakened_exh] ) >>
  imp_res_tac FLOOKUP_weakened_exh_imp >>
  metis_tac[]);

val v_to_i2_weakening = Q.prove (
`(!gtagenv v v_i2.
  v_to_i2 gtagenv v v_i2
  ⇒
    !gtagenv'. gtagenv_weak gtagenv gtagenv'
    ⇒
    v_to_i2 gtagenv' v v_i2) ∧
 (!gtagenv vs vs_i2.
  vs_to_i2 gtagenv vs vs_i2
  ⇒
   !gtagenv'. gtagenv_weak gtagenv gtagenv'
    ⇒
    vs_to_i2 gtagenv' vs vs_i2) ∧
 (!gtagenv env env_i2.
  env_to_i2 gtagenv env env_i2
  ⇒
   !gtagenv'. gtagenv_weak gtagenv gtagenv'
    ⇒
    env_to_i2 gtagenv' env env_i2)`,
 ho_match_mp_tac v_to_i2_ind >>
 rw [v_to_i2_eqns] >>
 res_tac
 >- metis_tac [gtagenv_weak_def, FLOOKUP_SUBMAP]
 >- (
     rw [Once v_to_i2_cases] >>
     fs [cenv_inv_def, gtagenv_wf_def, envC_tagged_def] >>
     imp_res_tac exhaustive_env_weak >>
     MAP_EVERY qexists_tac [`exh'`, `tagenv`] >>
     fs [gtagenv_weak_def, cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >> 
     rw []
     >- (res_tac >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (fs [has_exns_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (fs [has_bools_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (fs [has_lists_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- metis_tac []
     >- metis_tac [])
 >- (fs [cenv_inv_def, gtagenv_wf_def, envC_tagged_def] >>
     imp_res_tac exhaustive_env_weak >>
     rw [Once v_to_i2_cases] >>
     MAP_EVERY qexists_tac [`exh'`, `tagenv`] >>
     fs [gtagenv_weak_def, cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >> 
     rw []
     >- (res_tac >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (fs [has_exns_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (fs [has_bools_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (fs [has_lists_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- metis_tac []
     >- metis_tac []));

val (result_to_i2_rules, result_to_i2_ind, result_to_i2_cases) = Hol_reln `
(∀gtagenv v v'.
  f gtagenv v v'
  ⇒
  result_to_i2 f gtagenv (Rval v) (Rval v')) ∧
(∀gtagenv v v'.
  v_to_i2 gtagenv v v'
  ⇒
  result_to_i2 f gtagenv (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
(!gtagenv.
  result_to_i2 f gtagenv (Rerr Rtimeout_error) (Rerr Rtimeout_error)) ∧
(!gtagenv.
  result_to_i2 f gtagenv (Rerr Rtype_error) (Rerr Rtype_error))`;

val result_to_i2_eqns = Q.prove (
`(!gtagenv v r.
  result_to_i2 f gtagenv (Rval v) r ⇔
    ?v'. f gtagenv v v' ∧ r = Rval v') ∧
 (!gtagenv v r.
  result_to_i2 f gtagenv (Rerr (Rraise v)) r ⇔
    ?v'. v_to_i2 gtagenv v v' ∧ r = Rerr (Rraise v')) ∧
 (!gtagenv v r.
  result_to_i2 f gtagenv (Rerr Rtimeout_error) r ⇔
    r = Rerr Rtimeout_error) ∧
 (!gtagenv v r.
  result_to_i2 f gtagenv (Rerr Rtype_error) r ⇔
    r = Rerr Rtype_error)`,
rw [result_to_i2_cases] >>
metis_tac []);

val (sv_to_i2_rules, sv_to_i2_ind, sv_to_i2_cases) = Hol_reln `
(!genv v v'.
  v_to_i2 genv v v'
  ⇒
  sv_to_i2 genv (Refv v) (Refv v')) ∧
(!genv w.
  sv_to_i2 genv (W8array w) (W8array w)) ∧
(!genv vs vs'.
  vs_to_i2 genv vs vs'
  ⇒
  sv_to_i2 genv (Varray vs) (Varray vs'))`;

val sv_to_i2_weakening = Q.prove (
`(!gtagenv sv sv_i2 gtagenv'.
  sv_to_i2 gtagenv sv sv_i2 ∧
  gtagenv_weak gtagenv gtagenv'
  ⇒
  sv_to_i2 gtagenv' sv sv_i2)`,
 rw [sv_to_i2_cases] >>
 metis_tac [v_to_i2_weakening]);

val (s_to_i2_rules, s_to_i2_ind, s_to_i2_cases) = Hol_reln `
(!gtagenv c s s'.
  LIST_REL (sv_to_i2 gtagenv) s s'
  ⇒
  s_to_i2 gtagenv (c,s) (c,s'))`;

val length_vs_to_i2 = Q.prove (
`!vs gtagenv vs'.
  vs_to_i2 gtagenv vs vs'
  ⇒
  LENGTH vs = LENGTH vs'`,
 induct_on `vs` >>
 rw [v_to_i2_eqns] >>
 rw [] >>
 metis_tac []);

val length_evaluate_list_i2 = Q.prove (
`!b env s gtagenv es s' vs.
  evaluate_list_i2 b env s (exps_to_i2 gtagenv es) (s', Rval vs)
  ⇒
  LENGTH es = LENGTH vs`,
 induct_on `es` >>
 rw [exp_to_i2_def] >>
 cases_on `vs` >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_i2_cases]) >>
 rw [] >>
 metis_tac []);

val env_to_i2_el = Q.prove (
`!gtagenv env env_i2.
  env_to_i2 gtagenv env env_i2 ⇔
  LENGTH env = LENGTH env_i2 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i2)) ∧ v_to_i2 gtagenv (SND (EL n env)) (SND (EL n env_i2))`,
 induct_on `env` >>
 rw [v_to_i2_eqns]
 >- (cases_on `env_i2` >>
     fs []) >>
 PairCases_on `h` >>
 rw [v_to_i2_eqns] >>
 eq_tac >>
 rw [] >>
 rw []
 >- (cases_on `n` >>
     fs [])
 >- (cases_on `n` >>
     fs [])
 >- (cases_on `env_i2` >>
     fs [] >>
     FIRST_ASSUM (qspecl_then [`0`] mp_tac) >>
     SIMP_TAC (srw_ss()) [] >>
     rw [] >>
     qexists_tac `SND h` >>
     rw [] >>
     FIRST_X_ASSUM (qspecl_then [`SUC n`] mp_tac) >>
     rw []));

val vs_to_i2_lupdate = Q.prove (
`!gtagenv v n s v_i2 n s_i2.
  vs_to_i2 gtagenv s s_i2 ∧
  v_to_i2 gtagenv v v_i2
  ⇒
  vs_to_i2 gtagenv (LUPDATE v n s) (LUPDATE v_i2 n s_i2)`,
 induct_on `n` >>
 rw [v_to_i2_eqns, LUPDATE_def] >>
 cases_on `s` >>
 fs [v_to_i2_eqns, LUPDATE_def]);

val match_result_to_i2_def = Define
`(match_result_to_i2 gtagenv (Match env) (Match env_i2) ⇔
   env_to_i2 gtagenv env env_i2) ∧
 (match_result_to_i2 gtagenv No_match No_match = T) ∧
 (match_result_to_i2 gtagenv Match_type_error Match_type_error = T) ∧
 (match_result_to_i2 gtagenv _ _ = F)`;

val store_lookup_vs_to_i2_2 = Q.prove (
`!gtagenv vs vs_i2 v v_i2 n.
  vs_to_i2 gtagenv vs vs_i2 ∧
  store_lookup n vs = SOME v
  ⇒
  ?v'. store_lookup n vs_i2 = SOME v'`,
 induct_on `vs` >>
 rw [v_to_i2_eqns] >>
 fs [store_lookup_def] >>
 cases_on `n` >>
 fs [] >>
 metis_tac []);

val pat_bindings_i2_accum = Q.store_thm ("pat_bindings_i2_accum",
`(!p acc. pat_bindings_i2 p acc = pat_bindings_i2 p [] ++ acc) ∧
 (!ps acc. pats_bindings_i2 ps acc = pats_bindings_i2 ps [] ++ acc)`,
 Induct >>
 rw []
 >- rw [pat_bindings_i2_def]
 >- rw [pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]
 >- rw [pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]);

val pat_bindings_to_i2 = Q.prove (
`!tagenv p x. pat_bindings_i2 (pat_to_i2 tagenv p) x = pat_bindings p x`,
 ho_match_mp_tac pat_to_i2_ind >>
 rw [pat_bindings_def, pat_bindings_i2_def, pat_to_i2_def] >>
 induct_on `ps` >>
 rw [] >>
 fs [pat_bindings_def, pat_bindings_i2_def, pat_to_i2_def] >>
 metis_tac [APPEND_11, pat_bindings_accum, pat_bindings_i2_accum]);

val pmatch_to_i2_correct = Q.prove (
`(!envC s p v env r env_i2 s_i2 v_i2 tagenv gtagenv exh.
  r ≠ Match_type_error ∧
  cenv_inv envC exh tagenv gtagenv ∧
  pmatch_i1 envC s p v env = r ∧
  LIST_REL (sv_to_i2 gtagenv) s s_i2 ∧
  v_to_i2 gtagenv v v_i2 ∧
  env_to_i2 gtagenv env env_i2
  ⇒
  ?r_i2.
    pmatch_i2 exh s_i2 (pat_to_i2 tagenv p) v_i2 env_i2 = r_i2 ∧
    match_result_to_i2 gtagenv r r_i2) ∧
 (!envC s ps vs env r env_i2 s_i2 vs_i2 tagenv gtagenv exh.
  r ≠ Match_type_error ∧
  cenv_inv envC exh tagenv gtagenv ∧
  pmatch_list_i1 envC s ps vs env = r ∧
  LIST_REL (sv_to_i2 gtagenv) s s_i2 ∧
  vs_to_i2 gtagenv vs vs_i2 ∧
  env_to_i2 gtagenv env env_i2
  ⇒
  ?r_i2.
    pmatch_list_i2 exh s_i2 (MAP (pat_to_i2 tagenv) ps) vs_i2 env_i2 = r_i2 ∧
    match_result_to_i2 gtagenv r r_i2)`,
 ho_match_mp_tac pmatch_i1_ind >>
 rw [pmatch_i1_def, pmatch_i2_def, pat_to_i2_def, match_result_to_i2_def] >>
 fs [match_result_to_i2_def, v_to_i2_eqns] >>
 rw [pmatch_i2_def, match_result_to_i2_def]
 >- (
   every_case_tac >> fs []
     >- (`lookup_tag_env (SOME n) tagenv = SOME (tag, t')`
                  by (qpat_assum`∀x. Y`kall_tac >>
                      fs[cenv_inv_def,envC_tagged_def] >>
                      first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
                      metis_tac [length_vs_to_i2, SOME_11, same_ctor_and_same_tid, PAIR_EQ]) >>
         rw [pmatch_i2_def] >>
         `(?tid. t' = TypeId tid) ∨ (?exid. t' = TypeExn exid)`
                    by (Cases_on `t'` >>
                        metis_tac []) >>
         rw [pmatch_i2_def]
         >- (
             fs[GSYM AND_IMP_INTRO] >>
             first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
             rpt(disch_then(fn th => first_assum(mp_tac o MATCH_MP th))) >>
             strip_tac >> (simp_tac(srw_ss()++boolSimps.ETA_ss)[]) >>
             fs[cenv_inv_def,exhaustive_env_correct_def,PULL_EXISTS] >> simp[] >>
             qmatch_assum_rename_tac`FLOOKUP gtagenv (cn,TypeId tid) = _` >>
             first_x_assum(qspecl_then[`tid`,`cn`]mp_tac) >>
             discharge_hyps >- fs[FLOOKUP_DEF] >> rw[] >>
             first_x_assum(qspec_then`cn`mp_tac) >> simp[] >>
             strip_tac >> simp[] >>
             imp_res_tac length_vs_to_i2 >> fs[] >> rw[] >>
             fs[envC_tagged_def] >>
             first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
             fs[same_ctor_def] >> rw[] >> fs[])
         >- metis_tac [tid_or_exn_11, SOME_11, PAIR_EQ]
         >- (
           imp_res_tac same_ctor_and_same_tid >>
           fs[cenv_inv_def,envC_tagged_def] >>
           res_tac >> rw[] >> fs[] >>
           imp_res_tac length_vs_to_i2 >>
           metis_tac[] ))
     >- (fs [cenv_inv_def, envC_tagged_def] >>
         res_tac >>
         simp_tac(srw_ss()++boolSimps.ETA_ss)[] >>
         rw [] >>
         `(?tid. t' = TypeId tid) ∨ (?exid. t' = TypeExn exid)`
                    by (Cases_on `t'` >>
                        metis_tac []) >>
         `(?tid. r = TypeId tid) ∨ (?exid. r = TypeExn exid)`
                    by (Cases_on `r` >>
                        metis_tac []) >>
         imp_res_tac same_tid_diff_ctor >>
         rw [] >>
         simp [pmatch_i2_def] >>
         rw[match_result_to_i2_def] >>
         TRY(fs[same_tid_def]>>NO_TAC)
         >- (
           fs[exhaustive_env_correct_def,PULL_EXISTS] >>
           first_x_assum(qspecl_then[`tid`,`id_to_n n`]mp_tac) >>
           discharge_hyps >- fs[FLOOKUP_DEF] >> strip_tac >> simp[] >>
           first_x_assum(qspec_then`id_to_n n`mp_tac) >> simp[] >> strip_tac >>
           imp_res_tac length_vs_to_i2 >> fs[] >>
           rw[match_result_to_i2_def] >>
           fs[gtagenv_wf_def] >>
           metis_tac[] )
         >- (
           imp_res_tac length_vs_to_i2 >>
           metis_tac[gtagenv_wf_def] )
         >- metis_tac [tid_or_exn_11, gtagenv_wf_def, length_vs_to_i2]))
 >- (PairCases_on `tagenv` >>
     fs [pmatch_i2_def, lookup_tag_env_def] >>
     rw [] >>
     metis_tac [length_vs_to_i2])
 >- (every_case_tac >>
     fs [store_lookup_def] >>
     imp_res_tac LIST_REL_LENGTH >>
     fs [LIST_REL_EL_EQN] >>
     fs [sv_to_i2_cases] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [] >>
     metis_tac [])
 >- (every_case_tac >>
     fs [match_result_to_i2_def] >>
     rw [] >>
     pop_assum mp_tac >>
     pop_assum mp_tac >>
     res_tac >>
     rw [] >>
     CCONTR_TAC >>
     fs [match_result_to_i2_def] >>
     metis_tac [match_result_to_i2_def, match_result_distinct]));

val (env_all_to_i2_rules, env_all_to_i2_ind, env_all_to_i2_cases) = Hol_reln `
(!genv envC gtagenv exh env env_i2 genv_i2.
  cenv_inv envC exh tagenv gtagenv ∧
  LIST_REL (OPTION_REL (v_to_i2 gtagenv)) genv genv_i2 ∧
  env_to_i2 gtagenv env env_i2
  ⇒
  env_all_to_i2 tagenv (genv,envC,env) (exh,genv_i2,env_i2) gtagenv)`;

val env_to_i2_append = Q.prove (
`!gtagenv env1 env2 env1' env2'.
  env_to_i2 gtagenv env1 env1' ∧
  env_to_i2 gtagenv env2 env2'
  ⇒
  env_to_i2 gtagenv (env1++env2) (env1'++env2')`,
 induct_on `env1` >>
 rw [v_to_i2_eqns] >>
 PairCases_on `h` >>
 fs [v_to_i2_eqns]);

val env_to_i2_lookup = Q.prove (
`!gtagenv env x v env'.
  ALOOKUP env x = SOME v ∧
  env_to_i2 gtagenv env env'
  ⇒
  ?v'.
    v_to_i2 gtagenv v v' ∧
    ALOOKUP env' x = SOME v'`,
 induct_on `env` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 cases_on `h0 = x` >>
 fs [] >>
 rw [] >>
 fs [v_to_i2_eqns]);

val genv_to_i2_lookup = Q.prove (
`!gtagenv genv n genv'.
  LIST_REL (OPTION_REL (v_to_i2 gtagenv)) genv genv' ∧
  LENGTH genv > n
  ⇒
  !v.  
  EL n genv = SOME v
  ⇒
  ?v'. EL n genv' = SOME v' ∧ 
  v_to_i2 gtagenv v v'`,
 induct_on `genv` >>
 srw_tac [ARITH_ss] [] >>
 cases_on `n` >>
 srw_tac [ARITH_ss] [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 fs [OPTREL_def]);

val vs_to_i2_append1 = Q.prove (
`!gtagenv vs v vs' v'.
  vs_to_i2 gtagenv (vs++[v]) (vs'++[v'])
  ⇔
  vs_to_i2 gtagenv vs vs' ∧
  v_to_i2 gtagenv v v'`,
 induct_on `vs` >>
 rw [] >>
 cases_on `vs'` >>
 rw [v_to_i2_eqns]
 >- (cases_on `vs` >>
     rw [v_to_i2_eqns]) >>
 metis_tac []);

val vs_to_i2_append = Q.prove (
`!gtagenv vs1 vs1' vs2 vs2'.
  (LENGTH vs2 = LENGTH vs2' ∨ LENGTH vs1 = LENGTH vs1')
  ⇒
  (vs_to_i2 gtagenv (vs1++vs2) (vs1'++vs2') ⇔
   vs_to_i2 gtagenv vs1 vs1' ∧ vs_to_i2 gtagenv vs2 vs2')`,
 induct_on `vs1` >>
 rw [v_to_i2_eqns] >>
 eq_tac >>
 rw [] >>
 imp_res_tac length_vs_to_i2 >>
 fs [] >>
 cases_on `vs1'` >>
 fs [] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 metis_tac []);

val do_eq_i2 = Q.prove (
`(!v1 v2 r v1_i2 v2_i2 gtagenv.
  gtagenv_wf gtagenv ∧
  do_eq_i1 v1 v2 = r ∧
  v_to_i2 gtagenv v1 v1_i2 ∧
  v_to_i2 gtagenv v2 v2_i2
  ⇒
  do_eq_i2 v1_i2 v2_i2 = r) ∧
 (!vs1 vs2 r vs1_i2 vs2_i2 gtagenv.
  gtagenv_wf gtagenv ∧
  do_eq_list_i1 vs1 vs2 = r ∧
  vs_to_i2 gtagenv vs1 vs1_i2 ∧
  vs_to_i2 gtagenv vs2 vs2_i2
  ⇒
  do_eq_list_i2 vs1_i2 vs2_i2 = r)`,
 ho_match_mp_tac do_eq_i1_ind >>
 rw [do_eq_i2_def, do_eq_i1_def, v_to_i2_eqns] >>
 rw [] >>
 rw [do_eq_i2_def, do_eq_i1_def, v_to_i2_eqns] >>
 imp_res_tac length_vs_to_i2 >>
 fs [env_all_to_i2_cases] >>
 rw []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac [same_tid_refl, gtagenv_wf_def, SOME_11, PAIR_EQ, pair_CASES]
 >- metis_tac [cenv_inv_def, gtagenv_wf_def, SOME_11, PAIR_EQ, pair_CASES]
 >> TRY (
   BasicProvers.CASE_TAC >>
   res_tac >> every_case_tac >> fs [] >> metis_tac []) >>
 fs [Once v_to_i2_cases] >>
 rw [do_eq_i2_def])

val v_to_list_i2_correct = Q.prove (
`!v1 v2 vs1.
  gtagenv_wf gtagenv ∧
  v_to_i2 gtagenv v1 v2 ∧
  v_to_list_i1 v1 = SOME vs1
  ⇒
  ?vs2.
    v_to_list_i2 v2 = SOME vs2 ∧
    vs_to_i2 gtagenv vs1 vs2`,
 ho_match_mp_tac v_to_list_i1_ind >>
 rw [v_to_list_i1_def] >>
 every_case_tac >>
 fs [v_to_i2_eqns, v_to_list_i2_def] >>
 rw [] >>
 every_case_tac >>
 fs [v_to_i2_eqns, v_to_list_i2_def] >>
 rw [] >>
 res_tac >>
 fs [gtagenv_wf_def, has_lists_def] >>
 res_tac >>
 fs [] >>
 metis_tac [NOT_SOME_NONE, SOME_11]);

val char_list_to_v_i2_correct = prove(
  ``gtagenv_wf gtagenv ⇒
    ∀ls. v_to_i2 gtagenv (char_list_to_v_i1 ls) (char_list_to_v_i2 ls)``,
  strip_tac >>
  Induct >> simp[char_list_to_v_i1_def,char_list_to_v_i2_def,v_to_i2_eqns] >>
  fs[gtagenv_wf_def,has_lists_def])

val v_i2_to_char_list_correct = Q.prove (
`!v1 v2 vs1.
  gtagenv_wf gtagenv ∧
  v_to_i2 gtagenv v1 v2 ∧
  v_i1_to_char_list v1 = SOME vs1
  ⇒
    v_i2_to_char_list v2 = SOME vs1`,
 ho_match_mp_tac v_i1_to_char_list_ind >>
 rw [v_i1_to_char_list_def] >>
 every_case_tac >>
 fs [v_to_i2_eqns, v_i2_to_char_list_def] >>
 rw [] >>
 every_case_tac >>
 fs [v_to_i2_eqns, v_i2_to_char_list_def] >>
 rw [] >>
 res_tac >>
 fs [gtagenv_wf_def, has_lists_def])

val v_to_i2_Boolv_i2 = store_thm("v_to_i2_Boolv_i2",
  ``gtagenv_wf gtagenv ⇒
    v_to_i2 gtagenv (Boolv_i1 b) (Boolv_i2 b) ∧
    (∀v. v_to_i2 gtagenv (Boolv_i1 b) v ⇔ (v = Boolv_i2 b)) ∧
    (∀v. v_to_i2 gtagenv v (Boolv_i2 b) ⇔ (v = Boolv_i1 b))``,
  rw[Once v_to_i2_cases,Boolv_i1_def,Boolv_i2_def,
     vs_to_i2_list_rel,gtagenv_wf_def,has_bools_def] >>
  rw[Once v_to_i2_cases] >>
  rw[Once v_to_i2_cases] >>
  metis_tac[same_tid_refl])

val tac =
  fs [do_app_i1_def] >>
  every_case_tac >>
  fs [vs_to_i2_list_rel] >>
  rw [do_app_i2_def] >>
  fs [LET_THM,store_lookup_def, store_alloc_def, store_assign_def, v_to_i2_eqns, result_to_i2_cases, prim_exn_i1_def, prim_exn_i2_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  rw [] >>
  fs [] >>
  fs [] >>
  fs[LIST_REL_EL_EQN,sv_to_i2_cases] >>
  res_tac >>
  fs [store_v_same_type_def] >>
  rw [EL_LUPDATE, v_to_i2_eqns] >>
  rw [] >>
  fs [v_to_i2_eqns] >>
  rw [v_to_i2_eqns] >>
  fs [v_to_i2_Boolv_i2] >>
  TRY (fs [gtagenv_wf_def, has_exns_def] >> NO_TAC);

val do_app_i2_correct = Q.prove (
`!gtagenv s1 s2 op vs r s1_i2 vs_i2.
  do_app_i1 s1 op vs = SOME (s2, r) ∧
  LIST_REL (sv_to_i2 gtagenv) s1 s1_i2 ∧
  vs_to_i2 gtagenv vs vs_i2 ∧
  gtagenv_wf gtagenv
  ⇒
   ∃r_i2 s2_i2.
     LIST_REL (sv_to_i2 gtagenv) s2 s2_i2 ∧
     result_to_i2 v_to_i2 gtagenv r r_i2 ∧
     do_app_i2 s1_i2 (Op_i2 op) vs_i2 = SOME (s2_i2, r_i2)`,
 cases_on `op` >>
 rw []
 >- tac
 >- tac
 >- (fs [do_app_i1_def] >>
     cases_on `vs` >>
     fs [] >>
     cases_on `t` >>
     fs [] >>
     cases_on `t'` >>
     fs [vs_to_i2_list_rel] >>
     rw []
     >- (every_case_tac >>
         imp_res_tac do_eq_i2 >>
         rw [do_app_i2_def, result_to_i2_cases, v_to_i2_eqns, prim_exn_i1_def, prim_exn_i2_def] >>
         rw [] >> fs[v_to_i2_Boolv_i2] >>
         fs [gtagenv_wf_def, has_exns_def])
     >- (every_case_tac >>
         fs []))
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- (tac >>
     pop_assum mp_tac >>
     rw [])
 >- tac
 >- (tac >>
     pop_assum mp_tac >>
     rw [EL_LUPDATE] >>
     fs [LENGTH_LUPDATE] >>
     pop_assum mp_tac >>
     pop_assum mp_tac >>
     rw [])
 >- tac
 >- tac
 >- tac
 >- (
   tac >>
   simp[char_list_to_v_i2_correct] )
 >- (
   fs[do_app_i1_def]>>
   Cases_on`vs`>>fs[]>>
   Cases_on`t`>>fs[]>>
   TRY (cases_on `t'`) >>
   fs [vs_to_i2_list_rel] >> rw [] >- (
     every_case_tac >>
     imp_res_tac v_i2_to_char_list_correct >>
     fs[] >> rw[do_app_i2_def,result_to_i2_cases,v_to_i2_eqns]) >>
   every_case_tac >> fs[])
 >- tac
 >- (fs [do_app_i1_def] >>
     cases_on `vs` >>
     fs [] >>
     cases_on `t` >>
     fs [] >>
     TRY (cases_on `t'`) >>
     fs [vs_to_i2_list_rel] >>
     rw []
     >- (every_case_tac >>
         imp_res_tac v_to_list_i2_correct >>
         rw [do_app_i2_def, result_to_i2_cases, v_to_i2_eqns, prim_exn_i1_def, prim_exn_i2_def] >>
         rw [])
     >- (every_case_tac >>
         fs []))
 >- (tac >>
     fs [vs_to_i2_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     fs [] >>
     rw [v_to_i2_eqns] >>
     rpt (pop_assum mp_tac) >>
     rw []
     >- fs [gtagenv_wf_def, has_exns_def] >>
     fs [LIST_REL_EL_EQN] >>
     FIRST_X_ASSUM match_mp_tac >>
     decide_tac)
 >- (tac >>
     fs [vs_to_i2_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     fs [])
 >- (tac >>
     fs [vs_to_i2_list_rel, LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE] >>
     rw [v_to_i2_eqns, vs_to_i2_list_rel, LIST_REL_EL_EQN])
 >- (tac >>
     fs [vs_to_i2_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     fs [] >>
     rw [v_to_i2_eqns] >>
     rpt (pop_assum mp_tac) >>
     rw []
     >- fs [gtagenv_wf_def, has_exns_def] >>
     fs [LIST_REL_EL_EQN] >>
     FIRST_X_ASSUM match_mp_tac >>
     decide_tac)
 >- (tac >>
     fs [vs_to_i2_list_rel, LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE] >>
     rw [v_to_i2_eqns, vs_to_i2_list_rel, LIST_REL_EL_EQN])
 >- (tac >>
     fs [vs_to_i2_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     fs [] >>
     rw [v_to_i2_eqns] >>
     rpt (pop_assum mp_tac) >>
     rw []
     >- fs [gtagenv_wf_def, has_exns_def] >>
     fs [LIST_REL_EL_EQN] >>
     rw [EL_LUPDATE] >>
     full_case_tac >>
     metis_tac []));

val do_opapp_i2 = Q.prove (
`!gtagenv vs vs_i2 env e genv env' tagenv envC env_i2.
  do_opapp_i1 genv vs = SOME (env', e) ∧
  env_all_to_i2 tagenv (genv,envC,env) env_i2 gtagenv ∧
  vs_to_i2 gtagenv vs vs_i2
  ⇒
   ∃tagenv env_i2'.
     env_all_to_i2 tagenv env' (FST env_i2, FST (SND env_i2), env_i2') gtagenv ∧
     do_opapp_i2 vs_i2 = SOME (env_i2', exp_to_i2 tagenv e)`,
 rw [do_opapp_i1_def] >>
 every_case_tac >>
 fs [do_opapp_i2_def, vs_to_i2_list_rel] >>
 rw []
 >- (qpat_assum `v_to_i2 a0 (Closure_i1 b0 c0 d0) e0` (mp_tac o SIMP_RULE (srw_ss()) [Once v_to_i2_cases]) >>
     rw [] >>
     rw [] >>
     qexists_tac `tagenv'` >>
     rw [] >>
     fs [env_all_to_i2_cases] >>
     rw [v_to_i2_eqns, all_env_i1_to_genv_def, all_env_i2_to_genv_def, get_tagenv_def] >>
     fs [cenv_inv_def])
 >- (qpat_assum `v_to_i2 a0 (Recclosure_i1 b0 c0 d0) e0` (mp_tac o SIMP_RULE (srw_ss()) [Once v_to_i2_cases]) >>
     rw [] >>
     rw [] >>
     every_case_tac >>
     fs []
     >- (fs [find_recfun_lookup] >>
         induct_on `l` >>
         rw [] >>
         PairCases_on `h'` >>
         fs [exp_to_i2_def] >>
         every_case_tac >>
         fs [])
     >- (qexists_tac `tagenv'` >>
         rw [] >>
         fs [env_all_to_i2_cases] >>
         rw [v_to_i2_eqns, all_env_i1_to_genv_def, all_env_i2_to_genv_def,
             build_rec_env_i1_merge, build_rec_env_i2_merge] >>
         fs [funs_to_i2_map]
         >- fs [cenv_inv_def]
         >- (match_mp_tac env_to_i2_append >>
             rw [funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, env_to_i2_el, EL_MAP] >>
             `?f x e. EL n l = (f,x,e)` by metis_tac [pair_CASES] >>
             rw [] >>
             rw [Once v_to_i2_cases] >>
             metis_tac [funs_to_i2_map])
         >- (fs [find_recfun_lookup] >>
             induct_on `l` >>
             rw [] >>
             PairCases_on `h'` >>
             fs [exp_to_i2_def] >>
             every_case_tac >>
             fs [])
         >- (CCONTR_TAC >> fs[funs_to_i2_map] >>
             fs[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,FST_triple])
         >- (fs [find_recfun_lookup] >>
             induct_on `l` >>
             rw [] >>
             PairCases_on `h'` >>
             fs [exp_to_i2_def] >>
             every_case_tac >>
             fs [get_tagenv_def] >>
             rw []))));

val lookup_tag_env_NONE = Q.prove (
`lookup_tag_env NONE tagenv = NONE`,
PairCases_on `tagenv` >>
rw [lookup_tag_env_def]);

val exps_to_i2_map = Q.prove (
`!tagenv es.
  exps_to_i2 tagenv es = MAP (exp_to_i2 tagenv) es`,
 Induct_on `es` >>
 rw [exp_to_i2_def]);

val Boolv_i2_11 = store_thm("Boolv_i2_11[simp]",
  ``Boolv_i2 b1 = Boolv_i2 b2 ⇔ (b1 = b2)``,
  EVAL_TAC >> rw[])

val Boolv_i1_11 = store_thm("Boolv_i1_11[simp]",
  ``Boolv_i1 b1 = Boolv_i1 b2 ⇔ (b1 = b2)``,
  EVAL_TAC >> rw[])

val exp_to_i2_correct = Q.prove (
`(∀b env s e res.
   evaluate_i1 b env s e res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !tagenv s' r env_i2 s_i2 e_i2 gtagenv.
     (res = (s',r)) ∧
     env_all_to_i2 tagenv env env_i2 gtagenv ∧
     s_to_i2 gtagenv s s_i2 ∧
     e_i2 = exp_to_i2 tagenv e
     ⇒
     ∃s'_i2 r_i2.
       result_to_i2 v_to_i2 gtagenv r r_i2 ∧
       s_to_i2 gtagenv s' s'_i2 ∧
       evaluate_i2 b env_i2 s_i2 e_i2 (s'_i2, r_i2)) ∧
 (∀b env s es res.
   evaluate_list_i1 b env s es res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !tagenv s' r env_i2 s_i2 es_i2 gtagenv.
     (res = (s',r)) ∧
     env_all_to_i2 tagenv env env_i2 gtagenv ∧
     s_to_i2 gtagenv s s_i2 ∧
     (es_i2 = exps_to_i2 tagenv es)
     ⇒
     ?s'_i2 r_i2.
       result_to_i2 vs_to_i2 gtagenv r r_i2 ∧
       s_to_i2 gtagenv s' s'_i2 ∧
       evaluate_list_i2 b env_i2 s_i2 es_i2 (s'_i2, r_i2)) ∧
 (∀b env s v pes err_v res.
   evaluate_match_i1 b env s v pes err_v res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !tagenv s' r env_i2 s_i2 v_i2 pes_i2 err_v_i2 gtagenv.
     (res = (s',r)) ∧
     env_all_to_i2 tagenv env env_i2 gtagenv ∧
     s_to_i2 gtagenv s s_i2 ∧
     v_to_i2 gtagenv v v_i2 ∧
     pes_i2 = pat_exp_to_i2 tagenv pes ∧
     v_to_i2 gtagenv err_v err_v_i2
     ⇒
     ?s'_i2 r_i2.
       result_to_i2 v_to_i2 gtagenv r r_i2 ∧
       s_to_i2 gtagenv s' s'_i2 ∧
       evaluate_match_i2 b env_i2 s_i2 v_i2 pes_i2 err_v_i2 (s'_i2, r_i2))`,
 ho_match_mp_tac evaluate_i1_ind >>
 rw [] >>
 rw [Once evaluate_i2_cases,exp_to_i2_def] >>
 TRY (Cases_on `err`) >>
 fs [result_to_i2_eqns, v_to_i2_eqns]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (* Constructor application *)
    (res_tac >>
     rw [] >>
     fs [env_all_to_i2_cases, build_conv_i1_def] >>
     rw [] >>
     MAP_EVERY qexists_tac [`s'_i2`, `Rval (Conv_i2 (lookup_tag_env cn tagenv) (REVERSE v'))`] >>
     rw [] >>
     Cases_on `cn` >>
     fs [] >>
     rw [v_to_i2_eqns, lookup_tag_env_NONE] >>
     fs [all_env_i1_to_cenv_def] >>
     every_case_tac >>
     fs [get_tagenv_def] >>
     rw [v_to_i2_eqns] >>
     fs [cenv_inv_def, envC_tagged_def, gtagenv_wf_def, do_con_check_def] >>
     rw [] >>
     metis_tac [length_evaluate_list_i2, length_vs_to_i2, FST, exps_to_i2_map, MAP_REVERSE,
                vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE])
 >- (res_tac >>
     rw [] >>
     metis_tac [exps_to_i2_map, MAP_REVERSE, vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE])
 >- metis_tac [exps_to_i2_map, MAP_REVERSE, vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE]
 >- (* Local variable lookup *)
    (fs [env_all_to_i2_cases, all_env_i2_to_env_def] >>
     rw [] >>
     fs [all_env_i1_to_env_def] >>
     metis_tac [env_to_i2_lookup])
 >- (* Global variable lookup *)
    (fs [env_all_to_i2_cases, all_env_i2_to_genv_def] >>
     rw [] >>
     fs [all_env_i1_to_genv_def] >>
     `n < LENGTH genv` by decide_tac >>
     `LENGTH genv_i2 = LENGTH genv` by metis_tac [LIST_REL_LENGTH] >>
     fs [EL_MAP] >>
     metis_tac [genv_to_i2_lookup])
 >- (rw [Once v_to_i2_cases] >>
     fs [env_all_to_i2_cases] >>
     rw [all_env_i1_to_env_def, all_env_i2_to_env_def, all_env_i1_to_cenv_def] >>
     metis_tac [])
 >- (* Function application *)
    (pop_assum mp_tac >>
     rw [] >>
     res_tac >>
     rw [] >>
     `?genv envC env''. env = (genv,envC,env'')` by metis_tac [pair_CASES] >>
     fs [all_env_i1_to_genv_def] >>
     `?tagenv env_i2'.
       env_all_to_i2 tagenv env' (FST env_i2, FST (SND env_i2), env_i2') gtagenv ∧
       do_opapp_i2 (REVERSE v'') = SOME (env_i2', exp_to_i2 tagenv e)`
                 by metis_tac [do_opapp_i2, vs_to_i2_list_rel, EVERY2_REVERSE] >>
     full_simp_tac (srw_ss()++boolSimps.DNF_ss) [s_to_i2_cases] >>
     PairCases_on `s'` >>
     rw [] >>
     PairCases_on `env_i2` >>
     rw [] >>
     metis_tac [FST,SND, exps_to_i2_map, MAP_REVERSE, vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE])
 >- (* Function application *)
    (pop_assum mp_tac >>
     rw [] >>
     res_tac >>
     rw [] >>
     `?genv envC env''. env = (genv,envC,env'')` by metis_tac [pair_CASES] >>
     fs [all_env_i1_to_genv_def] >>
     `?tagenv env_i2'.
       env_all_to_i2 tagenv env' (FST env_i2, FST (SND env_i2), env_i2') gtagenv ∧
       do_opapp_i2 (REVERSE v'') = SOME (env_i2', exp_to_i2 tagenv e)`
                 by metis_tac [do_opapp_i2, vs_to_i2_list_rel, EVERY2_REVERSE] >>
     full_simp_tac (srw_ss()++boolSimps.DNF_ss) [s_to_i2_cases] >>
     PairCases_on `s'` >>
     rw [] >>
     PairCases_on `env_i2` >>
     rw [] >>
     metis_tac [FST,SND,exps_to_i2_map, MAP_REVERSE, vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE])
 >- (* Function application *)
    (res_tac >>
     rw [] >>
     `?genv envC env''. env = (genv,envC,env'')` by metis_tac [pair_CASES] >>
     fs [all_env_i1_to_genv_def] >>
     `?tagenv env_i2'.
       env_all_to_i2 tagenv env' (FST env_i2, FST (SND env_i2), env_i2') gtagenv ∧
       do_opapp_i2 (REVERSE v'') = SOME (env_i2', exp_to_i2 tagenv e)`
                 by metis_tac [do_opapp_i2, vs_to_i2_list_rel, EVERY2_REVERSE] >>
     full_simp_tac (srw_ss()++boolSimps.DNF_ss) [s_to_i2_cases] >>
     metis_tac [FST,SND, exps_to_i2_map, MAP_REVERSE, vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE])
 >- (* Primitive application *)
    (LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s_i2`, `gtagenv`] mp_tac) >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     `gtagenv_wf gtagenv` by fs [env_all_to_i2_cases, cenv_inv_def] >>
     imp_res_tac do_app_i2_correct >>
     rw [] >>
     PairCases_on `env_i2` >>
     fs [] >>
     metis_tac [FST,SND, exps_to_i2_map, MAP_REVERSE, vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE])
 >- (LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s_i2`, `gtagenv`] mp_tac) >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     `gtagenv_wf gtagenv` by fs [env_all_to_i2_cases, cenv_inv_def] >>
     imp_res_tac do_app_i2_correct >>
     rw [] >>
     PairCases_on `env_i2` >>
     fs [] >>
     metis_tac [FST,SND, exps_to_i2_map, MAP_REVERSE, vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE])
 >- metis_tac [exps_to_i2_map, MAP_REVERSE, vs_to_i2_list_rel, EVERY2_REVERSE, LENGTH_REVERSE]
 >- (* If *)
    (fs [do_if_i2_def, do_if_i1_def] >>
     every_case_tac >>
     rw [] >>
     res_tac >>
     rw [] >>
     res_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`s'_i2''`, `r_i2`] >>
     rw [] >>
     disj1_tac >> fs[] >>
     `gtagenv_wf gtagenv` by(
       fs[Once env_all_to_i2_cases] >>
       fs[cenv_inv_def] )
     >- (qexists_tac `(Boolv_i2 F)` >>
         fs [v_to_i2_Boolv_i2, v_to_i2_eqns, exp_to_i2_def] >>
         metis_tac [])
     >- (qexists_tac `(Boolv_i2 T)` >>
         fs [v_to_i2_Boolv_i2, v_to_i2_eqns, exp_to_i2_def] >>
         metis_tac []))
 >- metis_tac []
 >- metis_tac []
 >- (* Match *)
   (pop_assum mp_tac >>
     res_tac >>
     rw [] >>
     FIRST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s'_i2'`, `v''`,
                                  `Conv_i2 (SOME (bind_tag,(TypeExn (Short "Bind")))) []`, `gtagenv`] mp_tac) >>
     rw [] >>
     fs [env_all_to_i2_cases] >>
     rw [] >>
     fs [cenv_inv_def, envC_tagged_def, gtagenv_wf_def, has_exns_def] >>
     pop_assum (fn _ => all_tac) >>
     pop_assum mp_tac >>
     rw [] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (* Let *)
    (`?exh' genv' env'. env_i2 = (exh',genv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     `env_all_to_i2 tagenv (genv,cenv,opt_bind n v env) (exh',genv', opt_bind n v' env') gtagenv`
                by (fs [env_all_to_i2_cases] >>
                    fs [opt_bind_def, v_to_i2_eqns] >>
                    rw [] >>
                    every_case_tac >>
                    fs [] >>
                    rw [v_to_i2_eqns]) >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (* Letrec *)
    (pop_assum mp_tac >>
     rw [] >>
     `?exh' genv' env'. env_i2 = (exh',genv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     `env_all_to_i2 tagenv (genv,cenv,build_rec_env_i1 funs (cenv,env) env)
                           (exh',genv',build_rec_env_i2 (funs_to_i2 tagenv funs) env' env')
                           gtagenv`
         by (fs [env_all_to_i2_cases] >>
             rw [build_rec_env_i1_merge, build_rec_env_i2_merge] >>
             rw [] >>
             match_mp_tac env_to_i2_append >>
             rw [] >>
             rw [funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, env_to_i2_el, EL_MAP] >>
             `?f x e. EL n funs = (f,x,e)` by metis_tac [pair_CASES] >>
             rw [] >>
             rw [Once v_to_i2_cases] >>
             metis_tac [funs_to_i2_map]) >>
      res_tac >>
      MAP_EVERY qexists_tac [`s'_i2'`, `r_i2'`] >>
      rw [] >>
      disj1_tac >>
      rw [funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (pop_assum mp_tac >>
     rw [] >>
     fs [s_to_i2_cases, env_all_to_i2_cases] >>
     rw [] >>
     `match_result_to_i2 gtagenv (Match env')
            (pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2')`
                   by metis_tac [pmatch_to_i2_correct, match_result_distinct] >>
     cases_on `pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2'` >>
     fs [match_result_to_i2_def] >>
     rw [] >>
     fs [METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     FIRST_X_ASSUM (qspecl_then [`tagenv`, `gtagenv`, `exh`, `a`, `genv_i2`, `s''`] mp_tac) >>
     rw [] >>
     fs [] >>
     MAP_EVERY qexists_tac [`(c, s'''')`, `r_i2`] >>
     metis_tac [pat_bindings_to_i2])
 >- (pop_assum mp_tac >>
     rw [] >>
     fs [s_to_i2_cases, env_all_to_i2_cases] >>
     rw [] >>
     `match_result_to_i2 gtagenv No_match
            (pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2')`
                   by metis_tac [pmatch_to_i2_correct, match_result_distinct] >>
     cases_on `pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2'` >>
     fs [match_result_to_i2_def] >>
     rw [] >>
     fs [METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     pop_assum mp_tac >>
     pop_assum (qspecl_then [`tagenv`, `(count',s'')`, `v_i2`, `err_v_i2`, `gtagenv`, `exh`, `env_i2'`, `genv_i2`] mp_tac) >>
     rw [] >>
     metis_tac [pat_bindings_to_i2]));

val flat_envC_tagged_def = Define `
 flat_envC_tagged (envC:flat_envC) (tagenv:flat_tag_env) gtagenv ⇔
   ∀cn num_args t.
     ALOOKUP envC cn = SOME (num_args,t) ⇒
     ∃tag.
       lookup_tag_flat cn tagenv = SOME (tag,t) ∧
       FLOOKUP gtagenv (cn,t) = SOME (tag,num_args)`

val envC_tagged_flat_envC_tagged = Q.prove(
  `envC_tagged envC tagenv gtagenv ⇒
   flat_envC_tagged (SND envC) (SND tagenv) gtagenv`,
  rw[envC_tagged_def,flat_envC_tagged_def] >>
  first_x_assum(qspec_then`Short cn`mp_tac) >>
  Cases_on`envC`>>simp[lookup_alist_mod_env_def] >>
  Cases_on`tagenv`>>fs[lookup_tag_env_def,id_to_n_def])

val next_inv_def = Define`
  next_inv tids next (gtagenv:gtagenv) ⇔
    (∀cn t tag a.
       FLOOKUP gtagenv (cn,TypeExn t) = SOME (tag,a) ⇒
       ∃max. lookup a next = SOME max ∧ tag < max)
    ∧ IMAGE SND (FDOM gtagenv) ⊆ tids`

val alloc_tag_accumulates = Q.prove(
  `∀tn cn arity ta.
    ∃acc. SND (alloc_tag tn cn arity ta) = acc ⊌ SND ta ∧
         FDOM acc = {cn} ∧
         OPTION_MAP SND (FLOOKUP acc cn) = lookup_tag_env (SOME (Short cn)) (get_tagenv (alloc_tag tn cn arity ta))`,
  rpt gen_tac >>
  PairCases_on`ta` >>
  rw[alloc_tag_def] >>
  every_case_tac >> simp[] >>
  simp[Once FUPDATE_EQ_FUNION] >>
  (fn g => (g |> snd |> strip_exists |> snd |> dest_conj |> fst |> lhs |> REFL |> concl |> match_exists_tac) g) >>
  simp[lookup_tag_env_def,FLOOKUP_UPDATE,get_tagenv_def,insert_tag_env_def,lookup_tag_flat_def])

val lookup_tag_env_insert = Q.prove (
`(!cn tag tagenv. lookup_tag_env (SOME (Short cn)) (insert_tag_env cn tag tagenv) = SOME (SND tag)) ∧
 (!cn cn' tag tagenv.
   cn' ≠ Short cn
   ⇒
   lookup_tag_env (SOME cn') (insert_tag_env cn tag tagenv) = lookup_tag_env (SOME cn') tagenv)`,
 rw [] >>
 PairCases_on `tagenv` >>
 rw [lookup_tag_env_def, insert_tag_env_def, lookup_tag_flat_def, FLOOKUP_UPDATE] >>
 every_case_tac >>
 fs []);

val lookup_tag_env_Short_alloc_tag_notin = Q.prove(
  `b ≠ x ⇒
   lookup_tag_env (SOME (Short x)) (get_tagenv (alloc_tag a b c d)) =
   lookup_tag_env (SOME (Short x)) (get_tagenv d)`,
   PairCases_on`d`>>simp[alloc_tag_def] >>
   every_case_tac >> simp[get_tagenv_def,lookup_tag_env_insert])

val lookup_tag_env_Short_alloc_tags0_notin = Q.prove(
  `x ∉ set (MAP FST f) ⇒
   lookup_tag_env (SOME (Short x)) (get_tagenv
     (FOLDL (λa (b,c). alloc_tag e b (LENGTH c) a) d f)) =
   lookup_tag_env (SOME (Short x)) (get_tagenv (d:tagenv_state_acc))`,
  qid_spec_tac`d` >> Induct_on`f` >> simp[] >>
  Cases >> simp[lookup_tag_env_Short_alloc_tag_notin])

val lookup_tag_env_Short_alloc_tags_notin = Q.prove(
  `x ∉ set (MAP FST (FLAT (MAP (SND o SND) c))) ⇒
   lookup_tag_env (SOME (Short x)) (get_tagenv (alloc_tags a (b:tagenv_state_acc) c)) =
   lookup_tag_env (SOME (Short x)) (get_tagenv b)`,
  map_every qid_spec_tac[`a`,`b`,`c`] >>
  Induct >> simp[alloc_tags_def] >>
  qx_gen_tac`p`>>PairCases_on`p` >>
  simp[alloc_tags_def,lookup_tag_env_Short_alloc_tags0_notin])

val FOLDL_alloc_tag_accumulates = Q.prove(
  `∀ls (st:tagenv_state_acc).
    ∃acc. SND (FOLDL (λst' (cn,ts). alloc_tag (TypeId (mk_id mn tn)) cn (LENGTH ts) st') st ls) =
         acc ⊌ SND st ∧
         FDOM acc = set (MAP FST ls) ∧
         (∀cn. MEM cn (MAP FST ls) ⇒
           OPTION_MAP SND (FLOOKUP acc cn) =
           lookup_tag_env (SOME (Short cn))
             (get_tagenv (FOLDL (λst' (cn,ts). alloc_tag (TypeId (mk_id mn tn)) cn (LENGTH ts) st') st ls)))`,
  ho_match_mp_tac SNOC_INDUCT >>
  simp[FDOM_EQ_EMPTY] >> rw[] >>
  simp[FOLDL_SNOC,UNCURRY] >>
  specl_args_of_then``alloc_tag``alloc_tag_accumulates strip_assume_tac >>
  simp[] >>
  first_x_assum(qspec_then`st`strip_assume_tac) >> rw[] >>
  qexists_tac`acc ⊌ acc'` >>
  simp[MAP_SNOC,LIST_TO_SET_SNOC,FUNION_ASSOC,GSYM INSERT_SING_UNION] >>
  simp[FLOOKUP_FUNION] >>
  rw[] >> every_case_tac >> fs[] >>
  TRY(rfs[FLOOKUP_DEF]>>NO_TAC) >>
  TRY(
    `FST x ≠ cn` by (rfs[FLOOKUP_DEF]) >>
    simp[lookup_tag_env_Short_alloc_tag_notin] >>
    NO_TAC) >>
  rfs[FLOOKUP_DEF] >> fs[])

val MAP_FST_build_tdefs = store_thm("MAP_FST_build_tdefs",
  ``set (MAP FST (build_tdefs mn ls)) =
    set (MAP FST (FLAT (MAP (SND o SND) ls)))``,
  Induct_on`ls`>>simp[build_tdefs_cons] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[build_tdefs_cons,MAP_REVERSE] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  metis_tac[UNION_COMM])

val alloc_tags_accumulates = Q.prove(
  `∀ls mn ta.
    ∃acc. SND (alloc_tags (mn:modN option) (ta:tagenv_state_acc) (ls:type_def)) = acc ⊌ SND ta ∧
          FDOM acc = set (MAP FST (build_tdefs mn ls)) ∧
          (∀cn. MEM cn (MAP FST (build_tdefs mn ls)) ⇒
           OPTION_MAP SND (FLOOKUP acc cn) =
           lookup_tag_env (SOME (Short cn))
             (get_tagenv (alloc_tags mn ta ls)))`,
  Induct >> rw[alloc_tags_def] >- (
    simp[build_tdefs_def,FDOM_EQ_EMPTY] ) >>
  PairCases_on`h`>>simp[alloc_tags_def]>>
  simp[build_tdefs_cons] >>
  qho_match_abbrev_tac`∃acc. SND (alloc_tags mn ta' ls) = acc ⊌ SND ta ∧ X acc` >>
  qunabbrev_tac`X` >>
  Q.ISPECL_THEN[`h1`,`h2`,`ta`]strip_assume_tac (Q.GEN`tn`FOLDL_alloc_tag_accumulates) >>
  first_x_assum(qspecl_then[`mn`,`ta'`]mp_tac) >> rw[] >> rw[] >>
  rfs[] >>
  qexists_tac`acc' ⊌ acc` >>
  simp[FUNION_ASSOC,MAP_REVERSE,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  simp[FLOOKUP_FUNION] >>
  rw[] >> every_case_tac >> fs[] >>
  TRY(rfs[FLOOKUP_DEF]>>NO_TAC) >>
  TRY(
    match_mp_tac EQ_SYM >>
    match_mp_tac lookup_tag_env_Short_alloc_tags_notin >>
    rfs[FLOOKUP_DEF] >>
    fs[MAP_FST_build_tdefs] ) >>
  TRY (
    rfs[FLOOKUP_DEF] >> rw[] ) >>
  metis_tac[optionTheory.OPTION_MAP_DEF])

val tagacc_accumulates = Q.prove (
`!(tagenv_st:tagenv_state_acc) ds tagenv_st' ds_i2'.
  decs_to_i2 tagenv_st ds = (tagenv_st',ds_i2') ⇒
  ?acc'. SND tagenv_st' = FUNION acc' (SND tagenv_st)`,
 induct_on `ds` >>
 rw [decs_to_i2_def]
 >- metis_tac [FUNION_FEMPTY_1] >>
 every_case_tac >>
 rw [] >>
 fs [LET_THM] >>
 first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rw[] >>
 res_tac >> rw[]
 >> metis_tac[alloc_tag_accumulates,alloc_tags_accumulates,FUNION_ASSOC])

val exh_weak_def = Define`
  exh_weak (exh:exh_ctors_env) (exh':exh_ctors_env) ⇔
    ∀tid m. FLOOKUP exh tid = SOME m ⇒
      ∃m'. FLOOKUP exh' tid = SOME m' ∧
        ∀a x. lookup a m = SOME x ⇒
           ∃y. lookup a m' = SOME y ∧ x ≤ y`

val exh_weak_refl = store_thm("exh_weak_refl[simp]",
  ``exh_weak exh exh``,
  rw[exh_weak_def])

val exh_weak_trans = store_thm("exh_weak_trans",
  ``exh_weak exh1 exh2 ∧ exh_weak exh2 exh3 ⇒ exh_weak exh1 exh3``,
  rw[exh_weak_def] >>
  res_tac >> res_tac >> rw[] >> fs[] >> rw[] >>
  res_tac >> fs[] >> rw[] >> res_tac >> rw[] >> simp[])

val pmatch_i2_exh_weak = Q.prove (
`(!(exh:exh_ctors_env) s p v env res exh'.
  pmatch_i2 exh s p v env = res ∧
  res ≠ Match_type_error ∧
  exh_weak exh exh'
  ⇒
  pmatch_i2 exh' s p v env = res) ∧
 (!(exh:exh_ctors_env) s ps vs env res exh'.
  pmatch_list_i2 exh s ps vs env = res ∧
  res ≠ Match_type_error ∧
  exh_weak exh exh'
  ⇒
  pmatch_list_i2 exh' s ps vs env = res)`,
 ho_match_mp_tac pmatch_i2_ind >>
 rw [pmatch_i2_def, LET_THM] >>
 every_case_tac >>
 rw [] >>
 TRY (
   fs [exh_weak_def] >> res_tac >> fs[] >> rw[] >> res_tac >> fs[] >> rw[] >> DECIDE_TAC) >>
 metis_tac [exh_weak_def,NOT_SOME_NONE,match_result_distinct, match_result_11]);

val evaluate_exp_i2_exh_weak = Q.prove (
`(∀b tmp_env s e res.
   evaluate_i2 b tmp_env s e res ⇒
   !exh genv env exh'.
     SND res ≠ Rerr Rtype_error ∧
     tmp_env = ((exh:exh_ctors_env),genv,env) ∧
     exh_weak exh exh' ⇒
     evaluate_i2 b (exh',genv,env) s e res) ∧
 (∀b tmp_env s es res.
   evaluate_list_i2 b tmp_env s es res ⇒
   !exh genv env exh'.
     SND res ≠ Rerr Rtype_error ∧
     tmp_env = ((exh:exh_ctors_env),genv,env) ∧
     exh_weak exh exh' ⇒
     evaluate_list_i2 b (exh',genv,env) s es res) ∧
 (∀b tmp_env s v pes err_v res.
   evaluate_match_i2 b tmp_env s v pes err_v res ⇒
   !(exh:exh_ctors_env) genv env exh'.
     SND res ≠ Rerr Rtype_error ∧
     tmp_env = (exh,genv,env) ∧
     exh_weak exh exh' ⇒
     evaluate_match_i2 b (exh',genv,env) s v pes err_v res)`,
 ho_match_mp_tac evaluate_i2_ind >>
 rw [] >>
 rw [Once evaluate_i2_cases] >>
 fs [all_env_i2_to_env_def, all_env_i2_to_genv_def] >>
 metis_tac [pmatch_i2_exh_weak, match_result_distinct]);

val alloc_tag_exh_weak = store_thm("alloc_tag_exh_weak",
  ``exh_weak (get_exh (FST st)) (get_exh (FST (alloc_tag a b c st)))``,
  `∃next menv env exh acc. st = ((next,(menv,env),exh),acc)` by metis_tac[PAIR] >>
  simp[alloc_tag_def]>>
  every_case_tac >> simp[UNCURRY,get_exh_def,exh_weak_def] >> rw[] >>
  simp[FLOOKUP_UPDATE] >> rw[] >>
  rw[sptreeTheory.lookup_insert] >> fs[] >> rw[] >> fs[])

val alloc_tags_exh_weak = store_thm("alloc_tags_exh_weak",
  ``∀ls mn ta. exh_weak (get_exh (FST ta)) (get_exh (FST (alloc_tags mn ta ls)))``,
  Induct >> rw[alloc_tags_def] >>
  PairCases_on`h`>>simp[alloc_tags_def]>>
  qmatch_abbrev_tac`exh_weak X (get_exh (FST (alloc_tags mn ta' ls)))` >>
  qunabbrev_tac`X` >>
  first_x_assum(qspecl_then[`mn`,`ta'`]mp_tac) >>
  `exh_weak (get_exh (FST ta)) (get_exh (FST ta'))` suffices_by metis_tac[exh_weak_trans] >>
  rw[Abbr`ta'`] >>
  qid_spec_tac`ta` >>
  Induct_on`h2` >> rw[] >>
  fs[UNCURRY] >>
  qpat_abbrev_tac`ta' = alloc_tag X Y Z ta` >>
  first_x_assum(qspec_then`ta'`mp_tac) >> rw[] >>
  rw[Abbr`ta'`] >>
  metis_tac[alloc_tag_exh_weak,exh_weak_trans])

val decs_to_i2_exh_weak = store_thm("decs_to_i2_exh_weak",
  ``∀ds st.
      exh_weak (get_exh (FST st)) (get_exh (FST (FST (decs_to_i2 st ds))))``,
  Induct >> simp[decs_to_i2_def] >> rw[] >>
  every_case_tac >> simp[UNCURRY] >>
  metis_tac[exh_weak_trans,alloc_tag_exh_weak,alloc_tags_exh_weak])

val exh_wf_def = Define`
  exh_wf exh = ∀t. t ∈ FRANGE exh ⇒ wf t`

val alloc_tag_exh_wf = store_thm("alloc_tag_exh_wf",
  ``exh_wf (get_exh (FST st)) ⇒ exh_wf (get_exh (FST (alloc_tag a b c st)))``,
  `∃next menv env exh acc. st = ((next,(menv,env),exh),acc)` by metis_tac[PAIR] >>
  simp[alloc_tag_def]>>
  every_case_tac >> simp[UNCURRY,get_exh_def,exh_wf_def] >> rw[] >>
  fs[IN_FRANGE_FLOOKUP,PULL_EXISTS,DOMSUB_FLOOKUP_THM] >>
  res_tac >> fs[] >>
  match_mp_tac sptreeTheory.wf_insert >>
  simp[sptreeTheory.wf_def])

val alloc_tags_exh_wf = store_thm("alloc_tags_exh_wf",
  ``∀ls mn ta. exh_wf (get_exh (FST ta)) ⇒ exh_wf (get_exh (FST (alloc_tags mn ta ls)))``,
  Induct >> rw[alloc_tags_def] >>
  PairCases_on`h`>>simp[alloc_tags_def]>>
  qmatch_abbrev_tac`exh_wf (get_exh (FST (alloc_tags mn ta' ls)))` >>
  first_x_assum(qspecl_then[`mn`,`ta'`]match_mp_tac) >>
  rw[Abbr`ta'`] >>
  pop_assum mp_tac >>
  qid_spec_tac`ta` >>
  Induct_on`h2` >> rw[] >>
  fs[UNCURRY] >>
  qpat_abbrev_tac`ta' = alloc_tag X Y Z ta` >>
  first_x_assum(qspec_then`ta'`mp_tac) >> rw[] >>
  first_x_assum match_mp_tac >>
  rw[Abbr`ta'`] >>
  metis_tac[alloc_tag_exh_wf])

val decs_to_i2_exh_wf = store_thm("decs_to_i2_exh_wf",
  ``∀ds st.
      exh_wf (get_exh (FST st)) ⇒ exh_wf (get_exh (FST (FST (decs_to_i2 st ds))))``,
  Induct >> simp[decs_to_i2_def] >> rw[] >>
  every_case_tac >> simp[UNCURRY] >>
  metis_tac[alloc_tag_exh_wf,alloc_tags_exh_wf])

val exhaustive_env_correct_exh_weak = store_thm("exhaustive_env_correct_exh_weak",
  ``exhaustive_env_correct exh gtagenv ∧
    exh_weak exh exh' ∧ exh_wf exh' (* ∧ FDOM exh' ⊆ { t | TypeId t ∈ IMAGE SND (FDOM gtagenv) } *) ⇒
    exhaustive_env_correct exh' gtagenv``,
  rw[exhaustive_env_correct_def] >>
  fs[PULL_EXISTS,exh_weak_def,exh_wf_def] >>
  res_tac >> res_tac >> rw[] >>
  res_tac >> fs[] >> rw[] >>
  res_tac >> fs[] >> rw[] >> simp[])

val recfun_helper = Q.prove (
`cenv_inv envC exh tagenv gtagenv
 ⇒
 LIST_REL (OPTREL (v_to_i2 gtagenv))
          (MAP SOME (MAP (\(f:string,x,e). Closure_i1 (envC,[]) x e) l))
          (MAP SOME (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 tagenv e)) l))`,
 induct_on `l` >>
 rw [] >>
 PairCases_on `h` >>
 rw [] >>
 rw [OPTREL_def] >>
 rw [Once v_to_i2_cases, v_to_i2_eqns] >>
 metis_tac []);

val mk_id_11 = prove(
  ``mk_id a b = mk_id c d ⇔ (a = c) ∧ (b = d)``,
  map_every Cases_on[`a`,`c`] >> EVAL_TAC)

val next_weak_def = Define`
  next_weak next1 next2 ⇔
    ∀a max1. lookup a next1 = SOME (max1:num) ⇒
      ∃max2. lookup a next2 = SOME max2 ∧ max1 ≤ max2`

val next_weak_trans = store_thm("next_weak_trans",
  ``next_weak n1 n2 ∧ next_weak n2 n3 ⇒ next_weak n1 n3``,
  rw[next_weak_def] >> res_tac >> rw[] >>
  res_tac >> rw[] >> simp[])

val alloc_tags_next = store_thm("alloc_tags_next",
  ``∀x st z. FST (FST (alloc_tags x st z)) = FST (FST st)``,
  ho_match_mp_tac alloc_tags_ind >>
  rw[alloc_tags_def] >> rw[] >>
  rw[Abbr`st'`] >>
  qid_spec_tac`st` >>
  pop_assum kall_tac >>
  qid_spec_tac`constrs` >>
  Induct_on`constrs` >>
  rw[] >>
  PairCases_on`st`>>rw[alloc_tag_def] >>
  simp[UNCURRY])

val decs_to_i2_next_weak = store_thm("decs_to_i2_next_weak",
  ``next_weak (FST(FST st)) (FST(FST(FST (decs_to_i2 (st:tagenv_state_acc) ds))))``,
  qid_spec_tac`st`>>Induct_on`ds`>>
  rw[decs_to_i2_def] >- rw[next_weak_def] >>
  Cases_on`h`>>simp[UNCURRY] >- (
    match_mp_tac (GEN_ALL next_weak_trans) >>
    qpat_abbrev_tac`st1:tagenv_state_acc = alloc_tags X Y Z` >>
    first_x_assum(qspec_then`st1`strip_assume_tac) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[Abbr`st1`,alloc_tags_next] >>
    simp[next_weak_def] ) >>
  match_mp_tac (GEN_ALL next_weak_trans) >>
  qpat_abbrev_tac`st1:tagenv_state_acc = alloc_tag A X Y Z` >>
  first_x_assum(qspec_then`st1`strip_assume_tac) >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  rw[Abbr`st1`] >>
  PairCases_on`st`>>rw[alloc_tag_def] >>
  simp[next_weak_def,sptreeTheory.lookup_insert] >>
  rw[] >>
  simp[Abbr`tag`])

val same_tid_tid = prove(
  ``(same_tid (TypeId x) y ⇔ (y = TypeId x)) ∧
    (same_tid y (TypeId x) ⇔ (y = TypeId x))``,
  Cases_on`y`>>EVAL_TAC>>rw[EQ_IMP_THM])

val alloc_tag_cenv_inv = prove(
  ``cenv_inv envC (get_exh (FST st)) (get_tagenv st) gtagenv ∧
    next_inv tids (FST (FST st)) gtagenv ∧
    (cn,tn) ∉ FDOM gtagenv ⇒
    ∃gtagenv'.
      cenv_inv (merge_alist_mod_env ([],[(cn,arity,tn)]) envC)
        (get_exh (FST (alloc_tag tn cn arity st)))
        (get_tagenv (alloc_tag tn cn arity st))
        gtagenv' ∧
      next_inv (tn INSERT tids) (FST (FST (alloc_tag tn cn arity st))) gtagenv' ∧
      gtagenv ⊑ gtagenv' ∧
      FDOM gtagenv' = FDOM gtagenv ∪ {(cn,tn)}``,
  `∃next tagenv exh acc. st = ((next,tagenv,exh),acc)` by metis_tac[PAIR] >>
  `∃env menv. envC = (menv,env)` by metis_tac[PAIR] >>
  simp[merge_alist_mod_env_def] >> strip_tac >>
  Cases_on`tn` >>
  simp[alloc_tag_def,UNCURRY,get_exh_def,get_tagenv_def] >- (
    qpat_abbrev_tac`tagexh:num#exh_ctors_env = X Y` >>
    qexists_tac`gtagenv |+ ((cn,TypeId i),(FST tagexh,arity))` >>
    reverse conj_tac >- (
      conj_tac >- (
        fs[next_inv_def,FLOOKUP_UPDATE] >>
        metis_tac[SUBSET_INSERT_RIGHT] ) >>
      simp[] >> simp[EXTENSION] >>
      metis_tac[] ) >>
    fs[cenv_inv_def] >>
    conj_tac >- (
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[envC_tagged_def] >>
      reverse Cases >> simp[lookup_alist_mod_env_def] >- (
        first_x_assum(qspec_then`Long s a`mp_tac) >>
        simp[lookup_alist_mod_env_def] >> strip_tac >>
        rpt gen_tac >>
        BasicProvers.CASE_TAC >> fs[] >>
        strip_tac >> fs[] >>
        `∃mtagenv ftagenv. tagenv = (mtagenv,ftagenv)` by metis_tac[PAIR]>>
        simp[insert_tag_env_def,lookup_tag_env_def] >>
        fs[get_tagenv_def,lookup_tag_env_def] >>
        simp[FLOOKUP_UPDATE] >>
        fs[id_to_n_def] >>
        fs[get_exh_def,exhaustive_env_correct_def,PULL_EXISTS] >>
        IF_CASES_TAC >> simp[] >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >>
        fs[FLOOKUP_DEF] ) >>
      rpt gen_tac >>
      `∃mtagenv ftagenv. tagenv = (mtagenv,ftagenv)` by metis_tac[PAIR]>>
      rw[insert_tag_env_def,lookup_tag_env_def,lookup_tag_flat_def,FLOOKUP_UPDATE,id_to_n_def] >>
      first_x_assum(qspec_then`Short a`mp_tac) >>
      simp[lookup_alist_mod_env_def] >> strip_tac >>
      fs[lookup_tag_env_def,get_tagenv_def,lookup_tag_flat_def] >>
      fs[id_to_n_def] ) >>
    conj_tac >- (
      fs[exhaustive_env_correct_def,get_exh_def,PULL_EXISTS] >>
      conj_tac >- (
        simp[Abbr`tagexh`] >>
        every_case_tac >> simp[] >> rw[] >>
        TRY(
          match_mp_tac sptreeTheory.wf_insert >>
          rw[sptreeTheory.wf_def] >>
          fs[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
          first_x_assum match_mp_tac >>
          first_assum(match_exists_tac o concl) >>
          rw[] >> NO_TAC) >>
        pop_assum mp_tac >>
        match_mp_tac IN_FRANGE_DOMSUB_suff >>
        rw[] ) >>
      (*
      conj_tac >- (
        fs[SUBSET_DEF,EXISTS_PROD] >>
        simp[Abbr`tagexh`] >>
        every_case_tac >> simp[] >>
        metis_tac[] ) >>
      *)
      rw[Abbr`tagexh`] >- (
        every_case_tac  >> simp[FLOOKUP_UPDATE,sptreeTheory.lookup_insert] >> rw[] >>
        first_x_assum(qspecl_then[`i`,`cn'`]mp_tac) >>
        (discharge_hyps >- fs[FLOOKUP_DEF]) >> rw[] >>
        res_tac >> fs[] >> rw[] >> simp[] ) >>
      every_case_tac >> simp[FLOOKUP_UPDATE] >> rw[sptreeTheory.lookup_insert] >>
      every_case_tac >> fs[] >> rw[] >> fs[] >>
      TRY (
        qmatch_assum_rename_tac`FLOOKUP gtagenv (cnz,TypeId i) = SOME (tag,az)` >>
        first_x_assum(qspecl_then[`i`,`cnz`]mp_tac) >>
        (discharge_hyps >- fs[FLOOKUP_DEF]) >> rw[] >>
        res_tac >> fs[] >> simp[]) >>
      res_tac >> fs[] >>
      metis_tac[] ) >>
    fs[gtagenv_wf_def] >>
    conj_tac >- fs[has_exns_def,FLOOKUP_UPDATE] >>
    conj_tac >- (
      fs[has_bools_def,FLOOKUP_UPDATE] >>
      rw[] >> fs[FLOOKUP_DEF] ) >>
    conj_tac >- (
      fs[has_lists_def,FLOOKUP_UPDATE] >>
      rw[] >> fs[FLOOKUP_DEF] ) >>
    simp[FLOOKUP_UPDATE] >>
    simp[Abbr`tagexh`] >>
    rpt gen_tac >>
    every_case_tac >> fs[same_tid_tid] >> rpt BasicProvers.VAR_EQ_TAC >> simp[same_tid_tid] >>
    spose_not_then strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    fs[exhaustive_env_correct_def,get_exh_def,PULL_EXISTS] >>
    qmatch_assum_rename_tac`FLOOKUP gtagenv (cnz,TypeId i) = SOME _` >>
    first_x_assum(qspecl_then[`i`,`cnz`]mp_tac) >>
    (discharge_hyps >- fs[FLOOKUP_DEF] >> rw[]) >>
    first_assum(match_exists_tac o concl) >>
    simp[] ) >>
  qpat_abbrev_tac`tag:num = X Y` >>
  qexists_tac`gtagenv |+ ((cn,TypeExn i),(tag,arity))` >>
  reverse conj_tac >- (
    conj_tac >- (
      fs[next_inv_def,FLOOKUP_UPDATE,sptreeTheory.lookup_insert,Abbr`tag`] >>
      reverse conj_tac >- (
        metis_tac[SUBSET_INSERT_RIGHT] ) >>
      rpt gen_tac >> every_case_tac >> rw[] >> fs[] >>
      res_tac >> fs[] >> rw[] >> simp[] ) >>
    simp[] >> simp[EXTENSION] >>
    metis_tac[] ) >>
  fs[cenv_inv_def] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  conj_tac >- (
    fs[envC_tagged_def] >>
    reverse Cases >> simp[lookup_alist_mod_env_def] >- (
      first_x_assum(qspec_then`Long s a`mp_tac) >>
      simp[lookup_alist_mod_env_def] >> strip_tac >>
      rpt gen_tac >>
      BasicProvers.CASE_TAC >> fs[] >>
      strip_tac >> fs[] >>
      `∃mtagenv ftagenv. tagenv = (mtagenv,ftagenv)` by metis_tac[PAIR]>>
      simp[insert_tag_env_def,lookup_tag_env_def] >>
      fs[get_tagenv_def,lookup_tag_env_def] >>
      simp[FLOOKUP_UPDATE] >>
      fs[id_to_n_def] >>
      fs[get_exh_def,exhaustive_env_correct_def,PULL_EXISTS] >>
      IF_CASES_TAC >> simp[] >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[FLOOKUP_DEF] ) >>
    rpt gen_tac >>
    `∃mtagenv ftagenv. tagenv = (mtagenv,ftagenv)` by metis_tac[PAIR]>>
    rw[insert_tag_env_def,lookup_tag_env_def,lookup_tag_flat_def,FLOOKUP_UPDATE,id_to_n_def] >>
    first_x_assum(qspec_then`Short a`mp_tac) >>
    simp[lookup_alist_mod_env_def] >> strip_tac >>
    fs[lookup_tag_env_def,get_tagenv_def,lookup_tag_flat_def] >>
    fs[id_to_n_def] ) >>
  conj_tac >- (
    fs[exhaustive_env_correct_def,get_exh_def,PULL_EXISTS] >>
    (* conj_tac >- (fs[SUBSET_DEF] >> metis_tac[]) >> *)
    rw[] >> res_tac >> simp[] >>
    simp[FLOOKUP_UPDATE] >>
    metis_tac[] ) >>
  fs[gtagenv_wf_def] >>
  conj_tac >- (
    fs[has_exns_def,FLOOKUP_UPDATE] >>
    rw[] >> fs[FLOOKUP_DEF] ) >>
  conj_tac >- fs[has_bools_def,FLOOKUP_UPDATE] >>
  conj_tac >- fs[has_lists_def,FLOOKUP_UPDATE] >>
  simp[FLOOKUP_UPDATE] >>
  Cases >> Cases >> simp[same_tid_def,FLOOKUP_UPDATE] >- (
    metis_tac[same_tid_refl] ) >>
  simp[Abbr`tag`] >>
  rpt gen_tac >>
  fs[next_inv_def] >>
  every_case_tac >> fs[] >> rw[] >>
  spose_not_then strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  res_tac >> fs[same_tid_def] >> rw[] >> fs[])

val next_inv_tids_subset = prove(
  ``s1 ⊆ s2 ∧ next_inv s1 st g ⇒ next_inv s2 st g``,
  rw[next_inv_def] >>
  metis_tac[SUBSET_TRANS])

val FOLDL_alloc_tag_cenv_inv = prove(
  ``∀(constrs:(conN # t list) list) envC st gtagenv tids.
    cenv_inv envC (get_exh (FST st)) (get_tagenv st) gtagenv ∧
    next_inv tids (FST (FST st)) gtagenv ∧
    (∀cn. MEM cn (MAP FST constrs) ⇒ (cn,TypeId(mk_id mn tn)) ∉ FDOM gtagenv) ∧
    ALL_DISTINCT (MAP FST constrs)
    ⇒
    let st' = FOLDL (λst (cn,ts). alloc_tag (TypeId (mk_id mn tn)) cn (LENGTH ts) st) st constrs in
    ∃gtagenv'.
    cenv_inv
      (merge_alist_mod_env ([],REVERSE (MAP (λ(cn,ts). (cn,LENGTH ts,TypeId (mk_id mn tn))) constrs)) envC)
      (get_exh (FST st'))
      (get_tagenv st')
      gtagenv' ∧
    next_inv (TypeId(mk_id mn tn) INSERT tids) (FST (FST st')) gtagenv' ∧
    gtagenv ⊑ gtagenv' ∧
    FDOM gtagenv' = FDOM gtagenv ∪ { (cn,TypeId(mk_id mn tn)) | MEM cn (MAP FST constrs) }``,
  ho_match_mp_tac SNOC_INDUCT >>
  conj_tac >- (
    simp[merge_alist_mod_env_empty] >>
    metis_tac[SUBMAP_REFL,next_inv_tids_subset,INSERT_SUBSET,SUBSET_REFL] ) >>
  rw[FOLDL_SNOC] >>
  rw[MAP_SNOC,REVERSE_SNOC] >>
  `∃cn ts. x = (cn,ts)` by metis_tac[PAIR] >>
  fs[] >> BasicProvers.VAR_EQ_TAC >>
  first_x_assum(qspecl_then[`envC`,`st`,`gtagenv`,`tids`]mp_tac) >>
  discharge_hyps >- (
    fs[MAP_SNOC,ALL_DISTINCT_SNOC] ) >>
  BasicProvers.LET_ELIM_TAC >> rfs[] >>
  first_x_assum(mp_tac o MATCH_MP(
    GEN_ALL(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]alloc_tag_cenv_inv))) >>
  disch_then(qspecl_then[`TypeId(mk_id mn tn)`,`TypeId (mk_id mn tn) INSERT tids`,`cn`,`LENGTH ts`]mp_tac) >>
  discharge_hyps >- (
    fs[MAP_SNOC,ALL_DISTINCT_SNOC] >>
    Cases_on`envC`>>fs[merge_alist_mod_env_def]) >>
  simp[merge_alist_mod_env_assoc,merge_alist_mod_env_def] >>
  strip_tac >>
  first_assum(match_exists_tac o concl) >>
  simp[] >>
  simp[EXTENSION] >>
  metis_tac[SUBMAP_TRANS] )

val union_insert_lem = prove(
  ``a ∪ (b INSERT c) = (a ∪ {b}) ∪ c``,
  rw[EXTENSION] >> metis_tac[])

val alloc_tags_cenv_inv = prove(
  ``∀mn st (ls:(tvarN list # typeN # (conN # t list) list) list) envC gtagenv tids.
    cenv_inv envC (get_exh (FST st)) (get_tagenv st) gtagenv ∧
    next_inv tids (FST (FST st)) gtagenv ∧
    (* new types only *)
    DISJOINT (set (MAP (TypeId o mk_id mn o FST o SND) ls)) (IMAGE SND (FDOM gtagenv))
    ∧ ALL_DISTINCT (MAP (FST o SND) ls)
    ∧ check_dup_ctors ls
    ⇒
    ∃gtagenv'.
    cenv_inv (merge_alist_mod_env ([],build_tdefs mn ls) envC)
      (get_exh (FST (alloc_tags mn st ls)))
      (get_tagenv (alloc_tags mn st ls))
      gtagenv' ∧
    next_inv (tids ∪ type_defs_to_new_tdecs mn ls) (FST (FST (alloc_tags mn st ls))) gtagenv' ∧
    gtagenv_weak gtagenv gtagenv' ∧
    IMAGE SND (FDOM gtagenv') = IMAGE SND (FDOM gtagenv)
      ∪ IMAGE (TypeId o mk_id mn o FST o SND)
        (set (FILTER ($~ o NULL o SND o SND) ls))``,
  ho_match_mp_tac alloc_tags_ind >>
  conj_tac >- (
    simp[alloc_tags_def,build_tdefs_def,merge_alist_mod_env_empty,get_exh_def,get_tagenv_def,type_defs_to_new_tdecs_def] >>
    metis_tac[cenv_inv_def,gtagenv_weak_refl] ) >>
  rpt gen_tac >>
  qpat_abbrev_tac`tagenv_st:tagenv_state_acc = FOLDL X Y Z` >>
  reverse(rw[build_tdefs_cons]) >- (
    Cases_on`constrs`>>fs[] >>
    simp[alloc_tags_def] >>
    fs[type_defs_to_new_tdecs_def,Once union_insert_lem] >>
    first_x_assum match_mp_tac >>
    rfs[] >>
    fs[check_dup_ctors_thm] >>
    match_mp_tac (GEN_ALL next_inv_tids_subset) >>
    qexists_tac`tids`>>simp[]) >>
  first_x_assum(qspecl_then[`constrs`,`tids`]mp_tac o
    MATCH_MP(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]FOLDL_alloc_tag_cenv_inv)) >>
  discharge_hyps >- (
    fs[check_dup_ctors_thm,ALL_DISTINCT_APPEND,FST_pair] >>
    metis_tac[SND] ) >>
  simp[] >> strip_tac >>
  simp[alloc_tags_def] >>
  first_x_assum(fn th =>
    first_assum(mp_tac o MATCH_MP(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  disch_then(qspec_then`TypeId(mk_id mn tn) INSERT tids`mp_tac) >>
  discharge_hyps >- (
    imp_res_tac check_dup_ctors_cons >>
    simp[] >>
    conj_tac >- metis_tac[DISJOINT_SYM] >>
    fs[check_dup_ctors_thm,ALL_DISTINCT_APPEND] >>
    fs[IN_DISJOINT,MEM_FLAT,MEM_MAP,PULL_EXISTS,FORALL_PROD] >>
    spose_not_then strip_assume_tac >> rw[] >>
    fs[mk_id_11] >> rw[] >>
    metis_tac[] ) >>
  simp[merge_alist_mod_env_assoc,merge_alist_mod_env_def] >>
  strip_tac >>
  first_assum (match_exists_tac o concl) >> simp[] >>
  conj_tac >- (
    Cases_on`envC`>>fs[merge_alist_mod_env_def] >>
    fs[type_defs_to_new_tdecs_def,GSYM union_insert_lem,Once INSERT_SING_UNION] >>
    metis_tac[UNION_ASSOC,UNION_COMM]) >>
  conj_tac >- (
    match_mp_tac gtagenv_weak_trans >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> rw[] >>
    simp[gtagenv_weak_def] >>
    reverse conj_tac >- (
      fs[cenv_inv_def,gtagenv_wf_def] >>
      metis_tac[] ) >>
    metis_tac[SND] ) >>
  simp[EXTENSION,PULL_EXISTS] >>
  rw[EQ_IMP_THM] >>
  TRY(metis_tac[]) >>
  simp[mk_id_11,EXISTS_PROD,MEM_FILTER] >>
  fs[NOT_NULL_MEM,MEM_MAP] >>
  metis_tac[])

val decs_to_i2_correct = store_thm("decs_to_i2_correct",
  ``∀ck genv envC s ds r.
      evaluate_decs_i1 ck genv envC s ds r ⇒
    ∀res s1 tids s1_i2 genv_i2 tagenv_st ds_i2 tagenv_st' genv' envC' s' tids' gtagenv.
      s = (s1,tids) ∧
      r = ((s',tids'), envC', genv', res) ∧
      res ≠ SOME Rtype_error ∧
      no_dup_types_i1 ds ∧
      decs_to_i2 tagenv_st ds = (tagenv_st', ds_i2) ∧
      cenv_inv envC (get_exh (FST tagenv_st)) (get_tagenv tagenv_st) gtagenv ∧
      s_to_i2 gtagenv s1 s1_i2 ∧
      LIST_REL (OPTREL (v_to_i2 gtagenv)) genv genv_i2 ∧
      next_inv tids (FST (FST tagenv_st)) gtagenv
      ⇒
      ∃genv'_i2 s'_i2 res_i2 gtagenv' acc'.
        evaluate_decs_i2 ck (get_exh (FST tagenv_st')) genv_i2 s1_i2 ds_i2 (s'_i2,genv'_i2,res_i2) ∧
        gtagenv_weak gtagenv gtagenv' ∧
        vs_to_i2 gtagenv' genv' genv'_i2 ∧
        s_to_i2 gtagenv' s' s'_i2 ∧
        next_inv tids' (FST (FST tagenv_st')) gtagenv' ∧
        SND tagenv_st' = FUNION acc' (SND tagenv_st) ∧
        gtagenv_wf gtagenv' ∧
        exhaustive_env_correct (get_exh (FST tagenv_st')) gtagenv' ∧
        (res = NONE ∧ res_i2 = NONE ∧ FDOM acc' = set (MAP FST envC') ∧
         flat_envC_tagged envC' acc' gtagenv'
         ∨
         (∃err err_i2.
           res = SOME err ∧ res_i2 = SOME err_i2 ∧
           result_to_i2 v_to_i2 gtagenv' (Rerr err) (Rerr err_i2)))``,
  ho_match_mp_tac evaluate_decs_i1_strongind >>
  conj_tac >- (
    simp[FDOM_EQ_EMPTY,decs_to_i2_def] >>
    rw[Once evaluate_decs_i2_cases,vs_to_i2_list_rel] >>
    qexists_tac`gtagenv` >>
    fs[cenv_inv_def] >>
    simp[gtagenv_weak_refl] >>
    simp[flat_envC_tagged_def] ) >>
  conj_tac >- (
    simp[decs_to_i2_def] >>
    simp[Once evaluate_dec_i1_cases] >>
    rw[] >> fs[] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rw[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 exp_to_i2_correct)) >> simp[] >>
    `env_all_to_i2 (get_tagenv tagenv_st) (genv,envC,[]) (get_exh (FST tagenv_st),genv_i2,[]) gtagenv`
                by (fs [env_all_to_i2_cases] >> rw [v_to_i2_eqns]) >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    disch_then(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
    rw[Once evaluate_decs_i2_cases,Once evaluate_dec_i2_cases,PULL_EXISTS,vs_to_i2_list_rel] >>
    srw_tac[boolSimps.DNF_ss][] >> disj1_tac >> rpt disj2_tac >>
    `∃err_i2. r_i2 = Rerr err_i2` by fs[result_to_i2_cases] >> rw[] >>
    imp_res_tac tagacc_accumulates >> simp[] >>
    first_assum(mp_tac o MATCH_MP (CONJUNCT1 evaluate_exp_i2_exh_weak)) >> simp[] >>
    disch_then(qspec_then`get_exh (FST st')`mp_tac) >>
    discharge_hyps >- (
      fs[result_to_i2_cases] >> fs[] >>
      metis_tac[decs_to_i2_exh_weak,FST] ) >>
    strip_tac >>
    CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``evaluate_i2`` o fst o strip_comb))) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    (*
    qabbrev_tac`extra:gtagenv = FUN_FMAP (K (ARB,ARB))
      { (ARB,TypeId t) | t ∈ FDOM (get_exh (FST st')) ∧ TypeId t ∉ IMAGE SND (FDOM gtagenv) }` >>
    map_every qexists_tac[`gtagenv ⊌ extra`,`acc'`] >>
    qmatch_assum_abbrev_tac`Abbrev(extra = FUN_FMAP aa pp)` >>
    `FINITE pp` by (
      `pp ⊆ IMAGE (λt. (ARB,TypeId t)) (FDOM (get_exh (FST st')))` suffices_by (
        metis_tac[IMAGE_FINITE,FDOM_FINITE,SUBSET_FINITE] ) >>
      simp[Abbr`pp`,SUBSET_DEF,PULL_EXISTS] ) >>
    `gtagenv_weak gtagenv (gtagenv ⊌ extra)` by (
      simp[gtagenv_weak_def,SUBMAP_FUNION_ID] >>
      conj_tac >- (
        simp[Abbr`extra`,FUN_FMAP_DEF] >>
        simp[Abbr`pp`,FORALL_PROD] >>
        metis_tac[] ) >>
      fs[cenv_inv_def,gtagenv_wf_def] >>
      simp[FLOOKUP_FUNION] >> rpt gen_tac >>
      strip_tac >>
      every_case_tac >>
      rfs[Abbr`extra`,FLOOKUP_FUN_FMAP] >>
      fs[Abbr`pp`,Abbr`aa`,same_tid_tid] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[same_tid_tid] >> rpt BasicProvers.VAR_EQ_TAC >>
      fs[FLOOKUP_DEF,FORALL_PROD] >> metis_tac[] ) >>
    fs[cenv_inv_def] >>
    *)
    map_every qexists_tac[`gtagenv`,`acc'`] >>
    fs[cenv_inv_def] >> simp[gtagenv_weak_refl] >>
    (*
    conj_tac >- (
      fs[s_to_i2_cases] >>
      metis_tac[LIST_REL_mono,sv_to_i2_weakening] ) >>
    conj_tac >- (
      fs[next_inv_def] >>
      simp[FLOOKUP_FUNION] >>
      conj_tac >- (
        rpt gen_tac >>
        BasicProvers.CASE_TAC >> rw[] >- (
          rfs[Abbr`extra`,FLOOKUP_FUN_FMAP] >>
          fs[Abbr`pp`] ) >>
        PairCases_on`tagenv_st` >>
        PairCases_on`st'` >>
        fs[next_inv_def] >>
        rw[] >> res_tac >>
        `next_weak tagenv_st0 st'0` by metis_tac[decs_to_i2_next_weak,FST] >>
        fs[next_weak_def] >> res_tac >> simp[] ) >>
      simp[Abbr`extra`,FUN_FMAP_DEF] >>
      simp[Abbr`pp`,SUBSET_DEF]
    *)
    conj_tac >- (
      PairCases_on`tagenv_st` >>
      PairCases_on`st'` >>
      fs[next_inv_def] >>
      rw[] >> res_tac >>
      `next_weak tagenv_st0 st'0` by metis_tac[decs_to_i2_next_weak,FST] >>
      fs[next_weak_def] >> res_tac >> simp[] ) >>
    match_mp_tac (GEN_ALL exhaustive_env_correct_exh_weak) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fs[exhaustive_env_correct_def,GSYM exh_wf_def] >>
    metis_tac[decs_to_i2_exh_wf,decs_to_i2_exh_weak,FST]) >>
  rw[] >>
  imp_res_tac no_dup_types_i1_cons_imp >>
  Cases_on`s'` >> rfs[] >> fs[] >>
  rator_x_assum`decs_to_i2`mp_tac >>
  simp[decs_to_i2_def] >>
  BasicProvers.CASE_TAC >> strip_tac >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  BasicProvers.VAR_EQ_TAC >>
  first_x_assum(fn th => first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  fs[evaluate_dec_i1_cases] >> rpt BasicProvers.VAR_EQ_TAC >>
  fs[merge_alist_mod_env_empty]
  >- (
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 exp_to_i2_correct)) >>
    simp[env_all_to_i2_cases,PULL_EXISTS,GSYM AND_IMP_INTRO] >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[v_to_i2_eqns] >>
    disch_then(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    fs[result_to_i2_eqns,v_to_i2_eqns,vs_to_i2_list_rel] >>
    disch_then(qspec_then`genv_i2 ++ MAP SOME vs'`mp_tac) >>
    discharge_hyps >- (
      MATCH_MP_TAC EVERY2_APPEND_suff >>
      simp[EVERY2_MAP,optionTheory.OPTREL_def] >>
      simp_tac(srw_ss()++boolSimps.ETA_ss)[] >> rw[] ) >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[PULL_EXISTS] >> rpt gen_tac >>
    qpat_abbrev_tac`D ⇔ a ∨ b` >> strip_tac >>
    qho_match_abbrev_tac`∃a b c d e. P a b c ∧ Q a b c d e` >>
    qunabbrev_tac`P` >>
    simp[Once evaluate_decs_i2_cases,PULL_EXISTS] >>
    srw_tac[boolSimps.DNF_ss][] >> rpt disj2_tac >>
    simp[Abbr`Q`] >>
    simp[evaluate_dec_i2_cases,PULL_EXISTS] >>
    CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``evaluate_decs_i2`` o fst o strip_comb))) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[LEFT_EXISTS_AND_THM] >>
    reverse conj_tac >- (
      conj_tac >- (imp_res_tac LIST_REL_LENGTH) >>
      match_mp_tac (MP_CANON (CONJUNCT1 evaluate_exp_i2_exh_weak)) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      metis_tac[decs_to_i2_exh_weak,FST] ) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    qexists_tac`acc'` >> simp[] >>
    match_mp_tac EVERY2_APPEND_suff >> simp[] >>
    metis_tac[v_to_i2_weakening,vs_to_i2_list_rel] )
  >- (
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    imp_res_tac recfun_helper >>
    pop_assum(qspec_then`l`assume_tac) >>
    qmatch_assum_abbrev_tac`LIST_REL R l1 l2` >>
    disch_then(qspec_then`genv_i2 ++ l2`mp_tac) >>
    discharge_hyps >- (
      match_mp_tac EVERY2_APPEND_suff >> rw[] ) >>
    simp[] >> unabbrev_all_tac >>
    simp[PULL_EXISTS] >> rpt gen_tac >>
    qpat_abbrev_tac`D ⇔ a ∨ b` >> strip_tac >>
    qho_match_abbrev_tac`∃a b c d e. P a b c ∧ Q a b c d e` >>
    qunabbrev_tac`P` >>
    simp[Once evaluate_decs_i2_cases,PULL_EXISTS] >>
    srw_tac[boolSimps.DNF_ss][] >> rpt disj2_tac >>
    simp[Abbr`Q`] >>
    simp[evaluate_dec_i2_cases,PULL_EXISTS] >>
    simp[funs_to_i2_map] >>
    rator_x_assum`evaluate_decs_i2`mp_tac >>
    simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >> strip_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    qexists_tac`acc'`>>simp[]>>
    fs[vs_to_i2_list_rel] >>
    match_mp_tac EVERY2_APPEND_suff >> simp[] >>
    fs[EVERY2_MAP,optionTheory.OPTREL_def,UNCURRY] >>
    match_mp_tac (MP_CANON (GEN_ALL LIST_REL_mono)) >>
    rw[Once CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    metis_tac[v_to_i2_weakening] )
  >- (
    first_x_assum(mp_tac o MATCH_MP(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]alloc_tags_cenv_inv)) >>
    qmatch_assum_rename_tac`decs_to_i2 (alloc_tags mn tagenv_st ls) ds = _` >>
    disch_then(qspecl_then[`mn`,`ls`,`tids`]mp_tac) >>
    discharge_hyps >- (
      simp[combinTheory.o_DEF,LAMBDA_PROD] >>
      PairCases_on`tagenv_st`>>
      fs[next_inv_def] >>
      fs[type_defs_to_new_tdecs_def,IN_DISJOINT,SUBSET_DEF] >>
      metis_tac[] ) >>
    strip_tac >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    disch_then(qspecl_then[`s1_i2`,`genv_i2`]mp_tac) >>
    discharge_hyps >- (
      fs[s_to_i2_cases] >>
      match_mp_tac (GEN_ALL(MP_CANON LIST_REL_mono)) >>
      metis_tac[sv_to_i2_weakening] ) >>
    discharge_hyps >- (
      match_mp_tac (GEN_ALL(MP_CANON LIST_REL_mono)) >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      first_assum(match_exists_tac o concl) >>
      simp[optionTheory.OPTREL_def] >> rw[] >>
      metis_tac[v_to_i2_weakening] ) >>
    discharge_hyps >- (
      Cases_on`envC`>>fs[merge_alist_mod_env_def] >>
      simp[Once UNION_COMM] ) >>
    simp[PULL_EXISTS] >> rpt gen_tac >>
    qpat_abbrev_tac`D ⇔ a ∨ b` >> strip_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    qexists_tac`gtagenv''` >> simp[] >>
    qspecl_then[`ls`,`mn`,`tagenv_st`]strip_assume_tac alloc_tags_accumulates >>
    qexists_tac`acc' ⊌ acc` >>
    conj_tac >- metis_tac[gtagenv_weak_trans] >>
    conj_tac >- metis_tac[FUNION_ASSOC] >>
    qunabbrev_tac`D` >> fs[] >>
    `∃next tagenv exh acc. alloc_tags mn tagenv_st ls = ((next,tagenv,exh),acc)` by metis_tac[PAIR] >>
    fs[cenv_inv_def] >>
    imp_res_tac envC_tagged_flat_envC_tagged >>
    fs[flat_envC_tagged_def] >>
    fs[ALOOKUP_APPEND] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >- (
      strip_tac >>
      first_x_assum(qspec_then`cn`mp_tac) >>
      first_x_assum(qspec_then`cn`mp_tac) >>
      discharge_hyps >- (
        imp_res_tac ALOOKUP_MEM >>
        simp[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      strip_tac >>
      Cases_on`envC`>>simp[merge_alist_mod_env_def,ALOOKUP_APPEND]>>
      strip_tac >>
      fs[lookup_tag_flat_def,FLOOKUP_FUNION] >>
      reverse BasicProvers.CASE_TAC >- (
        fs[FLOOKUP_DEF] >>
        imp_res_tac ALOOKUP_FAILS >>
        rfs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      every_case_tac >> fs[] >- (
        rfs[FLOOKUP_DEF] >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      fs[get_tagenv_def] >>
      Cases_on`tagenv`>>fs[lookup_tag_env_def] >>
      fs[lookup_tag_flat_def] >>
      fs[gtagenv_weak_def] >>
      metis_tac[FLOOKUP_SUBMAP] ) >>
    strip_tac >> BasicProvers.VAR_EQ_TAC >>
    fs[lookup_tag_flat_def,FLOOKUP_FUNION] >>
    res_tac >> simp[] >>
    BasicProvers.CASE_TAC >> fs[]) >>
  qmatch_assum_rename_tac`no_dup_types_i1 (Dexn_i1 mn tn ls::ds)` >>
  first_x_assum(qspecl_then[`TypeExn(mk_id mn tn)`,`tids`,`tn`,`LENGTH ls`]mp_tac o
    MATCH_MP(GEN_ALL(ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]alloc_tag_cenv_inv))) >>
  discharge_hyps >- (
    fs[] >>
    PairCases_on`tagenv_st`>>
    fs[next_inv_def,SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[SND] ) >>
  strip_tac >>
  `gtagenv_weak gtagenv gtagenv'` by (
    simp[gtagenv_weak_def] >>
    reverse conj_tac >- (
      fs[cenv_inv_def,gtagenv_wf_def] >>
      metis_tac[] ) >>
    PairCases_on`tagenv_st`>>
    fs[next_inv_def,SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[SND] ) >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qspecl_then[`s1_i2`,`genv_i2`]mp_tac) >>
  discharge_hyps >- (
    fs[s_to_i2_cases] >>
    match_mp_tac (GEN_ALL(MP_CANON LIST_REL_mono)) >>
    metis_tac[sv_to_i2_weakening] ) >>
  discharge_hyps >- (
    match_mp_tac (GEN_ALL(MP_CANON LIST_REL_mono)) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >>
    simp[optionTheory.OPTREL_def] >> rw[] >>
    metis_tac[v_to_i2_weakening] ) >>
  discharge_hyps >- (
    simp[GSYM INSERT_SING_UNION] >>
    Cases_on`envC`>>fs[merge_alist_mod_env_def]) >>
  simp[PULL_EXISTS] >> rpt gen_tac >>
  qpat_abbrev_tac`D ⇔ a ∨ b` >> strip_tac >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  qexists_tac`gtagenv''` >>
  specl_args_of_then``alloc_tag``alloc_tag_accumulates strip_assume_tac >>
  simp[] >>
  qexists_tac`acc' ⊌ acc` >>
  simp[FUNION_ASSOC] >>
  conj_tac >- metis_tac[gtagenv_weak_trans] >>
  qunabbrev_tac`D` >> fs[] >>
  `∃next tagenv exh acc. alloc_tag (TypeExn (mk_id mn tn)) tn (LENGTH ls) tagenv_st = ((next,tagenv,exh),acc)` by metis_tac[PAIR] >>
  fs[cenv_inv_def] >> imp_res_tac envC_tagged_flat_envC_tagged >>
  fs[flat_envC_tagged_def] >>
  simp[ALOOKUP_APPEND] >>
  rpt gen_tac >>
  Cases_on`ALOOKUP new_tds' cn`>>fs[]>-(
    strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    fs[lookup_tag_flat_def,FLOOKUP_FUNION] >>
    reverse BasicProvers.CASE_TAC >- (
      fs[FLOOKUP_DEF] >>
      imp_res_tac ALOOKUP_FAILS >>
      rfs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    first_x_assum(qspec_then`cn`mp_tac) >>
    first_x_assum(qspec_then`cn`mp_tac) >>
    Cases_on`envC`>>simp[merge_alist_mod_env_def,get_tagenv_def] >>
    strip_tac >>
    every_case_tac >> fs[] >- (
      rfs[FLOOKUP_DEF] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    fs[get_tagenv_def] >>
    Cases_on`tagenv`>>fs[lookup_tag_env_def] >>
    fs[lookup_tag_flat_def] >>
    fs[gtagenv_weak_def] >>
    metis_tac[FLOOKUP_SUBMAP] ) >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  fs[lookup_tag_flat_def,FLOOKUP_FUNION] >>
  res_tac >> simp[] >>
  BasicProvers.CASE_TAC >> fs[])

val tids_of_decs_def = Define`
  tids_of_decs ds = set (FLAT (MAP (λd. case d of Dtype_i1 mn tds => MAP (mk_id mn o FST o SND) tds | _ => []) ds))`;

val tids_of_decs_thm = prove(
  ``(tids_of_decs [] = {}) ∧
    (tids_of_decs (d::ds) = tids_of_decs ds ∪
      case d of Dtype_i1 mn tds => set (MAP (mk_id mn o FST o SND) tds) | _ => {})``,
  simp[tids_of_decs_def] >>
  every_case_tac >> simp[] >>
  metis_tac[UNION_COMM]);

val alloc_tag_exh_FDOM = Q.prove(
  `∀a b c st.
    FDOM (get_exh (FST (alloc_tag a b c st))) =
    FDOM (get_exh (FST st)) ∪ (case a of TypeId t => {t} | _ => {})`,
  rpt gen_tac >>
  PairCases_on`st`>>rw[alloc_tag_def] >>
  every_case_tac >> simp[get_exh_def] >>
  simp[Once INSERT_SING_UNION,UNION_COMM])

val FOLDL_alloc_tags_exh_FDOM = Q.prove(
  `∀(ls:(tvarN,t list)alist) (st:tagenv_state_acc).
     FDOM (get_exh (FST (
       FOLDL (λst' (cn,ts). alloc_tag (TypeId (mk_id mn tn)) cn (LENGTH ts) st') st ls))) ⊆
     FDOM (get_exh (FST st)) ∪ { (mk_id mn tn) }`,
  ho_match_mp_tac SNOC_INDUCT >>
  simp[FOLDL_SNOC] >> rw[] >>
  simp[UNCURRY] >>
  specl_args_of_then``alloc_tag``alloc_tag_exh_FDOM strip_assume_tac >>
  fs[])

val alloc_tags_exh_FDOM = Q.prove(
  `∀mn (ta:tagenv_state_acc) (ls:type_def).
   FDOM (get_exh (FST (alloc_tags mn ta ls))) ⊆
   FDOM (get_exh (FST ta)) ∪ IMAGE (mk_id mn o FST o SND) (set ls)`,
  ho_match_mp_tac alloc_tags_ind >>
  simp[alloc_tags_def] >> rw[] >>
  qspecl_then[`constrs`,`ta`]strip_assume_tac FOLDL_alloc_tags_exh_FDOM >>
  fs[SUBSET_DEF] >>
  metis_tac[])

val FDOM_decs_to_i2_exh = prove(
  ``∀ds (st:tagenv_state_acc) st' ds'.
    decs_to_i2 st ds = (st',ds') ⇒
    FDOM (get_exh (FST st')) ⊆ FDOM (get_exh (FST st)) ∪ tids_of_decs ds``,
  Induct >> simp[decs_to_i2_def,tids_of_decs_thm] >>
  rpt gen_tac >>
  every_case_tac >> fs[] >> rw[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >- (
    pop_assum mp_tac >>
    specl_args_of_then``alloc_tags``alloc_tags_exh_FDOM strip_assume_tac >>
    fs[SUBSET_DEF] >> rw[] >>
    res_tac >- (
      res_tac >> fs[] >>
      simp[MEM_MAP] >>
      metis_tac[] ) >>
    fs[tids_of_decs_def] ) >>
  pop_assum mp_tac >>
  specl_args_of_then``alloc_tag``alloc_tag_exh_FDOM strip_assume_tac >>
  fs[])

val check_dup_ctors_flat = Q.prove (
`!defs.
  check_dup_ctors (defs:type_def) =
  ALL_DISTINCT (MAP FST (build_tdefs mn defs))`,
 rw [check_dup_ctors_thm, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
     build_tdefs_def,
     rich_listTheory.MAP_REVERSE, ALL_DISTINCT_REVERSE]);

(*
val envC_tagged_add_empty_mod = prove(
  ``∀ls mn tagenv g.
      envC_tagged ([(mn,[])],[]) (mod_tagenv (SOME mn) ls tagenv) g``,
  rpt gen_tac >> PairCases_on`tagenv`>>
  rw[envC_tagged_def,mod_tagenv_def,lookup_alist_mod_env_def] >>
  every_case_tac >> fs[FLOOKUP_UPDATE] >>
  rw [] >>
  fs [FLOOKUP_DEF]);
*)

val envC_tagged_add_empty_mod = prove(
  ``∀ls mn tagenv g envC.
      envC_tagged envC tagenv g ⇒
      envC_tagged (merge_alist_mod_env ([(mn,[])],[]) envC) (mod_tagenv (SOME mn) ls tagenv) g``,
  rpt gen_tac >> PairCases_on`tagenv`>> PairCases_on`envC` >>
  simp[envC_tagged_def,mod_tagenv_def,lookup_alist_mod_env_def,merge_alist_mod_env_def,
       lookup_tag_env_def,FLOOKUP_UPDATE,lookup_tag_flat_def] >>
  rw[] >>
  first_x_assum(qspec_then`cn`mp_tac) >>
  fs[FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
  every_case_tac >> fs[] );

val to_i2_invariant_def = Define `
to_i2_invariant mods tids envC tagenv_st gtagenv s s_i2 genv genv_i2 ⇔
  set (MAP FST (FST envC)) ⊆ mods ∧
  (∀x. Short x ∈ FDOM (get_exh tagenv_st) ⇒ TypeId (Short x) ∈ tids) ∧
  (∀mn x. Long mn x ∈ FDOM (get_exh tagenv_st) ⇒ mn ∈ mods) ∧
  cenv_inv envC (get_exh tagenv_st) (get_tagenv ((tagenv_st,FEMPTY):tagenv_state_acc)) gtagenv ∧
  s_to_i2 gtagenv s s_i2 ∧
  LIST_REL (OPTION_REL (v_to_i2 gtagenv)) genv genv_i2 ∧
  next_inv tids (FST tagenv_st) gtagenv`;

val decs_to_i2_dummy_env_num_defs =prove(
  ``∀ds x y z ds2.
    decs_to_i2 x ds = (y,ds2) ⇒
    decs_to_dummy_env ds = num_defs ds2``,
  Induct >> simp[decs_to_i2_def,decs_to_dummy_env_def,num_defs_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >> rw[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  rw[] >>
  simp[dec_to_dummy_env_def,num_defs_def,funs_to_i2_map]);

val envC_tagged_extend = prove(
  ``envC_tagged envC tagenv gtagenv ∧
    flat_envC_tagged cenv acc gtagenv' ∧
    FDOM acc = set (MAP FST cenv) ∧
    gtagenv_weak gtagenv gtagenv'
    ⇒
    envC_tagged (merge_alist_mod_env (mod_cenv mn cenv) envC)
      (mod_tagenv mn acc tagenv) gtagenv'``,
  PairCases_on`envC` >>
  PairCases_on`tagenv` >>
  simp[envC_tagged_def] >>
  Cases_on`mn`>>simp[mod_cenv_def,mod_tagenv_def,merge_alist_mod_env_def,flat_envC_tagged_def] >- (
    rw[lookup_alist_mod_env_def,lookup_tag_env_def,lookup_tag_flat_def,FLOOKUP_FUNION,ALOOKUP_APPEND] >>
    first_x_assum(qspec_then`cn`mp_tac) >>
    pop_assum mp_tac >>
    BasicProvers.CASE_TAC >> fs[] >- (
      BasicProvers.CASE_TAC >> fs[] >- (
        imp_res_tac ALOOKUP_NONE >>
        `FLOOKUP acc a = NONE` by (
          fs[FLOOKUP_DEF] ) >>
        simp[] >> strip_tac >>
        fs[gtagenv_weak_def] >>
        metis_tac[FLOOKUP_SUBMAP] ) >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
      simp[id_to_n_def] >> strip_tac >>
      BasicProvers.CASE_TAC >> simp[] >- (
        BasicProvers.CASE_TAC >> fs[] >>
        BasicProvers.CASE_TAC >> fs[] ) >>
      BasicProvers.CASE_TAC >> simp[] >>
      rw[] >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] ) >>
    BasicProvers.CASE_TAC >>
    strip_tac >>
    fs[gtagenv_weak_def] >>
    metis_tac[FLOOKUP_SUBMAP] ) >>
  simp[lookup_alist_mod_env_def,lookup_tag_flat_def,lookup_tag_env_def,FLOOKUP_UPDATE] >>
  rw[] >>
  first_x_assum(qspec_then`cn`mp_tac) >>
  BasicProvers.CASE_TAC >> fs[] >- (
    fs[gtagenv_weak_def] >>
    metis_tac[FLOOKUP_SUBMAP] ) >>
  rw[] >> fs[FLOOKUP_UPDATE, FLOOKUP_FUNION] >- (
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[id_to_n_def] >> rw[]  >>
    BasicProvers.CASE_TAC >> fs[] ) >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  metis_tac[gtagenv_weak_def,FLOOKUP_SUBMAP]);

val evaluate_dec_i1_tids_acc = store_thm("evaluate_dec_i1_tids_acc",
  ``∀ck genv envC st d res. evaluate_dec_i1 ck genv envC st d res ⇒
      SND st ⊆ SND (FST res)``,
  ho_match_mp_tac evaluate_dec_i1_ind >> simp[])

val evaluate_decs_i1_tids_acc = store_thm("evaluate_decs_i1_tids_acc",
  ``∀ck genv envC st ds res. evaluate_decs_i1 ck genv envC st ds res ⇒
      SND st ⊆ SND(FST res)``,
  ho_match_mp_tac evaluate_decs_i1_ind >> simp[] >> rw[] >>
  first_x_assum(mp_tac o MATCH_MP evaluate_dec_i1_tids_acc) >>
  fs[] >> metis_tac[SUBSET_TRANS])

val evaluate_decs_i1_tids = prove(
  ``∀ck genv envC st ds res. evaluate_decs_i1 ck genv envC st ds res ⇒
      SND(SND(SND res)) = NONE ⇒
      {id | TypeId id ∈ SND(FST res)} = (tids_of_decs ds) ∪ {id | TypeId id ∈ SND st}``,
  ho_match_mp_tac evaluate_decs_i1_ind >> simp[] >>
  conj_tac >- simp[tids_of_decs_thm] >>
  rw[evaluate_dec_i1_cases,tids_of_decs_thm] >> fs[] >>
  simp[EXTENSION,type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  metis_tac[])

val prompt_to_i2_correct = store_thm("prompt_to_i2_correct",
``!ck genv envC s tids mods prompt s_i2 genv_i2 tagenv_st prompt_i2 genv' envC' s' tids' mods' res gtagenv tagenv_st'.
  evaluate_prompt_i1 ck genv envC (s,tids,mods) prompt ((s',tids',mods'), envC', genv', res) ∧
  res ≠ SOME Rtype_error ∧
  to_i2_invariant mods tids envC tagenv_st gtagenv s s_i2 genv genv_i2 ∧
  (tagenv_st', prompt_i2) = prompt_to_i2 tagenv_st prompt
  ⇒
  ?genv'_i2 s'_i2 res_i2 gtagenv' new_envC.
    gtagenv_weak gtagenv gtagenv' ∧
    evaluate_prompt_i2 ck (get_exh tagenv_st') genv_i2 s_i2 prompt_i2 (s'_i2,genv'_i2,res_i2) ∧
    to_i2_invariant mods' tids' new_envC tagenv_st' gtagenv' s' s'_i2 (genv++genv') (genv_i2 ++ genv'_i2) ∧
    (res = NONE ∧ res_i2 = NONE ∧ new_envC = (merge_alist_mod_env envC' envC) ∨
     ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ new_envC = envC ∧
                  result_to_i2 v_to_i2 gtagenv' (Rerr err) (Rerr err_i2))``,
 rw [evaluate_prompt_i1_cases, evaluate_prompt_i2_cases, prompt_to_i2_def, LET_THM] >>
 every_case_tac >> fs [] >> rw [] >>
 first_assum(split_applied_pair_tac o rhs o concl) >> fs[] >>
 rw [] >>
 fs [to_i2_invariant_def]
 >- (
   first_assum(mp_tac o MATCH_MP decs_to_i2_correct) >> simp[] >>
   REWRITE_TAC[GSYM AND_IMP_INTRO] >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
   rpt(disch_then(fn th => first_assum(mp_tac o MATCH_MP th))) >>
   strip_tac >>
   first_assum(match_exists_tac o concl) >>
   simp[PULL_EXISTS] >>
   fs[get_exh_def] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   conj_tac >- (
     Cases_on`envC`>> Cases_on`mn`>>
     simp[mod_cenv_def,update_mod_state_def,merge_alist_mod_env_def] >>
     fs[] >> fs[SUBSET_DEF]) >>
   imp_res_tac FDOM_decs_to_i2_exh >>
   fs[get_exh_def] >>
   conj_tac >- (
     imp_res_tac evaluate_decs_i1_tids >> fs[] >>
     imp_res_tac evaluate_decs_i1_tids_acc >> fs[] >>
     rw[] >> fs[SUBSET_DEF] >>
     res_tac >> fs[] >>
     fs[EXTENSION] ) >>
   conj_tac >- (
     rw[] >> fs[SUBSET_DEF] >>
     res_tac >- (
       res_tac >>
       Cases_on`mn`>>simp[update_mod_state_def] ) >>
     fs[tids_of_decs_def,MEM_FLAT,MEM_MAP,prompt_mods_ok_def,EVERY_MEM] >>
     first_x_assum(qspec_then`d`mp_tac) >>
     simp[] >> BasicProvers.CASE_TAC >> fs[] >>
     rw[] >> fs[MEM_MAP] >>
     Cases_on`mn`>>fs[mk_id_def] >>
     rw[update_mod_state_def] ) >>
   conj_tac >- (
     fs[cenv_inv_def] >>
     simp[get_tagenv_def] >>
     match_mp_tac envC_tagged_extend >>
     simp[] >>
     PairCases_on`tagenv_st`>>fs[get_tagenv_def] ) >>
   match_mp_tac EVERY2_APPEND_suff >>
   conj_tac >- (
     match_mp_tac (GEN_ALL(MP_CANON LIST_REL_mono)) >>
     ONCE_REWRITE_TAC[CONJ_COMM] >>
     first_assum(match_exists_tac o concl) >>
     rw[optionTheory.OPTREL_def] >>
     metis_tac[v_to_i2_weakening] ) >>
   simp[EVERY2_MAP,optionTheory.OPTREL_def] >>
   srw_tac[boolSimps.ETA_ss][GSYM vs_to_i2_list_rel] )
 >- (
   first_assum(mp_tac o MATCH_MP decs_to_i2_correct) >> simp[] >>
   disch_then(mp_tac o REWRITE_RULE[GSYM AND_IMP_INTRO]) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
   rpt(disch_then(fn th => first_assum(mp_tac o MATCH_MP th))) >>
   strip_tac >>
   first_assum(match_exists_tac o concl) >>
   simp[PULL_EXISTS] >>
   fs[get_exh_def] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   conj_tac >- (
     Cases_on`envC`>> Cases_on`mn`>>
     simp[mod_cenv_def,update_mod_state_def,merge_alist_mod_env_def] >>
     fs[] >> fs[SUBSET_DEF]) >>
   imp_res_tac FDOM_decs_to_i2_exh >>
   fs[get_exh_def] >>
   conj_tac >- (
     imp_res_tac evaluate_decs_i1_tids_acc >> fs[] >>
     rw[] >> fs[SUBSET_DEF] >>
     res_tac >> fs[] >>
     fs[tids_of_decs_def,MEM_FLAT,MEM_MAP] >>
     fs[prompt_mods_ok_def,EVERY_MEM] >>
     first_x_assum(qspec_then`d`mp_tac) >>
     simp[] >> BasicProvers.CASE_TAC >> fs[] >>
     rw[] >> fs[MEM_MAP] >>
     Cases_on`mn`>>fs[mk_id_def] >> rw[] >>
     Cases_on`ds`>>fsrw_tac[boolSimps.DNF_ss,ARITH_ss][decs_to_i2_def]>>
     TRY(Cases_on`t`>>fsrw_tac[ARITH_ss][])>>rw[]>>fs[]>>
     fs[LET_THM,decs_to_i2_def]>>rw[]>>
     fs[Once evaluate_decs_i1_cases] >>
     TRY(fs[Once evaluate_decs_i1_cases]>>NO_TAC) >>
     fs[Once evaluate_dec_i1_cases] ) >>
   conj_tac >- (
     rw[] >> fs[SUBSET_DEF] >>
     res_tac >- (
       res_tac >>
       Cases_on`mn`>>simp[update_mod_state_def] ) >>
     fs[tids_of_decs_def,MEM_FLAT,MEM_MAP,prompt_mods_ok_def,EVERY_MEM] >>
     first_x_assum(qspec_then`d`mp_tac) >>
     simp[] >> BasicProvers.CASE_TAC >> fs[] >>
     rw[] >> fs[MEM_MAP] >>
     Cases_on`mn`>>fs[mk_id_def] >>
     rw[update_mod_state_def] ) >>
   conj_tac >- (
     fs[cenv_inv_def] >>
     simp[get_tagenv_def] >>
     PairCases_on`tagenv_st`>>fs[get_tagenv_def] >>
     fs[envC_tagged_def] >>
     rw[] >>
     first_assum(fn th => first_x_assum (strip_assume_tac o MATCH_MP th)) >>
     Cases_on`mn`>>simp[mod_tagenv_def] >> fs[lookup_tag_env_def] >>
     BasicProvers.CASE_TAC >> fs[gtagenv_weak_def]
     >- (
       fs[lookup_tag_flat_def,FLOOKUP_FUNION] >>
       BasicProvers.CASE_TAC >> fs[]
       >- metis_tac[FLOOKUP_SUBMAP] >>
       fs[prompt_mods_ok_def] >>
       Cases_on`ds`>>fs[decs_to_i2_def]>>rw[]>>fs[]>>
       Cases_on`t'`>>fsrw_tac[ARITH_ss][]>>
       fs[LET_THM,decs_to_i2_def] >>
       Cases_on`h`>>fs[]>>rw[]>>fs[]>>
       cheat (* alloc_tags_accumulates? *) )
     >- metis_tac[FLOOKUP_SUBMAP]
     >- metis_tac[FLOOKUP_SUBMAP]
     >- (
       simp[FLOOKUP_UPDATE] >>
       reverse(rw[]) >- metis_tac[FLOOKUP_SUBMAP] >>
       every_case_tac >> fs[get_exh_def] >>
       fs[exhaustive_env_correct_def,PULL_EXISTS] >>
       fs[id_to_n_def] >>
       fs[next_inv_def] >>
       PairCases_on`envC`>>fs[lookup_alist_mod_env_def] >>
       cheat)) >>
   match_mp_tac EVERY2_APPEND_suff >>
   conj_tac >- (
     match_mp_tac EVERY2_APPEND_suff >>
     conj_tac >- PROVE_TAC[LIST_REL_mono,optionTheory.OPTREL_MONO,v_to_i2_weakening] >>
     simp[EVERY2_MAP,optionTheory.OPTREL_def] >>
     srw_tac[boolSimps.ETA_ss][] >>
     fs[vs_to_i2_list_rel] ) >>
   imp_res_tac decs_to_i2_dummy_env_num_defs >>
   fs[vs_to_i2_list_rel] >>
   imp_res_tac LIST_REL_LENGTH >>
   simp[LIST_REL_EL_EQN,EL_GENLIST,optionTheory.OPTREL_def] )

   rw [] >>
   Q.LIST_EXISTS_TAC [`MAP SOME genv'_i2 ++ GENLIST (λn. NONE) (num_defs ds_i2 − LENGTH genv'_i2)`, `s'_i2`, `SOME err_i2`, `gtagenv'`] >>
   fs [get_tagenv_def] >>
   conj_tac >- metis_tac[] >>
   conj_tac >- (
     Cases_on`mn`>>rw[update_mod_state_def] >>
     fs[SUBSET_DEF] ) >>
   imp_res_tac FDOM_decs_to_i2_exh >>
   imp_res_tac evaluate_decs_i1_tids_acc >> fs[] >>
   conj_tac >- (
     gen_tac >> reverse strip_tac >- metis_tac[SUBSET_DEF] >>
     reverse(Cases_on`mn`)>>fs[]>-(
       imp_res_tac IN_tids_of_mod_decs >> fs[] ) >>
     Cases_on`ds`>-fs[tids_of_decs_thm]>>
     Cases_on`t`>>fsrw_tac[ARITH_ss][]>>
     fs[tids_of_decs_thm,not_mod_decs_def] >>
     Cases_on`h`>>fs[]>>rw[]>>fs[mk_id_def,MEM_MAP]>>
     fs[Once evaluate_decs_i1_cases] >>
     fs[Once evaluate_dec_i1_cases] >>
     fs[Once evaluate_decs_i1_cases] >>
     rw[type_defs_to_new_tdecs_def] >>
     rw[MEM_MAP,UNCURRY,mk_id_def] >>
     metis_tac[] ) >>
   conj_tac >- (
     simp[update_mod_state_def] >>
     rpt gen_tac >> reverse strip_tac >- (
       BasicProvers.CASE_TAC >> rw[] >>
       metis_tac[] ) >>
     BasicProvers.CASE_TAC >> fs[] >- (
       imp_res_tac IN_tids_of_not_mod_decs >> fs[] ) >>
     imp_res_tac IN_tids_of_mod_decs >> fs[] ) >>
   rw[]
   >- (
     fs[cenv_inv_def] >>
     fs[get_tagacc_def,get_tagenv_def,FUNION_FEMPTY_2] >> rw[] >>
     Cases_on`mn`>>fs[mod_cenv_def]>-(
       PairCases_on`envC` >>
       fs[mod_tagenv_def,merge_alist_mod_env_def] >>
       Cases_on`ds` >- (
         fs[Once evaluate_decs_i1_cases] ) >>
       Cases_on`t`>>fsrw_tac[ARITH_ss][]>>rw[]>>
       fs[Once evaluate_decs_i1_cases] >- (
         rw[] >>
         fs[Once evaluate_dec_i1_cases] >> rw[] >>
         fs[decs_to_i2_def,LET_THM] >> rw[FUNION_FEMPTY_1] >>
         fs[envC_tagged_def,gtagenv_weak_def] >>
         rw[] >>
         first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
         rw[] >> rw[] >>
         metis_tac[FLOOKUP_SUBMAP] ) >>
       fs[Once evaluate_decs_i1_cases] ) >>
     PairCases_on`envC` >> simp[merge_alist_mod_env_def] >>
     fs[envC_tagged_def,lookup_alist_mod_env_def] >> strip_tac >>
     rpt gen_tac >>
     rpt (first_x_assum(qspec_then`cn`mp_tac)) >>
     BasicProvers.CASE_TAC >- (
       simp[mod_tagenv_def,lookup_tag_env_def] >>
       metis_tac[gtagenv_weak_def,FLOOKUP_SUBMAP] ) >>
     rw[] >> every_case_tac >> fs[] >>
     fs[lookup_tag_env_def,mod_tagenv_def,FLOOKUP_UPDATE] >>
     first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
     BasicProvers.CASE_TAC >- fs[gtagenv_wf_def] >>
     rw[] >- (
       imp_res_tac ALOOKUP_MEM >>
       fs[SUBSET_DEF, MEM_MAP] >>
       metis_tac [pair_CASES, FST]) >>
     metis_tac[gtagenv_weak_def,FLOOKUP_SUBMAP])
   >- (
     match_mp_tac EVERY2_APPEND_suff >>
     conj_tac >- (
       match_mp_tac EVERY2_APPEND_suff >>
       conj_tac >- (
         match_mp_tac EVERY2_MEM_MONO >>
         HINT_EXISTS_TAC >> simp[UNCURRY] >>
         simp[optionTheory.OPTREL_def] >>
         rw[FORALL_PROD] >> rw[] >>
         metis_tac[v_to_i2_weakening] ) >>
       simp[EVERY2_MAP,optionTheory.OPTREL_def] >>
       srw_tac[boolSimps.ETA_ss][] >>
       fs[vs_to_i2_list_rel] ) >>
     qsuff_tac`decs_to_dummy_env ds = num_defs ds_i2` >- (
       fs[vs_to_i2_list_rel] >>
       imp_res_tac EVERY2_LENGTH >> rw[] >>
       simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] ) >>
     metis_tac[decs_to_i2_dummy_env_num_defs])
   >- (
     fs[alloc_tags_invariant_def,get_next_def,get_tagacc_def] >>
     fs[gtagenv_wf_def])));

val prompt_to_i2_correct = Q.store_thm ("prompt_to_i2_correct",
`!ck genv envC s tids mods prompt s_i2 genv_i2 tagenv_st prompt_i2 genv' envC' s' tids' mods' res gtagenv tagenv_st' exh exh'.
  evaluate_prompt_i1 ck genv envC (s,tids,mods) prompt ((s',tids',mods'), envC', genv', res) ∧
  res ≠ SOME Rtype_error ∧
  to_i2_invariant mods tids envC exh tagenv_st gtagenv s s_i2 genv genv_i2 ∧
  (tagenv_st', exh', prompt_i2) = prompt_to_i2 tagenv_st prompt
  ⇒
  ?genv'_i2 s'_i2 res_i2 gtagenv' new_envC.
    gtagenv_weak gtagenv gtagenv' ∧
    DISJOINT (FDOM exh') (FDOM exh) ∧
    evaluate_prompt_i2 ck (FUNION exh' exh) genv_i2 s_i2 prompt_i2 (s'_i2,genv'_i2,res_i2) ∧
    to_i2_invariant mods' tids' new_envC (FUNION exh' exh) tagenv_st' gtagenv' s' s'_i2 (genv++genv') (genv_i2 ++ genv'_i2) ∧
    (res = NONE ∧ res_i2 = NONE ∧ new_envC = (merge_alist_mod_env envC' envC) ∨
     ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ new_envC = envC ∧
                  result_to_i2 (\a b c. T) gtagenv' (Rerr err) (Rerr err_i2))`,
 rw [] >>
 match_mp_tac prompt_to_i2_correct_lem >>
 MAP_EVERY qexists_tac [`s`, `tids`, `mods`, `prompt`, `tagenv_st`] >>
 rw [] >>
 fs [evaluate_prompt_i1_cases] >>
 rw [] >>
 fs [prompt_mods_ok_def, not_mod_decs_def, mod_decs_def]);

val evaluate_dec_i2_exh_weak = prove(
  ``∀ck (exh:exh_ctors_env) genv s d res.
      evaluate_dec_i2 ck exh genv s d res ⇒
      ∀exh'. DISJOINT (FDOM exh) (FDOM exh') ∧ SND res ≠ Rerr Rtype_error
        ⇒ evaluate_dec_i2 ck (exh' ⊌ exh) genv s d res``,
  ho_match_mp_tac evaluate_dec_i2_ind >> rw[] >>
  TRY (
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 evaluate_exp_i2_exh_weak)) >> simp[] >>
    disch_then(qspec_then`exh'`mp_tac) >> simp[DISJOINT_SYM] >> strip_tac ) >>
  rw[Once evaluate_dec_i2_cases] );

val evaluate_decs_i2_exh_weak = prove(
 ``∀ck (exh:exh_ctors_env) genv s ds res.
     evaluate_decs_i2 ck exh genv s ds res
     ⇒
     ∀exh'. DISJOINT (FDOM exh) (FDOM exh') ∧ SND (SND res) ≠ SOME Rtype_error ⇒
       evaluate_decs_i2 ck (exh' ⊌ exh) genv s ds res``,
  ho_match_mp_tac evaluate_decs_i2_ind >> rw[]
  >- rw[Once evaluate_decs_i2_cases] >>
  first_x_assum(strip_assume_tac o MATCH_MP evaluate_dec_i2_exh_weak) >>
  first_x_assum(qspec_then`exh'`strip_assume_tac) >> rfs[] >>
  rw[Once evaluate_decs_i2_cases] >>
  metis_tac[]);

val evaluate_prompt_i2_exh_weak = Q.prove (
`!ck (exh:exh_ctors_env) genv s p s' genv' res exh1.
 evaluate_prompt_i2 ck exh genv s p (s',genv',res) ∧
 DISJOINT (FDOM exh1) (FDOM exh) ∧ res ≠ SOME Rtype_error
 ⇒
 evaluate_prompt_i2 ck (exh1 ⊌ exh) genv s p (s',genv',res)`,
 rw[evaluate_prompt_i2_cases] >>
 first_x_assum(strip_assume_tac o MATCH_MP evaluate_decs_i2_exh_weak) >>
 first_x_assum(qspec_then`exh1`mp_tac) >>
 rw[] >> metis_tac[DISJOINT_SYM]);

val tids_of_prompt_def = Define`
  tids_of_prompt (Prompt_i1 _ ds) = tids_of_decs ds`;

val FDOM_prompt_to_i2_exh = prove(
  ``∀x p y z a. prompt_to_i2 x p = (y,z,a) ⇒ FDOM z = tids_of_prompt p``,
  rw[prompt_to_i2_def] >> every_case_tac >>
  fs[LET_THM,UNCURRY] >> rw[] >>
  rw[tids_of_prompt_def] >>
  match_mp_tac FDOM_decs_to_i2_exh >>
  metis_tac[pair_CASES,FST,SND,PAIR_EQ]);

val tids_of_prog_def = Define`
  tids_of_prog prog = BIGUNION (set (MAP tids_of_prompt prog))`;

val FDOM_prog_to_i2_exh = prove(
  ``∀x p y z a. prog_to_i2 x p = (y,z,a) ⇒ FDOM z = tids_of_prog p``,
  Induct_on`p`>>rw[prog_to_i2_def,tids_of_prog_def]>>rw[]>>
  fs[LET_THM,tids_of_prog_def] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rw[] >>
  res_tac >> simp[] >>
  imp_res_tac FDOM_prompt_to_i2_exh >>
  simp[UNION_COMM]);

val evaluate_decs_i1_tids_disjoint = prove(
  ``∀ck genv envC st ds res. evaluate_decs_i1 ck genv envC st ds res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_decs ds)) (SND st)``,
  ho_match_mp_tac evaluate_decs_i1_ind >> simp[] >>
  conj_tac >- simp[tids_of_decs_thm] >>
  rw[evaluate_dec_i1_cases,tids_of_decs_thm] >> fs[DISJOINT_SYM] >>
  fs[type_defs_to_new_tdecs_def,IN_DISJOINT,MEM_MAP,UNCURRY] >>
  metis_tac[]);

val evaluate_prompt_i1_tids_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_prompt p)) (FST(SND stm))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[] >> rw[] >>
  imp_res_tac evaluate_decs_i1_tids_disjoint >> fs[tids_of_prompt_def]);

val evaluate_prompt_i1_tids_acc = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      FST(SND stm) ⊆ FST(SND(FST res))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[] >> rw[] >>
  imp_res_tac evaluate_decs_i1_tids_acc >> fs[]);

val evaluate_prompt_i1_tids = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      {id | TypeId id ∈ FST(SND(FST res))} = (tids_of_prompt p) ∪ {id | TypeId id ∈ FST(SND stm)}``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[] >> rw[] >>
  imp_res_tac evaluate_decs_i1_tids >> fs[tids_of_prompt_def])

val evaluate_prog_i1_tids_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prog_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_prog p)) (FST(SND stm))``,
  ho_match_mp_tac evaluate_prog_i1_ind >> simp[] >> rw[] >>
  fs[tids_of_prog_def] >>
  imp_res_tac evaluate_prompt_i1_tids_disjoint >> fs[] >>
  imp_res_tac evaluate_prompt_i1_tids_acc >>
  fs[IN_DISJOINT,SUBSET_DEF] >>
  metis_tac[]);

val mods_of_prog_def = Define`
  mods_of_prog [] = {} ∧
  mods_of_prog ((Prompt_i1 (SOME mn) ds)::ps) = mn INSERT mods_of_prog ps ∧
  mods_of_prog (_::ps) = mods_of_prog ps`

val IN_mods_of_prog = prove(
  ``∀prog mn ds. MEM (Prompt_i1 (SOME mn) ds) prog ⇒ mn ∈ mods_of_prog prog``,
  Induct >> simp[mods_of_prog_def] >> rw[] >> simp[mods_of_prog_def] >>
  `∃x y. h = Prompt_i1 x y` by (Cases_on`h` >> simp[GSYM EXISTS_PROD]) >>
  Cases_on`x`>>simp[mods_of_prog_def] >>
  metis_tac[])

val evaluate_prog_i1_mods_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prog_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (SND(SND stm)) (mods_of_prog p)``,
  ho_match_mp_tac evaluate_prog_i1_ind >> simp[] >>
  simp[mods_of_prog_def] >> rw[] >>
  fs[evaluate_prompt_i1_cases] >> rw[] >>
  Cases_on`mn`>>fs[mods_of_prog_def,update_mod_state_def] >>
  fs[IN_DISJOINT] >> metis_tac[])

val evaluate_prompt_i1_mods_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      ∀mn ds. p = Prompt_i1 (SOME mn) ds ⇒ mn ∉ (SND(SND stm))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[])

val evaluate_prompt_i1_mods_acc = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      SND(SND stm) ⊆ SND(SND(FST res))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[] >>
  rw[update_mod_state_def] >>
  BasicProvers.CASE_TAC >> simp[]);

val no_dup_mods_i1_eqn = Q.prove (
`!p ps.
  (no_dup_mods_i1 [] (x,y,mods) ⇔ T) ∧
  (no_dup_mods_i1 (p::ps) (x,y,mods) ⇔
     (case p of
       | Prompt_i1 (SOME mn) ds =>
           ~MEM mn (prog_i1_to_mods ps) ∧ mn ∉ mods
       | Prompt_i1 NONE _ => T) ∧
    no_dup_mods_i1 ps (x,y,mods))`,
 rw [no_dup_mods_i1_def, prog_i1_to_mods_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac []);

val no_dup_top_types_i1_eqn = Q.prove (
`!p ps.
  (no_dup_top_types_i1 [] (x,tids,y) ⇔ T) ∧
  (no_dup_top_types_i1 (p::ps) (x,tids,y) ⇔
     (case p of
       | Prompt_i1 NONE ds =>
           ALL_DISTINCT (decs_to_types_i1 ds) ∧
           DISJOINT (set (decs_to_types_i1 ds)) (set (prog_i1_to_top_types ps)) ∧
           DISJOINT (IMAGE (\tn. TypeId (Short tn)) (set (decs_to_types_i1 ds))) tids
       | Prompt_i1 (SOME mn) _ => T) ∧
    no_dup_top_types_i1 ps (x,tids,y))`,
 rw [no_dup_top_types_i1_def, prog_i1_to_top_types_def] >>
 every_case_tac >>
 rw [ALL_DISTINCT_APPEND, DISJOINT_DEF, EXTENSION] >>
 fs [MEM_MAP] >>
 metis_tac []);

val evaluate_prog_i1_prompt_ok = prove(
  ``∀a b c d e f. evaluate_prog_i1 a b c d e f ⇒
    ∀g h. MEM (Prompt_i1 g h) e ∧ SND(SND(SND f)) = NONE ⇒
    prompt_mods_ok g h``,
  ho_match_mp_tac evaluate_prog_i1_ind >>
  rw[] >> res_tac >> fs[evaluate_prompt_i1_cases]);

val mods_of_prog_thm = prove(
  ``mods_of_prog prog = {mn | ∃d. MEM (Prompt_i1 (SOME mn) d) prog}``,
  Induct_on`prog`>>simp[mods_of_prog_def]>>
  Cases>>simp[mods_of_prog_def]>>
  Cases_on`o'`>>simp[mods_of_prog_def]>>
  simp[EXTENSION] >> metis_tac[]);

val exh_disjoint1 = Q.prove (
`prompt_to_i2 (next,tagenv,inv') prompt = ((next2,tagenv2,inv2),exh2,p2) ∧
  prog_to_i2 (next2,tagenv2,inv2) prog = ((next',tagenv',inv''),exh1,ps1)  ∧
  no_dup_mods_i1 (prompt::prog) (s:v_i1 count_store,tids,mods) ∧
  no_dup_top_types_i1 (prompt::prog) (s,tids,mods) ∧
  EVERY (λprompt. case prompt of Prompt_i1 mn ds => prompt_mods_ok mn ds) (prompt::prog)
  ⇒
  DISJOINT (FDOM exh2) (FDOM exh1)`,
 rw [] >>
 imp_res_tac FDOM_prompt_to_i2_exh >>
 imp_res_tac FDOM_prog_to_i2_exh >>
 rw [] >>
 fs [no_dup_mods_i1_eqn, no_dup_top_types_i1_eqn] >>
 every_case_tac >>
 fs [tids_of_prompt_def, LET_THM]
 >- (
   fs[IN_DISJOINT,decs_to_types_i1_def,prog_i1_to_top_types_def,
      tids_of_decs_def,tids_of_prog_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   spose_not_then strip_assume_tac >>
   every_case_tac >> fs[MEM_MAP] >> rw[] >>
   qmatch_assum_rename_tac`MEM (Dtype_i1 mno tds) decs` >>
   qmatch_assum_rename_tac`MEM td tds` >>
   PairCases_on`td` >>
   first_x_assum(qspec_then`td1`mp_tac) >> simp[PULL_EXISTS] >>
   HINT_EXISTS_TAC >> simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   qmatch_assum_rename_tac`MEM prompt prog` >>
   Cases_on`prompt`>>fs[tids_of_prompt_def] >>
   HINT_EXISTS_TAC >> simp[] >>
   fs[EVERY_MEM] >> res_tac >> fs[] >>
   fs[prompt_mods_ok_def,EVERY_MEM] >>
   res_tac >> fs[mk_id_def] >>
   BasicProvers.CASE_TAC >- (
     simp[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
     simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     rw[] >>
     every_case_tac >> fs[] >>
     fs[MEM_MAP] >>
     HINT_EXISTS_TAC >> simp[MEM_MAP,EXISTS_PROD] >>
     PairCases_on`y`>>Cases_on`o'`>>fs[mk_id_def]>>metis_tac[]) >>
   qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
   simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   spose_not_then strip_assume_tac >>
   every_case_tac >> fs[] >>
   res_tac >> fs[MEM_MAP,mk_id_def] )
 >- (
   pop_assum kall_tac >>
   fs[IN_DISJOINT,tids_of_decs_def,tids_of_prog_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   spose_not_then strip_assume_tac >> every_case_tac >> fs[] >>
   fs[prompt_mods_ok_def,EVERY_MEM] >> res_tac >> fs[] >>
   fs[MEM_MAP,mk_id_def] >> rw[] >>
   qmatch_assum_rename_tac`MEM p prog` >>
   Cases_on`p`>>fs[tids_of_prompt_def] >>
   qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
   simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   spose_not_then strip_assume_tac >>
   pop_assum mp_tac >> BasicProvers.CASE_TAC >> fs[MEM_MAP] >>
   res_tac >> fs[] >> rw[] >>
   every_case_tac >> fs[mk_id_def] >>
   spose_not_then strip_assume_tac >> rw[] >>
   fs[prog_i1_to_mods_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   qmatch_assum_abbrev_tac`MEM p prog` >>
   first_x_assum(qspec_then`p`mp_tac) >>
   simp[Abbr`p`]));

val exh_disjoint2 = Q.prove (
`prog_to_i2 (next2,tagenv2,inv2) prog = ((next',tagenv',inv''),exh1,ps1)  ∧
  (∀x. Short x ∈ FDOM exh ⇒ TypeId (Short x) ∈ tids) ∧
  (∀mn x. Long mn x ∈ FDOM exh ⇒ mn ∈ mods) ∧
  no_dup_mods_i1 (prompt::prog) (s:v_i1 count_store,tids,mods) ∧
  no_dup_top_types_i1 (prompt::prog) (s,tids,mods) ∧
  EVERY (λprompt. case prompt of Prompt_i1 mn ds => prompt_mods_ok mn ds) (prompt::prog)
  ⇒
  DISJOINT (FDOM exh) (FDOM exh1)`,
 rw [] >>
 imp_res_tac FDOM_prog_to_i2_exh >>
 rw [] >>
 fs [no_dup_mods_i1_eqn, no_dup_top_types_i1_eqn] >>
 every_case_tac >>
 fs [tids_of_prompt_def]
 >- (
   fs[IN_DISJOINT] >>
   spose_not_then strip_assume_tac >>
   Cases_on`x` >- (
     rator_x_assum`no_dup_top_types_i1`mp_tac >>
     res_tac >> simp[no_dup_top_types_i1_def] >>
     simp[IN_DISJOINT,MEM_MAP,PULL_EXISTS] >>
     fs[tids_of_prog_def,prog_i1_to_top_types_def,MEM_MAP,MEM_FLAT,PULL_EXISTS] >>
     disj2_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     BasicProvers.CASE_TAC >> fs[tids_of_prompt_def] >>
     BasicProvers.CASE_TAC >> simp[] >- (
       fs[tids_of_decs_def,decs_to_types_i1_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       every_case_tac >> fs[] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       fs[MEM_MAP,PULL_EXISTS] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[UNCURRY] >>
       qmatch_assum_rename_tac`Short a = mk_id mno _` >>
       Cases_on`mno`>>fs[mk_id_def] ) >>
     fs[EVERY_MEM] >>
     res_tac >> fs[] >>
     fs[prompt_mods_ok_def] >>
     fs[EVERY_MEM,tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     every_case_tac >> fs[] >>
     res_tac >> fs[MEM_MAP,mk_id_def]) >>
   fs[no_dup_mods_i1_def,IN_DISJOINT] >> res_tac >>
   fs[prog_i1_to_mods_def,tids_of_prog_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   qmatch_assum_rename_tac`mn ∈ mods` >>
   first_x_assum(qspec_then`mn`mp_tac) >>
   first_x_assum(qspec_then`mn`mp_tac) >>
   qmatch_assum_rename_tac`MEM prompt prog` >>
   Cases_on`prompt`>>fs[tids_of_prompt_def] >>
   strip_tac >>
   qmatch_assum_abbrev_tac`MEM p prog` >>
   first_x_assum(qspec_then`p`mp_tac) >> simp[Abbr`p`] >>
   BasicProvers.CASE_TAC >> simp[] >- (
     fs[EVERY_MEM] >> res_tac >> fs[prompt_mods_ok_def,EVERY_MEM] >>
     fs[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     every_case_tac >> fs[] >>
     res_tac >> fs[MEM_MAP,mk_id_def] ) >>
   strip_tac >>
   fs[EVERY_MEM] >> res_tac >> fs[prompt_mods_ok_def,EVERY_MEM] >>
   fs[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   every_case_tac >> fs[] >>
   res_tac >> fs[MEM_MAP,mk_id_def] >> rw[] )
 >- (
   fs[IN_DISJOINT] >>
   spose_not_then strip_assume_tac >>
   qmatch_assum_rename_tac`z ∈ FDOM exh` >>
   Cases_on`z` >- (
     rator_x_assum`no_dup_top_types_i1`mp_tac >>
     res_tac >> simp[no_dup_top_types_i1_def] >>
     simp[IN_DISJOINT,MEM_MAP,PULL_EXISTS] >>
     fs[tids_of_prog_def,prog_i1_to_top_types_def,MEM_MAP,MEM_FLAT,PULL_EXISTS] >>
     disj2_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     BasicProvers.CASE_TAC >> fs[tids_of_prompt_def] >>
     BasicProvers.CASE_TAC >> simp[] >- (
       fs[tids_of_decs_def,decs_to_types_i1_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       every_case_tac >> fs[] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       fs[MEM_MAP,PULL_EXISTS] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[UNCURRY] >>
       qmatch_assum_rename_tac`Short a = mk_id mno _` >>
       Cases_on`mno`>>fs[mk_id_def] ) >>
     fs[EVERY_MEM] >>
     res_tac >> fs[] >>
     fs[prompt_mods_ok_def] >>
     fs[EVERY_MEM,tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     every_case_tac >> fs[] >>
     res_tac >> fs[MEM_MAP,mk_id_def]) >>
   fs[no_dup_mods_i1_def,IN_DISJOINT] >> res_tac >>
   fs[prog_i1_to_mods_def,tids_of_prog_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   qmatch_assum_rename_tac`mn ∈ mods` >>
   first_x_assum(qspec_then`mn`mp_tac) >>
   qmatch_assum_rename_tac`MEM prompt prog` >>
   Cases_on`prompt`>>fs[tids_of_prompt_def] >>
   qmatch_assum_abbrev_tac`MEM p prog` >>
   first_x_assum(qspec_then`p`mp_tac) >> simp[Abbr`p`] >>
   BasicProvers.CASE_TAC >> simp[] >- (
     fs[EVERY_MEM] >> res_tac >> fs[prompt_mods_ok_def,EVERY_MEM] >>
     fs[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     every_case_tac >> fs[] >>
     res_tac >> fs[MEM_MAP,mk_id_def] ) >>
   strip_tac >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   fs[EVERY_MEM] >> res_tac >> fs[prompt_mods_ok_def,EVERY_MEM] >>
   fs[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   every_case_tac >> fs[] >>
   res_tac >> fs[MEM_MAP,mk_id_def] >> rw[] ));

val prog_to_i2_correct = Q.store_thm ("prog_to_i2_correct",
`!ck genv envC s_tmp prog res_tmp.
  evaluate_prog_i1 ck genv envC s_tmp prog res_tmp ⇒
  !s tids mods s_i2 genv_i2 next tagenv inv prog_i2 genv' envC' s' tids' mods' res gtagenv next' tagenv' inv' exh exh'.
  s_tmp = (s,tids,mods) ∧
  res_tmp = ((s',tids',mods'), envC', genv', res) ∧
  res ≠ SOME Rtype_error ∧
  to_i2_invariant mods tids envC exh (next,tagenv,inv) gtagenv s s_i2 genv genv_i2 ∧
  no_dup_mods_i1 prog s_tmp ∧
  no_dup_top_types_i1 prog s_tmp ∧
  EVERY (λp. case p of Prompt_i1 mn ds => prompt_mods_ok mn ds) prog ∧
  ((next',tagenv',inv'), exh', prog_i2) = prog_to_i2 (next,tagenv,inv) prog
  ⇒
  ?genv'_i2 s'_i2 res_i2 gtagenv'.
    DISJOINT (FDOM exh) (FDOM exh') ∧
    gtagenv_weak gtagenv gtagenv' ∧
    evaluate_prog_i2 ck (FUNION exh' exh) genv_i2 s_i2 prog_i2 (s'_i2,genv'_i2,res_i2) ∧
    (res = NONE ∧ res_i2 = NONE ∧
     to_i2_invariant mods' tids' (merge_alist_mod_env envC' envC) (FUNION exh' exh) (next',tagenv',inv') gtagenv' s' s'_i2 (genv++genv') (genv_i2++genv'_i2) ∨
     ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ result_to_i2 (\a b c. T) gtagenv' (Rerr err) (Rerr err_i2))`,
 ho_match_mp_tac evaluate_prog_i1_strongind >>
 rw []
 >- (PairCases_on `envC` >>
     fs [merge_alist_mod_env_def, prog_to_i2_def] >>
     rw [Once evaluate_prog_i2_cases, FUNION_FEMPTY_1] >>
     fs [to_i2_invariant_def] >>
     metis_tac [gtagenv_weak_refl, cenv_inv_def])
 >- (fs [prog_to_i2_def, LET_THM] >>
     `?st2 exh2 p2. prompt_to_i2 (next,tagenv,inv') prompt = (st2,exh2,p2)`
             by metis_tac [pair_CASES] >>
     fs [] >>
     `?st1 exh1 ps1. prog_to_i2 st2 prog = (st1,exh1,ps1)`
             by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     `?s1 tids1 mods1. s_tmp' = (s1,tids1,mods1)` by metis_tac [pair_CASES] >>
     rw [Once evaluate_prog_i2_cases] >>
     `?next2 tagenv2 inv2. st2 = (next2, tagenv2, inv2)` by metis_tac [pair_CASES] >>
     rw [] >>
    (prompt_to_i2_correct |> REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
     simp[] >>
     disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
     simp[] >>
     disch_then(qx_choosel_then[`genv'_i2`,`s'_i2`,`gtagenv'`]strip_assume_tac) >>
     rfs[] >>
     first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
     simp[] >>
     `DISJOINT (FDOM exh2) (FDOM exh1)` by (
       MATCH_MP_TAC exh_disjoint1 >> simp[] ) >>
     `DISJOINT (FDOM exh) (FDOM exh1)`
              by (fs [to_i2_invariant_def] >>
                  match_mp_tac exh_disjoint2 >>
                  simp[] >> metis_tac[]) >>
     fs [no_dup_mods_i1_eqn, no_dup_top_types_i1_eqn] >>
      discharge_hyps >- (
       imp_res_tac evaluate_prompt_i1_mods_disjoint >>
       Cases_on`prompt`>>fs[Once evaluate_prompt_i1_cases,update_mod_state_def] >>
       fs[no_dup_mods_i1_def] >>
       BasicProvers.CASE_TAC>>fs[DISJOINT_SYM] ) >>
     discharge_hyps >- (
       imp_res_tac evaluate_prompt_i1_tids >> fs[] >>
       rator_x_assum`no_dup_top_types_i1`mp_tac >>
       simp[no_dup_top_types_i1_def,GSYM AND_IMP_INTRO] >>
       strip_tac >>
       simp[IN_DISJOINT,MEM_MAP,PULL_EXISTS] >> strip_tac >>
       spose_not_then strip_assume_tac >>
       first_x_assum(qspec_then`TypeId(Short tn)`mp_tac) >>
       simp[] >>
       qpat_assum`A = y ∪ z`mp_tac >>
       simp[EXTENSION] >> rw[] >>
       first_x_assum(qspec_then`(Short tn)`mp_tac) >>
       rw[] >>
       Cases_on`prompt`>>fs[tids_of_prompt_def] >>
       rator_x_assum`prompt_mods_ok`mp_tac >>
       simp[prompt_mods_ok_def] >>
       BasicProvers.CASE_TAC >> fs[] >- (
         fs[IN_DISJOINT] >> rw[] >>
         first_x_assum(qspec_then`tn`mp_tac) >>
         simp[decs_to_types_i1_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
         qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
         simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,PULL_FORALL] >>
         gen_tac >> strip_tac >>
         every_case_tac >> fs[] >> fs[MEM_MAP] >> rw[] >>
         qmatch_assum_abbrev_tac`MEM d l` >>
         first_x_assum(qspec_then`d`mp_tac) >>
         simp[Abbr`d`,MEM_MAP,FORALL_PROD] >>
         qmatch_assum_rename_tac`MEM (Dtype_i1 mno tds) decs` >>
         Cases_on`mno`>>fs[mk_id_def]>>
         qmatch_assum_rename_tac`MEM p tds` >>
         PairCases_on`p`>>fs[] >> metis_tac[] ) >>
       simp[EVERY_MEM] >>
       qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
       simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >> rw[] >>
       every_case_tac >> fs[] >>
       res_tac >> fs[mk_id_def,MEM_MAP] ) >>
     rw[]
       >- (MAP_EVERY qexists_tac [`genv'_i2 ++ genv'_i2'`, `s'_i2'`, `gtagenv''`] >>
           rw [] >>
           fs [merge_alist_mod_env_assoc, FUNION_ASSOC]
           >- metis_tac[DISJOINT_SYM]
           >- metis_tac [gtagenv_weak_trans]
           >- (`DISJOINT (FDOM exh1) (FDOM (FUNION exh2 exh))` 
                  by rw [FDOM_FUNION, DISJOINT_UNION_BOTH] >>
               metis_tac [evaluate_prompt_i2_exh_weak, FUNION_ASSOC, NOT_SOME_NONE]))
       >- (MAP_EVERY qexists_tac [`genv'_i2 ++ genv'_i2'`, `s'_i2'`, `SOME err_i2`, `gtagenv''`] >>
           rw [] >>
           fs [merge_alist_mod_env_assoc, FUNION_ASSOC]
           >- metis_tac[DISJOINT_SYM]
           >- metis_tac [gtagenv_weak_trans]
           >- (`DISJOINT (FDOM exh1) (FDOM (FUNION exh2 exh))` 
                  by rw [FDOM_FUNION, DISJOINT_UNION_BOTH] >>
               metis_tac [evaluate_prompt_i2_exh_weak, FUNION_ASSOC, NOT_SOME_NONE])))
 >- (fs [prog_to_i2_def, LET_THM] >>
     `?st2 exh2 p2. prompt_to_i2 (next,tagenv,inv') prompt = (st2,exh2,p2)`
             by metis_tac [pair_CASES] >>
     fs [] >>
     `?st1 exh1 ps1. prog_to_i2 st2 prompts = (st1,exh1,ps1)`
             by metis_tac [pair_CASES] >>
     fs [] >>
     rw [Once evaluate_prog_i2_cases] >>
     (prompt_to_i2_correct |> REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
     simp[] >>
     disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
     simp[] >>
     simp[PULL_EXISTS] >>
     map_every qx_gen_tac[`genv'_i2`,`s'_i2`,`gtagenv'`,`err_i2`] >>
     strip_tac >>
     MAP_EVERY qexists_tac [`genv'_i2`, `s'_i2`, `gtagenv'`, `err_i2`] >>
     `DISJOINT (FDOM exh2) (FDOM exh1)` by (
       match_mp_tac (GEN_ALL exh_disjoint1) >>
       simp[] >>
       PairCases_on`st2` >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       first_assum(match_exists_tac o concl) >> simp[]) >>
     `DISJOINT (FDOM exh) (FDOM exh1)`
              by (fs [to_i2_invariant_def] >>
                  match_mp_tac (GEN_ALL exh_disjoint2) >>
                  PairCases_on`st2` >>
                  first_assum(match_exists_tac o concl) >> simp[] >>
                  metis_tac[]) >>
     `DISJOINT (FDOM exh1) (FDOM (FUNION exh2 exh))`
                  by rw [FDOM_FUNION, DISJOINT_UNION_BOTH] >>
     rw [] >- metis_tac[DISJOINT_SYM] >>
     disj2_tac >>
     ONCE_REWRITE_TAC[GSYM(FUNION_ASSOC)] >>
     match_mp_tac evaluate_prompt_i2_exh_weak >>
     fs[result_to_i2_cases] >> fs[]));

val whole_prog_to_i2_correct = Q.store_thm ("whole_prog_to_i2_correct",
`!ck genv envC prog s tids mods s_i2 genv_i2 next tagenv inv prog_i2 genv' envC' s' tids' mods' res gtagenv next' tagenv' inv' exh exh'.
  evaluate_whole_prog_i1 ck genv envC (s,tids,mods) prog ((s',tids',mods'), envC', genv', res) ∧
  res ≠ SOME Rtype_error ∧
  to_i2_invariant mods tids envC exh (next,tagenv,inv) gtagenv s s_i2 genv genv_i2 ∧
  ((next',tagenv',inv'), exh', prog_i2) = prog_to_i2 (next,tagenv,inv) prog
  ⇒
  ?genv'_i2 s'_i2 res_i2 gtagenv'.
    DISJOINT (FDOM exh) (FDOM exh') ∧
    gtagenv_weak gtagenv gtagenv' ∧
    evaluate_prog_i2 ck (FUNION exh' exh) genv_i2 s_i2 prog_i2 (s'_i2,genv'_i2,res_i2) ∧
    (res = NONE ∧ res_i2 = NONE ∧
     to_i2_invariant mods' tids' (merge_alist_mod_env envC' envC) (FUNION exh' exh) (next',tagenv',inv') gtagenv' s' s'_i2 (genv++genv') (genv_i2++genv'_i2) ∨
     ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ result_to_i2 (\a b c. T) gtagenv' (Rerr err) (Rerr err_i2))`,
 rw [evaluate_whole_prog_i1_def] >>
 match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] prog_to_i2_correct) >>
 metis_tac []);

val _ = export_theory ();

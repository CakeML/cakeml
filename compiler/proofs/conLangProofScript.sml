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

val same_tid_diff_ctor = Q.prove (
`!cn1 cn2 t1 t2.
  same_tid t1 t2 ∧ ~same_ctor (cn1, t1) (cn2, t2)
  ⇒
  (cn1 ≠ cn2) ∨ (cn1 = cn2 ∧ ?mn1 mn2. t1 = TypeExn mn1 ∧ t2 = TypeExn mn2 ∧ mn1 ≠ mn2)`,
srw_tac[][] >>
cases_on `t1` >>
cases_on `t2` >>
full_simp_tac(srw_ss())[same_tid_def, same_ctor_def]);

val build_rec_env_i2_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. ((f, Recclosure_i2 env funs' f) :: env')) env' funs =
MAP (λ(fn,n,e). (fn, Recclosure_i2 env funs' fn)) funs ++ env'`,
Induct >>
srw_tac[][] >>
PairCases_on `h` >>
srw_tac[][]);

val build_rec_env_i2_merge = Q.store_thm ("build_rec_env_i2_merge",
`∀funs funs' env env'.
  build_rec_env_i2 funs env env' =
  MAP (λ(fn,n,e). (fn, Recclosure_i2 env funs fn)) funs ++ env'`,
srw_tac[][build_rec_env_i2_def, build_rec_env_i2_help_lem]);

val funs_to_i2_map = Q.prove (
`!funs.
  funs_to_i2 cenv funs = MAP (\(f,x,e). (f,x,exp_to_i2 cenv e)) funs`,
 induct_on `funs` >>
 srw_tac[][exp_to_i2_def] >>
 PairCases_on `h` >>
 srw_tac[][exp_to_i2_def]);

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
  (∀cn l. FLOOKUP gtagenv cn ≠ SOME (tuple_tag,l)) ∧
  has_exns gtagenv ∧
  has_bools gtagenv ∧
  has_lists gtagenv ∧
  (∀t1 t2 tag l1 l2 cn cn'.
    (* Comment out same_tid because we're not using separate tag spaces per type *)
    (* same_tid t1 t2 ∧ *)
    FLOOKUP gtagenv (cn,t1) = SOME (tag,l1) ∧
    FLOOKUP gtagenv (cn',t2) = SOME (tag,l2) ⇒
    cn = cn' ∧ t1 = t2)`;

val envC_tagged_def = Define `
envC_tagged envC tagenv gtagenv =
  (!cn num_args t.
    lookup_alist_mod_env cn envC = SOME (num_args, t)
    ⇒
    ?tag t'.
      lookup_tag_env (SOME cn) tagenv = (tag, t') ∧
      FLOOKUP gtagenv (id_to_n cn, t) = SOME (tag,num_args) ∧
      (if tag = tuple_tag then t' = NONE else t' = SOME t))`;

val exhaustive_env_correct_def = Define `
exhaustive_env_correct (exh:exh_ctors_env) gtagenv ⇔
  (∀t. t ∈ FRANGE exh ⇒ wf t) ∧
  (!t.
     (?cn. (cn, TypeId t) ∈ FDOM gtagenv)
     ⇒
     ?tags.
       FLOOKUP exh t = SOME tags ∧
       (!cn tag l. FLOOKUP gtagenv (cn,TypeId t) = SOME (tag,l) ⇒ tag ∈ domain tags))`;

val cenv_inv_def = Define `
cenv_inv envC exh tagenv gtagenv ⇔
 envC_tagged envC tagenv gtagenv ∧
 exhaustive_env_correct exh gtagenv ∧
 gtagenv_wf gtagenv`;

val (v_to_i2_rules, v_to_i2_ind, v_to_i2_cases) = Hol_reln `
(!gtagenv lit.
  v_to_i2 gtagenv (Litv_i1 lit) (Litv_i2 lit)) ∧
(!gtagenv vs vs'.
  vs_to_i2 gtagenv vs vs'
  ⇒
  v_to_i2 gtagenv (Conv_i1 NONE vs) (Conv_i2 (tuple_tag,NONE) vs')) ∧
(!gtagenv cn tn tag vs vs'.
  FLOOKUP gtagenv (cn,tn) = SOME (tag, LENGTH vs) ∧
  vs_to_i2 gtagenv vs vs'
  ⇒
  v_to_i2 gtagenv (Conv_i1 (SOME (cn,tn)) vs) (Conv_i2 (tag,SOME tn) vs')) ∧
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
    (?vs' tag gtagenv' t'.
       vs_to_i2 gtagenv vs vs' ∧ (v = Conv_i2 (tag,t') vs') ∧
       (cn = NONE ∧ tag = tuple_tag ∧ t' = NONE ∨
        ?cn' tn.
          FLOOKUP gtagenv (cn',tn) = SOME (tag,LENGTH vs) ∧
          cn = SOME (cn',tn) ∧ t' = SOME tn))) ∧
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
srw_tac[][] >>
srw_tac[][Once v_to_i2_cases] >>
metis_tac []);

val vs_to_i2_list_rel = Q.prove (
`!gtagenv vs vs'. vs_to_i2 gtagenv vs vs' = LIST_REL (v_to_i2 gtagenv) vs vs'`,
 induct_on `vs` >>
 srw_tac[][v_to_i2_eqns] >>
 metis_tac []);

val gtagenv_weak_def = Define `
gtagenv_weak gtagenv1 gtagenv2 ⇔
  gtagenv1 SUBMAP gtagenv2 ∧
  (!cn l. FLOOKUP gtagenv2 cn ≠ SOME (tuple_tag,l)) ∧
  (* Don't weaken by adding a constructor to an existing type. This is necessary for pattern exhaustiveness checking. *)
  (!t. (?cn. (cn,t) ∈ FDOM gtagenv1) ⇒ !cn. (cn,t) ∈ FDOM gtagenv2 ⇒ (cn,t) ∈ FDOM gtagenv1) ∧
  (!t1 t2 tag cn cn' l1 l2.
     (* Comment out same_tid because we're not using separate tag spaces per type *)
     (* same_tid t1 t2 ∧ *)
     FLOOKUP gtagenv2 (cn,t1) = SOME (tag,l1) ∧
     FLOOKUP gtagenv2 (cn',t2) = SOME (tag,l2)
     ⇒
     cn = cn' ∧ t1 = t2)`;

val gtagenv' = ``(gtagenv':'a # tid_or_exn |-> num # num)``

val weakened_exh_def = Define`
  ((weakened_exh ^gtagenv' (exh:exh_ctors_env)):exh_ctors_env) =
    FUN_FMAP (λt. (FOLDL (λs n. insert n () s) LN
                    (SET_TO_LIST ({tag | ∃cn l. FLOOKUP gtagenv' (cn, TypeId t) = SOME (tag,l)} ∪
                                  case FLOOKUP exh t of NONE => {} | SOME tags => domain tags))))
      { t | ∃cn. (cn, TypeId t) ∈ FDOM gtagenv' }`

val FINITE_weakened_exh_dom = prove(
  ``FINITE {t | ∃cn. (cn,TypeId t) ∈ FDOM ^gtagenv'}``,
  qmatch_abbrev_tac`FINITE P` >>
  qsuff_tac`∃f. P ⊆ IMAGE f (FDOM gtagenv')` >-
    metis_tac[IMAGE_FINITE,SUBSET_FINITE,FDOM_FINITE] >>
  simp[Abbr`P`,SUBSET_DEF] >>
  qexists_tac`λx. @y. SND x = TypeId y` >>
  srw_tac[][EXISTS_PROD] >> metis_tac[tid_or_exn_11]);

val FDOM_weakened_exh = prove(
  ``FDOM (weakened_exh ^gtagenv' exh) = { t | ∃cn. (cn, TypeId t) ∈ FDOM gtagenv' }``,
  srw_tac[][weakened_exh_def] >>
  (FUN_FMAP_DEF |> SPEC_ALL |> UNDISCH |> CONJUNCT1 |> DISCH_ALL |> GEN_ALL |> match_mp_tac) >>
  srw_tac[][FINITE_weakened_exh_dom]);

val FLOOKUP_weakened_exh_imp = prove(
  ``(FLOOKUP (weakened_exh ^gtagenv' exh) t = SOME tags) ⇒
    wf tags ∧
    (domain tags = {tag | ∃cn l. FLOOKUP gtagenv' (cn, TypeId t) = SOME (tag,l)} ∪
                   case FLOOKUP exh t of NONE => {} | SOME tags => domain tags)``,
  simp[Once FLOOKUP_DEF,FDOM_weakened_exh] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  simp[weakened_exh_def] >>
  qmatch_abbrev_tac`wf (FUN_FMAP f X ' t) ∧ Z` >>
  strip_assume_tac(
    Q.ISPEC`f:string id -> unit spt`(MATCH_MP FUN_FMAP_DEF FINITE_weakened_exh_dom)) >>
  full_simp_tac(srw_ss())[Abbr`X`,PULL_EXISTS,Abbr`Z`] >>
  simp[Once EXTENSION] >>
  res_tac >>
  pop_assum (SUBST1_TAC) >>
  simp[Abbr`f`] >> srw_tac[][] >- (
    match_mp_tac wf_nat_set_from_list >>
    srw_tac[][sptreeTheory.wf_def] ) >>
  qmatch_abbrev_tac`MEM x (SET_TO_LIST s) ⇔ Z` >>
  `FINITE s` by (
    simp[Abbr`s`,FLOOKUP_DEF] >>
    reverse conj_tac >- srw_tac[][] >>
    qmatch_abbrev_tac`FINITE P` >>
    qsuff_tac`∃f. P ⊆ IMAGE f (FDOM gtagenv')` >-
      metis_tac[IMAGE_FINITE,SUBSET_FINITE,FDOM_FINITE] >>
    simp[Abbr`P`,SUBSET_DEF,PULL_EXISTS] >>
    qexists_tac`λx. FST (gtagenv' ' x)` >>
    srw_tac[][EXISTS_PROD] >> metis_tac[FST]) >>
  pop_assum(strip_assume_tac o MATCH_MP (GSYM SET_TO_LIST_IN_MEM)) >>
  simp[Abbr`s`,Abbr`Z`]);

val exhaustive_env_weak = Q.prove (
`!gtagenv gtagenv' exh.
    exhaustive_env_correct exh gtagenv ∧
    gtagenv_weak gtagenv ^gtagenv'
    ⇒
    ?exh'.
      exhaustive_env_correct exh' gtagenv'`,
 srw_tac[][gtagenv_weak_def, exhaustive_env_correct_def] >>
 qexists_tac `weakened_exh gtagenv' exh ⊌ exh` >>
 conj_tac >- (
   ho_match_mp_tac IN_FRANGE_FUNION_suff >> simp[] >>
   srw_tac[][IN_FRANGE_FLOOKUP] >> imp_res_tac FLOOKUP_weakened_exh_imp) >>
 srw_tac[][] >>
 cases_on `?cn. (cn,TypeId t) ∈ FDOM gtagenv` >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][]
 >- (`(cn,TypeId t) ∈ FDOM gtagenv` by metis_tac [] >>
     `?tags. FLOOKUP exh t = SOME tags ∧
             ∀cn tag l. FLOOKUP gtagenv (cn,TypeId t) = SOME (tag,l) ⇒ tag ∈ domain tags` by metis_tac [] >>
     full_simp_tac(srw_ss())[FLOOKUP_FUNION] >>
     Cases_on `FLOOKUP (weakened_exh gtagenv' exh) t` >> simp[] >- (
       full_simp_tac(srw_ss())[FLOOKUP_DEF,FDOM_weakened_exh,PULL_EXISTS] ) >>
     imp_res_tac FLOOKUP_weakened_exh_imp >>
     srw_tac[][] >>
     `(cn'',TypeId t) ∈ FDOM gtagenv`
               by (full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
                   metis_tac [FLOOKUP_DEF]) >>
     `?tag l. FLOOKUP gtagenv (cn'',TypeId t) = SOME (tag,l)`
                by (full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
                    metis_tac [SUBMAP_DEF]) >>
     full_simp_tac(srw_ss())[Once EXTENSION] >> metis_tac[]) >>
  simp[FLOOKUP_FUNION] >>
  BasicProvers.CASE_TAC >- (
    full_simp_tac(srw_ss())[FLOOKUP_DEF,FDOM_weakened_exh] ) >>
  imp_res_tac FLOOKUP_weakened_exh_imp >>
  full_simp_tac(srw_ss())[Once EXTENSION] >> metis_tac[]);

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
 srw_tac[][v_to_i2_eqns] >>
 res_tac
 >- metis_tac [gtagenv_weak_def, FLOOKUP_SUBMAP]
 >- (full_simp_tac(srw_ss())[cenv_inv_def, gtagenv_wf_def, envC_tagged_def] >>
     imp_res_tac exhaustive_env_weak >>
     srw_tac[][Once v_to_i2_cases] >>
     MAP_EVERY qexists_tac [`exh'`, `tagenv`] >>
     full_simp_tac(srw_ss())[gtagenv_weak_def, cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >> 
     srw_tac[][]
     >- (res_tac >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (full_simp_tac(srw_ss())[has_exns_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (full_simp_tac(srw_ss())[has_bools_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (full_simp_tac(srw_ss())[has_lists_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- metis_tac []
     >- metis_tac [])
 >- (full_simp_tac(srw_ss())[cenv_inv_def, gtagenv_wf_def, envC_tagged_def] >>
     imp_res_tac exhaustive_env_weak >>
     srw_tac[][Once v_to_i2_cases] >>
     MAP_EVERY qexists_tac [`exh'`, `tagenv`] >>
     full_simp_tac(srw_ss())[gtagenv_weak_def, cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >> 
     srw_tac[][]
     >- (res_tac >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (full_simp_tac(srw_ss())[has_exns_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (full_simp_tac(srw_ss())[has_bools_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (full_simp_tac(srw_ss())[has_lists_def] >>
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
srw_tac[][result_to_i2_cases] >>
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
 srw_tac[][sv_to_i2_cases] >>
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
 srw_tac[][v_to_i2_eqns] >>
 srw_tac[][] >>
 metis_tac []);

val length_evaluate_list_i2 = Q.prove (
`!b env s gtagenv es s' vs.
  evaluate_list_i2 b env s (exps_to_i2 gtagenv es) (s', Rval vs)
  ⇒
  LENGTH es = LENGTH vs`,
 induct_on `es` >>
 srw_tac[][exp_to_i2_def] >>
 cases_on `vs` >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_i2_cases]) >>
 srw_tac[][] >>
 metis_tac []);

val env_to_i2_el = Q.prove (
`!gtagenv env env_i2.
  env_to_i2 gtagenv env env_i2 ⇔
  LENGTH env = LENGTH env_i2 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i2)) ∧ v_to_i2 gtagenv (SND (EL n env)) (SND (EL n env_i2))`,
 induct_on `env` >>
 srw_tac[][v_to_i2_eqns]
 >- (cases_on `env_i2` >>
     full_simp_tac(srw_ss())[]) >>
 PairCases_on `h` >>
 srw_tac[][v_to_i2_eqns] >>
 eq_tac >>
 srw_tac[][] >>
 srw_tac[][]
 >- (cases_on `n` >>
     full_simp_tac(srw_ss())[])
 >- (cases_on `n` >>
     full_simp_tac(srw_ss())[])
 >- (cases_on `env_i2` >>
     full_simp_tac(srw_ss())[] >>
     FIRST_ASSUM (qspecl_then [`0`] mp_tac) >>
     SIMP_TAC (srw_ss()) [] >>
     srw_tac[][] >>
     qexists_tac `SND h` >>
     srw_tac[][] >>
     FIRST_X_ASSUM (qspecl_then [`SUC n`] mp_tac) >>
     srw_tac[][]));

val vs_to_i2_lupdate = Q.prove (
`!gtagenv v n s v_i2 n s_i2.
  vs_to_i2 gtagenv s s_i2 ∧
  v_to_i2 gtagenv v v_i2
  ⇒
  vs_to_i2 gtagenv (LUPDATE v n s) (LUPDATE v_i2 n s_i2)`,
 induct_on `n` >>
 srw_tac[][v_to_i2_eqns, LUPDATE_def] >>
 cases_on `s` >>
 full_simp_tac(srw_ss())[v_to_i2_eqns, LUPDATE_def]);

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
 srw_tac[][v_to_i2_eqns] >>
 full_simp_tac(srw_ss())[store_lookup_def] >>
 cases_on `n` >>
 full_simp_tac(srw_ss())[] >>
 metis_tac []);

val pat_bindings_i2_accum = Q.store_thm ("pat_bindings_i2_accum",
`(!p acc. pat_bindings_i2 p acc = pat_bindings_i2 p [] ++ acc) ∧
 (!ps acc. pats_bindings_i2 ps acc = pats_bindings_i2 ps [] ++ acc)`,
 Induct >>
 srw_tac[][]
 >- srw_tac[][pat_bindings_i2_def]
 >- srw_tac[][pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]
 >- srw_tac[][pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]);

val pat_bindings_to_i2 = Q.prove (
`!tagenv p x. pat_bindings_i2 (pat_to_i2 tagenv p) x = pat_bindings p x`,
 ho_match_mp_tac pat_to_i2_ind >>
 srw_tac[][pat_bindings_def, pat_bindings_i2_def, pat_to_i2_def] >>
 induct_on `ps` >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[pat_bindings_def, pat_bindings_i2_def, pat_to_i2_def] >>
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
 srw_tac[][pmatch_i1_def, pmatch_i2_def, pat_to_i2_def, match_result_to_i2_def] >>
 full_simp_tac(srw_ss())[match_result_to_i2_def, v_to_i2_eqns] >>
 srw_tac[][pmatch_i2_def, match_result_to_i2_def]
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[]
     >- (`lookup_tag_env (SOME n) tagenv = (tag, if tag = tuple_tag then NONE else SOME t')`
                  by (full_simp_tac(srw_ss())[cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >>
                      res_tac >>
                      full_simp_tac(srw_ss())[] >>
                      metis_tac [length_vs_to_i2, SOME_11, same_ctor_and_same_tid, PAIR_EQ]) >>
         srw_tac[][pmatch_i2_def] >>
         full_simp_tac(srw_ss())[]
         >- (full_simp_tac(srw_ss())[cenv_inv_def,gtagenv_wf_def] >>
             metis_tac []) >>
         `(?tid. t' = TypeId tid) ∨ (?exid. t' = TypeExn exid)`
                    by (Cases_on `t'` >>
                        metis_tac []) >>
         srw_tac[][pmatch_i2_def]
         >- (`?tags. FLOOKUP exh tid = SOME tags ∧ tag ∈ domain tags`
                    by (full_simp_tac(srw_ss())[cenv_inv_def, exhaustive_env_correct_def, FLOOKUP_DEF] >>
                        srw_tac[][] >>
                        metis_tac []) >>
             srw_tac[][] >>
             metis_tac [])
         >- (full_simp_tac(srw_ss())[cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >>
             imp_res_tac same_ctor_and_same_tid >> srw_tac[][] >>
             imp_res_tac length_vs_to_i2 >>
             PROVE_TAC[ SOME_11, PAIR_EQ])
         >- metis_tac [tid_or_exn_11, SOME_11, PAIR_EQ]
         >- (full_simp_tac(srw_ss())[cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >>
             imp_res_tac same_ctor_and_same_tid >> srw_tac[][] >>
             imp_res_tac length_vs_to_i2 >>
             PROVE_TAC [SOME_11, PAIR_EQ]))
     >- (full_simp_tac(srw_ss())[cenv_inv_def, envC_tagged_def] >>
         res_tac >>
         srw_tac[][] >>
         `(?tid. t' = TypeId tid) ∨ (?exid. t' = TypeExn exid)`
                    by (Cases_on `t'` >>
                        metis_tac []) >>
         `(?tid. r = TypeId tid) ∨ (?exid. r = TypeExn exid)`
                    by (Cases_on `r` >>
                        metis_tac []) >>
         imp_res_tac same_tid_diff_ctor >>
         full_simp_tac(srw_ss())[same_tid_def] >>
         srw_tac[][] >>
         `tag' ≠ tuple_tag` by metis_tac [gtagenv_wf_def] >>
         full_simp_tac(srw_ss())[] >>
         srw_tac[][pmatch_i2_def]
         >- metis_tac [gtagenv_wf_def]
         >- metis_tac [gtagenv_wf_def]
         >- (`?tags. FLOOKUP exh tid = SOME tags ∧ tag ∈ domain tags`
                    by (full_simp_tac(srw_ss())[cenv_inv_def, exhaustive_env_correct_def, FLOOKUP_DEF] >>
                        srw_tac[][] >>
                        metis_tac []) >>
             srw_tac[][match_result_to_i2_def]  >>
             `?tags. FLOOKUP exh tid = SOME tags ∧ tag' ∈ domain tags`
                    by (full_simp_tac(srw_ss())[cenv_inv_def, exhaustive_env_correct_def, FLOOKUP_DEF] >>
                        srw_tac[][] >>
                        metis_tac []) >>
             full_simp_tac(srw_ss())[] >>
             srw_tac[][] >>
             full_simp_tac(srw_ss())[])
         >- metis_tac [gtagenv_wf_def]
         >- metis_tac [gtagenv_wf_def]
         >- srw_tac[][match_result_to_i2_def]
         >- metis_tac [tid_or_exn_11, gtagenv_wf_def]
         >- metis_tac [tid_or_exn_11, gtagenv_wf_def]
         >- srw_tac[][match_result_to_i2_def]))
 >- (PairCases_on `tagenv` >>
     full_simp_tac(srw_ss())[pmatch_i2_def, lookup_tag_env_def] >>
     srw_tac[][] >>
     metis_tac [length_vs_to_i2])
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[store_lookup_def] >>
     imp_res_tac LIST_REL_LENGTH >>
     full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
     full_simp_tac(srw_ss())[sv_to_i2_cases] >>
     res_tac >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     metis_tac [])
 >- (every_case_tac >>
     full_simp_tac(srw_ss())[match_result_to_i2_def] >>
     srw_tac[][] >>
     pop_assum mp_tac >>
     pop_assum mp_tac >>
     res_tac >>
     srw_tac[][] >>
     CCONTR_TAC >>
     full_simp_tac(srw_ss())[match_result_to_i2_def] >>
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
 srw_tac[][v_to_i2_eqns] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss())[v_to_i2_eqns]);

val env_to_i2_lookup = Q.prove (
`!gtagenv env x v env'.
  ALOOKUP env x = SOME v ∧
  env_to_i2 gtagenv env env'
  ⇒
  ?v'.
    v_to_i2 gtagenv v v' ∧
    ALOOKUP env' x = SOME v'`,
 induct_on `env` >>
 srw_tac[][] >>
 PairCases_on `h` >>
 full_simp_tac(srw_ss())[] >>
 cases_on `h0 = x` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[v_to_i2_eqns]);

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
 full_simp_tac(srw_ss())[OPTREL_def]);

val vs_to_i2_append1 = Q.prove (
`!gtagenv vs v vs' v'.
  vs_to_i2 gtagenv (vs++[v]) (vs'++[v'])
  ⇔
  vs_to_i2 gtagenv vs vs' ∧
  v_to_i2 gtagenv v v'`,
 induct_on `vs` >>
 srw_tac[][] >>
 cases_on `vs'` >>
 srw_tac[][v_to_i2_eqns]
 >- (cases_on `vs` >>
     srw_tac[][v_to_i2_eqns]) >>
 metis_tac []);

val vs_to_i2_append = Q.prove (
`!gtagenv vs1 vs1' vs2 vs2'.
  (LENGTH vs2 = LENGTH vs2' ∨ LENGTH vs1 = LENGTH vs1')
  ⇒
  (vs_to_i2 gtagenv (vs1++vs2) (vs1'++vs2') ⇔
   vs_to_i2 gtagenv vs1 vs1' ∧ vs_to_i2 gtagenv vs2 vs2')`,
 induct_on `vs1` >>
 srw_tac[][v_to_i2_eqns] >>
 eq_tac >>
 srw_tac[][] >>
 imp_res_tac length_vs_to_i2 >>
 full_simp_tac(srw_ss())[] >>
 cases_on `vs1'` >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
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
 srw_tac[][do_eq_i2_def, do_eq_i1_def, v_to_i2_eqns] >>
 srw_tac[][] >>
 srw_tac[][do_eq_i2_def, do_eq_i1_def, v_to_i2_eqns] >>
 imp_res_tac length_vs_to_i2 >>
 full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
 srw_tac[][]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac [cenv_inv_def, gtagenv_wf_def, SOME_11, PAIR_EQ, pair_CASES]
 >- metis_tac [cenv_inv_def, gtagenv_wf_def, SOME_11, PAIR_EQ, pair_CASES]
 >- metis_tac [cenv_inv_def, gtagenv_wf_def, SOME_11, PAIR_EQ, pair_CASES]
 >- metis_tac [cenv_inv_def, gtagenv_wf_def, SOME_11, PAIR_EQ, pair_CASES]
 >- metis_tac [cenv_inv_def, gtagenv_wf_def, SOME_11, PAIR_EQ, pair_CASES]
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def])
 >- (full_simp_tac(srw_ss())[Once v_to_i2_cases] >>
     srw_tac[][do_eq_i2_def]) >>
  res_tac >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 metis_tac []);

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
 srw_tac[][v_to_list_i1_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[v_to_i2_eqns, v_to_list_i2_def] >>
 srw_tac[][] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[v_to_i2_eqns, v_to_list_i2_def] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[gtagenv_wf_def, has_lists_def] >>
 res_tac >>
 full_simp_tac(srw_ss())[] >>
 metis_tac [NOT_SOME_NONE, SOME_11]);

val char_list_to_v_i2_correct = prove(
  ``gtagenv_wf gtagenv ⇒
    ∀ls. v_to_i2 gtagenv (char_list_to_v_i1 ls) (char_list_to_v_i2 ls)``,
  strip_tac >>
  Induct >> simp[char_list_to_v_i1_def,char_list_to_v_i2_def,v_to_i2_eqns] >>
  full_simp_tac(srw_ss())[gtagenv_wf_def,has_lists_def])

val v_i2_to_char_list_correct = Q.prove (
`!v1 v2 vs1.
  gtagenv_wf gtagenv ∧
  v_to_i2 gtagenv v1 v2 ∧
  v_i1_to_char_list v1 = SOME vs1
  ⇒
    v_i2_to_char_list v2 = SOME vs1`,
 ho_match_mp_tac v_i1_to_char_list_ind >>
 srw_tac[][v_i1_to_char_list_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[v_to_i2_eqns, v_i2_to_char_list_def] >>
 srw_tac[][] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[v_to_i2_eqns, v_i2_to_char_list_def] >>
 srw_tac[][] >>
 res_tac >>
 full_simp_tac(srw_ss())[gtagenv_wf_def, has_lists_def])

val v_to_i2_Boolv_i2 = store_thm("v_to_i2_Boolv_i2",
  ``gtagenv_wf gtagenv ⇒
    v_to_i2 gtagenv (Boolv_i1 b) (Boolv_i2 b) ∧
    (∀v. v_to_i2 gtagenv (Boolv_i1 b) v ⇔ (v = Boolv_i2 b)) ∧
    (∀v. v_to_i2 gtagenv v (Boolv_i2 b) ⇔ (v = Boolv_i1 b))``,
  srw_tac[][Once v_to_i2_cases,Boolv_i1_def,Boolv_i2_def,
     vs_to_i2_list_rel,gtagenv_wf_def,has_bools_def] >>
  srw_tac[][Once v_to_i2_cases] >>
  srw_tac[][Once v_to_i2_cases] >>
  metis_tac[])

val tac =
  full_simp_tac(srw_ss())[do_app_i1_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[vs_to_i2_list_rel] >>
  srw_tac[][do_app_i2_def] >>
  full_simp_tac(srw_ss())[LET_THM,store_lookup_def, store_alloc_def, store_assign_def, v_to_i2_eqns, result_to_i2_cases, prim_exn_i1_def, prim_exn_i2_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN,sv_to_i2_cases] >>
  res_tac >>
  full_simp_tac(srw_ss())[store_v_same_type_def] >>
  srw_tac[][EL_LUPDATE, v_to_i2_eqns] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[v_to_i2_eqns] >>
  srw_tac[][v_to_i2_eqns] >>
  full_simp_tac(srw_ss())[v_to_i2_Boolv_i2] >>
  TRY (full_simp_tac(srw_ss())[gtagenv_wf_def, has_exns_def] >> NO_TAC);

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
 srw_tac[][]
 >- tac
 >- tac
 >- (full_simp_tac(srw_ss())[do_app_i1_def] >>
     cases_on `vs` >>
     full_simp_tac(srw_ss())[] >>
     cases_on `t` >>
     full_simp_tac(srw_ss())[] >>
     cases_on `t'` >>
     full_simp_tac(srw_ss())[vs_to_i2_list_rel] >>
     srw_tac[][]
     >- (every_case_tac >>
         imp_res_tac do_eq_i2 >>
         srw_tac[][do_app_i2_def, result_to_i2_cases, v_to_i2_eqns, prim_exn_i1_def, prim_exn_i2_def] >>
         srw_tac[][] >> full_simp_tac(srw_ss())[v_to_i2_Boolv_i2] >>
         full_simp_tac(srw_ss())[gtagenv_wf_def, has_exns_def])
     >- (every_case_tac >>
         full_simp_tac(srw_ss())[]))
 >- tac
 >- tac
 >- tac
 >- tac
 >- tac
 >- (tac >>
     pop_assum mp_tac >>
     srw_tac[][])
 >- tac
 >- (tac >>
     pop_assum mp_tac >>
     srw_tac[][EL_LUPDATE] >>
     full_simp_tac(srw_ss())[LENGTH_LUPDATE] >>
     pop_assum mp_tac >>
     pop_assum mp_tac >>
     srw_tac[][])
 >- tac
 >- tac
 >- tac
 >- (
   tac >>
   simp[char_list_to_v_i2_correct] )
 >- (
   full_simp_tac(srw_ss())[do_app_i1_def]>>
   Cases_on`vs`>>full_simp_tac(srw_ss())[]>>
   Cases_on`t`>>full_simp_tac(srw_ss())[]>>
   TRY (cases_on `t'`) >>
   full_simp_tac(srw_ss())[vs_to_i2_list_rel] >> srw_tac[][] >- (
     every_case_tac >>
     imp_res_tac v_i2_to_char_list_correct >>
     full_simp_tac(srw_ss())[] >> srw_tac[][do_app_i2_def,result_to_i2_cases,v_to_i2_eqns]) >>
   every_case_tac >> full_simp_tac(srw_ss())[])
 >- tac
 >- (full_simp_tac(srw_ss())[do_app_i1_def] >>
     cases_on `vs` >>
     full_simp_tac(srw_ss())[] >>
     cases_on `t` >>
     full_simp_tac(srw_ss())[] >>
     TRY (cases_on `t'`) >>
     full_simp_tac(srw_ss())[vs_to_i2_list_rel] >>
     srw_tac[][]
     >- (every_case_tac >>
         imp_res_tac v_to_list_i2_correct >>
         srw_tac[][do_app_i2_def, result_to_i2_cases, v_to_i2_eqns, prim_exn_i1_def, prim_exn_i2_def] >>
         srw_tac[][])
     >- (every_case_tac >>
         full_simp_tac(srw_ss())[]))
 >- (tac >>
     full_simp_tac(srw_ss())[vs_to_i2_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][v_to_i2_eqns] >>
     rpt (pop_assum mp_tac) >>
     srw_tac[][]
     >- full_simp_tac(srw_ss())[gtagenv_wf_def, has_exns_def] >>
     full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
     FIRST_X_ASSUM match_mp_tac >>
     decide_tac)
 >- (tac >>
     full_simp_tac(srw_ss())[vs_to_i2_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     full_simp_tac(srw_ss())[])
 >- (tac >>
     full_simp_tac(srw_ss())[vs_to_i2_list_rel, LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE] >>
     srw_tac[][v_to_i2_eqns, vs_to_i2_list_rel, LIST_REL_EL_EQN])
 >- (tac >>
     full_simp_tac(srw_ss())[vs_to_i2_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][v_to_i2_eqns] >>
     rpt (pop_assum mp_tac) >>
     srw_tac[][]
     >- full_simp_tac(srw_ss())[gtagenv_wf_def, has_exns_def] >>
     full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
     FIRST_X_ASSUM match_mp_tac >>
     decide_tac)
 >- (tac >>
     full_simp_tac(srw_ss())[vs_to_i2_list_rel, LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE] >>
     srw_tac[][v_to_i2_eqns, vs_to_i2_list_rel, LIST_REL_EL_EQN])
 >- (tac >>
     full_simp_tac(srw_ss())[vs_to_i2_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][v_to_i2_eqns] >>
     rpt (pop_assum mp_tac) >>
     srw_tac[][]
     >- full_simp_tac(srw_ss())[gtagenv_wf_def, has_exns_def] >>
     full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
     srw_tac[][EL_LUPDATE] >>
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
 srw_tac[][do_opapp_i1_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[do_opapp_i2_def, vs_to_i2_list_rel] >>
 srw_tac[][]
 >- (qpat_assum `v_to_i2 a0 (Closure_i1 b0 c0 d0) e0` (mp_tac o SIMP_RULE (srw_ss()) [Once v_to_i2_cases]) >>
     srw_tac[][] >>
     srw_tac[][] >>
     qexists_tac `tagenv'` >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
     srw_tac[][v_to_i2_eqns, all_env_i1_to_genv_def, all_env_i2_to_genv_def, get_tagenv_def] >>
     full_simp_tac(srw_ss())[cenv_inv_def])
 >- (qpat_assum `v_to_i2 a0 (Recclosure_i1 b0 c0 d0) e0` (mp_tac o SIMP_RULE (srw_ss()) [Once v_to_i2_cases]) >>
     srw_tac[][] >>
     srw_tac[][] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[]
     >- (full_simp_tac(srw_ss())[find_recfun_lookup] >>
         induct_on `l` >>
         srw_tac[][] >>
         PairCases_on `h'` >>
         full_simp_tac(srw_ss())[exp_to_i2_def] >>
         every_case_tac >>
         full_simp_tac(srw_ss())[])
     >- (qexists_tac `tagenv'` >>
         srw_tac[][] >>
         full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
         srw_tac[][v_to_i2_eqns, all_env_i1_to_genv_def, all_env_i2_to_genv_def,
             build_rec_env_i1_merge, build_rec_env_i2_merge] >>
         full_simp_tac(srw_ss())[funs_to_i2_map]
         >- full_simp_tac(srw_ss())[cenv_inv_def]
         >- (match_mp_tac env_to_i2_append >>
             srw_tac[][funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, env_to_i2_el, EL_MAP] >>
             `?f x e. EL n l = (f,x,e)` by metis_tac [pair_CASES] >>
             srw_tac[][] >>
             srw_tac[][Once v_to_i2_cases] >>
             metis_tac [funs_to_i2_map])
         >- (full_simp_tac(srw_ss())[find_recfun_lookup] >>
             induct_on `l` >>
             srw_tac[][] >>
             PairCases_on `h'` >>
             full_simp_tac(srw_ss())[exp_to_i2_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[])
         >- (CCONTR_TAC >> full_simp_tac(srw_ss())[funs_to_i2_map] >>
             full_simp_tac(srw_ss())[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,FST_triple])
         >- (full_simp_tac(srw_ss())[find_recfun_lookup] >>
             induct_on `l` >>
             srw_tac[][] >>
             PairCases_on `h'` >>
             full_simp_tac(srw_ss())[exp_to_i2_def] >>
             every_case_tac >>
             full_simp_tac(srw_ss())[get_tagenv_def] >>
             srw_tac[][]))));

val lookup_tag_env_NONE = Q.prove (
`lookup_tag_env NONE tagenv = (tuple_tag, NONE)`,
PairCases_on `tagenv` >>
srw_tac[][lookup_tag_env_def]);

val Boolv_i2_11 = store_thm("Boolv_i2_11[simp]",
  ``Boolv_i2 b1 = Boolv_i2 b2 ⇔ (b1 = b2)``,
  EVAL_TAC >> srw_tac[][])

val Boolv_i1_11 = store_thm("Boolv_i1_11[simp]",
  ``Boolv_i1 b1 = Boolv_i1 b2 ⇔ (b1 = b2)``,
  EVAL_TAC >> srw_tac[][])

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
 srw_tac[][] >>
 srw_tac[][Once evaluate_i2_cases,exp_to_i2_def] >>
 TRY (Cases_on `err`) >>
 full_simp_tac(srw_ss())[result_to_i2_eqns, v_to_i2_eqns]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (* Constructor application *)
    (res_tac >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[env_all_to_i2_cases, build_conv_i1_def] >>
     srw_tac[][] >>
     MAP_EVERY qexists_tac [`s'_i2`, `Rval (Conv_i2 (lookup_tag_env cn tagenv) v')`] >>
     srw_tac[][] >>
     Cases_on `cn` >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][v_to_i2_eqns, lookup_tag_env_NONE] >>
     full_simp_tac(srw_ss())[all_env_i1_to_cenv_def] >>
     every_case_tac >>
     full_simp_tac(srw_ss())[get_tagenv_def] >>
     srw_tac[][v_to_i2_eqns] >>
     full_simp_tac(srw_ss())[cenv_inv_def, envC_tagged_def, gtagenv_wf_def, do_con_check_def] >>
     srw_tac[][] >>
     metis_tac [length_evaluate_list_i2, length_vs_to_i2, FST])
 >- metis_tac []
 >- (* Local variable lookup *)
    (full_simp_tac(srw_ss())[env_all_to_i2_cases, all_env_i2_to_env_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[all_env_i1_to_env_def] >>
     metis_tac [env_to_i2_lookup])
 >- (* Global variable lookup *)
    (full_simp_tac(srw_ss())[env_all_to_i2_cases, all_env_i2_to_genv_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[all_env_i1_to_genv_def] >>
     `n < LENGTH genv` by decide_tac >>
     `LENGTH genv_i2 = LENGTH genv` by metis_tac [LIST_REL_LENGTH] >>
     full_simp_tac(srw_ss())[EL_MAP] >>
     metis_tac [genv_to_i2_lookup])
 >- (srw_tac[][Once v_to_i2_cases] >>
     full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
     srw_tac[][all_env_i1_to_env_def, all_env_i2_to_env_def, all_env_i1_to_cenv_def] >>
     metis_tac [])
 >- (* Function application *)
    (pop_assum mp_tac >>
     srw_tac[][] >>
     res_tac >>
     srw_tac[][] >>
     `?genv envC env''. env = (genv,envC,env'')` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[all_env_i1_to_genv_def] >>
     `?tagenv env_i2'.
       env_all_to_i2 tagenv env' (FST env_i2, FST (SND env_i2), env_i2') gtagenv ∧
       do_opapp_i2 v'' = SOME (env_i2', exp_to_i2 tagenv e)`
                 by metis_tac [do_opapp_i2] >>
     full_simp_tac (srw_ss()++boolSimps.DNF_ss) [s_to_i2_cases] >>
     PairCases_on `s'` >>
     srw_tac[][] >>
     PairCases_on `env_i2` >>
     srw_tac[][] >>
     metis_tac [FST,SND])
 >- (* Function application *)
    (pop_assum mp_tac >>
     srw_tac[][] >>
     res_tac >>
     srw_tac[][] >>
     `?genv envC env''. env = (genv,envC,env'')` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[all_env_i1_to_genv_def] >>
     `?tagenv env_i2'.
       env_all_to_i2 tagenv env' (FST env_i2, FST (SND env_i2), env_i2') gtagenv ∧
       do_opapp_i2 v'' = SOME (env_i2', exp_to_i2 tagenv e)`
                 by metis_tac [do_opapp_i2] >>
     full_simp_tac (srw_ss()++boolSimps.DNF_ss) [s_to_i2_cases] >>
     PairCases_on `s'` >>
     srw_tac[][] >>
     PairCases_on `env_i2` >>
     srw_tac[][] >>
     metis_tac [FST,SND])
 >- (* Function application *)
    (res_tac >>
     srw_tac[][] >>
     `?genv envC env''. env = (genv,envC,env'')` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[all_env_i1_to_genv_def] >>
     `?tagenv env_i2'.
       env_all_to_i2 tagenv env' (FST env_i2, FST (SND env_i2), env_i2') gtagenv ∧
       do_opapp_i2 v'' = SOME (env_i2', exp_to_i2 tagenv e)`
                 by metis_tac [do_opapp_i2] >>
     full_simp_tac (srw_ss()++boolSimps.DNF_ss) [s_to_i2_cases] >>
     metis_tac [FST,SND])
 >- (* Primitive application *)
    (LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s_i2`, `gtagenv`] mp_tac) >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[s_to_i2_cases] >>
     srw_tac[][] >>
     `gtagenv_wf gtagenv` by full_simp_tac(srw_ss())[env_all_to_i2_cases, cenv_inv_def] >>
     imp_res_tac do_app_i2_correct >>
     srw_tac[][] >>
     PairCases_on `env_i2` >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (* If *)
    (full_simp_tac(srw_ss())[do_if_i2_def, do_if_i1_def] >>
     every_case_tac >>
     srw_tac[][] >>
     res_tac >>
     srw_tac[][] >>
     res_tac >>
     srw_tac[][] >>
     MAP_EVERY qexists_tac [`s'_i2''`, `r_i2`] >>
     srw_tac[][] >>
     disj1_tac >> full_simp_tac(srw_ss())[] >>
     `gtagenv_wf gtagenv` by(
       full_simp_tac(srw_ss())[Once env_all_to_i2_cases] >>
       full_simp_tac(srw_ss())[cenv_inv_def] )
     >- (qexists_tac `(Boolv_i2 F)` >>
         full_simp_tac(srw_ss())[v_to_i2_Boolv_i2, v_to_i2_eqns, exp_to_i2_def] >>
         metis_tac [])
     >- (qexists_tac `(Boolv_i2 T)` >>
         full_simp_tac(srw_ss())[v_to_i2_Boolv_i2, v_to_i2_eqns, exp_to_i2_def] >>
         metis_tac []))
 >- metis_tac []
 >- metis_tac []
 >- (* Match *)
   (pop_assum mp_tac >>
     res_tac >>
     srw_tac[][] >>
     FIRST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s'_i2'`, `v''`,
                                  `Conv_i2 (bind_tag,SOME (TypeExn (Short "Bind"))) []`, `gtagenv`] mp_tac) >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[cenv_inv_def, envC_tagged_def, gtagenv_wf_def, has_exns_def] >>
     pop_assum (fn _ => all_tac) >>
     pop_assum mp_tac >>
     srw_tac[][] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (* Let *)
    (`?exh' genv' env'. env_i2 = (exh',genv',env')` by metis_tac [pair_CASES] >>
     srw_tac[][] >>
     res_tac >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     `env_all_to_i2 tagenv (genv,cenv,opt_bind n v env) (exh',genv', opt_bind n v' env') gtagenv`
                by (full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
                    full_simp_tac(srw_ss())[opt_bind_def, v_to_i2_eqns] >>
                    srw_tac[][] >>
                    every_case_tac >>
                    full_simp_tac(srw_ss())[] >>
                    srw_tac[][v_to_i2_eqns]) >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (* Letrec *)
    (pop_assum mp_tac >>
     srw_tac[][] >>
     `?exh' genv' env'. env_i2 = (exh',genv',env')` by metis_tac [pair_CASES] >>
     srw_tac[][] >>
     `env_all_to_i2 tagenv (genv,cenv,build_rec_env_i1 funs (cenv,env) env)
                           (exh',genv',build_rec_env_i2 (funs_to_i2 tagenv funs) env' env')
                           gtagenv`
         by (full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
             srw_tac[][build_rec_env_i1_merge, build_rec_env_i2_merge] >>
             srw_tac[][] >>
             match_mp_tac env_to_i2_append >>
             srw_tac[][] >>
             srw_tac[][funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, env_to_i2_el, EL_MAP] >>
             `?f x e. EL n funs = (f,x,e)` by metis_tac [pair_CASES] >>
             srw_tac[][] >>
             srw_tac[][Once v_to_i2_cases] >>
             metis_tac [funs_to_i2_map]) >>
      res_tac >>
      MAP_EVERY qexists_tac [`s'_i2'`, `r_i2'`] >>
      srw_tac[][] >>
      disj1_tac >>
      srw_tac[][funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (pop_assum mp_tac >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[s_to_i2_cases, env_all_to_i2_cases] >>
     srw_tac[][] >>
     `match_result_to_i2 gtagenv (Match env')
            (pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2')`
                   by metis_tac [pmatch_to_i2_correct, match_result_distinct] >>
     cases_on `pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2'` >>
     full_simp_tac(srw_ss())[match_result_to_i2_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     FIRST_X_ASSUM (qspecl_then [`tagenv`, `gtagenv`, `exh`, `a`, `genv_i2`, `s''`] mp_tac) >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     MAP_EVERY qexists_tac [`(c, s'''')`, `r_i2`] >>
     metis_tac [pat_bindings_to_i2])
 >- (pop_assum mp_tac >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[s_to_i2_cases, env_all_to_i2_cases] >>
     srw_tac[][] >>
     `match_result_to_i2 gtagenv No_match
            (pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2')`
                   by metis_tac [pmatch_to_i2_correct, match_result_distinct] >>
     cases_on `pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2'` >>
     full_simp_tac(srw_ss())[match_result_to_i2_def] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     pop_assum mp_tac >>
     pop_assum (qspecl_then [`tagenv`, `(count',s'')`, `v_i2`, `err_v_i2`, `gtagenv`, `exh`, `env_i2'`, `genv_i2`] mp_tac) >>
     srw_tac[][] >>
     metis_tac [pat_bindings_to_i2]));

val alloc_tags_flat = Q.prove (
`!mn tagenv_st defs.
  alloc_tags mn tagenv_st defs =
  FOLDL (λst' (cn,l,t). alloc_tag t cn st') tagenv_st
        (FLAT (MAP (\(tvs,tn,ctors). (MAP (\(cn,ts). (cn, LENGTH ts, TypeId (mk_id mn tn))) ctors)) defs))`,
 induct_on `defs` >>
 srw_tac[][alloc_tags_def, LET_THM] >>
 PairCases_on `h` >>
 srw_tac[][LET_THM, alloc_tags_def, FOLDL_APPEND, FOLDL_MAP, LAMBDA_PROD]);

val alloc_tags_build_tdefs = Q.prove (
`!mn tagenv_st tdefs.
  alloc_tags mn tagenv_st tdefs =
  FOLDL (λst' (cn,l,t). alloc_tag t cn st') tagenv_st (REVERSE (build_tdefs mn tdefs))`,
 srw_tac[][alloc_tags_flat, FOLDL_FOLDR_REVERSE, build_tdefs_def, LAMBDA_PROD]);

val flat_alloc_tags_def = Define `
flat_alloc_tags next tdefs =
  MAP2 (\(cn,len,tid) tag. (cn,next + tag,SOME tid)) tdefs (COUNT_LIST (LENGTH tdefs))`;

val helper_lem = Q.prove (
`∀l1 l2.
  LENGTH l1 = LENGTH l2
  ⇒
  MAP (λ((cn,len,tid),tag). (cn,next + tag,SOME tid)) (ZIP (l1,MAP SUC l2)) =
  MAP (λ((cn,len,tid),tag). (cn,next + (tag + 1),SOME tid)) (ZIP (l1,l2))`,
 induct_on `l1` >>
 srw_tac[][] >>
 cases_on `l2` >>
 full_simp_tac(srw_ss())[] >>
 PairCases_on `h` >>
 srw_tac [ARITH_ss] []);


val flat_alloc_tags_cons = Q.prove (
`!next cn len tid tds.
  flat_alloc_tags next ((cn,len,tid)::tds) =
    (cn,next,SOME tid) :: flat_alloc_tags (next + 1) tds`,
 simp [flat_alloc_tags_def, COUNT_LIST_def, MAP2_ZIP, LENGTH_MAP, LENGTH_COUNT_LIST] >>
 metis_tac [helper_lem,LENGTH_MAP, LENGTH_COUNT_LIST]);

val get_next_def = Define `
get_next ((a,b,c),d) = a`;

val get_tagacc_def = Define `
get_tagacc ((a,b,c),d) = d`;

val alloc_tags_eqns = Q.prove (
`!mn tagenv_st tdefs.
  (get_next (alloc_tags mn tagenv_st tdefs) =
   get_next tagenv_st + LENGTH (REVERSE (build_tdefs mn tdefs))) ∧
  (get_tagenv (alloc_tags mn tagenv_st tdefs) =
   FOLDL (\tagenv (cn,tag). insert_tag_env cn tag tagenv)
         (get_tagenv tagenv_st)
         (flat_alloc_tags (get_next tagenv_st) (REVERSE (build_tdefs mn tdefs)))) ∧
  (get_tagacc (alloc_tags mn tagenv_st tdefs) =
   get_tagacc tagenv_st |++ flat_alloc_tags (get_next tagenv_st) (REVERSE (build_tdefs mn tdefs)))`,
 REWRITE_TAC [alloc_tags_build_tdefs] >>
 rpt GEN_TAC >>
 Q.SPEC_TAC (`REVERSE (build_tdefs mn tdefs)`, `tds`) >>
 Q.SPEC_TAC (`tagenv_st`, `tagenv_st`) >>
 induct_on `tds` >>
 simp []
 >- srw_tac[][flat_alloc_tags_def, COUNT_LIST_def, FUPDATE_LIST_THM, flat_alloc_tags_def, COUNT_LIST_def] >>
 srw_tac[][] >>
 PairCases_on `h` >>
 PairCases_on `tagenv_st` >>
 srw_tac [ARITH_ss] [alloc_tag_def, get_next_def, get_tagenv_def, get_tagacc_def, flat_alloc_tags_cons, FUPDATE_LIST_THM]);

val merge_alist_mod_env_empty = Q.prove (
`!mod_env. merge_alist_mod_env ([],[]) mod_env = mod_env`,
srw_tac[][] >>
PairCases_on `mod_env` >>
srw_tac[][merge_alist_mod_env_def]);

val lookup_tag_env_insert = Q.prove (
`(!cn tag tagenv. lookup_tag_env (SOME (Short cn)) (insert_tag_env cn tag tagenv) = tag) ∧
 (!cn cn' tag tagenv.
   cn' ≠ Short cn
   ⇒
   lookup_tag_env (SOME cn') (insert_tag_env cn tag tagenv) = lookup_tag_env (SOME cn') tagenv)`,
 srw_tac[][] >>
 PairCases_on `tagenv` >>
 srw_tac[][lookup_tag_env_def, insert_tag_env_def, lookup_tag_flat_def, FLOOKUP_UPDATE] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[]);

val gtagenv_weak_refl = Q.prove (
`!gtagenv envC tagenv.
  gtagenv_wf gtagenv
  ⇒
  gtagenv_weak gtagenv gtagenv`,
 srw_tac[][gtagenv_weak_def] >>
 metis_tac [SUBMAP_REFL, gtagenv_wf_def]);

val gtagenv_weak_trans = Q.prove (
`!gtagenv1 gtagenv2 gtagenv3.
  gtagenv_weak gtagenv1 gtagenv2 ∧
  gtagenv_weak gtagenv2 gtagenv3
  ⇒
  gtagenv_weak gtagenv1 gtagenv3`,
 srw_tac[][gtagenv_weak_def] >>
 full_simp_tac(srw_ss())[FLOOKUP_DEF, SUBMAP_DEF] >>
 metis_tac []);

val alloc_tags_invariant_def = Define `
alloc_tags_invariant tids tagenv_st gtagenv ⇔
  IMAGE SND (FDOM gtagenv) ⊆ tids ∧
  get_next tagenv_st > tuple_tag ∧
  (!cn t tag l. FLOOKUP gtagenv (cn,t) = SOME (tag,l) ⇒ get_next tagenv_st > tag) ∧
  (!cn tag t. FLOOKUP (get_tagacc tagenv_st) cn = SOME (tag,t) ⇒ get_next tagenv_st > tag)`;

val flat_envC_tagged_def = Define `
 flat_envC_tagged envC tagenv gtagenv ⇔
   ∀cn num_args t.
     ALOOKUP envC cn = SOME (num_args,t) ⇒
     ∃tag.
       lookup_tag_flat cn tagenv = tag ∧
       FLOOKUP gtagenv (cn,t) = SOME (FST tag,num_args) ∧
       if FST tag = tuple_tag then SND tag = NONE else SND tag = SOME t`;

val flat_envC_tagged_weakening = Q.prove (
`!envC tagenv gtagenv gtagenv'.
  flat_envC_tagged envC tagenv gtagenv ∧
  gtagenv_weak gtagenv gtagenv'
  ⇒
  flat_envC_tagged envC tagenv gtagenv'`,
 srw_tac[][flat_envC_tagged_def, gtagenv_weak_def] >>
 res_tac >>
 metis_tac [FLOOKUP_SUBMAP]);

val flat_envC_tagged_append = Q.prove (
`ALL_DISTINCT (MAP FST tagenv2) ∧
 set (MAP FST tagenv1) ⊆ set (MAP FST envC1) ∧
 (∀cn l. FLOOKUP gtagenv cn ≠ SOME (tuple_tag,l)) ∧
 flat_envC_tagged envC1 (FEMPTY |++ tagenv1) gtagenv ∧
 flat_envC_tagged envC2 (FEMPTY |++ REVERSE tagenv2) gtagenv
 ⇒
 flat_envC_tagged (envC1 ++ envC2) (FEMPTY |++ (tagenv2 ++ tagenv1)) gtagenv`,
 reverse(srw_tac[][flat_envC_tagged_def]) >- (
   imp_res_tac alookup_distinct_reverse >>
   full_simp_tac(srw_ss())[FLOOKUP_FUNION,lookup_tag_flat_def,flookup_fupdate_list, ALOOKUP_APPEND, REVERSE_APPEND] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >>
   TRY(first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >> NO_TAC) >>
   full_simp_tac(srw_ss())[flookup_thm] >>
   imp_res_tac ALOOKUP_MEM >>
   full_simp_tac(srw_ss())[ALOOKUP_FAILS, SUBSET_DEF,MEM_MAP,FORALL_PROD,PULL_EXISTS,EXISTS_PROD] >>
   metis_tac[] ) >>
 full_simp_tac(srw_ss())[FLOOKUP_FUNION, lookup_tag_flat_def, flookup_fupdate_list, ALOOKUP_APPEND] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[]
 >- (res_tac >>
     cases_on `ALOOKUP tagenv2 cn` >>
     full_simp_tac(srw_ss())[ALOOKUP_NONE] >>
     imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss())[MEM_REVERSE, MEM_MAP] >>
     metis_tac [FST])
 >- (res_tac >>
     cases_on `ALOOKUP (REVERSE tagenv1) cn` >>
     full_simp_tac(srw_ss())[ALOOKUP_NONE] >>
     imp_res_tac ALOOKUP_MEM >>
     full_simp_tac(srw_ss())[MEM_REVERSE, MEM_MAP] >>
     metis_tac [FST])
 >- (res_tac >>
     cases_on `ALOOKUP tagenv2 cn` >>
     full_simp_tac(srw_ss())[ALOOKUP_NONE, REVERSE_APPEND, ALOOKUP_APPEND] >>
     cases_on `ALOOKUP (REVERSE tagenv1) cn` >>
     full_simp_tac(srw_ss())[ALOOKUP_NONE, flookup_thm]
     >- (imp_res_tac ALOOKUP_MEM >>
         full_simp_tac(srw_ss())[MEM_REVERSE, MEM_MAP, REVERSE_APPEND] >>
         metis_tac [FST])
     >- (imp_res_tac ALOOKUP_MEM >>
         `MEM cn (MAP FST tagenv1)`
                    by (srw_tac[][MEM_MAP] >>
                        metis_tac [FST, MEM_REVERSE]) >>
         metis_tac [FST,SUBSET_DEF])
     >- ( PairCases_on`x`>>full_simp_tac(srw_ss())[] >>
          metis_tac [SOME_11, alookup_distinct_reverse,PAIR_EQ] )
     >- (imp_res_tac ALOOKUP_MEM >>
         `MEM cn (MAP FST tagenv1)`
                    by (srw_tac[][MEM_MAP] >>
                        metis_tac [FST, MEM_REVERSE]) >>
         metis_tac [FST,SUBSET_DEF]))
 >- (res_tac >>
     cases_on `ALOOKUP (REVERSE tagenv1) cn` >>
     full_simp_tac(srw_ss())[]
     >- (full_simp_tac(srw_ss())[ALOOKUP_NONE] >>
         `cn ∉ set (MAP FST envC1)` by full_simp_tac(srw_ss())[flookup_thm] >>
         metis_tac [flookup_thm, NOT_SOME_NONE,SUBSET_DEF])
     >- full_simp_tac(srw_ss())[REVERSE_APPEND, ALOOKUP_APPEND]));

val recfun_helper = Q.prove (
`cenv_inv envC exh tagenv gtagenv
 ⇒
 LIST_REL (OPTREL (v_to_i2 gtagenv))
          (MAP SOME (MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l))
          (MAP SOME (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 tagenv e)) l))`,
 induct_on `l` >>
 srw_tac[][] >>
 PairCases_on `h` >>
 srw_tac[][] >>
 srw_tac[][OPTREL_def] >>
 srw_tac[][Once v_to_i2_cases, v_to_i2_eqns] >>
 metis_tac []);

val recfun_helper2 = Q.prove (
`cenv_inv envC exh tagenv gtagenv
 ⇒
 vs_to_i2 gtagenv
          (MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l)
          (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 tagenv e)) l)`,
 induct_on `l` >>
 srw_tac[][v_to_i2_eqns] >>
 PairCases_on `h` >>
 srw_tac[][] >>
 srw_tac[][Once v_to_i2_cases] >>
 srw_tac[][v_to_i2_eqns] >>
 metis_tac []);

val alloc_tags_inv_weak = Q.prove (
`!tids tagenv_st gtagenv mn tdefs.
  alloc_tags_invariant tids (tagenv_st:tagenv_state) gtagenv ⇒
  alloc_tags_invariant tids (alloc_tags mn tagenv_st (tdefs:type_def)) gtagenv`,
 induct_on `tdefs` >>
 srw_tac[][alloc_tags_def] >>
 PairCases_on `h` >>
 srw_tac[][alloc_tags_def, LET_THM] >>
 FIRST_X_ASSUM match_mp_tac >>
 pop_assum mp_tac >>
 Q.SPEC_TAC (`tagenv_st`, `tagenv_st`) >>
 induct_on `h2` >>
 srw_tac[][alloc_tag_def] >>
 PairCases_on `h` >>
 srw_tac[][] >>
 FIRST_X_ASSUM match_mp_tac >>
 PairCases_on `tagenv_st` >>
 full_simp_tac(srw_ss())[alloc_tag_def, alloc_tags_invariant_def, get_next_def, get_tagacc_def, FLOOKUP_UPDATE] >>
 srw_tac[][] >> res_tac >> simp[])

val decs_to_i2_inv_weak = Q.prove (
`!tid tagenv_st gtagenv ds tagenv_st' ds_i2 tids exh'.
  alloc_tags_invariant tids tagenv_st gtagenv ∧
  decs_to_i2 tagenv_st ds = (tagenv_st',exh',ds_i2)
  ⇒
  alloc_tags_invariant tids tagenv_st' gtagenv`,
 induct_on `ds` >>
 srw_tac[][decs_to_i2_def] >>
 srw_tac[][] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[LET_THM]
 >- (`?tagenv_st' exh' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st',exh',ds_i2)` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     metis_tac [])
 >- (`?tagenv_st' exh' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st',exh',ds_i2)` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     metis_tac [])
 >- (`?tagenv_st' exh' ds_i2. decs_to_i2 (alloc_tags o' tagenv_st l) ds = (tagenv_st',exh',ds_i2)` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     metis_tac [alloc_tags_inv_weak])
 >- (`?tagenv_st' exh' ds_i2. decs_to_i2 (alloc_tag (TypeExn (mk_id o' s)) s tagenv_st) ds = (tagenv_st',exh',ds_i2)` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     first_x_assum(fn th => first_assum (match_mp_tac o
       MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
                 (ONCE_REWRITE_RULE[CONJ_COMM]th)))) >>
     PairCases_on `tagenv_st` >>
     full_simp_tac(srw_ss())[alloc_tag_def, alloc_tags_invariant_def, get_next_def, get_tagacc_def, FLOOKUP_UPDATE] >>
     srw_tac[][] >> res_tac >> simp[]))

val pmatch_i2_exh_weak = Q.prove (
`(!(exh:exh_ctors_env) s p v env res exh'.
  pmatch_i2 exh s p v env = res ∧
  res ≠ Match_type_error ∧
  DISJOINT (FDOM exh') (FDOM exh)
  ⇒
  pmatch_i2 (FUNION exh' exh) s p v env = res) ∧
 (!(exh:exh_ctors_env) s ps vs env res exh'.
  pmatch_list_i2 exh s ps vs env = res ∧
  res ≠ Match_type_error ∧
  DISJOINT (FDOM exh') (FDOM exh)
  ⇒
  pmatch_list_i2 (FUNION exh' exh) s ps vs env = res)`,
 ho_match_mp_tac pmatch_i2_ind >>
 srw_tac[][pmatch_i2_def, FLOOKUP_FUNION] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
 metis_tac [match_result_distinct, match_result_11]);

val evaluate_exp_i2_exh_weak = Q.prove (
`(∀b tmp_env s e res.
   evaluate_i2 b tmp_env s e res ⇒
   !exh genv env exh'.
     SND res ≠ Rerr Rtype_error ∧
     tmp_env = ((exh:exh_ctors_env),genv,env) ∧
     DISJOINT (FDOM exh') (FDOM exh) ⇒
     evaluate_i2 b (FUNION exh' exh,genv,env) s e res) ∧
 (∀b tmp_env s es res.
   evaluate_list_i2 b tmp_env s es res ⇒
   !exh genv env exh'.
     SND res ≠ Rerr Rtype_error ∧
     tmp_env = ((exh:exh_ctors_env),genv,env) ∧
     DISJOINT (FDOM exh') (FDOM exh) ⇒
     evaluate_list_i2 b (FUNION exh' exh,genv,env) s es res) ∧
 (∀b tmp_env s v pes err_v res.
   evaluate_match_i2 b tmp_env s v pes err_v res ⇒
   !(exh:exh_ctors_env) genv env exh'.
     SND res ≠ Rerr Rtype_error ∧
     tmp_env = (exh,genv,env) ∧
     DISJOINT (FDOM exh') (FDOM exh) ⇒
     evaluate_match_i2 b (FUNION exh' exh,genv,env) s v pes err_v res)`,
 ho_match_mp_tac evaluate_i2_ind >>
 srw_tac[][] >>
 srw_tac[][Once evaluate_i2_cases] >>
 full_simp_tac(srw_ss())[all_env_i2_to_env_def, all_env_i2_to_genv_def] >>
 metis_tac [pmatch_i2_exh_weak, match_result_distinct]);

val tagacc_accumulates = Q.prove (
`!tagenv_st ds tagenv_st' exh' ds_i2'.
  decs_to_i2 tagenv_st ds = (tagenv_st',exh',ds_i2') ⇒
  ?acc'. get_tagacc tagenv_st' = FUNION acc' (get_tagacc tagenv_st)`,
 induct_on `ds` >>
 srw_tac[][decs_to_i2_def]
 >- metis_tac [FUNION_FEMPTY_1] >>
 every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[LET_THM]
 >- (`?tagenv_st'' exh'' ds_i2''. decs_to_i2 tagenv_st ds = (tagenv_st'',exh'',ds_i2'')`
             by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- (`?tagenv_st'' exh'' ds_i2''. decs_to_i2 tagenv_st ds = (tagenv_st'',exh'',ds_i2'')`
             by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     metis_tac [])
 >- (`?tagenv_st'' exh'' ds_i2''. decs_to_i2 (alloc_tags o' tagenv_st l) ds = (tagenv_st'',exh'',ds_i2'')`
             by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     res_tac >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[alloc_tags_eqns] >>
     metis_tac [fupdate_list_funion, FUNION_ASSOC])
 >- (`?tagenv_st'' exh'' ds_i2''. decs_to_i2 (alloc_tag (TypeExn (mk_id o' s)) s tagenv_st) ds = (tagenv_st'',exh'',ds_i2'')`
             by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     res_tac >>
     srw_tac[][] >>
     PairCases_on `tagenv_st` >>
     srw_tac[][alloc_tag_def, get_tagacc_def] >>
     metis_tac [FUPDATE_EQ_FUNION, FUNION_ASSOC]));

val FOLDL_insert_tag_env = prove(
  ``∀ls tagenv.
    FOLDL (λtagenv (cn,tag). insert_tag_env cn tag tagenv) tagenv ls =
      (FST tagenv, SND tagenv |++ ls)``,
  Induct >> simp[FUPDATE_LIST_THM,UNCURRY,FORALL_PROD,insert_tag_env_def])

val tagenv_accumulates = Q.prove (
`!tagenv_st ds tagenv_st' exh' ds_i2'.
  decs_to_i2 tagenv_st ds = (tagenv_st',exh',ds_i2') ⇒
  ?acc'. get_tagenv tagenv_st' = (FST (get_tagenv tagenv_st), acc' ⊌ (SND (get_tagenv tagenv_st)))`,
 induct_on `ds` >>
 srw_tac[][decs_to_i2_def] >>
 PairCases_on`tagenv_st` >> full_simp_tac(srw_ss())[get_tagenv_def]
 >- metis_tac [FUNION_FEMPTY_1] >>
 reverse every_case_tac >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[LET_THM] >>
 first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
 first_x_assum(fn th => (first_assum (mp_tac o MATCH_MP th))) >>
 simp[get_tagenv_def,alloc_tags_eqns,get_next_def] >- (
   simp[alloc_tag_def,get_tagenv_def,insert_tag_env_def] >>
   ONCE_REWRITE_TAC[FUPDATE_EQ_FUNION] >> srw_tac[][] >> srw_tac[][] >>
   metis_tac[FUNION_ASSOC] ) >>
 simp[FOLDL_insert_tag_env] >>
 ONCE_REWRITE_TAC[fupdate_list_funion] >>
 srw_tac[][] >> srw_tac[][] >> metis_tac[FUNION_ASSOC]);

val eta2 = Q.prove (
`(\x y. f a x y) = f a`,
metis_tac []);

val nat_set_eq_thm = store_thm("nat_set_eq_thm",
  ``∀s1 s2. wf s1 ∧ wf s2 ⇒ (((s1:(unit spt)) = s2) ⇔ (domain s1 = domain s2))``,
  srw_tac[][sptreeTheory.spt_eq_thm] >> srw_tac[][EQ_IMP_THM] >- (
    srw_tac[][Once EXTENSION] >> srw_tac[][sptreeTheory.domain_lookup] ) >>
  Cases_on`lookup n s1` >> Cases_on`lookup n s2` >> srw_tac[][] >>
  metis_tac[sptreeTheory.lookup_NONE_domain,optionTheory.NOT_SOME_NONE,oneTheory.one]);

val exhaustive_env_weakened_exh_SUBMAP = prove(
  ``exhaustive_env_correct exh gtagenv ⇒
    weakened_exh gtagenv exh ⊑ exh``,
  srw_tac[][exhaustive_env_correct_def] >>
  simp[SUBMAP_DEF] >> gen_tac >> strip_tac >>
  conj_asm1_tac >- (
    full_simp_tac(srw_ss())[FDOM_weakened_exh,PULL_EXISTS,FLOOKUP_DEF] >>
    metis_tac[] ) >>
  Q.ISPECL_THEN[`weakened_exh gtagenv exh`,`x`]strip_assume_tac FLOOKUP_DEF >> rev_full_simp_tac(srw_ss())[] >>
  imp_res_tac FLOOKUP_weakened_exh_imp >>
  `wf (exh ' x)` by full_simp_tac(srw_ss())[IN_FRANGE,PULL_EXISTS] >>
  simp[nat_set_eq_thm] >>
  simp[EXTENSION,FLOOKUP_DEF] >>
  srw_tac[][EQ_IMP_THM] >> full_simp_tac(srw_ss())[PULL_EXISTS] >>
  res_tac >> full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
  metis_tac[]);

val galloc_tags_def = Define`
  galloc_tags n tdefs =
    MAP2 (λ(cn,ar,t) tag. ((cn,t),(n + tag,ar))) tdefs (COUNT_LIST (LENGTH tdefs))`;

val galloc_tags_cons = prove(
  ``galloc_tags next ((cn,len,tid)::tds) = ((cn,tid),(next,len))::(galloc_tags (next+1) tds)``,
 simp [galloc_tags_def, COUNT_LIST_def, MAP2_ZIP, LENGTH_MAP, LENGTH_COUNT_LIST] >>
 simp[LIST_EQ_REWRITE,LENGTH_ZIP,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP,EL_COUNT_LIST,UNCURRY]);

val flat_alloc_tags_append = prove(
  ``∀l1 l2 n. flat_alloc_tags n (l1 ++ l2) = flat_alloc_tags n l1 ++ flat_alloc_tags (n+LENGTH l1) l2``,
  simp[flat_alloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST] >>
  simp[LIST_EQ_REWRITE,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP,EL_COUNT_LIST] >>
  srw_tac[][] >> Cases_on`x < LENGTH l1` >>
  simp[EL_APPEND1,EL_APPEND2,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP,EL_COUNT_LIST] >>
  simp[UNCURRY]);

val galloc_tags_append = prove(
  ``∀l1 l2 n. galloc_tags n (l1 ++ l2) = galloc_tags n l1 ++ galloc_tags (n+LENGTH l1) l2``,
  simp[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST] >>
  simp[LIST_EQ_REWRITE,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP,EL_COUNT_LIST] >>
  srw_tac[][] >> Cases_on`x < LENGTH l1` >>
  simp[EL_APPEND1,EL_APPEND2,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP,EL_COUNT_LIST] >>
  simp[UNCURRY]);

val flat_alloc_tags_nil = prove(
  ``flat_alloc_tags n [] = []``,
  srw_tac[][flat_alloc_tags_def,COUNT_LIST_def]);

val galloc_tags_nil = prove(
  ``galloc_tags n [] = []``,
  srw_tac[][galloc_tags_def,COUNT_LIST_def]);

val nat_set_from_list_def = Define`
  nat_set_from_list = FOLDL (λs n. insert n () s) LN`

val alloc_tags_to_exh_def = Define`
  alloc_tags_to_exh ls = FUN_FMAP
    (λt. nat_set_from_list
      (MAP (FST o SND) (FILTER ($= (SOME (TypeId t)) o SND o SND) ls)))
    {t | MEM (SOME (TypeId t)) (MAP (SND o SND) ls) }`;

val alloc_tags_to_exh_nil = prove(
  ``alloc_tags_to_exh [] = FEMPTY``,
  srw_tac[][alloc_tags_to_exh_def]);

val FINITE_alloc_tags_to_exh_dom = prove(
  ``FINITE {t | MEM (SOME (TypeId t)) (MAP (SND o SND) ls) }``,
  qmatch_abbrev_tac`FINITE P` >>
  qsuff_tac`∃f. P ⊆ IMAGE f (set (MAP (SND o SND) ls))` >-
    metis_tac[IMAGE_FINITE,SUBSET_FINITE,FINITE_LIST_TO_SET] >>
  simp[Abbr`P`,SUBSET_DEF] >>
  qexists_tac`λx. @y. x = SOME (TypeId y)` >>
  srw_tac[][EXISTS_PROD] >> metis_tac[tid_or_exn_11,SOME_11]);

val FDOM_alloc_tags_to_exh = prove(
  ``FDOM (alloc_tags_to_exh ls) =
    {t | MEM (SOME (TypeId t)) (MAP (SND o SND) ls)}``,
  srw_tac[][alloc_tags_to_exh_def] >>
  simp[FUN_FMAP_DEF,FINITE_alloc_tags_to_exh_dom]);

val FLOOKUP_alloc_tags_to_exh_imp = prove(
  ``FLOOKUP (alloc_tags_to_exh ls) t = SOME tags ⇒
    wf tags ∧
    (domain tags = { tag | MEM (tag,(SOME (TypeId t))) (MAP SND ls) })``,
  simp[alloc_tags_to_exh_def] >>
  qmatch_abbrev_tac`FLOOKUP (FUN_FMAP f P) k = SOME v ⇒ Z` >>
  `FINITE P` by (
    unabbrev_all_tac >>
    simp[FINITE_alloc_tags_to_exh_dom]) >>
  simp[FLOOKUP_FUN_FMAP,Abbr`f`,Abbr`Z`] >> srw_tac[][] >- (
    simp[nat_set_from_list_def] >>
    match_mp_tac wf_nat_set_from_list >>
    srw_tac[][sptreeTheory.wf_def] ) >>
  srw_tac[][nat_set_from_list_def] >>
  srw_tac[][EXTENSION,MEM_MAP,PULL_EXISTS,MEM_FILTER,EXISTS_PROD]);

val build_tdefs_append = prove(
  ``∀l1 mn l2.
    build_tdefs mn (l1++l2) =
    build_tdefs mn l2 ++ build_tdefs mn l1``,
  simp[build_tdefs_def])

val build_tdefs_cons = prove(
  ``build_tdefs mn ((x,y,z)::tdefs) =
    build_tdefs mn tdefs ++ REVERSE (MAP (λ(a,b). (a,LENGTH b,TypeId(mk_id mn y))) z)``,
  REWRITE_TAC[Once CONS_APPEND] >>
  REWRITE_TAC[build_tdefs_append] >>
  simp[] >> simp[build_tdefs_def]);

val mk_id_inj = store_thm("mk_id_inj",
  ``mk_id mn1 s1 = mk_id mn2 s2 ⇔ (mn1 = mn2) ∧ (s1 = s2)``,
  srw_tac[][mk_id_def] >> every_case_tac);

val build_exh_env_cons = prove(
  ``tn ∉ set (MAP (FST o SND) tds) ⇒
    build_exh_env mn (n,acc) ((tvs,tn,constrs)::tds) =
    build_exh_env mn (n,acc) tds |+
    (mk_id mn tn, nat_set_from_list (MAP (λ(cn,ts). FST (option_CASE (FLOOKUP acc cn) (0,NONE) I)) constrs))``,
  srw_tac[][build_exh_env_def,FUPDATE_LIST_THM] >>
  qmatch_abbrev_tac`FEMPTY |+ (k,v) |++ ls = (FEMPTY |++ ls) |+ (k,w)` >>
  `FEMPTY |+ (k,v) |++ ls = (FEMPTY |++ ls) |+ (k,v)` by (
    match_mp_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
    full_simp_tac(srw_ss())[Abbr`ls`,Abbr`k`,MEM_MAP,FORALL_PROD,mk_id_inj] ) >>
  pop_assum SUBST1_TAC >>
  AP_TERM_TAC >> simp[] >>
  unabbrev_all_tac >>
  simp[nat_set_from_list_def,FOLDL_MAP,LAMBDA_PROD]);

val type_defs_to_new_tdecs_cons = prove(
  ``type_defs_to_new_tdecs mn ((x,y,z)::ls) = TypeId (mk_id mn y) INSERT type_defs_to_new_tdecs mn ls``,
  srw_tac[][type_defs_to_new_tdecs_def]);

val cenv_inv_to_mod = prove(
  ``∀tdefs n mn tids envC exh tagenv gtagenv emptys.
    cenv_inv envC exh tagenv gtagenv ⇒
    tuple_tag < n ∧ (∀p. p ∈ FRANGE gtagenv ⇒ FST p < n) ∧
    ALL_DISTINCT (MAP FST tdefs) ∧
    (∀s. s ∈ FRANGE emptys ⇒ s = LN) ∧ DISJOINT (FDOM emptys) (FDOM exh) ∧
    DISJOINT (IMAGE (SND o SND) (set tdefs)) (IMAGE SND (FDOM gtagenv)) ⇒
    cenv_inv (merge_alist_mod_env ([],REVERSE tdefs) envC) (alloc_tags_to_exh (flat_alloc_tags n tdefs) ⊌ emptys ⊌ exh)
      (FST tagenv, SND tagenv |++ (flat_alloc_tags n tdefs))
      (gtagenv |++ (galloc_tags n tdefs))``,
  Induct >- (
    Cases_on`envC` >>
    simp[cenv_inv_def,FUPDATE_LIST_THM,flat_alloc_tags_def,merge_alist_mod_env_def,
         COUNT_LIST_def,galloc_tags_def,alloc_tags_to_exh_nil,
         FUNION_FEMPTY_1] >>
    srw_tac[][exhaustive_env_correct_def,FRANGE_FUNION] >>
    res_tac >> srw_tac[][FLOOKUP_FUNION] >- srw_tac[][sptreeTheory.wf_def] >>
    BasicProvers.CASE_TAC >- metis_tac[] >>
    full_simp_tac(srw_ss())[FLOOKUP_DEF,IN_DISJOINT] >> metis_tac[]) >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  srw_tac[][galloc_tags_append,flat_alloc_tags_append
    ,galloc_tags_cons,flat_alloc_tags_cons
    ,galloc_tags_nil,flat_alloc_tags_nil] >>
  first_x_assum(qspec_then`n+1`mp_tac) >> simp[] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qspec_then`emptys`mp_tac) >>
  discharge_hyps >- ( srw_tac[][] >> res_tac >> simp[] ) >>
  full_simp_tac(srw_ss())[FUPDATE_LIST_APPEND,FUPDATE_LIST_THM] >>
  `¬MEM p0 (MAP FST (flat_alloc_tags (n+1) tdefs))` by (
    simp[flat_alloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,MAP_ZIP] >>
    simp[GSYM combinTheory.o_DEF,MAP_ZIP,LENGTH_COUNT_LIST] ) >>
  pop_assum (strip_assume_tac o MATCH_MP (GEN_ALL FUPDATE_FUPDATE_LIST_COMMUTES)) >>
  simp[] >> pop_assum kall_tac >>
  `¬MEM (p0,p2) (MAP FST (galloc_tags (n+1) tdefs))` by (
    simp[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
    simp[MEM_MAP,MEM_ZIP,LENGTH_COUNT_LIST,FORALL_PROD] >>
    full_simp_tac(srw_ss())[MEM_MAP,FORALL_PROD,MEM_EL] ) >>
  pop_assum (strip_assume_tac o MATCH_MP (GEN_ALL FUPDATE_FUPDATE_LIST_COMMUTES)) >>
  full_simp_tac(srw_ss())[] >> pop_assum kall_tac >>
  Q.PAT_ABBREV_TAC`gt0 = gtagenv |++ X` >>
  Q.PAT_ABBREV_TAC`ft0 = SND tagenv |++ X` >>
  full_simp_tac(srw_ss())[cenv_inv_def] >> strip_tac >>
  conj_tac >- (
    Cases_on`envC` >>
    full_simp_tac(srw_ss())[envC_tagged_def,merge_alist_mod_env_def,lookup_alist_mod_env_def,
       lookup_tag_env_def,lookup_tag_flat_def] >>
    rpt gen_tac >>
    first_x_assum(qspec_then`cn`mp_tac) >>
    first_x_assum(qspec_then`cn`mp_tac) >>
    reverse(Cases_on`cn`)>>full_simp_tac(srw_ss())[id_to_n_def]>- (
      BasicProvers.CASE_TAC >>
      BasicProvers.CASE_TAC >- metis_tac[gtagenv_wf_def] >>
      BasicProvers.CASE_TAC >- metis_tac[gtagenv_wf_def] >>
      srw_tac[][] >>
      first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
      first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
      `tag ≠ tuple_tag` by metis_tac[gtagenv_wf_def] >> full_simp_tac(srw_ss())[] >>
      simp[FLOOKUP_UPDATE] >>
      BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF,FORALL_PROD] >>
      metis_tac[] ) >>
    simp[ALOOKUP_APPEND] >>
    BasicProvers.CASE_TAC >- (
      ntac 2 strip_tac >>
      BasicProvers.CASE_TAC >- (
        srw_tac[][FLOOKUP_UPDATE] >> simp[] ) >>
      srw_tac[][] >>
      first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
      first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
      `tag ≠ tuple_tag` by metis_tac[gtagenv_wf_def] >> full_simp_tac(srw_ss())[] >>
      simp[FLOOKUP_UPDATE] ) >>
    imp_res_tac ALOOKUP_MEM >>
    srw_tac[][] >>
    simp[FLOOKUP_UPDATE] >>
    `tag ≠ tuple_tag` by metis_tac[gtagenv_wf_def] >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    BasicProvers.VAR_EQ_TAC >>
    full_simp_tac(srw_ss())[MAP_REVERSE, MEM_MAP] >>
    metis_tac [pair_CASES, FST, SND] ) >>
  conj_tac >- (
    full_simp_tac(srw_ss())[exhaustive_env_correct_def] >>
    conj_tac >- (
      full_simp_tac(srw_ss())[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[FLOOKUP_FUNION] >>
      pop_assum mp_tac >>
      BasicProvers.CASE_TAC >- (
        BasicProvers.CASE_TAC >- metis_tac[] >>
        res_tac >> srw_tac[][] >> srw_tac[][sptreeTheory.wf_def] ) >>
      imp_res_tac FLOOKUP_alloc_tags_to_exh_imp >>
      metis_tac[] ) >>
    full_simp_tac(srw_ss())[PULL_EXISTS,FLOOKUP_UPDATE] >>
    rpt gen_tac >>
    simp[FLOOKUP_FUNION] >>
    strip_tac >> simp[] >- (
      rpt BasicProvers.VAR_EQ_TAC >>
      BasicProvers.CASE_TAC >- (
        full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
        full_simp_tac(srw_ss())[FDOM_alloc_tags_to_exh] >>
        metis_tac[] ) >>
      imp_res_tac FLOOKUP_alloc_tags_to_exh_imp >>
      simp[FLOOKUP_UPDATE] >> srw_tac[][] >>
      full_simp_tac(srw_ss())[flookup_fupdate_list,Abbr`gt0`] >>
      pop_assum mp_tac >>
      BasicProvers.CASE_TAC >- (
        simp[FLOOKUP_DEF] >>
        full_simp_tac(srw_ss())[FORALL_PROD] ) >>
      srw_tac[][] >>
      imp_res_tac ALOOKUP_MEM >>
      full_simp_tac(srw_ss())[galloc_tags_def,flat_alloc_tags_def,MEM_MAP,LENGTH_COUNT_LIST,MAP2_MAP,EXISTS_PROD] >>
      metis_tac[]) >>
    BasicProvers.CASE_TAC >- (
      pop_assum(strip_assume_tac o SIMP_RULE(srw_ss())[FLOOKUP_DEF,FDOM_alloc_tags_to_exh]) >>
      first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
      simp[FLOOKUP_FUNION,Once FLOOKUP_DEF,FDOM_alloc_tags_to_exh] ) >>
    imp_res_tac FLOOKUP_alloc_tags_to_exh_imp >>
    srw_tac[][] >>
    first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[FLOOKUP_FUNION] >>
    BasicProvers.CASE_TAC >- (
      `p2 = TypeId t` by (
        full_simp_tac(srw_ss())[FLOOKUP_DEF,FDOM_alloc_tags_to_exh] >> srw_tac[][] ) >>
      full_simp_tac(srw_ss())[] >> srw_tac[][] >>
      full_simp_tac(srw_ss())[Abbr`gt0`,flookup_fupdate_list] >>
      reverse (Cases_on`FLOOKUP emptys t`) >- (
        full_simp_tac(srw_ss())[] >> srw_tac[][] >>
        `tag ∈ domain tags` by metis_tac[] >>
        full_simp_tac(srw_ss())[FRANGE_FLOOKUP,PULL_EXISTS] >>
        res_tac >> full_simp_tac(srw_ss())[] ) >>
      full_simp_tac(srw_ss())[] >>
      every_case_tac >- (full_simp_tac(srw_ss())[FLOOKUP_DEF,FORALL_PROD] >> metis_tac[]) >>
      imp_res_tac ALOOKUP_MEM >>
      full_simp_tac(srw_ss())[FLOOKUP_DEF,FDOM_alloc_tags_to_exh] >>
      full_simp_tac(srw_ss())[galloc_tags_def,LENGTH_COUNT_LIST,MAP2_MAP,MEM_MAP,PULL_EXISTS,EXISTS_PROD,MEM_ZIP,flat_alloc_tags_def] >>
      metis_tac[] ) >>
    srw_tac[][] >>
    `MEM (SOME (TypeId t)) (MAP (SND o SND) (flat_alloc_tags (n+1) tdefs))` by (
      full_simp_tac(srw_ss())[FLOOKUP_DEF,FDOM_alloc_tags_to_exh] ) >>
    pop_assum mp_tac >>
    simp[MEM_MAP,Once flat_alloc_tags_def] >>
    simp[MAP2_MAP,LENGTH_COUNT_LIST,PULL_EXISTS,MEM_MAP,EXISTS_PROD,MEM_ZIP] >>
    srw_tac[][] >>
    qpat_assum`FLOOKUP gt0 X = SOME y`mp_tac >>
    simp[Abbr`gt0`,flookup_fupdate_list] >>
    BasicProvers.CASE_TAC >- (
      simp[FLOOKUP_DEF] >>
      full_simp_tac(srw_ss())[IN_DISJOINT,FORALL_PROD] >>
      metis_tac[MEM_EL] ) >>
    srw_tac[][] >> imp_res_tac ALOOKUP_MEM >>
    pop_assum mp_tac >>
    simp[galloc_tags_def,flat_alloc_tags_def] >>
    simp[MAP2_MAP,LENGTH_COUNT_LIST,PULL_EXISTS,MEM_MAP,EXISTS_PROD,MEM_ZIP,EL_COUNT_LIST] >>
    srw_tac[][] >> metis_tac[EL_COUNT_LIST]) >>
  full_simp_tac(srw_ss())[gtagenv_wf_def,FLOOKUP_UPDATE] >>
  conj_tac >- ( srw_tac[][] >> simp[] ) >>
  conj_tac >- (
    full_simp_tac(srw_ss())[has_exns_def,FLOOKUP_UPDATE] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_DEF,FORALL_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    full_simp_tac(srw_ss())[has_bools_def,FLOOKUP_UPDATE] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_DEF,FORALL_PROD] >>
    metis_tac[] ) >>
  conj_tac >- (
    full_simp_tac(srw_ss())[has_lists_def,FLOOKUP_UPDATE] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_DEF,FORALL_PROD] >>
    metis_tac[] ) >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >- (
    full_simp_tac(srw_ss())[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    pop_assum mp_tac >>
    BasicProvers.CASE_TAC >>
    spose_not_then strip_assume_tac >>
    qpat_assum`¬X`mp_tac >> simp[] >>
    full_simp_tac(srw_ss())[Abbr`gt0`,flookup_fupdate_list] >>
    pop_assum mp_tac >>
    BasicProvers.CASE_TAC >- (
      full_simp_tac(srw_ss())[IN_FRANGE_FLOOKUP,FORALL_PROD] >>
      metis_tac[prim_recTheory.LESS_REFL] ) >>
    imp_res_tac ALOOKUP_MEM >>
    full_simp_tac(srw_ss())[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,MEM_ZIP] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    fsrw_tac[ARITH_ss][UNCURRY] ) >>
  strip_tac >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >- (
    strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    qpat_assum`~X`mp_tac >>
    full_simp_tac(srw_ss())[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    full_simp_tac(srw_ss())[Abbr`gt0`,flookup_fupdate_list] >>
    pop_assum mp_tac >>
    BasicProvers.CASE_TAC >- (
      full_simp_tac(srw_ss())[IN_FRANGE_FLOOKUP,FORALL_PROD] >>
      metis_tac[prim_recTheory.LESS_REFL] ) >>
    imp_res_tac ALOOKUP_MEM >>
    full_simp_tac(srw_ss())[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,MEM_ZIP] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    fsrw_tac[ARITH_ss][UNCURRY] ) >>
  metis_tac[]);

val galloc_tags_submap = prove(
  ``∀ls n gtagenv.
    (∃tid. EVERY ($= tid) (MAP (SND o SND) ls) ∧ tid ∉ (IMAGE SND (FDOM gtagenv))) ∧
    ALL_DISTINCT (MAP FST ls)
    ⇒
    gtagenv ⊑ gtagenv |++ galloc_tags n ls``,
  Induct >> simp[FUPDATE_LIST_THM,galloc_tags_nil] >>
  qx_gen_tac`p` >> PairCases_on`p` >> simp[galloc_tags_cons,FUPDATE_LIST_THM] >>
  srw_tac[][] >>
  qmatch_abbrev_tac`a ⊑ a |+ (k,v) |++ b` >>
  `a |+ (k,v) |++ b = (a |++ b) |+ (k,v)` by (
    match_mp_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
    simp[Abbr`b`,galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,PULL_EXISTS,Abbr`k`] >>
    full_simp_tac(srw_ss())[MEM_MAP,UNCURRY,MEM_ZIP,LENGTH_COUNT_LIST,FORALL_PROD] >>
    metis_tac[MEM_EL] ) >>
  srw_tac[][] >> pop_assum kall_tac >>
  match_mp_tac SUBMAP_TRANS >>
  qexists_tac`a |++ b` >>
  reverse conj_tac >- (
    simp[Abbr`k`,FDOM_FUPDATE_LIST] >>
    disj1_tac >> full_simp_tac(srw_ss())[FORALL_PROD] >>
    simp[Abbr`b`,galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,PULL_EXISTS] >>
    full_simp_tac(srw_ss())[MEM_MAP,UNCURRY,MEM_ZIP,LENGTH_COUNT_LIST,FORALL_PROD] >>
    metis_tac[MEM_EL] ) >>
  simp[Abbr`b`] >>
  first_x_assum match_mp_tac >>
  simp[] >> metis_tac[]);

val gtagenv_weak_galloc_tags = prove(
  ``∀ls mn x n gtagenv.
    tuple_tag < n ∧ (∀p. p ∈ FRANGE gtagenv ⇒ FST p < n) ∧
    TypeId (mk_id mn x) ∉ IMAGE SND (FDOM gtagenv) ∧
    gtagenv_wf gtagenv ∧ ALL_DISTINCT (MAP FST ls)
    ⇒
    let gtagenv' = gtagenv |++ galloc_tags n (MAP (λ(a,b). (a, LENGTH b, TypeId (mk_id mn x))) ls) in
    gtagenv_weak gtagenv gtagenv' ∧
    gtagenv_wf gtagenv'``,
  rpt gen_tac >> strip_tac >>
  simp[gtagenv_weak_def,GSYM CONJ_ASSOC] >>
  conj_asm1_tac >- (
    match_mp_tac galloc_tags_submap >>
    simp[MAP_MAP_o,EVERY_MAP,UNCURRY,combinTheory.o_DEF,ETA_AX] >> full_simp_tac(srw_ss())[] >>
    metis_tac[] ) >>
  conj_asm1_tac >- (
    simp[flookup_fupdate_list] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[gtagenv_wf_def] >>
    BasicProvers.CASE_TAC >- metis_tac[] >>
    imp_res_tac ALOOKUP_MEM >>
    full_simp_tac(srw_ss())[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,PULL_EXISTS,MEM_ZIP,UNCURRY] >>
    simp[] ) >>
  conj_asm1_tac >- (
    simp[PULL_EXISTS,FDOM_FUPDATE_LIST] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[MEM_MAP,galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_ZIP] >>
    srw_tac[][] >> full_simp_tac(srw_ss())[UNCURRY] >> srw_tac[][] >> full_simp_tac(srw_ss())[EL_MAP,UNCURRY] >>
    full_simp_tac(srw_ss())[FORALL_PROD] >> metis_tac[] ) >>
  conj_asm1_tac >- (
    rpt gen_tac >>
    simp[flookup_fupdate_list] >>
    BasicProvers.CASE_TAC >- (
      BasicProvers.CASE_TAC >-
        (full_simp_tac(srw_ss())[gtagenv_wf_def] >> metis_tac[]) >>
      imp_res_tac ALOOKUP_MEM >>
      full_simp_tac(srw_ss())[MEM_MAP,galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_ZIP] >>
      strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      full_simp_tac(srw_ss())[UNCURRY,EL_MAP] >> rpt BasicProvers.VAR_EQ_TAC >>
      full_simp_tac(srw_ss())[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    BasicProvers.CASE_TAC >- (
      imp_res_tac ALOOKUP_MEM >>
      full_simp_tac(srw_ss())[MEM_MAP,galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_ZIP] >>
      strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      full_simp_tac(srw_ss())[UNCURRY,EL_MAP] >> rpt BasicProvers.VAR_EQ_TAC >>
      full_simp_tac(srw_ss())[IN_FRANGE_FLOOKUP,PULL_EXISTS] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac ALOOKUP_MEM >>
    full_simp_tac(srw_ss())[MEM_MAP,galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_ZIP] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    full_simp_tac(srw_ss())[UNCURRY,EL_MAP] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    full_simp_tac(srw_ss())[EL_COUNT_LIST]) >>
  full_simp_tac(srw_ss())[gtagenv_wf_def] >>
  conj_tac >- (
    full_simp_tac(srw_ss())[has_exns_def,flookup_fupdate_list] >>
    every_case_tac >>
    imp_res_tac ALOOKUP_MEM >>
    full_simp_tac(srw_ss())[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,MEM_ZIP,UNCURRY] >>
    rpt BasicProvers.VAR_EQ_TAC >> full_simp_tac(srw_ss())[EL_MAP,UNCURRY] ) >>
  conj_tac >- (
    full_simp_tac(srw_ss())[has_bools_def,flookup_fupdate_list] >>
    full_simp_tac(srw_ss())[FORALL_PROD,FLOOKUP_DEF] >>
    every_case_tac >>
    imp_res_tac ALOOKUP_MEM >>
    full_simp_tac(srw_ss())[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,MEM_ZIP,UNCURRY] >>
    rpt BasicProvers.VAR_EQ_TAC >> full_simp_tac(srw_ss())[EL_MAP,UNCURRY] >>
    metis_tac[]) >>
  conj_tac >- (
    full_simp_tac(srw_ss())[has_lists_def,flookup_fupdate_list] >>
    full_simp_tac(srw_ss())[FORALL_PROD,FLOOKUP_DEF] >>
    every_case_tac >>
    imp_res_tac ALOOKUP_MEM >>
    full_simp_tac(srw_ss())[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,MEM_ZIP,UNCURRY] >>
    rpt BasicProvers.VAR_EQ_TAC >> full_simp_tac(srw_ss())[EL_MAP,UNCURRY]>>
    metis_tac[]) >>
  metis_tac[]);

val gtagenv_weak_galloc_tags_build_tdefs = prove(
  ``∀tdefs mn gtagenv n.
    gtagenv_wf gtagenv ∧
    DISJOINT (type_defs_to_new_tdecs mn tdefs) (IMAGE SND (FDOM gtagenv)) ∧
    check_dup_ctors tdefs ∧
    ALL_DISTINCT (MAP (FST o SND) tdefs) ∧
    tuple_tag < n ∧ (∀p. p ∈ FRANGE gtagenv ⇒ FST p < n) ⇒
    gtagenv_weak gtagenv (gtagenv |++ galloc_tags n (REVERSE (build_tdefs mn tdefs)))``,
  Induct >- simp[gtagenv_weak_refl,build_tdefs_def,galloc_tags_nil,FUPDATE_LIST_THM] >>
  qx_gen_tac`p` >> PairCases_on`p` >> srw_tac[][] >>
  simp[build_tdefs_cons,REVERSE_APPEND,galloc_tags_append,FUPDATE_LIST_APPEND] >>
  qmatch_abbrev_tac`gtagenv_weak gtagenv ((gtagenv |++ x1) |++ x2)` >>
  Q.ISPECL_THEN[`p2`,`mn`,`p1`,`n`,`gtagenv`]mp_tac gtagenv_weak_galloc_tags >>
  discharge_hyps >- (
    simp[] >>
    full_simp_tac(srw_ss())[type_defs_to_new_tdecs_def,check_dup_ctors_thm,ALL_DISTINCT_APPEND,FST_pair] ) >>
  simp[] >> strip_tac >>
  match_mp_tac gtagenv_weak_trans >>
  HINT_EXISTS_TAC >> simp[] >>
  simp[Abbr`x2`] >>
  first_x_assum match_mp_tac >>
  simp[] >>
  full_simp_tac(srw_ss())[check_dup_ctors_thm,ALL_DISTINCT_APPEND,type_defs_to_new_tdecs_def,FDOM_FUPDATE_LIST] >>
  reverse conj_tac >- (
    ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
    conj_tac >- ( srw_tac[][] >> res_tac >> simp[] ) >>
    simp[Abbr`x1`] >>
    simp[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,MEM_ZIP,UNCURRY,PULL_EXISTS,EL_COUNT_LIST] ) >>
  conj_tac >- metis_tac[DISJOINT_SYM] >>
  `IMAGE SND (set (MAP FST x1)) ⊆ {TypeId (mk_id mn p1)}` by (
    simp[SUBSET_DEF,Abbr`x1`,galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,PULL_EXISTS,MEM_ZIP,EL_MAP,UNCURRY] ) >>
  full_simp_tac(srw_ss())[IN_DISJOINT,SUBSET_DEF,PULL_EXISTS,EXISTS_PROD,FORALL_PROD] >>
  spose_not_then strip_assume_tac >> srw_tac[][] >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >> srw_tac[][] >>
  res_tac >> full_simp_tac(srw_ss())[] >>
  qmatch_assum_rename_tac`mk_id mn a = mk_id mn b` >>
  `a = b` by (Cases_on`mn`>>full_simp_tac(srw_ss())[mk_id_def]) >>
  metis_tac[]);

val FDOM_build_exh_env = prove(
  ``FDOM (build_exh_env mn res tds) = set (MAP (mk_id mn o FST o SND) tds)``,
  PairCases_on`res` >>
  simp[build_exh_env_def,FDOM_FUPDATE_LIST,
       MAP_MAP_o,combinTheory.o_DEF,UNCURRY]);

val MAP_FST_galloc_tags = prove(
  ``MAP FST (galloc_tags n tds) = MAP (λ(x,y,z). (x,z)) tds``,
  simp[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MAP_MAP_o,
       combinTheory.o_DEF,UNCURRY] >>
  simp[LIST_EQ_REWRITE,LENGTH_COUNT_LIST,EL_MAP,UNCURRY,EL_ZIP]);

val MAP_FST_flat_alloc_tags = prove(
  ``MAP FST (flat_alloc_tags n tds) = MAP FST tds``,
  simp[flat_alloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MAP_MAP_o,
       combinTheory.o_DEF,UNCURRY] >>
  simp[LIST_EQ_REWRITE,LENGTH_COUNT_LIST,EL_MAP,UNCURRY,EL_ZIP]);

val tids_of_decs_def = Define`
  tids_of_decs ds = set (FLAT (MAP (λd. case d of Dtype_i1 mn tds => MAP (mk_id mn o FST o SND) tds | _ => []) ds))`;

val tids_of_decs_thm = prove(
  ``(tids_of_decs [] = {}) ∧
    (tids_of_decs (d::ds) = tids_of_decs ds ∪
      case d of Dtype_i1 mn tds => set (MAP (mk_id mn o FST o SND) tds) | _ => {})``,
  simp[tids_of_decs_def] >>
  every_case_tac >> simp[] >>
  metis_tac[UNION_COMM]);

val FDOM_decs_to_i2_exh = prove(
  ``∀ds st st' exh' ds'.
    decs_to_i2 st ds = (st',exh',ds') ⇒
    FDOM exh' = tids_of_decs ds``,
  Induct >> simp[decs_to_i2_def] >>
  rpt gen_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[tids_of_decs_def] >> srw_tac[][] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  srw_tac[][] >>
  simp[FDOM_build_exh_env] >>
  metis_tac[UNION_COMM]);

val decs_to_i2_exh_wf = prove(
  ``∀ds st st' exh' ds'.
    decs_to_i2 st ds = (st',exh',ds') ⇒
    ∀t. t ∈ FRANGE exh' ⇒ wf t``,
  Induct >> simp[decs_to_i2_def] >>
  rpt gen_tac >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  srw_tac[][] >>
  last_x_assum mp_tac >>
  qid_spec_tac`t` >>
  ho_match_mp_tac IN_FRANGE_FUNION_suff >> srw_tac[][] >>
  qmatch_assum_rename_tac`t ∈ FRANGE (build_exh_env mn _ l)` >>
  Cases_on`alloc_tags mn st l`>>
  full_simp_tac(srw_ss())[FRANGE_FLOOKUP,build_exh_env_def,flookup_fupdate_list] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac ALOOKUP_MEM >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >> srw_tac[][] >>
  qmatch_abbrev_tac`wf (FOLDL g LN c)` >>
  `∃f. FOLDL g LN c = nat_set_from_list (MAP f c)` by (
    simp[nat_set_from_list_def,FOLDL_MAP,Abbr`g`,LAMBDA_PROD] >>
    qexists_tac`λ(cn,ts). FST (option_CASE (FLOOKUP r cn) (0,NONE) I)` >>
    simp[]) >>
  simp[nat_set_from_list_def] >>
  match_mp_tac wf_nat_set_from_list >>
  simp[sptreeTheory.wf_def]);

val MAP_SND_o_SND_flat_alloc_tags = prove(
  ``MAP (SND o SND) (flat_alloc_tags n ls) = MAP (SOME o SND o SND) ls``,
  srw_tac[][flat_alloc_tags_def] >>
  simp[MAP2_MAP,LENGTH_COUNT_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
  simp[LIST_EQ_REWRITE,LENGTH_COUNT_LIST,EL_MAP,EL_ZIP]);

val no_dup_types_i1_cons_imp = prove(
  ``no_dup_types_i1 (d::ds) ⇒ no_dup_types_i1 ds``,
  srw_tac[][decs_to_types_i1_def,no_dup_types_i1_def,ALL_DISTINCT_APPEND]);

val FLOOKUP_build_exh_env_imp = prove(
  ``FLOOKUP (build_exh_env mn zz tds) k = SOME tags ⇒
    ALL_DISTINCT (MAP (FST o SND) tds) ⇒
    ∃tn tvs constrs.
      wf tags ∧
      k = mk_id mn tn ∧
      MEM (tvs,tn,constrs) tds ∧
      domain tags = set (MAP (λ(cn,ts). FST (option_CASE (FLOOKUP (get_tagacc zz) cn) (0,NONE) I)) constrs)``,
   PairCases_on`zz` >>
   srw_tac[][build_exh_env_def,flookup_fupdate_list,get_tagacc_def] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   qmatch_assum_abbrev_tac`ALOOKUP ls k = SOME v` >>
   `ALL_DISTINCT (MAP FST ls)` by (
     simp[Abbr`ls`,MAP_REVERSE,ALL_DISTINCT_REVERSE,MAP_MAP_o,UNCURRY,combinTheory.o_DEF] >>
     simp[GSYM combinTheory.o_DEF] >> simp[Once (GSYM MAP_MAP_o)] >>
     match_mp_tac ALL_DISTINCT_MAP_INJ >>
     simp[mk_id_inj]) >>
   imp_res_tac ALOOKUP_MEM >>
   full_simp_tac(srw_ss())[Abbr`ls`,MEM_MAP,EXISTS_PROD] >>
   unabbrev_all_tac >> srw_tac[][] >>
   simp[mk_id_inj] >>
   ONCE_REWRITE_TAC[CONJ_COMM] >>
   ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   qmatch_assum_rename_tac`MEM (a,b,c) tds` >>
   qmatch_abbrev_tac`X = set (MAP f c) ∧ Z` >>
   map_every qunabbrev_tac[`X`,`Z`] >>
   qmatch_abbrev_tac`domain (FOLDL g LN c) = X ∧ Z` >>
   map_every qunabbrev_tac[`X`,`Z`] >>
   `FOLDL g LN c = nat_set_from_list (MAP f c)` by (
     simp[nat_set_from_list_def,FOLDL_MAP,Abbr`g`,Abbr`f`,LAMBDA_PROD] ) >>
   simp[nat_set_from_list_def] >>
   match_mp_tac wf_nat_set_from_list >>
   simp[sptreeTheory.wf_def]);

val MEM_flat_alloc_tags_REVERSE_build_tdefs_suff = prove(
  ``MEM (tvs,tn,constrs) tdefs ⇒ MEM (k,ts) constrs ⇒
    ∃n. MEM (k,m+n,SOME (TypeId (mk_id mn tn))) (flat_alloc_tags m (REVERSE (build_tdefs mn tdefs)))``,
  simp[flat_alloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,ZIP_COUNT_LIST,MAP_GENLIST,MEM_GENLIST,UNCURRY] >>
  srw_tac[][] >>
  qsuff_tac`∃x. MEM(k,x,TypeId (mk_id mn tn)) (build_tdefs mn tdefs)` >- (
    simp[MEM_EL] >> srw_tac[][] >>
    qexists_tac`LENGTH (build_tdefs mn tdefs) - n - 1` >>
    simp[EL_REVERSE,arithmeticTheory.PRE_SUB1] >>
    metis_tac[pair_CASES,FST,SND] ) >>
  simp[build_tdefs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD,mk_id_inj] >>
  metis_tac[] );

val MEM_flat_alloc_tags_REVERSE_build_tdefs_imp = prove(
  ``MEM (k,m,SOME(TypeId(mk_id mn tn))) (flat_alloc_tags n (REVERSE (build_tdefs mn tdefs))) ⇒
    ∃tvs constrs a. MEM (tvs,tn,constrs) tdefs ∧ MEM (k,a) constrs``,
  simp[flat_alloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,ZIP_COUNT_LIST,MAP_GENLIST,MEM_GENLIST,UNCURRY] >>
  srw_tac[][] >>
  qmatch_assum_rename_tac`n < LENGTH _` >>
  `∃a b c. EL n (REVERSE (build_tdefs mn tdefs)) = (a,b,c)` by simp[GSYM EXISTS_PROD] >> full_simp_tac(srw_ss())[] >>
  `MEM (a,b,c) (build_tdefs mn tdefs)` by (
    simp[MEM_EL] >> rev_full_simp_tac(srw_ss())[EL_REVERSE] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl o SYM) >>
    simp[] ) >>
  srw_tac[][] >>
  pop_assum mp_tac >>
  simp[build_tdefs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD,mk_id_inj] >>
  metis_tac[] );

val check_dup_ctors_flat = Q.prove (
`!defs.
  check_dup_ctors (defs:type_def) =
  ALL_DISTINCT (MAP FST (build_tdefs mn defs))`,
 srw_tac[][check_dup_ctors_thm, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
     build_tdefs_def,
     rich_listTheory.MAP_REVERSE, ALL_DISTINCT_REVERSE]);

val MEM_flat_alloc_tags_REVERSE_build_tdefs_imp2 = prove(
  ``MEM (k,m,t) (flat_alloc_tags n (REVERSE (build_tdefs mn tdefs))) ⇒
    check_dup_ctors (tdefs:type_def) ⇒
    ∃tn tvs constrs a. t =
      SOME (TypeId (mk_id mn tn)) ∧ n ≤ m ∧ m < n + LENGTH (build_tdefs mn tdefs) ∧
      MEM (tvs,tn,constrs) tdefs ∧ MEM (k,a) constrs ∧
      ALOOKUP (build_tdefs mn tdefs) k = SOME (LENGTH a,TypeId(mk_id mn tn))``,
  simp[flat_alloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,ZIP_COUNT_LIST,MAP_GENLIST,MEM_GENLIST,UNCURRY] >>
  srw_tac[][] >>
  imp_res_tac check_dup_ctors_flat >>
  first_x_assum(qspec_then`mn`strip_assume_tac) >>
  imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
  qmatch_assum_rename_tac`n < LENGTH _` >>
  `∃a b c. EL n (REVERSE (build_tdefs mn tdefs)) = (a,b,c)` by simp[GSYM EXISTS_PROD] >> full_simp_tac(srw_ss())[] >>
  `MEM (a,b,c) (build_tdefs mn tdefs)` by (
    simp[MEM_EL] >> rev_full_simp_tac(srw_ss())[EL_REVERSE] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl o SYM) >>
    simp[] ) >>
  srw_tac[][] >>
  first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
  qpat_assum`MEM X Y` mp_tac >>
  simp[build_tdefs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD,mk_id_inj] >>
  metis_tac[] );

val ALOOKUP_flat_alloc_tags_galloc_tags = prove(
  ``∀ls n cn t x.
    ALOOKUP (galloc_tags n ls) (cn,t) = SOME x ⇒
    ALL_DISTINCT (MAP FST ls) ⇒
    ∃z. ALOOKUP (flat_alloc_tags n ls) cn = SOME (FST x,z)``,
  Induct >> simp[galloc_tags_nil,flat_alloc_tags_nil] >>
  qx_gen_tac`p`>>PairCases_on`p` >>
  simp[galloc_tags_cons,flat_alloc_tags_cons] >>
  srw_tac[][] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >> TRY (metis_tac[]) >>
  imp_res_tac ALOOKUP_MEM >>
  `MEM (cn,t) (MAP FST (galloc_tags (n+1) ls))` by (
    simp[MEM_MAP] >> metis_tac[pair_CASES,FST] ) >>
  full_simp_tac(srw_ss())[MAP_FST_galloc_tags] >>
  full_simp_tac(srw_ss())[MEM_MAP,UNCURRY] >> metis_tac[]);

val mod_decs_def = Define`
  mod_decs mod ds = EVERY (λd. case d of
   | Dtype_i1 mn _ => mn = SOME mod
   | Dexn_i1 mn _ _ => mn = SOME mod
   | _ => T) ds`;

val mod_decs_cons_imp = prove(
  ``mod_decs mod (d::ds) ⇒ mod_decs mod ds``,
  srw_tac[][mod_decs_def]);

val not_mod_decs_def = Define`
  not_mod_decs ds = EVERY (λd. case d of
   | Dtype_i1 mn _ => mn = NONE
   | Dexn_i1 mn _ _ => mn = NONE
   | _ => T) ds`;

val not_mod_decs_cons_imp = prove(
  ``not_mod_decs (d::ds) ⇒ not_mod_decs ds``,
  srw_tac[][not_mod_decs_def])

val envC_tagged_add_empty_mod = prove(
  ``∀ls mn tagenv g.
      envC_tagged ([(mn,[])],[]) (mod_tagenv (SOME mn) ls tagenv) g``,
  rpt gen_tac >> PairCases_on`tagenv`>>
  srw_tac[][envC_tagged_def,mod_tagenv_def,lookup_alist_mod_env_def] >>
  every_case_tac >> full_simp_tac(srw_ss())[FLOOKUP_UPDATE] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[FLOOKUP_DEF]);

val envC_tagged_add_empty_mod = prove(
  ``∀ls mn tagenv g envC.
      envC_tagged envC tagenv g ⇒
      envC_tagged (merge_alist_mod_env ([(mn,[])],[]) envC) (mod_tagenv (SOME mn) ls tagenv) g``,
  rpt gen_tac >> PairCases_on`tagenv`>> PairCases_on`envC` >>
  simp[envC_tagged_def,mod_tagenv_def,lookup_alist_mod_env_def,merge_alist_mod_env_def,
       lookup_tag_env_def,FLOOKUP_UPDATE,lookup_tag_flat_def] >>
  srw_tac[][] >>
  first_x_assum(qspec_then`cn`mp_tac) >>
  full_simp_tac(srw_ss())[FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
  every_case_tac >> full_simp_tac(srw_ss())[] );

val ALOOKUP_galloc_tags_flat_alloc_tags = prove(
  ``∀ls n cn a b c d t.
    ALOOKUP (flat_alloc_tags n ls) a = SOME (b,c) ∧
    ALOOKUP ls a = SOME (d,t)
    ⇒ ALOOKUP (galloc_tags n ls) (a,t) = SOME (b,d)``,
  Induct >> simp[ALOOKUP_APPEND] >>
  qx_gen_tac`p` >> PairCases_on`p` >>
  simp[flat_alloc_tags_cons,galloc_tags_cons,ALOOKUP_APPEND] >>
  rpt gen_tac >>
  every_case_tac >> srw_tac[][]);

val decs_to_i2_correct = Q.prove (
`!ck genv envC s ds r.
  evaluate_decs_i1 ck genv envC s ds r
  ⇒
  !res s1 tids s1_i2 genv_i2 tagenv_st ds_i2 tagenv_st' exh' genv' envC' s' tids' gtagenv exh.
    s = (s1,tids) ∧
    r = ((s',tids'), envC', genv', res) ∧
    res ≠ SOME Rtype_error ∧
    no_dup_types_i1 ds ∧
    decs_to_i2 tagenv_st ds = (tagenv_st', exh', ds_i2) ∧
    cenv_inv envC exh (get_tagenv tagenv_st) gtagenv ∧
    s_to_i2 gtagenv s1 s1_i2 ∧
    LIST_REL (OPTREL (v_to_i2 gtagenv)) genv genv_i2 ∧
    DISJOINT (FDOM exh') (FDOM exh) ∧
    alloc_tags_invariant tids tagenv_st gtagenv
    ⇒
    ?genv'_i2 s'_i2 res_i2 gtagenv' acc'.
      gtagenv_weak gtagenv gtagenv' ∧
      evaluate_decs_i2 ck (FUNION exh' exh) genv_i2 s1_i2 ds_i2 (s'_i2,genv'_i2,res_i2) ∧
      vs_to_i2 gtagenv' genv' genv'_i2 ∧
      s_to_i2 gtagenv' s' s'_i2 ∧
      alloc_tags_invariant tids' tagenv_st' gtagenv' ∧
      gtagenv_wf gtagenv' ∧
      get_tagacc tagenv_st' = FUNION acc' (get_tagacc tagenv_st) ∧
      exhaustive_env_correct (exh' ⊌ exh) gtagenv' ∧
      (res = NONE ∧ res_i2 = NONE ∧ FDOM acc' = set (MAP FST envC') ∧
       flat_envC_tagged envC' acc' gtagenv'
       ∨
       ((*(∀mn. mod_decs mn ds ⇒
          envC_tagged ([mn,envC'],[]) (mod_tagenv (SOME mn) acc' (get_tagenv tagenv_st)) gtagenv') ∧ *)
       ?err err_i2.
         res = SOME err ∧ res_i2 = SOME err_i2 ∧
         result_to_i2 (\a b c. T) gtagenv' (Rerr err) (Rerr err_i2)))`,
 ho_match_mp_tac evaluate_decs_i1_strongind >>
 srw_tac[][decs_to_i2_def] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[LET_THM, evaluate_dec_i1_cases] >>
 srw_tac[][]
 >- (full_simp_tac(srw_ss())[Once evaluate_decs_i2_cases, v_to_i2_eqns, merge_alist_mod_env_empty, flat_envC_tagged_def] >>
     metis_tac [gtagenv_weak_refl, cenv_inv_def, FUNION_FEMPTY_1, FDOM_FEMPTY])
 >- (`?tagenv_st' exh' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st', exh', ds_i2)` by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][Once evaluate_decs_i2_cases] >>
     `env_all_to_i2 (get_tagenv tagenv_st) (genv,envC,[]) (exh,genv_i2,[]) gtagenv`
                 by (full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
                     srw_tac[][] >>
                     srw_tac[][v_to_i2_eqns]) >>
     `?s'_i2 r_i2 count' s''.
        result_to_i2 v_to_i2 gtagenv (Rerr e) r_i2 ∧
        s_to_i2 gtagenv s' s'_i2 ∧
        evaluate_i2 ck (exh,genv_i2,[]) s1_i2 (exp_to_i2 (get_tagenv tagenv_st) e') (s'_i2,r_i2)`
           by (imp_res_tac exp_to_i2_correct >>
               full_simp_tac(srw_ss())[] >>
               pop_assum mp_tac >>
               srw_tac[][] >>
               res_tac >>
               full_simp_tac(srw_ss())[] >>
               res_tac >>
               full_simp_tac(srw_ss())[] >>
               metis_tac []) >>
     srw_tac[][evaluate_dec_i2_cases] >>
     `alloc_tags_invariant tids tagenv_st' gtagenv` by metis_tac [decs_to_i2_inv_weak] >>
     `?acc'. get_tagacc tagenv_st' = FUNION acc' (get_tagacc tagenv_st)`
                 by metis_tac [tagacc_accumulates] >>
     `exhaustive_env_correct (exh' ⊌ exh) gtagenv` by (
       full_simp_tac(srw_ss())[cenv_inv_def,exhaustive_env_correct_def] >>
       conj_tac >- (
         ho_match_mp_tac IN_FRANGE_FUNION_suff >>
         metis_tac[decs_to_i2_exh_wf] ) >>
       simp[FLOOKUP_FUNION] >> srw_tac[][] >>
       BasicProvers.CASE_TAC >- metis_tac[] >>
       imp_res_tac FDOM_decs_to_i2_exh >>
       full_simp_tac(srw_ss())[alloc_tags_invariant_def] >>
       full_simp_tac(srw_ss())[PULL_EXISTS,FLOOKUP_DEF,IN_DISJOINT] >>
       metis_tac[] ) >>
     simp[envC_tagged_add_empty_mod] >>
     full_simp_tac(srw_ss())[result_to_i2_cases, v_to_i2_eqns] >>
     srw_tac[][merge_alist_mod_env_empty, flat_envC_tagged_def] >>
     metis_tac [gtagenv_weak_refl, cenv_inv_def, evaluate_exp_i2_exh_weak, SND,
                result_11, error_result_distinct])
 >- (`?tagenv_st' exh' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st', exh', ds_i2)` by metis_tac [pair_CASES] >>
     imp_res_tac no_dup_types_i1_cons_imp >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][Once evaluate_decs_i2_cases] >>
     full_simp_tac(srw_ss())[] >>
     `env_all_to_i2 (get_tagenv tagenv_st) (genv,envC,[]) (exh,genv_i2,[]) gtagenv`
                 by (full_simp_tac(srw_ss())[env_all_to_i2_cases] >>
                     srw_tac[][v_to_i2_eqns] >>
                     every_case_tac >>
                     metis_tac []) >>
     `?r_i2 s'_i2. result_to_i2 v_to_i2 gtagenv (Rval (Conv_i1 NONE new_env)) r_i2 ∧
                s_to_i2 gtagenv s2 s'_i2 ∧
                evaluate_i2 ck (exh,genv_i2,[]) s1_i2 (exp_to_i2 (get_tagenv tagenv_st) e) (s'_i2,r_i2)`
                     by (imp_res_tac exp_to_i2_correct >>
                         full_simp_tac(srw_ss())[] >>
                         res_tac >>
                         full_simp_tac(srw_ss())[] >>
                         metis_tac []) >>
     srw_tac[][evaluate_dec_i2_cases] >>
     full_simp_tac(srw_ss())[result_to_i2_cases, v_to_i2_eqns, merge_alist_mod_env_empty] >>
     srw_tac[][] >>
     `LIST_REL (OPTREL (v_to_i2 gtagenv)) (MAP SOME new_env) (MAP SOME vs')`
            by (`OPTREL (v_to_i2 gtagenv) = (\x y. OPTREL (v_to_i2 gtagenv) x y)` by metis_tac [] >>
                ONCE_ASM_REWRITE_TAC [] >>
                srw_tac[][LIST_REL_MAP1, LIST_REL_MAP2, combinTheory.o_DEF, OPTREL_def] >>
                full_simp_tac(srw_ss())[vs_to_i2_list_rel, eta2]) >>
     `LIST_REL (OPTREL (v_to_i2 gtagenv)) (genv ++ MAP SOME new_env) (genv_i2++MAP SOME vs')`
                  by metis_tac [EVERY2_APPEND, LIST_REL_LENGTH] >>
     FIRST_X_ASSUM (qspecl_then [`s'_i2`, `genv_i2 ++ MAP SOME vs'`, `tagenv_st`, `ds_i2'`, `tagenv_st'`, `exh'`, `gtagenv`, `exh`] mp_tac) >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[] >>
     `vs_to_i2 gtagenv'' (new_env ++ new_env') (vs' ++ genv'_i2)`
                  by metis_tac [vs_to_i2_append, length_vs_to_i2, v_to_i2_weakening] >>
     metis_tac [length_vs_to_i2, cenv_inv_def, evaluate_exp_i2_exh_weak, SND,
                result_distinct, result_11, error_result_distinct, mod_decs_cons_imp])
 >- (`?tagenv_st' exh' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st',exh',ds_i2)` by metis_tac [pair_CASES] >>
     imp_res_tac no_dup_types_i1_cons_imp >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     full_simp_tac(srw_ss())[merge_alist_mod_env_empty] >>
     `LIST_REL (OPTREL (v_to_i2 gtagenv))
               (genv ++ MAP SOME (MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l))
               (genv_i2 ++ MAP SOME (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 (get_tagenv tagenv_st) e)) l))`
              by metis_tac [recfun_helper, LIST_REL_LENGTH, EVERY2_APPEND] >>
     FIRST_X_ASSUM (qspecl_then [`s1_i2`, `genv_i2 ++ MAP SOME (MAP (λ(f,x,e).  Closure_i2 [] x (exp_to_i2 (get_tagenv tagenv_st) e)) l)`, 
                                 `tagenv_st`, `ds_i2'`, `tagenv_st'`, `exh'`, `gtagenv`, `exh`] mp_tac) >>
     srw_tac[][] >>
     srw_tac[][Once evaluate_decs_i2_cases, evaluate_dec_i2_cases] >>
     `vs_to_i2 gtagenv'
               (MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l ++ new_env')
               (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 (get_tagenv tagenv_st) e)) l ++ genv'_i2)`
               by (metis_tac [recfun_helper2, v_to_i2_weakening, vs_to_i2_append, length_vs_to_i2]) >>
     full_simp_tac(srw_ss())[funs_to_i2_map , MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM PEXISTS_THM] >>
     full_simp_tac(srw_ss())[result_to_i2_cases] >>
     metis_tac [pair_CASES,mod_decs_cons_imp])
 >- (
   first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   imp_res_tac no_dup_types_i1_cons_imp >>
   rev_full_simp_tac(srw_ss())[] >>
   qmatch_assum_rename_tac`DISJOINT (_ mn tdefs) tids` >>
   full_simp_tac(srw_ss())[] >>
   first_x_assum(fn th => first_assum (mp_tac o (MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))) >>
   first_assum(mp_tac o MATCH_MP alloc_tags_inv_weak) >>
   disch_then(qspecl_then[`mn`,`tdefs`]strip_assume_tac) >>
   simp[alloc_tags_eqns,FOLDL_insert_tag_env] >>
   first_assum(mp_tac o (MATCH_MP cenv_inv_to_mod)) >>
   qabbrev_tac`emptys = { (mk_id mn tn) | ∃tvs. MEM (tvs,tn,[]) tdefs }` >>
   `FINITE emptys` by (
      qsuff_tac`∃f. emptys ⊆ IMAGE f (set tdefs)` >-
        metis_tac[IMAGE_FINITE,SUBSET_FINITE,FINITE_LIST_TO_SET] >>
      simp[Abbr`emptys`,SUBSET_DEF] >>
      qexists_tac`λx. mk_id mn (FST(SND x))` >>
      srw_tac[][EXISTS_PROD] >> metis_tac[]) >>
   disch_then(qspecl_then[`REVERSE (build_tdefs mn tdefs)`,`get_next tagenv_st`,`FUN_FMAP (K (LN:unit spt)) emptys`]mp_tac) >>
   simp[] >>
   discharge_hyps >- (
     full_simp_tac(srw_ss())[alloc_tags_invariant_def,cenv_inv_def] >> simp[] >>
     simp[IN_FRANGE_FLOOKUP,PULL_EXISTS,FORALL_PROD] >>
     conj_tac >- ( srw_tac[][] >> res_tac >> simp[] ) >>
     conj_tac >- (
       simp[MAP_REVERSE,ALL_DISTINCT_REVERSE] >>
       metis_tac[check_dup_ctors_flat] ) >>
     full_simp_tac(srw_ss())[IN_DISJOINT,SUBSET_DEF,PULL_EXISTS,FORALL_PROD,type_defs_to_new_tdecs_def,Abbr`emptys`] >>
     simp[build_tdefs_def] >>
     full_simp_tac(srw_ss())[MEM_MAP,MEM_FLAT,UNCURRY,FORALL_PROD,PULL_EXISTS] >>
     full_simp_tac(srw_ss())[FDOM_build_exh_env,MEM_MAP,FORALL_PROD] >>
     metis_tac[] ) >>
   strip_tac >>
   ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
   full_simp_tac(srw_ss())[] >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
   disch_then(qspecl_then[`s1_i2`,`genv_i2`]mp_tac) >>
   Q.PAT_ABBREV_TAC`g2 = gtagenv |++ X` >>
   `gtagenv_weak gtagenv g2` by (
     qunabbrev_tac`g2` >>
     match_mp_tac gtagenv_weak_galloc_tags_build_tdefs >>
     full_simp_tac(srw_ss())[cenv_inv_def,alloc_tags_invariant_def] >>
     conj_tac >- (
       full_simp_tac(srw_ss())[IN_DISJOINT,SUBSET_DEF,PULL_EXISTS] >>
       metis_tac[] ) >>
     conj_tac >- full_simp_tac(srw_ss())[combinTheory.o_DEF,LAMBDA_PROD] >>
     simp[IN_FRANGE_FLOOKUP,PULL_EXISTS,FORALL_PROD] >>
     srw_tac[][] >> res_tac >> simp[] ) >>
   discharge_hyps >- (
     full_simp_tac(srw_ss())[s_to_i2_cases] >>
     full_simp_tac(srw_ss())[] >>
     conj_tac >- metis_tac[sv_to_i2_weakening, LIST_REL_mono] >>
     conj_tac >- (
       match_mp_tac EVERY2_MEM_MONO >>
       HINT_EXISTS_TAC >> simp[UNCURRY] >>
       simp[OPTREL_def] >> srw_tac[][] >> srw_tac[][] >>
       metis_tac[v_to_i2_weakening] ) >>
     conj_tac >- (
       reverse conj_tac >- metis_tac[DISJOINT_SYM] >>
       simp[FDOM_alloc_tags_to_exh,Abbr`emptys`] >>
       imp_res_tac FDOM_decs_to_i2_exh >>
       pop_assum SUBST1_TAC >>
       simp[MAP_SND_o_SND_flat_alloc_tags,MAP_REVERSE] >>
       simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD,build_tdefs_def,MEM_FLAT] >>
       qsuff_tac`DISJOINT (type_defs_to_new_tdecs mn tdefs) (IMAGE TypeId (tids_of_decs ds))` >- (
         simp[IN_DISJOINT,type_defs_to_new_tdecs_def,MEM_MAP,FORALL_PROD,PULL_FORALL] >>
         metis_tac[tid_or_exn_11] ) >>
       qpat_assum`no_dup_types_i1 (X::Y)`mp_tac >>
       simp[IN_DISJOINT,no_dup_types_i1_def,decs_to_types_i1_def,ALL_DISTINCT_APPEND,tids_of_decs_def,
            MEM_FLAT,MEM_MAP,type_defs_to_new_tdecs_def,PULL_EXISTS,FORALL_PROD] >>
       srw_tac[][] >> spose_not_then strip_assume_tac >> srw_tac[][] >> pop_assum mp_tac >>
       BasicProvers.CASE_TAC >> simp[] >>
       simp[MEM_MAP,FORALL_PROD] >>
       spose_not_then strip_assume_tac >>
       full_simp_tac(srw_ss())[mk_id_inj] >> srw_tac[][] >>
       first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
       simp[] >> HINT_EXISTS_TAC >> simp[] >>
       simp[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
     full_simp_tac(srw_ss())[alloc_tags_invariant_def,Abbr`g2`,FDOM_FUPDATE_LIST,MAP_FST_galloc_tags] >>
     conj_tac >- (
       full_simp_tac(srw_ss())[SUBSET_DEF,PULL_EXISTS] >>
       simp[type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY,EXISTS_PROD] >>
       simp[build_tdefs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,UNCURRY,FORALL_PROD] >>
       metis_tac[] ) >>
     reverse conj_tac >- (
       simp[alloc_tags_eqns,flookup_fupdate_list] >>
       rpt gen_tac >> BasicProvers.CASE_TAC >- (
         srw_tac[][] >> res_tac >> simp[] ) >>
       srw_tac[][] >> imp_res_tac ALOOKUP_MEM >> full_simp_tac(srw_ss())[] >>
       imp_res_tac MEM_flat_alloc_tags_REVERSE_build_tdefs_imp2 >>
       simp[] ) >>
     simp[flookup_fupdate_list] >>
     rpt gen_tac >>
     BasicProvers.CASE_TAC >- metis_tac[] >>
     imp_res_tac ALOOKUP_MEM >> srw_tac[][] >>
     full_simp_tac(srw_ss())[galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,PULL_EXISTS,EXISTS_PROD,MEM_ZIP,
        alloc_tags_eqns,EL_COUNT_LIST] >> simp[] ) >>
   Q.PAT_ABBREV_TAC`exh1 = build_exh_env mn X tdefs` >>
   Q.PAT_ABBREV_TAC`exh2 = alloc_tags_to_exh X ⊌ Y` >>
   `exh1 = exh2` by (
     simp[fmap_eq_flookup] >>
     `FDOM exh1 = FDOM exh2` by (
       simp[Abbr`exh1`,FDOM_build_exh_env,Abbr`exh2`,FDOM_alloc_tags_to_exh,
            FDOM_FUPDATE_LIST,MAP_FST_galloc_tags,MAP_SND_o_SND_flat_alloc_tags] >>
       simp[build_tdefs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD,Abbr`emptys`] >>
       simp[EXTENSION,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
       srw_tac[][EQ_IMP_THM] >> TRY(metis_tac[]) >>
       simp[mk_id_inj] >>
       qmatch_assum_rename_tac`MEM (a,b,c) tdefs` >>
       Cases_on`c`>>metis_tac[pair_CASES,MEM] ) >>
     qx_gen_tac`k` >>
     Cases_on`FLOOKUP exh2 k` >- full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
     full_simp_tac(srw_ss())[Abbr`exh2`,FLOOKUP_FUNION] >>
     pop_assum mp_tac >>
     BasicProvers.CASE_TAC >- (
       rev_full_simp_tac(srw_ss())[FLOOKUP_FUN_FMAP] >>
       rev_full_simp_tac(srw_ss())[Abbr`emptys`] >>
       srw_tac[][Abbr`exh1`] >>
       Cases_on`alloc_tags mn tagenv_st tdefs` >>
       srw_tac[][build_exh_env_def,flookup_fupdate_list] >>
       BasicProvers.CASE_TAC >- (
         imp_res_tac ALOOKUP_FAILS >>
         full_simp_tac(srw_ss())[MEM_MAP,UNCURRY,FORALL_PROD,mk_id_inj] ) >>
       qmatch_assum_abbrev_tac`ALOOKUP ls k = SOME v` >>
       `ALL_DISTINCT (MAP FST ls)` by (
         simp[Abbr`ls`,MAP_REVERSE,ALL_DISTINCT_REVERSE,MAP_MAP_o,UNCURRY,combinTheory.o_DEF] >>
         simp[GSYM combinTheory.o_DEF] >> simp[Once (GSYM MAP_MAP_o)] >>
         match_mp_tac ALL_DISTINCT_MAP_INJ >>
         simp[mk_id_inj] >>
         simp[combinTheory.o_DEF,LAMBDA_PROD] ) >>
       `MEM (k,LN) ls` by (
         simp[Abbr`ls`,MEM_MAP,EXISTS_PROD,Abbr`k`,mk_id_inj] >>
         metis_tac[FOLDL] ) >>
       imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
       full_simp_tac(srw_ss())[] ) >>
     srw_tac[][Abbr`exh1`] >>
     imp_res_tac FLOOKUP_alloc_tags_to_exh_imp >>
     qmatch_abbrev_tac`FLOOKUP fm k = SOME x` >>
     Cases_on`FLOOKUP fm k` >- (
       full_simp_tac(srw_ss())[FLOOKUP_DEF,EXTENSION] >>
       metis_tac[] ) >>
     simp[Abbr`fm`] >>
     first_assum(mp_tac o (MATCH_MP FLOOKUP_build_exh_env_imp)) >>
     discharge_hyps >- ( simp[combinTheory.o_DEF,LAMBDA_PROD] ) >>
     strip_tac >>
     simp[nat_set_eq_thm] >>
     simp[EXTENSION,alloc_tags_eqns,flookup_fupdate_list] >>
     simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
     srw_tac[][EQ_IMP_THM] >- (
       BasicProvers.CASE_TAC >- (
         imp_res_tac ALOOKUP_FAILS >>
         full_simp_tac(srw_ss())[flat_alloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,EXISTS_PROD,PULL_EXISTS,MEM_ZIP] >>
         qmatch_assum_rename_tac`MEM (a,b) constrs` >>
         qsuff_tac`MEM a (MAP FST (build_tdefs mn tdefs))` >- (
           simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
           metis_tac[MEM_EL,MEM_REVERSE,LENGTH_REVERSE] ) >>
         simp[build_tdefs_def,MEM_MAP,EXISTS_PROD,MEM_FLAT,PULL_EXISTS] >>
         metis_tac[] ) >>
       qmatch_assum_abbrev_tac`ALOOKUP ls k = SOME v` >>
       `ALL_DISTINCT (MAP FST ls)` by (
         simp[Abbr`ls`,MAP_REVERSE,ALL_DISTINCT_REVERSE,MAP_FST_flat_alloc_tags] >>
         rator_x_assum`check_dup_ctors`mp_tac >>
         metis_tac[check_dup_ctors_flat] ) >>
       first_assum(mp_tac o MATCH_MP (GEN_ALL MEM_flat_alloc_tags_REVERSE_build_tdefs_suff)) >>
       disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
       disch_then(qspecl_then[`mn`,`get_next tagenv_st`]mp_tac) >> strip_tac >>
       qmatch_assum_abbrev_tac`MEM (k,w) rls` >>
       `MEM (k,w) ls` by simp[Abbr`ls`] >>
       `SOME v = SOME w` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
       full_simp_tac(srw_ss())[Abbr`w`,Abbr`rls`,Abbr`ls`] >>
       metis_tac[] ) >>
     qmatch_assum_rename_tac`MEM (k,m,_) _` >>
     qexists_tac`k` >>
     BasicProvers.CASE_TAC >- (
       imp_res_tac ALOOKUP_FAILS >> full_simp_tac(srw_ss())[] ) >>
     qmatch_assum_abbrev_tac`ALOOKUP ls k = SOME v` >>
     `ALL_DISTINCT (MAP FST ls)` by (
       simp[Abbr`ls`,MAP_REVERSE,ALL_DISTINCT_REVERSE,MAP_FST_flat_alloc_tags] >>
       rator_x_assum`check_dup_ctors`mp_tac >>
       metis_tac[check_dup_ctors_flat] ) >>
     qmatch_assum_abbrev_tac`MEM (k,w) rls` >>
     `SOME v = SOME w` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM,MEM_REVERSE] >>
     full_simp_tac(srw_ss())[Abbr`v`,Abbr`w`,Abbr`rls`] >>
     imp_res_tac MEM_flat_alloc_tags_REVERSE_build_tdefs_imp >>
     qmatch_assum_abbrev_tac`ALL_DISTINCT (MAP f tdefs)` >>
     `∃n1 n2. n1 < LENGTH tdefs ∧ n2 < LENGTH tdefs ∧ EL n1 tdefs = (tvs,tn,constrs) ∧ EL n2 tdefs = (tvs',tn,constrs')` by (
       metis_tac[MEM_EL] ) >>
     `EL n1 (MAP f tdefs) = EL n2 (MAP f tdefs)` by (
       simp[EL_MAP,Abbr`f`] ) >>
     `n1 = n2` by metis_tac[EL_ALL_DISTINCT_EL_EQ,LENGTH_MAP] >>
     full_simp_tac(srw_ss())[] >> metis_tac[] ) >>
   pop_assum (assume_tac o SYM) >>
   map_every qunabbrev_tac[`exh1`,`exh2`] >> full_simp_tac(srw_ss())[] >>
   simp[FUNION_ASSOC] >>
   strip_tac >> simp[] >> rpt BasicProvers.VAR_EQ_TAC >>
   ONCE_REWRITE_TAC[CONJ_COMM] >>
   ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   simp[LEFT_EXISTS_AND_THM] >>
   (reverse conj_tac >- metis_tac[gtagenv_weak_trans]) >>
   (FUNION_alist_to_fmap
    |> Q.SPEC`REVERSE ls`
    |> GSYM
    |> SIMP_RULE list_ss []
    |> C cons nil
    |> SIMP_TAC std_ss ) >>
   simp[Once FUNION_ASSOC] >>
   TRY (
     qho_match_abbrev_tac`∃acc'. (foo ⊌ bar = acc' ⊌ bar)` >>
     qexists_tac`foo` >> simp[] >> NO_TAC) >>
   qho_match_abbrev_tac`∃acc'. (foo ⊌ bar = acc' ⊌ bar) ∧ Z acc'` >>
   qexists_tac`foo` >>
   simp[Abbr`Z`,Abbr`foo`] >>
   simp[MAP_REVERSE,MAP_FST_flat_alloc_tags] >>
   Q.ISPEC_THEN`acc'`(SUBST1_TAC o SYM)(Q.GEN`fm`fmap_to_alist_to_fmap) >>
   REWRITE_TAC[FUNION_alist_to_fmap] >>
   (FUNION_alist_to_fmap
    |> CONV_RULE SWAP_FORALL_CONV
    |> Q.SPEC`FEMPTY`
    |> SIMP_RULE (srw_ss())[FUNION_FEMPTY_2]
    |> C cons nil
    |> ONCE_REWRITE_TAC) >>
   ONCE_REWRITE_TAC[GSYM FUPDATE_LIST_APPEND] >>
   match_mp_tac flat_envC_tagged_append >>
   simp[MAP_REVERSE] >>
   (FUNION_alist_to_fmap
    |> CONV_RULE SWAP_FORALL_CONV
    |> Q.SPEC`FEMPTY`
    |> SIMP_RULE (srw_ss())[FUNION_FEMPTY_2]
    |> GSYM
    |> C cons nil
    |> ONCE_REWRITE_TAC) >>
   simp[MAP_FST_flat_alloc_tags,MAP_REVERSE,ALL_DISTINCT_REVERSE] >>
   (conj_tac >- metis_tac[check_dup_ctors_flat]) >>
   (conj_tac >- metis_tac[gtagenv_wf_def]) >>
   match_mp_tac flat_envC_tagged_weakening >>
   qexists_tac`g2` >> simp[] >>
   simp[Abbr`g2`,flat_envC_tagged_def] >>
   simp[lookup_tag_flat_def,flookup_fupdate_list] >>
   rpt gen_tac >>
   strip_tac >>
   reverse conj_tac >- (
     BasicProvers.CASE_TAC >> simp[] >>
     BasicProvers.CASE_TAC >> simp[] >>
     imp_res_tac ALOOKUP_MEM >>
     imp_res_tac MEM_flat_alloc_tags_REVERSE_build_tdefs_imp2 >>
     PairCases_on`tagenv_st`>>full_simp_tac(srw_ss())[alloc_tags_invariant_def,get_next_def] >>
     DECIDE_TAC) >>
   srw_tac[][] >>
   imp_res_tac ALOOKUP_MEM >>
   (BasicProvers.CASE_TAC >- (
      imp_res_tac ALOOKUP_FAILS >>
      qsuff_tac`F`>-srw_tac[][] >>
      pop_assum mp_tac >> simp[] >>
      qmatch_abbrev_tac`∃v. MEM (k,v) ls` >>
      qsuff_tac`MEM k (MAP FST ls)` >- (simp[MEM_MAP,EXISTS_PROD] >> metis_tac[]) >>
      simp[Abbr`ls`,MAP_FST_galloc_tags] >>
      simp[MEM_MAP,Abbr`k`,EXISTS_PROD] >>
      metis_tac[] )) >>
   qmatch_assum_abbrev_tac`ALOOKUP (REVERSE ls) k = SOME x` >>
   `ALL_DISTINCT (MAP FST ls)` by (
     simp[Abbr`ls`,MAP_FST_galloc_tags,ALL_DISTINCT_REVERSE,MAP_REVERSE] >>
     qmatch_abbrev_tac`ALL_DISTINCT (MAP f ls)` >>
     `ALL_DISTINCT (MAP FST ls)` by metis_tac[check_dup_ctors_flat] >>
     Q.ISPEC_THEN`FST`match_mp_tac ALL_DISTINCT_MAP >>
     simp[Abbr`f`,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
   full_simp_tac(srw_ss())[alookup_distinct_reverse,Abbr`ls`,Abbr`k`] >>
   first_assum(mp_tac o MATCH_MP ALOOKUP_flat_alloc_tags_galloc_tags) >>
   (discharge_hyps >- (
      metis_tac[MAP_REVERSE,ALL_DISTINCT_REVERSE,check_dup_ctors_flat] )) >>
   srw_tac[][] >> srw_tac[][] >>
   qmatch_assum_abbrev_tac`ALOOKUP ls (cn,t) = SOME x` >>
   qsuff_tac`∃v. MEM ((cn,t),v,num_args) ls` >- (
     strip_tac >>
     imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >>
     full_simp_tac(srw_ss())[] >> srw_tac[][] ) >>
   simp[Abbr`ls`,galloc_tags_def,MAP2_MAP,LENGTH_COUNT_LIST,MEM_MAP,
        PULL_EXISTS,FORALL_PROD,EXISTS_PROD,MEM_ZIP] >>
   metis_tac[MEM_EL,MEM_REVERSE,LENGTH_REVERSE] )
 >- (
   first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   imp_res_tac no_dup_types_i1_cons_imp >>
   rev_full_simp_tac(srw_ss())[] >>
   qmatch_assum_rename_tac`TypeExn (mk_id mn xn) ∉ tids` >>
   full_simp_tac(srw_ss())[] >>
   first_x_assum(fn th => first_assum (mp_tac o (MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th)))) >>
   simp[] >>
   qabbrev_tac`gtagenv' = gtagenv |+ ((xn,TypeExn(mk_id mn xn)),get_next tagenv_st,LENGTH l)` >>
   `∀cn. (cn,TypeExn (mk_id mn xn)) ∉ FDOM gtagenv` by (
     full_simp_tac(srw_ss())[alloc_tags_invariant_def,SUBSET_DEF,PULL_EXISTS,FORALL_PROD] >>
     metis_tac[] ) >>
   `gtagenv_weak gtagenv gtagenv' ∧ gtagenv_wf gtagenv'` by (
     simp[gtagenv_weak_def,Abbr`gtagenv'`,FLOOKUP_UPDATE] >>
     simp[] >>
     full_simp_tac(srw_ss())[alloc_tags_invariant_def,gtagenv_wf_def,FLOOKUP_UPDATE] >>
     conj_asm1_tac >- (
       conj_tac >- (
         srw_tac[][] >> simp[] >>
         full_simp_tac(srw_ss())[cenv_inv_def,gtagenv_wf_def] ) >>
       conj_tac >- ( srw_tac[][] >> metis_tac[] ) >>
       full_simp_tac(srw_ss())[cenv_inv_def,gtagenv_wf_def] >>
       srw_tac[][] >> full_simp_tac(srw_ss())[] >>
       metis_tac[prim_recTheory.LESS_REFL,arithmeticTheory.GREATER_DEF] ) >>
     conj_tac >- metis_tac[] >>
     conj_tac >- (
       pop_assum kall_tac >>
       full_simp_tac(srw_ss())[cenv_inv_def,gtagenv_wf_def,has_exns_def,FLOOKUP_UPDATE] >>
       srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_DEF] ) >>
     conj_tac >- (
       pop_assum kall_tac >>
       full_simp_tac(srw_ss())[cenv_inv_def,gtagenv_wf_def,has_bools_def,FLOOKUP_UPDATE] >>
       srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_DEF] ) >>
     conj_tac >- (
       pop_assum kall_tac >>
       full_simp_tac(srw_ss())[cenv_inv_def,gtagenv_wf_def,has_lists_def,FLOOKUP_UPDATE] >>
       srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_DEF] ) >>
     pop_assum (MATCH_ACCEPT_TAC o CONJUNCT2 o CONJUNCT2)) >>
   disch_then(qspecl_then[`s1_i2`,`genv_i2`,`gtagenv'`,`exh`]mp_tac) >>
   discharge_hyps >- (
     simp[] >>
     conj_tac >- (
       full_simp_tac(srw_ss())[cenv_inv_def] >>
       PairCases_on`envC` >>
       PairCases_on`tagenv_st` >>
       simp[merge_alist_mod_env_def,alloc_tag_def,get_tagenv_def] >>
       full_simp_tac(srw_ss())[envC_tagged_def,get_tagenv_def,lookup_alist_mod_env_def] >>
       conj_tac >- (
         rpt gen_tac >>
         first_x_assum(qspec_then`cn`mp_tac) >>
         reverse BasicProvers.CASE_TAC >> simp[lookup_tag_env_insert] >- (
           simp[Abbr`gtagenv'`,FLOOKUP_UPDATE] >>
           BasicProvers.CASE_TAC >>
           BasicProvers.CASE_TAC >>
           disch_then(fn th => disch_then (fn th2 => assume_tac th2 >> mp_tac (MATCH_MP th th2))) >>
           strip_tac >>
           full_simp_tac(srw_ss())[FLOOKUP_DEF] >> metis_tac[] ) >>
         simp [FLOOKUP_UPDATE, FLOOKUP_FUNION] >>
         reverse BasicProvers.CASE_TAC >> simp[lookup_tag_env_insert] >- (
           disch_then(fn th => disch_then (fn th2 => assume_tac th2 >> mp_tac (MATCH_MP th th2))) >>
           simp[Abbr`gtagenv'`,FLOOKUP_UPDATE,id_to_n_def] ) >>
         simp[Abbr`gtagenv'`,FLOOKUP_UPDATE,id_to_n_def,get_next_def] >>
         full_simp_tac(srw_ss())[alloc_tags_invariant_def,get_next_def] >>
         simp[] ) >>
       full_simp_tac(srw_ss())[exhaustive_env_correct_def,Abbr`gtagenv'`,FLOOKUP_UPDATE] ) >>
     full_simp_tac(srw_ss())[s_to_i2_cases] >>
     full_simp_tac(srw_ss())[] >>
     conj_tac >- metis_tac[sv_to_i2_weakening, LIST_REL_mono] >>
     conj_tac >- (
       match_mp_tac EVERY2_MEM_MONO >>
       HINT_EXISTS_TAC >> simp[UNCURRY] >>
       simp[OPTREL_def] >> srw_tac[][] >> srw_tac[][] >>
       metis_tac[v_to_i2_weakening] ) >>
     PairCases_on`tagenv_st` >>
     full_simp_tac(srw_ss())[alloc_tags_invariant_def,Abbr`gtagenv'`,alloc_tag_def,get_next_def,FLOOKUP_UPDATE,get_tagacc_def] >>
     simp[] >>
     conj_tac >- full_simp_tac(srw_ss())[SUBSET_DEF] >>
     srw_tac[][] >> simp[] >> res_tac >> simp[] ) >>
   strip_tac >> simp[] >> rpt BasicProvers.VAR_EQ_TAC >>
   ONCE_REWRITE_TAC[CONJ_COMM] >>
   ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   simp[LEFT_EXISTS_AND_THM] >>
   (reverse conj_tac >- metis_tac[gtagenv_weak_trans]) >>
   PairCases_on`tagenv_st` >>
   simp[alloc_tag_def,get_tagacc_def] >>
   simp[Once FUPDATE_EQ_FUNION] >>
   simp[Once FUNION_ASSOC] >>
   TRY(
     qho_match_abbrev_tac`∃acc'. (foo ⊌ bar = acc' ⊌ bar)` >>
     qexists_tac`foo` >> simp[] >> NO_TAC ) >>
   qho_match_abbrev_tac`∃acc'. (foo ⊌ bar = acc' ⊌ bar) ∧ Z acc'` >>
   qexists_tac`foo`>>simp[Abbr`Z`,Abbr`foo`] >>
   Q.ISPEC_THEN`acc'`(SUBST1_TAC o SYM)(Q.GEN`fm`fmap_to_alist_to_fmap) >>
   REWRITE_TAC[FUNION_alist_to_fmap] >>
   ONCE_REWRITE_TAC[FUPDATE_EQ_FUPDATE_LIST] >>
   ONCE_REWRITE_TAC[GSYM FUPDATE_LIST_APPEND] >>
   match_mp_tac flat_envC_tagged_append >>
   REWRITE_TAC[GSYM FUNION_alist_to_fmap,FUNION_FEMPTY_2] >>
   simp[MAP_REVERSE] >>
   simp[flat_envC_tagged_def,lookup_tag_flat_def,FLOOKUP_UPDATE] >>
   conj_tac >- metis_tac[gtagenv_wf_def] >>
   reverse conj_tac >- (
     full_simp_tac(srw_ss())[alloc_tags_invariant_def,get_next_def] >>
     DECIDE_TAC ) >>
   match_mp_tac (GEN_ALL (MP_CANON FLOOKUP_SUBMAP)) >>
   full_simp_tac(srw_ss())[gtagenv_weak_def] >>
   HINT_EXISTS_TAC >> simp[Abbr`gtagenv'`] >>
   simp_tac (srw_ss()) [FLOOKUP_UPDATE] >>
   simp[get_next_def] ));

val to_i2_invariant_def = Define `
to_i2_invariant mods tids envC exh tagenv_st gtagenv s s_i2 genv genv_i2 ⇔
  set (MAP FST (FST envC)) ⊆ mods ∧
  (∀x. Short x ∈ FDOM exh ⇒ TypeId (Short x) ∈ tids) ∧
  (∀mn x. Long mn x ∈ FDOM exh ⇒ mn ∈ mods) ∧
  cenv_inv envC exh (FST (SND tagenv_st)) gtagenv ∧
  s_to_i2 gtagenv s s_i2 ∧
  LIST_REL (OPTION_REL (v_to_i2 gtagenv)) genv genv_i2 ∧
  alloc_tags_invariant tids (tagenv_st,FEMPTY:conN |-> (num # tid_or_exn option)) gtagenv`;

fun dec_lem t =
(SIMP_RULE (srw_ss()) [] o
 GEN_ALL o
 Q.INST [`res` |-> t] o
 SPEC_ALL o
 SIMP_RULE (srw_ss()) [PULL_FORALL]) decs_to_i2_correct

val list_rel_optrel_args = Q.prove (
`!gtagenv. LIST_REL (OPTREL (v_to_i2 gtagenv)) = LIST_REL (\x y. OPTREL (v_to_i2 gtagenv) x y)`,
 srw_tac[][eta2]);

val decs_to_i2_dummy_env_num_defs =prove(
  ``∀ds x y z ds2.
    decs_to_i2 x ds = (y,z,ds2) ⇒
    decs_to_dummy_env ds = num_defs ds2``,
  Induct >> simp[decs_to_i2_def,decs_to_dummy_env_def,num_defs_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >> srw_tac[][] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  srw_tac[][] >>
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
    srw_tac[][lookup_alist_mod_env_def,lookup_tag_env_def,lookup_tag_flat_def,FLOOKUP_FUNION,ALOOKUP_APPEND] >>
    first_x_assum(qspec_then`cn`mp_tac) >>
    pop_assum mp_tac >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >- (
        imp_res_tac ALOOKUP_NONE >>
        `FLOOKUP acc a = NONE` by (
          full_simp_tac(srw_ss())[FLOOKUP_DEF] ) >>
        simp[] >> strip_tac >>
        full_simp_tac(srw_ss())[gtagenv_weak_def] >>
        metis_tac[FLOOKUP_SUBMAP] ) >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
      simp[id_to_n_def] >> strip_tac >>
      BasicProvers.CASE_TAC >> simp[] >- (
        BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
        BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
      BasicProvers.CASE_TAC >> simp[] >>
      srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >-
        metis_tac[gtagenv_weak_def] >>
      BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
    BasicProvers.CASE_TAC >>
    strip_tac >>
    full_simp_tac(srw_ss())[gtagenv_weak_def] >>
    metis_tac[FLOOKUP_SUBMAP] ) >>
  simp[lookup_alist_mod_env_def,lookup_tag_flat_def,lookup_tag_env_def,FLOOKUP_UPDATE] >>
  srw_tac[][] >>
  first_x_assum(qspec_then`cn`mp_tac) >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >- (
    full_simp_tac(srw_ss())[gtagenv_weak_def] >>
    metis_tac[FLOOKUP_SUBMAP] ) >>
  srw_tac[][] >> full_simp_tac(srw_ss())[FLOOKUP_UPDATE, FLOOKUP_FUNION] >- (
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[id_to_n_def] >> srw_tac[][] >- metis_tac[gtagenv_weak_def] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
  metis_tac[gtagenv_weak_def,FLOOKUP_SUBMAP]);

val IN_tids_of_mod_decs = prove(
  ``∀ds mn x. x ∈ tids_of_decs ds ⇒ mod_decs mn ds ⇒ ∃y. x = Long mn y``,
  Induct >> simp[tids_of_decs_thm] >> full_simp_tac(srw_ss())[mod_decs_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> TRY(metis_tac[]) >> srw_tac[][] >>
  full_simp_tac(srw_ss())[mk_id_def,MEM_MAP])

val IN_tids_of_not_mod_decs = prove(
  ``∀ds x. x ∈ tids_of_decs ds ⇒ not_mod_decs ds ⇒ ∃y. x = Short y``,
  Induct >> simp[tids_of_decs_thm] >> full_simp_tac(srw_ss())[not_mod_decs_def] >> srw_tac[][] >>
  every_case_tac >> full_simp_tac(srw_ss())[] >> TRY(metis_tac[]) >> srw_tac[][] >>
  full_simp_tac(srw_ss())[mk_id_def,MEM_MAP])

val evaluate_dec_i1_tids_acc = store_thm("evaluate_dec_i1_tids_acc",
  ``∀ck genv envC st d res. evaluate_dec_i1 ck genv envC st d res ⇒
      SND st ⊆ SND (FST res)``,
  ho_match_mp_tac evaluate_dec_i1_ind >> simp[])

val evaluate_decs_i1_tids_acc = store_thm("evaluate_decs_i1_tids_acc",
  ``∀ck genv envC st ds res. evaluate_decs_i1 ck genv envC st ds res ⇒
      SND st ⊆ SND(FST res)``,
  ho_match_mp_tac evaluate_decs_i1_ind >> simp[] >> srw_tac[][] >>
  first_x_assum(mp_tac o MATCH_MP evaluate_dec_i1_tids_acc) >>
  full_simp_tac(srw_ss())[] >> metis_tac[SUBSET_TRANS])

val mod_decs_decs_to_i1 = store_thm("mod_decs_decs_to_i1",
  ``∀ds mn a b c. mod_decs mn (SND (SND (decs_to_i1 a (SOME mn) b c ds)))``,
  Induct >> simp[decs_to_i1_def] >> full_simp_tac(srw_ss())[mod_decs_def] >> srw_tac[][] >>
  simp[UNCURRY] >> srw_tac[][dec_to_i1_def] >>
  BasicProvers.CASE_TAC >> simp[]);

(* Proved before the assumptons about mod_decs and not_mod_decs and LENGTH ds
 * were built in to the semantics of modLang. But left for now with the better
 * version immediately following, and using this one. *)
val prompt_to_i2_correct_lem = Q.prove (
`!ck genv envC s tids mods prompt s_i2 genv_i2 tagenv_st prompt_i2 genv' envC' s' tids' mods' res gtagenv tagenv_st' exh exh'.
  evaluate_prompt_i1 ck genv envC (s,tids,mods) prompt ((s',tids',mods'), envC', genv', res) ∧
  res ≠ SOME Rtype_error ∧
  to_i2_invariant mods tids envC exh tagenv_st gtagenv s s_i2 genv genv_i2 ∧
  (tagenv_st', exh', prompt_i2) = prompt_to_i2 tagenv_st prompt ∧
  (∀ds. prompt = Prompt_i1 NONE ds ⇒ LENGTH ds < 2 ∧ not_mod_decs ds) ∧
  (∀ds mn. prompt = Prompt_i1 (SOME mn) ds ⇒ mod_decs mn ds)
  ⇒
  ?genv'_i2 s'_i2 res_i2 gtagenv' new_envC.
    gtagenv_weak gtagenv gtagenv' ∧
    DISJOINT (FDOM exh') (FDOM exh) ∧
    evaluate_prompt_i2 ck (FUNION exh' exh) genv_i2 s_i2 prompt_i2 (s'_i2,genv'_i2,res_i2) ∧
    to_i2_invariant mods' tids' new_envC (FUNION exh' exh) tagenv_st' gtagenv' s' s'_i2 (genv++genv') (genv_i2 ++ genv'_i2) ∧
    (res = NONE ∧ res_i2 = NONE ∧ new_envC = (merge_alist_mod_env envC' envC) ∨
     ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ new_envC = envC ∧
                  result_to_i2 (\a b c. T) gtagenv' (Rerr err) (Rerr err_i2))`,
 srw_tac[][evaluate_prompt_i1_cases, evaluate_prompt_i2_cases, prompt_to_i2_def, LET_THM] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 `?next' tagenv' inv'' acc exh'' ds_i2. decs_to_i2 (tagenv_st,FEMPTY) ds = (((next',tagenv',inv''),acc),exh'',ds_i2)` by metis_tac [pair_CASES] >>
 full_simp_tac(srw_ss())[] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[to_i2_invariant_def]
 >- (`DISJOINT (FDOM exh') (FDOM exh)` by (
         imp_res_tac FDOM_decs_to_i2_exh >>
         simp[IN_DISJOINT] >>
         Cases_on`mn` >> full_simp_tac(srw_ss())[] >- (
           Cases_on`ds`>-full_simp_tac(srw_ss())[decs_to_i2_def,tids_of_decs_thm]>>
           Cases_on`t`>>fsrw_tac[ARITH_ss][]>>
           full_simp_tac(srw_ss())[decs_to_i2_def,tids_of_decs_thm] >>
           BasicProvers.CASE_TAC >> simp[] >> full_simp_tac(srw_ss())[LET_THM] >> srw_tac[][] >>
           full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >>
           full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >>
           srw_tac[][] >>
           full_simp_tac(srw_ss())[Once evaluate_dec_i1_cases] >> srw_tac[][] >>
           full_simp_tac(srw_ss())[type_defs_to_new_tdecs_def,IN_DISJOINT,MEM_MAP,FORALL_PROD] >>
           full_simp_tac(srw_ss())[not_mod_decs_def,mk_id_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
           metis_tac[] ) >>
         srw_tac[][] >>
         spose_not_then strip_assume_tac >>
         first_x_assum(mp_tac o MATCH_MP IN_tids_of_mod_decs) >>
         disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
         strip_tac >> srw_tac[][] >>
         metis_tac[] ) >>
     `∃genv'_i2 s'_i2 gtagenv' acc'.
       gtagenv_weak gtagenv gtagenv' ∧
       evaluate_decs_i2 ck (FUNION exh' exh) genv_i2 s_i2 ds_i2 (s'_i2,genv'_i2,NONE) ∧
       vs_to_i2 gtagenv' env genv'_i2 ∧
       s_to_i2 gtagenv' s' s'_i2 ∧
       alloc_tags_invariant tids' ((next',tagenv',inv''),acc) gtagenv' ∧
       gtagenv_wf gtagenv' ∧
       get_tagacc ((next',tagenv',inv''),acc) = acc' ⊌ get_tagacc (tagenv_st,FEMPTY) ∧
       exhaustive_env_correct (exh' ⊌ exh) gtagenv' ∧
       FDOM acc' = set (MAP FST cenv') ∧
       flat_envC_tagged cenv' acc' gtagenv'
       (*∧
       cenv_inv (merge_envC (emp,cenv') envC) exh'' (get_tagenv (next',tagenv',inv'',acc)) gtagenv'*)`
           by (match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] (dec_lem `NONE`)) >>
               PairCases_on `tagenv_st` >>
               full_simp_tac(srw_ss())[get_tagenv_def] >>
               metis_tac []) >>
     srw_tac[][] >>
     Q.LIST_EXISTS_TAC [`MAP SOME genv'_i2`, `s'_i2`, `gtagenv'`] >>
     full_simp_tac(srw_ss())[get_tagenv_def] >>
     conj_tac >- (
       PairCases_on`envC`>> Cases_on`mn`>>
       srw_tac[][mod_cenv_def,update_mod_state_def,merge_alist_mod_env_def] >>
       full_simp_tac(srw_ss())[SUBSET_DEF] >>
       metis_tac[]) >>
     imp_res_tac FDOM_decs_to_i2_exh >>
     imp_res_tac evaluate_decs_i1_tids_acc >> full_simp_tac(srw_ss())[] >>
     conj_tac >- (
       PairCases_on`envC`>> Cases_on`mn`>>
       srw_tac[][mod_cenv_def,update_mod_state_def,merge_alist_mod_env_def] >>
       full_simp_tac(srw_ss())[SUBSET_DEF] ) >>
     conj_tac >- (
       gen_tac >> reverse strip_tac >- metis_tac[SUBSET_DEF] >>
       reverse(Cases_on`mn`)>>full_simp_tac(srw_ss())[]>-(
         imp_res_tac IN_tids_of_mod_decs >> full_simp_tac(srw_ss())[] ) >>
       Cases_on`ds`>-full_simp_tac(srw_ss())[tids_of_decs_thm]>>
       Cases_on`t`>>fsrw_tac[ARITH_ss][]>>
       full_simp_tac(srw_ss())[tids_of_decs_thm,not_mod_decs_def] >>
       Cases_on`h`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>full_simp_tac(srw_ss())[mk_id_def,MEM_MAP]>>
       full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >>
       full_simp_tac(srw_ss())[Once evaluate_dec_i1_cases] >>
       full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >>
       srw_tac[][type_defs_to_new_tdecs_def] >>
       srw_tac[][MEM_MAP,UNCURRY,mk_id_def] >>
       metis_tac[] ) >>
     conj_tac >- (
       simp[update_mod_state_def] >>
       rpt gen_tac >> reverse strip_tac >- (
         BasicProvers.CASE_TAC >> srw_tac[][] >>
         metis_tac[] ) >>
       BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >- (
         imp_res_tac IN_tids_of_not_mod_decs >> full_simp_tac(srw_ss())[] ) >>
       imp_res_tac IN_tids_of_mod_decs >> full_simp_tac(srw_ss())[] ) >>
     srw_tac[][]
     >- (
       full_simp_tac(srw_ss())[cenv_inv_def] >>
       match_mp_tac envC_tagged_extend >>
       PairCases_on`tagenv_st`>>
       full_simp_tac(srw_ss())[get_tagacc_def,get_tagenv_def,FUNION_FEMPTY_2] >> srw_tac[][] )
     >- (
       match_mp_tac EVERY2_APPEND_suff >>
       conj_tac >- (
         match_mp_tac EVERY2_MEM_MONO >>
         HINT_EXISTS_TAC >> simp[UNCURRY] >>
         simp[optionTheory.OPTREL_def] >>
         srw_tac[][FORALL_PROD] >> srw_tac[][] >>
         metis_tac[v_to_i2_weakening] ) >>
       simp[EVERY2_MAP,optionTheory.OPTREL_def] >>
       srw_tac[boolSimps.ETA_ss][] >>
       full_simp_tac(srw_ss())[vs_to_i2_list_rel] )
     >- (
       full_simp_tac(srw_ss())[alloc_tags_invariant_def,get_next_def,get_tagacc_def] >>
       full_simp_tac(srw_ss())[gtagenv_wf_def]))
 >- (
   first_assum(mp_tac o MATCH_MP decs_to_i2_correct) >> simp[] >>
   disch_then(mp_tac o REWRITE_RULE[GSYM AND_IMP_INTRO]) >>
   PairCases_on`tagenv_st`>>
   rpt (
     first_assum(fn th => disch_then (fn th2 => mp_tac (MATCH_MP th2 th))) >>
     full_simp_tac(srw_ss())[get_tagenv_def]) >>
   discharge_hyps_keep >- (
     imp_res_tac FDOM_decs_to_i2_exh >>
     simp[IN_DISJOINT] >>
     Cases_on`mn` >> full_simp_tac(srw_ss())[] >- (
       Cases_on`ds`>-full_simp_tac(srw_ss())[decs_to_i2_def,tids_of_decs_thm]>>
       Cases_on`t`>>fsrw_tac[ARITH_ss][]>>
       full_simp_tac(srw_ss())[decs_to_i2_def,tids_of_decs_thm] >>
       BasicProvers.CASE_TAC >> simp[] >> full_simp_tac(srw_ss())[LET_THM] >> srw_tac[][] >>
       full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >>
       full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >>
       srw_tac[][] >>
       full_simp_tac(srw_ss())[Once evaluate_dec_i1_cases] >> srw_tac[][] >>
       full_simp_tac(srw_ss())[type_defs_to_new_tdecs_def,IN_DISJOINT,MEM_MAP,FORALL_PROD] >>
       full_simp_tac(srw_ss())[not_mod_decs_def,mk_id_def] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
       metis_tac[] ) >>
     srw_tac[][] >>
     spose_not_then strip_assume_tac >>
     first_x_assum(mp_tac o MATCH_MP IN_tids_of_mod_decs) >>
     disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
     strip_tac >> srw_tac[][] >>
     metis_tac[] ) >>
   disch_then(qx_choosel_then[`genv'_i2`,`s'_i2`,`res_i2`,`gtagenv'`,`acc'`]strip_assume_tac) >>
   srw_tac[][] >>
   Q.LIST_EXISTS_TAC [`MAP SOME genv'_i2 ++ GENLIST (λn. NONE) (num_defs ds_i2 − LENGTH genv'_i2)`, `s'_i2`, `SOME err_i2`, `gtagenv'`] >>
   full_simp_tac(srw_ss())[get_tagenv_def] >>
   conj_tac >- metis_tac[] >>
   conj_tac >- (
     Cases_on`mn`>>srw_tac[][update_mod_state_def] >>
     full_simp_tac(srw_ss())[SUBSET_DEF] ) >>
   imp_res_tac FDOM_decs_to_i2_exh >>
   imp_res_tac evaluate_decs_i1_tids_acc >> full_simp_tac(srw_ss())[] >>
   conj_tac >- (
     gen_tac >> reverse strip_tac >- metis_tac[SUBSET_DEF] >>
     reverse(Cases_on`mn`)>>full_simp_tac(srw_ss())[]>-(
       imp_res_tac IN_tids_of_mod_decs >> full_simp_tac(srw_ss())[] ) >>
     Cases_on`ds`>-full_simp_tac(srw_ss())[tids_of_decs_thm]>>
     Cases_on`t`>>fsrw_tac[ARITH_ss][]>>
     full_simp_tac(srw_ss())[tids_of_decs_thm,not_mod_decs_def] >>
     Cases_on`h`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>full_simp_tac(srw_ss())[mk_id_def,MEM_MAP]>>
     full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >>
     full_simp_tac(srw_ss())[Once evaluate_dec_i1_cases] >>
     full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >>
     srw_tac[][type_defs_to_new_tdecs_def] >>
     srw_tac[][MEM_MAP,UNCURRY,mk_id_def] >>
     metis_tac[] ) >>
   conj_tac >- (
     simp[update_mod_state_def] >>
     rpt gen_tac >> reverse strip_tac >- (
       BasicProvers.CASE_TAC >> srw_tac[][] >>
       metis_tac[] ) >>
     BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >- (
       imp_res_tac IN_tids_of_not_mod_decs >> full_simp_tac(srw_ss())[] ) >>
     imp_res_tac IN_tids_of_mod_decs >> full_simp_tac(srw_ss())[] ) >>
   srw_tac[][]
   >- (
     full_simp_tac(srw_ss())[cenv_inv_def] >>
     full_simp_tac(srw_ss())[get_tagacc_def,get_tagenv_def,FUNION_FEMPTY_2] >> srw_tac[][] >>
     Cases_on`mn`>>full_simp_tac(srw_ss())[mod_cenv_def]>-(
       PairCases_on`envC` >>
       full_simp_tac(srw_ss())[mod_tagenv_def,merge_alist_mod_env_def] >>
       Cases_on`ds` >- (
         full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] ) >>
       Cases_on`t`>>fsrw_tac[ARITH_ss][]>>srw_tac[][]>>
       full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] >- (
         srw_tac[][] >>
         full_simp_tac(srw_ss())[Once evaluate_dec_i1_cases] >> srw_tac[][] >>
         full_simp_tac(srw_ss())[decs_to_i2_def,LET_THM] >> srw_tac[][FUNION_FEMPTY_1] >>
         full_simp_tac(srw_ss())[envC_tagged_def,gtagenv_weak_def] >>
         srw_tac[][] >>
         first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
         srw_tac[][] >> srw_tac[][] >>
         metis_tac[FLOOKUP_SUBMAP] ) >>
       full_simp_tac(srw_ss())[Once evaluate_decs_i1_cases] ) >>
     PairCases_on`envC` >> simp[merge_alist_mod_env_def] >>
     full_simp_tac(srw_ss())[envC_tagged_def,lookup_alist_mod_env_def] >> strip_tac >>
     rpt gen_tac >>
     rpt (first_x_assum(qspec_then`cn`mp_tac)) >>
     BasicProvers.CASE_TAC >- (
       simp[mod_tagenv_def,lookup_tag_env_def] >>
       metis_tac[gtagenv_weak_def,FLOOKUP_SUBMAP] ) >>
     srw_tac[][] >> every_case_tac >> full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[lookup_tag_env_def,mod_tagenv_def,FLOOKUP_UPDATE] >>
     first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
     BasicProvers.CASE_TAC >- full_simp_tac(srw_ss())[gtagenv_wf_def] >>
     srw_tac[][] >- (
       imp_res_tac ALOOKUP_MEM >>
       full_simp_tac(srw_ss())[SUBSET_DEF, MEM_MAP] >>
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
         srw_tac[][FORALL_PROD] >> srw_tac[][] >>
         metis_tac[v_to_i2_weakening] ) >>
       simp[EVERY2_MAP,optionTheory.OPTREL_def] >>
       srw_tac[boolSimps.ETA_ss][] >>
       full_simp_tac(srw_ss())[vs_to_i2_list_rel] ) >>
     qsuff_tac`decs_to_dummy_env ds = num_defs ds_i2` >- (
       full_simp_tac(srw_ss())[vs_to_i2_list_rel] >>
       imp_res_tac EVERY2_LENGTH >> srw_tac[][] >>
       simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] ) >>
     metis_tac[decs_to_i2_dummy_env_num_defs])
   >- (
     full_simp_tac(srw_ss())[alloc_tags_invariant_def,get_next_def,get_tagacc_def] >>
     full_simp_tac(srw_ss())[gtagenv_wf_def])));

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
 srw_tac[][] >>
 match_mp_tac prompt_to_i2_correct_lem >>
 MAP_EVERY qexists_tac [`s`, `tids`, `mods`, `prompt`, `tagenv_st`] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[evaluate_prompt_i1_cases] >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[prompt_mods_ok_def, not_mod_decs_def, mod_decs_def]);

val evaluate_dec_i2_exh_weak = prove(
  ``∀ck (exh:exh_ctors_env) genv s d res.
      evaluate_dec_i2 ck exh genv s d res ⇒
      ∀exh'. DISJOINT (FDOM exh) (FDOM exh') ∧ SND res ≠ Rerr Rtype_error
        ⇒ evaluate_dec_i2 ck (exh' ⊌ exh) genv s d res``,
  ho_match_mp_tac evaluate_dec_i2_ind >> srw_tac[][] >>
  TRY (
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 evaluate_exp_i2_exh_weak)) >> simp[] >>
    disch_then(qspec_then`exh'`mp_tac) >> simp[DISJOINT_SYM] >> strip_tac ) >>
  srw_tac[][Once evaluate_dec_i2_cases] );

val evaluate_decs_i2_exh_weak = prove(
 ``∀ck (exh:exh_ctors_env) genv s ds res.
     evaluate_decs_i2 ck exh genv s ds res
     ⇒
     ∀exh'. DISJOINT (FDOM exh) (FDOM exh') ∧ SND (SND res) ≠ SOME Rtype_error ⇒
       evaluate_decs_i2 ck (exh' ⊌ exh) genv s ds res``,
  ho_match_mp_tac evaluate_decs_i2_ind >> srw_tac[][]
  >- srw_tac[][Once evaluate_decs_i2_cases] >>
  first_x_assum(strip_assume_tac o MATCH_MP evaluate_dec_i2_exh_weak) >>
  first_x_assum(qspec_then`exh'`strip_assume_tac) >> rev_full_simp_tac(srw_ss())[] >>
  srw_tac[][Once evaluate_decs_i2_cases] >>
  metis_tac[]);

val evaluate_prompt_i2_exh_weak = Q.prove (
`!ck (exh:exh_ctors_env) genv s p s' genv' res exh1.
 evaluate_prompt_i2 ck exh genv s p (s',genv',res) ∧
 DISJOINT (FDOM exh1) (FDOM exh) ∧ res ≠ SOME Rtype_error
 ⇒
 evaluate_prompt_i2 ck (exh1 ⊌ exh) genv s p (s',genv',res)`,
 srw_tac[][evaluate_prompt_i2_cases] >>
 first_x_assum(strip_assume_tac o MATCH_MP evaluate_decs_i2_exh_weak) >>
 first_x_assum(qspec_then`exh1`mp_tac) >>
 srw_tac[][] >> metis_tac[DISJOINT_SYM]);

val tids_of_prompt_def = Define`
  tids_of_prompt (Prompt_i1 _ ds) = tids_of_decs ds`;

val FDOM_prompt_to_i2_exh = prove(
  ``∀x p y z a. prompt_to_i2 x p = (y,z,a) ⇒ FDOM z = tids_of_prompt p``,
  srw_tac[][prompt_to_i2_def] >> every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM,UNCURRY] >> srw_tac[][] >>
  srw_tac[][tids_of_prompt_def] >>
  match_mp_tac FDOM_decs_to_i2_exh >>
  metis_tac[pair_CASES,FST,SND,PAIR_EQ]);

val tids_of_prog_def = Define`
  tids_of_prog prog = BIGUNION (set (MAP tids_of_prompt prog))`;

val FDOM_prog_to_i2_exh = prove(
  ``∀x p y z a. prog_to_i2 x p = (y,z,a) ⇒ FDOM z = tids_of_prog p``,
  Induct_on`p`>>srw_tac[][prog_to_i2_def,tids_of_prog_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[LET_THM,tids_of_prog_def] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  res_tac >> simp[] >>
  imp_res_tac FDOM_prompt_to_i2_exh >>
  simp[UNION_COMM]);

val evaluate_decs_i1_tids_disjoint = prove(
  ``∀ck genv envC st ds res. evaluate_decs_i1 ck genv envC st ds res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_decs ds)) (SND st)``,
  ho_match_mp_tac evaluate_decs_i1_ind >> simp[] >>
  conj_tac >- simp[tids_of_decs_thm] >>
  srw_tac[][evaluate_dec_i1_cases,tids_of_decs_thm] >> full_simp_tac(srw_ss())[DISJOINT_SYM] >>
  full_simp_tac(srw_ss())[type_defs_to_new_tdecs_def,IN_DISJOINT,MEM_MAP,UNCURRY] >>
  metis_tac[]);

val evaluate_decs_i1_tids = prove(
  ``∀ck genv envC st ds res. evaluate_decs_i1 ck genv envC st ds res ⇒
      SND(SND(SND res)) = NONE ⇒
      {id | TypeId id ∈ SND(FST res)} = (tids_of_decs ds) ∪ {id | TypeId id ∈ SND st}``,
  ho_match_mp_tac evaluate_decs_i1_ind >> simp[] >>
  conj_tac >- simp[tids_of_decs_thm] >>
  srw_tac[][evaluate_dec_i1_cases,tids_of_decs_thm] >> full_simp_tac(srw_ss())[] >>
  simp[EXTENSION,type_defs_to_new_tdecs_def,MEM_MAP,PULL_EXISTS,UNCURRY] >>
  metis_tac[])

val evaluate_prompt_i1_tids_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_prompt p)) (FST(SND stm))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[] >> srw_tac[][] >>
  imp_res_tac evaluate_decs_i1_tids_disjoint >> full_simp_tac(srw_ss())[tids_of_prompt_def]);

val evaluate_prompt_i1_tids_acc = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      FST(SND stm) ⊆ FST(SND(FST res))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[] >> srw_tac[][] >>
  imp_res_tac evaluate_decs_i1_tids_acc >> full_simp_tac(srw_ss())[]);

val evaluate_prompt_i1_tids = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      {id | TypeId id ∈ FST(SND(FST res))} = (tids_of_prompt p) ∪ {id | TypeId id ∈ FST(SND stm)}``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[] >> srw_tac[][] >>
  imp_res_tac evaluate_decs_i1_tids >> full_simp_tac(srw_ss())[tids_of_prompt_def])

val evaluate_prog_i1_tids_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prog_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (IMAGE TypeId (tids_of_prog p)) (FST(SND stm))``,
  ho_match_mp_tac evaluate_prog_i1_ind >> simp[] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[tids_of_prog_def] >>
  imp_res_tac evaluate_prompt_i1_tids_disjoint >> full_simp_tac(srw_ss())[] >>
  imp_res_tac evaluate_prompt_i1_tids_acc >>
  full_simp_tac(srw_ss())[IN_DISJOINT,SUBSET_DEF] >>
  metis_tac[]);

val mods_of_prog_def = Define`
  mods_of_prog [] = {} ∧
  mods_of_prog ((Prompt_i1 (SOME mn) ds)::ps) = mn INSERT mods_of_prog ps ∧
  mods_of_prog (_::ps) = mods_of_prog ps`

val IN_mods_of_prog = prove(
  ``∀prog mn ds. MEM (Prompt_i1 (SOME mn) ds) prog ⇒ mn ∈ mods_of_prog prog``,
  Induct >> simp[mods_of_prog_def] >> srw_tac[][] >> simp[mods_of_prog_def] >>
  `∃x y. h = Prompt_i1 x y` by (Cases_on`h` >> simp[GSYM EXISTS_PROD]) >>
  Cases_on`x`>>simp[mods_of_prog_def] >>
  metis_tac[])

val evaluate_prog_i1_mods_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prog_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      DISJOINT (SND(SND stm)) (mods_of_prog p)``,
  ho_match_mp_tac evaluate_prog_i1_ind >> simp[] >>
  simp[mods_of_prog_def] >> srw_tac[][] >>
  full_simp_tac(srw_ss())[evaluate_prompt_i1_cases] >> srw_tac[][] >>
  Cases_on`mn`>>full_simp_tac(srw_ss())[mods_of_prog_def,update_mod_state_def] >>
  full_simp_tac(srw_ss())[IN_DISJOINT] >> metis_tac[])

val evaluate_prompt_i1_mods_disjoint = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      SND(SND(SND res)) = NONE ⇒
      ∀mn ds. p = Prompt_i1 (SOME mn) ds ⇒ mn ∉ (SND(SND stm))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[])

val evaluate_prompt_i1_mods_acc = prove(
  ``∀ck genv envC stm p res. evaluate_prompt_i1 ck genv envC stm p res ⇒
      SND(SND stm) ⊆ SND(SND(FST res))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >> simp[] >>
  srw_tac[][update_mod_state_def] >>
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
 srw_tac[][no_dup_mods_i1_def, prog_i1_to_mods_def] >>
 every_case_tac >>
 srw_tac[][] >>
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
 srw_tac[][no_dup_top_types_i1_def, prog_i1_to_top_types_def] >>
 every_case_tac >>
 srw_tac[][ALL_DISTINCT_APPEND, DISJOINT_DEF, EXTENSION] >>
 full_simp_tac(srw_ss())[MEM_MAP] >>
 metis_tac []);

val evaluate_prog_i1_prompt_ok = prove(
  ``∀a b c d e f. evaluate_prog_i1 a b c d e f ⇒
    ∀g h. MEM (Prompt_i1 g h) e ∧ SND(SND(SND f)) = NONE ⇒
    prompt_mods_ok g h``,
  ho_match_mp_tac evaluate_prog_i1_ind >>
  srw_tac[][] >> res_tac >> full_simp_tac(srw_ss())[evaluate_prompt_i1_cases]);

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
 srw_tac[][] >>
 imp_res_tac FDOM_prompt_to_i2_exh >>
 imp_res_tac FDOM_prog_to_i2_exh >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[no_dup_mods_i1_eqn, no_dup_top_types_i1_eqn] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[tids_of_prompt_def, LET_THM]
 >- (
   full_simp_tac(srw_ss())[IN_DISJOINT,decs_to_types_i1_def,prog_i1_to_top_types_def,
      tids_of_decs_def,tids_of_prog_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   spose_not_then strip_assume_tac >>
   every_case_tac >> full_simp_tac(srw_ss())[MEM_MAP] >> srw_tac[][] >>
   qmatch_assum_rename_tac`MEM (Dtype_i1 mno tds) decs` >>
   qmatch_assum_rename_tac`MEM td tds` >>
   PairCases_on`td` >>
   first_x_assum(qspec_then`td1`mp_tac) >> simp[PULL_EXISTS] >>
   HINT_EXISTS_TAC >> simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   qmatch_assum_rename_tac`MEM prompt prog` >>
   Cases_on`prompt`>>full_simp_tac(srw_ss())[tids_of_prompt_def] >>
   HINT_EXISTS_TAC >> simp[] >>
   full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> full_simp_tac(srw_ss())[] >>
   full_simp_tac(srw_ss())[prompt_mods_ok_def,EVERY_MEM] >>
   res_tac >> full_simp_tac(srw_ss())[mk_id_def] >>
   BasicProvers.CASE_TAC >- (
     simp[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
     simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     srw_tac[][] >>
     every_case_tac >> full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[MEM_MAP] >>
     HINT_EXISTS_TAC >> simp[MEM_MAP,EXISTS_PROD] >>
     PairCases_on`y`>>Cases_on`o'`>>full_simp_tac(srw_ss())[mk_id_def]>>metis_tac[]) >>
   qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
   simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   spose_not_then strip_assume_tac >>
   every_case_tac >> full_simp_tac(srw_ss())[] >>
   res_tac >> full_simp_tac(srw_ss())[MEM_MAP,mk_id_def] )
 >- (
   pop_assum kall_tac >>
   full_simp_tac(srw_ss())[IN_DISJOINT,tids_of_decs_def,tids_of_prog_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   spose_not_then strip_assume_tac >> every_case_tac >> full_simp_tac(srw_ss())[] >>
   full_simp_tac(srw_ss())[prompt_mods_ok_def,EVERY_MEM] >> res_tac >> full_simp_tac(srw_ss())[] >>
   full_simp_tac(srw_ss())[MEM_MAP,mk_id_def] >> srw_tac[][] >>
   qmatch_assum_rename_tac`MEM p prog` >>
   Cases_on`p`>>full_simp_tac(srw_ss())[tids_of_prompt_def] >>
   qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
   simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   spose_not_then strip_assume_tac >>
   pop_assum mp_tac >> BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[MEM_MAP] >>
   res_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
   every_case_tac >> full_simp_tac(srw_ss())[mk_id_def] >>
   spose_not_then strip_assume_tac >> srw_tac[][] >>
   full_simp_tac(srw_ss())[prog_i1_to_mods_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
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
 srw_tac[][] >>
 imp_res_tac FDOM_prog_to_i2_exh >>
 srw_tac[][] >>
 full_simp_tac(srw_ss())[no_dup_mods_i1_eqn, no_dup_top_types_i1_eqn] >>
 every_case_tac >>
 full_simp_tac(srw_ss())[tids_of_prompt_def]
 >- (
   full_simp_tac(srw_ss())[IN_DISJOINT] >>
   spose_not_then strip_assume_tac >>
   Cases_on`x` >- (
     rator_x_assum`no_dup_top_types_i1`mp_tac >>
     res_tac >> simp[no_dup_top_types_i1_def] >>
     simp[IN_DISJOINT,MEM_MAP,PULL_EXISTS] >>
     full_simp_tac(srw_ss())[tids_of_prog_def,prog_i1_to_top_types_def,MEM_MAP,MEM_FLAT,PULL_EXISTS] >>
     disj2_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[tids_of_prompt_def] >>
     BasicProvers.CASE_TAC >> simp[] >- (
       full_simp_tac(srw_ss())[tids_of_decs_def,decs_to_types_i1_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       every_case_tac >> full_simp_tac(srw_ss())[] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[UNCURRY] >>
       qmatch_assum_rename_tac`Short a = mk_id mno _` >>
       Cases_on`mno`>>full_simp_tac(srw_ss())[mk_id_def] ) >>
     full_simp_tac(srw_ss())[EVERY_MEM] >>
     res_tac >> full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[prompt_mods_ok_def] >>
     full_simp_tac(srw_ss())[EVERY_MEM,tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     every_case_tac >> full_simp_tac(srw_ss())[] >>
     res_tac >> full_simp_tac(srw_ss())[MEM_MAP,mk_id_def]) >>
   full_simp_tac(srw_ss())[no_dup_mods_i1_def,IN_DISJOINT] >> res_tac >>
   full_simp_tac(srw_ss())[prog_i1_to_mods_def,tids_of_prog_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   qmatch_assum_rename_tac`mn ∈ mods` >>
   first_x_assum(qspec_then`mn`mp_tac) >>
   first_x_assum(qspec_then`mn`mp_tac) >>
   qmatch_assum_rename_tac`MEM prompt prog` >>
   Cases_on`prompt`>>full_simp_tac(srw_ss())[tids_of_prompt_def] >>
   strip_tac >>
   qmatch_assum_abbrev_tac`MEM p prog` >>
   first_x_assum(qspec_then`p`mp_tac) >> simp[Abbr`p`] >>
   BasicProvers.CASE_TAC >> simp[] >- (
     full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> full_simp_tac(srw_ss())[prompt_mods_ok_def,EVERY_MEM] >>
     full_simp_tac(srw_ss())[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     every_case_tac >> full_simp_tac(srw_ss())[] >>
     res_tac >> full_simp_tac(srw_ss())[MEM_MAP,mk_id_def] ) >>
   strip_tac >>
   full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> full_simp_tac(srw_ss())[prompt_mods_ok_def,EVERY_MEM] >>
   full_simp_tac(srw_ss())[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >>
   res_tac >> full_simp_tac(srw_ss())[MEM_MAP,mk_id_def] >> srw_tac[][] )
 >- (
   full_simp_tac(srw_ss())[IN_DISJOINT] >>
   spose_not_then strip_assume_tac >>
   qmatch_assum_rename_tac`z ∈ FDOM exh` >>
   Cases_on`z` >- (
     rator_x_assum`no_dup_top_types_i1`mp_tac >>
     res_tac >> simp[no_dup_top_types_i1_def] >>
     simp[IN_DISJOINT,MEM_MAP,PULL_EXISTS] >>
     full_simp_tac(srw_ss())[tids_of_prog_def,prog_i1_to_top_types_def,MEM_MAP,MEM_FLAT,PULL_EXISTS] >>
     disj2_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[tids_of_prompt_def] >>
     BasicProvers.CASE_TAC >> simp[] >- (
       full_simp_tac(srw_ss())[tids_of_decs_def,decs_to_types_i1_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
       every_case_tac >> full_simp_tac(srw_ss())[] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       full_simp_tac(srw_ss())[MEM_MAP,PULL_EXISTS] >>
       first_assum(match_exists_tac o concl) >> simp[] >>
       simp[UNCURRY] >>
       qmatch_assum_rename_tac`Short a = mk_id mno _` >>
       Cases_on`mno`>>full_simp_tac(srw_ss())[mk_id_def] ) >>
     full_simp_tac(srw_ss())[EVERY_MEM] >>
     res_tac >> full_simp_tac(srw_ss())[] >>
     full_simp_tac(srw_ss())[prompt_mods_ok_def] >>
     full_simp_tac(srw_ss())[EVERY_MEM,tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     every_case_tac >> full_simp_tac(srw_ss())[] >>
     res_tac >> full_simp_tac(srw_ss())[MEM_MAP,mk_id_def]) >>
   full_simp_tac(srw_ss())[no_dup_mods_i1_def,IN_DISJOINT] >> res_tac >>
   full_simp_tac(srw_ss())[prog_i1_to_mods_def,tids_of_prog_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   qmatch_assum_rename_tac`mn ∈ mods` >>
   first_x_assum(qspec_then`mn`mp_tac) >>
   qmatch_assum_rename_tac`MEM prompt prog` >>
   Cases_on`prompt`>>full_simp_tac(srw_ss())[tids_of_prompt_def] >>
   qmatch_assum_abbrev_tac`MEM p prog` >>
   first_x_assum(qspec_then`p`mp_tac) >> simp[Abbr`p`] >>
   BasicProvers.CASE_TAC >> simp[] >- (
     full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> full_simp_tac(srw_ss())[prompt_mods_ok_def,EVERY_MEM] >>
     full_simp_tac(srw_ss())[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
     every_case_tac >> full_simp_tac(srw_ss())[] >>
     res_tac >> full_simp_tac(srw_ss())[MEM_MAP,mk_id_def] ) >>
   strip_tac >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   full_simp_tac(srw_ss())[EVERY_MEM] >> res_tac >> full_simp_tac(srw_ss())[prompt_mods_ok_def,EVERY_MEM] >>
   full_simp_tac(srw_ss())[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
   every_case_tac >> full_simp_tac(srw_ss())[] >>
   res_tac >> full_simp_tac(srw_ss())[MEM_MAP,mk_id_def] >> srw_tac[][] ));

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
 srw_tac[][]
 >- (PairCases_on `envC` >>
     full_simp_tac(srw_ss())[merge_alist_mod_env_def, prog_to_i2_def] >>
     srw_tac[][Once evaluate_prog_i2_cases, FUNION_FEMPTY_1] >>
     full_simp_tac(srw_ss())[to_i2_invariant_def] >>
     metis_tac [gtagenv_weak_refl, cenv_inv_def])
 >- (full_simp_tac(srw_ss())[prog_to_i2_def, LET_THM] >>
     `?st2 exh2 p2. prompt_to_i2 (next,tagenv,inv') prompt = (st2,exh2,p2)`
             by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     `?st1 exh1 ps1. prog_to_i2 st2 prog = (st1,exh1,ps1)`
             by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][] >>
     `?s1 tids1 mods1. s_tmp' = (s1,tids1,mods1)` by metis_tac [pair_CASES] >>
     srw_tac[][Once evaluate_prog_i2_cases] >>
     `?next2 tagenv2 inv2. st2 = (next2, tagenv2, inv2)` by metis_tac [pair_CASES] >>
     srw_tac[][] >>
    (prompt_to_i2_correct |> REWRITE_RULE[GSYM AND_IMP_INTRO]
      |> (fn th => first_assum (mp_tac o MATCH_MP th))) >>
     simp[] >>
     disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
     simp[] >>
     disch_then(qx_choosel_then[`genv'_i2`,`s'_i2`,`gtagenv'`]strip_assume_tac) >>
     rev_full_simp_tac(srw_ss())[] >>
     first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
     simp[] >>
     `DISJOINT (FDOM exh2) (FDOM exh1)` by (
       MATCH_MP_TAC exh_disjoint1 >> simp[] ) >>
     `DISJOINT (FDOM exh) (FDOM exh1)`
              by (full_simp_tac(srw_ss())[to_i2_invariant_def] >>
                  match_mp_tac exh_disjoint2 >>
                  simp[] >> metis_tac[]) >>
     full_simp_tac(srw_ss())[no_dup_mods_i1_eqn, no_dup_top_types_i1_eqn] >>
      discharge_hyps >- (
       imp_res_tac evaluate_prompt_i1_mods_disjoint >>
       Cases_on`prompt`>>full_simp_tac(srw_ss())[Once evaluate_prompt_i1_cases,update_mod_state_def] >>
       full_simp_tac(srw_ss())[no_dup_mods_i1_def] >>
       BasicProvers.CASE_TAC>>full_simp_tac(srw_ss())[DISJOINT_SYM] ) >>
     discharge_hyps >- (
       imp_res_tac evaluate_prompt_i1_tids >> full_simp_tac(srw_ss())[] >>
       rator_x_assum`no_dup_top_types_i1`mp_tac >>
       simp[no_dup_top_types_i1_def,GSYM AND_IMP_INTRO] >>
       strip_tac >>
       simp[IN_DISJOINT,MEM_MAP,PULL_EXISTS] >> strip_tac >>
       spose_not_then strip_assume_tac >>
       first_x_assum(qspec_then`TypeId(Short tn)`mp_tac) >>
       simp[] >>
       qpat_assum`A = y ∪ z`mp_tac >>
       simp[EXTENSION] >> srw_tac[][] >>
       first_x_assum(qspec_then`(Short tn)`mp_tac) >>
       srw_tac[][] >>
       Cases_on`prompt`>>full_simp_tac(srw_ss())[tids_of_prompt_def] >>
       rator_x_assum`prompt_mods_ok`mp_tac >>
       simp[prompt_mods_ok_def] >>
       BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >- (
         full_simp_tac(srw_ss())[IN_DISJOINT] >> srw_tac[][] >>
         first_x_assum(qspec_then`tn`mp_tac) >>
         simp[decs_to_types_i1_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
         qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
         simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,PULL_FORALL] >>
         gen_tac >> strip_tac >>
         every_case_tac >> full_simp_tac(srw_ss())[] >> full_simp_tac(srw_ss())[MEM_MAP] >> srw_tac[][] >>
         qmatch_assum_abbrev_tac`MEM d l` >>
         first_x_assum(qspec_then`d`mp_tac) >>
         simp[Abbr`d`,MEM_MAP,FORALL_PROD] >>
         qmatch_assum_rename_tac`MEM (Dtype_i1 mno tds) decs` >>
         Cases_on`mno`>>full_simp_tac(srw_ss())[mk_id_def]>>
         qmatch_assum_rename_tac`MEM p tds` >>
         PairCases_on`p`>>full_simp_tac(srw_ss())[] >> metis_tac[] ) >>
       simp[EVERY_MEM] >>
       qpat_assum`X ∈ tids_of_decs Y`mp_tac >>
       simp[tids_of_decs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >> srw_tac[][] >>
       every_case_tac >> full_simp_tac(srw_ss())[] >>
       res_tac >> full_simp_tac(srw_ss())[mk_id_def,MEM_MAP] ) >>
     srw_tac[][]
       >- (MAP_EVERY qexists_tac [`genv'_i2 ++ genv'_i2'`, `s'_i2'`, `gtagenv''`] >>
           srw_tac[][] >>
           full_simp_tac(srw_ss())[merge_alist_mod_env_assoc, FUNION_ASSOC]
           >- metis_tac[DISJOINT_SYM]
           >- metis_tac [gtagenv_weak_trans]
           >- (`DISJOINT (FDOM exh1) (FDOM (FUNION exh2 exh))` 
                  by srw_tac[][FDOM_FUNION, DISJOINT_UNION_BOTH] >>
               metis_tac [evaluate_prompt_i2_exh_weak, FUNION_ASSOC, NOT_SOME_NONE]))
       >- (MAP_EVERY qexists_tac [`genv'_i2 ++ genv'_i2'`, `s'_i2'`, `SOME err_i2`, `gtagenv''`] >>
           srw_tac[][] >>
           full_simp_tac(srw_ss())[merge_alist_mod_env_assoc, FUNION_ASSOC]
           >- metis_tac[DISJOINT_SYM]
           >- metis_tac [gtagenv_weak_trans]
           >- (`DISJOINT (FDOM exh1) (FDOM (FUNION exh2 exh))` 
                  by srw_tac[][FDOM_FUNION, DISJOINT_UNION_BOTH] >>
               metis_tac [evaluate_prompt_i2_exh_weak, FUNION_ASSOC, NOT_SOME_NONE])))
 >- (full_simp_tac(srw_ss())[prog_to_i2_def, LET_THM] >>
     `?st2 exh2 p2. prompt_to_i2 (next,tagenv,inv') prompt = (st2,exh2,p2)`
             by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     `?st1 exh1 ps1. prog_to_i2 st2 prompts = (st1,exh1,ps1)`
             by metis_tac [pair_CASES] >>
     full_simp_tac(srw_ss())[] >>
     srw_tac[][Once evaluate_prog_i2_cases] >>
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
              by (full_simp_tac(srw_ss())[to_i2_invariant_def] >>
                  match_mp_tac (GEN_ALL exh_disjoint2) >>
                  PairCases_on`st2` >>
                  first_assum(match_exists_tac o concl) >> simp[] >>
                  metis_tac[]) >>
     `DISJOINT (FDOM exh1) (FDOM (FUNION exh2 exh))`
                  by srw_tac[][FDOM_FUNION, DISJOINT_UNION_BOTH] >>
     srw_tac[][] >- metis_tac[DISJOINT_SYM] >>
     disj2_tac >>
     ONCE_REWRITE_TAC[GSYM(FUNION_ASSOC)] >>
     match_mp_tac evaluate_prompt_i2_exh_weak >>
     full_simp_tac(srw_ss())[result_to_i2_cases] >> full_simp_tac(srw_ss())[]));

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
 srw_tac[][evaluate_whole_prog_i1_def] >>
 match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL] prog_to_i2_correct) >>
 metis_tac []);

val _ = export_theory ();

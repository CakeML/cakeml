(*
  Relating inference and type system environments.
*)
open preamble;
open libTheory namespacePropsTheory typeSystemTheory astTheory
semanticPrimitivesTheory terminationTheory inferTheory unifyTheory inferPropsTheory;
open astPropsTheory typeSysPropsTheory;

val _ = new_theory "envRel";

(* ---------- Converting infer types and envs to type system ones ---------- *)

val convert_t_def = tDefine "convert_t" `
(convert_t (Infer_Tvar_db n) = Tvar_db n) ∧
(convert_t (Infer_Tapp ts tc) = Tapp (MAP convert_t ts) tc)`
(WF_REL_TAC `measure infer_t_size` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_tTheory.infer_t_size_def] >>
 res_tac >>
 decide_tac);

val convert_env_def = Define `
convert_env s env = MAP (\(x,t). (x, convert_t (t_walkstar s t))) env`;

(* val convert_decls_def = Define `
convert_decls idecls =
  <| defined_mods := set idecls.inf_defined_mods;
     defined_types :=  set idecls.inf_defined_types;
     defined_exns := set idecls.inf_defined_exns|>`;

Theorem convert_append_decls:
 !decls1 decls2. convert_decls (append_decls decls1 decls2) = union_decls (convert_decls decls1) (convert_decls decls2)
Proof
 rw [convert_decls_def, append_decls_def, union_decls_def]
QED
*)

Theorem check_convert_freevars:
 (!tvs uvs t. check_t tvs uvs t ⇒ (uvs = {}) ⇒ check_freevars tvs [] (convert_t t))
Proof
ho_match_mp_tac check_t_ind >>
rw [check_freevars_def, check_t_def, convert_t_def] >>
fs [EVERY_MEM, MEM_MAP] >>
metis_tac []
QED

Theorem check_t_to_check_freevars:
 !tvs (n:num set) t. check_t tvs {} t ⇒ check_freevars tvs [] (convert_t t)
Proof
ho_match_mp_tac check_t_ind >>
rw [check_t_def, check_freevars_def, convert_t_def, EVERY_MAP] >>
fs [EVERY_MEM]
QED

Theorem convert_inc:
 !t tvs tvs'.
  check_t tvs' {} t
  ⇒
  (convert_t (infer_deBruijn_inc tvs t) = deBruijn_inc 0 tvs (convert_t t))
Proof
ho_match_mp_tac (fetch "-" "convert_t_ind") >>
rw [check_t_def, convert_t_def, infer_deBruijn_inc_def, deBruijn_inc_def] >>
induct_on `ts` >>
fs [] >>
metis_tac []
QED

val infer_t_induction = infer_tTheory.infer_t_induction;

Theorem db_subst_infer_subst_swap:
 (!t s tvs uvar n.
  t_wfs s ∧
  count (uvar + tvs) ⊆ FDOM s ∧
  (!uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  check_t tvs (FDOM s) t
  ⇒
  (convert_t
    (t_walkstar s
       (infer_deBruijn_subst
          (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))
          t)) =
   deBruijn_subst 0
    (MAP (convert_t o t_walkstar s)
       (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
    (convert_t (t_walkstar (infer_deBruijn_inc tvs o_f s) t)))) ∧
 (!ts s tvs uvar n.
  t_wfs s ∧
  count (uvar + tvs) ⊆ FDOM s ∧
  (!uv. uv ∈ FDOM s ⇒ check_t n {} (t_walkstar s (Infer_Tuvar uv))) ∧
  EVERY (\t. check_t tvs (FDOM s) t) ts ⇒
  (MAP (convert_t o
       t_walkstar s o
       infer_deBruijn_subst (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs)))
      ts =
   MAP (deBruijn_subst 0 (MAP (convert_t o t_walkstar s) (MAP (λn. Infer_Tuvar (uvar + n)) (COUNT_LIST tvs))) o
       convert_t o
       t_walkstar (infer_deBruijn_inc tvs o_f s))
      ts))
Proof
ho_match_mp_tac infer_t_induction >>
rw [convert_t_def, deBruijn_subst_def, EL_MAP, t_walkstar_eqn1,
    infer_deBruijn_subst_def, MAP_MAP_o, combinTheory.o_DEF, check_t_def,
    LENGTH_COUNT_LIST] >|
[`t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     fs [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def,
         LENGTH_COUNT_LIST] >>
     fs [LENGTH_MAP, el_map_count, EL_COUNT_LIST],
 `t_wfs (infer_deBruijn_inc tvs o_f s)` by metis_tac [inc_wfs] >>
     fs [t_walkstar_eqn1, convert_t_def, deBruijn_subst_def, MAP_MAP_o,
         combinTheory.o_DEF] >>
     metis_tac [],
 res_tac >>
     imp_res_tac convert_inc >>
     rw [walkstar_inc2] >>
     metis_tac [subst_inc_cancel, arithmeticTheory.ADD,
                deBruijn_inc0,
                LENGTH_COUNT_LIST, LENGTH_MAP],
 metis_tac [],
 metis_tac []]
QED

Theorem inc_convert_t:
 (!t tvs' tvs. check_t tvs' {} t ⇒ (deBruijn_inc tvs' tvs (convert_t t) = convert_t t)) ∧
 (!ts tvs' tvs. EVERY (check_t tvs' {}) ts ⇒ (MAP (deBruijn_inc tvs' tvs o convert_t) ts = MAP convert_t ts))
Proof
ho_match_mp_tac infer_t_induction >>
rw [check_t_def, convert_t_def, deBruijn_inc_def] >>
metis_tac [MAP_MAP_o]
QED

Theorem convert_t_subst:
 (!t tvs ts'.
    (LENGTH tvs = LENGTH ts') ∧
    check_freevars 0 tvs t ⇒
    convert_t (infer_type_subst (ZIP (tvs,ts')) t) =
    type_subst (alist_to_fmap (ZIP (tvs, MAP convert_t ts'))) t) ∧
 (!ts tvs ts'.
    (LENGTH tvs = LENGTH ts') ∧
    EVERY (check_freevars 0 tvs) ts ⇒
    MAP convert_t (MAP (infer_type_subst (ZIP (tvs,ts'))) ts) =
    MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP convert_t ts')))) ts)
Proof
ho_match_mp_tac t_induction >>
rw [check_freevars_def, convert_t_def, type_subst_def, infer_type_subst_def] >|
[full_case_tac >>
     full_case_tac >>
     fs [ALOOKUP_FAILS] >>
     imp_res_tac ALOOKUP_MEM >>
     REPEAT (pop_assum mp_tac) >>
     rw [MAP_ZIP] >>
     REPEAT (pop_assum mp_tac) >>
     Q.SPEC_TAC (`tvs`,`tvs`) >>
     induct_on `ts'` >>
     rw [] >>
     cases_on `tvs` >>
     fs [] >>
     metis_tac [optionTheory.SOME_11],
 metis_tac []]
QED

Theorem deBruijn_subst_convert:
    (∀t.
  check_t n {} t ⇒
  deBruijn_subst 0 (MAP convert_t subst) (convert_t t) =
  convert_t (infer_deBruijn_subst subst t) ) ∧
  (∀ts.
  EVERY (check_t n {}) ts ⇒
  MAP ((deBruijn_subst 0 (MAP convert_t subst)) o convert_t) ts
  =
  MAP (convert_t o (infer_deBruijn_subst subst)) ts)
Proof
  ho_match_mp_tac infer_tTheory.infer_t_induction>>
  rw[check_t_def]>>
  fs[convert_t_def,deBruijn_subst_def,infer_deBruijn_subst_def]
  >-
    (IF_CASES_TAC>>fs[EL_MAP,convert_t_def])
  >>
    fs[MAP_MAP_o,EVERY_MEM,MAP_EQ_f]
QED

Theorem check_freevars_empty_convert_unconvert_id:
 !t. check_freevars n [] t ⇒ convert_t (unconvert_t t) = t
Proof
  ho_match_mp_tac unconvert_t_ind>>
  rw[]>>fs[unconvert_t_def,convert_t_def,check_freevars_def]>>
  fs[MAP_MAP_o,MAP_EQ_ID,EVERY_MEM]
QED

Theorem check_t_empty_unconvert_convert_id:
 !t n. check_t n {} t ⇒
  unconvert_t (convert_t t) = t
Proof
  ho_match_mp_tac (fetch "-" "convert_t_ind") >>
  rw[]>>
  fs[unconvert_t_def,convert_t_def,check_t_def]>>
  fs[MAP_MAP_o,MAP_EQ_ID,EVERY_MEM] >>
  metis_tac []
QED

Theorem check_freevars_to_check_t:
 !t z. check_freevars n [] t ⇒ check_t n {} (unconvert_t t)
Proof
  ho_match_mp_tac unconvert_t_ind>>rw[]>>
  fs[unconvert_t_def,check_freevars_def,check_t_def]>>
  fs[EVERY_MAP,EVERY_MEM]
QED

Theorem infer_type_subst_nil:
   (∀t. check_freevars n [] t ⇒ infer_type_subst [] t = unconvert_t t) ∧
    (∀ts. EVERY (check_freevars n []) ts ⇒ MAP (infer_type_subst []) ts = MAP unconvert_t ts)
Proof
  ho_match_mp_tac(TypeBase.induction_of(``:t``)) >>
  rw[infer_type_subst_def,convert_t_def,unconvert_t_def,check_freevars_def] >>
  fsrw_tac[boolSimps.ETA_ss][]
QED

(* ---------- relating inference and type system environments ---------- *)


(* We want tscheme_approx max_tvs s (tvs, t) (tvs', t') to hold iff (tvs', t') is
 * more general than (tvs, t) under substitution s constraining unification
 * variables.
 *
 * In general, there are 4 classes of variables that can appear in ts and ts':
 * - de Bruijn variables less than tvs, and hence bound by the type scheme,
 * - de Bruijn variables ≥ tvs that are bound in the enclosing context which
 *     binds max_tvs variables, appearing in t as tvs to tvs + max_tvs,
 * - unification variables constrained by s, and
 * - other unification variables.
 *
 * We assume that s only mentions de Bruijn variables bound in the context, but
 * unlike in t, they appear as 0 to max_tvs (since the substitution is not under
 * the typescheme binder).
 *
 * We'd like to instantiate the bound de Bruijn variables in t' so that it
 * matches t. To do so, we must apply s to both t and t', since they may contain
 * different bound unification variables that are constrained to be the same by
 * s. However, since s may contain de Bruijn type variables, we have to either
 * shift it by tvs/tvs' to avoid capture, or first instantiate both type schemes.
 * Since we have to instantiate one anyway, we choose the latter option.
 *
 * The main question is how to instantiate t. Crucially, we don't want to
 * over-specialise t, so that a less general t' can be matched to t. One
 * approach would be to instantiate t with fresh variables of some sort;
 * however, that does not work well with our general setup which requires all
 * type variables to be explicitly bound somewhere. Instead, we require that t'
 * be able to match the result of any instantiation of t. In fact, we slightly
 * restrict the form of instantiation to be on in which the instantiation has
 * only good de Bruijn and unification variables, and the substitution for t is
 * also applied to the substitution for t'. So t''s substitution is just
 * matching t, and then instantiation of t is making things good for the
 * walkstar
 *
 * *)

val tscheme_approx_def = Define `
  tscheme_approx max_tvs s (tvs,t) (tvs',t') ⇔
    ?subst'.
      LENGTH subst' = tvs' ∧
      EVERY (check_t (max_tvs + tvs) (FDOM s)) subst' ∧
      !subst.
       LENGTH subst = tvs
       ⇒
       t_walkstar s (infer_deBruijn_subst subst t) =
       t_walkstar s (infer_deBruijn_subst (MAP (infer_deBruijn_subst subst) subst') t')`;

Theorem tscheme_approx_thm:
   ∀t' max_tvs s tvs tvs' t.
    t_wfs s ⇒
    (tscheme_approx max_tvs s (tvs,t) (tvs',t') ⇒
     ∀subst.
      LENGTH subst = tvs ∧
      EVERY (check_t max_tvs ∅) subst
      ⇒
      ∃subst'.
        LENGTH subst' = tvs' ∧
        EVERY (check_t max_tvs (FDOM s)) subst' ∧
        t_walkstar s (infer_deBruijn_subst subst t) = t_walkstar s (infer_deBruijn_subst subst' t'))
Proof
 rw [tscheme_approx_def]
 >> qexists_tac `MAP (infer_deBruijn_subst subst) subst'`
 >> fs [EVERY_MAP, EVERY_MEM]
 >> rw []
 >> first_x_assum drule
 >> rw []
 >> irule check_t_infer_deBruijn_subst
 >> metis_tac [EVERY_MEM, check_t_more5, SUBSET_DEF, NOT_IN_EMPTY]
QED

Theorem tscheme_approx_refl:
   !max_tvs s tvs t. tscheme_approx max_tvs s (tvs,t) (tvs,t)
Proof
  rw [tscheme_approx_def] >>
  qexists_tac `MAP Infer_Tvar_db (COUNT_LIST tvs)` >>
  rw [LENGTH_COUNT_LIST, EVERY_MAP, every_count_list, check_t_def,
      MAP_MAP_o, combinTheory.o_DEF, infer_deBruijn_subst_def] >>
  irule (METIS_PROVE [] ``y = y' ⇒ f x y = f x y'``) >>
  irule (METIS_PROVE [] ``y = y' ⇒ f y x = f y' x``) >>
  irule LIST_EQ >>
  rw [LENGTH_COUNT_LIST, EL_MAP, EL_COUNT_LIST]
QED

(* TODO: should be able to use max_tvs in place of 0 *)
Theorem tscheme_approx_trans:
   tscheme_approx max_tvs s (tvs1,t1) (tvs2,t2) ∧
   tscheme_approx 0 s (tvs2,t2) (tvs3,t3)
   ⇒
   tscheme_approx max_tvs s (tvs1,t1) (tvs3,t3)
Proof
  rw [tscheme_approx_def] >>
  qexists_tac `MAP (infer_deBruijn_subst subst') subst''` >>
  simp [] >>
  conj_asm1_tac
  >- (
    fs [EVERY_MAP, EVERY_MEM] >>
    rw [] >>
    irule check_t_infer_deBruijn_subst >>
    rw [EVERY_MEM] >>
    first_x_assum drule >>
    metis_tac [check_t_more2, ADD_ASSOC, ADD_COMM]) >>
  rw [MAP_MAP_o] >>
  AP_TERM_TAC >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  irule (GSYM (CONJUNCT2 infer_deBruijn_subst_twice)) >>
  qexists_tac `FDOM s` >>
  metis_tac [check_t_more2, ADD_COMM, ADD_ASSOC]
QED

Theorem unconvert_db_subst:
   !t subst fvs l.
     check_freevars l [] t ⇒
     unconvert_t (deBruijn_subst 0 subst t) =
     infer_deBruijn_subst (MAP unconvert_t subst) (unconvert_t t)
Proof
 ho_match_mp_tac t_ind >>
 rw [deBruijn_subst_def, unconvert_t_def, infer_deBruijn_subst_def,
     check_freevars_def, EL_MAP] >>
 irule LIST_EQ >>
 rw [EL_MAP] >>
 fs [EVERY_MEM, MEM_EL] >>
 metis_tac []
QED

Theorem tscheme_inst_to_approx:
   tscheme_inst (tvs,t) (tvs',t') ⇒
   tscheme_approx 0 FEMPTY (tvs,unconvert_t t) (tvs',unconvert_t t')
Proof
  rw [tscheme_inst_def, tscheme_approx_def, t_walkstar_FEMPTY] >>
  qexists_tac `MAP unconvert_t subst` >>
  rw [EVERY_MAP]
  >- (
    fs [EVERY_MEM] >>
    metis_tac [check_freevars_to_check_t]) >>
  rw [MAP_MAP_o, combinTheory.o_DEF] >>
  drule unconvert_db_subst >>
  rw [] >>
  drule check_freevars_to_check_t >>
  rw [] >>
  `check_t (LENGTH (MAP unconvert_t subst)) {} (unconvert_t t')` by rw [] >>
  `check_t (LENGTH (MAP unconvert_t subst)) uvs (unconvert_t t')` by metis_tac [check_t_more] >>
  drule (GEN_ALL (CONJUNCT1 infer_deBruijn_subst_twice)) >>
  rw [MAP_MAP_o, combinTheory.o_DEF]
QED

val env_rel_sound_def = Define `
  env_rel_sound s ienv tenv tenvE ⇔
    ienv.inf_t = tenv.t ∧
    ienv.inf_c = tenv.c ∧
    !x ts.
      nsLookup ienv.inf_v x = SOME ts
      ⇒
      ?tvs' t'.
        check_freevars (tvs' + num_tvs tenvE) [] t' ∧
        lookup_var x tenvE tenv = SOME (tvs', t') ∧
        tscheme_approx (num_tvs tenvE) s ts (tvs', unconvert_t t')`;

Theorem env_rel_sound_lookup_none:
   !ienv tenv s tenvE id.
    env_rel_sound s ienv tenv tenvE ∧
    lookup_var id tenvE tenv = NONE
    ⇒
    nsLookup ienv.inf_v id = NONE
Proof
  rw [env_rel_sound_def, lookup_var_def] >>
  every_case_tac >>
  fs [] >>
  CCONTR_TAC >>
  `?v. nsLookup ienv.inf_v id = SOME v` by metis_tac [option_nchotomy] >>
  fs [] >>
  first_x_assum drule >>
  strip_tac >>
  every_case_tac >>
  fs []
QED

Theorem env_rel_sound_lookup_some:
   !id ts s ienv tenv tenvE.
    nsLookup ienv.inf_v id = SOME ts ∧ env_rel_sound s ienv tenv tenvE
    ⇒
    ?tvs' t'.
      check_freevars (tvs' + num_tvs tenvE) [] t' ∧
      lookup_var id tenvE tenv = SOME (tvs',t') ∧
      tscheme_approx (num_tvs tenvE) s ts (tvs', unconvert_t t')
Proof
 rw [env_rel_sound_def]
QED

Theorem db_subst_infer_subst_swap3:
   !t tvs s subst.
    t_wfs s ∧
    check_freevars tvs [] t
    ⇒
    convert_t (t_walkstar s (infer_deBruijn_subst subst (unconvert_t t)))
    =
    deBruijn_subst 0 (MAP (convert_t o t_walkstar s) subst) t
Proof
 ho_match_mp_tac unconvert_t_ind
 >> rw [unconvert_t_def, infer_deBruijn_subst_def, deBruijn_subst_def,
        check_freevars_def, convert_t_def, t_walkstar_eqn1]
 >- rw [EL_MAP]
 >> rw [MAP_MAP_o, combinTheory.o_DEF]
 >> rw [MAP_EQ_f]
 >> first_x_assum drule
 >> fs [EVERY_MEM]
 >> metis_tac []
QED

Theorem tscheme_approx_weakening:
   !tvs tvs' s1 s2 ts1 ts2.
    tscheme_approx tvs s1 ts1 ts2 ∧
    t_wfs s2 ∧
    s1 SUBMAP s2 ∧
    tvs ≤ tvs'
    ⇒
    tscheme_approx tvs' s2 ts1 ts2
Proof
 rw []
 >> Cases_on `ts1`
 >> Cases_on `ts2`
 >> fs [tscheme_approx_def]
 >> rw []
 >> qexists_tac `subst'`
 >> rw []
 >> `tvs + (tvs' - tvs) = tvs'` by decide_tac
 >- prove_tac [SUBMAP_DEF, check_t_more5, SUBSET_DEF, check_t_more2, ADD_COMM, ADD_ASSOC]
 >> first_x_assum (qspec_then `subst` mp_tac)
 >> rw []
 >> metis_tac [t_walkstar_idempotent, t_walkstar_SUBMAP]
QED

Theorem env_rel_sound_extend_tvs:
   !s ienv tenv bindings tvs.
    t_wfs s ∧
    env_rel_sound s ienv tenv Empty
    ⇒
    env_rel_sound s ienv tenv (bind_tvar tvs Empty)
Proof
 rw [env_rel_sound_def]
 >> first_x_assum drule
 >> simp [bind_tvar_def, lookup_var_def, lookup_varE_def, tveLookup_def]
 >> rw []
 >> every_case_tac
 >> fs []
 >> rw []
 >- metis_tac [check_freevars_add,DECIDE ``x+y>=x:num``, ADD_COMM, ADD_ASSOC]
 >- metis_tac [SUBMAP_REFL, tscheme_approx_weakening, DECIDE ``0n ≤ x``]
 >- metis_tac [check_freevars_add,DECIDE ``x+y>=x:num``, ADD_COMM, ADD_ASSOC]
 >- metis_tac [SUBMAP_REFL, tscheme_approx_weakening, DECIDE ``0n ≤ x``]
QED

Theorem tscheme_approx0:
   !tvs s t. t_wfs s ⇒ tscheme_approx tvs s (0, t) (0, t_walkstar s t)
Proof
 rw [tscheme_approx_def, LENGTH_NIL, infer_deBruijn_subst_id, t_walkstar_idempotent]
QED

Theorem env_rel_sound_extend0:
   !s x t ienv tenv tenvE.
    env_rel_sound s ienv tenv tenvE ∧
    t_wfs s ∧
    check_t (num_tvs tenvE) (FDOM s) t ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t (num_tvs tenvE) ∅ (t_walkstar s (Infer_Tuvar uv)))
    ⇒
    env_rel_sound s (ienv with inf_v := nsBind x (0,t) ienv.inf_v)
      tenv (Bind_name x 0 (convert_t (t_walkstar s t)) tenvE)
Proof
 rw [env_rel_sound_def]
 >> Cases_on `Short x = x'`
 >> rw []
 >> simp [lookup_var_def, lookup_varE_def, tveLookup_def, deBruijn_inc0]
 >- (
   `check_t (num_tvs tenvE) {} (t_walkstar s t)`
     by (
       irule (CONJUNCT1 check_t_walkstar)
       >> simp [])
   >> drule check_t_empty_unconvert_convert_id
   >> rw [check_t_to_check_freevars]
   >> fs []
   >> rw []
   >> metis_tac [tscheme_approx0])
 >- (
   fs []
   >> first_x_assum drule
   >> rw []
   >> every_case_tac
   >> fs [lookup_var_def, lookup_varE_def])
QED

Theorem env_rel_sound_merge0:
   !s ienv bindings tenv tenvE.
    t_wfs s ∧
    (∀uv. uv ∈ FDOM s ⇒ check_t (num_tvs tenvE) ∅ (t_walkstar s (Infer_Tuvar uv))) ∧
    EVERY (λ(x,t). check_t 0 (FDOM s) t) bindings ∧
    env_rel_sound s ienv tenv tenvE
    ⇒
    env_rel_sound s
       (ienv with inf_v := nsAppend (alist_to_ns (MAP (λ(n,t). (n,0,t)) bindings)) ienv.inf_v)
       tenv
       (bind_var_list 0 (convert_env s bindings) tenvE)
Proof
 rw [env_rel_sound_def]
 >> fs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_some, nsLookup_alist_to_ns_none]
 >- (
   rw [lookup_var_def, lookup_varE_def, tveLookup_bvl, convert_env_def, deBruijn_inc0]
   >> fs [ALOOKUP_MAP]
   >> rw []
   >- (
     irule check_t_to_check_freevars
     >> irule (CONJUNCT1 check_t_walkstar)
     >> rw []
     >> fs [EVERY_MEM]
     >> imp_res_tac ALOOKUP_MEM
     >> first_x_assum drule
     >> fs []
     >> metis_tac [check_t_more2, DECIDE ``x + 0n = x``])
   >- (
     `check_t (num_tvs tenvE) {} (t_walkstar s t)`
       by (
         irule (CONJUNCT1 check_t_walkstar)
         >> simp []
         >> imp_res_tac ALOOKUP_MEM
         >> fs [EVERY_MEM]
         >> first_x_assum drule
         >> rw []
         >> metis_tac [check_t_more2, DECIDE ``z + 0n = z``])
     >> drule check_t_empty_unconvert_convert_id
     >> simp []
     >> disch_then kall_tac
     >> irule tscheme_approx0
     >> rw []))
 >- (
   first_x_assum drule
   >> rw [lookup_var_def, lookup_varE_def]
   >> CASE_TAC
   >> fs [tveLookup_bvl]
   >> every_case_tac
   >> fs [deBruijn_inc0, ALOOKUP_MAP, convert_env_def]
   >> fs [])
QED

Theorem env_rel_e_sound_letrec_merge0:
 !funs ienv tenv tenvE s uvs.
  t_wfs s ∧
  (∀uv. uv ∈ FDOM s ⇒ check_t (num_tvs tenvE) ∅ (t_walkstar s (Infer_Tuvar uv))) ∧
  count (uvs + LENGTH funs) ⊆ FDOM s ∧
  env_rel_sound s ienv tenv tenvE
  ⇒
  env_rel_sound s
    (ienv with inf_v :=
      nsAppend
        (alist_to_ns
          (MAP2 (λ(f,x,e) uvar. (f,0,uvar))
            funs
            (MAP (λn. Infer_Tuvar (uvs + n)) (COUNT_LIST (LENGTH funs)))))
        ienv.inf_v)
    tenv
    (bind_var_list 0 (MAP2 (λ(f,x,e) t. (f,t))
                       funs
                       (MAP (λn. convert_t (t_walkstar s (Infer_Tuvar (uvs + n))))
                         (COUNT_LIST (LENGTH funs)))) tenvE)
Proof
  induct_on `funs` >>
  srw_tac[] [COUNT_LIST_def, bind_var_list_def] >>
  PairCases_on `h` >>
  srw_tac[] [bind_var_list_def] >>
  last_x_assum drule >>
  disch_then drule >>
  full_simp_tac (bool_ss) [DECIDE ``x+SUC y=SUC x + y``] >>
  disch_then drule >>
  disch_then drule >>
  rw [] >>
  drule env_rel_sound_extend0 >>
  simp [MAP_MAP_o, combinTheory.o_DEF] >>
  disch_then (qspecl_then [`h0`, `Infer_Tuvar uvs`] mp_tac) >>
  simp [check_t_def] >>
  fs [SUBSET_DEF] >>
  simp_tac (srw_ss()++ARITH_ss) [ADD1]
  >> rw []
  >> ONCE_REWRITE_TAC [DECIDE ``n + (x + 1) = x + (n + 1n)``]
  >> metis_tac []
QED

val env_rel_complete_def = Define `
  env_rel_complete s ienv tenv tenvE ⇔
    ienv.inf_t = tenv.t ∧
    ienv.inf_c = tenv.c ∧
    !x tvs t.
      lookup_var x tenvE tenv = SOME (tvs, t)
      ⇒
      (* t cannot have tyvars inside *)
      (∃n. check_freevars n [] t) ∧
      ?tvs' t'.
        nsLookup ienv.inf_v x = SOME (tvs', t') ∧
        (* A stronger version is guaranteed by ienv_ok
        check_t (tvs' + num_tvs tenvE) {} t' ∧*)
        tscheme_approx (num_tvs tenvE) s (tvs, unconvert_t t) (tvs', t')`;

Theorem env_rel_complete_lookup_none:
   !ienv tenv s tenvE x.
    env_rel_complete s ienv tenv tenvE ∧
    nsLookup ienv.inf_v x = NONE
    ⇒
    nsLookup tenv.v x = NONE
Proof
  rw [env_rel_complete_def, lookup_var_def] >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp [lookup_varE_def] >>
  every_case_tac >>
  rw [] >>
  metis_tac [option_nchotomy, pair_CASES]
QED

Theorem env_rel_e_sound_empty_to:
 !s ienv tenv tenvE.
  t_wfs s ∧ ienv_ok {} ienv ∧ env_rel_sound FEMPTY ienv tenv tenvE
  ⇒
  env_rel_sound s ienv tenv tenvE
Proof
 rw [env_rel_sound_def]
 >> first_x_assum drule
 >> rw []
 >> rename1 `lookup_var _ _ _ = SOME (tvs', t')`
 >> qexists_tac `tvs'`
 >> qexists_tac `t'`
 >> simp []
 >> irule tscheme_approx_weakening
 >> simp []
 >> qexists_tac `FEMPTY`
 >> simp [SUBMAP_FEMPTY]
 >> HINT_EXISTS_TAC>>fs[]
QED

(* Environment relation at infer_d and above *)
val env_rel_def = Define`
 env_rel tenv ienv ⇔
  ienv_ok {} ienv ∧
  tenv_ok tenv ∧
  (* To rule out 1 env with an empty module and the other without that module at all *)
  (!x. nsLookupMod ienv.inf_v x = NONE ⇔ nsLookupMod tenv.v x = NONE) ∧
  env_rel_sound FEMPTY ienv tenv Empty ∧
  env_rel_complete FEMPTY ienv tenv Empty`;

Theorem lookup_varE_empty[simp]:
   !x. lookup_varE x Empty = NONE
Proof
    rw [lookup_varE_def, tveLookup_def] >>
    every_case_tac
QED

Theorem env_rel_extend:
   !tenv1 ienv1 tenv2 ienv2.
    env_rel tenv1 ienv1 ∧
    env_rel tenv2 ienv2
    ⇒
    env_rel (extend_dec_tenv tenv1 tenv2) (extend_dec_ienv ienv1 ienv2)
Proof
  rpt gen_tac >>
  simp [env_rel_def] >>
  strip_tac >>
  conj_tac
  >- metis_tac [ienv_ok_extend_dec_ienv] >>
  conj_tac
  >- metis_tac [extend_dec_tenv_ok] >>
  simp [env_rel_sound_def, env_rel_complete_def, extend_dec_tenv_def,
        extend_dec_ienv_def, lookup_var_def, nsLookup_nsAppend_some,
        nsLookupMod_nsAppend_none] >>
  conj_tac
  >- metis_tac [NOT_SOME_NONE, option_nchotomy] >>
  conj_tac
  >- (
    conj_tac
    >- fs [env_rel_sound_def] >>
    conj_tac
    >- fs [env_rel_sound_def] >>
    rw []
    >- (
      fs [env_rel_sound_def] >>
      first_x_assum drule >>
      rw [] >>
      qexists_tac `tvs'` >>
      qexists_tac `t'` >>
      simp [] >>
      fs [lookup_var_def])
    >- (
      `nsLookup tenv1.v x = NONE` by metis_tac [env_rel_complete_lookup_none] >>
      rw [] >>
      fs [env_rel_sound_def] >>
      first_x_assum drule >>
      rw [] >>
      qexists_tac `tvs'` >>
      qexists_tac `t'` >>
      simp [] >>
      fs [lookup_var_def]))
  >- (
    conj_tac
    >- fs [env_rel_complete_def] >>
    conj_tac
    >- fs [env_rel_complete_def] >>
    rpt gen_tac >>
    strip_tac
    >- (
      fs [env_rel_complete_def, lookup_var_def] >>
      first_x_assum drule >>
      rw [] >>
      qexists_tac `tvs''` >>
      qexists_tac `t''` >>
      simp [])
    >- (
      `nsLookup ienv1.inf_v x = NONE`
        by (
          irule env_rel_sound_lookup_none >>
          rw [lookup_var_def, lookup_varE_def] >>
          qexists_tac `FEMPTY` >>
          qexists_tac `tenv1` >>
          qexists_tac `Empty` >>
          simp [] >>
          every_case_tac >>
          rw [] >>
          fs [tveLookup_def]) >>
      fs [env_rel_complete_def, lookup_var_def] >>
      first_x_assum drule >>
      rw [] >>
      qexists_tac `tvs''` >>
      qexists_tac `t''` >>
      simp []))
QED

Theorem env_rel_empty[simp]:
   env_rel <| v := nsEmpty; c := nsEmpty; t := nsEmpty |>
           <| inf_v := nsEmpty; inf_c := nsEmpty; inf_t := nsEmpty |>
Proof
  rw [env_rel_def, ienv_ok_def, ienv_val_ok_def, env_rel_sound_def,
      lookup_var_def, env_rel_complete_def] >>
  Cases_on `x` >>
  rw [namespaceTheory.nsLookupMod_def]
QED

Theorem env_rel_lift:
   !tenv ienv mn. env_rel tenv ienv ⇒ env_rel (tenvLift mn tenv) (lift_ienv mn ienv)
Proof
  rw [env_rel_def]
  >- metis_tac [ienv_ok_lift]
  >- fs [typeSoundInvariantsTheory.tenv_ok_def, tenvLift_def,
         typeSoundInvariantsTheory.tenv_abbrev_ok_def,
         typeSoundInvariantsTheory.tenv_ctor_ok_def,
         typeSoundInvariantsTheory.tenv_val_ok_def]
  >- (
    simp [lift_ienv_def, tenvLift_def, nsLookupMod_nsLift] >>
    every_case_tac)
  >- (
    fs [env_rel_sound_def, lift_ienv_def, tenvLift_def, nsLookup_nsLift] >>
    rw [] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    first_x_assum drule >>
    rw [] >>
    qexists_tac `tvs'` >>
    qexists_tac `t'` >>
    fs [lookup_var_def, nsLookup_nsLift])
  >- (
    fs [env_rel_complete_def, lift_ienv_def, tenvLift_def, nsLookup_nsLift] >>
    rw [] >>
    fs [lookup_var_def, nsLookup_nsLift] >>
    every_case_tac >>
    fs [] >>
    rw [] >>
    first_x_assum drule >>
    rw [])
QED

val ienv_to_tenv_def = Define `
  ienv_to_tenv ienv =
    <| v := nsMap (\(tvs, t). (tvs, convert_t t)) ienv.inf_v;
       c := ienv.inf_c;
       t := ienv.inf_t |>`;

Theorem ienv_to_tenv_extend:
   !ienv1 ienv2.
    ienv_to_tenv (extend_dec_ienv ienv2 ienv1) =
    extend_dec_tenv (ienv_to_tenv ienv2) (ienv_to_tenv ienv1)
Proof
  rw [ienv_to_tenv_def, extend_dec_tenv_def, extend_dec_ienv_def, nsMap_nsAppend]
QED

Theorem ienv_to_tenv_lift:
   !mn ienv. ienv_to_tenv (lift_ienv mn ienv) = tenvLift mn (ienv_to_tenv ienv)
Proof
  rw [ienv_to_tenv_def, lift_ienv_def, tenvLift_def, nsLift_nsMap]
QED

Theorem env_rel_ienv_to_tenv:
   !ienv. ienv_ok {} ienv ⇒ env_rel (ienv_to_tenv ienv) ienv
Proof
  rw [env_rel_def, ienv_to_tenv_def]
  >- (
    fs [ienv_ok_def, typeSoundInvariantsTheory.tenv_ok_def,
        typeSoundInvariantsTheory.tenv_val_ok_def] >>
    simp [nsAll_nsMap] >>
    fs [ienv_val_ok_def] >>
    irule nsAll_mono >>
    HINT_EXISTS_TAC >>
    rw [] >>
    pairarg_tac >>
    simp [] >>
    pairarg_tac >>
    fs [] >>
    rw [check_t_to_check_freevars])
  >- simp [nsLookupMod_nsMap]
  >- (
    rw [env_rel_sound_def, lookup_var_def] >>
    `?tvs t. ts = (tvs,t)` by metis_tac [pair_CASES] >>
    rw [] >>
    qexists_tac `tvs` >>
    qexists_tac `convert_t t` >>
    `check_t tvs {} t`
      by (
        fs [ienv_ok_def, ienv_val_ok_def] >>
        drule nsLookup_nsAll >>
        disch_then drule >>
        simp []) >>
    rw []
    >- metis_tac [check_t_to_check_freevars]
    >- simp [nsLookup_nsMap]
    >- (
      drule check_t_empty_unconvert_convert_id >>
      rw [tscheme_approx_refl]))
  >- (
    simp [env_rel_complete_def, lookup_var_def, nsLookup_nsMap] >>
    rpt gen_tac >>
    strip_tac >>
    pairarg_tac >>
    fs [] >>
    rpt var_eq_tac >>
    `check_t tvs {} t'`
      by (
        fs [ienv_ok_def, ienv_val_ok_def] >>
        drule nsLookup_nsAll >>
        disch_then drule >>
        simp []) >>
    rw []
    >- metis_tac [check_t_to_check_freevars] >>
    drule check_t_empty_unconvert_convert_id >>
    rw [tscheme_approx_refl])
QED

val tenv_to_ienv_def = Define `
  tenv_to_ienv tenv =
    <| inf_v := nsMap (\(tvs, t). (tvs, unconvert_t t)) tenv.v;
       inf_c := tenv.c;
       inf_t := tenv.t |>`;

Theorem tenv_to_ienv_extend:
   !tenv1 tenv2.
    tenv_to_ienv (extend_dec_tenv tenv2 tenv1) =
    extend_dec_ienv (tenv_to_ienv tenv2) (tenv_to_ienv tenv1)
Proof
  rw [tenv_to_ienv_def, extend_dec_tenv_def, extend_dec_ienv_def, nsMap_nsAppend]
QED

Theorem env_rel_tenv_to_ienv:
   !tenv. tenv_ok tenv ⇒ env_rel tenv (tenv_to_ienv tenv)
Proof
  rw [env_rel_def, tenv_to_ienv_def]
  >- (
    fs [ienv_ok_def, typeSoundInvariantsTheory.tenv_ok_def,
        typeSoundInvariantsTheory.tenv_val_ok_def] >>
    simp [ienv_val_ok_def] >>
    simp [nsAll_nsMap] >>
    irule nsAll_mono >>
    HINT_EXISTS_TAC >>
    rw [] >>
    pairarg_tac >>
    simp [] >>
    pairarg_tac >>
    fs [] >>
    rw [check_freevars_to_check_t])
  >- simp [nsLookupMod_nsMap]
  >- (
    rw [env_rel_sound_def, lookup_var_def] >>
    `?tvs t. ts = (tvs,t)` by metis_tac [pair_CASES] >>
    rw [] >>
    qexists_tac `tvs` >>
    qexists_tac `convert_t t` >>
    fs [nsLookup_nsMap] >>
    pairarg_tac >>
    fs [] >>
    rpt var_eq_tac >>
    `check_freevars tvs [] t'`
      by (
        fs [typeSoundInvariantsTheory.tenv_ok_def, typeSoundInvariantsTheory.tenv_val_ok_def] >>
        fs [nsLookup_nsMap] >>
        drule nsLookup_nsAll >>
        disch_then drule >>
        simp []) >>
    rw []
    >- metis_tac [check_freevars_empty_convert_unconvert_id]
    >- metis_tac [check_freevars_empty_convert_unconvert_id]
    >- (
      drule check_freevars_empty_convert_unconvert_id >>
      rw [tscheme_approx_refl]))
  >- (
    rw [env_rel_complete_def, lookup_var_def, nsLookup_nsMap, tscheme_approx_refl] >>
    fs [typeSoundInvariantsTheory.tenv_ok_def, typeSoundInvariantsTheory.tenv_val_ok_def] >>
    drule nsLookup_nsAll >>
    disch_then drule >>
    simp [] >>
    metis_tac [])
QED

Theorem tenv_to_ienv_lift:
   !mn tenv. tenv_to_ienv (tenvLift mn tenv) = lift_ienv mn (tenv_to_ienv tenv)
Proof
  rw [tenv_to_ienv_def, lift_ienv_def, tenvLift_def, namespacePropsTheory.nsLift_nsMap]
QED

val _ = export_theory ();

(*
  Defines a unification algorithm for use in the type inferencer.
  Based on the triangular unification algorithm in
  HOL/examples/unification/triangular/first-order.  We encode our
  CakeML types into the term structure used there and them bring over
  those definitions and theorems.
*)
open preamble;
open unifPropsTheory unifDefTheory walkTheory walkstarTheory collapseTheory;
open substTheory;
open infer_tTheory;
open rmfmapTheory tcallUnifTheory
open transferTheory transferLib

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = new_theory "unify";

val _ = monadsyntax.temp_enable_monadsyntax()
val _ = monadsyntax.temp_enable_monad "option"

val option_map_case = Q.prove (
  `!f opt.
    OPTION_MAP f opt =
    dtcase opt of
         NONE => NONE
       | SOME a => SOME (f a)`,
  simp[FUN_EQ_THM] >>
  gen_tac >> Cases >>
  rw[OPTION_MAP_DEF]);

val option_bind_thm = Q.prove (
`!x f. OPTION_BIND x f =
  dtcase x of
    | NONE => NONE
    | SOME y => f y`,
cases_on `x` >>
rw [OPTION_BIND_def]);

val I_o_f = Q.prove (
`!m. I o_f m = m`,
rw [GSYM fmap_EQ_THM]);

Datatype:
  atom
  = TC_tag type_ident
  | DB_tag num
  | Tapp_tag
  | Null_tag
End

Definition encode_infer_t_def:
(encode_infer_t (Infer_Tvar_db n) =
  Const (DB_tag n)) ∧
(encode_infer_t (Infer_Tapp ts tc) =
  Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) (encode_infer_ts ts))) ∧
(encode_infer_t (Infer_Tuvar n) =
  Var n) ∧
(encode_infer_ts [] =
  Const Null_tag) ∧
(encode_infer_ts (t::ts) =
  Pair (encode_infer_t t) (encode_infer_ts ts))
End

Definition decode_infer_t_def:
(decode_infer_t (Var n) =
  Infer_Tuvar n) ∧
(decode_infer_t (Const (DB_tag n)) =
  Infer_Tvar_db n) ∧
(decode_infer_t (Pair (Const Tapp_tag) (Pair (Const (TC_tag tc)) s)) =
  Infer_Tapp (decode_infer_ts s) tc) ∧
(decode_infer_t _ = Infer_Tuvar 5) ∧
(decode_infer_ts (Const Null_tag) =
  []) ∧
(decode_infer_ts (Pair s1 s2) =
  decode_infer_t s1 :: decode_infer_ts s2) ∧
(decode_infer_ts _ = [])
End

Theorem decode_left_inverse[local]:
  (!t. decode_infer_t (encode_infer_t t) = t) ∧
  (!ts. decode_infer_ts (encode_infer_ts ts) = ts)
Proof
Induct >>
rw [encode_infer_t_def, decode_infer_t_def]
QED

Theorem decode_right_inverse[local]:
  (!t. (?t'. t = encode_infer_t t') ⇒ (encode_infer_t (decode_infer_t t) = t)) ∧
  (!ts. (?ts'. ts = encode_infer_ts ts') ⇒ (encode_infer_ts (decode_infer_ts ts) = ts))
Proof
Induct  >>
rw [encode_infer_t_def, decode_infer_t_def] >>
rw [decode_left_inverse]
QED

Theorem option_CASE_MAP:
  option_CASE (OPTION_MAP f v) n sf =
  option_CASE v n (sf o f)
Proof
  Cases_on ‘v’ >> simp[]
QED

Theorem list_CASE_MAP:
  list_CASE (MAP f l) n cf =
  list_CASE l n (λh t. cf (f h) (MAP f t))
Proof
  Cases_on ‘l’ >> simp[]
QED


Theorem decode_option_CASE[local]:
  decode_infer_t (option_CASE v n sf) =
  option_CASE v (decode_infer_t n) (decode_infer_t o sf)
Proof
  Cases_on ‘v’ >> simp[]
QED

Theorem decode_infer_t_CASE[local]:
  decode_infer_t (infer_t_CASE it dbf appf uvf) =
  infer_t_CASE it (decode_infer_t o dbf)
                  (λl n. decode_infer_t (appf l n))
                  (decode_infer_t o uvf)
Proof
  Cases_on ‘it’ >> simp[]
QED

(* "Ramana Kumar unification type to CakeML type" relation *)
Definition RKC_def:
  RKC rkt ct ⇔ encode_infer_t ct = rkt
End

Definition cwfs_def:
  cwfs s <=> swfs (map encode_infer_t s) /\ wf s
End

Definition SPREL_def:
  SPREL R (sp1:'a num_map) (sp2:'b num_map) ⇔
    wf sp1 /\ wf sp2 /\
    ∀n. OPTREL R (lookup n sp1) (lookup n sp2)
End

Definition sprkc_def:
  sprkc m1 m2 ⇔ m1 = map encode_infer_t m2 /\ wf m2 /\ swfs m1
End

Theorem wfs_rule[transfer_rule]:
  (sprkc |==> (=)) swfs cwfs
Proof
  simp[cwfs_def, FUN_REL_def, sprkc_def, swfs_def,
       wfs_def] >> rw[]
QED

Theorem svwalk_result_encodable:
  wf fm /\ swfs (map f fm) ∧ (∀n. ∃y. Var n = f y) ⇒
  ∀x. ∃y. svwalk (map f fm) x = f y
Proof
  strip_tac >> ‘wfs (sp2fm (map f fm))’ by gvs[swfs_def] >>
  drule (DISCH_ALL walkTheory.vwalk_ind) >>
  simp[RIGHT_FORALL_IMP_THM] >> disch_then ho_match_mp_tac >> rw[] >>
  simp[Once svwalk_thm] >> rename [‘lookup k (map f fm)’] >>
  Cases_on ‘lookup k (map f fm)’ >> simp[] >>
  gvs[AllCaseEqs(), lookup_map] >> rename [‘f v = Pair _ _’] >>
  Cases_on ‘f v’ >> simp[] >> metis_tac[]
QED

Definition cvwalk_def:
  cvwalk s n = decode_infer_t (svwalk (map encode_infer_t s) n)
End

Theorem cvwalk_rule[transfer_rule]:
  (sprkc |==> (=) |==> RKC) svwalk cvwalk
Proof
  simp[cvwalk_def, FUN_REL_def, RKC_def, sprkc_def] >>
  rw[] >> rename [‘swfs (map encode_infer_t s)’] >>
  irule $ cj 1 decode_right_inverse >> irule svwalk_result_encodable >>
  simp[] >> metis_tac[encode_infer_t_def]
QED

Theorem sprkc_lookup[transfer_rule]:
  ((=) |==> sprkc |==> OPTREL RKC) lookup lookup
Proof
  simp[FUN_REL_def, sprkc_def] >> rw[] >>
  rename [‘lookup k (map encode_infer_t m)’] >>
  Cases_on ‘lookup k m’ >> simp[lookup_map, RKC_def]
QED

Theorem term_CASE_encode:
  term_CASE (encode_infer_t v) vf pf cf =
  infer_t_CASE v
               (cf o DB_tag)
               (λl n. pf (Const Tapp_tag)
                         (Pair (Const (TC_tag n)) (encode_infer_ts l)))
               vf
Proof
  Cases_on ‘v’ >> simp[encode_infer_t_def]
QED

Theorem cvwalk_thm =
        cvwalk_def |> SPEC_ALL
                   |> SRULE[lookup_map, option_CASE_MAP, combinTheory.o_ABS_L,
                            term_CASE_encode, Once svwalk_thm,
                           ASSUME “wf (map encode_infer_t s)”,
                           ASSUME “swfs (map encode_infer_t s)”]
                    |> SRULE[GSYM encode_infer_t_def, GSYM cvwalk_def,
                             decode_option_CASE, decode_left_inverse,
                             decode_infer_t_CASE,
                             combinTheory.o_ABS_R]

(*
Definition binRKC_def:
  binRKC AB (f : atom term -> atom term -> 'a)
            (itf : infer_t list -> num -> 'b) ⇔
    !l n. AB (f (Const Tapp_tag) (Pair (Const (TC_tag n)) (encode_infer_ts l)))
             (itf l n)
End

Theorem term_CASE_rule[transfer_rule]:
  (RKC |==> ((=) |==> AB) |==> binRKC AB |==> ((=) |==> AB) |==> AB)
  term_CASE
  (λarg v p c. infer_t_CASE arg (c o DB_tag) p v)
Proof
  simp[FUN_REL_def, RKC_def, term_CASE_encode, binRKC_def] >> rw[] >>
  Cases_on ‘arg’ >> simp[]
  qx_gen_tac ‘it’ >> qx_gen_tac ‘vf’ >> qx_gen_tac ‘cvf’ >> strip_tac >>

  cvwalk
*)

Definition cwalk_def[nocompute]:
  cwalk s it = decode_infer_t $ swalk (map encode_infer_t s) (encode_infer_t it)
End

Theorem swalk_result_encodable:
  !s it. cwfs s ==>
         ?it'. swalk (map encode_infer_t s) (encode_infer_t it) =
               encode_infer_t it'
Proof
  simp[cwfs_def, swalk_thm, term_CASE_encode,
       AllCaseEqs()] >> rpt strip_tac >>
  Cases_on ‘it’ >> simp[]
  >- metis_tac[encode_infer_t_def]
  >- metis_tac[encode_infer_t_def] >>
  rename [‘svwalk _ n’] >> qid_spec_tac ‘n’ >>
  irule svwalk_result_encodable >> simp[] >> metis_tac[encode_infer_t_def]
QED

Theorem swalk_elim:
  cwfs s ==>
  swalk (map encode_infer_t s) (encode_infer_t it) =
  encode_infer_t (cwalk s it)
Proof
  strip_tac >> simp[cwalk_def] >> ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
  irule (cj 1 decode_right_inverse) >> metis_tac[swalk_result_encodable]
QED

val cwf = ASSUME “cwfs s” |> SRULE[cwfs_def] |> cj 2
val cwfs = ASSUME “cwfs s” |> SRULE[cwfs_def] |> cj 1
Theorem cwalk_thm =
        cwalk_def |> SPEC_ALL
                  |> SRULE [swalk_thm, term_CASE_encode,
                            decode_infer_t_CASE, combinTheory.o_ABS_L,
                            combinTheory.o_ABS_R, cwf]
                  |> SRULE[decode_infer_t_def, decode_left_inverse,
                           GSYM cvwalk_def]

Definition coc_def[nocompute]:
  coc s it n = soc (map encode_infer_t s) (encode_infer_t it) n
End

Theorem soc_encode_ts:
  cwfs s ==>
  (soc (map encode_infer_t s) (encode_infer_ts its) n ⇔
     EXISTS (λi. soc (map encode_infer_t s) (encode_infer_t i) n) its)
Proof
  strip_tac >> map_every assume_tac [cwf, cwfs] >>
  Induct_on ‘its’ >>
  simp[encode_infer_t_def, soc_thm]
QED

Theorem coc_thm =
        coc_def |> SPEC_ALL
                |> SRULE[Once soc_walking, cwf, cwfs,
                         UNDISCH swalk_elim, term_CASE_encode,
                         combinTheory.o_DEF]
                |> SRULE[soc_thm, cwf, UNDISCH soc_encode_ts]
                |> SRULE[GSYM coc_def]

Definition cunify_def:
  cunify s t1 t2 = OPTION_MAP (map decode_infer_t)
                              (sunify (map encode_infer_t s) (encode_infer_t t1)
                                      (encode_infer_t t2))
End

Theorem fm2sp_delete:
  fm2sp (fm \\ k) = delete k $ fm2sp fm
Proof
  simp[spt_eq_thm, wf_delete, lookup_delete, DOMSUB_FLOOKUP_THM] >>
  metis_tac[]
QED

Theorem domain_fm2sp:
  ∀fm. domain (fm2sp fm) = FDOM fm
Proof
  Induct >> simp[fm2sp_delete, DELETE_NON_ELEMENT_RWT]
QED

Theorem swalk_encode_infer_ts_EQ_VAR:
  swfs s ∧ wf s ⇒ swalk s (encode_infer_ts ts) ≠ Var v
Proof
  Cases_on ‘ts’ >> simp[swalk_thm, encode_infer_t_def]
QED

Theorem encode_t_vs_ts:
  encode_infer_t x ≠ encode_infer_ts l
Proof
  Cases_on ‘x’ >> Cases_on ‘l’ >> simp[encode_infer_t_def] >>
  Cases_on ‘h’ >> simp[encode_infer_t_def]
QED

Theorem swalk_encode_infer_ts:
  wf s ⇒ swalk s (encode_infer_ts ts) = encode_infer_ts ts
Proof
  Cases_on ‘ts’ >> simp[encode_infer_t_def, swalk_thm]
QED

Theorem sunify_wf:
  ∀s t1 t2 s'. swfs s ∧ wf s ∧ sunify s t1 t2 = SOME s' ⇒ wf s'
Proof
  ‘∀f t1 t2 s'. wfs f ∧ sunify (fm2sp f) t1 t2 = SOME s' ⇒ wf s'’
    suffices_by (rpt strip_tac >>
                 first_x_assum $ qspec_then ‘sp2fm s’ mp_tac >>
                 simp[] >> gvs[swfs_def] >> metis_tac[]) >>
  recInduct unify_ind >> rpt gen_tac >> strip_tac >>
  simp[Once sunify_thm, swfs_def, SF CONJ_ss]>>
  simp[AllCaseEqs()] >> rw[] >> simp[wf_insert] >>
  gvs[swalk_def] >> gvs[sunify_def]
QED

Theorem sunify_constconst:
  wf s ∧ swfs s ⇒
  sunify s (Const c1) (Const c2) = if c1 = c2 then SOME s else NONE
Proof
  simp[Once sunify_thm, swalk_thm]
QED

Theorem sunify_pairconstconst:
  wf s ∧ swfs s ⇒
  sunify s (Pair (Const c1) t1) (Pair (Const c2) t2) =
  if c1 = c2 then sunify s t1 t2 else NONE
Proof
  simp[Once sunify_thm, swalk_thm, sunify_constconst] >> rw[]
QED

Theorem sunify_result_encodable:
  ∀st1t2 s pt1 pt2 s'.
    st1t2 = (s,pt1,pt2) ∧ swfs (map encode_infer_t s) ∧ wf s ∧
    ((∃t1 t2. pt1 = encode_infer_t t1 ∧ pt2 = encode_infer_t t2) ∨
     (∃ts1 ts2. pt1 = encode_infer_ts ts1 ∧ pt2 = encode_infer_ts ts2)) ∧
    sunify (map encode_infer_t s) pt1 pt2 = SOME s' ⇒
    ∃m. s' = map encode_infer_t m
Proof
  ‘WF (inv_image uR (λ(s,t1,t2). (sp2fm (map encode_infer_t s), t1, t2)))’
    by (irule WF_inv_image >> simp[unifDefTheory.WF_uR]) >>
  dxrule WF_INDUCTION_THM >> strip_tac >>
  RULE_ASSUM_TAC (SRULE[RIGHT_FORALL_IMP_THM])>>
  pop_assum ho_match_mp_tac >> simp[FORALL_PROD] >> rw[] >>
  rename [‘sunify (map encode_infer_t σ) _ _’] >>
  pop_assum mp_tac >> simp[Once sunify_thm] >>
  simp[AllCaseEqs()] >> rw[] >> gvs[swalk_encode_infer_ts_EQ_VAR] >>~-
  ([‘swalk _ (encode_infer_t _) = Var _’,
    ‘insert _ _ _ = map encode_infer_t _’],
   qmatch_abbrev_tac ‘∃m. insert k M _ = _ m’ >>
   ‘∃M0. M = encode_infer_t M0’
     by (qpat_x_assum ‘swalk _ _ = M’ (SUBST1_TAC o SYM) >>
         irule swalk_result_encodable >> simp[cwfs_def, swfs_def]) >>
   pop_assum SUBST1_TAC >>
   irule_at Any (GSYM map_insert)) >>~-
  ([‘map encode_infer_t σ = map encode_infer_t _’],
   irule_at Any EQ_REFL) >~
  [‘swalk (map encode_infer_t σ) (encode_infer_t t1) = Pair _ _’,
   ‘(_, encode_infer_t t1, encode_infer_t t2)’]
  >- (‘∃it1. swalk (map encode_infer_t σ) (encode_infer_t t1) =
             encode_infer_t it1’
        by (irule swalk_result_encodable >> simp[cwfs_def]) >>
      ‘∃it2. swalk (map encode_infer_t σ) (encode_infer_t t2) =
             encode_infer_t it2’
        by (irule swalk_result_encodable >> simp[cwfs_def]) >>
      gvs[] >>
      Cases_on ‘it1’ >> gvs[encode_infer_t_def] >>
      Cases_on ‘it2’ >> gvs[encode_infer_t_def] >>
      gvs[sunify_constconst, sunify_pairconstconst] >>
      first_x_assum irule >> first_assum $ irule_at (Pat ‘sunify _ _ _ = _’) >>
      simp[encode_t_vs_ts, PULL_EXISTS] >>
      rpt (irule_at Any EQ_REFL) >>
      simp[uR_def] >> gvs[swalk_def, swfs_def] >>
      qabbrev_tac ‘θ = sp2fm (map encode_infer_t σ)’ >>
      conj_tac
      >- (dxrule_all allvars_SUBSET >> simp[allvars_def] >>
          SET_TAC[]) >>
      drule_then (rpt o dxrule) walkstar_subterm_smaller >>
      simp[]) >>
  gvs[swalk_encode_infer_ts] >>
  Cases_on ‘ts1’ >> gvs[encode_infer_t_def] >>
  Cases_on ‘ts2’ >> gvs[encode_infer_t_def] >>
  rename [‘sunify _ (encode_infer_t t1) (encode_infer_t t2)’] >>
  first_assum (qpat_assum ‘sunify _ (encode_infer_t t1) _ = SOME _’ o
               mp_then Any mp_tac) >>
  impl_tac
  >- (simp[encode_t_vs_ts, PULL_EXISTS] >>
      rpt (irule_at Any EQ_REFL) >>
      simp[uR_def] >> gvs[swfs_def] >>
      simp[allvars_def] >> SET_TAC []) >>
  disch_then $ qx_choose_then ‘σ'’ strip_assume_tac >> gvs[] >>
  first_x_assum irule >> first_assum $ irule_at Any >>
  simp[encode_t_vs_ts, PULL_EXISTS] >> rpt $ irule_at Any EQ_REFL >>
  gvs[swfs_def, sunify_def] >>
  drule_all_then strip_assume_tac unify_unifier >> simp[] >>
  ‘wf (map encode_infer_t σ')’ by (ASM_REWRITE_TAC[] >> simp[]) >> gvs[] >>
  simp[uR_def] >> simp[allvars_def] >> rw[]
  >- SET_TAC[]
  >- SET_TAC[]
  >- (qpat_assum ‘unify _ (encode_infer_t t1) _ = SOME _’
                 (mp_then Any mp_tac unify_uP) >> simp[] >>
      simp[uP_def, allvars_def] >> SET_TAC[])
QED

Theorem map_decode_encode:
  cwfs s ==> map decode_infer_t (map encode_infer_t s) = s
Proof
  strip_tac >> gvs[cwfs_def] >> simp[spt_eq_thm, lookup_map]>>
  simp[OPTION_MAP_COMPOSE, combinTheory.o_DEF, decode_left_inverse]
QED

Theorem sunify_t_elim:
  cwfs s ⇒
  sunify (map encode_infer_t s) (encode_infer_t t1) (encode_infer_t t2) =
  OPTION_MAP (map encode_infer_t) (cunify s t1 t2)
Proof
  simp[cunify_def, OPTION_MAP_COMPOSE] >>
  Cases_on ‘sunify (map encode_infer_t s) (encode_infer_t t1)
            (encode_infer_t t2)’ >> simp[] >>
  drule_at Any sunify_result_encodable>> simp[encode_t_vs_ts] >> rw[] >>
  gvs[cwfs_def, PULL_EXISTS] >>
  first_x_assum (resolve_then Any mp_tac EQ_REFL) >>
  disch_then (resolve_then Any mp_tac EQ_REFL) >> rw[] >>
  AP_TERM_TAC >> irule (GSYM map_decode_encode) >>
  simp[cwfs_def] >> drule sunify_wf >> simp[] >> disch_then drule >> simp[] >>
  gvs[swfs_def, sunify_def] >> metis_tac[unify_unifier]
QED

Theorem option_map_itcase:
  OPTION_MAP f (infer_t_CASE arg x y z) =
  infer_t_CASE arg (OPTION_MAP f o x) (λl n. OPTION_MAP f (y l n))
               (OPTION_MAP f o z)
Proof
  Cases_on ‘arg’ >> simp[]
QED

Theorem option_map_COND:
  OPTION_MAP f (COND g t e) = COND g (OPTION_MAP f t) (OPTION_MAP f e)
Proof
  rw[]
QED

Theorem sptree_map_COND:
  sptree$map f (COND g t e) = COND g (map f t) (map f e)
Proof
  rw[]
QED

Theorem SOME_COND:
  SOME (COND g t e) = COND g (SOME t) (SOME e)
Proof
  rw[]
QED

Theorem OPTION_MAP_BIND:
  OPTION_MAP f (OPTION_BIND m mf) =
  OPTION_BIND m (OPTION_MAP f o mf)
Proof
  Cases_on ‘m’ >> simp[]
QED

Theorem OPTION_BIND_MAP:
  OPTION_BIND (OPTION_MAP f m) mf =
  OPTION_BIND m (mf o f)
Proof
  Cases_on ‘m’ >> simp[]
QED

Definition cunifyl_def:
    cunifyl s ts1 ts2 =
    OPTION_MAP (map decode_infer_t)
               (sunify (map encode_infer_t s)
                       (encode_infer_ts ts1)
                       (encode_infer_ts ts2))
End

Theorem sunify_preserves_swfs:
  swfs s ∧ sunify s t1 t2 = SOME s' ⇒ swfs s'
Proof
  simp[swfs_def, sunify_def, PULL_EXISTS] >>
  metis_tac[unifPropsTheory.unify_unifier]
QED

Theorem cunify_thm =
        cunify_def |> SPEC_ALL
                   |> SRULE [Once sunify_thm, cwf, cwfs,
                             UNDISCH swalk_elim, term_CASE_encode,
                             combinTheory.o_DEF]
                   |> SRULE[soc_thm, cwf, cwfs, GSYM coc_def,
                            option_map_itcase, combinTheory.o_ABS_R,
                            UNDISCH map_decode_encode, decode_left_inverse,
                            option_map_COND, map_insert, sptree_map_COND,
                            UNDISCH soc_encode_ts, decode_infer_t_def,
                            sunify_constconst, sunify_pairconstconst, SOME_COND,
                            GSYM cunifyl_def]

Theorem cunifyl_NIL2 =
        cunifyl_def |> SPEC_ALL
                    |> Q.INST [‘ts1’ |-> ‘[]’, ‘ts2’ |-> ‘[]’]
                    |> SRULE [Once sunify_thm, cwf, cwfs,
                              encode_infer_t_def, swalk_thm,
                              UNDISCH swalk_elim, term_CASE_encode,
                              UNDISCH map_decode_encode,
                              combinTheory.o_DEF]
Theorem cunifyl_NILCONS =
        cunifyl_def |> SPEC_ALL
                    |> Q.INST [‘ts1’ |-> ‘[]’, ‘ts2’ |-> ‘t2::ts2’]
                    |> SRULE [Once sunify_thm, cwf, cwfs,
                              encode_infer_t_def, swalk_thm,
                              UNDISCH swalk_elim, term_CASE_encode,
                              UNDISCH map_decode_encode,
                              combinTheory.o_DEF]
Theorem cunifyl_CONSNIL =
        cunifyl_def |> SPEC_ALL
                    |> Q.INST [‘ts1’ |-> ‘t1::ts1’, ‘ts2’ |-> ‘[]’]
                    |> SRULE [Once sunify_thm, cwf, cwfs,
                              encode_infer_t_def, swalk_thm,
                              UNDISCH swalk_elim, term_CASE_encode,
                              UNDISCH map_decode_encode,
                              combinTheory.o_DEF]

Theorem cunifyl_CONS2 =
        cunifyl_def |> SPEC_ALL
                    |> Q.INST [‘ts1’ |-> ‘t1::ts1’, ‘ts2’ |-> ‘t2::ts2’]
                    |> SRULE [Once sunify_thm, cwf, cwfs,
                              encode_infer_t_def, swalk_thm,
                              OPTION_MAP_BIND, combinTheory.o_DEF,
                              encode_infer_t_def, swalk_thm,
                              UNDISCH swalk_elim, term_CASE_encode,
                              UNDISCH map_decode_encode,
                              UNDISCH sunify_t_elim, OPTION_BIND_MAP,
                              combinTheory.o_DEF]
                    |> SRULE[GSYM cunifyl_def]

Theorem cunifyl_thm:
  cwfs s ⇒
  cunifyl s ts1 ts2 =
  dtcase (ts1,ts2) of
    ([],[]) => SOME s
  | (t1::ts1, t2::ts2) => do s' <- cunify s t1 t2; cunifyl s' ts1 ts2 od
  | _ => NONE
Proof
  Cases_on ‘ts1’ >> Cases_on ‘ts2’ >>
  simp[cunifyl_NILCONS, cunifyl_NIL2, cunifyl_CONS2, cunifyl_CONSNIL]
QED

Theorem sp2fm_map:
  sp2fm (map f sp) = f o_f sp2fm sp
Proof
  simp[finite_mapTheory.FLOOKUP_EXT, fmspTheory.FLOOKUP_sp2fm, FUN_EQ_THM,
       lookup_map, finite_mapTheory.FLOOKUP_o_f] >>
  simp[optionTheory.OPTION_MAP_CASE, combinTheory.o_DEF]
QED




Theorem decode_infer_t_pmatch:
    (!t. decode_infer_t t =
    case t of
      Var n => Infer_Tuvar n
    | Const (DB_tag n) => Infer_Tvar_db n
    | Pair (Const Tapp_tag) (Pair (Const (TC_tag tc')) s) =>
      Infer_Tapp (decode_infer_ts s) tc'
    | _ => Infer_Tuvar 5) /\
  (!ts. decode_infer_ts ts =
    case ts of
    | Const Null_tag => []
    | Pair s1 s2 => decode_infer_t s1 :: decode_infer_ts s2
    | _ => [])
Proof
  rpt strip_tac
  >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac)
  >> TRY (Cases_on `a`) >> fs[decode_infer_t_def]
QED

Theorem decode_left_inverse_I[local]:
  decode_infer_t o encode_infer_t = I
Proof
rw [FUN_EQ_THM] >>
metis_tac [decode_left_inverse]
QED

Theorem decode_right_inverse[local]:
  (!t. (?t'. t = encode_infer_t t') ⇒ (encode_infer_t (decode_infer_t t) = t)) ∧
  (!ts. (?ts'. ts = encode_infer_ts ts') ⇒ (encode_infer_ts (decode_infer_ts ts) = ts))
Proof
Induct  >>
rw [encode_infer_t_def, decode_infer_t_def] >>
rw [decode_left_inverse]
QED

Definition t_wfs_def[nocompute]:
  t_wfs s = wfs (encode_infer_t o_f s)
End

Definition t_vwalk_def[nocompute]:
  t_vwalk s v = decode_infer_t (vwalk (encode_infer_t o_f s) v)
End

val t_vwalk_ind' = Q.prove (
`!s'. t_wfs s' ⇒
   ∀P.
     (∀v. (∀v1 u. (FLOOKUP s' v = SOME v1) ∧ (v1 = Infer_Tuvar u) ⇒ P u) ⇒ P v) ⇒
     ∀v. P v`,
ntac 4 STRIP_TAC >>
fs [t_wfs_def] >>
imp_res_tac (DISCH_ALL vwalk_ind) >>
pop_assum ho_match_mp_tac >>
rw [] >>
qpat_x_assum `∀v. (∀u. (FLOOKUP s' v = SOME (Infer_Tuvar u)) ⇒ P u) ⇒ P v` ho_match_mp_tac >>
rw [] >>
qpat_x_assum `∀u. Q u ⇒ P u` ho_match_mp_tac >>
rw [FLOOKUP_o_f, encode_infer_t_def]);

val t_vwalk_ind = save_thm("t_vwalk_ind", (UNDISCH o Q.SPEC `s`) t_vwalk_ind')

Theorem t_vwalk_eqn:
 !s.
  t_wfs s ⇒
  (!v.
    t_vwalk s v =
    dtcase FLOOKUP s v of
      | NONE => Infer_Tuvar v
      | SOME (Infer_Tuvar u) => t_vwalk s u
      | SOME (Infer_Tapp ts tc') => Infer_Tapp ts tc'
      | SOME (Infer_Tvar_db n) => Infer_Tvar_db n)
Proof
rw [t_vwalk_def] >>
full_case_tac >>
rw [] >>
fs [t_wfs_def] >|
[rw [Once vwalk_def] >>
     full_case_tac >>
     rw [decode_infer_t_def] >>
     fs [FLOOKUP_o_f] >>
     cases_on `FLOOKUP s v` >>
     fs [],
 rw [Once vwalk_def, FLOOKUP_o_f] >>
     cases_on `x` >>
     rw [encode_infer_t_def, decode_infer_t_def, decode_left_inverse]]
QED

val t_walk_def = zDefine `
t_walk s t = decode_infer_t (walk (encode_infer_t o_f s) (encode_infer_t t))`;

Theorem t_walk_eqn:
 (!s v. t_walk s (Infer_Tuvar v) = t_vwalk s v) ∧
 (!s ts tc. t_walk s (Infer_Tapp ts tc) = Infer_Tapp ts tc) ∧
 (!s n. t_walk s (Infer_Tvar_db n) = Infer_Tvar_db n)
Proof
rw [t_walk_def, walk_def, t_vwalk_def, encode_infer_t_def,
    decode_infer_t_def, decode_left_inverse]
QED

val t_oc_def = zDefine `
t_oc s t v = oc (encode_infer_t o_f s) (encode_infer_t t) v`;

val t_vars_def = Define `
t_vars t = vars (encode_infer_t t)`;

(*
val t_oc_ind' = Q.prove (
`∀s oc'.
  t_wfs s ∧
  (∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v) ∧
  (∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v) ⇒
  (∀a0 a1. oc (FMAP_MAP2 (λ(n,t). encode_infer_t t) s) a0 a1 ⇒ !a0'. (a0 = encode_infer_t a0') ⇒ oc' a0' a1)`,
NTAC 3 STRIP_TAC >>
ho_match_mp_tac oc_ind >>
rw [] >|
[qpat_x_assum `∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v` ho_match_mp_tac >>
     fs [t_vars_def, FMAP_MAP2_THM],
 qpat_x_assum `∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v` ho_match_mp_tac >>
     rw [t_vars_def] >>
     qexists_tac `u` >>
     rw [] >>
     pop_assum ho_match_mp_tac >>
     rw [encode_vwalk]]);

Theorem t_oc_ind:
 ∀s oc'.
  t_wfs s ∧
  (∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v) ∧
  (∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v) ⇒
  (∀a0 a1. t_oc s a0 a1 ⇒ oc' a0 a1)
Proof
rw [t_oc_def] >>
metis_tac [t_oc_ind', FMAP2_FMAP2, FMAP2_id, decode_left_inverse]
QED
*)

val encode_vwalk = Q.prove (
`!s. t_wfs s ⇒ !u. vwalk (encode_infer_t o_f s) u = encode_infer_t (t_vwalk s u)`,
NTAC 2 STRIP_TAC >>
ho_match_mp_tac t_vwalk_ind >>
rw [] >>
`wfs (encode_infer_t o_f s)` by metis_tac [t_wfs_def] >>
rw [Once vwalk_def] >>
rw [Once t_vwalk_eqn, FLOOKUP_o_f] >>
cases_on `FLOOKUP s u` >>
rw [encode_infer_t_def] >>
cases_on `x` >>
rw [encode_infer_t_def]);

val t_oc_eqn_help = Q.prove (
`!l v s.
  oc (encode_infer_t o_f s) (encode_infer_ts l) v ⇔
  EXISTS (λt. oc (encode_infer_t o_f s) (encode_infer_t t) v) l`,
induct_on `l` >>
rw [encode_infer_t_def]);

Theorem t_oc_eqn:
 !s. t_wfs s ⇒
  !t v. t_oc s t v =
    dtcase t_walk s t of
      | Infer_Tuvar u => v = u
      | Infer_Tapp ts tc' => EXISTS (\t. t_oc s t v) ts
      | Infer_Tvar_db n => F
Proof
rw [t_oc_def] >>
`wfs (encode_infer_t o_f s)` by fs [t_wfs_def] >>
rw [Once oc_walking, t_walk_def] >>
cases_on `t` >>
rw [walk_def, encode_infer_t_def, decode_infer_t_def, decode_left_inverse,
    encode_vwalk, t_oc_eqn_help] >>
cases_on `t_vwalk s n` >>
rw [encode_infer_t_def, t_oc_eqn_help]
QED

val t_ext_s_check_def = zDefine `
t_ext_s_check s v t =
  OPTION_MAP
    ((o_f) decode_infer_t)
    (ext_s_check (encode_infer_t o_f s) v (encode_infer_t t))`;

Theorem t_ext_s_check_eqn:
 !s v t.
  t_ext_s_check s v t = if t_oc s t v then NONE else SOME (s |+ (v,t))
Proof
rw [t_ext_s_check_def, t_oc_def, decode_left_inverse_I,
    I_o_f, decode_left_inverse] >>
metis_tac [FUPDATE_PURGE]
QED

val t_unify_def = zDefine `
t_unify s t1 t2 =
  OPTION_MAP
    ((o_f) decode_infer_t)
    (unify (encode_infer_t o_f s) (encode_infer_t t1) (encode_infer_t t2))`;

val ts_unify_def = Define `
(ts_unify s [] [] = SOME s) ∧
(ts_unify s (t1::ts1) (t2::ts2) =
  dtcase t_unify s t1 t2 of
   | NONE => NONE
   | SOME s' => ts_unify s' ts1 ts2) ∧
(ts_unify s _ _ = NONE)`;

val encode_walk = Q.prove(
  `∀s. t_wfs s ⇒
      ∀t. walk (encode_infer_t o_f s) (encode_infer_t t) = encode_infer_t (t_walk s t)`,
  rw[walk_def] >>
  imp_res_tac encode_vwalk >>
  fs[] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[t_walk_def,decode_left_inverse] >>
  metis_tac[decode_left_inverse])

val encode_pair_cases = Q.prove(
  `(∀t t1 t2.
    (encode_infer_t t = Pair t1 t2) ⇒
      ((t1 = Const Tapp_tag) ∧
       (∃tc ts. t2 = Pair (Const (TC_tag tc)) (encode_infer_ts ts))))`,
  Cases >> rw[encode_infer_t_def] >>
  PROVE_TAC[])

val encode_unify_lemma = Q.prove (
`!s t1 t2 s' t1' t2'.
  (s = (encode_infer_t o_f s')) ∧
  (((t1 = encode_infer_t t1') ∧ (t2 = encode_infer_t t2')) ∨
   (∃c. (t1 = Const c) ∧ (t2 = Const c) ∧ (t1' = t2')) ∨
   (∃c ts1 ts2.
     (t1 = Pair (Const c) (encode_infer_ts ts1)) ∧
     (t2 = Pair (Const c) (encode_infer_ts ts2)) ∧
     (t1' = Infer_Tapp ts1 ARB) ∧
     (t2' = Infer_Tapp ts2 ARB)) ∨
   (∃ts1 ts2.
      (t1 = encode_infer_ts ts1) ∧
      (t2 = encode_infer_ts ts2) ∧
      (t1' = Infer_Tapp ts1 ARB) ∧
      (t2' = Infer_Tapp ts2 ARB))) ∧
  t_wfs s' ⇒
  (unify s t1 t2
   =
   OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))`,
ho_match_mp_tac unify_ind >>
simp[] >>
rw [t_unify_def] >>
fs[t_wfs_def, option_map_case] >>
qmatch_assum_abbrev_tac `wfs es` >>
TRY(simp[option_map_case] >>
  rw[GSYM fmap_EQ_THM,Abbr`es`,decode_left_inverse] >>
  NO_TAC) >>
  (*
TRY(simp[encode_infer_t_def] >>
  simp[Once unify_def,SimpRHS] >>
  rw[option_map_def] >>
  BasicProvers.CASE_TAC >>
  pop_assum mp_tac >>
  simp[Once unify_def] >>
  rw[] >>
  first_x_assum(qspecl_then[`s'`,`t1a`,`t2a`]mp_tac) >>
  rw[option_map_def] >> fs[] >>
  `wfs sx` by (PROVE_TAC[unify_unifier]) >>
  qabbrev_tac`dx = decode_infer_t o_f sx` >>
  first_x_assum(qspecl_then[`dx`,`t1d`,`t2d`]mp_tac) >>
  `sx = encode_infer_t o_f dx` by rw[Abbr`dx`] >>
  pop_assum (SUBST1_TAC o  SYM) >>
  simp[] >>
  rw[option_map_def] >>
  NO_TAC ) >>
  *)
TRY(simp[encode_infer_t_def] >>
  simp[Once unify_def,SimpRHS] >>
  simp[Once unify_def,SimpRHS] >>
  rw[] >>
  BasicProvers.CASE_TAC >>
  pop_assum mp_tac >>
  Cases_on `ts1` >> Cases_on `ts2` >> simp[encode_infer_t_def,Once unify_def] >- (
    rw[] >>
    rw[Abbr`es`,GSYM fmap_EQ_THM,decode_left_inverse] ) >>
  rw[] >>
  fs[encode_infer_t_def] >>
  first_x_assum(qspecl_then[`s'`,`h`,`h'`]mp_tac) >>
  simp[] >>
  rw[] >>
  `wfs sx` by (PROVE_TAC[unify_unifier]) >>
  qabbrev_tac`dx = decode_infer_t o_f sx` >>
  `sx = encode_infer_t o_f dx` by rw[Abbr`dx`] >>
  first_x_assum(qspecl_then[`dx`,`Infer_Tapp t ARB`,`Infer_Tapp t' ARB`]mp_tac) >>
  pop_assum (SUBST1_TAC o  SYM) >>
  simp[] >>
  simp[encode_infer_t_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  rw[] >>
  NO_TAC ) >>
TRY(simp[encode_infer_t_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def,SimpRHS] >>
  simp[Once unify_def,SimpRHS] >>
  rw[] >>
  BasicProvers.CASE_TAC >>
  first_x_assum(qspecl_then[`s'`,`h`,`h'`]kall_tac) >>
  first_x_assum(qspecl_then[`s'`,`Infer_Tapp ts1 ARB`,`Infer_Tapp ts2 ARB`]mp_tac) >>
  simp[encode_infer_t_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  rw[] >>
  NO_TAC ) >>
qmatch_abbrev_tac `unify es e1 e2 = X` >>
qunabbrev_tac`X`>>
Cases_on `unify es e1 e2` >>
rw[] >>
qsuff_tac `∃s. x = encode_infer_t o_f s` >- (
  rw[] >> rw[GSYM fmap_EQ_THM,decode_left_inverse] ) >>
pop_assum mp_tac >>
simp[Once unify_def] >>
Cases_on `walk es e1` >> fs[] >>
Cases_on `walk es e2` >> fs[] >>
TRY (
  strip_tac >> fs[] >>
  qmatch_assum_rename_tac`walk es e1 = Pair t1a t1d` >>
  qmatch_assum_rename_tac`walk es e2 = Pair t2a t2d` >>
  `Pair t1a t1d = encode_infer_t (t_walk s' t1')` by metis_tac[encode_walk,t_wfs_def] >>
  `Pair t2a t2d = encode_infer_t (t_walk s' t2')` by metis_tac[encode_walk,t_wfs_def] >>
  `wfs sx` by metis_tac[unify_unifier] >>
  `∀c1 c2. (((t1a = Const c1) ∧ (t2a = Const c2)) ∨
            ((t1d = Const c1) ∧ (t2d = Const c2)))
    ⇒ (c1 = c2)` by (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `unify X Y Z = SOME A` mp_tac >>
    qpat_x_assum `unify X Y Z = SOME A` mp_tac >>
    asm_simp_tac std_ss [Once unify_def] >>
    strip_tac >>
    asm_simp_tac std_ss [Once unify_def] >>
    pop_assum mp_tac >>
    simp[] ) >>
  qspecl_then[`t_walk s' t1'`,`t1a`,`t1d`]mp_tac encode_pair_cases >>
  qspecl_then[`t_walk s' t2'`,`t2a`,`t2d`]mp_tac encode_pair_cases >>
  simp[] >>
  strip_tac >> strip_tac >> fs[] (*>- (
    rfs[] >> rw[] >>
    rpt (qpat_x_assum `Pair X Y = Z` (assume_tac o SYM)) >>
    first_x_assum (qspecl_then[`s'`,`ARB`,`ARB`]kall_tac) >>
    first_x_assum (qspecl_then[`s'`,`Infer_Tfn ta' td'`,`Infer_Tfn ta td`]mp_tac) >>
    simp[option_map_def,encode_infer_t_def] >>
    simp[Once unify_def] >>
    metis_tac[o_f_o_f] )*) >>
  rfs[] >> rw[] >>
  rpt (qpat_x_assum `Pair X Y = Z` (assume_tac o SYM)) >>
  qpat_x_assum`unify es X Y = Z`mp_tac >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  rw[] >>
  first_x_assum (qspecl_then[`s'`,`Infer_Tapp ts' ARB`,`Infer_Tapp ts ARB`]mp_tac) >>
  simp[encode_infer_t_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  simp[Once unify_def] >>
  rw[] >>
  metis_tac[o_f_o_f] ) >>
metis_tac[o_f_FUPDATE,o_f_DOMSUB,FUPDATE_PURGE,encode_walk,t_wfs_def])

val encode_unify = Q.prove (
`!s t1 t2 s' t1' t2'.
  (s = encode_infer_t o_f s') ∧
  (t1 = encode_infer_t t1') ∧ (t2 = encode_infer_t t2') ∧
  t_wfs s' ⇒
  (unify s t1 t2
   =
   OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))`,
metis_tac[encode_unify_lemma])

val wfs_unify = Q.prove (
`!s t1 t2 s'. wfs s ∧ (unify s t1 t2 = SOME s') ⇒ wfs s'`,
metis_tac [unify_unifier]);

val ts_unify_thm = Q.prove (
`!s l1 l2.
  t_wfs s ⇒
  (ts_unify s l1 l2 =
   OPTION_MAP ((o_f) decode_infer_t)
     (unify (encode_infer_t o_f s) (encode_infer_ts l1) (encode_infer_ts l2)))`,
induct_on `l1` >>
cases_on `l2` >>
rw [ts_unify_def, encode_infer_t_def] >>
`wfs (encode_infer_t o_f s)` by metis_tac [t_wfs_def] >>
fs [option_map_case] >|
[rw [Once unify_def, decode_left_inverse_I, I_o_f],
 rw [Once unify_def, ts_unify_def],
 rw [Once unify_def, ts_unify_def],
 rw [Once unify_def] >>
     cases_on `t_unify s h' h` >>
     rw [] >|
     [fs [t_unify_def, option_bind_thm] >>
          every_case_tac >>
          fs [],
      fs [t_unify_def, option_bind_thm] >>
          every_case_tac >>
          fs [] >>
          rw [I_o_f] >>
          `?x. z = encode_infer_t o_f x`
                by (imp_res_tac encode_unify >>
                    fs [] >>
                    cases_on `t_unify s h' h` >>
                    fs [] >>
                    metis_tac []) >>
          `t_wfs x` by
                 (rw [t_wfs_def] >>
                  metis_tac [wfs_unify]) >>
          rw [I_o_f, decode_left_inverse_I]]]);

Theorem t_unify_eqn:
 (!t1 t2 s.
  t_wfs s ⇒
  (t_unify s t1 t2 =
   dtcase (t_walk s t1, t_walk s t2) of
      (Infer_Tuvar v1, Infer_Tuvar v2) =>
        SOME (if v1 = v2 then s else s |+ (v1,Infer_Tuvar v2))
    | (Infer_Tuvar v1, t2) => t_ext_s_check s v1 t2
    | (t1, Infer_Tuvar v2) => t_ext_s_check s v2 t1
    | (Infer_Tapp ts1 tc1, Infer_Tapp ts2 tc2) =>
        if tc1 = tc2 then
          ts_unify s ts1 ts2
        else
          NONE
    | (Infer_Tvar_db n1, Infer_Tvar_db n2) =>
        if n1 = n2 then
          SOME s
        else
          NONE
    | _ => NONE))
Proof
rw [t_unify_def] >>
`wfs (encode_infer_t o_f s)` by metis_tac [t_wfs_def] >>
rw [Once unify_def, t_walk_def] >>
cases_on `t1` >>
cases_on `t2` >>
rw [encode_infer_t_def, decode_infer_t_def, option_map_case, decode_left_inverse,
    decode_left_inverse_I, I_o_f, encode_vwalk, option_bind_thm]
THEN1
(cases_on `t_vwalk s n'` >>
     rw [encode_infer_t_def, decode_left_inverse,
         decode_left_inverse_I, I_o_f, o_f_FUPDATE, decode_infer_t_def] >>
     rw [t_ext_s_check_eqn] >>
     imp_res_tac t_oc_eqn >>
     pop_assum (fn x => ALL_TAC) >>
     pop_assum (fn x => ALL_TAC) >>
     pop_assum (ASSUME_TAC o Q.SPECL [`n''`, `Infer_Tvar_db n`]) >>
     fs [] >>
     rw [t_walk_def, encode_infer_t_def, decode_infer_t_def] >>
     metis_tac [FUPDATE_PURGE])
THEN1
(rw [Once unify_def] >>
     rw [ts_unify_thm, option_map_case])
THEN1
(rw [Once unify_def] >>
     rw [Once unify_def, option_map_case] >>
     rw [Once unify_def])
THEN1
(cases_on `t_vwalk s n'` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def] >>
     rw [ts_unify_thm, decode_left_inverse, decode_left_inverse_I,
     option_map_case,
         I_o_f, o_f_FUPDATE, decode_infer_t_def, t_ext_s_check_eqn] >>
     rw [Once oc_walking, encode_infer_t_def, t_oc_def] >>
     rw [Once unify_def] >>
     metis_tac [FUPDATE_PURGE])
THEN1
(cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def] >>
     rw [o_f_FUPDATE, I_o_f, decode_left_inverse_I, decode_left_inverse,
         decode_infer_t_def, t_ext_s_check_eqn] >>
     rw [ts_unify_thm, Once oc_walking, encode_infer_t_def, t_oc_def, option_bind_thm] >>
     rw [Once unify_def] >>
     metis_tac [FUPDATE_PURGE])
THEN1
(cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def, option_map_case] >>
     rw [o_f_FUPDATE, I_o_f, decode_left_inverse_I, decode_left_inverse,
     option_map_case,
         decode_infer_t_def, t_ext_s_check_eqn] >>
     rw [ts_unify_thm, Once oc_walking, encode_infer_t_def, t_oc_def, option_bind_thm] >>
     rw [option_map_case] >>
     rw [Once unify_def] >>
     metis_tac [FUPDATE_PURGE]) >>
 cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     cases_on `t_vwalk s n'` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def] >>
     rw [o_f_FUPDATE, I_o_f, decode_left_inverse, decode_left_inverse_I,
         decode_infer_t_def, t_ext_s_check_eqn, option_map_case] >>
     rw [ts_unify_thm, Once oc_walking, encode_infer_t_def, t_oc_def,
     option_bind_thm, option_map_case] >>
     rw [Once unify_def]
QED

val encode_infer_t_inj = Q.prove(
`(!t1 t2. (encode_infer_t t1 = encode_infer_t t2) ==> (t1 = t2)) /\
 (∀t1s t2s. (encode_infer_ts t1s = encode_infer_ts t2s) ⇒ (t1s = t2s))`,
 ho_match_mp_tac(TypeBase.induction_of``:infer_t``)>>
 simp[encode_infer_t_def] >>
 strip_tac >- (
   gen_tac >> Cases >> simp[encode_infer_t_def] ) >>
 strip_tac >- (
   gen_tac >> strip_tac >>
   gen_tac >> Cases >> simp[encode_infer_t_def] ) >>
 strip_tac >- (
   gen_tac >> Cases >> simp[encode_infer_t_def] ) >>
 strip_tac >- (
   Cases >> simp[encode_infer_t_def] ) >>
 rpt gen_tac >> strip_tac >>
 Cases >> simp[encode_infer_t_def])

val encode_infer_t_inj_rwt = Q.prove(
`(!t1 t2. (encode_infer_t t1 = encode_infer_t t2) <=> (t1 = t2)) /\
 (∀t1s t2s. (encode_infer_ts t1s = encode_infer_ts t2s) ⇔ (t1s = t2s))`,
 metis_tac[encode_infer_t_inj])

Theorem t_unify_ind:
   !P0 P1.
      (!s t1 t2.
         (!ts1 ts2 tc2.
            t_walk s t1 = Infer_Tapp ts1 tc2 /\
            t_walk s t2 = Infer_Tapp ts2 tc2 ==>
            P1 s ts1 ts2) ==>
         P0 s t1 t2) /\
      (!s ts1 ts2.
         (!t1 ts1' t2 ts2' s'.
            (ts1 = t1::ts1' /\ ts2 = t2::ts2') /\
            t_unify s t1 t2 = SOME s' ==>
            P1 s' ts1' ts2') /\
         (!t1 ts1' t2 ts2'.
            ts1 = t1::ts1' /\ ts2 = t2::ts2' ==> P0 s t1 t2) ==>
         P1 s ts1 ts2) ==>
      (!s t1 t2. t_wfs s ==> P0 s t1 t2) /\
      (!s ts1 ts2. t_wfs s ==> P1 s ts1 ts2)
Proof
  rpt gen_tac >> strip_tac >>
  Q.ISPEC_THEN`λs t1 t2.
    (∀us u1 u2. wfs s ∧ (s = encode_infer_t o_f us) ∧ (t1 = encode_infer_t u1) ∧ (t2 = encode_infer_t u2) ⇒ P0 us u1 u2) ∧
    (∀us tag u1 u2.
       wfs s ∧ (s = encode_infer_t o_f us) ∧
       (t1 = Pair (Const (TC_tag tag)) (encode_infer_ts u1)) ∧
       (t2 = Pair (Const (TC_tag tag)) (encode_infer_ts u2))
         ⇒ P1 us u1 u2) ∧
    (∀us v1 u1 v2 u2.
       wfs s ∧ (s = encode_infer_t o_f us) ∧
       (t1 = Pair (encode_infer_t v1) (encode_infer_ts u1)) ∧
       (t2 = Pair (encode_infer_t v2) (encode_infer_ts u2))
         ⇒ P0 us v1 v2 ∧
          (∀usx. (unify s (encode_infer_t v1) (encode_infer_t v2) = SOME (encode_infer_t o_f usx))
                 ⇒ P1 usx u1 u2))`
  strip_assume_tac unify_ind >>
  qmatch_assum_abbrev_tac`P ⇒ Q` >> qunabbrev_tac`Q` >>
  `P` by (
    qpat_x_assum`P ⇒ Q`kall_tac >>
    qunabbrev_tac`P` >>
    CONV_TAC (DEPTH_CONV BETA_CONV) >>
    rpt gen_tac >>
    strip_tac >>
    conj_tac >- (
      rw[] >>
      first_x_assum match_mp_tac >>
      rw[] >>
      fs[encode_walk,t_wfs_def,encode_infer_t_def] ) >>
    conj_tac >- (
      rw[] >>
      first_x_assum match_mp_tac >>
      fs[] >>
      conj_tac >- (
        rw[] >>
        fs[encode_infer_t_def,encode_infer_t_inj_rwt] >>
        first_x_assum(qspec_then`us`kall_tac) >>
        first_x_assum(qspec_then`us`mp_tac) >>
        simp[] >> disch_then (qspec_then`s'`mp_tac o CONJUNCT2) >>
        simp[t_wfs_def,SIMP_RULE(srw_ss())[]encode_unify] ) >>
      rw[] >>
      fs[encode_infer_t_def,SIMP_RULE(srw_ss())[]encode_unify,t_wfs_def,encode_infer_t_inj_rwt] ) >>
    rw[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac wfs_unify >>
    fs[encode_infer_t_inj_rwt] >>
    conj_tac >- (
      rw[] >>
      fs[encode_infer_t_def,encode_infer_t_inj_rwt] >>
      first_x_assum(qspec_then`us`kall_tac) >>
      first_x_assum(qspec_then`us`kall_tac) >>
      first_x_assum(qspec_then`us`kall_tac) >>
      first_x_assum(qspec_then`usx`mp_tac) >>
      simp[t_wfs_def,SIMP_RULE(srw_ss())[]encode_unify] ) >>
    rw[] >>
    fs[encode_infer_t_def,encode_infer_t_inj_rwt] ) >>
  qmatch_assum_abbrev_tac`P ⇒ Q` >>
  `Q` by metis_tac[] >>
  qunabbrev_tac`P` >>
  qunabbrev_tac`Q` >>
  pop_assum mp_tac >>
  rpt (pop_assum kall_tac) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  strip_tac >>
  rw[] >- (
    first_x_assum(qspecl_then[`encode_infer_t o_f s`,`encode_infer_t t1`,`encode_infer_t t2`]mp_tac) >>
    strip_tac >>
    first_x_assum match_mp_tac >>
    fs[t_wfs_def] ) >>
  first_x_assum(qspecl_then[`encode_infer_t o_f s`
                           ,`Pair (Const (DB_tag 0)) (encode_infer_ts ts1)`
                           ,`Pair (Const (DB_tag 0)) (encode_infer_ts ts2)`]mp_tac) >>
  simp[encode_infer_t_inj_rwt] >> strip_tac >>
  first_x_assum(qspecl_then[`s`,`Infer_Tvar_db 0`,`Infer_Tvar_db 0`]mp_tac) >>
  simp[encode_infer_t_def] >>
  fs[t_wfs_def]
QED

val apply_subst_t_def = zDefine `
apply_subst_t s t = decode_infer_t (subst_APPLY (encode_infer_t o_f s) (encode_infer_t t))`;

Theorem apply_subst_t_eqn:
 (!s n.
  apply_subst_t s (Infer_Tuvar n) =
   dtcase FLOOKUP s n of
     | NONE => Infer_Tuvar n
     | SOME t => t) ∧
 (!s ts tc.
  apply_subst_t s (Infer_Tapp ts tc) =
    Infer_Tapp (MAP (apply_subst_t s) ts) tc) ∧
 (!s n.
  apply_subst_t s (Infer_Tvar_db n) =
    Infer_Tvar_db n)
Proof
rw [apply_subst_t_def, encode_infer_t_def, FLOOKUP_o_f,
    decode_infer_t_def] >>
every_case_tac >>
rw [decode_left_inverse, decode_infer_t_def] >>
induct_on `ts` >>
rw [apply_subst_t_def, encode_infer_t_def, decode_infer_t_def]
QED

val t_walkstar_def = zDefine `
t_walkstar s t =
  decode_infer_t (walkstar (encode_infer_t o_f s) (encode_infer_t t))`;

val ts_walkstar_thm = Q.prove (
`!l s.
  t_wfs s ⇒
  (decode_infer_ts ((encode_infer_t o_f s) ◁ encode_infer_ts l) =
   MAP (t_walkstar s) l)`,
induct_on `l` >>
rw [t_wfs_def, encode_infer_t_def, Once walkstar_def, decode_infer_t_def] >>
rw [t_walkstar_def]);

Theorem t_walkstar_eqn:
 !s. t_wfs s ⇒
  !t.
    t_walkstar s t =
    dtcase t_walk s t of
      | Infer_Tuvar v => Infer_Tuvar v
      | Infer_Tapp ts tctor => Infer_Tapp (MAP (t_walkstar s) ts) tctor
      | Infer_Tvar_db n => Infer_Tvar_db n
Proof
rw [t_walkstar_def] >>
`wfs (encode_infer_t o_f s)` by fs [t_wfs_def] >>
rw [Once walkstar_def, t_walk_def] >>
cases_on `t` >>
rw [encode_infer_t_def, decode_infer_t_def, decode_left_inverse, encode_vwalk] >|
[rw [ts_walkstar_thm],
 cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def, decode_infer_t_def, ts_walkstar_thm]]
QED

Theorem t_walkstar_ind:
 !s. t_wfs s ==>
     !P.
       (!t.
          (!ts tt a. (t_walk s t = Infer_Tapp ts tt) /\ MEM a ts ==> P a) ==>
          P t) ==>
       !t. P t
Proof
  rw[] >>
  `wfs (encode_infer_t o_f s)` by fs[t_wfs_def] >>
  imp_res_tac(GEN_ALL (DISCH_ALL walkstar_ind)) >>
  qsuff_tac
    `(λx. (∀u. (x = encode_infer_t u) ⇒ P u) ∧
          (∀tag us. (x = Pair (Const (TC_tag tag)) (encode_infer_ts us)) ⇒ EVERY P us) ∧
          (∀u us. (x = Pair (encode_infer_t u) (encode_infer_ts us)) ⇒ EVERY P (u::us)))
     (encode_infer_t t)` >- (
    simp[decode_left_inverse] >> PROVE_TAC[] ) >>
  pop_assum match_mp_tac >> simp[] >>
  rw[decode_left_inverse] >- (
    rfs[encode_walk] >>
    first_x_assum match_mp_tac >> rw[] >>
    fs[t_walk_eqn,encode_infer_t_def] >>
    fs[EVERY_MEM] >> PROVE_TAC[] ) >>
  rfs[encode_walk] >- (
    Cases_on`us`>>fs[encode_infer_t_def] >>
    metis_tac[] ) >>
  Cases_on`us`>>fs[encode_infer_t_def] >>
  metis_tac[]
QED

val t_collapse_def = zDefine `
t_collapse s =
  decode_infer_t o_f collapse (encode_infer_t o_f s)`;

Theorem t_collapse_eqn:
 !s. t_collapse s = FUN_FMAP (\v. t_walkstar s (Infer_Tuvar v)) (FDOM s)
Proof
rw [collapse_def, t_collapse_def, t_walkstar_def, encode_infer_t_def, walkstar_def] >>
rw [GSYM fmap_EQ_THM, FUN_FMAP_DEF]
QED

Theorem t_unify_unifier:
   t_wfs s ∧ (t_unify s t1 t2 = SOME sx) ⇒ t_wfs sx ∧ s ⊑ sx ∧ (t_walkstar sx t1 = t_walkstar sx t2)
Proof
  simp[t_unify_def] >> strip_tac >>
  qmatch_assum_abbrev_tac`unify us ut1 ut2 = SOME uz` >>
  qspecl_then[`us`,`ut1`,`ut2`,`s`,`t1`,`t2`]mp_tac encode_unify >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`w`strip_assume_tac) >>
  `wfs us` by metis_tac[t_wfs_def] >>
  imp_res_tac unify_unifier >>
  unabbrev_all_tac >>
  rw[decode_left_inverse,decode_left_inverse_I,I_o_f] >>
  simp[t_wfs_def,t_walkstar_def] >>
  fs[SUBMAP_DEF] >>
  metis_tac[encode_infer_t_inj,o_f_FAPPLY]
QED

val t_unify_strongind' = Q.prove(
`!P0 P1.
    (!s t1 t2.
       t_wfs s ∧
       (!ts1 ts2 tc2.
          t_walk s t1 = Infer_Tapp ts1 tc2 /\
          t_walk s t2 = Infer_Tapp ts2 tc2 ==>
          P1 s ts1 ts2) ==>
       P0 s t1 t2) /\
    (!s ts1 ts2.
       t_wfs s ∧
       (!t1 ts1' t2 ts2' s'.
          (ts1 = t1::ts1' /\ ts2 = t2::ts2') /\
          t_unify s t1 t2 = SOME s' ==>
          P1 s' ts1' ts2') /\
       (!t1 ts1' t2 ts2'.
          ts1 = t1::ts1' /\ ts2 = t2::ts2' ==> P0 s t1 t2) ==>
       P1 s ts1 ts2) ==>
    (!s t1 t2. t_wfs s ==> (t_wfs s ==> P0 s t1 t2)) /\
    (!s ts1 ts2. t_wfs s ==> (t_wfs s ⇒ P1 s ts1 ts2))`,
NTAC 3 STRIP_TAC >>
ho_match_mp_tac t_unify_ind >>
rw [] >>
cases_on `ts1` >>
cases_on `ts2` >>
fs [] >>
qpat_x_assum `!s ts1 ts2. Q s ts1 ts2 ⇒ P1 s ts1 ts2` match_mp_tac >>
rw [] >>
metis_tac [t_unify_unifier]);

val t_unify_strongind = save_thm("t_unify_strongind", SIMP_RULE (bool_ss) [] t_unify_strongind');

val encode_walkstar = Q.prove (
`!s t.
  t_wfs s ⇒
  walkstar (encode_infer_t o_f s) (encode_infer_t t) =
  encode_infer_t (t_walkstar s t)`,
rw [] >>
imp_res_tac t_walkstar_ind >>
Q.SPEC_TAC (`t`,`t`) >>
pop_assum ho_match_mp_tac >>
rw [] >>
rw [Once t_walkstar_eqn] >>
`wfs (encode_infer_t o_f s)` by fs [t_wfs_def] >>
rw [Once walkstar_def] >>
rw [Once encode_walk] >>
cases_on `t_walk s t` >>
rw [encode_infer_t_def] >>
pop_assum mp_tac >>
pop_assum (fn _ => all_tac) >>
induct_on `l` >>
rw [encode_infer_t_def] >>
rw [Once walkstar_def]);

Theorem t_walkstar_FEMPTY:
 !t.(t_walkstar FEMPTY t = t)
Proof
rw [t_walkstar_def, decode_left_inverse]
QED

Theorem t_wfs_SUBMAP:
 !s1 s2. t_wfs s2 ∧ s1 ⊑ s2 ⇒ t_wfs s1
Proof
rw [t_wfs_def] >>
`encode_infer_t o_f s1 SUBMAP encode_infer_t o_f s2`
         by (fs [SUBMAP_DEF]) >>
metis_tac [wfs_SUBMAP]
QED

Theorem t_walkstar_SUBMAP:
 !s1 s2 t. s1 SUBMAP s2 ∧ t_wfs s2 ⇒ (t_walkstar s2 t = t_walkstar s2 (t_walkstar s1 t))
Proof
rw [t_walkstar_def] >>
`wfs (encode_infer_t o_f s2)` by fs [t_wfs_def] >>
`t_wfs s1` by metis_tac [t_wfs_SUBMAP] >>
`encode_infer_t o_f s1 SUBMAP encode_infer_t o_f s2` by fs [SUBMAP_DEF] >>
`walkstar (encode_infer_t o_f s2) (encode_infer_t t) =
 walkstar (encode_infer_t o_f s2) (walkstar (encode_infer_t o_f s1) (encode_infer_t t))`
       by metis_tac [walkstar_SUBMAP] >>
rw [encode_walkstar, decode_left_inverse]
QED

val t_vR_def = Define `
t_vR s = vR (encode_infer_t o_f s)`;

Theorem t_vR_eqn:
 !s x y. t_vR s y x = dtcase FLOOKUP s x of SOME t => y IN t_vars t | _ => F
Proof
rw [t_vR_def, vR_def] >>
every_case_tac >>
fs [FLOOKUP_o_f, t_vars_def]
QED

Theorem t_wfs_eqn:
 !s. t_wfs s = WF (t_vR s)
Proof
rw [wfs_def, t_wfs_def, t_vR_eqn, WF_DEF, vR_def, FLOOKUP_o_f, t_vars_def] >>
eq_tac >>
rw [] >>
res_tac >>
cases_on `FLOOKUP s min` >>
fs [] >>
qexists_tac `min` >>
rw []
QED

val t_rangevars_def = Define `
t_rangevars s = rangevars (encode_infer_t o_f s)`;

Theorem t_rangevars_eqn:
 !s. t_rangevars s = BIGUNION (IMAGE t_vars (FRANGE s))
Proof
rw [t_rangevars_def, rangevars_def, EXTENSION] >>
EQ_TAC >>
rw [t_vars_def, FRANGE_DEF, o_f_FAPPLY] >>
metis_tac [o_f_FAPPLY]
QED

Theorem t_vars_eqn:
 (!x. t_vars (Infer_Tvar_db x) = {}) ∧
 (!ts tc. t_vars (Infer_Tapp ts tc) = BIGUNION (set (MAP t_vars ts))) ∧
 (!u. t_vars (Infer_Tuvar u) = {u})
Proof
rw [t_vars_def, encode_infer_t_def] >>
induct_on `ts` >>
rw [encode_infer_t_def, t_vars_def]
QED

Theorem t_vwalk_to_var:
 t_wfs s ==> !v u. (t_vwalk s v = Infer_Tuvar u) ==> u NOTIN FDOM s
Proof
rw [t_wfs_def, t_vwalk_def] >>
imp_res_tac vwalk_to_var >>
fs [] >>
pop_assum match_mp_tac >>
qexists_tac `v` >>
`encode_infer_t (decode_infer_t (vwalk (encode_infer_t o_f s) v)) = encode_infer_t (Infer_Tuvar u)`
               by metis_tac [] >>
fs [encode_infer_t_def] >>
`t_wfs s` by metis_tac [t_wfs_def] >>
fs [encode_vwalk, decode_left_inverse]
QED

Theorem t_walkstar_vars_notin:
 !s. t_wfs s ⇒
  !t x. x ∈ t_vars (t_walkstar s t) ⇒ x ∉ FDOM s
Proof
STRIP_TAC >>
STRIP_TAC >>
imp_res_tac t_walkstar_ind >>
pop_assum ho_match_mp_tac >>
STRIP_TAC >>
ASM_SIMP_TAC (srw_ss()) [t_walkstar_eqn] >>
cases_on `t_walk s t` >>
rw [] >|
[fs [t_vars_eqn],
 fs [MEM_MAP, t_vars_eqn] >>
     rw [] >>
     res_tac >>
     pop_assum mp_tac >>
     rw [GSYM t_walkstar_eqn],
 cases_on `t` >>
     fs [t_walk_eqn, t_vars_eqn] >>
     metis_tac [t_vwalk_to_var]]
QED

Theorem t_walkstar_vars_in:
 !s. t_wfs s ⇒ ∀t. t_vars (t_walkstar s t) SUBSET t_vars t UNION BIGUNION (FRANGE (t_vars o_f s))
Proof
rw [t_walkstar_def, t_vars_def, t_wfs_def] >>
imp_res_tac vars_walkstar >>
fs [SUBSET_DEF] >>
rw [] >>
`t_vars = vars o encode_infer_t`
        by metis_tac [FUN_EQ_THM, t_vars_def, combinTheory.o_DEF] >>
metis_tac [decode_right_inverse, decode_left_inverse, t_wfs_def,
           encode_walkstar]
QED

Theorem t_walkstar_idempotent:
   ∀s. t_wfs s ⇒ ∀t. t_walkstar s (t_walkstar s t) = t_walkstar s t
Proof
  metis_tac[decode_right_inverse, decode_left_inverse, walkstar_idempotent, t_wfs_def, encode_walkstar]
QED

(* ---------- Lemmas about unification that don't need to go into the encoding ----------*)

Theorem t_unify_apply:
 !s1 s2 t1 t2.
  t_wfs s1 ∧
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)
Proof
metis_tac [t_unify_unifier]
QED

Theorem t_unify_apply2:
 !s1 s2 t1' t2' t1 t2.
  t_wfs s1 ∧
  (t_unify s1 t1' t2' = SOME s2) ∧
  (t_walkstar s1 t1 = t_walkstar s1 t2)
  ⇒
  (t_walkstar s2 t1 = t_walkstar s2 t2)
Proof
rw [] >>
`t_wfs s2 ∧ s1 SUBMAP s2` by metis_tac [t_unify_unifier] >>
metis_tac [t_walkstar_SUBMAP]
QED

Theorem t_unify_wfs:
 !s1 t1 t2 s2.
  t_wfs s1 ∧
  (t_unify s1 t1 t2 = SOME s2)
  ⇒
  t_wfs s2
Proof
metis_tac [t_unify_unifier]
QED

Theorem finite_t_rangevars:
 !t. FINITE (t_rangevars t)
Proof
rw [t_rangevars_eqn, t_vars_def] >>
rw [termTheory.FINITE_vars]
QED

Theorem t_walkstar_eqn1:
 !s idx ts tc.
  t_wfs s ⇒
  (t_walkstar s (Infer_Tvar_db idx) = Infer_Tvar_db idx) ∧
  (t_walkstar s (Infer_Tapp ts tc) = Infer_Tapp (MAP (t_walkstar s) ts) tc)
Proof
rw [t_walkstar_eqn, t_walk_eqn]
QED

Theorem oc_tvar_db:
 !s uv tvs. t_wfs s ⇒ ~t_oc s (Infer_Tvar_db tvs) uv
Proof
rw [] >>
imp_res_tac t_oc_eqn >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum (ASSUME_TAC o Q.SPECL [`uv`, `Infer_Tvar_db tvs`]) >>
rw [t_walk_eqn]
QED

Theorem oc_unit:
 !s uv tc. t_wfs s ⇒ ~t_oc s (Infer_Tapp [] tc) uv
Proof
rw [] >>
imp_res_tac t_oc_eqn >>
pop_assum (fn _ => all_tac) >>
pop_assum (fn _ => all_tac) >>
pop_assum (ASSUME_TAC o Q.SPECL [`uv`, `Infer_Tapp [] tc'`]) >>
rw [t_walk_eqn]
QED

Theorem no_vars_lem:
 !e l f.
  MEM e l ∧ set (MAP f l) = {{}}
  ⇒
  (f e = {})
Proof
induct_on `l` >>
rw [] >>
fs [MEM_MAP, EXTENSION] >>
metis_tac []
QED

Theorem no_vars_extend_subst_vwalk:
 !s. t_wfs s ⇒
   !n s'. t_wfs (s |++ s') ∧
         DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) ∧
         (!n'. t_vwalk s n ≠ Infer_Tuvar n')
         ⇒
         t_vwalk (s |++ s') n = t_vwalk s n
Proof
 strip_tac >>
 strip_tac >>
 imp_res_tac (DISCH_ALL t_vwalk_ind) >>
 pop_assum ho_match_mp_tac >>
 rw [] >>
 pop_assum mp_tac >>
 imp_res_tac t_vwalk_eqn >>
 ONCE_ASM_REWRITE_TAC [] >>
 pop_assum (fn _ => all_tac) >>
 pop_assum (fn _ => all_tac) >>
 cases_on `FLOOKUP (s |++ s') n` >>
 rw [] >>
 cases_on `FLOOKUP s n` >>
 fs [t_vars_eqn]
 >- fs [DISJOINT_DEF, EXTENSION, flookup_thm, FLOOKUP_DEF, FDOM_FUPDATE_LIST]
 >- (fs [alistTheory.flookup_fupdate_list] >>
     Cases_on `ALOOKUP (REVERSE s') n` >>
     fs [alistTheory.ALOOKUP_FAILS]
     >- (every_case_tac >>
         fs []) >>
     imp_res_tac alistTheory.ALOOKUP_MEM >>
     fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION, FDOM_FUPDATE_LIST, MEM_MAP] >>
     metis_tac [FST, pair_CASES])
QED

Theorem no_vars_extend_subst:
 !s. t_wfs s ⇒
  !t s'. t_wfs (s |++ s') ∧
         DISJOINT (FDOM s) (FDOM (FEMPTY |++ s')) ∧
         (t_vars (t_walkstar s t) = {})
         ⇒
         t_walkstar (s |++ s') t = t_walkstar s t
Proof
strip_tac >>
strip_tac >>
imp_res_tac t_walkstar_ind >>
pop_assum ho_match_mp_tac >>
rw [] >>
cases_on `t` >>
rw [t_walkstar_eqn, t_walk_eqn] >>
fs [t_walk_eqn] >>
pop_assum mp_tac >>
rw [t_walkstar_eqn, t_walk_eqn, t_vars_eqn] >>
rw [MAP_EQ_f] >-
metis_tac [no_vars_lem, MAP_MAP_o, combinTheory.o_DEF] >>
cases_on `t_vwalk s n` >>
fs [] >>
rw [no_vars_extend_subst_vwalk] >>
rw [MAP_EQ_f] >>
fs [t_vars_eqn] >>
rw [] >>
fs [] >>
metis_tac [no_vars_lem, MAP_MAP_o, combinTheory.o_DEF]
QED

(*Theorems about unification for completeness proof*)

Theorem t_walk_vwalk_id:
 t_wfs s ⇒
  !n. t_walk s (t_vwalk s n) = t_vwalk s n
Proof
  strip_tac>>
  ho_match_mp_tac (Q.INST[`s`|->`s`]t_vwalk_ind)>>
  rw[]>>
  Cases_on`FLOOKUP s n`>>fs[t_walk_eqn,Once t_vwalk_eqn]>>
  simp[EQ_SYM_EQ]>>
  fs[Once t_vwalk_eqn]>>
  Cases_on`x`
  >-
    fs[t_walk_eqn,Once t_vwalk_eqn]
  >-
    fs[t_walk_eqn,Once t_vwalk_eqn]
  >>
    fs[]
QED

Theorem t_walk_walk_id:
 t_wfs s ⇒
  t_walk s (t_walk s h) = t_walk s h
Proof
  Cases_on`h`>>
  fs[t_walk_eqn,t_walk_vwalk_id]
QED

Theorem eqs_t_unify:
 t_wfs s ∧ t_wfs s2 ∧
  t_walkstar s2 (t_walkstar s t1) = t_walkstar s2 (t_walkstar s t2)
  ⇒
  ?sx. t_unify s t1 t2 = SOME sx
Proof
  rw[t_unify_def] >>
  match_mp_tac (GEN_ALL eqs_unify) >>
  qexists_tac`encode_infer_t o_f s2` >>
  conj_asm1_tac >- fs[t_wfs_def] >>
  conj_asm1_tac >- fs[t_wfs_def] >>
  simp[encode_walkstar]
QED

val encode_walkstar_reverse = encode_walkstar |>
                              REWRITE_RULE [t_walkstar_def] |>
                              SPEC_ALL|>UNDISCH|>SYM |>
                              DISCH_ALL |> GEN_ALL;

Theorem t_unify_mgu:
 !s t1 t2 sx s2.
  t_wfs s ∧ (t_unify s t1 t2 = SOME sx) ∧ t_wfs s2 ∧
  (t_walkstar s2 (t_walkstar s t1)) = t_walkstar s2 (t_walkstar s t2)
  ⇒
  ∀t. t_walkstar s2 (t_walkstar sx t) = t_walkstar s2 (t_walkstar s t)
Proof
  rw[]>>
  `t_wfs sx` by metis_tac[t_unify_wfs]>>
  rfs[t_walkstar_def,encode_walkstar_reverse]>>
  AP_TERM_TAC>>
  match_mp_tac unify_mgu>>
  Q.EXISTS_TAC`encode_infer_t t1`>>
  Q.EXISTS_TAC`encode_infer_t t2`>>
  conj_asm1_tac >- fs[t_wfs_def] >>
  CONJ_TAC>-
  (Q.ISPECL_THEN [`encode_infer_t o_f s`,`encode_infer_t t1`,
                 `encode_infer_t t2`,`s`,`t1`,`t2`]
                 mp_tac encode_unify>>
  impl_tac>>fs[])>>
  conj_asm1_tac>- fs[t_wfs_def]>>
  qpat_x_assum `decode_infer_t A = B` mp_tac>>
  fs[encode_walkstar,decode_left_inverse]
QED

Theorem t_walkstar_tuvar_props:
 t_wfs s
  ⇒
  (uv ∉ FDOM s ⇔  t_walkstar s (Infer_Tuvar uv) = Infer_Tuvar uv)
Proof
  rw[EQ_IMP_THM]
  >-
    (fs[t_walkstar_eqn,t_walk_eqn,Once t_vwalk_eqn]>>
    imp_res_tac flookup_thm>>fs[])
  >>
    imp_res_tac t_walkstar_vars_notin>>
    pop_assum (Q.SPECL_THEN [`uv`,`Infer_Tuvar uv`] mp_tac)>>
    fs[t_vars_eqn]
QED

(*t_compat theorems*)
val t_compat_def = Define`
  t_compat s s' ⇔
  t_wfs s ∧ t_wfs s' ∧
  !t. t_walkstar s' (t_walkstar s t) = t_walkstar s' t`

Theorem t_compat_refl:
 t_wfs s ⇒ t_compat s s
Proof
  rw[t_compat_def]>>fs[t_walkstar_SUBMAP]
QED

Theorem t_compat_trans:
 t_compat a b ∧ t_compat b c ⇒ t_compat a c
Proof
  rw[t_compat_def]>>metis_tac[]
QED

Theorem SUBMAP_t_compat:
 t_wfs s' ∧ s SUBMAP s' ⇒ t_compat s s'
Proof
  rw[t_compat_def]
  >-
    metis_tac[t_wfs_SUBMAP]>>
  fs[t_walkstar_SUBMAP]
QED

(*t_compat is preserved under certain types of unification
  Proof basically from HOL*)
Theorem t_compat_eqs_t_unify:
 !s t1 t2 sx.
    t_compat s sx ∧ (t_walkstar sx t1 = t_walkstar sx t2)
    ⇒
    ?si. (t_unify s t1 t2 = SOME si) ∧ t_compat si sx
Proof
  rw[t_compat_def]>>
  Q.ISPECL_THEN [`t2`,`t1`,`sx`,`s`] assume_tac (GEN_ALL eqs_t_unify)>>
  rfs[]>>
  CONJ_ASM1_TAC>-metis_tac[t_unify_wfs]>>
  rw[]>>
  Q.ISPECL_THEN [`s`,`t1`,`t2`,`sx'`,`sx`] assume_tac t_unify_mgu>>
  rfs[]
QED

val _ = export_theory ();

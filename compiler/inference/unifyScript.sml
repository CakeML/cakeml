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
open cpsTheory cpsLib

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

val _ = new_theory "unify";

val _ = monadsyntax.temp_enable_monadsyntax()
val _ = monadsyntax.temp_enable_monad "option"

val option_map_case = optionTheory.OPTION_MAP_CASE
val option_bind_thm = oneline optionTheory.OPTION_BIND_def

Theorem I_o_f[local,simp]: !m. I o_f m = m
Proof rw [GSYM fmap_EQ_THM]
QED

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

Theorem encode_infer_t_11[simp]:
  (∀it1 it2. encode_infer_t it1 = encode_infer_t it2 ⇔ it1 = it2) ∧
  (∀its1 its2. encode_infer_ts its1 = encode_infer_ts its2 ⇔ its1 = its2)
Proof
  ho_match_mp_tac (TypeBase.induction_of “:infer_t”) >>
  rw[encode_infer_t_def]
  >- (Cases_on ‘it2’ >> simp[encode_infer_t_def])
  >- (Cases_on ‘it2’ >> simp[encode_infer_t_def] >> metis_tac[])
  >- (Cases_on ‘it2’ >> simp[encode_infer_t_def]) >>
  Cases_on ‘its2’ >> simp[encode_infer_t_def]
QED

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

Theorem decode_left_inverse[simp]:
  (!t. decode_infer_t (encode_infer_t t) = t) ∧
  (!ts. decode_infer_ts (encode_infer_ts ts) = ts)
Proof
Induct >>
rw [encode_infer_t_def, decode_infer_t_def]
QED

Theorem decode_left_inverse_I[simp]:
  decode_infer_t o encode_infer_t = I
Proof
  rw [FUN_EQ_THM]
QED

Theorem encode_eq_var[simp]:
  (Var n = encode_infer_t i ⇔ i = Infer_Tuvar n) ∧
  (encode_infer_t i = Var n ⇔ i = Infer_Tuvar n)
Proof
  rw[EQ_IMP_THM, encode_infer_t_def] >>
  pop_assum (mp_tac o Q.AP_TERM ‘decode_infer_t’) >>
  simp[decode_infer_t_def]
QED

Theorem decode_right_inverse[local]:
  (!t. (?t'. t = encode_infer_t t') ⇒ (encode_infer_t (decode_infer_t t) = t)) ∧
  (!ts. (?ts'. ts = encode_infer_ts ts') ⇒ (encode_infer_ts (decode_infer_ts ts) = ts))
Proof
Induct  >>
rw [encode_infer_t_def, decode_infer_t_def] >>
rw []
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

Theorem surj_RKC[transfer_simp]:
  surj RKC
Proof
  simp[transferTheory.surj_def, RKC_def]
QED

Definition substR_def:
 substR fm sp ⇔ wfs fm ∧ wf sp /\ fm = encode_infer_t o_f sp2fm sp
End

Theorem substR_FDOM[transfer_rule]:
  (substR |==> (=)) FDOM domain
Proof
  simp[FUN_REL_def, substR_def]
QED

Theorem substR_FLOOKUP[transfer_rule]:
  (substR |==> (=) |==> OPTREL RKC) FLOOKUP (flip lookup)
Proof
  simp[FUN_REL_def, substR_def, FLOOKUP_o_f] >> rpt strip_tac >>
  rename [‘lookup n sp’]>> Cases_on ‘lookup n sp’ >> simp[RKC_def]
QED

Definition cwfs_def:
  cwfs s <=> swfs (map encode_infer_t s) /\ wf s
End

Theorem sp2fm_map:
  sp2fm (map f sp) = f o_f sp2fm sp
Proof
  simp[finite_mapTheory.FLOOKUP_EXT, fmspTheory.FLOOKUP_sp2fm, FUN_EQ_THM,
       lookup_map, finite_mapTheory.FLOOKUP_o_f] >>
  simp[optionTheory.OPTION_MAP_CASE, combinTheory.o_DEF]
QED

Theorem substR_RFORALL[transfer_rule]:
  ((substR |==> (==>)) |==> (==>)) (RES_FORALL wfs) (RES_FORALL cwfs)
Proof
  simp[FUN_REL_def, RES_FORALL_THM, IN_DEF, substR_def] >> rpt strip_tac >>
  gvs[cwfs_def, swfs_def, sp2fm_map]
QED

(*
Theorem RKC_FORALL[transfer_rule]:
  ((RKC |==> (==>)) |==> (==>)) $! $!
Proof
  irule transferTheory.ALL_surj_imp_imp >> simp[surj_RKC]
QED
*)

Theorem wfs_rule[transfer_rule]:
  (substR |==> (=)) wfs cwfs
Proof
  simp[cwfs_def, FUN_REL_def, swfs_def, RKC_def, fmspTheory.FMSP_def,
       substR_def, sp2fm_map]
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
  (substR |==> (=) |==> RKC) vwalk cvwalk
Proof
  simp[cvwalk_def, FUN_REL_def, RKC_def, substR_def] >>
  rpt strip_tac >> rename [‘svwalk (map encode_infer_t sp) n’] >>
  ‘∃it. svwalk (map encode_infer_t sp) n = encode_infer_t it’
    by (irule svwalk_result_encodable >> simp[swfs_def, sp2fm_map] >>
        metis_tac[encode_infer_t_def]) >>
  simp[] >> gvs[svwalk_def, sp2fm_map]
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
                             decode_option_CASE, decode_infer_t_CASE,
                             combinTheory.o_ABS_R]

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

Theorem substR_walk[transfer_rule]:
  (substR |==> RKC |==> RKC) walk cwalk
Proof
  simp[cwalk_def, FUN_REL_def, substR_def] >> rpt strip_tac >>
  rename [‘swalk (map encode_infer_t sp) (encode_infer_t it)’] >>
  ‘?it'. swalk (map encode_infer_t sp) (encode_infer_t it) = encode_infer_t it'’
    by (irule swalk_result_encodable >> simp[cwfs_def, swfs_def, sp2fm_map]) >>
  gs[RKC_def, swalk_def, sp2fm_map]
QED

val cwf = ASSUME “cwfs s” |> SRULE[cwfs_def] |> cj 2
val cwfs = ASSUME “cwfs s” |> SRULE[cwfs_def] |> cj 1
Theorem cwalk_thm =
        cwalk_def |> SPEC_ALL
                  |> SRULE [swalk_thm, term_CASE_encode,
                            decode_infer_t_CASE, combinTheory.o_ABS_L,
                            combinTheory.o_ABS_R, cwf]
                  |> SRULE[decode_infer_t_def, GSYM cvwalk_def]

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

Theorem substR_oc[transfer_rule]:
  (substR |==> RKC |==> (=) |==> (=)) oc coc
Proof
  simp[FUN_REL_def, RKC_def, substR_def, coc_def, soc_def, sp2fm_map]
QED

Theorem coc_thm =
        coc_def |> SPEC_ALL
                |> SRULE[Once soc_walking, cwf, cwfs,
                         UNDISCH swalk_elim, term_CASE_encode,
                         combinTheory.o_DEF]
                |> SRULE[soc_thm, cwf, UNDISCH soc_encode_ts]
                |> SRULE[GSYM coc_def]

Definition t_vars_def: t_vars t = vars (encode_infer_t t)
End

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
  simp[OPTION_MAP_COMPOSE, combinTheory.o_DEF]
QED

Theorem sunify_t_elim:
  cwfs s ⇒
  sunify (map encode_infer_t s) (encode_infer_t t1) (encode_infer_t t2) =
  OPTION_MAP (map encode_infer_t) (cunify s t1 t2)
Proof
  strip_tac >> simp[cunify_def, OPTION_MAP_COMPOSE] >>
  Cases_on ‘sunify (map encode_infer_t s) (encode_infer_t t1)
            (encode_infer_t t2)’ >> simp[] >>
  drule_at Any sunify_result_encodable>> simp[encode_t_vs_ts] >> impl_tac
  >- gvs[cwfs_def, swfs_def, sp2fm_map] >>
  simp[PULL_EXISTS, map_map_o]
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

Theorem substR_unify:
  (substR |==> RKC |==> RKC |==> OPTREL substR) unify cunify
Proof
  simp[FUN_REL_def, RKC_def, cunify_def,
       optionTheory.OPTION_MAP_COMPOSE, sp2fm_map, substR_def] >>
  rpt strip_tac >> qmatch_abbrev_tac ‘OPTREL substR X _’ >>
  Cases_on ‘X’ >> simp[] >> gs[substR_def, sp2fm_map]
  >- simp[sunify_def, sp2fm_map] >>
  rename [‘unify _ _ _ = SOME result’] >>
  ‘wfs result’ by metis_tac[unifPropsTheory.unify_unifier] >>
  rename [‘sunify (map encode_infer_t sp) (encode_infer_t t1)
           (encode_infer_t t2)’] >>
  ‘?sresult. sunify (map encode_infer_t sp) (encode_infer_t t1)
                    (encode_infer_t t2) = SOME sresult’
    by simp[sunify_def, sp2fm_map] >>
  ‘wf sresult’
    by (irule sunify_wf >> first_assum $ irule_at (Pat ‘sunify _ _ _ = _’) >>
        simp[swfs_def, sp2fm_map]) >>
  drule_at (Pos last) sunify_result_encodable >>
  simp[swfs_def, sp2fm_map, PULL_EXISTS] >> rw[] >>
  gvs[sunify_def, sp2fm_map] >>
  simp[substR_def, sp2fm_map] >>
  first_x_assum (mp_tac o Q.AP_TERM ‘sp2fm’) >>
  simp[sp2fm_map]
QED

Definition capply_subst_def[nocompute]:
  (capply_subst s (Infer_Tuvar n) = dtcase lookup n s of
                                      NONE => Infer_Tuvar n
                                    | SOME it => it) ∧
  (capply_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP(capply_subst s) ts) tc) ∧
  (capply_subst s (Infer_Tvar_db n) = Infer_Tvar_db n)
Termination
  WF_REL_TAC ‘measure (infer_t_size o SND)’
End

Theorem capply_subst_thm[simp,compute] = SRULE [SF ETA_ss] capply_subst_def

Theorem cunify_thm =
        cunify_def |> SPEC_ALL
                   |> SRULE [Once sunify_thm, cwf, cwfs,
                             UNDISCH swalk_elim, term_CASE_encode,
                             combinTheory.o_DEF]
                   |> SRULE[soc_thm, cwf, cwfs, GSYM coc_def,
                            option_map_itcase, combinTheory.o_ABS_R,
                            UNDISCH map_decode_encode,
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

Theorem cunify_preserves_cwfs:
  cwfs s0 ∧ cunify s0 t1 t2 = SOME s ⇒ cwfs s
Proof
  simp[cunify_def, cwfs_def, PULL_EXISTS] >> gen_tac >>
  rpt (disch_then strip_assume_tac) >> reverse conj_asm2_tac
  >- (drule_at (Pos last) sunify_wf >> simp[]) >>
  drule_all sunify_preserves_swfs >> strip_tac >>
  drule_at (Pos last) sunify_result_encodable >> simp[encode_t_vs_ts] >>
  rw[] >> simp[map_map_o]
QED

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

Definition cwalkstar_def:
  cwalkstar s it =
  decode_infer_t (walkstar (encode_infer_t o_f sp2fm s) (encode_infer_t it))
End

Theorem walkstar1[local] =
        UNDISCH walkstar_thm |> oneline
                             |> INST_TYPE [alpha |-> “:atom”]
                             |> Q.INST [‘s’ |-> ‘encode_infer_t o_f sp2fm ss’]
                             |> Q.INST [‘ss’ |-> ‘s’]
Theorem walkstar2[local] =
        UNDISCH walkstar_thm |> INST_TYPE [alpha |-> “:atom”]
                             |> Q.INST [‘s’ |-> ‘encode_infer_t o_f sp2fm ss’]
                             |> Q.INST [‘ss’ |-> ‘s’]

Theorem cvwalk_rwt:
  wf s ⇒ wfs (encode_infer_t o_f sp2fm s) ⇒
  vwalk (encode_infer_t o_f sp2fm s) v =
  encode_infer_t (cvwalk s v)
Proof
  simp[cvwalk_def] >> rpt strip_tac >>
  ‘∃y. svwalk (map encode_infer_t s) v = encode_infer_t y’
    by (irule svwalk_result_encodable >>
        simp[encode_eq_var, swfs_def, sp2fm_map]) >>
  simp[decode_left_inverse_I] >> gvs[svwalk_def, sp2fm_map]
QED

Theorem decode_infer_ts_walkstar:
  wfs (encode_infer_t o_f sp2fm s) ⇒
  decode_infer_ts (walkstar (encode_infer_t o_f sp2fm s) (encode_infer_ts l)) =
  MAP (cwalkstar s) l
Proof
  strip_tac >> Induct_on ‘l’ >> simp[encode_infer_t_def, walkstar2] >>
  simp[decode_infer_t_def] >>
  simp[cwalkstar_def, sp2fm_map]
QED

Theorem cwalkstar_thm =
        cwalkstar_def |> SPEC_ALL
                      |> SRULE [term_CASE_encode,
                                decode_infer_t_CASE, combinTheory.o_ABS_L,
                                combinTheory.o_ABS_R, cwf, decode_infer_t_def,
                                Once $ walkstar1, walkstar2]
                      |> SRULE [UNDISCH_ALL cvwalk_rwt,
                                term_CASE_encode, decode_infer_t_CASE,
                                combinTheory.o_DEF, decode_infer_t_def,
                                walkstar2, UNDISCH_ALL decode_infer_ts_walkstar]
                      |> PROVE_HYP cwf
                      |> PROVE_HYP (SRULE [swfs_def, sp2fm_map] cwfs)
                      |> DISCH_ALL

Theorem walkstar_def'[local] =
        MATCH_MP
        (GEN_ALL walkstar_def)
        (ASSUME “wfs (sp2fm (map encode_infer_t s) : atom subst$subst)”)
Theorem walkstar_thm'[local] =
        MATCH_MP
        (GEN_ALL walkstar_thm)
        (ASSUME “wfs (sp2fm (map encode_infer_t s) : atom subst$subst)”)
Theorem infer_t_CASE_RAND:
  f (infer_t_CASE it tvf taf tuf) =
  infer_t_CASE it (f o tvf) (λl n. f (taf l n)) (f o tuf)
Proof
  Cases_on ‘it’ >> simp[]
QED

Theorem cunify_unifier:
  cwfs s ∧ cunify s t1 t2 = SOME sx ⇒
  cwfs sx ∧ subspt s sx ∧ cwalkstar sx t1 = cwalkstar sx t2
Proof
  simp[cwfs_def, cwalkstar_def, cunify_def, unify_unifier,
       PULL_EXISTS, wf_map, sp2fm_map] >> rpt strip_tac >>
  gvs[]>> drule_at (Pos last) sunify_result_encodable >>
  simp[encode_t_vs_ts] >> rw[] >>
  drule_all_then strip_assume_tac sunify_preserves_swfs >>
  drule_at (Pos last) sunify_wf >> simp[] >> strip_tac >>
  simp[SRULE [cwfs_def] map_decode_encode] >>
  gvs[sunify_def, swfs_def] >>
  drule_all unify_unifier
  >- (simp[SUBMAP_FLOOKUP_EQN, FLOOKUP_o_f, AllCaseEqs(), PULL_EXISTS,
           subspt_lookup, lookup_map] >> rpt strip_tac >> first_assum drule >>
      ‘cwfs m’ by simp[cwfs_def, swfs_def] >>
      first_x_assum (mp_tac o Q.AP_TERM ‘map decode_infer_t’) >>
      simp[map_decode_encode, lookup_map] >> disch_then SUBST_ALL_TAC >>
      first_x_assum drule >> simp[]) >>
  rpt strip_tac >>
  rename [‘walkstar ((encode_infer_t o decode_infer_t) o_f z)’] >>
  ‘(encode_infer_t o decode_infer_t) o_f z = z’ suffices_by simp[] >>
  simp[FLOOKUP_EXT, FLOOKUP_o_f, FUN_EQ_THM] >> qx_gen_tac ‘n’ >>
  Cases_on ‘FLOOKUP z n’ >> simp[] >>
  qpat_x_assum ‘map encode_infer_t _ = fm2sp z’ mp_tac >>
  simp[spt_eq_thm, lookup_map] >>
  disch_then $ qspec_then ‘n’ (assume_tac o SYM) >> gvs[]
QED

fun tcallify_th fixedvs th =
  let val (l,r) = dest_eq (concl th)
      val (lf0, args0) = strip_comb l
      val args = op_set_diff aconv args0 fixedvs
      val lf = list_mk_comb(lf0, fixedvs)
      val atup = pairSyntax.list_mk_pair args
      val inty = type_of atup
      val body_t = tailrecLib.mk_sum_term lf inty r
  in
      pairSyntax.mk_pabs(atup, body_t)
  end

val cvwalk_code = tcallify_th [“s:infer_t num_map”] cvwalk_thm

Definition cvwalk_code_def:
  cvwalk_code s = ^cvwalk_code
End

Theorem sum_CASE_infer_CASE:
  sum_CASE (infer_t_CASE i vf af uf) lf rf =
  infer_t_CASE i (λv. sum_CASE (vf v) lf rf)
             (λl n. sum_CASE (af l n) lf rf)
             (λu. sum_CASE (uf u) lf rf)
Proof
  Cases_on ‘i’ >> simp[]
QED

Theorem cvwalk_preserves_precond:
  ∀x y.
  (λn. cwfs s) x ∧ cvwalk_code s x = INL y ⇒ (λn. cwfs s) y
Proof
  simp[cvwalk_code_def, AllCaseEqs(), FORALL_PROD]
QED

Definition cvwalkR_def:
  cvwalkR σ = λv v0. vR (encode_infer_t o_f sp2fm σ) v v0
End

Theorem cvwalk_ensures_decrease:
  ∀x y. (λn. cwfs s) x ∧ cvwalk_code s x = INL y ⇒ cvwalkR s y x
Proof
  simp[cwfs_def, swfs_def, wfs_def, cvwalk_code_def, AllCaseEqs(), FORALL_PROD,
       cvwalkR_def, sp2fm_map] >>
  simp[substTheory.vR_def, FLOOKUP_o_f, encode_infer_t_def]
QED

Theorem WF_cvwalkR:
  ∀x. (λn. cwfs s) x ⇒ WF (cvwalkR s)
Proof
  simp[FORALL_PROD, cwfs_def, swfs_def, cvwalkR_def, wfs_def, sp2fm_map,
       SF ETA_ss]
QED

Theorem cvwalk_tcallish:
  ∀x. (λn. cwfs s) x ⇒
      cvwalk s x = TAILCALL (cvwalk_code s) (cvwalk s) x
Proof
  simp[whileTheory.TAILCALL_def, cvwalk_code_def, sum_CASE_option_CASE,
       sum_CASE_infer_CASE, FORALL_PROD] >>
  simp[Once (DISCH_ALL cvwalk_thm), cwfs_def]
QED

Theorem cvwalk_cleaned:
  ∀x. (λn. cwfs s) x ⇒ cvwalk s x = TAILREC (cvwalk_code s) x
Proof
  match_mp_tac whileTheory.TAILREC_GUARD_ELIMINATION >>
  rpt conj_tac
  >- ACCEPT_TAC cvwalk_preserves_precond
  >- (rpt strip_tac >> qexists_tac ‘cvwalkR s’ >> conj_tac
      >- (irule $ iffLR WF_EQ_WFP >> irule WF_cvwalkR >> gs[]) >>
      rpt strip_tac >> gvs[] >>
      irule cvwalk_ensures_decrease >> simp[])
  >- ACCEPT_TAC cvwalk_tcallish
QED

Definition tcvwalk_def:
  tcvwalk s n = TAILREC (cvwalk_code s) n
End

Theorem cvwalk_eta[local]: (λn. cvwalk_code s n) = cvwalk_code s
Proof simp[FUN_EQ_THM]
QED

Theorem tcvwalk_thm =
        tcvwalk_def |> SRULE[Once whileTheory.TAILREC, cvwalk_code_def]
                    |> SRULE[sum_CASE_option_CASE, sum_CASE_infer_CASE]
                    |> SRULE[GSYM tcvwalk_def, cvwalk_eta,
                             GSYM (SRULE [FUN_EQ_THM] cvwalk_code_def)]

Theorem tcvwalk_correct =
   SRULE[FORALL_PROD, GSYM tcvwalk_def] cvwalk_cleaned

Definition tcwalk_def:
  tcwalk s it = dtcase it of
                  Infer_Tvar_db c => Infer_Tvar_db c
                | Infer_Tapp l n => Infer_Tapp l n
                | Infer_Tuvar v => tcvwalk s v
End

Theorem tcwalk_correct:
  ∀s it. cwfs s ⇒ cwalk s it = tcwalk s it
Proof
  rpt strip_tac >> simp[cwalk_thm, tcvwalk_correct, tcwalk_def]
QED

Definition cocl_def:
  (cocl s [] n ⇔ F) ∧
  (cocl s (i::is) n ⇔ coc s i n ∨ cocl s is n)
End

Theorem cocl_EXISTS:
  cocl s its n ⇔ EXISTS (λi. coc s i n) its
Proof
  Induct_on ‘its’ >> simp[cocl_def]
QED

Theorem coc_thm' = CONJ (SRULE[GSYM cocl_EXISTS] coc_thm) cocl_def

Definition kcoc_def:
  kcoc s it n k = cwc (coc s it n) k
End

Definition kcocl_def:
  kcocl s its n k = cwc (cocl s its n) k
End

Theorem contify_infer_case:
  contify k (infer_t_CASE it cf af uf) =
  contify (λit. dtcase it of Infer_Tvar_db c => contify k (cf c)
                          | Infer_Tapp l n => contify k (af l n)
                          | Infer_Tuvar v => contify k (uf v))
          it
Proof
  Cases_on ‘it’ >> simp[contify_def]
QED

Theorem kcoc_thm =
        kcoc_def |> SPEC_ALL
                 |> SRULE[GSYM contify_cwc, ASSUME “cwfs s”, coc_thm']
                 |> CONV_RULE
                      (TOP_DEPTH_CONV (contify_CONV [contify_infer_case]))
                 |> SRULE [cwcp “cwalk”, cwcp “cwalk s”, cwcp “$=”, cwcp “$= x”,
                           cwcp “cocl”, cwcp “cocl s”]
                 |> SRULE [GSYM kcocl_def]

Theorem cwc_OR:
  cwc (bool$\/ b) k = if b then k (K T) else k I
Proof
  rw[cwc_def] >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

Theorem kcocl_Ky:
  kcocl s t n (λx. y) = y
Proof
  simp[kcocl_def, cwc_def]
QED

Theorem kcocl_thm =
        kcocl_def |> SPEC_ALL
                  |> SRULE [GSYM contify_cwc, ASSUME “cwfs s”,
                            Once $ DefnBase.one_line_ify NONE cocl_def]
                  |> CONV_RULE
                       (TOP_DEPTH_CONV (contify_CONV [contify_infer_case]))
                  |> SRULE [cwcp “coc”, cwcp “coc s”, cwc_OR,
                            cwcp “cocl”, cwcp “cocl s”]
                  |> SRULE[GSYM kcoc_def, GSYM kcocl_def]
                  |> SRULE[cwc_def, SF ETA_ss, kcocl_Ky]

Type kcockont = “:infer_t list list”

Definition apply_kcockont_def:
  apply_kcockont s n [] b = b ∧
  apply_kcockont s n (ts :: rest) b =
  if b then apply_kcockont s n rest T
  else kcocl s ts n (apply_kcockont s n rest)
End

Theorem apply_kcockontT[simp]:
  apply_kcockont s n ts T = T
Proof
  Induct_on ‘ts’ >> simp[apply_kcockont_def]
QED

Definition dfkcoc_def:
  dfkcoc s t n k = kcoc s t n (apply_kcockont s n k)
End

Definition dfkcocl_def:
  dfkcocl s ts n k = kcocl s ts n (apply_kcockont s n k)
End

Theorem apply_kcockont_thm =
        REWRITE_RULE [GSYM dfkcocl_def, apply_kcockontT] apply_kcockont_def

Theorem dfkcoc_thm =
        dfkcoc_def |> SPEC_ALL
                   |> ONCE_REWRITE_RULE [kcoc_thm]
                   |> SRULE [GSYM apply_kcockont_thm, GSYM dfkcocl_def]

Theorem dfkcocl_thm =
        dfkcocl_def |> SPEC_ALL
                    |> ONCE_REWRITE_RULE [kcocl_thm]
                    |> SRULE [GSYM apply_kcockont_thm, GSYM dfkcocl_def]
                    |> SRULE [SF ETA_ss, GSYM dfkcoc_def]

Theorem apply_kcockont_HDNIL:
  apply_kcockont s n ([] :: k) = apply_kcockont s n k
Proof
  simp[FUN_EQ_THM, apply_kcockont_thm, Once kcocl_thm, dfkcocl_thm] >>
  Cases >> simp[]
QED

Theorem dfkcocl_HDNIL:
  dfkcocl s ts n ([] :: k) = dfkcocl s ts n k
Proof
  simp[dfkcocl_def, apply_kcockont_HDNIL]
QED

Theorem dfkcocl_removed:
  dfkcocl s ts n k = apply_kcockont s n (ts :: k) F
Proof
  simp[apply_kcockont_thm] >> simp[dfkcocl_thm] >>
  simp[dfkcoc_def, apply_kcockont_HDNIL]
QED

val remove = CONV_RULE (RAND_CONV (REWRITE_CONV[dfkcocl_removed]))
Theorem dfkcocl_nonrecursive0 = remove dfkcocl_thm

Theorem dfkcocl_nonrecursive =
        dfkcocl_nonrecursive0
          |> SRULE[apply_kcockont_thm]
          |> CONV_RULE (RAND_CONV (SCONV [dfkcocl_thm]))
          |> SRULE[dfkcoc_thm, apply_kcockont_HDNIL, dfkcocl_HDNIL]
          |> CONV_RULE (RAND_CONV (SCONV [dfkcocl_removed]))

Overload kcocwl0 = “apply_kcockont”

Theorem kcocwl0_thm =
        apply_kcockont_thm
          |> CONJUNCTS
          |> map (GEN_ALL o PURE_REWRITE_RULE[dfkcocl_nonrecursive] o SPEC_ALL)
          |> LIST_CONJ

Definition kcocwl_def: kcocwl s n ts = kcocwl0 s n ts F
End

Theorem kcocwl0_varcheck: kcocwl0 s n ts b = if b then T else kcocwl s n ts
Proof
  rw[kcocwl_def] >> Cases_on ‘b’ >> simp[]
QED

Theorem kcocwl_thm =
        kcocwl0_thm |> SRULE [GSYM kcocwl_def]
                    |> SRULE [kcocwl0_varcheck]
                    |> SRULE [FORALL_BOOL, UNDISCH (SPEC_ALL tcwalk_correct)]
                    |> PURE_REWRITE_RULE[DECIDE “¬p = (p = F)”,
                                         DECIDE “p ∨ q ⇔ if p then T else q”]

val kcocwl_code =
tcallify_th [“s:infer_t num_map”, “n:num”]
            (DefnBase.one_line_ify NONE
                     (kcocwl_thm |> CONJUNCTS
                                 |> map SPEC_ALL
                                 |> LIST_CONJ
                                 |> Q.INST [‘s'’ |-> ‘s’]))

Definition kcocwl_code_def:
  kcocwl_code s n = ^kcocwl_code
End

Theorem kcocwl_preserves_precond:
  ∀x y. (λts. cwfs s) x ∧ kcocwl_code s n x = INL y ⇒
        (λts. cwfs s) y
Proof
  simp[]
QED

Definition kcocwlR_def:
  kcocwlR (s : infer_t num_map) (n:num) =
  inv_image (mlt1 (walkstarR (sp2fm (map encode_infer_t s))) LEX $<)
            (λts:infer_t list list.
               (BAG_OF_LIST (MAP encode_infer_t $ FLAT ts), LENGTH ts))
End

Theorem WF_kcocwlR:
  cwfs s ⇒ WF (kcocwlR s n)
Proof
  strip_tac >> gs[kcocwlR_def, cwfs_def] >>
  irule WF_inv_image >>
  irule pairTheory.WF_LEX >>
  simp[] >> irule bagTheory.WF_mlt1 >>
  irule walkstar_thWF >> gs[swfs_def]
QED

Theorem FINITE_BAG_FOLDR_INSERT[simp]:
  FINITE_BAG (FOLDR BAG_INSERT b xs) = FINITE_BAG b
Proof
  Induct_on ‘xs’ >> simp[]
QED

Theorem FOLDR_BAG_INSERT_UNION:
  FOLDR BAG_INSERT b xs = BAG_UNION b (BAG_OF_LIST xs)
Proof
  Induct_on ‘xs’ >> simp[BAG_UNION_INSERT]
QED

Theorem BAG_IN_BAG_OF_LIST:
  BAG_IN e (BAG_OF_LIST xs) = MEM e xs
Proof
  Induct_on ‘xs’ >> simp[]
QED

Theorem sum_CASE_list_CASE:
  sum_CASE (list_CASE l n cf) lf rf =
  list_CASE l (sum_CASE n lf rf) (λh t. sum_CASE (cf h t) lf rf)
Proof
  Cases_on ‘l’ >> simp[]
QED

Theorem walkstarR_trans:
  walkstarR s t1 t2 ∧ walkstarR s t2 t3 ⇒ walkstarR s t1 t3
Proof
  simp[walkstarR_def, LEX_DEF] >> rw[] >> gvs[] >>
  metis_tac [TC_TRANSITIVE, transitive_def]
QED

Definition subterm_def:
  subterm = TC (λa b. (∃t. b = Pair a t) ∨ (∃t. b = Pair t a))
End

Theorem subterm_thm[simp]:
  (subterm t (Pair u v) ⇔ t = u ∨ t = v ∨ subterm t u ∨ subterm t v) ∧
  (subterm t (Var vnm) ⇔ F) ∧
  (subterm t (Const c) ⇔ F)
Proof
  simp[subterm_def] >> rpt strip_tac >>~-
  ([‘F’], pop_assum mp_tac >> Induct_on ‘TC’ >> simp[PULL_EXISTS]) >>
  iff_tac >> rw[]
  >- (pop_assum mp_tac >>
      rename [‘TC _ t (Pair u v) ⇒ _’] >>
      map_every qid_spec_tac [‘t’,‘u’, ‘v’] >>
      Induct_on ‘TC’ using TC_STRONG_INDUCT_RIGHT1 >>
      rw[] >> simp[])
  >- (irule TC_SUBSET >> simp[])
  >- (irule TC_SUBSET >> simp[])
  >- (irule $ cj 2 TC_RULES >> first_assum $ irule_at Any >>
      irule TC_SUBSET >> simp[])
  >- (irule $ cj 2 TC_RULES >> first_assum $ irule_at Any >>
      irule TC_SUBSET >> simp[])
QED

Theorem subterm_pair_count:
  ∀t u. subterm t u ⇒ pair_count t < pair_count u
Proof
  simp[subterm_def] >> Induct_on ‘TC’ >> rw[] >> simp[termTheory.pair_count_def]
QED

Theorem subterm_REFL[simp]:
  ~subterm t t
Proof
  strip_tac >> drule subterm_pair_count >> simp[]
QED

Theorem subterm_TRANS:
  subterm t u ∧ subterm u v ⇒ subterm t v
Proof
  metis_tac[TC_TRANSITIVE, transitive_def, subterm_def]
QED

Theorem subterm_walkstarR:
  ∀t u. subterm t u ⇒ walkstarR s t u
Proof
  simp[subterm_def] >> Induct_on ‘TC’ >> rw[] >>~-
  ([‘walkstarR s t (Pair _ _)’],
   simp[walkstarR_def, LEX_DEF] >>
   rename [‘varb u = {||}’] >> Cases_on ‘varb u = {||}’ >> simp[] >>
   (irule bagTheory.TC_mlt1_UNION2_I ORELSE
    irule bagTheory.TC_mlt1_UNION1_I) >> simp[]) >>
  metis_tac[walkstarR_trans]
QED

Theorem MEM_subterm_encode:
  ∀i is. MEM i is ⇒ subterm (encode_infer_t i) (encode_infer_ts is)
Proof
  Induct_on ‘is’ >> simp[encode_infer_t_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem walkstar_opth:
  cwfs s ∧ tcwalk s i = Infer_Tapp is nm ∧ MEM i0 is ⇒
  walkstarR (sp2fm (map encode_infer_t s))
            (encode_infer_t i0)
            (encode_infer_t i)
Proof
  simp[GSYM tcwalk_correct, SF CONJ_ss] >> rpt strip_tac >>
  qpat_x_assum ‘cwalk _ _ = _’ (assume_tac o Q.AP_TERM ‘encode_infer_t’) >>
  gs[GSYM swalk_elim, encode_infer_t_def, Excl "encode_infer_t_11"] >>
  gs[swalk_def, cwfs_def, swfs_def] >>
  drule_all_then assume_tac walkstar_th2 >>
  irule walkstarR_trans >> first_assum $ irule_at Any >>
  irule subterm_walkstarR >> simp[MEM_subterm_encode]
QED

Theorem kcocwl_ensures_decrease:
  ∀x y. (λv. cwfs s) x ∧ kcocwl_code s n x = INL y ⇒
        kcocwlR s n y x
Proof
  simp[FORALL_PROD,kcocwl_code_def,AllCaseEqs()] >> rw[] >~
  [‘tcwalk s i = Infer_Tvar_db _’]
  >- simp[kcocwlR_def, pairTheory.LEX_DEF, tcallUnifTheory.mlt1_BAG_INSERT] >~
  [‘tcwalk s i = Infer_Tuvar v’]
  >- simp[kcocwlR_def, pairTheory.LEX_DEF, tcallUnifTheory.mlt1_BAG_INSERT] >~
  [‘kcocwlR s n _ ([] :: _)’]
  >- (simp[kcocwlR_def, pairTheory.LEX_DEF]) >~
  [‘tcwalk s i = Infer_Tapp is nm’, ‘(i::t) :: rest’]
  >- (simp[kcocwlR_def, pairTheory.LEX_DEF, rich_listTheory.FOLDR_APPEND] >>
      simp[mlt1_def] >>
      qexistsl [‘encode_infer_t i’,
                ‘BAG_OF_LIST $ MAP encode_infer_t is’,
                ‘BAG_UNION
                 (BAG_OF_LIST $ MAP encode_infer_t (FLAT rest))
                 (BAG_OF_LIST (MAP encode_infer_t t))’] >>
      simp[] >> ONCE_REWRITE_TAC[FOLDR_BAG_INSERT_UNION] >> simp[] >>
      simp[Once FOLDR_BAG_INSERT_UNION] >>
      simp[AC COMM_BAG_UNION ASSOC_BAG_UNION] >>
      simp[BAG_UNION_INSERT] >>
      simp[BAG_IN_BAG_OF_LIST, MEM_MAP, PULL_EXISTS] >>
      qx_gen_tac ‘i0’ >> strip_tac >> simp[walkstar_opth])
QED

Theorem kcocwl_tcallish:
  ∀x. (λv. cwfs s) x ⇒
      kcocwl s n x = TAILCALL (kcocwl_code s n) (kcocwl s n) x
Proof
  simp[FORALL_PROD, whileTheory.TAILCALL_def, kcocwl_code_def,
       sum_CASE_list_CASE, sum_CASE_infer_CASE, sum_CASE_COND] >>
  rpt strip_tac >> rename [‘kcocwl s n wl ⇔ _’] >>
  Cases_on ‘wl’ >> simp[Once kcocwl_thm, SimpLHS] >>
  simp[]
QED

Theorem kcocwl_cleaned:
  ∀x. (λv. cwfs s) x ⇒ kcocwl s n x = TAILREC (kcocwl_code s n) x
Proof
  match_mp_tac whileTheory.TAILREC_GUARD_ELIMINATION >> rpt conj_tac
  >- ACCEPT_TAC kcocwl_preserves_precond
  >- (qx_gen_tac ‘wl’ >> strip_tac >>
      qexists ‘kcocwlR s n’ >> conj_tac
      >- (irule $ iffLR WF_EQ_WFP >> gvs[WF_kcocwlR]) >>
      rpt strip_tac >> rename [‘kcocwlR s n wl2 wl1’] >>
      irule kcocwl_ensures_decrease >> simp[])
  >- ACCEPT_TAC kcocwl_tcallish
QED

Definition tcocwl_def:
  tcocwl s n is = TAILREC (kcocwl_code s n) is
End

Theorem tcocwl_correct0 =
        kcocwl_cleaned |> SRULE[FORALL_PROD, GSYM tcocwl_def]
Theorem tcocwl_correct:
  cwfs s ⇒ cocl s ts n = tcocwl s n [ts]
Proof
  simp[GSYM tcocwl_correct0, kcocwl_def, GSYM dfkcocl_removed,
       dfkcocl_def, kcocl_def, cwc_def, apply_kcockont_def]
QED
Theorem disj2cond[local] = DECIDE “p ∨ q ⇔ if p then T else q”

Theorem tcocwl_thm =
        tcocwl_def
          |> SRULE[Once whileTheory.TAILREC, sum_CASE_list_CASE,
                   sum_CASE_infer_CASE, sum_CASE_COND, kcocwl_code_def]
          |> SRULE [GSYM tcocwl_def, GSYM kcocwl_code_def]
          |> PURE_REWRITE_RULE [disj2cond]

(* ----------------------------------------------------------------------
    tail-recursification of cwalkstar
   ---------------------------------------------------------------------- *)

Definition cwalkstarl_def[simp]:
  cwalkstarl s [] = [] ∧
  cwalkstarl s (it::its) = cwalkstar s it :: cwalkstarl s its
End

Theorem MAP_cwalkstar:
  MAP (cwalkstar s) l = cwalkstarl s l
Proof
  Induct_on ‘l’ >> simp[]
QED

Definition kcwalkstar_def:
  kcwalkstar s it k = cwc (cwalkstar s it) k
End

Definition kcwalkstarl_def:
  kcwalkstarl s its k = cwc (cwalkstarl s its) k
End

Theorem cwalkstar_thm' =
        CONJ (UNDISCH_ALL $
                   SRULE[MAP_cwalkstar,
                         tcvwalk_correct |> SPEC_ALL |> UNDISCH_ALL]
                   cwalkstar_thm)
             (cwalkstarl_def)

Theorem kcwalkstar_thm =
        kcwalkstar_def
          |> SPEC_ALL
          |> SRULE[GSYM contify_cwc, ASSUME “cwfs s”, cwalkstar_thm']
          |> CONV_RULE
             (TOP_DEPTH_CONV (contify_CONV [contify_infer_case]))
          |> SRULE [cwcp “tcvwalk”, cwcp “tcvwalk s”, cwcp “$=”, cwcp “$= x”,
                    cwcp “Infer_Tvar_db”, cwcp “Infer_Tapp”,
                    cwcp “Infer_Tapp l”, cwcp “Infer_Tuvar”, cwcp “cwalkstarl”]
          |> SRULE [GSYM kcwalkstarl_def]

Theorem kcwalkstarl_thm0 =
        kcwalkstarl_def
          |> SPEC_ALL
          |> SRULE [GSYM contify_cwc, ASSUME “cwfs s”,
                    Once $ oneline cwalkstarl_def]
          |> CONV_RULE
             (TOP_DEPTH_CONV (contify_CONV [contify_infer_case]))
          |> SRULE [cwcp “cwalkstar”, cwcp “cwalkstarl”,
                    cwcp “CONS”, cwcp “CONS x”]
          |> SRULE[GSYM kcwalkstar_def, GSYM kcwalkstarl_def]

Theorem kcwalkstarl_thm =
        SRULE [kcwalkstar_thm] kcwalkstarl_thm0

Datatype:
  kclkont = DBk num | APPk (infer_t list) num | UVk num
          | CONSk (infer_t list) num
End

Definition apply_kclkont_def:
  apply_kclkont s [] its = its ∧
  apply_kclkont s (DBk n::k) its = apply_kclkont s k (Infer_Tvar_db n :: its) ∧
  apply_kclkont s (APPk aits n :: k) its =
    apply_kclkont s k (Infer_Tapp aits n :: its) ∧
  apply_kclkont s (UVk n::k) its = apply_kclkont s k (Infer_Tuvar n :: its) ∧
  apply_kclkont s (CONSk cits n :: k) its =
  kcwalkstarl s cits (λxk'. apply_kclkont s k (Infer_Tapp its n::xk'))
End

Definition dfkcwalkstarl_def:
  dfkcwalkstarl s t k = kcwalkstarl s t (apply_kclkont s k)
End

Theorem apply_kclkont5 = SRULE [GSYM $ cj 3 apply_kclkont_def, SF ETA_ss]
                               (cj 5 apply_kclkont_def)

Theorem apply_kclkont_thm =
        apply_kclkont_def |> (#1 o front_last o CONJUNCTS)
                          |> (fn cs => cs @ [apply_kclkont5])
                          |> LIST_CONJ
                          |> REWRITE_RULE [GSYM dfkcwalkstarl_def]
                          |> SRULE [SF ETA_ss]

Theorem dfkcwalkstarl_thm =
        dfkcwalkstarl_def |> SPEC_ALL
                          |> ONCE_REWRITE_RULE [kcwalkstarl_thm]
                          |> SRULE[GSYM apply_kclkont_thm, SF ETA_ss,
                                   GSYM apply_kclkont5]
                          |> SRULE [GSYM dfkcwalkstarl_def]

Definition kcwalkstarwl_def:
  kcwalkstarwl s T t k = apply_kclkont s k t ∧
  kcwalkstarwl s F t k = dfkcwalkstarl s t k
End

Theorem kcwalkstarwl_thm =
        oneline kcwalkstarwl_def
          |> ONCE_REWRITE_RULE [Once $ oneline apply_kclkont_thm,
                                Once dfkcwalkstarl_thm]
          |> SRULE[GSYM kcwalkstarwl_def]

Theorem dfkcwalkstarl_removed = GSYM $ cj 2 kcwalkstarwl_def
Theorem apply_kclkont_ID[simp]:
  apply_kclkont s [] = I
Proof
  simp[apply_kclkont_def, FUN_EQ_THM]
QED

Theorem cwalkstar_to_dfkcwalkstarl:
  cwalkstar s t = HD (dfkcwalkstarl s [t] [])
Proof
  simp[dfkcwalkstarl_def, apply_kclkont_def] >>
  simp[kcwalkstarl_def, cwc_def]
QED

(* kcwalkstarwl_thm is the target for tailcallification *)

Definition star_kwork_def[simp]:
  star_kwork [] = EMPTY_BAG ∧
  star_kwork (CONSk its n :: ks) = BAG_UNION (BAG_OF_LIST its) (star_kwork ks) ∧
  star_kwork (_ :: ks) = star_kwork ks
End

Definition star_workbag_def:
  star_workbag v its k =
  if v then star_kwork k
  else BAG_UNION (BAG_OF_LIST its) (star_kwork k)
End

Theorem FINITE_star_kwork[simp]:
  FINITE_BAG (star_kwork ks)
Proof
  Induct_on ‘ks’ >> simp[] >> Cases_on ‘h’ >> simp[]
QED

Theorem FINITE_star_workbag[simp]:
  FINITE_BAG (star_workbag v its k)
Proof
  rw[star_workbag_def]
QED

Definition isCONSk_def[simp]:
  isCONSk (CONSk _ _) = T ∧
  isCONSk _ = F
End

Definition kcwalkstarwlR_def:
  kcwalkstarwlR s =
  inv_image (mlt (inv_image
                   (walkstarR (encode_infer_t o_f sp2fm s))
                   encode_infer_t) LEX
             $< LEX
             measure (LENGTH o FILTER isCONSk) LEX
             measure (λb. if b then 0 else 1))
            (λ(v,its,k). (star_workbag v its k, LENGTH k, k, v))
End

Theorem WF_kcwalkstarwlR:
  cwfs s ⇒ WF (kcwalkstarwlR s)
Proof
  rw[kcwalkstarwlR_def] >> irule WF_inv_image >>
  rpt $ irule_at Any WF_LEX >> simp[WF_TC_EQN] >>
  irule WF_mlt1 >> irule WF_inv_image >>
  gs[cwfs_def, swfs_def, walkstar_thWF, sp2fm_map]
QED

val kcwalkstarwl_code = tcallify_th [“s:infer_t num_map”] $ kcwalkstarwl_thm
Definition kcwalkstarwl_code_def:
  kcwalkstarwl_code s = ^kcwalkstarwl_code
End

Theorem kcwalkstarwl_preserves_precond:
  ∀x y. (λ(v,t,k). cwfs s) x ∧ kcwalkstarwl_code s x = INL y ⇒
        (λ(v,t,k). cwfs s) y
Proof
  simp[FORALL_PROD]
QED

Theorem kcwalkstarwl_ensures_decrease:
  ∀x y. (λ(v,its,k). cwfs s) x ∧ kcwalkstarwl_code s x = INL y ⇒
        kcwalkstarwlR s y x
Proof
  simp[FORALL_PROD] >> rw[kcwalkstarwl_code_def, AllCaseEqs()] >>
  simp[kcwalkstarwlR_def] >~
  [‘star_workbag T []’]
  >- simp[LEX_DEF, star_workbag_def] >>~-
  ([‘star_workbag T (_ :: its) k’],
   simp[Once LEX_DEF] >> disj2_tac >> simp[star_workbag_def] >>
   simp[Once LEX_DEF]) >~
  [‘tcvwalk s v = Infer_Tapp args n’, ‘star_workbag F (Infer_Tuvar v :: its) k’]
  >- (simp[Once LEX_DEF] >> disj1_tac >>
      simp[star_workbag_def, BAG_UNION_INSERT] >>
      irule TC_SUBSET >> simp[mlt1_def] >>
      qexistsl [‘Infer_Tuvar v’, ‘BAG_OF_LIST args’,
                ‘BAG_OF_LIST its ⊎ star_kwork k’] >>
      simp[BAG_UNION_INSERT, BAG_IN_BAG_OF_LIST] >> rpt strip_tac >>
      irule (SRULE [sp2fm_map] walkstar_opth) >>
      simp[tcwalk_def]) >>~-
  ([‘tcvwalk s v = _’],
   simp[Once LEX_DEF] >> disj1_tac >> irule TC_SUBSET >>
   simp[star_workbag_def, BAG_UNION_INSERT, mlt1_BAG_INSERT]) >~
  [‘star_workbag F (Infer_Tvar_db n :: _)’]
  >- (simp[Once LEX_DEF] >> disj1_tac >>
      irule TC_SUBSET >>
      simp[BAG_UNION_INSERT, mlt1_BAG_INSERT, star_workbag_def]) >~
  [‘star_workbag F (Infer_Tapp args n :: rest) ks’]
  >- (simp[Once LEX_DEF] >> disj1_tac >>
      irule TC_SUBSET >> simp[star_workbag_def, BAG_UNION_INSERT] >>
      simp[mlt1_def] >>
      qexistsl [‘Infer_Tapp args n’, ‘BAG_OF_LIST args’,
                ‘BAG_OF_LIST rest ⊎ star_kwork ks’] >>
      simp[BAG_UNION_INSERT, BAG_IN_BAG_OF_LIST, encode_infer_t_def] >>
      rpt strip_tac >> irule subterm_walkstarR >>
      simp[MEM_subterm_encode]) >>
  rename [‘star_workbag T results (CONSk args m :: ks)’] >>
  simp[Once LEX_DEF] >> disj2_tac >> simp[star_workbag_def] >>
  simp[LEX_DEF]
QED

Theorem sum_CASE_wstarcont_CASE:
  sum_CASE (kclkont_CASE k dbf appf uvf consf) lf rf =
  kclkont_CASE k
               (λn. sum_CASE (dbf n) lf rf)
               (λits n. sum_CASE (appf its n) lf rf)
               (λn. sum_CASE (uvf n) lf rf)
               (λits n. sum_CASE (consf its n) lf rf)
Proof
  Cases_on ‘k’ >> simp[]
QED

Theorem kcwalkstarwl_tcallish:
  ∀x. (λ(v,its,k). cwfs s) x ⇒
      (λ(v,its,k). kcwalkstarwl s v its k) x =
      TAILCALL (kcwalkstarwl_code s) (λ(v,its,k). kcwalkstarwl s v its k) x
Proof
  simp[whileTheory.TAILCALL_def, kcwalkstarwl_code_def, FORALL_PROD,
       sum_CASE_COND, sum_CASE_list_CASE, sum_CASE_infer_CASE,
       sum_CASE_wstarcont_CASE] >>
  simp[Once $ DISCH_ALL kcwalkstarwl_thm]
QED

Theorem kcwalkstarwl_cleaned:
  ∀x. (λ(v,its,k). cwfs s) x ⇒
      (λ(v,its,k). kcwalkstarwl s v its k) x = TAILREC (kcwalkstarwl_code s) x
Proof
  match_mp_tac whileTheory.TAILREC_GUARD_ELIMINATION >> rpt conj_tac
  >- ACCEPT_TAC kcwalkstarwl_preserves_precond
  >- (qx_gen_tac ‘trip’ >> strip_tac >>
      qexists ‘kcwalkstarwlR s’ >> conj_tac
      >- (irule $ iffLR WF_EQ_WFP >> PairCases_on ‘trip’ >>
          gvs[WF_kcwalkstarwlR]) >>
      metis_tac [kcwalkstarwl_ensures_decrease])
  >- ACCEPT_TAC kcwalkstarwl_tcallish
QED

Definition tcwalkstarwl_def:
  tcwalkstarwl s v its k = TAILREC (kcwalkstarwl_code s) (v,its,k)
End

Definition tcwalkstar_p1_def:
  tcwalkstar_p1 s its k = tcwalkstarwl s F its k
End

Definition tcwalkstar_p2_def:
  tcwalkstar_p2 s its k = tcwalkstarwl s T its k
End

Theorem tcwalkstarwl_thm =
        tcwalkstarwl_def
          |> SRULE[Once whileTheory.TAILREC]
          |> SRULE[kcwalkstarwl_code_def, sum_CASE_COND,
                   sum_CASE_wstarcont_CASE,
                   sum_CASE_list_CASE, sum_CASE_infer_CASE]
          |> SRULE [GSYM kcwalkstarwl_code_def, GSYM tcwalkstarwl_def]
          |> SPEC_ALL
          |> (fn th => (GEN_ALL $ Q.INST [‘v’ |-> ‘T’] th,
                        GEN_ALL $ Q.INST [‘v’ |-> ‘F’] th))
          |> uncurry CONJ
          |> SRULE[GSYM tcwalkstar_p2_def, GSYM tcwalkstar_p1_def]

Theorem tcwalkstarwl_correct0 =
        kcwalkstarwl_cleaned |> SRULE[FORALL_PROD, GSYM tcwalkstarwl_def]

Theorem tcwalkstarwl_correct:
  cwfs s ⇒ cwalkstar s it = HD (tcwalkstar_p1 s [it] [])
Proof
  simp[tcwalkstar_p1_def, GSYM tcwalkstarwl_correct0, kcocwl_def,
       GSYM dfkcwalkstarl_removed,
       dfkcwalkstarl_def, cwc_def, kcwalkstarl_def]
QED


(* handle tail-recursification of unify *)

Definition kcunifyl_def:
  kcunifyl s ts us k = cwc (cunifyl s ts us) k
End

Theorem cunifyl_thm' = SRULE[cunify_thm, GSYM cocl_EXISTS, tcocwl_correct,
                             tcwalk_correct]
                            cunifyl_thm

Theorem kcunifyl_thm =
        kcunifyl_def
          |> SPEC_ALL
          |> SRULE[GSYM contify_cwc, ASSUME “cwfs s”, Once cunifyl_thm']
          |> CONV_RULE
             (TOP_DEPTH_CONV
              (contify_CONV [contify_infer_case, contify_optbind]))
          |> SRULE [cwcp “tcwalk”, cwcp “tcwalk s”, cwcp “$=”, cwcp “$= x”,
                    cwcp “tcocwl”, cwcp “tcocwl s”, cwcp “SOME”,
                    cwcp “CONS”, cwcp “insert”, cwcp “Infer_Tapp”,
                    cwcp “Infer_Tapp x”,
                    cwcp “sptree$insert v”, cwcp “sptree$insert x y”,
                    cwcp “cunifyl”, cwcp “cunifyl s”, cwcp “CONS h”,
                    cwcp “Infer_Tvar_db”, cwcp “tcocwl x y”, cwcp “Infer_Tuvar”]
          |> SRULE [GSYM kcunifyl_def]

Type kcunifkont = “:(infer_t list # infer_t list) list”
Definition apply_cunifk_def:
  apply_cunifk [] x = x ∧
  apply_cunifk ((ts,us)::k) NONE = apply_cunifk k NONE ∧
  apply_cunifk ((ts,us)::k) (SOME m) = kcunifyl m ts us (apply_cunifk k)
End

Theorem apply_cunif_NONE[simp]:
  apply_cunifk k NONE = NONE
Proof
  Induct_on ‘k’ >> simp[apply_cunifk_def] >> Cases >> simp[apply_cunifk_def]
QED

Definition dfkcunifyl_def:
  dfkcunifyl s ts us k = kcunifyl s ts us (apply_cunifk k)
End

Theorem abs_EQ_apply_cunifk:
  (λov. dtcase ov of NONE => NONE | SOME x => dfkcunifyl x ts us k) =
  apply_cunifk ((ts,us)::k)
Proof
  simp[FUN_EQ_THM, apply_cunifk_def, FORALL_OPTION, SF ETA_ss] >>
  simp[dfkcunifyl_def]
QED

Theorem apply_cunifk_thm =
        SRULE [GSYM dfkcunifyl_def, SF ETA_ss] apply_cunifk_def

Theorem dfkcunifyl_thm =
        dfkcunifyl_def
          |> SPEC_ALL
          |> ONCE_REWRITE_RULE[kcunifyl_thm]
          |> SRULE [GSYM dfkcunifyl_def, abs_EQ_apply_cunifk]
          |> CONV_RULE
             (RHS_CONV (REWRITE_CONV [GSYM $ cj 2 $ apply_cunifk_thm]))

Theorem cunifywl0 =
        LIST_CONJ (map SPEC_ALL $ CONJUNCTS apply_cunifk_thm)
          |> Q.INST [‘m’ |-> ‘s’]
          |> PURE_REWRITE_RULE[dfkcunifyl_thm]

Definition kcunifywl_def:
  kcunifywl s k = apply_cunifk k (SOME s)
End

Theorem kcunifywl_thm =
        REWRITE_RULE [GSYM kcunifywl_def]
                     (CONJ (Q.INST [‘x’ |-> ‘SOME s’] $ cj 1 cunifywl0)
                           (cj 2 cunifywl0))

val cunify_code = DefnBase.one_line_ify NONE kcunifywl_thm |> tcallify_th []
Definition cunify_code_def:
  cunify_code = ^cunify_code
End

Theorem kcunifywl_tcallish:
  ∀x. (λ(s,k). cwfs s) x ⇒
      (λ(s,k). kcunifywl s k) x =
      TAILCALL cunify_code (λ(s,k). kcunifywl s k) x
Proof
  simp[whileTheory.TAILCALL_def, FORALL_PROD, sum_CASE_list_CASE,
       cunify_code_def, sum_CASE_pair_CASE, sum_CASE_infer_CASE,
       sum_CASE_COND] >>
  qx_genl_tac [‘s’, ‘k’] >> strip_tac >>
  simp[Once $ DefnBase.one_line_ify NONE kcunifywl_thm, SimpLHS]
QED

Definition isvars_def[simp]:
  isvars [] = {} ∧
  isvars (t::ts) = vars (encode_infer_t t) ∪ isvars ts
End

Theorem FINITE_isvars[simp]:
  FINITE (isvars ts)
Proof
  Induct_on ‘ts’ >> simp[]
QED


Definition cplist_vars_def[simp]:
  cplist_vars [] = {} ∧
  cplist_vars ((ts,us)::rest) = isvars ts ∪ isvars us ∪ cplist_vars rest
End

Theorem FINITE_cplist_vars[simp]:
  FINITE (cplist_vars wl)
Proof
  Induct_on ‘wl’ >> simp[] >> Cases >> simp[]
QED

Definition PFLAT_def[simp]:
  PFLAT [] = EMPTY_BAG ∧
  PFLAT (([],[])::ps) = PFLAT ps ∧
  PFLAT (([], j :: js)::ps) =
    BAG_INSERT (encode_infer_t j) (PFLAT (([],js)::ps)) ∧
  PFLAT ((i::is, js)::ps) =
    BAG_INSERT (encode_infer_t i) (PFLAT ((is,js)::ps))
End

Theorem FINITE_BAG_PFLAT[simp]:
  ∀ps. FINITE_BAG (PFLAT ps)
Proof
  recInduct PFLAT_ind >> rw[]
QED

Definition kcunifywlR_def:
  kcunifywlR (s : infer_t num_map, wl : (infer_t list # infer_t list) list)
             (s0,wl0) ⇔
    cwfs s ∧ cwfs s0 ∧ sp2fm s0 ⊑ sp2fm s ∧
    substvars (encode_infer_t o_f sp2fm s) ∪ cplist_vars wl ⊆
    substvars (encode_infer_t o_f sp2fm s0) ∪ cplist_vars wl0 ∧
    (mlt (walkstarR (sp2fm (map encode_infer_t s))) LEX $<)
         (PFLAT wl, LENGTH wl)
         (PFLAT wl0, LENGTH wl0)
End

Overload kcuR[local,inferior] = “kcunifywlR”

Theorem WF_kcunifywlR:
  WF kcunifywlR
Proof
  simp[WF_DEF] >> qx_gen_tac ‘A’ >>
  disch_then $ qx_choose_then ‘a’ assume_tac >> CCONTR_TAC >>
  gs[DECIDE “¬p ∨ q ⇔ p ⇒ q”] >>
  ‘∃s0 wl0. a = (s0,wl0)’ by (Cases_on ‘a’ >> simp[]) >>
  gvs[FORALL_PROD, EXISTS_PROD] >>
  reverse $ Cases_on ‘cwfs s0’
  >- (first_x_assum drule >> simp[kcunifywlR_def]) >>
  qabbrev_tac ‘R = λ(a,b) (x,y). kcuR (a,b) (x,y) ∧ A (a,b)’ >>
  ‘∀a b x y. kcuR (a,b) (x,y) ∧ A (a,b) ⇔ R (a,b) (x,y)’ by simp[Abbr‘R’] >>
  qpat_x_assum ‘Abbrev(R = _)’ kall_tac >> gvs[] >>
  ‘∀s0 wl0 s wl. R⁺ (s,wl) (s0,wl0) ⇒
                 cwfs s0 ∧ cwfs s ∧ sp2fm s0 ⊑ sp2fm s ∧
                 (A(s0,wl0) ⇒ A(s,wl)) ∧
                 substvars (encode_infer_t o_f sp2fm s) ∪ cplist_vars wl ⊆
                 substvars (encode_infer_t o_f sp2fm s0) ∪ cplist_vars wl0’
    by (Induct_on ‘TC R’ >> simp[FORALL_PROD] >>
        pop_assum (assume_tac o GSYM) >> simp[kcunifywlR_def] >> rw[] >~
        [‘sp2fm a ⊑ sp2fm b’] >- metis_tac[SUBMAP_TRANS] >>
        ASM_SET_TAC[]) >>
  ‘∃s wl. cwfs s ∧ sp2fm s0 ⊑ sp2fm s ∧ A(s,wl) ∧
          substvars (encode_infer_t o_f sp2fm s) ∪ cplist_vars wl ⊆
          substvars (encode_infer_t o_f sp2fm s0) ∪ cplist_vars wl0 ∧
          ∀s' wl'. R⁺ (s',wl') (s,wl) ⇒ s' = s’
    by (qpat_x_assum ‘A _’ mp_tac >>
        completeInduct_on
        ‘CARD (substvars (encode_infer_t o_f sp2fm s0) ∪ cplist_vars wl0) -
         CARD (FDOM (sp2fm s0))’ >>
        gvs[GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO, GSYM CONJ_ASSOC] >>
        rw[] >> gvs[] >>
        reverse $ Cases_on ‘∃s' wl'. R⁺ (s',wl') (s0,wl0) ∧ s' ≠ s0’ >> gvs[]
        >- (qexistsl [‘s0’, ‘wl0’] >> rw[] >> metis_tac[]) >>
        first_x_assum $ qspecl_then [‘s'’, ‘wl'’] mp_tac >> simp[] >> impl_tac
        >- (first_x_assum $ drule_then strip_assume_tac >>
            ‘CARD (domain s0) ≤
               CARD (substvars (encode_infer_t o_f sp2fm s0) ∪ cplist_vars wl0)’
              by (irule CARD_SUBSET >> simp[substvars_def] >> SET_TAC[]) >>
            ‘domain s0 ⊂ domain s'’
              by (simp[PSUBSET_DEF] >>
                  qpat_x_assum ‘_ ⊑ _’ mp_tac >>
                  simp[SUBMAP_FLOOKUP_EQN] >> strip_tac >>
                  ‘domain s0 ⊆ domain s'’
                    by (simp[SUBSET_DEF] >> metis_tac[domain_lookup]) >>
                  simp[] >> strip_tac >> qpat_x_assum ‘s' ≠ s0’ mp_tac >>
                  gvs[spt_eq_thm, cwfs_def] >> pop_assum mp_tac >>
                  simp[EXTENSION, domain_lookup] >>
                  metis_tac[SOME_11, option_CASES]) >>
            simp[DECIDE “x ≤ y ⇒ (0n < y - x ⇔ x < y)”,
                 DECIDE “a ≤ x ⇒ (y < b + x - a ⇔ a + y < b + x:num)”] >>
            conj_tac
            >- (irule (DECIDE “x :num < y ∧ a ≤ b ⇒ x + a < y + b”) >>
                conj_tac >- (irule CARD_PSUBSET >> simp[]) >>
                irule CARD_SUBSET >> simp[]) >>
            irule CARD_PSUBSET >> simp[] >>
            irule PSUBSET_SUBSET_TRANS >> first_x_assum $ irule_at Any >>
            gvs[substvars_def]) >>
        strip_tac >> first_x_assum $ drule_then strip_assume_tac >>
        gvs[] >> qexistsl [‘s’, ‘wl’] >> simp[] >> rw[] >~
        [‘_ ⊑ _’] >- metis_tac[SUBMAP_TRANS] >>
        ((qmatch_abbrev_tac ‘_ ⊆ _’ >> ASM_SET_TAC[]) ORELSE metis_tac[])) >>
  qabbrev_tac ‘M = walkstarR (sp2fm (map encode_infer_t s)) :
                   atom term -> atom term -> bool’ >>
  ‘∀s' wl'.
     R⁺ (s',wl') (s,wl) ⇒
     (mlt M LEX $<) (PFLAT wl',LENGTH wl') (PFLAT wl, LENGTH wl)’
    by (Induct_on ‘R⁺’ using TC_STRONG_INDUCT_LEFT1 >>
        simp[GSYM RIGHT_FORALL_IMP_THM, FORALL_PROD] >> rw[]
        >- (rename [‘TC R’, ‘R (s',wl') (s,wl)’] >>
            ‘R⁺ (s',wl') (s,wl)’ by simp[TC_SUBSET] >>
            ‘s' = s’ by metis_tac[] >> pop_assum SUBST_ALL_TAC >>
            qpat_x_assum ‘R _ _’ mp_tac >>
            (* flip R's "definition" *)
            first_x_assum (assume_tac o GSYM o
                           assert (is_eq o #2 o strip_forall o concl) o
                           assert (is_forall o concl)
                          ) >>
            simp[kcunifywlR_def]) >>
        ‘transitive (mlt M LEX prim_rec$<)’ by simp[transitive_LEX] >>
        dxrule_then irule (iffLR transitive_def) >>
        first_assum $ irule_at Any >>
        rename [‘TC R (s1,wl1) (s,wl)’, ‘R (s2,wl2) (s1,wl1)’]>>
        ‘s1 = s ∧ s2 = s’ by metis_tac[TC_RULES] >>
        ntac 2 $ pop_assum SUBST_ALL_TAC >>
        qpat_x_assum ‘R _ _’ mp_tac >>
        first_x_assum (assume_tac o GSYM o
                       assert (is_eq o #2 o strip_forall o concl) o
                       assert (is_forall o concl)) >>
        simp[kcunifywlR_def]) >>
  qabbrev_tac ‘rwlbs (* reachable wl bags and lengths *) =
               λrwlb. ∃rwl. R⁺ (s,rwl) (s,wl) ∧
                            rwlb = (PFLAT rwl, LENGTH rwl)’ >>
  ‘WF (mlt M LEX prim_rec$<)’
    by gvs[WF_LEX, WF_mlt1, Abbr‘M’, prim_recTheory.WF_measure,
           WF_TC_EQN, walkstar_thWF, cwfs_def, swfs_def] >>
  drule_then (assume_tac o SRULE[PULL_EXISTS]) (iffLR WF_DEF) >>
  ‘∀wl'. R꙳(s,wl') (s,wl) ⇒ ∃wl''. R(s,wl'') (s,wl')’
    by (simp[cj 1 (GSYM TC_RC_EQNS), RC_DEF, DISJ_IMP_THM, FORALL_AND_THM] >>
        metis_tac[TC_RULES]) >>
  ‘∃b. rwlbs b’ by (simp[Abbr‘rwlbs’] >> irule_at Any TC_SUBSET >>
                    metis_tac[TC_RULES]) >>
  first_assum (pop_assum o
               mp_then Any (qx_choose_then‘minwlb’ strip_assume_tac)) >>
  gvs[Abbr‘rwlbs’, PULL_FORALL] >>
  rename [‘R⁺ (s,minwl) (s,wl)’] >>
  ‘∃cwl. R (s,cwl) (s,minwl)’ by metis_tac[TC_RTC] >>
  ‘R⁺ (s,cwl) (s,wl)’ by metis_tac[TC_LEFT1_I] >>
  first_x_assum (pop_assum o mp_then Concl mp_tac) >>
  pop_assum mp_tac >>
  first_x_assum (assume_tac o GSYM o
                 assert (is_eq o #2 o strip_forall o concl) o
                 assert (is_forall o concl)) >>
  simp[kcunifywlR_def]
QED

Theorem PFLAT_CONS2[simp]:
  PFLAT ((l1,h2::t2)::rest) =
  BAG_INSERT (encode_infer_t h2) (PFLAT ((l1,t2)::rest))
Proof
  Induct_on ‘l1’ >> simp[BAG_INSERT_commutes]
QED

Theorem mlt_BAG_INSERT2:
  FINITE_BAG b ⇒
  mlt R b (BAG_INSERT x (BAG_INSERT y b))
Proof
  strip_tac >> irule TC_LEFT1_I >> irule_at Any TC_SUBSET >>
  irule_at Any mlt1_BAG_INSERT >> simp[mlt1_BAG_INSERT]
QED

Theorem cwfs_insert_tvar_db:
  v ∉ domain s ∧ cwfs s ⇒ cwfs (insert v (Infer_Tvar_db c) s)
Proof
  simp[cwfs_def, wf_insert, swfs_def, map_insert, wf_insert] >>
  strip_tac >> irule unifDefTheory.wfs_extend >> simp[] >>
  simp[encode_infer_t_def]
QED

Theorem tcwalk_EQ_Infer_Tuvar:
  cwfs s ∧ tcwalk s t = Infer_Tuvar v ⇒
  v ∉ domain s ∧ ∃u. t = Infer_Tuvar u
Proof
  simp[SF CONJ_ss, GSYM tcwalk_correct, cwalk_def] >> strip_tac >>
  rename [‘swalk (map encode_infer_t s) (encode_infer_t t)’] >>
  drule_then (qspec_then ‘t’ strip_assume_tac) swalk_result_encodable >>
  gvs[encode_infer_t_def] >>
  gvs[swalk_def, cwfs_def, sp2fm_map, swfs_def] >>
  drule_all walk_to_var >> rw[] >>
  pop_assum (mp_tac o Q.AP_TERM ‘decode_infer_t’) >>
  simp[decode_infer_t_def]
QED

Theorem svwalk_result_encodable' =
        svwalk_result_encodable
          |> INST_TYPE [alpha |-> “:infer_t”, beta |-> “:atom”]
          |> Q.INST [‘f’ |-> ‘encode_infer_t’]
          |> SRULE[]

Theorem tcvwalk_substvars:
  cwfs s ∧ tcvwalk s v = t ⇒
  t = Infer_Tuvar v ∧ v ∉ domain s ∨
  vars (encode_infer_t t) ⊆ substvars (encode_infer_t o_f sp2fm s)
Proof
  simp[SF CONJ_ss, GSYM tcvwalk_correct, cvwalk_def] >> strip_tac >>
  gvs[cwfs_def] >>
  drule_all_then (qspec_then ‘v’ strip_assume_tac) svwalk_result_encodable' >>
  simp[] >> gvs[svwalk_def, swfs_def] >>
  drule_all_then strip_assume_tac vwalk_rangevars >>
  gvs[sp2fm_map] >> simp[substvars_def] >> ASM_SET_TAC[]
QED

Theorem tcwalk_rangevars:
  cwfs s ∧ tcwalk s t = u ⇒
  vars (encode_infer_t u) ⊆ rangevars (encode_infer_t o_f sp2fm s) ∪
                            vars (encode_infer_t t)
Proof
  simp[SF CONJ_ss, GSYM tcwalk_correct, cwalk_def] >> strip_tac >>
  drule_all_then (qspec_then ‘t’ strip_assume_tac) swalk_result_encodable >>
  gvs[] >> gvs[swalk_def,cwfs_def,swfs_def] >>
  drule_all walk_rangevars >> simp[sp2fm_map]
QED

Theorem cwfs_var2_extend:
  cwfs s ∧ v1 ≠ v2 ∧ v1 ∉ domain s ∧ v2 ∉ domain s ⇒
  cwfs (insert v1 (Infer_Tuvar v2) s)
Proof
  simp[cwfs_def, wf_insert, map_insert, encode_infer_t_def, swfs_def] >>
  rpt strip_tac >> irule wfs_extend >> simp[] >>
  simp[Once vwalk_def] >> simp[lookup_map] >>
  ‘lookup v2 s = NONE’ by simp[lookup_NONE_domain] >> simp[]
QED

Theorem vars_encode_infer_ts:
  vars (encode_infer_ts is) = isvars is
Proof
  Induct_on ‘is’ >> simp[encode_infer_t_def]
QED

Theorem PFLAT_NIL1[simp]:
  PFLAT (([], l2) :: rest) =
  BAG_UNION (BAG_OF_LIST (MAP encode_infer_t l2)) (PFLAT rest)
Proof
  Induct_on ‘l2’ >> simp[BAG_UNION_INSERT]
QED

Theorem PFLAT_eqn:
  ∀l1 l2.
    PFLAT ((l1,l2)::rest) =
    BAG_UNION (BAG_OF_LIST (MAP encode_infer_t l1))
              (BAG_UNION (BAG_OF_LIST (MAP encode_infer_t l2)) (PFLAT rest))
Proof
  Induct_on ‘l1’ >> simp[PFLAT_def, BAG_UNION_INSERT]
QED

Theorem vars_walkstar_encode_infer_ts:
  wfs s ⇒
  vars (s ◁ encode_infer_ts L) =
  BIGUNION { vars (s ◁ encode_infer_t e) | MEM e L }
Proof
  Induct_on ‘L’ >> simp[encode_infer_t_def] >>
  rpt strip_tac >> simp[Once EXTENSION] >>
  simp[PULL_EXISTS] >> metis_tac[]
QED

Theorem kcunifywl_ensures_decrease:
  ∀x. (λ(s,k). cwfs s) x ∧ cunify_code x = INL y ⇒ kcunifywlR y x
Proof
  simp[cunify_code_def, AllCaseEqs(), PULL_EXISTS, FORALL_PROD] >> rw[] >~
  [‘kcuR _ (_, ([],[])::_)’]
  >- simp[kcunifywlR_def, LEX_DEF] >>~-
  ([‘kcuR (s, (tl1,tl2)::rest) (s, (h1::tl1, h2::tl2) :: rest)’],
   simp[kcunifywlR_def, LEX_DEF, mlt_BAG_INSERT2] >> SET_TAC[]) >~
  [‘kcuR (insert v1 (Infer_Tuvar v2) s0, (t1,t2)::rest)
         (s0, (h1::t1,h2::t2)::rest)’]
  >- (simp[kcunifywlR_def, LEX_DEF, mlt_BAG_INSERT2] >>
      ‘∃cv1 cv2. h1 = Infer_Tuvar cv1 ∧ h2 = Infer_Tuvar cv2 ∧
                 v1 ∉ domain s0 ∧ v2 ∉ domain s0’
        by metis_tac[tcwalk_EQ_Infer_Tuvar] >>
      gvs[] >>
      simp[substvars_FUPDATE, DOMSUB_NOT_IN_DOM, encode_infer_t_def] >>
      gvs[tcwalk_def] >>
      drule tcvwalk_substvars >>
      disch_then (rpt o dxrule_then strip_assume_tac) >> gvs[] >>
      rpt (dxrule_all tcvwalk_substvars) >>
      gvs[cwfs_var2_extend, encode_infer_t_def] >> SET_TAC[]) >~
  [‘kcuR (s,(l1,l2)::(t1,t2)::rest) (s,(h1::t1,h2::t2)::rest)’,
   ‘tcwalk _ _ = Infer_Tapp l1 n1’]
  >- (simp[kcunifywlR_def, LEX_DEF] >> rpt strip_tac >>
      TRY (SET_TAC []) >>~-
      ([‘tcwalk s h = Infer_Tapp L _’, ‘isvars L ⊆ _’],
       drule tcwalk_rangevars >>
       disch_then (qpat_assum ‘tcwalk s h = Infer_Tapp L _’ o
                   mp_then Any mp_tac) >>
       simp[encode_infer_t_def, vars_encode_infer_ts] >>
       SET_TAC[substvars_def]) >>
      simp[PFLAT_eqn] >>
      irule TC_RIGHT1_I >> simp[mlt1_def, PULL_EXISTS] >>
      qexistsl [‘encode_infer_t h1’, ‘BAG_OF_LIST (MAP encode_infer_t l1)’]>>
      simp[BAG_UNION_INSERT, BAG_IN_BAG_OF_LIST] >>
      irule_at Any TC_SUBSET >> simp[mlt1_def, PULL_EXISTS] >>
      qexistsl [‘encode_infer_t h2’, ‘BAG_OF_LIST (MAP encode_infer_t l2)’]>>
      simp[BAG_UNION_INSERT, BAG_IN_BAG_OF_LIST,
           AC COMM_BAG_UNION ASSOC_BAG_UNION] >>
      simp[MEM_MAP, PULL_EXISTS] >>
      metis_tac[walkstar_opth]) >>~-
  ([‘kcuR (insert _ _ s0, (t1,t2)::rest) (s0, (h1::t1,h2::t2)::rest)’,
    ‘¬tcocwl s0 v [L]’],
   simp[kcunifywlR_def, LEX_DEF, mlt_BAG_INSERT2] >>
   gvs[GSYM tcwalk_correct, cwalk_def, GSYM tcocwl_correct] >>
   rename [‘decode_infer_t (swalk _ (encode_infer_t V)) = Infer_Tuvar v’] >>
   qpat_x_assum ‘_ = Infer_Tuvar _’ assume_tac >>
   drule_then (qspec_then ‘V’ strip_assume_tac) swalk_result_encodable >>
   rename [‘decode_infer_t (swalk _ (encode_infer_t A)) = Infer_Tapp L n’] >>
   qpat_x_assum ‘_ = Infer_Tapp _ _’ assume_tac >>
   drule_then (qspec_then ‘A’ strip_assume_tac) swalk_result_encodable >>
   gvs[] >> gs[encode_infer_t_def, swalk_def] >>
   gvs[cwfs_def, swfs_def] >> drule_all walk_to_var >>
   simp[map_insert, wf_insert, encode_infer_t_def] >>
   rpt strip_tac >~
   [‘wfs (_ |+ _)’]
   >- (irule wfs_extend >> simp[] >>
       gvs[cocl_EXISTS, EVERY_MEM, coc_def, soc_def, oc_eq_vars_walkstar] >>
       simp[vars_walkstar_encode_infer_ts] >> metis_tac[]) >~
   [‘substvars (_ |+ _)’]
   >- (simp[substvars_FUPDATE, DOMSUB_NOT_IN_DOM, encode_infer_t_def] >>
       gvs[encode_infer_t_def] >> conj_tac
       >- (rename [‘vwalk _ u = Var v’, ‘v ∉ domain s0’] >>
           drule_all vwalk_rangevars >> simp[sp2fm_map] >> rw[] >>
           simp[substvars_def]) >>
       drule_all walk_rangevars >> simp[substvars_def, sp2fm_map] >>
       SET_TAC[]) >>
   SET_TAC[]) >>~-
  ([‘kcuR (insert _ _ s0, (t1,t2)::rest) (s0, (h1::t1,h2::t2)::rest)’],
   simp[kcunifywlR_def, LEX_DEF, mlt_BAG_INSERT2] >>
   gvs[GSYM tcwalk_correct, cwalk_def] >>
   rename [‘decode_infer_t (swalk _ (encode_infer_t V)) = Infer_Tuvar v’] >>
   qpat_x_assum ‘_ = Infer_Tuvar _’ assume_tac >>
   drule_then (qspec_then ‘V’ strip_assume_tac) swalk_result_encodable >>
   gvs[] >> gs[encode_infer_t_def, swalk_def] >>
   gvs[cwfs_def, swfs_def] >> drule_all walk_to_var >>
   simp[map_insert, wf_insert, encode_infer_t_def] >>
   rpt strip_tac >> gvs[encode_infer_t_def] >~
   [‘wfs (_ |+ _)’]
   >- (irule wfs_extend >> simp[]) >~
   [‘substvars (_ o_f _ |+ _) ⊆ _’]
   >- (simp[substvars_FUPDATE, DOMSUB_NOT_IN_DOM] >>
       drule_all vwalk_rangevars >> rw[sp2fm_map] >> simp[substvars_def]) >>
   SET_TAC[])
QED

Theorem kcunifywl_preserves_precond:
  ∀x y. (λ(s,k). cwfs s) x ∧ cunify_code x = INL y ⇒ (λ(s,k). cwfs s) y
Proof
  simp[cunify_code_def, AllCaseEqs(), FORALL_PROD] >> rw[] >> simp[] >~
  [‘insert _ (Infer_Tuvar v2) s’]
  >- (irule cwfs_var2_extend >> metis_tac[tcwalk_EQ_Infer_Tuvar]) >>
  drule_all_then strip_assume_tac tcwalk_EQ_Infer_Tuvar >>
  simp[cwfs_insert_tvar_db] >>
  rename [‘tcwalk s0 t1 = Infer_Tuvar var’, ‘tcwalk s0 t2 = Infer_Tapp ts n’] >>
  gvs[GSYM tcwalk_correct, cwalk_def, encode_infer_t_def,
      GSYM tcocwl_correct] >>
  ‘∃it. swalk (map encode_infer_t s0) (encode_infer_t t2) = encode_infer_t it’
    by metis_tac[swalk_result_encodable] >>
  gvs[encode_infer_t_def, swalk_def, cwfs_def, swfs_def,
      wf_insert, sp2fm_map, cocl_EXISTS, EVERY_MEM, coc_def, soc_def] >>
  irule wfs_extend >> simp[vars_walkstar_encode_infer_ts] >>
  metis_tac[oc_eq_vars_walkstar]
QED

Theorem kcunifywl_cleaned:
  ∀x. (λ(s,wl). cwfs s) x ⇒
      (λ(s,wl). kcunifywl s wl) x = TAILREC cunify_code x
Proof
  match_mp_tac whileTheory.TAILREC_GUARD_ELIMINATION >> rpt conj_tac
  >- ACCEPT_TAC kcunifywl_preserves_precond
  >- (rpt strip_tac >> qexists ‘kcunifywlR’ >> conj_tac
      >- (irule $ iffLR WF_EQ_WFP >> simp[WF_kcunifywlR]) >>
      simp[kcunifywl_ensures_decrease])
  >- ACCEPT_TAC kcunifywl_tcallish
QED

Definition tcunify_def:
  tcunify s wl = TAILREC cunify_code (s,wl)
End

Theorem tcunify_thm =
        tcunify_def |> SRULE[Once whileTheory.TAILREC]
                    |> SRULE[cunify_code_def,
                             sum_CASE_list_CASE, sum_CASE_pair_CASE,
                             sum_CASE_infer_CASE, sum_CASE_COND]
                    |> SRULE[GSYM cunify_code_def, GSYM tcunify_def]

Theorem tcunify_correct0 =
        SRULE[FORALL_PROD, GSYM tcunify_def] kcunifywl_cleaned

Theorem tcunify_correct:
  cwfs s ⇒ cunify s t1 t2 = tcunify s [([t1],[t2])]
Proof
  strip_tac >>
  simp[GSYM tcunify_correct0, kcunifywl_def, apply_cunifk_thm,
       dfkcunifyl_def] >>
  simp[kcunifyl_def, cwc_def, apply_cunifk_thm] >>
  simp[cunifyl_CONS2] >>
  Cases_on ‘cunify s t1 t2’ >> simp[] >>
  drule_all cunify_preserves_cwfs >>
  simp[DISCH_ALL cunifyl_NIL2]
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

Triviality t_vwalk_ind':
  !s'. t_wfs s' ⇒
   ∀P.
     (∀v. (∀v1 u. (FLOOKUP s' v = SOME v1) ∧ (v1 = Infer_Tuvar u) ⇒ P u) ⇒ P v) ⇒
     ∀v. P v
Proof
  ntac 4 STRIP_TAC >>
fs [t_wfs_def] >>
imp_res_tac (DISCH_ALL vwalk_ind) >>
pop_assum ho_match_mp_tac >>
rw [] >>
qpat_x_assum `∀v. (∀u. (FLOOKUP s' v = SOME (Infer_Tuvar u)) ⇒ P u) ⇒ P v` ho_match_mp_tac >>
rw [] >>
qpat_x_assum `∀u. Q u ⇒ P u` ho_match_mp_tac >>
rw [FLOOKUP_o_f, encode_infer_t_def]
QED

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

Definition t_walk_def[nocompute]:
t_walk s t = decode_infer_t (walk (encode_infer_t o_f s) (encode_infer_t t))
End

Theorem t_walk_eqn:
 (!s v. t_walk s (Infer_Tuvar v) = t_vwalk s v) ∧
 (!s ts tc. t_walk s (Infer_Tapp ts tc) = Infer_Tapp ts tc) ∧
 (!s n. t_walk s (Infer_Tvar_db n) = Infer_Tvar_db n)
Proof
rw [t_walk_def, walk_def, t_vwalk_def, encode_infer_t_def,
    decode_infer_t_def, decode_left_inverse]
QED

Definition t_oc_def[nocompute]:
t_oc s t v = oc (encode_infer_t o_f s) (encode_infer_t t) v
End

(*
Triviality t_oc_ind':
  ∀s oc'.
  t_wfs s ∧
  (∀t v. v ∈ t_vars t ∧ v ∉ FDOM s ⇒ oc' t v) ∧
  (∀t v u t'. u ∈ t_vars t ∧ (t_vwalk s u = t') ∧ oc' t' v ⇒ oc' t v) ⇒
  (∀a0 a1. oc (FMAP_MAP2 (λ(n,t). encode_infer_t t) s) a0 a1 ⇒ !a0'. (a0 = encode_infer_t a0') ⇒ oc' a0' a1)
Proof
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
     rw [encode_vwalk]]
QED

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

Triviality encode_vwalk:
  !s. t_wfs s ⇒ !u. vwalk (encode_infer_t o_f s) u = encode_infer_t (t_vwalk s u)
Proof
  NTAC 2 STRIP_TAC >>
ho_match_mp_tac t_vwalk_ind >>
rw [] >>
`wfs (encode_infer_t o_f s)` by metis_tac [t_wfs_def] >>
rw [Once vwalk_def] >>
rw [Once t_vwalk_eqn, FLOOKUP_o_f] >>
cases_on `FLOOKUP s u` >>
rw [encode_infer_t_def] >>
cases_on `x` >>
rw [encode_infer_t_def]
QED

Triviality t_oc_eqn_help:
  !l v s.
  oc (encode_infer_t o_f s) (encode_infer_ts l) v ⇔
  EXISTS (λt. oc (encode_infer_t o_f s) (encode_infer_t t) v) l
Proof
  induct_on `l` >>
rw [encode_infer_t_def]
QED

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

Definition t_ext_s_check_def[nocompute]:
t_ext_s_check s v t =
  OPTION_MAP
    ((o_f) decode_infer_t)
    (ext_s_check (encode_infer_t o_f s) v (encode_infer_t t))
End

Theorem t_ext_s_check_eqn:
 !s v t.
  t_ext_s_check s v t = if t_oc s t v then NONE else SOME (s |+ (v,t))
Proof
rw [t_ext_s_check_def, t_oc_def, decode_left_inverse_I,
    decode_left_inverse] >>
metis_tac [FUPDATE_PURGE]
QED

Definition t_unify_def[nocompute]:
t_unify s t1 t2 =
  OPTION_MAP
    ((o_f) decode_infer_t)
    (unify (encode_infer_t o_f s) (encode_infer_t t1) (encode_infer_t t2))
End

Definition ts_unify_def:
(ts_unify s [] [] = SOME s) ∧
(ts_unify s (t1::ts1) (t2::ts2) =
  dtcase t_unify s t1 t2 of
   | NONE => NONE
   | SOME s' => ts_unify s' ts1 ts2) ∧
(ts_unify s _ _ = NONE)
End

Triviality encode_walk:
  ∀s. t_wfs s ⇒
      ∀t. walk (encode_infer_t o_f s) (encode_infer_t t) = encode_infer_t (t_walk s t)
Proof
  rw[walk_def] >>
  imp_res_tac encode_vwalk >>
  fs[] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[t_walk_def,decode_left_inverse] >>
  metis_tac[decode_left_inverse]
QED

Triviality encode_pair_cases:
  (∀t t1 t2.
    (encode_infer_t t = Pair t1 t2) ⇒
      ((t1 = Const Tapp_tag) ∧
       (∃tc ts. t2 = Pair (Const (TC_tag tc)) (encode_infer_ts ts))))
Proof
  Cases >> rw[encode_infer_t_def] >>
  PROVE_TAC[]
QED

Triviality encode_unify_lemma:
  !s t1 t2 s' t1' t2'.
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
   OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))
Proof
  ho_match_mp_tac unify_ind >>
simp[] >>
rw [t_unify_def] >>
fs[t_wfs_def, option_map_case, combinTheory.o_DEF] >>
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
metis_tac[o_f_FUPDATE,o_f_DOMSUB,FUPDATE_PURGE,encode_walk,t_wfs_def]
QED

Triviality encode_unify:
  !s t1 t2 s' t1' t2'.
  (s = encode_infer_t o_f s') ∧
  (t1 = encode_infer_t t1') ∧ (t2 = encode_infer_t t2') ∧
  t_wfs s' ⇒
  (unify s t1 t2
   =
   OPTION_MAP ((o_f) encode_infer_t) (t_unify s' t1' t2'))
Proof
  metis_tac[encode_unify_lemma]
QED

Theorem wfs_unify[local]:
  !s t1 t2 s'. wfs s ∧ (unify s t1 t2 = SOME s') ⇒ wfs s'
Proof
  metis_tac [unify_unifier]
QED

Theorem ts_unify_thm[local]:
  !s l1 l2.
    t_wfs s ⇒
    (ts_unify s l1 l2 =
     OPTION_MAP
     ((o_f) decode_infer_t)
     (unify (encode_infer_t o_f s) (encode_infer_ts l1) (encode_infer_ts l2)))
Proof
induct_on `l1` >>
cases_on `l2` >>
rw [ts_unify_def, encode_infer_t_def] >>
`wfs (encode_infer_t o_f s)` by metis_tac [t_wfs_def] >>
fs [option_map_case] >|
[rw [Once unify_def, ts_unify_def],
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
          rw [] >>
          `?x. z = encode_infer_t o_f x`
                by (imp_res_tac encode_unify >>
                    fs [] >>
                    cases_on `t_unify s h' h` >>
                    fs [] >>
                    metis_tac []) >>
          `t_wfs x` by
                 (rw [t_wfs_def] >>
                  metis_tac [wfs_unify]) >>
          rw [decode_left_inverse_I]
     ]
]
QED

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
    decode_left_inverse_I, encode_vwalk, option_bind_thm]
THEN1
(cases_on `t_vwalk s n'` >>
     rw [encode_infer_t_def, decode_left_inverse,
         decode_left_inverse_I, o_f_FUPDATE, decode_infer_t_def] >>
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
         o_f_FUPDATE, decode_infer_t_def, t_ext_s_check_eqn] >>
     rw [Once oc_walking, encode_infer_t_def, t_oc_def] >>
     rw [Once unify_def] >>
     metis_tac [FUPDATE_PURGE])
THEN1
(cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def] >>
     rw [o_f_FUPDATE, decode_left_inverse_I, decode_left_inverse,
         decode_infer_t_def, t_ext_s_check_eqn] >>
     rw [ts_unify_thm, Once oc_walking, encode_infer_t_def, t_oc_def, option_bind_thm] >>
     rw [Once unify_def] >>
     metis_tac [FUPDATE_PURGE])
THEN1
(cases_on `t_vwalk s n` >>
     rw [encode_infer_t_def] >>
     rw [Once unify_def, option_map_case] >>
     rw [o_f_FUPDATE, decode_left_inverse_I, decode_left_inverse,
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
     rw [o_f_FUPDATE, decode_left_inverse, decode_left_inverse_I,
         decode_infer_t_def, t_ext_s_check_eqn, option_map_case] >>
     rw [ts_unify_thm, Once oc_walking, encode_infer_t_def, t_oc_def,
     option_bind_thm, option_map_case] >>
     rw [Once unify_def]
QED

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
        fs[encode_infer_t_def] >>
        first_x_assum(qspec_then`us`kall_tac) >>
        first_x_assum(qspec_then`us`mp_tac) >>
        simp[] >> disch_then (qspec_then`s'`mp_tac o CONJUNCT2) >>
        simp[t_wfs_def,SIMP_RULE(srw_ss())[]encode_unify] ) >>
      rw[] >>
      fs[encode_infer_t_def,SIMP_RULE(srw_ss())[]encode_unify,t_wfs_def] ) >>
    rw[] >>
    first_x_assum match_mp_tac >>
    imp_res_tac wfs_unify >>
    fs[] >>
    conj_tac >- (
      rw[] >>
      fs[encode_infer_t_def] >>
      first_x_assum(qspec_then`us`kall_tac) >>
      first_x_assum(qspec_then`us`kall_tac) >>
      first_x_assum(qspec_then`us`kall_tac) >>
      first_x_assum(qspec_then`usx`mp_tac) >>
      simp[t_wfs_def,SIMP_RULE(srw_ss())[]encode_unify] ) >>
    rw[] >>
    fs[encode_infer_t_def] ) >>
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
  simp[] >> strip_tac >>
  first_x_assum(qspecl_then[`s`,`Infer_Tvar_db 0`,`Infer_Tvar_db 0`]mp_tac) >>
  simp[encode_infer_t_def] >>
  fs[t_wfs_def]
QED

Definition apply_subst_t_def[nocompute]:
apply_subst_t s t = decode_infer_t (subst_APPLY (encode_infer_t o_f s) (encode_infer_t t))
End

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

Definition t_walkstar_def[nocompute]:
t_walkstar s t =
  decode_infer_t (walkstar (encode_infer_t o_f s) (encode_infer_t t))
End

Theorem t_walkstar_cwalkstar:
  t_walkstar s t = cwalkstar (fm2sp s) t
Proof
  simp[t_walkstar_def, cwalkstar_def]
QED

Triviality ts_walkstar_thm:
  !l s.
  t_wfs s ⇒
  (decode_infer_ts ((encode_infer_t o_f s) ◁ encode_infer_ts l) =
   MAP (t_walkstar s) l)
Proof
  induct_on `l` >>
rw [t_wfs_def, encode_infer_t_def, Once walkstar_def, decode_infer_t_def] >>
rw [t_walkstar_def]
QED

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

Definition t_collapse_def[nocompute]:
t_collapse s =
  decode_infer_t o_f collapse (encode_infer_t o_f s)
End

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
  rw[decode_left_inverse,decode_left_inverse_I] >>
  simp[t_wfs_def,t_walkstar_def] >>
  fs[SUBMAP_DEF] >>
  metis_tac[encode_infer_t_11,o_f_FAPPLY]
QED

Triviality t_unify_strongind':
  !P0 P1.
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
    (!s ts1 ts2. t_wfs s ==> (t_wfs s ⇒ P1 s ts1 ts2))
Proof
  NTAC 3 STRIP_TAC >>
ho_match_mp_tac t_unify_ind >>
rw [] >>
cases_on `ts1` >>
cases_on `ts2` >>
fs [] >>
qpat_x_assum `!s ts1 ts2. Q s ts1 ts2 ⇒ P1 s ts1 ts2` match_mp_tac >>
rw [] >>
metis_tac [t_unify_unifier]
QED

val t_unify_strongind = save_thm("t_unify_strongind", SIMP_RULE (bool_ss) [] t_unify_strongind');

Triviality encode_walkstar:
  !s t.
  t_wfs s ⇒
  walkstar (encode_infer_t o_f s) (encode_infer_t t) =
  encode_infer_t (t_walkstar s t)
Proof
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
rw [Once walkstar_def]
QED

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

Definition t_vR_def:
t_vR s = vR (encode_infer_t o_f s)
End

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

Definition t_rangevars_def:
t_rangevars s = rangevars (encode_infer_t o_f s)
End

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
Definition t_compat_def:
  t_compat s s' ⇔
  t_wfs s ∧ t_wfs s' ∧
  !t. t_walkstar s' (t_walkstar s t) = t_walkstar s' t
End

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

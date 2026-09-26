(*
  Consistency of the contexts that HOL Light actually builds.

  holConsistency proves consistency for a context extending init_ctxt,
  fhol_ctxt or hol_ctxt, subject in each case to a condition on the axioms
  the context asserts. A real HOL Light session - Candle running hol.ml -
  meets none of those hypotheses. Its context does extend init_ctxt, but it
  asserts three axioms, so the init_ctxt result does not apply; and it is
  not an extension of fhol_ctxt or hol_ctxt at all, since it interleaves
  ordinary definitions between the axioms, states ETA_AX and SELECT_AX in
  universally closed form, declares the type ind before ONE_ONE and ONTO
  rather than after, and binds those two definitions with generated variable
  names.

  This theory restates consistency for the shape a session really has: a
  predicate constraining only the bool definitions, the three axiom terms,
  the declaration of @ next to SELECT_AX, and the four updates of the
  infinity block, quantifying over everything in between subject only to
  axiom-freeness. Each shape is then shown realisable, and checked against
  the context a Candle session prints after loading core HOL Light.

  The same four differences are visible in the sources of the reference
  implementation, which agree with the ones Candle loads on every file that
  creates a context; but only Candle was run.
*)
Theory holLightConsistency
Ancestors
  setSpec setModel holSyntaxLib holSyntax holSyntaxExtra holBoolSyntax
  holAxiomsSyntax holSemantics holSemanticsExtra holSoundness
  holExtension holBool holAxioms holConsistency
Libs
  preamble

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = Parse.hide "mem"

Overload A[local] = ``Tyvar «A»``
Overload B[local] = ``Tyvar «B»``
Overload x[local] = ``Var «x» A``
Overload P[local] = ``Var «P» (Fun A Bool)``
Overload tf[local] = ``Var «t» (Fun A B)``
Overload gf[local] = ``Var «f» (Fun A B)``
Overload x1[local] = ``Var «x1» A``
Overload x2[local] = ``Var «x2» A``
Overload y[local] = ``Var «y» B``
Overload h[local] = ``Var «f» (Fun Ind Ind)``

(* ------------------------------------------------------------------------
   The three axiom-carrying blocks, in the form HOL Light states them.

   ETA_AX and SELECT_AX are the universal closures of the terms modelled in
   holAxiomsSyntax, with the closure binders pinned to the names HOL Light
   uses (class.ml): the predicates below fix these updates by equality of
   contexts, not up to alpha, so a different binder is a different context.
   The two constants of the infinity block are bound by generated variables,
   so those two names alone are parameters.
   ------------------------------------------------------------------------ *)

Definition mk_eta_ctxt_cl_def:
  mk_eta_ctxt_cl ctxt =
    NewAxiom (Forall «t» (Fun A B) (Abs x (Comb tf x) === tf)) :: ctxt
End

Definition mk_select_ctxt_cl_def:
  mk_select_ctxt_cl ctxt =
    NewAxiom (Forall «P» (Fun A Bool)
               (Forall «x» A (Implies (Comb P x) (Comb P (Comb (Select A) P))))) ::
    NewConst «@» (Fun (Fun A Bool) A) ::
    ctxt
End

Definition mk_infinity_ctxt_hl_def:
  mk_infinity_ctxt_hl b1 b2 ctxt =
    NewAxiom (Exists «f» (Fun Ind Ind) (And (One_One h) (Not (Onto h)))) ::
    ConstDef «ONTO»
      (Abs (Var b2 (Fun A B))
        (Forall «y» B (Exists «x» A (y === Comb (Var b2 (Fun A B)) x)))) ::
    ConstDef «ONE_ONE»
      (Abs (Var b1 (Fun A B))
        (Forall «x1» A (Forall «x2» A
          (Implies (Comb (Var b1 (Fun A B)) x1 === Comb (Var b1 (Fun A B)) x2)
                   (x1 === x2))))) ::
    NewType «ind» 0 ::
    ctxt
End

val mem = ``mem:'U->'U->bool``

Overload axiom_free = ``λl. EVERY (λu. ∀p. u ≠ NewAxiom p) l``

(* ------------------------------------------------------------------------
   Extension chains and their suffixes

   Each step of an extension conses a single update, so the chain from c0 up
   to ctxt visits precisely the suffixes of ctxt. Any suffix that still has
   c0 below it is therefore one of them, and the update sitting directly on
   top of such a suffix is one the chain performed - which is where every
   freshness side condition below comes from.
   ------------------------------------------------------------------------ *)

(* the chain cannot already have arrived at c0, since c0 sits strictly below
   the update on top; so its last step is that update *)

Theorem extends_CONS[local]:
  ∀u ctxt c0 m.
    (u::ctxt) extends c0 ∧ ctxt = m ++ c0 ⇒ u updates ctxt ∧ ctxt extends c0
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum`_ extends _`(mp_tac o REWRITE_RULE[extends_def]) >>
  simp[Once relationTheory.RTC_CASES1] >> strip_tac >>
  gvs[GSYM extends_def]
QED

Theorem extends_CONS_I[local]:
  ∀u ctxt base. ctxt extends base ∧ u updates ctxt ⇒ (u::ctxt) extends base
Proof
  rw[extends_def] >> simp[Once relationTheory.RTC_CASES1] >> metis_tac[]
QED

Theorem extends_suffix:
  ∀l base c0.
    (l ++ base) extends c0 ∧ (∃m. base = m ++ c0) ⇒ (l ++ base) extends base
Proof
  Induct >> rw[]
  >- simp[extends_def] >>
  irule extends_CONS_I >>
  drule extends_CONS >> disch_then(qspec_then`l ++ m`mp_tac) >> simp[] >>
  strip_tac >>
  first_x_assum(qspecl_then[`m ++ c0`,`c0`]mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> simp[]
QED

Theorem extends_suffix_below:
  ∀l base c0.
    (l ++ base) extends c0 ∧ (∃m. base = m ++ c0) ⇒ base extends c0
Proof
  Induct >> rw[] >>
  drule extends_CONS >> disch_then(qspec_then`l ++ m`mp_tac) >> simp[]
QED

Theorem extends_updates_at:
  ∀l u rest c0.
    (l ++ u::rest) extends c0 ∧ (∃m. rest = m ++ c0) ⇒
    u updates rest ∧ rest extends c0
Proof
  rpt gen_tac >> strip_tac >>
  irule extends_CONS >>
  conj_tac >- metis_tac[] >>
  irule extends_suffix_below >>
  conj_tac >- (qexists_tac`u::m` >> simp[]) >>
  metis_tac[]
QED

(* ------------------------------------------------------------------------
   Models along a chain
   ------------------------------------------------------------------------ *)

(* an axiom-free segment carries a model along with it *)

Theorem models_axiom_free_segment:
  is_set_theory ^mem ⇒
  ∀l base i.
    (l ++ base) extends base ∧ theory_ok (thyof base) ∧
    i models thyof base ∧ axiom_free l ⇒
    ∃i'. equal_on (sigof base) i i' ∧ i' models thyof (l ++ base)
Proof
  rw[] >>
  qspecl_then[`base`,`l ++ base`]mp_tac (UNDISCH extends_consistent) >>
  simp[] >> strip_tac >>
  first_x_assum irule >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* asserting an axiom leaves the signature alone *)

Theorem models_NewAxiom:
  ∀i p ctxt.
    i models thyof (NewAxiom p::ctxt) ⇔
    i models thyof ctxt ∧ i satisfies (sigof ctxt,[],p)
Proof
  rw[models_def,conexts_of_upd_def] >> metis_tac[]
QED

(* and a model does not see the names of bound variables *)

Theorem satisfies_ACONV:
  is_set_theory ^mem ⇒
  ∀i sig p q.
    ACONV p q ∧ welltyped p ∧ welltyped q ∧ i satisfies (sig,[],p) ⇒
    i satisfies (sig,[],q)
Proof
  rw[satisfies_def] >> metis_tac[termsem_aconv]
QED

Theorem models_ACONV:
  is_set_theory ^mem ⇒
  ∀i ctxt1 ctxt2.
    sigof ctxt1 = sigof ctxt2 ∧
    theory_ok (thyof ctxt1) ∧ theory_ok (thyof ctxt2) ∧
    (∀p. p ∈ axsof ctxt2 ⇒ ∃q. q ∈ axsof ctxt1 ∧ ACONV q p) ∧
    i models thyof ctxt1 ⇒
    i models thyof ctxt2
Proof
  rw[] >> gvs[models_def] >> rw[] >>
  `∃q. MEM q (axiom_list ctxt1) ∧ ACONV q p` by metis_tac[] >>
  `welltyped p ∧ welltyped q` by
    (fs[theory_ok_def] >> res_tac >> metis_tac[welltyped_def]) >>
  irule (UNDISCH satisfies_ACONV) >>
  metis_tac[]
QED

(* closing an axiom over a variable keeps it satisfied *)

Theorem satisfies_Forall:
  is_set_theory ^mem ⇒
  ∀i sig nm ty b.
    is_interpretation sig i ∧ is_std_interpretation i ∧
    type_ok (tysof sig) ty ∧ term_ok sig b ∧ typeof b = Bool ∧
    is_forall_sig (tmsof sig) ∧ is_forall_interpretation (tmaof i) ∧
    i satisfies (sig,[],b) ⇒
    i satisfies (sig,[],Forall nm ty b)
Proof
  rw[satisfies_def] >>
  qspecl_then[`sig`,`i`,`v`,`nm`,`ty`,`b`]mp_tac (UNDISCH termsem_forall) >>
  simp[] >> disch_then SUBST1_TAC >>
  simp[boolean_eq_true] >> rw[] >>
  first_x_assum irule >>
  gvs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[]
QED

(* ------------------------------------------------------------------------
   The blocks have models
   ------------------------------------------------------------------------ *)

Theorem welltyped_eta_ax[local]:
  ∀nm. welltyped
         (Forall nm (Fun A B)
            (Abs x (Comb (Var nm (Fun A B)) x) === Var nm (Fun A B)))
Proof
  rw[welltyped_def]
  >- (qexists_tac`Bool` >> simp[EQUATION_HAS_TYPE_BOOL]) >>
  simp[equation_def]
QED

Theorem ACONV_eta_ax[local]:
  ACONV (Forall «f» (Fun A B) (Abs x (Comb gf x) === gf))
        (Forall «t» (Fun A B) (Abs x (Comb tf x) === tf))
Proof
  simp[ACONV_def,RACONV,ALPHAVARS_def,equation_def]
QED

Theorem eta_cl_has_model:
  is_set_theory ^mem ⇒
  ∀ctxt i.
    theory_ok (thyof ctxt) ∧ is_bool_sig (sigof ctxt) ∧
    i models thyof ctxt ∧ is_bool_interpretation i ⇒
    i models thyof (mk_eta_ctxt_cl ctxt)
Proof
  rw[] >>
  `is_std_sig (sigof ctxt)` by metis_tac[is_bool_sig_std] >>
  drule_all (UNDISCH eta_has_model) >>
  PURE_REWRITE_TAC[mk_eta_ctxt_def,mk_eta_ctxt_cl_def,models_NewAxiom] >>
  strip_tac >> conj_tac >- simp[] >>
  irule (UNDISCH satisfies_ACONV) >>
  conj_tac >- simp[welltyped_eta_ax] >>
  qexists_tac`Forall «f» (Fun A B) (Abs x (Comb gf x) === gf)` >>
  conj_tac >- simp[welltyped_eta_ax] >>
  conj_tac >- simp[ACONV_eta_ax] >>
  irule (UNDISCH satisfies_Forall) >>
  rpt conj_tac
  >~ [`typeof _ = Bool`] >- simp[equation_def]
  >~ [`term_ok _ _`]
  >- (rw[term_ok_equation,term_ok_def,type_ok_def] >> fs[is_std_sig_def])
  >~ [`type_ok _ (Fun A B)`] >- (rw[type_ok_def] >> fs[is_std_sig_def]) >>
  gvs[is_bool_sig_def,is_bool_interpretation_def,models_def]
QED

Theorem equal_on_bool_interpretation[local]:
  ∀s j1 j2.
    equal_on s j1 j2 ∧ is_bool_interpretation j1 ∧ is_bool_sig s ∧
    is_std_interpretation j2 ⇒
    is_bool_interpretation j2
Proof
  rw[is_bool_interpretation_def,is_true_interpretation_def,
     is_and_interpretation_def,is_implies_interpretation_def,
     is_forall_interpretation_def,is_exists_interpretation_def,
     is_or_interpretation_def,is_false_interpretation_def,
     is_not_interpretation_def] >>
  irule equal_on_interprets >>
  qexistsl_tac[`j1`,`s`] >>
  fs[is_bool_sig_def,is_true_sig_def,is_and_sig_def,is_implies_sig_def,
     is_forall_sig_def,is_exists_sig_def,is_or_sig_def,is_false_sig_def,
     is_not_sig_def] >>
  simp[type_ok_def,tyvars_def] >>
  fs[is_std_sig_def]
QED

Theorem term_ok_Forall[local]:
  ∀sig nm ty p.
    is_std_sig sig ∧ is_forall_sig (tmsof sig) ∧ type_ok (tysof sig) ty ∧
    term_ok sig p ∧ typeof p = Bool ⇒
    term_ok sig (Forall nm ty p) ∧ typeof (Forall nm ty p) = Bool
Proof
  rw[] >> imp_res_tac term_ok_welltyped >>
  rw[term_ok_def,type_ok_def] >> fs[is_std_sig_def,is_forall_sig_def] >>
  qexists_tac`[(ty,Tyvar «A»)]` >> rw[holSyntaxLibTheory.REV_ASSOCD]
QED

Theorem models_close_axiom[local]:
  is_set_theory ^mem ⇒
  ∀i ctxt nm ty p.
    i models thyof (NewAxiom p::ctxt) ∧
    is_forall_sig (tmsof ctxt) ∧ is_forall_interpretation (tmaof i) ∧
    type_ok (tysof ctxt) ty ∧ term_ok (sigof ctxt) p ∧ typeof p = Bool ⇒
    i models thyof (NewAxiom (Forall nm ty p)::ctxt)
Proof
  rw[models_NewAxiom] >>
  irule (UNDISCH satisfies_Forall) >>
  gvs[models_def,models_NewAxiom]
QED

Theorem select_cl_has_model:
  is_set_theory ^mem ⇒
  ∀ctxt i.
    theory_ok (thyof ctxt) ∧ is_bool_sig (sigof ctxt) ∧
    «@» ∉ FDOM (tmsof ctxt) ∧
    i models thyof ctxt ∧ is_bool_interpretation i ⇒
    ∃i'. equal_on (sigof ctxt) i i' ∧ i' models thyof (mk_select_ctxt_cl ctxt)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `is_std_sig (sigof ctxt)` by metis_tac[is_bool_sig_std] >>
  `is_implies_sig (tmsof ctxt)` by fs[is_bool_sig_def] >>
  `is_implies_interpretation (tmaof i)` by fs[is_bool_interpretation_def] >>
  qspec_then`ctxt`mp_tac (UNDISCH select_has_model) >>
  impl_tac >- simp[] >>
  disch_then(qspec_then`i`mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  qexists_tac`i'` >> simp[] >>
  `NewConst «@» (Fun (Fun A Bool) A)::ctxt extends ctxt` by
    (irule extends_CONS_I >>
     simp[extends_def,updates_cases,type_ok_def] >> fs[is_std_sig_def]) >>
  `theory_ok (thyof (mk_select_ctxt ctxt))` by
    (irule (MP_CANON extends_theory_ok) >> qexists_tac`ctxt` >> simp[] >>
     irule select_extends >> fs[is_std_sig_def,is_implies_sig_def]) >>
  qabbrev_tac`C = NewConst «@» (Fun (Fun A Bool) A)::ctxt` >>
  qabbrev_tac`op = Implies (Comb P x) (Comb P (Comb (Select A) P))` >>
  `mk_select_ctxt ctxt = NewAxiom op::C` by
    simp[Abbr`C`,Abbr`op`,mk_select_ctxt_def] >>
  `mk_select_ctxt_cl ctxt =
     NewAxiom (Forall «P» (Fun A Bool) (Forall «x» A op))::C` by
    simp[Abbr`C`,Abbr`op`,mk_select_ctxt_cl_def] >>
  `is_bool_sig (sigof C)` by metis_tac[is_bool_sig_extends] >>
  `is_std_sig (sigof C)` by metis_tac[is_bool_sig_std] >>
  `is_forall_sig (tmsof C)` by fs[is_bool_sig_def] >>
  `term_ok (sigof C) op ∧ typeof op = Bool` by
    (qpat_x_assum`theory_ok (thyof (mk_select_ctxt _))`mp_tac >>
     simp[theory_ok_def] >> strip_tac >>
     first_x_assum(qspec_then`op`mp_tac) >>
     simp[conexts_of_upd_def] >> metis_tac[WELLTYPED_LEMMA]) >>
  `is_std_interpretation i'` by
    (qpat_x_assum`i' models _`mp_tac >> simp[models_def]) >>
  `is_bool_interpretation i'` by metis_tac[equal_on_bool_interpretation] >>
  `is_forall_interpretation (tmaof i')` by fs[is_bool_interpretation_def] >>
  qpat_x_assum`mk_select_ctxt_cl _ = _`SUBST1_TAC >>
  qpat_x_assum`mk_select_ctxt _ = _`
    (fn th => qpat_x_assum`i' models _`(assume_tac o REWRITE_RULE[th])) >>
  `term_ok (sigof C) (Forall «x» A op) ∧ typeof (Forall «x» A op) = Bool` by
    (irule term_ok_Forall >> simp[type_ok_def]) >>
  `type_ok (tysof C) (Fun A Bool)` by (simp[type_ok_def] >> fs[is_std_sig_def]) >>
  irule (UNDISCH models_close_axiom) >>
  ntac 5 (conj_tac >- simp[]) >>
  irule (UNDISCH models_close_axiom) >>
  simp[type_ok_def]
QED

(* HOL Light declares ind at the bottom of the infinity block rather than
   above the two definitions, and binds the two definitions with generated
   variables. A NewType update contributes no constants and no axioms and a
   ConstSpec update contributes no types, so moving ind past them leaves the
   type and constant lists as the very same lists; and a bound variable name
   is invisible to the signature. *)

Theorem sigof_mk_infinity_ctxt_hl[local]:
  ∀b1 b2 ctxt.
    tysof (mk_infinity_ctxt_hl b1 b2 ctxt) = tysof (mk_infinity_ctxt ctxt) ∧
    tmsof (mk_infinity_ctxt_hl b1 b2 ctxt) = tmsof (mk_infinity_ctxt ctxt)
Proof
  simp[mk_infinity_ctxt_hl_def,mk_infinity_ctxt_def]
QED

Theorem ACONV_ONE_ONE_conext[local]:
  ∀b.
    ACONV
      (Const «ONE_ONE» (Fun (Fun A B) Bool) ===
       Abs gf (Forall «x1» A (Forall «x2» A
         (Implies (Comb gf x1 === Comb gf x2) (x1 === x2)))))
      (Const «ONE_ONE» (Fun (Fun A B) Bool) ===
       Abs (Var b (Fun A B)) (Forall «x1» A (Forall «x2» A
         (Implies (Comb (Var b (Fun A B)) x1 === Comb (Var b (Fun A B)) x2)
                  (x1 === x2)))))
Proof
  simp[ACONV_def,RACONV,ALPHAVARS_def,equation_def]
QED

Theorem ACONV_ONTO_conext[local]:
  ∀b.
    ACONV
      (Const «ONTO» (Fun (Fun A B) Bool) ===
       Abs gf (Forall «y» B (Exists «x» A (y === Comb gf x))))
      (Const «ONTO» (Fun (Fun A B) Bool) ===
       Abs (Var b (Fun A B))
         (Forall «y» B (Exists «x» A (y === Comb (Var b (Fun A B)) x))))
Proof
  simp[ACONV_def,RACONV,ALPHAVARS_def,equation_def]
QED

Theorem axioms_mk_infinity_ctxt_hl[local]:
  ∀b1 b2 ctxt p.
    p ∈ axsof (mk_infinity_ctxt_hl b1 b2 ctxt) ⇒
    ∃q. q ∈ axsof (mk_infinity_ctxt ctxt) ∧ ACONV q p
Proof
  simp[mk_infinity_ctxt_hl_def,mk_infinity_ctxt_def,conexts_of_upd_def,
       VSUBST_def,equation_def,holSyntaxLibTheory.REV_ASSOCD] >>
  rw[]
  >- metis_tac[ACONV_REFL]
  >- (irule_at Any (SIMP_RULE (srw_ss()) [equation_def] ACONV_ONTO_conext) >>
      simp[])
  >- (irule_at Any (SIMP_RULE (srw_ss()) [equation_def] ACONV_ONE_ONE_conext) >>
      simp[]) >>
  metis_tac[ACONV_REFL]
QED

Theorem infinity_hl_has_model:
  is_set_theory ^mem ∧ (∃inf. is_infinite ^mem inf) ⇒
  ∀ctxt i b1 b2.
    theory_ok (thyof ctxt) ∧
    theory_ok (thyof (mk_infinity_ctxt_hl b1 b2 ctxt)) ∧
    is_bool_sig (sigof ctxt) ∧
    DISJOINT (FDOM (tmsof ctxt)) {«ONE_ONE»;«ONTO»} ∧
    «ind» ∉ FDOM (tysof ctxt) ∧
    i models thyof ctxt ∧ is_bool_interpretation i ⇒
    ∃i'. equal_on (sigof ctxt) i i' ∧
         i' models thyof (mk_infinity_ctxt_hl b1 b2 ctxt)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `is_std_sig (sigof ctxt)` by metis_tac[is_bool_sig_std] >>
  qspec_then`ctxt`mp_tac
    (infinity_has_model |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
                        |> UNDISCH |> UNDISCH) >>
  impl_tac >- fs[is_bool_sig_def] >>
  disch_then(qspec_then`i`mp_tac) >>
  impl_tac >- fs[is_bool_interpretation_def] >>
  strip_tac >> qexists_tac`i'` >> simp[] >>
  `theory_ok (thyof (mk_infinity_ctxt ctxt))` by
    (irule (MP_CANON extends_theory_ok) >> qexists_tac`ctxt` >> simp[] >>
     irule infinity_extends >> fs[is_bool_sig_def,is_true_sig_def,is_and_sig_def,
       is_implies_sig_def,is_forall_sig_def,is_exists_sig_def,is_or_sig_def,
       is_false_sig_def,is_not_sig_def]) >>
  qspecl_then[`i'`,`mk_infinity_ctxt ctxt`,`mk_infinity_ctxt_hl b1 b2 ctxt`]mp_tac
    (UNDISCH models_ACONV) >>
  impl_tac
  >- (conj_tac >- simp[sigof_mk_infinity_ctxt_hl] >>
      conj_tac >- simp[] >>
      conj_tac >- simp[] >>
      conj_tac >- metis_tac[axioms_mk_infinity_ctxt_hl] >>
      simp[]) >>
  simp[]
QED

(* ------------------------------------------------------------------------
   The context shapes a HOL Light session builds

   Everything the predicates pin down is decidable on a printed context: the
   eight boolean definitions on top of the initial context, the three axiom
   terms, the declaration of @ immediately below SELECT_AX, and the four
   updates of the infinity block. Everything else is quantified over, and
   asked only not to assert an axiom.
   ------------------------------------------------------------------------ *)

Definition fhol_light_ctxt_def:
  fhol_light_ctxt ctxt ⇔
    ∃l2 l1 l0.
      ctxt = l2 ++ mk_select_ctxt_cl
                     (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)) ∧
      axiom_free (l0 ++ l1 ++ l2)
End

Definition hol_light_ctxt_def:
  hol_light_ctxt ctxt ⇔
    ∃l3 l2 l1 l0 b1 b2.
      ctxt = l3 ++ mk_infinity_ctxt_hl b1 b2
                     (l2 ++ mk_select_ctxt_cl
                              (l1 ++ mk_eta_ctxt_cl
                                       (l0 ++ mk_bool_ctxt init_ctxt))) ∧
      axiom_free (l0 ++ l1 ++ l2 ++ l3)
End

(* ------------------------------------------------------------------------
   Consistency
   ------------------------------------------------------------------------ *)

(* the facts every cut point of the chain needs: it lies above the boolean
   definitions, so it is a good theory with a boolean signature, and any
   model of it interprets the boolean constants as intended *)

Theorem mk_bool_ctxt_APPEND[local]:
  ∀ctxt. ∃m. mk_bool_ctxt ctxt = m ++ ctxt
Proof
  rw[mk_bool_ctxt_def] >>
  qexists_tac`[ConstDef «~» NotDef; ConstDef «F» FalseDef;
               ConstDef «\\/» OrDef; ConstDef «?» ExistsDef;
               ConstDef «!» ForallDef; ConstDef «==>» ImpliesDef;
               ConstDef «/\\» AndDef; ConstDef «T» TrueDef]` >>
  simp[]
QED

Theorem extends_bool_suffix[local]:
  ∀l. (l ++ mk_bool_ctxt init_ctxt) extends init_ctxt ⇒
      (l ++ mk_bool_ctxt init_ctxt) extends mk_bool_ctxt init_ctxt
Proof
  rw[] >> irule extends_suffix >> qexists_tac`init_ctxt` >> simp[] >>
  metis_tac[mk_bool_ctxt_APPEND]
QED

Theorem suffix_facts_m[local]:
  is_set_theory ^mem ⇒
  ∀m i.
    (m ++ mk_bool_ctxt init_ctxt) extends init_ctxt ∧
    i models thyof (m ++ mk_bool_ctxt init_ctxt) ⇒
    theory_ok (thyof (m ++ mk_bool_ctxt init_ctxt)) ∧
    is_bool_sig (sigof (m ++ mk_bool_ctxt init_ctxt)) ∧
    is_bool_interpretation i
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule extends_bool_suffix >> strip_tac >>
  `is_std_sig (sigof init_ctxt)` by (mp_tac init_theory_ok >> simp[theory_ok_def]) >>
  `is_bool_sig (sigof (mk_bool_ctxt init_ctxt))` by (irule bool_has_bool_sig >> simp[]) >>
  `theory_ok (thyof (mk_bool_ctxt init_ctxt))` by
    (irule (MP_CANON extends_theory_ok) >> qexists_tac`init_ctxt` >>
     simp[bool_extends_init,init_theory_ok]) >>
  `theory_ok (thyof (m ++ mk_bool_ctxt init_ctxt))` by
    (irule (MP_CANON extends_theory_ok) >>
     qexists_tac`mk_bool_ctxt init_ctxt` >> simp[]) >>
  `is_bool_sig (sigof (m ++ mk_bool_ctxt init_ctxt))` by
    (irule (MP_CANON is_bool_sig_extends) >>
     qexists_tac`mk_bool_ctxt init_ctxt` >> simp[]) >>
  simp[] >>
  irule extends_is_bool_interpretation >>
  conj_tac >- simp[] >>
  qexistsl_tac[`init_ctxt`,`m ++ mk_bool_ctxt init_ctxt`] >> simp[]
QED

Theorem suffix_facts[local]:
  is_set_theory ^mem ⇒
  ∀sfx i.
    sfx extends init_ctxt ∧ (∃m. sfx = m ++ mk_bool_ctxt init_ctxt) ∧
    i models thyof sfx ⇒
    theory_ok (thyof sfx) ∧ is_bool_sig (sigof sfx) ∧ is_bool_interpretation i
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qspecl_then[`m`,`i`]mp_tac (UNDISCH suffix_facts_m) >>
  impl_tac >- simp[] >> simp[]
QED

Theorem bool_ctxt_has_model[local]:
  is_set_theory ^mem ⇒ ∃i. i models thyof (mk_bool_ctxt init_ctxt)
Proof
  strip_tac >>
  drule init_ctxt_has_model >> strip_tac >>
  qspecl_then[`init_ctxt`,`mk_bool_ctxt init_ctxt`]mp_tac
    (UNDISCH extends_consistent) >>
  simp[bool_extends_init] >> strip_tac >>
  qsuff_tac`∃i'. equal_on (sigof init_ctxt) i i' ∧
                 i' models thyof (mk_bool_ctxt init_ctxt)`
  >- metis_tac[] >>
  first_x_assum irule >>
  simp[init_theory_ok] >> EVAL_TAC >> simp[]
QED

Theorem climb_axiom_free[local]:
  is_set_theory ^mem ⇒
  ∀l sfx i.
    (l ++ sfx) extends sfx ∧ sfx extends init_ctxt ∧ axiom_free l ∧
    i models thyof sfx ⇒
    ∃i'. i' models thyof (l ++ sfx)
Proof
  rw[] >>
  `theory_ok (thyof sfx)` by
    (irule (MP_CANON extends_theory_ok) >> qexists_tac`init_ctxt` >>
     simp[init_theory_ok]) >>
  qspecl_then[`l`,`sfx`,`i`]mp_tac (UNDISCH models_axiom_free_segment) >>
  simp[] >> strip_tac >> metis_tac[]
QED

Theorem bool_ctxt_suffix_init[local]:
  ∀mk. ∃m. mk ++ mk_bool_ctxt init_ctxt = m ++ init_ctxt
Proof
  rw[] >> strip_assume_tac (Q.SPEC`init_ctxt` mk_bool_ctxt_APPEND) >>
  qexists_tac`mk ++ m` >> simp[]
QED

Theorem chain_cut[local]:
  ∀l mk.
    (l ++ (mk ++ mk_bool_ctxt init_ctxt)) extends init_ctxt ⇒
    (l ++ (mk ++ mk_bool_ctxt init_ctxt)) extends
      (mk ++ mk_bool_ctxt init_ctxt) ∧
    (mk ++ mk_bool_ctxt init_ctxt) extends init_ctxt
Proof
  rw[]
  >- (qspecl_then[`l`,`mk ++ mk_bool_ctxt init_ctxt`,`init_ctxt`]mp_tac
        extends_suffix >> simp[bool_ctxt_suffix_init]) >>
  qspecl_then[`l`,`mk ++ mk_bool_ctxt init_ctxt`,`init_ctxt`]mp_tac
    extends_suffix_below >> simp[bool_ctxt_suffix_init]
QED

(* every cut point of the chain is again of the form "something on top of the
   boolean definitions", so one lemma recognises them all *)

Theorem above_bool[local]:
  (∃m. mk_bool_ctxt init_ctxt = m ++ mk_bool_ctxt init_ctxt) ∧
  (∀X l. (∃m. X = m ++ mk_bool_ctxt init_ctxt) ⇒
         ∃m. l ++ X = m ++ mk_bool_ctxt init_ctxt) ∧
  (∀X u. (∃m. X = m ++ mk_bool_ctxt init_ctxt) ⇒
         ∃m. u::X = m ++ mk_bool_ctxt init_ctxt)
Proof
  rw[]
  >- (qexists_tac`l ++ m` >> simp[]) >>
  qexists_tac`u::m` >> simp[]
QED

Theorem chain_cut2[local]:
  ∀l base.
    (l ++ base) extends init_ctxt ∧ (∃m. base = m ++ mk_bool_ctxt init_ctxt) ⇒
    (l ++ base) extends base ∧ base extends init_ctxt
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qspecl_then[`l`,`m`]mp_tac chain_cut >> simp[]
QED

Theorem chain_cut_CONS[local]:
  ∀u base m.
    (u::base) extends init_ctxt ∧ base = m ++ mk_bool_ctxt init_ctxt ⇒
    (u::base) extends base ∧ base extends init_ctxt
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then[`[u]`,`base`]mp_tac chain_cut2 >>
  impl_tac >- (simp[] >> metis_tac[]) >> simp[]
QED

Theorem cut_eta[local]:
  ∀X. mk_eta_ctxt_cl X extends init_ctxt ∧
      (∃m. X = m ++ mk_bool_ctxt init_ctxt) ⇒
      mk_eta_ctxt_cl X extends X ∧ X extends init_ctxt
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum`_ extends init_ctxt`
    (mp_tac o REWRITE_RULE[mk_eta_ctxt_cl_def]) >> strip_tac >>
  drule_all chain_cut_CONS >> strip_tac >>
  qpat_x_assum`X = _`kall_tac >> simp[mk_eta_ctxt_cl_def]
QED

Theorem cut_select[local]:
  ∀X. mk_select_ctxt_cl X extends init_ctxt ∧
      (∃m. X = m ++ mk_bool_ctxt init_ctxt) ⇒
      mk_select_ctxt_cl X extends X ∧ X extends init_ctxt ∧
      «@» ∉ FDOM (tmsof X)
Proof
  rpt gen_tac >> strip_tac >>
  `∃m. NewConst «@» (Fun (Fun A Bool) A)::X = m ++ mk_bool_ctxt init_ctxt` by
    metis_tac[above_bool] >>
  qpat_x_assum`_ extends init_ctxt`
    (mp_tac o REWRITE_RULE[mk_select_ctxt_cl_def]) >> strip_tac >>
  drule_all chain_cut_CONS >> strip_tac >>
  drule_all chain_cut_CONS >> strip_tac >>
  `∃m. X = m ++ init_ctxt` by metis_tac[bool_ctxt_suffix_init] >>
  drule_all extends_CONS >> strip_tac >>
  simp[mk_select_ctxt_cl_def] >>
  conj_tac >- metis_tac[extends_trans] >>
  qpat_x_assum`NewConst _ _ updates _`mp_tac >> simp[updates_cases]
QED

Theorem chain_cut_CONS4[local]:
  ∀u1 u2 u3 u4 base m.
    (u1::u2::u3::u4::base) extends init_ctxt ∧
    base = m ++ mk_bool_ctxt init_ctxt ⇒
    (u1::u2::u3::u4::base) extends base ∧ base extends init_ctxt ∧
    u4 updates base ∧ u3 updates (u4::base) ∧ u2 updates (u3::u4::base)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then[`u1`,`u2::u3::u4::base`,`u2::u3::u4::m`]mp_tac chain_cut_CONS >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then[`u2`,`u3::u4::base`,`u3::u4::m`]mp_tac chain_cut_CONS >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then[`u3`,`u4::base`,`u4::m`]mp_tac chain_cut_CONS >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then[`u4`,`base`,`m`]mp_tac chain_cut_CONS >>
  impl_tac >- simp[] >> strip_tac >>
  `∃k1. base = k1 ++ init_ctxt` by metis_tac[bool_ctxt_suffix_init] >>
  `u4 updates base` by metis_tac[extends_CONS] >>
  `∃k2. u4::base = k2 ++ init_ctxt` by (qexists_tac`u4::k1` >> simp[]) >>
  `u3 updates (u4::base)` by metis_tac[extends_CONS] >>
  `∃k3. u3::u4::base = k3 ++ init_ctxt` by (qexists_tac`u3::u4::k1` >> simp[]) >>
  `u2 updates (u3::u4::base)` by metis_tac[extends_CONS] >>
  simp[] >> metis_tac[extends_trans]
QED

Theorem cut_infinity[local]:
  ∀X b1 b2.
    mk_infinity_ctxt_hl b1 b2 X extends init_ctxt ∧
    (∃m. X = m ++ mk_bool_ctxt init_ctxt) ⇒
    mk_infinity_ctxt_hl b1 b2 X extends X ∧ X extends init_ctxt ∧
    «ind» ∉ FDOM (tysof X) ∧
    DISJOINT (FDOM (tmsof X)) {«ONE_ONE»;«ONTO»}
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum`_ extends init_ctxt`
    (mp_tac o REWRITE_RULE[mk_infinity_ctxt_hl_def]) >> strip_tac >>
  drule_all chain_cut_CONS4 >> strip_tac >>
  qpat_x_assum`X = _`kall_tac >>
  imp_res_tac updates_DISJOINT >>
  gvs[mk_infinity_ctxt_hl_def,IN_DISJOINT] >> metis_tac[]
QED

Theorem fhol_light_has_model:
  is_set_theory ^mem ⇒
  ∀ctxt. ctxt extends init_ctxt ∧ fhol_light_ctxt ctxt ⇒
    theory_ok (thyof ctxt) ∧ ∃i. i models thyof ctxt
Proof
  strip_tac >> gen_tac >> strip_tac >>
  conj_asm1_tac
  >- (irule (MP_CANON extends_theory_ok) >> qexists_tac`init_ctxt` >>
      simp[init_theory_ok]) >>
  qpat_x_assum`fhol_light_ctxt _`
    (strip_assume_tac o REWRITE_RULE[fhol_light_ctxt_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `axiom_free l0 ∧ axiom_free l1 ∧ axiom_free l2` by fs[] >>
  (* peel the chain apart from the top *)
  qspecl_then[`l2`,
    `mk_select_ctxt_cl (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt))`]
    mp_tac chain_cut2 >>
  impl_tac
  >- (conj_tac >- simp[] >>
      simp[mk_select_ctxt_cl_def,mk_eta_ctxt_cl_def] >> metis_tac[above_bool]) >>
  strip_tac >>
  qspec_then`l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)`mp_tac
    cut_select >>
  impl_tac
  >- (conj_tac >- simp[] >>
      simp[mk_eta_ctxt_cl_def] >> metis_tac[above_bool]) >>
  strip_tac >>
  qspecl_then[`l1`,`mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)`]mp_tac
    chain_cut2 >>
  impl_tac
  >- (conj_tac >- simp[] >>
      simp[mk_eta_ctxt_cl_def] >> metis_tac[above_bool]) >>
  strip_tac >>
  qspec_then`l0 ++ mk_bool_ctxt init_ctxt`mp_tac cut_eta >>
  impl_tac
  >- (conj_tac >- simp[] >> metis_tac[above_bool]) >>
  strip_tac >>
  qspecl_then[`l0`,`mk_bool_ctxt init_ctxt`]mp_tac chain_cut2 >>
  impl_tac
  >- (conj_tac >- simp[] >> metis_tac[above_bool]) >>
  strip_tac >>
  (* climb, building the model *)
  mp_tac (UNDISCH bool_ctxt_has_model) >>
  disch_then(qx_choose_then`j0`strip_assume_tac) >>
  qspecl_then[`l0`,`mk_bool_ctxt init_ctxt`,`j0`]mp_tac
    (UNDISCH climb_axiom_free) >>
  impl_tac
  >- (simp[]) >>
  disch_then(qx_choose_then`j1`strip_assume_tac) >>
  qspecl_then[`l0 ++ mk_bool_ctxt init_ctxt`,`j1`]mp_tac (UNDISCH suffix_facts) >>
  impl_tac
  >- (simp[] >> metis_tac[above_bool]) >>
  strip_tac >>
  qspecl_then[`l0 ++ mk_bool_ctxt init_ctxt`,`j1`]mp_tac
    (UNDISCH eta_cl_has_model) >>
  impl_tac
  >- (simp[]) >>
  strip_tac >>
  qspecl_then[`l1`,`mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)`,`j1`]mp_tac
    (UNDISCH climb_axiom_free) >>
  impl_tac
  >- (simp[]) >>
  disch_then(qx_choose_then`j2`strip_assume_tac) >>
  qspecl_then[`l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)`,`j2`]mp_tac
    (UNDISCH suffix_facts) >>
  impl_tac
  >- (simp[] >> simp[mk_eta_ctxt_cl_def] >> metis_tac[above_bool]) >>
  strip_tac >>
  qspecl_then[`l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)`,`j2`]mp_tac
    (UNDISCH select_cl_has_model) >>
  impl_tac
  >- (simp[]) >>
  disch_then(qx_choose_then`j3`strip_assume_tac) >>
  qspecl_then[`l2`,
    `mk_select_ctxt_cl (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt))`,
    `j3`]mp_tac (UNDISCH climb_axiom_free) >>
  impl_tac
  >- (simp[]) >>
  strip_tac >> metis_tac[]
QED

Theorem hol_light_has_model:
  is_set_theory ^mem ∧ (∃inf. is_infinite ^mem inf) ⇒
  ∀ctxt. ctxt extends init_ctxt ∧ hol_light_ctxt ctxt ⇒
    theory_ok (thyof ctxt) ∧ ∃i. i models thyof ctxt
Proof
  strip_tac >> gen_tac >> strip_tac >>
  conj_asm1_tac
  >- (irule (MP_CANON extends_theory_ok) >> qexists_tac`init_ctxt` >>
      simp[init_theory_ok]) >>
  qpat_x_assum`hol_light_ctxt _`
    (strip_assume_tac o REWRITE_RULE[hol_light_ctxt_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `axiom_free l0 ∧ axiom_free l1 ∧ axiom_free l2 ∧ axiom_free l3` by fs[] >>
  qspecl_then[`l3`,
    `mk_infinity_ctxt_hl b1 b2
       (l2 ++ mk_select_ctxt_cl
                (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)))`]
    mp_tac chain_cut2 >>
  impl_tac
  >- (conj_tac >- simp[] >>
      simp[mk_infinity_ctxt_hl_def,mk_select_ctxt_cl_def,mk_eta_ctxt_cl_def] >>
      metis_tac[above_bool]) >>
  strip_tac >>
  qspecl_then[
    `l2 ++ mk_select_ctxt_cl (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt))`,
    `b1`,`b2`]mp_tac cut_infinity >>
  impl_tac
  >- (conj_tac >- simp[] >>
      simp[mk_select_ctxt_cl_def,mk_eta_ctxt_cl_def] >> metis_tac[above_bool]) >>
  strip_tac >>
  `theory_ok (thyof (mk_infinity_ctxt_hl b1 b2
     (l2 ++ mk_select_ctxt_cl
              (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)))))` by
    (irule (MP_CANON extends_theory_ok) >> qexists_tac`init_ctxt` >>
     simp[init_theory_ok]) >>
  qspec_then
    `l2 ++ mk_select_ctxt_cl (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt))`
    mp_tac (UNDISCH fhol_light_has_model) >>
  impl_tac >- (simp[fhol_light_ctxt_def] >> metis_tac[]) >>
  disch_then(CONJUNCTS_THEN2 assume_tac (qx_choose_then`k0`assume_tac)) >>
  qspecl_then[
    `l2 ++ mk_select_ctxt_cl (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt))`,
    `k0`]mp_tac (UNDISCH suffix_facts) >>
  impl_tac
  >- (simp[] >> simp[mk_select_ctxt_cl_def,mk_eta_ctxt_cl_def] >>
      metis_tac[above_bool]) >>
  strip_tac >>
  qspecl_then[
    `l2 ++ mk_select_ctxt_cl (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt))`,
    `k0`,`b1`,`b2`]mp_tac
    (infinity_hl_has_model |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
                           |> UNDISCH |> UNDISCH) >>
  impl_tac >- simp[] >>
  disch_then(qx_choose_then`k1`strip_assume_tac) >>
  qspecl_then[`l3`,
    `mk_infinity_ctxt_hl b1 b2
       (l2 ++ mk_select_ctxt_cl
                (l1 ++ mk_eta_ctxt_cl (l0 ++ mk_bool_ctxt init_ctxt)))`,
    `k1`]mp_tac (UNDISCH climb_axiom_free) >>
  impl_tac >- simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem init_light_consistent:
  ∀ctxt. ctxt extends init_ctxt ∧ axiom_free ctxt ⇒
    consistent_theory (thyof ctxt)
Proof
  rw[] >>
  mp_tac (Q.ISPEC`V_mem` (Q.GEN`mem` min_hol_consistent)) >>
  simp[is_set_theory_V] >>
  disch_then irule >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem fhol_light_consistent:
  ∀ctxt. ctxt extends init_ctxt ∧ fhol_light_ctxt ctxt ⇒
    consistent_theory (thyof ctxt)
Proof
  rw[] >>
  mp_tac (Q.ISPEC`V_mem` (Q.GEN`mem` proves_consistent)) >>
  simp[is_set_theory_V] >>
  disch_then irule >>
  mp_tac (Q.ISPEC`V_mem` (Q.GEN`mem` fhol_light_has_model)) >>
  simp[is_set_theory_V] >>
  disch_then(qspec_then`ctxt`mp_tac) >> simp[] >> metis_tac[]
QED

Theorem hol_light_consistent:
  (∃inf. is_infinite V_mem inf) ⇒
  ∀ctxt. ctxt extends init_ctxt ∧ hol_light_ctxt ctxt ⇒
    consistent_theory (thyof ctxt)
Proof
  rw[] >>
  mp_tac (Q.ISPEC`V_mem` (Q.GEN`mem` proves_consistent)) >>
  simp[is_set_theory_V] >>
  disch_then irule >>
  mp_tac (Q.ISPEC`V_mem` (Q.GEN`mem` hol_light_has_model)) >>
  simp[is_set_theory_V] >>
  impl_tac >- metis_tac[] >>
  disch_then(qspec_then`ctxt`mp_tac) >> simp[] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   The shapes are realisable

   The results above are conditional on a context both extending init_ctxt
   and having one of the shapes, and nothing so far rules out those two
   conditions being jointly unsatisfiable - which would leave the results
   true but empty, the same defect the kernel channel had before it carried
   the extension. So exhibit a context of each shape that really is a
   definitional extension of the initial context. The measured context below
   says more, since it is a context a session actually reached, but it is
   compared against a translation of the kernel printout prepared outside
   the logic; these three owe nothing to anything outside it.
   ------------------------------------------------------------------------ *)

Theorem eta_cl_extends:
  ∀ctxt. is_bool_sig (sigof ctxt) ⇒ mk_eta_ctxt_cl ctxt extends ctxt
Proof
  rpt strip_tac >>
  `is_std_sig (sigof ctxt)` by fs[is_bool_sig_def] >>
  `type_ok (tysof (sigof ctxt)) (Fun A B)` by
    (simp[type_ok_def] >> fs[is_std_sig_def]) >>
  `term_ok (sigof ctxt) (Abs x (Comb tf x) === tf)` by
    (simp[term_ok_equation] >> simp[term_ok_def,type_ok_def] >>
     fs[is_std_sig_def]) >>
  `typeof (Abs x (Comb tf x) === tf) = Bool` by simp[equation_def] >>
  `term_ok (sigof ctxt) (Forall «t» (Fun A B) (Abs x (Comb tf x) === tf)) ∧
   typeof (Forall «t» (Fun A B) (Abs x (Comb tf x) === tf)) = Bool` by
    (irule term_ok_Forall >> fs[is_bool_sig_def]) >>
  simp[mk_eta_ctxt_cl_def] >>
  irule extends_CONS_I >>
  simp[extends_def,updates_cases] >>
  metis_tac[term_ok_welltyped,WELLTYPED]
QED

Theorem select_cl_extends:
  ∀ctxt. is_bool_sig (sigof ctxt) ∧ «@» ∉ FDOM (tmsof ctxt) ⇒
    mk_select_ctxt_cl ctxt extends ctxt
Proof
  rpt strip_tac >>
  `is_std_sig (sigof ctxt)` by fs[is_bool_sig_def] >>
  `(NewConst «@» (Fun (Fun A Bool) A)::ctxt) extends ctxt` by
    (irule extends_CONS_I >>
     simp[extends_def,updates_cases,type_ok_def] >> fs[is_std_sig_def]) >>
  `is_bool_sig (sigof (NewConst «@» (Fun (Fun A Bool) A)::ctxt))` by
    (drule is_bool_sig_extends >> simp[]) >>
  `is_std_sig (sigof (NewConst «@» (Fun (Fun A Bool) A)::ctxt))` by
    fs[is_bool_sig_def] >>
  `term_ok (sigof (NewConst «@» (Fun (Fun A Bool) A)::ctxt))
     (Implies (Comb P x) (Comb P (Comb (Select A) P))) ∧
   typeof (Implies (Comb P x) (Comb P (Comb (Select A) P))) = Bool` by
    (simp[term_ok_def,type_ok_def,FLOOKUP_UPDATE] >>
     fs[is_std_sig_def,is_bool_sig_def,is_implies_sig_def,FLOOKUP_UPDATE]) >>
  `term_ok (sigof (NewConst «@» (Fun (Fun A Bool) A)::ctxt))
     (Forall «x» A (Implies (Comb P x) (Comb P (Comb (Select A) P)))) ∧
   typeof (Forall «x» A (Implies (Comb P x) (Comb P (Comb (Select A) P)))) =
     Bool` by
    (irule term_ok_Forall >> fs[is_bool_sig_def] >> simp[type_ok_def] >>
     fs[is_std_sig_def]) >>
  `term_ok (sigof (NewConst «@» (Fun (Fun A Bool) A)::ctxt))
     (Forall «P» (Fun A Bool)
       (Forall «x» A (Implies (Comb P x) (Comb P (Comb (Select A) P))))) ∧
   typeof (Forall «P» (Fun A Bool)
       (Forall «x» A (Implies (Comb P x) (Comb P (Comb (Select A) P))))) =
     Bool` by
    (irule term_ok_Forall >> fs[is_bool_sig_def] >> simp[type_ok_def] >>
     fs[is_std_sig_def]) >>
  simp[mk_select_ctxt_cl_def] >>
  irule extends_CONS_I >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[Once updates_cases] >>
  fs[] >>
  rpt (simp[Once has_type_cases])
QED

(* the two definitions of the infinity block, over any bool signature that
   has not used their names - in particular over one that has already
   declared ind, which is where HOL Light puts them *)

Theorem ONE_ONE_def_updates[local]:
  ∀b ctxt.
    theory_ok (thyof ctxt) ∧ is_bool_sig (sigof ctxt) ∧
    «ONE_ONE» ∉ FDOM (tmsof ctxt) ⇒
    ConstDef «ONE_ONE»
      (Abs (Var b (Fun A B))
        (Forall «x1» A (Forall «x2» A
          (Implies (Comb (Var b (Fun A B)) x1 === Comb (Var b (Fun A B)) x2)
                   (x1 === x2))))) updates ctxt
Proof
  rpt strip_tac >>
  `is_std_sig (sigof ctxt)` by fs[is_bool_sig_def] >>
  irule ConstDef_updates >>
  simp[CLOSED_def,tvars_def,tyvars_def,equation_def,term_ok_def,type_ok_def] >>
  fs[is_bool_sig_def,is_std_sig_def,is_forall_sig_def,is_implies_sig_def] >>
  conj_tac >- metis_tac[] >>
  qexists_tac`[(B,A)]` >> simp[holSyntaxLibTheory.REV_ASSOCD]
QED

Theorem ONTO_def_updates[local]:
  ∀b ctxt.
    theory_ok (thyof ctxt) ∧ is_bool_sig (sigof ctxt) ∧
    «ONTO» ∉ FDOM (tmsof ctxt) ⇒
    ConstDef «ONTO»
      (Abs (Var b (Fun A B))
        (Forall «y» B (Exists «x» A (y === Comb (Var b (Fun A B)) x))))
      updates ctxt
Proof
  rpt strip_tac >>
  `is_std_sig (sigof ctxt)` by fs[is_bool_sig_def] >>
  irule ConstDef_updates >>
  simp[CLOSED_def,tvars_def,tyvars_def,equation_def,term_ok_def,type_ok_def] >>
  fs[is_bool_sig_def,is_std_sig_def,is_forall_sig_def,is_exists_sig_def] >>
  conj_tac >- metis_tac[] >>
  qexists_tac`[(B,A)]` >> simp[holSyntaxLibTheory.REV_ASSOCD]
QED

(* INFINITY_AX is well formed as soon as ind and the two constants are
   there, whatever the definitions bound them with *)

Theorem infinity_ax_updates[local]:
  ∀ctxt.
    is_bool_sig (sigof ctxt) ∧
    FLOOKUP (tmsof ctxt) «ONE_ONE» = SOME (Fun (Fun A B) Bool) ∧
    FLOOKUP (tmsof ctxt) «ONTO» = SOME (Fun (Fun A B) Bool) ∧
    FLOOKUP (tysof ctxt) «ind» = SOME 0 ⇒
    NewAxiom (Exists «f» (Fun Ind Ind) (And (One_One h) (Not (Onto h))))
      updates ctxt
Proof
  rpt strip_tac >>
  `is_std_sig (sigof ctxt)` by fs[is_bool_sig_def] >>
  simp[Once updates_cases] >>
  conj_tac >- rpt (simp[Once has_type_cases]) >>
  simp[term_ok_def,type_ok_def] >>
  fs[is_bool_sig_def,is_std_sig_def,is_and_sig_def,is_not_sig_def,
     is_exists_sig_def] >>
  conj_tac
  >- (qexists_tac`[(Fun Ind Ind,A)]` >> simp[holSyntaxLibTheory.REV_ASSOCD]) >>
  qexists_tac`[(Ind,A);(Ind,B)]` >> simp[holSyntaxLibTheory.REV_ASSOCD]
QED

Theorem infinity_hl_extends:
  ∀b1 b2 ctxt.
    theory_ok (thyof ctxt) ∧ is_bool_sig (sigof ctxt) ∧
    DISJOINT (FDOM (tmsof ctxt)) {«ONE_ONE»;«ONTO»} ∧
    «ind» ∉ FDOM (tysof ctxt) ⇒
    mk_infinity_ctxt_hl b1 b2 ctxt extends ctxt
Proof
  rpt strip_tac >>
  `is_std_sig (sigof ctxt)` by fs[is_bool_sig_def] >>
  (* the type of individuals, declared first *)
  `NewType «ind» 0 updates ctxt` by fs[updates_cases] >>
  `(NewType «ind» 0::ctxt) extends ctxt` by
    (irule extends_CONS_I >> simp[extends_def]) >>
  `theory_ok (thyof (NewType «ind» 0::ctxt))` by
    metis_tac[updates_theory_ok] >>
  `is_bool_sig (sigof (NewType «ind» 0::ctxt))` by
    metis_tac[is_bool_sig_extends] >>
  (* then the two definitions, over a signature that already has ind *)
  qspecl_then[`b1`,`NewType «ind» 0::ctxt`]mp_tac ONE_ONE_def_updates >>
  impl_tac >- (fs[IN_DISJOINT] >> metis_tac[]) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac`u1 updates (NewType «ind» 0::ctxt)` >>
  `(u1::NewType «ind» 0::ctxt) extends ctxt` by
    (irule extends_CONS_I >> conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  `theory_ok (thyof (u1::NewType «ind» 0::ctxt))` by
    metis_tac[updates_theory_ok] >>
  `is_bool_sig (sigof (u1::NewType «ind» 0::ctxt))` by
    metis_tac[is_bool_sig_extends] >>
  qspecl_then[`b2`,`u1::NewType «ind» 0::ctxt`]mp_tac ONTO_def_updates >>
  impl_tac >- (fs[IN_DISJOINT,Abbr`u1`] >> metis_tac[]) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac`u2 updates (u1::NewType «ind» 0::ctxt)` >>
  `(u2::u1::NewType «ind» 0::ctxt) extends ctxt` by
    (irule extends_CONS_I >> conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  `theory_ok (thyof (u2::u1::NewType «ind» 0::ctxt))` by
    metis_tac[updates_theory_ok] >>
  `is_bool_sig (sigof (u2::u1::NewType «ind» 0::ctxt))` by
    metis_tac[is_bool_sig_extends] >>
  (* and finally the axiom *)
  `NewAxiom (Exists «f» (Fun Ind Ind) (And (One_One h) (Not (Onto h))))
     updates (u2::u1::NewType «ind» 0::ctxt)` by
    (irule infinity_ax_updates >>
     simp[Abbr`u1`,Abbr`u2`,FLOOKUP_UPDATE]) >>
  `(NewAxiom (Exists «f» (Fun Ind Ind) (And (One_One h) (Not (Onto h))))::
      u2::u1::NewType «ind» 0::ctxt) extends ctxt` by
    (irule extends_CONS_I >> conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  fs[mk_infinity_ctxt_hl_def,Abbr`u1`,Abbr`u2`]
QED

Theorem init_light_nonempty:
  ∃ctxt. ctxt extends init_ctxt ∧ axiom_free ctxt
Proof
  qexists_tac`init_ctxt` >> simp[extends_def] >> EVAL_TAC >> simp[]
QED

(* the shapes with nothing interleaved anywhere *)

Theorem fhol_light_base_extends[local]:
  mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)) extends
  init_ctxt ∧
  is_bool_sig (sigof (mk_select_ctxt_cl (mk_eta_ctxt_cl
    (mk_bool_ctxt init_ctxt))))
Proof
  `is_std_sig (sigof init_ctxt)` by EVAL_TAC >>
  `is_bool_sig (sigof (mk_bool_ctxt init_ctxt))` by
    metis_tac[bool_has_bool_sig] >>
  `mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt) extends mk_bool_ctxt init_ctxt` by
    metis_tac[eta_cl_extends] >>
  `is_bool_sig (sigof (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))` by
    metis_tac[is_bool_sig_extends] >>
  `«@» ∉ FDOM (tmsof (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))` by EVAL_TAC >>
  `mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)) extends
   mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)` by metis_tac[select_cl_extends] >>
  conj_asm1_tac
  >- metis_tac[extends_trans,bool_extends_init] >>
  metis_tac[is_bool_sig_extends,bool_extends_init,extends_trans]
QED

Theorem fhol_light_nonempty:
  ∃ctxt. ctxt extends init_ctxt ∧ fhol_light_ctxt ctxt
Proof
  qexists_tac`mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt))` >>
  simp[fhol_light_base_extends,fhol_light_ctxt_def] >>
  qexists_tac`[]` >> qexists_tac`[]` >> qexists_tac`[]` >> simp[]
QED

Theorem hol_light_nonempty:
  ∃ctxt. ctxt extends init_ctxt ∧ hol_light_ctxt ctxt
Proof
  qexists_tac`mk_infinity_ctxt_hl «b1» «b2»
    (mk_select_ctxt_cl (mk_eta_ctxt_cl (mk_bool_ctxt init_ctxt)))` >>
  assume_tac fhol_light_base_extends >>
  `theory_ok (thyof (mk_select_ctxt_cl (mk_eta_ctxt_cl
     (mk_bool_ctxt init_ctxt))))` by
    metis_tac[extends_theory_ok,init_theory_ok] >>
  `DISJOINT (FDOM (tmsof (mk_select_ctxt_cl (mk_eta_ctxt_cl
     (mk_bool_ctxt init_ctxt))))) {«ONE_ONE»;«ONTO»}` by EVAL_TAC >>
  `«ind» ∉ FDOM (tysof (mk_select_ctxt_cl (mk_eta_ctxt_cl
     (mk_bool_ctxt init_ctxt))))` by EVAL_TAC >>
  conj_tac
  >- metis_tac[extends_trans,infinity_hl_extends] >>
  simp[hol_light_ctxt_def] >>
  qexists_tac`[]` >> qexists_tac`[]` >> qexists_tac`[]` >>
  qexists_tac`[]` >> qexists_tac`«b1»` >> qexists_tac`«b2»` >> simp[]
QED

(* ------------------------------------------------------------------------
   The measured context.

   What follows is the first 42 updates - newest first, so the oldest
   position 1 is last - of the record the Candle kernel printed for a
   session that loaded core HOL Light. It is a mechanical retranslation of
   that record's s-expressions through the grammar of print_thm, so the
   theorems below compare the definitions above against the kernel's own
   output rather than against a hand-written guess. Beyond position 42 the
   session declares no further axiom.

   The two generated binder names are the only session-dependent part.
   ------------------------------------------------------------------------ *)

Definition measured_prefix_def:
  measured_prefix =
    (* 42 *)
    [ NewAxiom (Comb (Const «?» (Tyapp «fun» [Tyapp «fun» [Tyapp «fun»
      [Tyapp «ind» []; Tyapp «ind» []]; Tyapp «bool» []]; Tyapp «bool» []]))
      (Abs (Var «f» (Tyapp «fun» [Tyapp «ind» []; Tyapp «ind» []])) (Comb
      (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Comb (Const «ONE_ONE» (Tyapp «fun»
      [Tyapp «fun» [Tyapp «ind» []; Tyapp «ind» []]; Tyapp «bool» []])) (Var
      «f» (Tyapp «fun» [Tyapp «ind» []; Tyapp «ind» []])))) (Comb (Const «~»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []])) (Comb (Const «ONTO»
      (Tyapp «fun» [Tyapp «fun» [Tyapp «ind» []; Tyapp «ind» []]; Tyapp
      «bool» []])) (Var «f» (Tyapp «fun» [Tyapp «ind» []; Tyapp «ind»
      []])))))))
    (* 41 *)
    ; ConstSpec [(«ONTO»,Abs (Var «_2045» (Tyapp «fun» [Tyvar «A»; Tyvar
      «B»])) (Comb (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp
      «bool» []]; Tyapp «bool» []])) (Abs (Var «y» (Tyvar «B»)) (Comb (Const
      «?» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp
      «bool» []])) (Abs (Var «x» (Tyvar «A»)) (Comb (Comb (Const «=» (Tyapp
      «fun» [Tyvar «B»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Var «y»
      (Tyvar «B»))) (Comb (Var «_2045» (Tyapp «fun» [Tyvar «A»; Tyvar «B»]))
      (Var «x» (Tyvar «A»)))))))))] (Comb (Comb (Const «=» (Tyapp «fun»
      [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «B»]; Tyapp «bool» []];
      Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «B»]; Tyapp
      «bool» []]; Tyapp «bool» []]])) (Var «ONTO» (Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyvar «B»]; Tyapp «bool» []]))) (Abs (Var «_2045» (Tyapp
      «fun» [Tyvar «A»; Tyvar «B»])) (Comb (Const «!» (Tyapp «fun» [Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «y»
      (Tyvar «B»)) (Comb (Const «?» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «x» (Tyvar «A»)) (Comb
      (Comb (Const «=» (Tyapp «fun» [Tyvar «B»; Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]])) (Var «y» (Tyvar «B»))) (Comb (Var «_2045» (Tyapp
      «fun» [Tyvar «A»; Tyvar «B»])) (Var «x» (Tyvar «A»))))))))))
    (* 40 *)
    ; ConstSpec [(«ONE_ONE»,Abs (Var «_2040» (Tyapp «fun» [Tyvar «A»; Tyvar
      «B»])) (Comb (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp
      «bool» []]; Tyapp «bool» []])) (Abs (Var «x1» (Tyvar «A»)) (Comb
      (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []];
      Tyapp «bool» []])) (Abs (Var «x2» (Tyvar «A»)) (Comb (Comb (Const
      «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar «B»;
      Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Comb (Var «_2040» (Tyapp
      «fun» [Tyvar «A»; Tyvar «B»])) (Var «x1» (Tyvar «A»)))) (Comb (Var
      «_2040» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Var «x2» (Tyvar
      «A»))))) (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]])) (Var «x1» (Tyvar «A»))) (Var «x2»
      (Tyvar «A»)))))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyvar «B»]; Tyapp «bool» []]; Tyapp «fun»
      [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «B»]; Tyapp «bool» []];
      Tyapp «bool» []]])) (Var «ONE_ONE» (Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyvar «B»]; Tyapp «bool» []]))) (Abs (Var «_2040» (Tyapp «fun»
      [Tyvar «A»; Tyvar «B»])) (Comb (Const «!» (Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «x1» (Tyvar
      «A»)) (Comb (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp
      «bool» []]; Tyapp «bool» []])) (Abs (Var «x2» (Tyvar «A»)) (Comb (Comb
      (Const «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar
      «B»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Comb (Var «_2040»
      (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Var «x1» (Tyvar «A»)))) (Comb
      (Var «_2040» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Var «x2» (Tyvar
      «A»))))) (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]])) (Var «x1» (Tyvar «A»))) (Var «x2»
      (Tyvar «A»))))))))))
    (* 39 *)
    ; NewType «ind» 0
    (* 38 *)
    ; ConstSpec [(«PASSOC»,Abs (Var «_1297» (Tyapp «fun» [Tyapp «prod»
      [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»]; Tyvar «D»])) (Abs
      (Var «_1298» (Tyapp «prod» [Tyvar «A»; Tyapp «prod» [Tyvar «B»; Tyvar
      «C»]])) (Comb (Var «_1297» (Tyapp «fun» [Tyapp «prod» [Tyapp «prod»
      [Tyvar «A»; Tyvar «B»]; Tyvar «C»]; Tyvar «D»])) (Comb (Comb (Const
      «,» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyapp «fun»
      [Tyvar «C»; Tyapp «prod» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar
      «C»]]])) (Comb (Comb (Const «,» (Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «B»; Tyapp «prod» [Tyvar «A»; Tyvar «B»]]])) (Comb (Const «FST»
      (Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyapp «prod» [Tyvar «B»; Tyvar
      «C»]]; Tyvar «A»])) (Var «_1298» (Tyapp «prod» [Tyvar «A»; Tyapp
      «prod» [Tyvar «B»; Tyvar «C»]])))) (Comb (Const «FST» (Tyapp «fun»
      [Tyapp «prod» [Tyvar «B»; Tyvar «C»]; Tyvar «B»])) (Comb (Const «SND»
      (Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyapp «prod» [Tyvar «B»; Tyvar
      «C»]]; Tyapp «prod» [Tyvar «B»; Tyvar «C»]])) (Var «_1298» (Tyapp
      «prod» [Tyvar «A»; Tyapp «prod» [Tyvar «B»; Tyvar «C»]])))))) (Comb
      (Const «SND» (Tyapp «fun» [Tyapp «prod» [Tyvar «B»; Tyvar «C»]; Tyvar
      «C»])) (Comb (Const «SND» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyapp
      «prod» [Tyvar «B»; Tyvar «C»]]; Tyapp «prod» [Tyvar «B»; Tyvar «C»]]))
      (Var «_1298» (Tyapp «prod» [Tyvar «A»; Tyapp «prod» [Tyvar «B»; Tyvar
      «C»]]))))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «fun» [Tyapp «prod» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»];
      Tyvar «D»]; Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyapp «prod» [Tyvar
      «B»; Tyvar «C»]]; Tyvar «D»]]; Tyapp «fun» [Tyapp «fun» [Tyapp «fun»
      [Tyapp «prod» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»]; Tyvar
      «D»]; Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyapp «prod» [Tyvar «B»;
      Tyvar «C»]]; Tyvar «D»]]; Tyapp «bool» []]])) (Var «PASSOC» (Tyapp
      «fun» [Tyapp «fun» [Tyapp «prod» [Tyapp «prod» [Tyvar «A»; Tyvar «B»];
      Tyvar «C»]; Tyvar «D»]; Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyapp
      «prod» [Tyvar «B»; Tyvar «C»]]; Tyvar «D»]]))) (Abs (Var «_1297»
      (Tyapp «fun» [Tyapp «prod» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar
      «C»]; Tyvar «D»])) (Abs (Var «_1298» (Tyapp «prod» [Tyvar «A»; Tyapp
      «prod» [Tyvar «B»; Tyvar «C»]])) (Comb (Var «_1297» (Tyapp «fun»
      [Tyapp «prod» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»]; Tyvar
      «D»])) (Comb (Comb (Const «,» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]; Tyapp «fun» [Tyvar «C»; Tyapp «prod» [Tyapp «prod» [Tyvar
      «A»; Tyvar «B»]; Tyvar «C»]]])) (Comb (Comb (Const «,» (Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «prod» [Tyvar «A»; Tyvar
      «B»]]])) (Comb (Const «FST» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»;
      Tyapp «prod» [Tyvar «B»; Tyvar «C»]]; Tyvar «A»])) (Var «_1298» (Tyapp
      «prod» [Tyvar «A»; Tyapp «prod» [Tyvar «B»; Tyvar «C»]])))) (Comb
      (Const «FST» (Tyapp «fun» [Tyapp «prod» [Tyvar «B»; Tyvar «C»]; Tyvar
      «B»])) (Comb (Const «SND» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyapp
      «prod» [Tyvar «B»; Tyvar «C»]]; Tyapp «prod» [Tyvar «B»; Tyvar «C»]]))
      (Var «_1298» (Tyapp «prod» [Tyvar «A»; Tyapp «prod» [Tyvar «B»; Tyvar
      «C»]])))))) (Comb (Const «SND» (Tyapp «fun» [Tyapp «prod» [Tyvar «B»;
      Tyvar «C»]; Tyvar «C»])) (Comb (Const «SND» (Tyapp «fun» [Tyapp «prod»
      [Tyvar «A»; Tyapp «prod» [Tyvar «B»; Tyvar «C»]]; Tyapp «prod» [Tyvar
      «B»; Tyvar «C»]])) (Var «_1298» (Tyapp «prod» [Tyvar «A»; Tyapp «prod»
      [Tyvar «B»; Tyvar «C»]])))))))))
    (* 37 *)
    ; ConstSpec [(«UNCURRY»,Abs (Var «_1280» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyvar «C»]])) (Abs (Var «_1281» (Tyapp «prod» [Tyvar
      «A»; Tyvar «B»])) (Comb (Comb (Var «_1280» (Tyapp «fun» [Tyvar «A»;
      Tyapp «fun» [Tyvar «B»; Tyvar «C»]])) (Comb (Const «FST» (Tyapp «fun»
      [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «A»])) (Var «_1281» (Tyapp
      «prod» [Tyvar «A»; Tyvar «B»])))) (Comb (Const «SND» (Tyapp «fun»
      [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «B»])) (Var «_1281» (Tyapp
      «prod» [Tyvar «A»; Tyvar «B»]))))))] (Comb (Comb (Const «=» (Tyapp
      «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»;
      Tyvar «C»]]; Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar
      «C»]]; Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «B»; Tyvar «C»]]; Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar
      «B»]; Tyvar «C»]]; Tyapp «bool» []]])) (Var «UNCURRY» (Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyvar «C»]]; Tyapp
      «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»]]))) (Abs (Var
      «_1280» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyvar «C»]]))
      (Abs (Var «_1281» (Tyapp «prod» [Tyvar «A»; Tyvar «B»])) (Comb (Comb
      (Var «_1280» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyvar
      «C»]])) (Comb (Const «FST» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]; Tyvar «A»])) (Var «_1281» (Tyapp «prod» [Tyvar «A»; Tyvar
      «B»])))) (Comb (Const «SND» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]; Tyvar «B»])) (Var «_1281» (Tyapp «prod» [Tyvar «A»; Tyvar
      «B»])))))))
    (* 36 *)
    ; ConstSpec [(«CURRY»,Abs (Var «_1259» (Tyapp «fun» [Tyapp «prod» [Tyvar
      «A»; Tyvar «B»]; Tyvar «C»])) (Abs (Var «_1260» (Tyvar «A»)) (Abs (Var
      «_1261» (Tyvar «B»)) (Comb (Var «_1259» (Tyapp «fun» [Tyapp «prod»
      [Tyvar «A»; Tyvar «B»]; Tyvar «C»])) (Comb (Comb (Const «,» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]]])) (Var «_1260» (Tyvar «A»))) (Var «_1261» (Tyvar
      «B»)))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»]; Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyvar «C»]]]; Tyapp «fun» [Tyapp
      «fun» [Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»];
      Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyvar «C»]]]; Tyapp
      «bool» []]])) (Var «CURRY» (Tyapp «fun» [Tyapp «fun» [Tyapp «prod»
      [Tyvar «A»; Tyvar «B»]; Tyvar «C»]; Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyvar «C»]]]))) (Abs (Var «_1259» (Tyapp «fun»
      [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»])) (Abs (Var «_1260»
      (Tyvar «A»)) (Abs (Var «_1261» (Tyvar «B»)) (Comb (Var «_1259» (Tyapp
      «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar «C»])) (Comb (Comb
      (Const «,» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp
      «prod» [Tyvar «A»; Tyvar «B»]]])) (Var «_1260» (Tyvar «A»))) (Var
      «_1261» (Tyvar «B»))))))))
    (* 35 *)
    ; ConstSpec [(«SND»,Abs (Var «p» (Tyapp «prod» [Tyvar «A»; Tyvar «B»]))
      (Comb (Const «@» (Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool»
      []]; Tyvar «B»])) (Abs (Var «y» (Tyvar «B»)) (Comb (Const «?» (Tyapp
      «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []]))
      (Abs (Var «x» (Tyvar «A»)) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp
      «prod» [Tyvar «A»; Tyvar «B»]; Tyapp «fun» [Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]; Tyapp «bool» []]])) (Var «p» (Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]))) (Comb (Comb (Const «,» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «prod» [Tyvar «A»; Tyvar «B»]]])) (Var «x»
      (Tyvar «A»))) (Var «y» (Tyvar «B»)))))))))] (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar
      «B»]; Tyapp «fun» [Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»];
      Tyvar «B»]; Tyapp «bool» []]])) (Var «SND» (Tyapp «fun» [Tyapp «prod»
      [Tyvar «A»; Tyvar «B»]; Tyvar «B»]))) (Abs (Var «p» (Tyapp «prod»
      [Tyvar «A»; Tyvar «B»])) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun»
      [Tyvar «B»; Tyapp «bool» []]; Tyvar «B»])) (Abs (Var «y» (Tyvar «B»))
      (Comb (Const «?» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []]; Tyapp «bool» []])) (Abs (Var «x» (Tyvar «A»)) (Comb (Comb (Const
      «=» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyapp «fun»
      [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyapp «bool» []]])) (Var «p»
      (Tyapp «prod» [Tyvar «A»; Tyvar «B»]))) (Comb (Comb (Const «,» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]]])) (Var «x» (Tyvar «A»))) (Var «y» (Tyvar «B»))))))))))
    (* 34 *)
    ; ConstSpec [(«FST»,Abs (Var «p» (Tyapp «prod» [Tyvar «A»; Tyvar «B»]))
      (Comb (Const «@» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []]; Tyvar «A»])) (Abs (Var «x» (Tyvar «A»)) (Comb (Const «?» (Tyapp
      «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «bool» []]))
      (Abs (Var «y» (Tyvar «B»)) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp
      «prod» [Tyvar «A»; Tyvar «B»]; Tyapp «fun» [Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]; Tyapp «bool» []]])) (Var «p» (Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]))) (Comb (Comb (Const «,» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «prod» [Tyvar «A»; Tyvar «B»]]])) (Var «x»
      (Tyvar «A»))) (Var «y» (Tyvar «B»)))))))))] (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyvar
      «A»]; Tyapp «fun» [Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»];
      Tyvar «A»]; Tyapp «bool» []]])) (Var «FST» (Tyapp «fun» [Tyapp «prod»
      [Tyvar «A»; Tyvar «B»]; Tyvar «A»]))) (Abs (Var «p» (Tyapp «prod»
      [Tyvar «A»; Tyvar «B»])) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]; Tyvar «A»])) (Abs (Var «x» (Tyvar «A»))
      (Comb (Const «?» (Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool»
      []]; Tyapp «bool» []])) (Abs (Var «y» (Tyvar «B»)) (Comb (Comb (Const
      «=» (Tyapp «fun» [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyapp «fun»
      [Tyapp «prod» [Tyvar «A»; Tyvar «B»]; Tyapp «bool» []]])) (Var «p»
      (Tyapp «prod» [Tyvar «A»; Tyvar «B»]))) (Comb (Comb (Const «,» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]]])) (Var «x» (Tyvar «A»))) (Var «y» (Tyvar «B»))))))))))
    (* 33 *)
    ; ConstSpec [(«,»,Abs (Var «x» (Tyvar «A»)) (Abs (Var «y» (Tyvar «B»))
      (Comb (Const «ABS_prod» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyapp «prod» [Tyvar «A»; Tyvar
      «B»]])) (Comb (Comb (Const «mk_pair» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]]]])) (Var «x» (Tyvar «A»))) (Var «y» (Tyvar
      «B»))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyapp «fun» [Tyvar «B»; Tyapp «prod» [Tyvar «A»; Tyvar «B»]]];
      Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp
      «prod» [Tyvar «A»; Tyvar «B»]]]; Tyapp «bool» []]])) (Var «,» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «prod» [Tyvar «A»;
      Tyvar «B»]]]))) (Abs (Var «x» (Tyvar «A»)) (Abs (Var «y» (Tyvar «B»))
      (Comb (Const «ABS_prod» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyapp «prod» [Tyvar «A»; Tyvar
      «B»]])) (Comb (Comb (Const «mk_pair» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]]]])) (Var «x» (Tyvar «A»))) (Var «y» (Tyvar
      «B»)))))))
    (* 32 *)
    ; TypeDefn «prod» (Abs (Var «x» (Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «B»; Tyapp «bool» []]])) (Comb (Const «?» (Tyapp «fun» [Tyapp
      «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «a»
      (Tyvar «A»)) (Comb (Const «?» (Tyapp «fun» [Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «b» (Tyvar «B»)) (Comb
      (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «B»; Tyapp «bool» []]]; Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyapp «bool» []]])) (Var
      «x» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool»
      []]]))) (Comb (Comb (Const «mk_pair» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]]]])) (Var «a» (Tyvar «A»))) (Var «b» (Tyvar
      «B»))))))))) «ABS_prod» «REP_prod»
    (* 31 *)
    ; ConstSpec [(«mk_pair»,Abs (Var «x» (Tyvar «A»)) (Abs (Var «y» (Tyvar
      «B»)) (Abs (Var «a» (Tyvar «A»)) (Abs (Var «b» (Tyvar «B»)) (Comb
      (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Comb (Comb (Const «=» (Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]])) (Var «a»
      (Tyvar «A»))) (Var «x» (Tyvar «A»)))) (Comb (Comb (Const «=» (Tyapp
      «fun» [Tyvar «B»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Var «b»
      (Tyvar «B»))) (Var «y» (Tyvar «B»))))))))] (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]]]; Tyapp
      «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]]]; Tyapp «bool»
      []]])) (Var «mk_pair» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»;
      Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]]])))
      (Abs (Var «x» (Tyvar «A»)) (Abs (Var «y» (Tyvar «B»)) (Abs (Var «a»
      (Tyvar «A»)) (Abs (Var «b» (Tyvar «B»)) (Comb (Comb (Const «/\\»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «A»; Tyapp «bool» []]])) (Var «a» (Tyvar «A»))) (Var «x»
      (Tyvar «A»)))) (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar «B»; Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]])) (Var «b» (Tyvar «B»))) (Var «y»
      (Tyvar «B»)))))))))
    (* 30 *)
    ; ConstSpec [(«_FUNCTION»,Abs (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]])) (Abs (Var «x» (Tyvar «A»)) (Comb
      (Comb (Comb (Const «COND» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyvar «B»; Tyapp «fun» [Tyvar «B»; Tyvar «B»]]])) (Comb (Const «?!»
      (Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «bool»
      []])) (Comb (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]])) (Var «x» (Tyvar «A»))))) (Comb (Const «@» (Tyapp
      «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]; Tyvar «B»])) (Comb
      (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool»
      []]])) (Var «x» (Tyvar «A»))))) (Comb (Const «@» (Tyapp «fun» [Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]; Tyvar «B»])) (Abs (Var «z» (Tyvar
      «B»)) (Const «F» (Tyapp «bool» [])))))))] (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar
      «B»; Tyapp «bool» []]]; Tyapp «fun» [Tyvar «A»; Tyvar «B»]]; Tyapp
      «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]]; Tyapp «fun» [Tyvar «A»; Tyvar «B»]]; Tyapp «bool»
      []]])) (Var «_FUNCTION» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyapp «fun» [Tyvar «A»; Tyvar
      «B»]]))) (Abs (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar
      «B»; Tyapp «bool» []]])) (Abs (Var «x» (Tyvar «A»)) (Comb (Comb (Comb
      (Const «COND» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyvar «B»;
      Tyapp «fun» [Tyvar «B»; Tyvar «B»]]])) (Comb (Const «?!» (Tyapp «fun»
      [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «bool» []])) (Comb
      (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool»
      []]])) (Var «x» (Tyvar «A»))))) (Comb (Const «@» (Tyapp «fun» [Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]; Tyvar «B»])) (Comb (Var «r» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Var «x»
      (Tyvar «A»))))) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]; Tyvar «B»])) (Abs (Var «z» (Tyvar «B»)) (Const «F»
      (Tyapp «bool» []))))))))
    (* 29 *)
    ; ConstSpec [(«_MATCH»,Abs (Var «e» (Tyvar «A»)) (Abs (Var «r» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Comb
      (Comb (Comb (Const «COND» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyvar «B»; Tyapp «fun» [Tyvar «B»; Tyvar «B»]]])) (Comb (Const «?!»
      (Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «bool»
      []])) (Comb (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]])) (Var «e» (Tyvar «A»))))) (Comb (Const «@» (Tyapp
      «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]; Tyvar «B»])) (Comb
      (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool»
      []]])) (Var «e» (Tyvar «A»))))) (Comb (Const «@» (Tyapp «fun» [Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]; Tyvar «B»])) (Abs (Var «z» (Tyvar
      «B»)) (Const «F» (Tyapp «bool» [])))))))] (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyvar «B»]]; Tyapp
      «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyvar «B»]]; Tyapp «bool»
      []]])) (Var «_MATCH» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyvar «B»]])))
      (Abs (Var «e» (Tyvar «A»)) (Abs (Var «r» (Tyapp «fun» [Tyvar «A»;
      Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Comb (Comb (Comb (Const
      «COND» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyvar «B»; Tyapp
      «fun» [Tyvar «B»; Tyvar «B»]]])) (Comb (Const «?!» (Tyapp «fun» [Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «bool» []])) (Comb (Var «r»
      (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]))
      (Var «e» (Tyvar «A»))))) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun»
      [Tyvar «B»; Tyapp «bool» []]; Tyvar «B»])) (Comb (Var «r» (Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Var «e»
      (Tyvar «A»))))) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]; Tyvar «B»])) (Abs (Var «z» (Tyvar «B»)) (Const «F»
      (Tyapp «bool» []))))))))
    (* 28 *)
    ; ConstSpec [(«_GUARDED_PATTERN»,Abs (Var «p» (Tyapp «bool» [])) (Abs
      (Var «g» (Tyapp «bool» [])) (Abs (Var «r» (Tyapp «bool» [])) (Comb
      (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Var «p» (Tyapp «bool» []))) (Comb
      (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Var «g» (Tyapp «bool» []))) (Var «r»
      (Tyapp «bool» [])))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp
      «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]]]; Tyapp «fun» [Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]]]; Tyapp «bool» []]])) (Var «_GUARDED_PATTERN» (Tyapp
      «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]]]))) (Abs (Var «p» (Tyapp «bool»
      [])) (Abs (Var «g» (Tyapp «bool» [])) (Abs (Var «r» (Tyapp «bool» []))
      (Comb (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]])) (Var «p» (Tyapp «bool» [])))
      (Comb (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]])) (Var «g» (Tyapp «bool» [])))
      (Var «r» (Tyapp «bool» []))))))))
    (* 27 *)
    ; ConstSpec [(«_UNGUARDED_PATTERN»,Abs (Var «p» (Tyapp «bool» [])) (Abs
      (Var «r» (Tyapp «bool» [])) (Comb (Comb (Const «/\\» (Tyapp «fun»
      [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]))
      (Var «p» (Tyapp «bool» []))) (Var «r» (Tyapp «bool» [])))))] (Comb
      (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp «bool» []; Tyapp
      «fun» [Tyapp «bool» []; Tyapp «bool» []]]; Tyapp «fun» [Tyapp «fun»
      [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]];
      Tyapp «bool» []]])) (Var «_UNGUARDED_PATTERN» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]))) (Abs
      (Var «p» (Tyapp «bool» [])) (Abs (Var «r» (Tyapp «bool» [])) (Comb
      (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Var «p» (Tyapp «bool» []))) (Var «r»
      (Tyapp «bool» []))))))
    (* 26 *)
    ; ConstSpec [(«_SEQPATTERN»,Abs (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]])) (Abs (Var «s» (Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Abs (Var «x»
      (Tyvar «A»)) (Comb (Comb (Comb (Const «COND» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []];
      Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «fun»
      [Tyvar «B»; Tyapp «bool» []]]]])) (Comb (Const «?» (Tyapp «fun» [Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «y»
      (Tyvar «B»)) (Comb (Comb (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «B»; Tyapp «bool» []]])) (Var «x» (Tyvar «A»))) (Var «y» (Tyvar
      «B»)))))) (Comb (Var «r» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar
      «B»; Tyapp «bool» []]])) (Var «x» (Tyvar «A»)))) (Comb (Var «s» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Var «x»
      (Tyvar «A»)))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]];
      Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp
      «bool» []]]; Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp
      «bool» []]]]]; Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp
      «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyapp «fun» [Tyvar
      «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]]]; Tyapp «bool» []]]))
      (Var «_SEQPATTERN» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «B»; Tyapp «bool» []]]; Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]; Tyapp «fun» [Tyvar «A»;
      Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]]]))) (Abs (Var «r» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Abs
      (Var «s» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool»
      []]])) (Abs (Var «x» (Tyvar «A»)) (Comb (Comb (Comb (Const «COND»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «fun» [Tyvar «B»;
      Tyapp «bool» []]; Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool»
      []]; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]]]])) (Comb (Const «?»
      (Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]; Tyapp «bool»
      []])) (Abs (Var «y» (Tyvar «B»)) (Comb (Comb (Var «r» (Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Var «x»
      (Tyvar «A»))) (Var «y» (Tyvar «B»)))))) (Comb (Var «r» (Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «B»; Tyapp «bool» []]])) (Var «x»
      (Tyvar «A»)))) (Comb (Var «s» (Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «B»; Tyapp «bool» []]])) (Var «x» (Tyvar «A»))))))))
    (* 25 *)
    ; ConstSpec [(«GEQ»,Abs (Var «a» (Tyvar «A»)) (Abs (Var «b» (Tyvar «A»))
      (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar
      «A»; Tyapp «bool» []]])) (Var «a» (Tyvar «A»))) (Var «b» (Tyvar
      «A»)))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]]; Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]]; Tyapp «bool»
      []]])) (Var «GEQ» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []]]))) (Abs (Var «a» (Tyvar «A»)) (Abs (Var «b» (Tyvar
      «A»)) (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar «A»; Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]])) (Var «a» (Tyvar «A»))) (Var «b» (Tyvar
      «A»))))))
    (* 24 *)
    ; ConstSpec [(«GABS»,Abs (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []])) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp
      «bool» []]; Tyvar «A»])) (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp
      «bool» []]))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyvar «A»]; Tyapp «fun»
      [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyvar «A»];
      Tyapp «bool» []]])) (Var «GABS» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []]; Tyvar «A»]))) (Abs (Var «P» (Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []])) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyapp «bool» []]; Tyvar «A»])) (Var «P» (Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []])))))
    (* 23 *)
    ; ConstSpec [(«LET_END»,Abs (Var «t» (Tyvar «A»)) (Var «t» (Tyvar
      «A»)))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyvar «A»]; Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «A»]; Tyapp
      «bool» []]])) (Var «LET_END» (Tyapp «fun» [Tyvar «A»; Tyvar «A»])))
      (Abs (Var «t» (Tyvar «A»)) (Var «t» (Tyvar «A»))))
    (* 22 *)
    ; ConstSpec [(«LET»,Abs (Var «f» (Tyapp «fun» [Tyvar «A»; Tyvar «B»]))
      (Abs (Var «x» (Tyvar «A»)) (Comb (Var «f» (Tyapp «fun» [Tyvar «A»;
      Tyvar «B»])) (Var «x» (Tyvar «A»)))))] (Comb (Comb (Const «=» (Tyapp
      «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «B»]; Tyapp «fun»
      [Tyvar «A»; Tyvar «B»]]; Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyvar «B»]; Tyapp «fun» [Tyvar «A»; Tyvar «B»]]; Tyapp «bool»
      []]])) (Var «LET» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «B»];
      Tyapp «fun» [Tyvar «A»; Tyvar «B»]]))) (Abs (Var «f» (Tyapp «fun»
      [Tyvar «A»; Tyvar «B»])) (Abs (Var «x» (Tyvar «A»)) (Comb (Var «f»
      (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Var «x» (Tyvar «A»))))))
    (* 21 *)
    ; ConstSpec [(«one»,Comb (Const «@» (Tyapp «fun» [Tyapp «fun» [Tyapp «1»
      []; Tyapp «bool» []]; Tyapp «1» []])) (Abs (Var «x» (Tyapp «1» []))
      (Const «T» (Tyapp «bool» []))))] (Comb (Comb (Const «=» (Tyapp «fun»
      [Tyapp «1» []; Tyapp «fun» [Tyapp «1» []; Tyapp «bool» []]])) (Var
      «one» (Tyapp «1» []))) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun»
      [Tyapp «1» []; Tyapp «bool» []]; Tyapp «1» []])) (Abs (Var «x» (Tyapp
      «1» [])) (Const «T» (Tyapp «bool» [])))))
    (* 20 *)
    ; TypeDefn «1» (Abs (Var «b» (Tyapp «bool» [])) (Var «b» (Tyapp «bool»
      []))) «one_ABS» «one_REP»
    (* 19 *)
    ; ConstSpec [(«I»,Abs (Var «x» (Tyvar «A»)) (Var «x» (Tyvar «A»)))]
      (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar
      «A»]; Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «A»]; Tyapp «bool»
      []]])) (Var «I» (Tyapp «fun» [Tyvar «A»; Tyvar «A»]))) (Abs (Var «x»
      (Tyvar «A»)) (Var «x» (Tyvar «A»))))
    (* 18 *)
    ; ConstSpec [(«o»,Abs (Var «f» (Tyapp «fun» [Tyvar «B»; Tyvar «C»]))
      (Abs (Var «g» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Abs (Var «x»
      (Tyvar «A»)) (Comb (Var «f» (Tyapp «fun» [Tyvar «B»; Tyvar «C»]))
      (Comb (Var «g» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Var «x» (Tyvar
      «A»)))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «fun» [Tyvar «B»; Tyvar «C»]; Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyvar «B»]; Tyapp «fun» [Tyvar «A»; Tyvar «C»]]]; Tyapp «fun» [Tyapp
      «fun» [Tyapp «fun» [Tyvar «B»; Tyvar «C»]; Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyvar «B»]; Tyapp «fun» [Tyvar «A»; Tyvar «C»]]]; Tyapp
      «bool» []]])) (Var «o» (Tyapp «fun» [Tyapp «fun» [Tyvar «B»; Tyvar
      «C»]; Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «B»]; Tyapp «fun»
      [Tyvar «A»; Tyvar «C»]]]))) (Abs (Var «f» (Tyapp «fun» [Tyvar «B»;
      Tyvar «C»])) (Abs (Var «g» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Abs
      (Var «x» (Tyvar «A»)) (Comb (Var «f» (Tyapp «fun» [Tyvar «B»; Tyvar
      «C»])) (Comb (Var «g» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Var «x»
      (Tyvar «A»))))))))
    (* 17 *)
    ; ConstSpec [(«COND»,Abs (Var «t» (Tyapp «bool» [])) (Abs (Var «t1»
      (Tyvar «A»)) (Abs (Var «t2» (Tyvar «A»)) (Comb (Const «@» (Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyvar «A»])) (Abs (Var «x»
      (Tyvar «A»)) (Comb (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» [];
      Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Comb (Const
      «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «bool»
      []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Var «t» (Tyapp
      «bool» []))) (Const «T» (Tyapp «bool» [])))) (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]]))
      (Var «x» (Tyvar «A»))) (Var «t1» (Tyvar «A»))))) (Comb (Comb (Const
      «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «bool»
      []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Var «t» (Tyapp
      «bool» []))) (Const «F» (Tyapp «bool» [])))) (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]]))
      (Var «x» (Tyvar «A»))) (Var «t2» (Tyvar «A»))))))))))] (Comb (Comb
      (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyvar «A»]]]; Tyapp «fun» [Tyapp
      «fun» [Tyapp «bool» []; Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar
      «A»; Tyvar «A»]]]; Tyapp «bool» []]])) (Var «COND» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyvar
      «A»]]]))) (Abs (Var «t» (Tyapp «bool» [])) (Abs (Var «t1» (Tyvar «A»))
      (Abs (Var «t2» (Tyvar «A»)) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]; Tyvar «A»])) (Abs (Var «x» (Tyvar «A»))
      (Comb (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Comb (Const «==>» (Tyapp
      «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool»
      []]])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «bool» []; Tyapp
      «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Var «t» (Tyapp «bool»
      []))) (Const «T» (Tyapp «bool» [])))) (Comb (Comb (Const «=» (Tyapp
      «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]])) (Var «x»
      (Tyvar «A»))) (Var «t1» (Tyvar «A»))))) (Comb (Comb (Const «==>»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «bool» [];
      Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Var «t» (Tyapp
      «bool» []))) (Const «F» (Tyapp «bool» [])))) (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]]))
      (Var «x» (Tyvar «A»))) (Var «t2» (Tyvar «A»)))))))))))
    (* 16 *)
    ; NewAxiom (Comb (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []]; Tyapp «bool» []]))
      (Abs (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool» []])) (Comb (Const
      «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp
      «bool» []])) (Abs (Var «x» (Tyvar «A»)) (Comb (Comb (Const «==>»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Comb (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []])) (Var «x» (Tyvar «A»)))) (Comb (Var «P» (Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []])) (Comb (Const «@» (Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyapp «bool» []]; Tyvar «A»])) (Var «P» (Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []])))))))))
    (* 15 *)
    ; NewConst «@» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []];
      Tyvar «A»])
    (* 14 *)
    ; NewAxiom (Comb (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyvar «B»]; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var
      «t» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyvar «B»]; Tyapp «fun» [Tyapp
      «fun» [Tyvar «A»; Tyvar «B»]; Tyapp «bool» []]])) (Abs (Var «x» (Tyvar
      «A»)) (Comb (Var «t» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])) (Var «x»
      (Tyvar «A»))))) (Var «t» (Tyapp «fun» [Tyvar «A»; Tyvar «B»])))))
    (* 13 *)
    ; ConstSpec [(«_FALSITY_»,Const «F» (Tyapp «bool» []))] (Comb (Comb
      (Const «=» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]])) (Var «_FALSITY_» (Tyapp «bool» []))) (Const
      «F» (Tyapp «bool» [])))
    (* 12 *)
    ; ConstSpec [(«?!»,Abs (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []])) (Comb (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp
      «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Const «?» (Tyapp
      «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []]))
      (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool» []])))) (Comb (Const
      «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp
      «bool» []])) (Abs (Var «x» (Tyvar «A»)) (Comb (Const «!» (Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []])) (Abs
      (Var «y» (Tyvar «A»)) (Comb (Comb (Const «==>» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb
      (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Comb (Var «P» (Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []])) (Var «x» (Tyvar «A»)))) (Comb (Var «P» (Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []])) (Var «y» (Tyvar «A»))))) (Comb (Comb
      (Const «=» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyapp
      «bool» []]])) (Var «x» (Tyvar «A»))) (Var «y» (Tyvar «A»))))))))))]
      (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyapp «bool» []]; Tyapp «bool» []]; Tyapp «fun» [Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []]; Tyapp
      «bool» []]])) (Var «?!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp
      «bool» []]; Tyapp «bool» []]))) (Abs (Var «P» (Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []])) (Comb (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool»
      []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Const «?»
      (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool»
      []])) (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool» []])))) (Comb
      (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []];
      Tyapp «bool» []])) (Abs (Var «x» (Tyvar «A»)) (Comb (Const «!» (Tyapp
      «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []]))
      (Abs (Var «y» (Tyvar «A»)) (Comb (Comb (Const «==>» (Tyapp «fun»
      [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]))
      (Comb (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Var «P» (Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []])) (Var «x» (Tyvar «A»)))) (Comb (Var «P»
      (Tyapp «fun» [Tyvar «A»; Tyapp «bool» []])) (Var «y» (Tyvar «A»)))))
      (Comb (Comb (Const «=» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar
      «A»; Tyapp «bool» []]])) (Var «x» (Tyvar «A»))) (Var «y» (Tyvar
      «A»)))))))))))
    (* 11 *)
    ; ConstSpec [(«~»,Abs (Var «p» (Tyapp «bool» [])) (Comb (Comb (Const
      «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]])) (Var «p» (Tyapp «bool» []))) (Const «F» (Tyapp
      «bool» []))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]; Tyapp «fun» [Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]; Tyapp «bool» []]])) (Var «~» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]))) (Abs (Var «p» (Tyapp «bool» [])) (Comb
      (Comb (Const «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Var «p» (Tyapp «bool» []))) (Const «F»
      (Tyapp «bool» [])))))
    (* 10 *)
    ; ConstSpec [(«F»,Comb (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «p» (Tyapp
      «bool» [])) (Var «p» (Tyapp «bool» []))))] (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Var «F» (Tyapp «bool» []))) (Comb (Const «!» (Tyapp
      «fun» [Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]; Tyapp «bool»
      []])) (Abs (Var «p» (Tyapp «bool» [])) (Var «p» (Tyapp «bool» [])))))
    (*  9 *)
    ; ConstSpec [(«\\/»,Abs (Var «p» (Tyapp «bool» [])) (Abs (Var «q» (Tyapp
      «bool» [])) (Comb (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «r» (Tyapp «bool»
      [])) (Comb (Comb (Const «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp
      «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Comb (Const «==>»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Var «p» (Tyapp «bool» []))) (Var «r» (Tyapp «bool»
      [])))) (Comb (Comb (Const «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp
      «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Comb (Const «==>»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Var «q» (Tyapp «bool» []))) (Var «r» (Tyapp «bool»
      [])))) (Var «r» (Tyapp «bool» []))))))))] (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]]; Tyapp «fun» [Tyapp «fun» [Tyapp «bool» [];
      Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]; Tyapp «bool» []]]))
      (Var «\\/» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]]))) (Abs (Var «p» (Tyapp «bool» [])) (Abs (Var
      «q» (Tyapp «bool» [])) (Comb (Const «!» (Tyapp «fun» [Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «r»
      (Tyapp «bool» [])) (Comb (Comb (Const «==>» (Tyapp «fun» [Tyapp «bool»
      []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Comb
      (Const «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]])) (Var «p» (Tyapp «bool» []))) (Var «r» (Tyapp
      «bool» [])))) (Comb (Comb (Const «==>» (Tyapp «fun» [Tyapp «bool» [];
      Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Comb (Const
      «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]])) (Var «q» (Tyapp «bool» []))) (Var «r» (Tyapp
      «bool» [])))) (Var «r» (Tyapp «bool» [])))))))))
    (*  8 *)
    ; ConstSpec [(«?»,Abs (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []])) (Comb (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var «q» (Tyapp «bool» []))
      (Comb (Comb (Const «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Const «!» (Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []])) (Abs
      (Var «x» (Tyvar «A»)) (Comb (Comb (Const «==>» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb
      (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool» []])) (Var «x» (Tyvar
      «A»)))) (Var «q» (Tyapp «bool» [])))))) (Var «q» (Tyapp «bool»
      []))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []]; Tyapp «fun»
      [Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool»
      []]; Tyapp «bool» []]])) (Var «?» (Tyapp «fun» [Tyapp «fun» [Tyvar
      «A»; Tyapp «bool» []]; Tyapp «bool» []]))) (Abs (Var «P» (Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []])) (Comb (Const «!» (Tyapp «fun» [Tyapp
      «fun» [Tyapp «bool» []; Tyapp «bool» []]; Tyapp «bool» []])) (Abs (Var
      «q» (Tyapp «bool» [])) (Comb (Comb (Const «==>» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb
      (Const «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []];
      Tyapp «bool» []])) (Abs (Var «x» (Tyvar «A»)) (Comb (Comb (Const «==>»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Comb (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []])) (Var «x» (Tyvar «A»)))) (Var «q» (Tyapp «bool» [])))))) (Var «q»
      (Tyapp «bool» [])))))))
    (*  7 *)
    ; ConstSpec [(«!»,Abs (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []]; Tyapp «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool»
      []]; Tyapp «bool» []]])) (Var «P» (Tyapp «fun» [Tyvar «A»; Tyapp
      «bool» []]))) (Abs (Var «x» (Tyvar «A»)) (Const «T» (Tyapp «bool»
      [])))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []]; Tyapp «fun» [Tyapp
      «fun» [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []];
      Tyapp «bool» []]])) (Var «!» (Tyapp «fun» [Tyapp «fun» [Tyvar «A»;
      Tyapp «bool» []]; Tyapp «bool» []]))) (Abs (Var «P» (Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []])) (Comb (Comb (Const «=» (Tyapp «fun»
      [Tyapp «fun» [Tyvar «A»; Tyapp «bool» []]; Tyapp «fun» [Tyapp «fun»
      [Tyvar «A»; Tyapp «bool» []]; Tyapp «bool» []]])) (Var «P» (Tyapp
      «fun» [Tyvar «A»; Tyapp «bool» []]))) (Abs (Var «x» (Tyvar «A»))
      (Const «T» (Tyapp «bool» []))))))
    (*  6 *)
    ; ConstSpec [(«==>»,Abs (Var «p» (Tyapp «bool» [])) (Abs (Var «q» (Tyapp
      «bool» [])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «bool» [];
      Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Comb (Const
      «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]])) (Var «p» (Tyapp «bool» []))) (Var «q» (Tyapp
      «bool» [])))) (Var «p» (Tyapp «bool» [])))))] (Comb (Comb (Const «=»
      (Tyapp «fun» [Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]]; Tyapp «fun» [Tyapp «fun» [Tyapp «bool» [];
      Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]; Tyapp «bool» []]]))
      (Var «==>» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]]))) (Abs (Var «p» (Tyapp «bool» [])) (Abs (Var
      «q» (Tyapp «bool» [])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb
      (Comb (Const «/\\» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Var «p» (Tyapp «bool» []))) (Var «q»
      (Tyapp «bool» [])))) (Var «p» (Tyapp «bool» []))))))
    (*  5 *)
    ; ConstSpec [(«/\\»,Abs (Var «p» (Tyapp «bool» [])) (Abs (Var «q» (Tyapp
      «bool» [])) (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool»
      []]]; Tyapp «bool» []]; Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]; Tyapp
      «bool» []]; Tyapp «bool» []]])) (Abs (Var «f» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb
      (Comb (Var «f» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Var «p» (Tyapp «bool» []))) (Var «q»
      (Tyapp «bool» []))))) (Abs (Var «f» (Tyapp «fun» [Tyapp «bool» [];
      Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Comb (Comb (Var «f»
      (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Const «T» (Tyapp «bool» []))) (Const «T» (Tyapp «bool»
      [])))))))] (Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]; Tyapp
      «fun» [Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» [];
      Tyapp «bool» []]]; Tyapp «bool» []]])) (Var «/\\» (Tyapp «fun» [Tyapp
      «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]))) (Abs
      (Var «p» (Tyapp «bool» [])) (Abs (Var «q» (Tyapp «bool» [])) (Comb
      (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyapp «bool»
      []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]; Tyapp «bool» []];
      Tyapp «fun» [Tyapp «fun» [Tyapp «fun» [Tyapp «bool» []; Tyapp «fun»
      [Tyapp «bool» []; Tyapp «bool» []]]; Tyapp «bool» []]; Tyapp «bool»
      []]])) (Abs (Var «f» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]])) (Comb (Comb (Var «f» (Tyapp «fun»
      [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]))
      (Var «p» (Tyapp «bool» []))) (Var «q» (Tyapp «bool» []))))) (Abs (Var
      «f» (Tyapp «fun» [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp
      «bool» []]])) (Comb (Comb (Var «f» (Tyapp «fun» [Tyapp «bool» [];
      Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]])) (Const «T» (Tyapp
      «bool» []))) (Const «T» (Tyapp «bool» []))))))))
    (*  4 *)
    ; ConstSpec [(«T»,Comb (Comb (Const «=» (Tyapp «fun» [Tyapp «fun» [Tyapp
      «bool» []; Tyapp «bool» []]; Tyapp «fun» [Tyapp «fun» [Tyapp «bool»
      []; Tyapp «bool» []]; Tyapp «bool» []]])) (Abs (Var «p» (Tyapp «bool»
      [])) (Var «p» (Tyapp «bool» [])))) (Abs (Var «p» (Tyapp «bool» []))
      (Var «p» (Tyapp «bool» []))))] (Comb (Comb (Const «=» (Tyapp «fun»
      [Tyapp «bool» []; Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]]))
      (Var «T» (Tyapp «bool» []))) (Comb (Comb (Const «=» (Tyapp «fun»
      [Tyapp «fun» [Tyapp «bool» []; Tyapp «bool» []]; Tyapp «fun» [Tyapp
      «fun» [Tyapp «bool» []; Tyapp «bool» []]; Tyapp «bool» []]])) (Abs
      (Var «p» (Tyapp «bool» [])) (Var «p» (Tyapp «bool» [])))) (Abs (Var
      «p» (Tyapp «bool» [])) (Var «p» (Tyapp «bool» [])))))
    (*  3 *)
    ; NewConst «=» (Tyapp «fun» [Tyvar «A»; Tyapp «fun» [Tyvar «A»; Tyapp
      «bool» []]])
    (*  2 *)
    ; NewType «bool» 0
    (*  1 *)
    ; NewType «fun» 2
    ]
End

(* ------------------------------------------------------------------------
   Each block agrees with the kernel printout update for update. The index
   arithmetic reads the list newest first: positions 42-39 are the infinity
   block, 16-15 the select block, 14 the eta axiom, and 11-1 the booleans on
   top of the initial context.
   ------------------------------------------------------------------------ *)

Theorem measured_infinity_block:
  TAKE 4 measured_prefix = mk_infinity_ctxt_hl «_2040» «_2045» []
Proof
  EVAL_TAC
QED

Theorem measured_select_block:
  TAKE 2 (DROP 26 measured_prefix) = mk_select_ctxt_cl []
Proof
  EVAL_TAC
QED

Theorem measured_eta_block:
  TAKE 1 (DROP 28 measured_prefix) = mk_eta_ctxt_cl []
Proof
  EVAL_TAC
QED

Theorem measured_bool_block:
  DROP 31 measured_prefix = mk_bool_ctxt init_ctxt
Proof
  EVAL_TAC
QED

(* the four blocks compose, with positions 38-17 and 13-12 in between and
   nothing at all between the eta and select blocks *)

Theorem measured_prefix_decomposition:
  measured_prefix =
    mk_infinity_ctxt_hl «_2040» «_2045»
      (TAKE 22 (DROP 4 measured_prefix) ++
       mk_select_ctxt_cl
         (mk_eta_ctxt_cl
            (TAKE 2 (DROP 29 measured_prefix) ++ mk_bool_ctxt init_ctxt)))
Proof
  EVAL_TAC
QED

(* so the guarantee fires on the measured session: whatever the session goes
   on to define after position 42, as long as it declares no further axiom -
   and the record shows it does not - the context it reaches is one of the
   shapes above *)

Theorem measured_prefix_hol_light_ctxt:
  ∀l. axiom_free l ⇒ hol_light_ctxt (l ++ measured_prefix)
Proof
  rw[hol_light_ctxt_def] >>
  qexists_tac`l` >>
  qexists_tac`TAKE 22 (DROP 4 measured_prefix)` >>
  qexists_tac`[]` >>
  qexists_tac`TAKE 2 (DROP 29 measured_prefix)` >>
  qexists_tac`«_2040»` >>
  qexists_tac`«_2045»` >>
  conj_tac >- simp[GSYM measured_prefix_decomposition] >>
  simp[] >>
  EVAL_TAC >> simp[]
QED

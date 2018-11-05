open preamble setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
     holSemanticsTheory holSemanticsExtraTheory

val _ = new_theory"holSoundness"

val mem = ``mem:'U->'U-> bool``

val binary_inference_rule = Q.store_thm("binary_inference_rule",
  `is_set_theory ^mem ⇒
    ∀thy h1 h2 p1 p2 q.
    q has_type Bool ∧ term_ok (sigof thy) q ∧
    (∀δ γ v sigma. is_frag_interpretation (total_fragment (sigof thy)) δ γ ∧
           valuates_frag δ v sigma ∧
           (∀ty. tyvars (sigma ty) = []) ∧
           (∀ty. type_ok (tysof (sigof thy)) (sigma ty)) ∧
           p1 ∈ ground_terms_uninst (sigof thy) sigma ∧
           p2 ∈ ground_terms_uninst (sigof thy) sigma ∧
           termsem_ext δ γ v sigma p1 = True ∧
           termsem_ext δ γ v sigma p2 = True ⇒
           termsem_ext δ γ v sigma q = True) ∧
    (thy,h1) |= p1 ∧ (thy,h2) |= p2
    ⇒ (thy, term_union h1 h2) |= q`,
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  fs[entails_def,EVERY_term_union] >> rw[] >>
  rpt (first_x_assum(qspecl_then[`δ`,`γ`]mp_tac)>>rw[]) >>
  fs[satisfies_t_def,satisfies_def,termsem_ext_def,EVERY_term_union] >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- fs[models_def] >>
  conj_tac >- fs[valuates_frag_builtins] >>
  fs[PULL_FORALL,AND_IMP_INTRO] >>
  `∀x y ls. hypset_ok ls ⇒
         (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
    metis_tac[MEM_term_remove,MEM_term_remove_imp] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  `is_frag_interpretation (total_fragment (sigof thy)) δ γ` by fs[models_def] >>
  qpat_x_assum `hypset_ok h1` assume_tac >> drule MEM_term_union >>
  qpat_x_assum `hypset_ok h2` assume_tac >> disch_then drule >>
  simp [DISJ_IMP_THM,FORALL_AND_THM] >> strip_tac >>
  `EVERY (λt. t ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma) h1`
    by(fs[EVERY_MEM] >> rw[]
       >> first_x_assum drule >> strip_tac
       >> `welltyped t` by metis_tac[term_ok_welltyped]
       >> drule terms_of_frag_uninst_ACONV
       >> simp[GSYM PULL_FORALL]
       >> impl_tac
       >- (rpt(first_x_assum drule) >> fs[ground_terms_uninst_def,welltyped_def]
           >> metis_tac[])
       >> simp[]) >>
  `EVERY (λt. t ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma) h2`
    by(fs[EVERY_MEM] >> rw[]
       >> first_x_assum drule >> strip_tac
       >> `welltyped t` by metis_tac[term_ok_welltyped]
       >> drule terms_of_frag_uninst_ACONV
       >> simp[GSYM PULL_FORALL]
       >> impl_tac
       >- (rpt(first_x_assum drule) >> fs[ground_terms_uninst_def,welltyped_def]
           >> metis_tac[])
       >> simp[]) >>
  `EVERY (λt. t ∈ ground_terms_uninst (sigof thy) sigma) h1`
    by(fs[EVERY_MEM] >> rw[] >>
       fs[ground_terms_uninst_def] >>
       metis_tac[WELLTYPED_LEMMA]) >>
  `EVERY (λt. t ∈ ground_terms_uninst (sigof thy) sigma) h2`
    by(fs[EVERY_MEM] >> rw[] >>
       fs[ground_terms_uninst_def] >>
       metis_tac[WELLTYPED_LEMMA]) >>
  `p1 ∈ ground_terms_uninst (sigof thy) sigma`
    by(fs[ground_terms_uninst_def] >> asm_exists_tac >> metis_tac[WELLTYPED_LEMMA]) >>
  `p2 ∈ ground_terms_uninst (sigof thy) sigma`
    by(fs[ground_terms_uninst_def] >> asm_exists_tac >> metis_tac[WELLTYPED_LEMMA]) >>
  rpt conj_tac >> TRY(first_x_assum ACCEPT_TAC) >> first_x_assum match_mp_tac >> rw[]
  >- (match_mp_tac terms_of_frag_uninst_term_ok >> metis_tac[])
  >- (fs[EVERY_MEM] >> rw[] >> rpt(first_x_assum drule) >> rpt strip_tac >>
      rpt(first_x_assum drule) >> rpt strip_tac >>
      `welltyped t` by metis_tac[welltyped_def] >>
      `welltyped y` by metis_tac[terms_of_frag_uninst_welltyped] >>
      metis_tac[termsem_aconv])
  >- (match_mp_tac terms_of_frag_uninst_term_ok >> metis_tac[])
  >- (fs[EVERY_MEM] >> rw[] >> rpt(first_x_assum drule) >> rpt strip_tac >>
      rpt(first_x_assum drule) >> rpt strip_tac >>
      `welltyped t` by metis_tac[welltyped_def] >>
      `welltyped y` by metis_tac[terms_of_frag_uninst_welltyped] >>
      metis_tac[termsem_aconv]));

val ABS_correct = Q.store_thm("ABS_correct",
  `is_set_theory ^mem ⇒
    ∀thy x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (tysof thy) ty ∧
    (thy,h) |= l === r
    ⇒ (thy,h) |= Abs (Var x ty) l === Abs (Var x ty) r`,
  rw[] >> fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- fs[term_ok_equation,term_ok_def] >>
  conj_asm1_tac >- fs[EQUATION_HAS_TYPE_BOOL] >> rw[] >>
  fs[satisfies_t_def,satisfies_def] >> rw[] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  `is_frag_interpretation (total_fragment (sigof thy)) δ γ` by(fs[models_def]) >>
  `Abs (Var x ty) l ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma`
    by(drule terms_of_frag_uninst_equation >> simp[welltyped_equation] >> disch_then drule >>
       metis_tac[]) >>
  `Abs (Var x ty) r ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma`
    by(drule terms_of_frag_uninst_equation >> simp[welltyped_equation] >> disch_then drule >>
       metis_tac[]) >>
  `l ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma`
    by(drule terms_of_frag_uninst_AbsE >> disch_then(qspecl_then [`Var x ty`,`l`,`sigma`] mp_tac) >>
       simp[]) >>
  `r ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma`
    by(drule terms_of_frag_uninst_AbsE >> disch_then(qspecl_then [`Var x ty`,`r`,`sigma`] mp_tac) >>
       simp[]) >>
  drule termsem_ext_equation >> simp[termsem_ext_def] >>
  fs[valuates_frag_builtins] >>
  ntac 3 (disch_then drule) >>
  disch_then(qspecl_then [`Abs (Var x ty) l`,`Abs (Var x ty) r`] mp_tac) >>
  impl_tac >- fs[term_ok_equation] >>
  simp[] >> disch_then kall_tac >>
  simp[boolean_eq_true] >>
  simp[termsem_def] >>
  `typeof l = typeof r`
      by(fs[GSYM welltyped_equation] >> qpat_x_assum `welltyped _` mp_tac
         >> simp[equation_def]) >>
  simp[] >>
  drule abstract_eq >> disch_then match_mp_tac >>
  ntac 2 strip_tac >>
  simp[] >>
  conj_tac >-
   (qpat_x_assum `typeof _ = typeof_` (assume_tac o GSYM) >>
    simp[] >> match_mp_tac termsem_in_type_ext2 >>
    simp[] >> asm_exists_tac >> simp[] >> rw[combinTheory.UPDATE_def] >>
    fs[valuates_frag_def]) >>
  conj_tac >-
   (match_mp_tac termsem_in_type_ext2 >>
    simp[] >> asm_exists_tac >> simp[] >> rw[combinTheory.UPDATE_def] >>
    fs[valuates_frag_def]) >>
  rename1 `_ =+ x2` >>
  first_x_assum drule >>
  disch_then(qspecl_then [`sigma`,`((x,ty) =+ x2) v`] mp_tac) >>
  impl_tac >-
    (fs[] >>
     conj_tac >-
       (fs[ground_terms_uninst_def] >> imp_res_tac WELLTYPED_LEMMA >>
        qexists_tac `Bool` >> simp[EQUATION_HAS_TYPE_BOOL]
        >> simp[ground_types_def,tyvars_def,type_ok_def] >> fs[is_std_sig_def]) >>
     conj_tac >-
       (fs[valuates_frag_def] >> rw[combinTheory.UPDATE_def] >> simp[]) >>
     conj_tac >-
       (drule terms_of_frag_uninst_equation >>
        disch_then(qspecl_then [`sigma`,`l`,`r`] mp_tac) >>
        rw[welltyped_equation]) >>
     fs[EVERY_MEM] >> rw[] >>
     `welltyped t` by(metis_tac[welltyped_def]) >>
     drule termsem_frees >>
     disch_then(qspecl_then [`ext_type_frag_builtins δ`,`ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,`v`,`((x,ty) =+ x2) v`] mp_tac) >>
     impl_tac >- (rw[combinTheory.UPDATE_def] >> metis_tac[]) >>
     simp[]) >>
  drule termsem_ext_equation >> ntac 2 (disch_then drule) >>
  disch_then(qspecl_then [`((x,ty) =+ x2) v`,`l`,`r`] mp_tac) >>
  impl_tac >-
    (rw[valuates_frag_def,combinTheory.UPDATE_def] >> rw[] >> simp[] >> fs[valuates_frag_def]) >>
  simp[termsem_ext_def,boolean_eq_true]);

val ASSUME_correct = Q.store_thm("ASSUME_correct",
  `∀thy p.
      theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
      ⇒ (thy,[p]) |= p`,
  rw[entails_def,satisfies_t_def,satisfies_def])
                                
val BETA_correct = Q.store_thm("BETA_correct",
  `is_set_theory ^mem ⇒
    ∀thy x ty t.
      theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= Comb (Abs (Var x ty) t) (Var x ty) === t`,
  rw[] >> simp[entails_def] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_welltyped >>
  conj_asm1_tac >- ( simp[term_ok_equation,term_ok_def] ) >>
  conj_asm1_tac >- ( simp[EQUATION_HAS_TYPE_BOOL] ) >>
  rw[satisfies_t_def,satisfies_def] >>
  drule termsem_ext_equation >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  disch_then drule >> fs[models_def] >> disch_then drule >>
  disch_then(qspecl_then [`v`,`Comb (Abs (Var x ty) t) (Var x ty)`,`t`] mp_tac) >>
  fs[valuates_frag_builtins] >> simp[] >> drule terms_of_frag_uninst_equationE
  >> disch_then drule >> simp[welltyped_equation]
  >> strip_tac >> simp[termsem_ext_def] >> disch_then kall_tac
  >> simp[boolean_eq_true]
  >> simp[termsem_def]
  >> match_mp_tac apply_abstract_matchable
  >> conj_tac
  >- fs[valuates_frag_def]
  >> conj_tac
  >- (fs[APPLY_UPDATE_ID] >> match_mp_tac termsem_in_type_ext2
      >> simp[] >> asm_exists_tac >> fs[valuates_frag_def])
  >> conj_tac >- simp[]
  >> simp[APPLY_UPDATE_ID]);

val DEDUCT_ANTISYM_correct = Q.store_thm("DEDUCT_ANTISYM_correct",
  `is_set_theory ^mem ⇒
    ∀thy h1 p1 h2 p2.
      (thy,h1) |= p1 ∧ (thy,h2) |= p2 ⇒
      (thy,
       term_union (term_remove p2 h1)
                  (term_remove p1 h2))
      |= p1 === p2`,
  rw[] >> fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- (
    simp[term_ok_equation] >>
    imp_res_tac WELLTYPED_LEMMA >> simp[] >>
    match_mp_tac EVERY_term_union >>
    rpt conj_tac >>
    match_mp_tac EVERY_term_remove >>
    fs[EVERY_MEM] ) >>
  conj_asm1_tac >- (
    simp[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac WELLTYPED_LEMMA >> simp[WELLTYPED] >>
    match_mp_tac EVERY_term_union >>
    rpt conj_tac >>
    match_mp_tac EVERY_term_remove >>
    fs[EVERY_MEM] ) >>
  rw[satisfies_t_def,satisfies_def] >>
  drule termsem_ext_equation >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  disch_then drule >> fs[models_def] >>
  disch_then drule >> fs[valuates_frag_builtins] >> disch_then drule >>
  disch_then(qspecl_then [`p1`,`p2`] mp_tac) >>
  impl_tac >-
    (metis_tac[terms_of_frag_uninst_equationE,welltyped_equation])
  >> simp[termsem_ext_def] >> disch_then kall_tac
  >> simp[boolean_eq_true]
  >> `∀x y ls. hypset_ok ls ⇒
         (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
           metis_tac[MEM_term_remove,MEM_term_remove_imp]
  >> `EVERY (λt. t ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma) h1`
    by(fs[valuates_frag_builtins]
       >> drule terms_of_frag_uninst_equationE >> disch_then drule
       >> simp[welltyped_equation] >> strip_tac
       >> fs[EVERY_MEM]
       >> qpat_x_assum `hypset_ok h1` assume_tac >> first_assum drule
       >> strip_tac >> qpat_x_assum `hypset_ok h2` assume_tac >> first_x_assum drule
       >> strip_tac
       >> rw[]
       >> `welltyped t` by metis_tac[term_ok_welltyped]
       >> `welltyped p2` by metis_tac[welltyped_def]
       >> Cases_on `ACONV t p2`
       >> rveq
       >- metis_tac[terms_of_frag_uninst_ACONV]
       >> `~ACONV p2 t` by(metis_tac[ACONV_SYM])
       >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
       >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
       >> imp_res_tac hypset_ok_term_remove
       >> first_x_assum(qspec_then `p2` assume_tac)
       >> drule MEM_term_union
       >> first_x_assum(qspec_then `p1` assume_tac)
       >> disch_then drule
       >> disch_then(qspec_then `t` mp_tac) >> simp[]
       >> strip_tac
       >> metis_tac[terms_of_frag_uninst_ACONV,welltyped_def])
  >> `EVERY (λt. t ∈ terms_of_frag_uninst (total_fragment (sigof thy)) sigma) h2`
    by(fs[valuates_frag_builtins]
       >> drule terms_of_frag_uninst_equationE >> disch_then drule
       >> simp[welltyped_equation] >> strip_tac
       >> fs[EVERY_MEM]
       >> qpat_x_assum `hypset_ok h1` assume_tac >> first_assum drule
       >> strip_tac >> qpat_x_assum `hypset_ok h2` assume_tac >> first_x_assum drule
       >> strip_tac
       >> rw[]
       >> `welltyped t` by metis_tac[term_ok_welltyped]
       >> `welltyped p1` by metis_tac[welltyped_def]
       >> Cases_on `ACONV t p1`
       >> rveq
       >- metis_tac[terms_of_frag_uninst_ACONV]
       >> `~ACONV p1 t` by(metis_tac[ACONV_SYM])
       >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
       >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
       >> imp_res_tac hypset_ok_term_remove
       >> first_x_assum(qspec_then `p2` assume_tac)
       >> drule MEM_term_union
       >> first_x_assum(qspec_then `p1` assume_tac)
       >> disch_then drule
       >> disch_then(qspec_then `t` mp_tac) >> simp[]
       >> strip_tac
       >> metis_tac[terms_of_frag_uninst_ACONV,welltyped_def])
  >> qpat_x_assum `!x y z. hypset_ok _ ==> _` kall_tac
  >> qmatch_goalsub_abbrev_tac `a1 = a2`
  >> Cases_on `a2 = True`
  >- (`a1 = True` suffices_by simp[]
      >> unabbrev_all_tac
      >> ntac 2(first_x_assum drule
                >> impl_tac >- rw[]
                >> strip_tac)
      >> ntac 2 (pop_assum mp_tac)
      >> simp[satisfies_t_def]
      >> ntac 2 (disch_then drule
                 >> impl_tac
                 >- (fs[ground_terms_uninst_def,EVERY_MEM,PULL_EXISTS,PULL_FORALL]
                     >> rw[] >> simp[AC CONJ_ASSOC CONJ_SYM] >> asm_exists_tac
                     >> simp[ground_types_def,tyvars_def,type_ok_def]
                     >> fs[is_std_sig_def]
                     >> rw[]
                     >> rpt(first_x_assum drule >> strip_tac)
                     >> asm_exists_tac >> simp[tyvars_def,type_ok_def])
                 >> strip_tac)
      >> fs[satisfies_def]
      >> first_x_assum match_mp_tac
      >> fs[valuates_frag_builtins]
      >> drule terms_of_frag_uninst_equationE >> disch_then drule
      >> simp[welltyped_equation] >> strip_tac
      >> fs[EVERY_MEM]
      >> `∀x y ls. hypset_ok ls ⇒
             (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
              metis_tac[MEM_term_remove,MEM_term_remove_imp]
      >> qpat_x_assum `hypset_ok h1` assume_tac >> first_assum drule
      >> strip_tac >> qpat_x_assum `hypset_ok h2` assume_tac >> first_x_assum drule
      >> strip_tac
      >> rw[]
      >> `welltyped t` by metis_tac[term_ok_welltyped]
      >> `welltyped p2` by metis_tac[welltyped_def]
      >> Cases_on `ACONV t p2`
      >> rveq
      >- (drule termsem_aconv
          >> rpt(disch_then drule) >> simp[])
      >> `~ACONV p2 t` by(metis_tac[ACONV_SYM])
      >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
      >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
      >> imp_res_tac hypset_ok_term_remove
      >> first_x_assum(qspec_then `p2` assume_tac)
      >> drule MEM_term_union
      >> first_x_assum(qspec_then `p1` assume_tac)
      >> disch_then drule
      >> disch_then(qspec_then `t` mp_tac) >> simp[]
      >> strip_tac
      >> metis_tac[termsem_aconv,term_ok_welltyped])
  >> `a2 = False`
    by(`a2 ⋲ boolset` suffices_by metis_tac[mem_boolset,true_neq_false]
       >> drule termsem_in_type_ext2 >> ntac 2 (disch_then drule)
       >> disch_then(qspecl_then [`v`,`sigma`,`p2`] mp_tac)
       >> `typeof p2 = Bool` by metis_tac[WELLTYPED_LEMMA]
       >> simp[]
       >> impl_tac
       >- (conj_tac >- metis_tac[terms_of_frag_uninst_equationE,welltyped_equation]
           >> fs[valuates_frag_def])
       >> rw[ext_type_frag_builtins_def])
  >> `a1 <> True ==> a1 = False`
    by(`a1 ⋲ boolset` suffices_by metis_tac[mem_boolset,true_neq_false]
       >> drule termsem_in_type_ext2 >> ntac 2 (disch_then drule)
       >> disch_then(qspecl_then [`v`,`sigma`,`p1`] mp_tac)
       >> `typeof p1 = Bool` by metis_tac[WELLTYPED_LEMMA]
       >> simp[]
       >> impl_tac
       >- (conj_tac >- metis_tac[terms_of_frag_uninst_equationE,welltyped_equation]
           >> fs[valuates_frag_def])
       >> rw[ext_type_frag_builtins_def])
  >> simp[]
  >> first_x_assum match_mp_tac
  >> unabbrev_all_tac
  >> ntac 2(first_x_assum drule
            >> impl_tac >- rw[]
            >> strip_tac)
  >> ntac 2 (pop_assum mp_tac)
  >> simp[satisfies_t_def]
  >> ntac 2 (disch_then drule
             >> impl_tac
             >- (fs[ground_terms_uninst_def,EVERY_MEM,PULL_EXISTS,PULL_FORALL]
                 >> rw[] >> simp[AC CONJ_ASSOC CONJ_SYM] >> asm_exists_tac
                 >> simp[ground_types_def,tyvars_def,type_ok_def]
                 >> fs[is_std_sig_def]
                 >> rw[]
                 >> rpt(first_x_assum drule >> strip_tac)
                 >> asm_exists_tac >> simp[tyvars_def,type_ok_def])
             >> strip_tac)
  >> fs[satisfies_def]
  >> qpat_x_assum `_ = False` mp_tac
  >> ntac 2 (first_x_assum(qspec_then `v` mp_tac))
  >> fs[valuates_frag_builtins]
  >> drule terms_of_frag_uninst_equationE
  >> disch_then drule
  >> simp[welltyped_equation]
  >> strip_tac
  >> rpt strip_tac >> fs[]
  >> rfs[]
  >> fs[EXISTS_MEM]
  >> fs[EVERY_MEM]
  >> `∀x y ls. hypset_ok ls ⇒
             (MEM x (term_remove y ls) ⇔ ¬ACONV y x ∧ MEM x ls)` by
              metis_tac[MEM_term_remove,MEM_term_remove_imp]
  >> qpat_x_assum `hypset_ok h1` assume_tac >> first_assum drule
  >> strip_tac >> qpat_x_assum `hypset_ok h2` assume_tac >> first_x_assum drule
  >> strip_tac
  >> rw[]
  >> `welltyped e` by metis_tac[term_ok_welltyped]
  >> `welltyped p1` by metis_tac[welltyped_def]
  >> Cases_on `ACONV e p1`
  >> rveq
  >- metis_tac[termsem_aconv]
  >> `~ACONV p1 e` by(metis_tac[ACONV_SYM])
  >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
  >> qpat_x_assum `!x y. _ <=> _ /\ _` (imp_res_tac o GSYM)
  >> imp_res_tac hypset_ok_term_remove
  >> first_x_assum(qspec_then `p2` assume_tac)
  >> drule MEM_term_union
  >> first_x_assum(qspec_then `p1` assume_tac)
  >> disch_then drule
  >> disch_then(qspec_then `e` mp_tac) >> simp[]
  >> strip_tac
  >> metis_tac[termsem_aconv,term_ok_welltyped]);

val EQ_MP_correct = Q.store_thm("EQ_MP_correct",
  `is_set_theory ^mem ⇒
    ∀thy h1 h2 p q p'.
      (thy,h1) |= p === q ∧ (thy,h2) |= p' ∧ ACONV p p' ⇒
      (thy,term_union h1 h2) |= q`,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>    
  map_every qexists_tac[`p === q`,`p'`] >>
  fs[entails_def] >> fs[EQUATION_HAS_TYPE_BOOL] >>
  fs[theory_ok_def] >>
  drule(GEN_ALL term_ok_equation) >> rpt(disch_then drule) >>
  disch_then(qspecl_then [`q`,`p`] assume_tac) >> fs[] >>
  conj_asm1_tac >- metis_tac[ACONV_TYPE,WELLTYPED,WELLTYPED_LEMMA] >> rw[] >>  
  `term_ok (sigof thy) (p === q)` by metis_tac[term_ok_equation] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  drule termsem_ext_equation >> 
  rpt(disch_then drule) >>
  disch_then(qspecl_then [`p`,`q`] mp_tac) >>
  impl_tac >- (simp[] >> conj_tac >> match_mp_tac terms_of_frag_uninst_term_ok >> fs[]) >>
  rfs[boolean_eq_true] >>
  metis_tac[termsem_aconv,term_ok_welltyped,termsem_ext_def]);

val INST_correct = Q.store_thm("INST_correct",
  `is_set_theory ^mem ⇒
    ∀thy h c.
      (∀s s'. MEM (s',s) ilist ⇒
              ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
      (thy, h) |= c
    ⇒ (thy, term_image (VSUBST ilist) h) |= VSUBST ilist c`,
  rw[entails_def,EVERY_MEM,satisfies_t_def] >>
  TRY ( imp_res_tac MEM_term_image_imp >> rw[] ) >>
  TRY ( match_mp_tac term_ok_VSUBST >> metis_tac[] ) >>
  TRY ( match_mp_tac VSUBST_HAS_TYPE >> metis_tac[] ) >>
  TRY ( match_mp_tac hypset_ok_term_image >> rw[] ) >>
  rw[satisfies_def,satisfies_t_def] >>  
  qspecl_then[`c`,`ilist`]mp_tac termsem_VSUBST >>
  impl_tac >- metis_tac[welltyped_def] >>  
  disch_then(qspecl_then[`ext_type_frag_builtins δ`,
                         `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                         `v`,`sigma`]SUBST1_TAC) >>
  first_x_assum drule >> simp[satisfies_def,satisfies_t_def] >>
  disch_then(match_mp_tac o MP_CANON) >>
  simp[] >>
  rpt conj_tac
  >- (rw[ground_terms_uninst_def] >> qexists_tac `Bool`
      >> conj_tac >- metis_tac[]
      >> fs[ground_types_def,tyvars_def,theory_ok_def,is_std_sig_def,type_ok_def])
  >- (rw[ground_terms_uninst_def] >> asm_exists_tac
      >> fs[ground_types_def,tyvars_def,theory_ok_def,is_std_sig_def,type_ok_def])
  >- (fs[valuates_frag_builtins] >> fs[valuates_frag_def] >> rw[]
      >> fs[APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE]
      >> BasicProvers.CASE_TAC >- metis_tac[]
      >> imp_res_tac ALOOKUP_MEM
      >> fs[MEM_MAP,UNCURRY,EXISTS_PROD]
      >> res_tac >> imp_res_tac WELLTYPED_LEMMA >> fs[]
      >> rpt BasicProvers.VAR_EQ_TAC
      >> match_mp_tac termsem_in_type_ext2
      >> simp[]
      >> qspec_then `sigof thy` assume_tac total_fragment_is_fragment
      >> asm_exists_tac
      >> fs[]
      >> conj_tac >- fs[models_def]
      >> match_mp_tac terms_of_frag_uninst_term_ok
      >> fs[])
  >- (match_mp_tac terms_of_frag_uninst_term_ok >> fs[])
  >- (rw[EVERY_MEM] >> match_mp_tac terms_of_frag_uninst_term_ok >> fs[]) >>
  rw[EVERY_MEM] >>
  qspecl_then[`h`,`VSUBST ilist`,`t`]mp_tac MEM_term_image >>
  impl_tac >- rw[] >> strip_tac >>
  drule MEM_term_image_imp >> strip_tac >> rveq >>
  `term_ok (sigof thy) x` by metis_tac[] >>
  `term_ok (sigof thy) t` by metis_tac[] >>
  `welltyped x` by metis_tac[term_ok_welltyped] >>
  `welltyped t` by metis_tac[term_ok_welltyped] >>
  drule termsem_VSUBST >>
  disch_then(qspecl_then [`ilist`,
                          `ext_type_frag_builtins δ`,
                          `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                          `v`,`sigma`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  disch_then (SUBST1_TAC o GSYM) >>
  drule termsem_aconv >> simp[GSYM PULL_FORALL] >>
  impl_tac >- metis_tac[welltyped_def,VSUBST_WELLTYPED] >>
  disch_then(qspecl_then [`ext_type_frag_builtins δ`,
                          `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                          `v`] SUBST1_TAC) >>
  fs[EVERY_MEM]);

val INST_TYPE_correct = Q.store_thm("INST_TYPE_correct",
  `is_set_theory ^mem ⇒
    ∀thy h c.
      EVERY (type_ok (tysof thy)) (MAP FST tyin) ∧
      (thy, h) |= c
    ⇒ (thy, term_image (INST tyin) h) |= INST tyin c`,
  rw[entails_def,EVERY_MAP,EVERY_MEM] >>
  TRY ( match_mp_tac hypset_ok_term_image >> rw[] ) >>
  TRY ( imp_res_tac MEM_term_image_imp >> rw[] ) >>
  TRY ( match_mp_tac term_ok_INST >> fs[EVERY_MAP,EVERY_MEM] >> metis_tac[] ) >>
  TRY ( match_mp_tac INST_HAS_TYPE >> metis_tac[TYPE_SUBST_Bool] ) >>
  rw[satisfies_t_def,satisfies_def] >>
  drule termsem_INST >>
  disch_then(qspecl_then [`ext_type_frag_builtins δ`,
                          `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                          `sigma`,`tyin`,`v`] mp_tac) >>
  simp[] >> disch_then kall_tac >>
  first_x_assum drule >> simp[satisfies_t_def,satisfies_def] >>
  simp[PULL_FORALL,AND_IMP_INTRO] >> disch_then match_mp_tac >>
  simp[GSYM PULL_FORALL] >>
  rpt conj_tac
  >- rw[ground_TYPE_SUBSTf]
  >- (rw[] >> match_mp_tac type_ok_TYPE_SUBSTf >>
      rw[] >> `type_ok (tysof (sigof thy)) (Tyvar ty')`by simp[type_ok_def] >>
      drule type_ok_TYPE_SUBST >>
      simp[EVERY_MEM,MEM_MAP,PULL_EXISTS])
  >- (rw[EVERY_MEM] >> fs[ground_terms_uninst_def] >>
      qexists_tac `Bool` >> conj_tac >- metis_tac[] >>
      rw[ground_types_def,tyvars_def] >>
      fs[theory_ok_def,is_std_sig_def,type_ok_def])
  >- (rw[EVERY_MEM] >> fs[ground_terms_uninst_def] >>
      qexists_tac `Bool` >> conj_tac >- metis_tac[] >>
      rw[ground_types_def,tyvars_def] >>
      fs[theory_ok_def,is_std_sig_def,type_ok_def])
  >- (fs[valuates_frag_builtins] >> fs[valuates_frag_def]
      >> rw[] >> simp[GSYM TYPE_SUBSTf_TYPE_SUBST_compose])
  >- (match_mp_tac terms_of_frag_uninst_term_ok
      >> simp[]
      >> conj_tac
      >- (rw[] >> metis_tac[ground_TYPE_SUBSTf])
      >> rw[]
      >> match_mp_tac type_ok_TYPE_SUBSTf
      >> simp[]
      >> `type_ok (tysof (sigof thy)) (Tyvar ty)`by simp[type_ok_def]
      >> drule type_ok_TYPE_SUBST
      >> simp[EVERY_MEM,MEM_MAP,PULL_EXISTS])
  >- (rw[EVERY_MEM] >> match_mp_tac terms_of_frag_uninst_term_ok
      >> simp[]
      >> conj_tac >- (rw[] >> metis_tac[ground_TYPE_SUBSTf])
      >> rw[]
      >> match_mp_tac type_ok_TYPE_SUBSTf
      >> simp[]
      >> `type_ok (tysof (sigof thy)) (Tyvar ty)`by simp[type_ok_def]
      >> drule type_ok_TYPE_SUBST
      >> simp[EVERY_MEM,MEM_MAP,PULL_EXISTS]) >>
  rw[EVERY_MEM] >>
  qspecl_then[`h`,`INST tyin`,`t`]mp_tac MEM_term_image >>
  impl_tac >- rw[] >> strip_tac >>
  fs[EVERY_MEM] >>
  drule MEM_term_image_imp >> strip_tac >> rveq >>
  `term_ok (sigof thy) x` by metis_tac[] >>
  `term_ok (sigof thy) t` by metis_tac[] >>
  drule termsem_INST >>
  disch_then(qspecl_then [`ext_type_frag_builtins δ`,
                          `ext_term_frag_builtins (ext_type_frag_builtins δ) γ`,
                          `sigma`,`tyin`,`v`] (mp_tac o GSYM)) >>
  simp[] >> disch_then kall_tac >>
  drule termsem_aconv >> simp[GSYM PULL_FORALL] >>
  impl_tac >- metis_tac[welltyped_def,INST_WELLTYPED] >>
  metis_tac[]);

val MK_COMB_correct = Q.store_thm("MK_COMB_correct",
  `is_set_theory ^mem ⇒
    ∀thy h1 h2 l1 r1 l2 r2.
      (thy,h1) |= l1 === r1 ∧ (thy,h2) |= l2 === r2 ∧
      welltyped (Comb l1 l2)
      ⇒ (thy,term_union h1 h2) |= Comb l1 l2 === Comb r1 r2`,
  rw[] >>
  match_mp_tac (UNDISCH binary_inference_rule) >>
  map_every qexists_tac[`l1 === r1`,`l2 === r2`] >>
  fs[entails_def] >>
  imp_res_tac theory_ok_sig >>
  conj_asm1_tac >- (
    fs[EQUATION_HAS_TYPE_BOOL,term_ok_equation] >>
    metis_tac[] ) >>
  conj_asm1_tac >- (
    fs[term_ok_equation,term_ok_def,EQUATION_HAS_TYPE_BOOL] ) >>
  rw[] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  drule termsem_ext_equation >> 
  rpt(disch_then drule) >>
  disch_then(qspecl_then [`l1`,`r1`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >>
      match_mp_tac terms_of_frag_uninst_term_ok >>
      fs[term_ok_equation]) >>
  strip_tac >>
  drule termsem_ext_equation >> 
  rpt(disch_then drule) >>
  disch_then(qspecl_then [`l2`,`r2`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >>
      match_mp_tac terms_of_frag_uninst_term_ok >>
      fs[term_ok_equation]) >>
  strip_tac >> fs[] >>
  drule termsem_ext_equation >> rpt(disch_then drule) >>
  disch_then(qspecl_then [`Comb l1 l2`,`Comb r1 r2`] mp_tac) >>
  impl_tac >- (simp[] >> conj_tac >>
               match_mp_tac terms_of_frag_uninst_term_ok >>
               fs[term_ok_equation] >> fs[term_ok_def] >> metis_tac[term_ok_welltyped]) >>
  simp[] >> rpt strip_tac >>
  rfs[boolean_eq_true] >>
  fs[termsem_def,termsem_ext_def]);

val REFL_correct = Q.store_thm("REFL_correct",
  `is_set_theory ^mem ⇒
    ∀thy t.
      theory_ok thy ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= t === t`,
  rw[] >>
  simp[entails_def,EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_welltyped >>
  conj_asm1_tac >- rw[term_ok_equation] >>
  rw[satisfies_def,satisfies_t_def] >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  drule termsem_ext_equation >> fs[models_def,valuates_frag_builtins] >>
  ntac 3(disch_then drule) >>
  disch_then(qspecl_then [`t`,`t`] mp_tac) >>
  impl_tac
  >- (fs[] >> drule terms_of_frag_uninst_equationE >> disch_then drule >>
      fs[] >> disch_then match_mp_tac >>
      simp[welltyped_equation,EQUATION_HAS_TYPE_BOOL]) >>
  rw[termsem_ext_def] >> simp[boolean_eq_true]);

val proves_sound = Q.store_thm("proves_sound",
  `is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c`,
  strip_tac >> match_mp_tac proves_ind >>
  conj_tac >- metis_tac[ABS_correct] >>
  conj_tac >- metis_tac[ASSUME_correct] >>
  conj_tac >- metis_tac[BETA_correct] >>
  conj_tac >- metis_tac[DEDUCT_ANTISYM_correct] >>
  conj_tac >- metis_tac[EQ_MP_correct] >>
  conj_tac >- metis_tac[INST_correct] >>
  conj_tac >- metis_tac[INST_TYPE_correct] >>
  conj_tac >- metis_tac[MK_COMB_correct] >>
  conj_tac >- metis_tac[REFL_correct] >>
  rw[entails_def,theory_ok_def,models_def])

val _ = export_theory()

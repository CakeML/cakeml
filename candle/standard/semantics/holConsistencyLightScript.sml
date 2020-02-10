(*
  Proves consistency of the inference system
*)
open preamble
     setSpecTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holBoolSyntaxTheory holAxiomsSyntaxTheory
     holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory holExtensionTheory holBoolTheory(* holAxiomsTheory*)

val _ = new_theory"holConsistencyLight"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

val consistent_theory_def = Define`
  consistent_theory thy ⇔
        (thy,[]) |- (Var (strlit"x") Bool === Var (strlit"x") Bool) ∧
      ¬((thy,[]) |- (Var (strlit"x") Bool === Var (strlit"y") Bool))`

Theorem proves_consistent:
   is_set_theory ^mem ⇒
    ∀thy. theory_ok thy ∧ (∃δ γ. models δ γ thy) ⇒
      consistent_theory thy
Proof
  rw[consistent_theory_def] >- (
    match_mp_tac (List.nth(CONJUNCTS proves_rules,8)) >>
    simp[term_ok_def,type_ok_def] >>
    imp_res_tac theory_ok_sig >>
    fs[is_std_sig_def] ) >>
  spose_not_then strip_assume_tac >>
  imp_res_tac proves_sound >>
  fs[entails_def] >>
  first_x_assum drule >>
  simp[satisfies_def,satisfies_t_def] >>
  qexists_tac `K Bool` >>
  simp[tyvars_def] >>
  conj_tac >- (
    imp_res_tac theory_ok_sig >>
    imp_res_tac term_ok_welltyped >>
    imp_res_tac term_ok_type_ok >>
    rfs[typeof_equation] >>
    fs[ground_terms_uninst_def] >>
    qexists_tac `Bool` >> fs[ground_types_def,tyvars_def]) >>
  qexists_tac`λ(x,ty). if (x,ty) = (strlit"x",Bool) then True else
                       if (x,ty) = (strlit"y",Bool) then False else
                       @v. v <: ext_type_frag_builtins δ (TYPE_SUBSTf (K Bool) ty)` >>
  conj_asm1_tac >- (
    reverse conj_asm2_tac >-
      (match_mp_tac terms_of_frag_uninst_term_ok >> simp[tyvars_def] >>
       imp_res_tac theory_ok_sig >> fs[term_ok_clauses]) >>
    simp[valuates_frag_builtins] >> rw[valuates_frag_def] >>
    rw[ext_type_frag_builtins_simps,mem_boolset] >>
    `is_type_frag_interpretation (FST(total_fragment (sigof thy))) δ`
      by(fs[models_def,is_frag_interpretation_def,total_fragment_def]) >>
    pop_assum mp_tac >> rw[total_fragment_def] >>
    qspec_then `sigof thy` mp_tac total_fragment_is_fragment >>
    rw[total_fragment_def] >>
    drule is_type_frag_interpretation_ext >>
    rpt(disch_then drule) >>
    simp[is_type_frag_interpretation_def] >>
    qpat_x_assum `_ ∈ _` mp_tac >>
    simp[types_of_frag_def,total_fragment_def] >>
    strip_tac >> disch_then drule >>
    metis_tac[]) >>
  drule (GEN_ALL termsem_ext_equation) >>
  qspec_then `sigof thy` assume_tac total_fragment_is_fragment >>
  disch_then drule >>
  `is_frag_interpretation (total_fragment (sigof thy)) δ γ`
    by(fs[models_def]) >>
  disch_then drule >>
  fs[valuates_frag_builtins] >>
  disch_then drule >>
  disch_then(qspecl_then [`Var (strlit "x") Bool`,`Var (strlit "y") Bool`] mp_tac) >>
  impl_tac >- (
    simp[] >>
    conj_tac >> match_mp_tac terms_of_frag_uninst_term_ok >>
    imp_res_tac theory_ok_sig >>
    simp[term_ok_def,tyvars_def,term_ok_clauses]) >>
  simp[termsem_ext_def] >> disch_then kall_tac >>
  simp[boolean_eq_true,termsem_def,true_neq_false]
QED

val init_ctxt_builtin = Q.store_thm("init_ctxt_builtin",
  `!ty. type_ok (tysof init_ctxt) ty /\ tyvars ty = [] ==> is_builtin_type ty`,
  Cases >> rw[init_ctxt_def,type_ok_def,tyvars_def,is_builtin_type_def]);

val init_ctxt_no_ground = Q.store_thm("init_ctxt_no_ground",
`!ty. ty ∈ ground_types (sigof init_ctxt) ∩ nonbuiltin_types ==> F`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- fs[ground_types_def,tyvars_def]
  >> fs[ground_types_def,init_ctxt_def,tyvars_def]
  >> imp_res_tac FOLDR_LIST_UNION_empty'
  >> fs[type_ok_def]
  >> fs[EVERY_MEM,FLOOKUP_UPDATE]
  >> every_case_tac
  >> rveq >> fs[nonbuiltin_types_def,is_builtin_type_def]);

val init_ctxt_no_ground_set = Q.store_thm("init_ctxt_no_ground_set",
  `ground_types (sigof init_ctxt) ∩ nonbuiltin_types = {}`,
  PURE_REWRITE_TAC [FUN_EQ_THM,EQ_IMP_THM,EMPTY_DEF] >> rpt strip_tac >>
  metis_tac[init_ctxt_no_ground,IN_DEF]);

val init_ctxt_has_model = Q.store_thm("init_ctxt_has_model",
  `is_set_theory ^mem ⇒ ∃δ γ. models δ γ (thyof init_ctxt)`,
  rw[models_def,conexts_of_upd_def,total_fragment_def,
     is_frag_interpretation_def,init_ctxt_no_ground_set] >>
  MAP_EVERY qexists_tac [`ARB`,`ARB`] >>
  reverse conj_tac >-
    (rw[init_ctxt_def,conexts_of_upd_def]) >>
  reverse conj_tac >-
    (mp_tac init_ctxt_no_ground_set >>
     fs[INTER_DEF,IN_DEF,FUN_EQ_THM,ELIM_UNCURRY,GSYM IMP_DISJ_THM] >>
     fs[ground_consts_def,term_ok_def,ELIM_UNCURRY,PULL_EXISTS] >>
     fs[init_ctxt_def,nonbuiltin_constinsts_def,builtin_consts_def] >>
     strip_tac >> Cases >> rw[]) >>
  rw[is_type_frag_interpretation_def]);

Theorem min_hol_consistent:
   is_set_theory ^mem ⇒
    ∀ctxt. ctxt extends init_ctxt ∧
      orth_ctxt ctxt ∧ terminating(subst_clos (dependency ctxt)) ∧ (* TODO: these should follow from the previous conjunct *)
      (∀p. MEM (NewAxiom p) ctxt ⇒ MEM (NewAxiom p) init_ctxt) ⇒
      consistent_theory (thyof ctxt)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  match_mp_tac (UNDISCH proves_consistent) >>
  metis_tac[extends_theory_ok,init_theory_ok,interpretation_is_model]
QED

val _ = export_theory()

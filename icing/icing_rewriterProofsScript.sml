(*
  Correctness proofs for the expression rewriting function
  Shows that matchesExpr e p = SOME s ==> appExpr p s = SOME e
*)
open icing_rewriterTheory source_to_source2Theory fpOptTheory fpOptPropsTheory
     fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
     semanticsTheory semanticsPropsTheory floatToRealTheory
     evaluatePropsTheory fpSemPropsTheory;
open preamble;

val _ = new_theory "icing_rewriterProofs";

Theorem isFpArithExp_matched_evaluates:
  (∀ e env.
    isFpArithExp e ∧
    (∀ x. x IN FV (e) ⇒ ∃ r fp. nsLookup env.v x = SOME (FP_WordTree fp)) ⇒
    ∀ (st:'a semanticPrimitives$state). ∃ st2 r fp. evaluate st env [e] = (st2, Rval [r]) ∧
    r = (FP_WordTree fp)) ∧
  (∀ exps subst env.
     isFpArithExpList exps ∧
    (∀ x. x IN FV_list exps ⇒ ∃ r fp. nsLookup env.v x = SOME (FP_WordTree fp)) ⇒
     ∀ e. MEM e exps ⇒
          ∀ (st:'a semanticPrimitives$state).
            ∃ st2 r fp. evaluate st env [e] = (st2, Rval [r]) ∧
    r = FP_WordTree fp)
Proof
  ho_match_mp_tac isFpArithExp_ind
  \\ rpt strip_tac \\ fs[isFpArithExp_def]
  >- fs[evaluate_def]
  >- (fs[evaluate_def, fp_translate_def, astTheory.getOpClass_def,
         astTheory.isFpBool_def, semanticPrimitivesTheory.do_app_def])
  >- (
    Cases_on ‘exps’ \\ fs[] \\ rveq
    \\ simp[Once evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def]
    \\ first_x_assum (qspec_then ‘env’ mp_tac) \\ impl_tac
    >- (fs[])
    \\ disch_then $ qspec_then ‘st’ strip_assume_tac \\ fs[do_app_def]
    \\ COND_CASES_TAC \\ fs[fp_translate_def]
    \\ TOP_CASE_TAC \\ fs[fp_translate_def, do_fprw_def, CaseEq"option"]
    \\ rveq \\ fs[fp_translate_def])
  >- (
    fs [quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] \\ rveq
    \\ rename1 ‘isFpArithExpList [e1;e2]’
    \\ simp[Once evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def]
    \\ first_x_assum (qspec_then ‘env’ mp_tac) \\ impl_tac
    >- (fs[] \\ metis_tac[])
    \\ disch_then (fn th => qspec_then ‘e1’ strip_assume_tac th
                   \\ qspec_then ‘e2’ strip_assume_tac th)
    \\ fs[]
    \\ simp[Once evaluate_cons]
    \\ pop_assum $ qspec_then ‘st’ strip_assume_tac \\ fs[]
    \\ first_x_assum $ qspec_then ‘st2’ strip_assume_tac \\ fs[]
    \\ fs[do_app_def]
    \\ COND_CASES_TAC \\ fs[fp_translate_def]
    \\ TOP_CASE_TAC \\ fs[fp_translate_def, do_fprw_def, CaseEq"option"]
    \\ rveq \\ fs[fp_translate_def])
  >- (
    fs [quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] \\ rveq
    \\ rename1 ‘isFpArithExpList [e1;e2;e3]’
    \\ simp[Once evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def]
    \\ first_x_assum (qspec_then ‘env’ mp_tac) \\ impl_tac
    >- (fs[] \\ metis_tac[])
    \\ disch_then (fn th => qspec_then ‘e1’ strip_assume_tac th
                   \\ qspec_then ‘e2’ strip_assume_tac th
                   \\ qspec_then ‘e3’ strip_assume_tac th)
    \\ fs[]
    \\ simp[Once evaluate_cons]
    \\ pop_assum $ qspec_then ‘st’ strip_assume_tac \\ fs[]
    \\ simp[Once evaluate_cons]
    \\ first_x_assum $ qspec_then ‘st2’ strip_assume_tac \\ fs[]
    \\ first_x_assum $ qspec_then ‘st2'’ strip_assume_tac \\ fs[]
    \\ fs[do_app_def]
    \\ COND_CASES_TAC \\ fs[fp_translate_def]
    \\ TOP_CASE_TAC \\ fs[fp_translate_def, do_fprw_def, CaseEq"option"]
    \\ rveq \\ fs[fp_translate_def])
QED

Theorem isFpArithExp_matched_evaluates_real:
  (∀ e env.
    isFpArithExp e ∧
    (∀ x. x IN FV (e) ⇒ ∃ r. nsLookup env.v x = SOME (Real r)) ⇒
    ∀ (st:'a semanticPrimitives$state).
      st.fp_state.real_sem ⇒
      ∃ choices r rn.
        evaluate st env [realify e] =
        (st with fp_state := st.fp_state with choices := choices, Rval [r]) ∧
        r = Real rn) ∧
  (∀ exps subst env.
     isFpArithExpList exps ∧
    (∀ x. x IN FV_list exps ⇒ ∃ r. nsLookup env.v x = SOME (Real r)) ⇒
     ∀ e. MEM e exps ⇒
          ∀ (st:'a semanticPrimitives$state).
            st.fp_state.real_sem ⇒
            ∃ choices r rn.
              evaluate st env [realify e] =
              (st with fp_state := st.fp_state with choices := choices, Rval [r]) ∧
              r = Real rn)
Proof
  ho_match_mp_tac isFpArithExp_ind
  \\ rpt strip_tac \\ fs[isFpArithExp_def, realify_def]
  >- fs[evaluate_def, fpState_component_equality, semanticPrimitivesTheory.state_component_equality]
  >- (fs[evaluate_def, fp_translate_def, astTheory.getOpClass_def,
         fpState_component_equality,
         semanticPrimitivesTheory.state_component_equality,
         astTheory.isFpBool_def, semanticPrimitivesTheory.do_app_def])
  >- (
    Cases_on ‘exps’ \\ fs[] \\ rveq
    \\ simp[Once evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def]
    \\ first_x_assum (qspec_then ‘env’ mp_tac) \\ impl_tac
    >- (fs[])
    \\ disch_then $ qspec_then ‘st’ mp_tac \\ fs[do_app_def]
    \\ strip_tac
    \\ gs[fpState_component_equality,
         semanticPrimitivesTheory.state_component_equality])
  >- (
    fs [quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] \\ rveq
    \\ rename1 ‘isFpArithExpList [e1; e2]’
    \\ simp[Once evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def]
    \\ first_x_assum (qspec_then ‘env’ mp_tac) \\ impl_tac
    >- (fs[] \\ metis_tac[])
    \\ disch_then (fn th => qspec_then ‘e1’ strip_assume_tac th
                   \\ qspec_then ‘e2’ strip_assume_tac th)
    \\ gs[]
    \\ simp[Once evaluate_cons]
    \\ pop_assum $ qspec_then ‘st’ mp_tac \\ impl_tac \\ fs[]
    \\ strip_tac \\ gs[]
    \\ first_x_assum $ qspec_then ‘st with fp_state := st.fp_state with choices := choices’ mp_tac \\ impl_tac \\ fs[]
    \\ rpt strip_tac
    \\ fs[do_app_def, fpState_component_equality,
         semanticPrimitivesTheory.state_component_equality])
  >- (
    fs [quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] \\ rveq
    \\ rename1 ‘isFpArithExpList [e1; e2; e3]’
    \\ simp[Once evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def]
    \\ first_x_assum (qspec_then ‘env’ mp_tac) \\ impl_tac
    >- (fs[] \\ metis_tac[])
    \\ disch_then (fn th => qspec_then ‘e1’ strip_assume_tac th
                   \\ qspec_then ‘e2’ strip_assume_tac th
                   \\ qspec_then ‘e3’ strip_assume_tac th)
    \\ fs[]
    \\ simp[Once evaluate_cons]
    \\ last_x_assum $ qspec_then ‘st’ mp_tac \\ impl_tac \\ fs[]
    \\ rpt strip_tac \\ gs[]
    \\ simp[Once evaluate_def, Once evaluate_cons]
    \\ first_x_assum $ qspec_then ‘st with fp_state := st.fp_state with choices := choices’ mp_tac
    \\ impl_tac \\ fs[]
    \\ rpt strip_tac \\ gs[]
    \\ first_x_assum $ qspec_then ‘st with fp_state := st.fp_state with choices := choices'’ mp_tac
    \\ impl_tac \\ fs[]
    \\ rpt strip_tac \\ gs[]
    \\ fs[do_app_def, astTheory.getOpClass_def, fpState_component_equality,
         semanticPrimitivesTheory.state_component_equality])
QED

Theorem isFpArithExp_all_lookup:
  ∀ lhs e subst init.
  isFpArithExp e ∧
  (∀ n eSub.
     substLookup init n = SOME eSub ⇒
     isFpArithExp eSub) ∧
  matchesFPexp lhs e init = SOME subst ⇒
  ∀ n eSub.
    substLookup subst n = SOME eSub ⇒
    isFpArithExp eSub
Proof
  Induct_on ‘lhs’ \\ rpt strip_tac
  \\ fs[matchesFPexp_def, CaseEq"exp", CaseEq"op", CaseEq"list", CaseEq"lit",
        CaseEq"option"]
  \\ rveq \\ fs[isFpArithExp_def]
  >- (res_tac)
  >- (fs[substLookup_substAdd_alt] \\ Cases_on ‘n = n'’ \\ fs[] \\ res_tac)
  >- (res_tac)
  >- (res_tac)
  >- (
    first_x_assum drule
    \\ disch_then $ qspecl_then [‘subst’, ‘s1’, ‘n’, ‘eSub’] mp_tac
    \\ impl_tac \\ fs[]
    \\ rpt strip_tac \\ last_x_assum $ irule
    \\ qexistsl_tac [‘e1’, ‘init’, ‘n'’, ‘s1’] \\ fs[]
    \\ first_x_assum MATCH_ACCEPT_TAC)
  >- (
    first_x_assum drule
    \\ disch_then $ qspecl_then [‘subst’, ‘s2’, ‘n’, ‘eSub’] mp_tac
    \\ impl_tac \\ fs[]
    \\ qpat_x_assum ‘matchesFPexp _ e3 _ = SOME _’ kall_tac
    \\ qpat_x_assum ‘isFpArithExp e3’ kall_tac
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ disch_then $ qspecl_then [‘s2’, ‘s1’, ‘n'’, ‘eSub'’] mp_tac
    \\ impl_tac \\ fs[]
    \\ qpat_x_assum ‘matchesFPexp _ e2 _ = SOME _’ kall_tac
    \\ qpat_x_assum ‘isFpArithExp e2’ kall_tac
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ disch_then $ qspecl_then [‘s1’, ‘init’, ‘n''’, ‘eSub''’] mp_tac
    \\ impl_tac \\ fs[]
    \\ first_x_assum MATCH_ACCEPT_TAC)
QED

Theorem match_preserves_FV_lookup:
  ∀ lhs e subst init P.
  (∀ x. x IN FV e ⇒ P x) ∧
  (∀ n eSub.
     substLookup init n = SOME eSub ⇒
     ∀ x. x IN FV (eSub) ⇒ P x) ∧
  matchesFPexp lhs e init = SOME subst ⇒
  (∀ n eSub.
    substLookup subst n = SOME eSub ⇒
    ∀ x. x IN FV (eSub) ⇒ P x)
Proof
  Induct_on ‘lhs’ \\ rpt strip_tac
  >- (
    fs[Once matchesFPexp_def, CaseEq"exp", CaseEq"op", CaseEq"list", CaseEq"lit",
       CaseEq"option"]
    \\ rveq \\ fs[] \\ res_tac)
  >- (
    fs[Once matchesFPexp_def, CaseEq"exp", CaseEq"op", CaseEq"list", CaseEq"lit",
       CaseEq"option"]
    \\ rveq \\ fs[] \\ res_tac
    \\ fs[substLookup_substAdd_alt] \\ Cases_on ‘n = n'’ \\ fs[] \\ res_tac)
  >- (
    fs[Once matchesFPexp_def, CaseEq"exp", CaseEq"op", CaseEq"list", CaseEq"lit",
       CaseEq"option"]
    \\ rveq \\ fs[] \\ res_tac)
  >- (
    fs[Once matchesFPexp_def, CaseEq"exp", CaseEq"op", CaseEq"list", CaseEq"lit",
       CaseEq"option"]
    \\ rveq \\ fs[]
    \\ first_x_assum $ qspecl_then [‘e2’, ‘subst’, ‘s1’, ‘P’] mp_tac
    \\ impl_tac \\ fs[]
    >- (
      first_x_assum (qspecl_then [‘e1’, ‘s1’, ‘init’, ‘P’] mp_tac)
      \\ impl_tac \\ fs[]
      \\ first_x_assum MATCH_ACCEPT_TAC)
    \\ rpt strip_tac \\ res_tac \\ fs[])
  >- (
    qpat_x_assum ‘matchesFPexp _ _ _ = SOME _’ mp_tac
    \\ simp[Once matchesFPexp_def, CaseEq"exp", CaseEq"op", CaseEq"list", CaseEq"lit",
       CaseEq"option"]
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ first_x_assum $ qspecl_then [‘e3’, ‘subst’, ‘s2’, ‘P’] mp_tac
    \\ impl_tac \\ fs[]
    >- (
      first_x_assum (qspecl_then [‘e2’, ‘s2’, ‘s1’, ‘P’] mp_tac)
      \\ impl_tac \\ fs[]
      \\ first_x_assum (qspecl_then [‘e1’, ‘s1’, ‘init’, ‘P’] mp_tac)
      \\ impl_tac \\ fs[]
      \\ first_x_assum MATCH_ACCEPT_TAC)
    \\ rpt strip_tac \\ res_tac \\ fs[])
  >- (
    fs[Once matchesFPexp_def, CaseEq"exp", CaseEq"op", CaseEq"list", CaseEq"lit",
       CaseEq"option"]
    \\ rveq \\ fs[]
    \\ first_x_assum $ qspecl_then [‘e2’, ‘subst’, ‘s1’, ‘P’] mp_tac
    \\ impl_tac \\ fs[]
    >- (
      first_x_assum (qspecl_then [‘e1’, ‘s1’, ‘init’, ‘P’] mp_tac)
      \\ impl_tac \\ fs[]
      \\ first_x_assum MATCH_ACCEPT_TAC)
    \\ rpt strip_tac \\ res_tac \\ fs[])
  \\ fs[Once matchesFPexp_def, CaseEq"exp", CaseEq"op", CaseEq"list", CaseEq"lit",
       CaseEq"option"]
  \\ rveq \\ fs[] \\ res_tac
QED

Theorem match_preserves_FV:
  ∀ rhs lhs e eNew subst init P.
  (∀ x. x IN FV e ⇒ P x) ∧
  (∀ n eSub.
     substLookup init n = SOME eSub ⇒
     ∀ x. x IN FV (eSub) ⇒ P x) ∧
  matchesFPexp lhs e init = SOME subst ∧
  appFPexp rhs subst = SOME eNew ⇒
  ∀ x. x IN FV (eNew) ⇒ P x
Proof
  Induct_on ‘rhs’
  \\ rewrite_tac[appFPexp_def] \\ simp[CaseEq "option"] \\ rpt strip_tac
  \\ rveq \\ pop_assum mp_tac
  \\ rewrite_tac[semanticPrimitivesPropsTheory.FV_def, IN_UNION]
  \\ imp_res_tac match_preserves_FV_lookup
  \\ rpt strip_tac \\ res_tac \\ fs[]
QED

Theorem rewrite_preserves_FV:
  ∀ rws e eNew P.
  (∀ x. x IN FV e ⇒ P x) ∧
  rewriteFPexp rws e = eNew ⇒
  ∀ x. x IN FV eNew ⇒ P x
Proof
  Induct_on ‘rws’ \\ gs[rewriteFPexp_def]
  \\ rpt strip_tac \\ Cases_on ‘h’ \\ gs[rewriteFPexp_def]
  \\ pop_assum mp_tac \\ COND_CASES_TAC \\ gs[]
  \\ TOP_CASE_TAC \\ gs[]
  >- (first_x_assum $ qspecl_then [‘e’, ‘P’] mp_tac \\ impl_tac \\ gs[])
  \\ TOP_CASE_TAC \\ gs[]
  >- (first_x_assum $ qspecl_then [‘e’, ‘P’] mp_tac \\ impl_tac \\ gs[])
  \\ strip_tac
  \\ first_x_assum $ qspecl_then [‘x''’, ‘P’] mp_tac \\ impl_tac \\ gs[]
  \\ qspecl_then [‘r’, ‘q’, ‘e’, ‘x''’, ‘x'’, ‘[]’, ‘P’]  mp_tac match_preserves_FV
  \\ impl_tac \\ gs[substLookup_def]
QED

Theorem isFpArithExp_match_preserved:
  ∀ rhs lhs e subst eNew.
    isFpArithExp e ∧
    isFpArithPat rhs ∧
    matchesFPexp lhs e [] = SOME subst ⇒
    appFPexp rhs subst = SOME eNew ⇒
    isFpArithExp eNew
Proof
  Induct_on ‘rhs’ \\ fs[appFPexp_def, isFpArithExp_def, isFpArithPat_def]
  >- (rpt strip_tac \\ drule isFpArithExp_all_lookup
      \\ disch_then $ qspecl_then [‘lhs’, ‘subst’, ‘[]’, ‘n’, ‘eNew’] mp_tac
      \\ impl_tac \\ gs[substLookup_def])
  >- (rpt strip_tac \\ rveq \\ fs[isFpArithExp_def]
      \\ first_x_assum drule \\ rpt (disch_then drule) \\ fs[])
  >- (rpt strip_tac \\ fs[CaseEq"option"]
      \\ rveq \\ fs[isFpArithExp_def]
      \\ conj_tac
      >- (last_x_assum drule \\ rpt (disch_then drule) \\ fs[])
      \\ first_x_assum drule \\ rpt (disch_then drule) \\ fs[])
  >- (rpt strip_tac \\ fs[CaseEq"option"]
      \\ rveq \\ fs[isFpArithExp_def]
      \\ rpt conj_tac
      >- (last_x_assum drule \\ rpt (disch_then drule) \\ fs[])
      >- (last_x_assum kall_tac \\ last_x_assum drule
          \\ rpt (disch_then drule) \\ fs[])
      \\ first_x_assum drule \\ rpt (disch_then drule) \\ fs[])
QED

Theorem isFpArithExp_rewrite_preserved:
  ∀ rws e.
    rewriteFPexp rws e ≠ e ⇒
    isFpArithExp (rewriteFPexp rws e) ∧
    isFpArithExp e
Proof
  Induct_on ‘rws’ \\ gs[rewriteFPexp_def]
  \\ rpt gen_tac  \\ Cases_on ‘h’
  \\ gs[rewriteFPexp_def]
  \\ COND_CASES_TAC \\ gs[]
  \\ rpt (TOP_CASE_TAC \\ gs[])
  \\ ‘isFpArithExp x'’
    by (drule isFpArithExp_match_preserved
        \\ disch_then $ qspecl_then [‘r’, ‘q’, ‘x’, ‘x'’] mp_tac
        \\ impl_tac \\ fs[])
  \\ Cases_on ‘rewriteFPexp rws x' ≠ x'’ \\ gs[]
QED

Theorem rewriteFPexp_returns_fp:
  ∀ (st:'a semanticPrimitives$state) st2 e lhs rhs env eOpt r.
  (∀ x.
     x IN FV (e) ⇒
     ∃ fp.
       nsLookup env.v x = SOME (FP_WordTree fp)) ∧
  isPureExp e ∧
  isFpArithExp e ∧
  rewriteFPexp [(lhs,rhs)] e = eOpt ∧
  evaluate st env [eOpt] = (st2, Rval [r]) ⇒
  ∃ fp. r = (FP_WordTree fp)
Proof
  rpt gen_tac \\ gs[rewriteFPexp_def] \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  >~ [‘appFPexp rhs subst = SOME eOpt’]
  >- (
    ‘isFpArithExp eOpt’
     by (drule isFpArithExp_match_preserved
         \\ rpt (disch_then drule) \\ fs[])
    \\ ‘∀ x. x IN FV eOpt ⇒
             ∃ r fp.
               nsLookup env.v x = SOME (FP_WordTree fp)’
      by (
      qspecl_then [‘rhs’, ‘lhs’, ‘e’, ‘eOpt’, ‘subst’, ‘[]’,
                   ‘λ x. ∃ r fp. nsLookup env.v x = SOME (FP_WordTree fp)’]
        mp_tac match_preserves_FV
      \\ impl_tac \\ fs[substLookup_def])
    \\ drule $ CONJUNCT1 isFpArithExp_matched_evaluates
    \\ disch_then (qspecl_then [‘env’, ‘st’] strip_assume_tac)
    \\ gs[])
  \\ drule $ CONJUNCT1 isFpArithExp_matched_evaluates
  \\ disch_then (qspecl_then [‘env’, ‘st’] strip_assume_tac)
  \\ gs[]
QED

Theorem rewriteFPexp_returns_real:
  ∀ (st:'a semanticPrimitives$state) st2 e lhs rhs env eOpt r.
  (∀ x.
     x IN FV (e) ⇒
     ∃ r.
       nsLookup env.v x = SOME (Real r)) ∧
  isPureExp e ∧
  isFpArithExp e ∧
  rewriteFPexp [(lhs,rhs)] e = eOpt ∧
  st.fp_state.real_sem ∧
  evaluate st env [realify eOpt] = (st2, Rval [r]) ⇒
  ∃ rn. r = Real rn
Proof
  rpt gen_tac \\ gs[rewriteFPexp_def] \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  >~ [‘appFPexp rhs subst = SOME eOpt’]
  >- (
    ‘isFpArithExp eOpt’
     by (drule isFpArithExp_match_preserved
         \\ rpt (disch_then drule) \\ fs[])
    \\ ‘∀ x. x IN FV eOpt ⇒
             ∃ r.
               nsLookup env.v x = SOME (Real r)’
      by (
      qspecl_then [‘rhs’, ‘lhs’, ‘e’, ‘eOpt’, ‘subst’, ‘[]’,
                   ‘λ x. ∃ r. nsLookup env.v x = SOME (Real r)’]
        mp_tac match_preserves_FV
      \\ impl_tac \\ fs[substLookup_def])
    \\ drule $ CONJUNCT1 isFpArithExp_matched_evaluates_real
    \\ disch_then (qspecl_then [‘env’, ‘st’] strip_assume_tac)
    \\ gs[])
  \\ drule $ CONJUNCT1 isFpArithExp_matched_evaluates_real
  \\ disch_then (qspecl_then [‘env’, ‘st’] strip_assume_tac)
  \\ gs[]
QED

Theorem matchExpr_preserving:
  ! p.
    (! e s1 s2.
     matchesFPexp p e s1 = SOME s2 ==>
      substMonotone s1 s2)
Proof
  Induct_on `p`
  \\ simp[Once matchesFPexp_def, option_case_eq]
  \\ rpt gen_tac
  \\ TRY (rpt strip_tac \\ rveq \\ fs[substMonotone_def]
          \\ rpt strip_tac \\ fs[substLookup_substAdd_alt]
          \\ TOP_CASE_TAC \\ fs[] \\ NO_TAC)
  \\ rpt (TOP_CASE_TAC \\ fs[substMonotone_def])
  \\ rpt strip_tac \\ res_tac
  \\ rveq \\ first_x_assum irule \\ fs[]
QED

Theorem appFPexp_weakening:
  ! p.
    (! e s1 s2.
      substMonotone s1 s2 /\
      appFPexp p s1 = SOME e ==>
      appFPexp p s2 = SOME e)
Proof
  Induct_on `p`
  \\ rpt strip_tac \\ fs[]
  \\ fs[appFPexp_def, pair_case_eq, option_case_eq, substMonotone_def]
  \\ res_tac \\ fs[]
QED

Theorem subst_pat_is_exp:
  ! p e s1 s2.
      matchesFPexp p e s1 = SOME s2 ==>
      appFPexp p s2 = SOME e
Proof
  Induct_on `p`
  \\ rpt gen_tac
  \\ simp[Once matchesFPexp_def, option_case_eq]
  \\ rpt (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac \\ rveq
  \\ fs[Once appFPexp_def]
  \\ simp [substLookup_substAdd_alt]
  \\ res_tac \\ fs[]
  \\ imp_res_tac matchExpr_preserving
  \\ imp_res_tac (SIMP_RULE std_ss [FORALL_AND_THM] appFPexp_weakening)
  \\ res_tac \\ fs[]
QED

val _ = export_theory();

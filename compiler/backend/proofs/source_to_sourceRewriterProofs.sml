(*
  Correctness proofs for the expression rewriting function
  Shows that matchesExpr e p = SOME s ==> appExpr p s = SOME e
*)
open source_to_sourceIcingTheory fpOptPropsTheory semanticPrimitivesTheory evaluateTheory
     terminationTheory fpSemPropsTheory;
open preamble;

val _ = new_theory "source_to_sourceRewriterProofs";

Theorem no_match_word_cond:
  ! w e s1 s2.
    matchesFPcexp (Word w) e s1 = SOME s2 ==> F
Proof
  rpt strip_tac
  \\ Cases_on `e` \\ fs[matchesFPcexp_def]
  \\ rename [`App op l`]
  \\ Cases_on `l` \\ fs[matchesFPcexp_def]
  \\ Cases_on `t` \\ fs[matchesFPcexp_def]
QED

Theorem no_match_var_cond:
  ! n e s1 s2.
    matchesFPcexp (Var n) e s1 = SOME s2 ==> F
Proof
  rpt strip_tac
  \\ Cases_on `e` \\ fs[matchesFPcexp_def]
  \\ rename [`App op l`]
  \\ Cases_on `l` \\ fs[matchesFPcexp_def]
  \\ Cases_on `t` \\ fs[matchesFPcexp_def]
QED

Theorem matchExpr_preserving:
  ! p.
    (! e s1 s2.
     matchesFPexp p e s1 = SOME s2 ==>
      substMonotone s1 s2)
  /\
    (! ce s1 s2.
      matchesFPcexp p ce s1 = SOME s2 ==>
      substMonotone s1 s2)
Proof
  Induct_on `p`
  \\ simp[no_match_word_cond, no_match_var_cond]
  \\ rpt gen_tac \\ TRY conj_tac
  \\ simp[Once matchesFPexp_def, option_case_eq]
  \\ simp[Once matchesFPcexp_def]
  \\ TRY (fs[substMonotone_def] \\ rpt strip_tac \\ imp_res_tac substLookup_substUpdate \\ rveq \\ fs[] \\ NO_TAC)
  \\ rpt gen_tac
  \\ rpt (TOP_CASE_TAC \\ fs[substMonotone_def]) \\ rpt strip_tac \\ fs[substMonotone_def]
  \\ rpt res_tac
QED

Theorem appFPexp_weakening:
  ! p.
    (! e s1 s2.
      substMonotone s1 s2 /\
      appFPexp p s1 = SOME e ==>
      appFPexp p s2 = SOME e) /\
    (! ce s1 s2.
      substMonotone s1 s2 /\
      appFPcexp p s1 = SOME ce ==>
      appFPcexp p s2 = SOME ce)
Proof
  Induct_on `p`
  \\ rpt strip_tac \\ fs[]
  \\ fs[appFPexp_def, appFPcexp_def, pair_case_eq, option_case_eq, substMonotone_def]
  \\ res_tac \\ fs[]
QED

val exprSolve_tac =
  (let
    val thms = CONJ_LIST 2 (SIMP_RULE std_ss [FORALL_AND_THM] appFPexp_weakening)
  in
  (irule (hd thms) ORELSE irule (hd (tl thms)))
  end)
  \\ asm_exists_tac \\ fs[substMonotone_def]
  \\ rpt strip_tac
  \\ imp_res_tac matchExpr_preserving \\ fs[substMonotone_def];

Theorem subst_pat_is_exp:
  ! p.
    (! e s1 s2.
      matchesFPexp p e s1 = SOME s2 ==>
      appFPexp p s2 = SOME e) /\
    (! ce s1 s2.
      matchesFPcexp p ce s1 = SOME s2 ==>
      appFPcexp p s2 = SOME ce)
Proof
  Induct_on `p` \\ rpt gen_tac \\ conj_tac
  \\ rpt gen_tac
  \\ simp[Once matchesFPexp_def]
  \\ simp[Once matchesFPcexp_def, option_case_eq]
  \\ rpt (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac \\ rveq
  \\ fs[Once appFPexp_def, Once appFPcexp_def]
  \\ TRY (imp_res_tac substLookup_substUpdate \\ fs[])
  \\ res_tac \\ fs[]
  \\ rpt conj_tac \\ exprSolve_tac
QED

val _ = export_theory();

(*
  Correctness proofs for the expression rewriting function
  Shows that matchesExpr e p = SOME s ==> appExpr p s = SOME e
*)
open source_rewriterTheory source_to_sourceTheory fpOptTheory fpOptPropsTheory
     fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
     semanticsTheory semanticsPropsTheory
     evaluatePropsTheory terminationTheory fpSemPropsTheory;
open preamble;

val _ = new_theory "source_rewriterProofs";

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

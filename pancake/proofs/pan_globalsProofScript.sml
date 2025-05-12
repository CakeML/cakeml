(*
  Correctness proof for pan_globals
*)

open preamble
     panSemTheory panLangTheory pan_globalsTheory panPropsTheory

val _ = new_theory "pan_globalsProof";

val _ = set_grammar_ancestry  ["panSem", "pan_globals", "panProps", "panLang"];

val s = ``s:('a,'ffi) panSem$state``

Theorem resort_decls_evaluate:
  ∀s decs. evaluate_decls s (resort_decls decs) = evaluate_decls s decs
Proof
  Induct_on ‘decs’ >> gvs[resort_decls_def] >>
  Cases >>
  gvs[is_function_def,evaluate_decls_def] >>
  strip_tac >>
  irule EQ_TRANS >>
  first_x_assum $ irule_at $ Pos last >>
  qmatch_goalsub_abbrev_tac ‘a1 ++ _’ >>
  ‘EVERY ($¬ ∘ is_function) a1’
    by(gvs[Abbr ‘a1’] >> rw[EVERY_MEM,MEM_FILTER]) >>
  rename1 ‘_::a2’ >>
  last_x_assum kall_tac >>
  qid_spec_tac ‘a2’ >>
  qid_spec_tac ‘s’ >>
  Induct_on ‘a1’ using SNOC_INDUCT
  >- simp[evaluate_decls_def] >>
  Cases >>
  rw[SNOC_APPEND,is_function_def] >>
  SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND] >>
  gvs[] >>
  irule EQ_TRANS >>
  first_x_assum $ irule_at $ Pos last >>
  simp[evaluate_decls_append,evaluate_decl_commute]
QED

val _ = export_theory();

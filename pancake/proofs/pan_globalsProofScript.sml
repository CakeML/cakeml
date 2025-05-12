(*
  Correctness proof for pan_globals
*)

open preamble
     panSemTheory panLangTheory pan_globalsTheory panPropsTheory

val _ = new_theory "pan_globalsProof";

val _ = set_grammar_ancestry  ["panSem", "pan_globals", "panProps", "panLang"];

val s = ``s:('a,'ffi) panSem$state``

Definition state_rel_def:
  state_rel ctxt s t ⇔
  s.top_addr = t.top_addr - ctxt.globals_size ∧
  s.locals = t.locals ∧
  s.base_addr = t.base_addr ∧
  (∀v val.
     FLOOKUP s.globals v = SOME val ⇒
     ∃addr. FLOOKUP ctxt.globals v = SOME(shape_of val, addr) ∧
            mem_load (shape_of val) (t.top_addr - addr) t.memaddrs t.memory = SOME val
  ) ∧
  s.memaddrs ⊆ t.memaddrs
End

Theorem compile_exp_correct:
  ∀s e v ctxt t.
  state_rel ctxt s t ∧
  eval s e = SOME v
  ⇒
  eval t (compile_exp ctxt e) = SOME v
Proof
  recInduct eval_ind >> rpt strip_tac
  >~ [‘Var Global’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs(),state_rel_def] >>
      first_x_assum drule >>
      rw[] >> rw[eval_def,wordLangTheory.word_op_def])
  >~ [‘Struct’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs()] >>
      simp[OPT_MMAP_MAP_o] >>
      irule EQ_TRANS >>
      first_assum $ irule_at $ Pos last >>
      irule OPT_MMAP_CONG >>
      rw[] >>
      first_x_assum $ drule_then drule >>
      drule_all pan_commonPropsTheory.opt_mmap_mem_func >>
      strip_tac >> gvs[])
  >~ [‘Load’]
  >- (cheat (* memory *)
     )
  >~ [‘LoadByte’]
  >- (cheat (* memory *)
     )
  >~ [‘Op’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs()] >>
      first_assum $ irule_at $ Pos last >>
      simp[OPT_MMAP_MAP_o] >>
      irule EQ_TRANS >>
      first_assum $ irule_at $ Pos last >>
      irule OPT_MMAP_CONG >>
      rw[] >>
      first_x_assum $ drule_then drule >>
      drule_all pan_commonPropsTheory.opt_mmap_mem_func >>
      strip_tac >> gvs[])
  >~ [‘Panop’]
  >- (gvs[eval_def,compile_exp_def,AllCaseEqs()] >>
      first_assum $ irule_at $ Pos last >>
      simp[OPT_MMAP_MAP_o] >>
      irule EQ_TRANS >>
      first_assum $ irule_at $ Pos last >>
      irule OPT_MMAP_CONG >>
      rw[] >>
      first_x_assum $ drule_then drule >>
      drule_all pan_commonPropsTheory.opt_mmap_mem_func >>
      strip_tac >> gvs[]) >>
  gvs[wordLangTheory.word_op_def,state_rel_def,eval_def,compile_exp_def,AllCaseEqs()]
QED

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

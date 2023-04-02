(*

composing semantics correctness from pan to target

*)

open preamble
     backendProofTheory pan_to_wordProofTheory
     pan_to_targetTheory

val _ = new_theory "pan_to_targetProof";

Overload stack_remove_prog_comp[local] = ``stack_remove$prog_comp``
Overload stack_alloc_prog_comp[local] = ``stack_alloc$prog_comp``
Overload stack_names_prog_comp[local] = ``stack_names$prog_comp``
Overload word_to_word_compile[local] = ``word_to_word$compile``
Overload word_to_stack_compile[local] = ``word_to_stack$compile``
Overload stack_to_lab_compile[local] = ``stack_to_lab$compile``
Overload pan_to_word_compile_prog[local] = ``pan_to_word$compile_prog
``

Theorem pan_to_lab_good_code_lemma:
  compile c.stack_conf c.data_conf lim1 lim2 offs stack_prog = code ∧
  compile asm_conf3 word_prog = (bm, wc, fs, stack_prog) ∧
  word_to_word$compile word_conf asm_conf3 word_prog0 = (col, word_prog) ∧
  compile_prog pan_prog = word_prog0 ∧
  stack_to_labProof$labels_ok code ∧
  all_enc_ok_pre conf code ⇒
  lab_to_targetProof$good_code conf LN code
Proof
  (* start of 'good_code' proof for initial compilation *)
  rw []
  \\ qmatch_asmsub_abbrev_tac `stack_to_labProof$labels_ok lab_prog`
  \\ fs[lab_to_targetProofTheory.good_code_def]
  \\ CONJ_TAC >- fs[Abbr `lab_prog`, stack_to_labTheory.compile_def]
  \\ CONJ_ASM1_TAC >- (
    fs [stack_to_labProofTheory.labels_ok_def]
    \\ qpat_x_assum `all_enc_ok_pre _ _` kall_tac
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC)
    \\ simp[] \\ Cases \\ simp[]
    \\ metis_tac [labPropsTheory.EVERY_sec_label_ok]
  )
  \\ CONJ_TAC >- (
    fs [stack_to_labProofTheory.labels_ok_def]
    \\ qmatch_asmsub_abbrev_tac `ALL_DISTINCT (MAP ff _)`
    \\ `ff = Section_num` by
      (simp[Abbr`ff`,FUN_EQ_THM]>>Cases>>simp[])
    \\ fs [])
  \\ CONJ_TAC >- (
    fs [stack_to_labProofTheory.labels_ok_def]
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC
      \\ simp[] \\ Cases \\ simp[] \\ NO_TAC)
  )
  \\ qpat_x_assum`Abbrev(lab_prog = _)` mp_tac
  \\ simp[markerTheory.Abbrev_def]
  \\disch_then (assume_tac o SYM)
  \\ drule stack_to_labProofTheory.stack_to_lab_stack_good_handler_labels
  \\ simp []
  \\ disch_then match_mp_tac
  \\ qmatch_asmsub_abbrev_tac ‘word_to_word$compile _ _ wprog’
  \\ pop_assum $ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ drule pan_to_word_good_handlers
  \\ disch_tac
  \\ drule data_to_wordProofTheory.word_good_handlers_word_to_word
  \\ disch_then (qspecl_then [‘word_conf’, ‘asm_conf3’] assume_tac)
  \\ drule (INST_TYPE [beta|->alpha] word_to_stackProofTheory.word_to_stack_good_handler_labels)
  \\ strip_tac
  \\ pop_assum $ irule
  \\ simp []
  \\ qexists_tac ‘asm_conf3’>>gs[]
QED

Theorem word_to_stack_compile_FST:
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ⇒
  MAP FST p =
  raise_stub_location::store_consts_stub_location::MAP FST wprog
Proof
  strip_tac>>gs[word_to_stackTheory.compile_def]>>
  pairarg_tac>>gs[]>>rveq>>gs[]>>
  drule_then irule word_to_stackProofTheory.MAP_FST_compile_word_to_stack
QED

Theorem pan_to_stack_first_ALL_DISTINCT:
  pan_to_word_compile_prog pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST pan_code) ⇒
  ALL_DISTINCT (MAP FST p)
Proof
  strip_tac>>drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>
  drule backendProofTheory.compile_to_word_conventions2>>strip_tac>>
  gs[]>>
  qpat_x_assum ‘MAP FST wprog = _’ $ assume_tac o GSYM>>gs[]>>
  drule word_to_stack_compile_FST>>
  strip_tac>>gs[]>>
  drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>
  strip_tac>>
  gs[GSYM EVERY_MAP]>>EVAL_TAC>>gs[EVERY_MEM]>>
  rw[]>- (first_x_assum $ qspec_then ‘5’ assume_tac>>gs[])>>
  first_x_assum $ qspec_then ‘6’ assume_tac>>gs[]
QED

Theorem pan_to_stack_compile_lab_pres:
  pan_to_word$compile_prog pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 =(col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST pan_code) ⇒
  ALL_DISTINCT (MAP FST p) ∧
  EVERY (λn. n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gc_stub_location) (MAP FST p) ∧
  EVERY
  (λ(n,p).
     (let
        labs = extract_labels p
      in
        EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
        ALL_DISTINCT labs)) p
Proof
  strip_tac>>
  drule pan_to_wordProofTheory.pan_to_word_compile_lab_pres>>strip_tac>>
  gs[]>>
  drule backendProofTheory.compile_to_word_conventions2>>
  strip_tac>>
  drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>gs[]>>
  ‘EVERY
   (λ(n,m,p).
      (let
         labs = extract_labels p
       in
         EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
         ALL_DISTINCT labs)) wprog’
    by (gs[EVERY2_EVERY]>>gs[EVERY_EL]>>ntac 2 strip_tac>>
        ntac 3 (first_x_assum $ qspec_then ‘n’ assume_tac)>>
        pairarg_tac>>gs[EL_ZIP, word_simpProofTheory.labels_rel_def]>>
        pairarg_tac>>gs[EL_MAP]>>strip_tac>>strip_tac>>
        ‘EL n (MAP FST wprog) = EL n (MAP FST wprog0)’ by rfs[]>>
        gs[EL_MAP]>>
        pairarg_tac>>gs[]>>
        ‘(l1, l2) ∈ set (extract_labels p'')’
          by (gs[MEM_SET_TO_LIST, SUBSET_DEF]>>
              first_assum irule>>metis_tac[MEM_EL])>>
        gs[MEM_EL]>>
        first_x_assum $ qspec_then ‘n''''’ assume_tac>>
        gs[]>>pairarg_tac>>gs[])>>
  drule (INST_TYPE [beta|->alpha] word_to_stackProofTheory.word_to_stack_compile_lab_pres)>>
  disch_then $ qspec_then ‘mc.target.config’ assume_tac>>
  drule_all pan_to_stack_first_ALL_DISTINCT>>
  strip_tac>>gs[]>>
  strip_tac>>gs[backend_commonTheory.stack_num_stubs_def]>>
  gs[backend_commonTheory.word_num_stubs_def,
     wordLangTheory.store_consts_stub_location_def,
     wordLangTheory.raise_stub_location_def,
     stackLangTheory.gc_stub_location_def,
     backend_commonTheory.stack_num_stubs_def]>>
  drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>
  gs[GSYM EVERY_MAP, EVERY_MEM]>>ntac 3 strip_tac>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>gs[]
QED

Theorem pan_to_lab_labels_ok:
  pan_to_word_compile_prog pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  stack_to_lab_compile c.stack_conf c.data_conf max_heap sp mc.target.config.addr_offset p = lprog ∧
  ALL_DISTINCT (MAP FST pan_code) ⇒
  labels_ok lprog
Proof
  strip_tac>>
  qpat_x_assum ‘_ = lprog’ (assume_tac o GSYM)>>gs[]>>
  irule stack_to_labProofTheory.stack_to_lab_compile_lab_pres>>
  drule_all pan_to_stack_compile_lab_pres>>gs[]
QED

(** stack_to_lab$good_code **)

Theorem word_to_stack_good_code_lemma:
  word_to_word_compile c.word_to_word_conf mc.target.config
          (pan_to_word_compile_prog pan_code) = (col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  LENGTH mc.target.config.avoid_regs + 13 ≤ mc.target.config.reg_count ∧
         (* from backend_config_ok c *)
  ALL_DISTINCT (MAP FST pan_code) ⇒
  good_code (mc.target.config.reg_count −
           (LENGTH mc.target.config.avoid_regs + 3)) p
Proof
  gs[stack_to_labProofTheory.good_code_def]>>strip_tac>>
  qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
  qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
  drule_all pan_to_stack_compile_lab_pres>>strip_tac>>gs[]>>
  drule backendProofTheory.compile_to_word_conventions2>>
  strip_tac>>
  drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>gs[]>>
  drule word_to_stack_compile_FST>>strip_tac>>
  drule word_to_stackProofTheory.word_to_stack_stack_convs>>
  gs[]>>impl_tac
  >- (gs[EVERY_EL]>>
      ntac 2 strip_tac>>
      ntac 3 (first_x_assum $ qspec_then ‘n’ assume_tac)>>
      gs[]>>
      pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>simp[EL_MAP])>>
  strip_tac>>gs[backend_commonTheory.stack_num_stubs_def]>>
  gs[EVERY_EL]>>rpt strip_tac>>
  pairarg_tac>>gs[EL_MAP]>>
  qpat_x_assum ‘∀n. _ ⇒ alloc_arg _’ $ qspec_then ‘n’ assume_tac>>
  gs[]>>

  drule pan_to_word_compile_prog_lab_min>>
  gs[GSYM EVERY_MAP]>>
  qpat_x_assum ‘MAP FST _ = MAP FST _’ $ assume_tac o GSYM>>
  gs[]>>
  gs[GSYM EVERY_MAP, EVERY_MEM]>>strip_tac>>
  ‘MEM k (MAP FST p)’
    by (gs[MEM_MAP]>>gs[MEM_EL]>>gs[PULL_EXISTS]>>
        first_assum $ irule_at (Pos last)>>gs[])>>
  gs[backend_commonTheory.word_num_stubs_def,
     wordLangTheory.store_consts_stub_location_def,
     wordLangTheory.raise_stub_location_def,
     backend_commonTheory.stack_num_stubs_def]>>
  first_x_assum $ qspec_then ‘k’ assume_tac>>gs[]
QED

val _ = export_theory();

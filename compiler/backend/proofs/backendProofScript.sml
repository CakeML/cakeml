open preamble primSemEnvTheory semanticsPropsTheory
     backendTheory
     source_to_flatProofTheory
     flat_to_patProofTheory
     pat_to_closProofTheory
     clos_to_bvlProofTheory
     bvl_to_bviProofTheory
     bvi_to_dataProofTheory
     data_to_wordProofTheory
     word_to_stackProofTheory
     stack_to_labProofTheory
     lab_to_targetProofTheory
     backend_commonTheory
local open dataPropsTheory in end
open word_to_stackTheory

val _ = new_theory"backendProof";

val _ = Parse.set_grammar_ancestry
  [ "backend",
    "backend_common",
    "primSemEnv", "semanticsProps",
    "labProps" (* for good_dimindex *)
  ];

(* TODO: move *)

val WORD_LS_IMP = Q.store_thm("WORD_LS_IMP",
  `a <=+ b ==>
    ?k. Abbrev (b = a + n2w k) /\
        w2n (b - a) = k /\
        (!w. a <=+ w /\ w <+ b <=> ?i. w = a + n2w i /\ i < k)`,
  Cases_on `a` \\ Cases_on `b` \\ fs [WORD_LS]
  \\ fs [markerTheory.Abbrev_def]
  \\ full_simp_tac std_ss [GSYM word_sub_def,addressTheory.word_arith_lemma2]
  \\ fs [] \\ rw [] THEN1
   (rewrite_tac [GSYM word_sub_def]
    \\ once_rewrite_tac [WORD_ADD_COMM]
    \\ rewrite_tac [WORD_ADD_SUB])
  \\ Cases_on `w` \\ fs [WORD_LO,word_add_n2w]
  \\ eq_tac \\ rw [] \\ fs []
  \\ rename1 `k < m:num` \\ qexists_tac `k - n` \\ fs [])

val MOD_SUB_LEMMA = Q.store_thm("MOD_SUB_LEMMA",
  `n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0`,
  Cases_on `m <= n` \\ fs []
  \\ imp_res_tac LESS_EQ_EXISTS \\ rw []
  \\ qpat_x_assum `(m + _) MOD k = 0` mp_tac
  \\ drule MOD_PLUS
  \\ disch_then (fn th => once_rewrite_tac [GSYM th]) \\ fs []);

val LESS_MULT_LEMMA = Q.store_thm("LESS_MULT_LEMMA",
  `n1 < n2 /\ d < k ==> k * n1 + d < k * n2:num`,
  Cases_on `n2` \\ fs [MULT_CLAUSES] \\ rw []
  \\ fs [DECIDE ``n1 < SUC k <=> n1 <= k``]
  \\ match_mp_tac (DECIDE ``n < n' /\ m <= m' ==> n + m < n' + m':num``)
  \\ fs []);

val word_list_exists_imp = Q.store_thm("word_list_exists_imp",
  `dm = stack_removeProof$addresses a n /\
    dimindex (:'a) DIV 8 * n < dimword (:'a) ∧ good_dimindex (:'a) ⇒
    word_list_exists a n (fun2set (m1,dm:'a word set))`,
  metis_tac [stack_removeProofTheory.word_list_exists_addresses]);

val byte_aligned_mult = Q.store_thm("byte_aligned_mult",
  `good_dimindex (:'a) ==>
    byte_aligned (a + bytes_in_word * n2w i) = byte_aligned (a:'a word)`,
  fs [alignmentTheory.byte_aligned_def,labPropsTheory.good_dimindex_def]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM (EVAL ``2n**2``),GSYM (EVAL ``2n**3``), aligned_add_pow]);

val byte_aligned_MOD = Q.store_thm("byte_aligned_MOD",`
  good_dimindex (:'a) ⇒
  ∀x:'a word.x ∈ byte_aligned ⇒
  w2n x MOD (dimindex (:'a) DIV 8) = 0`,
  rw[IN_DEF]>>
  fs [aligned_w2n, alignmentTheory.byte_aligned_def]>>
  rfs[labPropsTheory.good_dimindex_def] \\ rfs []);

val extend_with_resource_limit_not_fail = Q.store_thm("extend_with_resource_limit_not_fail",
  `x ∈ extend_with_resource_limit y ∧ Fail ∉ y ⇒ x ≠ Fail`,
  rw[extend_with_resource_limit_def] \\ metis_tac[])

val fun2set_disjoint_union = Q.store_thm("fun2set_disjoint_union",
  `
   DISJOINT d1 d2 ∧
  p (fun2set (m,d1)) ∧
   q (fun2set (m,d2))
   ⇒ (p * q) (fun2set (m,d1 ∪ d2))`,
  rw[set_sepTheory.fun2set_def,set_sepTheory.STAR_def,set_sepTheory.SPLIT_def]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ simp[]
  \\ first_assum(part_match_exists_tac (last o strip_conj) o concl) \\ simp[]
  \\ simp[EXTENSION]
  \\ conj_tac >- metis_tac[]
  \\ fs[IN_DISJOINT,FORALL_PROD]);

(* -- *)

val prim_config = prim_config_eq |> concl |> lhs

val backend_config_ok_def = Define`
  backend_config_ok (c:'a config) ⇔
    c.source_conf = ^prim_config.source_conf ∧
    0 < c.clos_conf.max_app ∧
    c.bvl_conf.next_name2 = bvl_num_stubs + 2 ∧
    LENGTH c.lab_conf.asm_conf.avoid_regs + 13 ≤ c.lab_conf.asm_conf.reg_count ∧
    c.lab_conf.pos = 0 ∧
    c.lab_conf.labels = LN ∧
    conf_ok (:'a) c.data_conf ∧
    (c.data_conf.has_longdiv ⇒ c.lab_conf.asm_conf.ISA = x86_64) /\
    (c.data_conf.has_div ⇒
      c.lab_conf.asm_conf.ISA = ARMv8 ∨ c.lab_conf.asm_conf.ISA = MIPS ∨
      c.lab_conf.asm_conf.ISA = RISC_V) ∧
    max_stack_alloc ≤ 2 * max_heap_limit (:'a) c.data_conf − 1 ∧
    addr_offset_ok c.lab_conf.asm_conf 0w ∧
    (∀w. -8w ≤ w ∧ w ≤ 8w ⇒ byte_offset_ok c.lab_conf.asm_conf w) ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 8w ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 4w ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 1w ∧
    c.lab_conf.asm_conf.valid_imm (INL Sub) 1w ∧
    find_name c.stack_conf.reg_names PERMUTES UNIV ∧
    names_ok c.stack_conf.reg_names c.lab_conf.asm_conf.reg_count c.lab_conf.asm_conf.avoid_regs ∧
    stackProps$fixed_names c.stack_conf.reg_names c.lab_conf.asm_conf ∧
    (∀s. addr_offset_ok c.lab_conf.asm_conf (store_offset s)) ∧
    (∀n.
         n ≤ max_stack_alloc ⇒
         c.lab_conf.asm_conf.valid_imm (INL Sub) (n2w (n * (dimindex (:α) DIV 8))) ∧
         c.lab_conf.asm_conf.valid_imm (INL Add) (n2w (n * (dimindex (:α) DIV 8))))`;

val backend_config_ok_with_bvl_conf_updated = Q.store_thm("backend_config_ok_with_bvl_conf_updated[simp]",
  `(f cc.bvl_conf).next_name2 = cc.bvl_conf.next_name2 ⇒
   (backend_config_ok (cc with bvl_conf updated_by f) ⇔ backend_config_ok cc)`,
  rw[backend_config_ok_def]);

val backend_config_ok_with_word_to_word_conf_updated = Q.store_thm("backend_config_ok_with_word_to_word_conf_updated[simp]",
  `backend_config_ok (cc with word_to_word_conf updated_by f) ⇔ backend_config_ok cc`,
  rw[backend_config_ok_def]);

val backend_config_ok_call_empty_ffi = store_thm("backend_config_ok_call_empty_ffi[simp]",
  ``backend_config_ok (cc with
      data_conf updated_by (λc. c with call_empty_ffi updated_by x)) =
    backend_config_ok cc``,
  fs [backend_config_ok_def,data_to_wordTheory.conf_ok_def,
      data_to_wordTheory.shift_length_def,
      data_to_wordTheory.max_heap_limit_def]);

(* TODO: ?? where to put these ?? *)
val mc_init_ok_def = Define`
  mc_init_ok c mc ⇔
  EVERY (λr. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] ∧
  find_name c.stack_conf.reg_names 4 = mc.len2_reg ∧
  find_name c.stack_conf.reg_names 3 = mc.ptr2_reg ∧
  find_name c.stack_conf.reg_names 2 = mc.len_reg ∧
  find_name c.stack_conf.reg_names 1 = mc.ptr_reg ∧
  find_name c.stack_conf.reg_names 0 =
    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ∧
  (* the next four are implied by injectivity of find_name *)
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len2_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr2_reg ∧
  ¬MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs ∧
   c.lab_conf.asm_conf = mc.target.config`

val mc_init_ok_with_bvl_conf_updated = Q.store_thm("mc_init_ok_with_bvl_conf_updated[simp]",
  `mc_init_ok (cc with bvl_conf updated_by f) mc ⇔ mc_init_ok cc mc`,
  rw[mc_init_ok_def]);

val mc_init_ok_with_word_to_word_conf_updated = Q.store_thm("mc_init_ok_with_word_to_word_conf_updated[simp]",
  `mc_init_ok (cc with word_to_word_conf updated_by f) mc ⇔ mc_init_ok cc mc`,
  rw[mc_init_ok_def]);

val mc_init_ok_call_empty_ffi = store_thm("mc_init_ok_call_empty_ffi[simp]",
  ``mc_init_ok (cc with
      data_conf updated_by (λc. c with call_empty_ffi updated_by x)) =
    mc_init_ok cc``,
  fs [mc_init_ok_def,data_to_wordTheory.conf_ok_def,
      data_to_wordTheory.shift_length_def,FUN_EQ_THM]);

val heap_regs_def = Define`
  heap_regs reg_names =
    (find_name reg_names 2, find_name reg_names 4)`;

val _ = temp_overload_on("bvl_inline_compile_prog",``bvl_inline$compile_prog``);
val _ = temp_overload_on("bvi_tailrec_compile_prog",``bvi_tailrec$compile_prog``);
val _ = temp_overload_on("bvi_to_data_compile_prog",``bvi_to_data$compile_prog``);
val _ = temp_overload_on("bvl_to_bvi_compile_prog",``bvl_to_bvi$compile_prog``);
val _ = temp_overload_on("bvl_to_bvi_compile_inc",``bvl_to_bvi$compile_inc``);
val _ = temp_overload_on("bvl_to_bvi_compile",``bvl_to_bvi$compile``);
val _ = temp_overload_on("bvi_to_data_compile",``bvi_to_data$compile``);
val _ = temp_overload_on("bvi_let_compile",``bvi_let$compile``);
val _ = temp_overload_on("bvl_const_compile",``bvl_const$compile``);
val _ = temp_overload_on("bvl_handle_compile",``bvl_handle$compile``);
val _ = temp_overload_on("bvl_inline_compile_inc",``bvl_inline$compile_inc``);
val _ = temp_overload_on("bvl_to_bvi_compile_exps",``bvl_to_bvi$compile_exps``);
val _ = temp_overload_on("pat_to_clos_compile",``pat_to_clos$compile``);
val _ = temp_overload_on("flat_to_pat_compile",``flat_to_pat$compile``);
val _ = temp_overload_on("stack_remove_prog_comp",``stack_remove$prog_comp``);
val _ = temp_overload_on("stack_alloc_prog_comp",``stack_alloc$prog_comp``);
val _ = temp_overload_on("stack_names_prog_comp",``stack_names$prog_comp``);

(* TODO: move things that need moving *)

(* word_to_stack *)
val word_get_code_labels_def = Define`
  (word_get_code_labels (Call r d a h) =
    (case d of SOME x => {x} | _ => {}) ∪
    (case r of SOME (_,_,x,_,_) => word_get_code_labels x | _ => {}) ∪
    (case h of SOME (_,x,l1,l2) => word_get_code_labels x | _ => {})) ∧
  (word_get_code_labels (Seq p1 p2) = word_get_code_labels p1 ∪ word_get_code_labels p2) ∧
  (word_get_code_labels (If _ _ _ p1 p2) = word_get_code_labels p1 ∪ word_get_code_labels p2) ∧
  (word_get_code_labels (MustTerminate p) = word_get_code_labels p) ∧
  (word_get_code_labels (LocValue _ l1) = {l1}) ∧
  (word_get_code_labels _ = {})`;
val _ = export_rewrites["word_get_code_labels_def"];

(* TODO: This seems like it must have been established before
  handler labels point only within the current table entry
*)

val word_good_handlers_def = Define`
  (word_good_handlers n (Call r d a h) <=>
    case r of
      NONE => T
    | SOME (_,_,x,_,_) => word_good_handlers n x ∧
    (case h of SOME (_,x,l1,_) => l1 = n ∧ word_good_handlers n x | _ => T)) ∧
  (word_good_handlers n (Seq p1 p2) <=> word_good_handlers n p1 ∧ word_good_handlers n p2) ∧
  (word_good_handlers n (If _ _ _ p1 p2) <=> word_good_handlers n p1 ∧ word_good_handlers n p2) ∧
  (word_good_handlers n (MustTerminate p) <=> word_good_handlers n p) ∧
  (word_good_handlers n _ <=> T)`;
val _ = export_rewrites["word_good_handlers_def"];

val _ = temp_overload_on("get_code_labels",``stack_to_labProof$get_code_labels``);
val _ = temp_overload_on("stack_get_handler_labels",``stack_to_labProof$stack_get_handler_labels``);
val _ = temp_overload_on("stack_good_code_labels",``stack_to_labProof$stack_good_code_labels``);

(* this is the only property needed of the wRegs  *)
val get_code_labels_wReg = Q.prove(`
  (∀n. get_code_labels (f n) = {}) ⇒
  get_code_labels (wRegWrite1 f n kf) = {} ∧
  get_code_labels (wRegWrite2 f n kf) = {}
  `,
  PairCases_on`kf`>>rw[wRegWrite1_def,wRegWrite2_def]) |> SIMP_RULE std_ss [IMP_CONJ_THM];

val get_code_handler_labels_wStackLoad = Q.prove(`
  ∀ls.
  get_code_labels (wStackLoad ls x) = get_code_labels x ∧
  stack_get_handler_labels n (wStackLoad ls x) = stack_get_handler_labels n x`,
  Induct>>fs[wStackLoad_def,FORALL_PROD]);

val wLive_code_labels = Q.prove(`
  wLive q bs kf = (q',bs') ⇒
  get_code_labels q' = {}`,
  PairCases_on`kf`>>rw[wLive_def]>>fs[]>>
  pairarg_tac>>fs[]>>rw[]);

val stack_move_code_labels = Q.prove(`
  ∀a b c d e.
  get_code_labels (stack_move a b c d e) = get_code_labels e`,
  Induct>>rw[stack_move_def]);

val word_to_stack_comp_code_labels = Q.prove(`
  ∀prog bs kf n.
  word_good_handlers n prog ⇒
  get_code_labels (FST (comp prog bs kf)) ⊆
  (raise_stub_location,0n) INSERT ((IMAGE (λn.(n,0)) (word_get_code_labels prog)) ∪ stack_get_handler_labels n (FST (comp prog bs kf)))`,
  ho_match_mp_tac word_to_stackTheory.comp_ind>>
  rw[word_to_stackTheory.comp_def]>>
  TRY(PairCases_on`kf`)>>
  fs[word_get_code_labels_def]>>
  rpt (fs[]>>pairarg_tac>>fs[])>>
  fs[get_code_handler_labels_wStackLoad]>>
  rw[SeqStackFree_def]
  >-
    (* move *)
    (simp[wMove_def]>>
    rename1`wMoveAux ls _`>>
    Induct_on`ls`>>fs[wMoveAux_def]>>
    Cases_on`ls`>>simp[wMoveAux_def,wMoveSingle_def,FORALL_PROD]>>
    rw[]>>every_case_tac>>simp[])
  >-
    (map_every (fn q=> TRY(Cases_on q)) [`i`,`a`,`b`,`r`,`f`,`m`]>>
    fs[wInst_def]>>
    rpt (pairarg_tac>>fs[])>>
    fs[get_code_handler_labels_wStackLoad]>>
    rpt(dep_rewrite.DEP_REWRITE_TAC [get_code_labels_wReg]>>rw[]))
  >>
    rpt(first_x_assum drule)>>rw[]>>
    TRY(fs[SUBSET_DEF]>>metis_tac[])
  >-
    (TOP_CASE_TAC>>fs[]>>pairarg_tac>>fs[get_code_handler_labels_wStackLoad])
  >-
    rpt(dep_rewrite.DEP_REWRITE_TAC [get_code_labels_wReg]>>rw[])
  >> TRY (
    TOP_CASE_TAC>>fs[]>>
    every_case_tac>>fs[call_dest_def]>>
    every_case_tac>>fs[]>>rw[]>>
    rpt(pairarg_tac>>fs[])>>rw[]>>
    fs[get_code_handler_labels_wStackLoad]>>
    fs[StackArgs_def,stack_move_code_labels,PushHandler_def,StackHandlerArgs_def,PopHandler_def]>>
    TRY(drule wLive_code_labels>>fs[])>>
    fs[SUBSET_DEF]>>metis_tac[])
  >-
    (drule wLive_code_labels>>fs[])
  >>
    rw[wRegWrite1_def]);

val compile_word_to_stack_code_labels = Q.prove(`
  ∀ac p bs p' bs'.
  EVERY (λ(n,m,pp). word_good_handlers n pp) p ∧
  compile_word_to_stack ac p bs = (p',bs') ⇒
  (* every label in the compiled code *)
  BIGUNION (IMAGE get_code_labels (set (MAP SND p'))) ⊆
  (raise_stub_location,0n) INSERT
  (* either came from wordLang *)
  IMAGE (\n.(n,0n)) (BIGUNION (set (MAP (λ(n,m,pp). (word_get_code_labels pp)) p))) UNION
  (* or has been introduced into the handler labels *)
  BIGUNION (set (MAP (λ(n,pp). (stack_get_handler_labels n pp)) p'))`,
  ho_match_mp_tac compile_word_to_stack_ind>>
  fs[compile_word_to_stack_def]>>rw[]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>fs[]
  >- (
    qpat_x_assum `compile_prog _ _ _ _ = _` mp_tac>>
    PURE_REWRITE_TAC [compile_prog_def,LET_THM]>>
    rpt(pairarg_tac>>fs[])>>
    rw[]>>simp[]>>
    drule word_to_stack_comp_code_labels>>
    qmatch_asmsub_abbrev_tac`comp p bs kf`>>
    disch_then(qspecl_then [`bs`,`kf`] assume_tac)>>rfs[]>>
    fs[SUBSET_DEF]>>
    metis_tac[])
  >>
  fs[SUBSET_DEF]>>
  metis_tac[]);

val word_good_code_labels_def = Define`
  word_good_code_labels p ⇔
  EVERY (λ(n,m,pp). word_good_handlers n pp) p ∧
  (BIGUNION (set (MAP (λ(n,m,pp). (word_get_code_labels pp)) p))) ⊆
  (set (MAP FST p))`

val word_to_stack_good_code_labels = Q.store_thm("word_to_stack_good_code_labels",`
  compile asm_conf progs = (bs,prog') ∧
  word_good_code_labels progs ⇒
  stack_good_code_labels prog'`,
  fs[word_to_stackTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  fs[word_good_code_labels_def,stack_good_code_labels_def]>>
  rw[]>>
  drule compile_word_to_stack_code_labels>>
  disch_then drule>>fs[]>>
  drule MAP_FST_compile_word_to_stack>>
  rw[]
  >-
    simp[raise_stub_def]
  >>
  match_mp_tac SUBSET_TRANS>> asm_exists_tac>>simp[]>>
  rw[]
  >-
    (match_mp_tac IMAGE_SUBSET_gen>>
    asm_exists_tac>>simp[SUBSET_DEF])
  >>
    fs[SUBSET_DEF]);

(* word_to_word never introduces any labels, so the statements are easy *)
local
  open word_removeTheory word_allocTheory word_instTheory word_simpTheory word_to_wordTheory
  open data_to_wordTheory
in

(* remove_must_terminate*)
val word_get_code_labels_remove_must_terminate = Q.prove(`
  ∀ps.
  word_get_code_labels (remove_must_terminate ps) =
  word_get_code_labels ps`,
  ho_match_mp_tac remove_must_terminate_ind>>rw[]>>
  fs[remove_must_terminate_def]>>
  every_case_tac>>fs[]);

val word_good_handlers_remove_must_terminate = Q.prove(`
  ∀ps.
  word_good_handlers n (remove_must_terminate ps) ⇔
  word_good_handlers n ps`,
  ho_match_mp_tac remove_must_terminate_ind>>rw[]>>
  fs[remove_must_terminate_def]>>
  every_case_tac>>fs[]);

(* word_alloc *)

val word_get_code_labels_apply_colour = Q.prove(`
  ∀col ps.
  word_get_code_labels (apply_colour col ps) =
  word_get_code_labels ps`,
  ho_match_mp_tac apply_colour_ind>>rw[]>>
  fs[apply_colour_def]>>
  every_case_tac>>fs[]);

val word_good_handlers_apply_colour = Q.prove(`
  ∀col ps.
  word_good_handlers n (apply_colour col ps) ⇔
  word_good_handlers n ps`,
  ho_match_mp_tac apply_colour_ind>>rw[]>>
  fs[apply_colour_def]>>
  every_case_tac>>fs[]);

val word_get_code_labels_word_alloc = Q.prove(`
  word_get_code_labels (word_alloc fc c alg k prog col_opt) =
  word_get_code_labels prog`,
  fs[word_alloc_def,oracle_colour_ok_def]>>
  EVERY_CASE_TAC>>fs[]>>
  TRY(pairarg_tac)>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[word_get_code_labels_apply_colour])

val word_good_handlers_word_alloc = Q.prove(`
  word_good_handlers n (word_alloc fc c alg k prog col_opt) ⇔
  word_good_handlers n prog`,
  fs[word_alloc_def,oracle_colour_ok_def]>>
  EVERY_CASE_TAC>>fs[]>>
  TRY(pairarg_tac)>>fs[]>>
  EVERY_CASE_TAC>>fs[]>>
  metis_tac[word_good_handlers_apply_colour]);

(* three to two *)
val word_get_code_labels_three_to_two_reg = Q.prove(`
  ∀ps.
  word_get_code_labels (three_to_two_reg ps) =
  word_get_code_labels ps`,
  ho_match_mp_tac three_to_two_reg_ind>>rw[]>>
  fs[three_to_two_reg_def]>>
  every_case_tac>>fs[]);

val word_good_handlers_three_to_two_reg = Q.prove(`
  ∀ps.
  word_good_handlers n (three_to_two_reg ps) ⇔
  word_good_handlers n ps`,
  ho_match_mp_tac three_to_two_reg_ind>>rw[]>>
  fs[three_to_two_reg_def]>>
  every_case_tac>>fs[]);

(* remove_dead *)
val word_get_code_labels_remove_dead = Q.prove(`
  ∀ps live.
  word_get_code_labels (FST (remove_dead ps live)) ⊆
  word_get_code_labels ps`,
  ho_match_mp_tac remove_dead_ind>>rw[]>>
  fs[remove_dead_def]>>
  every_case_tac>>fs[]>>
  rpt(pairarg_tac>>fs[])>>rw[]>>
  fs[SUBSET_DEF]);

val word_good_handlers_remove_dead = Q.prove(`
  ∀ps live.
  word_good_handlers n ps ⇒
  word_good_handlers n (FST (remove_dead ps live))`,
  ho_match_mp_tac remove_dead_ind>>rw[]>>
  fs[remove_dead_def]>>
  every_case_tac>>fs[]>>
  rpt(pairarg_tac>>fs[])>>rw[]);

(* ssa *)

val word_get_code_labels_fake_moves = Q.store_thm("word_get_code_labels_fake_moves",
  `∀a b c d e f g h i.
   fake_moves a b c d = (e,f,g,h,i) ⇒
   word_get_code_labels e = {} ∧
   word_get_code_labels f = {}`,
  Induct \\ rw[fake_moves_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ fs[CaseEq"option"] \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ rw[fake_move_def]);

val word_get_code_labels_ssa_cc_trans = Q.store_thm("word_get_code_labels_ssa_cc_trans",
  `∀x y z a b c.
   ssa_cc_trans x y z = (a,b,c) ⇒
   word_get_code_labels a = word_get_code_labels x`,
  recInduct ssa_cc_trans_ind
  \\ rw[ssa_cc_trans_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  >- (
    Cases_on`i` \\ fs[ssa_cc_trans_inst_def]
    \\ rveq \\ fs[]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
    \\ TRY(rename1`Arith arith` \\ Cases_on`arith`)
    \\ TRY(rename1`Mem memop _ dst` \\ Cases_on`memop` \\ Cases_on`dst`)
    \\ TRY(rename1`FP flop` \\ Cases_on`flop`)
    \\ fs[ssa_cc_trans_inst_def,CaseEq"reg_imm",CaseEq"bool"]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[] )
  >- (
    fs[fix_inconsistencies_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ imp_res_tac word_get_code_labels_fake_moves
    \\ rw[])
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[CaseEq"option"] \\ rveq \\ fs[]
    \\ fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ fs[CaseEq"prod", fix_inconsistencies_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ imp_res_tac word_get_code_labels_fake_moves
    \\ fs[]));

val word_get_code_labels_full_ssa_cc_trans = Q.prove(`
  ∀m p.
  word_get_code_labels (full_ssa_cc_trans m p) =
  word_get_code_labels p`,
  simp[full_ssa_cc_trans_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ fs[setup_ssa_def]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ drule word_get_code_labels_ssa_cc_trans
  \\ rw[]);

val word_good_handlers_fake_moves = Q.store_thm("word_good_handlers_fake_moves",
  `∀a b c d e f g h i.
   fake_moves a b c d = (e,f,g,h,i) ⇒
   word_good_handlers n e ∧
   word_good_handlers n f`,
  Induct \\ rw[fake_moves_def] \\ rw[]
  \\ pairarg_tac \\ fs[]
  \\ fs[CaseEq"option"] \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ rw[fake_move_def]);

val word_good_handlers_ssa_cc_trans = Q.store_thm("word_good_handlers_ssa_cc_trans",
  `∀x y z a b c.
   ssa_cc_trans x y z = (a,b,c) ⇒
   word_good_handlers n a = word_good_handlers n x`,
  recInduct ssa_cc_trans_ind
  \\ rw[ssa_cc_trans_def] \\ fs[]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  >- (
    Cases_on`i` \\ fs[ssa_cc_trans_inst_def]
    \\ rveq \\ fs[]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
    \\ TRY(rename1`Arith arith` \\ Cases_on`arith`)
    \\ TRY(rename1`Mem memop _ dst` \\ Cases_on`memop` \\ Cases_on`dst`)
    \\ TRY(rename1`FP flop` \\ Cases_on`flop`)
    \\ fs[ssa_cc_trans_inst_def,CaseEq"reg_imm",CaseEq"bool"]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[] )
  >- (
    fs[fix_inconsistencies_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ imp_res_tac word_good_handlers_fake_moves
    \\ rw[])
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[] )
  >- (
    fs[CaseEq"option"] \\ rveq \\ fs[]
    \\ fs[list_next_var_rename_move_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ fs[CaseEq"prod", fix_inconsistencies_def]
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ imp_res_tac word_good_handlers_fake_moves
    \\ fs[]));

val word_good_handlers_full_ssa_cc_trans = Q.prove(`
  ∀m p.
  word_good_handlers n (full_ssa_cc_trans m p) ⇔
  word_good_handlers n p`,
  simp[full_ssa_cc_trans_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ fs[setup_ssa_def]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ drule word_good_handlers_ssa_cc_trans
  \\ rw[]);

(* inst *)
val word_get_code_labels_inst_select_exp = Q.prove(`
  ∀a b c exp.
  word_get_code_labels (inst_select_exp a b c exp) = {}`,
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>
  fs[inst_select_exp_def]>>
  every_case_tac>>fs[inst_select_exp_def]);

val word_get_code_labels_inst_select = Q.prove(`
  ∀ac v ps.
  word_get_code_labels (inst_select ac v ps) =
  word_get_code_labels ps`,
  ho_match_mp_tac inst_select_ind>>rw[]>>
  fs[inst_select_def]>>
  every_case_tac>>fs[word_get_code_labels_inst_select_exp]);

val word_good_handlers_inst_select_exp = Q.prove(`
  ∀a b c exp.
  word_good_handlers n (inst_select_exp a b c exp)`,
  ho_match_mp_tac inst_select_exp_ind>>rw[]>>
  fs[inst_select_exp_def]>>
  every_case_tac>>fs[inst_select_exp_def]);

val word_good_handlers_inst_select = Q.prove(`
  ∀ac v ps.
  word_good_handlers n (inst_select ac v ps) ⇔
  word_good_handlers n ps`,
  ho_match_mp_tac inst_select_ind>>rw[]>>
  fs[inst_select_def]>>
  every_case_tac>>fs[word_good_handlers_inst_select_exp]);

(* simp *)
val word_get_code_labels_const_fp_loop = Q.prove(`
  ∀p l.
  word_get_code_labels (FST (const_fp_loop p l)) ⊆ word_get_code_labels p`,
  ho_match_mp_tac const_fp_loop_ind \\ rw []
  \\ fs [const_fp_loop_def]
  \\ every_case_tac\\ fs[]
  \\ rpt (pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF] \\ metis_tac[]);

val word_good_handlers_const_fp_loop = Q.prove(`
  ∀p l.
  word_good_handlers n p ⇒
  word_good_handlers n (FST (const_fp_loop p l))`,
  ho_match_mp_tac const_fp_loop_ind \\ rw []
  \\ fs [const_fp_loop_def]
  \\ every_case_tac\\ fs[]
  \\ rpt (pairarg_tac \\ fs[]));

val word_get_code_labels_apply_if_opt = Q.store_thm("word_get_code_labels_apply_if_opt",
  `∀x y z. apply_if_opt x y = SOME z ⇒ word_get_code_labels z = word_get_code_labels x ∪ word_get_code_labels y`,
  rw[apply_if_opt_def]
  \\ fs[CaseEq"option",CaseEq"prod"]
  \\ pairarg_tac \\ fs[]
  \\ fs[CaseEq"option",CaseEq"prod"]
  \\ rveq
  \\ fs[CaseEq"bool"] \\ rveq
  \\ rw[SmartSeq_def]
  \\ rename1`dest_If iff`
  \\ Cases_on`iff` \\ fs[dest_If_def]
  \\ rveq \\ fs[]
  \\ fs[dest_If_Eq_Imm_def,CaseEq"option",CaseEq"prod",CaseEq"cmp",CaseEq"reg_imm"]
  \\ Cases_on`y` \\ fs[dest_If_def] \\ rveq
  \\ Cases_on`x` \\ fs[dest_Seq_def] \\ rveq \\ fs[]
  \\ rw[EXTENSION, EQ_IMP_THM] \\ rw[]);

val word_get_code_labels_simp_if = Q.store_thm("word_get_code_labels_simp_if[simp]",
   `∀p.  word_get_code_labels (simp_if p) = word_get_code_labels p`,
  recInduct simp_if_ind
  \\ rw[simp_if_def]
  \\ CASE_TAC \\ simp[]
  >- ( drule word_get_code_labels_apply_if_opt \\ rw[] )
  \\ every_case_tac \\ fs[]);

val word_good_handlers_apply_if_opt = Q.store_thm("word_good_handlers_apply_if_opt",
  `∀x y z. apply_if_opt x y = SOME z ∧
           word_good_handlers n x ∧ word_good_handlers n y
           ⇒
           word_good_handlers n z `,
  rw[apply_if_opt_def]
  \\ fs[CaseEq"option",CaseEq"prod"]
  \\ pairarg_tac \\ fs[]
  \\ fs[CaseEq"option",CaseEq"prod"]
  \\ rveq
  \\ fs[CaseEq"bool"] \\ rveq
  \\ rw[SmartSeq_def]
  \\ rename1`dest_If iff`
  \\ Cases_on`iff` \\ fs[dest_If_def]
  \\ rveq \\ fs[]
  \\ fs[dest_If_Eq_Imm_def,CaseEq"option",CaseEq"prod",CaseEq"cmp",CaseEq"reg_imm"]
  \\ Cases_on`y` \\ fs[dest_If_def] \\ rveq
  \\ Cases_on`x` \\ fs[dest_Seq_def] \\ rveq \\ fs[]);

val word_good_handlers_simp_if = Q.prove(`
  ∀p.
  word_good_handlers n p ⇒
  word_good_handlers n (simp_if p)`,
  recInduct simp_if_ind
  \\ rw[simp_if_def]
  \\ CASE_TAC \\ simp[]
  >- ( drule word_good_handlers_apply_if_opt \\ rw[] )
  \\ every_case_tac \\ fs[]);

val word_get_code_labels_Seq_assoc = Q.prove(`
  ∀p1 p2.
  word_get_code_labels (Seq_assoc p1 p2) = word_get_code_labels p1 ∪ word_get_code_labels p2`,
  ho_match_mp_tac Seq_assoc_ind>>rw[]>>
  fs[Seq_assoc_def,SmartSeq_def]>>rw[]>>
  fs[UNION_ASSOC]>>
  every_case_tac>>fs[]);

val word_good_handlers_Seq_assoc = Q.prove(`
  ∀p1 p2.
  word_good_handlers n (Seq_assoc p1 p2) ⇔
  word_good_handlers n p1 ∧ word_good_handlers n p2`,
  ho_match_mp_tac Seq_assoc_ind>>rw[]>>
  fs[Seq_assoc_def,SmartSeq_def]>>rw[]>>
  every_case_tac>>fs[]>>metis_tac[]);

val word_get_code_labels_word_simp = Q.prove(`
  ∀ps.
  word_get_code_labels (word_simp$compile_exp ps) ⊆
  word_get_code_labels ps`,
  PURE_REWRITE_TAC [compile_exp_def]>>
  LET_ELIM_TAC>>
  match_mp_tac SUBSET_TRANS >>
  qexists_tac`word_get_code_labels e'`>>rw[]
  >- (
    unabbrev_all_tac>>EVAL_TAC>>
    metis_tac[word_get_code_labels_const_fp_loop])>>
  match_mp_tac SUBSET_TRANS >>
  qexists_tac`word_get_code_labels e`>>rw[]
  >- (
    unabbrev_all_tac>>EVAL_TAC>>
    metis_tac[word_get_code_labels_simp_if, SUBSET_REFL])>>
  unabbrev_all_tac>>
  fs[word_get_code_labels_Seq_assoc]);

val word_good_handlers_word_simp = Q.prove(`
  ∀ps.
  word_good_handlers n ps ⇒
  word_good_handlers n (word_simp$compile_exp ps)`,
  rw[compile_exp_def]>>
  EVAL_TAC>>match_mp_tac word_good_handlers_const_fp_loop>>
  match_mp_tac word_good_handlers_simp_if>>
  fs[word_good_handlers_Seq_assoc]);

val word_get_code_labels_word_to_word = Q.prove(`
  word_good_code_labels progs ⇒
  word_good_code_labels (SND (compile wc ac progs))`,
  fs[word_to_wordTheory.compile_def]>>
  rpt(pairarg_tac>>fs[])>>
  fs[word_good_code_labels_def,next_n_oracle_def]>>
  rw[]
  >- (
    rfs[EVERY_MAP,LENGTH_GENLIST,EVERY_MEM,MEM_ZIP,PULL_EXISTS]>>
    rw[full_compile_single_def]>>
    Cases_on`EL n progs`>>Cases_on`r`>>fs[compile_single_def]>>
    fs[word_good_handlers_remove_must_terminate,word_good_handlers_word_alloc]>>
    simp[COND_RAND]>>
    fs[word_good_handlers_three_to_two_reg]>>
    match_mp_tac word_good_handlers_remove_dead>>
    simp[word_good_handlers_full_ssa_cc_trans,word_good_handlers_inst_select]>>
    match_mp_tac word_good_handlers_word_simp>>
    fs[FORALL_PROD]>>
    metis_tac[EL_MEM])
  >>
    fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP,MEM_ZIP]>>
    rw[full_compile_single_def]>>
    Cases_on`EL n progs`>>Cases_on`r`>>fs[compile_single_def]>>
    fs[word_get_code_labels_remove_must_terminate,word_get_code_labels_word_alloc]>>
    fs[COND_RAND]>>
    fs[word_get_code_labels_three_to_two_reg]>>
    drule (word_get_code_labels_remove_dead|>SIMP_RULE std_ss [SUBSET_DEF])>>
    simp[word_get_code_labels_full_ssa_cc_trans,word_get_code_labels_inst_select]>>
    strip_tac>>
    drule (word_get_code_labels_word_simp|>SIMP_RULE std_ss [SUBSET_DEF])>>
    rw[]>>fs[FORALL_PROD,EXISTS_PROD,PULL_EXISTS,EVERY_MEM]>>
    first_x_assum drule>>
    disch_then(qspecl_then [`q`,`q'`] mp_tac)>>
    impl_tac >-
        metis_tac[EL_MEM]>>
    rw[]>>
    fs[MEM_EL]>>
    qexists_tac`n'`>>simp[]>>
    Cases_on`EL n' progs`>>Cases_on`r`>>fs[compile_single_def]);

val assign_get_code_label_def = Define`
  (assign_get_code_label (closLang$Label x) = {x}) ∧
  (assign_get_code_label x = {})`

val data_get_code_labels_def = Define`
  (data_get_code_labels (Call r d a h) =
    (case d of SOME x => {x} | _ => {}) ∪
    (case h of SOME (n,p) => data_get_code_labels p | _ => {})) ∧
  (data_get_code_labels (Seq p1 p2) = data_get_code_labels p1 ∪ data_get_code_labels p2) ∧
  (data_get_code_labels (If _ p1 p2) = data_get_code_labels p1 ∪ data_get_code_labels p2) ∧
  (data_get_code_labels (Assign _ op _ _) = assign_get_code_label op) ∧
  (data_get_code_labels _ = {})`;
val _ = export_rewrites["data_get_code_labels_def"];

val word_get_code_labels_StoreEach = Q.prove(`
  ∀ls off.
  word_get_code_labels (StoreEach v ls off) = {}`,
  Induct>>fs[StoreEach_def]);

val word_get_code_labels_MemEqList = Q.prove(`
  ∀x b.
  word_get_code_labels (MemEqList b x) = {}`,
  Induct>>fs[MemEqList_def]);

(* slow... *)
val word_get_code_labels_assign = Q.prove(`
  ∀x.
  word_get_code_labels (FST (assign c secn v w x y z)) SUBSET
  assign_get_code_label x ∪ (set(MAP FST (stubs (:α) c)))`,
  ho_match_mp_tac (fetch "-" "assign_get_code_label_ind")>>
  rw[assign_def,all_assign_defs,arg1_def,arg2_def,arg3_def,arg4_def,
     assign_get_code_label_def]>>
  fs[list_Seq_def,word_get_code_labels_StoreEach,word_get_code_labels_MemEqList]>>
  rpt(every_case_tac>>fs[]>>
  fs[list_Seq_def,word_get_code_labels_StoreEach,word_get_code_labels_MemEqList]>>
  EVAL_TAC));

val data_to_word_comp_code_labels = Q.prove(`
  ∀c secn l p.
  word_get_code_labels ((FST (comp c secn l p)):'a wordLang$prog) SUBSET
  data_get_code_labels p ∪ set(MAP FST (stubs (:α) c))`,
  ho_match_mp_tac comp_ind>>
  rw[]>>Cases_on`p`>>fs[]>>
  simp[Once comp_def]>>
  rpt(pairarg_tac>>fs[])
  >- (
    every_case_tac>>fs[]>>
    rpt(pairarg_tac>>fs[])>>
    fs[SUBSET_DEF]>>fs[]>>
    metis_tac[])
  >-
    fs[word_get_code_labels_assign]
  >-
    (fs[SUBSET_DEF]>>metis_tac[])
  >-
    (fs[SUBSET_DEF]>>metis_tac[])
  >>
    EVAL_TAC>>rw[]>>fs[]);

val word_good_handlers_StoreEach = Q.prove(`
  ∀ls off.
  word_good_handlers secn (StoreEach v ls off)`,
  Induct>>fs[StoreEach_def]);

val word_good_handlers_MemEqList = Q.prove(`
  ∀x b.
  word_good_handlers secn (MemEqList b x)`,
  Induct>>fs[MemEqList_def]);

(* slow... *)
val word_good_handlers_assign = Q.prove(`
  ∀x.
  word_good_handlers secn (FST (assign c secn v w x y z))`,
  ho_match_mp_tac (fetch "-" "assign_get_code_label_ind")>>
  rw[assign_def,all_assign_defs,arg1_def,arg2_def,arg3_def,arg4_def]>>
  rpt(
  every_case_tac>>fs[list_Seq_def,word_good_handlers_StoreEach,word_good_handlers_MemEqList]>>
  rw[]>>EVAL_TAC
  ));

val data_to_word_comp_good_handlers = Q.prove(`
  ∀c secn l p.
  word_good_handlers secn ((FST (comp c secn l p)):'a wordLang$prog)`,
  ho_match_mp_tac comp_ind>>
  rw[]>>Cases_on`p`>>fs[]>>
  simp[Once comp_def]>>
  rpt(pairarg_tac>>fs[])
  >- (
    every_case_tac>>fs[]>>
    rpt(pairarg_tac>>fs[])>>
    fs[SUBSET_DEF]>>fs[]>>
    metis_tac[])
  >-
    fs[word_good_handlers_assign]
  >>
    EVAL_TAC>>rw[]>>fs[]);

val data_good_code_labels_def = Define`
  data_good_code_labels p ⇔
  (BIGUNION (set (MAP (λ(n,m,pp). (data_get_code_labels pp)) p))) ⊆
  (set (MAP FST p))`

val stubs_labels = Q.prove(`
  BIGUNION (set (MAP (λ(n,m,pp). word_get_code_labels pp)  (stubs (:'a) data_conf)))
  ⊆ set (MAP FST (stubs (:'a) data_conf))`,
  rpt(EVAL_TAC>>
  IF_CASES_TAC>>
  simp[]));

val data_to_word_good_code_labels = Q.store_thm("data_to_word_good_code_labels",`
  (data_to_word$compile data_conf word_conf asm_conf prog) = (xx,prog') ∧
  data_good_code_labels prog ⇒
  word_good_code_labels prog'`,
  fs[data_to_wordTheory.compile_def]>>rw[]>>
  qmatch_asmsub_abbrev_tac`LHS = _`>>
  `prog' = SND LHS` by (unabbrev_all_tac>>fs[])>>
  pop_assum SUBST_ALL_TAC>>
  fs[Abbr`LHS`]>>
  match_mp_tac word_get_code_labels_word_to_word>>
  fs[word_good_code_labels_def,data_good_code_labels_def]>>rw[]
  >-
    (EVAL_TAC>>rw[])
  >-
    (simp[EVERY_MAP,LAMBDA_PROD,compile_part_def,data_to_word_comp_good_handlers]>>
    fs[EVERY_MEM,FORALL_PROD])
  >-
    (assume_tac stubs_labels>>
    match_mp_tac SUBSET_TRANS>>asm_exists_tac>>fs[])
  >>
    fs[MAP_MAP_o,o_DEF,LAMBDA_PROD,compile_part_def]>>
    fs[SUBSET_DEF,PULL_EXISTS,Once MEM_MAP,FORALL_PROD]>>
    rw[]>>
    drule (data_to_word_comp_code_labels |> SIMP_RULE std_ss [SUBSET_DEF])>>
    rw[]
    >-
      (first_x_assum drule>>
      disch_then drule>>fs[MEM_MAP,EXISTS_PROD])
    >>
      fs[MEM_MAP]>>metis_tac[]);

end

val compile_prog_keeps_names = Q.store_thm("compile_prog_keeps_names",
  `∀next xs next' ys. compile_prog next xs = (next',ys) ∧ MEM x (MAP FST xs) ⇒ MEM x (MAP FST ys)`,
  recInduct bvi_tailrecTheory.compile_prog_ind
  \\ rw[bvi_tailrecTheory.compile_prog_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]);

val bvl_get_code_labels_def = tDefine"bvl_get_code_labels"
  `(bvl_get_code_labels (Var _) = {}) ∧
   (bvl_get_code_labels (If e1 e2 e3) = bvl_get_code_labels e1 ∪ bvl_get_code_labels e2 ∪ bvl_get_code_labels e3) ∧
   (bvl_get_code_labels (Let es e) = BIGUNION (set (MAP bvl_get_code_labels es)) ∪ bvl_get_code_labels e) ∧
   (bvl_get_code_labels (Raise e) = bvl_get_code_labels e) ∧
   (bvl_get_code_labels (Handle e1 e2) = bvl_get_code_labels e1 ∪ bvl_get_code_labels e2) ∧
   (bvl_get_code_labels (Tick e) = bvl_get_code_labels e) ∧
   (bvl_get_code_labels (Call _ d es) = (case d of NONE => {} | SOME n => {n}) ∪ BIGUNION (set (MAP bvl_get_code_labels es))) ∧
   (bvl_get_code_labels (Op op es) = assign_get_code_label op ∪ BIGUNION (set (MAP bvl_get_code_labels es)))`
  (wf_rel_tac`measure exp_size`
   \\ simp[bvlTheory.exp_size_def]
   \\ rpt conj_tac \\ rpt gen_tac
   \\ Induct_on`es`
   \\ rw[bvlTheory.exp_size_def]
   \\ simp[] \\ res_tac \\ simp[]);
val bvl_get_code_labels_def = bvl_get_code_labels_def |> SIMP_RULE (srw_ss()++ETA_ss)[] |> curry save_thm "bvl_get_code_labels_def[simp]"

val bvl_good_code_labels_def = Define`
  bvl_good_code_labels p ⇔
    BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) p)) ⊆ set (MAP FST p)`;

val bvi_get_code_labels_def = tDefine"bvi_get_code_labels"
  `(bvi_get_code_labels (Var _) = {}) ∧
   (bvi_get_code_labels (If e1 e2 e3) = bvi_get_code_labels e1 ∪ bvi_get_code_labels e2 ∪ bvi_get_code_labels e3) ∧
   (bvi_get_code_labels (Let es e) = BIGUNION (set (MAP bvi_get_code_labels es)) ∪ bvi_get_code_labels e) ∧
   (bvi_get_code_labels (Raise e) = bvi_get_code_labels e) ∧
   (bvi_get_code_labels (Tick e) = bvi_get_code_labels e) ∧
   (bvi_get_code_labels (Call _ d es h) =
     (case d of NONE => {} | SOME n => {n}) ∪
     (case h of NONE => {} | SOME e => bvi_get_code_labels e) ∪
     BIGUNION (set (MAP bvi_get_code_labels es))) ∧
   (bvi_get_code_labels (Op op es) = assign_get_code_label op ∪ BIGUNION (set (MAP bvi_get_code_labels es)))`
  (wf_rel_tac`measure exp_size`
   \\ simp[bviTheory.exp_size_def]
   \\ rpt conj_tac \\ rpt gen_tac
   \\ Induct_on`es`
   \\ rw[bviTheory.exp_size_def]
   \\ simp[] \\ res_tac \\ simp[]);
val bvi_get_code_labels_def = bvi_get_code_labels_def |> SIMP_RULE (srw_ss()++ETA_ss)[] |> curry save_thm "bvi_get_code_labels_def[simp]"

val bvi_good_code_labels_def = Define`
  bvi_good_code_labels p ⇔
    BIGUNION (set (MAP (bvi_get_code_labels o SND o SND) p)) ⊆ set (MAP FST p)`;

val data_get_code_labels_space = Q.store_thm("data_get_code_labels_space",
  `∀x y y0 y1 y2.
   (space x = INL y ⇒ data_get_code_labels y = data_get_code_labels x) ∧
   (space x = INR (y0,y1,y2) ⇒ data_get_code_labels y2 = data_get_code_labels x)`,
  recInduct data_spaceTheory.space_ind
  \\ rw[data_spaceTheory.space_def] \\ simp[]
  \\ fs[CaseEq"sum",CaseEq"dataLang$prog"] \\ rveq \\ fs[data_spaceTheory.space_def]
  \\ fs[data_spaceTheory.pMakeSpace_def]
  \\ every_case_tac \\ fs[data_spaceTheory.pMakeSpace_def,CaseEq"option",data_spaceTheory.space_def]
  \\ rveq \\ fs[]
  \\ every_case_tac \\ fs[data_spaceTheory.pMakeSpace_def,CaseEq"option",data_spaceTheory.space_def]
  \\ Cases_on`space c2` \\ Cases_on`space c3` \\ fs[] \\ TRY(PairCases_on`y`)
  \\ fs[data_spaceTheory.pMakeSpace_def,CaseEq"option",data_spaceTheory.space_def]
  \\ PairCases_on`y'`
  \\ fs[data_spaceTheory.pMakeSpace_def,CaseEq"option",data_spaceTheory.space_def]);

val data_get_code_labels_compile = Q.store_thm("data_get_code_labels_compile[simp]",
  `∀x. data_get_code_labels (data_space$compile x) = data_get_code_labels x`,
  rw[data_spaceTheory.compile_def]
  \\ Cases_on`space x`
  \\ simp[data_spaceTheory.pMakeSpace_def]
  \\ TRY (PairCases_on`y`)
  \\ simp[data_spaceTheory.pMakeSpace_def]
  \\ imp_res_tac data_get_code_labels_space);

val data_get_code_labels_simp = Q.store_thm("data_get_code_labels_simp",
  `∀x y. data_get_code_labels (simp x y) ⊆ data_get_code_labels x ∪ data_get_code_labels y`,
  recInduct data_simpTheory.simp_ind
  \\ rw[data_simpTheory.simp_def]
  \\ fs[SUBSET_DEF, data_simpTheory.pSeq_def] \\ rw[]
  \\ metis_tac[]);

val data_get_code_labels_compile_TODO_move = Q.store_thm("data_get_code_labels_compile_TODO_move",
  `∀x y. data_get_code_labels (FST (compile x y)) ⊆ data_get_code_labels x`,
  recInduct data_liveTheory.compile_ind
  \\ rw[data_liveTheory.compile_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF]);

val data_get_code_labels_mk_ticks = Q.store_thm("data_get_code_labels_mk_ticks",
  `∀n m. data_get_code_labels (mk_ticks n m) ⊆ data_get_code_labels m`,
   Induct
   \\ rw[dataLangTheory.mk_ticks_def] \\ rw[FUNPOW]
   \\ fs[dataLangTheory.mk_ticks_def]
   \\ first_x_assum (qspec_then`Seq Tick m`mp_tac)
   \\ rw[]);

val data_get_code_labels_iAssign = Q.store_thm("data_get_code_labels_iAssign[simp]",
  `∀a b c d e. data_get_code_labels (iAssign a b c d e) = assign_get_code_label b`,
  rw[bvi_to_dataTheory.iAssign_def]
  \\ EVAL_TAC);

val data_get_code_labels_compile_TODO_move2 = Q.store_thm("data_get_code_labels_compile_TODO_move2",
  `∀a b c d e. data_get_code_labels (FST (compile a b c d e)) ⊆
    BIGUNION (set (MAP bvi_get_code_labels e)) `,
  recInduct bvi_to_dataTheory.compile_ind
  \\ rw[bvi_to_dataTheory.compile_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF]
  \\ rw[] \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`mk_ticks a b`
  \\ qspecl_then[`a`,`b`]mp_tac data_get_code_labels_mk_ticks
  \\ simp[SUBSET_DEF]
  \\ disch_then drule \\ rw[Abbr`b`,Abbr`a`]
  \\ qmatch_asmsub_abbrev_tac`mk_ticks a b`
  \\ qspecl_then[`a`,`b`]mp_tac data_get_code_labels_mk_ticks
  \\ simp[SUBSET_DEF]
  \\ disch_then drule \\ rw[Abbr`b`,Abbr`a`]);

val compile_prog_good_code_labels = Q.store_thm("compile_prog_good_code_labels",
  `∀p. bvi_good_code_labels p ⇒ data_good_code_labels (bvi_to_data$compile_prog p)`,
  simp[bvi_to_dataTheory.compile_prog_def]
  \\ simp[data_good_code_labels_def, MAP_MAP_o, o_DEF, LAMBDA_PROD]
  \\ simp[bvi_to_dataTheory.compile_part_def]
  \\ simp[FST_triple]
  \\ simp[bvi_good_code_labels_def]
  \\ simp[SUBSET_DEF, PULL_EXISTS, MEM_MAP, FORALL_PROD, EXISTS_PROD]
  \\ rw[]
  \\ first_x_assum irule
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ fs[bvi_to_dataTheory.compile_exp_def]
  \\ fs[bvi_to_dataTheory.optimise_def]
  \\ qmatch_asmsub_abbrev_tac`data_get_code_labels (simp a b)`
  \\ qspecl_then[`a`,`b`]mp_tac data_get_code_labels_simp
  \\ simp_tac std_ss [SUBSET_DEF]
  \\ disch_then drule
  \\ rw[Abbr`a`,Abbr`b`]
  \\ qmatch_asmsub_abbrev_tac`FST (compile a b)`
  \\ qspecl_then[`a`,`b`]mp_tac data_get_code_labels_compile_TODO_move
  \\ simp[SUBSET_DEF]
  \\ disch_then drule
  \\ rw[Abbr`a`, Abbr`b`]
  \\ qmatch_asmsub_abbrev_tac`FST (compile a b c d e)`
  \\ qspecl_then[`a`,`b`,`c`,`d`,`e`]mp_tac data_get_code_labels_compile_TODO_move2
  \\ simp[SUBSET_DEF,Abbr`c`]
  \\ disch_then drule
  \\ simp[Abbr`e`]);

val bvi_get_code_labels_rewrite = Q.store_thm("bvi_get_code_labels_rewrite",
  `∀loc next op arity foo exp bar exp_opt.
    rewrite loc next op arity foo exp = (bar, exp_opt) ⇒
    bvi_get_code_labels exp_opt ⊆ next INSERT bvi_get_code_labels exp`,
  recInduct bvi_tailrecTheory.rewrite_ind
  \\ rw[bvi_tailrecTheory.rewrite_def] \\ simp[]
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ fs[CaseEq"option"] \\ rveq
  \\ fs[bvi_tailrecTheory.check_op_def,CaseEq"option",CaseEq"prod",CaseEq"bool"] \\ rveq \\ fs[]
  \\ rveq \\ fs[bvi_tailrecTheory.apply_op_def] \\ rw[] \\ fs[SUBSET_DEF]
  \\ Cases_on`opr` \\ fs[bvi_tailrecTheory.to_op_def, assign_get_code_label_def]
  \\ fs[bvi_tailrecTheory.opbinargs_def, bvi_tailrecTheory.get_bin_args_def]
  \\ imp_res_tac bvi_tailrecProofTheory.is_rec_term_ok \\ fs[]
  \\ TRY(metis_tac[])
  \\ Cases_on`f` \\ fs[bvi_tailrecTheory.is_rec_def]
  \\ rename1`Call _ opt _ _`
  \\ Cases_on`opt` \\ fs[bvi_tailrecTheory.is_rec_def]
  \\ fs[bvi_tailrecTheory.args_from_def,bvi_tailrecTheory.push_call_def]
  \\ fs[bvi_tailrecTheory.apply_op_def, bvi_tailrecTheory.to_op_def, assign_get_code_label_def]
  \\ fs[bvi_tailrecTheory.try_swap_def, bvi_tailrecTheory.opbinargs_def]
  \\ fs[CaseEq"bool",CaseEq"option"] \\ rveq
  \\ fs[CaseEq"option",bvi_tailrecTheory.get_bin_args_def,CaseEq"bool",bvi_tailrecTheory.apply_op_def] \\ rveq \\ fs[]
  \\ fs[PULL_EXISTS, assign_get_code_label_def]
  \\ TRY(EVAL_TAC \\ rw[] \\ NO_TAC)
  \\ fsrw_tac[DNF_ss][PULL_EXISTS]
  \\ metis_tac[]);

val bvi_get_code_labels_let_wrap = Q.store_thm("bvi_get_code_labels_let_wrap[simp]",
  `∀a b c. bvi_get_code_labels (let_wrap a b c) = bvi_get_code_labels b ∪ bvi_get_code_labels c`,
  rw[bvi_tailrecTheory.let_wrap_def, MAP_GENLIST, o_DEF]
  \\ rw[EXTENSION, MEM_GENLIST]
  \\ rw[EQ_IMP_THM] \\ rw[] \\ fs[]);

val bvi_get_code_labels_compile_exp = Q.store_thm("bvi_get_code_labels_compile_exp",
  `∀loc next arity exp exp_aux exp_opt.
   compile_exp loc next arity exp = SOME (exp_aux, exp_opt) ⇒
   bvi_get_code_labels exp_aux ∪ bvi_get_code_labels exp_opt ⊆ next INSERT bvi_get_code_labels exp`,
  simp[bvi_tailrecTheory.compile_exp_def,CaseEq"option"]
  \\ rpt gen_tac \\ strip_tac
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ drule bvi_get_code_labels_rewrite
  \\ simp[] \\ strip_tac
  \\ Cases_on`op` \\ simp[bvi_tailrecTheory.id_from_op_def, assign_get_code_label_def]
  \\ EVAL_TAC);

val TODO_MOVE_1_compile_prog_good_code_labels = Q.store_thm("TODO_MOVE_1_compile_prog_good_code_labels",
  `∀n c n2 c2.
   bvi_tailrec$compile_prog n c = (n2,c2) ∧
   BIGUNION (set (MAP (bvi_get_code_labels o SND o SND) c)) ⊆ all ∧ set (MAP FST p) ⊆ all ∧
   { n + k * bvl_to_bvi_namespaces | k | n + k * bvl_to_bvi_namespaces < n2 } ⊆ all ⇒
   BIGUNION (set (MAP (bvi_get_code_labels o SND o SND) c2)) ⊆ all`,
  recInduct bvi_tailrecTheory.compile_prog_ind
  \\ simp[bvi_tailrecTheory.compile_prog_def]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ rpt(pairarg_tac \\ fs[])
  \\ drule (GEN_ALL compile_prog_keeps_names) \\ strip_tac
  \\ qpat_x_assum`_ next xs = _`assume_tac
  \\ drule (GEN_ALL compile_prog_keeps_names) \\ strip_tac
  \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
  \\ drule bvi_get_code_labels_compile_exp
  \\ fs[SUBSET_DEF,PULL_EXISTS]
  \\ rw[]
  \\ first_x_assum drule \\ rw[]
  \\ TRY (metis_tac[])
  \\ TRY (
    first_x_assum(qspecl_then[`0`](fn th => mp_tac th \\ simp[] \\ disch_then irule))
    \\ qpat_x_assum`_ (next + _) xs = _`assume_tac
    \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
    \\ rw[] \\ simp[]
    \\ EVAL_TAC \\ simp[])
  \\ last_x_assum irule
  \\ reverse conj_tac >- metis_tac[]
  \\ gen_tac
  \\ rpt(first_x_assum(qspec_then`SUC k`mp_tac))
  \\ simp[ADD1,LEFT_ADD_DISTRIB]);

(*
val backend_cs =
  let val cs = wordsLib.words_compset() in
    cs before backendComputeLib.add_backend_compset cs end
*)

(* TODO re-define syntax_ok on terms of things in closPropsTheory
 * (invent new properties), and prove elsewhere
 * that the pat_to_clos compiler satisfies these things.*)
val syntax_ok_pat_to_clos = Q.store_thm("syntax_ok_pat_to_clos",
  `!e. clos_mtiProof$syntax_ok [pat_to_clos$compile e]`,
  ho_match_mp_tac pat_to_closTheory.compile_ind
  \\ rw [pat_to_closTheory.compile_def,
         clos_mtiProofTheory.syntax_ok_def,
         pat_to_closTheory.CopyByteStr_def,
         pat_to_closTheory.CopyByteAw8_def]
  \\ rw [Once clos_mtiProofTheory.syntax_ok_cons]
  \\ fs [clos_mtiProofTheory.syntax_ok_MAP, clos_mtiProofTheory.syntax_ok_def,
         clos_mtiProofTheory.syntax_ok_REPLICATE, EVERY_MAP, EVERY_MEM]
  \\ PURE_CASE_TAC \\ fs []
  \\ rw [clos_mtiProofTheory.syntax_ok_def,
         Once clos_mtiProofTheory.syntax_ok_cons,
         clos_mtiProofTheory.syntax_ok_REVERSE,
         clos_mtiProofTheory.syntax_ok_MAP]);

val syntax_ok_MAP_pat_to_clos = store_thm("syntax_ok_MAP_pat_to_clos",
  ``!xs. clos_mtiProof$syntax_ok (MAP pat_to_clos_compile xs)``,
  Induct \\ fs [clos_mtiProofTheory.syntax_ok_def]
  \\ once_rewrite_tac [clos_mtiProofTheory.syntax_ok_cons]
  \\ fs [syntax_ok_pat_to_clos]);

(* TODO: move to flat_to_patProof, and rename the other one to compile_exp... *)
val compile_esgc_free = Q.store_thm("compile_esgc_free",
  `∀p. EVERY (esgc_free o dest_Dlet) (FILTER is_Dlet p) ⇒
    EVERY esgc_free (flat_to_pat$compile p)`,
  recInduct flat_to_patTheory.compile_ind
  \\ rw[flat_to_patTheory.compile_def]
  \\ irule (CONJUNCT1 flat_to_patProofTheory.compile_esgc_free)
  \\ rw[]);

val set_globals_make_varls = Q.store_thm("set_globals_make_varls",
  `∀a b c d. flatProps$set_globals (make_varls a b c d) =
             bag_of_list (MAP ((+)c) (COUNT_LIST (LENGTH d)))`,
  recInduct source_to_flatTheory.make_varls_ind
  \\ rw[source_to_flatTheory.make_varls_def]
  >- EVAL_TAC
  >- ( EVAL_TAC \\ rw[] \\ rw[EL_BAG] )
  \\ simp[COUNT_LIST_def, MAP_MAP_o, ADD1, o_DEF, bag_of_list_thm]
  \\ EVAL_TAC
  \\ AP_THM_TAC
  \\ simp[FUN_EQ_THM]
  \\ simp[BAG_INSERT_UNION]);

val num_bindings_def = tDefine"num_bindings"
  `(num_bindings (Dlet _ p _) = LENGTH (pat_bindings p [])) ∧
   (num_bindings (Dletrec _ f) = LENGTH f) ∧
   (num_bindings (Dmod _ ds) = SUM (MAP num_bindings ds)) ∧
   (num_bindings _ = 0)`
(wf_rel_tac`measure dec_size`
 \\ gen_tac \\ Induct
 \\ simp [astTheory.dec_size_def]
 \\ rw[] \\ simp[]
 \\ res_tac \\ simp[]);
val _ = export_rewrites["num_bindings_def"];

val compile_decs_num_bindings = Q.store_thm("compile_decs_num_bindings",
  `∀n next env ds e f g p. compile_decs n next env ds = (e,f,g,p) ⇒
   next.vidx ≤ f.vidx ∧
   SUM (MAP num_bindings ds) = f.vidx - next.vidx`,
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ rw[]
  \\ pairarg_tac \\ fsrw_tac[ETA_ss][]
  \\ pairarg_tac \\ fs[] \\ rw[]);

val FILTER_MAPi_ID = Q.store_thm("FILTER_MAPi_ID",
  `∀ls f. FILTER P (MAPi f ls) = MAPi f ls ⇔
   (∀n. n < LENGTH ls ⇒ P (f n (EL n ls)))`,
  Induct \\ reverse(rw[])
  >- (
    qmatch_goalsub_abbrev_tac`a ⇔ b`
    \\ `¬a`
    by (
      simp[Abbr`a`]
      \\ disch_then(mp_tac o Q.AP_TERM`LENGTH`)
      \\ rw[]
      \\ specl_args_of_then``FILTER``LENGTH_FILTER_LEQ mp_tac
      \\ simp[] )
    \\ simp[Abbr`b`]
    \\ qexists_tac`0`
    \\ simp[] )
  \\ simp[Once FORALL_NUM, SimpRHS]);

val compile_decs_elist_globals = Q.store_thm("compile_decs_elist_globals",
  `∀n next env ds e f g p.
   compile_decs n next env ds = (e,f,g,p) ∧
   nsAll (λ_ v. esgc_free v ∧ set_globals v = {||}) env.v ⇒
   elist_globals (MAP dest_Dlet (FILTER is_Dlet p)) =
     bag_of_list (MAP ((+) next.vidx) (COUNT_LIST (SUM (MAP num_bindings ds))))`,
  recInduct source_to_flatTheory.compile_decs_ind
  \\ rw[source_to_flatTheory.compile_decs_def]
  \\ rw[set_globals_make_varls]
  \\ rw[source_to_flatProofTheory.compile_exp_esgc_free]
  >- ( EVAL_TAC \\ rw[EL_BAG] )
  >- EVAL_TAC
  >- (
    qmatch_goalsub_abbrev_tac`FILTER P (MAPi f ls)`
    \\ qmatch_asmsub_abbrev_tac`compile_funs _ _ ll`
    \\ Q.ISPECL_THEN[`P`,`ls`,`f`]mp_tac(Q.GEN`P` FILTER_MAPi_ID)
    \\ simp[Abbr`P`, Abbr`f`, UNCURRY]
    \\ disch_then kall_tac
    \\ simp[o_DEF, UNCURRY]
    \\ qmatch_goalsub_abbrev_tac`COUNT_LIST l`
    \\ `l = LENGTH ls` by simp[Abbr`ls`, Abbr`l`,source_to_flatTheory.compile_funs_map,Abbr`ll`]
    \\ qmatch_goalsub_abbrev_tac`MAPi f ls`
    \\ `∀n. n < LENGTH ls ⇒ set_globals (EL n (MAPi f ls)) = {|next.vidx + n|}`
    by (
      simp[Abbr`f`, EL_MAPi]
      \\ EVAL_TAC
      \\ qx_gen_tac`m`
      \\ strip_tac
      \\ `set_globals (SND(SND(EL m ls))) = {||}` suffices_by simp[]
      \\ fs[Abbr`ls`, source_to_flatTheory.compile_funs_map]
      \\ simp[EL_MAP]
      \\ simp[UNCURRY]
      \\ qmatch_goalsub_abbrev_tac`compile_exp tra venv exp`
      \\ qspecl_then[`tra`,`venv`,`exp`]mp_tac (CONJUNCT1 source_to_flatProofTheory.compile_exp_esgc_free)
      \\ impl_tac
      >- (
        rw[Abbr`venv`]
        \\ irule namespacePropsTheory.nsAll_nsBind
        \\ rw[source_to_flatTheory.extend_env_def]
        \\ irule namespacePropsTheory.nsAll_nsAppend
        \\ rw[]
        \\ irule namespacePropsTheory.nsAll_alist_to_ns
        \\ simp[UNCURRY]
        \\ qmatch_goalsub_abbrev_tac`alloc_defs n v l`
        \\ Q.ISPECL_THEN[`l`,`n`,`v`] mp_tac source_to_flatProofTheory.alloc_defs_set_globals
        \\ simp[flatPropsTheory.elist_globals_eq_empty]
        \\ simp[EVERY_MEM, UNCURRY]
        \\ simp[MEM_MAP, PULL_EXISTS]
        \\ Q.ISPECL_THEN[`l`,`n`,`v`] mp_tac source_to_flatProofTheory.alloc_defs_esgc_free
        \\ simp[EVERY_MEM, UNCURRY]
        \\ simp[MEM_MAP, PULL_EXISTS] )
      \\ rw[] )
    \\ qhdtm_x_assum`Abbrev`kall_tac
    \\ qhdtm_x_assum`Abbrev`kall_tac
    \\ rw[]
    \\ pop_assum mp_tac
    \\ `LENGTH (MAPi f ls) = LENGTH ls` by simp[]
    \\ pop_assum mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ qspec_tac(`next.vidx`,`b`)
    \\ qspec_tac(`MAPi f ls`,`l1`)
    \\ Induct_on`ls` \\ simp[]
    >- (EVAL_TAC \\ rw[])
    \\ simp[o_DEF] \\ rw[ADD1]
    \\ Cases_on`l1` \\ fs[]
    \\ last_x_assum(qspecl_then[`t`,`b+1`]mp_tac)
    \\ impl_tac >- ( fs[ADD1] )
    \\ impl_tac >- (
      rw[]
      \\ first_x_assum(qspec_then`SUC n`mp_tac)
      \\ rw[] )
    \\ rw[]
    \\ once_rewrite_tac[ADD_SYM]
    \\ rw[COUNT_LIST_ADD]
    \\ simp[MAP_MAP_o, o_DEF]
    \\ rw[bag_of_list_append]
    \\ simp[EVAL``COUNT_LIST 1``]
    \\ rw[bag_of_list_thm]
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ rw[]
    \\ AP_TERM_TAC
    \\ simp[MAP_EQ_f])
  >- (
    simp[MAPi_enumerate_MAP, FILTER_MAP, o_DEF, UNCURRY]
    \\ EVAL_TAC )
  >- EVAL_TAC
  >- EVAL_TAC
  >- (
    pairarg_tac \\ fs[] \\ rveq
    \\ srw_tac[ETA_ss][] )
  >- EVAL_TAC
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq
  \\ simp[flatPropsTheory.elist_globals_append, FILTER_APPEND]
  \\ drule source_to_flatProofTheory.compile_decs_esgc_free
  \\ disch_then drule
  \\ strip_tac
  \\ qpat_x_assum`_ ⇒ _`mp_tac
  \\ impl_tac
  >- (
    simp[source_to_flatTheory.extend_env_def]
    \\ irule namespacePropsTheory.nsAll_nsAppend
    \\ simp[] )
  \\ rw[]
  \\ drule compile_decs_num_bindings
  \\ rw[]
  \\ pop_assum (assume_tac o SYM) \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`a + (b + c)`
  \\ `a + (b + c) = b + (a + c)` by simp[]
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[Once COUNT_LIST_ADD,SimpRHS]
  \\ simp[bag_of_list_append]
  \\ simp[MAP_MAP_o, o_DEF]
  \\ qpat_x_assum`compile_decs _ _ _ [d] = _`assume_tac
  \\ drule compile_decs_num_bindings
  \\ rw[]
  \\ AP_TERM_TAC
  \\ simp[MAP_EQ_f]);

(* TODO move *)
val bvi_tailrec_compile_prog_labels = Q.store_thm("bvi_tailrec_compile_prog_labels",
  `!next1 code1 next2 code2.
     bvi_tailrec_compile_prog next1 code1 = (next2, code2)
     ==>
     set (MAP FST code1) UNION { next1 + k * bvl_to_bvi_namespaces | k
                               | next1 + k * bvl_to_bvi_namespaces < next2 } =
     set (MAP FST code2) /\
     next1 <= next2`,
   recInduct bvi_tailrecTheory.compile_prog_ind
   \\ rw [bvi_tailrecTheory.compile_prog_def] \\ fs []
   \\ pop_assum mp_tac
   \\ fs [CaseEq"prod", CaseEq"option"]
   \\ rpt (pairarg_tac \\ fs []) \\ rw [] \\ fs []
   \\ fs [INSERT_UNION_EQ]
   \\ last_x_assum (SUBST1_TAC o GSYM)
   \\ rw [EXTENSION]
   \\ eq_tac \\ rw []
   \\ simp [METIS_PROVE [] ``a \/ b <=> ~a ==> b``]
   \\ rw []
   >- (Cases_on `k` \\ fs [ADD1, LEFT_ADD_DISTRIB])
   >-
    (qexists_tac `0` \\ fs []
     \\ `0n < bvl_to_bvi_namespaces` by fs [bvl_to_bvi_namespaces_def]
     \\ match_mp_tac (GEN_ALL (DECIDE ``0n < z /\ x + z <= y ==> x < y``))
     \\ asm_exists_tac \\ fs [])
   \\ qexists_tac `k + 1` \\ fs [LEFT_ADD_DISTRIB]);

val bvi_tailrec_compile_prog_get_code_labels = Q.store_thm("bvi_tailrec_compile_prog_get_code_labels",
  `!next1 code1 next2 code2.
     bvi_tailrec_compile_prog next1 code1 = (next2, code2)
     ==>
     BIGUNION (set (MAP (bvi_get_code_labels o SND o SND) code2)) ⊆
     BIGUNION (set (MAP (bvi_get_code_labels ∘ SND ∘ SND) code1)) UNION
       { next1 + k * bvl_to_bvi_namespaces | k
       | next1 + k * bvl_to_bvi_namespaces < next2 }`,
  recInduct bvi_tailrecTheory.compile_prog_ind
  \\ rw[bvi_tailrecTheory.compile_prog_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[PULL_EXISTS]
  >- ( simp[GSYM UNION_ASSOC] \\ fs[SUBSET_DEF] )
  \\ drule bvi_get_code_labels_compile_exp
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ rw[] \\ fs[]
  \\ first_x_assum drule \\ rw[] \\ rw[]
  \\ TRY (metis_tac[])
  \\ TRY (
    rpt disj2_tac
    \\ qexists_tac`0` \\ rw[]
    \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
    \\ rw[] \\ EVAL_TAC \\ rw[]
    \\ NO_TAC )
  \\ rpt disj2_tac
  \\ qexists_tac`SUC k`
  \\ rw[ADD1, LEFT_ADD_DISTRIB]);

(* not true
val not_has_rec_code_labels = Q.store_thm("not_has_rec_code_labels",
  `∀loc xs. ¬has_rec loc xs ⇒ EVERY (((=) {}) o bvi_get_code_labels) xs`,
  recInduct bvi_tailrecTheory.has_rec_ind
  \\ rw[bvi_tailrecTheory.has_rec_def] \\ fs[]
  \\ rpt(qpat_x_assum`{} = _`(assume_tac o SYM) \\ fs[])
*)

val destLet_code_labels = Q.store_thm("destLet_code_labels",
  `destLet x = (y,z) ⇒
    BIGUNION (set (MAP bvl_get_code_labels y)) ∪ bvl_get_code_labels z ⊆ bvl_get_code_labels x`,
 Cases_on`x`
 \\ rw[bvl_to_bviTheory.destLet_def]
 \\ fs[bvl_to_bviTheory.destLet_def]);

val compile_int_code_labels = Q.store_thm("compile_int_code_labels[simp]",
  `∀i. bvi_get_code_labels (compile_int i) = {}`,
  recInduct bvl_to_bviTheory.compile_int_ind
  \\ rw[]
  \\ rw[Once bvl_to_bviTheory.compile_int_def]
  \\ rw[assign_get_code_label_def]);

val compile_op_code_labels = Q.store_thm("compile_op_code_labels",
  `bvi_get_code_labels (compile_op op c) ⊆
    BIGUNION (set (MAP bvi_get_code_labels c)) ∪
    IMAGE (λn. bvl_num_stubs + n * bvl_to_bvi_namespaces) (assign_get_code_label op) ∪
    set (MAP FST (bvl_to_bvi$stubs x y))`,
  simp[bvl_to_bviTheory.compile_op_def, bvl_to_bviTheory.stubs_def, SUBSET_DEF]
  \\ every_case_tac \\ fs[assign_get_code_label_def, REPLICATE_GENLIST, PULL_EXISTS, MAPi_GENLIST, MEM_GENLIST]
  \\ rw[] \\ fsrw_tac[DNF_ss][PULL_EXISTS] \\ metis_tac[]);

val dest_var_code_labels = Q.store_thm("dest_var_code_labels[simp]",
  `∀x. bvi_get_code_labels (delete_var x) = bvi_get_code_labels x`,
  recInduct bvi_letTheory.delete_var_ind
  \\ rw[bvi_letTheory.delete_var_def]
  \\ EVAL_TAC);

val compile_code_labels = Q.store_thm("compile_code_labels",
  `∀x y z. BIGUNION (set (MAP bvi_get_code_labels (bvi_let$compile x y z))) =
           BIGUNION (set (MAP bvi_get_code_labels z)) `,
  recInduct bvi_letTheory.compile_ind
  \\ rw[bvi_letTheory.compile_def]
  \\ TRY PURE_CASE_TAC \\ fs[]
  \\ TRY PURE_CASE_TAC \\ fs[]
  \\ fs[Once(GSYM bvi_letTheory.compile_HD_SING)]
  \\ fsrw_tac[ETA_ss][MAP_MAP_o, o_DEF]
  \\ drule APPEND_FRONT_LAST
  \\ disch_then(fn th => CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[GSYM th])))
  \\ simp[]);

val compile_exp_code_labels = Q.store_thm("compile_exp_code_labels[simp]",
  `∀x. bvi_get_code_labels (bvi_let$compile_exp x) = bvi_get_code_labels x`,
  rw[bvi_letTheory.compile_exp_def]
  \\ simp[Once(GSYM bvi_letTheory.compile_HD_SING)]
  \\ specl_args_of_then``bvi_let$compile``compile_code_labels mp_tac
  \\ simp[]
  \\ simp[Once(GSYM bvi_letTheory.compile_HD_SING)]);

val compile_exps_get_code_labels = Q.store_thm("compile_exps_get_code_labels",
  `∀n xs ys aux m.
    bvl_to_bvi$compile_exps n xs = (ys,aux,m) ⇒
     BIGUNION (set (MAP bvi_get_code_labels ys)) ∪
     BIGUNION (set (MAP (bvi_get_code_labels o SND o SND) (append aux)))
     ⊆
     IMAGE (λk. bvl_num_stubs + (k * bvl_to_bvi_namespaces)) (BIGUNION (set (MAP bvl_get_code_labels xs))) ∪
     { bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n ≤ k ∧ k < m } ∪
     set (MAP FST (bvl_to_bvi$stubs x y))`,
  recInduct bvl_to_bviTheory.compile_exps_ind
  \\ rw[bvl_to_bviTheory.compile_exps_def]
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ imp_res_tac destLet_code_labels \\ fs[NULL_EQ]
  \\ fsrw_tac[DNF_ss][SUBSET_DEF, PULL_EXISTS]
  \\ imp_res_tac bvl_to_bviProofTheory.compile_exps_aux_sorted \\ fs[]
  \\ imp_res_tac bvl_to_bviTheory.compile_exps_SING \\ rveq \\ fs[bvl_to_bviTheory.compile_aux_def]
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (disj1_tac \\ rpt disj2_tac
      \\ rw[] \\ res_tac \\ fs[]
      \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ qspecl_then[`op`,`c1`]mp_tac(Q.GENL[`op`,`c`]compile_op_code_labels)
    \\ simp[SUBSET_DEF, PULL_EXISTS]
    \\ disch_then drule
    \\ strip_tac
    \\ TRY(last_x_assum drule \\ simp[] \\ strip_tac \\
            ((ntac 2 disj1_tac \\ disj2_tac \\ rpt(asm_exists_tac \\ simp[]) \\ NO_TAC) ORELSE
             (disj1_tac \\ rpt disj2_tac \\ asm_exists_tac \\ simp[] \\ NO_TAC) ORELSE
             (rpt disj2_tac \\ fs[] \\ NO_TAC)))
    \\ rpt disj1_tac
    \\ rveq \\ simp[]
    \\ metis_tac[])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    disj1_tac
    \\ disj2_tac
    \\ disj2_tac
    \\ rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    Cases_on`dest` \\ fs[] \\ rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``])
  >- (
    Cases_on`dest` \\ fs[] \\ rw[] \\ res_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS, LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_LESS_TRANS, DECIDE``n < n+1n``]));

val compile_exps_aux_contains = Q.store_thm("compile_exps_aux_contains",
  `∀n es c aux n1. compile_exps n es = (c,aux,n1) ⇒
    { bvl_num_stubs + (k * bvl_to_bvi_namespaces + 1) | k | n ≤ k ∧ k < n1 } ⊆ set (MAP FST (append aux))`,
  ho_match_mp_tac bvl_to_bviTheory.compile_exps_ind
  \\ rw[bvl_to_bviTheory.compile_exps_def]
  \\ rpt (pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ fs[SUBSET_DEF, PULL_EXISTS] \\ rw[]
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS] )
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ Cases_on`k < n2` >- metis_tac[]
    \\ fs[NOT_LESS]  )
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ Cases_on`k < n2` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ `k = n2` by decide_tac \\ rveq \\ fs[]
    \\ fs[bvl_to_bviTheory.compile_aux_def] )
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS]  )
  >- (
    rename1`_ = (c1,aux1,m1)`
    \\ Cases_on`k < m1` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ Cases_on`k < n2` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ Cases_on`k < n3` >- metis_tac[]
    \\ fs[NOT_LESS]
    \\ `k = n3` by decide_tac \\ rveq \\ fs[]
    \\ fs[bvl_to_bviTheory.compile_aux_def] ));

val compile_single_get_code_labels = Q.store_thm("compile_single_get_code_labels",
  `∀n p code m. compile_single n p = (code, m) ⇒
      BIGUNION (set (MAP (bvi_get_code_labels o SND o SND) (append code))) ⊆
      IMAGE (λk. bvl_num_stubs + k * bvl_to_bvi_namespaces) (bvl_get_code_labels (SND(SND p))) ∪
      set (MAP FST (append code)) ∪
      set (MAP FST (bvl_to_bvi$stubs x y))`,
  rw[]
  \\ PairCases_on`p`
  \\ fs[bvl_to_bviTheory.compile_single_def]
  \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
  \\ imp_res_tac compile_exps_get_code_labels
  \\ imp_res_tac bvl_to_bviTheory.compile_exps_SING
  \\ rveq \\ fs[]
  \\ fs[bvl_to_bviTheory.compile_exps_def]
  \\ first_x_assum(qspecl_then[`y`,`x`]mp_tac)
  \\ fs[SUBSET_DEF, PULL_EXISTS] \\ strip_tac
  \\ drule compile_exps_aux_contains
  \\ fsrw_tac[DNF_ss][SUBSET_DEF] \\ rw[]
  \\ metis_tac[]);

val compile_list_get_code_labels = Q.store_thm("compile_list_get_code_labels",
    `∀n p code m. compile_list n p = (code,m) ⇒
     n ≤ m ∧
     BIGUNION (set (MAP (bvi_get_code_labels o SND o SND) (append code))) ⊆
     set (MAP FST (append code)) ∪
     IMAGE (λk. bvl_num_stubs + k * bvl_to_bvi_namespaces)
       (BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) p))) ∪
     set (MAP FST (bvl_to_bvi$stubs x y))`,
  Induct_on`p`
  \\ rw[bvl_to_bviTheory.compile_list_def]
  >- (EVAL_TAC \\ rw[])
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ first_x_assum drule \\ rw[]
  >- (
    PairCases_on`h`
    \\ fs[bvl_to_bviTheory.compile_single_def]
    \\ pairarg_tac \\ fs[]
    \\ imp_res_tac bvl_to_bviProofTheory.compile_exps_aux_sorted
    \\ fs[] )
  >- (
    drule compile_single_get_code_labels
    \\ rw[]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fsrw_tac[DNF_ss][] \\ rw[]
    \\ first_x_assum drule
    \\ simp[]
    \\ strip_tac \\ fs[]
    \\ metis_tac[LESS_LESS_EQ_TRANS,LESS_EQ_LESS_TRANS,LESS_TRANS] )
  >- (
    fs[SUBSET_DEF, PULL_EXISTS] \\ rw[]
    \\ fsrw_tac[DNF_ss][]
    \\ first_x_assum drule \\ rw[]
    \\ PairCases_on`h`
    \\ fs[bvl_to_bviTheory.compile_single_def]
    \\ pairarg_tac \\ fs[]
    \\ imp_res_tac bvl_to_bviProofTheory.compile_exps_aux_sorted
    \\ metis_tac[LESS_LESS_EQ_TRANS,LESS_EQ_LESS_TRANS,LESS_TRANS,LESS_EQ_TRANS] ));

val compile_prog_get_code_labels_TODO_move = Q.store_thm("compile_prog_get_code_labels_TODO_move",
  `∀s n p t q m.
   bvl_to_bvi$compile_prog s n p = (t,q,m) ⇒
   BIGUNION (set (MAP (bvi_get_code_labels o SND o SND) q)) ⊆
     bvl_num_stubs + s * bvl_to_bvi_namespaces INSERT
     set (MAP FST q) ∪
     IMAGE (λk. bvl_num_stubs + (k * bvl_to_bvi_namespaces)) (BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) p))) `,
  rw[bvl_to_bviTheory.compile_prog_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[]
  \\ drule (GEN_ALL compile_list_get_code_labels)
  \\ strip_tac
  \\ reverse conj_tac
  >- (
    qmatch_goalsub_abbrev_tac`stubs x y`
    \\ first_x_assum(qspecl_then[`y`,`x`]strip_assume_tac)
    \\ fs[SUBSET_DEF, PULL_EXISTS] \\ metis_tac[] )
  \\ simp[bvl_to_bviTheory.stubs_def]
  \\ rpt conj_tac
  \\ CONV_TAC(LAND_CONV EVAL) \\ simp[] \\ EVAL_TAC
  \\ simp[]);

val compile_list_code_labels_domain = Q.store_thm("compile_list_code_labels_domain",
  `∀n p code m. compile_list n p = (code,m) ⇒
     n ≤ m ∧
     set (MAP FST (append code)) =
     IMAGE (λk. bvl_num_stubs + k * bvl_to_bvi_namespaces) (set (MAP FST p)) ∪
     { bvl_num_stubs + k * bvl_to_bvi_namespaces + 1 | k | n ≤ k ∧ k < m }`,
  Induct_on`p`
  \\ rw[bvl_to_bviTheory.compile_list_def]
  >- (EVAL_TAC \\ rw[])
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq \\ fs[]
  \\ first_x_assum drule \\ rw[]
  >- (
    PairCases_on`h`
    \\ fs[bvl_to_bviTheory.compile_single_def]
    \\ pairarg_tac \\ fs[]
    \\ imp_res_tac bvl_to_bviProofTheory.compile_exps_aux_sorted
    \\ fs[] )
  \\ PairCases_on`h`
  \\ fs[bvl_to_bviTheory.compile_single_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac bvl_to_bviProofTheory.compile_exps_aux_sorted
  \\ fs[] \\ rveq \\ fs[]
  \\ imp_res_tac compile_exps_aux_contains
  \\ fs[EVERY_MEM, SUBSET_DEF, PULL_EXISTS]
  \\ simp[Once EXTENSION]
  \\ rw[EQ_IMP_THM] \\ fs[between_def]
  \\ res_tac \\ fs[backend_commonTheory.bvl_to_bvi_namespaces_def] \\ rveq
  \\ fs[EVAL``bvl_num_stubs``] \\ rw[]
  \\ Cases_on`n1 ≤ k` \\ fs[]);

val compile_prog_code_labels_domain = Q.store_thm("compile_prog_code_labels_domain",
  `∀s n p t q m.
   bvl_to_bvi$compile_prog s n p = (t,q,m) ⇒
   set (MAP FST q) =
     IMAGE (λk. bvl_num_stubs + k * bvl_to_bvi_namespaces) (set (MAP FST p)) ∪
     { bvl_num_stubs + k * bvl_to_bvi_namespaces + 1 | k | n ≤ k ∧ k < m } ∪
     set (MAP FST (bvl_to_bvi$stubs x y))`,
  rw[bvl_to_bviTheory.compile_prog_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[]
  \\ drule compile_list_code_labels_domain \\ rw[]
  \\ rw[bvl_to_bviTheory.stubs_def]
  \\ metis_tac[UNION_ASSOC, UNION_COMM]);

val LetLet_code_labels = Q.store_thm("LetLet_code_labels[simp]",
  `bvl_get_code_labels (LetLet x y z) = bvl_get_code_labels z`,
  rw[bvl_handleTheory.LetLet_def]
  \\ rw[bvl_handleTheory.SmartLet_def, MAP_MAP_o, o_DEF, MAP_GENLIST]
  \\ rw[Once EXTENSION, MEM_FILTER, MEM_MAP, MEM_GENLIST, PULL_EXISTS, PULL_FORALL]
  \\ rw[EQ_IMP_THM]
  \\ rpt(pop_assum mp_tac)
  \\ TOP_CASE_TAC \\ fs[]
  \\ EVAL_TAC);

val compile_code_labels_TODO_move = Q.store_thm("compile_code_labels_TODO_move",
  `∀a b c. BIGUNION (set (MAP bvl_get_code_labels (FST (bvl_handle$compile a b c)))) ⊆
           BIGUNION (set (MAP bvl_get_code_labels c))`,
  recInduct bvl_handleTheory.compile_ind
  \\ rw[bvl_handleTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs[])
  \\ imp_res_tac bvl_handleTheory.compile_sing
  \\ rveq \\ fs[NULL_EQ] \\ rw[bvl_handleTheory.OptionalLetLet_def]
  \\ fs[]
  \\ fsrw_tac[DNF_ss][SUBSET_DEF]
  \\ EVAL_TAC);

val dest_var_code_labels_TODO_move = Q.store_thm("dest_var_code_labels_TODO_move[simp]",
  `∀x. bvl_get_code_labels (delete_var x) = bvl_get_code_labels x`,
  recInduct bvl_constTheory.delete_var_ind
  \\ rw[bvl_constTheory.delete_var_def]
  \\ EVAL_TAC);

val dest_simple_SOME_code_labels = Q.store_thm("dest_simple_SOME_code_labels",
  `∀x y. dest_simple x = SOME y ⇒ bvl_get_code_labels x = {}`,
  recInduct bvl_constTheory.dest_simple_ind
  \\ rw[NULL_EQ] \\ EVAL_TAC);

val SmartOp2_code_labels = Q.store_thm("SmartOp2_code_labels[simp]",
  `bvl_get_code_labels (SmartOp2 (op,x1,x2)) =
    assign_get_code_label op ∪ bvl_get_code_labels x1 ∪ bvl_get_code_labels x2`,
  rw[bvl_constTheory.SmartOp2_def, assign_get_code_label_def]
  \\ rpt(PURE_CASE_TAC \\ simp[assign_get_code_label_def])
  \\ imp_res_tac dest_simple_SOME_code_labels \\ fs[]
  \\ fs[bvl_constTheory.case_op_const_def, CaseEq"option", CaseEq"op", CaseEq"bvl$exp", CaseEq"list", NULL_EQ]
  \\ rveq \\ fs[assign_get_code_label_def,bvlTheory.Bool_def]
  \\ simp[EXTENSION] \\ metis_tac[]);

val SmartOp_code_labels = Q.store_thm("SmartOp_code_labels[simp]",
  `bvl_get_code_labels (SmartOp op xs) = assign_get_code_label op ∪ BIGUNION (set (MAP bvl_get_code_labels xs))`,
  rw[bvl_constTheory.SmartOp_def]
  \\ PURE_CASE_TAC \\ simp[]
  \\ PURE_CASE_TAC \\ simp[]
  \\ PURE_CASE_TAC \\ simp[]
  \\ simp[bvl_constTheory.SmartOp_flip_def]
  \\ PURE_TOP_CASE_TAC \\ fs[]
  >- ( rw[EXTENSION] \\ metis_tac[] )
  \\ imp_res_tac dest_simple_SOME_code_labels
  \\ rw[assign_get_code_label_def]);

val MEM_extract_list_code_labels = Q.store_thm("MEM_extract_list_code_labels",
  `∀xs x. MEM (SOME x) (extract_list xs) ⇒ bvl_get_code_labels x = {}`,
  Induct
  \\ rw[bvl_constTheory.extract_list_def]
  \\ res_tac \\ fs[]
  \\ Cases_on`h` \\ fs[bvl_constTheory.extract_def]
  \\ rename1`Op op l`
  \\ Cases_on`op` \\ fs[bvl_constTheory.extract_def] \\ rw[]
  \\ EVAL_TAC);

val compile_code_labels_TODO_move_1 = Q.store_thm("compile_code_labels_TODO_move_1",
  `∀x y. BIGUNION (set (MAP bvl_get_code_labels (bvl_const$compile x y))) ⊆
         BIGUNION (set (MAP bvl_get_code_labels y)) ∪
         BIGUNION (set (MAP (bvl_get_code_labels o THE) (FILTER IS_SOME x)))`,
  recInduct bvl_constTheory.compile_ind
  \\ rw[bvl_constTheory.compile_def]
  \\ fsrw_tac[DNF_ss][SUBSET_DEF]
  \\ fs[Once(GSYM bvl_constTheory.compile_HD_SING)]
  \\ fsrw_tac[ETA_ss][MAP_MAP_o, o_DEF]
  \\ TRY(metis_tac[])
  >- (
    PURE_CASE_TAC \\ fs[]
    \\ PURE_CASE_TAC \\ fs[]
    \\ rw[]
    \\ asm_exists_tac \\ fs[]
    \\ fs[LLOOKUP_THM]
    \\ fs[MEM_MAP, MEM_FILTER, IS_SOME_EXISTS, PULL_EXISTS]
    \\ simp[MEM_EL, PULL_EXISTS]
    \\ goal_assum(first_assum o mp_then Any mp_tac) \\ simp[]
    \\ PURE_FULL_CASE_TAC \\ fs[] )
  >- (
    rw[]
    \\ last_x_assum drule
    \\ rw[] >- metis_tac[]
    \\ reverse(fs[MEM_MAP, PULL_EXISTS, MEM_FILTER, IS_SOME_EXISTS])
    >- metis_tac[]
    \\ imp_res_tac MEM_extract_list_code_labels
    \\ fs[]));

val compile_exp_code_labels_TODO_move_1 = Q.store_thm("compile_exp_code_labels_TODO_move_1",
  `∀e. bvl_get_code_labels (bvl_const$compile_exp e) ⊆ bvl_get_code_labels e`,
  rw[bvl_constTheory.compile_exp_def]
  \\ rw[Once(GSYM bvl_constTheory.compile_HD_SING)]
  \\ specl_args_of_then``bvl_const$compile``compile_code_labels_TODO_move_1 mp_tac
  \\ rw[] \\ fs[Once(GSYM bvl_constTheory.compile_HD_SING)]);

val compile_exp_code_labels_TODO_move = Q.store_thm("compile_exp_code_labels_TODO_move",
  `∀a b c. bvl_get_code_labels (compile_exp a b c) ⊆ bvl_get_code_labels c `,
  rw[bvl_handleTheory.compile_exp_def]
  \\ Cases_on`bvl_handle$compile a b [compile_exp c]`
  \\ PairCases_on`r`
  \\ imp_res_tac bvl_handleTheory.compile_sing \\ rveq \\ fs[]
  \\ pop_assum mp_tac
  \\ specl_args_of_then``bvl_handle$compile``compile_code_labels_TODO_move mp_tac
  \\ rw[] \\ fs[]
  \\ metis_tac[compile_exp_code_labels_TODO_move_1, SUBSET_TRANS]);

val var_list_code_labels_imp = Q.store_thm("var_list_code_labels_imp",
  `∀n x y. var_list n x y ⇒ BIGUNION (set (MAP bvl_get_code_labels x)) = {} (*∧
                            BIGUNION (set (MAP bvl_get_code_labels y)) = {}*)`,
  recInduct bvl_inlineTheory.var_list_ind
  \\ rw[bvl_inlineTheory.var_list_def] \\ fs[]);

val let_op_code_labels = Q.store_thm("let_op_code_labels",
  `∀x. BIGUNION (set (MAP bvl_get_code_labels (let_op x))) = BIGUNION (set (MAP bvl_get_code_labels x))`,
  recInduct bvl_inlineTheory.let_op_ind
  \\ rw[bvl_inlineTheory.let_op_def]
  \\ full_simp_tac std_ss [Once(GSYM bvl_inlineProofTheory.HD_let_op)] \\ fs[]
  \\ PURE_CASE_TAC \\ fs[]
  \\ Cases_on`HD (let_op [x2])` \\ fs[bvl_inlineTheory.dest_op_def]
  \\ rveq
  \\ imp_res_tac var_list_code_labels_imp
  \\ fs[] \\ rveq \\ fs[]
  \\ simp[EXTENSION]
  \\ metis_tac[]);

val let_op_sing_code_labels = Q.store_thm("let_op_sing_code_labels[simp]",
  `bvl_get_code_labels (let_op_sing x) = bvl_get_code_labels x`,
  rw[bvl_inlineTheory.let_op_sing_def]
  \\ simp_tac std_ss [Once(GSYM bvl_inlineProofTheory.HD_let_op)]
  \\ simp[]
  \\ specl_args_of_then``bvl_inline$let_op``let_op_code_labels mp_tac
  \\ simp_tac std_ss [Once(GSYM bvl_inlineProofTheory.HD_let_op)]
  \\ rw[]);

val remove_ticks_code_labels = Q.store_thm("remove_ticks_code_labels",
  `∀x.
     BIGUNION (set (MAP bvl_get_code_labels (remove_ticks x))) =
     BIGUNION (set (MAP bvl_get_code_labels x))`,
  recInduct bvl_inlineTheory.remove_ticks_ind
  \\ rw[bvl_inlineTheory.remove_ticks_def]
  \\ FULL_SIMP_TAC std_ss [Once (GSYM bvl_inlineTheory.remove_ticks_SING)] \\ fs[]);

(* TODO move *)
val dest_Seq_SOME = Q.store_thm("dest_Seq_SOME",
  `!e. dest_Seq e = SOME (x, y) <=> e = Let [x; y] (Var 1)`,
  Cases \\ fs [bvl_handleTheory.dest_Seq_def]
  \\ rename1 `Let xs e` \\ Cases_on `xs` \\ fs [bvl_handleTheory.dest_Seq_def]
  \\ rename1 `_::xs` \\ Cases_on `xs` \\ fs [bvl_handleTheory.dest_Seq_def]
  \\ rename1 `_::_::xs` \\ Cases_on `xs` \\ fs [bvl_handleTheory.dest_Seq_def]
  \\ Cases_on `e` \\ fs [bvl_handleTheory.dest_Seq_def]
  \\ metis_tac []);

val compile_seqs_code_labels = Q.store_thm("compile_seqs_code_labels",
  `!cut e acc.
     bvl_get_code_labels (compile_seqs cut e acc) SUBSET
     bvl_get_code_labels e UNION
     (case acc of NONE => {} | SOME r => bvl_get_code_labels r)`,
  ho_match_mp_tac bvl_handleTheory.compile_seqs_ind \\ rw []
  \\ rw [Once bvl_handleTheory.compile_seqs_def]
  \\ rpt (PURE_TOP_CASE_TAC \\ fs []) \\ rw []
  \\ fs [dest_Seq_SOME] \\ rw []
  \\ metis_tac [compile_exp_code_labels_TODO_move, SUBSET_UNION, SUBSET_TRANS, UNION_SUBSET]);

val optimise_get_code_labels = Q.store_thm("optimise_get_code_labels",
  `∀x y z.
     bvl_get_code_labels (SND (SND (optimise x y z))) ⊆
     bvl_get_code_labels (SND (SND z))`,
  rpt gen_tac \\ PairCases_on`z`
  \\ reverse(rw[bvl_inlineTheory.optimise_def, bvl_handleTheory.compile_any_def, bvl_handleTheory.compile_exp_def])
  >- (
    specl_args_of_then``bvl_handle$compile``compile_code_labels_TODO_move mp_tac
    \\ rw[]
    \\ qmatch_goalsub_abbrev_tac`bvl_handle$compile a b c`
    \\ Cases_on`bvl_handle$compile a b c`
    \\ PairCases_on`r`
    \\ unabbrev_all_tac
    \\ imp_res_tac bvl_handleTheory.compile_sing
    \\ rveq
    \\ qpat_x_assum`_ ⊆ _`mp_tac
    \\ simp[]
    \\ strip_tac
    \\ match_mp_tac SUBSET_TRANS
    \\ asm_exists_tac \\ simp[]
    \\ match_mp_tac SUBSET_TRANS
    \\ specl_args_of_then``bvl_const$compile_exp`` compile_exp_code_labels_TODO_move_1 mp_tac
    \\ strip_tac \\ asm_exists_tac \\ simp[]
    \\ specl_args_of_then``bvl_inline$remove_ticks`` remove_ticks_code_labels mp_tac
    \\ SIMP_TAC std_ss [Once (GSYM bvl_inlineTheory.remove_ticks_SING)] \\ fs[] )
  \\ Cases_on `remove_ticks [z2]` \\ fs []
  \\ first_assum (assume_tac o Q.AP_TERM `LENGTH`) \\ fs [] \\ rw []
  \\ qspec_then `[z2]` assume_tac remove_ticks_code_labels \\ fs [] \\ rfs []
  \\ pop_assum (SUBST1_TAC o GSYM)
  \\ qspecl_then [`y`,`let_op_sing h`,`NONE`]
       assume_tac compile_seqs_code_labels \\ fs []);

val mk_tick_code_labels = Q.store_thm("mk_tick_code_labels[simp]",
  `!n x. bvl_get_code_labels (mk_tick n x) = bvl_get_code_labels x`,
  Induct \\ rw [] \\ fs [bvlTheory.mk_tick_def, FUNPOW_SUC]);

val tick_inline_code_labels = Q.store_thm ("tick_inline_code_labels",
  `!cs xs.
     BIGUNION (set (MAP bvl_get_code_labels (tick_inline cs xs))) SUBSET
     BIGUNION (set (MAP bvl_get_code_labels xs)) UNION
     BIGUNION (set (MAP (bvl_get_code_labels o SND) (toList cs)))`,
  ho_match_mp_tac bvl_inlineTheory.tick_inline_ind
  \\ rw [bvl_inlineTheory.tick_inline_def]
  \\ TRY
   (qmatch_goalsub_rename_tac `_ (HD (tick_inline cs [x])) SUBSET _`
    \\ Cases_on `tick_inline cs [x]`
    \\ pop_assum (assume_tac o Q.AP_TERM `LENGTH`)
    \\ fs [bvl_inlineTheory.LENGTH_tick_inline] \\ rw []
    \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
  \\ TRY
   (rename1 `assign_get_code_label op`
    \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac [])
  \\ TRY (* what... *)
   (rename1 `option_CASE dest`
    \\ rpt (PURE_FULL_CASE_TAC \\ fs []) \\ rw []
    \\ fs [SUBSET_DEF] \\ rw []
    \\ fs [MEM_MAP, MEM_toList]
    \\ metis_tac [FST, SND, PAIR])
  \\ Cases_on `tick_inline cs [x1]` \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ Cases_on `tick_inline cs [x2]` \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ Cases_on `tick_inline cs [x3]` \\ pop_assum (mp_tac o Q.AP_TERM `LENGTH`)
  \\ rw [bvl_inlineTheory.LENGTH_tick_inline]
  \\ fs [SUBSET_DEF] \\ rw [] \\ metis_tac []);

val tick_inline_all_code_labels = Q.store_thm("tick_inline_all_code_labels",
  `!limit cs xs aux cs1 xs1.
     tick_inline_all limit cs xs aux = (cs1, xs1)
     ==>
     BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) xs1)) SUBSET
     BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) xs)) UNION
     BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) aux)) UNION
     BIGUNION (set (MAP (bvl_get_code_labels o SND) (toList cs)))`,
  ho_match_mp_tac bvl_inlineTheory.tick_inline_all_ind
  \\ rw [bvl_inlineTheory.tick_inline_all_def]
  \\ fs [MAP_REVERSE]
  \\ Cases_on `tick_inline cs [e1]`
  \\ first_assum (assume_tac o Q.AP_TERM `LENGTH`)
  \\ fs [bvl_inlineTheory.LENGTH_tick_inline] \\ rw []
  \\ qispl_then [`cs`,`[e1]`] assume_tac tick_inline_code_labels \\ fs [] \\ rfs []
  \\ fs [AC UNION_COMM UNION_ASSOC]
  \\ qmatch_goalsub_abbrev_tac `s1 SUBSET s2 UNION (s3 UNION (s4 UNION s5))`
  \\ fs [SUBSET_DEF] \\ rw []
  \\ rpt (first_x_assum drule \\ rw []) \\ fs []
  \\ fs [MEM_MAP, MEM_toList, lookup_insert]
  \\ FULL_CASE_TAC \\ fs [] \\ rw [] \\ fs []
  \\ res_tac \\ fs []
  \\ fs [Abbr `s3`, MEM_MAP, MEM_toList, PULL_EXISTS]
  \\ metis_tac [PAIR, FST, SND]);

val compile_prog_get_code_labels_TODO_move_1 = Q.store_thm("compile_prog_get_code_labels_TODO_move_1",
  `bvl_inline$compile_prog x y z p = (inlines,q) ⇒
   BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) q)) ⊆
   BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) p))`,
  rw[bvl_inlineTheory.compile_prog_def, bvl_inlineTheory.compile_inc_def, bvl_inlineTheory.tick_compile_prog_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ simp[MAP_MAP_o, o_DEF]
  \\ match_mp_tac SUBSET_TRANS
  \\ qexists_tac`BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) prog1))`
  \\ conj_tac
  >- (
    rw[SUBSET_DEF, MEM_MAP, PULL_EXISTS]
    \\ rpt(pop_assum mp_tac)
    \\ specl_args_of_then``bvl_inline$optimise``optimise_get_code_labels mp_tac
    \\ rw[SUBSET_DEF]
    \\ metis_tac[])
  \\ imp_res_tac tick_inline_all_code_labels
  \\ fs [o_DEF, toList_def, toListA_def]);

val set_MAP_code_sort = Q.store_thm("set_MAP_code_sort",
  `LIST_TO_SET (MAP f (code_sort x)) = set (MAP f x)`,
  Q.ISPEC_THEN`x`mp_tac clos_to_bvlProofTheory.PERM_code_sort
  \\ rw[EXTENSION, MEM_MAP]
  \\ imp_res_tac MEM_PERM \\ fs[]);

val assign_get_code_label_compile_op = Q.store_thm("assign_get_code_label_compile_op",
  `assign_get_code_label (compile_op op) = case some n. op = Label n of SOME n => {n} | _ => {}`,
  Cases_on`op` \\ rw[clos_to_bvlTheory.compile_op_def, assign_get_code_label_def]);

val clos_get_code_labels_def = tDefine"bvl_get_code_labels" `
  (clos_get_code_labels (Var _ _) = {}) ∧
  (clos_get_code_labels (If _ e1 e2 e3) =
    clos_get_code_labels e1 ∪
    clos_get_code_labels e2 ∪
    clos_get_code_labels e3) ∧
  (clos_get_code_labels (Let _ es e) =
    BIGUNION (set (MAP clos_get_code_labels es)) ∪
    clos_get_code_labels e) ∧
  (clos_get_code_labels (Raise _ e) = clos_get_code_labels e) ∧
  (clos_get_code_labels (Handle _ e1 e2) =
    clos_get_code_labels e1 ∪
    clos_get_code_labels e2) ∧
  (clos_get_code_labels (Tick _ e) = clos_get_code_labels e) ∧
  (clos_get_code_labels (Call _ _ l es) =
    {l} ∪ BIGUNION (set (MAP clos_get_code_labels es))) ∧
  (clos_get_code_labels (App _ l e es) =
    (case l of NONE => {} | SOME n => {n}) ∪
    clos_get_code_labels e ∪
    BIGUNION (set (MAP clos_get_code_labels es))) ∧
  (clos_get_code_labels (Fn _ l _ _ e) =
   (case l of NONE => {} | SOME n => {n}) ∪
   clos_get_code_labels e) ∧
  (clos_get_code_labels (Letrec _ l _ es e) =
   (case l of NONE => {} | SOME n =>
     IMAGE (λk. n + 2 * k) (count (LENGTH es))) ∪
    clos_get_code_labels e ∪
    BIGUNION (set (MAP clos_get_code_labels (MAP SND es)))) ∧
  (clos_get_code_labels (Op _ op es) =
    BIGUNION (set (MAP clos_get_code_labels es)) ∪
    assign_get_code_label op)`
  (wf_rel_tac `measure exp_size`
   \\ simp [closLangTheory.exp_size_def]
   \\ rpt conj_tac \\ rpt gen_tac
   \\ Induct_on`es`
   \\ rw [closLangTheory.exp_size_def]
   \\ simp [] \\ res_tac \\ simp []);

val clos_get_code_labels_def =
  clos_get_code_labels_def
  |> SIMP_RULE (srw_ss()++ETA_ss)[MAP_MAP_o]
  |> curry save_thm "clos_get_code_labels_def[simp]"

val SUM_SET_count_2 = Q.store_thm("SUM_SET_count_2",
  `∀n. 2 * SUM_SET (count (SUC n)) = n * (n + 1)`,
  Induct \\ rw[Once COUNT_SUC, SUM_SET_THM, LEFT_ADD_DISTRIB, SUM_SET_DELETE]
  \\ rewrite_tac[EXP, ONE, TWO, MULT, ADD, LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
  \\ rw[]);

val SUM_SET_count = Q.store_thm("SUM_SET_count",
  `∀n. n ≠ 0 ⇒ SUM_SET (count n) = n * (n - 1) DIV 2`,
  Cases \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`a = b`
  \\ qspecl_then[`2`,`a`,`b`]mp_tac EQ_MULT_LCANCEL
  \\ disch_then(mp_tac o #1 o EQ_IMP_RULE)
  \\ CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV(srw_ss())[])))
  \\ disch_then irule
  \\ unabbrev_all_tac
  \\ rewrite_tac[SUM_SET_count_2]
  \\ simp[ADD1, LEFT_ADD_DISTRIB, bitTheory.DIV_MULT_THM2]
  \\ qmatch_goalsub_abbrev_tac`a = a - a MOD 2`
  \\ `a MOD 2 = 0` suffices_by simp[]
  \\ simp[Abbr`a`,GSYM EVEN_MOD2]
  \\ simp[EVEN_ADD]
  \\ rw[EVEN_EXP_IFF]);

val domain_init_code = Q.store_thm("domain_init_code",
  `0 < max_app ⇒ domain (init_code max_app) = count (max_app + max_app * (max_app - 1) DIV 2)`,
  rw[clos_to_bvlTheory.init_code_def, domain_fromList, LENGTH_FLAT, MAP_GENLIST, o_DEF,
     GSYM SUM_IMAGE_count_SUM_GENLIST]
  \\ qmatch_goalsub_abbrev_tac`SUM_IMAGE f`
  \\ `f = I` by simp[Abbr`f`,FUN_EQ_THM]
  \\ rw[GSYM SUM_SET_DEF, SUM_SET_count]);

val MEM_build_aux_imp_SND_MEM = Q.store_thm("MEM_build_aux_imp_SND_MEM",
  `∀n ls acc m aux x.
    build_aux n ls acc = (m,aux) ∧ MEM x aux ⇒
     MEM (SND x) ls ∨ MEM x acc`,
  Induct_on`ls`
  \\ rw[clos_to_bvlTheory.build_aux_def]
  \\ first_x_assum drule \\ rw[]
  \\ first_x_assum drule \\ rw[] \\ fs[]);

val recc_Lets_code_labels = Q.store_thm("recc_Lets_code_labels",
  `∀n nargs k rest. bvl_get_code_labels (recc_Lets n nargs k rest) =
   IMAGE (λj. n + 2 * j) (count k) ∪ bvl_get_code_labels rest`,
  recInduct clos_to_bvlTheory.recc_Lets_ind \\ rw[]
  \\ rw[Once clos_to_bvlTheory.recc_Lets_def] \\ fs[]
  \\ fs[clos_to_bvlTheory.recc_Let_def, assign_get_code_label_def]
  \\ rw[Once EXTENSION]
  \\ Cases_on`k` \\ fs[]
  \\ fsrw_tac[DNF_ss][EQ_IMP_THM, PULL_EXISTS,ADD1] \\ rw[ADD1]
  >- ( disj1_tac \\ qexists_tac`n'` \\ simp[] )
  \\ Cases_on`j < n'` \\ fs[]);

val compile_exps_code_labels = Q.store_thm("compile_exps_code_labels",
  `!app es1 aux1 es2 aux2.
     compile_exps app es1 aux1 = (es2, aux2) ∧
     EVERY no_Labels es1 ∧ 0 < app ∧ EVERY (obeys_max_app app) es1 ∧ every_Fn_SOME es1
     ==>
     BIGUNION (set (MAP bvl_get_code_labels es2)) ∪
     BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) aux2))
     ⊆
     IMAGE (((+) (num_stubs app))) (BIGUNION (set (MAP clos_get_code_labels es1))) ∪
     BIGUNION (set (MAP (bvl_get_code_labels o SND o SND) aux1)) ∪
     domain (init_code app)`,
  recInduct clos_to_bvlTheory.compile_exps_ind
  \\ rw [clos_to_bvlTheory.compile_exps_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs []) \\ rw []
  \\ imp_res_tac clos_to_bvlTheory.compile_exps_SING \\ rveq \\ fs []
  \\ fs[assign_get_code_label_def]
  \\ fs[MAP_GENLIST, o_DEF]
  \\ TRY (
    CHANGED_TAC(rw[assign_get_code_label_compile_op])
    \\ CASE_TAC \\ fs[]
    \\ Cases_on`op` \\ fs[assign_get_code_label_def]
    \\ fsrw_tac[DNF_ss][]
    \\ NO_TAC )
  \\ TRY (
    fs[SUBSET_DEF, PULL_EXISTS] \\ rw[]
    \\ last_x_assum (fn th => drule th \\ disch_then drule) \\ rw[]
    \\ metis_tac[] )
  \\ TRY (
    reverse PURE_CASE_TAC
    \\ fs[clos_to_bvlTheory.mk_cl_call_def, assign_get_code_label_def, MAP_GENLIST, o_DEF]
    \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_GENLIST, clos_to_bvlTheory.generic_app_fn_location_def]
    \\ rw[]
    >- (
      last_x_assum (fn th => drule th \\ disch_then drule) \\ rw[]
      \\ metis_tac[] )
    >- metis_tac[]
    >- (
      last_x_assum (fn th => drule th \\ disch_then drule) \\ rw[]
      \\ metis_tac[] )
    >- metis_tac[]
    \\ simp[domain_init_code]
    \\ imp_res_tac clos_to_bvlTheory.compile_exps_LENGTH
    \\ fs[] \\ NO_TAC)
  \\ TRY (
    reverse PURE_CASE_TAC
    \\ fs[clos_to_bvlTheory.mk_cl_call_def, assign_get_code_label_def, MAP_GENLIST, o_DEF, IS_SOME_EXISTS]
    \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_GENLIST, clos_to_bvlTheory.generic_app_fn_location_def]
    \\ rw[]
    \\ simp[domain_init_code, clos_to_bvlTheory.num_stubs_def]
    \\ fs[MEM_MAP, clos_to_bvlTheory.free_let_def, MEM_GENLIST] \\ rveq \\ fs[assign_get_code_label_def]
    \\ NO_TAC)
  \\ TRY (
    fs[IS_SOME_EXISTS] \\ rveq \\ fs[]
    \\ CHANGED_TAC(fs[CaseEq"list"]) \\ rveq \\ fs[]
    \\ TRY (
      CHANGED_TAC(fs[CaseEq"prod"]) \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[assign_get_code_label_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_MAP]
      \\ imp_res_tac clos_to_bvlTheory.compile_exps_SING \\ rveq \\ fs[] \\ rveq \\ rw[]
      \\ fs[clos_to_bvlTheory.build_aux_def, clos_to_bvlTheory.build_recc_lets_def]
      \\ rveq \\ fs[MEM_GENLIST, clos_to_bvlTheory.free_let_def,MEM_MAP, clos_to_bvlTheory.recc_Let0_def]
      \\ fsrw_tac[DNF_ss][assign_get_code_label_def]
      \\ metis_tac[] )
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ fsrw_tac[DNF_ss][SUBSET_DEF, PULL_EXISTS]
    \\ simp[clos_to_bvlTheory.build_recc_lets_def, assign_get_code_label_def]
    \\ fsrw_tac[DNF_ss][MEM_MAP, PULL_EXISTS, assign_get_code_label_def]
    \\ simp[clos_to_bvlTheory.recc_Let0_def, assign_get_code_label_def]
    \\ rw[]
    \\ TRY ( rpt disj1_tac \\ qexists_tac`SUC (LENGTH v7)` \\ simp[] \\ NO_TAC )
    \\ fs[recc_Lets_code_labels]
    \\ last_x_assum drule \\ rw[]
    >- metis_tac[]
    >- (
      drule MEM_build_aux_imp_SND_MEM
      \\ disch_then drule
      \\ reverse strip_tac
      >- (
        fs[clos_to_bvlTheory.compile_exps_def]
        \\ rveq \\ metis_tac[] )
      \\ imp_res_tac clos_to_bvlTheory.compile_exps_LENGTH
      \\ fs[MAP2_MAP, MEM_MAP, UNCURRY]
      \\ fs[clos_to_bvlTheory.code_for_recc_case_def, SND_EQ_EQUIV]
      \\ rveq \\ fs[assign_get_code_label_def, MEM_MAP, MEM_GENLIST] \\ rveq \\ fs[assign_get_code_label_def]
      \\ fs[MEM_ZIP] \\ rveq \\ fs[]
      \\ fs[clos_to_bvlTheory.compile_exps_def] \\ rveq \\ fs[]
      \\ `MEM (EL n (c1 ++ c2)) (c1 ++ c2)` by (
        simp[MEM_EL, EL_APPEND_EQN] \\ rw[]
        \\ Cases_on`n` \\ fs[LENGTH_EQ_NUM_compute]
        \\ rveq \\ fs[ADD1] \\ disj2_tac
        \\ qexists_tac`n'` \\ simp[] )
      \\ fs[]
      \\ metis_tac[] )
    >- metis_tac[])
  \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_GENLIST] \\ rw[] \\ metis_tac[]);

val compile_prog_code_labels = Q.store_thm("compile_prog_code_labels",
  `0 < max_app ∧
   EVERY no_Labels (MAP (SND o SND) prog) ∧
   EVERY (obeys_max_app max_app) (MAP (SND o SND) prog) ∧
   every_Fn_SOME (MAP (SND o SND) prog)
   ⇒
   BIGUNION (set (MAP (bvl_get_code_labels o SND o SND)
                   (compile_prog max_app prog))) SUBSET
   IMAGE (((+) (clos_to_bvl$num_stubs max_app))) (BIGUNION (set (MAP clos_get_code_labels (MAP (SND o SND) prog)))) ∪
   domain (init_code max_app)`,
  rw[clos_to_bvlTheory.compile_prog_def]
  \\ pairarg_tac \\ fs[]
  \\ imp_res_tac clos_to_bvlTheory.compile_exps_LENGTH \\ fs[]
  \\ simp[MAP2_MAP]
  \\ fs[MAP_MAP_o, o_DEF, UNCURRY]
  \\ simp[GSYM o_DEF, GSYM MAP_MAP_o, MAP_ZIP]
  \\ fs[MAP_MAP_o, o_DEF]
  \\ drule compile_exps_code_labels
  \\ simp[MAP_MAP_o, o_DEF]);

val bvl_get_code_labels_JumpList = Q.store_thm("bvl_get_code_labels_JumpList",
  `∀n xs. bvl_get_code_labels (JumpList n xs) = BIGUNION (set (MAP bvl_get_code_labels xs))`,
  recInduct bvl_jumpTheory.JumpList_ind
  \\ rw[]
  \\ rw[Once  bvl_jumpTheory.JumpList_def, assign_get_code_label_def]
  \\ fs[LENGTH_EQ_NUM_compute]
  \\ Q.ISPECL_THEN[`LENGTH xs DIV 2`,`xs`]
       ((fn th => CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[th]))) o SYM)TAKE_DROP
  \\ simp[]);

val clos_get_code_labels_shift = Q.store_thm("clos_get_code_labels_shift",
  `∀a b c d. MAP clos_get_code_labels (shift a b c d) = MAP clos_get_code_labels a`,
  recInduct clos_annotateTheory.shift_ind
  \\ rw[clos_annotateTheory.shift_def] \\ fs[]
  \\ simp[Once EXTENSION, MEM_MAP, PULL_EXISTS, UNCURRY, FORALL_PROD, EXISTS_PROD]
  \\ rw[EQ_IMP_THM] \\ fs[]
  \\ first_x_assum drule \\ rw[] \\ fs[]
  \\ metis_tac[HD]);

val call_dests_shift = Q.store_thm("call_dests_shift[simp]",
  `∀a b c d. app_call_dests opt (shift a b c d) = app_call_dests opt a`,
  recInduct clos_annotateTheory.shift_ind
  \\ rw[clos_annotateTheory.shift_def, closPropsTheory.app_call_dests_def,
        closPropsTheory.app_call_dests_append]
  \\ fs[] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[closPropsTheory.app_call_dests_map]
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ rw[MAP_MAP_o, MAP_EQ_f, FORALL_PROD]);

val clos_get_code_labels_alt_free = Q.store_thm("clos_get_code_labels_alt_free",
  `∀xs. BIGUNION (set (MAP clos_get_code_labels (FST (alt_free xs)))) ⊆
        BIGUNION (set (MAP clos_get_code_labels xs))`,
  recInduct clos_annotateTheory.alt_free_ind
  \\ rw[clos_annotateTheory.alt_free_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rw[] \\ fs[map_replicate, clos_annotateTheory.const_0_def, assign_get_code_label_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ imp_res_tac clos_annotateTheory.alt_free_SING \\ fs[MEM_REPLICATE_EQ]
  \\ fs[MEM_MAP, PULL_EXISTS, FORALL_PROD, UNCURRY, clos_annotateTheory.HD_FST_alt_free]
  \\ rw[Once(GSYM clos_annotateTheory.HD_FST_alt_free)]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ impl_tac >- metis_tac[clos_annotateTheory.HD_FST_alt_free, MEM]
  \\ metis_tac[SND]);

val app_call_dests_alt_free = Q.store_thm("app_call_dests_alt_free",
  `∀xs. (app_call_dests opt (FST (alt_free xs))) ⊆
        (app_call_dests opt xs)`,
  recInduct clos_annotateTheory.alt_free_ind
  \\ rw[clos_annotateTheory.alt_free_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rw[closPropsTheory.app_call_dests_def]
  \\ imp_res_tac clos_annotateTheory.alt_free_SING \\ fs[]
  \\ fs[SUBSET_DEF, PULL_EXISTS, GSYM MAP_K_REPLICATE]
  >- ( rw[Once closPropsTheory.app_call_dests_cons] \\ fs[] )
  \\ rw[closPropsTheory.app_call_dests_map, clos_annotateTheory.const_0_def,
        closPropsTheory.app_call_dests_def, MEM_MAP, FORALL_PROD, EXISTS_PROD] \\ fs[]
  \\ first_x_assum drule
  \\ rw[] \\ pairarg_tac \\ fs[] \\ rw[]
  \\ rw[PULL_EXISTS]
  \\ imp_res_tac clos_annotateTheory.alt_free_SING \\ fs[]
  \\ rw[] \\ fs[]
  \\ metis_tac[]);

val app_call_dests_annotate = Q.store_thm("app_call_dests_annotate",
  `app_call_dests opt (annotate n xs) ⊆ app_call_dests opt xs`,
  rw[clos_annotateTheory.annotate_def, app_call_dests_alt_free]);

val clos_get_code_labels_annotate = Q.store_thm("clos_get_code_labels_annotate",
  `BIGUNION (set (MAP clos_get_code_labels (annotate n xs))) ⊆
   BIGUNION (set (MAP clos_get_code_labels xs))`,
  rw[clos_annotateTheory.annotate_def, clos_get_code_labels_shift, clos_get_code_labels_alt_free]);

val clos_get_code_labels_chain_exps = Q.store_thm("clos_get_code_labels_chain_exps",
  `∀n es.
   BIGUNION (set (MAP (clos_get_code_labels o SND o SND) (chain_exps n es))) =
   BIGUNION (set (MAP (clos_get_code_labels) es)) ∪
   IMAGE ((+) n) (count (LENGTH es) DELETE 0)`,
  recInduct clos_to_bvlTheory.chain_exps_ind
  \\ rw[clos_to_bvlTheory.chain_exps_def, assign_get_code_label_def]
  >- ( EVAL_TAC \\ simp[] )
  \\ simp[Once EXTENSION, PULL_EXISTS, MEM_MAP, ADD1]
  \\ rw[EQ_IMP_THM] \\ fs[]
  \\ TRY (
    qmatch_assum_rename_tac`z ≠ 0`
    \\ Cases_on`z` \\ fs[ADD1]
    \\ Cases_on`n` \\ fs[]
    \\ NO_TAC)
  \\ metis_tac[]);

val clos_get_code_labels_code_locs = Q.store_thm("clos_get_code_labels_code_locs",
  `∀xs. EVERY no_Labels xs ∧ every_Fn_SOME xs ⇒
        BIGUNION (set (MAP clos_get_code_labels xs)) =
        set (code_locs xs) ∪ any_dests xs`,
  recInduct closPropsTheory.code_locs_ind
  \\ rw[closPropsTheory.code_locs_def, closPropsTheory.app_call_dests_def] \\ fs[]
  >- ( rw[EXTENSION] \\ metis_tac[] )
  >- ( rw[EXTENSION] \\ metis_tac[] )
  >- ( rw[EXTENSION] \\ metis_tac[] )
  >- ( Cases_on`op` \\ fs[assign_get_code_label_def] )
  >- (
    rw[EXTENSION]
    \\ PURE_TOP_CASE_TAC \\ fs[]
    \\ metis_tac[] )
  >- (
    fs[IS_SOME_EXISTS]
    \\ rw[EXTENSION]
    \\ metis_tac[] )
  >- (
    fs[IS_SOME_EXISTS]
    \\ fs[MAP_MAP_o]
    \\ rw[EXTENSION, MEM_GENLIST, MEM_MAP, PULL_EXISTS, closPropsTheory.code_locs_map, MEM_FLAT]
    \\ metis_tac[] )
  >- ( rw[EXTENSION] \\ metis_tac[] )
  >- ( rw[EXTENSION] \\ metis_tac[] ));

val BIGUNION_clos_get_code_labels_GENLIST_Var = store_thm(
   "BIGUNION_clos_get_code_labels_GENLIST_Var",
  ``!t n a. BIGUNION (set (MAP clos_get_code_labels (GENLIST_Var t n a))) = EMPTY``,
  Induct_on `a`
  \\ once_rewrite_tac [clos_callTheory.GENLIST_Var_def]
  \\ asm_simp_tac std_ss [ADD1,MAP_APPEND,LIST_TO_SET_APPEND,BIGUNION_UNION]
  \\ fs []);

val no_Labels_labs = store_thm("no_Labels_labs",
  ``!xs.
      EVERY no_Labels (MAP (SND o SND) xs) ==>
      EVERY no_Labels (MAP (SND ∘ SND) (clos_labels$compile xs))``,
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_labelsTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ rename [`(x1,x2,x3)`,`remove_dests ds`] \\ fs []
  \\ qspecl_then [`ds`,`[x3]`] mp_tac clos_labelsProofTheory.remove_dests_no_Labels
  \\ fs [clos_labelsProofTheory.EVERY_remove_dests_sing]);

val no_Labels_ann = store_thm("no_Labels_ann",
  ``!xs.
      EVERY no_Labels (MAP (SND o SND) xs) ==>
      EVERY no_Labels (MAP (SND ∘ SND) (clos_annotate$compile xs))``,
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_annotateTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ rename [`(x1,x2,x3)`]
  \\ `?t. annotate x2 [x3] = [t]` by
    (fs [clos_annotateTheory.annotate_def]
     \\ Cases_on `alt_free [x3]` \\ fs []
     \\ imp_res_tac clos_annotateTheory.alt_free_SING \\ fs [] \\ rveq
     \\ metis_tac [clos_annotateTheory.shift_SING])
  \\ fs []
  \\ qspecl_then [`x2`,`[x3]`] mp_tac clos_annotateProofTheory.annotate_no_Labels
  \\ fs []);

val obeys_max_app_labs = store_thm("obeys_max_app_labs",
  ``!xs.
      EVERY (obeys_max_app k) (MAP (SND o SND) xs) ==>
      EVERY (obeys_max_app k) (MAP (SND ∘ SND) (clos_labels$compile xs))``,
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_labelsTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ rename [`(x1,x2,x3)`,`remove_dests ds`] \\ fs []
  \\ qspecl_then [`ds`,`[x3]`] mp_tac
        clos_labelsProofTheory.remove_dests_obeys_max_app
  \\ fs [clos_labelsProofTheory.EVERY_remove_dests_sing]);

val obeys_max_app_ann = store_thm("obeys_max_app_ann",
  ``!xs.
      EVERY (obeys_max_app m) (MAP (SND o SND) xs) ==>
      EVERY (obeys_max_app m) (MAP (SND ∘ SND) (clos_annotate$compile xs))``,
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_annotateTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ rename [`(x1,x2,x3)`]
  \\ `?t. annotate x2 [x3] = [t]` by
    (fs [clos_annotateTheory.annotate_def]
     \\ Cases_on `alt_free [x3]` \\ fs []
     \\ imp_res_tac clos_annotateTheory.alt_free_SING \\ fs [] \\ rveq
     \\ metis_tac [clos_annotateTheory.shift_SING])
  \\ fs []
  \\ qspecl_then [`x2`,`[x3]`] mp_tac clos_annotateProofTheory.annotate_obeys_max_app
  \\ fs []);

val every_Fn_SOME_labs = store_thm("every_Fn_SOME_labs",
  ``!xs.
      every_Fn_SOME (MAP (SND o SND) xs) ==>
      every_Fn_SOME (MAP (SND ∘ SND) (clos_labels$compile xs))``,
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_labelsTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs [] \\ fs [MAP_MAP_o,o_DEF,UNCURRY]
  \\ rename [`remove_dests ds`] \\ fs []
  \\ Induct_on `xs` \\ fs []
  \\ once_rewrite_tac [closPropsTheory.every_Fn_SOME_APPEND
      |> Q.INST [`l1`|->`x::[]`] |> SIMP_RULE std_ss [APPEND]]
  \\ fs [] \\ rw []);

val every_Fn_SOME_ann = store_thm("every_Fn_SOME_ann",
  ``!xs.
      every_Fn_SOME (MAP (SND o SND) xs) ==>
      every_Fn_SOME (MAP (SND ∘ SND) (clos_annotate$compile xs))``,
  fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS,clos_annotateTheory.compile_def]
  \\ rw [] \\ res_tac \\ fs [] \\ fs [MAP_MAP_o,o_DEF,UNCURRY]
  \\ Induct_on `xs` \\ fs []
  \\ once_rewrite_tac [closPropsTheory.every_Fn_SOME_APPEND
      |> Q.INST [`l1`|->`x::[]`] |> SIMP_RULE std_ss [APPEND]]
  \\ fs [] \\ rw []
  \\ fs [clos_to_bvlProofTheory.HD_annotate_SING]
  \\ match_mp_tac clos_annotateProofTheory.every_Fn_SOME_annotate \\ fs []);

val chain_exps_no_Labels = store_thm("chain_exps_no_Labels",
  ``!es l. EVERY no_Labels es ==>
           EVERY no_Labels (MAP (SND ∘ SND) (chain_exps l es))``,
  Induct_on `es` \\ fs [clos_to_bvlTheory.chain_exps_def]
  \\ Cases_on `es` \\ fs [clos_to_bvlTheory.chain_exps_def]);

val chain_exps_obeys_max_app = store_thm("chain_exps_obeys_max_app",
  ``!es l. EVERY (obeys_max_app k) es ==>
           EVERY (obeys_max_app k) (MAP (SND ∘ SND) (chain_exps l es))``,
  Induct_on `es` \\ fs [clos_to_bvlTheory.chain_exps_def]
  \\ Cases_on `es` \\ fs [clos_to_bvlTheory.chain_exps_def]);

val chain_exps_every_Fn_SOME = store_thm("chain_exps_every_Fn_SOME",
  ``!es l. every_Fn_SOME es ==>
           every_Fn_SOME (MAP (SND ∘ SND) (chain_exps l es))``,
  Induct_on `es` \\ fs [clos_to_bvlTheory.chain_exps_def]
  \\ Cases_on `es` \\ fs [clos_to_bvlTheory.chain_exps_def]
  \\ rw [] \\ res_tac \\ fs []
  \\ once_rewrite_tac [closPropsTheory.every_Fn_SOME_APPEND
      |> Q.INST [`l1`|->`x::[]`] |> SIMP_RULE std_ss [APPEND]]
  \\ fs []);

val syntax_ok_IMP_obeys_max_app = store_thm("syntax_ok_IMP_obeys_max_app",
  ``!e3. 0 < m /\ clos_mtiProof$syntax_ok e3 ==> EVERY (obeys_max_app m) e3``,
  ho_match_mp_tac clos_mtiProofTheory.syntax_ok_ind \\ rpt strip_tac \\ fs []
  \\ pop_assum mp_tac \\ once_rewrite_tac [clos_mtiProofTheory.syntax_ok_def]
  \\ fs [] \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ rw [] \\ res_tac);

val compile_common_syntax = store_thm("compile_common_syntax",
  ``!cf e3 cf1 e4.
      clos_to_bvl$compile_common cf e3 = (cf1,e4) ==>
      (EVERY no_Labels e3 ==>
       EVERY no_Labels (MAP (SND o SND) e4)) /\
      (0 < cf.max_app /\ clos_mtiProof$syntax_ok e3 ==>
       EVERY (obeys_max_app cf.max_app) (MAP (SND o SND) e4)) /\
      every_Fn_SOME (MAP (SND o SND) e4)``,
  fs [clos_to_bvlTheory.compile_common_def]
  \\ rpt gen_tac \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq \\ fs [] \\ rw []
  THEN1 (* no_Labels *)
   (drule (clos_numberProofTheory.renumber_code_locs_no_Labels |> CONJUNCT1)
    \\ impl_tac THEN1
     (Cases_on `cf.do_mti` \\ fs [clos_mtiTheory.compile_def]
      \\ fs [clos_mtiProofTheory.intro_multi_no_Labels])
    \\ strip_tac
    \\ `EVERY no_Labels es'` by
      (Cases_on `cf.known_conf` THEN1 (fs [clos_knownTheory.compile_def] \\ rfs [])
       \\ drule clos_knownProofTheory.compile_no_Labels
       \\ fs [clos_knownTheory.compile_def] \\ rw [] \\ fs [])
    \\ Cases_on `cf.do_call` \\ fs [clos_callTheory.compile_def] \\ rveq \\ fs []
    \\ TRY pairarg_tac \\ fs [] \\ rveq
    \\ TRY (drule clos_callProofTheory.calls_no_Labels
            \\ (impl_tac THEN1 (fs [] \\ EVAL_TAC) \\ rw []))
    \\ match_mp_tac no_Labels_labs
    \\ match_mp_tac no_Labels_ann
    \\ fs [clos_callProofTheory.state_syntax_def]
    \\ rw [] \\ TRY (match_mp_tac chain_exps_no_Labels \\ fs [])
    \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
    \\ rw [] \\ res_tac \\ fs [])
  THEN1 (* obeys_max_app *)
   (drule (clos_numberProofTheory.renumber_code_locs_obeys_max_app
           |> CONJUNCT1 |> GEN_ALL)
    \\ disch_then (qspec_then `cf.max_app` mp_tac)
    \\ impl_tac THEN1
     (Cases_on `cf.do_mti` \\ fs [clos_mtiTheory.compile_def]
      \\ fs [clos_mtiProofTheory.intro_multi_obeys_max_app]
      \\ match_mp_tac syntax_ok_IMP_obeys_max_app \\ fs[])
    \\ strip_tac
    \\ `EVERY (obeys_max_app cf.max_app) es'` by
      (Cases_on `cf.known_conf` THEN1 (fs [clos_knownTheory.compile_def] \\ rfs [])
       \\ drule (GEN_ALL clos_knownProofTheory.compile_obeys_max_app)
       \\ disch_then (qspec_then `cf.max_app` mp_tac)
       \\ fs [clos_knownTheory.compile_def] \\ rw [] \\ fs [])
    \\ Cases_on `cf.do_call` \\ fs [clos_callTheory.compile_def] \\ rveq \\ fs []
    \\ TRY pairarg_tac \\ fs [] \\ rveq
    \\ TRY (drule (GEN_ALL clos_callProofTheory.calls_obeys_max_app)
            \\ disch_then (qspec_then `cf.max_app` mp_tac)
            \\ (impl_tac THEN1 (fs [] \\ EVAL_TAC) \\ rw []))
    \\ match_mp_tac obeys_max_app_labs
    \\ match_mp_tac obeys_max_app_ann
    \\ fs [clos_callProofTheory.state_syntax_def]
    \\ rw [] \\ TRY (match_mp_tac chain_exps_obeys_max_app \\ fs [])
    \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
    \\ rw [] \\ res_tac \\ fs [])
  \\ rename [`renumber_code_locs_list r1 r2`]
  \\ qspecl_then [`r1`,`r2`] mp_tac
      (clos_numberProofTheory.renumber_code_locs_every_Fn_SOME |> CONJUNCT1)
  \\ fs [] \\ strip_tac
  \\ rename [`_ cf.known_conf es = (kc4,es4)`]
  \\ rename [`_ = (r5,r6,r7)`]
  \\ `every_Fn_SOME es4` by
    (Cases_on `cf.known_conf` THEN1 (fs [clos_knownTheory.compile_def] \\ rfs [])
     \\ fs [clos_knownTheory.compile_def]
     \\ pairarg_tac \\ fs [] \\ rveq \\ fs []
     \\ qspecl_then [`x`,`clos_fvs$compile es`,`[]`,`LN`] mp_tac
           clos_knownProofTheory.known_every_Fn_SOME
     \\ fs [] \\ impl_tac THEN1
      (simp [clos_fvsTheory.compile_def,clos_fvsProofTheory.remove_fvs_every_Fn_SOME]
       \\ EVAL_TAC \\ fs [lookup_def])
     \\ strip_tac \\ fs [])
  \\ Cases_on `cf.do_call` \\ fs [clos_callTheory.compile_def] \\ rveq \\ fs []
  \\ TRY pairarg_tac \\ fs [] \\ rveq
  \\ TRY (drule clos_callProofTheory.calls_preserves_every_Fn_SOME
          \\ impl_tac THEN1 (fs [] \\ EVAL_TAC) \\ strip_tac \\ fs [])
  \\ match_mp_tac every_Fn_SOME_labs
  \\ match_mp_tac every_Fn_SOME_ann
  \\ fs [closPropsTheory.every_Fn_SOME_APPEND]
  \\ match_mp_tac chain_exps_every_Fn_SOME \\ fs []);

val var_list_code_labels_imp_TODO_move = Q.store_thm("var_list_code_labels_imp_TODO_move",
  `∀n x y. var_list n x y ⇒ BIGUNION (set (MAP clos_get_code_labels x)) = {} (*∧
                            BIGUNION (set (MAP bvl_get_code_labels y)) = {}*)`,
  recInduct clos_letopTheory.var_list_ind
  \\ rw[clos_letopTheory.var_list_def] \\ fs[]);

val let_op_get_code_labels = Q.store_thm("let_op_get_code_labels[simp]",
  `∀es. MAP clos_get_code_labels (let_op es) = MAP clos_get_code_labels es`,
  recInduct clos_letopTheory.let_op_ind
  \\ rw[clos_letopTheory.let_op_def] \\ fs[]
  >- (
    PURE_TOP_CASE_TAC \\ fs[]
    \\ qmatch_assum_rename_tac`dest_op op _ = _`
    \\ Cases_on`op` \\ fs[clos_letopTheory.dest_op_def] \\ rveq
    \\ imp_res_tac var_list_code_labels_imp_TODO_move \\ fs[])
  \\ fs[MAP_MAP_o, UNCURRY, o_DEF]
  \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ simp[MAP_EQ_f, FORALL_PROD] \\ rw[]
  \\ res_tac \\ fs[]);

val remove_ticks_code_labels = Q.store_thm("remove_ticks_code_labels[simp]",
  `∀es. MAP clos_get_code_labels (remove_ticks es) = MAP clos_get_code_labels es`,
  recInduct clos_ticksTheory.remove_ticks_ind
  \\ rw[clos_ticksTheory.remove_ticks_def] \\ fs[]
  \\ fs[MAP_MAP_o, UNCURRY, o_DEF]
  \\ AP_TERM_TAC \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ simp[MAP_EQ_f, FORALL_PROD] \\ rw[]
  \\ res_tac \\ fs[]);

val val_approx_labels_def = tDefine"val_approx_labels"`
  val_approx_labels (ClosNoInline loc _) = {loc} ∧
  val_approx_labels (Clos loc _ body _) = loc INSERT (clos_get_code_labels body) ∧
  val_approx_labels (Tuple _ ls) = BIGUNION (set (MAP val_approx_labels ls)) ∧
  val_approx_labels _ = {}`
 (wf_rel_tac`measure val_approx_size`
  \\ gen_tac \\ Induct \\ rw[clos_knownTheory.val_approx_size_def]
  \\ res_tac \\ rw[]);

val val_approx_labels_merge = Q.store_thm("val_approx_labels_merge",
  `∀x y. val_approx_labels (merge x y) ⊆ val_approx_labels x ∪ val_approx_labels y`,
  recInduct clos_knownTheory.merge_ind
  \\ rw[clos_knownTheory.merge_def, val_approx_labels_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_MAP, MAP2_MAP, FORALL_PROD, MEM_ZIP]
  \\ rw[] \\ fs[MEM_EL, PULL_EXISTS]
  \\ metis_tac[]);

val clos_get_code_labels_mk_Ticks = Q.store_thm("clos_get_code_labels_mk_Ticks[simp]",
  `∀a b c d. clos_get_code_labels (mk_Ticks a b c d) = clos_get_code_labels d`,
  recInduct clos_knownTheory.mk_Ticks_ind
  \\ rw[]
  \\ rw[Once clos_knownTheory.mk_Ticks_def]);

val clos_get_code_labels_remove_fvs = Q.store_thm("clos_get_code_labels_remove_fvs[simp]",
  `∀n es. MAP clos_get_code_labels (remove_fvs n es) = MAP clos_get_code_labels es`,
  recInduct clos_fvsTheory.remove_fvs_ind
  \\ rw[clos_fvsTheory.remove_fvs_def] \\ fs[assign_get_code_label_def]
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ simp[MAP_MAP_o, MAP_EQ_f, FORALL_PROD]
  \\ rw[]
  \\ first_x_assum drule
  \\ rw[] \\ fs[]);

val renumber_code_locs_imp_EVEN = Q.store_thm("renumber_code_locs_imp_EVEN",
  `(renumber_code_locs_list n es = (n',es') ∧ EVEN n ⇒ EVEN n') ∧
   (renumber_code_locs n e = (n',e') ∧ EVEN n ⇒ EVEN n')`,
  rw[]
  \\ strip_assume_tac(SPEC_ALL (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_EVEN)) \\ rfs[]
  \\ strip_assume_tac(SPEC_ALL (CONJUNCT2 clos_numberProofTheory.renumber_code_locs_EVEN)) \\ rfs[]);

val renumber_code_locs_clos_get_code_labels = Q.store_thm("renumber_code_locs_clos_get_code_labels",
  `(∀n es n' es'. renumber_code_locs_list n es = (n',es') ∧ EVERY ((=){}) (MAP clos_get_code_labels es) ∧ EVEN n ⇒
      BIGUNION (set (MAP clos_get_code_labels es')) = { n + 2 * k | k | n + 2 * k < n' }) ∧
   (∀n e n' e'. renumber_code_locs n e = (n',e') ∧ clos_get_code_labels e = {} ∧ EVEN n ⇒
     clos_get_code_labels e' = { n + 2 * k | k | n + 2 * k < n' })`,
  ho_match_mp_tac clos_numberTheory.renumber_code_locs_ind
  \\ rw[clos_numberTheory.renumber_code_locs_def]
  \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
  \\ imp_res_tac clos_numberProofTheory.renumber_code_locs_imp_inc
  \\ imp_res_tac renumber_code_locs_imp_EVEN \\ fs[]
  >- (
    rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ qpat_x_assum`EVEN _`mp_tac
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[]
      \\ qpat_x_assum`EVEN n`mp_tac
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ))
  >- (
    rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      `EVEN (n'''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[] \\ rw[] \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ Cases_on`p' + p'' ≤ k` \\ fs[]
      >- ( qexists_tac`k - p' - p''` \\ simp[] )
      \\ qexists_tac`k - p''`
      \\ simp[] ) )
  >- (
    rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rw[] \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ) )
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- fs[EVERY_MEM]
    \\ rw[]
    \\ rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rw[] \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ) )
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- fs[EVERY_MEM]
    \\ rw[] )
  >- fs[clos_numberTheory.renumber_code_locs_def]
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- fs[EVERY_MEM]
    \\ rw[]
    \\ rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k` \\ simp[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rw[] \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] ) )
  >- (
    reverse(rw[EXTENSION, EQ_IMP_THM])
    >- (
      Cases_on`2 * k + n = n''` \\ fs[]
      \\ rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ rw[EVEN_EXISTS] \\ fs[]
      \\ fs[GSYM LEFT_ADD_DISTRIB] )
    >- ( qexists_tac`k` \\ fs[] )
    >- (
      rpt(qpat_x_assum`EVEN _`mp_tac)
      \\ rw[EVEN_EXISTS] \\ fs[]
      \\ fs[GSYM LEFT_ADD_DISTRIB]
      \\ qexists_tac`m'-m`
      \\ simp[] ) )
  >- (
    imp_res_tac clos_numberProofTheory.renumber_code_locs_list_IMP_LENGTH
    \\ fs[] \\ rveq \\ rfs[]
    \\ qpat_x_assum`{} = _`(assume_tac o SYM) \\ fs[]
    \\ rpt(qpat_x_assum`EVEN _`mp_tac)
    \\ rw[EVEN_EXISTS] \\ fs[]
    \\ rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k + m'' - m'` \\ simp[] )
    \\ fs[EXTENSION]
    \\ fs[LESS_EQ_EXISTS] \\ rveq
    \\ qexists_tac`k-p`
    \\ simp[LEFT_ADD_DISTRIB]
    \\ fs[LEFT_ADD_DISTRIB]
    \\ fs[clos_numberTheory.renumber_code_locs_def] )
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- (
      fs[EVERY_MEM]
      \\ fs[EVEN_ADD]
      \\ fs[EVEN_EXISTS] )
    \\ rw[]
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- (
      fs[EVERY_MEM]
      \\ fs[EXTENSION, MEM_MAP, PULL_EXISTS] )
    \\ rw[]
    \\ imp_res_tac clos_numberProofTheory.renumber_code_locs_list_IMP_LENGTH \\ fs[]
    \\ simp[MAP_ZIP]
    \\ qpat_x_assum`_ ⇒ _`mp_tac
    \\ impl_tac >- (
      fs[EVERY_MEM]
      \\ fs[EVEN_ADD]
      \\ fs[EVEN_EXISTS] )
    \\ rw[]
    \\ rpt(qpat_x_assum`EVEN _`mp_tac)
    \\ rw[EVEN_EXISTS] \\ fs[]
    \\ fs[LESS_EQ_EXISTS] \\ rveq
    \\ rw[EXTENSION, EQ_IMP_THM]
    >- ( qexists_tac`k+p` \\ simp[LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB] )
    >- ( qexists_tac`k + LENGTH fns + p` \\ simp[LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB] )
    >- ( qexists_tac`k` \\ simp[LEFT_ADD_DISTRIB, LEFT_SUB_DISTRIB] )
    \\ fs[]
    \\ Cases_on`k < p` \\ fs[]
    \\ fs[LEFT_ADD_DISTRIB]
    \\ Cases_on`k - p < LENGTH fns` \\ fs[]
    >- ( qexists_tac`k-p` \\ simp[] )
    >- ( qexists_tac`k - p - LENGTH fns` \\ fs[] )
    >- ( qexists_tac`k - p` \\ fs[] ) )
  >- (
    rw[EQ_IMP_THM, EXTENSION]
    >- ( qexists_tac`k` \\ fs[] )
    >- (
      `EVEN (n''-n)` by simp[EVEN_SUB]
      \\ pop_assum mp_tac \\ simp[EVEN_EXISTS] \\ strip_tac
      \\ qexists_tac`k + m`
      \\ simp[] )
    >- (
      Cases_on`2 * k + n < n''` \\ fs[]
      \\ qpat_x_assum`EVEN _`mp_tac
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[]
      \\ qpat_x_assum`EVEN n`mp_tac
      \\ simp[EVEN_EXISTS] \\ strip_tac \\ rveq \\ fs[]
      \\ fs[LESS_EQ_EXISTS] \\ rveq
      \\ qexists_tac`k-p`
      \\ simp[] )));

val EVEN_make_even = Q.store_thm("EVEN_make_even[simp]",
  `EVEN (make_even x)`,
  rw[make_even_def, EVEN_ADD]);

val call_dests_chain_exps = store_thm("call_dests_chain_exps",
  ``!xs n. any_dests (MAP (SND ∘ SND) (chain_exps n xs)) =
           any_dests xs UNION set (MAP ($+ (n + 1)) (COUNT_LIST (LENGTH xs - 1)))``,
  Induct \\ fs [clos_to_bvlTheory.chain_exps_def]
  THEN1 EVAL_TAC
  \\ Cases_on `xs` \\ fs [clos_to_bvlTheory.chain_exps_def]
  \\ once_rewrite_tac [closPropsTheory.app_call_dests_cons]
  \\ simp []
  \\ once_rewrite_tac [closPropsTheory.app_call_dests_cons]
  \\ simp [] \\ rw[]
  \\ qsuff_tac `MAP ($+ (n + 1)) (COUNT_LIST (SUC (LENGTH t))) =
      n+1 :: MAP ($+ (n + 2)) (COUNT_LIST (LENGTH t))`
  THEN1
   (fs [AC UNION_COMM UNION_ASSOC]
    \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs [])
  \\ pop_assum kall_tac
  \\ fs [COUNT_LIST_def]
  \\ fs [MAP_MAP_o,o_DEF,ADD1,MAP_EQ_f]);

val renumber_code_locs_any_dests = store_thm("renumber_code_locs_any_dests",
  ``(!k xs n ys. renumber_code_locs_list k xs = (n,ys) ==> any_dests ys = ∅) /\
    (!k x n y. renumber_code_locs k x = (n,y) ==> any_dests [y] = ∅)``,
  ho_match_mp_tac clos_numberTheory.renumber_code_locs_ind \\ rpt strip_tac
  \\ fs [clos_numberTheory.renumber_code_locs_def] \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ once_rewrite_tac [closPropsTheory.app_call_dests_cons] \\ fs []
  \\ `LENGTH fns = LENGTH fns'` by
       metis_tac [clos_numberTheory.renumber_code_locs_length,LENGTH_MAP,SND]
  \\ fs [MAP_ZIP]);

val BIGUNION_MAP_code_locs_SND_SND = store_thm("BIGUNION_MAP_code_locs_SND_SND",
  ``BIGUNION (set (MAP (set ∘ code_locs ∘ (λx. [SND (SND x)])) xs)) =
    set (code_locs (MAP (SND o SND) xs))``,
  Induct_on `xs` \\ fs [closPropsTheory.code_locs_def]
  \\ once_rewrite_tac [closPropsTheory.code_locs_cons]
  \\ fs [closPropsTheory.code_locs_def]);

val compile_common_code_locs = store_thm("compile_common_code_locs",
  ``!c es c1 xs.
      clos_to_bvl$compile_common c (MAP pat_to_clos_compile es) = (c1,xs) ==>
      BIGUNION (set (MAP clos_get_code_labels (MAP (SND ∘ SND) xs))) ⊆
      set (MAP FST xs) ∪ set (code_locs (MAP (SND ∘ SND) xs))``,
  rpt strip_tac
  \\ drule compile_common_syntax
  \\ fs [EVERY_MAP,compile_no_Labels]
  \\ strip_tac
  \\ qpat_x_assum `_ ==> _` kall_tac
  \\ fs [clos_to_bvlTheory.compile_common_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ fs [clos_to_bvlProofTheory.MAP_FST_chain_exps_any]
  \\ qmatch_goalsub_abbrev_tac `clos_annotate$compile ls`
  \\ simp[closPropsTheory.code_locs_map, LIST_TO_SET_FLAT, MAP_MAP_o, o_DEF,
          LIST_TO_SET_MAP, GSYM IMAGE_COMPOSE]
  \\ simp[GSYM LIST_TO_SET_MAP]
  \\ fs[clos_annotateTheory.compile_def,MAP_MAP_o,UNCURRY,o_DEF]
  \\ simp[GSYM o_DEF]
  \\ simp[Once(GSYM MAP_MAP_o)]
  \\ DEP_REWRITE_TAC[clos_get_code_labels_code_locs]
  \\ conj_tac THEN1
   (fs [o_DEF] \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ rw[] \\ res_tac \\ fs [])
  \\ simp[]
  \\ conj_tac >- (
        simp[SUBSET_DEF, o_DEF, closPropsTheory.code_locs_map, MEM_FLAT,
             MEM_MAP, PULL_EXISTS] \\ metis_tac[] )
  \\ rename [`clos_labels$compile input`]
  \\ fs [BIGUNION_MAP_code_locs_SND_SND]
  \\ metis_tac [clos_labelsProofTheory.compile_any_dests_SUBSET_code_locs]);

val compile_correct = Q.store_thm("compile_correct",
  `compile (c:'a config) prog = SOME (bytes,bitmaps,c') ⇒
   let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   ¬semantics_prog s env prog Fail ∧
   backend_config_ok c ∧ mc_conf_ok mc ∧ mc_init_ok c mc ∧
   installed bytes cbspace bitmaps data_sp c'.ffi_names ffi (heap_regs c.stack_conf.reg_names) mc ms ⇒
     machine_sem (mc:(α,β,γ) machine_config) ffi ms ⊆
       extend_with_resource_limit (semantics_prog s env prog)`,

  srw_tac[][compile_eq_from_source,from_source_def,backend_config_ok_def,heap_regs_def] >>
  `c.lab_conf.asm_conf = mc.target.config` by fs[mc_init_ok_def] >>
  `c'.ffi_names = SOME mc.ffi_names` by fs[installed_def] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP source_to_flatProofTheory.compile_semantics)) >>
  fs[primSemEnvTheory.prim_sem_env_eq] >>
  qpat_x_assum`_ = s`(assume_tac o Abbrev_intro o SYM) >>
  qpat_x_assum`_ = env`(assume_tac o Abbrev_intro o SYM) >>
  `precondition s env c.source_conf` by (
    simp[source_to_flatProofTheory.precondition_def] >>
    simp[Abbr`env`,Abbr`s`] >>
    srw_tac[QUANT_INST_ss[pair_default_qp,record_default_qp]][] >>
    rw[source_to_flatProofTheory.invariant_def] >>
    rw[source_to_flatProofTheory.genv_c_ok_def] >>
    rw[source_to_flatProofTheory.s_rel_cases] >>
    rw[flatSemTheory.initial_state_def] >>
    rw[prim_config_eq] >>
    rw[Once source_to_flatProofTheory.v_rel_cases] >>
    rw[nsLookup_Bind_v_some,PULL_EXISTS] \\
    (fn g as (asl,w) =>
      let
        val (genv_c,tm) = dest_exists w
        val tm = tm |> strip_conj |> el 10 |> strip_forall |> #2
        val (tms1, tm) = dest_imp tm
        val tms2 = tm |> dest_exists |> #2 |> strip_conj |> el 1
        fun get_data (tm,acc) =
          let
            val (eq, data, rest) = dest_cond tm
          in
            get_data (rest, (lhs eq, subst[rhs eq |-> lhs eq](optionSyntax.dest_some data))::acc)
          end handle HOL_ERR _ => acc
        val d1 = get_data (lhs tms1,[])
        val d2 = get_data (lhs tms2,[])
        fun get_pair (k,cn) =
          let
            val (arity, stamp) = pairSyntax.dest_pair (assoc k d1)
          in
            pairSyntax.mk_pair(pairSyntax.mk_pair(cn, arity), stamp)
          end
        val al = map get_pair d2
      in
        exists_tac (
          finite_mapSyntax.list_mk_fupdate(
            finite_mapSyntax.mk_fempty(finite_mapSyntax.dest_fmap_ty (type_of genv_c)),
            al)
        )
      end g)
    \\ simp[IN_FRANGE, DOMSUB_FAPPLY_THM]
    \\ EVAL_TAC \\ rw[] \\ EVAL_TAC
    \\ CCONTR_TAC \\ fs[] \\ rw[] \\ fs[])
  \\ disch_then drule >> strip_tac >>
  pairarg_tac \\ fs[] >>
  qhdtm_x_assum`from_flat`mp_tac >>
  srw_tac[][from_flat_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_assum_abbrev_tac`semantics_prog s env prog sem2` >>
  `sem2 ≠ Fail` by metis_tac[] >>
  `semantics_prog s env prog = { sem2 }` by (
    simp[EXTENSION,IN_DEF] >>
    metis_tac[semantics_prog_deterministic] ) >>
  qunabbrev_tac`sem2` >>

  qabbrev_tac`TODO_co1 = ARB ** 0 - SUC ZERO` >>

  (flat_to_patProofTheory.compile_semantics
   |> Q.GEN`cc`
   |> (
     ``
     pure_cc (λes. (MAP pat_to_clos$compile es, [])) (
      compile_common_inc (c:'a config).clos_conf
         (pure_cc (compile_inc c.clos_conf.max_app)
           (full_cc c.bvl_conf (pure_cc bvi_to_data_compile_prog
             (λcfg. OPTION_MAP (I ## MAP upper_w2w ## I) o
                    (λprogs.
                      (λ(bm0,cfg) progs.
                        (λ(progs,bm).
                          OPTION_MAP
                            (λ(bytes,cfg).
                              (bytes, DROP (LENGTH bm0) bm,bm,cfg))
                            (compile cfg
                              (MAP prog_to_section
                                (MAP
                                  (prog_comp c.stack_conf.reg_names)
                                  (MAP
                                    (prog_comp c.stack_conf.jump
                                      c.lab_conf.asm_conf.addr_offset
                                      (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3)))
                                    (MAP prog_comp progs))))))
                         (compile_word_to_stack ((c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3))-2) progs bm0)) cfg (MAP (λp. full_compile_single mc.target.config.two_reg_arith (mc.target.config.reg_count - (LENGTH mc.target.config.avoid_regs + 5)) aa (mc:('a,'b,'c)machine_config).target.config (p,NONE)) progs)) o MAP (compile_part (c.data_conf with has_fp_ops := (1 < mc.target.config.fp_reg_count))))))))``
     |> ISPEC)
   |> Q.GEN`co`
   |> Q.GEN`k0`
   |>  drule)
  \\ disch_then(
       qspecl_then[`TODO_clock`,
                   `K ((TODO_co1,
                        (
                          (case
                            (FST(compile c.clos_conf.known_conf (SND (renumber_code_locs_list (make_even (LENGTH (compile p) + c.clos_conf.next_loc)) (compile c.clos_conf.do_mti c.clos_conf.max_app (MAP compile (compile p)))))))
                          of NONE => LN | SOME x => x.val_approx_spt)
                        ,
                         (FST(SND(compile T (SND(compile c.clos_conf.known_conf (SND (renumber_code_locs_list (make_even (LENGTH (compile p) + c.clos_conf.next_loc)) (compile c.clos_conf.do_mti c.clos_conf.max_app (MAP compile (compile p))))))))),
                          FST(SND(SND(compile (FST(compile c.clos_conf (MAP compile (compile p)))).start c.bvl_conf (SND(compile c.clos_conf (MAP compile (compile p))))))),
                          FST(SND(SND(SND(compile (FST(compile c.clos_conf (MAP compile (compile p)))).start c.bvl_conf (SND(compile c.clos_conf (MAP compile (compile p)))))))),
                          SND(SND(SND(SND(compile (FST(compile c.clos_conf (MAP compile (compile p)))).start c.bvl_conf (SND(compile c.clos_conf (MAP compile (compile p)))))))),
                           let e3 = MAP compile (compile (SND (compile (prim_config:'a config).source_conf prog))) in
                           let stk = c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3) in
                           let stoff = c.lab_conf.asm_conf.addr_offset in
                           let p1 = SND (compile c.clos_conf e3) in
                           let p2 = SND (bvl_inline$compile_prog c.bvl_conf.inline_size_limit c.bvl_conf.split_main_at_seq c.bvl_conf.exp_cut p1) in
                           let strt = (FST (compile c.clos_conf e3)).start in
                           let code = FST(SND(bvl_to_bvi$compile_prog strt 0 p2)) in
                           let p3 = SND (bvi_tailrec$compile_prog (bvl_num_stubs + 2) code) in
                           let p4 = bvi_to_data$compile_prog p3 in
                           let c4_data_conf = c.data_conf with has_fp_ops := (1 < c.lab_conf.asm_conf.fp_reg_count) in
                           let t_code = stubs (:'a) c4_data_conf ++ MAP (compile_part c4_data_conf) p4 in
                           let p5 = SND (compile c.word_to_word_conf c.lab_conf.asm_conf t_code) in
                           let p6 = SND (compile c.lab_conf.asm_conf p5) in
                           let p7 = compile c.stack_conf c.data_conf (2 * max_heap_limit (:'a) c.data_conf - 1) stk stoff p6 in
                          ((FST(compile c.lab_conf.asm_conf p5)).bitmaps,
                           (
                           <|labels := (SND(THE(compile c.lab_conf p7))).labels;
                             pos := LENGTH (FST(THE(compile c.lab_conf p7)));
                             asm_conf := mc.target.config;
                             ffi_names := SOME mc.ffi_names|>)
                             )
                             ))),
                           [])`]
     (strip_assume_tac o SYM)) >>
  fs[] >>
  qhdtm_x_assum`from_pat`mp_tac >>
  srw_tac[][from_pat_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { patSem$semantics [] (st4 (pure_cc pc cc3) st3) es3 }` >>
  (pat_to_closProofTheory.compile_semantics
   |> Q.GENL[`cc`,`st`,`es`,`max_app`]
   |> qispl_then[`cc3`,`st4 (pure_cc pc cc3) st3`,`es3`]mp_tac) >>
  simp[Abbr`es3`] >>
  disch_then drule >>
  impl_tac >- (
    fs[Abbr`st3`, flat_to_patProofTheory.compile_state_def, Abbr`st4`]
    \\ EVAL_TAC ) >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_clos`mp_tac >>
  srw_tac[][from_clos_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qunabbrev_tac`st4` >>
  simp[flat_to_patProofTheory.compile_state_def] >>
  simp[Abbr`st3`,flatSemTheory.initial_state_def] >>
  qmatch_abbrev_tac`_ ⊆ _ { closSem$semantics _ _ _ co3 cc3 e3 }` >>
  qmatch_asmsub_abbrev_tac`compile_common_inc cf (pure_cc (compile_inc _) cc)`
  \\ qmatch_asmsub_abbrev_tac`(TODO_co1, (coa,cob,__))`
  \\ Q.ISPECL_THEN[`co3`,`cc`,`e3`,`ffi`,`cf`]mp_tac
       (Q.GENL[`co`,`cc`,`es`,`ffi`,`c`,`c'`,`prog`]clos_to_bvlProofTheory.compile_semantics)
  \\ simp[]
  \\ impl_keep_tac
  >- (
    conj_tac
    >- (
      fs[flat_to_patProofTheory.compile_state_def,
         flatSemTheory.initial_state_def,Abbr`s`] )
    \\ simp[Abbr`cf`,Abbr`co3`,Abbr`pc`]
    \\ simp[syntax_oracle_ok_def]
    \\ `clos_mtiProof$syntax_ok e3`
    by (
      simp[Abbr`e3`, Abbr`p''`]
      \\ match_mp_tac clos_mtiProofTheory.syntax_ok_MAP
      \\ rw [syntax_ok_pat_to_clos] )
    \\ conj_tac
    >- ( simp[Abbr`e3`, Abbr`p''`] \\ strip_tac \\ EVAL_TAC)
    \\ conj_tac
    >- (
      strip_tac
      \\ simp[Abbr`e3`, Abbr`p''`, Abbr`p'`]
      \\ fs[IS_SOME_EXISTS]
      \\ simp[Abbr`coa`]
      \\ CASE_TAC \\ fs[]
      \\ fs[clos_knownTheory.compile_def, UNCURRY])
    \\ conj_tac
    >- ( strip_tac \\ simp[Abbr`e3`, Abbr`p''`, Abbr`p'`] )
    \\ `EVERY esgc_free e3`
    by (
      simp[Abbr`e3`, Abbr`p''`]
      \\ simp[EVERY_MAP]
      \\ simp[EVERY_MEM] \\ rw[]
      \\ irule pat_to_closProofTheory.compile_esgc_free
      \\ fs[Abbr`p'`]
      \\ pop_assum mp_tac
      \\ qid_spec_tac`x`
      \\ simp[GSYM EVERY_MEM]
      \\ irule compile_esgc_free
      \\ simp[EVERY_o]
      \\ irule source_to_flatProofTheory.compile_esgc_free
      \\ asm_exists_tac \\ rw[]
      \\ EVAL_TAC
      \\ Cases \\ simp[namespaceTheory.nsLookup_def])
    \\ conj_tac
    >- (
      gen_tac
      \\ qhdtm_x_assum`clos_to_bvl$compile`mp_tac
      \\ simp[clos_to_bvlTheory.compile_def, clos_to_bvlTheory.compile_common_def]
      \\ qmatch_goalsub_abbrev_tac`renumber_code_locs_list nn`
      \\ qmatch_asmsub_abbrev_tac`renumber_code_locs_list nn1`
      \\ `nn = nn1`
      by (
        simp[Abbr`nn`,Abbr`nn1`,Abbr`e3`,Abbr`p''`]
        \\ rw[make_even_def, EVEN_MOD2] )
      \\ fs[Abbr`nn`]
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[]
      \\ pairarg_tac \\ fs[]
      \\ strip_tac \\ fs[Abbr`nn1`]
      \\ rveq
      \\ `BAG_ALL_DISTINCT (elist_globals e3)`
      by (
        simp[Abbr`e3`,Abbr`p''`,Abbr`p'`]
        \\ simp[closPropsTheory.elist_globals_FOLDR]
        \\ simp[BAG_ALL_DISTINCT_FOLDR_BAG_UNION]
        \\ simp[EL_MAP]
        \\ simp[GSYM pat_to_closProofTheory.set_globals_eq]
        \\ CONV_TAC(REWR_CONV(GSYM(SIMP_RULE(srw_ss()++ARITH_ss)[EL_MAP](
                  Q.ISPEC`MAP set_globals (flat_to_pat$compile p)`BAG_ALL_DISTINCT_FOLDR_BAG_UNION
                  |> Q.SPEC`{||}`))))
        \\ simp[GSYM patPropsTheory.elist_globals_FOLDR]
        \\ irule BAG_ALL_DISTINCT_SUB_BAG
        \\ qspec_then`p`mp_tac elist_globals_compile
        \\ strip_tac
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ qpat_x_assum`_ = (_,p)`assume_tac
        \\ fs[source_to_flatTheory.compile_def]
        \\ pairarg_tac \\ fs[] \\ rveq
        \\ simp[source_to_flatTheory.compile_flat_def]
        \\ simp[flat_exh_matchTheory.compile_def]
        \\ irule flat_reorder_matchProofTheory.compile_decs_distinct_globals
        \\ irule flat_uncheck_ctorsProofTheory.compile_decs_distinct_globals
        \\ irule flat_elimProofTheory.remove_flat_prog_distinct_globals
        \\ irule flat_exh_matchProofTheory.compile_exps_distinct_globals
        \\ fs[source_to_flatTheory.compile_prog_def]
        \\ pairarg_tac \\ fs[] \\ rveq
        \\ simp[source_to_flatTheory.glob_alloc_def]
        \\ simp[flatPropsTheory.op_gbag_def]
        \\ drule compile_decs_elist_globals
        \\ impl_tac >- (
          EVAL_TAC \\ Cases \\ simp[namespaceTheory.nsLookup_def] )
        \\ rw[]
        \\ simp[bag_of_list_ALL_DISTINCT]
        \\ irule ALL_DISTINCT_MAP_INJ
        \\ simp[]
        \\ simp[all_distinct_count_list])
      \\ Cases_on`kc` \\ fs[]
      >- (
        simp[Abbr`coa`]
        \\ conj_tac >- (EVAL_TAC \\ rw[lookup_def])
        \\ conj_tac >- (EVAL_TAC
             \\ simp[GSYM REPLICATE_GENLIST]
             \\ simp[FLAT_REPLICATE_NIL] )
        \\ conj_tac >- EVAL_TAC
        \\ conj_tac >- (EVAL_TAC \\ rw[])
        \\ EVAL_TAC \\ rw[lookup_def] )
      \\ simp[Abbr`coa`]
      \\ Cases_on`c.clos_conf.known_conf` \\ fs[clos_knownTheory.compile_def]
      \\ pairarg_tac \\ fs[]
      \\ drule clos_knownProofTheory.known_preserves_esgc_free
      \\ impl_keep_tac
      >- (
        fs[] \\ rveq \\ rfs[]
        \\ reverse conj_tac >- (EVAL_TAC \\ rw[lookup_def])
        \\ simp[clos_fvsTheory.compile_def]
        \\ irule (CONJUNCT1 clos_numberProofTheory.renumber_code_locs_esgc_free)
        \\ asm_exists_tac \\ simp[]
        \\ Cases_on`c.clos_conf.do_mti` \\ simp[clos_mtiTheory.compile_def]
        \\ irule clos_mtiProofTheory.intro_multi_preserves_esgc_free
        \\ simp[] )
      \\ strip_tac \\ fs[] \\ rfs[] \\ rveq \\ fs[]
      \\ conj_tac
      >- (
        EVAL_TAC
        \\ simp[GSYM REPLICATE_GENLIST]
        \\ simp[FLAT_REPLICATE_NIL] )
      \\ conj_tac >- EVAL_TAC
      \\ conj_tac >- ( EVAL_TAC \\ rw[] )
      \\ conj_tac >- (
        qmatch_asmsub_abbrev_tac`known aaa bbb ccc ddd`
        \\ qspecl_then[`aaa`,`bbb`,`ccc`,`ddd`]mp_tac clos_knownProofTheory.known_every_Fn_vs_NONE
        \\ unabbrev_all_tac \\ simp[clos_fvsTheory.compile_def]
        \\ impl_tac
        >- (
          reverse conj_tac >- (EVAL_TAC \\ rw[lookup_def])
          \\ qmatch_asmsub_abbrev_tac`renumber_code_locs_list nn xx`
          \\ qspecl_then[`nn`,`xx`]mp_tac(CONJUNCT1 clos_numberProofTheory.renumber_code_locs_every_Fn_vs_NONE)
          \\ simp[]
          \\ rw[Abbr`xx`]
          \\ simp[Once closPropsTheory.every_Fn_vs_NONE_EVERY]
          \\ simp[EVERY_MAP]
          \\ simp[pat_to_closProofTheory.compile_every_Fn_vs_NONE] )
        \\ simp[] )
      \\ qmatch_asmsub_abbrev_tac`known aaa bbb ccc ddd`
      \\ qspecl_then[`aaa`,`bbb`,`ccc`,`ddd`]mp_tac clos_knownProofTheory.known_every_Fn_SOME
      \\ unabbrev_all_tac \\ simp[clos_fvsTheory.compile_def]
      \\ impl_tac
      >- (
        reverse conj_tac >- (EVAL_TAC \\ rw[lookup_def])
        \\ qmatch_asmsub_abbrev_tac`renumber_code_locs_list nn xx`
        \\ qspecl_then[`nn`,`xx`]mp_tac(CONJUNCT1 clos_numberProofTheory.renumber_code_locs_every_Fn_SOME)
        \\ simp[])
      \\ simp[])
    \\ conj_asm1_tac
    >- (
      simp[Abbr`e3`, Abbr`p''`]
      \\ simp[Once closPropsTheory.contains_App_SOME_EXISTS]
      \\ simp[EVERY_MAP]
      \\ simp[pat_to_closProofTheory.compile_contains_App_SOME] )
    \\ simp[clos_knownProofTheory.syntax_ok_def]
    \\ simp[Abbr`e3`,Abbr`p''`]
    \\ simp[Once closPropsTheory.every_Fn_vs_NONE_EVERY]
    \\ simp[EVERY_MAP]
    \\ simp[pat_to_closProofTheory.compile_every_Fn_vs_NONE])
  \\ disch_then(strip_assume_tac o SYM) \\ fs[] \\
  qhdtm_x_assum`from_bvl`mp_tac >>
  simp[from_bvl_def] >>
  pairarg_tac \\ fs[] \\ strip_tac \\
  fs[from_bvi_def] \\
  `s.ffi = ffi` by simp[Abbr`s`] \\ pop_assum SUBST_ALL_TAC \\ fs[] \\
  qmatch_goalsub_abbrev_tac`semantics _ _ co cc`
  \\ Q.ISPEC_THEN`co`(drule o GEN_ALL) (Q.GEN`co`bvl_to_bviProofTheory.compile_semantics)
  \\ disch_then(qspec_then`ffi`mp_tac)
  \\ qunabbrev_tac`cc`
  \\ qmatch_goalsub_abbrev_tac`semantics _ _ co (full_cc _ cc) _`
  \\ disch_then(qspecl_then[`co`,`cc`]mp_tac)
  \\ fs[Abbr`c''''`]
  \\ impl_tac
  >- (
    conj_tac
    >- (
      simp[Abbr`co`, backendPropsTheory.FST_state_co, FST_known_co]
      \\ simp[Abbr`co3`] \\ rw[] )
    \\ conj_tac >- (
      simp[Abbr`co`, backendPropsTheory.FST_state_co, FST_known_co]
      \\ rw[Abbr`co3`] )
    \\ conj_tac >- (
      simp[Abbr`co`, backendPropsTheory.FST_state_co, FST_known_co]
      \\ rw[Abbr`co3`] )
    \\ conj_tac
    >- (
      simp[Abbr`co`, backendPropsTheory.SND_state_co, FST_known_co,
           backendPropsTheory.FST_state_co ]
      \\ gen_tac
      \\ conj_tac
      >- (
        simp[Abbr`co3`]
        \\ simp[clos_knownProofTheory.known_co_def]
        \\ Cases_on`cf.known_conf`
        \\ rw[backendPropsTheory.SND_state_co,Abbr`pc`]
        \\ EVAL_TAC \\ simp[UNCURRY] \\ EVAL_TAC )
      \\ conj_tac
      >- (
        simp[Abbr`co3`]
        \\ `bvl_num_stubs ≤ n2` suffices_by rw[]
        \\ fs[bvl_to_bviTheory.compile_def]
        \\ rpt(pairarg_tac \\ fs[])
        \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
        \\ rveq \\ rw[])
      >- (
        simp[Abbr`co3`]
        \\ `in_ns 2 n2` suffices_by rw[]
        \\ fs[bvl_to_bviTheory.compile_def]
        \\ rpt(pairarg_tac \\ fs[])
        \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
        \\ rw[]
        \\ simp[bvl_to_bviProofTheory.mult_nss_in_ns_2] ))
    \\ (
      qpat_x_assum`_ = (_,p''')`mp_tac
      \\ MATCH_ACCEPT_TAC clos_to_bvlProofTheory.compile_all_distinct_locs))
  \\ disch_then(strip_assume_tac o SYM) \\ fs[] \\
  qunabbrev_tac`cc`

  \\ (bvi_to_dataProofTheory.compile_prog_semantics
      |> SIMP_RULE std_ss [GSYM backendPropsTheory.pure_cc_def |> SIMP_RULE std_ss [LET_THM]]
      |> drule)
  \\ disch_then(strip_assume_tac o SYM) \\ fs[] \\
  qmatch_assum_abbrev_tac `from_data c4 p4 = _` \\
  qhdtm_x_assum`from_data`mp_tac
  \\ simp[from_data_def]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac
  \\ rename1`compile _ _ _ p4 = (col,p5)` \\
  qhdtm_x_assum`from_word`mp_tac \\
  simp[from_word_def] \\ pairarg_tac \\ fs[] \\ strip_tac \\
  qmatch_assum_rename_tac`compile _ p5 = (c6,p6)` \\
  fs[from_stack_def,from_lab_def] \\
  qmatch_assum_abbrev_tac`_ _ (compile c4.lab_conf p7) = SOME (bytes,_,c')`
  \\ `compile c4.lab_conf p7 = SOME (bytes,c')`
  by (
    Cases_on`compile c4.lab_conf p7` \\ fs[attach_bitmaps_def] \\
    Cases_on`x` \\ fs[attach_bitmaps_def] ) \\
  fs[installed_def] \\

  qmatch_assum_abbrev_tac`good_init_state mc ms ffi bytes cbspace tar_st m dm io_regs cc_regs` \\
  qpat_x_assum`Abbrev(p7 = _)` mp_tac>>
  qmatch_goalsub_abbrev_tac`compile _ _ _ stk stoff`>>
  strip_tac \\
  qabbrev_tac`kkk = stk - 2`>>
  qmatch_goalsub_abbrev_tac`semantics _ _ data_oracle` \\

  qabbrev_tac `c4_data_conf = (c4.data_conf with has_fp_ops := (1 < c4.lab_conf.asm_conf.fp_reg_count))` \\
  qabbrev_tac`word_oracle =
    (I ## MAP (λp. full_compile_single mc.target.config.two_reg_arith kkk aa c4.lab_conf.asm_conf (p,NONE))) o
    (I ## MAP (compile_part c4_data_conf)) o
    data_oracle`>>
  qabbrev_tac`stack_oracle =
     (λn.
      let ((bm0,cfg),progs) = word_oracle n in
      let (progs,bm) = word_to_stack$compile_word_to_stack kkk progs bm0 in
        (cfg,progs,DROP (LENGTH bm0) bm))`>>
  qabbrev_tac`lab_oracle =
    (λn.
     let (cfg,p,b) = stack_oracle n in
       (cfg,compile_no_stubs c4.stack_conf.reg_names c4.stack_conf.jump stoff stk p))`\\
  qabbrev_tac`lab_st:('a,'a lab_to_target$config,'ffi) labSem$state = lab_to_targetProof$make_init mc ffi io_regs cc_regs tar_st m (dm ∩ byte_aligned) ms p7 lab_to_target$compile
       (mc.target.get_pc ms + n2w (LENGTH bytes)) cbspace lab_oracle` \\
  qabbrev_tac`stack_st_opt =
    full_make_init
      c4.stack_conf
      c4.data_conf
      (2 * max_heap_limit (:'a) c4_data_conf - 1)
      stk
      stoff
      c6.bitmaps
      p6
      lab_st
      (set mc.callee_saved_regs)
      data_sp
      stack_oracle` >>
  qabbrev_tac`stack_st = FST stack_st_opt` >>
  qabbrev_tac`word_st = make_init kkk stack_st (fromAList p5) word_oracle` \\
  (data_to_wordProofTheory.compile_semantics
   |> GEN_ALL
   |> SIMP_RULE (srw_ss()) [markerTheory.Abbrev_def]
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["t","co","x1","start","prog","c"]))
   |> Q.ISPECL_THEN [`word_st`,`data_oracle`]mp_tac)
  \\ qhdtm_x_assum`data_to_word$compile`mp_tac
  \\ (data_to_word_compile_conventions
     |> Q.GENL[`data_conf`,`wc`,`ac`,`prog`]
     |> C (specl_args_of_then``data_to_word$compile``)mp_tac)
  \\ impl_tac >- fs[mc_conf_ok_def]
  \\ strip_tac \\ fs[]
  \\ (data_to_word_compile_lab_pres
     |> Q.GENL[`data_conf`,`word_conf`,`asm_conf`,`prog`]
     |> C (specl_args_of_then``data_to_word$compile``)mp_tac)
  \\ ntac 2 strip_tac
  \\ FULL_SIMP_TAC std_ss [Once LET_THM]>>
  imp_res_tac (word_to_stack_compile_lab_pres |> INST_TYPE [beta|->alpha])>>
  pop_assum (qspec_then`c4.lab_conf.asm_conf` assume_tac)>>fs[]>>
  rfs[]>>
  (word_to_stack_stack_asm_convs |> GEN_ALL |> Q.SPECL_THEN[`p5`,`c4.lab_conf.asm_conf`] mp_tac)>>
  impl_tac>-
    (fs[Abbr`c4`,EVERY_MEM,FORALL_PROD]>>
     unabbrev_all_tac \\ fs[] >>
    metis_tac[])>>
  strip_tac>>
  drule (word_to_stack_stack_convs|> GEN_ALL)>>
  simp[]>>
  impl_tac>-
    (fs[backend_config_ok_def,Abbr`c4`]>>
    unabbrev_all_tac >>
    fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD]>>
    fs[PULL_EXISTS]>>
    metis_tac[])>>
  strip_tac>>
  fs[data_to_wordTheory.compile_def]
  \\ qmatch_assum_abbrev_tac`compile _ _ t_code = (_,p5)`
  \\ drule (GEN_ALL compile_distinct_names)
  \\ fs[bvl_to_bviTheory.compile_def]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq
  \\ drule clos_to_bvlProofTheory.compile_all_distinct_locs
  \\ strip_tac
  \\ disch_then(qspec_then`0`mp_tac) \\ simp[] \\ strip_tac
  \\ `stubs (:'a) c4.data_conf = stubs (:'a) c4_data_conf` by ( simp[Abbr`c4_data_conf`] )
  \\ qmatch_assum_rename_tac`_ _ code = (n2,p3)`
  \\ `MAP FST p4 = MAP FST p3`
    by metis_tac[bvi_to_dataProofTheory.MAP_FST_compile_prog]
  \\ `code_rel c4_data_conf (fromAList p4) (fromAList t_code)`
  by (
    simp[data_to_word_gcProofTheory.code_rel_def] \\
    simp[Abbr`t_code`,lookup_fromAList,ALOOKUP_APPEND,EVERY_MEM,FORALL_PROD] \\
    conj_tac>-
      (fs[domain_fromAList]>>
      simp[Once UNION_COMM,SimpRHS]>>
      AP_TERM_TAC>>
      simp[data_to_wordTheory.compile_part_def,FST_triple,MAP_MAP_o,o_DEF,LAMBDA_PROD])>>
    conj_tac >- (
      rw[] \\
      drule(ONCE_REWRITE_RULE[CONJ_COMM] ALOOKUP_ALL_DISTINCT_MEM) \\
      impl_tac >- MATCH_ACCEPT_TAC ALL_DISTINCT_MAP_FST_stubs \\ simp[] ) \\
    rw[] \\
    reverse CASE_TAC >- (
      imp_res_tac ALOOKUP_MEM \\
      qpat_x_assum`MAP FST p4 = _`(assume_tac o SYM) \\ fs[] \\
      fs[EVERY_MEM,EVERY_MAP,FORALL_PROD] \\
      res_tac \\
      imp_res_tac(SIMP_RULE(std_ss)[MEM_MAP,Once EXISTS_PROD,PULL_EXISTS]MAP_FST_stubs_bound) \\
      fs[] ) \\
    match_mp_tac ALOOKUP_ALL_DISTINCT_MEM \\
    simp[MAP_MAP_o,o_DEF,LAMBDA_PROD,data_to_wordTheory.compile_part_def,FST_triple,MEM_MAP,EXISTS_PROD] \\
    metis_tac[ALOOKUP_MEM] ) \\
  `code_rel_ext (fromAList t_code) (fromAList p5)` by metis_tac[code_rel_ext_word_to_word] \\
  qpat_x_assum`Abbrev(tar_st = _)`kall_tac \\
  (* syntactic properties from stack_to_lab *)
  `all_enc_ok_pre c4.lab_conf.asm_conf p7` by (
    fs[Abbr`p7`,Abbr`stoff`,Abbr`stk`]>>
    match_mp_tac stack_to_lab_compile_all_enc_ok>>
    fs[stackPropsTheory.reg_name_def,Abbr`c4`,mc_conf_ok_def]>>
    unabbrev_all_tac >>
    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]>>rfs[]>>
    `-8w ≤ 0w:'a word ∧ 0w:'a word ≤ 8w` by
      fs[WORD_LE,labPropsTheory.good_dimindex_def,word_2comp_n2w,dimword_def,word_msb_n2w]>>
    metis_tac[])>>
  `labels_ok p7` by
    (fs[Abbr`p7`]>>
    match_mp_tac stack_to_lab_compile_lab_pres>>
    rw[]>>EVAL_TAC>>
    fs[EVERY_MEM]>> rpt strip_tac>>
    first_x_assum drule>>
    EVAL_TAC>>rw[])>>
  disch_then(qspecl_then[`fromAList t_code`,`InitGlobals_location`,`p4`,`c4_data_conf`]mp_tac) \\
  (* TODO: make this auto *)
  disch_then(qspecl_then[`mc.target.config.two_reg_arith`,`kkk`,`c4.lab_conf.asm_conf`,`aa`]mp_tac) \\
  `∀n. EVERY ($<= data_num_stubs) (MAP FST (SND (full_co c.bvl_conf co n)))` by (
    simp[Abbr`co`,full_co_def, Abbr`co3`,bvi_tailrecProofTheory.mk_co_def] \\
    simp[UNCURRY, backendPropsTheory.FST_state_co, FST_known_co]
    \\ simp[EVERY_MEM]
    \\ rpt gen_tac
    \\ qmatch_goalsub_abbrev_tac`bvi_tailrec$compile_prog znn xxs`
    \\ Cases_on`bvi_tailrec_compile_prog znn xxs`
    \\ rw[]
    \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
    \\ disch_then drule
    \\ simp[Abbr`xxs`, Abbr`znn`]
    \\ strip_tac
    >- (
      pop_assum mp_tac
      \\ simp[backendPropsTheory.SND_state_co]
      \\ qmatch_goalsub_abbrev_tac`bvl_to_bvi$compile_inc znn xxs`
      \\ Cases_on`bvl_to_bvi$compile_inc znn xxs`
      \\ rw[]
      \\ drule (GEN_ALL compile_inc_next_range)
      \\ disch_then drule
      \\ rw[]
      \\ qpat_x_assum`_ ≤ e`mp_tac
      \\ EVAL_TAC
      \\ rw[] )
    \\ qpat_x_assum`_ ≤ e`mp_tac
    \\ simp_tac(srw_ss())[Abbr`pc`]
    \\ qmatch_goalsub_rename_tac`IG.bitmaps,NORE`
    \\ EVAL_TAC
    \\ qpat_x_assum`_ = (n2,_)`assume_tac
    \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
    \\ IF_CASES_TAC \\ EVAL_TAC \\ rw[] )
  \\ `loc = InitGlobals_location` by
   (fs [bvl_to_bviTheory.compile_def,bvl_to_bviTheory.compile_prog_def]
    \\ rpt (pairarg_tac \\ fs []))
  \\ impl_tac >- (
    simp[Abbr`word_st`,word_to_stackProofTheory.make_init_def,Abbr`c4`,Abbr`c4_data_conf`] \\
    (*
    qmatch_goalsub_rename_tac`c5.data_conf` \\ qunabbrev_tac`c5` \\
    *)
    fs[mc_conf_ok_def] \\
    conj_tac >- (
      simp[Abbr`stack_st`] \\
      simp[full_make_init_def,stack_allocProofTheory.make_init_def,Abbr`stack_st_opt`] ) \\
    simp[Abbr`stack_st`] \\
    conj_tac>-
      (match_mp_tac (GEN_ALL IMP_init_store_ok)
       \\ simp[Abbr`stack_st_opt`]
       \\ metis_tac[PAIR])>>
    fs[Abbr`stack_st_opt`,full_make_init_buffer]>>
    fs[Abbr`lab_st`,full_make_init_ffi]>>
    fs[Abbr`word_oracle`,Abbr`t_code`,domain_fromAList]>>
    conj_tac
    >- fs [data_to_wordTheory.conf_ok_def,
           data_to_wordTheory.shift_length_def] \\
    CONJ_TAC>- (
      fs[Abbr`data_oracle`,full_co_def,bvi_tailrecProofTheory.mk_co_def]
      \\ qpat_x_assum`∀n. EVERY _ _`mp_tac
      \\ rewrite_tac[GSYM bvi_to_dataProofTheory.MAP_FST_compile_prog]
      \\ simp[EVERY_MAP, LAMBDA_PROD] ) \\
    conj_tac >- (
      AP_TERM_TAC>>
      simp[data_to_wordTheory.compile_part_def,FST_triple,MAP_MAP_o,o_DEF,LAMBDA_PROD])>>
    qmatch_goalsub_abbrev_tac`semantics _ _ _ TODO_cc'`
    \\ qpat_x_assum`semantics _ _ data_oracle _ _ ≠ Fail`mp_tac
    \\ qmatch_goalsub_abbrev_tac`semantics _ _ _ TODO_cc`
    \\ `TODO_cc' = TODO_cc` suffices_by simp[]
    \\ simp[Abbr`TODO_cc`,Abbr`TODO_cc'`, FUN_EQ_THM]
    \\ rpt gen_tac
    \\ AP_TERM_TAC
    \\ simp[Abbr`kkk`,Abbr`stk`]
    \\ AP_THM_TAC \\ AP_THM_TAC
    \\ simp[full_make_init_compile]
    \\ simp[EVAL``(make_init a b c d e f g h i j k l m).compile``]
    \\ simp[Abbr`stoff`] ) \\
  `lab_st.ffi = ffi` by ( fs[Abbr`lab_st`] ) \\
  `word_st.ffi = ffi` by (
    simp[Abbr`word_st`,word_to_stackProofTheory.make_init_def] \\
    fs[Abbr`stack_st`,Abbr`lab_st`,Abbr`stack_st_opt`] \\
    fs [full_make_init_def,stack_allocProofTheory.make_init_def,
        stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC) \\
  strip_tac \\
  qmatch_abbrev_tac`x ⊆ extend_with_resource_limit y` \\
  `Fail ∉ y` by fs[Abbr`y`] \\
  pop_assum mp_tac \\ simp[GSYM implements_def] \\
  simp[Abbr`y`] \\
  drule (GEN_ALL semantics_compile) \\
  disch_then(drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(optionSyntax.is_some o rhs))))) \\
  simp[Abbr`c4`] \\
  disch_then(drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``good_init_state`` o fst o strip_comb))))) \\
  disch_then(qspec_then`lab_oracle`mp_tac) \\

  `∀k. SND (co k) = []` by (
      gen_tac
      \\ simp[Abbr`co`, Abbr`co3`, backendPropsTheory.state_co_def, Abbr`pc`, backendPropsTheory.pure_co_def, UNCURRY]
      \\ simp[flat_to_patTheory.compile_def]
      \\ qmatch_goalsub_abbrev_tac`SND (aaa (bbb,[],[]))`
      \\ `SND (aaa (bbb,[],[])) = ([],[])`  by ( rw[Abbr`bbb`,Abbr`aaa`] \\ EVAL_TAC )
      \\ fs[]
      \\ simp[closPropsTheory.ignore_table_def, UNCURRY]
      \\ `FST (FST (aaa (bbb,[],[]))) = TODO_co1`
      by ( simp[Abbr`aaa`,Abbr`bbb`] \\ rw[] )
      \\ fs[]
      \\ qmatch_goalsub_abbrev_tac`SND ccc,[]`
      \\ `ccc = (make_even (TODO_co1+1), [Op None (Const (&TODO_co1))[]])`
      by ( simp[Abbr`ccc`] \\ EVAL_TAC )
      \\ fs[Abbr`ccc`]
      \\ qmatch_goalsub_abbrev_tac`_ _ (SND ccc)`
      \\ `ccc = (SND (SND (FST (aaa (bbb,[],[])))),[Op None (Const (&TODO_co1)) []],[])`
      by (
        simp[Abbr`ccc`]
        \\ EVAL_TAC \\ simp[UNCURRY]
        \\ CASE_TAC \\ EVAL_TAC )
      \\ fs[Abbr`ccc`]
      \\ qmatch_goalsub_abbrev_tac`_ (SND ccc)`
      \\ `SND ccc = ([Op None (Const (&TODO_co1)) []],[])`
      by ( rw[Abbr`ccc`] \\ EVAL_TAC )
      \\ fs[]
      \\ simp[clos_annotateProofTheory.compile_inc_def]
      \\ CONV_TAC(LAND_CONV(RAND_CONV EVAL))
      \\ simp[clos_to_bvlProofTheory.compile_inc_def]) \\
  `∀k. FST (SND (FST (co k))) = n1`
  by (
    simp[Abbr`co`, backendPropsTheory.FST_state_co, FST_known_co]
    \\ simp[Abbr`co3`]
    \\ rewrite_tac[COND_RATOR]
    \\ rewrite_tac[Ntimes COND_RAND 3]
    \\ simp[] )
  \\ drule (GEN_ALL bvl_to_bviProofTheory.compile_prog_distinct_locs)
  \\ impl_tac >- ( drule bvl_inlineProofTheory.compile_prog_names \\ rw[] )
  \\ strip_tac
  \\ `∀k. FST (SND (SND (FST (co k)))) = n2`
  by (
    simp[Abbr`co`, backendPropsTheory.FST_state_co, FST_known_co]
    \\ simp[Abbr`co3`]
    \\ rewrite_tac[COND_RATOR]
    \\ rewrite_tac[Ntimes COND_RAND 3]
    \\ simp[] )
  \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_next_mono)
  \\ strip_tac
  \\ pop_assum(assume_tac o Abbrev_intro)

  \\ `∀k. FST (SND (SND (SND (FST (co k))))) = ((FST(compile c.lab_conf.asm_conf p5)).bitmaps)`
  by (
    simp[Abbr`co`, backendPropsTheory.FST_state_co, FST_known_co]
    \\ simp[Abbr`co3`]
    \\ rewrite_tac[COND_RATOR]
    \\ rewrite_tac[Ntimes COND_RAND 5]
    \\ simp[]
    \\ qpat_x_assum`_ = (_,p5)`mp_tac
    \\ simp[]
    \\ simp[Abbr`t_code`]
    \\ qunabbrev_tac`c4_data_conf`
    \\ simp_tac(srw_ss())[]
    \\ simp[])
  \\ `∀k. (SND(SND(SND(SND(FST(co k)))))).labels = (SND(THE(compile c.lab_conf p7))).labels`
  by (
    simp[Abbr`co`, backendPropsTheory.FST_state_co, FST_known_co]
    \\ simp[Abbr`co3`]
    \\ rewrite_tac[COND_RATOR]
    \\ rewrite_tac[Ntimes COND_RAND 8]
    \\ simp[]
    \\ rpt AP_TERM_TAC
    \\ simp[Abbr`p7`,Abbr`stk`,Abbr`stoff`]
    \\ AP_TERM_TAC
    \\ qpat_x_assum`_ = (_,p6)`mp_tac
    \\ simp[]
    \\ simp[SND_EQ_EQUIV] \\ rw[]
    \\ qexists_tac`c6` \\ pop_assum(SUBST1_TAC o SYM)
    \\ AP_TERM_TAC
    \\ qpat_x_assum`_ = (_,p5)`mp_tac
    \\ simp[]
    \\ simp[SND_EQ_EQUIV] \\ rw[]
    \\ qexists_tac`col` \\ pop_assum(SUBST1_TAC o SYM)
    \\ AP_TERM_TAC
    \\ simp[Abbr`t_code`]
    \\ qunabbrev_tac`c4_data_conf`
    \\ simp_tac (srw_ss())[]
    \\ simp[] )
  \\ impl_keep_tac
  >- (

    conj_tac >- (
      simp[compiler_oracle_ok_def,good_code_def] \\
      conj_tac
      >- (
        simp[Abbr`lab_oracle`, UNCURRY]
        \\ simp[compile_no_stubs_def]
        \\ gen_tac
        \\ qmatch_goalsub_abbrev_tac`MAP prog_to_section ppg`
        \\ `labels_ok (MAP prog_to_section ppg)`
        by (
          irule prog_to_section_labels_ok
          \\ simp[Abbr`ppg`,MAP_MAP_o, o_DEF]
          \\ simp_tac(srw_ss()++ETA_ss)[Abbr`stack_oracle`]
          \\ simp[UNCURRY]
          \\ qmatch_goalsub_abbrev_tac`compile_word_to_stack kkk psk bmk`
          \\ Cases_on`compile_word_to_stack kkk psk bmk`
          \\ imp_res_tac word_to_stackProofTheory.MAP_FST_compile_word_to_stack
          \\ fs[Abbr`psk`]
          \\ simp[Abbr`word_oracle`, MAP_MAP_o, o_DEF]
          \\ simp[word_to_wordTheory.full_compile_single_def, UNCURRY]
          \\ simp_tac(srw_ss()++ETA_ss)[Abbr`data_oracle`]
          \\ conj_tac >- (
            irule ALL_DISTINCT_MAP_FST_SND_full_co
            \\ simp[]
            \\ simp[Abbr`n2`]
            \\ EVAL_TAC \\ simp[])
          \\ simp[stack_namesTheory.compile_def, MAP_MAP_o, EVERY_MAP]
          \\ simp[LAMBDA_PROD]
          \\ simp[stack_allocTheory.prog_comp_def]
          \\ simp[stack_removeTheory.prog_comp_def]
          \\ simp[stack_namesTheory.prog_comp_def]
          \\ simp[Once EVERY_MEM, FORALL_PROD]
          \\ qx_genl_tac[`l1`,`l2`] \\ strip_tac
          \\ simp[GSYM stack_namesProofTheory.stack_names_lab_pres]
          \\ simp[GSYM stack_removeProofTheory.stack_remove_lab_pres]
          \\ simp[GSYM word_to_stackProofTheory.word_to_stack_lab_pres]
          \\ qspecl_then[`l1`,`next_lab l2 1`,`l2`]mp_tac stack_allocProofTheory.stack_alloc_lab_pres
          \\ simp[]
          \\ pairarg_tac \\ simp[]
          \\ reverse impl_tac >- rw[]
          \\ drule compile_word_to_stack_lab_pres
          \\ CONV_TAC(PATH_CONV"lrr"(SIMP_CONV(srw_ss())[Once EVERY_MEM]))
          \\ simp[FORALL_PROD]
          \\ disch_then irule \\ simp[]
          \\ qmatch_goalsub_abbrev_tac`EVERY _ pp`
          \\ qmatch_asmsub_abbrev_tac`Abbrev (pp = MAP _ pp0)`
          \\ `∃wc ign. compile wc mc.target.config pp0 = (ign, pp)`
          by (
            simp[word_to_wordTheory.compile_def]
            \\ qexists_tac`<| col_oracle := K NONE; reg_alg := aa |>`
            \\ simp[]
            \\ simp[word_to_wordTheory.next_n_oracle_def]
            \\ simp[Abbr`pp`]
            \\ simp[Abbr`kkk`,Abbr`stk`]
            \\ simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP] )
          \\ qspecl_then[`wc`,`mc.target.config`,`pp0`]mp_tac (Q.GENL[`wc`,`ac`,`p`]word_to_wordProofTheory.compile_to_word_conventions)
          \\ simp[]
          \\ strip_tac
          \\ qhdtm_x_assum`EVERY`mp_tac
          \\ simp[Once EVERY_MEM] \\ strip_tac
          \\ simp[Once EVERY_MEM]
          \\ ntac 2 strip_tac
          \\ first_x_assum drule
          \\ pairarg_tac \\ fs[]
          \\ strip_tac
          \\ qhdtm_x_assum`LIST_REL`mp_tac
          \\ simp[EVERY2_MAP,word_simpProofTheory.labels_rel_def]
          \\ simp[LIST_REL_EL_EQN]
          \\ strip_tac
          \\ qpat_x_assum`MEM _ pp`mp_tac
          \\ simp[MEM_EL]
          \\ disch_then(qx_choose_then`i`strip_assume_tac)
          \\ first_x_assum(qspec_then`i`mp_tac)
          \\ simp[] \\ strip_tac
          \\ qpat_x_assum`_ = EL i pp`(assume_tac o SYM) \\ fs[]
          \\ fs[Abbr`pp0`] \\ rfs[EL_MAP]
          \\ qmatch_asmsub_abbrev_tac`compile_part c4_data_conf pp4`
          \\ PairCases_on`pp4`
          \\ pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])
          \\ fs[data_to_wordTheory.compile_part_def]
          \\ qspecl_then[`c4_data_conf`,`pp40`,`1`,`pp42`]mp_tac data_to_wordProofTheory.data_to_word_lab_pres_lem
          \\ simp[]
          \\ pairarg_tac \\ fs[]
          \\ simp[EVERY_MEM]
          \\ rw[]
          \\ fs[SUBSET_DEF]
          \\ first_x_assum drule
          \\ strip_tac
          \\ first_x_assum drule
          \\ pairarg_tac \\ rw[]
          \\ qpat_x_assum`MAP FST pp = _`mp_tac
          \\ simp[LIST_EQ_REWRITE, EL_MAP]
          \\ disch_then(qspec_then`i`mp_tac)
          \\ simp[])
        \\ drule labels_ok_imp
        \\ simp[]
        \\ strip_tac
        \\ simp[Abbr`stack_oracle`, UNCURRY]
        \\ simp[Abbr`word_oracle`]
        \\ simp[Abbr`data_oracle`]
        \\ simp[full_co_def, bvi_tailrecProofTheory.mk_co_def, UNCURRY, backendPropsTheory.FST_state_co]
        \\ fs[]
        \\ qpat_x_assum`compile _ p7 = _`mp_tac
        \\ simp[lab_to_targetTheory.compile_def]
        \\ simp[lab_to_targetTheory.compile_lab_def]
        \\ pairarg_tac \\ fs[]
        \\ pop_assum mp_tac
        \\ simp[CaseEq"prod",CaseEq"option"]
        \\ once_rewrite_tac[GSYM AND_IMP_INTRO]
        \\ disch_then(assume_tac o Abbrev_intro)
        \\ strip_tac
        \\ strip_tac
        \\ rveq
        \\ simp[]
        \\ imp_res_tac remove_labels_domain_labs
        \\ simp[]
        \\ fs[PAIR_MAP, UNCURRY]
        \\ simp[CONJ_ASSOC]
        \\ reverse conj_tac
        >- (
          irule compile_all_enc_ok_pre
          \\ reverse conj_tac
          >- (
            first_x_assum irule
            \\ fs[mc_conf_ok_def]
            \\ fs[WORD_LE,labPropsTheory.good_dimindex_def,word_2comp_n2w,dimword_def,word_msb_n2w] )
          \\ simp[Abbr`ppg`]
          \\ irule stack_namesProofTheory.stack_names_stack_asm_ok
          \\ reverse conj_tac
          >- ( qhdtm_x_assum`mc_conf_ok`mp_tac \\ simp[mc_conf_ok_def] )
          \\ simp[Once EVERY_MAP]
          \\ simp[LAMBDA_PROD]
          \\ simp[stack_removeTheory.prog_comp_def]
          \\ simp[Once EVERY_MEM, FORALL_PROD]
          \\ rpt gen_tac \\ strip_tac
          \\ irule stack_removeProofTheory.stack_remove_comp_stack_asm_name
          \\ simp[]
          \\ conj_tac >- fs[mc_conf_ok_def]
          \\ conj_tac >- fs[Abbr`stoff`]
          \\ conj_tac >- ( fs[Abbr`stk`] \\ EVAL_TAC \\ fs[] )
          \\ conj_tac >- ( fs[Abbr`stk`] \\ EVAL_TAC \\ fs[] )
          \\ conj_tac >- ( fs[Abbr`stk`] \\ EVAL_TAC \\ fs[] )
          \\ pop_assum mp_tac
          \\ simp[Once MEM_MAP, EXISTS_PROD]
          \\ simp[stack_allocTheory.prog_comp_def]
          \\ simp[FST_EQ_EQUIV]
          \\ strip_tac
          \\ qhdtm_x_assum`comp`mp_tac
          \\ specl_args_of_then``stack_alloc$comp`` stack_allocProofTheory.stack_alloc_comp_stack_asm_name
                (Q.ISPEC_THEN`mc.target.config`mp_tac o Q.GEN`c`)
          \\ ntac 2 strip_tac \\ fs[]
          \\ first_x_assum match_mp_tac
          \\ qmatch_asmsub_abbrev_tac`compile_word_to_stack kkk pp qq`
          \\ Cases_on`compile_word_to_stack kkk pp qq`
          \\ drule (Q.GEN`c`compile_word_to_stack_convs)
          \\ disch_then(qspec_then`mc.target.config`mp_tac)
          \\ impl_tac
          >- (
            reverse conj_tac
            >- ( fs[Abbr`kkk`,Abbr`stk`] )
            \\ qmatch_asmsub_abbrev_tac`Abbrev (pp = MAP _ pp0)`
            \\ `∃wc ign. compile wc mc.target.config pp0 = (ign, pp)`
            by (
              simp[word_to_wordTheory.compile_def]
              \\ qexists_tac`<| col_oracle := K NONE; reg_alg := aa |>`
              \\ simp[]
              \\ simp[word_to_wordTheory.next_n_oracle_def]
              \\ simp[Abbr`pp`]
              \\ simp[Abbr`kkk`,Abbr`stk`]
              \\ simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP]
              \\ simp[UNCURRY])
            \\ qspecl_then[`wc`,`mc.target.config`,`pp0`]mp_tac(
                 Q.GENL[`wc`,`ac`,`p`]word_to_wordProofTheory.compile_to_word_conventions)
            \\ simp[]
            \\ simp[EVERY_MEM, UNCURRY, Abbr`kkk`, Abbr`stk`]
            \\ rw[]
            \\ first_x_assum drule
            \\ rw[]
            \\ first_x_assum irule
            \\ simp[Abbr`pp0`, FORALL_PROD]
            \\ simp[MEM_MAP, EXISTS_PROD]
            \\ simp[data_to_wordTheory.compile_part_def]
            \\ simp[PULL_EXISTS] \\ rw[]
            \\ irule data_to_wordProofTheory.comp_no_inst
            \\ qunabbrev_tac`c4_data_conf`
            \\ EVAL_TAC
            \\ fs[backend_config_ok_def, asmTheory.offset_ok_def]
            \\ pairarg_tac \\ fs[]
            \\ pairarg_tac \\ fs[]
            \\ fsrw_tac[DNF_ss][]
            \\ conj_tac \\ first_x_assum irule
            \\ fs[mc_conf_ok_def]
            \\ fs[WORD_LE,labPropsTheory.good_dimindex_def,word_2comp_n2w,dimword_def,word_msb_n2w] )
          \\ simp[EVERY_MEM, FORALL_PROD] \\ fs[]
          \\ disch_then drule
          \\ simp[])
        \\ simp[MAP_prog_to_section_Section_num]
        \\ `ppg = []`
        by (
          simp[Abbr`ppg`]
          \\ EVAL_TAC
          \\ simp[UNCURRY]
          \\ EVAL_TAC )
        \\ simp[]
        \\ EVAL_TAC
        \\ simp[]
        (*
        \\ conj_tac
        >- (
          simp[Abbr`ppg`]
          \\ simp[MAP_MAP_o, o_DEF]
          \\ srw_tac[ETA_ss][]
          \\ qmatch_goalsub_abbrev_tac`compile_word_to_stack kkk pp qq`
          \\ Cases_on`compile_word_to_stack kkk pp qq`
          \\ drule word_to_stackProofTheory.MAP_FST_compile_word_to_stack \\ rw[]
          \\ simp[Abbr`pp`, MAP_MAP_o, o_DEF]
          \\ simp[word_to_wordTheory.full_compile_single_def, UNCURRY]
          \\ srw_tac[ETA_ss][bvi_to_dataTheory.compile_prog_def]
          \\ srw_tac[ETA_ss][MAP_MAP_o, o_DEF]
          \\ simp[full_co_def, bvi_tailrecProofTheory.mk_co_def, UNCURRY, backendPropsTheory.FST_state_co, backendPropsTheory.SND_state_co]
          \\ qmatch_goalsub_abbrev_tac`compile_prog n2 pp`
          \\ Cases_on`compile_prog n2 pp`
          \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
          \\ rw[]
          \\ simp[IN_DISJOINT]
          \\ CCONTR_TAC \\ fs[]
          \\ first_x_assum drule
          \\ simp[]
          \\ rveq
          \\ qunabbrev_tac`pp`
          \\ qmatch_goalsub_abbrev_tac`bvl_to_bvi$compile_inc n1 pp`
          \\ Cases_on`compile_inc n1 pp`
          \\ drule (GEN_ALL bvl_to_bviProofTheory.compile_inc_next_range)
          \\ strip_tac \\ fs[]
          \\ qmatch_assum_rename_tac`z ∈ get_code_labels p7`
          \\ PairCases_on`z` \\ fs[]
          \\ conj_tac
          >- (
            strip_tac
            \\ first_x_assum drule
            \\ simp[]
            \\ cheat (* oracle labels... *) )
          \\ disj1_tac
          \\ fs[Abbr`p7`]
          \\ cheat (* get_code_labels range...  *) )
        \\ qspec_then`ppg`mp_tac get_labels_MAP_prog_to_section_SUBSET_code_labels
        \\ simp[SUBSET_DEF]
        \\ strip_tac
        \\ gen_tac \\ strip_tac
        \\ first_x_assum drule
        \\ strip_tac \\ rw[]
        \\ cheat (* referenced labels are present (for oracle) *) *))
      \\ fs[Abbr`stack_oracle`,Abbr`word_oracle`,Abbr`data_oracle`,Abbr`lab_oracle`] >>
      simp[Abbr`co`, Abbr`co3`] \\
      rpt(pairarg_tac \\ fs[]) \\
      fs[full_co_def,bvi_tailrecProofTheory.mk_co_def] \\
      rpt(pairarg_tac \\ fs[]) \\
      fs[backendPropsTheory.state_co_def] \\
      rpt(pairarg_tac \\ fs[]) \\
      rveq \\ fs[] \\
      rveq \\ fs[]
      \\ fs[backendPropsTheory.pure_co_def]
      \\ rveq \\ fs[]
      \\ qhdtm_assum`known_co`(mp_tac o Q.AP_TERM`FST`)
      \\ simp[FST_known_co]
      \\ qmatch_goalsub_rename_tac`SND ppp = _`
      \\ Cases_on`ppp` \\ strip_tac \\ fs[] \\ rveq
      \\ qpat_assum`_ = ((_,_,_,_,_,_,_,cfg),_)`(mp_tac o Q.AP_TERM`FST`)
      \\ rewrite_tac[COND_RATOR]
      \\ rewrite_tac[COND_RAND]
      \\ simp[]
      \\ strip_tac \\ rveq
      \\ simp[]
      \\ qpat_x_assum`compile c.lab_conf p7 = _`mp_tac
      \\ qmatch_asmsub_abbrev_tac`compile c.lab_conf TODO_p7`
      \\ `TODO_p7 = p7` suffices_by simp[]
      \\ simp[Abbr`p7`]
      \\ fs[Abbr`TODO_p7`,Abbr`stk`,Abbr`stoff`]
      \\ AP_TERM_TAC \\ rfs[])>>
    fs[good_code_def,labels_ok_def] \\
    (*
    qmatch_goalsub_rename_tac`c5.lab_conf.labels` \\ qunabbrev_tac`c5` >>
    *)
    rfs[]>>
    CONJ_TAC>-
      fs[Abbr`p7`,stack_to_labTheory.compile_def]>>
    CONJ_ASM1_TAC>-
      (match_mp_tac (MP_CANON EVERY_MONOTONIC)>>
      simp[Once CONJ_COMM]>>
      qpat_x_assum`all_enc_ok_pre _ _` kall_tac>>
      asm_exists_tac>>
      simp[]>>Cases>> simp[]>>
      rpt(pop_assum kall_tac)>>
      metis_tac [EVERY_sec_label_ok])>>
    CONJ_TAC>-
      (qpat_x_assum`ALL_DISTINCT (MAP _ p7)` mp_tac>>
      qmatch_goalsub_abbrev_tac`MAP ff p7`>>
      `ff = Section_num` by
        (simp[Abbr`ff`,FUN_EQ_THM]>>
        Cases>>simp[])>>
      simp[])>>
    CONJ_TAC>-
      (match_mp_tac (MP_CANON EVERY_MONOTONIC)>>
      simp[Once CONJ_COMM]>>
      qpat_x_assum`all_enc_ok_pre _ _` kall_tac>>
      pop_assum kall_tac>>
      asm_exists_tac>>
      simp[]>>Cases>> simp[]) >>
    qpat_x_assum`Abbrev(p7 = _)` mp_tac>>
    simp[markerTheory.Abbrev_def]>>
    disch_then (assume_tac o SYM)>>
    drule stack_to_lab_stack_good_code_labels>>
    simp[]>>
    disch_then match_mp_tac>>
    CONJ_TAC>- (
      EVAL_TAC
      \\ drule (GEN_ALL compile_prog_keeps_names)
      \\ disch_then irule
      \\ fs[bvl_to_bviTheory.compile_prog_def]
      \\ pairarg_tac \\ fs[] \\ rveq
      \\ simp[]
      \\ disj1_tac
      \\ EVAL_TAC )
    \\ drule word_to_stack_good_code_labels>>
    disch_then match_mp_tac>>
    irule data_to_word_good_code_labels \\
    simp[data_to_wordTheory.compile_def]
    \\ qpat_x_assum` _ = (_,p5)` assume_tac
    \\ qunabbrev_tac`t_code` \\ qunabbrev_tac`c4_data_conf`
    \\ fs[]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ simp[Abbr`p4`]
    \\ irule compile_prog_good_code_labels
    \\ qpat_x_assum`_ = (_,p3)`assume_tac
    \\ rpt(qhdtm_x_assum`semantics`kall_tac)
    \\ qpat_x_assum`_ = (_,code,_)`assume_tac
    \\ qpat_x_assum`_ = (_,prog')`assume_tac
    \\ qpat_x_assum`_ = (_,p''')`assume_tac
    \\ simp[bvi_good_code_labels_def]
    \\ drule
      (TODO_MOVE_1_compile_prog_good_code_labels
       |> INST_TYPE [alpha|->``:num#bvi$exp``]
       |> GEN_ALL)
    \\ disch_then match_mp_tac \\ fs []
    \\ qexists_tac `p3` \\ fs []
    \\ reverse conj_tac
    >-
     (imp_res_tac bvi_tailrec_compile_prog_labels
      \\ pop_assum kall_tac
      \\ pop_assum (SUBST1_TAC o GSYM) \\ fs [])
    \\ drule bvi_tailrec_compile_prog_labels
    \\ strip_tac
    \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o GSYM)
    \\ drule compile_prog_get_code_labels_TODO_move
    \\ qmatch_goalsub_abbrev_tac`ss ⊆ star INSERT _`
    \\ drule compile_prog_get_code_labels_TODO_move_1
    \\ strip_tac
    \\ fs[clos_to_bvlTheory.compile_def]
    \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
    \\ fs[set_MAP_code_sort]
    \\ qmatch_goalsub_abbrev_tac`star INSERT fcc ∪ pp`
    \\ `star ∈ fcc ∧ pp ⊆ fcc` suffices_by ( simp[SUBSET_DEF] \\ metis_tac[] )
    \\ drule (GEN_ALL compile_prog_code_labels_domain) \\ simp[]
    \\ disch_then(qspecl_then[`ARB`,`ARB`]strip_assume_tac)
    \\ fs[Abbr`fcc`]
    \\ conj_tac
    >- (
      simp[Abbr`star`,Abbr`pp`, PULL_EXISTS]
      \\ qmatch_goalsub_abbrev_tac`_ * mm`
      \\ disj1_tac \\ disj1_tac
      \\ qexists_tac`mm` \\ simp[]
      \\ fs[bvl_inlineTheory.compile_prog_def, bvl_inlineTheory.compile_inc_def]
      \\ pairarg_tac \\ fs[] \\ rveq
      \\ simp[bvl_inlineProofTheory.MAP_FST_MAP_optimise]
      \\ fs[bvl_inlineTheory.tick_compile_prog_def]
      \\ qmatch_asmsub_abbrev_tac`tick_inline_all limit ts qrog []`
      \\ qspecl_then[`limit`,`ts`,`qrog`]mp_tac bvl_inlineProofTheory.MAP_FST_tick_inline_all
      \\ simp[]
      \\ rw[Abbr`qrog`]
      \\ simp[set_MAP_code_sort] )
    \\ simp[Abbr`pp`]
    \\ drule bvl_inlineProofTheory.compile_prog_names
    \\ rw[set_MAP_code_sort]
    \\ qmatch_goalsub_abbrev_tac`IMAGE ff _`
    \\ qmatch_asmsub_abbrev_tac`star = _ + _ * mm`
    \\ `star = ff mm` by simp[Abbr`ff`,Abbr`star`]
    \\ pop_assum SUBST1_TAC
    \\ qmatch_goalsub_abbrev_tac`IMAGE ff AA ⊆ IMAGE ff CC ∪ {ff mm} ∪ IMAGE ff BB ∪ DD ∪ EE`
    \\ `DISJOINT (IMAGE ff AA) DD`
    by (
      simp[Abbr`DD`,Abbr`ff`,IN_DISJOINT]
      \\ EVAL_TAC
      \\ CCONTR_TAC \\ fs[]
      \\ rveq
      \\ first_x_assum(mp_tac o Q.AP_TERM`λn. n MOD 3`)
      \\ simp[] )
    \\ `DISJOINT (IMAGE ff AA) EE`
    by (
      simp[Abbr`EE`,Abbr`ff`,bvl_to_bviTheory.stubs_def]
      \\ EVAL_TAC
      \\ CCONTR_TAC \\ fs[] )
    \\ `IMAGE ff AA ⊆ IMAGE ff CC ∪ IMAGE ff BB ∪ IMAGE ff {mm}` suffices_by (simp[SUBSET_DEF] \\ metis_tac[])
    \\ simp_tac std_ss [GSYM IMAGE_UNION]
    \\ irule IMAGE_SUBSET
    \\ match_mp_tac SUBSET_TRANS
    \\ asm_exists_tac
    \\ simp[Abbr`AA`,Abbr`BB`,Abbr`CC`]
    \\ simp[linear_scanProofTheory.set_MAP_FST_toAList]
    \\ conj_tac >- (
      reverse conj_tac
      >- (
        simp[clos_to_bvlTheory.init_globals_def, assign_get_code_label_def]
        \\ simp[clos_to_bvlTheory.partial_app_fn_location_def]
        \\ simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, MEM_FLAT, MEM_GENLIST, assign_get_code_label_def, domain_init_code]
        \\ conj_tac
        >- (
          rw[]
          \\ simp[Abbr`mm`, clos_to_bvlTheory.num_stubs_def]
          \\ simp[GSYM SUM_SET_count]
          \\ rewrite_tac[ADD_ASSOC] \\ simp[]
          \\ qmatch_goalsub_abbrev_tac`_ < SUM_SET (count ma)`
          \\ `prev + SUM_SET (count tot) ≤ SUM_SET (count ma)` suffices_by metis_tac[LESS_OR_EQ]
          \\ Cases_on`ma` \\ simp[COUNT_SUC]
          \\ simp[SUM_SET_THM, SUM_SET_DELETE]
          \\ `SUM_SET (count tot) ≤ SUM_SET (count n)` suffices_by simp[]
          \\ simp[SUM_SET_count]
          \\ simp[X_LE_DIV]
          \\ qspec_then`1`mp_tac bitTheory.DIV_MULT_THM
          \\ simp[]
          \\ disch_then kall_tac
          \\ `tot * (tot -1) ≤ n * (n - 1)` suffices_by simp[]
          \\ match_mp_tac LESS_MONO_MULT2
          \\ simp[] )
        \\ fs[clos_to_bvlTheory.compile_common_def]
        \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
        \\ simp[GSYM MEM_MAP]
        \\ simp[clos_to_bvlProofTheory.MAP_FST_compile_prog, Abbr`mm`]
        \\ simp[Once MEM_MAP]
        \\ simp[clos_labelsProofTheory.MAP_FST_compile]
        \\ simp[clos_to_bvlProofTheory.MAP_FST_chain_exps_any]
        \\ simp[Once MEM_MAP, MEM_COUNT_LIST]
        \\ metis_tac[ADD])
      \\ simp[clos_to_bvlTheory.init_code_def, domain_fromList, LENGTH_FLAT, MAP_GENLIST, o_DEF]
      \\ simp[SUBSET_DEF, PULL_EXISTS, MEM_MAP, FORALL_PROD]
      \\ simp[MEM_toAList, lookup_fromList, LENGTH_FLAT, MAP_GENLIST, o_DEF]
      \\ rpt gen_tac
      \\ simp[EL_APPEND_EQN]
      \\ rw[]
      >- (
        pop_assum mp_tac
        \\ simp[clos_to_bvlTheory.generate_generic_app_def]
        \\ simp[assign_get_code_label_def, bvl_get_code_labels_def,
                bvl_jumpTheory.Jump_def,
                clos_to_bvlTheory.partial_app_fn_location_code_def]
        \\ simp[MEM_MAP, MEM_GENLIST, PULL_EXISTS, bvl_get_code_labels_JumpList]
        \\ simp[assign_get_code_label_def, clos_to_bvlTheory.mk_cl_call_def]
        \\ simp[MEM_MAP, PULL_EXISTS, MEM_GENLIST]
        \\ simp[clos_to_bvlTheory.generic_app_fn_location_def] )
      \\ qmatch_asmsub_abbrev_tac`EL _ ls = z`
      \\ `MEM z ls` by (
        simp[MEM_EL, Abbr`ls`, Abbr`z`]
        \\ pop_assum (assume_tac o SYM)
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ simp[LENGTH_FLAT, MAP_GENLIST, o_DEF] )
      \\ pop_assum mp_tac
      \\ simp[MEM_FLAT, Abbr`ls`, MEM_GENLIST, PULL_EXISTS,Abbr`z`]
      \\ simp[clos_to_bvlTheory.generate_partial_app_closure_fn_def]
      \\ rw[]
      \\ fs[assign_get_code_label_def, MEM_MAP, MEM_GENLIST] \\ rveq \\ fs[assign_get_code_label_def] )
    \\ fs[clos_to_bvlTheory.compile_common_def]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
    \\ specl_args_of_then``clos_to_bvl$compile_prog``(Q.GENL[`max_app`,`prog`] compile_prog_code_labels)mp_tac
    \\ impl_tac >- (
        simp[]
        \\ `EVERY no_Labels e3 /\ clos_mtiProof$syntax_ok e3` by
         (qpat_x_assum `Abbrev (e3 = MAP pat_to_clos_compile _)` mp_tac
          \\ rpt (pop_assum kall_tac) \\ strip_tac \\ unabbrev_all_tac
          \\ fs [pat_to_closProofTheory.compile_no_Labels,EVERY_MEM,
                 MEM_MAP,PULL_EXISTS,syntax_ok_MAP_pat_to_clos])
        \\ qspecl_then [`cf`,`e3`] mp_tac compile_common_syntax
        \\ simp [clos_to_bvlTheory.compile_common_def]
        \\ Cases_on `cf.known_conf` \\ fs [])
    \\ strip_tac
    \\ match_mp_tac SUBSET_TRANS
    \\ asm_exists_tac \\ simp[]
    \\ reverse conj_tac >- simp[SUBSET_DEF]
    \\ qmatch_goalsub_abbrev_tac`compile_prog _ (compile ls)`
    \\ simp[clos_to_bvlProofTheory.MAP_FST_compile_prog]
    \\ qunabbrev_tac`ff`
    \\ qmatch_goalsub_abbrev_tac`IMAGE ff AA ⊆ BB ∪ CC ∪ {mm}`
    \\ `DISJOINT (IMAGE ff AA) {mm}` by (
      simp[Abbr`ff`, Abbr`mm`,clos_to_bvlTheory.num_stubs_def] )
    \\ `DISJOINT (IMAGE ff AA) BB`
    by(
      simp[Abbr`ff`,Abbr`BB`,IN_DISJOINT,domain_init_code,clos_to_bvlTheory.num_stubs_def]
      \\ CCONTR_TAC \\ fs[] )
    \\ `IMAGE ff AA ⊆ CC` suffices_by simp[SUBSET_DEF]
    \\ simp[Abbr`CC`]
    \\ rewrite_tac[GSYM LIST_TO_SET_APPEND, GSYM MAP_APPEND]
    \\ qmatch_goalsub_abbrev_tac`MAP ff CC`
    \\ `AA ⊆ set CC` suffices_by (
      simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS]
      \\ metis_tac[] )
    \\ simp[Abbr`AA`, Abbr`CC`]
    \\ qpat_x_assum `Abbrev (e3 = _)` kall_tac
    \\ qpat_x_assum `Abbrev (e3 = _)` assume_tac
    \\ rename [`Abbrev (_ = MAP pat_to_clos_compile pat_prog)`]
    \\ qspecl_then [`cf`,`pat_prog`] mp_tac compile_common_code_locs
    \\ simp [Abbr`ls`,Abbr`e3`]
    \\ fs [clos_to_bvlTheory.compile_common_def]
    \\ disch_then match_mp_tac
    \\ rpt strip_tac \\ fs [])
  \\ strip_tac
  \\ qpat_x_assum`Abbrev(stack_st_opt = _)`(mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) \\
  disch_then(assume_tac o SYM) \\
  Cases_on`stack_st_opt` \\
  drule full_make_init_semantics \\

  impl_tac >- (
    simp_tac std_ss [Once EVERY_FST_SND] \\
    qunabbrev_tac`stack_st` \\
    fs[Abbr`lab_st`,make_init_def] \\
    fs[mc_init_ok_def, mc_conf_ok_def, Abbr`stk`,byte_aligned_MOD] \\
    `max_heap_limit (:'a) c4_data_conf = max_heap_limit (:'a) c.data_conf` by
      (simp[Abbr`c4_data_conf`] \\ EVAL_TAC) \\
    conj_tac>- fs[Abbr`p7`] \\
    conj_tac>- simp[ETA_AX] \\
    `max_stack_alloc ≤ 2 * max_heap_limit (:α) c4_data_conf − 1` by
       fs [] \\ fs [] \\
    conj_tac >- (
      rfs[memory_assumption_def,Abbr`dm`] \\
      `(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8` by
       rfs [labPropsTheory.good_dimindex_def,bytes_in_word_def,dimword_def]>>
      fs [attach_bitmaps_def] \\
      once_rewrite_tac[INTER_COMM] \\
      rewrite_tac[UNION_OVER_INTER] \\
      once_rewrite_tac[UNION_COMM] \\
      match_mp_tac fun2set_disjoint_union \\
      conj_tac >- (
        match_mp_tac DISJOINT_INTER
        \\ metis_tac[DISJOINT_SYM] ) \\
      conj_tac >- (
        fs[attach_bitmaps_def] )
      \\ (
        match_mp_tac word_list_exists_imp>>
        fs [addresses_thm]>>
        fs[mc_conf_ok_def]>>
        `0 < dimindex (:α) DIV 8` by
          rfs [labPropsTheory.good_dimindex_def]>>
        reverse conj_tac >-
         (fs [] \\ match_mp_tac IMP_MULT_DIV_LESS \\ fs [w2n_lt]
          \\ rfs [labPropsTheory.good_dimindex_def])
        \\ qabbrev_tac `a = tar_st.regs mc.len_reg`
        \\ qabbrev_tac `b = tar_st.regs mc.len2_reg`
        \\ qpat_x_assum `a <=+ b` assume_tac
        \\ drule WORD_LS_IMP \\ strip_tac \\ fs [EXTENSION]
        \\ fs [IN_DEF,PULL_EXISTS,bytes_in_word_def,word_mul_n2w]
        \\ rw [] \\ reverse eq_tac THEN1
         (rw [] \\ fs [] \\ qexists_tac `i * (dimindex (:α) DIV 8)` \\ fs []
          \\ `0 < dimindex (:α) DIV 8` by rfs [labPropsTheory.good_dimindex_def]
          \\ drule X_LT_DIV \\ disch_then (fn th => fs [th])
          \\ fs [RIGHT_ADD_DISTRIB]
          \\ fs [GSYM word_mul_n2w,GSYM bytes_in_word_def]
          \\ fs [byte_aligned_mult])
        \\ rw [] \\ fs []
        \\ `i < dimword (:'a)` by metis_tac [LESS_TRANS,w2n_lt] \\ fs []
        \\ qexists_tac `i DIV (dimindex (:α) DIV 8)`
        \\ rfs [alignmentTheory.byte_aligned_def,
             ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
        \\ fs [aligned_w2n]
        \\ drule DIVISION
        \\ disch_then (qspec_then `i` (strip_assume_tac o GSYM))
        \\ `2 ** LOG2 (dimindex (:α) DIV 8) = dimindex (:α) DIV 8` by
             (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
        \\ fs [] \\ rfs [] \\ `-1w * a + b = b - a` by fs []
        \\ full_simp_tac std_ss []
        \\ Cases_on `a` \\ Cases_on `b`
        \\ full_simp_tac std_ss [WORD_LS,addressTheory.word_arith_lemma2]
        \\ fs [] \\ match_mp_tac DIV_LESS_DIV \\ fs []
        \\ rfs [] \\ fs [] \\ match_mp_tac MOD_SUB_LEMMA \\ fs []))>>
    conj_tac>- (
      fs[stack_to_labProofTheory.good_code_def]>>
      rfs[]>>
      CONJ_TAC>-
        (fs[ALL_DISTINCT_MAP_FST_stubs,ALL_DISTINCT_APPEND]
        \\ fs[EVERY_MEM]
        \\ rw[] \\ CCONTR_TAC \\ fs[]
        \\ res_tac
        \\ imp_res_tac MAP_FST_stubs_bound
        \\ pop_assum mp_tac \\ EVAL_TAC
        \\ pop_assum mp_tac \\ EVAL_TAC
        \\ pop_assum mp_tac \\ EVAL_TAC
        \\ TRY (
          strip_tac
          \\ qpat_x_assum`MEM k _ `mp_tac
          \\ EVAL_TAC
          \\ simp[] \\ NO_TAC )
        \\ decide_tac )>>
      (* simple syntactic thing *)
      simp[EVERY_FST_SND]>>
      CONJ_TAC>- EVAL_TAC>>
      `!k. data_num_stubs<= k ⇒ stack_num_stubs <=k` by
        (EVAL_TAC>>fs[])>>
      CONJ_TAC>-
        EVAL_TAC>>
      metis_tac[EVERY_MONOTONIC])
    >>
      fs[stack_to_labProofTheory.good_code_def,Abbr`stack_oracle`]>>
      simp[MAP_MAP_o, UNCURRY]
      \\ gen_tac
      \\ qmatch_goalsub_abbrev_tac`compile_word_to_stack kkk psk bmk`
      \\ Cases_on`compile_word_to_stack kkk psk bmk`
      \\ imp_res_tac word_to_stackProofTheory.MAP_FST_compile_word_to_stack
      \\ fs[Abbr`psk`]
      \\ simp[Abbr`word_oracle`, MAP_MAP_o, o_DEF]
      \\ simp[word_to_wordTheory.full_compile_single_def, UNCURRY]
      \\ simp_tac(srw_ss()++ETA_ss)[Abbr`data_oracle`]
      \\ conj_tac >- (
        irule ALL_DISTINCT_MAP_FST_SND_full_co
        \\ simp[]
        \\ simp[Abbr`n2`]
        \\ EVAL_TAC \\ simp[])
      \\ simp[Q.SPEC`P o FST`(INST_TYPE[alpha|->``:'a # 'b``]EVERY_CONJ)
              |> Q.SPEC`Q o SND` |> SIMP_RULE (srw_ss()) [LAMBDA_PROD]]
      \\ simp[EVERY_o, GSYM CONJ_ASSOC]
      \\ simp[MAP_MAP_o, o_DEF]
      \\ qpat_x_assum`Abbrev(bmk = _)`mp_tac
      \\ simp[PAIR_MAP]
      \\ simp[Once full_co_def]
      \\ simp[bvi_tailrecProofTheory.mk_co_def, UNCURRY]
      \\ simp[backendPropsTheory.FST_state_co]
      \\ strip_tac \\ qunabbrev_tac`bmk`
      \\ fs[PAIR_MAP]
      \\ qmatch_asmsub_abbrev_tac`compile_word_to_stack kkk pp`
      \\ drule (GEN_ALL compile_word_to_stack_convs)
      \\ disch_then(qspec_then`mc.target.config`mp_tac)
      \\ simp[]
      \\ qmatch_asmsub_abbrev_tac`Abbrev (pp = MAP _ pp0)`
      \\ `∃wc ign. compile wc mc.target.config pp0 = (ign, pp)`
      by (
        simp[word_to_wordTheory.compile_def]
        \\ qexists_tac`<| col_oracle := K NONE; reg_alg := aa |>`
        \\ simp[]
        \\ simp[word_to_wordTheory.next_n_oracle_def]
        \\ simp[Abbr`pp`]
        \\ simp[Abbr`kkk`]
        \\ simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP] )
      \\ qspecl_then[`wc`,`mc.target.config`,`pp0`]mp_tac (Q.GENL[`wc`,`ac`,`p`]word_to_wordProofTheory.compile_to_word_conventions)
      \\ simp[]
      \\ strip_tac
      \\ impl_tac
      >- (
        simp[EVERY_MAP, LAMBDA_PROD]
        \\ fs[Abbr`kkk`]
        \\ fs[EVERY_MEM] \\ rw[]
        \\ first_x_assum drule
        \\ pairarg_tac \\ rw[]
        \\ first_x_assum irule
        \\ simp[Abbr`pp0`, FORALL_PROD]
        \\ simp[MEM_MAP, EXISTS_PROD]
        \\ simp[data_to_wordTheory.compile_part_def]
        \\ simp[PULL_EXISTS] \\ rw[]
        \\ irule data_to_wordProofTheory.comp_no_inst
        \\ qunabbrev_tac`c4_data_conf`
        \\ EVAL_TAC
        \\ fs[backend_config_ok_def, asmTheory.offset_ok_def]
        \\ pairarg_tac \\ fs[]
        \\ pairarg_tac \\ fs[]
        \\ fsrw_tac[DNF_ss][]
        \\ conj_tac \\ first_x_assum irule
        \\ fs[mc_conf_ok_def]
        \\ fs[WORD_LE,labPropsTheory.good_dimindex_def,word_2comp_n2w,dimword_def,word_msb_n2w] )
      \\ simp[]
      \\ strip_tac
      \\ simp[EVERY_MAP]
      \\ simp[word_to_wordTheory.full_compile_single_def, UNCURRY]
      \\ simp[Once(GSYM o_DEF)]
      \\ simp[EVERY_o]
      \\ qpat_assum`∀n. EVERY ($<= _) _`mp_tac
      \\ disch_then(qspec_then`n`strip_assume_tac)
      \\ conj_tac
      >- (
        irule MONO_EVERY
        \\ goal_assum(first_assum o mp_then Any mp_tac)
        \\ EVAL_TAC \\ rw[] )
      \\ drule compile_word_to_stack_lab_pres
      \\ simp[Q.SPEC`P o FST`(INST_TYPE[alpha|->``:'a # 'b``]EVERY_CONJ)
              |> Q.SPEC`Q o SND` |> SIMP_RULE (srw_ss()) [LAMBDA_PROD]]
      \\ simp[o_DEF]
      \\ reverse impl_tac
      >- (
        fs[EVERY_MEM, FORALL_PROD]
        \\ rfs[Abbr`kkk`]
        \\ metis_tac[] )
      \\ qhdtm_x_assum`LIST_REL`mp_tac
      \\ simp[EVERY2_MAP,word_simpProofTheory.labels_rel_def]
      \\ simp[LIST_REL_EL_EQN]
      \\ strip_tac
      \\ simp[Once EVERY_MEM]
      \\ simp[MEM_EL]
      \\ gen_tac
      \\ disch_then(qx_choose_then`i`strip_assume_tac)
      \\ first_x_assum(qspec_then`i`mp_tac)
      \\ pairarg_tac \\ fs[]
      \\ strip_tac
      \\ qpat_x_assum`_ = EL i _`(assume_tac o SYM) \\ fs[]
      \\ fs[Abbr`pp0`] \\ rfs[EL_MAP]
      \\ qmatch_asmsub_abbrev_tac`compile_part c4_data_conf pp4`
      \\ PairCases_on`pp4`
      \\ pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])
      \\ fs[data_to_wordTheory.compile_part_def]
      \\ qspecl_then[`c4_data_conf`,`pp40`,`1`,`pp42`]mp_tac data_to_wordProofTheory.data_to_word_lab_pres_lem
      \\ simp[]
      \\ pairarg_tac \\ fs[]
      \\ simp[EVERY_MEM]
      \\ strip_tac
      \\ fs[SUBSET_DEF]
      \\ simp[GSYM FORALL_AND_THM, GSYM IMP_CONJ_THM]
      \\ gen_tac \\ strip_tac
      \\ first_x_assum drule
      \\ strip_tac
      \\ first_x_assum drule
      \\ pairarg_tac \\ rw[]
      \\ qpat_x_assum`MAP FST pp = _`mp_tac
      \\ simp[LIST_EQ_REWRITE, EL_MAP]
      \\ disch_then(qspec_then`i`mp_tac)
      \\ simp[]) >>
  CASE_TAC
  >- (
    strip_tac \\
    match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
    simp[Once CONJ_COMM] \\ rfs[] \\
    asm_exists_tac \\ simp[] \\
    fs[Abbr`lab_st`] \\
    metis_tac[dataPropsTheory.Resource_limit_hit_implements_semantics] ) \\
  fs[Abbr`word_st`] \\ rfs[] \\
  strip_tac \\
  match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
  qmatch_assum_abbrev_tac`z InitGlobals_location ∈ _ {_}` \\
  qexists_tac`{z InitGlobals_location}` \\
  fsrw_tac [ETA_ss] []>>
  conj_tac >- (
    match_mp_tac (GEN_ALL(MP_CANON implements_intro_ext)) \\
    simp[]
    \\ fs[full_make_init_compile]
    \\ fs[EVAL``(make_init a b c d e f g h i j k l m).compile``]
    \\ fs[Abbr`stoff`]
    \\ fs[EVAL``(word_to_stackProof$make_init a b c d).compile``]
    \\ fs[Abbr`kkk`,Abbr`stk`,Abbr`stack_st`] \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`semantics _ _ _ foo1`
    \\ qmatch_asmsub_abbrev_tac`semantics _ _ _ foo2`
    \\ `foo1 = foo2` suffices_by fs[]
    \\ simp[Abbr`foo1`,Abbr`foo2`]
    \\ simp[FUN_EQ_THM]
    \\ rpt gen_tac \\ AP_TERM_TAC
    \\ qhdtm_assum`full_make_init`(mp_tac o Q.AP_TERM`FST`)
    \\ simp_tac std_ss []
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[full_make_init_compile, Abbr`lab_st`]
    \\ fs[EVAL``(make_init a b c d e f g h i j k l m).compile``] ) \\
  simp[Abbr`z`] \\
  (word_to_stackProofTheory.compile_semantics
   |> Q.GENL[`t`,`code`,`asm_conf`,`start`]
   |> GEN_ALL
   |> Q.ISPECL_THEN[`kkk`,`word_oracle`,`stack_st`,`p5`,`c.lab_conf.asm_conf`,`InitGlobals_location`]mp_tac) \\

  impl_tac >- (
    fs[] \\
    conj_tac >- (
      fs[Abbr`stack_st`,full_make_init_def]
      \\ rveq
      \\ fs[stack_allocProofTheory.make_init_def] ) \\
    conj_asm1_tac >- (
      fs[Abbr`kkk`,Abbr`stk`]) >>
    conj_tac >- (
      match_mp_tac (GEN_ALL IMP_init_state_ok) \\
      fs[Abbr`kkk`,Abbr`stk`]>>
      fs[mc_conf_ok_def,backend_config_ok_def,Abbr`stack_st`] >>
      rfs[ETA_AX,Abbr`word_oracle`,Abbr`data_oracle`]>>
      simp[PAIR_MAP] >>
      simp[GSYM PULL_EXISTS] >>
      drule compile_word_to_stack_bitmaps>>
      CASE_TAC>>strip_tac>>
      fs[attach_bitmaps_def]>>
      simp[UNCURRY] >>
      simp[PULL_EXISTS] >> rveq >>
      goal_assum(first_assum o mp_then Any mp_tac) \\
      simp[EVERY_MAP] \\
      gen_tac
      \\ simp[GSYM EVERY_CONJ, CONJ_ASSOC]
      \\ reverse conj_tac
      >- ( EVAL_TAC \\ simp[UNCURRY] )
      \\ simp[EVERY_MEM]
      \\ gen_tac
      \\ simp[bvi_to_dataTheory.compile_prog_def]
      \\ qmatch_goalsub_abbrev_tac`MEM _ pp0`
      \\ qmatch_goalsub_rename_tac`MEM z pp0`
      \\ strip_tac
      \\ reverse conj_tac
      >- (
        EVAL_TAC
        \\ simp[UNCURRY]
        \\ simp[Abbr`pp0`]
        \\ fs[bvi_to_dataTheory.compile_prog_def, MEM_MAP]
        \\ pop_assum mp_tac
        \\ EVAL_TAC
        \\ simp[UNCURRY]
        \\ qmatch_asmsub_rename_tac`compile_part xxx`
        \\ PairCases_on`xxx`
        \\ simp[bvi_to_dataTheory.compile_part_def]
        \\ qmatch_goalsub_abbrev_tac`bvi_tailrec$compile_prog n2 pp`
        \\ Cases_on`bvi_tailrec$compile_prog n2 pp`
        \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
        \\ fs[]
        \\ simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD]
        \\ ntac 2 strip_tac
        \\ first_x_assum drule
        \\ reverse strip_tac
        >- (
          pop_assum mp_tac
          \\ simp[Abbr`n2`]
          \\ EVAL_TAC \\ rw[] )
        \\ strip_tac \\ rveq
        \\ pop_assum mp_tac
        \\ simp[Abbr`pp`]
        \\ qmatch_goalsub_abbrev_tac`bvl_to_bvi$compile_list n1 pp`
        \\ qspecl_then[`n1`,`pp`]mp_tac bvl_to_bviProofTheory.compile_list_distinct_locs
        \\ Cases_on`compile_list n1 pp` \\ simp[]
        \\ impl_tac
        >- ( simp[Abbr`pp`] \\ EVAL_TAC )
        \\ simp[EVERY_MEM, MEM_FILTER, FORALL_PROD, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
        \\ EVAL_TAC \\ rw[]
        \\ strip_tac \\ first_x_assum drule \\ EVAL_TAC
        \\ first_x_assum drule \\ rw[] )
      \\ qho_match_abbrev_tac`(_ _ (SND (SND (pp1 _))) ∧ _)`
      \\ `MEM (compile_part c4_data_conf z) (MAP (compile_part c4_data_conf) pp0)` by metis_tac[MEM_MAP]
      \\ qmatch_assum_abbrev_tac`MEM zz pp00`
      \\ `∃wc ign. compile wc mc.target.config pp00 = (ign, MAP (pp1 o (λz. (z, NONE))) pp00)`
      by (
        simp[word_to_wordTheory.compile_def]
        \\ qexists_tac`<| col_oracle := K NONE; reg_alg := aa |>`
        \\ simp[]
        \\ simp[word_to_wordTheory.next_n_oracle_def]
        \\ simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP] )
      \\ qspecl_then[`wc`,`mc.target.config`,`pp00`]mp_tac (Q.GENL[`wc`,`ac`,`p`]word_to_wordProofTheory.compile_to_word_conventions)
      \\ simp[]
      \\ simp[EVERY_MAP, UNCURRY]
      \\ simp[EVERY_MEM])>>
    conj_tac >- (
      qunabbrev_tac`t_code` \\
      imp_res_tac data_to_word_names \\
      simp[ALOOKUP_NONE] \\
      conj_tac >- EVAL_TAC \\
      strip_tac \\ fs[EVERY_MEM] \\
      res_tac \\ pop_assum mp_tac >> EVAL_TAC) \\
    conj_tac >- (
      simp[Abbr`stack_st`] \\
      fs[full_make_init_def] \\ rveq \\
      simp[stack_allocProofTheory.make_init_def,
           stack_removeProofTheory.make_init_any_bitmaps] ) \\
    conj_tac >- (
      fs[EVERY_MEM,FORALL_PROD] \\
      metis_tac[] ) \\
    fs[extend_with_resource_limit_def]
    \\ qpat_x_assum`_ ≠ Fail`assume_tac
    \\ qmatch_asmsub_abbrev_tac`semantics _ _ _ foo1 _ ≠ Fail`
    \\ qmatch_goalsub_abbrev_tac`semantics _ _ _ foo2`
    \\ `foo1 = foo2` suffices_by metis_tac[]
    \\ simp[Abbr`foo1`,Abbr`foo2`,FUN_EQ_THM]
    \\ rpt gen_tac \\ AP_TERM_TAC
    \\ AP_THM_TAC
    \\ simp[EVAL``(word_to_stackProof$make_init a b c e).compile``]
    \\ rfs[Abbr`stack_st`]
    \\ qhdtm_assum`full_make_init`(mp_tac o Q.AP_TERM`FST`)
    \\ simp_tac std_ss []
    \\ disch_then(SUBST_ALL_TAC o SYM)
    \\ fs[full_make_init_compile, Abbr`lab_st`]
    \\ fs[EVAL``(make_init a b c d e f g h i j k l m).compile``]) \\
  strip_tac \\
  match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
  qmatch_assum_abbrev_tac`z ∈ _ {_}` \\
  qexists_tac`{z}` \\
  conj_tac >- (
    match_mp_tac (GEN_ALL(MP_CANON implements_intro_ext)) \\
    simp[] ) \\
  simp[Abbr`z`] \\
  simp[Abbr`stack_st`] \\
  simp[Abbr`x`] \\
  match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
  ONCE_REWRITE_TAC[CONJ_COMM] \\
  asm_exists_tac \\ simp[]
  \\ first_x_assum match_mp_tac
  \\ match_mp_tac (GEN_ALL extend_with_resource_limit_not_fail)
  \\ asm_exists_tac \\ simp[]
  \\ CONV_TAC(RAND_CONV SYM_CONV)
  \\ match_mp_tac (GEN_ALL extend_with_resource_limit_not_fail)
  \\ asm_exists_tac \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`semantics _ _ _ foo1 _ ≠ Fail`
  \\ qmatch_goalsub_abbrev_tac`semantics _ _ _ foo2`
  \\ `foo1 = foo2` suffices_by metis_tac[]
  \\ simp[Abbr`foo1`,Abbr`foo2`,FUN_EQ_THM]
  \\ rpt gen_tac \\ AP_TERM_TAC
  \\ rfs[Abbr`kkk`,Abbr`stk`]
  \\ AP_THM_TAC
  \\ simp[EVAL``(word_to_stackProof$make_init a b c e).compile``]
  \\ qhdtm_assum`full_make_init`(mp_tac o Q.AP_TERM`FST`)
  \\ simp_tac std_ss []
  \\ disch_then(SUBST_ALL_TAC o SYM)
  \\ fs[full_make_init_compile, Abbr`lab_st`]
  \\ fs[EVAL``(make_init a b c d e f g h i j k l m).compile``]);

val _ = export_theory();

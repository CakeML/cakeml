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

(* TODO: move *)

fun Abbrev_intro th =
  EQ_MP (SYM(SPEC(concl th)markerTheory.Abbrev_def)) th

val EVERY_sec_label_ok = store_thm("EVERY_sec_label_ok",
  ``EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels l) (*∧
    ALL_DISTINCT (extract_labels l) *)⇔
    EVERY (sec_label_ok n) l``,
  Induct_on`l`>>simp[labPropsTheory.extract_labels_def]>>
  Cases>>simp[labPropsTheory.extract_labels_def]);

val EVERY_FST_SND = Q.store_thm("EVERY_FST_SND",
  `EVERY (λ(a,b). P a ∧ Q b) ls ⇔ EVERY P (MAP FST ls) ∧ EVERY Q (MAP SND ls)`,
  rw[EVERY_MEM,MEM_MAP,UNCURRY,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac[]);

val BIJ_FLOOKUP_MAPKEYS = Q.store_thm("BIJ_FLOOKUP_MAPKEYS",
  `BIJ bij UNIV UNIV ==>
    FLOOKUP (MAP_KEYS (LINV bij UNIV) f) n = FLOOKUP f (bij n)`,
  fs [FLOOKUP_DEF,MAP_KEYS_def,BIJ_DEF] \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x=x'/\(x /\ x' ==> y=y') ==> (if x then y else z) = (if x' then y' else z)``)
  \\ fs [] \\ rw []
  THEN1 (eq_tac \\ rw [] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF])
  \\ `BIJ (LINV bij UNIV) UNIV UNIV` by metis_tac [BIJ_LINV_BIJ,BIJ_DEF]
  \\ `INJ (LINV bij UNIV) (FDOM f) UNIV` by fs [INJ_DEF,IN_UNIV,BIJ_DEF]
  \\ fs [MAP_KEYS_def] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF]);

val word_list_exists_imp = Q.store_thm("word_list_exists_imp",
  `dm = addresses a n /\
    dimindex (:'a) DIV 8 * n < dimword (:'a) ∧ good_dimindex (:'a) ⇒
    word_list_exists a n (fun2set (m1,dm:'a word set))`,
  metis_tac [stack_removeProofTheory.word_list_exists_addresses]);

val addresses_thm = Q.store_thm("addresses_thm",
  `!n a. addresses a n = { a + n2w i * bytes_in_word | i < n }`,
  Induct \\ fs [stack_removeProofTheory.addresses_def]
  \\ rw [EXTENSION] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `0` \\ fs [])
  THEN1 (qexists_tac `SUC i` \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ Cases_on `i` \\ fs []
  \\ disj2_tac \\ fs []
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs []
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]);

val byte_aligned_mult = Q.store_thm("byte_aligned_mult",
  `good_dimindex (:'a) ==>
    byte_aligned (a + bytes_in_word * n2w i) = byte_aligned (a:'a word)`,
  fs [alignmentTheory.byte_aligned_def,labPropsTheory.good_dimindex_def]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM (EVAL ``2n**2``),GSYM (EVAL ``2n**3``),
        data_to_word_memoryProofTheory.aligned_add_pow]);

val IMP_MULT_DIV_LESS = Q.store_thm("IMP_MULT_DIV_LESS",
  `m <> 0 /\ d < k ==> m * (d DIV m) < k`,
  strip_tac \\ `0 < m` by decide_tac
  \\ drule DIVISION
  \\ disch_then (qspec_then `d` assume_tac)
  \\ decide_tac);

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

val DIV_LESS_DIV = Q.store_thm("DIV_LESS_DIV",
  `n MOD k = 0 /\ m MOD k = 0 /\ n < m /\ 0 < k ==> n DIV k < m DIV k`,
  strip_tac
  \\ drule DIVISION \\ disch_then (qspec_then `n` (strip_assume_tac o GSYM))
  \\ drule DIVISION \\ disch_then (qspec_then `m` (strip_assume_tac o GSYM))
  \\ rfs [] \\ metis_tac [LT_MULT_LCANCEL]);

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

val nsLookup_Bind_v_some = Q.store_thm("nsLookup_Bind_v_some",
  `nsLookup (Bind v []) k = SOME x ⇔
   ∃y. k = Short y ∧ ALOOKUP v y = SOME x`,
  Cases_on`k` \\ EVAL_TAC \\ simp[]);

val prim_config_eq = save_thm("prim_config_eq", EVAL ``prim_config`` |> SIMP_RULE std_ss [FUNION_FUPDATE_1,FUNION_FEMPTY_1]);

val IMP_init_state_ok = Q.store_thm("IMP_init_state_ok",
  `
  4 < kkk /\
    (bitmaps:'a word list) = 4w::t ∧
    good_dimindex (:α) /\
  (∀n.
    (λ((bm0,cfg),progs).
     EVERY
       (post_alloc_conventions kkk ∘ SND ∘ SND) progs ∧
     EVERY (flat_exp_conventions ∘ SND ∘ SND) progs ∧
     EVERY ((λy. raise_stub_location ≠ y) ∘ FST) progs ∧
     (n = 0 ⇒ bm0 = bitmaps)) (word_oracle n)) ∧
  stack_oracle =
  (λn.
   (λ((bm0,cfg),progs).
      (λ(progs,bm). (cfg,progs,DROP (LENGTH bm0) bm))
        (compile_word_to_stack
           kkk progs
           bm0)) (word_oracle n)) ∧
    (full_make_init sc dc max_heap stk stoff bitmaps p6 lab_st save_regs data_sp stack_oracle = (fmis,SOME xxx))
    ==>
    init_state_ok kkk fmis word_oracle`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_def] \\ strip_tac
  \\ every_case_tac \\ fs []
  \\ fs [init_state_ok_def,data_to_word_gcProofTheory.gc_fun_ok_word_gc_fun]
  \\ conj_tac THEN1 fs [labPropsTheory.good_dimindex_def]
  \\ qpat_x_assum`_ = fmis` sym_sub_tac \\ rveq\\ fs[]
  \\ `init_prop (is_gen_gc dc.gc_kind) max_heap data_sp x /\ x.bitmaps = 4w::t` by
        (fs [stack_removeProofTheory.make_init_opt_def]
         \\ every_case_tac \\ fs [stack_removeProofTheory.init_reduce_def] \\ rw [])
  \\ fs [stack_removeProofTheory.init_prop_def]
  \\ `x.stack <> []` by (rpt strip_tac \\ fs [])
  \\ `?t1 t2. x.stack = SNOC t1 t2` by metis_tac [SNOC_CASES]
  \\ fs [] \\ rpt var_eq_tac \\ fs[ADD1]
  \\ qpat_x_assum `LENGTH t2 = x.stack_space` (assume_tac o GSYM)
  \\ fs [DROP_LENGTH_APPEND] \\ fs [FLOOKUP_DEF] >>
  fs[data_to_word_gcProofTheory.gc_fun_ok_word_gc_fun] >>
  qhdtm_x_assum `make_init_opt` mp_tac>>
  simp[stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>fs[stack_removeProofTheory.init_reduce_def]>>rw[]>>fs[]);

val extend_with_resource_limit_not_fail = Q.store_thm("extend_with_resource_limit_not_fail",
  `x ∈ extend_with_resource_limit y ∧ Fail ∉ y ⇒ x ≠ Fail`,
  rw[extend_with_resource_limit_def] \\ metis_tac[])

val full_make_init_buffer = Q.prove(`
  (FST(full_make_init a b c d e f g h i j k)).code_buffer.buffer = [] ∧
  (FST(full_make_init a b c d e f g h i j k)).data_buffer.buffer = []`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
     stack_removeProofTheory.make_init_any_def] >>
  every_case_tac>>fs[]>>
  EVAL_TAC>>
  pop_assum mp_tac>>fs[stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>rw[]>>
  fs [stack_removeProofTheory.init_prop_def]);

val full_make_init_ffi = Q.prove(`
  (FST(full_make_init a b c d e f g h i j k)).ffi = h.ffi`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def] >>
  fs [stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC);

val full_make_init_compile = Q.store_thm("full_make_init_compile",
  `(FST(full_make_init a b c d e f g h i j k)).compile =
   (λc. (λp. h.compile c (MAP prog_to_section (MAP (prog_comp a.reg_names) (MAP (prog_comp a.jump e d) p)))) o MAP prog_comp)`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def]
  \\ simp[stack_removeProofTheory.make_init_any_def,
          stack_removeProofTheory.make_init_opt_def]
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac stackPropsTheory.evaluate_consts \\ fs[]
  \\ EVAL_TAC \\ fs[]
  \\ EVAL_TAC \\ fs[]);

(*
val full_make_init_ffi = Q.prove(
  `(full_make_init
         (bitmaps,c1,code,f,ggg,jump,k,max_heap,off,regs,
          make_init mc_conf ffi io_regs cc_regs t m dm ms code2 compiler cbpos cbspace coracle,
          save_regs)).ffi = ffi`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC);

val full_make_init_code =
  ``(^(full_make_init_def |> SPEC_ALL |> concl |> dest_eq |> fst)).code``
  |> SIMP_CONV (srw_ss()) [full_make_init_def,stack_allocProofTheory.make_init_def];

val args = full_make_init_semantics_fail |> concl |> dest_imp |> #1 |> dest_conj |> #1 |> rand
val defn = full_make_init_semantics_fail |> concl |> dest_imp |> #1 |> dest_conj |> #2 |> lhs
val full_init_pre_fail_def =
  Define`full_init_pre_fail ^args = ^defn`;

val full_make_init_bitmaps = Q.prove(
  `full_init_pre_fail args = SOME x ==>
    (full_make_init args).bitmaps = FST args`,
  PairCases_on`args` \\
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_bitmaps]
  \\ every_case_tac \\ fs [] \\ fs [full_init_pre_fail_def]);
*)

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

val DISJOINT_INTER = Q.store_thm("DISJOINT_INTER",
  `DISJOINT b c ⇒ DISJOINT (a ∩ b) (a ∩ c)`,
  rw[IN_DISJOINT] \\ metis_tac[]);

(* -- *)

(* TODO: should be defined in targetSem *)
(* CakeML code, bytes, and code buffer space, cspace, and FFI functions, ffi,
   are installed into the machine, mc_conf + ms
   r1 and r2 are the names of registers containing
   the first address of the CakeML heap and the first address past the CakeML stack
   i.e., the range of the data memory
*)
val installed_def = Define`
  installed bytes cbspace bitmaps data_sp ffi_names ffi (r1,r2) mc_conf ms ⇔
    ∃t m io_regs cc_regs bitmap_ptr bitmaps_dm.
      (*let bitmaps_dm = { w | bitmap_ptr <=+ w ∧ w <+ bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)} in*)
      let heap_stack_dm = { w | t.regs r1 <=+ w ∧ w <+ t.regs r2 } in
      good_init_state mc_conf ms ffi bytes cbspace t m (heap_stack_dm ∪ bitmaps_dm) io_regs cc_regs ∧
      DISJOINT heap_stack_dm bitmaps_dm ∧
      m (t.regs r1) = Word bitmap_ptr ∧
      m (t.regs r1 + bytes_in_word) =
        Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) ∧
      m (t.regs r1 + 2w * bytes_in_word) =
        Word (bitmap_ptr + bytes_in_word * n2w data_sp +
              bytes_in_word * n2w (LENGTH bitmaps)) ∧
      m (t.regs r1 + 3w * bytes_in_word) =
        Word (mc_conf.target.get_pc ms + n2w (LENGTH bytes)) ∧
      m (t.regs r1 + 4w * bytes_in_word) =
        Word (mc_conf.target.get_pc ms + n2w cbspace + n2w (LENGTH bytes)) ∧
      (word_list bitmap_ptr (MAP Word bitmaps) *
        word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp)
       (fun2set (m,byte_aligned ∩ bitmaps_dm)) ∧
      ffi_names = SOME mc_conf.ffi_names`;

val byte_aligned_MOD = Q.store_thm("byte_aligned_MOD",`
  good_dimindex (:'a) ⇒
  ∀x:'a word.x ∈ byte_aligned ⇒
  w2n x MOD (dimindex (:'a) DIV 8) = 0`,
  rw[IN_DEF]>>
  fs [stack_removeProofTheory.aligned_w2n, alignmentTheory.byte_aligned_def]>>
  rfs[labPropsTheory.good_dimindex_def] \\ rfs []);

val prim_config = prim_config_eq |> concl |> lhs

val backend_config_ok_def = Define`
  backend_config_ok (c:'a config) ⇔
    c.source_conf = ^prim_config.source_conf ∧
    0 < c.clos_conf.max_app ∧
    (case c.clos_conf.known_conf of SOME kcfg => kcfg.val_approx_spt = LN | _ => T) ∧
    c.bvl_conf.next_name2 = bvl_num_stubs + 2 ∧
    LENGTH c.lab_conf.asm_conf.avoid_regs + 13 ≤ c.lab_conf.asm_conf.reg_count ∧
    c.lab_conf.pos = 0 ∧
    c.lab_conf.labels = LN ∧
    conf_ok (:'a) c.data_conf ∧
    (c.data_conf.has_longdiv ⇒ c.lab_conf.asm_conf.ISA = x86_64) /\
    (c.data_conf.has_div ⇒
      c.lab_conf.asm_conf.ISA = ARMv8 ∨ c.lab_conf.asm_conf.ISA = MIPS ∨
      c.lab_conf.asm_conf.ISA = RISC_V) ∧
    addr_offset_ok c.lab_conf.asm_conf 0w ∧
    (∀w. -8w ≤ w ∧ w ≤ 8w ⇒ byte_offset_ok c.lab_conf.asm_conf w) ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 8w ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 4w ∧
    c.lab_conf.asm_conf.valid_imm (INL Add) 1w ∧
    c.lab_conf.asm_conf.valid_imm (INL Sub) 1w ∧
    find_name c.stack_conf.reg_names PERMUTES UNIV ∧
    names_ok c.stack_conf.reg_names c.lab_conf.asm_conf.reg_count c.lab_conf.asm_conf.avoid_regs ∧
    fixed_names c.stack_conf.reg_names c.lab_conf.asm_conf ∧
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

(* not true...
val encode_header_with_has_fp_ops = Q.store_thm("encode_header_with_has_fp_ops[simp]",
  `encode_header (c with has_fp_ops := x) = encode_header c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val tag_mask_with_has_fp_ops = Q.store_thm("tag_mask_with_has_fp_ops[simp]",
  `tag_mask (c with has_fp_ops := x) = tag_mask c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val ptr_bits_with_has_fp_ops = Q.store_thm("ptr_bits_with_has_fp_ops[simp]",
  `ptr_bits (c with has_fp_ops := x) = ptr_bits c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val Make_ptr_bits_code_with_has_fp_ops = Q.store_thm("Make_ptr_bits_code_with_has_fp_ops[simp]",
  `Make_ptr_bits_code (c with has_fp_ops := x) = Make_ptr_bits_code c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val small_shift_length_with_has_fp_ops = Q.store_thm("small_shift_length_with_has_fp_ops[simp]",
  `small_shift_length (c with has_fp_ops := x) = small_shift_length c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val real_addr_with_has_fp_ops = Q.store_thm("real_addr_with_has_fp_ops[simp]",
  `real_addr (c with has_fp_ops := x) = real_addr c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val real_offset_with_has_fp_ops = Q.store_thm("real_offset_with_has_fp_ops[simp]",
  `real_offset (c with has_fp_ops := x) = real_offset c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val bignum_words_with_has_fp_ops = Q.store_thm("bignum_words_with_has_fp_ops[simp]",
  `bignum_words (c with has_fp_ops := x) = bignum_words c`,
  rw[FUN_EQ_THM] \\ rw[data_to_wordTheory.bignum_words_def]);

val WriteWord64_on_32_with_has_fp_ops = Q.store_thm("WriteWord64_on_32_with_has_fp_ops[simp]",
  `WriteWord64_on_32 (c with has_fp_ops := x) = WriteWord64_on_32 c`,
  rw[FUN_EQ_THM] \\ EVAL_TAC);

val assign_with_has_fp_ops = Q.store_thm("assign_with_has_fp_ops",
  `assign (c with has_fp_ops := x) secn l dest op args names =
   assign c secn l dest op args names`,
  rw[data_to_wordTheory.assign_def] \\
  PURE_TOP_CASE_TAC \\ fsrw_tac[][]
*)

val backend_config_ok_call_empty_ffi = store_thm("backend_config_ok_call_empty_ffi[simp]",
  ``backend_config_ok (cc with
      data_conf updated_by (λc. c with call_empty_ffi updated_by x)) =
    backend_config_ok cc``,
  fs [backend_config_ok_def,data_to_wordTheory.conf_ok_def,
      data_to_wordTheory.shift_length_def]);

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

val FST_known_co = Q.store_thm("FST_known_co",
  `FST (known_co kc co n) = SND (FST (co n))`,
  rw[clos_knownProofTheory.known_co_def]
  \\ CASE_TAC
  \\ simp[backendPropsTheory.FST_state_co]);

val FST_prog_comp = Q.store_thm("FST_prog_comp[simp]",
  `FST (prog_comp jump off k pp) = FST pp`,
  Cases_on`pp` \\ EVAL_TAC);

val FST_prog_comp_TODO_move = Q.store_thm("FST_prog_comp_TODO_move[simp]",
  `FST (prog_comp pp) = FST pp`,
  Cases_on`pp` \\ EVAL_TAC);

val FST_compile_single = Q.store_thm("FST_compile_single[simp]",
  `FST (compile_single a b c d e) = FST (FST e)`,
  PairCases_on`e` \\ EVAL_TAC);

val FST_compile_part = Q.store_thm("FST_compile_part[simp]",
  `FST (compile_part a b) = (FST b)`,
  PairCases_on`b` \\ EVAL_TAC);

val FST_compile_part_TODO_move = Q.store_thm("FST_compile_part_TODO_move[simp]",
  `FST (compile_part a) = (FST a)`,
  PairCases_on`a` \\ EVAL_TAC);

val ALL_DISTINCT_MAP_FST_SND_full_co = Q.store_thm("ALL_DISTINCT_MAP_FST_SND_full_co",
  `ALL_DISTINCT (MAP FST (SND (co n))) ∧
   (FST (SND (SND (FST (co n)))) MOD bvl_to_bvi_namespaces = 2)
  ⇒
   ALL_DISTINCT (MAP FST (SND (full_co c co n)))`,
  rw[full_co_def, bvi_tailrecProofTheory.mk_co_def, UNCURRY, backendPropsTheory.FST_state_co]
  \\ qmatch_goalsub_abbrev_tac`bvi_tailrec$compile_prog m xs`
  \\ Cases_on`bvi_tailrec$compile_prog m xs`
  \\ drule bvi_tailrecProofTheory.compile_prog_ALL_DISTINCT
  \\ impl_tac
  >- (
    simp[Abbr`xs`]
    \\ simp[backendPropsTheory.SND_state_co, backendPropsTheory.FST_state_co]
    \\ qmatch_goalsub_abbrev_tac`bvl_to_bvi$compile_inc v p`
    \\ Cases_on`bvl_to_bvi$compile_inc v p`
    \\ drule bvl_to_bviProofTheory.compile_inc_DISTINCT
    \\ impl_tac
    >- (
      simp[Abbr`p`]
      \\ simp[bvl_inlineTheory.compile_inc_def, UNCURRY]
      \\ simp[bvl_inlineTheory.tick_compile_prog_def]
      \\ simp[bvl_inlineProofTheory.MAP_FST_tick_inline_all] )
    \\ rw[]
    \\ drule (GEN_ALL bvl_to_bviProofTheory.compile_inc_next_range)
    \\ simp[MEM_MAP, PULL_EXISTS, EVERY_o, EVERY_MEM, EXISTS_PROD]
    \\ rpt strip_tac
    \\ first_x_assum drule
    \\ simp[bvi_tailrecProofTheory.free_names_def]
    \\ rw[] \\ strip_tac \\ rw[]
    \\ qpat_x_assum`_ MOD _ = _`mp_tac
    \\ qpat_x_assum`_ MOD _ = _`mp_tac
    \\ EVAL_TAC \\ simp[] )
  \\ simp[]);

val compile_word_to_stack_lab_pres = Q.store_thm("compile_word_to_stack_lab_pres",
  `∀p b q r.
   compile_word_to_stack k p b = (q,r) ∧
   EVERY (λ(l,m,e).
     EVERY (λ(l1,l2). (l1 = l) ∧ (l2 ≠ 0)) (extract_labels e) ∧
     ALL_DISTINCT (extract_labels e)) p
   ⇒
   EVERY (λ(l,e).
     EVERY (λ(l1,l2). (l1 = l) ∧ (l2 ≠ 0)) (extract_labels e) ∧
     ALL_DISTINCT (extract_labels e)) q`,
  Induct
  \\ simp[word_to_stackTheory.compile_word_to_stack_def]
  \\ simp[FORALL_PROD]
  \\ rw[word_to_stackTheory.compile_word_to_stack_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rveq \\ simp[]
  \\ first_x_assum drule
  \\ simp[] \\ strip_tac
  \\ fs[Once word_to_stackTheory.compile_prog_def]
  \\ pairarg_tac \\ fs[] \\ rveq
  \\ EVAL_TAC \\ pop_assum mp_tac
  \\ specl_args_of_then``word_to_stack$comp``word_to_stackProofTheory.word_to_stack_lab_pres mp_tac
  \\ ntac 2 strip_tac \\ fs[]);

val compile_word_to_stack_convs = Q.store_thm("compile_word_to_stack_convs",
  `∀p bm q bm'.
   compile_word_to_stack k p bm = (q,bm') ∧
   EVERY (λ(n,m,p).
     full_inst_ok_less c p ∧
     (c.two_reg_arith ⇒ every_inst two_reg_inst p) ∧
     post_alloc_conventions k p) p ∧ 4 < k ∧ k + 1 < c.reg_count - LENGTH c.avoid_regs
   ⇒
   EVERY (λ(x,y).
     stack_asm_name c y ∧
     stack_asm_remove c y ∧
     alloc_arg y ∧
     reg_bound y (k+2) ∧
     call_args y 1 2 3 4 0) q`,
  Induct>>fs[FORALL_PROD,compile_word_to_stack_def]>>
  rpt strip_tac>>
  FULL_SIMP_TAC (srw_ss())[compile_prog_def]>>
  rpt(pairarg_tac \\ fs[]) \\ rveq
  \\ qmatch_asmsub_abbrev_tac`comp p_2 bm (k,f)`
  \\ Q.ISPECL_THEN[`p_2`,`bm`,`(k,f)`,`c`]mp_tac
        word_to_stackProofTheory.word_to_stack_stack_asm_name_lem
  \\ impl_tac >- fs[] \\ strip_tac
  \\ Q.ISPECL_THEN[`p_2`,`bm`,`(k,f)`,`c`]mp_tac
        word_to_stackProofTheory.word_to_stack_stack_asm_remove_lem
  \\ impl_tac >- fs[] \\ strip_tac
  \\ simp_tac(srw_ss())[]
  \\ simp_tac(srw_ss())[GSYM CONJ_ASSOC]
  \\ conj_tac >- (EVAL_TAC \\ rfs[] )
  \\ conj_tac >- (EVAL_TAC \\ rfs[] )
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_alloc_arg,FST])
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_reg_bound,FST,LESS_OR_EQ])
  \\ conj_tac >- (EVAL_TAC \\ metis_tac[word_to_stack_call_args,FST])
  \\ metis_tac[]);

val elist_globals_compile = Q.store_thm("elist_globals_compile",
  `∀ls.
      elist_globals (flat_to_pat$compile ls) ≤ elist_globals (MAP dest_Dlet (FILTER is_Dlet ls))`,
  recInduct flat_to_patTheory.compile_ind
  \\ rw[flat_to_patTheory.compile_def]
  \\ irule (List.nth(CONJUNCTS SUB_BAG_UNION, 6))
  \\ rw[]
  \\ rw[flat_to_patProofTheory.set_globals_eq]);

val get_labels_cons = Q.store_thm("get_labels_cons",
  `get_labels (x::xs) = sec_get_labels x ∪ get_labels xs`,
  rw[labPropsTheory.get_labels_def]);

val get_code_labels_cons = Q.store_thm("get_code_labels_cons",
  `get_code_labels (x::xs) = sec_get_code_labels x ∪ get_code_labels xs`,
  rw[labPropsTheory.get_code_labels_def]);

val get_code_labels_def = Define`
  (get_code_labels (Call r d h) =
    (case d of INL x => {(x,0n)} | _ => {}) ∪
    (case r of SOME (x,_,_) => get_code_labels x | _ => {}) ∪
    (case h of SOME (x,_,_) => get_code_labels x | _ => {})) ∧
  (get_code_labels (Seq p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (If _ _ _ p1 p2) = get_code_labels p1 ∪ get_code_labels p2) ∧
  (get_code_labels (While _ _ _ p) = get_code_labels p) ∧
  (get_code_labels (JumpLower _ _ t) = {(t,0)}) ∧
  (get_code_labels (LocValue _ l1 l2) = {(l1,l2)}) ∧
  (get_code_labels _ = {})`;
val _ = export_rewrites["get_code_labels_def"];

val _ = temp_overload_on("new_get_code_labels",``backendProof$get_code_labels``);

val flatten_labels = Q.store_thm("flatten_labels",
  `∀m n p l x y.
     flatten m n p = (l,x,y) ∧
     EVERY (sec_label_ok n) (append l)
     ⇒
     BIGUNION (IMAGE line_get_labels (set (append l))) ⊆
     sec_get_code_labels (Section n (append l)) ∪
     get_code_labels m`,
  recInduct stack_to_labTheory.flatten_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rw[Once stack_to_labTheory.flatten_def]
  \\ qabbrev_tac`XXX = debug p`
  \\ Cases_on`p` \\ fs[] \\ rveq
  \\ fs[labPropsTheory.line_get_labels_def,
        labPropsTheory.sec_get_code_labels_def]
  >- (
    fs[CaseEq"option",CaseEq"prod"]
    \\ rveq \\ fs[]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
      \\ EVAL_TAC \\ fs[] \\ rw[] )
    \\ rpt(pairarg_tac \\ fs[])
    \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
      \\ fs[labPropsTheory.line_get_labels_def,
            labPropsTheory.line_get_code_labels_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
      \\ metis_tac[] )
    \\ rpt(pairarg_tac \\ fs[])
    \\ rveq \\ fs[]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def]
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ metis_tac[] )
  \\ (
    rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS, FORALL_PROD]
    \\ fs[CaseEq"bool"] \\ rveq
    \\ fsrw_tac[DNF_ss][labPropsTheory.line_get_labels_def,
          labPropsTheory.line_get_code_labels_def]
    \\ metis_tac[] ));

val good_calls_def = Define`
  (good_calls (Call r d h) ⇔
     ¬(IS_NONE r ∧ IS_SOME h) ∧
    (case r of SOME (x,_,_) => good_calls x | _ => T) ∧
    (case h of SOME (x,_,_) => good_calls x | _ => T)) ∧
  (good_calls (Seq p1 p2) ⇔ good_calls p1 ∧ good_calls p2) ∧
  (good_calls (If _ _ _ p1 p2) ⇔ good_calls p1 ∧ good_calls p2) ∧
  (good_calls (While _ _ _ p) ⇔ good_calls p) ∧
  (good_calls _ ⇔ T)`;
val _ = export_rewrites["good_calls_def"];

(* this is probably useless *)
val flatten_preserves_labels = Q.store_thm("flatten_preserves_labels",
  `∀m n p l x y.
   flatten m n p = (l,x,y) ∧
   good_calls m
   ⇒
   get_code_labels m ⊆
     sec_get_labels (Section n (append l))`,
  recInduct stack_to_labTheory.flatten_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rw[Once stack_to_labTheory.flatten_def]
  \\ qabbrev_tac`XXX = FOO p`
  \\ simp[labPropsTheory.sec_get_labels_def]
  \\ Cases_on`p` \\ fs[] \\ rveq \\ fs[]
  >- (
    fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_labels_def, labPropsTheory.sec_get_labels_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS] )
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_labels_def, labPropsTheory.sec_get_labels_def]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_labels_def, labPropsTheory.sec_get_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS] )
  >- (
    fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_labels_def, labPropsTheory.sec_get_labels_def]
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_labels_def, labPropsTheory.sec_get_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fsrw_tac[DNF_ss][]
    \\ fs[labPropsTheory.line_get_labels_def, labPropsTheory.sec_get_labels_def] )
  \\ (
    rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[SUBSET_DEF, PULL_EXISTS, CaseEq"bool"] \\ rveq
    \\ fs[labPropsTheory.line_get_labels_def, labPropsTheory.sec_get_labels_def]
    \\ metis_tac[] ));

val MAP_prog_to_section_preserves_labels = Q.store_thm("MAP_prog_to_section_preserves_labels",
  `∀p.
    EVERY good_calls (MAP SND p) ⇒
    BIGUNION (IMAGE get_code_labels (set (MAP SND p))) ⊆
    get_labels (MAP prog_to_section p)`,
  Induct \\ simp[FORALL_PROD]
  \\ simp[stack_to_labTheory.prog_to_section_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs[]
  \\ simp[get_labels_cons, labPropsTheory.sec_get_labels_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, FORALL_PROD] \\ rw[]
  \\ drule flatten_preserves_labels
  \\ rw[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, FORALL_PROD]
  \\ first_x_assum drule
  \\ rw[labPropsTheory.sec_get_labels_def]
  \\ metis_tac[]);

val stack_get_handler_labels_def = Define`
  (stack_get_handler_labels n (Call r d h) =
    (case r of SOME (x,_,_) => stack_get_handler_labels n x  ∪
      (case h of SOME (x,l1,l2) => (if l1 = n then {(l1,l2)} else {}) ∪ (stack_get_handler_labels n x) | _ => {})
    | _ => {})
  ) ∧
  (stack_get_handler_labels n (Seq p1 p2) = stack_get_handler_labels n p1 ∪ stack_get_handler_labels n p2) ∧
  (stack_get_handler_labels n (If _ _ _ p1 p2) = stack_get_handler_labels n p1 ∪ stack_get_handler_labels n p2) ∧
  (stack_get_handler_labels n (While _ _ _ p) = stack_get_handler_labels n p) ∧
  (stack_get_handler_labels n _ = {})`;
val _ = export_rewrites["stack_get_handler_labels_def"];

val flatten_preserves_handler_labels = Q.store_thm("flatten_preserves_handler_labels",
  `∀m n p l x y.
   flatten m n p = (l,x,y)
   ⇒
   stack_get_handler_labels n m ⊆
     sec_get_code_labels (Section n (append l))`,
  recInduct stack_to_labTheory.flatten_ind
  \\ rpt gen_tac \\ strip_tac
  \\ rw[Once stack_to_labTheory.flatten_def]
  \\ qabbrev_tac`XXX = FOO p`
  \\ simp[labPropsTheory.sec_get_code_labels_def]
  \\ Cases_on`p` \\ fs[] \\ rveq \\ fs[stack_get_handler_labels_def]
  >- (
    fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    >- (
      Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
      \\ fs[SUBSET_DEF, PULL_EXISTS]
      \\ metis_tac[] )
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ rw[] \\ TRY(metis_tac[]))
  (* >- (
    fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
    \\ Cases_on`s` \\ fs[stack_to_labTheory.compile_jump_def, labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ fs[SUBSET_DEF, PULL_EXISTS]
    \\ fsrw_tac[DNF_ss][]
    \\ fs[labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def]
    \\ metis_tac[]) *)
  \\ (
    rpt (pairarg_tac \\ fs[]) \\ rveq
    \\ fs[SUBSET_DEF, PULL_EXISTS, CaseEq"bool"] \\ rveq
    \\ fs[labPropsTheory.line_get_code_labels_def, labPropsTheory.sec_get_code_labels_def,stack_get_handler_labels_def]
    \\ metis_tac[] ));

val MAP_prog_to_section_preserves_handler_labels = Q.store_thm("MAP_prog_to_section_preserves_handler_labels",
  `∀p.
    BIGUNION (set (MAP (λ(n,pp). stack_get_handler_labels n pp) p)) ⊆
    get_code_labels (MAP prog_to_section p)`,
  Induct \\ simp[FORALL_PROD]
  \\ simp[stack_to_labTheory.prog_to_section_def]
  \\ rpt gen_tac
  \\ pairarg_tac \\ fs[]
  \\ simp[get_code_labels_cons, labPropsTheory.sec_get_code_labels_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, FORALL_PROD] \\ rw[]
  \\ drule flatten_preserves_handler_labels
  \\ rw[SUBSET_DEF, PULL_EXISTS, EXISTS_PROD, FORALL_PROD]
  \\ first_x_assum drule
  \\ rw[labPropsTheory.sec_get_code_labels_def]
  \\ metis_tac[]);

val prog_to_section_preserves_MAP_FST = Q.prove(`
    ∀p.
    IMAGE (λn. n,0) (set (MAP FST p)) ⊆
    get_code_labels (MAP prog_to_section p)`,
    Induct>>
    fs[get_code_labels_cons,FORALL_PROD,stack_to_labTheory.prog_to_section_def]>>
    rw[]>> rpt(pairarg_tac>>fs[])>>
    simp[get_code_labels_cons, labPropsTheory.sec_get_code_labels_def]>>
    fs[SUBSET_DEF]);

val get_labels_MAP_prog_to_section_SUBSET_code_labels = Q.store_thm("get_labels_MAP_prog_to_section_SUBSET_code_labels",
  `∀p. EVERY sec_labels_ok (MAP prog_to_section p) ⇒
    get_labels (MAP prog_to_section p) ⊆
    get_code_labels (MAP prog_to_section p) ∪
    BIGUNION (IMAGE get_code_labels (set (MAP SND p)))`,
  Induct \\ simp[FORALL_PROD] >- (EVAL_TAC \\ simp[])
  \\ rw[stack_to_labTheory.prog_to_section_def]
  \\ pairarg_tac \\ fs[get_labels_cons, get_code_labels_cons]
  \\ simp[labPropsTheory.sec_get_labels_def, labPropsTheory.sec_get_code_labels_def]
  \\ fs[SUBSET_DEF, PULL_EXISTS]
  \\ simp[labPropsTheory.line_get_labels_def]
  \\ qmatch_asmsub_abbrev_tac`flatten q n z`
  \\ qspecl_then[`q`,`n`,`z`]mp_tac flatten_labels
  \\ simp[]
  \\ simp[SUBSET_DEF, PULL_EXISTS, labPropsTheory.sec_get_code_labels_def]
  \\ rw[] \\ first_x_assum drule \\ rw[]
  \\ metis_tac[]);

val stack_good_code_labels_def = Define`
  stack_good_code_labels p ⇔
  BIGUNION (IMAGE get_code_labels (set (MAP SND p))) ⊆
  BIGUNION (set (MAP (λ(n,pp). stack_get_handler_labels n pp) p)) ∪
  IMAGE (λn. n,0) (set (MAP FST p))
`

val get_labels_MAP_prog_to_section_SUBSET_code_labels_TODO = Q.store_thm("get_labels_MAP_prog_to_section_SUBSET_code_labels_TODO",
`∀p. EVERY sec_labels_ok (MAP prog_to_section p) ∧
    stack_good_code_labels p
   ⇒
    get_labels (MAP prog_to_section p) ⊆
    get_code_labels (MAP prog_to_section p)`,
  rw[stack_good_code_labels_def]>>
  drule get_labels_MAP_prog_to_section_SUBSET_code_labels>>
  strip_tac >> match_mp_tac SUBSET_TRANS>>
  asm_exists_tac>> simp[]>>
  match_mp_tac SUBSET_TRANS>>
  asm_exists_tac>> rw[]>>
  metis_tac[MAP_prog_to_section_preserves_handler_labels,prog_to_section_preserves_MAP_FST]);

(* moving stackLang syntactic invariant across stackLang passes *)

(* stack_names *)
val get_code_labels_comp = Q.prove(
  `!f p. get_code_labels (comp f p) = get_code_labels p`,
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs [get_code_labels_def]
  \\ every_case_tac \\ fs [] \\
  fs[stack_namesTheory.dest_find_name_def]);

val stack_get_handler_labels_comp = Q.prove(`
  !f p n.
  stack_get_handler_labels n (comp f p) =
  stack_get_handler_labels n p`,
  HO_MATCH_MP_TAC stack_namesTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_namesTheory.comp_def] \\ fs [stack_get_handler_labels_def]
  \\ every_case_tac \\ fs [] \\
  fs[stack_namesTheory.dest_find_name_def]);

val UNCURRY_PAIR_ETA = Q.prove(`
  UNCURRY f = λ(p1,p2). f p1 p2`,
  fs[FUN_EQ_THM]);

val stack_names_stack_good_code_labels = Q.prove(`
  ∀prog f. stack_good_code_labels prog ⇒
  stack_good_code_labels (stack_names$compile f prog)`,
  EVAL_TAC>>rw[]>>
  fs[GSYM LIST_TO_SET_MAP]>>
  fs[MAP_MAP_o,o_DEF,stack_namesTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
  fs[stack_get_handler_labels_comp,get_code_labels_comp]>>
  fs[UNCURRY_PAIR_ETA]);

(* stack_remove *)
val get_code_labels_comp = Q.prove(
  `!a b c p.
  get_code_labels (comp a b c p) SUBSET (stack_err_lab,0) INSERT get_code_labels p`,
  HO_MATCH_MP_TAC stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_removeTheory.comp_def]
  \\ rw[] \\ fs [get_code_labels_def,stackLangTheory.list_Seq_def]
  \\ every_case_tac \\ fs [] \\
  TRY(rw[]>>match_mp_tac SUBSET_TRANS>> asm_exists_tac>>fs[]>>
  metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS])
  >- (
    completeInduct_on`n`>>
    ONCE_REWRITE_TAC [stack_removeTheory.stack_alloc_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_alloc_def]>>rw[]>>
    fs[get_code_labels_def]>>rw[]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]>>
    rw[]>>EVAL_TAC)
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    completeInduct_on`n`>>simp[Once stack_removeTheory.stack_free_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_free_def,get_code_labels_def]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_store_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    match_mp_tac SUBSET_TRANS >> qexists_tac`{}` >>fs[] >>
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_load_def]>>
    rw[get_code_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[get_code_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]));

val stack_get_handler_labels_comp = Q.prove(
  `!a b c p m.
  stack_get_handler_labels m (comp a b c p) =
  stack_get_handler_labels m p`,
  HO_MATCH_MP_TAC stack_removeTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_removeTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def]
  \\ every_case_tac \\ fs []
  >- (
    completeInduct_on`n`>>
    ONCE_REWRITE_TAC [stack_removeTheory.stack_alloc_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_alloc_def]>>rw[]>>
    fs[stack_get_handler_labels_def]>>rw[]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]>>
    rw[]>>EVAL_TAC)
  >- (
    completeInduct_on`n`>>simp[Once stack_removeTheory.stack_free_def]>>
    rw[]>>fs[stack_removeTheory.single_stack_free_def,stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_store_def]>>
    rw[stack_get_handler_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def])
  >- (
    pop_assum kall_tac>>
    simp[Once stack_removeTheory.stack_load_def]>>
    rw[stack_get_handler_labels_def]>>
    completeInduct_on`n0`>>simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
    rw[]>>fs[stack_get_handler_labels_def]>>
    first_x_assum(qspec_then`n0-max_stack_alloc` mp_tac)>>
    fs[stack_removeTheory.max_stack_alloc_def]));

val init_code_labels = Q.prove(`
  x ∈ get_code_labels (init_code ggc mh sp) ⇒ x = (1n,0n)`,
  rpt(EVAL_TAC>>rw[]>>fs[]));

val stack_remove_stack_good_code_labels = Q.prove(`
  ∀prog.
  MEM loc (MAP FST prog) ∧
  stack_good_code_labels prog ⇒
  stack_good_code_labels (stack_remove$compile jump off ggc mh sp loc prog)`,
  rw[]>>
  simp[stack_removeTheory.compile_def]>>
  fs[stack_good_code_labels_def]>>rw[]
  >- (
    fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF]>>
    simp[SUBSET_DEF,stack_removeTheory.init_stubs_def,PULL_EXISTS]>>
    fs[get_code_labels_def,stack_removeTheory.halt_inst_def]>>
    rw[]>>fs[]
    >-
      metis_tac[init_code_labels]
    >>
      fs[MEM_MAP,EXISTS_PROD]>>metis_tac[])
  >>
    fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,stack_removeTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
    simp[stack_get_handler_labels_comp]>>
    fs[SUBSET_DEF,MEM_MAP,PULL_EXISTS,UNCURRY]>> rw[]>>
    drule (get_code_labels_comp |> SIMP_RULE std_ss [SUBSET_DEF])>>
    rw[]
    >-
      fs[stack_removeTheory.init_stubs_def,stack_removeTheory.stack_err_lab_def,EXISTS_PROD]
    >>
      metis_tac[]);

(* stack_alloc *)
val get_code_labels_comp = Q.prove(`
  !n m p pp mm.
  get_code_labels (FST (comp n m p)) ⊆ (gc_stub_location,0) INSERT get_code_labels p`,
  HO_MATCH_MP_TAC stack_allocTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_allocTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def]
  \\ every_case_tac \\ fs []
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[SUBSET_DEF]>>metis_tac[]);

val stack_get_handler_labels_comp = Q.prove(`
  !n m p pp mm.
  stack_get_handler_labels i (FST (comp n m p)) = stack_get_handler_labels i p`,
  HO_MATCH_MP_TAC stack_allocTheory.comp_ind \\ rw []
  \\ Cases_on `p` \\ once_rewrite_tac [stack_allocTheory.comp_def]
  \\ rw[] \\ fs [stack_get_handler_labels_def,stackLangTheory.list_Seq_def]
  \\ every_case_tac \\ fs []
  \\ rpt(pairarg_tac \\ fs[stack_get_handler_labels_def])
  \\ fs[stack_get_handler_labels_def]);

val init_code_labels = Q.prove(`
  get_code_labels (word_gc_code c) = {}`,
  simp[stack_allocTheory.word_gc_code_def]>>
  EVAL_TAC>>
  EVERY_CASE_TAC>>fs[]>>
  rpt(EVAL_TAC>>rw[]>>fs[]));

val stack_alloc_stack_good_code_labels = Q.prove(`
  ∀prog c.
  stack_good_code_labels prog ⇒
  stack_good_code_labels (stack_alloc$compile c prog)`,
  simp[stack_allocTheory.compile_def]>>
  fs[stack_good_code_labels_def]>>rw[]
  >- (
    fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF]>>
    simp[SUBSET_DEF,stack_allocTheory.stubs_def,PULL_EXISTS]>>
    simp[init_code_labels])
  >>
    fs[GSYM LIST_TO_SET_MAP,MAP_MAP_o,o_DEF,stack_allocTheory.prog_comp_def,UNCURRY,LAMBDA_PROD]>>
    simp[stack_get_handler_labels_comp]>>
    fs[SUBSET_DEF,MEM_MAP,PULL_EXISTS,UNCURRY]>> rw[]>>
    drule (get_code_labels_comp |> SIMP_RULE std_ss [SUBSET_DEF])>>
    rw[]
    >-
      fs[stack_allocTheory.stubs_def]
    >>
      metis_tac[]);

(* stack_to_lab *)
val stack_to_lab_stack_good_code_labels = Q.store_thm("stack_to_lab_stack_good_code_labels",`
  compile stack_conf data_conf max_heap sp offset prog = prog' ∧
  MEM InitGlobals_location (MAP FST prog) ∧
  stack_good_code_labels prog ∧
  EVERY sec_labels_ok  prog' ⇒
  get_labels prog' ⊆ get_code_labels prog'`,
  rw[stack_to_labTheory.compile_def]>>
  match_mp_tac get_labels_MAP_prog_to_section_SUBSET_code_labels_TODO>>
  simp[]>>
  match_mp_tac stack_names_stack_good_code_labels>>
  match_mp_tac stack_remove_stack_good_code_labels>>
  rw[]
  >- (
    simp[stack_allocTheory.compile_def,MAP_MAP_o,UNCURRY,o_DEF,LAMBDA_PROD]>>
    fs[MEM_MAP,EXISTS_PROD]>>
    metis_tac[])
  >>
  match_mp_tac stack_alloc_stack_good_code_labels>>
  fs[]);

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
  BIGUNION (IMAGE new_get_code_labels (set (MAP SND p'))) ⊆
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
  rw[assign_def,assign_get_code_label_def]>>
  fs[list_Seq_def,word_get_code_labels_StoreEach,word_get_code_labels_MemEqList]>>
  rpt(every_case_tac>>fs[]>>
  fs[list_Seq_def,word_get_code_labels_StoreEach,word_get_code_labels_MemEqList]>>
  EVAL_TAC));

val data_to_word_comp_code_labels = Q.prove(`
  ∀c secn l p.
  word_get_code_labels ((FST (comp c secn l p)):'a prog) SUBSET
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
  rw[assign_def]>>
  rpt(
  every_case_tac>>fs[list_Seq_def,word_good_handlers_StoreEach,word_good_handlers_MemEqList]>>
  rw[]>>EVAL_TAC
  ));

val data_to_word_comp_good_handlers = Q.prove(`
  ∀c secn l p.
  word_good_handlers secn ((FST (comp c secn l p)):'a prog)`,
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

val bvl_get_code_labels_def = tDefine"bvl_get_code_labels"
  `(bvl_get_code_labels (Var _) = {}) ∧
   (bvl_get_code_labels (If e1 e2 e3) = bvl_get_code_labels e1 ∪ bvl_get_code_labels e2 ∪ bvl_get_code_labels e3) ∧
   (bvl_get_code_labels (Let es e) = BIGUNION (set (MAP bvl_get_code_labels es)) ∪ bvl_get_code_labels e) ∧
   (bvl_get_code_labels (Raise e) = bvl_get_code_labels e) ∧
   (bvl_get_code_labels (Handle e1 e2) = bvl_get_code_labels e1 ∪ bvl_get_code_labels e2) ∧
   (bvl_get_code_labels (Tick e) = bvl_get_code_labels e) ∧
   (bvl_get_code_labels (Call _ d es) = (case d of NONE => {} | SOME n => {n}) ∪ BIGUNION (set (MAP bvl_get_code_labels es))) ∧
   (bvl_get_code_labels (Op _ es) = BIGUNION (set (MAP bvl_get_code_labels es)))`
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
   (bvi_get_code_labels (Op _ es) = BIGUNION (set (MAP bvi_get_code_labels es)))`
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
  \\ cheat);

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

(* TODO: move to flat_to_patProof, and rename the other one to compile_exp... *)
val compile_esgc_free = Q.store_thm("compile_esgc_free",
  `∀p. EVERY (esgc_free o dest_Dlet) (FILTER is_Dlet p) ⇒
    EVERY esgc_free (flat_to_pat$compile p)`,
  recInduct flat_to_patTheory.compile_ind
  \\ rw[flat_to_patTheory.compile_def]
  \\ irule (CONJUNCT1 flat_to_patProofTheory.compile_esgc_free)
  \\ rw[]);

val set_globals_make_varls = Q.store_thm("set_globals_make_varls",
  `∀a b c d. set_globals (make_varls a b c d) =
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

val compile_prog_keeps_names = Q.store_thm("compile_prog_keeps_names",
  `∀next xs next' ys. compile_prog next xs = (next',ys) ∧ MEM x (MAP FST xs) ⇒ MEM x (MAP FST ys)`,
  recInduct bvi_tailrecTheory.compile_prog_ind
  \\ rw[bvi_tailrecTheory.compile_prog_def]
  \\ rpt(pairarg_tac \\ fs[])
  \\ fs[CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]);

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
    \\ `syntax_ok e3`
    by (
      simp[Abbr`e3`, Abbr`p''`]
      \\ ho_match_mp_tac clos_mtiProofTheory.syntax_ok_MAP
      \\ rw [syntax_ok_pat_to_clos] )
    \\ conj_tac
    >- ( simp[Abbr`e3`, Abbr`p''`] \\ strip_tac \\ EVAL_TAC)
    \\ conj_tac
    >- (
      strip_tac
      \\ conj_tac
      >- ( fs[IS_SOME_EXISTS] \\ fs[backend_config_ok_def] )
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
        \\ irule flat_elimProofTheory.removeFlatProg_distinct_globals
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
  `∀k. SND (co k) = [(num_stubs cf.max_app, 0, Op (Const (&TODO_co1)) [])]` by (
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
      \\ simp[clos_to_bvlProofTheory.compile_inc_def]
      \\ simp[clos_to_bvlProofTheory.extract_name_def]
      \\ simp[clos_to_bvlTheory.chain_exps_def]
      \\ simp[clos_to_bvlTheory.compile_prog_def, clos_to_bvlTheory.compile_exps_def] ) \\
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

  \\ impl_keep_tac >- (
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
        \\ cheat (* referenced labels are present (for oracle) *) )
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
      simp[]>>Cases>> simp[])
    >- (
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

      \\ cheat (* referenced labels are present *)))>>
  strip_tac \\
  qpat_x_assum`Abbrev(stack_st_opt = _)`(mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) \\
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
    conj_tac >- (
      rfs[memory_assumption_def,Abbr`dm`]
      \\ qmatch_goalsub_abbrev_tac`a <=+ b` >>
      `(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8` by
       rfs [labPropsTheory.good_dimindex_def,bytes_in_word_def,dimword_def]>>
      fs [attach_bitmaps_def] \\
      once_rewrite_tac[INTER_COMM] \\
      rewrite_tac[UNION_OVER_INTER] \\
      once_rewrite_tac[UNION_COMM] \\
      strip_tac \\
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
        \\ `a <=+ b` by metis_tac[WORD_LOWER_IMP_LOWER_OR_EQ]
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
        \\ fs [stack_removeProofTheory.aligned_w2n]
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

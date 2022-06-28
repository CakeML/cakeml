(*
  Composes the correctness theorems for all of the compiler phases.
*)
open preamble primSemEnvTheory semanticsPropsTheory
     backendTheory
     source_to_sourceProofTheory
     source_to_flatProofTheory
     flat_to_closProofTheory
     clos_to_bvlProofTheory
     bvl_to_bviProofTheory
     bvi_to_dataProofTheory
     data_to_wordProofTheory
     word_to_stackProofTheory
     stack_to_labProofTheory
     lab_to_targetProofTheory
     backend_commonTheory
     backendPropsTheory
local open dataPropsTheory finite_mapSyntax in end
open word_to_stackTheory

val _ = new_theory"backendProof";

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = Parse.set_grammar_ancestry
  [ "backend", "backend_common", "backendProps",
    "primSemEnv", "semanticsProps",
    "labProps", (* for good_dimindex *)
    "source_evalProof" (* for compiler instance structure *)
  ];

(* TODO: move/rephrase *)

Theorem byte_aligned_mult:
   good_dimindex (:'a) ==>
    byte_aligned (a + bytes_in_word * n2w i) = byte_aligned (a:'a word)
Proof
  fs [alignmentTheory.byte_aligned_def,labPropsTheory.good_dimindex_def]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM (EVAL ``2n**2``),GSYM (EVAL ``2n**3``), aligned_add_pow]
QED

Theorem byte_aligned_MOD:
    good_dimindex (:'a) ⇒
  ∀x:'a word.x ∈ byte_aligned ⇒
  w2n x MOD (dimindex (:'a) DIV 8) = 0
Proof
  rw[IN_DEF]>>
  fs [aligned_w2n, alignmentTheory.byte_aligned_def]>>
  rfs[labPropsTheory.good_dimindex_def] \\ rfs []
QED

(* -- *)

Theorem backend_upper_w2w[simp]:
  backend$upper_w2w = data_to_word_gcProof$upper_w2w
Proof
  fs [backendTheory.upper_w2w_def, data_to_word_gcProofTheory.upper_w2w_def, FUN_EQ_THM]
QED

val backend_config_ok_def = Define`
  backend_config_ok (c:'a config) ⇔
    c.source_conf = prim_src_config ∧
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
    (c.data_conf.has_fp_tern ⇔
        c.lab_conf.asm_conf.ISA = ARMv7 ∧ 2 < c.lab_conf.asm_conf.fp_reg_count) ∧
    (c.data_conf.has_fp_ops ⇔ 1 < c.lab_conf.asm_conf.fp_reg_count) ∧
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

Theorem backend_config_ok_with_bvl_conf_updated[simp]:
   (f cc.bvl_conf).next_name2 = cc.bvl_conf.next_name2 ⇒
   (backend_config_ok (cc with bvl_conf updated_by f) ⇔ backend_config_ok cc)
Proof
  rw[backend_config_ok_def]
QED

Theorem backend_config_ok_with_word_to_word_conf_updated[simp]:
   backend_config_ok (cc with word_to_word_conf updated_by f) ⇔ backend_config_ok cc
Proof
  rw[backend_config_ok_def]
QED

Theorem backend_config_ok_call_empty_ffi[simp]:
   backend_config_ok (cc with
      data_conf updated_by (λc. c with call_empty_ffi updated_by x)) =
    backend_config_ok cc
Proof
  fs [backend_config_ok_def,data_to_wordTheory.conf_ok_def,
      data_to_wordTheory.shift_length_def,
      data_to_wordTheory.max_heap_limit_def]
QED

val mc_init_ok_def = Define`
  mc_init_ok c mc ⇔
  EVERY (λr. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] ∧
  find_name c.stack_conf.reg_names 4 = mc.len2_reg ∧
  find_name c.stack_conf.reg_names 3 = mc.ptr2_reg ∧
  find_name c.stack_conf.reg_names 2 = mc.len_reg ∧
  find_name c.stack_conf.reg_names 1 = mc.ptr_reg ∧
  find_name c.stack_conf.reg_names 0 =
    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ∧
  c.data_conf.be = mc.target.config.big_endian ∧
  (* the next four are implied by injectivity of find_name *)
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len2_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr2_reg ∧
  ¬MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs ∧
   c.lab_conf.asm_conf = mc.target.config`

Theorem mc_init_ok_with_bvl_conf_updated[simp]:
   mc_init_ok (cc with bvl_conf updated_by f) mc ⇔ mc_init_ok cc mc
Proof
  rw[mc_init_ok_def]
QED

Theorem mc_init_ok_with_word_to_word_conf_updated[simp]:
   mc_init_ok (cc with word_to_word_conf updated_by f) mc ⇔ mc_init_ok cc mc
Proof
  rw[mc_init_ok_def]
QED

Theorem mc_init_ok_with_clos_conf_updated[simp]:
   mc_init_ok (cc with clos_conf updated_by f) mc ⇔ mc_init_ok cc mc
Proof
  rw[mc_init_ok_def]
QED

Theorem mc_init_ok_call_empty_ffi[simp]:
   mc_init_ok (cc with
      data_conf updated_by (λc. c with call_empty_ffi updated_by x)) =
    mc_init_ok cc
Proof
  fs [mc_init_ok_def,data_to_wordTheory.conf_ok_def,
      data_to_wordTheory.shift_length_def,FUN_EQ_THM]
QED

val heap_regs_def = Define`
  heap_regs reg_names =
    (find_name reg_names 2, find_name reg_names 4)`;

Overload bvl_inline_compile_prog[local] = ``bvl_inline$compile_prog``
Overload bvi_tailrec_compile_prog[local] = ``bvi_tailrec$compile_prog``
Overload bvi_to_data_compile_prog[local] = ``bvi_to_data$compile_prog``
Overload bvl_to_bvi_compile_prog[local] = ``bvl_to_bvi$compile_prog``
Overload bvl_to_bvi_compile_inc[local] = ``bvl_to_bvi$compile_inc``
Overload bvl_to_bvi_compile[local] = ``bvl_to_bvi$compile``
Overload bvi_to_data_compile[local] = ``bvi_to_data$compile``
Overload bvi_let_compile[local] = ``bvi_let$compile``
Overload bvl_const_compile[local] = ``bvl_const$compile``
Overload bvl_handle_compile[local] = ``bvl_handle$compile``
Overload bvl_inline_compile_inc[local] = ``bvl_inline$compile_inc``
Overload bvl_to_bvi_compile_exps[local] = ``bvl_to_bvi$compile_exps``
Overload flat_to_clos_inc_compile[local] = ``flat_to_clos$inc_compile_decs``
Overload stack_remove_prog_comp[local] = ``stack_remove$prog_comp``
Overload stack_alloc_prog_comp[local] = ``stack_alloc$prog_comp``
Overload stack_names_prog_comp[local] = ``stack_names$prog_comp``

(* TODO: remove when theorems are moved *)
Overload obeys_max_app[local] = ``closProps$obeys_max_app``
Overload no_Labels[local] = ``closProps$no_Labels``
Overload every_Fn_SOME[local] = ``closProps$every_Fn_SOME``
Overload code_locs[local] = ``closProps$code_locs``
Overload no_mti[local] = ``closProps$no_mti``

Theorem no_mti_IMP_obeys_max_app:
  !m exp. 0 < m /\ no_mti exp ==> obeys_max_app m exp
Proof
  ho_match_mp_tac closPropsTheory.obeys_max_app_ind
  \\ rpt conj_tac
  \\ simp [closPropsTheory.no_mti_def, ETA_THM]
  \\ rw [EVERY_MAP]
  \\ fs [EVERY_MEM, FORALL_PROD, MEM_MAP, PULL_EXISTS]
  \\ rw []
  \\ res_tac
QED

Theorem EVERY_no_mti_IMP_obeys_max_app:
  !e3. 0 < m /\ EVERY no_mti exps ==> EVERY (obeys_max_app m) exps
Proof
  metis_tac [EVERY_MONOTONIC, no_mti_IMP_obeys_max_app]
QED

(* TODO: move these *)
Theorem compile_common_syntax:
   !cf e3 cf1 e4.
      clos_to_bvl$compile_common cf e3 = (cf1,e4) ==>
      (EVERY no_Labels e3 ==>
       EVERY no_Labels (MAP (SND o SND) e4)) /\
      (0 < cf.max_app /\ EVERY no_mti e3 ==>
       EVERY (obeys_max_app cf.max_app) (MAP (SND o SND) e4)) /\
      every_Fn_SOME (MAP (SND o SND) e4)
Proof
  fs [clos_to_bvlTheory.compile_common_def]
  \\ rpt gen_tac \\ rpt (pairarg_tac \\ fs [])
  \\ strip_tac \\ rveq \\ fs [] \\ rw []
  THEN1 (* no_Labels *)
   (old_drule (clos_numberProofTheory.renumber_code_locs_no_Labels |> CONJUNCT1)
    \\ impl_tac THEN1
     (Cases_on `cf.do_mti` \\ fs [clos_mtiTheory.compile_def]
      \\ fs [clos_mtiProofTheory.intro_multi_no_Labels])
    \\ strip_tac
    \\ `EVERY no_Labels es'` by
      (Cases_on `cf.known_conf` THEN1 (fs [clos_knownTheory.compile_def] \\ rfs [])
       \\ old_drule clos_knownProofTheory.compile_no_Labels
       \\ fs [clos_knownTheory.compile_def] \\ rw [] \\ fs [])
    \\ Cases_on `cf.do_call` \\ fs [clos_callTheory.compile_def] \\ rveq \\ fs []
    \\ TRY pairarg_tac \\ fs [] \\ rveq
    \\ TRY (old_drule clos_callProofTheory.calls_no_Labels
            \\ (impl_tac THEN1 (fs [] \\ EVAL_TAC) \\ rw []))
    \\ match_mp_tac clos_annotateProofTheory.no_Labels_ann
    \\ fs [clos_callProofTheory.state_syntax_def]
    \\ rw [] \\ TRY (match_mp_tac clos_to_bvlProofTheory.chain_exps_no_Labels \\ fs [])
    \\ fs [EVERY_MEM,FORALL_PROD,MEM_MAP,PULL_EXISTS]
    \\ rw [] \\ res_tac \\ fs [])
  THEN1 (* obeys_max_app *)
   (drule (clos_numberProofTheory.renumber_code_locs_obeys_max_app
           |> CONJUNCT1 |> GEN_ALL)
    \\ disch_then (qspec_then `cf.max_app` mp_tac)
    \\ impl_tac THEN1
     (Cases_on `cf.do_mti` \\ fs [clos_mtiTheory.compile_def]
      \\ fs [clos_mtiProofTheory.intro_multi_obeys_max_app]
      \\ simp [EVERY_no_mti_IMP_obeys_max_app])
    \\ strip_tac
    \\ `EVERY (obeys_max_app cf.max_app) es'` by
      (Cases_on `cf.known_conf` THEN1 (fs [clos_knownTheory.compile_def] \\ rfs [])
       \\ old_drule (GEN_ALL clos_knownProofTheory.compile_obeys_max_app)
       \\ disch_then (qspec_then `cf.max_app` mp_tac)
       \\ fs [clos_knownTheory.compile_def] \\ rw [] \\ fs [])
    \\ Cases_on `cf.do_call` \\ fs [clos_callTheory.compile_def] \\ rveq \\ fs []
    \\ TRY pairarg_tac \\ fs [] \\ rveq
    \\ TRY (old_drule (GEN_ALL clos_callProofTheory.calls_obeys_max_app)
            \\ disch_then (qspec_then `cf.max_app` mp_tac)
            \\ (impl_tac THEN1 (fs [] \\ EVAL_TAC) \\ rw []))
    \\ match_mp_tac clos_annotateProofTheory.obeys_max_app_ann
    \\ fs [clos_callProofTheory.state_syntax_def]
    \\ rw [] \\ TRY (match_mp_tac clos_to_bvlProofTheory.chain_exps_obeys_max_app \\ fs [])
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
  \\ TRY (old_drule clos_callProofTheory.calls_preserves_every_Fn_SOME
          \\ impl_tac THEN1 (fs [] \\ EVAL_TAC) \\ strip_tac \\ fs [])
  \\ match_mp_tac clos_annotateProofTheory.every_Fn_SOME_ann
  \\ fs [closPropsTheory.every_Fn_SOME_APPEND]
  \\ match_mp_tac clos_to_bvlProofTheory.chain_exps_every_Fn_SOME \\ fs []
QED

Theorem word_list_exists_imp:
   dm = stack_removeProof$addresses a n /\
    dimindex (:'a) DIV 8 * n < dimword (:'a) ∧ good_dimindex (:'a) ⇒
    word_list_exists a n (fun2set (m1,dm:'a word set))
Proof
  metis_tac [stack_removeProofTheory.word_list_exists_addresses]
QED

val semantics_thms = [source_to_flatProofTheory.compile_semantics,
  flat_to_closProofTheory.compile_semantics,
  clos_to_bvlProofTheory.compile_semantics,
  bvl_to_bviProofTheory.compile_semantics,
  bvi_to_dataProofTheory.compile_prog_semantics,
  data_to_wordProofTheory.compile_semantics,
  word_to_stackProofTheory.compile_semantics,
  full_make_init_semantics]

val cake_configs_def = Define`
  cake_configs c source = state_orac_states (compile_inc_progs T) c source`;

val cake_orac_def = Define`
  cake_orac c source f g i =
    let c = cake_configs c source i in
    let (_, progs) = compile_inc_progs T c (source i) in
    (f c, g progs)`;

val config_tuple2_def = Define`
  config_tuple2 c = (c.bvl_conf.inlines, c.bvl_conf.next_name1,
    c.bvl_conf.next_name2, c.word_conf.bitmaps_length, c.lab_conf)`;

val config_tuple1_def = Define`
  config_tuple1 c = (c.source_conf, c.clos_conf.next_loc,
    clos_known$option_val_approx_spt c.clos_conf.known_conf,
    FST c.clos_conf.call_state, config_tuple2 c)`;

Theorem cake_configs_eq:
  !f. compile c prog = SOME (b,bm,c') /\
    f c' = f c /\ (!c p. f (FST (compile_inc_progs T c p)) = f c) ==>
  f c' = f c /\ (!i. f (cake_configs c' src x) = f c)
Proof
  rw []
  \\ fs [cake_configs_def]
  \\ Q.ISPECL_THEN [`c'`, `src`, `x`, `compile_inc_progs T`, `\x. f x = f c`]
    mp_tac (GEN_ALL state_orac_states_inv)
  \\ simp [PAIR_FST_SND_EQ]
QED

Theorem PAIR_MAP_EQ_EQ:
  (f ## g) x = y <=> (?x0 x1. x = (x0, x1) /\ (f x0, g x1) = y)
Proof
  Cases_on `x` \\ simp []
QED

Theorem known_compile_IS_SOME:
  compile kc es = (kc',es') ⇒ (IS_SOME kc' <=> IS_SOME kc)
Proof
  Cases_on `kc`
  \\ fs [clos_knownTheory.compile_def]
  \\ pairarg_tac \\ fs []
  \\ rw [] \\ simp []
QED

Theorem compile_lab_lab_conf:
  compile_lab lc es = SOME (b, lc')
    ==> lc'.asm_conf = lc.asm_conf
Proof
  simp [lab_to_targetTheory.compile_lab_def, UNCURRY]
  \\ every_case_tac \\ rw [] \\ simp []
QED

Theorem attach_bitmaps_SOME:
  attach_bitmaps names c bm v = SOME r ==>
  ?bytes c'. v = SOME (bytes, c') /\ r = (bytes,bm,c with <| lab_conf := c'; symbols := MAP (\(n,p,l). (lookup_any n names «NOTFOUND»,p,l)) c'.sec_pos_len |>)
Proof
  Cases_on `THE v` \\ Cases_on `v` \\ fs [attach_bitmaps_def]
QED

Theorem known_compile_static_conf:
  compile kc es = (kc',es') ⇒ known_static_conf kc' = known_static_conf kc
Proof
  Cases_on `kc` \\ fs [clos_knownTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ fs [clos_knownTheory.known_static_conf_def, clos_knownTheory.reset_inline_factor_def]
QED

Theorem known_option_upd_val_spt_eq:
  IS_SOME (option_upd_val_spt spt kc) = IS_SOME kc /\
  known_static_conf (option_upd_val_spt spt kc) = known_static_conf kc
Proof
  Cases_on `kc` \\ fs [clos_knownTheory.known_static_conf_def,
    clos_knownTheory.option_upd_val_spt_def,
    clos_knownTheory.reset_inline_factor_def]
QED

Theorem source_compile_pattern_cfg:
  (compile c p = (c', p') ==> c'.pattern_cfg = c.pattern_cfg) /\
  (inc_compile env_id c p = (c', p') ==> c'.pattern_cfg = c.pattern_cfg)
Proof
  simp [source_to_flatTheory.compile_def, source_to_flatTheory.inc_compile_def,
    source_to_flatTheory.compile_prog_def, source_to_flatTheory.inc_compile_prog_def]
  \\ rw [UNCURRY]
  \\ simp []
QED

val cake_orac_config_inv_f =
  ``(\ (sc, cc, bc, mc). (sc.pattern_cfg, cc.max_app, cc.do_call, IS_SOME cc.known_conf,
        known_static_conf cc.known_conf, cc.do_mti, bc.inline_size_limit,
        bc.split_main_at_seq, bc.exp_cut, mc))
    o (\c. (c.source_conf, c.clos_conf, c.bvl_conf, c.data_conf,
        c.word_to_word_conf.reg_alg, c.stack_conf, c.lab_conf.asm_conf))``

val cake_orac_config_tuple_eq_step = ISPEC cake_orac_config_inv_f cake_configs_eq
  |> SIMP_RULE std_ss []

val orac_eq_prop = let
    val m = match_term ``A /\ B /\ C ==> P``
        (concl cake_orac_config_tuple_eq_step)
  in subst (fst m) ``A ==> P`` end;

Theorem cake_orac_config_eqs:
  ^orac_eq_prop
Proof
  disch_tac
  \\ old_drule cake_orac_config_tuple_eq_step
  \\ reverse impl_tac >- fs []
  \\ conj_tac
  \\ TRY (gen_tac \\ pop_assum kall_tac)
  \\ rpt gen_tac
  \\ fs [compile_inc_progs_def, backendTheory.compile_def,
            backendTheory.compile_tap_def, clos_to_bvlTheory.compile_def,
            clos_to_bvlTheory.compile_common_def,
            clos_to_bvlTheory.clos_to_bvl_compile_inc_def, lab_to_targetTheory.compile_def,
            bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def ]
  \\ rpt (pairarg_tac \\ fs [])
  \\ imp_res_tac attach_bitmaps_SOME \\ fs []
  \\ imp_res_tac known_compile_IS_SOME
  \\ imp_res_tac known_compile_static_conf
  \\ imp_res_tac compile_lab_lab_conf
  \\ imp_res_tac source_compile_pattern_cfg
  \\ rveq \\ fs []
  \\ fs [known_option_upd_val_spt_eq]
  \\ every_case_tac
  \\ simp []
  \\ imp_res_tac compile_lab_lab_conf
QED

Theorem decide_inline_reset_spt:
  decide_inline (kc with val_approx_spt updated_by f) = decide_inline kc
Proof
  fs [clos_knownTheory.decide_inline_def, FUN_EQ_THM]
QED

Theorem known_reset_spt:
  !kc. known (kc with val_approx_spt updated_by f) = known (kc)
Proof
  simp [FUN_EQ_THM]
  \\ ho_match_mp_tac clos_knownTheory.known_ind
  \\ rw []
  \\ fs [clos_knownTheory.known_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ TRY (irule listTheory.MAP_CONG)
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [decide_inline_reset_spt, clos_knownTheory.dec_inline_factor_def]
  \\ rpt (CASE_TAC \\ fs [])
QED

Theorem known_reset_to_static_conf:
  known (reset_inline_factor kc) = known (THE (known_static_conf (SOME kc)))
Proof
  fs [clos_knownTheory.known_static_conf_def, known_reset_spt]
QED

Theorem known_co_eq_state_co_inc:
  clos_knownProof$known_co kc co =
  state_co (known_compile_inc (known_static_conf kc)) co
Proof
  Cases_on `kc`
  >- (
    simp [clos_knownTheory.known_static_conf_def, clos_knownTheory.known_compile_inc_def,
        clos_knownProofTheory.known_co_def, FUN_EQ_THM, state_co_def]
  )
  \\ simp [clos_knownTheory.known_static_conf_def, clos_knownTheory.known_compile_inc_def,
      clos_knownProofTheory.known_co_def, FUN_EQ_THM, state_co_def]
  \\ simp [pure_co_def, UNCURRY, clos_to_bvlProofTheory.kcompile_inc_uncurry]
  \\ simp [known_reset_to_static_conf]
  \\ simp [clos_knownTheory.known_static_conf_def, clos_knownTheory.reset_inline_factor_def]
QED

Triviality keep_progs_T:
  keep_progs T = I
Proof
  simp [keep_progs_def, FUN_EQ_THM]
QED

Triviality compile_inc_progs_defs = LIST_CONJ
  [compile_inc_progs_def, keep_progs_T, quotient_pairTheory.PAIR_MAP_I]

Theorem cake_orac_eqs:
  state_co (\c (env_id, decs). inc_compile env_id c
    (source_to_source$compile decs))
    (cake_orac c' src config_tuple1 (\ps. (ps.env_id, ps.source_prog))) =
  cake_orac c' src (SND o config_tuple1) (\ps. ps.flat_prog)
  /\
  pure_co (flat_to_clos_inc_compile)
    o cake_orac c' src f1 (\ps. ps.flat_prog) =
  cake_orac c' src f1 (\ps. ps.clos_prog)
  /\ (
  compile c prog = SOME (b,bm,c') /\ clos_c = c.clos_conf ==>
  pure_co (clos_to_bvl$compile_inc clos_c.max_app) o
  pure_co clos_annotate$compile_inc o
  state_co (clos_call$cond_call_compile_inc clos_c.do_call)
    (clos_knownProof$known_co clos_c.known_conf
      (state_co (clos_number$ignore_table clos_number$compile_inc)
        (pure_co (clos_mti$cond_mti_compile_inc clos_c.do_mti
                    clos_c.max_app) o
          cake_orac c' src (SND o config_tuple1) (\ps. ps.clos_prog)))) =
  cake_orac c' src config_tuple2 (\ps. ps.bvl_prog)
  )
  /\ (
  compile c prog = SOME (b,bm,c') /\ bvl_c = c.bvl_conf ==>
  bvl_to_bviProof$full_co bvl_c
    (cake_orac c' src config_tuple2 (\ps. ps.bvl_prog)) =
  cake_orac c' src (SND o SND o SND o config_tuple2) (\ps. ps.bvi_prog)
  )
  /\
  pure_co bvi_to_data_compile_prog o
    cake_orac c' src f3 (\ps. ps.bvi_prog) =
  cake_orac c' src f3 (\ps. ps.data_prog)
  /\ (
  compile c prog = SOME (b,bm,c') /\
    dc = ensure_fp_conf_ok c.lab_conf.asm_conf c.data_conf /\
    tr_c = c.lab_conf.asm_conf.two_reg_arith /\
    reg_c = c.lab_conf.asm_conf.reg_count -
        (LENGTH c.lab_conf.asm_conf.avoid_regs + 5) /\
    reg_alg = c.word_to_word_conf.reg_alg /\ asm_c = c.lab_conf.asm_conf
    ==>
  pure_co (MAP (λp. full_compile_single tr_c reg_c reg_alg asm_c (p,NONE))) o
    pure_co (MAP (compile_part dc)) o cake_orac c' src f4 (\ps. ps.data_prog) =
  cake_orac c' src f4 (\ps. ps.word_prog)
  )
  /\
  (
  compile c prog = SOME (b, bm, c') ==>
  (λ((bm0,cfg),prg). (λ(prg2,fs,bm). (cfg,prg2,append(FST bm)))
    (compile_word_to_stack (c.lab_conf.asm_conf.reg_count -
      (LENGTH c.lab_conf.asm_conf.avoid_regs + 5)) prg (Nil, bm0))) ∘
  cake_orac c' src (SND ∘ SND ∘ SND ∘ config_tuple2) (λps. ps.word_prog) =
  cake_orac c' src (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
    (λps. (ps.stack_prog,ps.cur_bm))
  )
  /\
  (
  compile c prog = SOME (b,bm,c') /\ reg_nm = c.stack_conf.reg_names /\
    jump = c.stack_conf.jump /\ sp = c.lab_conf.asm_conf.reg_count -
      (LENGTH c.lab_conf.asm_conf.avoid_regs + 3) /\
    offs = c.lab_conf.asm_conf.addr_offset
    ==>
  pure_co (stack_to_lab$compile_no_stubs reg_nm jump offs sp ∘ FST) ∘
  cake_orac c' src f5 (λps. (ps.stack_prog, ps.cur_bm)) =
  cake_orac c' src f5 (λps. ps.lab_prog)
  )
Proof
  rw [cake_orac_def, FUN_EQ_THM, config_tuple1_def]
  \\ simp [known_co_eq_state_co_inc, bvl_to_bviProofTheory.full_co_def]
  \\ simp [cake_orac_def, compile_inc_progs_defs, pure_co_def, state_co_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [config_tuple1_def, config_tuple2_def]
  \\ rveq \\ fs []
  (* assumption-free goals need to be proven by now *)
  \\ drule_then assume_tac cake_orac_config_eqs
  \\ fs []
  >- (
    fs [clos_to_bvlTheory.clos_to_bvl_compile_inc_def,
        config_tuple1_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
  )
  >- (
    fs [bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def, config_tuple2_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
  )
QED

val [source_to_flat_orac_eq, flat_to_clos_orac_eq,
    clos_to_bvl_orac_eq, bvl_to_bvi_orac_eq, bvi_to_data_orac_eq,
    data_to_word_orac_eq, word_to_stack_orac_eq, stack_to_lab_orac_eq] =
        map GEN_ALL (CONJUNCTS cake_orac_eqs);

val simple_orac_eqs = LIST_CONJ [source_to_flat_orac_eq, flat_to_clos_orac_eq,
    bvi_to_data_orac_eq];

Theorem cake_orac_0:
  cake_orac c' src f g 0 = (f c', g (SND (compile_inc_progs T c' (src 0))))
Proof
  fs [cake_orac_def, UNCURRY]
  \\ fs [cake_configs_def, state_orac_states_def]
QED

Theorem cake_orac_SUC:
  cake_orac c' src f g (SUC i) = (let (c'', ps) = cake_orac c' src I I i in
    let c''' = FST (compile_inc_progs T c'' (src i)) in
    (f c''', g (SND (compile_inc_progs T c''' (src (SUC i))))))
Proof
  simp [cake_orac_def, cake_configs_def, state_orac_states_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
QED

Triviality compile_inc_progs_src_env_tup:
  compile_inc_progs T cfg p = (cfg', progs) ==>
  progs.env_id = FST p /\ progs.source_prog = SND p
Proof
  simp [compile_inc_progs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [] \\ simp []
QED

Theorem cake_orac_SUC2:
  cake_orac c' src f g (SUC i) = (let (c'', ps) = cake_orac c' src I I i in
    let c''' = FST (compile_inc_progs T c'' (ps.env_id, ps.source_prog)) in
    (f c''', g (SND (compile_inc_progs T c''' (src (SUC i))))))
Proof
  simp [cake_orac_def, cake_configs_def, state_orac_states_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac compile_inc_progs_src_env_tup
  \\ simp []
QED

Theorem from_clos_conf_EX:
  from_clos c p = v ==>
  ?cc names p. from_bvl (c with clos_conf := cc) names p = v
Proof
  fs [from_clos_def]
  \\ pairarg_tac \\ fs []
  \\ metis_tac []
QED

Theorem from_bvl_conf_EX:
  from_bvl c names p = v ==>
  ?st bvlcu (names:mlstring sptree$num_map) p.
    from_bvi (c with <| bvl_conf updated_by bvlcu;
    clos_conf updated_by (λc. c with start := st) |>) names p = v
Proof
  fs [from_bvl_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ metis_tac []
QED

Theorem from_bvi_conf_EX:
  from_bvi c names p = v ==>
  ?p. from_data c names p = v
Proof
  fs [from_bvi_def]
  \\ metis_tac []
QED

Theorem from_data_conf_EX:
  from_data c names p = v ==>
  ?wcu p. from_word (c with word_to_word_conf updated_by wcu) names p = v
Proof
  fs [from_data_def]
  \\ pairarg_tac \\ fs []
  \\ metis_tac []
QED

Theorem from_word_conf_EX:
  from_word c names p = v ==>
  ?wc p bm. from_stack (c with word_conf := wc) names p bm = v
Proof
  fs [from_word_def]
  \\ pairarg_tac \\ fs []
  \\ metis_tac []
QED

Theorem from_stack_conf_EX:
  from_stack c names p bm = v ==>
  ?p. from_lab c names p bm = v
Proof
  fs [from_stack_def]
  \\ metis_tac []
QED

Theorem from_lab_conf_EX:
  from_lab c names p bm = SOME (bytes, bitmap, c') ==>
  ?lc. c' = c with <| lab_conf := lc; symbols := MAP (\(n,p,l). (lookup_any n names «NOTFOUND»,p,l)) lc.sec_pos_len |>
Proof
  Cases_on `THE (compile c.lab_conf p)`
  \\ Cases_on `compile c.lab_conf p`
  \\ fs [from_lab_def, attach_bitmaps_def]
  \\ metis_tac []
QED

val from_EXS = [
    from_clos_conf_EX,
    from_bvl_conf_EX,
    from_bvi_conf_EX,
    from_data_conf_EX,
    from_word_conf_EX,
    from_stack_conf_EX,
    from_lab_conf_EX]

(*
Theorem MAP_compile_distinct_setglobals:
  BAG_ALL_DISTINCT (flatProps$elist_globals es) ⇒
  BAG_ALL_DISTINCT (closProps$elist_globals (flat_to_clos_compile m es))
Proof
  fs [closPropsTheory.elist_globals_FOLDR, MAP_MAP_o, o_DEF,
    GSYM pat_to_closProofTheory.set_globals_eq, ETA_THM,
    patPropsTheory.elist_globals_FOLDR]
QED
*)

Theorem oracle_monotonic_globals_flat_to_clos:
  flatProps$no_Mat_decs p /\
  (!n. flatProps$no_Mat_decs (SND (orac n))) /\
  oracle_monotonic (SET_OF_BAG ∘ flatProps$elist_globals
        ∘ MAP flatProps$dest_Dlet ∘ FILTER flatProps$is_Dlet ∘ SND) $<
    (SET_OF_BAG (flatProps$elist_globals
      (MAP flatProps$dest_Dlet (FILTER flatProps$is_Dlet p))))
    orac ==>
  oracle_monotonic (SET_OF_BAG ∘ closProps$elist_globals ∘ FST ∘ SND) $<
    (SET_OF_BAG (closProps$elist_globals (compile_decs p)))
    (pure_co flat_to_clos_inc_compile ∘ orac)
Proof
  rw []
  \\ pop_assum mp_tac
  \\ match_mp_tac backendPropsTheory.oracle_monotonic_subset
  \\ simp [flat_to_closTheory.inc_compile_decs_def, closPropsTheory.elist_globals_append]
  \\ simp [PULL_FORALL, compile_decs_set_globals]
QED

Theorem cake_orac_eq_I:
  !f g. cake_orac c syntax f g = (f ## g) o cake_orac c syntax I I
Proof
  simp [FUN_EQ_THM, cake_orac_def, UNCURRY]
QED

Theorem cake_orac_invariant:
  P (f c) /\
  (!c prog. P (f c) ==> P (f (FST (compile_inc_progs T c prog)))) ==>
  (!i. P (FST (cake_orac c syntax f g i)))
Proof
  disch_tac
  \\ simp [Once cake_orac_eq_I]
  \\ Induct
  \\ simp [cake_orac_0, cake_orac_SUC2]
  \\ fs [UNCURRY]
QED

fun conseq xs = ConseqConv.CONSEQ_REWRITE_TAC (xs, [], [])

fun qsubpat_x_assum tac = let
    fun m t = can (find_term (can (match_term t)))
    fun ttac t thm = if m t (concl thm) then tac thm else NO_TAC
  in Tactical.Q_TAC (fn t => first_x_assum (ttac t)) end

Theorem bvl_to_bvi_compile_semantics2:
  bvl_to_bvi_compile start c names prog = (start',prog',inlines,n1,n2,names1) ∧
  (?v. FST (co 0) = (inlines, n1, n2, v)) ∧
  (∀n. ALL_DISTINCT (MAP FST (SND (co n)))) ∧
  ALL_DISTINCT (MAP FST prog) ∧
  is_state_oracle bvi_tailrec_compile_prog
    (state_co bvl_to_bvi_compile_inc
      (state_co (bvl_inline_compile_inc c.inline_size_limit
          c.split_main_at_seq c.exp_cut) co))
  ⇒
  bvlSem$semantics ffi0 (fromAList prog) co (bvl_to_bviProof$full_cc c cc)
    start ≠ Fail ⇒
  bviSem$semantics ffi0 (fromAList prog') (bvl_to_bviProof$full_co c co)
    cc start' =
  bvlSem$semantics (ffi0 : 'ffi ffi_state) (fromAList prog)
    co (bvl_to_bviProof$full_cc c cc) start
Proof
  rw []
  \\ irule bvl_to_bviProofTheory.compile_semantics
  \\ fs []
  \\ reverse conj_tac THEN1 metis_tac []
  \\ Induct
  >- (
    simp []
    \\ fs [bvl_to_bviTheory.compile_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ imp_res_tac bvi_tailrecProofTheory.compile_prog_next_mono
    \\ simp [bvl_to_bviProofTheory.mult_nss_in_ns_2]
  )
  \\ drule is_state_oracle_k
  \\ disch_then (qspecl_then [`n`] assume_tac)
  \\ fs [backendPropsTheory.FST_state_co]
  \\ qmatch_goalsub_abbrev_tac `bvi_tailrec_compile_prog st_n prog_n`
  \\ Cases_on `bvi_tailrec_compile_prog st_n prog_n`
  \\ imp_res_tac bvi_tailrecProofTheory.compile_prog_next_mono
  \\ fs [PAIR_FST_SND_EQ, backendPropsTheory.FST_state_co]
  \\ rveq \\ fs []
  \\ fs [bvl_to_bviProofTheory.in_ns_def]
  \\ metis_tac [arithmeticTheory.ADD_COMM, arithmeticTheory.MOD_TIMES,
        EVAL ``0 < bvl_to_bvi_namespaces``]
QED

Theorem compile_no_stubs_wrap_pure_co:
  (λn. (let (c,p,b) = coracle n in
    (c, stack_to_lab$compile_no_stubs rn j offs sp p)))
    =
  (pure_co (stack_to_lab$compile_no_stubs rn j offs sp o FST) o coracle)
Proof
  rw [FUN_EQ_THM, pure_co_def]
  \\ rpt (pairarg_tac \\ fs [])
QED

Theorem full_make_init_semantics2 = full_make_init_semantics
  |> REWRITE_RULE [compile_no_stubs_wrap_pure_co]

Theorem data_num_stubs_LE_tailrec_compile:
  data_num_stubs <= nn2 /\ EVERY ($<= data_num_stubs) (MAP FST (orac n)) ==>
  EVERY ($<= data_num_stubs)
    (MAP FST (state_co_progs bvi_tailrec_compile_prog nn2 orac n))
Proof
  disch_tac
  \\ fs [state_co_progs_def]
  \\ qmatch_goalsub_abbrev_tac `bvi_tailrec_compile_prog st_n prog_n`
  \\ Cases_on `bvi_tailrec_compile_prog st_n prog_n`
  \\ rw [EVERY_MEM]
  \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
  \\ disch_then drule
  \\ rw []
  >- (
   fs [EVERY_MEM]
  )
  \\ qsuff_tac `data_num_stubs <= st_n` \\ fs []
  \\ unabbrev_all_tac
  \\ Q.SPEC_TAC (`n`, `n`)
  \\ Induct \\ fs [state_orac_states_def]
  \\ qmatch_goalsub_abbrev_tac `bvi_tailrec_compile_prog st_n prog_n`
  \\ Cases_on `bvi_tailrec_compile_prog st_n prog_n`
  \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
  \\ rw []
QED

Theorem data_num_stubs_LE_bvl_bvi_compile:
  EVERY ($<= data_num_stubs)
    (MAP FST (state_co_progs bvl_to_bvi_compile_inc nn1 orac n))
Proof
  fs [state_co_progs_def]
  \\ qmatch_goalsub_abbrev_tac `bvl_to_bvi_compile_inc st_n prog_n`
  \\ Cases_on `bvl_to_bvi_compile_inc st_n prog_n`
  \\ rw [EVERY_MEM]
  \\ drule (GEN_ALL bvl_to_bviProofTheory.compile_inc_next_range)
  \\ disch_then drule
  \\ `data_num_stubs <= bvl_num_stubs` by EVAL_TAC
  \\ CASE_TAC
  \\ rw []
QED

Theorem configs_nn2_MULT_namespaces:
  ?k. (cake_configs c' syntax n).bvl_conf.next_name2
    = c'.bvl_conf.next_name2 + (k * bvl_to_bvi_namespaces)
Proof
  Induct_on `n` \\ fs [cake_configs_def, state_orac_states_def]
  >- (qexists_tac `0` \\ simp [])
  \\ simp [compile_inc_progs_def, bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
  \\ rw []
  \\ rveq \\ fs []
  \\ metis_tac [arithmeticTheory.RIGHT_ADD_DISTRIB]
QED

Theorem configs_nn2_MOD_namespaces:
  (cake_configs c' syntax n).bvl_conf.next_name2
        MOD bvl_to_bvi_namespaces
    = c'.bvl_conf.next_name2 MOD bvl_to_bvi_namespaces
Proof
  mp_tac configs_nn2_MULT_namespaces
  \\ rw []
  \\ simp [EVAL ``0 < bvl_to_bvi_namespaces``]
QED

Theorem configs_nn2_MOD_namespaces_ok:
  compile c prog = SOME (b, bm, c') /\ backend_config_ok c ==>
  c'.bvl_conf.next_name2 MOD bvl_to_bvi_namespaces = 2
Proof
  fs [backendTheory.compile_def, compile_tap_def, bvl_to_bviTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ drule_then assume_tac attach_bitmaps_SOME
  \\ rveq \\ fs []
  \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
  \\ rw [] \\ simp [EVAL ``0 < bvl_to_bvi_namespaces``]
  \\ EVAL_TAC
QED

Theorem bvl_to_bvi_compile_inc_all_num_stubs_LE:
  bvl_to_bvi_compile_inc_all c bvl = (c', bvi) ==>
  bvl_num_stubs <= c.next_name2 ==>
  EVERY ($<= bvl_num_stubs) (MAP FST bvi)
Proof
  rw [EVERY_MEM, bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
  \\ disch_then drule
  \\ rw [] \\ fs []
  \\ drule (GEN_ALL bvl_to_bviProofTheory.compile_inc_next_range)
  \\ disch_then drule
  \\ rw []
QED

Theorem bvl_num_stubs_LE_bvi_prog:
  compile c prog = SOME (b, bm, c') ==>
  EVERY ($<= bvl_num_stubs)
    (MAP FST (SND (cake_orac c' syntax f (\ps. ps.bvi_prog) n)))
Proof
  rw [cake_orac_def]
  \\ simp [compile_inc_progs_def, keep_progs_T]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ drule (GEN_ALL bvl_to_bvi_compile_inc_all_num_stubs_LE)
  \\ disch_then irule
  \\ qsuff_tac `bvl_num_stubs <= c'.bvl_conf.next_name2`
  >- (
    mp_tac configs_nn2_MULT_namespaces
    \\ rw [] \\ fs []
  )
  \\ fs [backendTheory.compile_def, compile_tap_def, bvl_to_bviTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule_then assume_tac attach_bitmaps_SOME
  \\ rveq \\ fs []
  \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
  \\ rw []
QED

Theorem stack_to_lab_orac_eq_std_sym = stack_to_lab_orac_eq
  |> SIMP_RULE std_ss []
  |> SPEC_ALL |> UNDISCH_ALL |> GSYM |> DISCH_ALL

val state_co_fun_def = Define `
  state_co_fun f_inc x =
    let ((cfg1, cfg2), p) = x in
    let (_, p') = f_inc cfg1 p in
    (cfg2, p')`;

Theorem state_co_eq_comp:
  state_co f_inc orac = state_co_fun f_inc o orac
Proof
  fs [state_co_def, state_co_fun_def, FUN_EQ_THM]
QED

Theorem is_state_oracle_cake_orac_comp:
  (!i ps'.
    let (c'', ps) = compile_inc_progs T (cake_configs c' syntax i) (syntax i) in
    let ((f_c, _), f_p) = f (g (cake_configs c' syntax i), h ps) in
    let ((f_c', _), _) = f (g c'', ps') in
    f_c' = FST (f_inc f_c f_p))
  ==>
  is_state_oracle f_inc (f o cake_orac c' syntax g h)
Proof
  rw [is_state_oracle_def]
  \\ simp [cake_orac_SUC]
  \\ first_x_assum (qspecl_then [`n`] mp_tac)
  \\ simp [cake_orac_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ qmatch_goalsub_abbrev_tac `f (g c_x, h p_x)`
  \\ disch_then (qspecl_then [`h p_x`] mp_tac)
  \\ pairarg_tac \\ fs []
QED

Theorem is_state_oracle_cake_orac = is_state_oracle_cake_orac_comp
  |> Q.GEN `f` |> Q.ISPEC `I : (('x # 'y) # 'z -> ('x # 'y) # 'z)`
  |> REWRITE_RULE [combinTheory.I_o_ID]

Theorem cake_orac_clos_is_state:
  is_state_oracle clos_to_bvl_compile_inc
    (cake_orac c' syntax (\c. (c.clos_conf, ())) (\ps. ps.clos_prog))
Proof
  match_mp_tac is_state_oracle_cake_orac
  \\ rw []
  \\ fs [compile_inc_progs_defs]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
QED

Theorem cake_orac_source_is_state:
  is_state_oracle
    (\c (env_id, decs). inc_compile env_id c (source_to_source$compile decs))
    (cake_orac c' syntax config_tuple1 (\ps. (ps.env_id, ps.source_prog)))
Proof
  match_mp_tac is_state_oracle_cake_orac
  \\ rw []
  \\ fs [compile_inc_progs_def, config_tuple1_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
QED

Triviality SND_flat_to_clos_inc_compile =
    REWRITE_CONV [flat_to_closTheory.inc_compile_decs_def]
        ``SND (flat_to_clos_inc_compile p)``

Theorem is_state_oracle_cake_orac_to_comp:
  is_state_oracle f_inc (cake_orac c' syntax st_f ps_f) ==>
  compile c prog = SOME (b, bm, c') ==>
  (!c'' ps c''' g_p'.
    ^cake_orac_config_inv_f c'' = ^cake_orac_config_inv_f c ==>
    (* f step *)
    let (f_c', _) = f_inc (FST (st_f c'')) (ps_f ps) in
    (* g step *)
    let ((g_c, _), g_p) = adj (g c'', h ps) in
    let (g_c', _) = g_inc g_c g_p in
    (* for some c''', if f step agrees, g step should agree *)
    f_c' = FST (st_f c''') ==> g_c' = FST (FST (adj (g c''', g_p')))) ==>
  is_state_oracle g_inc (adj o cake_orac c' syntax g h)
Proof
  rw [is_state_oracle_def]
  \\ first_x_assum (qspecl_then [`n`] mp_tac)
  \\ simp [cake_orac_def]
  \\ first_x_assum (qspecl_then [`(cake_configs c' syntax n)`] mp_tac)
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule_then (fn t => simp [t]) cake_orac_config_eqs
  \\ fs [UNCURRY]
  \\ metis_tac []
QED

Theorem cake_orac_clos_syntax_oracle_ok:
  compile (c : 's config) prog = SOME (b, bm, c') /\
  compile c2 clos_prog = (clos_c', clos_prog') /\
  (?st. c'.clos_conf = clos_c' with start := st) /\
  c2 = c.clos_conf /\ clos_prog = SND (to_clos c prog) /\
  1 <= c.clos_conf.max_app /\
  c.source_conf = prim_src_config ==>
  clos_to_bvlProof$syntax_oracle_ok c.clos_conf clos_c' clos_prog
     (cake_orac c' syntax (SND ∘ config_tuple1) (λps.ps.clos_prog))
Proof
  rw []
  \\ simp [to_clos_def, to_flat_def, flatPropsTheory.elist_globals_REVERSE]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ simp [syntax_oracle_ok_def, to_clos_def]
  \\ simp [backendPropsTheory.FST_state_co, cake_orac_0,
      config_tuple1_def, FST_inc_compile_syntactic_props,
      compile_decs_syntactic_props]
  \\ simp [clos_knownProofTheory.syntax_ok_def]
  \\ simp [GSYM simple_orac_eqs]
  \\ csimp [FST_inc_compile_syntactic_props]
  \\ simp [PULL_FORALL] \\ rpt gen_tac
  \\ conseq [FST_inc_compile_esgc_free, compile_decs_esgc_free,
    oracle_monotonic_globals_flat_to_clos]
  \\ DEP_REWRITE_TAC [FST_inc_compile_set_globals, compile_decs_set_globals]
  \\ csimp []
  \\ fs [PAIR_FST_SND_EQ |> Q.ISPEC `source_to_flat$compile c p`, SND_state_co]
  \\ rveq
  \\ simp [UNCURRY, compile_no_Mat, inc_compile_no_Mat, inc_compile_esgc_free,
        EVERY_MAP |> REWRITE_RULE [GSYM o_DEF] |> GSYM,
        inc_compile_globals_BAG_ALL_DISTINCT,
        compile_globals_BAG_ALL_DISTINCT,
        source_to_flatProofTheory.compile_esgc_free,
        SND_flat_to_clos_inc_compile, compile_decs_syntactic_props]
  \\ simp [Q.prove (`prim_src_config.mod_env.v = nsEmpty`, EVAL_TAC)]
  \\ qpat_assum `compile c _ = SOME _`
    (assume_tac o REWRITE_RULE [compile_eq_from_source])
  \\ fs [from_source_def, from_flat_def,
        to_clos_def, to_flat_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ drule_then (fn t => conseq [t]) monotonic_globals_state_co_compile
  \\ simp [cake_orac_0, config_tuple1_def]
  \\ rename [`compile prim_src_config _ = (source_conf',_)`]
  \\ `source_conf' = c'.source_conf` by (
    EVERY (map imp_res_tac from_EXS)
    \\ fs [] \\ rfs []
    \\ rveq \\ fs []
  )
  \\ simp [simple_orac_eqs, cake_orac_source_is_state]
  \\ Q.ISPECL_THEN [`c'`] assume_tac (Q.GEN `c'` cake_orac_clos_is_state)
  (* should just be is_state_oracle assumptions by now *)
  \\ rw []
  \\ REWRITE_TAC [state_co_eq_comp, o_ASSOC, known_co_eq_state_co_inc]
  \\ drule_then (drule_then irule) (GEN_ALL is_state_oracle_cake_orac_to_comp)
  \\ fs [state_co_fun_def, pure_co_def, config_tuple1_def,
        clos_to_bvlTheory.clos_to_bvl_compile_inc_def]
  \\ rpt (gen_tac ORELSE disch_tac ORELSE (pairarg_tac \\ fs []))
  \\ fs [clos_to_bvlTheory.config_component_equality]
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  >- (
    fs [SPEC T clos_callTheory.cond_call_compile_inc_def]
    \\ rveq \\ fs []
    \\ fs [PAIR_FST_SND_EQ]
  )
  >- (
    fs [IS_SOME_EXISTS]
    \\ rfs [clos_knownTheory.known_static_conf_def,
            clos_knownTheory.known_compile_inc_def, kcompile_inc_uncurry]
    \\ fs [known_reset_to_static_conf]
    \\ fs [clos_knownTheory.known_static_conf_def, clos_knownTheory.reset_inline_factor_def,
clos_knownTheory.option_val_approx_spt_def, clos_knownTheory.option_upd_val_spt_def]
    \\ fs [Q.ISPEC `SOME z` boolTheory.EQ_SYM_EQ]
  )
QED

Theorem cake_orac_bvl_ALL_DISTINCT:
  compile c prog = SOME (b, bm, c') ==>
  ALL_DISTINCT (MAP FST (SND (cake_orac c' syntax f (λps. ps.bvl_prog) n)))
Proof
  rw []
  \\ qsuff_tac `ALL_DISTINCT (MAP FST (SND (cake_orac c' syntax config_tuple2
        (λps. ps.bvl_prog) n)))`
  >- (simp [cake_orac_def, UNCURRY])
  \\ drule clos_to_bvl_orac_eq
  \\ simp []
  \\ disch_then (fn t => simp [GSYM t])
  \\ simp [SND_state_co]
  \\ irule compile_inc_phases_all_distinct
  \\ simp [clos_to_bvlProofTheory.SND_cond_mti_compile_inc]
  \\ rw [cake_orac_def, UNCURRY]
  \\ simp [compile_inc_progs_defs, UNCURRY, SND_flat_to_clos_inc_compile]
QED

Theorem compile_lab_LENGTH:
  compile_lab c secs = SOME (bytes, c') ==>
  c'.pos = LENGTH bytes + c.pos
Proof
  simp [lab_to_targetTheory.compile_lab_def, UNCURRY]
  \\ every_case_tac \\ rw [] \\ simp []
QED

Theorem bvl_to_bvi_compile_inc_all_DISTINCT:
  bvl_to_bvi_compile_inc_all c p = (c', p') /\
  ALL_DISTINCT (MAP FST p) /\ c.next_name2 MOD bvl_to_bvi_namespaces = 2 ==>
  ALL_DISTINCT (MAP FST p')
Proof
  mp_tac (GEN_ALL ALL_DISTINCT_MAP_FST_SND_full_co
    |> Q.SPECL [`n`, `K ((c.inlines, c.next_name1, c.next_name2, cfg), p)`, `c`])
  \\ simp [bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def, full_co_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp [state_co_def]
  \\ rw []
  \\ simp []
QED

Theorem cake_orac_stack_ALL_DISTINCT:
  compile c prog = SOME (b, bm, c') ==>
  ALL_DISTINCT (MAP FST (FST (SND (cake_orac c' syntax
    (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
    (λps. (ps.stack_prog,ps.cur_bm)) n))))
Proof
  rw []
  \\ old_drule cake_orac_bvl_ALL_DISTINCT
  \\ simp [cake_orac_def, compile_inc_progs_defs]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ rw []
  \\ imp_res_tac word_to_stackProofTheory.MAP_FST_compile_word_to_stack
  \\ fs []
  \\ simp [MAP_MAP_o, o_DEF]
  \\ simp[word_to_wordTheory.full_compile_single_def, UNCURRY]
  \\ simp [ETA_THM]
  \\ drule_then irule bvl_to_bvi_compile_inc_all_DISTINCT
  \\ simp [configs_nn2_MOD_namespaces]
  \\ fs [backendTheory.compile_def, compile_tap_def, bvl_to_bviTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule attach_bitmaps_SOME
  \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
  \\ rw []
  \\ simp []
  \\ EVAL_TAC
  \\ simp []
QED

Theorem MAP_full_compile_single_to_compile:
  Abbrev (pp = MAP (\p. full_compile_single asm_c.two_reg_arith reg_count
      reg_alg asm_c (p, NONE)) pp0) /\
  reg_count = (asm_c.reg_count - (LENGTH asm_c.avoid_regs + 5)) ==>
  ∃wc ign. word_to_word$compile wc asm_c pp0 = (ign, pp)
Proof
  rw [word_to_wordTheory.compile_def]
  \\ qexists_tac`<| col_oracle := []; reg_alg := reg_alg |>`
  \\ simp[]
  \\ simp[word_to_wordTheory.next_n_oracle_def]
  \\ simp[Abbr`pp`]
  \\ rw[]
  \\ simp[LIST_EQ_REWRITE, EL_MAP, EL_ZIP, EL_REPLICATE]
QED

Theorem compile_to_word_conventions2:
  compile wc ac p = (_,ps) ==>
  MAP FST ps = MAP FST p ∧
  LIST_REL word_simpProof$labels_rel
    (MAP (wordProps$extract_labels ∘ SND ∘ SND) p)
    (MAP (wordProps$extract_labels ∘ SND ∘ SND) ps) ∧
  EVERY (λ(n,m,prog).
    wordProps$flat_exp_conventions prog ∧
    wordProps$post_alloc_conventions
      (ac.reg_count - (5 + LENGTH ac.avoid_regs)) prog ∧
    (EVERY (λ(n,m,prog).
                      wordProps$every_inst (wordProps$inst_ok_less ac) prog)
                 p ∧ addr_offset_ok ac 0w ⇒
               wordProps$full_inst_ok_less ac prog) ∧
              (ac.two_reg_arith ⇒
               wordProps$every_inst wordProps$two_reg_inst prog)) ps
Proof
  rw []
  \\ mp_tac word_to_wordProofTheory.compile_to_word_conventions
  \\ simp []
QED

Theorem sec_labels_ok_FST_code_labels_Section_num:
  EVERY sec_labels_ok code ==>
  IMAGE FST (get_code_labels code) = set (MAP Section_num code)
Proof
  simp [labPropsTheory.get_code_labels_extract_labels]
  \\ simp [LIST_TO_SET_MAP, IMAGE_IMAGE, o_DEF, Q.ISPEC `Section_num` ETA_THM]
  \\ rw [pred_setTheory.EXTENSION]
  \\ EQ_TAC \\ rw []
  >- prove_tac []
  \\ fs [MEM_FLAT, MEM_MAP]
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rveq \\ fs []
  \\ fs [EVERY_MEM]
  \\ first_x_assum drule
  \\ Cases_on `x`
  \\ fs [GSYM labPropsTheory.EVERY_sec_label_ok]
  \\ simp [EVERY_MEM]
  \\ disch_then drule
  \\ pairarg_tac \\ simp []
QED

Theorem stack_labels_ok_FST_code_labels_Section_num:
  stack_to_labProof$labels_ok code ==>
  IMAGE FST (get_code_labels code) = set (MAP Section_num code)
Proof
  metis_tac [sec_labels_ok_FST_code_labels_Section_num, labels_ok_imp]
QED

Theorem lab_labels_ok_oracle:
  compile c prog = SOME (b, bm, c') /\
  cake_orac c' syntax (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
    (λps. ps.lab_prog) i = (cfg,code) ==>
  stack_to_labProof$labels_ok code
Proof
  simp [cake_orac_def, compile_inc_progs_defs]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [] \\ rveq \\ fs []
  \\ simp[stack_to_labTheory.compile_no_stubs_def, good_code_def]
  \\ irule prog_to_section_labels_ok
  \\ old_drule (Q.SPEC `i` (Q.GEN `n` cake_orac_stack_ALL_DISTINCT))
  \\ simp[MAP_MAP_o, o_DEF]
  \\ simp [cake_orac_def, compile_inc_progs_defs, Q.ISPEC `FST` ETA_THM]
  \\ rw []
  \\ simp[stack_namesTheory.compile_def, MAP_MAP_o, EVERY_MAP]
  \\ simp[LAMBDA_PROD]
  \\ simp[stack_allocTheory.prog_comp_def]
  \\ simp[stack_removeTheory.prog_comp_def]
  \\ simp[stack_namesTheory.prog_comp_def]
  \\ simp[Once EVERY_MEM, FORALL_PROD]
  \\ qx_genl_tac[`l1`,`l2`] \\ strip_tac
  \\ simp[GSYM stack_namesProofTheory.stack_names_lab_pres]
  \\ simp[GSYM stack_removeProofTheory.stack_remove_lab_pres]
  \\ qspecl_then[`l1`,`next_lab l2 2`,`l2`]mp_tac stack_allocProofTheory.stack_alloc_lab_pres
  \\ simp[UNCURRY]
  \\ reverse impl_tac >- rw []
  \\ drule compile_word_to_stack_lab_pres
  \\ CONV_TAC(PATH_CONV"lrr"(SIMP_CONV(srw_ss())[Once EVERY_MEM]))
  \\ simp[FORALL_PROD]
  \\ disch_then irule \\ simp[]
  \\ fs [pure_co_def, PAIR_MAP_EQ_EQ]
  \\ rveq \\ fs []
  \\ qmatch_goalsub_abbrev_tac`EVERY _ fcs_pp`
  \\ drule_then assume_tac (GEN_ALL MAP_full_compile_single_to_compile)
  \\ rfs []
  \\ drule compile_to_word_conventions2
  \\ rw []
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
  \\ qpat_x_assum`MEM _ fcs_pp`mp_tac
  \\ simp[MEM_EL]
  \\ disch_then(qx_choose_then`j`strip_assume_tac)
  \\ first_x_assum(qspec_then`j`mp_tac)
  \\ simp[] \\ strip_tac
  \\ qpat_x_assum`_ = EL j pp`(assume_tac o SYM) \\ fs[]
  \\ fs[Abbr`fcs_pp`] \\ rfs[EL_MAP]
  \\ qmatch_asmsub_abbrev_tac`compile_part c4_data_conf pp4`
  \\ PairCases_on`pp4`
  \\ pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])
  \\ fs[data_to_wordTheory.compile_part_def]
  \\ qspecl_then[`c4_data_conf`,`pp40`,`2`,`pp42`]mp_tac data_to_wordProofTheory.data_to_word_lab_pres_lem
  \\ simp[]
  \\ pairarg_tac \\ fs[]
  \\ simp[EVERY_MEM]
  \\ rw[]
  \\ imp_res_tac SUBSET_IMP
  \\ pairarg_tac \\ fs[]
  \\ qpat_x_assum`MAP FST pp = _`mp_tac
  \\ simp[LIST_EQ_REWRITE, EL_MAP]
  \\ disch_then(qspec_then`j`mp_tac)
  \\ simp[data_to_wordTheory.compile_part_def]
  \\ first_x_assum drule
  \\ rw []
QED

Theorem compile_lab_domain_labels:
  compile_lab c prog = SOME (b, c') ==>
  domain c'.labels = IMAGE FST (get_code_labels prog) ∪ domain c.labels
Proof
  simp [lab_to_targetTheory.compile_lab_def, UNCURRY]
  \\ EVERY_CASE_TAC
  \\ rw []
  \\ drule remove_labels_domain_labs
  \\ rw []
QED

Theorem accum_lab_conf_labels:
  compile c prog = SOME (b, bm, c') ==>
  domain (cake_configs c' syntax i).lab_conf.labels ⊆
  domain c'.lab_conf.labels ∪ BIGUNION (set (MAP (set ∘ MAP Section_num ∘
    SND ∘ cake_orac c' syntax (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
    (λps. ps.lab_prog)) (COUNT_LIST i)))
Proof
  disch_tac \\ Induct_on `i`
  \\ simp [cake_configs_def, state_orac_states_def, COUNT_LIST_SNOC]
  \\ simp [MAP_SNOC, LIST_TO_SET_SNOC, GSYM cake_configs_def]
  \\ simp [compile_inc_progs_defs]
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac
  >- (
    simp []
    \\ drule_then irule SUBSET_TRANS
    \\ simp [SUBSET_DEF]
  )
  \\ simp []
  \\ drule_then (fn t => fs [t]) cake_orac_config_eqs
  \\ fs[lab_to_targetTheory.compile_def]
  \\ old_drule (Q.GENL [`cfg`, `code`] lab_labels_ok_oracle)
  \\ simp [PAIR_FST_SND_EQ]
  \\ disch_tac
  \\ drule_then assume_tac compile_lab_domain_labels
  \\ simp []
  \\ rw [] \\ TRY (drule_then irule SUBSET_TRANS \\ simp [SUBSET_DEF])
  \\ drule stack_labels_ok_FST_code_labels_Section_num
  \\ simp [cake_orac_def, config_tuple2_def, compile_inc_progs_defs]
  \\ drule_then (fn t => simp [t]) cake_orac_config_eqs
  \\ simp [SUBSET_DEF]
QED

Theorem MAP_Section_num_stack_to_lab_SUBSET:
  set (MAP FST prog) ⊆ labs /\ count (SUC gc_stub_location) ⊆ labs ==>
  set (MAP Section_num (compile sc dc max_heap sp offset prog)) ⊆ labs
Proof
  simp [stack_to_labTheory.compile_def, MAP_prog_to_section_Section_num]
  \\ simp [stack_removeTheory.compile_def,
       stack_rawcallTheory.compile_def,
       stack_allocTheory.compile_def, MAP_MAP_o, o_DEF, Q.ISPEC `FST` ETA_THM]
  \\ fs [UNCURRY,Q.ISPEC `FST` ETA_THM]
  \\ EVAL_TAC \\ simp []
QED

Theorem to_data_labels_ok:
  compile c prog = SOME (b, bm, c') /\ backend_config_ok c
  ==>
  let (_, p, _) = to_data c prog in
  EVERY (λn. data_num_stubs <= n) (MAP FST p) /\ ALL_DISTINCT (MAP FST p)
Proof
  rw [to_data_def, to_bvi_def, to_bvl_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ drule_then irule bvl_to_bviProofTheory.compile_distinct_names
  \\ drule_then (fn t => simp [t]) compile_all_distinct_locs
  \\ fs [to_clos_def, to_flat_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ fs [backend_config_ok_def]
  \\ qexists_tac `0` \\ simp []
QED

Theorem data_to_word_stubs_above_store_consts_stub:
  EVERY (λn. n > store_consts_stub_location) (MAP FST (data_to_word$stubs (:'a) dc))
Proof
  EVAL_TAC
QED

Theorem to_word_labels_ok:
  compile c prog = SOME (b, bm, c') /\ backend_config_ok c
  ==>
  let (_, p, _) = to_word c prog in
  ALL_DISTINCT (MAP FST p) /\
  EVERY (λn. n > store_consts_stub_location) (MAP FST p) /\
  EVERY (λ(n,m,p).
    let labs = wordProps$extract_labels p in
    EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧ ALL_DISTINCT labs) p
Proof
  rw [to_word_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ qpat_x_assum `compile _.data_conf _ _ _ = _` mp_tac
  \\ (data_to_word_compile_lab_pres
     |> Q.GENL[`data_conf`,`word_conf`,`asm_conf`,`prog`]
     |> C (specl_args_of_then``data_to_word$compile``)mp_tac)
  \\ rpt disch_tac \\ fs []
  \\ drule to_data_labels_ok
  \\ simp [data_to_word_stubs_above_store_consts_stub]
  \\ simp [ALL_DISTINCT_APPEND, EVERY_MEM, ALL_DISTINCT_MAP_FST_stubs]
  \\ metis_tac [prim_recTheory.LESS_REFL, MAP_FST_stubs_bound,
    LESS_LESS_EQ_TRANS, (EVAL ``store_consts_stub_location < data_num_stubs``),
    arithmeticTheory.GREATER_DEF]
QED

Theorem to_lab_labels_ok:
  compile c prog = SOME (b, bm, c') /\ backend_config_ok c
  ==>
  stack_to_labProof$labels_ok (FST (SND (SND (to_lab c prog))))
Proof
  simp [to_lab_def, to_stack_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ irule stack_to_lab_compile_lab_pres
  \\ drule to_word_labels_ok
  \\ simp []
  \\ rename [`to_word c prog = (word_c, word_p, word_n)`]
  \\ qspecl_then [`word_p`, `word_c.lab_conf.asm_conf`] mp_tac
    (GEN_ALL word_to_stack_compile_lab_pres)
  \\ simp []
  \\ rpt disch_tac
  \\ fs []
  \\ EVAL_TAC
  \\ fs [EVERY_MEM]
  \\ CCONTR_TAC
  \\ fs []
  \\ RES_THEN mp_tac
  \\ EVAL_TAC
  \\ simp []
  \\ gvs []
QED

Theorem oracle_monotonic_slice:
  !g. (!z. oracle_monotonic (\x. f x ∩ PREIMAGE g {z}) (≠)
    (init_s ∩ PREIMAGE g {z}) orac)
  ==>
  oracle_monotonic f (≠) init_s orac
Proof
  rw []
  \\ simp [oracle_monotonic_def]
  \\ CCONTR_TAC \\ fs []
  >- (
    first_x_assum (qspec_then `g y` assume_tac)
    \\ drule oracle_monotonic_step
    \\ simp [pred_setTheory.IN_PREIMAGE]
    \\ metis_tac []
  )
  \\ first_x_assum (qspec_then `g y` assume_tac)
  \\ drule oracle_monotonic_init
  \\ simp [pred_setTheory.IN_PREIMAGE]
  \\ metis_tac []
QED

Theorem oracle_monotonic_rel_mono:
  !R R'. (!x y. R x y ==> R' x y) /\ oracle_monotonic f R init_s orac ==>
  oracle_monotonic f R' init_s orac
Proof
  simp [oracle_monotonic_def] \\ metis_tac []
QED

Theorem oracle_monotonic_state_with_inv:
  !P n_f. P (FST (FST (orac 0))) /\
  (!x. x ∈ St ==> x < n_f (FST (FST (orac 0)))) /\
  (! i st prog st' prog' st_ex. f_inc st prog = (st', prog') /\ P st /\
        orac i = ((st, st_ex), prog) ==>
    P st' /\ n_f st <= n_f st' /\
    (!cfg x. x ∈ f (cfg, prog') ==> n_f st <= x /\ x < n_f st')) /\
  is_state_oracle f_inc orac ==>
  oracle_monotonic f (<) (St : num set) (state_co f_inc orac)
Proof
  rw []
  \\ `!i. P (FST (FST (orac i))) /\
        (!j. j <= i ==> n_f (FST (FST (orac j))) <= n_f (FST (FST (orac i))))`
  by (
    Induct \\ fs [is_state_oracle_def]
    \\ fs [PAIR_FST_SND_EQ, LE]
    \\ rw [] \\ fs []
    \\ metis_tac [LESS_EQ_TRANS]
  )
  \\ fs [oracle_monotonic_def, is_state_oracle_def, state_co_def, UNCURRY]
  \\ fs [PAIR_FST_SND_EQ]
  \\ rw []
  \\ metis_tac [state_orac_states_def, LESS_LESS_EQ_TRANS,
        arithmeticTheory.LESS_OR, LESS_EQ_TRANS,
        arithmeticTheory.ZERO_LESS_EQ]
QED

Theorem oracle_monotonic_bounded_state:
  !n_f.
  (!x. x ∈ St ==> x < n_f (orac 0)) /\
  (!i. n_f (orac i) <= n_f (orac (SUC i)) /\
        (!x. x ∈ f (orac i) ==> n_f (orac i) <= x /\ x < n_f (orac (SUC i))))
  ==>
  oracle_monotonic f (<) (St : num set) orac
Proof
  rw []
  \\ `!i. (!j. j <= i ==> n_f (orac j) <= n_f (orac i))`
  by (
    Induct \\ fs []
    \\ simp [LE]
    \\ rw [] \\ simp []
    \\ metis_tac [LESS_EQ_TRANS]
  )
  \\ simp [oracle_monotonic_def]
  \\ metis_tac [LESS_LESS_EQ_TRANS,
        arithmeticTheory.LESS_OR, LESS_EQ_TRANS,
        arithmeticTheory.ZERO_LESS_EQ]
QED

Theorem compile_prog_avoids_nss_2:
   compile_prog start f prog = (loc,code,new_state) /\
   MEM k (MAP FST code) /\ k MOD bvl_to_bvi_namespaces = 2 ==>
   k < bvl_num_stubs
Proof
  fs [bvl_to_bviTheory.compile_prog_def] \\ pairarg_tac \\ fs []
  \\ drule_then assume_tac bvl_to_bviProofTheory.compile_list_code_labels_domain
  \\ rw [] \\ fs []
  \\ rfs [EVAL ``0 < bvl_to_bvi_namespaces``]
  \\ TRY (qpat_x_assum `MEM _ _` mp_tac)
  \\ qpat_x_assum `_ = 2` mp_tac
  \\ EVAL_TAC \\ rw []
QED

Theorem tailrec_compile_prog_MEM_not_nss_2:
  ∀ys xs n1 n e.
  bvi_tailrec_compile_prog n xs = (n1,ys) ∧ MEM e (MAP FST ys) ∧
  n MOD bvl_to_bvi_namespaces = 2 /\ e MOD bvl_to_bvi_namespaces ≠ 2 ⇒
  MEM e (MAP FST xs)
Proof
  rw []
  \\ drule_then drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
  \\ rw []
  \\ fs [EVAL ``0 < bvl_to_bvi_namespaces``]
QED

Theorem is_state_oracle_tailrec_cake_orac:
  compile c prog = SOME (b,bm,c') ==>
  is_state_oracle bvi_tailrec_compile_prog
    (state_co bvl_to_bvi_compile_inc (state_co
      (bvl_inline_compile_inc c.bvl_conf.inline_size_limit
        c.bvl_conf.split_main_at_seq c.bvl_conf.exp_cut)
      (cake_orac c' syntax config_tuple2 (λps. ps.bvl_prog))))
Proof
  rw []
  \\ REWRITE_TAC [state_co_eq_comp, o_ASSOC]
  \\ irule is_state_oracle_cake_orac_comp
  \\ rw []
  \\ simp [compile_inc_progs_defs, state_co_fun_def,
           bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ fs [config_tuple2_def]
  \\ rveq \\ fs []
  \\ drule_then (fn t => fs (CONJUNCTS t)) cake_orac_config_eqs
  \\ rveq \\ fs []
  \\ rveq \\ fs []
QED

Theorem inline_compile_inc_names:
   bvl_inline$compile_inc l b i spt prog = (inlines,prog3) ==>
   MAP FST prog3 = MAP FST prog
Proof
  fs [bvl_inlineTheory.compile_prog_def,bvl_inlineTheory.compile_inc_def]
  \\ pairarg_tac \\ fs []
  \\ fs [bvl_inlineTheory.tick_compile_prog_def]
  \\ imp_res_tac bvl_inlineProofTheory.tick_inline_all_names \\ rw []
  \\ rw[] \\ fs[]
QED

Theorem oracle_monotonic_subset_inject:
  !g. (!x y. R (g x) (g y) ==> R' x y) ∧
  IMAGE g init_set' ⊆ init_set ∧ (∀n. IMAGE g (f' (co' n)) ⊆ f (co n)) ==>
  oracle_monotonic f R init_set co ==>
  oracle_monotonic f' R' init_set' co'
Proof
  fs [oracle_monotonic_def, SUBSET_DEF]
  \\ metis_tac []
QED

Theorem oracle_monotonic_handle_init_component:
  !D. (!i x y. x ∈ D /\ y ∈ f (co i) ==> R x y) /\
  oracle_monotonic f R (init_set DIFF D) co ==>
  oracle_monotonic f R init_set co
Proof
  fs [oracle_monotonic_def]
  \\ metis_tac []
QED

Theorem oracle_monotonic_cake_orac_to_I:
  oracle_monotonic (\ (cfg, p). f (cfg_f cfg, p_f p)) R init_st
    (cake_orac c' syntax I I) ==>
  oracle_monotonic f R init_st (cake_orac c' syntax cfg_f p_f)
Proof
  match_mp_tac oracle_monotonic_subset
  \\ simp [cake_orac_def, UNCURRY]
QED

Theorem cake_orac_monotonic_bounded_state:
  !n_f.
  (!x. x ∈ St ==> x < n_f c') /\
  (!i c2 ps. let c1 = cake_configs c' syntax i in
    compile_inc_progs T c1 (syntax i) = (c2, ps) ==>
    n_f c1 <= n_f c2 /\
    (!x. x ∈ f (cfg_f c1, p_f ps) ==> n_f c1 <= x /\ x < n_f c2))
  ==>
  oracle_monotonic f (<) (St : num set) (cake_orac c' syntax cfg_f p_f)
Proof
  rw []
  \\ irule oracle_monotonic_cake_orac_to_I
  \\ Q.ISPEC_THEN `n_f o FST` irule oracle_monotonic_bounded_state
  \\ qexists_tac `n_f`
  \\ simp [cake_orac_def, cake_configs_def, state_orac_states_def]
  \\ simp [GSYM cake_configs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gen_tac
  \\ rpt (pairarg_tac \\ fs [])
  \\ metis_tac []
QED

Theorem monotonic_DISJOINT_labels_lab:
  compile c prog = SOME (b, bm, c') /\
  oracle_monotonic (set ∘ MAP Section_num ∘ SND) (≠)
    (domain c'.lab_conf.labels)
    (cake_orac c' syntax (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
                (λps. ps.lab_prog))
  ==>
  DISJOINT (domain (cake_configs c' syntax i).lab_conf.labels)
    (set (MAP Section_num (SND (cake_orac c' syntax
      (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2) (λps. ps.lab_prog) i))))
Proof
  rw []
  \\ old_drule accum_lab_conf_labels
  \\ disch_tac
  \\ REWRITE_TAC [Once DISJOINT_SYM]
  \\ drule_then irule (REWRITE_RULE [Once CONJ_COMM] DISJOINT_SUBSET)
  \\ CCONTR_TAC
  \\ fs [IN_DISJOINT]
  >- (
    drule oracle_monotonic_init
    \\ disch_then drule
    \\ simp [PULL_EXISTS]
    \\ asm_exists_tac
    \\ simp []
  )
  \\ fs [MEM_MAP, MEM_COUNT_LIST]
  \\ drule oracle_monotonic_step
  \\ disch_then drule
  \\ rfs []
  \\ rveq \\ fs [MEM_MAP, PULL_EXISTS]
  \\ metis_tac []
QED

Theorem monotonic_labels_stack_to_lab:
  compile c prog = SOME (b, bm, c') /\ backend_config_ok c
  ==>
  oracle_monotonic (set o MAP FST o FST o SND) (≠)
    (set (MAP FST (FST (SND (SND (to_stack c prog))))) ∪ count (SUC gc_stub_location))
    (cake_orac c' syntax (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
        (λps. (ps.stack_prog,ps.cur_bm)))
 ==>
  oracle_monotonic (set ∘ MAP Section_num ∘ SND) (≠)
    (domain c'.lab_conf.labels)
    (cake_orac c' syntax (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
        (λps. ps.lab_prog))
Proof
  disch_tac
  \\ match_mp_tac oracle_monotonic_subset
  \\ conj_tac >- (
    fs []
    \\ drule_then drule to_lab_labels_ok
    \\ fs [backendTheory.compile_def, backendTheory.compile_tap_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ drule_then strip_assume_tac attach_bitmaps_SOME
    \\ simp [to_stack_def, to_word_def, to_data_def, to_bvi_def, to_bvl_def,
        to_clos_def, to_flat_def, to_lab_def]
    \\ fs[lab_to_targetTheory.compile_def]
    \\ drule compile_lab_domain_labels
    \\ `domain c.lab_conf.labels = {}` by fs [backend_config_ok_def]
    \\ rw []
    \\ simp [stack_labels_ok_FST_code_labels_Section_num]
    \\ irule MAP_Section_num_stack_to_lab_SUBSET
    \\ simp []
  )
  \\ simp [cake_orac_def, compile_inc_progs_defs, Q.ISPEC `FST` ETA_THM]
  \\ rw []
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ simp [stack_to_labTheory.compile_no_stubs_def, MAP_prog_to_section_Section_num,
    MAP_MAP_o, o_DEF, Q.ISPEC `FST` ETA_THM]
QED

Theorem monotonic_labels_bvi_down_to_stack:
  compile c prog = SOME (b, bm, c') /\ backend_config_ok c
  ==>
  oracle_monotonic (set o MAP FST o SND) (≠)
    (set (MAP FST (FST (SND (to_bvi c prog)))) ∪ count (SUC data_num_stubs))
    (cake_orac c' syntax (SND o SND o SND o config_tuple2) (\ps. ps.bvi_prog))
  ==>
  oracle_monotonic (set o MAP FST o FST o SND) (≠)
    (set (MAP FST (FST (SND (SND (to_stack c prog))))) ∪ count (SUC gc_stub_location))
    (cake_orac c' syntax (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
        (λps. (ps.stack_prog,ps.cur_bm)))
Proof
  disch_tac
  \\ match_mp_tac oracle_monotonic_subset
  \\ fs []
  \\ conj_tac >- (
    drule to_word_labels_ok
    \\ simp [to_stack_def, to_word_def, to_data_def]
    \\ disch_tac
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ rename [`compile c2.lab_conf.asm_conf word_p = _`]
    \\ qspecl_then [`word_p`, `c2.lab_conf.asm_conf`] mp_tac
        (GEN_ALL word_to_stack_compile_lab_pres)
    \\ simp [EVAL ``raise_stub_location < SUC data_num_stubs``]
    \\ simp [EVAL ``store_consts_stub_location < SUC data_num_stubs``]
    \\ disch_tac
    \\ qpat_x_assum `compile _.data_conf _ _ _ = _` mp_tac
    \\ (data_to_word_compile_lab_pres
       |> Q.GENL[`data_conf`,`word_conf`,`asm_conf`,`prog`]
       |> C (specl_args_of_then``data_to_word$compile``)mp_tac)
    \\ simp []
    \\ rpt disch_tac
    \\ fs []
    \\ simp [SUBSET_DEF]
    \\ metis_tac [MAP_FST_stubs_bound, prim_recTheory.LESS_THM,
        EVAL ``gc_stub_location < data_num_stubs``, LESS_TRANS]
  )
  \\ rw [cake_orac_def, compile_inc_progs_defs]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ drule_then assume_tac MAP_FST_compile_word_to_stack
  \\ fs [REWRITE_RULE [o_DEF] MAP_MAP_o,
        word_to_wordTheory.full_compile_single_def, UNCURRY,
        Q.ISPEC `FST` ETA_THM]
QED

Theorem monotonic_labels_bvl_to_bvi:
  compile c prog = SOME (b, bm, c') /\ backend_config_ok c
  ==>
  oracle_monotonic (set o MAP FST o SND) (≠)
    (set (MAP FST (FST (SND (to_bvl c prog)))))
    (cake_orac c' syntax config_tuple2 (\ps. ps.bvl_prog))
  ==>
  oracle_monotonic (set o MAP FST o SND) (≠)
    (set (MAP FST (FST (SND (to_bvi c prog)))) ∪ count (SUC data_num_stubs))
    (cake_orac c' syntax (SND o SND o SND o config_tuple2) (\ps. ps.bvi_prog))
Proof
  rw []
  \\ irule (Q.ISPEC `\i. i MOD bvl_to_bvi_namespaces` oracle_monotonic_slice)
  \\ rw []
  \\ reverse (Cases_on `z < bvl_to_bvi_namespaces`)
  >- (
    simp [oracle_monotonic_def, IN_PREIMAGE]
    \\ metis_tac [MOD_LESS, EVAL ``0 < bvl_to_bvi_namespaces``]
  )
  \\ Cases_on `z = 0`
  >- (
    (* labels in modulus group 0 are passed through from bvl *)
    irule (Q.ISPEC `count bvl_num_stubs`
        oracle_monotonic_handle_init_component)
    \\ conj_tac >- (
      simp [IN_PREIMAGE]
      \\ rw [cake_orac_def, compile_inc_progs_defs, bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
      \\ CCONTR_TAC \\ fs []
      \\ drule_then drule tailrec_compile_prog_MEM_not_nss_2
      \\ drule_then drule configs_nn2_MOD_namespaces_ok
      \\ rw [configs_nn2_MOD_namespaces]
      \\ CCONTR_TAC \\ fs []
      \\ drule_then drule
            (GEN_ALL bvl_to_bviProofTheory.compile_inc_next_range)
      \\ qpat_x_assum `_ < bvl_num_stubs` mp_tac
      \\ EVAL_TAC \\ simp []
    )
    \\ first_x_assum (fn t => mp_tac t
      \\ match_mp_tac (Q.ISPEC
          `\n. (n - bvl_num_stubs) DIV bvl_to_bvi_namespaces`
          oracle_monotonic_subset_inject))
    \\ simp []
    \\ conj_tac >- (
      simp [to_bvi_def, bvl_to_bviTheory.compile_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
      \\ simp [SUBSET_DEF, PULL_EXISTS, IN_PREIMAGE]
      \\ gen_tac
      \\ Cases_on `n < SUC data_num_stubs`
      >- ( pop_assum mp_tac \\ EVAL_TAC \\ simp [] )
      \\ rw []
      \\ drule_then drule tailrec_compile_prog_MEM_not_nss_2
      \\ simp [EVAL ``(bvl_num_stubs + 2) MOD bvl_to_bvi_namespaces``]
      \\ disch_tac
      \\ old_drule bvl_to_bviProofTheory.compile_prog_code_labels_domain
      \\ imp_res_tac bvl_inlineProofTheory.compile_prog_names
      \\ disch_tac \\ fs []
      \\ qpat_x_assum `_ MOD _ = 0` mp_tac
      \\ qpat_x_assum `~ (_ < bvl_num_stubs)` mp_tac
      \\ simp [EVAL ``0 < bvl_to_bvi_namespaces``, arithmeticTheory.MULT_DIV]
      \\ TRY (qpat_x_assum `MEM _ (MAP FST (stubs _ _))` mp_tac)
      \\ EVAL_TAC \\ rw [] \\ simp []
    )
    \\ rw [cake_orac_def, compile_inc_progs_defs, bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ rveq \\ fs []
    \\ simp [SUBSET_DEF, PULL_EXISTS, IN_PREIMAGE]
    \\ drule_then drule configs_nn2_MOD_namespaces_ok
    \\ rw []
    \\ drule_then drule tailrec_compile_prog_MEM_not_nss_2
    \\ rw [configs_nn2_MOD_namespaces]
    \\ drule_then drule
          (GEN_ALL bvl_to_bviProofTheory.compile_inc_next_range)
    \\ imp_res_tac inline_compile_inc_names
    \\ simp []
  )
  \\ Cases_on `z = 1`
  >- (
    (* labels in modulus `2` are allocated by bvl_to_bvi *)
    irule (Q.ISPEC `((<) : num -> num -> bool)` oracle_monotonic_rel_mono)
    \\ simp []
    \\ irule (Q.ISPEC `\cfg. bvl_num_stubs
                + (cfg.bvl_conf.next_name1 * bvl_to_bvi_namespaces)`
            cake_orac_monotonic_bounded_state)
    \\ simp [IN_PREIMAGE]
    \\ conj_tac
    >- (
      simp [compile_inc_progs_defs, bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def]
      \\ rpt (gen_tac ORELSE disch_tac)
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
      \\ imp_res_tac bvl_to_bviProofTheory.compile_inc_next
      \\ simp []
      \\ rpt (gen_tac ORELSE disch_tac)
      \\ fs []
      \\ drule_then drule configs_nn2_MOD_namespaces_ok
      \\ drule_then drule tailrec_compile_prog_MEM_not_nss_2
      \\ simp [configs_nn2_MOD_namespaces]
      \\ rpt disch_tac \\ fs []
      \\ drule_then drule
            (GEN_ALL bvl_to_bviProofTheory.compile_inc_next_range)
      \\ simp []
    )
    \\ rw []
    \\ TRY (qpat_x_assum `_ < SUC _` mp_tac \\ EVAL_TAC \\ simp [])
    \\ fs [backendTheory.compile_def, backendTheory.compile_tap_def,
          to_bvi_def, to_bvl_def, to_clos_def, to_flat_def,
          bvl_to_bviTheory.compile_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ drule_then assume_tac attach_bitmaps_SOME
    \\ ntac 5 (rveq \\ fs [])
    \\ drule_then drule tailrec_compile_prog_MEM_not_nss_2
    \\ simp [EVAL ``(bvl_num_stubs + 2) MOD bvl_to_bvi_namespaces``]
    \\ rw []
    \\ old_drule bvl_to_bviProofTheory.compile_prog_code_labels_domain
    \\ disch_tac \\ fs []
    \\ fs [EVAL ``0 < bvl_to_bvi_namespaces``, EVAL ``bvl_num_stubs MOD bvl_to_bvi_namespaces``]
    \\ TRY (qpat_x_assum `MEM _ (MAP FST (stubs _ _))` mp_tac)
    \\ EVAL_TAC \\ rw [] \\ simp []
  )
  \\ Cases_on `z = 2`
  >- (
    (* labels in modulus `2` are allocated by bvi_tailrec *)
    irule (Q.ISPEC `((<) : num -> num -> bool)` oracle_monotonic_rel_mono)
    \\ simp []
    \\ drule_then (mp_tac o GSYM) bvl_to_bvi_orac_eq
    \\ simp [full_co_def]
    \\ disch_then kall_tac
    \\ irule (Q.ISPEC `\n. n MOD bvl_to_bvi_namespaces = 2`
            oracle_monotonic_state_with_inv
        |> Q.SPEC `\n. n`)
    \\ drule_then (fn t => simp [t]) is_state_oracle_tailrec_cake_orac
    \\ conj_tac
    >- (
      rpt (gen_tac ORELSE disch_tac)
      \\ fs [pred_setTheory.IN_PREIMAGE]
      \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
      \\ disch_tac \\ fs [EVAL ``0 < bvl_to_bvi_namespaces``]
      \\ rpt (gen_tac ORELSE disch_tac)
      \\ fs []
      \\ drule_then drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
      \\ rpt (gen_tac ORELSE disch_tac)
      \\ fs [state_co_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
      \\ drule_then drule
            (GEN_ALL bvl_to_bviProofTheory.compile_inc_next_range)
      \\ simp []
    )
    \\ simp [FST_state_co, pred_setTheory.IN_PREIMAGE, cake_orac_0,
            config_tuple2_def]
    \\ fs [backendTheory.compile_def, backendTheory.compile_tap_def,
          to_bvi_def, to_bvl_def, to_clos_def, to_flat_def,
          bvl_to_bviTheory.compile_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ drule_then assume_tac attach_bitmaps_SOME
    \\ ntac 6 (rveq \\ fs [])
    \\ drule bvi_tailrecProofTheory.compile_prog_next_mono
    \\ disch_tac \\ fs []
    \\ simp [EVAL ``0 < bvl_to_bvi_namespaces``,
        EVAL ``(bvl_num_stubs + 2) MOD bvl_to_bvi_namespaces``]
    \\ assume_tac (EVAL ``SUC data_num_stubs <= bvl_num_stubs``)
    \\ fs [] \\ rw [] \\ simp []
    \\ drule_then drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_MEM)
    \\ disch_tac \\ fs []
    \\ drule_then drule (GEN_ALL compile_prog_avoids_nss_2)
    \\ simp []
  )
  \\ qpat_x_assum `z < _`
    (mp_tac o CONV_RULE EVAL o REWRITE_RULE [GSYM IN_COUNT])
  \\ simp []
QED

Theorem syntax_oracle_ok_start:
  clos_to_bvlProof$syntax_oracle_ok c (c' with start updated_by f) es co =
  clos_to_bvlProof$syntax_oracle_ok c c' es co
Proof
  simp [clos_to_bvlProofTheory.syntax_oracle_ok_def]
QED

Theorem monotonic_labels_bvl:
  compile c prog = SOME (b, bm, c') /\ backend_config_ok c
  ==>
  oracle_monotonic (set o MAP FST o SND) (≠)
    (set (MAP FST (FST (SND (to_bvl c prog)))))
    (cake_orac c' syntax config_tuple2 (\ps. ps.bvl_prog))
Proof
  rw []
  \\ qpat_assum `_ = SOME _`
    (assume_tac o REWRITE_RULE [backendTheory.compile_def])
  \\ fs [compile_tap_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ drule attach_bitmaps_SOME
  \\ rw []
  \\ drule_then drule (GEN_ALL cake_orac_clos_syntax_oracle_ok)
  \\ simp [to_clos_def, to_flat_def]
  \\ disch_then (qspec_then `syntax` mp_tac)
  \\ impl_tac >- (
    fs [backend_config_ok_def] \\ metis_tac []
  )
  \\ disch_tac
  \\ irule (Q.ISPEC `((<) : num -> num -> bool)` oracle_monotonic_rel_mono)
  \\ simp []
  \\ drule_then drule (GEN_ALL
    (Q.INST_TYPE [`:'a` |-> `:'x`] syntax_oracle_ok_bvl_FST_monotonic))
  \\ drule_then (fn t => simp [t]) clos_to_bvl_orac_eq
  \\ match_mp_tac backendPropsTheory.oracle_monotonic_subset
  \\ simp [cake_orac_0, config_tuple1_def]
  \\ simp [to_bvl_def, to_clos_def, to_flat_def]
  \\ fs [clos_to_bvlTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ drule clos_to_bvlProofTheory.compile_common_MAP_FST_compile_prog
  \\ imp_res_tac clos_to_bvlProofTheory.compile_common_max_app
  \\ simp [clos_to_bvlProofTheory.set_MAP_code_sort]
  \\ rw []
  >- (
    rw [SUBSET_DEF, miscTheory.toAList_domain]
    \\ drule clos_to_bvlProofTheory.domain_init_code_lt_num_stubs
    \\ simp []
  )
  \\ simp [clos_to_bvlTheory.num_stubs_def]
QED

Theorem good_code_lab_oracle:
  compile c prog = SOME (b, bm, c') /\
  (* validity of the code produced in the oracle at step i
    - the tricky bit is cfg.labels, which gathers past and current labels
    - older labels must always be there
    - newer labels should never overlap older ones
  *)
  cake_orac c' syntax (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2)
    (λps. ps.lab_prog) i = (cfg,code) /\
  backend_config_ok c /\
  conf = c.lab_conf.asm_conf /\ conf = mc.target.config /\
  lab_to_targetProof$mc_conf_ok mc
  ==>
  lab_to_targetProof$good_code conf cfg.labels code
Proof
  simp [cake_orac_def, compile_inc_progs_defs]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [] \\ rveq \\ fs []
  \\ simp[stack_to_labTheory.compile_no_stubs_def, good_code_def]
  \\ qmatch_goalsub_abbrev_tac`MAP prog_to_section ppg`
  \\ `stack_to_labProof$labels_ok (MAP prog_to_section ppg)`
  by (
    old_drule_then match_mp_tac (Q.GEN `cfg` lab_labels_ok_oracle)
    \\ simp [cake_orac_def, compile_inc_progs_defs, stack_to_labTheory.compile_no_stubs_def]
  )
  \\ drule labels_ok_imp
  \\ simp[]
  \\ strip_tac
  \\ simp[CONJ_ASSOC]
  \\ reverse conj_tac
  >- (
    fs [backend_config_ok_def]
    \\ irule compile_all_enc_ok_pre
    \\ reverse conj_tac >- (
      first_x_assum irule
      \\ fs[mc_conf_ok_def]
      \\ fs[WORD_LE,labPropsTheory.good_dimindex_def,word_2comp_n2w,dimword_def,word_msb_n2w]
    )
    \\ simp[Abbr`ppg`]
    \\ irule stack_namesProofTheory.stack_names_stack_asm_ok
    \\ drule_then (fn t => simp [t]) cake_orac_config_eqs
    \\ simp[Once EVERY_MAP]
    \\ simp[LAMBDA_PROD]
    \\ simp[stack_removeTheory.prog_comp_def]
    \\ simp[Once EVERY_MEM, FORALL_PROD]
    \\ rpt gen_tac \\ strip_tac
    \\ irule stack_removeProofTheory.stack_remove_comp_stack_asm_name
    \\ simp[]
    \\ conj_tac >- fs[mc_conf_ok_def]
    \\ rpt (conj_tac >- ( fs[] \\ EVAL_TAC \\ fs[] ))
    \\ pop_assum mp_tac
    \\ simp[Once MEM_MAP, EXISTS_PROD]
    \\ simp[stack_allocTheory.prog_comp_def]
    \\ simp[FST_EQ_EQUIV]
    \\ strip_tac
    \\ qhdtm_x_assum`comp`mp_tac
    \\ specl_args_of_then``stack_alloc$comp`` stack_allocProofTheory.stack_alloc_comp_stack_asm_name
          (Q.ISPEC_THEN`mc.target.config`mp_tac o Q.GEN`c`)
    \\ ntac 2 strip_tac \\ fs[]
    \\ rfs []
    \\ first_x_assum match_mp_tac
    \\ qmatch_asmsub_abbrev_tac`compile_word_to_stack kkk pp qq`
    \\ Cases_on`compile_word_to_stack kkk pp qq`
    \\ drule (Q.GEN`c`compile_word_to_stack_convs)
    \\ disch_then(qspec_then`mc.target.config`mp_tac)
    \\ impl_tac
    >- (
      reverse conj_tac
      >- ( fs[Abbr`kkk`] \\ drule_then (fn t => simp [t]) cake_orac_config_eqs )
      \\ qmatch_asmsub_abbrev_tac`Abbrev (pp = MAP _ pp0)`
      \\ drule_then assume_tac (GEN_ALL MAP_full_compile_single_to_compile)
      \\ drule_then (fn t => rfs [t]) cake_orac_config_eqs
      \\ drule compile_to_word_conventions2
      \\ simp[]
      \\ simp[EVERY_MEM, UNCURRY, Abbr`kkk`]
      \\ rw[]
      \\ first_x_assum drule
      \\ rw[]
      \\ first_x_assum irule
      \\ simp[Abbr`pp0`, FORALL_PROD]
      \\ simp[MEM_MAP, EXISTS_PROD]
      \\ simp[data_to_wordTheory.compile_part_def]
      \\ simp[PULL_EXISTS] \\ rw[]
      \\ irule data_to_wordProofTheory.comp_no_inst
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
    \\ simp[]
  )
  \\ conj_tac >- (
    old_drule monotonic_DISJOINT_labels_lab
    \\ impl_tac >- (
      drule_then irule monotonic_labels_stack_to_lab
      \\ simp []
      \\ drule_then irule monotonic_labels_bvi_down_to_stack
      \\ simp []
      \\ drule_then irule monotonic_labels_bvl_to_bvi
      \\ simp []
      \\ drule_then irule monotonic_labels_bvl
      \\ simp []
    )
    \\ simp[config_tuple2_def]
    \\ disch_tac
    \\ drule_then irule DISJOINT_SUBSET
    \\ simp [Abbr `ppg`]
    \\ simp [cake_orac_def, compile_inc_progs_defs, stack_to_labTheory.compile_no_stubs_def]
    \\ qmatch_goalsub_abbrev_tac`MAP prog_to_section ps`
    \\ simp [labPropsTheory.get_code_labels_def]
    \\ simp [SUBSET_DEF, MEM_MAP, PULL_EXISTS]
    \\ simp [stack_to_labTheory.prog_to_section_def, UNCURRY, PULL_EXISTS,
       labPropsTheory.sec_get_code_labels_def, EXISTS_PROD, FORALL_PROD]
    \\ metis_tac []
  )
  \\ drule (word_to_stack_good_handler_labels_incr
    |> REWRITE_RULE [AND_IMP_INTRO, Once CONJ_COMM] |> GEN_ALL)
  \\ impl_tac >- simp [word_good_handlers_word_to_word_incr,
    data_to_word_good_handlers_incr]
  \\ disch_tac
  \\ drule_then drule (stack_to_lab_stack_good_handler_labels_incr
    |> REWRITE_RULE [Once CONJ_COMM] |> GEN_ALL)
  \\ simp [GSYM PULL_EXISTS]
  \\ reverse impl_tac >- simp [SUBSET_DEF]
  \\ simp [stack_to_labTheory.compile_no_stubs_def, Abbr `ppg`] \\ metis_tac []
QED

Theorem oracle_stack_good_code:
  compile c prog = SOME (b, bm, c') /\
  reg_count_sub = (c.lab_conf.asm_conf.reg_count
    - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3)) /\
  backend_config_ok c /\ lab_to_targetProof$mc_conf_ok mc /\
  c.lab_conf.asm_conf = mc.target.config ==>
  stack_to_labProof$good_code reg_count_sub
    (FST (SND (cake_orac c' syntax f (\ps. (ps.stack_prog, ps.cur_bm)) n)))
Proof
  strip_tac
  \\ old_drule cake_orac_stack_ALL_DISTINCT
  \\ fs [cake_orac_def, compile_inc_progs_defs]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw [] \\ rveq \\ fs []
  \\ simp [stack_to_labProofTheory.good_code_def]
  \\ imp_res_tac word_to_stackProofTheory.MAP_FST_compile_word_to_stack
  \\ simp [Q.SPEC`P o FST`(INST_TYPE[alpha|->``:'a # 'b``]EVERY_CONJ)
              |> Q.SPEC`Q o SND` |> SIMP_RULE (srw_ss()) [LAMBDA_PROD]]
  \\ simp [GSYM ALL_EL_MAP, GSYM CONJ_ASSOC]
  \\ simp [MAP_MAP_o, o_DEF, word_to_wordTheory.full_compile_single_def, UNCURRY]
  \\ simp [ETA_THM]
  \\ conj_tac >- (
    old_drule bvl_num_stubs_LE_bvi_prog
    \\ simp [cake_orac_def, compile_inc_progs_defs]
    \\ match_mp_tac listTheory.EVERY_MONOTONIC
    \\ EVAL_TAC
    \\ simp []
  )
  \\ qmatch_asmsub_abbrev_tac`compile_word_to_stack kkk pp`
  \\ drule (GEN_ALL compile_word_to_stack_convs)
  \\ disch_then(qspec_then`mc.target.config`mp_tac)
  \\ simp[]
  \\ qmatch_asmsub_abbrev_tac`Abbrev (pp = MAP _ pp0)`
  \\ drule_then assume_tac (GEN_ALL MAP_full_compile_single_to_compile)
  \\ rfs []
  \\ drule compile_to_word_conventions2
  \\ drule_then (fn t => simp [t]) cake_orac_config_eqs
  \\ simp[]
  \\ strip_tac
  \\ impl_tac
  >- (
    simp[EVERY_MAP, LAMBDA_PROD]
    \\ fs[Abbr`kkk`]
    \\ fs [backend_config_ok_def, lab_to_targetProofTheory.mc_conf_ok_def]
    \\ drule_then (fn t => simp [t]) cake_orac_config_eqs
    \\ fs[EVERY_MEM] \\ rw[]
    \\ first_x_assum drule
    \\ pairarg_tac \\ rw[]
    \\ first_x_assum irule
    \\ simp[Abbr`pp0`, FORALL_PROD]
    \\ simp[MEM_MAP, EXISTS_PROD]
    \\ simp[data_to_wordTheory.compile_part_def]
    \\ simp[PULL_EXISTS] \\ rw[]
    \\ irule data_to_wordProofTheory.comp_no_inst
    \\ drule_then (fn t => simp [t]) cake_orac_config_eqs
    \\ fs[backend_config_ok_def, asmTheory.offset_ok_def, ensure_fp_conf_ok_def]
    \\ rpt (pairarg_tac \\ fs[])
    \\ fsrw_tac[DNF_ss][]
    \\ conj_tac \\ first_x_assum irule
    \\ fs[mc_conf_ok_def]
    \\ fs[WORD_LE,labPropsTheory.good_dimindex_def,word_2comp_n2w,dimword_def,word_msb_n2w])
  \\ simp[]
  \\ strip_tac
  \\ simp[EVERY_MAP]
  \\ rw [] \\ TRY (
    first_x_assum (fn t => mp_tac t \\ match_mp_tac MONO_EVERY)
    \\ simp [UNCURRY]
    \\ simp [Abbr `kkk`]
    \\ drule_then (fn t => simp [t]) cake_orac_config_eqs
    \\ rw []
    \\ drule_then irule word_to_stackProofTheory.reg_bound_mono
    \\ fs [backend_config_ok_def]
  )
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
  \\ qspecl_then[`c4_data_conf`,`pp40`,`2`,`pp42`]mp_tac data_to_wordProofTheory.data_to_word_lab_pres_lem
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
  \\ simp[]
QED

Theorem to_lab_good_code_lemma:
  compile c.stack_conf c.data_conf lim1 lim2 offs stack_prog = code /\
  compile asm_conf3 word_prog = (bm, wc, fs, stack_prog) /\
  compile data_conf word_conf asm_conf2 data_prog = (col, word_prog) /\
  stack_to_labProof$labels_ok code /\
  all_enc_ok_pre conf code
  ==>
  lab_to_targetProof$good_code conf LN code
Proof
  (* start of 'good_code' proof for initial compilation *)
  rw []
  \\ qmatch_asmsub_abbrev_tac `stack_to_labProof$labels_ok lab_prog`
  \\ fs[good_code_def]
  \\ CONJ_TAC >- fs[Abbr `lab_prog`, stack_to_labTheory.compile_def]
  \\ CONJ_ASM1_TAC >- (
    fs [labels_ok_def]
    \\ qpat_x_assum `all_enc_ok_pre _ _` kall_tac
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC)
    \\ simp[] \\ Cases \\ simp[]
    \\ metis_tac [labPropsTheory.EVERY_sec_label_ok]
  )
  \\ CONJ_TAC >- (
    fs [labels_ok_def]
    \\ qmatch_asmsub_abbrev_tac `ALL_DISTINCT (MAP ff _)`
    \\ `ff = Section_num` by
      (simp[Abbr`ff`,FUN_EQ_THM]>>Cases>>simp[])
    \\ fs [])
  \\ CONJ_TAC >- (
    fs [labels_ok_def]
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC
      \\ simp[] \\ Cases \\ simp[] \\ NO_TAC)
  ) >>
  qpat_x_assum`Abbrev(lab_prog = _)` mp_tac>>
  simp[markerTheory.Abbrev_def]>>
  disch_then (assume_tac o SYM)>>
  drule stack_to_lab_stack_good_handler_labels
  \\ simp []
  \\ disch_then match_mp_tac
  \\ drule data_to_wordProofTheory.data_to_word_good_handlers
  \\ disch_tac
  \\ drule_then drule word_to_stack_good_handler_labels
  \\ simp []
QED

Theorem data_to_word_orac_eq_std = data_to_word_orac_eq
  |> SPEC_ALL |> Q.GEN `f4` |> Q.ISPEC `(SND ∘ SND ∘ SND ∘ config_tuple2)` |> GEN_ALL

Theorem data_to_word_orac_eq_sym_std = data_to_word_orac_eq_std
  |> SIMP_RULE bool_ss []
  |> SPEC_ALL |> UNDISCH_ALL |> GSYM |> DISCH_ALL |> GEN_ALL

(*
max_print_depth := 20
*)

Definition compute_stack_frame_sizes_def:
  compute_stack_frame_sizes c word_prog =
    let reg_count = c.reg_count - LENGTH c.avoid_regs - 5 in
      mapi (λn (arg_count,prog).
              let stack_arg_count = arg_count - reg_count ;
                  stack_var_count = MAX (max_var prog DIV 2 + 1 - reg_count) stack_arg_count ;
              in if stack_var_count = 0 then 0 else stack_var_count + 1)
        (fromAList (word_prog))
End

Theorem compute_stack_frame_sizes_thm:
  compute_stack_frame_sizes c word_prog =
    let k = c.reg_count - LENGTH c.avoid_regs - 5 in
      mapi (λn (arg_count,prog).
        FST (SND (compile_prog prog arg_count k (Nil,0)))) (fromAList word_prog)
Proof
  fs [compute_stack_frame_sizes_def]
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ qmatch_goalsub_abbrev_tac `compile_prog _ _ k`
  \\ fs [FUN_EQ_THM,FORALL_PROD]
  \\ rpt gen_tac
  \\ once_rewrite_tac [word_to_stackTheory.compile_prog_def]
  \\ rewrite_tac [LET_THM]
  \\ CONV_TAC (DEPTH_CONV BETA_CONV)
  \\ pairarg_tac \\ asm_rewrite_tac [FST,SND]
  \\ simp []
QED

Definition is_64_bits_def:
  is_64_bits (c:'a backend$config) <=> (dimindex (:'a) = 64)
End

Definition is_safe_for_space_def:
  is_safe_for_space ffi c prog stack_heap_limit =
    let data_prog = FST (SND (to_data c prog)) in
    let word_prog = FST (SND (to_word c prog)) in
      dataSem$data_lang_safe_for_space ffi (fromAList data_prog)
        (dataSem$compute_limits c.data_conf.len_size (is_64_bits c) c.data_conf.has_fp_ops c.data_conf.has_fp_tern stack_heap_limit)
        (compute_stack_frame_sizes c.lab_conf.asm_conf word_prog) InitGlobals_location /\
      c.data_conf.gc_kind <> None
End

Theorem compile_word_conf_eq:
  ∀c prog code data conf w_conf stack_prog stack_names.
    (backend$compile c prog = SOME (code,data,conf)) ∧
    (to_stack c prog = (bm, w_conf,stack_prog,stack_names))
    ⇒ conf.word_conf.stack_frame_size = w_conf.word_conf.stack_frame_size
Proof
  srw_tac[][FUN_EQ_THM,backendTheory.compile_def,compile_tap_def,
     to_target_def,
     to_lab_def,
     to_stack_def,
     to_word_def,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_flat_def]
  \\ unabbrev_all_tac
  \\ rpt (CHANGED_TAC (srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[]))
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ rfs []
  \\ fs [backendTheory.compile_def,compile_tap_def
        ,compute_stack_frame_sizes_thm
        ,to_word_def,to_data_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [] \\ rveq \\ rfs [] \\ rveq
  \\ qmatch_asmsub_abbrev_tac `attach_bitmaps _ _ _ c0`
  \\ Cases_on `c0` \\ fs [attach_bitmaps_def]
  \\ PairCases_on `x` \\ fs [attach_bitmaps_def]
  \\ UNABBREV_ALL_TAC \\ rfs [] \\ rveq \\ fs []
QED

Theorem to_word_lab_conf:
  ∀c c' prog p n.
    (to_word c prog = (c',p,n))
    ⇒ c.lab_conf = c'.lab_conf
Proof
  srw_tac[][FUN_EQ_THM,backendTheory.compile_def,compile_tap_def,
     to_word_def,
     to_data_def,
     to_bvi_def,
     to_bvl_def,
     to_clos_def,
     to_flat_def]
  \\ rpt (CHANGED_TAC (srw_tac[][] >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> rev_full_simp_tac(srw_ss())[]))
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ rfs []
  \\ fs [backendTheory.compile_def,compile_tap_def
        ,compute_stack_frame_sizes_thm
        ,to_word_def,to_data_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs [] \\ rveq \\ rfs [] \\ rveq
QED


(* TODO: MOVE *)
Theorem PERM_toAList_fromAList:
  ∀p. ALL_DISTINCT (MAP FST p) ⇒ PERM (toAList (fromAList p)) p
Proof
  rw []
  \\ ho_match_mp_tac PERM_ALL_DISTINCT
  \\ conj_tac
  >- (qspec_then `FST` ho_match_mp_tac ALL_DISTINCT_MAP
     \\ rw [ALL_DISTINCT_MAP_FST_toAList])
  \\ conj_tac
  >- (drule ALL_DISTINCT_MAP \\ fs [])
  \\ rw [] \\ PairCases_on `x`
  \\ rw [MEM_toAList,lookup_fromAList]
  \\ drule MEM_ALOOKUP \\ rw []
QED

Theorem compile_word_to_stack_sfs_aux:
∀k p bm progs' fs' bitmaps.
  compile_word_to_stack k p bm = (progs',fs',bitmaps) ⇒
   fromAList
     (MAP
        (λkv.
             (FST kv,
              (λ(arg_count,prog).
                   FST (SND (compile_prog prog arg_count k (Nil,0)))) (SND kv))) p)
   = fromAList (MAP (λ((i,_),n). (i,n)) (ZIP (progs',fs')))
Proof
  ho_match_mp_tac compile_word_to_stack_ind
  \\ rw [fromAList_def,compile_word_to_stack_def] \\ fs [fromAList_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ rw [fromAList_def] \\ rveq \\ rfs []
  \\ Cases_on `compile_prog p n k (Nil,0)`
  \\ PairCases_on `r` \\ rfs [] \\ rveq \\ fs []
  \\  `f = r0` suffices_by fs []
  \\ fs [compile_prog_def]
  \\ qmatch_asmsub_abbrev_tac `_ p0 = (q,_,_)`
  \\ qmatch_asmsub_abbrev_tac `_ p1 = (prog,_,_)`
  \\ pairarg_tac \\ rveq \\ rfs [] \\ rveq
  \\ pairarg_tac \\ rveq \\ rfs [] \\ rveq
QED

Theorem IMP_is_safe_for_space:
  backend_config_ok c ⇒
  compile c prog = SOME (code,data,conf) ⇒
  to_data c prog = (bvi_conf,data_prog,names) ⇒
  c.data_conf.gc_kind <> None ⇒
  dataSem$data_lang_safe_for_space ffi (fromAList data_prog)
    (dataSem$compute_limits c.data_conf.len_size (is_64_bits c) c.data_conf.has_fp_ops c.data_conf.has_fp_tern stack_heap_limit)
    conf.word_conf.stack_frame_size InitGlobals_location
  ⇒ is_safe_for_space ffi c prog stack_heap_limit
Proof
  rw [word_to_stackTheory.compile_def,word_to_stackTheory.compile_prog_def
     ,is_safe_for_space_def]
  \\ qmatch_goalsub_abbrev_tac `dataSem$data_lang_safe_for_space _ _ _ sfs0`
  \\ qmatch_asmsub_abbrev_tac `dataSem$data_lang_safe_for_space _ _ _ sfs1`
  \\ `sfs0 = sfs1` suffices_by fs []
  \\ UNABBREV_ALL_TAC
  \\ fs [compute_stack_frame_sizes_thm]
  \\ Cases_on `to_stack c prog` \\ PairCases_on `r`
  \\ drule_then drule compile_word_conf_eq
  \\ rw []
  \\ fs [to_stack_def,word_to_stackTheory.compile_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq \\ fs []
  \\ fs [compile_word_to_stack_def]
  \\ rw [fromAList_def]
  \\ drule_then drule to_word_labels_ok
  \\ rw [] \\ ntac 2 (pop_assum kall_tac)
  \\ fs [mapi_Alist]
  \\ drule_then assume_tac PERM_toAList_fromAList
  \\ qmatch_goalsub_abbrev_tac `fromAList (MAP f0 _)`
  \\ drule_then (qspec_then `f0` assume_tac) PERM_MAP
  \\ drule PERM_IMP_fromAList_EQ_fromAList
  \\ impl_tac
  >- (qspecl_then [`MAP FST (MAP f0 (toAList (fromAList p)))`,
                  `MAP FST (MAP f0 p)`] mp_tac ALL_DISTINCT_PERM
     \\ impl_tac >- rw [PERM_MAP]
     \\ rw [MAP_MAP_o]
     \\ `FST o f0 = FST` suffices_by fs []
     \\ rw [FUN_EQ_THM]
     \\ Cases_on `x`
     \\ UNABBREV_ALL_TAC
     \\ rw [])
  \\ rw [Abbr`f0`]
  \\ ntac 2 (pop_assum kall_tac)
  \\ qpat_x_assum `compile_word_to_stack _ _ _ = _` mp_tac
  \\ qmatch_goalsub_abbrev_tac `compile_word_to_stack k0`
  \\ qmatch_goalsub_abbrev_tac `compile_prog _ _ k1 `
  \\ `k0 = k1` suffices_by
     (rw [] \\ ho_match_mp_tac compile_word_to_stack_sfs_aux
     \\ asm_exists_tac \\ fs [])
  \\ UNABBREV_ALL_TAC
  \\ drule to_word_lab_conf
  \\ rw []
QED

Definition read_limits_def:
  read_limits (c:'a config) mc ms =
    stack_removeProof$get_stack_heap_limit
      (2 * max_heap_limit (:α) c.data_conf - 1)
      (mc.target.get_reg ms (find_name c.stack_conf.reg_names 2) :'a word,
       mc.target.get_reg ms (find_name c.stack_conf.reg_names 3) :'a word,
       mc.target.get_reg ms (find_name c.stack_conf.reg_names 4) :'a word)
End

Triviality FST_SND_EQ:
  (FST x = y /\ SND x = z <=> x = (y,z)) /\
  (SND x = z /\ FST x = y <=> x = (y,z))
Proof
  Cases_on `x` \\ fs [] \\ metis_tac []
QED

Triviality PERMUTE_IMP_LINV:
  f PERMUTES UNIV ⇒ ∀x y. (y = LINV f UNIV x ⇔ x = f y)
Proof
  rw [] \\ eq_tac \\ rw []
  \\ imp_res_tac pred_setTheory.BIJ_LINV_INV \\ fs [BIJ_DEF]
  \\ imp_res_tac pred_setTheory.LINV_DEF \\ fs []
QED

Theorem state_co_inc_compile_has_flat_comp:
  compile c prog = SOME (b,bm,c') ==>
  state_co (\c (env_id,decs:ast$dec list). inc_compile env_id c (f decs)) (cake_orac c' src config_tuple1 g) =
  pure_co (MAP (flat_pattern$compile_dec c.source_conf.pattern_cfg)) o
  state_co (\c (env_id,decs). inc_compile_prog env_id c (f decs)) (cake_orac c' src config_tuple1 g)
Proof
  simp [FUN_EQ_THM, state_co_def, pure_co_def, UNCURRY]
  \\ simp [source_to_flatTheory.inc_compile_def, source_to_flatTheory.compile_flat_def, UNCURRY]
  \\ rw []
  \\ AP_THM_TAC
  \\ simp [source_to_flatTheory.inc_compile_prog_def, UNCURRY]
  \\ simp [cake_orac_def, UNCURRY, config_tuple1_def]
  \\ drule_then (simp o single) cake_orac_config_eqs
QED

Definition add_eval_state_def:
  add_eval_state NONE s0 = s0 /\
  add_eval_state (SOME ci) s0 =
    s0 with <| eval_state := SOME (mk_init_eval_state ci) |>
End

Theorem add_eval_state_ffi:
  (add_eval_state opt_ev s0).ffi = s0.ffi
Proof
  Cases_on `opt_ev` \\ simp [add_eval_state_def]
QED

(* delete?
Definition compile_inc_progs_for_eval_def:
  compile_inc_progs_for_eval asm_c x =
  let (env_id, inc_c', decs) = x in
  let c' = inc_config_to_config asm_c inc_c' in
  let (c'', ps) = compile_inc_progs T c' (env_id, decs) in
    OPTION_MAP (\(bs, ws). (config_to_inc_config c'', bs,
            MAP data_to_word_gcProof$upper_w2w ws))
        ps.target_prog
End
*)

Definition opt_eval_config_wf_def:
  opt_eval_config_wf c' (SOME ci) = (
    ci.compiler_fun = compile_inc_progs_for_eval c'.lab_conf.asm_conf /\
    INJ ci.config_v UNIV UNIV /\ ci.init_state = config_to_inc_config c') /\
  opt_eval_config_wf c' NONE = T
End

Definition backend_from_data_tuple_cc_def:
  backend_from_data_tuple_cc (c : 'a config) cfg =
    OPTION_MAP (I ## MAP data_to_word_gcProof$upper_w2w ## I) o
      (λprogs.
        (λ(bm0,cfg) progs.
          (λ(progs,fs,bm).
            OPTION_MAP
              (λ(bytes,cfg).
                (bytes,append (FST bm),(SND bm,cfg)))
              (compile cfg
                (MAP prog_to_section
                  (MAP
                    (prog_comp c.stack_conf.reg_names)
                    (MAP
                      (prog_comp c.stack_conf.jump
                        c.lab_conf.asm_conf.addr_offset
                        (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3)))
                      (MAP prog_comp progs))))))
           (compile_word_to_stack ((c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3))-2) progs (Nil, bm0)))
              cfg (MAP (λp. full_compile_single c.lab_conf.asm_conf.two_reg_arith (c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 5))
              c.word_to_word_conf.reg_alg
              c.lab_conf.asm_conf (p,NONE)) progs)) o
              MAP (compile_part (ensure_fp_conf_ok c.lab_conf.asm_conf c.data_conf))
End

Definition backend_from_flat_tuple_cc_def:
  backend_from_flat_tuple_cc (c : 'a config) =
    backendProps$pure_cc flat_to_clos$inc_compile_decs
      (clos_to_bvlProof$compile_common_inc c.clos_conf
         (backendProps$pure_cc (clos_to_bvl$compile_inc c.clos_conf.max_app)
           (bvl_to_bviProof$full_cc c.bvl_conf (backendProps$pure_cc bvi_to_data_compile_prog
             (backend_from_data_tuple_cc c)))))
End

Theorem known_cc_eq_state_cc_inc:
  clos_knownProof$known_cc kc cc =
  state_cc (known_compile_inc (known_static_conf kc)) cc
Proof
  Cases_on `kc`
  \\ simp [clos_knownProofTheory.known_cc_def,
           clos_knownTheory.known_compile_inc_def, clos_knownTheory.known_static_conf_def]
  \\ simp [pure_cc_def, state_cc_def, UNCURRY, clos_knownTheory.known_compile_inc_def]
  \\ rw [FUN_EQ_THM, FORALL_PROD]
  \\ simp [clos_to_bvlProofTheory.kcompile_inc_uncurry, clos_knownTheory.reset_inline_factor_def]
  \\ simp [known_reset_spt |> Q.SPEC `kc with inline_factor updated_by g`
        |> SIMP_RULE (srw_ss ()) []]
QED

Theorem known_compile_inc_retreive_spt:
  known_compile_inc (known_static_conf kcfg1)
    (clos_known$option_val_approx_spt kcfg2) p = (spt, p') /\
  IS_SOME kcfg2 = IS_SOME kcfg1 ==>
  clos_known$option_val_approx_spt (option_upd_val_spt spt kcfg2) = spt
Proof
  simp [clos_knownTheory.option_val_approx_spt_def, clos_knownTheory.option_upd_val_spt_def]
  \\ CASE_TAC
  \\ rw []
  \\ fs [clos_knownTheory.known_static_conf_def, clos_knownTheory.known_compile_inc_def]
  \\ rw [clos_knownTheory.option_upd_val_spt_def]
QED

Theorem backend_from_flat_tuple_cc_eq_compile_inc_progs:
  ((^cake_orac_config_inv_f) c') = ((^cake_orac_config_inv_f) c) /\
  src_cfg = c'.source_conf /\
  c.source_conf.pattern_cfg = prim_src_config.pattern_cfg ==>
  backend_from_flat_tuple_cc c (SND (config_tuple1 c'))
    (MAP (flat_pattern$compile_dec prim_src_config.pattern_cfg)
      (SND (inc_compile_prog env_id src_cfg (source_to_source$compile decs)))) =
  let (c'', ps) = compile_inc_progs T c' (env_id, decs) in
    OPTION_MAP (\(bs, ws). (bs,
        MAP data_to_word_gcProof$upper_w2w ws,
        SND (config_tuple1 c''))) ps.target_prog
Proof
  disch_tac
  \\ simp [compile_inc_progs_def, pure_cc_def, state_cc_def,
    clos_to_bvlTheory.clos_to_bvl_compile_inc_def,
    clos_to_bvlProofTheory.compile_common_inc_def,
    known_cc_eq_state_cc_inc, bvl_to_bviProofTheory.full_cc_def,
    bvl_to_bviTheory.bvl_to_bvi_compile_inc_all_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [config_tuple1_def, config_tuple2_def]
  \\ rveq \\ fs []
  \\ imp_res_tac source_compile_pattern_cfg
  \\ rfs []
  \\ fs [source_to_flatTheory.inc_compile_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ CASE_TAC
  \\ fs [stack_to_labTheory.compile_no_stubs_def, stack_namesTheory.compile_def]
  \\ simp [backend_from_flat_tuple_cc_def, pure_cc_def, state_cc_def,
    backend_from_data_tuple_cc_def,
    clos_to_bvlProofTheory.compile_common_inc_def, known_cc_eq_state_cc_inc,
    bvl_to_bviProofTheory.full_cc_def, stack_to_labTheory.compile_no_stubs_def, stack_namesTheory.compile_def]
  \\ simp [pairTheory.PAIR_MAP]
  \\ simp [UNCURRY]
  \\ imp_res_tac known_compile_inc_retreive_spt
  \\ simp []
  \\ every_case_tac
  \\ simp [DROP_APPEND]
QED

Triviality compile_inc_progs_src_env:
  (SND (compile_inc_progs T c env_decs)).env_id = FST env_decs /\
  (SND (compile_inc_progs T c env_decs)).source_prog = SND env_decs
Proof
  simp [compile_inc_progs_def, UNCURRY]
QED

Theorem cake_orac_cfg_f_eq_I:
  !f g. cake_orac c syntax f g = (f ## I) o cake_orac c syntax I g
Proof
  simp [FUN_EQ_THM, cake_orac_def, UNCURRY]
QED

Overload "mk_flat_install_conf" = “flatProps$mk_flat_install_conf”;

val mk_flat_install_conf_def = flatPropsTheory.mk_flat_install_conf_def;

Theorem config_wf_abs_conc:
  opt_eval_config_wf c' (SOME ci) ==>
  v_fun_abs dom ci.config_v (ci.config_v cfg) = (if cfg IN dom then SOME cfg else NONE)
Proof
  simp [opt_eval_config_wf_def, source_evalProofTheory.v_rel_abs, INJ_IFF]
  \\ DEEP_INTRO_TAC some_intro
  \\ fs []
  \\ CCONTR_TAC
  \\ gs []
QED

Triviality compile_asm_config_eq:
  compile (c : 'a config) prog = SOME (b,bm,c') ==>
  c'.lab_conf.asm_conf = c.lab_conf.asm_conf
Proof
  rw []
  \\ drule cake_orac_config_eqs
  \\ disch_then (qspecl_then [`0`, `syntax`] mp_tac)
  \\ rw []
  \\ fs [cake_configs_def, state_orac_states_def]
QED

Triviality cake_orac_extended_wf:
  compile (c : 'a config) prog = SOME (b,bm,c') /\
  opt_eval_config_wf c' (SOME ci) ==>
  orac_extended_wf (mk_compiler_fun_from_ci ci)
    ((\(cfg,id,ds). (id, ci.config_v (config_to_inc_config cfg), ds)) ∘
    cake_orac c' syntax I (λps. (ps.env_id,ps.source_prog)))
Proof
  simp [Once cake_orac_eq_I]
  \\ rw [source_evalProofTheory.orac_extended_wf_def, cake_orac_SUC2]
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [source_evalProofTheory.mk_compiler_fun_from_ci_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ imp_res_tac config_wf_abs_conc
  \\ rfs [opt_eval_config_wf_def]
  \\ fs [compile_inc_progs_for_eval_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ qpat_x_assum `compile_inc_progs _ (inc_config_to_config _ _) _ = _` mp_tac
  \\ dep_rewrite.DEP_REWRITE_TAC [inc_config_to_config_inv]
  \\ simp []
  \\ fs [cake_orac_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs []
  \\ drule cake_orac_config_eqs
  \\ imp_res_tac compile_asm_config_eq
  \\ simp []
QED

Triviality compile_inc_progs_asm_conf:
  compile_inc_progs k c p_env = (c', progs) ==>
  c'.lab_conf.asm_conf = c.lab_conf.asm_conf
Proof
  simp [compile_inc_progs_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ simp []
  \\ EVERY_CASE_TAC
  \\ fs [lab_to_targetTheory.compile_def]
  \\ imp_res_tac compile_lab_lab_conf
QED

Triviality cake_orac_eq_get_oracle:
  ¬ semantics_prog s env prog Fail /\
  opt_eval_config_wf c' (SOME ci) /\
  nsAll (K concrete_v) env.v /\ s.refs = [] /\
  s.eval_state = SOME (mk_init_eval_state ci) /\
  (!i r. get_oracle ci s env prog i = SOME r ==> syntax i = (I ## SND) r) /\
  s' = s
  ==>
  !i r x. get_oracle ci s' env prog i = SOME r /\
  cake_orac c' syntax I (\ps. (ps.env_id,ps.source_prog)) i = x ==>
  (case r of (id, cfg_v, ds) => ?cfg. cfg_v = ci.config_v cfg /\
    x = (inc_config_to_config c'.lab_conf.asm_conf cfg, id, ds))
Proof
  strip_tac
  \\ imp_res_tac config_wf_abs_conc
  \\ drule_then (drule_then drule) source_evalProofTheory.get_oracle_props
  \\ disch_then drule
  \\ strip_tac
  \\ Induct
  >- (
    simp [FORALL_PROD]
    \\ rpt (gen_tac ORELSE disch_tac)
    \\ fs [cake_orac_0, compile_inc_progs_src_env, opt_eval_config_wf_def]
    \\ rpt (first_x_assum drule)
    \\ rw []
    \\ irule_at Any EQ_REFL
    \\ simp [inc_config_to_config_inv]
  )
  >- (
    simp [FORALL_PROD]
    \\ rpt (gen_tac ORELSE disch_tac)
    \\ fs []
    \\ last_x_assum (fn t => qspec_then `i` mp_tac t \\ qspec_then `SUC i` mp_tac t)
    \\ rpt (first_x_assum drule)
    \\ simp [EXISTS_PROD]
    \\ rpt disch_tac
    \\ fs [cake_orac_SUC]
    \\ fs [cake_orac_def, source_evalProofTheory.mk_compiler_fun_from_ci_def]
    \\ imp_res_tac config_wf_abs_conc
    \\ rfs [opt_eval_config_wf_def, compile_inc_progs_for_eval_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ imp_res_tac compile_inc_progs_asm_conf
    \\ fs [compile_inc_progs_src_env]
    \\ gvs []
    \\ irule_at Any EQ_REFL
    \\ irule (GSYM inc_config_to_config_inv)
    \\ simp [backendTheory.inc_config_to_config_def,
        lab_to_targetTheory.inc_config_to_config_def]
  )
QED

Triviality compile_inc_config_inv:
  compile (c : 'a config) prog = SOME (b,bm,c') ==>
  inc_config_to_config c.lab_conf.asm_conf
    (config_to_inc_config (cake_configs c' syntax k)) =
    cake_configs c' syntax k
Proof
  rw []
  \\ drule cake_orac_config_eqs
  \\ simp [inc_config_to_config_inv]
QED

Triviality step_invs_cake_orac:
  st.oracle = f o cake_orac c' syn I I ==>
  (! x k env_id st decs. x = cake_orac c' syn I I k ==>
    f x = (env_id, st, decs) ==>
    decs = (SND x).source_prog /\
    env_id = (SND x).env_id /\
    (?d_st. decf st = SOME d_st /\ FST d_st = (FST x).source_conf)) ==>
  source_to_flatProof$src_orac_step_invs (SOME decf)
    (source_to_source$compile) (SOME (EvalOracle st))
Proof
  rw []
  \\ simp [source_to_flatProofTheory.src_orac_step_invs_def]
  \\ rw []
  >- (
    res_tac
    \\ simp [PAIR_FST_SND_EQ]
  )
  \\ Cases_on `SND (f (cake_orac c' syn I I (SUC k)))`
  \\ Cases_on `f (cake_orac c' syn I I (SUC k))`
  \\ gvs []
  \\ res_tac
  \\ simp [cake_orac_SUC2]
  \\ rpt (pairarg_tac \\ fs [])
  \\ gvs []
  \\ simp [compile_inc_progs_def]
  \\ simp [source_to_flatTheory.inc_compile_def, source_to_flatTheory.inc_compile_prog_def]
  \\ rpt (pairarg_tac \\ fs [])
QED

Triviality source_to_source_semantics_prog_equiv:
  ~ semantics_prog s0 env prog Fail ==>
  semantics_prog s0 env (source_to_source$compile prog) res =
  semantics_prog s0 env prog res
Proof
  metis_tac [semantics_prog_deterministic, semantics_prog_total,
                  source_to_sourceProofTheory.compile_semantics]
QED

Triviality source_to_source_semantics_prog_intro:
  ~ semantics_prog s0 env prog Fail ==>
  (~ semantics_prog s0 env (source_to_source$compile prog) Fail ==>
    semantics_prog s0 env (source_to_source$compile prog) res) ==>
  semantics_prog s0 env prog res
Proof
  metis_tac [semantics_prog_deterministic, semantics_prog_total,
                  source_to_sourceProofTheory.compile_semantics]
QED

Triviality eval_oracle_semantics_prog_intro:
  !ci. ~ semantics_prog s1 env decs Fail /\
  precond_eval_state orac ci s1 env decs /\ s1.refs = [] /\
  nsAll (K concrete_v) env.v /\
  (~ semantics_prog (s1 with eval_state := put_oracle ci orac) env decs Fail ==>
    semantics_prog (s1 with eval_state := put_oracle ci orac) env decs res) ==>
  semantics_prog s1 env decs res
Proof
  metis_tac [semantics_prog_deterministic, semantics_prog_total,
            source_evalProofTheory.oracle_semantics_prog]
QED

Triviality source_to_source_semantics_prog_oracle_intro:
  ~ semantics_prog (s0 with eval_state := insert_gen_oracle ev I sf orac es) env prog Fail ==>
  (~ semantics_prog (s0 with eval_state := insert_gen_oracle ev source_to_source$compile sf orac es) env prog Fail ==>
      semantics_prog (s0 with eval_state := insert_gen_oracle ev source_to_source$compile sf orac es) env prog res) ==>
  semantics_prog (s0 with eval_state := insert_gen_oracle ev I sf orac es) env prog res
Proof
  rw []
  \\ `is_insert_oracle ev I (s0 with eval_state := insert_gen_oracle ev I sf orac es).eval_state`
  by (
    simp [source_evalProofTheory.is_insert_oracle_def] \\ irule_at Any EQ_REFL
  )
  \\ drule_then drule source_to_sourceProofTheory.compile_semantics_oracle
  \\ simp [source_evalProofTheory.adjust_oracle_insert_gen_oracle]
  \\ metis_tac [semantics_prog_deterministic, semantics_prog_total]
QED

Theorem source_eval_to_flat_semantics:
  ~ semantics_prog (add_eval_state ev s0) env prog Fail /\
  compile (c : 'a config) prog = SOME (b,bm,c') /\
  source_to_flat$compile prim_src_config (source_to_source$compile prog) = (src_c', p') /\
  THE (prim_sem_env (ffi:'ffi ffi_state)) = (s0, env) /\
  opt_eval_config_wf c' ev /\
  c.source_conf = prim_src_config ==>
  ? syntax_oracle.
  semantics_prog (add_eval_state ev s0) env prog (flatSem$semantics
    (mk_flat_install_conf
        (backend_from_flat_tuple_cc c)
        (cake_orac c' syntax_oracle (SND o config_tuple1) (\ps. ps.flat_prog)))
    s0.ffi p')
Proof
  rw []
  \\ qabbrev_tac `orac =
        (\ (cfg, id, ds). (id, (THE ev).config_v (config_to_inc_config cfg), ds))
            o
        cake_orac c'
            (\i. case get_oracle (THE ev) (add_eval_state ev s0) env prog i of
                   SOME (id, (v : v), ds) => (id, ds)
                 | _ => ((0, 0), []))
            I (\ps. (ps.env_id,ps.source_prog))`
  \\ qabbrev_tac `es = put_oracle (THE ev) orac`
  \\ qexists_tac `(I ## SND) o ((source_evalProof$orac_s es).oracle)`
  \\ fs [Q.ISPEC `compile prim_src_config _` PAIR_FST_SND_EQ]
  \\ rveq \\ fs []
  \\ reverse (qsuff_tac `flat_patternProof$install_conf_rel
        prim_src_config.pattern_cfg
        (mk_flat_install_conf
            (pure_cc (MAP (flat_pattern$compile_dec prim_src_config.pattern_cfg))
                (backend_from_flat_tuple_cc c))
            (state_co (λc (env_id,decs).
                         source_to_flat$inc_compile_prog env_id c (source_to_source$compile decs))
                (cake_orac c' ((I ## SND) ∘ (source_evalProof$orac_s es).oracle)
                    config_tuple1 (\ps. (ps.env_id, ps.source_prog)))))
        (mk_flat_install_conf (backend_from_flat_tuple_cc c)
            (cake_orac c' ((I ## SND) ∘ (source_evalProof$orac_s es).oracle)
                (SND ∘ config_tuple1) (λps. ps.flat_prog)))`)
  >- (
    simp [flat_patternProofTheory.install_conf_rel_def, mk_flat_install_conf_def]
    \\ fs [markerTheory.Abbrev_def]
    \\ drule state_co_inc_compile_has_flat_comp
    \\ simp [GSYM source_to_flat_orac_eq]
  )
  \\ disch_tac
  \\ qabbrev_tac `the_ev = THE ev`
  \\ Cases_on `ev` \\ fs []
  >- (
    fs [add_eval_state_def]
    \\ simp [Once (GSYM source_to_source_semantics_prog_equiv)]
    \\ irule source_to_flatProofTheory.compile_semantics
    \\ simp [source_to_source_semantics_prog_equiv]
    \\ qexists_tac `NONE`
    \\ simp [source_to_flatProofTheory.precondition_def]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ simp [source_to_flatProofTheory.precondition1_def]
    \\ fs [prim_sem_env_eq]
    \\ rveq \\ fs []
    \\ qexists_tac `I`
    \\ EVAL_TAC
  )
  \\ gs [add_eval_state_def]
  \\ qspec_then `the_ev` irule eval_oracle_semantics_prog_intro
  \\ simp [CONJ_ASSOC]
  \\ conj_asm1_tac
  >- (
    fs [prim_sem_env_eq, GSYM namespaceTheory.nsEmpty_def]
    \\ rw []
  )
  \\ qexists_tac `orac`
  \\ qexists_tac `the_ev`
  \\ reverse conj_asm2_tac
  >- (
    simp [source_evalProofTheory.precond_eval_state_def,
        source_evalProofTheory.mk_init_eval_state_def]
    \\ fs [markerTheory.Abbrev_def]
    \\ drule_then (CHANGED_TAC o simp o single) cake_orac_extended_wf
    \\ simp [FORALL_PROD]
    \\ rw []
    \\ rpt (pairarg_tac \\ fs [])
    \\ drule_then drule cake_orac_eq_get_oracle
    \\ disch_then (first_assum o mp_then (Pat `cake_orac _ _ _ _ _ = _`) mp_tac)
    \\ disch_then (first_assum o mp_then (Pat `get_oracle _ _ _ _ _ = _`) mp_tac)
    \\ fs [source_evalProofTheory.mk_init_eval_state_def, opt_eval_config_wf_def]
    \\ simp [FORALL_PROD]
    \\ rw []
    \\ simp [config_to_inc_config_inv]
  )
  \\ rw []
  \\ irule source_to_source_semantics_prog_intro
  \\ rw []
  \\ fs [markerTheory.Abbrev_def, source_evalProofTheory.put_oracle_def]
  \\ irule source_to_source_semantics_prog_oracle_intro
  \\ rfs []
  \\ rw []
  \\ irule (source_to_flatProofTheory.compile_semantics
        |> Q.INST [`s` |-> `_ with <| eval_state := _|>`] |> SIMP_RULE (srw_ss ()) [])
  \\ simp []
  \\ qexists_tac `SOME (OPTION_MAP (config_tuple1 o inc_config_to_config c.lab_conf.asm_conf)
        o v_fun_abs UNIV the_ev.config_v)`
  \\ imp_res_tac compile_inc_config_inv
  \\ imp_res_tac compile_asm_config_eq
  \\ simp [source_to_flatProofTheory.precondition_def]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ qexists_tac `source_to_source$compile`
  \\ simp [source_to_flatProofTheory.precondition1_def]
  (* should be done with install_conf_rel now *)
  \\ qpat_x_assum `flat_patternProof$install_conf_rel _ _ _` kall_tac
  \\ conj_tac
  >- (
    (* src_orac_step_invs *)
    fs [markerTheory.Abbrev_def, source_evalProofTheory.put_oracle_def]
    \\ gvs [source_evalProofTheory.insert_gen_oracle_def]
    \\ simp_tac bool_ss [Once cake_orac_eq_I]
    \\ irule step_invs_cake_orac
    \\ simp []
    \\ simp_tac bool_ss [combinTheory.o_ASSOC]
    \\ irule_at Any EQ_REFL
    \\ simp [cake_orac_def]
    \\ rpt ((gen_tac ORELSE pairarg_tac ORELSE disch_tac) \\ fs [])
    \\ gvs []
    \\ imp_res_tac config_wf_abs_conc
    \\ simp [config_tuple1_def]
  )
  \\ conj_tac
  >- (
    fs [markerTheory.Abbrev_def]
    \\ qmatch_goalsub_abbrev_tac `cake_orac _ syntax`
    \\ qmatch_goalsub_abbrev_tac `state_co _ (cake_orac _ syntax2 _ _)`
    \\ reverse (qsuff_tac `syntax2 = syntax`)
    >- (
      fs [markerTheory.Abbrev_def]
      \\ simp [source_evalProofTheory.put_oracle_def,
            source_evalProofTheory.insert_gen_oracle_def, source_evalProofTheory.orac_s_def]
      \\ rw [FUN_EQ_THM, cake_orac_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
      \\ fs [Q.ISPEC `compile_inc_progs _ _ _` PAIR_FST_SND_EQ]
      \\ rveq \\ fs []
      \\ simp [compile_inc_progs_src_env]
    )
    \\ rw []
    \\ simp [source_to_flatProofTheory.orac_rel_def,
        source_evalProofTheory.put_oracle_def, source_evalProofTheory.insert_gen_oracle_def]
    \\ irule_at Any EQ_REFL
    \\ imp_res_tac config_wf_abs_conc
    \\ simp [mk_flat_install_conf_def]
    \\ rw [source_to_flatProofTheory.orac_rel_inner_def]
    >- (
      simp [state_co_def, UNCURRY]
      \\ fs [cake_orac_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
    )
    >- (
      fs [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
      \\ simp [pure_cc_def]
      \\ DEP_REWRITE_TAC [backend_from_flat_tuple_cc_eq_compile_inc_progs]
      \\ conj_tac
      >- (
        simp [config_tuple1_def]
        \\ fs [cake_orac_def, FUN_EQ_THM, UNCURRY]
        \\ drule cake_orac_config_eqs
        \\ rveq \\ fs []
      )
      \\ simp [UNCURRY, PULL_EXISTS]
      \\ fs [source_evalProofTheory.mk_compiler_fun_from_ci_def]
      \\ rfs [opt_eval_config_wf_def, compile_inc_progs_for_eval_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ rveq \\ fs []
      \\ DEP_REWRITE_TAC [inc_config_to_config_inv]
      \\ imp_res_tac compile_inc_progs_asm_conf
      \\ simp [backendTheory.inc_config_to_config_def,
        lab_to_targetTheory.inc_config_to_config_def]
    )
  )
  \\ conj_tac
  >- (
    simp [source_to_flatProofTheory.src_orac_next_cfg_def]
    \\ fs [markerTheory.Abbrev_def,
        source_evalProofTheory.put_oracle_def, source_evalProofTheory.insert_gen_oracle_def]
    \\ rveq \\ fs []
    \\ simp [source_to_flatProofTheory.src_orac_next_cfg_inner_def, cake_orac_0]
    \\ imp_res_tac config_wf_abs_conc
    \\ simp [config_tuple1_def, inc_config_to_config_inv]
    \\ fs [backendTheory.compile_def, compile_tap_def, source_to_flatTheory.compile_def]
    \\ rpt (pairarg_tac \\ fs [])
    \\ imp_res_tac attach_bitmaps_SOME
    \\ fs [Q.ISPEC `compile_prog _.source_conf _` PAIR_FST_SND_EQ]
    \\ rveq \\ fs []
  )
  \\ fs [markerTheory.Abbrev_def]
  \\ simp [source_evalProofTheory.put_oracle_def,
        source_evalProofTheory.insert_gen_oracle_def,
        source_to_flatProofTheory.init_eval_state_ok_def]
  \\ fs [prim_sem_env_eq]
  \\ rveq \\ fs []
  \\ EVAL_TAC
QED

Theorem flat_semantics:
  let co = cake_orac c' syn (SND o config_tuple1) (\ps. ps.flat_prog) in
  let f_inst = mk_flat_install_conf
        (pure_cc flat_to_clos$inc_compile_decs cc)
        co in
  flatSem$semantics f_inst ffi ds <> Fail /\
  0 < cconf.max_app /\ flatProps$no_Mat_decs ds ==>
  closSem$semantics ffi cconf.max_app FEMPTY
    (pure_co flat_to_clos$inc_compile_decs o co) cc (compile_decs ds) =
  flatSem$semantics f_inst ffi ds
Proof
  rw []
  \\ irule flat_to_closProofTheory.compile_semantics
  \\ simp [flat_to_closProofTheory.install_config_rel_def, mk_flat_install_conf_def]
  \\ simp [GSYM cake_orac_eqs, SND_state_co, UNCURRY]
  \\ simp [source_to_flatProofTheory.inc_compile_no_Mat]
QED


Theorem compile_correct':

  compile (c:'a config) prog = SOME (bytes,bitmaps,c') ⇒
   let (s0,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   let s = add_eval_state ev s0 in
   ¬semantics_prog s env prog Fail ∧
   backend_config_ok c ∧ lab_to_targetProof$mc_conf_ok mc ∧ mc_init_ok c mc ∧
   opt_eval_config_wf c' ev ∧
   installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names (heap_regs c.stack_conf.reg_names) mc ms ⇒
     machine_sem (mc:(α,β,γ) machine_config) ffi ms ⊆
       extend_with_resource_limit'
         (is_safe_for_space ffi c prog (read_limits c mc ms))
         (semantics_prog s env prog)

Proof

  disch_then (fn t => mp_tac t >>
    srw_tac[][compile_eq_from_source,from_source_def,
        backend_config_ok_def,heap_regs_def] >>
    assume_tac t) >>
  `c.lab_conf.asm_conf = mc.target.config` by fs[mc_init_ok_def] >>
  `c'.lab_conf.ffi_names = SOME mc.ffi_names` by fs[targetSemTheory.installed_def] >>

  fs [] >>
  rpt (pairarg_tac >> fs []) >>

  fs [Abbr `s`] >>

  drule_then drule source_eval_to_flat_semantics >>
  simp [] >>
  disch_then drule >>

  fs[primSemEnvTheory.prim_sem_env_eq] >>
  qpat_x_assum`_ = s0`(assume_tac o Abbrev_intro o SYM) >>
  qpat_x_assum`_ = env`(assume_tac o Abbrev_intro o SYM) >>


  strip_tac >>
  fs[] >>
  qhdtm_x_assum`from_flat`mp_tac >>
  srw_tac[][from_flat_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_assum_abbrev_tac`semantics_prog s env prog sem2` >>
  `sem2 ≠ Fail` by metis_tac[] >>
  `semantics_prog s env prog = { sem2 }` by (
    simp[EXTENSION,IN_DEF] >>
    metis_tac[semantics_prog_deterministic] ) >>
  qunabbrev_tac`sem2` >>

  fs [backend_from_flat_tuple_cc_def] >>

  drule_then drule (SIMP_RULE bool_ss [LET_DEF] flat_semantics)
  \\ impl_tac >- (
    fs [PAIR_FST_SND_EQ]
    \\ rw []
    \\ simp [compile_no_Mat]
  )

  \\ disch_then (strip_assume_tac o SYM) >>

  qhdtm_x_assum`from_clos`mp_tac >>
  srw_tac[][from_clos_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  simp[flatSemTheory.initial_state_def] >>
  qmatch_abbrev_tac`_ ⊆ _ { closSem$semantics _ _ _ co3 cc3 e3 }` >>
  qmatch_asmsub_abbrev_tac`clos_to_bvlProof$compile_common_inc cf (pure_cc (clos_to_bvl$compile_inc _) cc)`
  \\ Q.ISPECL_THEN[`co3`,`cc`,`e3`,`ffi`,`cf`]mp_tac
       (Q.GENL[`co`,`cc`,`es`,`ffi`,`c`,`c'`,`prog`]clos_to_bvlProofTheory.compile_semantics)
  \\ simp[]

  \\ qunabbrev_tac `co3`
  \\ qunabbrev_tac `cf`
  \\ DEP_REWRITE_TAC (map GEN_ALL (CONJUNCTS cake_orac_eqs))
  \\ rpt (conj_tac >- (asm_exists_tac \\ simp [] \\ NO_TAC))
  \\ impl_keep_tac
  >- (
    rpt (qsubpat_x_assum kall_tac `patSem$semantics []`)
    \\ conj_tac
    >- (
      fs[flatSemTheory.initial_state_def,Abbr`s0`,
         cake_orac_eqs] )
    \\ drule_then irule cake_orac_clos_syntax_oracle_ok
    \\ unabbrev_all_tac
    \\ simp [to_clos_def, to_flat_def]
    \\ EVERY (map imp_res_tac from_EXS)
    \\ rveq \\ fs []
    \\ simp [clos_to_bvlTheory.config_component_equality]
  )

  \\ disch_then(strip_assume_tac o SYM) \\ fs[] \\
  qhdtm_x_assum`from_bvl`mp_tac >>
  simp[from_bvl_def] >>
  pairarg_tac \\ fs[] \\ strip_tac \\
  fs[from_bvi_def] \\
  `s0.ffi = ffi` by simp[Abbr`s0`] \\ pop_assum SUBST_ALL_TAC \\ fs[] \\
  qmatch_goalsub_abbrev_tac`bvlSem$semantics _ _ co cc`
  \\ Q.ISPEC_THEN `co` (old_drule o GEN_ALL) (Q.GEN `co` bvl_to_bvi_compile_semantics2)
  \\ disch_then(qspec_then`ffi`mp_tac)
  \\ qunabbrev_tac`cc`
  \\ qmatch_goalsub_abbrev_tac`bvlSem$semantics _ _ co (full_cc _ cc) _`
  \\ disch_then(qspecl_then[`co`,`cc`]mp_tac)
  \\ fs[Abbr`c''''`]
  \\ impl_tac
  >- (
    rpt (qsubpat_x_assum kall_tac `bvlSem$semantics`)
    \\ simp [Abbr `co`]
    \\ simp [cake_orac_0, config_tuple2_def]
    \\ drule_then (fn t => conseq [t]) cake_orac_bvl_ALL_DISTINCT
    \\ unabbrev_all_tac
    \\ imp_res_tac clos_to_bvlProofTheory.compile_all_distinct_locs
    \\ drule_then (fn t => simp [t]) is_state_oracle_tailrec_cake_orac
    (* equalities on final config *)
    \\ EVERY (map imp_res_tac from_EXS)
    \\ fs []
  )

  \\ simp [Abbr `co`]
  \\ drule_then (fn t => simp [t]) bvl_to_bvi_orac_eq
  \\ disch_then(strip_assume_tac o SYM) \\ fs[] \\
  qunabbrev_tac`cc`
  \\ rpt (qsubpat_x_assum kall_tac `patSem$semantics`)

  \\ (bvi_to_dataProofTheory.compile_prog_semantics
      |> SIMP_RULE std_ss [GSYM backendPropsTheory.pure_cc_def |> SIMP_RULE std_ss [LET_THM]]
      |> REWRITE_RULE [GSYM pure_co_def] |> Q.GEN ‘lim’
      |> old_drule)

  \\ disch_then (qspec_then `dataProps$zero_limits` mp_tac)
  \\ once_rewrite_tac [dataPropsTheory.semantics_zero_limits]
  \\ disch_then(strip_assume_tac o SYM) \\ fs[] \\
  qmatch_assum_abbrev_tac `from_data c4 n4 p4 = _` \\
  qhdtm_x_assum`from_data`mp_tac
  \\ simp[from_data_def]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac
  \\ rename1`compile _ _ _ p4 = (col,p5)` \\

  qhdtm_x_assum`from_word`mp_tac \\
  simp[from_word_def] \\ pairarg_tac \\ fs[] \\ strip_tac \\

  qmatch_goalsub_abbrev_tac`cake_orac _ orac_syntax _ (\ps. ps.bvi_prog)` \\
  simp [simple_orac_eqs] \\
  qabbrev_tac `data_oracle = cake_orac c' orac_syntax
        (SND ∘ SND ∘ SND ∘ config_tuple2) (λps. ps.data_prog)` \\
  qabbrev_tac `word_oracle = cake_orac c' orac_syntax
        (SND ∘ SND ∘ SND ∘ config_tuple2) (λps. ps.word_prog)` \\
  qmatch_assum_rename_tac`compile _ p5 = (bm,c6,_,p6)` \\
  fs[from_stack_def,from_lab_def] \\

  qabbrev_tac `stack_oracle = cake_orac c' orac_syntax
        (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2) (λps. (ps.stack_prog, ps.cur_bm))` \\
  qabbrev_tac `lab_oracle = cake_orac c' orac_syntax
        (SND ∘ SND ∘ SND ∘ SND ∘ config_tuple2) (λps. ps.lab_prog)` \\
  qmatch_assum_abbrev_tac`_ _ (compile c4.lab_conf p7) = SOME (bytes,bitmaps,c')`
  \\ drule attach_bitmaps_SOME
  \\ disch_tac \\ fs []
  \\ fs [attach_bitmaps_def] \\ rveq \\ fs [] \\
  fs[targetSemTheory.installed_def] \\
  qmatch_assum_abbrev_tac`good_init_state mc ms bytes cbspace tar_st m dm io_regs cc_regs` \\
  qpat_x_assum`Abbrev(p7 = _)` mp_tac>>
  qmatch_goalsub_abbrev_tac`compile _ _ _ stk stoff`>>
  strip_tac \\
  qabbrev_tac`kkk = stk - 2`>>
  qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ data_oracle` \\
  qabbrev_tac `c4_data_conf = (c4.data_conf with <| has_fp_ops := (1 < c4.lab_conf.asm_conf.fp_reg_count);
                                                    has_fp_tern := (c4.lab_conf.asm_conf.ISA = ARMv7 /\ 2 < c4.lab_conf.asm_conf.fp_reg_count) |>)` \\
  qabbrev_tac`lab_st:('a,'a lab_to_target$config,'ffi) labSem$state = lab_to_targetProof$make_init mc ffi io_regs cc_regs tar_st m (dm ∩ byte_aligned) ms p7 lab_to_target$compile
       (mc.target.get_pc ms + n2w (LENGTH bytes)) cbspace lab_oracle` \\

  qabbrev_tac`stack_st_opt =
    stack_to_labProof$full_make_init
      c4.stack_conf
      c4.data_conf
      (2 * max_heap_limit (:'a) c4_data_conf - 1)
      stk
      stoff
      bitmaps
      p6
      lab_st
      (set mc.callee_saved_regs)
      data_sp
      stack_oracle` >>
  qabbrev_tac`stack_st = FST stack_st_opt` >>
  qabbrev_tac`word_st = word_to_stackProof$make_init kkk stack_st (fromAList p5) word_oracle` \\

  rewrite_tac [is_safe_for_space_def] \\
  `FST(SND(to_data c prog)) = p4 /\ FST(SND(to_word c prog)) = p5` by
    fs[to_word_def,to_data_def,to_bvi_def,to_bvl_def,to_clos_def,to_flat_def] \\
  pop_assum (fn th => rewrite_tac [th]) \\
  pop_assum (fn th => rewrite_tac [th,LET_THM]) \\
  simp_tac std_ss [] \\

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
  old_drule (word_to_stack_stack_convs|> GEN_ALL)>>
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
  \\ old_drule (GEN_ALL compile_distinct_names)
  \\ fs[bvl_to_bviTheory.compile_def]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ rveq
  \\ old_drule clos_to_bvlProofTheory.compile_all_distinct_locs
  \\ strip_tac
  \\ disch_then(qspec_then`0`mp_tac) \\ simp[] \\ strip_tac
  \\ `stubs (:'a) c4.data_conf = stubs (:'a) c4_data_conf` by ( simp[Abbr`c4_data_conf`] )
  \\ qmatch_assum_rename_tac`_ _ code = (n2,p3)`
  \\ `MAP FST p4 = MAP FST p3`
    by metis_tac[bvi_to_dataProofTheory.MAP_FST_compile_prog]
  \\ `data_to_word_gcProof$code_rel c4_data_conf (fromAList p4) (fromAList t_code)`
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
      old_drule(ONCE_REWRITE_RULE[CONJ_COMM] ALOOKUP_ALL_DISTINCT_MEM) \\
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
  `data_to_wordProof$code_rel_ext (fromAList t_code) (fromAList p5)` by metis_tac[code_rel_ext_word_to_word] \\
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
  `stack_to_labProof$labels_ok p7` by
    (fs[Abbr`p7`]>>
    match_mp_tac stack_to_lab_compile_lab_pres>>
    rw[]>>EVAL_TAC>>
    fs[EVERY_MEM]>> rpt strip_tac>>
    first_x_assum old_drule>>
    EVAL_TAC>>rw[])>>
  disch_then(qspecl_then[`fromAList t_code`,`InitGlobals_location`,`p4`,`c4_data_conf`]mp_tac) \\

  (* TODO: make this auto *)
  disch_then(qspecl_then[`mc.target.config.two_reg_arith`,`kkk`,`c4.lab_conf.asm_conf`,`c.word_to_word_conf.reg_alg`]mp_tac)

  \\ rpt (qsubpat_x_assum kall_tac `closSem$semantics`)
  \\ rpt (qsubpat_x_assum kall_tac `bvlSem$semantics`)

  \\ `∀n. EVERY ($<= data_num_stubs) (MAP FST (SND (data_oracle n)))` by (
    rpt (qsubpat_x_assum kall_tac `dataSem$semantics`)
    \\ gen_tac
    \\ simp[Abbr`data_oracle`, GSYM simple_orac_eqs]
    \\ irule (listTheory.MONO_EVERY |> Q.GEN `P` |> Q.ISPEC `$<= bvl_num_stubs`)
    \\ drule_then (fn t => conseq [t]) bvl_num_stubs_LE_bvi_prog
    \\ EVAL_TAC \\ simp []
  )
  \\ `loc = InitGlobals_location` by
   (fs [bvl_to_bviTheory.compile_def,bvl_to_bviTheory.compile_prog_def]
    \\ rpt (pairarg_tac \\ fs []))

  \\ impl_tac >- (
    simp[Abbr`word_st`,word_to_stackProofTheory.make_init_def,Abbr`c4`,Abbr`c4_data_conf`,
         EVAL ``wordSem$stack_size []``]
    (*
    qmatch_goalsub_rename_tac`c5.data_conf` \\ qunabbrev_tac`c5` \\
    *)
    \\ fs[mc_conf_ok_def] \\
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
      fs[Abbr`data_oracle`,full_co_def]
      \\ fs [backendPropsTheory.SND_state_co]
      \\ qpat_x_assum`∀n. EVERY _ _`mp_tac
      \\ rewrite_tac[GSYM bvi_to_dataProofTheory.MAP_FST_compile_prog]
      \\ simp[EVERY_MAP, LAMBDA_PROD] ) \\
    conj_tac >- (
      AP_TERM_TAC>>
      simp[data_to_wordTheory.compile_part_def,FST_triple,MAP_MAP_o,o_DEF,LAMBDA_PROD])>>
    conj_tac >- (
      simp [stack_to_labProofTheory.full_make_init_def,
            stack_allocProofTheory.make_init_def,
            stack_removeProofTheory.make_init_any_def,
            stack_removeProofTheory.make_init_opt_def,AllCaseEqs()]
      \\ TOP_CASE_TAC \\ fs []
      \\ fs [stack_removeProofTheory.make_init_opt_def,CaseEq"option",pair_case_eq] \\ rveq
      \\ fs [stack_namesProofTheory.make_init_def,stack_to_labProofTheory.make_init_def,
             lab_to_targetProofTheory.make_init_def,mc_init_ok_def,
             stack_removeProofTheory.init_reduce_def]
      \\ imp_res_tac stackPropsTheory.evaluate_consts \\ fs [])>>
    conj_tac >- (
      simp [stack_to_labProofTheory.full_make_init_def,
            stack_allocProofTheory.make_init_def,
            stack_removeProofTheory.make_init_any_def]
      \\ TOP_CASE_TAC \\ fs []
      \\ fs [stack_removeProofTheory.make_init_opt_def,CaseEq"option",pair_case_eq] \\ rveq
      \\ fs [stack_removeProofTheory.init_reduce_def]
      \\ rewrite_tac [GSYM ADD1,stack_removeProofTheory.read_mem_def] \\ simp []) >>
    conj_tac >- (
      simp [Abbr `data_oracle`]
      \\ simp [GSYM pure_co_def]
      \\ drule_then (irule o GSYM) data_to_word_orac_eq
      \\ fs [markerTheory.Abbrev_def, ensure_fp_conf_ok_def]
    )
    \\ qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ _ TODO_cc'`
    \\ qpat_x_assum`dataSem$semantics _ _ _ _ _ _ _ ≠ Fail`mp_tac
    \\ qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ _ TODO_cc`
    \\ simp [Abbr `data_oracle`]
    \\ simp [simple_orac_eqs]
    \\ `TODO_cc' = TODO_cc` suffices_by
          (once_rewrite_tac [dataPropsTheory.semantics_zero_limits] \\ simp[])
    \\ simp[Abbr`TODO_cc`,Abbr`TODO_cc'`, FUN_EQ_THM]
    \\ rpt gen_tac
    \\ simp [backend_from_data_tuple_cc_def]
    \\ AP_TERM_TAC
    \\ simp[Abbr`kkk`,Abbr`stk`]
    \\ simp[ensure_fp_conf_ok_def]
    \\ AP_THM_TAC \\ AP_THM_TAC
    \\ simp[full_make_init_compile]
    \\ simp[EVAL``(lab_to_targetProof$make_init a b c d e f g h i j k l m).compile``]
    \\ simp[Abbr`stoff`] ) \\

  `lab_st.ffi = ffi` by ( fs[Abbr`lab_st`] ) \\
  `word_st.ffi = ffi` by (
    simp[Abbr`word_st`,word_to_stackProofTheory.make_init_def] \\
    fs[Abbr`stack_st`,Abbr`lab_st`,Abbr`stack_st_opt`] \\
    fs [full_make_init_def,stack_allocProofTheory.make_init_def,
        stack_removeProofTheory.make_init_any_ffi] \\ EVAL_TAC) \\
  strip_tac \\

  qmatch_abbrev_tac`x ⊆ extend_with_resource_limit' _ y` \\
  `Fail ∉ y` by (fs [Abbr `y`] \\ fs [GSYM pure_co_def, simple_orac_eqs]) \\
  pop_assum mp_tac \\ simp[GSYM implements'_def] \\
  simp[Abbr`y`] \\
  old_drule $ GEN_ALL $
    INST_TYPE [delta |-> ``:'ffi``] lab_to_targetProofTheory.semantics_compile \\
  disch_then(old_drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(optionSyntax.is_some o rhs))))) \\
  simp[Abbr`c4`] \\
  disch_then(old_drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``good_init_state`` o fst o strip_comb))))) \\
  disch_then(qspecl_then[`ffi`,`lab_oracle`]mp_tac)
  \\ old_drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_next_mono)
  \\ strip_tac
  \\ pop_assum(assume_tac o Abbrev_intro)
  \\ full_simp_tac (bool_ss ++ simpLib.type_ssfrag ``: 'a config``) []

  \\ impl_keep_tac
  >- (
    conj_tac >- (
      rpt (qsubpat_x_assum kall_tac `dataSem$semantics`)
      \\ rpt (qsubpat_x_assum kall_tac `closSem$semantics`)
      \\ simp [Abbr `lab_oracle`]
      \\ simp [compiler_oracle_ok_def]
      \\ conj_tac >- (
        gen_tac
        \\ pairarg_tac \\ simp []
        \\ drule_then (drule_then irule) (GEN_ALL good_code_lab_oracle)
        \\ fs [Abbr `stoff`, backend_config_ok_def, asmTheory.offset_ok_def]
        \\ asm_exists_tac
        \\ simp []
      )
      \\ fs [markerTheory.Abbrev_def]
      \\ fs [lab_to_targetTheory.compile_def]
      \\ drule compile_lab_lab_conf
      \\ drule compile_lab_LENGTH
      \\ simp [cake_orac_0, config_tuple2_def]
    )
    (* ugh have to use metis just to show p7 is compiled from a data prog *)
    \\ qpat_x_assum`Abbrev(p7 = _)` mp_tac
    \\ disch_then (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def])
    \\ drule_then (drule_then irule) (GEN_ALL to_lab_good_code_lemma)
    \\ qpat_x_assum `all_enc_ok_pre _ _` mp_tac \\ simp []
    \\ disch_tac
    \\ simp [data_to_wordTheory.compile_def]
    \\ fs [markerTheory.Abbrev_def]
    \\ metis_tac []
  )

  \\ strip_tac
  \\ qpat_x_assum`Abbrev(stack_st_opt = _)`(mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) \\
  disch_then(assume_tac o SYM) \\
  Cases_on`stack_st_opt` \\
  drule full_make_init_semantics2 \\

  impl_tac >- (
    simp_tac std_ss [Once EVERY_FST_SND] \\
    qunabbrev_tac`stack_st` \\
    fs[Abbr`lab_st`,make_init_def] \\
    fs[mc_init_ok_def, mc_conf_ok_def, Abbr`stk`,byte_aligned_MOD] \\
    `max_heap_limit (:'a) c4_data_conf = max_heap_limit (:'a) c.data_conf` by
      (simp[Abbr`c4_data_conf`] \\ EVAL_TAC) \\
    rewrite_tac [GSYM CONJ_ASSOC] \\
    conj_tac >- fs[Abbr`p7`] \\
    conj_tac >- (
      qunabbrev_tac `lab_oracle`
      \\ qunabbrev_tac `stack_oracle`
      \\ drule_then (fn t => DEP_REWRITE_TAC [t]) stack_to_lab_orac_eq
      \\ simp []
    ) \\
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
        fs [stack_removeProofTheory.addresses_thm]>>
        fs[mc_conf_ok_def]>>
        `0 < dimindex (:α) DIV 8` by
          rfs [labPropsTheory.good_dimindex_def]>>
        reverse conj_tac >-
         (fs [] \\ match_mp_tac IMP_MULT_DIV_LESS \\ fs [w2n_lt]
          \\ rfs [labPropsTheory.good_dimindex_def])
        \\ qabbrev_tac `a = tar_st.regs mc.len_reg`
        \\ qabbrev_tac `b = tar_st.regs mc.len2_reg`
        \\ qpat_x_assum `a <=+ b` assume_tac
        \\ old_drule WORD_LS_IMP \\ strip_tac \\ fs [EXTENSION]
        \\ fs [IN_DEF,PULL_EXISTS,bytes_in_word_def,word_mul_n2w]
        \\ rw [] \\ reverse eq_tac THEN1
         (rw [] \\ fs [] \\ qexists_tac `i * (dimindex (:α) DIV 8)` \\ fs []
          \\ `0 < dimindex (:α) DIV 8` by rfs [labPropsTheory.good_dimindex_def]
          \\ old_drule X_LT_DIV \\ disch_then (fn th => fs [th])
          \\ fs [RIGHT_ADD_DISTRIB]
          \\ fs [GSYM word_mul_n2w,GSYM bytes_in_word_def]
          \\ fs [byte_aligned_mult])
        \\ rw [] \\ fs []
        \\ `i < dimword (:'a)` by metis_tac [LESS_TRANS,w2n_lt] \\ fs []
        \\ qexists_tac `i DIV (dimindex (:α) DIV 8)`
        \\ rfs [alignmentTheory.byte_aligned_def,
             ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
        \\ fs [aligned_w2n]
        \\ old_drule DIVISION
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
      CONJ_TAC>- EVAL_TAC>>
      `!k. data_num_stubs<= k ⇒ stack_num_stubs <=k` by
        (EVAL_TAC>>fs[])>>
      CONJ_TAC>-
        EVAL_TAC>>
      metis_tac[EVERY_MONOTONIC]) >>
    fs[Abbr `stack_oracle`]
    \\ gen_tac
    \\ drule_then irule oracle_stack_good_code
    \\ simp [backend_config_ok_def]
    \\ simp [Abbr `stoff`]
    \\ qexists_tac `mc`
    \\ simp [mc_conf_ok_def]
  ) \\
  fs[Abbr`word_st`] \\ rfs[] \\
  strip_tac \\

  qmatch_goalsub_abbrev_tac `dataSem$data_lang_safe_for_space _ _ lim1 fs1` \\
  qmatch_asmsub_abbrev_tac `dataSem$data_lang_safe_for_space _ _ lim2 fs2` \\
  `lim1 = lim2 /\ fs1 = fs2` by
    (reverse conj_tac THEN1
      (simp [Abbr`fs1`,Abbr`fs2`]
       \\ simp [word_to_stackProofTheory.make_init_def,compute_stack_frame_sizes_thm]
       \\ qpat_abbrev_tac `kkk2 = _ - (_:num)`
       \\ qsuff_tac `kkk = kkk2` \\ fs []
       \\ simp [Abbr`kkk`,Abbr`kkk2`,Abbr`stk`])
     \\ simp [Abbr`lim1`,Abbr`lim2`]
     \\ simp [dataSemTheory.limits_component_equality]
     \\ fs [data_to_wordProofTheory.get_limits_def]
     \\ simp [dataSemTheory.compute_limits_def,is_64_bits_def]
     \\ qunabbrev_tac `c4_data_conf` \\ simp []
     \\ simp [word_to_stackProofTheory.make_init_def,DOMSUB_FAPPLY_THM]
     \\ fs [stack_to_labProofTheory.full_make_init_def]
     \\ Cases_on `r` \\ fs []
     \\ fs [stack_removeProofTheory.make_init_opt_def,CaseEq"option",pair_case_eq]
     \\ qpat_x_assum `_ = x'` assume_tac \\ var_eq_tac
     \\ qmatch_asmsub_abbrev_tac `stack_removeProof$read_pointers stack_names_init`
     \\ qmatch_asmsub_abbrev_tac `stack_removeProof$get_stack_heap_limit real_max_heap`
     \\ fs [stack_removeProofTheory.init_prop_def]
     \\ qpat_x_assum `stack_removeProof$stack_heap_limit_ok _ _` assume_tac
     \\ qpat_assum `_ = stack_st` (fn th => rewrite_tac [GSYM th])
     \\ rewrite_tac [stack_removeProofTheory.make_init_any_def]
     \\ simp [stack_removeProofTheory.make_init_opt_def]
     \\ reverse IF_CASES_TAC THEN1
      (qsuff_tac `F` \\ fs [] \\ pop_assum mp_tac
       \\ fs [stack_removeProofTheory.init_prop_def]
       \\ qexists_tac `len` \\ fs [])
     \\ simp []
     \\ simp [stack_allocProofTheory.make_init_def]
     \\ qpat_abbrev_tac `init_reduce_state = stack_removeProof$init_reduce _ _ _ _ _ _ _ _ _`
     \\ Cases_on `stack_removeProof$get_stack_heap_limit real_max_heap
                    (stack_removeProof$read_pointers stack_names_init)`
     \\ fs [stack_removeProofTheory.stack_heap_limit_ok_def]
     \\ qpat_x_assum `FLOOKUP _ _ = _` mp_tac
     \\ simp_tac std_ss [FLOOKUP_DEF,wordSemTheory.theWord_def,bytes_in_word_def]
     \\ strip_tac
     \\ rename [`_ = (stack_len, heap_len)`]
     \\ qpat_x_assum `stack_len = _` (assume_tac o GSYM)
     \\ `LENGTH (stackSem$read_stack init_reduce_state) =
         stackSem$read_stack_space init_reduce_state + 1`
           by fs [Abbr`init_reduce_state`,stack_removeProofTheory.init_reduce_def,
                  stackSemTheory.read_stack_def,stackSemTheory.read_stack_space_def]
     \\ pop_assum (assume_tac o REWRITE_RULE
           [stackSemTheory.read_stack_def,stackSemTheory.read_stack_space_def])
     \\ pop_assum mp_tac \\ asm_rewrite_tac [] \\ pop_assum kall_tac \\ strip_tac
     \\ Cases_on `stack_len` \\ fs [ADD1]
     \\ simp [word_mul_n2w]
     \\ `0 < dimindex (:α) DIV 8` by
      (fs [lab_to_targetProofTheory.mc_conf_ok_def]
       \\ qpat_x_assum `good_dimindex _` mp_tac
       \\ rpt (pop_assum kall_tac)
       \\ rw [labPropsTheory.good_dimindex_def] \\ simp [])
     \\ rewrite_tac[CONJ_ASSOC]
     \\ simp [MULT_DIV,FST_SND_EQ]
     \\ qpat_x_assum `_ = (_,_)` (assume_tac o GSYM) \\ simp []
     \\ rewrite_tac [read_limits_def]
     \\ simp [Abbr`real_max_heap`,data_to_wordTheory.max_heap_limit_def,
              data_to_wordTheory.shift_length_def]
     \\ AP_TERM_TAC \\ simp [stack_removeProofTheory.read_pointers_def]
     \\ simp [Abbr`stack_names_init`,stack_namesProofTheory.make_init_def]
     \\ simp [stack_to_labProofTheory.make_init_def]
     \\ simp [lab_to_targetProofTheory.make_init_def,Abbr`lab_st`]
     \\ simp [FUPDATE_LIST]
     \\ qmatch_goalsub_abbrev_tac `MAP_KEYS fff`
     \\ drule pred_setTheory.BIJ_LINV_BIJ \\ simp []
     \\ strip_tac
     \\ `!m. INJ fff m UNIV` by fs [BIJ_DEF,INJ_DEF]
     \\ `!x. ((2 = fff x) <=> x = find_name c.stack_conf.reg_names 2) /\
             ((3 = fff x) <=> x = find_name c.stack_conf.reg_names 3) /\
             ((4 = fff x) <=> x = find_name c.stack_conf.reg_names 4)` by
      (rpt (qpat_x_assum `BIJ _ _ _` mp_tac) \\ simp [Abbr`fff`]
       \\ rpt (pop_assum kall_tac) \\ metis_tac [PERMUTE_IMP_LINV])
     \\ asm_rewrite_tac [] \\ csimp [FLOOKUP_MAP_KEYS]
     \\ simp [FLOOKUP_UPDATE,wordSemTheory.theWord_def]
     \\ fs [targetSemTheory.good_init_state_def]
     \\ qpat_x_assum `target_state_rel mc.target tar_st ms` assume_tac
     \\ fs [asmPropsTheory.target_state_rel_def]
     \\ rpt conj_tac
     \\ first_x_assum match_mp_tac
     \\ qpat_x_assum `names_ok _ _ _` mp_tac
     \\ simp [stack_namesTheory.names_ok_def]
     \\ qmatch_goalsub_abbrev_tac `GENLIST _ k1`
     \\ `?k2. k1 = SUC (SUC (SUC (SUC (SUC k2))))` by
      (`5 <= k1` by fs [Abbr`k1`]
       \\ drule (DECIDE ``5 <= n ==> n = SUC (SUC (SUC (SUC (SUC (n-5)))))``)
       \\ strip_tac \\ asm_exists_tac  \\ simp [])
     \\ pop_assum (fn th => rewrite_tac [th])
     \\ rewrite_tac [GENLIST_CONS]
     \\ simp [ADD1,o_DEF]) \\
  pop_assum (fn th => full_simp_tac bool_ss [th]) \\
  pop_assum (fn th => full_simp_tac bool_ss [th]) \\

  match_mp_tac implements'_trans \\
  qmatch_assum_abbrev_tac`z InitGlobals_location ∈ _ {_}` \\
  qexists_tac`{z InitGlobals_location}` \\
  conj_tac >- (
    rewrite_tac [implements'_def,extend_with_resource_limit'_def] \\
    simp[]
    \\ fs[full_make_init_compile]
    \\ fs[EVAL``(lab_to_targetProof$make_init a b c d e f g h i j k l m).compile``]
    \\ fs[Abbr`stoff`]
    \\ fs[EVAL``(word_to_stackProof$make_init a b c d).compile``]
    \\ fs[Abbr`kkk`,Abbr`stk`,Abbr`stack_st`] \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ _ foo1`
    \\ qmatch_asmsub_abbrev_tac`dataSem$semantics _ _ _ foo2`
    \\ `c4_data_conf.gc_kind = c.data_conf.gc_kind` by fs [Abbr`c4_data_conf`]
    \\ fs []
    \\ `foo1 = foo2` suffices_by
      (qpat_x_assum `z InitGlobals_location IN _` mp_tac
       \\ once_rewrite_tac [dataPropsTheory.semantics_zero_limits]
       \\ fs [extend_with_resource_limit'_def])
    \\ simp[Abbr`foo1`,Abbr`foo2`]
    \\ simp[backend_from_data_tuple_cc_def, FUN_EQ_THM, ensure_fp_conf_ok_def]
    \\ rpt gen_tac \\ AP_TERM_TAC
    \\ qhdtm_assum`stack_to_labProof$full_make_init`(mp_tac o Q.AP_TERM`FST`)
    \\ simp_tac std_ss []
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[full_make_init_compile, Abbr`lab_st`]
    \\ fs[EVAL``(lab_to_targetProof$make_init a b c d e f g h i j k l m).compile``]
    \\ simp[append_def]) \\
  simp[Abbr`z`] \\
  match_mp_tac implements'_strengthen \\
  qmatch_goalsub_abbrev_tac `semantics s_tmp start_tmp` \\
  qexists_tac `wordSem$word_lang_safe_for_space s_tmp start_tmp` \\
  qunabbrev_tac `s_tmp` \\
  qunabbrev_tac `start_tmp` \\
  conj_tac THEN1
   (qpat_x_assum `dataSem$data_lang_safe_for_space _ _ _ _ _ /\ _ ==> _` mp_tac
    \\ `c4_data_conf.gc_kind = c.data_conf.gc_kind` by fs [Abbr`c4_data_conf`]
    \\ simp []) \\

  (word_to_stackProofTheory.compile_semantics
   |> Q.GENL[`t`,`code`,`asm_conf`,`start`]
   |> GEN_ALL
   |> Q.ISPECL_THEN[`kkk`,`word_oracle`,`stack_st`,`p5`,`c.lab_conf.asm_conf`,`InitGlobals_location`]mp_tac) \\

  impl_tac >- (
    rename [`rrr <> NONE`] \\ Cases_on `rrr` \\ fs [] \\
    fs[] \\
    conj_tac >- (
      fs[Abbr`stack_st`,full_make_init_def]
      \\ rveq
      \\ fs[stack_allocProofTheory.make_init_def] ) \\
    conj_asm1_tac >- (
      fs[Abbr`kkk`,Abbr`stk`]) >>
    conj_tac >- (
      match_mp_tac (GEN_ALL IMP_init_state_ok) \\
      goal_assum(first_assum o mp_then Any mp_tac) \\
      fs[Abbr`kkk`,Abbr`stk`]>>
      fs[mc_conf_ok_def,backend_config_ok_def,Abbr`stack_st`] >>
      old_drule compile_word_to_stack_bitmaps>>
      CASE_TAC>>strip_tac>>
      reverse conj_tac >- (
        simp [Abbr `stack_oracle`, Abbr `word_oracle`]
        \\ drule_then (fn t => simp [GSYM t]) word_to_stack_orac_eq
        \\ simp [FUN_EQ_THM, UNCURRY, ETA_THM]
      )
      \\ simp [Abbr `word_oracle`]
      \\ drule_then (fn t => simp [t]) data_to_word_orac_eq_sym_std
      \\ gen_tac \\ Cases_on `data_oracle n`
      \\ simp [pure_co_def]
      \\ rpt (pairarg_tac \\ fs [])
      \\ qmatch_goalsub_abbrev_tac`EVERY _ fcs_pp`
      \\ drule_then assume_tac (GEN_ALL MAP_full_compile_single_to_compile)
      \\ fs []
      \\ drule compile_to_word_conventions2
      \\ simp [EVERY_MAP |> REWRITE_RULE [GSYM o_DEF] |> Q.SPEC `P` |> Q.ISPEC `FST` |> GSYM]
      \\ simp [MAP_MAP_o |> REWRITE_RULE [o_DEF], Q.ISPEC `FST` ETA_THM]
      \\ rw [EVERY_MEM] \\ TRY (first_x_assum drule \\ simp [UNCURRY])
      \\ fs [Abbr `data_oracle`] \\ fs [cake_orac_0, config_tuple2_def]
      \\ first_x_assum (qspecl_then [`n`] mp_tac)
      \\ simp [EVERY_MEM]
      \\ metis_tac [EVAL ``data_num_stubs <= raise_stub_location``,
                    EVAL ``data_num_stubs <= store_consts_stub_location``]
    ) \\
    conj_tac >- (
      qunabbrev_tac`t_code` \\
      imp_res_tac data_to_word_names \\
      simp[ALOOKUP_NONE] \\
      conj_tac >- EVAL_TAC \\
      strip_tac \\ fs[EVERY_MEM] \\
      res_tac \\ pop_assum mp_tac >> EVAL_TAC) \\
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
    fs[extend_with_resource_limit_def,extend_with_resource_limit'_def]
    \\ qmatch_asmsub_abbrev_tac `if bb then _ else _`
    \\ Cases_on `bb` \\ pop_assum mp_tac \\ simp [Once markerTheory.Abbrev_def]
    \\ strip_tac \\ fs []
    \\ qpat_x_assum`_ ≠ Fail`assume_tac
    \\ once_rewrite_tac [dataPropsTheory.semantics_zero_limits]
    \\ qmatch_asmsub_abbrev_tac`dataSem$semantics _ _ orac1 foo1 _ _ _ ≠ Fail`
    \\ qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ orac2 foo2`
    \\ `foo1 = foo2 /\ orac1 = orac2` suffices_by metis_tac []
    \\ simp[Abbr`foo1`,Abbr`foo2`,Abbr`orac1`,Abbr`orac2`,FUN_EQ_THM,
        Abbr `data_oracle`]
    \\ simp [GSYM simple_orac_eqs, ensure_fp_conf_ok_def, backend_from_data_tuple_cc_def]
    \\ rpt gen_tac \\ AP_TERM_TAC
    \\ AP_THM_TAC
    \\ simp[EVAL``(word_to_stackProof$make_init a b c e).compile``]
    \\ rfs[Abbr`stack_st`]
    \\ qhdtm_assum`stack_to_labProof$full_make_init`(mp_tac o Q.AP_TERM`FST`)
    \\ simp_tac std_ss []
    \\ disch_then(SUBST_ALL_TAC o SYM)
    \\ fs[full_make_init_compile, Abbr`lab_st`]
    \\ fs[EVAL``(lab_to_targetProof$make_init a b c d e f g h i j k l m).compile``]
    \\ simp[append_def]) \\

  strip_tac \\
  match_mp_tac implements'_trans \\
  qmatch_assum_abbrev_tac`z ∈ _ {_}` \\
  qexists_tac`{z}` \\
  conj_tac >- (
    fs [implements'_def]
    \\ strip_tac \\ fs [] \\ rveq \\ fs [] ) \\
  simp[Abbr`z`] \\
  simp[Abbr`stack_st`] \\
  simp[Abbr`x`] \\
  match_mp_tac implements'_strengthen \\ qexists_tac `T` \\ rewrite_tac [] \\
  match_mp_tac (GEN_ALL (MP_CANON implements'_trans)) \\
  ONCE_REWRITE_TAC[CONJ_COMM] \\
  asm_exists_tac \\ simp[] \\
  fs [implements'_def] \\ rw [] \\ fs [] \\
  fs [extend_with_resource_limit'_def]
QED

Triviality compile_correct_no_eval =
  compile_correct' |> Q.INST [`ev` |-> `NONE`]
    |> SIMP_RULE bool_ss [add_eval_state_def, opt_eval_config_wf_def]

Theorem compile_correct:
  compile (c:'a config) prog = SOME (bytes,bitmaps,c') ⇒
   let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   ¬semantics_prog s env prog Fail ∧
   backend_config_ok c ∧ lab_to_targetProof$mc_conf_ok mc ∧ mc_init_ok c mc ∧
   installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
        (heap_regs c.stack_conf.reg_names) mc ms ⇒
     machine_sem (mc:(α,β,γ) machine_config) ffi ms ⊆
       extend_with_resource_limit (semantics_prog s env prog)
Proof
  rw [] \\ pairarg_tac \\ fs [] \\ rw []
  \\ match_mp_tac SUBSET_TRANS
  \\ mp_tac compile_correct_no_eval \\ fs []
  \\ strip_tac \\ asm_exists_tac
  \\ fs [extend_with_resource_limit'_SUBSET]
QED

Theorem semantics_prog_sing:
  ?x. semantics_prog s env prog = { x }
Proof
  fs [EXTENSION,IN_DEF]
  \\ metis_tac [semanticsPropsTheory.semantics_prog_total,
             semanticsPropsTheory.semantics_prog_deterministic]
QED

Theorem compile_correct_is_safe_for_space:
  compile (c:'a config) prog = SOME (bytes,bitmaps,c') ⇒
  is_safe_for_space ffi c prog (stack_limit,heap_limit) ⇒
  (read_limits c mc ms) = (stack_limit,heap_limit) ⇒
  let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
  ¬semantics_prog s env prog Fail ∧
  backend_config_ok c ∧ lab_to_targetProof$mc_conf_ok mc ∧ mc_init_ok c mc ∧
  installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
       (heap_regs c.stack_conf.reg_names) mc ms ⇒
  machine_sem (mc:(α,β,γ) machine_config) ffi ms =
  semantics_prog s env prog
Proof
  rw [] \\ pairarg_tac \\ fs [] \\ rw []
  \\ mp_tac compile_correct_no_eval \\ fs []
  \\ fs [extend_with_resource_limit'_def]
  \\ `?x. semantics_prog s env prog = { x }` by metis_tac [semantics_prog_sing]
  \\ fs [SUBSET_DEF,EXTENSION]
  \\ rw [] \\ eq_tac \\ rw []
  \\ `?x. machine_sem mc ffi ms x` by metis_tac [targetPropsTheory.machine_sem_total]
  \\ fs [IN_DEF] \\ res_tac \\ fs []
QED

Definition the_EvalDecs_def:
  the_EvalDecs (EvalDecs x) = x
End

Theorem compile_correct_eval:
  compile c prog = SOME (bytes,bitmaps,c') ⇒
   let (s0,env) = THE (prim_sem_env (ffi: 'ffi ffi_state)) in
   ¬semantics_prog (add_eval_state ev s0) env prog Fail ∧ backend_config_ok c ∧
   lab_to_targetProof$mc_conf_ok mc ∧ mc_init_ok c mc ∧ opt_eval_config_wf c' ev ∧
   installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
     (heap_regs c.stack_conf.reg_names) mc ms ⇒
   machine_sem mc ffi ms ⊆
     extend_with_resource_limit
       (semantics_prog (add_eval_state ev s0) env prog)
Proof
  fs [LET_THM] \\ pairarg_tac \\ rw []
  \\ mp_tac compile_correct' \\ fs []
  \\ rw [extend_with_resource_limit'_def]
  \\ fs [extend_with_resource_limit_def,SUBSET_DEF]
QED

val _ = export_theory();

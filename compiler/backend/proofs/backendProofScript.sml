(*
  Composes the correctness theorems for all of the compiler phases.
*)

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
  [ "backend", "backend_common", "backendProps",
    "primSemEnv", "semanticsProps",
    "labProps" (* for good_dimindex *)
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

(* TODO: remove when theorems are moved *)
val _ = temp_overload_on("obeys_max_app",``closProps$obeys_max_app``);
val _ = temp_overload_on("no_Labels",``closProps$no_Labels``);
val _ = temp_overload_on("every_Fn_SOME",``closProps$every_Fn_SOME``);
val _ = temp_overload_on("code_locs",``closProps$code_locs``);

(* TODO re-define syntax_ok on terms of things in closPropsTheory
 * (invent new properties), and prove elsewhere
 * that the pat_to_clos compiler satisfies these things.*)
Theorem syntax_ok_pat_to_clos:
   !e. clos_mtiProof$syntax_ok [pat_to_clos$compile e]
Proof
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
         clos_mtiProofTheory.syntax_ok_MAP]
QED

Theorem syntax_ok_MAP_pat_to_clos:
   !xs. clos_mtiProof$syntax_ok (MAP pat_to_clos_compile xs)
Proof
  Induct \\ fs [clos_mtiProofTheory.syntax_ok_def]
  \\ once_rewrite_tac [clos_mtiProofTheory.syntax_ok_cons]
  \\ fs [syntax_ok_pat_to_clos]
QED

Theorem syntax_ok_IMP_obeys_max_app:
   !e3. 0 < m /\ clos_mtiProof$syntax_ok e3 ==> EVERY (obeys_max_app m) e3
Proof
  ho_match_mp_tac clos_mtiProofTheory.syntax_ok_ind \\ rpt strip_tac \\ fs []
  \\ pop_assum mp_tac \\ once_rewrite_tac [clos_mtiProofTheory.syntax_ok_def]
  \\ fs [] \\ fs [EVERY_MEM,MEM_MAP,FORALL_PROD,PULL_EXISTS]
  \\ rw [] \\ res_tac
QED

(* TODO: move these *)
Theorem compile_common_syntax:
   !cf e3 cf1 e4.
      clos_to_bvl$compile_common cf e3 = (cf1,e4) ==>
      (EVERY no_Labels e3 ==>
       EVERY no_Labels (MAP (SND o SND) e4)) /\
      (0 < cf.max_app /\ clos_mtiProof$syntax_ok e3 ==>
       EVERY (obeys_max_app cf.max_app) (MAP (SND o SND) e4)) /\
      every_Fn_SOME (MAP (SND o SND) e4)
Proof
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
    \\ match_mp_tac clos_labelsProofTheory.no_Labels_labs
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
    \\ match_mp_tac clos_labelsProofTheory.obeys_max_app_labs
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
  \\ TRY (drule clos_callProofTheory.calls_preserves_every_Fn_SOME
          \\ impl_tac THEN1 (fs [] \\ EVAL_TAC) \\ strip_tac \\ fs [])
  \\ match_mp_tac clos_labelsProofTheory.every_Fn_SOME_labs
  \\ match_mp_tac clos_annotateProofTheory.every_Fn_SOME_ann
  \\ fs [closPropsTheory.every_Fn_SOME_APPEND]
  \\ match_mp_tac clos_to_bvlProofTheory.chain_exps_every_Fn_SOME \\ fs []
QED

Theorem compile_common_code_locs:
   !c es c1 xs.
      clos_to_bvl$compile_common c (MAP pat_to_clos_compile es) = (c1,xs) ==>
      BIGUNION (set (MAP closProps$get_code_labels (MAP (SND ∘ SND) xs))) ⊆
      set (MAP FST xs) ∪ set (code_locs (MAP (SND ∘ SND) xs))
Proof
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
  \\ DEP_REWRITE_TAC[closPropsTheory.get_code_labels_code_locs]
  \\ conj_tac THEN1
   (fs [o_DEF] \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]
    \\ rw[] \\ res_tac \\ fs [])
  \\ simp[]
  \\ conj_tac >- (
        simp[SUBSET_DEF, o_DEF, closPropsTheory.code_locs_map, MEM_FLAT,
             MEM_MAP, PULL_EXISTS] \\ metis_tac[] )
  \\ rename [`clos_labels$compile input`]
  \\ fs [closPropsTheory.BIGUNION_MAP_code_locs_SND_SND]
  \\ metis_tac [clos_labelsProofTheory.compile_any_dests_SUBSET_code_locs]
QED
(* -- *)

val _ = temp_overload_on("esgc_free",``patProps$esgc_free``);
val _ = temp_overload_on("elist_globals",``flatProps$elist_globals``);
val _ = temp_overload_on("set_globals",``flatProps$set_globals``);

Theorem word_list_exists_imp:
   dm = stack_removeProof$addresses a n /\
    dimindex (:'a) DIV 8 * n < dimword (:'a) ∧ good_dimindex (:'a) ⇒
    word_list_exists a n (fun2set (m1,dm:'a word set))
Proof
  metis_tac [stack_removeProofTheory.word_list_exists_addresses]
QED

Theorem compile_correct:
   compile (c:'a config) prog = SOME (bytes,bitmaps,c') ⇒
   let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   ¬semantics_prog s env prog Fail ∧
   backend_config_ok c ∧ lab_to_targetProof$mc_conf_ok mc ∧ mc_init_ok c mc ∧
   installed bytes cbspace bitmaps data_sp c'.ffi_names ffi (heap_regs c.stack_conf.reg_names) mc ms ⇒
     machine_sem (mc:(α,β,γ) machine_config) ffi ms ⊆
       extend_with_resource_limit (semantics_prog s env prog)
Proof
  srw_tac[][compile_eq_from_source,from_source_def,backend_config_ok_def,heap_regs_def] >>
  `c.lab_conf.asm_conf = mc.target.config` by fs[mc_init_ok_def] >>
  `c'.ffi_names = SOME mc.ffi_names` by fs[targetSemTheory.installed_def] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP source_to_flatProofTheory.compile_semantics)) >>
  fs[primSemEnvTheory.prim_sem_env_eq] >>
  qpat_x_assum`_ = s`(assume_tac o Abbrev_intro o SYM) >>
  qpat_x_assum`_ = env`(assume_tac o Abbrev_intro o SYM) >>
  `source_to_flatProof$precondition s env c.source_conf` by (
    simp[source_to_flatProofTheory.precondition_def] >>
    simp[Abbr`env`,Abbr`s`] >>
    srw_tac[QUANT_INST_ss[pair_default_qp,record_default_qp]][] >>
    rw[source_to_flatProofTheory.invariant_def] >>
    rw[source_to_flatProofTheory.genv_c_ok_def] >>
    rw[source_to_flatProofTheory.s_rel_cases] >>
    rw[flatSemTheory.initial_state_def] >>
    rw[prim_config_eq] >>
    rw[Once source_to_flatProofTheory.v_rel_cases] >>
    rw[namespacePropsTheory.nsLookup_Bind_v_some,PULL_EXISTS] \\
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
            val (arity, stamp) = pairSyntax.dest_pair (tassoc k d1)
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
     backendProps$pure_cc (λes. (MAP pat_to_clos$compile es, [])) (
      clos_to_bvlProof$compile_common_inc (c:'a config).clos_conf
         (backendProps$pure_cc (clos_to_bvlProof$compile_inc c.clos_conf.max_app)
           (bvl_to_bviProof$full_cc c.bvl_conf (backendProps$pure_cc bvi_to_data_compile_prog
             (λcfg. OPTION_MAP (I ## MAP data_to_word_gcProof$upper_w2w ## I) o
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
                         (compile_word_to_stack ((c.lab_conf.asm_conf.reg_count - (LENGTH c.lab_conf.asm_conf.avoid_regs + 3))-2) progs bm0))
                            cfg (MAP (λp. full_compile_single mc.target.config.two_reg_arith (mc.target.config.reg_count - (LENGTH mc.target.config.avoid_regs + 5))
                            aa (mc:('a,'b,'c)machine_config).target.config (p,NONE)) progs)) o
                            MAP (compile_part (c.data_conf with
                                                <| has_fp_ops := (1 < mc.target.config.fp_reg_count);
                                                   has_fp_tern := (mc.target.config.ISA = ARMv7 /\ 2 < mc.target.config.fp_reg_count) |>)))))))``
     |> ISPEC)
   |> Q.GEN`co`
   |> Q.GEN`k0`
   |>  drule)
  \\ disch_then(
       qspecl_then[`TODO_clock`,
                   `K ((TODO_co1,
                        (
                          (case
                            (FST(compile c.clos_conf.known_conf (SND (renumber_code_locs_list (make_even (LENGTH (compile p) + c.clos_conf.next_loc))
                                 (compile c.clos_conf.do_mti c.clos_conf.max_app (MAP compile (compile p)))))))
                          of NONE => LN | SOME x => x.val_approx_spt)
                        ,
                         (FST(SND(compile T (SND(compile c.clos_conf.known_conf (SND (renumber_code_locs_list
                            (make_even (LENGTH (compile p) + c.clos_conf.next_loc)) (compile c.clos_conf.do_mti c.clos_conf.max_app (MAP compile (compile p))))))))),
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
                           let c4_data_conf =
                                c.data_conf with
                                  <| has_fp_ops := (1 < c.lab_conf.asm_conf.fp_reg_count);
                                     has_fp_tern := (c.lab_conf.asm_conf.ISA = ARMv7 /\ 2 < c.lab_conf.asm_conf.fp_reg_count) |>  in
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
  qmatch_asmsub_abbrev_tac`clos_to_bvlProof$compile_common_inc cf (pure_cc (clos_to_bvlProof$compile_inc _) cc)`
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
    \\ `EVERY closProps$esgc_free e3`
    by (
      simp[Abbr`e3`, Abbr`p''`]
      \\ simp[EVERY_MAP]
      \\ simp[EVERY_MEM] \\ rw[]
      \\ irule pat_to_closProofTheory.compile_esgc_free
      \\ fs[Abbr`p'`]
      \\ pop_assum mp_tac
      \\ qid_spec_tac`x`
      \\ simp[GSYM EVERY_MEM]
      \\ irule flat_to_patProofTheory.compile_esgc_free
      \\ simp[GSYM ALL_EL_MAP]
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
      \\ `BAG_ALL_DISTINCT (closProps$elist_globals e3)`
      by (
        simp[Abbr`e3`,Abbr`p''`,Abbr`p'`]
        \\ simp[closPropsTheory.elist_globals_FOLDR]
        \\ simp[BAG_ALL_DISTINCT_FOLDR_BAG_UNION]
        \\ simp[EL_MAP]
        \\ simp[GSYM pat_to_closProofTheory.set_globals_eq]
        \\ CONV_TAC(REWR_CONV(GSYM(SIMP_RULE(srw_ss()++ARITH_ss)[EL_MAP](
                  Q.ISPEC`MAP patProps$set_globals (flat_to_pat$compile p)`BAG_ALL_DISTINCT_FOLDR_BAG_UNION
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
        \\ simp[LIST_TO_BAG_DISTINCT]
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
  qmatch_goalsub_abbrev_tac`bvlSem$semantics _ _ co cc`
  \\ Q.ISPEC_THEN`co`(drule o GEN_ALL) (Q.GEN`co`bvl_to_bviProofTheory.compile_semantics)
  \\ disch_then(qspec_then`ffi`mp_tac)
  \\ qunabbrev_tac`cc`
  \\ qmatch_goalsub_abbrev_tac`bvlSem$semantics _ _ co (full_cc _ cc) _`
  \\ disch_then(qspecl_then[`co`,`cc`]mp_tac)
  \\ fs[Abbr`c''''`]
  \\ impl_tac
  >- (
    conj_tac
    >- (
      simp[Abbr`co`, backendPropsTheory.FST_state_co, clos_knownProofTheory.FST_known_co]
      \\ simp[Abbr`co3`] \\ rw[] )
    \\ conj_tac >- (
      simp[Abbr`co`, backendPropsTheory.FST_state_co, clos_knownProofTheory.FST_known_co]
      \\ rw[Abbr`co3`] )
    \\ conj_tac >- (
      simp[Abbr`co`, backendPropsTheory.FST_state_co, clos_knownProofTheory.FST_known_co]
      \\ rw[Abbr`co3`] )
    \\ conj_tac
    >- (
      simp[Abbr`co`, backendPropsTheory.SND_state_co, clos_knownProofTheory.FST_known_co,
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
        \\ `bvl_to_bviProof$in_ns 2 n2` suffices_by rw[]
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
  fs[targetSemTheory.installed_def] \\

  qmatch_assum_abbrev_tac`good_init_state mc ms ffi bytes cbspace tar_st m dm io_regs cc_regs` \\
  qpat_x_assum`Abbrev(p7 = _)` mp_tac>>
  qmatch_goalsub_abbrev_tac`compile _ _ _ stk stoff`>>
  strip_tac \\
  qabbrev_tac`kkk = stk - 2`>>
  qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ data_oracle` \\

  qabbrev_tac `c4_data_conf = (c4.data_conf with <| has_fp_ops := (1 < c4.lab_conf.asm_conf.fp_reg_count);
                                                    has_fp_tern := (c4.lab_conf.asm_conf.ISA = ARMv7 /\ 2 < c4.lab_conf.asm_conf.fp_reg_count) |>)` \\
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
       (cfg,stack_to_labProof$compile_no_stubs c4.stack_conf.reg_names c4.stack_conf.jump stoff stk p))`\\
  qabbrev_tac`lab_st:('a,'a lab_to_target$config,'ffi) labSem$state = lab_to_targetProof$make_init mc ffi io_regs cc_regs tar_st m (dm ∩ byte_aligned) ms p7 lab_to_target$compile
       (mc.target.get_pc ms + n2w (LENGTH bytes)) cbspace lab_oracle` \\
  qabbrev_tac`stack_st_opt =
    stack_to_labProof$full_make_init
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
  qabbrev_tac`word_st = word_to_stackProof$make_init kkk stack_st (fromAList p5) word_oracle` \\
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
    first_x_assum drule>>
    EVAL_TAC>>rw[])>>
  disch_then(qspecl_then[`fromAList t_code`,`InitGlobals_location`,`p4`,`c4_data_conf`]mp_tac) \\
  (* TODO: make this auto *)
  disch_then(qspecl_then[`mc.target.config.two_reg_arith`,`kkk`,`c4.lab_conf.asm_conf`,`aa`]mp_tac) \\
  `∀n. EVERY ($<= data_num_stubs) (MAP FST (SND (bvl_to_bviProof$full_co c.bvl_conf co n)))` by (
    simp[Abbr`co`,full_co_def, Abbr`co3`,bvi_tailrecProofTheory.mk_co_def] \\
    simp[UNCURRY, backendPropsTheory.FST_state_co, clos_knownProofTheory.FST_known_co]
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
    qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ _ TODO_cc'`
    \\ qpat_x_assum`dataSem$semantics _ _ data_oracle _ _ ≠ Fail`mp_tac
    \\ qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ _ TODO_cc`
    \\ `TODO_cc' = TODO_cc` suffices_by simp[]
    \\ simp[Abbr`TODO_cc`,Abbr`TODO_cc'`, FUN_EQ_THM]
    \\ rpt gen_tac
    \\ AP_TERM_TAC
    \\ simp[Abbr`kkk`,Abbr`stk`]
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
    simp[Abbr`co`, backendPropsTheory.FST_state_co, clos_knownProofTheory.FST_known_co]
    \\ simp[Abbr`co3`]
    \\ rewrite_tac[COND_RATOR]
    \\ rewrite_tac[Ntimes COND_RAND 3]
    \\ simp[] )
  \\ drule (GEN_ALL bvl_to_bviProofTheory.compile_prog_distinct_locs)
  \\ impl_tac >- ( drule bvl_inlineProofTheory.compile_prog_names \\ rw[] )
  \\ strip_tac
  \\ `∀k. FST (SND (SND (FST (co k)))) = n2`
  by (
    simp[Abbr`co`, backendPropsTheory.FST_state_co, clos_knownProofTheory.FST_known_co]
    \\ simp[Abbr`co3`]
    \\ rewrite_tac[COND_RATOR]
    \\ rewrite_tac[Ntimes COND_RAND 3]
    \\ simp[] )
  \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_next_mono)
  \\ strip_tac
  \\ pop_assum(assume_tac o Abbrev_intro)

  \\ `∀k. FST (SND (SND (SND (FST (co k))))) = ((FST(compile c.lab_conf.asm_conf p5)).bitmaps)`
  by (
    simp[Abbr`co`, backendPropsTheory.FST_state_co, clos_knownProofTheory.FST_known_co]
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
    simp[Abbr`co`, backendPropsTheory.FST_state_co, clos_knownProofTheory.FST_known_co]
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
        \\ `stack_to_labProof$labels_ok (MAP prog_to_section ppg)`
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
          >- ( qhdtm_x_assum`lab_to_targetProof$mc_conf_ok`mp_tac \\ simp[mc_conf_ok_def] )
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
            \\ ... (* oracle labels... *) )
          \\ disj1_tac
          \\ fs[Abbr`p7`]
          \\ ... (* get_code_labels range...  *) )
        \\ qspec_then`ppg`mp_tac get_labels_MAP_prog_to_section_SUBSET_code_labels
        \\ simp[SUBSET_DEF]
        \\ strip_tac
        \\ gen_tac \\ strip_tac
        \\ first_x_assum drule
        \\ strip_tac \\ rw[]
        \\ ... (* referenced labels are present (for oracle) *) *))
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
      \\ qhdtm_assum`clos_knownProof$known_co`(mp_tac o Q.AP_TERM`FST`)
      \\ simp[clos_knownProofTheory.FST_known_co]
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
      metis_tac [labPropsTheory.EVERY_sec_label_ok])>>
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
      \\ drule (GEN_ALL bvi_tailrecProofTheory.compile_prog_keeps_names)
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
    \\ irule bvi_to_dataProofTheory.compile_prog_good_code_labels
    \\ qpat_x_assum`_ = (_,p3)`assume_tac
    \\ rpt(qhdtm_x_assum`semantics`kall_tac)
    \\ qpat_x_assum`_ = (_,code,_)`assume_tac
    \\ qpat_x_assum`_ = (_,prog')`assume_tac
    \\ qpat_x_assum`_ = (_,p''')`assume_tac
    \\ simp[bviPropsTheory.good_code_labels_def]
    \\ drule
      (bvi_tailrecProofTheory.compile_prog_good_code_labels
       |> INST_TYPE [alpha|->``:num#bvi$exp``]
       |> GEN_ALL)
    \\ disch_then match_mp_tac \\ fs []
    \\ qexists_tac `p3` \\ fs []
    \\ reverse conj_tac
    >-
     (imp_res_tac bvi_tailrecProofTheory.compile_prog_labels
      \\ pop_assum kall_tac
      \\ pop_assum (SUBST1_TAC o GSYM) \\ fs [])
    \\ drule bvi_tailrecProofTheory.compile_prog_labels
    \\ strip_tac
    \\ first_x_assum(CHANGED_TAC o SUBST1_TAC o GSYM)
    \\ drule bvl_to_bviProofTheory.compile_prog_get_code_labels
    \\ qmatch_goalsub_abbrev_tac`ss ⊆ star INSERT _`
    \\ drule bvl_inlineProofTheory.compile_prog_get_code_labels
    \\ strip_tac
    \\ fs[clos_to_bvlTheory.compile_def]
    \\ pairarg_tac \\ fs[] \\ rveq \\ fs[]
    \\ fs[clos_to_bvlProofTheory.set_MAP_code_sort]
    \\ qmatch_goalsub_abbrev_tac`star INSERT fcc ∪ pp`
    \\ `star ∈ fcc ∧ pp ⊆ fcc` suffices_by ( simp[SUBSET_DEF] \\ metis_tac[] )
    \\ drule (GEN_ALL bvl_to_bviProofTheory.compile_prog_code_labels_domain) \\ simp[]
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
      \\ simp[clos_to_bvlProofTheory.set_MAP_code_sort] )
    \\ simp[Abbr`pp`]
    \\ drule bvl_inlineProofTheory.compile_prog_names
    \\ rw[clos_to_bvlProofTheory.set_MAP_code_sort]
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
    \\ simp[linear_scanProofTheory.set_MAP_FST_toAList_eq_domain]
    \\ conj_tac >- (
      reverse conj_tac
      >- (
        simp[clos_to_bvlTheory.init_globals_def, closLangTheory.assign_get_code_label_def]
        \\ simp[clos_to_bvlTheory.partial_app_fn_location_def]
        \\ simp[SUBSET_DEF, MEM_MAP, PULL_EXISTS, MEM_FLAT, MEM_GENLIST,
                closLangTheory.assign_get_code_label_def,
                clos_to_bvlProofTheory.domain_init_code]
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
        \\ simp[closLangTheory.assign_get_code_label_def, bvlPropsTheory.get_code_labels_def,
                bvl_jumpTheory.Jump_def,
                clos_to_bvlTheory.partial_app_fn_location_code_def]
        \\ simp[MEM_MAP, MEM_GENLIST, PULL_EXISTS, bvl_jumpProofTheory.bvl_get_code_labels_JumpList]
        \\ simp[closLangTheory.assign_get_code_label_def, clos_to_bvlTheory.mk_cl_call_def]
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
      \\ fs[closLangTheory.assign_get_code_label_def, MEM_MAP, MEM_GENLIST] \\ rveq \\ fs[closLangTheory.assign_get_code_label_def] )
    \\ fs[clos_to_bvlTheory.compile_common_def]
    \\ rpt(pairarg_tac \\ fs[]) \\ rveq \\ fs[]
    \\ specl_args_of_then``clos_to_bvl$compile_prog``(Q.GENL[`max_app`,`prog`]
        clos_to_bvlProofTheory.compile_prog_code_labels)mp_tac
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
    \\ qmatch_goalsub_abbrev_tac`compile_prog _ (clos_labels$compile ls)`
    \\ simp[clos_to_bvlProofTheory.MAP_FST_compile_prog]
    \\ qunabbrev_tac`ff`
    \\ qmatch_goalsub_abbrev_tac`IMAGE ff AA ⊆ BB ∪ CC ∪ {mm}`
    \\ `DISJOINT (IMAGE ff AA) {mm}` by (
      simp[Abbr`ff`, Abbr`mm`,clos_to_bvlTheory.num_stubs_def] )
    \\ `DISJOINT (IMAGE ff AA) BB`
    by(
      simp[Abbr`ff`,Abbr`BB`,IN_DISJOINT,
           clos_to_bvlProofTheory.domain_init_code,clos_to_bvlTheory.num_stubs_def]
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
      \\ simp[GSYM ALL_EL_MAP, GSYM CONJ_ASSOC]
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
      \\ simp[GSYM ALL_EL_MAP]
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
    \\ fs[EVAL``(lab_to_targetProof$make_init a b c d e f g h i j k l m).compile``]
    \\ fs[Abbr`stoff`]
    \\ fs[EVAL``(word_to_stackProof$make_init a b c d).compile``]
    \\ fs[Abbr`kkk`,Abbr`stk`,Abbr`stack_st`] \\ rfs[]
    \\ qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ _ foo1`
    \\ qmatch_asmsub_abbrev_tac`dataSem$semantics _ _ _ foo2`
    \\ `foo1 = foo2` suffices_by fs[]
    \\ simp[Abbr`foo1`,Abbr`foo2`]
    \\ simp[FUN_EQ_THM]
    \\ rpt gen_tac \\ AP_TERM_TAC
    \\ qhdtm_assum`stack_to_labProof$full_make_init`(mp_tac o Q.AP_TERM`FST`)
    \\ simp_tac std_ss []
    \\ disch_then(SUBST1_TAC o SYM)
    \\ simp[full_make_init_compile, Abbr`lab_st`]
    \\ fs[EVAL``(lab_to_targetProof$make_init a b c d e f g h i j k l m).compile``] ) \\
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
    \\ qmatch_asmsub_abbrev_tac`dataSem$semantics _ _ _ foo1 _ ≠ Fail`
    \\ qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ _ foo2`
    \\ `foo1 = foo2` suffices_by metis_tac[]
    \\ simp[Abbr`foo1`,Abbr`foo2`,FUN_EQ_THM]
    \\ rpt gen_tac \\ AP_TERM_TAC
    \\ AP_THM_TAC
    \\ simp[EVAL``(word_to_stackProof$make_init a b c e).compile``]
    \\ rfs[Abbr`stack_st`]
    \\ qhdtm_assum`stack_to_labProof$full_make_init`(mp_tac o Q.AP_TERM`FST`)
    \\ simp_tac std_ss []
    \\ disch_then(SUBST_ALL_TAC o SYM)
    \\ fs[full_make_init_compile, Abbr`lab_st`]
    \\ fs[EVAL``(lab_to_targetProof$make_init a b c d e f g h i j k l m).compile``]) \\
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
  \\ qmatch_asmsub_abbrev_tac`dataSem$semantics _ _ _ foo1 _ ≠ Fail`
  \\ qmatch_goalsub_abbrev_tac`dataSem$semantics _ _ _ foo2`
  \\ `foo1 = foo2` suffices_by metis_tac[]
  \\ simp[Abbr`foo1`,Abbr`foo2`,FUN_EQ_THM]
  \\ rpt gen_tac \\ AP_TERM_TAC
  \\ rfs[Abbr`kkk`,Abbr`stk`]
  \\ AP_THM_TAC
  \\ simp[EVAL``(word_to_stackProof$make_init a b c e).compile``]
  \\ qhdtm_assum`stack_to_labProof$full_make_init`(mp_tac o Q.AP_TERM`FST`)
  \\ simp_tac std_ss []
  \\ disch_then(SUBST_ALL_TAC o SYM)
  \\ fs[full_make_init_compile, Abbr`lab_st`]
  \\ fs[EVAL``(lab_to_targetProof$make_init a b c d e f g h i j k l m).compile``]
QED

val _ = export_theory();

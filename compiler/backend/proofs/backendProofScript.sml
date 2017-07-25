open preamble primSemEnvTheory semanticsPropsTheory
     backendTheory
     source_to_modProofTheory
     mod_to_conProofTheory
     con_to_decProofTheory
     dec_to_exhProofTheory
     exh_to_patProofTheory
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

val pair_CASE_eq = Q.store_thm("pair_CASE_eq",
  `pair_CASE p f = a ⇔ ∃x y. p = (x,y) ∧ f x y = a`,
  Cases_on`p`>>rw[]);

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
  `4 < asm_conf.reg_count − (LENGTH asm_conf.avoid_regs + 5) /\
    (case bitmaps of [] => F | h::_ => 4w = h) /\
    good_dimindex (:α) ==>
    init_state_ok
      (asm_conf.reg_count − (LENGTH (asm_conf:'a asm_config).avoid_regs + 5))
      (full_make_init
        (bitmaps:'a word list,c1,code3,f,ggc,
         jump,k,max_heap,off,regs,s,save_regs))`,
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_def] \\ strip_tac
  \\ CASE_TAC \\ fs [] THEN1
   (fs [init_state_ok_def,data_to_word_gcProofTheory.gc_fun_ok_word_gc_fun]
    \\ strip_tac
    \\ fs [FUPDATE_LIST,stack_removeTheory.store_list_def,FLOOKUP_UPDATE]
    \\ fs [labPropsTheory.good_dimindex_def,dimword_def])
  \\ fs [] \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [init_state_ok_def,data_to_word_gcProofTheory.gc_fun_ok_word_gc_fun]
  \\ conj_tac THEN1 fs [labPropsTheory.good_dimindex_def]
  \\ `init_prop ggc max_heap x /\ x.bitmaps = 4w::t` by
        (fs [stack_removeProofTheory.make_init_opt_def]
         \\ every_case_tac \\ fs [stack_removeProofTheory.init_reduce_def] \\ rw [])
  \\ fs [stack_removeProofTheory.init_prop_def]
  \\ `x.stack <> []` by (rpt strip_tac \\ fs [])
  \\ `?t1 t2. x.stack = SNOC t1 t2` by metis_tac [SNOC_CASES]
  \\ fs [] \\ rpt var_eq_tac \\ fs[ADD1]
  \\ qpat_x_assum `LENGTH t2 = x.stack_space` (assume_tac o GSYM)
  \\ fs [DROP_LENGTH_APPEND] \\ fs [FLOOKUP_DEF]);

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

val full_make_init_bitmaps = Q.prove(
  `full_init_pre args ==>
    (full_make_init args).bitmaps = FST args`,
  PairCases_on`args` \\
  fs [full_make_init_def,stack_allocProofTheory.make_init_def,
      stack_removeProofTheory.make_init_any_bitmaps]
  \\ every_case_tac \\ fs [] \\ fs [full_init_pre_def]);

(* -- *)

(* TODO: Move somewhere, not sure where though *)
val make_init_opt_imp_bitmaps_limit = Q.store_thm("make_init_opt_imp_bitmaps_limit",
  `make_init_opt ggc max_heap bitmaps k code s = SOME x ==>
    LENGTH (bitmaps:'a word list) < dimword (:'a) − 1`,
  fs [stack_removeProofTheory.make_init_opt_def]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [stack_removeProofTheory.init_prop_def,
         stack_removeProofTheory.init_reduce_def]);

(* TODO: Move into stack_to_lab *)
val full_init_shared_def =
  let
    val (l,r) = full_init_pre_fail_def |> SPEC_ALL |> concl |> dest_eq
    val (_,a) = dest_comb l
    val t = r |> move_conj_right (optionSyntax.is_none o rhs) |> rconc |> dest_conj |> #1
  in
    new_definition("full_init_shared_def",``full_init_shared ^a = ^t``)
  end

val code_installed'_def = Define `
  (code_installed' n [] code ⇔ T) /\
  (code_installed' n (x::xs) code ⇔
     if is_Label x then code_installed' n xs code
     else asm_fetch_aux n code = SOME x ∧ code_installed' (n + 1) xs code)`;

val code_installed'_cons_label = Q.store_thm("code_installed'_cons_label",
  `!lines pos.
      is_Label h ==>
      code_installed' pos lines (Section n (h::xs)::other) =
      code_installed' pos lines (Section n xs::other)`,
  Induct \\ fs [code_installed'_def]
  \\ rw [] \\ fs [labSemTheory.asm_fetch_aux_def]);

val code_installed'_cons_non_label = Q.store_thm("code_installed'_cons_non_label",
  `!lines pos.
      ~is_Label h ==>
      code_installed' (pos+1) lines (Section n (h::xs)::other) =
      code_installed' pos lines (Section n xs::other)`,
  Induct \\ fs [code_installed'_def]
  \\ rw [] \\ fs [labSemTheory.asm_fetch_aux_def])
  |> Q.SPECL [`lines`,`0`] |> SIMP_RULE std_ss [];

val code_installed'_simp = Q.store_thm("code_installed'_simp",
  `!lines. code_installed' 0 lines (Section n (lines ++ rest)::other)`,
  Induct \\ fs [code_installed'_def]
  \\ fs [labSemTheory.asm_fetch_aux_def]
  \\ rpt strip_tac \\ IF_CASES_TAC
  \\ fs [code_installed'_cons_label,code_installed'_cons_non_label]);

val loc_to_pc_skip_section = Q.store_thm("loc_to_pc_skip_section",
  `!lines.
      n <> p ==>
      loc_to_pc n 0 (Section p lines :: xs) =
      case loc_to_pc n 0 xs of
      | NONE => NONE
      | SOME k => SOME (k + LENGTH (FILTER (\x. ~(is_Label x)) lines))`,
  Induct \\ once_rewrite_tac [labSemTheory.loc_to_pc_def] \\ fs []
  THEN1 (every_case_tac \\ fs [])
  \\ strip_tac \\ IF_CASES_TAC \\ fs [] \\ CASE_TAC \\ fs []);

val asm_fetch_aux_add = Q.store_thm("asm_fetch_aux_add",
  `!ys pc rest.
      asm_fetch_aux (pc + LENGTH (FILTER (λx. ¬is_Label x) ys))
        (Section pos ys::rest) = asm_fetch_aux pc rest`,
  Induct \\ fs [labSemTheory.asm_fetch_aux_def,ADD1]);

val labs_correct_def = Define `
  (labs_correct n [] code ⇔ T) /\
  (labs_correct n (x::xs) code ⇔
     if is_Label x then labs_correct n xs code /\
       (case x of
        | Label l1 l2 v2 => loc_to_pc l1 l2 code = SOME n
        | _ => T)
     else labs_correct (n + 1) xs code)`

val is_Label_def = labSemTheory.is_Label_def

val code_installed_eq = Q.store_thm("code_installed_eq",
  `!pc xs code.
      code_installed pc xs code <=>
      code_installed' pc xs code /\ labs_correct pc xs code`,
  Induct_on `xs`
  \\ fs [code_installed_def,code_installed'_def,labs_correct_def]
  \\ ntac 3 strip_tac \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `h` \\ fs [is_Label_def]
  \\ rw [] \\ eq_tac \\ fs []);

val code_installed_cons = Q.store_thm("code_installed_cons",
  `!xs ys pos pc.
      code_installed' pc xs rest ==>
      code_installed' (pc + LENGTH (FILTER (λx. ¬is_Label x) ys)) xs
        (Section pos ys :: rest)`,
  Induct \\ fs [] \\ fs [code_installed'_def]
  \\ ntac 4 strip_tac \\ IF_CASES_TAC \\ fs []
  \\ rw [] \\ res_tac \\ fs [asm_fetch_aux_add]);

val code_installed_prog_to_section_lemma = Q.prove(
  `!prog4 n prog3.
      ALOOKUP prog4 n = SOME prog3 ==>
      ?pc.
        code_installed' pc (append (FST (flatten prog3 n (next_lab prog3 1))))
          (MAP prog_to_section prog4) /\
        loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc`,
  Induct_on `prog4` \\ fs [] \\ Cases \\ fs [ALOOKUP_def] \\ rw []
  THEN1
   (fs [stack_to_labTheory.prog_to_section_def] \\ pairarg_tac \\ fs []
    \\ once_rewrite_tac [labSemTheory.loc_to_pc_def]
    \\ fs [code_installed'_simp])
  \\ res_tac \\ fs [stack_to_labTheory.prog_to_section_def] \\ pairarg_tac
  \\ fs [loc_to_pc_skip_section,code_installed_cons]);

val extract_labels_def = labPropsTheory.extract_labels_def
val extract_labels_append = labPropsTheory.extract_labels_append

val labs_correct_hd = Q.store_thm("labs_correct_hd",`
  ∀extra l.
  ALL_DISTINCT (extract_labels (extra++l)) ∧
  EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels (extra++l)) ⇒
  labs_correct (LENGTH (FILTER (\x. ~(is_Label x)) extra)) l (Section n (extra++l) ::code)`,
  Induct_on`l`>>fs[labs_correct_def]>>rw[]
  >-
    (first_x_assum(qspec_then `extra++[h]` mp_tac)>>
    Cases_on`h`>>fs[extract_labels_def,labSemTheory.is_Label_def,FILTER_APPEND]>>
    metis_tac[APPEND_ASSOC,APPEND])
  >-
    (Cases_on`h`>>fs[]>>
    ntac 2 (pop_assum mp_tac)>>
    rpt (pop_assum kall_tac)>>
    Induct_on`extra`>>fs[extract_labels_def]>>rw[]
    >-
      (once_rewrite_tac [labSemTheory.loc_to_pc_def]>>
      fs[])
    >>
    `n = n' ∧ n0 ≠ 0` by
      (Cases_on`h`>>fs[extract_labels_append,extract_labels_def])>>
    once_rewrite_tac [labSemTheory.loc_to_pc_def]>>
    Cases_on`h`>>fs[extract_labels_def]>>
    IF_CASES_TAC>>fs[extract_labels_append,extract_labels_def])
  >>
    first_x_assum(qspec_then `extra++[h]` mp_tac)>>
    Cases_on`h`>>fs[extract_labels_def,FILTER_APPEND]>>
    metis_tac[APPEND_ASSOC,APPEND]);

val labels_ok_imp = Q.store_thm("labels_ok_imp",
  `∀code.
   labels_ok code ⇒
   EVERY sec_labels_ok code ∧
   ALL_DISTINCT (MAP Section_num code) ∧
   EVERY (ALL_DISTINCT o extract_labels o Section_lines) code`,
  Induct_on`code` \\ simp[]
  \\ Cases \\ simp[]
  \\ fs[labels_ok_def]
  \\ strip_tac \\ fs[]
  \\ reverse conj_tac
  >- (
    strip_tac \\ fs[MEM_MAP,EXISTS_PROD] \\ fs[]
    \\ qmatch_assum_rename_tac`MEM sec code`
    \\ first_x_assum(qspec_then`sec`mp_tac) \\ simp[]
    \\ CASE_TAC \\ fs[] )
  \\ Induct_on`l` \\ fs[]
  \\ Cases \\ fs[]);

val labels_ok_labs_correct = Q.store_thm("labels_ok_labs_correct",`
  ∀code.
  labels_ok code ⇒
  EVERY ( λs. case s of Section n lines =>
      case loc_to_pc n 0 code of
       SOME pc => labs_correct pc lines code
      | _ => T) code`,
  Induct>>fs[labels_ok_def]>>Cases_on`h`>>fs[]>>
  rw[]
  >-
    (once_rewrite_tac[labSemTheory.loc_to_pc_def]>>fs[]>>
    assume_tac (Q.SPEC `[]` labs_correct_hd)>>fs[])
  >>
    fs[EVERY_MEM]>>rw[]>>res_tac>>
    Cases_on`s`>>fs[]>>
    `n ≠ n'` by
      (fs[MEM_MAP]>>
      last_x_assum kall_tac>>
      last_x_assum (qspec_then`Section n' l'` assume_tac)>>rfs[])>>
    fs[loc_to_pc_skip_section]>>
    BasicProvers.EVERY_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>
    pop_assum kall_tac>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    ntac 2 (pop_assum kall_tac)>>
    pop_assum mp_tac>>
    pop_assum mp_tac>>
    rpt (pop_assum kall_tac)>>
    qid_spec_tac`x`>>
    Induct_on`l'`>>rw[labs_correct_def]>>fs[AND_IMP_INTRO]
    >-
      (first_assum match_mp_tac>>
      Cases_on`h`>>fs[ALL_DISTINCT,extract_labels_def])
    >-
      (Cases_on`h`>>fs[]>>
      `n'' ≠ n` by
        (fs[extract_labels_def]>>
        first_x_assum(qspec_then`n'',n0` mp_tac)>>fs[])>>
      pop_assum mp_tac>>
      pop_assum mp_tac>>
      ntac 5 (pop_assum kall_tac)>>
      ntac 2 (pop_assum mp_tac)>>
      rpt (pop_assum kall_tac)>>
      map_every qid_spec_tac [`n''`,`n0`,`l`]>>
      Induct>> once_rewrite_tac [labSemTheory.loc_to_pc_def]>>fs[]>>
      rw[]>>fs[is_Label_def,extract_labels_def,AND_IMP_INTRO]
      >-
        (fs[FORALL_PROD]>>metis_tac[])
      >-
        (fs[FORALL_PROD]>>metis_tac[])
      >-
        (first_assum match_mp_tac>>
        Cases_on`h`>>fs[extract_labels_def])
      >>
        rveq>>fs[loc_to_pc_skip_section]>>
        (first_x_assum(qspecl_then[`n0`,`n''`] mp_tac)>>
        impl_tac>- (Cases_on`h`>>fs[extract_labels_def])>>
        fs[]))
    >>
      first_x_assum (qspec_then`x+1` mp_tac)>>
      impl_tac
      >-
        (Cases_on`h`>>fs[ALL_DISTINCT,extract_labels_def])
      >>
       fs[]);

val labs_correct_append = Q.store_thm("labs_correct_append",`
  ∀ls pc.
  labs_correct pc (ls ++ rest) code ⇒
  labs_correct pc ls code`,
  Induct>>fs[labs_correct_def]>>rw[]);

val code_installed_prog_to_section = Q.store_thm("code_installed_prog_to_section",
  `!prog4 n prog3.
      labels_ok (MAP prog_to_section prog4) ∧
      ALOOKUP prog4 n = SOME prog3 ==>
      ?pc.
        code_installed pc (append (FST (flatten prog3 n (next_lab prog3 1))))
          (MAP prog_to_section prog4) /\
        loc_to_pc n 0 (MAP prog_to_section prog4) = SOME pc`,
  rpt strip_tac \\ fs [code_installed_eq]
  \\ drule code_installed_prog_to_section_lemma \\ strip_tac
  \\ asm_exists_tac \\ fs []
  \\ imp_res_tac labels_ok_labs_correct
  \\ fs[EVERY_MEM,MEM_MAP]
  \\ imp_res_tac ALOOKUP_MEM
  \\ first_x_assum (qspec_then`prog_to_section (n,prog3)` mp_tac)
  \\ impl_tac >- metis_tac[]
  \\ BasicProvers.TOP_CASE_TAC>>fs[stack_to_labTheory.prog_to_section_def]
  \\ pairarg_tac>>fs[]>>rveq>>fs[]
  \\ metis_tac[labs_correct_append]);


(* TODO: should be defined in targetSem *)
(* CakeML code, bytes, and code buffer space, cspace, and FFI functions, ffi,
   are installed into the machine, mc_conf + ms
   r1 and r2 are the names of registers containing
   the first address of the CakeML heap and the first address past the CakeML stack
   i.e., the range of the data memory
*)
val installed_def = Define`
  installed bytes cbspace ffi (r1,r2) mc_conf ms ⇔
    ∃t m io_regs cc_regs.
      good_init_state mc_conf ms ffi bytes cbspace t m
      { w | t.regs r1 <=+ w ∧ w <+ t.regs r2 } io_regs cc_regs ∧
      byte_aligned (t.regs r1) ∧
      byte_aligned (t.regs r2) ∧
      t.regs r1 <=+ t.regs r2`;

(* this should let us remove a conjunct from good_init_state *)
val byte_aligned_lemma = Q.store_thm("byte_aligned_lemma",
  `byte_aligned a1 ∧ byte_aligned a2 ⇒
   (!w. a1 <=+ byte_align w ∧ byte_align w <+ a2 ⇒ a1 <=+ w ∧ w <+ a2)`,
   cheat);
(* -- *)

val byte_aligned_MOD = Q.store_thm("byte_aligned_MOD",`
  good_dimindex (:'a) ⇒
  ∀x:'a word.x ∈ byte_aligned ⇒
  w2n x MOD (dimindex (:'a) DIV 8) = 0`,
  rw[IN_DEF]>>
  fs [stack_removeProofTheory.aligned_w2n, alignmentTheory.byte_aligned_def]>>
  rfs[labPropsTheory.good_dimindex_def] \\ rfs []);

val prim_config = prim_config_eq |> concl |> lhs

val compiler_config_ok_def = Define`
  compiler_config_ok (c:'a config) ⇔
    c.source_conf = ^prim_config.source_conf ∧
    c.mod_conf = ^prim_config.mod_conf ∧
    0 < c.clos_conf.max_app ∧
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

(* TODO: ?? where to put these ?? *)
val mc_init_ok_def = Define`
  mc_init_ok c mc ⇔
  EVERY (λr. MEM (find_name c.stack_conf.reg_names (r + mc.target.config.reg_count -(LENGTH mc.target.config.avoid_regs+5))) mc.callee_saved_regs) [2;3;4] ∧
  find_name c.stack_conf.reg_names 2 = mc.len_reg ∧
  find_name c.stack_conf.reg_names 1 = mc.ptr_reg ∧
  find_name c.stack_conf.reg_names 0 =
    (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ∧
  (* the next two are implied by injectivity of find_name *)
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.len_reg ∧
  (case mc.target.config.link_reg of NONE => 0 | SOME n => n) ≠ mc.ptr_reg ∧
  ¬MEM (case mc.target.config.link_reg of NONE => 0 | SOME n => n) mc.callee_saved_regs`

val compile_correct = Q.store_thm("compile_correct",
  `compile (c:'a config) prog = SOME (bytes,c') ⇒
   let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
   ¬semantics_prog s env prog Fail ∧
   compiler_config_ok c ∧ mc_conf_ok mc ∧
   mc_init_ok c mc ∧
   c.lab_conf.asm_conf = mc.target.config ∧
   c'.ffi_names = SOME mc.ffi_names ∧ (* TODO: compile should return new config *)
   installed bytes cbspace ffi
     (find_name c.stack_conf.reg_names 2,
      find_name c.stack_conf.reg_names 4) mc ms ⇒
     machine_sem (mc:(α,β,γ) machine_config) ffi ms ⊆
       extend_with_resource_limit (semantics_prog s env prog)`,
  srw_tac[][compile_eq_from_source,from_source_def,compiler_config_ok_def] >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP source_to_modProofTheory.compile_correct)) >>
  fs[primSemEnvTheory.prim_sem_env_eq] >>
  qpat_x_assum`_ = s`(assume_tac o Abbrev_intro o SYM) >>
  qpat_x_assum`_ = env`(assume_tac o Abbrev_intro o SYM) >>
  `∃s2 env2 gtagenv.
     precondition s env c.source_conf s2 env2 ∧
     nsDomMod env2.c = {[]} ∧
     s2.globals = [] ∧
     s2.ffi = ffi ∧
     s2.refs = [] ∧
     s2.defined_types = s.defined_types ∧
     (* s2.defined_mods = s.defined_mods ∧ *)
     envC_tagged env2.c (prim_config:'a backend$config).mod_conf.tag_env gtagenv ∧
     exhaustive_env_correct (prim_config:'a backend$config).mod_conf.exh_ctors_env gtagenv ∧
     gtagenv_wf gtagenv ∧
     next_inv s.defined_types
       (prim_config:'a backend$config).mod_conf.next_exception gtagenv` by (
    simp[source_to_modProofTheory.precondition_def] >>
    simp[Abbr`env`,Abbr`s`] >>
    srw_tac[QUANT_INST_ss[pair_default_qp,record_default_qp]][] >>
    rw[source_to_modProofTheory.invariant_def] >>
    rw[source_to_modProofTheory.s_rel_cases] >>
    (* TODO: Not sure why these got broken *)
    rw[Once source_to_modProofTheory.v_rel_cases] >>
    simp[Once (GSYM PULL_EXISTS)]>> CONJ_TAC >-
      (rw[]>>Cases_on`x`>>fs[namespaceTheory.nsLookup_def])>>
    rw[Once prim_config_eq] >>
    simp[Once (GSYM PULL_EXISTS)]>> CONJ_TAC >-
      (rw[namespaceTheory.nsDomMod_def,EXTENSION,GSPECIFICATION,PULL_EXISTS]>>
      simp[EXISTS_PROD]>>Cases_on`x`>>fs[namespaceTheory.nsLookupMod_def])>>
    rw[envC_tagged_def, mod_to_conTheory.lookup_tag_env_def,PULL_EXISTS] >>
    CONV_TAC(PATH_CONV"blrbbblr"EVAL) >>
    rw[prim_config_eq,option_fold_def] >>
    CONV_TAC(PATH_CONV"blrbbbrbblr"EVAL) >>
    (fn g as (asl,w) =>
      let
        val tms = w |> dest_exists |> #2
                    |> dest_conj |> #1
                    |> strip_forall |> #2
                    |> dest_imp |> #2
                    |> strip_exists |> #2
                    |> funpow 2 (rand o rator)
                    |> lhs |> funpow 2 (rand o rator)
        val (ls,ty) = listSyntax.dest_list tms
        val (ty1,ty2) = pairSyntax.dest_prod ty
        val (ty2,ty3) = pairSyntax.dest_prod ty2
        val (ty3,ty4) = pairSyntax.dest_prod ty3
        val ty1 = pairSyntax.mk_prod(ty1,ty4)
        val ty2 = pairSyntax.mk_prod (ty3,ty2)
        fun fix_pair tm =
          let val ls = pairSyntax.strip_pair tm
          in pairSyntax.mk_pair(pairSyntax.mk_pair(el 1 ls, el 4 ls),
                                pairSyntax.mk_pair(el 3 ls, el 2 ls))
          end
        val ls = map fix_pair ls
        val fm = finite_mapSyntax.list_mk_fupdate
                  (finite_mapSyntax.mk_fempty (ty1,ty2), ls)
      in exists_tac fm end g) >>
    conj_tac
    >- (
      Cases \\ simp[nsLookup_Bind_v_some,FLOOKUP_UPDATE,namespaceTheory.id_to_n_def] >>
      rpt ( IF_CASES_TAC \\ fs[] \\ rveq \\ fs[] )) >>
    conj_tac >- (
      simp[exhaustive_env_correct_def,IN_FRANGE,FLOOKUP_UPDATE,PULL_EXISTS] >>
      srw_tac[DNF_ss][] >>
      EVAL_TAC >>
      pop_assum mp_tac >> rw[] >>
      EVAL_TAC >>
      simp[PULL_EXISTS]) >>
    conj_tac >- (
      EVAL_TAC >> rw[] >> fs[semanticPrimitivesTheory.same_tid_def,namespaceTheory.id_to_n_def] ) >>
    simp[next_inv_def,PULL_EXISTS] >>
    simp[FLOOKUP_UPDATE] >>
    rw[] >> EVAL_TAC >>
    srw_tac[QUANT_INST_ss[std_qp]][]) >>
  disch_then drule >> strip_tac >>
  pairarg_tac \\ fs[] >>
  qhdtm_x_assum`from_mod`mp_tac >>
  srw_tac[][from_mod_def,mod_to_conTheory.compile_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_assum_abbrev_tac`semantics_prog s env prog sem2` >>
  `sem2 ≠ Fail` by metis_tac[] >>
  `semantics_prog s env prog = { sem2 }` by (
    simp[EXTENSION,IN_DEF] >>
    metis_tac[semantics_prog_deterministic] ) >>
  qunabbrev_tac`sem2` >>
  drule (GEN_ALL mod_to_conProofTheory.compile_prog_semantics) >>
  fs[] >> rveq >>
  simp[AND_IMP_INTRO] >> simp[Once CONJ_COMM] >>
  disch_then drule >>
  simp[mod_to_conProofTheory.invariant_def,
       mod_to_conTheory.get_exh_def,
       mod_to_conTheory.get_tagenv_def] >>
  simp[mod_to_conProofTheory.s_rel_cases] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[mod_to_conProofTheory.cenv_inv_def] >>
  disch_then(qspec_then`gtagenv`mp_tac)>>
  impl_tac >- ( fs[] >> rw[Abbr`s`,prim_config_eq] ) >>
  strip_tac >>
  pop_assum(assume_tac o SYM) >> simp[] >>
  qmatch_assum_rename_tac`from_con ccon _ = _` \\
  qunabbrev_tac`ccon`>>
  qhdtm_x_assum`from_con`mp_tac >>
  srw_tac[][from_con_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  rfs[] >> fs[] >>
  qpat_x_assum`Fail ≠ _`(assume_tac o GSYM) >>
  drule(GEN_ALL(MATCH_MP SWAP_IMP (REWRITE_RULE[GSYM AND_IMP_INTRO]con_to_decProofTheory.compile_semantics))) >>
  simp[] >>
  impl_tac >- (
    qhdtm_x_assum`mod_to_con$compile_prog`mp_tac >>
    simp[prim_config_eq] >> EVAL_TAC >>
    `semantics env2 s2 p ≠ Fail` by simp[] >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[modSemTheory.semantics_def] >>
    IF_CASES_TAC >> simp[] >> disch_then kall_tac >>
    pop_assum mp_tac >>
    simp[modSemTheory.evaluate_prog_def] >>
    BasicProvers.TOP_CASE_TAC >> simp[] >> strip_tac >> fs[] >>
    `¬MEM "option" (prog_to_top_types p)` by (
      fs[modSemTheory.no_dup_top_types_def,IN_DISJOINT,MEM_MAP] >>
      fs[Abbr`s`] >> metis_tac[] ) >>
    strip_tac >>
    match_mp_tac compile_prog_exh_unchanged >>
    asm_exists_tac >> simp[] >>
    qmatch_assum_abbrev_tac`compile_prog st p = _` >>
    qexists_tac`st`>>simp[Abbr`st`,mod_to_conTheory.get_exh_def] >>
    simp[FLOOKUP_UPDATE]) >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_dec`mp_tac >> srw_tac[][from_dec_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qhdtm_x_assum`con_to_dec$compile`mp_tac >>
  qmatch_assum_rename_tac`compile _ _ = (cc,_)` >>
  `cc.next_global = 0` by (
    fs[source_to_modTheory.compile_def,LET_THM] >>
    pairarg_tac >> fs[] >>
    rveq >> simp[prim_config_eq] ) >> fs[] >>
  strip_tac >> fs[] >>
  qmatch_assum_rename_tac`from_exh c3 _ = _` >>
  qunabbrev_tac`c3`>>fs[] >>
  qmatch_abbrev_tac`_ ⊆ _ { decSem$semantics env3 st3 [e3] }` >>
  (dec_to_exhProofTheory.compile_semantics
    |> Q.GENL[`env`,`st`,`e`,`envh`,`sth`]
    |> qispl_then[`env3`,`st3`,`e3`]mp_tac) >>
  simp[Abbr`env3`] >>
  simp[Once dec_to_exhProofTheory.v_rel_cases] >>
  simp[dec_to_exhProofTheory.state_rel_def] >>
  fs[Abbr`st3`,con_to_decProofTheory.compile_state_def] >>
  CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[record_default_qp,pair_default_qp])[])) >>
  simp[Abbr`e3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_exh`mp_tac >>
  srw_tac[][from_exh_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  fs[exh_to_patTheory.compile_def] >>
  qmatch_abbrev_tac`_ ⊆ _ { exhSem$semantics env3 st3 es3 }` >>
  (exh_to_patProofTheory.compile_exp_semantics
   |> Q.GENL[`env`,`st`,`es`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`es3`,Abbr`env3`] >>
  fs[exh_to_patProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_pat`mp_tac >>
  srw_tac[][from_pat_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { patSem$semantics env3 st3 es3 }` >>
  (pat_to_closProofTheory.compile_semantics
   |> Q.GENL[`env`,`st`,`es`,`max_app`]
   |> qispl_then[`env3`,`st3`,`es3`]mp_tac) >>
  simp[Abbr`env3`,Abbr`es3`] >>
  first_assum(fn th => disch_then(mp_tac o C MATCH_MP th)) >>
  fs[pat_to_closProofTheory.compile_state_def,Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_clos`mp_tac >>
  srw_tac[][from_clos_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { closSem$semantics [] st3 [e3] }` >>
  (clos_to_bvlProofTheory.compile_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["s","e","c"]))
   |> qispl_then[`st3`,`e3`,`c.clos_conf`]mp_tac) >>
  simp[] >>
  impl_tac >- (
    `esgc_free e3 ∧ BAG_ALL_DISTINCT (set_globals e3)` by
      (unabbrev_all_tac>>
      fs[con_to_decTheory.compile_def]>> pairarg_tac>>fs[]>>
      metis_tac[SND,
      mod_to_conProofTheory.compile_no_set_globals,con_to_decProofTheory.no_set_globals_imp_esgc_free,con_to_decTheory.compile_def,dec_to_exhProofTheory.compile_esgc_free,exh_to_patProofTheory.compile_esgc_free,pat_to_closProofTheory.compile_esgc_free,
      mod_to_conProofTheory.compile_no_set_globals,con_to_decProofTheory.no_set_globals_imp_bag_all_distinct,con_to_decTheory.compile_def,dec_to_exhProofTheory.compile_distinct_setglobals,exh_to_patProofTheory.compile_distinct_setglobals,pat_to_closProofTheory.compile_distinct_setglobals])>>
    EVAL_TAC>>simp[Abbr`st3`]>>
    unabbrev_all_tac >>
    simp[pat_to_closProofTheory.compile_contains_App_SOME] >>
    simp[pat_to_closProofTheory.compile_every_Fn_vs_NONE] >>
    simp[EVEN_ADD,EVEN_EXP_IFF])>>
  simp[Abbr`e3`] >>
  fs[Abbr`st3`] >>
  disch_then(strip_assume_tac o SYM) >> fs[] >>
  qhdtm_x_assum`from_bvl`mp_tac >>
  srw_tac[][from_bvl_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  Q.ISPEC_THEN`s2.ffi`drule(Q.GEN`ffi0` bvl_to_bviProofTheory.compile_semantics) >>
  qunabbrev_tac`c'''`>>fs[] >>
  impl_keep_tac >- (
    match_mp_tac (GEN_ALL clos_to_bvlProofTheory.compile_all_distinct_locs)>>
    qexists_tac`e''''`>>
    qexists_tac`c''`>>
    qexists_tac`c.clos_conf`>>
    simp[]>>
    EVAL_TAC >>
    simp[EVEN_ADD,EVEN_EXP_IFF])>>
  disch_then(SUBST_ALL_TAC o SYM) >>
  qhdtm_x_assum`from_bvi`mp_tac >>
  srw_tac[][from_bvi_def] >>
  pop_assum mp_tac >> BasicProvers.LET_ELIM_TAC >>
  qmatch_abbrev_tac`_ ⊆ _ { bviSem$semantics ffi (fromAList p3) s3 }` >>
  (bvi_to_dataProofTheory.compile_prog_semantics
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["prog","start"]))
   |> qispl_then[`p3`,`s3`,`ffi`]mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (SUBST_ALL_TAC o SYM)
  \\ `s3 = InitGlobals_location` by
   (fs [bvl_to_bviTheory.compile_def,bvl_to_bviTheory.compile_prog_def]
    \\ rpt (pairarg_tac \\ fs []))
  \\ rename1 `from_data c4 p4 = _`
  \\ qhdtm_x_assum`from_data`mp_tac
  \\ simp[from_data_def]
  \\ pairarg_tac \\ fs[]
  \\ strip_tac
  \\ rename1`compile _ _ _ p4 = (col,p5)` \\
  qhdtm_x_assum`from_word`mp_tac \\
  simp[from_word_def] \\ pairarg_tac \\ fs[] \\ strip_tac \\
  qmatch_assum_rename_tac`compile _ p5 = (c6,p6)` \\
  fs[from_stack_def,from_lab_def] \\
  qmatch_assum_abbrev_tac`compile c4.lab_conf p7 = SOME (bytes,c')`
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
    metis_tac[])>>
  strip_tac>>
  drule (word_to_stack_stack_convs|> GEN_ALL)>>
  simp[]>>
  impl_tac>-
    (fs[compiler_config_ok_def,Abbr`c4`]>>
    fs[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD]>>
    fs[PULL_EXISTS]>>
    metis_tac[])>>
  strip_tac>>
  fs[data_to_wordTheory.compile_def]
  \\ qmatch_assum_abbrev_tac`compile _ _ t_code = (_,p5)`
  \\ imp_res_tac compile_distinct_names
  \\ `MAP FST p4 = MAP FST p3`
  by metis_tac[bvi_to_dataProofTheory.MAP_FST_compile_prog]
  \\ `code_rel c4.data_conf (fromAList p4) (fromAList t_code)`
  by (
    simp[data_to_word_gcProofTheory.code_rel_def] \\
    simp[Abbr`t_code`,lookup_fromAList,ALOOKUP_APPEND,EVERY_MEM,FORALL_PROD] \\
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
  `code_rel_ext (fromAList t_code, fromAList p5)` by metis_tac[code_rel_ext_word_to_word] \\
  fs[installed_def] \\
  qmatch_assum_abbrev_tac`good_init_state mc ms ffi bytes cbspace tar_st m dm io_regs cc_regs` \\
  qpat_x_assum`Abbrev(tar_st = _)`kall_tac \\
  qabbrev_tac`coracle =λn:num.
      (<| labels := c'.labels; pos := LENGTH bytes; asm_conf := mc.target.config; ffi_names := SOME mc.ffi_names|>, ([]:'a labLang$prog))` \\
  qabbrev_tac`lab_st:('a,'a lab_to_target$config,'ffi) labSem$state = make_init mc ffi io_regs cc_regs tar_st m (dm ∩ byte_aligned) ms p7 lab_to_target$compile
       (mc.target.get_pc ms + n2w (LENGTH bytes)) cbspace coracle` \\
  (* syntactic properties from stack_to_lab *)
  `labels_ok p7` by
    (fs[Abbr`p7`]>>
    match_mp_tac stack_to_lab_compile_lab_pres>>
    rw[]>>EVAL_TAC>>
    fs[EVERY_MEM]>> rpt strip_tac>>
    first_x_assum drule>>
    EVAL_TAC>>rw[])>>
  `all_enc_ok_pre c4.lab_conf.asm_conf p7` by
    (fs[Abbr`p7`]>>
    match_mp_tac stack_to_lab_compile_all_enc_ok>>
    fs[stackPropsTheory.reg_name_def,Abbr`c4`,mc_conf_ok_def]>>
    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]>>rfs[]>>
    metis_tac[])>>
  qpat_x_assum`Abbrev(p7 = _)` mp_tac>>
  simp[stack_to_labTheory.compile_def]>>
  qpat_abbrev_tac`sl1 = stack_alloc$compile _ p6`>>
  qpat_abbrev_tac`sl2 = stack_remove$compile _ _ _ _ _ _ _ sl1`>>
  qpat_abbrev_tac`sl3 = stack_names$compile _ sl2`>>
  strip_tac>>
  qmatch_asmsub_abbrev_tac`stack_remove$compile stjump stoff _ _ _ stk _ _`>>
  (* syntactic properties of stackLang passes needed to discharge full_init *)
  (* stack_alloc *)
  drule (GEN_ALL stack_allocProofTheory.stack_alloc_call_args |> INST_TYPE[beta|->alpha])>>
  disch_then(qspec_then `c4`assume_tac)>>
  drule (GEN_ALL stack_allocProofTheory.stack_alloc_reg_bound |> INST_TYPE[beta|->alpha] |>
    SIMP_RULE std_ss [Once CONJ_COMM])>>
  disch_then(qspec_then `c4`mp_tac)>>
  impl_tac>-
    fs[Abbr`stk`,compiler_config_ok_def,Abbr`c4`]>>
  strip_tac>>
  rfs[]>>
  (* stack_remove *)
  qpat_x_assum`Abbrev (sl2 = _)` mp_tac>> simp[Once markerTheory.Abbrev_def]>>
  disch_then (assume_tac o SYM)>>
  drule (stack_removeProofTheory.stack_remove_call_args)>>
  simp[]>> strip_tac>>
  (* stack_names *)
  qpat_x_assum`Abbrev (sl3 = _)` mp_tac>> simp[Once markerTheory.Abbrev_def]>>
  disch_then (assume_tac o SYM)>>
  drule stack_namesProofTheory.stack_names_call_args>>
  simp[]>> strip_tac>>
  qabbrev_tac`stregs = MAP (find_name c.stack_conf.reg_names) [2;3;4]`>>
  qabbrev_tac`stack_st =
    full_make_init (c6.bitmaps,c.data_conf,p6,c.stack_conf.reg_names,is_gen_gc c.data_conf.gc_kind,
                    stjump,stk,2 * max_heap_limit (:'a) c.data_conf - 1,
                    stoff,stregs,lab_st,set mc.callee_saved_regs)` \\
  qmatch_asmsub_abbrev_tac`full_make_init stack_args`>>
  qabbrev_tac`word_st = make_init stack_st (fromAList p5)` \\
  (data_to_wordProofTheory.compile_semantics
   |> DISCH_ALL
   |> GEN_ALL
   |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["t"]))
   |> qspec_then`word_st`mp_tac) \\
  disch_then(qspecl_then[`fromAList t_code`,`InitGlobals_location`,`p4`,`c4.data_conf`]mp_tac) \\
  impl_tac >- (
    simp[Abbr`word_st`,word_to_stackProofTheory.make_init_def,Abbr`c4`] \\
    fs[mc_conf_ok_def] \\
    conj_tac >- (
      simp[Abbr`stack_st`,Abbr`stack_args`] \\
      simp[full_make_init_def,stack_allocProofTheory.make_init_def] ) \\
    simp[Abbr`stack_st`,Abbr`stack_args`] \\
    match_mp_tac IMP_init_store_ok \\ simp[] ) \\
  `lab_st.ffi = ffi` by ( fs[Abbr`lab_st`] ) \\
  `word_st.ffi = ffi` by (
    simp[Abbr`word_st`,word_to_stackProofTheory.make_init_def] \\
    fs[Abbr`stack_st`,Abbr`stack_args`,Abbr`lab_st`,full_make_init_ffi] ) \\
  `ffi.final_event = NONE` by
    fs[installed_def,good_init_state_def]>>
  impl_tac >- fs[Abbr`word_st`,word_to_stackProofTheory.make_init_def] \\
  strip_tac \\
  (* This invariant is shared between full_init_pre_fail and full_init_pre *)
  `full_init_shared stack_args` by (
    simp[full_init_shared_def,Abbr`stack_args`] \\
    CONJ_TAC >- (
      (* stl *)
      simp[state_rel_make_init,Abbr`lab_st`,make_init_def]>>
      CONJ_TAC>-
        (fs[Abbr`c4`,lookup_fromAList]>>rw[]
        >-
          (imp_res_tac ALOOKUP_MEM>>
          fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]>>
          rfs[mc_init_ok_def]>>
          metis_tac[])>>
        metis_tac[code_installed_prog_to_section])>>
      fs[mc_init_ok_def,Abbr`dm`]>>
      fs[mc_conf_ok_def]>>
      metis_tac[byte_aligned_MOD])>>
    CONJ_TAC>-
      (unabbrev_all_tac>>
      qpat_x_assum`_ = sl3` sym_sub_tac>>
      qpat_x_assum`_ = sl2` sym_sub_tac>>
      simp[stack_removeTheory.compile_def
          ,stack_namesTheory.compile_def
          ,stack_to_labTheory.compile_def
          ,stack_to_labTheory.prog_to_section_def
          ,stack_removeTheory.init_stubs_def
          ,stack_namesTheory.prog_comp_def]>>
      pairarg_tac \\ fs [] \\ fs [Once labSemTheory.loc_to_pc_def])>>
    CONJ_TAC>-
      (* stack rm*)
      (simp[stack_removeProofTheory.init_pre_def]>>
      rw[]
      >-
        (simp[stack_to_labProofTheory.make_init_def,stack_namesProofTheory.make_init_def
            ,stack_removeTheory.compile_def]>>
        simp[stack_removeTheory.init_stubs_def,lookup_fromAList])
      >-
        (EVAL_TAC>>fs[])
      >>
        simp[stack_removeProofTheory.init_code_pre_def]>>
        simp[stack_to_labProofTheory.make_init_def,stack_namesProofTheory.make_init_def
             ,stack_removeTheory.compile_def,GSYM PULL_EXISTS]>>
        CONJ_TAC >-
          fs[mc_conf_ok_def]>>
        CONJ_TAC >-
          fs[Abbr`stk`,Abbr`c4`]>>
        CONJ_TAC >-
          (simp[domain_fromAList]>>
          DISJ1_TAC>>
          EVAL_TAC)>>
        CONJ_TAC>-
          (fs[mc_init_ok_def,Abbr`stk`,Abbr`c4`]>>
          metis_tac[LINV_DEF,IN_UNIV,BIJ_DEF])>>
        simp[PULL_EXISTS]>>
        simp[Abbr`lab_st`,make_init_def,Abbr`dm`,Abbr`stregs`]>>
        simp[BIJ_FLOOKUP_MAPKEYS,flookup_fupdate_list]>>
        fs[installed_def,mc_conf_ok_def]>>
        rpt (qpat_x_assum `byte_aligned (_.regs _)` mp_tac)>>
        rpt (qpat_x_assum `_ <=+ _` mp_tac)>>
        qspec_tac (`tar_st.regs (find_name c.stack_conf.reg_names 2)`,`a`)>>
        qspec_tac (`tar_st.regs (find_name c.stack_conf.reg_names 4)`,`b`)>>
        `(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8` by
         rfs [labPropsTheory.good_dimindex_def,bytes_in_word_def,dimword_def]>>
        fs [] \\ rpt strip_tac>>
        match_mp_tac word_list_exists_imp>>
        fs [addresses_thm]>>
        fs[mc_conf_ok_def]>>
        `0 < dimindex (:α) DIV 8` by
          rfs [labPropsTheory.good_dimindex_def]>>
        reverse conj_tac >-
         (fs [] \\ match_mp_tac IMP_MULT_DIV_LESS \\ fs [w2n_lt]
          \\ rfs [labPropsTheory.good_dimindex_def])
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
        \\ rfs [] \\ fs [] \\ match_mp_tac MOD_SUB_LEMMA \\ fs [])>>
    CONJ_TAC>- (
      simp[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,Abbr`c4`]>>
      rw[]>-
        (fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]>>
        metis_tac[])>>
      fs[Abbr`sl1`,stack_allocTheory.compile_def]
      >-
        (fs[stack_allocTheory.stubs_def]>>
        EVAL_TAC)
      >>
        `MEM p_1 (MAP FST p6)` by
          (fs[stack_allocProofTheory.prog_comp_lambda,MEM_MAP]>>
          pairarg_tac>>fs[]>>
          metis_tac[FST])>>
        rfs[]
        >-
          EVAL_TAC
        >-
          (pop_assum mp_tac>>EVAL_TAC>>
          rpt(pop_assum kall_tac)>>
          DECIDE_TAC)
        >>
          fs[EVERY_MEM]>>
          first_x_assum drule>>
          EVAL_TAC>>fs[])>>
    rw[]>>EVAL_TAC>>
    CCONTR_TAC>>fs[EVERY_MEM]>>
    first_x_assum drule>>
    EVAL_TAC)>>
  qmatch_abbrev_tac`x ⊆ extend_with_resource_limit y` \\
  `Fail ∉ y` by fs[Abbr`y`] \\
  pop_assum mp_tac \\ simp[GSYM implements_def] \\
  simp[Abbr`y`] \\
  drule (GEN_ALL semantics_compile) \\
  disch_then(drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(optionSyntax.is_some o rhs))))) \\
  simp[Abbr`c4`] \\
  disch_then(drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(move_conj_left(same_const``good_init_state`` o fst o strip_comb))))) \\
  disch_then(qspec_then`coracle`mp_tac) \\
  impl_tac >- (
    conj_tac >- simp[compiler_oracle_ok_def,good_code_def,Abbr`coracle`] \\
    fs[good_code_def,labels_ok_def] \\
    rfs[]>>rw[]
    >-
      fs[Abbr`p7`]
    >-
      (match_mp_tac (MP_CANON EVERY_MONOTONIC)>>
      simp[Once CONJ_COMM]>>
      qpat_x_assum`all_enc_ok_pre _ _` kall_tac>>
      asm_exists_tac>>
      simp[]>>Cases>> simp[]>>
      rpt(pop_assum kall_tac)>>
      Induct_on`l`>>simp[extract_labels_def]>>
      Cases>>simp[extract_labels_def])
    >-
      (qpat_x_assum`ALL_DISTINCT (MAP _ p7)` mp_tac>>
      qmatch_goalsub_abbrev_tac`MAP ff p7`>>
      `ff = Section_num` by
        (simp[Abbr`ff`,FUN_EQ_THM]>>
        Cases>>simp[])>>
      simp[])
    >-
      (match_mp_tac (MP_CANON EVERY_MONOTONIC)>>
      simp[Once CONJ_COMM]>>
      qpat_x_assum`all_enc_ok_pre _ _` kall_tac>>
      asm_exists_tac>>
      simp[]>>Cases>> simp[]))>>
  strip_tac \\
  Cases_on`full_init_pre_fail stack_args` >- (
    qunabbrev_tac`stack_args` \\
    drule full_make_init_semantics_fail \\
    strip_tac \\ rfs[] \\
    match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
    simp[Once CONJ_COMM] \\
    asm_exists_tac \\ simp[] \\
    match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
    simp[Once CONJ_COMM] \\
    asm_exists_tac \\ simp[] \\
    metis_tac[dataPropsTheory.Resource_limit_hit_implements_semantics] ) \\
  `full_init_pre stack_args` by (
    fs[full_init_pre_def,full_init_shared_def,Abbr`stack_args`] \\
    IF_CASES_TAC \\ fs[] >- (
      fs[IS_SOME_EXISTS]>>
      drule make_init_opt_imp_bitmaps_limit>>simp[]>>
      ntac 4 strip_tac>>
      imp_res_tac ALOOKUP_MEM>>
      `MEM k (MAP FST p6) ∧ MEM prog' (MAP SND p6)` by
        metis_tac[MEM_MAP,FST,SND]>>
      qpat_x_assum`MAP FST p6 = _` SUBST_ALL_TAC>>
      fs[EVERY_MEM]
      >-
        (qpat_x_assum`MEM k _` mp_tac>>
        EVAL_TAC>>
        rpt(pop_assum kall_tac)>>
        DECIDE_TAC)
      >>
        first_x_assum drule>>
        EVAL_TAC>>
        fs[])>>
    qhdtm_x_assum`(~)`mp_tac \\
    simp[full_init_pre_fail_def] ) \\
  fs[Abbr`word_st`] \\ rfs[] \\
  match_mp_tac (GEN_ALL (MP_CANON implements_trans)) \\
  qmatch_assum_abbrev_tac`z InitGlobals_location ∈ _ {_}` \\
  qexists_tac`{z InitGlobals_location}` \\
  conj_tac >- (
    match_mp_tac (GEN_ALL(MP_CANON implements_intro_ext)) \\
    simp[] ) \\
  simp[Abbr`z`] \\
  (word_to_stackProofTheory.compile_semantics
   |> Q.GENL[`t`,`code`,`asm_conf`,`start`]
   |> Q.ISPECL_THEN[`stack_st`,`p5`,`c.lab_conf.asm_conf`,`InitGlobals_location`]mp_tac) \\
  impl_tac >- (
    fs[] \\
    conj_tac >- simp[Abbr`stack_st`,full_make_init_code,Abbr`stack_args`] \\
    conj_tac >- (
      simp[Abbr`stack_st`,Abbr`stack_args`] \\
      match_mp_tac IMP_init_state_ok \\
      fs[mc_conf_ok_def,compiler_config_ok_def] \\
      metis_tac[compile_word_to_stack_bitmaps] ) \\
    conj_tac >- (
      qunabbrev_tac`t_code` \\
      imp_res_tac data_to_word_names \\
      simp[ALOOKUP_NONE] \\
      conj_tac >- EVAL_TAC \\
      strip_tac \\ fs[EVERY_MEM] \\
      res_tac \\ pop_assum mp_tac >> EVAL_TAC) \\
    conj_tac >- (
      simp[Abbr`stack_st`] \\
      drule full_make_init_bitmaps \\
      simp[Abbr`stack_args`] ) \\
    conj_tac >- (
      fs[EVERY_MEM,FORALL_PROD] \\
      metis_tac[] ) \\
    strip_tac \\ fs[] \\
    fs[extend_with_resource_limit_def] ) \\
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
  asm_exists_tac \\ simp[] \\
  simp[Abbr`stack_args`] \\
  match_mp_tac stack_to_labProofTheory.full_make_init_semantics \\
  simp[]);

val _ = export_theory();

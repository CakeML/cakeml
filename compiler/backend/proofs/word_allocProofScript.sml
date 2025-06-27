(*
  Correctness proof for word_alloc
*)
open preamble
     reg_allocTheory reg_allocProofTheory linear_scanTheory linear_scanProofTheory
     wordLangTheory wordSemTheory wordPropsTheory wordConvsTheory word_allocTheory;

val _ = new_theory "word_allocProof";

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = set_grammar_ancestry
  ["wordLang", "wordSem", "wordProps", "word_alloc",
   "reg_alloc", "reg_allocProof", "linear_scan", "linear_scanProof"];
val _ = Parse.bring_to_front_overload"numset_list_insert"
             {Thy="word_alloc",Name="numset_list_insert"};
val _ = Parse.hide"mem";
val _ = temp_delsimps ["fromAList_def", "domain_union"]

(*TODO: Move?*)
Theorem SUBSET_OF_INSERT:
 !s x. s ⊆ x INSERT s
Proof
  srw_tac[][SUBSET_DEF]
QED

Triviality INJ_UNION:
  !f A B.
  INJ f (A ∪ B) UNIV ⇒
  INJ f A UNIV ∧
  INJ f B UNIV
Proof
  srw_tac[][]>>
  metis_tac[INJ_SUBSET,SUBSET_DEF,SUBSET_UNION]
QED

Triviality INJ_less:
  INJ f s' UNIV ∧ s ⊆ s'
  ⇒
  INJ f s UNIV
Proof
  metis_tac[INJ_DEF,SUBSET_DEF]
QED

(* TODO: can we have a global for this *)
Definition hide_def:
  hide x = x
End

Triviality INJ_IMP_IMAGE_DIFF:
  INJ f (s ∪ t) UNIV ⇒
  IMAGE f (s DIFF t) = (IMAGE f s) DIFF (IMAGE f t)
Proof
  rw[EXTENSION,EQ_IMP_THM]>> TRY (metis_tac[])>>
  fs[INJ_DEF]>>
  metis_tac[]
QED

Triviality INJ_IMP_IMAGE_DIFF_single:
  INJ f (s ∪ {n}) UNIV ⇒
  (IMAGE f s) DIFF {f n} = IMAGE f (s DIFF {n})
Proof
  rw[]>>
  `{f n} = IMAGE f {n}` by fs[]>>
  fs[INJ_IMP_IMAGE_DIFF]
QED

Triviality INJ_ALL_DISTINCT_MAP:
  ∀ls.
  ALL_DISTINCT (MAP f ls) ⇒
  INJ f (set ls) UNIV
Proof
  Induct>>full_simp_tac(srw_ss())[INJ_DEF]>>srw_tac[][]>>
  metis_tac[MEM_MAP]
QED

(* word_alloc proofs
  1. correctness theorem about colouring_ok
  2. get_clash_sets (TODO: redundant)
  3. connect check_clash_tree to colouring_ok
  4. word_alloc_correct (connect 1 and 3)
  5. ssa_cc_trans correctness proof (including an invariant property), followed by full_ssa_cc_trans correctness
  6. ssa syntactic things (pre_alloc_conventions, wf_cutsets)
  7. word_alloc syntactic things
  8. misc
 *)

(* colouring_ok correctness proof *)
Definition colouring_ok_def:
  (colouring_ok f (Seq s1 s2) live =
    (*Normal live sets*)
    let s2_live = get_live s2 live in
    let s1_live = get_live s1 s2_live in
      INJ f (domain s1_live) UNIV ∧
      (*Internal clash sets*)
      colouring_ok f s2 live ∧ colouring_ok f s1 s2_live) ∧
  (colouring_ok f (If cmp r1 ri e2 e3) live =
    let e2_live = get_live e2 live in
    let e3_live = get_live e3 live in
    let union_live = union e2_live e3_live in
    let merged = case ri of Reg r2 => insert r2 () (insert r1 () union_live)
                      | _ => insert r1 () union_live in
    (*All of them must be live at once*)
      INJ f (domain merged) UNIV ∧
      (*Internal clash sets*)
      colouring_ok f e2 live ∧ colouring_ok f e3 live) ∧
  (colouring_ok f (Call(SOME(v,cutset,ret_handler,l1,l2))dest args h) live =
    let args_set = numset_list_insert args LN in
    let all_names = union (SND cutset) (FST cutset) in
    INJ f (domain (union all_names args_set)) UNIV ∧
    INJ f (domain (numset_list_insert v all_names )) UNIV ∧
    (*returning handler*)
    colouring_ok f ret_handler live ∧
    (*exception handler*)
    (case h of
    | NONE => T
    | SOME(v,prog,l1,l2) =>
        INJ f (domain (insert v () all_names)) UNIV ∧
        colouring_ok f prog live)) ∧
  (colouring_ok f (MustTerminate p) live =
    colouring_ok f p live) ∧
  (colouring_ok f prog live =
    (*live before must be fine, and clash set must be fine*)
    let lset = get_live prog live in
    let iset = union (get_writes prog) live in
      INJ f (domain lset) UNIV ∧ INJ f (domain iset) UNIV)
End

(*Equivalence on everything except permutation and locals*)
(* should we add local_size here? may be no, as locals are not included *)
(*TODO this definition is bad for automation remove it with
t = s with (...)*)
Definition word_state_eq_rel_def:
  word_state_eq_rel (s:('a,'c,'ffi) wordSem$state) (t:('a,'c,'ffi) wordSem$state) ⇔
  t.fp_regs = s.fp_regs ∧
  t.store = s.store ∧
  t.locals_size = s.locals_size /\
  t.stack = s.stack ∧
  t.stack_limit = s.stack_limit /\
  t.stack_max = s.stack_max /\
  t.stack_size = s.stack_size /\
  t.memory = s.memory ∧
  t.mdomain = s.mdomain ∧
  t.sh_mdomain = s.sh_mdomain ∧
  t.gc_fun = s.gc_fun ∧
  t.handler = s.handler ∧
  t.clock = s.clock ∧
  t.code = s.code ∧
  t.ffi = s.ffi ∧
  t.be = s.be ∧
  t.termdep = s.termdep ∧
  t.compile = s.compile ∧
  t.compile_oracle = s.compile_oracle ∧
  t.code_buffer = s.code_buffer ∧
  t.data_buffer = s.data_buffer
End


(*tlocs is a supermap of slocs under f for everything in a given
  live set*)

Definition strong_locals_rel_def:
  strong_locals_rel f ls slocs tlocs ⇔
  ∀n v.
    n ∈ ls ∧ lookup n slocs = SOME v ⇒
    lookup (f n) tlocs = SOME v
End

Theorem domain_numset_list_insert:
    ∀ls locs.
  domain (numset_list_insert ls locs) = domain locs UNION set ls
Proof
  Induct>>full_simp_tac(srw_ss())[numset_list_insert_def]>>srw_tac[][]>>
  metis_tac[INSERT_UNION_EQ,UNION_COMM]
QED

Triviality strong_locals_rel_get_var:
  strong_locals_rel f live st.locals cst.locals ∧
  n ∈ live ∧
  get_var n st = SOME x
  ⇒
  get_var (f n) cst = SOME x
Proof
  full_simp_tac(srw_ss())[get_var_def,strong_locals_rel_def]
QED

Triviality strong_locals_rel_get_var_imm:
  strong_locals_rel f live st.locals cst.locals ∧
  (case n of Reg n => n ∈ live | _ => T) ∧
  get_var_imm n st = SOME x
  ⇒
  get_var_imm (apply_colour_imm f n) cst = SOME x
Proof
  Cases_on`n`>>full_simp_tac(srw_ss())[get_var_imm_def]>>
  metis_tac[strong_locals_rel_get_var]
QED

Triviality strong_locals_rel_get_vars:
  ∀ls y f live st cst.
  strong_locals_rel f live st.locals cst.locals ∧
  (∀x. MEM x ls ⇒ x ∈ live) ∧
  get_vars ls st = SOME y
  ⇒
  get_vars (MAP f ls) cst = SOME y
Proof
  Induct>>full_simp_tac(srw_ss())[get_vars_def]>>srw_tac[][]>>
  Cases_on`get_var h st`>>full_simp_tac(srw_ss())[]>>
  `h ∈ live` by full_simp_tac(srw_ss())[]>>
  imp_res_tac strong_locals_rel_get_var>>full_simp_tac(srw_ss())[]>>
  Cases_on`get_vars ls st`>>full_simp_tac(srw_ss())[]>>
  res_tac>>
  pop_assum(qspec_then`live` mp_tac)>>impl_tac
  >-metis_tac[]>>
  full_simp_tac(srw_ss())[]
QED

Triviality domain_big_union_subset:
  !ls a.
  MEM a ls ⇒
  domain (get_live_exp a) ⊆
  domain (big_union (MAP get_live_exp ls))
Proof
  Induct>>rw[]>>fs[big_union_def,domain_union,SUBSET_UNION,SUBSET_DEF]>>
  metis_tac[]
QED

val size_tac= (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC);

Triviality apply_nummap_key_domain:
  ∀f names.
  domain (apply_nummap_key f names) =
  IMAGE f (domain names)
Proof
  full_simp_tac(srw_ss())[domain_def,domain_fromAList]>>
  full_simp_tac(srw_ss())[MEM_MAP,MAP_MAP_o,EXTENSION,EXISTS_PROD]>>
  metis_tac[MEM_toAList,domain_lookup]
QED


Theorem cut_names_lemma:
    ∀names sloc tloc x f.
  INJ f (domain names) UNIV ∧
  cut_names names sloc = SOME x ∧
  strong_locals_rel f (domain names) sloc tloc
  ⇒
  ∃y. cut_names (apply_nummap_key f names) tloc = SOME y ∧
      domain y = IMAGE f (domain x) ∧
      strong_locals_rel f (domain names) x y ∧
      INJ f (domain x) UNIV ∧
      domain x = domain names
Proof
  rpt strip_tac>>
  full_simp_tac(srw_ss())[domain_inter,cut_names_def,apply_nummap_key_domain
    ,strong_locals_rel_def]>>
  full_simp_tac (bool_ss)[GSYM apply_nummap_key_def] >>
  CONJ_ASM1_TAC>-
    (full_simp_tac(srw_ss())[SUBSET_DEF,domain_lookup]>>srw_tac[][]>>metis_tac[])>>
  CONJ_ASM1_TAC>-
    (Q.ISPECL_THEN[`f`,`names`] assume_tac apply_nummap_key_domain>>
    rveq >>
    full_simp_tac(srw_ss())[SUBSET_INTER_ABSORPTION,INTER_COMM,apply_nummap_key_def]
    )>>
  srw_tac[][]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[lookup_inter]>>
    Cases_on`lookup n sloc`>>full_simp_tac(srw_ss())[]>>
    Cases_on`lookup n names`>>full_simp_tac(srw_ss())[]>>
    res_tac>>
    imp_res_tac MEM_toAList>>
    full_simp_tac(srw_ss())[lookup_fromAList]>>
    EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[ALOOKUP_NONE,MEM_MAP,FORALL_PROD]>>metis_tac[])
  >>
    full_simp_tac(srw_ss())[domain_inter,SUBSET_INTER_ABSORPTION,INTER_COMM]
QED

Triviality nummaps_to_nummap:
   FST (apply_nummaps_key f a) = apply_nummap_key f (FST a) /\
   SND (apply_nummaps_key f a) = apply_nummap_key f (SND a)
Proof
   fs[apply_nummaps_key_def,apply_nummap_key_def]
QED

Theorem INJ_union:
    INJ f (A ∪ B) C ==> INJ f A C /\ INJ f B C
Proof
   disch_tac >> fs[INJ_DEF]
QED

Theorem strong_locals_rel_UNION:
    strong_locals_rel f (A ∪ B) t l <=> strong_locals_rel f A t l /\ strong_locals_rel f B t l
Proof
   EQ_TAC >> DISCH_TAC >> fs[strong_locals_rel_def] >>
   rpt strip_tac >> fs[]
QED


Triviality LENGTH_list_rerrange:
  LENGTH (list_rearrange mover xs) = LENGTH xs
Proof
  full_simp_tac(srw_ss())[list_rearrange_def]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]
QED

(*For any 2 lists that are permutations of each other,
  We can give a list_rearranger that permutes one to the other*)
Triviality list_rearrange_perm:
  PERM xs ys
  ⇒
  ∃perm. list_rearrange perm xs = ys
Proof
  srw_tac[][]>>
  imp_res_tac PERM_BIJ>>full_simp_tac(srw_ss())[list_rearrange_def]>>
  qexists_tac`f`>>
  IF_CASES_TAC>>
  full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF]>>metis_tac[]
QED

Triviality GENLIST_MAP:
  !k. (!i. i < LENGTH l ==> m i < LENGTH l) /\ k <= LENGTH l ==>
        GENLIST (\i. EL (m i) (MAP f l)) k =
        MAP f (GENLIST (\i. EL (m i) l) k)
Proof
  Induct \\ full_simp_tac(srw_ss())[GENLIST] \\ REPEAT STRIP_TAC
  \\ `k < LENGTH l /\ k <= LENGTH l` by DECIDE_TAC
  \\ full_simp_tac(srw_ss())[EL_MAP,SNOC_APPEND]
QED

Theorem list_rearrange_MAP:
   !l f m. list_rearrange m (MAP f l) = MAP f (list_rearrange m l)
Proof
  SRW_TAC [] [list_rearrange_def] \\ MATCH_MP_TAC GENLIST_MAP \\
  full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF]
QED

val ALL_DISTINCT_FST = ALL_DISTINCT_MAP |> Q.ISPEC `FST`

(*Main theorem for permute oracle usage!
  This shows that we can push locals that are exactly matching using
  any desired permutation
  and we can choose the final permutation to be anything we want
  (In Alloc we choose it to be cst.permute, in Call something
   given by the IH)
*)

Triviality env_to_list_perm:
  ∀y x f perm  tperm.
  domain y = IMAGE f (domain x) ∧
  INJ f (domain x) UNIV ∧
  strong_locals_rel f (domain x) x y
  ⇒
  let (l,permute) = env_to_list y perm in
  ∃perm'.
    let(l',permute') = env_to_list x perm' in
      permute' = tperm ∧ (*Just change the first permute*)
      MAP (λx,y.f x,y) l' = l
Proof
  srw_tac[][]>>
  full_simp_tac(srw_ss())[env_to_list_def,LET_THM,strong_locals_rel_def]>>
  qabbrev_tac `xls = QSORT key_val_compare (toAList x)`>>
  qabbrev_tac `yls = QSORT key_val_compare (toAList y)`>>
  qabbrev_tac `ls = list_rearrange (perm 0) yls`>>
  full_simp_tac(srw_ss())[(GEN_ALL o SYM o SPEC_ALL) list_rearrange_MAP]>>
  `PERM (MAP (λx,y.f x,y) xls) yls` by
    (match_mp_tac PERM_ALL_DISTINCT >>srw_tac[][]
    >-
      (match_mp_tac ALL_DISTINCT_MAP_INJ>>srw_tac[][]
      >-
        (full_simp_tac(srw_ss())[INJ_DEF,Abbr`xls`,QSORT_MEM]>>
        Cases_on`x'`>>Cases_on`y'`>>full_simp_tac(srw_ss())[]>>
        imp_res_tac MEM_toAList>>
        full_simp_tac(srw_ss())[domain_lookup])
      >>
      full_simp_tac(srw_ss())[Abbr`xls`]>>
      metis_tac[QSORT_PERM,ALL_DISTINCT_MAP_FST_toAList
               ,ALL_DISTINCT_FST,ALL_DISTINCT_PERM])
    >-
      metis_tac[QSORT_PERM,ALL_DISTINCT_MAP_FST_toAList
               ,ALL_DISTINCT_FST,ALL_DISTINCT_PERM]
    >>
      unabbrev_all_tac>>
      full_simp_tac(srw_ss())[QSORT_MEM,MEM_MAP]>>
      full_simp_tac(srw_ss())[EQ_IMP_THM]>>srw_tac[][]
      >-
        (Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList]>>metis_tac[domain_lookup])
      >>
        Cases_on`x'`>>full_simp_tac(srw_ss())[MEM_toAList]>>
        imp_res_tac domain_lookup>>
        full_simp_tac(srw_ss())[EXTENSION]>>res_tac>>
        qexists_tac`x',r`>>full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[MEM_toAList,domain_lookup]>>
        first_x_assum(qspecl_then[`x'`,`v'`] assume_tac)>>rev_full_simp_tac(srw_ss())[])
  >>
  `PERM yls ls` by
    (full_simp_tac(srw_ss())[list_rearrange_def,Abbr`ls`]>>
    qpat_x_assum`A=l` (SUBST1_TAC o SYM)>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
    match_mp_tac PERM_ALL_DISTINCT>>
    CONJ_ASM1_TAC>-
      metis_tac[QSORT_PERM,ALL_DISTINCT_MAP_FST_toAList
               ,ALL_DISTINCT_FST,ALL_DISTINCT_PERM]>>
    CONJ_ASM1_TAC>-
      (full_simp_tac(srw_ss())[ALL_DISTINCT_GENLIST]>>srw_tac[][]>>
      full_simp_tac(srw_ss())[EL_ALL_DISTINCT_EL_EQ]>>
      `perm 0 i = perm 0 i'` by
        (full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF]>>
        metis_tac[])>>
      full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF])
    >>
      full_simp_tac(srw_ss())[MEM_GENLIST,BIJ_DEF,INJ_DEF,SURJ_DEF]>>
      full_simp_tac(srw_ss())[MEM_EL]>>metis_tac[])>>
  imp_res_tac PERM_TRANS>>
  imp_res_tac list_rearrange_perm>>
  qexists_tac`λn. if n = 0:num then perm' else tperm (n-1)`>>
  full_simp_tac(srw_ss())[FUN_EQ_THM]
QED

(*Proves s_val_eq and some extra conditions on the resulting lists*)
Theorem push_env_s_val_eq:
    ∀tperm.
  st.handler = cst.handler ∧
  st.stack = cst.stack ∧
  st.locals_size = cst.locals_size /\
  domain y = IMAGE f (domain x) ∧
  INJ f (domain x) UNIV ∧
  strong_locals_rel f (domain x) x y ∧
  (case b of NONE => b' = NONE
         |  SOME(w,h,l1,l2) =>
            (case b' of NONE => F
            |  SOME(a,b,c,d) => c = l1 ∧ d = l2))
  ⇒
  ?perm.
  (let (l,permute) = env_to_list y cst.permute in
  let(l',permute') = env_to_list x perm in
      permute' = tperm ∧
      MAP (λx,y.f x,y) l' = l ∧
      (∀x y. MEM x (MAP FST l') ∧ MEM y (MAP FST l')
        ∧ f x = f y ⇒ x = y) ) ∧
  s_val_eq (push_env (l0,x) b (st with permute:=perm)).stack
           (push_env (l0,y) b' cst).stack
Proof
  srw_tac[][]>>Cases_on`b`>>
  TRY(PairCases_on`x'`>> Cases_on`b'`>>full_simp_tac(srw_ss())[]>>PairCases_on`x'`>>full_simp_tac(srw_ss())[])>>
  (fs[push_env_def]>>
  imp_res_tac env_to_list_perm>>
  pop_assum(qspecl_then[`tperm`,`cst.permute`]assume_tac)>>full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`env_to_list y cst.permute`>>
  fs[]>>
  qexists_tac`perm'`>>
  Cases_on`env_to_list x perm'`>>
  fs[env_to_list_def,LET_THM]>>
  fs[s_val_eq_def,s_val_eq_refl]>>
  srw_tac[][]>-
    (full_simp_tac(srw_ss())[INJ_DEF,MEM_MAP]>>
    imp_res_tac mem_list_rearrange>>
    full_simp_tac(srw_ss())[QSORT_MEM]>>
    Cases_on`y'''`>>Cases_on`y''`>>full_simp_tac(srw_ss())[MEM_toAList]>>
    metis_tac[domain_lookup])>>
  fs[s_frame_val_eq_def]>>
  qpat_abbrev_tac `q = list_rearrange A
    (QSORT key_val_compare (toAList x))`>>
  `MAP SND (MAP (λx,y.f x,y) q) = MAP SND q` by
    (fs[MAP_MAP_o]>>AP_THM_TAC>>AP_TERM_TAC>>fs[FUN_EQ_THM]>>
    srw_tac[][]>>Cases_on`x'`>>fs[])>>
  metis_tac[])
QED

(*TODO: Maybe move to props?
gc doesn't touch other components*)
Theorem gc_frame:
    gc st = SOME st'
  ⇒
  st'.fp_regs = st.fp_regs ∧
  st'.mdomain = st.mdomain ∧
  st'.sh_mdomain = st.sh_mdomain ∧
  st'.gc_fun = st.gc_fun ∧
  st'.handler = st.handler ∧
  st'.clock = st.clock ∧
  st'.code = st.code ∧
  st'.locals = st.locals ∧
  st'.locals_size = st.locals_size /\
  st'.stack_size = st.stack_size /\
  st'.stack_max = st.stack_max /\
  st'.stack_limit = st.stack_limit /\
  st'.be = st.be ∧
  st'.ffi = st.ffi ∧
  st'.compile = st.compile ∧
  st'.compile_oracle = st.compile_oracle ∧
  st'.code_buffer = st.code_buffer ∧
  st'.data_buffer = st.data_buffer ∧
  st'.permute = st.permute ∧
  st'.termdep = st.termdep
Proof
  full_simp_tac(srw_ss())[gc_def,LET_THM]>>EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[state_component_equality]
QED

(*Convenient rewrite for pop_env*)
(*
Theorem s_key_eq_val_eq_pop_env:
    pop_env s = SOME s' ∧
  s_key_eq s.stack ((StackFrame lsz ls opt)::keys) ∧
  s_val_eq s.stack vals
  ⇒
  ∃lsz' ls' rest.
  vals = StackFrame lsz' ls' opt :: rest ∧
  s'.locals = fromAList (ZIP (MAP FST ls,MAP SND ls')) ∧
  s_key_eq s'.stack keys ∧
  s_val_eq s'.stack rest ∧
  case opt of NONE => s'.handler = s.handler
            | SOME (h,l1,l2) => s'.handler = h
Proof
  strip_tac>>
  full_simp_tac(srw_ss())[pop_env_def]>>
  EVERY_CASE_TAC>>
  Cases_on`vals`>>
  full_simp_tac(srw_ss())[s_val_eq_def,s_key_eq_def]>>
  Cases_on`h`>>rename1 `StackFrame _ l' excp` >> Cases_on`excp`>>
  full_simp_tac(srw_ss())[s_frame_key_eq_def,s_frame_val_eq_def]>>
  full_simp_tac(srw_ss())[state_component_equality]>>
  metis_tac[ZIP_MAP_FST_SND_EQ]
QED
*)
(*Less powerful form*)
Theorem ALOOKUP_key_remap_2:
    ∀ls vals f.
    (∀x y. MEM x ls ∧ MEM y ls ∧ f x = f y ⇒ x = y) ∧
    LENGTH ls = LENGTH vals ∧
    ALOOKUP (ZIP (ls,vals)) n = SOME v
    ⇒
    ALOOKUP (ZIP (MAP f ls,vals)) (f n) = SOME v
Proof
  Induct>>srw_tac[][]>>
  Cases_on`vals`>>full_simp_tac(srw_ss())[]>>
  Cases_on`h=n`>>full_simp_tac(srw_ss())[]>>
  `MEM n ls` by
    (imp_res_tac ALOOKUP_MEM>>
    imp_res_tac MEM_ZIP>>
    full_simp_tac(srw_ss())[]>>
    metis_tac[MEM_EL])>>
  first_assum(qspecl_then[`h`,`n`] assume_tac)>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]
QED

val lookup_alist_insert = sptreeTheory.lookup_alist_insert |> INST_TYPE [alpha|->``:'a word_loc``]

Triviality strong_locals_rel_subset:
  s ⊆ s' ∧
  strong_locals_rel f s' stl cstl
  ⇒
  strong_locals_rel f s stl cstl
Proof
  srw_tac[][strong_locals_rel_def]>>
  metis_tac[SUBSET_DEF]
QED

Triviality env_to_list_keys:
  let (l,permute) = env_to_list x perm in
  set (MAP FST l) = domain x
Proof
  full_simp_tac(srw_ss())[LET_THM,env_to_list_def,EXTENSION,MEM_MAP,EXISTS_PROD]>>
  srw_tac[][EQ_IMP_THM]
  >-
    (imp_res_tac mem_list_rearrange>>
    full_simp_tac(srw_ss())[QSORT_MEM,MEM_toAList,domain_lookup])
  >>
    full_simp_tac(srw_ss())[mem_list_rearrange,QSORT_MEM,MEM_toAList,domain_lookup]
QED

Theorem list_rearrange_keys:
    list_rearrange perm (ls:('a,'b) alist) = e ⇒
  set(MAP FST e) = set(MAP FST ls)
Proof
  rw[]>>fs[EXTENSION]>>
  metis_tac[MEM_toAList,mem_list_rearrange,MEM_MAP]
QED

Theorem pop_env_frame:
   s_val_eq r'.stack st' ∧
    s_key_eq y'.stack y''.stack ∧
    pop_env (r' with stack:= st') = SOME y'' ∧
    pop_env r' = SOME y'
    ⇒
    word_state_eq_rel y' y''
Proof
    full_simp_tac(srw_ss())[pop_env_def]>>EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[s_val_eq_def,s_frame_val_eq_def,word_state_eq_rel_def
      ,state_component_equality]>>
    srw_tac[][]>>rev_full_simp_tac(srw_ss())[]>>
    metis_tac[s_val_and_key_eq]
QED

Theorem key_map_implies:
  MAP (λx,y.f x,y) l' = l
 ⇒ MAP f (MAP FST l') = MAP FST l
Proof
 srw_tac[][]>>match_mp_tac LIST_EQ>>
 srw_tac[][EL_MAP]>>
 Cases_on`EL x l'`>>full_simp_tac(srw_ss())[]
QED

(*Main proof of liveness theorem starts here*)
(*
 (* rm later *)
Theorem stack_size_map_excp_const:
  stack_size (StackFrame lsz lmp excp :: st.stack) =
    stack_size (StackFrame lsz lmp' excp' :: st.stack)
Proof
  rw [stack_size_def]
QED
*)

Triviality apply_colour_exp_lemma:
  ∀st w cst f res.
    word_exp st w = SOME res ∧
    word_state_eq_rel st cst ∧
    strong_locals_rel f (domain (get_live_exp w)) st.locals cst.locals
    ⇒
    word_exp cst (apply_colour_exp f w) = SOME res
Proof
  ho_match_mp_tac word_exp_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[word_exp_def,apply_colour_exp_def,strong_locals_rel_def,get_live_exp_def,word_state_eq_rel_def]
  >- gvs[get_var_def]
  >- gvs[get_store_def]
  >-
    (Cases_on`word_exp st w`>>full_simp_tac(srw_ss())[]>>
    FULL_CASE_TAC>>fs[]>>
    qsuff_tac`mem_load c st = mem_load c cst`>>fs[mem_load_def])
  >-
    (qpat_x_assum`A=SOME res` mp_tac>>TOP_CASE_TAC>>rw[]>>
    `MAP (\a.word_exp st a) wexps =
     MAP (\a.word_exp cst a) (MAP (\a. apply_colour_exp f a) wexps)` by
      (imp_res_tac the_words_EVERY_IS_SOME>>
      fs[MAP_MAP_o,MAP_EQ_f]>>
      fs[EVERY_MAP,EVERY_MEM]>>
      rw[]>>
      rpt(first_x_assum(qspec_then`a` mp_tac))>>
      rw[IS_SOME_EXISTS]>>
      simp[Once EQ_SYM_EQ]>>
      first_assum match_mp_tac>>
      fs[]>>
      imp_res_tac domain_big_union_subset>>
      metis_tac[SUBSET_DEF])>>
    fs[])
  >>
    qpat_x_assum`A=SOME res`mp_tac>>TOP_CASE_TAC>>rw[]>>
    fs[]
QED

Theorem strong_locals_rel_insert:
     INJ f (n INSERT l) UNIV /\
  strong_locals_rel f (l DELETE n) st cst ⇒
  strong_locals_rel f l (insert n v st) (insert (f n) v cst)
Proof
  rw[strong_locals_rel_def]>>fs[lookup_insert]>>
  Cases_on`n'=n`>>fs[]>>
  IF_CASES_TAC>>
  fs[INJ_DEF]>>
  metis_tac[domain_lookup]
QED

(*Frequently used tactics*)
val exists_tac = qexists_tac`cst.permute`>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def
      ,get_live_def,colouring_ok_def];

val exists_tac_2 =
    Cases_on`word_exp st e`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac apply_colour_exp_lemma>>
    pop_assum (qspecl_then[`f`,`cst`] mp_tac)>>
    impl_tac
    >-
      metis_tac[SUBSET_OF_INSERT,domain_union,SUBSET_UNION
               ,strong_locals_rel_subset];

val setup_tac = Cases_on`word_exp st expr`>>full_simp_tac(srw_ss())[]>>
      imp_res_tac apply_colour_exp_lemma>>
      pop_assum(qspecl_then[`f`,`cst`]mp_tac)>>unabbrev_all_tac;

Triviality LASTN_LENGTH2:
  LASTN (LENGTH xs +1) (x::xs) = x::xs
Proof
  `LENGTH (x::xs) = LENGTH xs +1` by simp[]>>
  metis_tac[LASTN_LENGTH_ID]
QED

Triviality toAList_not_empty:
  domain t ≠ {} ⇒
  toAList t ≠ []
Proof
  CCONTR_TAC>>full_simp_tac(srw_ss())[GSYM MEMBER_NOT_EMPTY]>>
  full_simp_tac(srw_ss())[GSYM toAList_domain]
QED

(*liveness theorem*)
Theorem evaluate_apply_colour:
  ∀prog st cst f live.
  colouring_ok f prog live ∧
  word_state_eq_rel (st:('a,'c,'ffi) wordSem$state) cst ∧
  strong_locals_rel f (domain (get_live prog live)) st.locals cst.locals
  ⇒
  ∃perm'.
  let (res,rst) = evaluate(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (res',rcst) = evaluate(apply_colour f prog,cst) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    (case res of
      NONE => strong_locals_rel f (domain live)
              rst.locals rcst.locals
    | SOME _ => rst.locals = rcst.locals )
Proof
  (*The cheats here require cut_{env,envs}_lemma to be fixed*)
  (*Induct on size of program*)
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >- (*Skip*)
    gvs[evaluate_def,get_live_def,word_state_eq_rel_def]
  >- (*Move*) (
    gvs[evaluate_def,get_live_def,colouring_ok_def] >>
    full_simp_tac(srw_ss())[MAP_ZIP,get_writes_def,domain_union,domain_numset_list_insert]>>
    Cases_on`ALL_DISTINCT (MAP FST l)`>>full_simp_tac(srw_ss())[]>>
    `ALL_DISTINCT (MAP f (MAP FST l))` by
      (match_mp_tac ALL_DISTINCT_MAP_INJ>>
      srw_tac[][]>>
      FULL_SIMP_TAC bool_ss [INJ_DEF]>>
      first_x_assum(qspecl_then[`x`,`y`] assume_tac)>>
      simp[])>>
    full_simp_tac(srw_ss())[MAP_MAP_o] >>
    Cases_on`get_vars (MAP SND l) st`>>full_simp_tac(srw_ss())[]>>
    `get_vars (MAP f (MAP SND l)) cst = SOME x` by
      (
      drule strong_locals_rel_get_vars>>
      disch_then (qspec_then `(MAP SND l)` mp_tac) >>
      simp[]) >>
    full_simp_tac(srw_ss())[MAP_MAP_o] >>
    fs[word_state_eq_rel_def] >>
    `LENGTH l = LENGTH x` by
      (imp_res_tac get_vars_length_lemma >>
      fs[LENGTH_MAP]) >>
    fs[strong_locals_rel_def,set_vars_def,lookup_alist_insert] >>
    rpt strip_tac >>
    Cases_on`ALOOKUP (ZIP (MAP FST l,x)) n'`>>full_simp_tac(srw_ss())[]
    (*NONE:
      Therefore n is not in l but it is in live and so it is not deleted
     *)
    >-(
       `n' ∈ domain (FOLDR delete live (MAP FST l))` by
        (full_simp_tac(srw_ss())[domain_FOLDR_delete]>>
        full_simp_tac(srw_ss())[ALOOKUP_NONE]>>rev_full_simp_tac(srw_ss())[MAP_ZIP])>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
        imp_res_tac ALOOKUP_MEM>>
        pop_assum mp_tac>>
        full_simp_tac(srw_ss())[MEM_ZIP]>>strip_tac>>
        rev_full_simp_tac(srw_ss())[EL_MAP,ALOOKUP_NONE]>>
        rev_full_simp_tac(srw_ss())[MAP_ZIP]>>
        `n' = FST (EL n'' l)` by
        (FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        first_assum(qspecl_then[`n'`,`FST (EL n'' l)`] mp_tac)>>
        impl_tac>-
          (srw_tac[][]>>DISJ1_TAC>>
          metis_tac[MEM_MAP,MEM_EL])>>
        metis_tac[])>> fs[] >>
        metis_tac[MEM_EL,MEM_MAP])
    >>
      drule_all_then assume_tac ALOOKUP_MEM >>
      `ALOOKUP (ZIP (MAP (f o FST) l ,x)) (f n') = SOME v` by
        (match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
        pop_assum mp_tac>>
        full_simp_tac(srw_ss())[MAP_ZIP,MEM_ZIP,LENGTH_MAP]>>strip_tac>>full_simp_tac(srw_ss())[]>>
        fs[EL_MAP] >> HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[EL_MAP]) >>
     full_simp_tac(srw_ss())[])
  >- (*Inst*)
    (exists_tac>>
    Cases_on`i`>> (TRY (Cases_on`a`))>> (TRY(Cases_on`m`))>>
    full_simp_tac(srw_ss())[get_live_def,get_live_inst_def,inst_def,assign_def]
    >-
      (Cases_on`word_exp st (Const c)`>>
      fs[word_exp_def,set_var_def,domain_union,get_writes_def,get_writes_inst_def]>>
      match_mp_tac strong_locals_rel_insert>>
      metis_tac[INSERT_SING_UNION])
    >-
      (Cases_on`r`>>full_simp_tac(srw_ss())[]>>
      qpat_abbrev_tac `expr = (Op b [Var n0;B])`>>
      setup_tac>>
      (impl_tac
      >-
        (full_simp_tac(srw_ss())[get_live_exp_def,domain_union,big_union_def]>>
        `{n0} ⊆ (n0 INSERT domain live DELETE n)` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
        TRY(`{n0} ∪ {n'} ⊆ (n0 INSERT n' INSERT domain live DELETE n)` by
          full_simp_tac(srw_ss())[SUBSET_DEF])>>
        metis_tac[strong_locals_rel_subset])
      >>
      fs[apply_colour_exp_def,word_state_eq_rel_def,set_var_def,get_writes_def
        ,get_writes_inst_def,domain_union]>>
      strip_tac>> match_mp_tac strong_locals_rel_insert>>
      metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT]))
    >-
      (qpat_abbrev_tac`expr = (Shift s (Var n0) B)`>>
      setup_tac>>
      impl_tac>-
        (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
        `{n0} ⊆ n0 INSERT domain live DELETE n` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
        metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset])>>
      pairarg_tac>>
      fs[word_exp_def,word_state_eq_rel_def,set_var_def]>> strip_tac>>
      match_mp_tac strong_locals_rel_insert>>
      fs[domain_union,get_writes_def,get_writes_inst_def]>>
      metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT])
    >>
    TRY (
      fs[]>>
      qmatch_goalsub_abbrev_tac `get_vars ls st`>>
      Cases_on`get_vars ls st`>>fs[Abbr`ls`]>>
      imp_res_tac strong_locals_rel_get_vars>>fs[]>>
      pop_assum kall_tac>> pop_assum mp_tac>>
      impl_tac>-
        metis_tac[]>>
      fs[]>>
      qmatch_asmsub_abbrev_tac `INJ f (domain A)`>>
      `!n n'. n ∈ domain A ∧
              n' ∈ domain A ∧ n ≠ n' ⇒ f n ≠ f n'` by
        (fs[get_writes_def,get_writes_inst_def,Abbr`A`]>>
        qpat_x_assum`INJ f A B` mp_tac>>
        rpt (pop_assum kall_tac)>>rw[]>>
        FULL_SIMP_TAC bool_ss [INJ_DEF,domain_union,get_writes_def,get_writes_inst_def,domain_insert,IN_UNION]>>
        metis_tac[IN_INSERT])>>
      fs[get_writes_def,get_writes_inst_def,Abbr`A`,domain_union]>>
      every_case_tac>>fs[set_var_def,strong_locals_rel_def,lookup_insert]>>
      rw[]>>
      pop_assum mp_tac>>
      rpt IF_CASES_TAC>>fs[]>>
      metis_tac[])
    >-
      (qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      impl_tac>-
        (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
        `{n'} ⊆ n' INSERT domain live DELETE n` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
        metis_tac[strong_locals_rel_subset])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
      Cases_on`x`>>simp[]>>
      fs[mem_load_def]>>
      IF_CASES_TAC>>fs[]>>
      fs[domain_union,get_writes_def,get_writes_inst_def]>>
      metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT,strong_locals_rel_insert])
    >-
      (qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      impl_tac>-
        (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
        `{n'} ⊆ n' INSERT domain live DELETE n` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
        metis_tac[strong_locals_rel_subset])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
      Cases_on`x`>>simp[]>>
      fs[mem_load_byte_aux_def]>>
      Cases_on`st.memory (byte_align c')`>>fs[]>>
      IF_CASES_TAC>>
      fs[domain_union,get_writes_def,get_writes_inst_def]>>
      metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT,strong_locals_rel_insert])
    >-
      (qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      impl_tac>-
        (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
        `{n'} ⊆ n' INSERT domain live DELETE n` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
        metis_tac[strong_locals_rel_subset])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
      Cases_on`x`>>simp[]>>
      fs[mem_load_32_def]>>
      Cases_on`st.memory (byte_align c')`>>fs[]>>
      ntac 2 (IF_CASES_TAC>>fs[]) >> gvs[] >>
      fs[domain_union,get_writes_def,get_writes_inst_def]>>
      metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT,strong_locals_rel_insert])
    >-
      (qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      setup_tac>>
      impl_tac>-
        (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
        `{n'} ⊆ n' INSERT n INSERT domain live` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
        metis_tac[strong_locals_rel_subset])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
      Cases_on`x`>>simp[]>>
      srw_tac[][]>>
      Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
      imp_res_tac strong_locals_rel_get_var>>
      Cases_on`mem_store c x' st`>>fs[mem_store_def]>>IF_CASES_TAC>>fs[]>>
      metis_tac[strong_locals_rel_subset,SUBSET_OF_INSERT])
    >-
      (qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      setup_tac>>
      impl_tac>-
        (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
        `{n'} ⊆ n' INSERT n INSERT domain live` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
        metis_tac[strong_locals_rel_subset])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
      Cases_on`x`>>simp[]>>
      srw_tac[][]>>
      Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
      imp_res_tac strong_locals_rel_get_var>>
      fs[]>>
      Cases_on`x`>>fs[]>>
      FULL_CASE_TAC>>fs[strong_locals_rel_def])
    >-
      (qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      setup_tac>>
      impl_tac>-
        (full_simp_tac(srw_ss())[get_live_exp_def,big_union_def]>>
        `{n'} ⊆ n' INSERT n INSERT domain live` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
        metis_tac[strong_locals_rel_subset])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def,LET_THM,set_var_def]>>
      Cases_on`x`>>simp[]>>
      srw_tac[][]>>
      Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
      imp_res_tac strong_locals_rel_get_var>>
      fs[]>>
      Cases_on`x`>>fs[]>>
      FULL_CASE_TAC>>fs[strong_locals_rel_def])
    >-
      (* All the FP cases *)
      (Cases_on`f'`>>fs[get_fp_var_def]>>
      every_case_tac>>simp[set_var_def]>>
      imp_res_tac strong_locals_rel_get_var>>
      fs[get_live_inst_def,get_writes_inst_def,get_writes_def,set_fp_var_def]>>
      fs[domain_union]>>
      rw[]>>
      TRY(
        rename1`INJ f ({n0;n} ∪ li) UNIV`>>
        match_mp_tac strong_locals_rel_insert>>
        CONJ_TAC>-
          (drule INJ_SUBSET>>
          disch_then match_mp_tac >>fs[])>>
        match_mp_tac strong_locals_rel_insert>>
        CONJ_TAC>-
          (drule INJ_SUBSET>>
          disch_then match_mp_tac >>fs[SUBSET_DEF]))>>
      metis_tac[strong_locals_rel_insert,SUBSET_OF_INSERT,INSERT_SING_UNION,strong_locals_rel_subset,INJ_SUBSET]
      ))
  >- (*Assign*)
    (
    exists_tac>>exists_tac_2>>  rpt strip_tac >>
    fs[word_state_eq_rel_def,set_var_def]>>
    fs[domain_union,get_writes_def,get_writes_inst_def,GSYM INSERT_SING_UNION]>>
    irule strong_locals_rel_insert >> fs[] >>
    metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT
             ,strong_locals_rel_insert,SUBSET_UNION])
  >- (*Get*)
    (exists_tac>>
    EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[colouring_ok_def,set_var_def,get_store_def,get_live_def]>>
    gvs[] >> irule strong_locals_rel_insert >> fs[] >>
    fs[domain_union,get_writes_def,get_writes_inst_def,GSYM INSERT_SING_UNION])
  >- (*Set*)
    (exists_tac>>exists_tac_2>>
    srw_tac[][]>>
    rev_full_simp_tac(srw_ss())[set_store_def,word_state_eq_rel_def]>>
    metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset
             ,domain_union,SUBSET_UNION])
  >- (*Store*)
    (exists_tac>>exists_tac_2>>
    srw_tac[][]>>
    rev_full_simp_tac(srw_ss())[set_store_def,word_state_eq_rel_def]>>
    Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac strong_locals_rel_get_var>>
    full_simp_tac(srw_ss())[mem_store_def]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset
             ,domain_union,SUBSET_UNION])
  >- (*MustTerminate*)
    (first_x_assum(qspec_then`p` assume_tac)>>
    full_simp_tac(srw_ss())[colouring_ok_def,evaluate_def,LET_THM,word_state_eq_rel_def]>>
    IF_CASES_TAC>>simp[]>>
    first_x_assum(qspecl_then[
    `st with <|clock:=MustTerminate_limit (:α);termdep:=st.termdep-1|>`,
    `cst with <|clock:=MustTerminate_limit (:α);termdep:=st.termdep-1|>`,`f`,`live`] mp_tac)>>
    impl_tac>- size_tac>>
    impl_tac>- fs[get_live_def]>>
    strip_tac>>
    qexists_tac`perm'`>>simp[]>>
    pop_assum mp_tac >>
    ntac 2 (pairarg_tac>>full_simp_tac(srw_ss())[])>>
    IF_CASES_TAC >> fs[] >> IF_CASES_TAC >> fs[] >>
    metis_tac[])
  >- (*Call*)
    (goalStack.print_tac"Slow evaluate_apply_colour Call proof" >>
    fs [evaluate_def,LET_THM,colouring_ok_def,get_live_def]>>
    Cases_on`get_vars l st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`bad_dest_args o1 l`>- full_simp_tac(srw_ss())[bad_dest_args_def]>>
    `¬bad_dest_args o1 (MAP f l)` by full_simp_tac(srw_ss())[bad_dest_args_def]>>
    imp_res_tac strong_locals_rel_get_vars>>
    pop_assum kall_tac>>
    pop_assum mp_tac >>
    impl_tac>-
      (Cases_on`o'`>>TRY(PairCases_on`x'`)>>fs[get_live_def]>>
      srw_tac[][domain_numset_list_insert]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[domain_numset_list_insert,domain_union])>>
    pop_assum kall_tac>>srw_tac[][]>>
    Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    Cases_on`x'`>>full_simp_tac(srw_ss())[]>>
    FULL_CASE_TAC
    >-
    (*Tail call*)
      (Cases_on`o0`>> fs []>> Cases_on `r` >> fs [] >>
      qexists_tac`cst.permute`>>full_simp_tac(srw_ss())[]>>
      Cases_on`st.clock=0`>- full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
      full_simp_tac(srw_ss())[]>>
      `call_env q r' (dec_clock cst) =
       call_env q r' (dec_clock(st with permute:= cst.permute))` by
        rev_full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def,state_component_equality]>>
      rfs [] >>EVERY_CASE_TAC>>
      fs [])
    >>
    (*Returning calls*)
    cheat (*
    Cases_on `r` >> fs [] >>
    PairCases_on`x'`>>full_simp_tac(srw_ss())[get_live_def]>>
    Cases_on`domain x'1 = {}`>>full_simp_tac(srw_ss())[]>>
    Cases_on`cut_envs (x'1,x'2) st.locals`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac cut_env_lemma>>
    pop_assum kall_tac>>
    pop_assum (qspecl_then [`cst.locals`,`f`] mp_tac)>>
    impl_tac >-
      full_simp_tac(srw_ss())[strong_locals_rel_def,domain_union]>>
    impl_tac >-
      (full_simp_tac(srw_ss())[colouring_ok_def,LET_THM,domain_union]>>
      `domain x'1 ⊆ x'0 INSERT domain x'1` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
      metis_tac[SUBSET_UNION,INJ_less,INSERT_UNION_EQ])>>
    srw_tac[][]>>
    full_simp_tac(srw_ss())[domain_fromAList,toAList_not_empty]>>
    Cases_on`st.clock=0` >>
    full_simp_tac(srw_ss())[call_env_def, flush_state_def,add_ret_loc_def]
    >- (
     Cases_on `o0` >> fs [push_env_def, env_to_list_def, stack_size_def, stack_size_frame_def] >>
     Cases_on `x''` >> fs [] >> Cases_on `r` >> fs [] >> Cases_on `r''` >>
     fs [push_env_def, env_to_list_def, stack_size_def, stack_size_frame_def]) >>
    qpat_abbrev_tac`f_o0=
      case o0 of NONE => NONE
      | SOME (v,prog,l1,l2) => SOME (f v,apply_colour f prog,l1,l2)`>>
    Q.ISPECL_THEN[
      `y`,`x'`,`st with clock := st.clock-1`,
      `f`,`cst with clock := st.clock-1`,`f_o0`,`o0`,`λn. cst.permute (n+1)`]
      mp_tac (GEN_ALL push_env_s_val_eq)>>
    impl_tac >-
      (rev_full_simp_tac(srw_ss())[LET_THM,Abbr`f_o0`]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    srw_tac[][]>>
    rfs [LET_THM,env_to_list_def,dec_clock_def]>>
    qabbrev_tac `envx = push_env x' o0
       (st with <|permute := perm; clock := st.clock − 1|>) with
         <| locals := fromList2 (q);
            locals_size := r' ;
            stack_max :=
             OPTION_MAP2 MAX (push_env x' o0
                 (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
                  (OPTION_MAP2 $+ (stack_size (push_env x' o0
                     (st with <|permute := perm; clock := st.clock - 1|>)).stack) r') |>`>>
    qpat_abbrev_tac `envy = (push_env y A B) with <| locals := C; locals_size := r' ;
      stack_max := _; clock := _ |>`>>
    Q.ISPECL_THEN [`q'`,`envx`] mp_tac evaluate_stack_swap>>
    `OPTION_MAP2 MAX (push_env x' NONE
     (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
       (OPTION_MAP2 $+ (stack_size (push_env x' NONE
        (st with <|permute := perm; clock := st.clock - 1|>)).stack) r') = OPTION_MAP2 MAX (push_env y NONE cst).stack_max
        (OPTION_MAP2 $+(stack_size (push_env y NONE cst).stack) r')` by
      fs [push_env_def, env_to_list_def, stack_size_def, stack_size_frame_def] >>
    ntac 2 FULL_CASE_TAC>-
      (srw_tac[][]>> qexists_tac`perm` >>
       unabbrev_all_tac>> fs [dec_clock_def]) >>
     `envx with stack := envy.stack = envy` by
      (unabbrev_all_tac>>
      Cases_on`o0`>>TRY(PairCases_on`x'''`)>>
      full_simp_tac(srw_ss())[push_env_def,state_component_equality]>>
      full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def, stack_size_def,
        stack_size_frame_def]) >>
     `s_val_eq envx.stack envy.stack` by
      (unabbrev_all_tac>>
       full_simp_tac(srw_ss())[state_component_equality])>>
    FULL_CASE_TAC
    >-
    (*Result*)
    (strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
    impl_tac>-
      (unabbrev_all_tac>>
       full_simp_tac(srw_ss())[state_component_equality,dec_clock_def])>>
    strip_tac>>full_simp_tac(srw_ss())[]>>
    rev_full_simp_tac(srw_ss())[]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[]>-
      (qexists_tac`perm`>>full_simp_tac(srw_ss())[dec_clock_def])>>
    (*Backwards chaining*)
    fs [Abbr`envy`,Abbr`envx`,state_component_equality]>>
    Q.ISPECL_THEN [`(cst with clock := st.clock-1)`,
                  `r with stack := st'`,`y`,`f_o0`]
                  mp_tac push_env_pop_env_s_key_eq >>
    impl_tac>-
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[])>>
    Q.ISPECL_THEN [`(st with <|permute:=perm;clock := st.clock-1|>)`,
                  `r`,`x'`,`o0`]
                  mp_tac push_env_pop_env_s_key_eq>>
    impl_tac>-
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[])>>
     ntac 2 strip_tac>>
    rev_full_simp_tac(srw_ss())[]>>
    (*Now we can finally use the IH*)
    last_x_assum(qspecl_then[`x'2`,`set_var x'0 w0 y'`
                            ,`set_var (f x'0) w0 y''`,`f`,`live`]mp_tac)>>
    impl_tac>-size_tac>>
    full_simp_tac(srw_ss())[colouring_ok_def]>>
    impl_tac>-
      (Cases_on`o0`>>TRY(PairCases_on`x''`)>>full_simp_tac(srw_ss())[]>>
      unabbrev_all_tac>>
      full_simp_tac(srw_ss())[set_var_def,state_component_equality]>>
      `s_key_eq y'.stack y''.stack` by
        metis_tac[s_key_eq_trans,s_key_eq_sym]>>
      Q.ISPECL_THEN [`y''`,`y'`] mp_tac (GEN_ALL pop_env_frame|>SIMP_RULE std_ss [Once CONJ_COMM])>>
      simp[GSYM AND_IMP_INTRO]>>
      rpt(disch_then drule)>>simp[]>>
      strip_tac>>
      rev_full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
      full_simp_tac(srw_ss())[colouring_ok_def,LET_THM,strong_locals_rel_def]>>
      srw_tac[][]>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      full_simp_tac(srw_ss())[s_key_eq_def,s_val_eq_def]>>
      Cases_on`opt`>>TRY(PairCases_on`x''`)>>
      Cases_on`opt'`>>TRY(PairCases_on`x''`)>>
      full_simp_tac(srw_ss())[s_frame_key_eq_def,s_frame_val_eq_def]>>
      Cases_on`n'' = x'0`>>
      full_simp_tac(srw_ss())[lookup_insert]>>
      `f n'' ≠ f x'0` by
        (imp_res_tac domain_lookup>>
        full_simp_tac(srw_ss())[domain_fromAList]>>
        (*some assumption movements to make this faster*)
        qpat_x_assum `INJ f (x'0 INSERT A) B` mp_tac>>
        rpt (qpat_x_assum `INJ f A B` kall_tac)>>
        strip_tac>>
        FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        pop_assum(qspecl_then [`n''`,`x'0`] mp_tac)>>
        srw_tac[][domain_union])>>
      full_simp_tac(srw_ss())[lookup_fromAList]>>
      imp_res_tac key_map_implies>>
      rev_full_simp_tac(srw_ss())[]>>
      `l'' = ZIP(MAP FST l'',MAP SND l'')` by full_simp_tac(srw_ss())[ZIP_MAP_FST_SND_EQ]>>
      pop_assum SUBST1_TAC>>
      pop_assum (SUBST1_TAC o SYM)>>
      match_mp_tac ALOOKUP_key_remap_2>>
      full_simp_tac(srw_ss())[]>>CONJ_TAC>>
      metis_tac[LENGTH_MAP,ZIP_MAP_FST_SND_EQ])>>
    strip_tac>>
    Q.ISPECL_THEN [`q'`,`push_env x' o0
            (st with <|permute := perm; clock := st.clock − 1|>) with
          <|locals := fromList2 (q);
            locals_size := r';
            stack_max := OPTION_MAP2 MAX (push_env y f_o0 cst).stack_max
                 (OPTION_MAP2 $+ (stack_size (push_env y f_o0 cst).stack) r')|> `,`perm'`]
      assume_tac permute_swap_lemma>>
    rev_full_simp_tac(srw_ss())[LET_THM]>>
    (*"Hot-swap" the suffix of perm, maybe move into lemma*)
    qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
    qpat_abbrev_tac `env1 = push_env A B C with <|locals := D; locals_size := E ; stack_max := SM|>`>>
    qpat_x_assum `A = (SOME B,C)` mp_tac>>
    qpat_abbrev_tac `env2 = push_env A B C with
                    <|locals:=D; locals_size := E; stack_max := SM'; permute:=E'|>`>>
    strip_tac>>
    Cases_on`o0`>>TRY(PairCases_on`x''`)>>full_simp_tac(srw_ss())[]>>
    `env1 = env2` by
      (unabbrev_all_tac>>
      simp[push_env_def,LET_THM,env_to_list_def,
           state_component_equality,ETA_AX, stack_size_def, stack_size_frame_def]) >>
    full_simp_tac(srw_ss())[]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])
    >-
    (*Exceptions*)
    (full_simp_tac(srw_ss())[]>>strip_tac>>
    imp_res_tac s_val_eq_LASTN_exists>>
    first_x_assum(Q.ISPECL_THEN[`envy.stack`,`e'`,`ls'`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]>>
    Cases_on`o0`
    >-
      (*No handler*)
      (full_simp_tac(srw_ss())[Abbr`f_o0`]>>
      qexists_tac`perm`>>
      `ls=ls'` by
        (unabbrev_all_tac>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM]>>
        Cases_on`st.handler < LENGTH st.stack`
        >-
          (imp_res_tac LASTN_TL>>
          rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[])
        >>
          `st.handler = LENGTH st.stack` by DECIDE_TAC>>
          rpt (qpat_x_assum `LASTN A B = C` mp_tac)>-
          simp[LASTN_LENGTH_cond])>>
      rev_full_simp_tac(srw_ss())[]>>
      `lss = lss'` by
        (match_mp_tac LIST_EQ_MAP_PAIR>>full_simp_tac(srw_ss())[]>>
        qsuff_tac `e = e''`>-metis_tac[]>>
        unabbrev_all_tac>>
        full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
        `st.handler < LENGTH st.stack` by
          (CCONTR_TAC>>
          `st.handler = LENGTH st.stack` by DECIDE_TAC>>
          ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
          simp[LASTN_LENGTH2])>>
        ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
        full_simp_tac(srw_ss())[LASTN_TL])>>
      metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans])
    >>
      (*Handler*)
      PairCases_on`x''`>>full_simp_tac(srw_ss())[]>>
      unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      IF_CASES_TAC>-
        (qexists_tac`perm`>>full_simp_tac(srw_ss())[])>>
      rpt (qpat_x_assum `LASTN A B = C` mp_tac)>>
      simp[LASTN_LENGTH_cond]>>
      rpt strip_tac>>
      full_simp_tac(srw_ss())[domain_fromAList]>>
      imp_res_tac list_rearrange_keys>>
      `set (MAP FST lss') = domain y` by
        (qpat_x_assum`A=MAP FST lss'` (SUBST1_TAC o SYM)>>
        full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][EXISTS_PROD]>>
        simp[MEM_MAP,QSORT_MEM]>>srw_tac[][EQ_IMP_THM]
        >-
          (Cases_on`y'`>>
          full_simp_tac(srw_ss())[MEM_toAList]>>
          imp_res_tac domain_lookup>>
          metis_tac[])
        >>
          full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList]>>
          metis_tac[domain_lookup])>>
      `domain x' = set (MAP FST lss)` by
        (qpat_x_assum `A = MAP FST lss` (SUBST1_TAC o SYM)>>
          full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,QSORT_MEM,MEM_toAList
            ,EXISTS_PROD,domain_lookup])>>
      full_simp_tac(srw_ss())[]>>
      qpat_abbrev_tac `cr'=r with<|locals:= A;stack:=C;handler:=D|>`>>
      (*Use the IH*)
      last_x_assum(qspecl_then[`x''1`,`set_var x''0 w0 r`
                            ,`set_var (f x''0) w0 cr'`,`f`,`live`]mp_tac)>>
      impl_tac>-size_tac>>
      full_simp_tac(srw_ss())[colouring_ok_def]>>
      impl_tac>-
      (full_simp_tac(srw_ss())[set_var_def,state_component_equality,Abbr`cr'`]>>
      full_simp_tac(srw_ss())[colouring_ok_def,LET_THM,strong_locals_rel_def]>>
      srw_tac[][]>-metis_tac[s_key_eq_trans,s_val_and_key_eq]>>
      Cases_on`n' = x''0`>>full_simp_tac(srw_ss())[lookup_insert]>>
      `f n' ≠ f x''0` by
       (imp_res_tac domain_lookup>>
        full_simp_tac(srw_ss())[domain_fromAList]>>
        qpat_x_assum `INJ f (C INSERT A) B` mp_tac>>
        qpat_x_assum `INJ f A B` kall_tac>>
        `n' ∈ set (MAP FST lss)` by full_simp_tac(srw_ss())[]>>
        `n' ∈ domain x'1` by
          (full_simp_tac(srw_ss())[domain_union]>>metis_tac[])>>
        ntac 4 (pop_assum mp_tac)>>
        rpt (pop_assum kall_tac)>>
        srw_tac[][]>>
        CCONTR_TAC>>
        FULL_SIMP_TAC bool_ss [INJ_DEF]>>
        first_x_assum(qspecl_then[`n'`,`x''0`] mp_tac)>>
        full_simp_tac(srw_ss())[])>>
      full_simp_tac(srw_ss())[lookup_fromAList]>>
      imp_res_tac key_map_implies>>
      rev_full_simp_tac(srw_ss())[]>>
      `lss' = ZIP(MAP FST lss',MAP SND lss')` by full_simp_tac(srw_ss())[ZIP_MAP_FST_SND_EQ]>>
      pop_assum SUBST1_TAC>>
      pop_assum (SUBST1_TAC o SYM)>>
      match_mp_tac ALOOKUP_key_remap_2>>
      full_simp_tac(srw_ss())[]>>CONJ_TAC>>
      metis_tac[LENGTH_MAP,ZIP_MAP_FST_SND_EQ])>>
      srw_tac[][]>>
      Q.ISPECL_THEN[`q'`,`st with <|locals := fromList2 (q);
            locals_size := r';
            stack := StackFrame st.locals_size (list_rearrange (perm 0)
              (QSORT key_val_compare ( (toAList x'))))
              (SOME (r.handler,x''2,x''3))::st.stack;
             stack_max := OPTION_MAP2 MAX (OPTION_MAP2 MAX st.stack_max
                          (stack_size (StackFrame st.locals_size
                          (list_rearrange (perm 0) (QSORT key_val_compare (toAList x')))
                          (SOME (st.handler,x''2,x''3))::st.stack))) (OPTION_MAP2 $+
                          (stack_size (StackFrame st.locals_size
                          (list_rearrange (perm 0) (QSORT key_val_compare (toAList x')))
                          (SOME (st.handler,x''2,x''3))::st.stack)) r');
            permute := (λn. perm (n + 1));
            handler := LENGTH st.stack;
            clock := st.clock − 1|>`,`perm'`]
        assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      `(λn. perm'' n) = perm''` by full_simp_tac(srw_ss())[FUN_EQ_THM]>>
      `domain (fromAList lss) = domain x'1` by
        metis_tac[domain_fromAList]>>
      full_simp_tac(srw_ss())[stack_size_def, stack_size_frame_def])
    >>
    (*The rest*)
    srw_tac[][]>>qexists_tac`perm`>>full_simp_tac(srw_ss())[]>>
    pop_assum(qspec_then`envy.stack` mp_tac)>>
    impl_tac>-
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[state_component_equality])>>
    srw_tac[][]>>full_simp_tac(srw_ss())[]>>NO_TAC*))
  >- (*Seq*)
    (srw_tac[][]>>fs[evaluate_def,colouring_ok_def,LET_THM,get_live_def]>>
    last_assum(qspecl_then[`p`,`st`,`cst`,`f`,`get_live p0 live`]
      mp_tac)>>
    impl_tac>-size_tac>>
    srw_tac[][]>>
    Cases_on`evaluate(p,st with permute:=perm')`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm'`>>full_simp_tac(srw_ss())[]) >>
    Cases_on`evaluate(apply_colour f p,cst)`>>full_simp_tac(srw_ss())[]>>
    reverse (Cases_on`q`)>>full_simp_tac(srw_ss())[]
    >-
      (qexists_tac`perm'`>>srw_tac[][])
    >>
    first_assum(qspecl_then[`p0`,`r`,`r'`,`f`,`live`] mp_tac)>>
    impl_tac>- size_tac>>
    srw_tac[][]>>
    Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rev_full_simp_tac(srw_ss())[LET_THM]>>
    qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[])
  >- (*If*)
    (full_simp_tac(srw_ss())[evaluate_def,colouring_ok_def,LET_THM,get_live_def]>>
    Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>imp_res_tac strong_locals_rel_get_var>>
    pop_assum kall_tac>>pop_assum mp_tac>>impl_tac >-
      (FULL_CASE_TAC>>full_simp_tac(srw_ss())[])
    >>
    srw_tac[][]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[]>>
    Cases_on`get_var_imm r st`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac strong_locals_rel_get_var_imm>>
    pop_assum kall_tac>>pop_assum mp_tac>>impl_tac>-
      (Cases_on`r`>>full_simp_tac(srw_ss())[])>>
    Cases_on`x`>>srw_tac[][]>>full_simp_tac(srw_ss())[]
    >-
     (first_assum(qspecl_then[`p`,`st`,`cst`,`f`,`live`] mp_tac)>>
      impl_tac>- size_tac>>
      impl_tac>-
        (Cases_on`r`>>
        full_simp_tac(srw_ss())[domain_insert,domain_union]>>
        metis_tac[SUBSET_OF_INSERT,SUBSET_UNION,strong_locals_rel_subset])>>
      srw_tac[][]>>
      Q.ISPECL_THEN[`w`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[])
    >>
      (first_assum(qspecl_then[`p0`,`st`,`cst`,`f`,`live`] mp_tac)>>
      impl_tac>- size_tac>>
      impl_tac>-
        (Cases_on`r`>>full_simp_tac(srw_ss())[domain_insert,domain_union]>>
        metis_tac[SUBSET_OF_INSERT,SUBSET_UNION,strong_locals_rel_subset])>>
      srw_tac[][]>>
      Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
        assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[]))
  >- cheat (*(*Alloc*)
    (
    full_simp_tac(srw_ss())[evaluate_def,colouring_ok_def,get_live_def,get_writes_def]>>
    Cases_on`get_var n st`>>full_simp_tac(srw_ss())[LET_THM]>>
    imp_res_tac strong_locals_rel_get_var>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[alloc_def]>>
    Cases_on`cut_env s st.locals`>>full_simp_tac(srw_ss())[]>>
    `domain s ⊆ (n INSERT domain s)` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
    imp_res_tac strong_locals_rel_subset>>
    imp_res_tac cut_env_lemma>>
    pop_assum mp_tac>>impl_tac
    >-
      (match_mp_tac (GEN_ALL INJ_less)>>metis_tac[])
    >>
    srw_tac[][]>>full_simp_tac(srw_ss())[set_store_def]>>
    qpat_abbrev_tac`non = NONE`>>
    Q.ISPECL_THEN [`y`,`x`,`st with store:= st.store |+ (AllocSize,Word c)`,
    `f`,`cst with store:= cst.store |+ (AllocSize,Word c)`,`non`,`non`,`cst.permute`] assume_tac  (GEN_ALL push_env_s_val_eq)>>
    rev_full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`non`]>>
    qexists_tac`perm`>>full_simp_tac(srw_ss())[]>>
    qpat_abbrev_tac `st' = push_env x NONE A`>>
    qpat_abbrev_tac `cst' = push_env y NONE B`>>
    Cases_on`gc st'`>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`st'`,`cst'`,`x'`] mp_tac gc_s_val_eq_gen>>
    impl_keep_tac>-
      (unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,word_state_eq_rel_def, stack_size_def, stack_size_frame_def]>>
      rev_full_simp_tac(srw_ss())[])
    >>
    srw_tac[][]>>simp[]>>
    unabbrev_all_tac>>
    imp_res_tac gc_frame>>
    imp_res_tac push_env_pop_env_s_key_eq>>
    Cases_on`pop_env x'`>>full_simp_tac(srw_ss())[]>>
    `strong_locals_rel f (domain live) x''.locals y'.locals ∧
     word_state_eq_rel x'' y'` suffices_by (fs[word_state_eq_rel_def]>>
      FULL_CASE_TAC>>full_simp_tac(srw_ss())[has_space_def]>>
      Cases_on`x'''`>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[call_env_def,flush_state_def]) >>
      imp_res_tac gc_s_key_eq>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      ntac 2(pop_assum mp_tac>>simp[Once s_key_eq_sym])>>
      ntac 2 strip_tac>>
      rpt (qpat_x_assum `s_key_eq A B` mp_tac)>>
      qpat_abbrev_tac `lsA = list_rearrange (cst.permute 0)
        (QSORT key_val_compare ( (toAList y)))`>>
      qpat_abbrev_tac `lsB = list_rearrange (perm 0)
        (QSORT key_val_compare ( (toAList x)))`>>
      ntac 4 strip_tac>>
      Q.ISPECL_THEN [`x'.stack`,`y'`,`t'`,`NONE:(num#num#num) option`,
         `st.locals_size`, `lsA`,`cst.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
      impl_tac
      >-
        (full_simp_tac(srw_ss())[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])
      >>
      Q.ISPECL_THEN [`t'.stack`,`x''`,`x'`,`NONE:(num#num#num) option`
        ,`st.locals_size`, `lsB`,`st.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
      impl_tac
      >-
        (full_simp_tac(srw_ss())[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])
      >>
      srw_tac[][]
      >-
        (simp[]>>
        full_simp_tac(srw_ss())[strong_locals_rel_def,lookup_fromAList]>>
        `MAP SND l = MAP SND ls'` by
          full_simp_tac(srw_ss())[s_val_eq_def,s_frame_val_eq_def]>>
        srw_tac[][]>>
        `MAP FST (MAP (λ(x,y). (f x,y)) lsB) =
         MAP f (MAP FST lsB)` by
          full_simp_tac(srw_ss())[MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
        full_simp_tac(srw_ss())[]>>
        match_mp_tac ALOOKUP_key_remap_2>>srw_tac[][]>>
        metis_tac[s_key_eq_def,s_frame_key_eq_def,LENGTH_MAP]) >>
        full_simp_tac(srw_ss())[word_state_eq_rel_def,pop_env_def]>>
        rev_full_simp_tac(srw_ss())[state_component_equality]>>
        conj_tac >- fs [s_val_eq_def, s_frame_val_eq_def] >>
        metis_tac[s_val_and_key_eq,s_key_eq_sym,s_val_eq_sym,s_key_eq_trans])*)
  >- (* StoreConsts *)
    (exists_tac>>
    Cases_on`get_var n1 st`>>fs[]>>
    imp_res_tac strong_locals_rel_get_var>>
    simp[]>>
    TOP_CASE_TAC>> simp[]>>
    Cases_on`get_var n2 st`>>fs[]>>
    imp_res_tac strong_locals_rel_get_var>>
    simp[]>>
    TOP_CASE_TAC>> simp[]>>
    rw[]>>simp[set_var_def,unset_var_def]>>
    match_mp_tac strong_locals_rel_insert>>
    CONJ_TAC >-
      (match_mp_tac (GEN_ALL INJ_less)>>
      asm_exists_tac>>simp[domain_union,get_writes_def])>>
    match_mp_tac strong_locals_rel_insert>>
    CONJ_TAC >-
      (match_mp_tac (GEN_ALL INJ_less)>>
      asm_exists_tac>>
      simp[domain_union,get_writes_def]>>
      simp[SUBSET_DEF])>>
    fs[get_writes_def,domain_union]>>
    fs[strong_locals_rel_def]>>
    rw[lookup_delete]
    >- (
      qpat_x_assum `INJ _ _ _` mp_tac>>
      REWRITE_TAC [INJ_DEF]>>
      strip_tac>>
      first_x_assum(qspecl_then[`n`,`n'`] mp_tac)>>
      simp[])
    >>
      qpat_x_assum `INJ _ _ _` mp_tac>>
      REWRITE_TAC [INJ_DEF]>>
      strip_tac>>
      first_x_assum(qspecl_then[`n0`,`n'`] mp_tac)>>
      simp[])
  >- (* Raise *)
    (exists_tac>>
    Cases_on`get_var n st`>> fs[]>>
    imp_res_tac strong_locals_rel_get_var>>full_simp_tac(srw_ss())[jump_exc_def]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[] >> gvs[])
  >- (* Return *)
    (exists_tac>>
    fs[get_writes_def] >>
    Cases_on`get_var n st`>>
    fs[]>>
    Cases_on `x` >> fs[] >>
    Cases_on`get_vars l st`>>
    fs[]>>
    imp_res_tac strong_locals_rel_get_var>>
    full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
    `get_vars (MAP f l) cst = SOME x` by
     (drule strong_locals_rel_get_vars >>
      disch_then (qspec_then `l` mp_tac) >>
      simp[domain_numset_list_insert]) >>
    full_simp_tac(srw_ss())[])
  >- (* Tick *)
    (exists_tac>>IF_CASES_TAC>>full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def])
  >- (* OpCurrHeap *)
    (exists_tac>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def,
      get_live_def,colouring_ok_def,word_exp_def,the_words_def] >>
    Cases_on `get_var n0 st` >> fs[] >>
    imp_res_tac strong_locals_rel_get_var>>
    full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
    Cases_on `x` >> fs[] >>
    fs[get_store_def] >> fs[GSYM get_store_def] >>
    Cases_on ‘get_store CurrHeap st’ >> fs [] >> Cases_on ‘x’ >> fs []>>
    EVERY_CASE_TAC>>fs [set_var_def]>>
    match_mp_tac strong_locals_rel_insert >>
    fs [get_writes_def,domain_union] >>
    metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT
             ,strong_locals_rel_insert,SUBSET_UNION])
  >- (* LocValue *)
    (exists_tac>>fs[set_var_def,strong_locals_rel_def]>>rw[]>>
    fs[lookup_insert]>>
    Cases_on`n'=n`>>fs[]>>
    `f n ≠ f n'` by
      (fs[get_writes_def]>>
      FULL_SIMP_TAC bool_ss [INJ_DEF,domain_union,domain_insert]>>
      first_x_assum(qspecl_then[`n`,`n'`] assume_tac)>>
      ntac 4 (pop_assum mp_tac)>>
      rpt (pop_assum kall_tac)>>
      simp[])>>
    fs[])
  >- (* Install *) cheat
    (*
    (exists_tac>>
    pairarg_tac>>fs[case_eq_thms]>>
    pop_assum mp_tac>>pairarg_tac>>strip_tac>>rfs[case_eq_thms]>>rw[]>>
    `domain s ⊆ domain (list_insert [n;n0;n1;n2] s)` by
      fs[list_insert_def,SUBSET_DEF]>>
    imp_res_tac strong_locals_rel_subset>>
    imp_res_tac cut_env_lemma>>fs[]>>
    pop_assum kall_tac>>
    pop_assum mp_tac >> impl_tac>-
      (match_mp_tac (GEN_ALL INJ_less)>>metis_tac[])>>
    strip_tac>>fs[]>>
    imp_res_tac strong_locals_rel_get_var>>fs[list_insert_def]>>
    fs[strong_locals_rel_def,lookup_insert]>>rw[]
    >-
      (qpat_x_assum`INJ _ _ _` kall_tac>>
      qpat_x_assum`INJ _ _ _` mp_tac>>
      simp[get_writes_def,domain_union]>>
      SIMP_TAC bool_ss [INJ_DEF]>>
      strip_tac>>
      first_x_assum(qspecl_then [`n'`,`n`] assume_tac)>>full_simp_tac(srw_ss())[])
    >>
      metis_tac[domain_lookup]) *)
  >- (* CBW *)
    (exists_tac>>pairarg_tac>>fs[case_eq_thms]>>
    imp_res_tac strong_locals_rel_get_var>>fs[list_insert_def]>>
    rw[]>>fs[]>>
    match_mp_tac (GEN_ALL strong_locals_rel_subset|>SIMP_RULE std_ss[Once CONJ_COMM])>>
    asm_exists_tac>>
    fs[SUBSET_DEF])
  >- (* DBW *)
    (exists_tac>>pairarg_tac>>fs[case_eq_thms]>>
    imp_res_tac strong_locals_rel_get_var>>fs[list_insert_def]>>
    rw[]>>fs[]>>
    match_mp_tac (GEN_ALL strong_locals_rel_subset|>SIMP_RULE std_ss[Once CONJ_COMM])>>
    asm_exists_tac>>
    fs[SUBSET_DEF])
  >- (* FFI *) cheat
     (*
     (exists_tac>>Cases_on`get_var n st`>>Cases_on`get_var n0 st`>>
      Cases_on`get_var n1 st`>>Cases_on`get_var n2 st`>>
      full_simp_tac(srw_ss())[get_writes_def,LET_THM]>>
      Cases_on`x`>>full_simp_tac(srw_ss())[]>>Cases_on`x'`>>full_simp_tac(srw_ss())[]>>
      Cases_on`x''`>>full_simp_tac(srw_ss())[]>>Cases_on`x'''`>>full_simp_tac(srw_ss())[]>>
      imp_res_tac strong_locals_rel_get_var>>full_simp_tac(srw_ss())[]>>
      Cases_on`cut_env s0 st.locals`>>full_simp_tac(srw_ss())[]>>
      `domain s0 ⊆ (n INSERT n0 INSERT n1 INSERT n2 INSERT domain s0)` by full_simp_tac(srw_ss())[SUBSET_DEF]>>
      imp_res_tac strong_locals_rel_subset>>
      imp_res_tac cut_env_lemma>>
      pop_assum mp_tac >> impl_tac>-
        (match_mp_tac (GEN_ALL INJ_less)>>metis_tac[])>>
      srw_tac[][]>>FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`call_FFI st.ffi (ExtCall s) x'' x'`>>full_simp_tac(srw_ss())[strong_locals_rel_def]>>
      srw_tac[][]>>simp[call_env_def,flush_state_def]>>
      metis_tac[domain_lookup]) *)
  >- (* ShareInst *)
    (exists_tac>>
    pairarg_tac>>
    gvs[AllCaseEqs()]>>
    drule apply_colour_exp_lemma >>
    disch_then $ qspecl_then [`cst`,`f`] mp_tac >>
    rename1`m = Store \/ m = Store8 \/ m = Store32`>>
    qabbrev_tac `mcase = (m = Store \/ m = Store8 \/ m = Store32)`>>
    qpat_x_assum `strong_locals_rel _ _ _ _` mp_tac >>
    IF_CASES_TAC >>
    fs[] >>
    disch_then assume_tac >>
    drule strong_locals_rel_get_var >>
    strip_tac >>
    impl_tac
    >- (
      fs[word_state_eq_rel_def] >>
      metis_tac[SUBSET_OF_INSERT,domain_union,SUBSET_UNION
         ,strong_locals_rel_subset])
    >- (
      strip_tac >>
      gvs[oneline share_inst_def,
        oneline sh_mem_store_def,
        oneline sh_mem_store_byte_def,
        oneline sh_mem_store32_def,
        flush_state_def,
        markerTheory.Abbrev_def,AllCaseEqs()] >>
      Cases_on `get_var n st` >> fs[] >>
      first_x_assum $ drule_at (Pos last) >>
      (impl_tac >- fs[domain_union,SUBSET_UNION]) >>
      gvs[] >>
      strip_tac >>
      EVERY_CASE_TAC >> gvs[] >>
      irule strong_locals_rel_subset >>
      first_assum $ irule_at (Pos last) >>
      simp[domain_union] >>
      metis_tac[SUBSET_OF_INSERT,SUBSET_TRANS,SUBSET_UNION])
    >- (
      fs[word_state_eq_rel_def] >>
      metis_tac[SUBSET_OF_INSERT,domain_union,SUBSET_UNION
         ,strong_locals_rel_subset])
    >- (
      strip_tac >>
      gvs[oneline share_inst_def,
        oneline sh_mem_load_def,
        oneline sh_mem_load_byte_def,
        oneline sh_mem_load32_def,
        oneline sh_mem_set_var_def,
        flush_state_def,set_var_def,
        markerTheory.Abbrev_def,AllCaseEqs()] >>
      irule strong_locals_rel_insert >>
      fs[domain_union] >>
      (conj_tac >- (
        drule_then irule INJ_SUBSET >>
        simp[get_writes_def])) >>
      drule_at_then (Pos last) irule strong_locals_rel_subset >>
      metis_tac[SUBSET_UNION]))
QED

(* TODO: get_clash_sets, made redundant by clash tree *)

(*
(*Alternate liveness*)
Definition colouring_ok_alt_def:
  colouring_ok_alt f prog live =
    let (hd,ls) = get_clash_sets prog live in
    EVERY (λs. INJ f (domain s) UNIV) ls ∧
    INJ f (domain hd) UNIV
End

(*hd element is just get_live*)
Triviality get_clash_sets_hd:
  ∀prog live hd ls.
  get_clash_sets prog live = (hd,ls) ⇒
  get_live prog live = hd
Proof
  Induct>>srw_tac[][get_clash_sets_def]>>full_simp_tac(srw_ss())[LET_THM]
  >-
    full_simp_tac(srw_ss())[get_live_def]
  >-
    (Cases_on`o'`>>full_simp_tac(srw_ss())[get_clash_sets_def,LET_THM]>>
    PairCases_on`x`>>full_simp_tac(srw_ss())[get_clash_sets_def,get_live_def]>>
    full_simp_tac(srw_ss())[LET_THM,UNCURRY]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])
  >-
    (Cases_on`get_clash_sets prog' live`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_clash_sets prog q`>>full_simp_tac(srw_ss())[]>>
    metis_tac[get_live_def])
  >>
    Cases_on`get_clash_sets prog live`>>
    Cases_on`get_clash_sets prog' live`>>
    full_simp_tac(srw_ss())[get_live_def,LET_THM]>>metis_tac[]
QED

(*The liveset passed in at the back is always satisfied*)
Theorem get_clash_sets_tl[local]:
 ∀prog live f.
  let (hd,ls) = get_clash_sets prog live in
  EVERY (λs. INJ f (domain s) UNIV) ls ⇒
  INJ f (domain live) UNIV
Proof
  completeInduct_on`prog_size (K 0) prog`>>
  full_simp_tac(srw_ss())[PULL_FORALL]>>
  rpt strip_tac>>
  Cases_on`prog`>>
  full_simp_tac(srw_ss())[colouring_ok_alt_def,LET_THM,get_clash_sets_def,get_live_def]>>
  full_simp_tac(srw_ss())[get_writes_def]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
  >-
    (first_x_assum(qspecl_then[`p`,`live`,`f`]mp_tac)>>
    impl_tac>-size_tac>>srw_tac[][])
  >-
    (Cases_on`o'`>>full_simp_tac(srw_ss())[UNCURRY,get_clash_sets_def,LET_THM]
    >- metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
    >>
    PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
    first_x_assum(qspecl_then[`x2`,`live`,`f`] mp_tac)>>
    impl_tac >- size_tac>>srw_tac[][]>>
    full_simp_tac(srw_ss())[get_clash_sets_def,UNCURRY,LET_THM]>>
    Cases_on`o0`>>TRY (PairCases_on`x`)>>full_simp_tac(srw_ss())[])
  >>
    TRY(first_x_assum(qspecl_then[`p0`,`live`,`f`]mp_tac)>>
    impl_tac>-size_tac>>srw_tac[][]>>
    full_simp_tac(srw_ss())[UNCURRY])
  >> metis_tac[INJ_UNION,domain_union,INJ_SUBSET,SUBSET_UNION]
QED

Theorem colouring_ok_alt_thm:
 ∀f prog live.
  colouring_ok_alt f prog live
  ⇒
  colouring_ok f prog live
Proof
  ho_match_mp_tac (fetch "-" "colouring_ok_ind")>>
  srw_tac[][]>>
  full_simp_tac(srw_ss())[get_clash_sets_def,colouring_ok_alt_def,colouring_ok_def,LET_THM]
  >-
    (Cases_on`get_clash_sets prog' live`>>
    Cases_on`get_clash_sets prog q`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac get_clash_sets_hd>>
    full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`prog`,`q`,`f`] assume_tac get_clash_sets_tl>>
    rev_full_simp_tac(srw_ss())[LET_THM])
  >-
    (
    Cases_on`get_clash_sets prog live`>>
    Cases_on`get_clash_sets prog' live`>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    imp_res_tac get_clash_sets_hd>>
    full_simp_tac(srw_ss())[]>>
    metis_tac[INJ_SUBSET,SUBSET_DEF,SUBSET_OF_INSERT,domain_union,SUBSET_UNION])
  >>
    Cases_on`h`>>full_simp_tac(srw_ss())[LET_THM]
    >-
      (Cases_on`get_clash_sets prog live`>>full_simp_tac(srw_ss())[])
    >>
    PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_clash_sets prog live`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_clash_sets x1 live`>>full_simp_tac(srw_ss())[]>>
    EVERY_CASE_TAC>>
    full_simp_tac(srw_ss())[LET_THM]>>
    Cases_on`get_clash_sets prog live`>>
    full_simp_tac(srw_ss())[UNCURRY]
QED

val fs1 = full_simp_tac(srw_ss())[LET_THM, get_clash_sets_def,
  every_var_def, get_live_def, domain_numset_list_insert,
  domain_union, EVERY_MEM, get_writes_def, every_var_inst_def,
  get_live_inst_def, every_name_def, toAList_domain];
*)

Triviality every_var_exp_get_live_exp:
  ∀exp.
  every_var_exp (λx. x ∈ domain (get_live_exp exp)) exp
Proof
  ho_match_mp_tac get_live_exp_ind>>
  srw_tac[][]>>full_simp_tac(srw_ss())[get_live_exp_def,every_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>res_tac>>
  match_mp_tac every_var_exp_mono>>
  HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
  metis_tac[SUBSET_DEF,domain_big_union_subset]
QED

(*
(*Every variable is in some clash set*)
Theorem every_var_in_get_clash_set:
 ∀prog live.
  let (hd,clash_sets) = get_clash_sets prog live in
  let ls = hd::clash_sets in
  (∀x. x ∈ domain live ⇒ in_clash_sets ls x) ∧
  (every_var (in_clash_sets ls) prog)
Proof
  completeInduct_on`prog_size (K 0) prog`>>
  ntac 2 (full_simp_tac(srw_ss())[Once PULL_FORALL])>>
  rpt strip_tac>>
  Cases_on`prog`>>fs1>>
  TRY(rw[list_insert_def,EXISTS_OR_THM,RIGHT_AND_OVER_OR,domain_union]>>
    NO_TAC)
  >-
    (*Move*)
    (qpat_abbrev_tac`s1 = numset_list_insert A B`>>
    qpat_abbrev_tac`s2 = union A live`>>
    srw_tac[][]
    >-
      (qexists_tac`s2`>>full_simp_tac(srw_ss())[Abbr`s2`,domain_union])
    >-
      (qexists_tac`s2`>>full_simp_tac(srw_ss())[Abbr`s2`,domain_numset_list_insert,domain_union])
    >>
      qexists_tac`s1`>>full_simp_tac(srw_ss())[Abbr`s1`,domain_numset_list_insert,domain_union])
  >-
    (Cases_on`i`>>fs1>>full_simp_tac(srw_ss())[get_writes_inst_def]>>
    `∀P A B. P A ∨ P B ⇒ (?y:num_set. (y = A ∨ y = B) ∧ P y)` by metis_tac[]
    >-
      (srw_tac[][]>>
      first_x_assum ho_match_mp_tac>>fs[domain_union])
    >-
      (Cases_on`a`>>fs1>>full_simp_tac(srw_ss())[get_writes_inst_def]>>
      EVERY_CASE_TAC>>srw_tac[][]>>
      full_simp_tac(srw_ss())[every_var_imm_def,in_clash_sets_def]>>
      first_x_assum ho_match_mp_tac>> fs[domain_union])
    >-
      (Cases_on`m`>>Cases_on`a`>>fs1>>full_simp_tac(srw_ss())[get_writes_inst_def]>>srw_tac[][]>>
      first_x_assum ho_match_mp_tac>> fs[domain_union])
    >-
      (Cases_on`f`>>fs1>>fs[get_writes_inst_def]>>rw[]>>
      first_x_assum ho_match_mp_tac>> fs[domain_union]))
  >-
    (srw_tac[][]>>
    TRY(qexists_tac`union (insert n () LN) live`>>full_simp_tac(srw_ss())[domain_union])>>
    Q.ISPEC_THEN `e` assume_tac every_var_exp_get_live_exp>>
    match_mp_tac every_var_exp_mono>>
    HINT_EXISTS_TAC>>srw_tac[][in_clash_sets_def]>>
    Cases_on`x=n`
    >-
      (qexists_tac`union (insert n () LN) live`>>full_simp_tac(srw_ss())[domain_union])
    >>
      (qexists_tac`union (get_live_exp e) (delete n live)`>>
      full_simp_tac(srw_ss())[domain_union]))
  >-
    (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
    Q.ISPEC_THEN `e` assume_tac every_var_exp_get_live_exp>>
    match_mp_tac every_var_exp_mono>>
    HINT_EXISTS_TAC>>srw_tac[][in_clash_sets_def]>>
    qexists_tac`union (get_live_exp e) live`>>
    full_simp_tac(srw_ss())[domain_union])
  >-
    (srw_tac[][]
    >-
      (HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
    >-
      (qexists_tac `insert n () (union (get_live_exp e) live)`>>full_simp_tac(srw_ss())[])
    >>
    Q.ISPEC_THEN `e` assume_tac every_var_exp_get_live_exp>>
    match_mp_tac every_var_exp_mono>>
    HINT_EXISTS_TAC>>srw_tac[][in_clash_sets_def]>>
    qexists_tac`insert n () (union (get_live_exp e) live)`>>
    full_simp_tac(srw_ss())[domain_union])
  >-
    (first_x_assum(qspecl_then[`p`,`live`] mp_tac)>>impl_tac>-
    size_tac>>
    pairarg_tac>>simp[])
  >-
    (*Call*)
    (Cases_on`o'`>>fs1
    >-
      (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
      qexists_tac`numset_list_insert l LN`>>full_simp_tac(srw_ss())[domain_numset_list_insert])
    >>
      PairCases_on`x`>>Cases_on`o0`>>fs1
      >-
        (first_x_assum(qspecl_then[`x2`,`live`] mp_tac)>>
        impl_tac>- (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)>>
        Cases_on`get_clash_sets x2 live`>>srw_tac[][]
        >-
          (first_x_assum(qspec_then`x'`assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
        >>
        TRY(full_simp_tac(srw_ss())[every_name_def,EVERY_MEM]>>
          full_simp_tac(srw_ss())[toAList_domain])>>
        qpat_abbrev_tac`A = union x1 X`>>
        qpat_abbrev_tac`Z = insert x0 () x1`>>
        TRY(qexists_tac`A`>>
          full_simp_tac(srw_ss())[Abbr`A`,domain_union,domain_numset_list_insert]>>NO_TAC)>>
        TRY(qexists_tac`Z`>>full_simp_tac(srw_ss())[Abbr`Z`]) >>
        match_mp_tac every_var_mono>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>srw_tac[][in_clash_sets_def]>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
      >>
        PairCases_on`x`>>full_simp_tac(srw_ss())[]>>
        first_assum(qspecl_then[`x2`,`live`] mp_tac)>>
        impl_tac>- (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)>>
        first_x_assum(qspecl_then[`x1'`,`live`] mp_tac)>>
        impl_tac>- (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)>>
        Cases_on`get_clash_sets x2 live`>>
        Cases_on`get_clash_sets x1' live`>>srw_tac[][]
        >-
          (first_x_assum(qspec_then`x'`assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
        >>
        qpat_abbrev_tac`A = union x1 X`>>
        qpat_abbrev_tac`Z = insert x0 () x1`>>
        qpat_abbrev_tac`D = insert x0' () x1`>>
        TRY(qexists_tac`A`>>
          full_simp_tac(srw_ss())[Abbr`A`,domain_union,domain_numset_list_insert]>>NO_TAC)>>
        TRY(qexists_tac`Z`>>full_simp_tac(srw_ss())[Abbr`Z`]>>NO_TAC) >>
        TRY(qexists_tac`D`>>full_simp_tac(srw_ss())[Abbr`D`]) >>
        match_mp_tac every_var_mono>>
        TRY(HINT_EXISTS_TAC)>>
        TRY(qexists_tac`in_clash_sets (q'::r')`)>>
        full_simp_tac(srw_ss())[]>>srw_tac[][in_clash_sets_def]>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
  >-
    (first_assum(qspecl_then[`p0`,`live`] mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
    >>
    Cases_on`get_clash_sets p0 live`>>srw_tac[][]>>
    first_x_assum(qspecl_then[`p`,`q`] mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
    >>
    Cases_on`get_clash_sets p q`>>srw_tac[][]>>
    TRY (metis_tac[every_var_mono])>>
    match_mp_tac every_var_mono>>
    TRY(pop_assum kall_tac>>HINT_EXISTS_TAC)>>
    TRY HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[in_clash_sets_def]>>
    metis_tac[])
  >-
    (first_assum(qspecl_then[`p0`,`live`] mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
    >>
    Cases_on`get_clash_sets p0 live`>>srw_tac[][]>>
    first_assum(qspecl_then[`p`,`live`] mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)
    >>
    Cases_on`get_clash_sets p live`>>srw_tac[][]>>
    Cases_on`r`>>full_simp_tac(srw_ss())[every_var_imm_def]>>
    full_simp_tac(srw_ss())[in_clash_sets_def,domain_union]>>
    TRY(match_mp_tac every_var_mono>>full_simp_tac(srw_ss())[in_clash_sets_def]>>
      HINT_EXISTS_TAC>>srw_tac[][]>>full_simp_tac(srw_ss())[in_clash_sets_def])>>
    TRY( match_mp_tac every_var_mono>>full_simp_tac(srw_ss())[in_clash_sets_def]>>
    full_simp_tac(srw_ss())[CONJ_COMM]>>
    first_assum (match_exists_tac o concl)>>srw_tac[][]>>full_simp_tac(srw_ss())[in_clash_sets_def])>>
    res_tac>>
    TRY(qexists_tac`insert n' () (insert n () (union q' q))`>>
        full_simp_tac(srw_ss())[domain_union]>>metis_tac[domain_union])>>
    TRY(HINT_EXISTS_TAC>>metis_tac[domain_union])>>
    TRY(qexists_tac`insert n () (union q' q)`>>
        full_simp_tac(srw_ss())[domain_union]>>metis_tac[domain_union]))
QED

        full_simp_tac(srw_ss())[domain_union]>>metis_tac[domain_union]))
  >-
    (srw_tac[][]
    >-
      (HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
    >>
      qexists_tac`insert n () s`>>full_simp_tac(srw_ss())[])
  >-
    (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
    qexists_tac`insert n () live`>>full_simp_tac(srw_ss())[])
  >-
    (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
    qexists_tac`insert n () (insert n0 () live)`>>full_simp_tac(srw_ss())[])
  >-
    (rw[]>>
    (qexists_tac`union (insert n () LN) live`>>fs[domain_union]))
  >-
    (srw_tac[][]>-(HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])>>
     qexists_tac `insert n () (insert n0 () (insert n1 () (insert n2 () s0)))` >> fs[])
    );
*)

(* Proofs for check_clash_tree *)
Theorem check_col_INJ:
     check_col f numset = SOME (q,r) ⇒
  q = numset ∧
  INJ f (domain q) UNIV ∧
  domain r = IMAGE f (domain q)
Proof
  rw[check_col_def,GSYM MAP_MAP_o]
  >-
    (fs[INJ_DEF,domain_lookup,FORALL_PROD,GSYM MEM_toAList]>>rw[]>>
    fs[EL_ALL_DISTINCT_EL_EQ,MEM_EL,EL_MAP]>>
    metis_tac[FST])
  >>
    fs[domain_fromAList,EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList]>>
    fs[domain_lookup]
QED

Triviality wf_insert_swap:
  wf (t:num_set) ⇒
  insert (a:num) () (insert c () t) =
  insert (c:num) () (insert a () t)
Proof
  rw[]>>
  dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]>>
  fs[wf_insert,lookup_insert]>>
  rw[]
QED

(*TODO: This is true without wf*)
Triviality numset_list_insert_swap:
  ∀ls h live.
  wf live ⇒
  wf (numset_list_insert ls live) ∧
  numset_list_insert ls (insert h () live) =
  insert h () (numset_list_insert ls live)
Proof
  Induct>>fs[numset_list_insert_def]>>rw[]>>
  res_tac>>
  fs[wf_insert,wf_insert_swap]
QED

Theorem check_partial_col_INJ:
   ∀ls f live flive live' flive'.
  wf live ∧
  domain flive = IMAGE f (domain live) ∧
  INJ f (domain live) UNIV ∧
  check_partial_col f ls live flive = SOME (live',flive') ⇒
  wf live' ∧
  live' = numset_list_insert ls live ∧
  INJ f (domain live') UNIV ∧
  domain flive' = IMAGE f (domain live')
Proof
  Induct>>fs[check_partial_col_def,numset_list_insert_def]>>
  ntac 6 strip_tac>>
  TOP_CASE_TAC>>fs[]>>strip_tac
  >-
    (`h ∉ domain live` by fs[domain_lookup]>>
    `lookup (f h) flive = NONE` by
      (CCONTR_TAC>>
      `∃s. lookup(f h) flive = SOME s` by
        (Cases_on`lookup (f h) flive`>>fs[])>>
      fs[EXTENSION,domain_lookup]>>
      first_x_assum(qspec_then`f h` mp_tac)>>
      rw[EQ_IMP_THM]>>
      Cases_on`h=x'`>>fs[]>>
      Cases_on`lookup x' live = SOME ()`>>fs[]>>
      FULL_SIMP_TAC bool_ss[INJ_DEF]>>
      first_x_assum(qspecl_then[`h`,`x'`] assume_tac)>>
      fs[domain_lookup]>>
      metis_tac[])>>
    fs[]>>
    first_x_assum(qspecl_then[`f`,`insert h () live`,`insert (f h) () flive`,`live'`,`flive'`] mp_tac)>>
    fs[wf_insert]>>
    impl_tac>-
      (fs[INJ_DEF]>>rw[]>>fs[]
      >-
        (`f y ∈ domain flive` by fs[]>>
        fs[domain_lookup])
      >-
        (`f h ∈ domain flive` by
          (fs[]>>metis_tac[])>>
        fs[domain_lookup]))>>
    fs[numset_list_insert_swap])
  >>
    first_x_assum(qspecl_then[`f`,` live`,`flive`,`live'`,`flive'`] mp_tac)>>
    fs[]>>rw[]>>
    fs[GSYM numset_list_insert_swap]>>
    `insert h () live = live` by
      (dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]>>
      simp[wf_insert,lookup_insert]>>
      rw[])>>
    fs[]
QED

Triviality domain_insert_eq_union:
  domain (insert num () live) = domain (union (insert num () LN) live)
Proof
  fs[domain_union,domain_insert,UNION_COMM,EXTENSION]>>
  metis_tac[]
QED

Triviality domain_numset_list_insert_eq_union:
  domain (numset_list_insert ls live) = domain (union (numset_list_insert ls LN) live)
Proof
  fs[domain_union,domain_numset_list_insert,UNION_COMM]
QED

Triviality get_reads_exp_get_live_exp:
  ∀exp.
  set(get_reads_exp exp) = domain (get_live_exp exp)
Proof
  ho_match_mp_tac get_reads_exp_ind>>
  fs[get_reads_exp_def,get_live_exp_def]>>
  rw[EXTENSION]>>
  fs[MEM_FLAT,MEM_MAP]>>rw[EQ_IMP_THM]>>
  res_tac>>fs[]>>
  imp_res_tac domain_big_union_subset>>
  fs[SUBSET_DEF]>>
  Induct_on`ls`>>rw[]>>
  fs[domain_union,big_union_def]
  >-
    metis_tac[]
  >-
    (qexists_tac`get_reads_exp h`>>simp[]>>
    metis_tac[])>>
  fs[]>>
  metis_tac[]
QED

Triviality lookup_numset_list_insert:
  ∀ls n t.
  lookup n (numset_list_insert ls t) =
  if MEM n ls then SOME () else lookup n t
Proof
  Induct>>fs[numset_list_insert_def,lookup_insert]>>rw[]>>
  fs[]
QED

Triviality numset_list_insert_eq_UNION:
  ∀t t' ls.
  wf t ∧ wf t' ∧
  domain t' = set ls ⇒
  numset_list_insert ls t =
  union t' t
Proof
  rw[]>>
  dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]>>
  fs[numset_list_insert_swap,wf_union,EXTENSION]>>rw[]>>
  fs[lookup_numset_list_insert]>>
  IF_CASES_TAC
  >-
    (`n ∈ domain t'` by fs[]>>
    fs[lookup_union,domain_lookup])
  >>
  `n ∉ domain t'` by fs[]>>
  `lookup n t' = NONE` by
    metis_tac[domain_lookup,option_CASES]>>
  fs[lookup_union,domain_lookup]
QED

Triviality wf_delete_swap:
  wf t ⇒
  delete a (delete c t) =
  delete c (delete a t)
Proof
  rw[]>>
  dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]>>
  fs[wf_delete,lookup_delete]>>
  rw[]
QED

Triviality numset_list_delete_swap:
  ∀ls h live.
  wf live ⇒
  wf (numset_list_delete ls live) ∧
  numset_list_delete ls (delete h live) =
  delete h (numset_list_delete ls live)
Proof
  Induct>>fs[numset_list_delete_def]>>rw[]>>
  res_tac>>
  fs[wf_delete,wf_delete_swap]
QED

Triviality wf_numset_list_delete_eq:
  ∀ls t live.
  wf t ⇒
  FOLDR delete t ls = numset_list_delete ls t
Proof
  Induct>>fs[numset_list_delete_def,numset_list_delete_swap]
QED

Triviality wf_get_live_exp:
  ∀exp. wf(get_live_exp exp)
Proof
  ho_match_mp_tac get_live_exp_ind>>fs[get_live_exp_def,wf_insert,wf_def]>>
  rw[]>>
  fs[big_union_def]>>
  Induct_on`ls`>>rw[wf_def,wf_union]
QED

val start_tac =
  FULL_CASE_TAC>>fs[]>>Cases_on`x`>>
  imp_res_tac check_partial_col_INJ>>
  rfs[numset_list_delete_swap,domain_numset_list_delete,AND_IMP_INTRO]>>
  TRY(pop_assum mp_tac>>
  impl_keep_tac)>>
  fs[domain_numset_list_delete,domain_numset_list_insert,hide_def]>>
  rfs[GSYM domain_numset_list_insert_eq_union,wf_numset_list_delete_eq]>>
  fs[domain_numset_list_delete,domain_numset_list_insert,numset_list_delete_def,numset_list_insert_def];

val subset_tac =
  match_mp_tac (GEN_ALL INJ_less)>>
  HINT_EXISTS_TAC>>fs[domain_numset_list_insert_eq_union,SUBSET_DEF]>>
  simp[domain_union];

Theorem IMAGE_DIFF:
  INJ f (s UNION t) UNIV ⇒
  IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t
Proof
  fs [EXTENSION,INJ_DEF] \\ rw [] \\ metis_tac []
QED

Theorem clash_tree_colouring_ok:
  ∀prog f live flive livein flivein.
  wf_cutsets prog ∧
  wf live ∧
  domain flive = IMAGE f (domain live) ∧
  INJ f (domain live) UNIV ∧
  check_clash_tree f (get_clash_tree prog) live flive = SOME (livein,flivein) ⇒
  (*very slow when this is not hidden...*)
  hide(wf livein ∧
  INJ f (domain livein) UNIV ∧
  colouring_ok f prog live ∧
  livein = get_live prog live ∧
  domain flivein = IMAGE f (domain livein))
Proof
  ho_match_mp_tac get_clash_tree_ind>>
  fs[get_clash_tree_def]>>
  rw[]>>
  fs[check_clash_tree_def,colouring_ok_def,get_live_def,get_writes_def]>>rw[]
  >-
    fs[hide_def,numset_list_delete_def,check_partial_col_def]
  >-
    (start_tac>>
    CONJ_TAC>-
      subset_tac>>
    fs[LIST_TO_SET_MAP,INJ_IMP_IMAGE_DIFF])
  >- (*Inst*)
    (Cases_on`i`>>TRY(Cases_on`a`)>>
    fs[get_delta_inst_def,get_live_inst_def,get_writes_inst_def,check_clash_tree_def]
    >-
      fs[hide_def,check_partial_col_def,numset_list_delete_def]
    >-
      (start_tac
      >-
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF_single])>>
      fs[domain_union,UNION_COMM,DELETE_DEF])
    >-
      (Cases_on`r`>>FULL_CASE_TAC>>fs[check_clash_tree_def]>>start_tac>>
      TRY (*2 cases*)
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF_single,wf_insert_swap])
      >> (*2 cases*)
        (strip_tac>>CONJ_TAC>-
          (match_mp_tac (GEN_ALL INJ_less)>>
          qpat_x_assum`INJ f A B` kall_tac>>
          HINT_EXISTS_TAC>>fs[DELETE_DEF])>>
        fs[domain_union,UNION_COMM]))
    >-
      (start_tac>-
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF_single])
      >>
      fs[domain_union,UNION_COMM,DELETE_DEF,INSERT_UNION_EQ])
    >-
      (start_tac>-
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF_single])
      >>
      fs[domain_union,UNION_COMM,DELETE_DEF,INSERT_UNION_EQ])
    >-
      (start_tac>-
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF])
      >>
      fs[domain_union,UNION_COMM,DELETE_DEF,INSERT_UNION_EQ,DIFF_UNION]>>
      rw[]>>
      `{n ; n0} = {n} ∪ {n0} ∧ {n0;n} = {n} ∪ {n0}` by fs[EXTENSION]>>
      fs[GSYM DIFF_UNION])
    >-
      (start_tac>-
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF])
      >>
      fs[domain_union,UNION_COMM,DELETE_DEF,INSERT_UNION_EQ,DIFF_UNION]>>
      rw[]>>
      `{n ; n0} = {n} ∪ {n0} ∧ {n0;n} = {n} ∪ {n0}` by fs[EXTENSION]>>
      fs[GSYM DIFF_UNION])
    >-
      (start_tac>-
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF])
      >>
      `n2 INSERT n1 INSERT n0 INSERT domain live DIFF {n;n2} =
       n2 INSERT n1 INSERT n0 INSERT domain live DIFF {n}` by
         (rw[EXTENSION,EQ_IMP_THM]>>fs[])>>
      fs[domain_union,UNION_COMM,DELETE_DEF,INSERT_UNION_EQ]>>rw[]>>
      `{ n ; n0} = {n} ∪ {n0}` by fs[EXTENSION]>>
      fs[GSYM DIFF_UNION]
      >-
        (match_mp_tac (GEN_ALL INJ_less)>>fs[]>>
        ntac 2 (qpat_x_assum`INJ f A B` kall_tac)>>
        HINT_EXISTS_TAC>>
        fs[])
      >>
        DEP_REWRITE_TAC[spt_eq_thm]>>rw[wf_insert,wf_delete,lookup_insert,lookup_delete])
    >-
      (start_tac>-
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF]) >>
      fs[domain_union,UNION_COMM,DELETE_DEF,INSERT_UNION_EQ]>>rw[]>>
      fs[GSYM DIFF_UNION] >>
      `!n n0:num. { n ; n0} = {n} ∪ {n0}` by fs[EXTENSION]>> fs [] >>
      fs [AC UNION_COMM UNION_ASSOC])
    >-
      (start_tac>-
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF]) >>
      fs[domain_union,UNION_COMM,DELETE_DEF,INSERT_UNION_EQ]>>rw[]>>
      fs[GSYM DIFF_UNION] >>
      `!n n0:num. { n ; n0} = {n} ∪ {n0}` by fs[EXTENSION]>> fs [] >>
      fs [AC UNION_COMM UNION_ASSOC])
    >- (* Mem *)
      (Cases_on`m`>>fs[check_clash_tree_def,get_delta_inst_def,get_live_inst_def,get_writes_inst_def]>>
      start_tac>>
      fs[INJ_IMP_IMAGE_DIFF_single]>>
      (*2 cases*)
      TRY subset_tac>>
      TRY (*2 cases*)
        (CONJ_TAC>-
          subset_tac>>
        fs[INJ_IMP_IMAGE_DIFF_single,wf_insert_swap])>>
      (strip_tac>>CONJ_TAC>-
          (match_mp_tac (GEN_ALL INJ_less)>>
          qpat_x_assum`INJ f A B` kall_tac>>
          HINT_EXISTS_TAC>>fs[DELETE_DEF])>>
      fs[domain_union,UNION_COMM]))
    >- (* FP *)
      (Cases_on`f'`>>
      fs[check_clash_tree_def,get_delta_inst_def,get_live_inst_def,get_writes_def,get_writes_inst_def]>>
      rw[]>>
      fs[check_clash_tree_def,get_delta_inst_def,get_live_inst_def,get_writes_def,get_writes_inst_def]>>
      TRY(start_tac>>
      (rw[]>- subset_tac >> fs[INJ_IMP_IMAGE_DIFF,domain_union, AC UNION_COMM UNION_ASSOC]))>>
      (* One last goal *)
      `!n n0:num. { n ; n0} = {n} ∪ {n0}` by fs[EXTENSION]>>
      fs[AC UNION_COMM UNION_ASSOC,wf_insert_swap,wf_delete_swap]))
  >-
    (start_tac
    >-
      (CONJ_TAC>-
        subset_tac>>
      fs[INJ_IMP_IMAGE_DIFF_single])
    >>
    strip_tac>>
    fs[domain_union,UNION_COMM,get_reads_exp_get_live_exp,DELETE_DEF]>>
    match_mp_tac numset_list_insert_eq_UNION>>
    fs[get_reads_exp_get_live_exp,wf_delete,wf_get_live_exp])
  >-
    (start_tac>>strip_tac>>
    fs[domain_union,UNION_COMM,get_reads_exp_get_live_exp,DELETE_DEF]
    >-
      subset_tac>>
    fs[INJ_IMP_IMAGE_DIFF_single])
  >-
    (start_tac>>
    CONJ_TAC>-
      metis_tac[INSERT_UNION_EQ,UNION_COMM,domain_union,get_reads_exp_get_live_exp]>>
    AP_TERM_TAC>>
    match_mp_tac numset_list_insert_eq_UNION>>
    fs[get_reads_exp_get_live_exp,wf_delete,wf_get_live_exp])
  >-
    (*Seq*)
    (EVERY_CASE_TAC>>fs[wf_cutsets_def]>>
    res_tac>>
    rpt (qpat_x_assum `!P. Q` kall_tac)>>
    fs[hide_def]>>
    metis_tac[])
  >-
    (*If*)
    (EVERY_CASE_TAC>>fs[check_clash_tree_def]>>
    EVERY_CASE_TAC>>fs[]>>
    fs[wf_cutsets_def]>>res_tac>>
    ntac 2(last_x_assum kall_tac)>>
    fs[hide_def]>>
    (fs[numset_list_delete_def]>>
    qpat_x_assum`A=SOME x`mp_tac>>
    simp[Once check_partial_col_def]>>
    strip_tac>>
    rveq>>
    qpat_x_assum`wf A` mp_tac>>
    drule check_partial_col_INJ>>
    rpt (disch_then drule)>>
    strip_tac>>
    drule check_partial_col_INJ>>
    rpt (disch_then drule)>>
    ntac 2 strip_tac>>
    fs[]>>rw[]
    >-
      (match_mp_tac (GEN_ALL INJ_less)>>
      HINT_EXISTS_TAC>>
      fs[SUBSET_DEF,domain_numset_list_insert,domain_union]>>
      rw[]>>fs[toAList_domain,domain_lookup,lookup_difference]>>
      Cases_on`lookup x (get_live prog live)`>>fs[])>>
    fs[numset_list_insert_def,wf_insert_swap]>>
    dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]>>
    fs[wf_insert,wf_union,lookup_insert,lookup_numset_list_insert,toAList_domain,domain_lookup,lookup_difference,lookup_union]>>rw[]>>
    FULL_CASE_TAC>>fs[])
    >-
      (Cases_on`lookup n' (get_live prog' live)`>>fs[])
    >>
      Cases_on`lookup n (get_live prog' live)`>>fs[])
  >-
    metis_tac[wf_cutsets_def]
  >-
    (
    Cases_on `numset` >>
    EVERY_CASE_TAC>>fs[]>>
    imp_res_tac check_col_INJ>>
    fs[numset_list_delete_def]>>
    imp_res_tac check_partial_col_INJ>>
    rpt (qpat_x_assum `!P. Q` kall_tac)>>
    rfs[AND_IMP_INTRO]>>
    fs[hide_def,numset_list_insert_def,wf_cutsets_def,wf_names_def,wf_union])
  >- (* Install *)
    (
    fs[case_eq_thms,list_insert_def,wf_cutsets_def]>>
    drule check_partial_col_INJ>>
    rpt(disch_then drule) >>
    Cases_on `v''` >>
    rpt(disch_then drule) >>
    disch_then assume_tac >>
    fs[numset_list_insert_def,domain_union]>>
    drule check_col_INJ>>rw[]>>
    qpat_x_assum`wf _` mp_tac>>
    drule check_partial_col_INJ>>
    rpt(disch_then drule)>>
    rw[]>>
    fs[numset_list_delete_def]>>
    qpat_x_assum`wf_names numset` assume_tac>>
    `wf (union (FST numset) (SND numset))` by
      fs[wf_names_def,wf_union] >>
    drule check_partial_col_INJ>>
    rpt (disch_then drule)>>
    rw[hide_def]
    >-
      (fs[domain_numset_list_insert]>>
      match_mp_tac (GEN_ALL INJ_less)>>
      asm_exists_tac>>fs[domain_union]>>
      metis_tac[SUBSET_UNION,UNION_COMM,UNION_ASSOC])
    >-
      (fs[GSYM INSERT_SING_UNION])
    >>
      fs[numset_list_insert_def])
  >- (* CBW *)
    (fs[case_eq_thms,numset_list_delete_def,wf_cutsets_def]>>
    drule check_partial_col_INJ>> rpt (disch_then drule)>>
    rw[hide_def,numset_list_insert_def,list_insert_def]>>
    fs[domain_insert])
  >- (* DBW *)
    (fs[case_eq_thms,numset_list_delete_def,wf_cutsets_def]>>
    drule check_partial_col_INJ>> rpt (disch_then drule)>>
    rw[hide_def,numset_list_insert_def,list_insert_def]>>
    fs[domain_insert])
  >- (* FFI *)
    (EVERY_CASE_TAC>>fs[]>>
    imp_res_tac check_col_INJ>>
    fs[numset_list_delete_def]>>
    imp_res_tac check_partial_col_INJ>>
    rpt (qpat_x_assum `!P. Q` kall_tac)>>
    rfs[AND_IMP_INTRO]>>
    fs[hide_def,numset_list_insert_def,wf_cutsets_def,wf_names_def,wf_union])
  >- (* Raise *)
    (start_tac>>
    fs[numset_list_delete_def,numset_list_insert_def]>>
    metis_tac[INSERT_SING_UNION,UNION_COMM])
  >- (* Return *)
    (start_tac>>
    fs[numset_list_delete_def,numset_list_insert_def]>>
    `domain live ∪ {num1;num2} = num1 INSERT num2 INSERT domain live` by
      (fs[EXTENSION]>>metis_tac[])>>
    fs[] >> metis_tac[INSERT_SING_UNION,UNION_ASSOC,UNION_COMM])
  >- (* Tick *)
    (start_tac>>
    fs[numset_list_delete_def,numset_list_insert_def])
  >- (* LocValue *)
    (start_tac>>
    fs[numset_list_delete_def,numset_list_insert_def,domain_union,DELETE_DEF,UNION_COMM]>>
    CONJ_TAC>- subset_tac>>
    fs[INJ_IMP_IMAGE_DIFF_single])
  >- (* Set *)
    (start_tac>>
    fs[numset_list_delete_def,numset_list_insert_def,domain_union,DELETE_DEF,UNION_COMM,get_reads_exp_get_live_exp]>>
    match_mp_tac numset_list_insert_eq_UNION>>
    fs[wf_get_live_exp,get_reads_exp_get_live_exp])
  >- (* OpCurrHeap *)
    (start_tac>>
    fs[numset_list_delete_def,numset_list_insert_def,domain_union,DELETE_DEF,
       UNION_COMM,get_reads_exp_get_live_exp]>>
    ‘INJ f (domain live DIFF {dst}) 𝕌(:num)’ by
      (qpat_x_assum ‘INJ f (domain live ∪ {dst}) 𝕌(:num)’ mp_tac
       \\ rpt (pop_assum kall_tac)
       \\ rewrite_tac [INJ_DEF,IN_DIFF,IN_UNION,NOT_IN_EMPTY,IN_UNIV,IN_INSERT]
       \\ metis_tac [])
    \\ gvs [IMAGE_DIFF] \\ rw []
    \\ rpt (pop_assum mp_tac)
    \\ rewrite_tac [INJ_DEF,IN_UNION,IN_INSERT]
    \\ metis_tac [])
  >- ((* StoreConsts *)
    start_tac
    >- (
      CONJ_TAC>- (
        match_mp_tac (GEN_ALL INJ_less)>>
        asm_exists_tac>>simp[SUBSET_DEF])>>
      simp[IMAGE_DIFF])>>
    strip_tac>>
    CONJ_TAC>- (
      simp[domain_union,UNION_COMM]>>
      match_mp_tac (GEN_ALL INJ_less)>>
      qpat_x_assum`INJ _ (domain _ ∪ _) _` assume_tac>>
      asm_exists_tac>>
      simp[SUBSET_DEF])>>
    dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]>>
    fs[wf_insert,lookup_insert,lookup_delete]>>
    CONJ_TAC>-
      metis_tac[wf_insert,wf_delete]>>
    rw[]>>fs[])
  >- ((*ShareInst Store*)
      start_tac >>
      fs[numset_list_insert_def,domain_union,
        UNION_COMM,get_reads_exp_get_live_exp] >>
      conj_tac >- (
        drule_then irule INJ_less >> rw[] >>
        metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS]) >>
      CONV_TAC $ RHS_CONV $ SCONV[Once insert_union] >>
      simp[union_assoc] >>
      CONV_TAC $ RHS_CONV $ RATOR_CONV $ RAND_CONV $
        REWRITE_CONV[Once union_num_set_sym] >>
      simp[union_insert_LN] >>
      fs[GSYM numset_list_insert_def] >>
      irule numset_list_insert_eq_UNION >>
      rw[IMAGE_DEF,get_reads_exp_get_live_exp] >>
      metis_tac[wf_insert,wf_get_live_exp])
  >- ((*ShareInst Store8*)
      start_tac >>
      fs[domain_union,UNION_COMM,get_reads_exp_get_live_exp] >>
      conj_tac >- (
        drule_then irule INJ_less >> rw[] >>
        metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS]) >>
      CONV_TAC $ RHS_CONV $ SCONV[Once insert_union] >>
      simp[union_assoc] >>
      CONV_TAC $ RHS_CONV $ RATOR_CONV $ RAND_CONV $
        REWRITE_CONV[Once union_num_set_sym] >>
      simp[union_insert_LN] >>
      fs[GSYM numset_list_insert_def] >>
      irule numset_list_insert_eq_UNION >>
      rw[IMAGE_DEF,get_reads_exp_get_live_exp] >>
      metis_tac[wf_insert,wf_get_live_exp])
  >- ((*ShareInst Store32*)
      start_tac >>
      fs[domain_union,UNION_COMM,get_reads_exp_get_live_exp] >>
      conj_tac >- (
        drule_then irule INJ_less >> rw[] >>
        metis_tac[SUBSET_UNION,SUBSET_OF_INSERT,SUBSET_TRANS]) >>
      CONV_TAC $ RHS_CONV $ SCONV[Once insert_union] >>
      simp[union_assoc] >>
      CONV_TAC $ RHS_CONV $ RATOR_CONV $ RAND_CONV $
        REWRITE_CONV[Once union_num_set_sym] >>
      simp[union_insert_LN] >>
      fs[GSYM numset_list_insert_def] >>
      irule numset_list_insert_eq_UNION >>
      rw[IMAGE_DEF,get_reads_exp_get_live_exp] >>
      metis_tac[wf_insert,wf_get_live_exp])
  >- ((*ShareInst Load/Load8/Load32*)
    start_tac
    >- (
      conj_tac >- (
        irule INJ_less >>
        last_assum $ irule_at (Pos last) >>
        simp[]) >>
      simp[IMAGE_DIFF]) >>
    strip_tac >>
    rename1`ShareInst op prog exp`>>
    `get_writes (ShareInst op prog exp) = insert prog () LN` by (
      simp[DefnBase.one_line_ify NONE get_writes_def,AllCaseEqs()]>>
      Cases_on `op` >>
      fs[]) >>
    fs[domain_union,UNION_COMM,get_reads_exp_get_live_exp] >>
    conj_tac >- (
      irule INJ_less >>
      irule_at (Pos hd) $ SUBSET_REFL >>
      simp[DELETE_DEF]) >>
    irule numset_list_insert_eq_UNION >>
    simp[get_reads_exp_get_live_exp,wf_get_live_exp,wf_delete] )
  >- (*Call*)
    (Cases_on`ret`>>fs[]
    >-
      (fs[check_clash_tree_def,hide_def,wf_cutsets_def,colouring_ok_def,get_live_def,get_writes_def]>>
      imp_res_tac check_col_INJ>>
      fs[]>>
      rveq>>fs[]>>
      metis_tac[numset_list_insert_swap,wf_def])
    >>
    PairCases_on`x`>>Cases_on`h`>>fs[check_clash_tree_def,colouring_ok_def,get_live_def]
    >-
      (EVERY_CASE_TAC>>
      fs[wf_cutsets_def]>>
      res_tac>>
      rpt (qpat_x_assum `!P. Q` kall_tac)>>
      fs[hide_def,numset_list_delete_def]>>
      rveq>>
      imp_res_tac check_col_INJ>>
      rveq>>
      fs[numset_list_insert_swap,wf_def,
      wf_names_def,wf_union,domain_union,
      domain_numset_list_insert] >>
      metis_tac[UNION_COMM,UNION_ASSOC])
    >>
      PairCases_on`x`>>fs[check_clash_tree_def]>>
      EVERY_CASE_TAC>>
      fs[wf_cutsets_def,check_clash_tree_def]>>
      TRY(EVERY_CASE_TAC>>fs[])>>
      res_tac>>
      rpt (qpat_x_assum `!P. Q` kall_tac)>>
      fs[hide_def,numset_list_delete_def]>>
      rveq>>
      imp_res_tac check_col_INJ>>
      rveq>>
      fs[numset_list_insert_swap,wf_def,
      wf_names_def,wf_union,domain_union,
      domain_numset_list_insert] >>
      metis_tac[UNION_COMM,UNION_ASSOC]
      )
QED

(*Actually, it should probably be exactly 0,2,4,6...*)
Definition even_starting_locals_def:
  even_starting_locals (locs:'a word_loc num_map) ⇔
    ∀x. x ∈ domain locs ⇒ is_phy_var x
End

fun rm_let tm = tm|> SIMP_RULE std_ss [LET_THM];

Triviality get_forced_tail_split:
  ∀c p ls ls'.
  get_forced c p (ls++ls') =
  get_forced c p ls ++ ls'
Proof
  ho_match_mp_tac get_forced_ind>>rw[get_forced_def]>>
  EVERY_CASE_TAC>>fs[]
QED

Triviality EVERY_get_forced:
  EVERY P (get_forced c p ls) ⇔
  EVERY P (get_forced c p []) ∧ EVERY P ls
Proof
  Q.SPECL_THEN [`c`,`p`,`[]`,`ls`] assume_tac get_forced_tail_split>>
  fs[]
QED

Triviality get_forced_pairwise_distinct:
  ∀c prog ls.
  EVERY (λx,y. x ≠ y) ls ⇒
  EVERY (λx,y. x ≠ y) (get_forced c prog ls)
Proof
  ho_match_mp_tac get_forced_ind>>rw[get_forced_def]>>
  EVERY_CASE_TAC>>fs[]
QED

Triviality get_forced_in_get_clash_tree:
  ∀prog c.
  EVERY (λx,y.in_clash_tree (get_clash_tree prog) x ∧ in_clash_tree (get_clash_tree prog) y) (get_forced c prog [])
Proof
  ho_match_mp_tac get_clash_tree_ind>>
  fs[]>>rw[get_clash_tree_def,get_forced_def,in_clash_tree_def]
  >-
    (every_case_tac>>fs[get_delta_inst_def,in_clash_tree_def]>>
    rfs[]>>fs[])
  >-
    (simp[Once EVERY_get_forced]>>
    rw[]>>
    fs[EVERY_MEM,FORALL_PROD]>>
    metis_tac[])
  >-
    (every_case_tac>>fs[in_clash_tree_def,get_forced_def]>>
    simp[Once EVERY_get_forced]>>
    rw[]>>
    fs[EVERY_MEM,FORALL_PROD]>>
    metis_tac[])
  >-
    (every_case_tac>>fs[in_clash_tree_def,get_forced_def]>>
    Cases_on`r`>>
    simp[get_forced_def,Once EVERY_get_forced]>>
    rw[]
    >-
      (fs[EVERY_MEM,FORALL_PROD]>>metis_tac[])
    >>
      (simp[Once EVERY_get_forced]>>
      fs[EVERY_MEM,FORALL_PROD]>>metis_tac[]))
QED

Theorem select_reg_alloc_correct:
    !alg spillcosts k heu_moves tree forced fs.
    EVERY (\r1,r2. in_clash_tree tree r1 /\ in_clash_tree tree r2) forced ==>
    ?spcol livein flivein.
    select_reg_alloc alg spillcosts k heu_moves tree forced fs = M_success spcol /\
    check_clash_tree (sp_default spcol) tree LN LN = SOME (livein, flivein) /\
    (!r. in_clash_tree tree r ==>
      r IN domain spcol /\
      if is_phy_var r then
        sp_default spcol r = r DIV 2
      else if is_stack_var r then
        k <= (sp_default spcol r)
      else
        T
    ) /\
    (!r. r IN domain spcol ==> in_clash_tree tree r) /\
    EVERY (\r1,r2. (sp_default spcol) r1 = (sp_default spcol) r2 ==> r1 = r2) forced
Proof
    simp [select_reg_alloc_def] >> rpt strip_tac >>
    qabbrev_tac`algg = if alg ≤ 1 then Simple else IRC` >>
    drule linear_scan_reg_alloc_correct >>
    disch_then (qspecl_then [`k`, `heu_moves`] assume_tac) >>
    drule reg_alloc_correct >>
    disch_then (qspecl_then [`algg`, `spillcosts`, `k`, `heu_moves`] assume_tac) >>
    rw [] >> fs []
QED

(*Prove the full correctness theorem for word_alloc*)
Theorem word_alloc_correct:
  ∀fc c alg prog k col_opt st.
  even_starting_locals st.locals ∧
  wf_cutsets prog
  ⇒
  ∃perm'.
  let (res,rst) = evaluate(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (res',rcst) = evaluate(word_alloc fc c alg k prog col_opt,st) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    case res of
      NONE => T
    | SOME _ => rst.locals = rcst.locals
Proof
  srw_tac[][]>>
  qpat_abbrev_tac`cprog = word_alloc _ _ _ _ _ _`>>
  full_simp_tac(srw_ss())[word_alloc_def]>>
  pop_assum mp_tac>>LET_ELIM_TAC>>
  pop_assum mp_tac>>reverse TOP_CASE_TAC>>strip_tac
  >-
    (fs[oracle_colour_ok_def]>>
    EVERY_CASE_TAC>>fs[]>>
    fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]>>
    Cases_on`x''`>>
    Q.ISPECL_THEN [`prog`,`total_colour x'`,`LN:num_set`,`LN:num_set`,`q`,`r`] mp_tac clash_tree_colouring_ok>>
    fs[wf_def,hide_def]>> rw[]>>
    Q.ISPECL_THEN[`prog`,`st`,`st`,`total_colour x'`,`LN:num_set`] mp_tac evaluate_apply_colour>>
    impl_tac>-
      (fs[word_state_eq_rel_def,strong_locals_rel_def,even_starting_locals_def]>>rw[]>>
      fs[domain_lookup,every_even_colour_def,total_colour_def]>>
      last_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
      fs[GSYM MEM_toAList]>>FULL_CASE_TAC>>fs[]>>
      fs[EVERY_MEM,FORALL_PROD,GSYM MEM_toAList]>>
      first_x_assum drule>>
      simp[]>>
      `?k. n = 2*k` by
        metis_tac[is_phy_var_def,EVEN_MOD2,EVEN_EXISTS]>>
      metis_tac[TWOxDIV2])>>
    srw_tac[][]>>
    qexists_tac`perm'`>>srw_tac[][]>>
    full_simp_tac(srw_ss())[LET_THM]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[])
  >>
  `EVERY (λx,y.in_clash_tree tree x ∧ in_clash_tree tree y) forced` by
    (unabbrev_all_tac>>fs[get_forced_in_get_clash_tree])>>
  drule select_reg_alloc_correct>>
  disch_then(qspecl_then [`alg`,`spillcosts`,`k`,`heu_moves`,`fs`] assume_tac)>>rfs[]>>fs[]>>
  Q.ISPECL_THEN[`prog`,`st`,`st`,`total_colour spcol`,`LN:num_set`] mp_tac evaluate_apply_colour>>
  impl_tac>-
    (rpt strip_tac
    >-
      (fs[total_colour_alt]>>
      `INJ (\x. 2n*x) UNIV UNIV` by fs[INJ_DEF]>>
      drule check_clash_tree_INJ >>
      disch_then(qspecl_then[`tree`,`sp_default spcol`,`LN`,`LN`,`LN`] assume_tac)>>
      rfs[]>>
      drule clash_tree_colouring_ok>>
      fs[GSYM total_colour_alt]>>
      disch_then(qspecl_then[`total_colour spcol`,`LN`,`LN`,`livein`,`gliveout`] assume_tac)>>
      rfs[wf_def]>>
      fs[hide_def])
    >-
      fs[word_state_eq_rel_def]
    >>
      fs[strong_locals_rel_def,even_starting_locals_def]>>rw[]>>
      fs[domain_lookup,total_colour_def]>>
      TOP_CASE_TAC>>fs[]>>
      rpt(first_x_assum(qspec_then`n` assume_tac))>>
      rfs[]>>fs[sp_default_def]>>rfs[]>>
      metis_tac[is_phy_var_def,EVEN_MOD2,EVEN_EXISTS,TWOxDIV2])
  >>
  rw[]>>
  qexists_tac`perm'`>>rw[]>>
  fs[]>>
  FULL_CASE_TAC>>fs[]
QED

Triviality apply_colour_exp_I:
  apply_colour_exp I exp = exp
Proof
 `∀f exp.
  f = I ⇒
  apply_colour_exp f exp = exp` by (
  ho_match_mp_tac apply_colour_exp_ind>>
  rw[]>>
  fs[MAP_EQ_ID])>>
  simp[]
QED

(* Dead code removal *)
Triviality strong_locals_rel_I_word_exp:
  word_exp st exp = SOME res ∧
   strong_locals_rel I (domain (union (get_live_exp exp) live)) st.locals t ⇒
   word_exp (st with locals := t) exp = SOME res
Proof
  rw[]>>drule apply_colour_exp_lemma>>
   disch_then (qspecl_then [`st with locals:= t`,`I`] mp_tac)>>
   rfs[word_state_eq_rel_def,apply_colour_exp_I]>>
   impl_tac>>fs[]>>
   fs[strong_locals_rel_def,domain_union]
QED

Triviality strong_locals_rel_insert_notin:
  strong_locals_rel f live s t ∧
  n ∉ live ⇒
  strong_locals_rel f live (insert n v s) t
Proof
  rw[strong_locals_rel_def,lookup_insert]>>
  Cases_on`n'=n`>>fs[]
QED

Triviality strong_locals_rel_I_get_var:
  get_var x st = SOME v ∧
  strong_locals_rel I (x INSERT live) st.locals t ⇒
  get_var x (st with locals:=t) = SOME v
Proof
  fs[strong_locals_rel_def,get_var_def]
QED

Triviality strong_locals_rel_I_get_vars:
  ∀ls live st t vs.
  (∀x. MEM x ls ⇒ x ∈ live) ∧
  strong_locals_rel I live st.locals t ∧
  get_vars ls st = SOME vs ⇒
  get_vars ls (st with locals:=t) = SOME vs
Proof
  Induct>>rw[get_vars_def]>>
  pop_assum mp_tac>>ntac 2 TOP_CASE_TAC>>
  strip_tac>>
  `get_var h (st with locals:=t) = SOME x` by
    fs[get_var_def,strong_locals_rel_def]>>
  fs[]>>
  `!x. MEM x ls ⇒ x ∈ live` by fs[]>>
  first_assum drule>>
  strip_tac >> res_tac>>
  fs[]
QED

Triviality strong_locals_rel_I_cut_envs:
  strong_locals_rel I (domain (FST cutset) ∪ domain (SND cutset)) st.locals t ∧
  cut_envs cutset st.locals = SOME x ⇒
  cut_envs cutset t = SOME x
Proof
  fs[strong_locals_rel_def,SUBSET_DEF,cut_envs_def,cut_names_def]>>
  rw[]
  >- (
    DEP_REWRITE_TAC [spt_eq_thm]>>
    simp[wf_union,lookup_union,lookup_inter]>>
    rw[]>>every_case_tac>>fs[domain_lookup]>>
    res_tac>>fs[])
  >>
    metis_tac[domain_lookup]
QED


Triviality strong_locals_rel_I_cut_env:
  strong_locals_rel I (domain (FST cutset) ∪ domain (SND cutset)) st.locals t ∧
  cut_env cutset st.locals = SOME x ⇒
  cut_env cutset t = SOME x
Proof
  fs[cut_env_def]>> rw[] >>
  pop_assum mp_tac >>
  TOP_CASE_TAC >> fs[] >>
  imp_res_tac strong_locals_rel_I_cut_envs >>
  fs[]
QED


val rm_tac =
    EVERY_CASE_TAC>>fs[]>>
    rpt var_eq_tac>>fs[evaluate_def,state_component_equality,set_var_def]>>
    TRY(qpat_x_assum`A=rst.locals` sym_sub_tac)>>fs[]
    >-
      (match_mp_tac strong_locals_rel_insert_notin>>fs[domain_lookup])
    >>
      imp_res_tac strong_locals_rel_I_word_exp>>
      fs[state_component_equality,strong_locals_rel_def,lookup_insert,domain_union]>>rw[]

Triviality get_vars_eq:
  (set ls) SUBSET domain st.locals ==> ?z. get_vars ls st = SOME z /\
                                             z = MAP (\x. THE (lookup x st.locals)) ls
Proof
  Induct_on`ls`>>full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[domain_lookup]
QED

Triviality get_vars_exists:
  ∀ls.
  (∃z. get_vars ls st = SOME z) ⇔
  set ls ⊆ domain st.locals
Proof
  Induct>>fs[get_vars_def,get_var_def]>>rw[]>>
  EVERY_CASE_TAC>>fs[domain_lookup]
QED

Triviality strong_locals_rel_I_insert_insert:
  strong_locals_rel I (live DELETE p) A B ∧
  v = v' ⇒
  strong_locals_rel I live (insert p v A) (insert p v' B)
Proof
  rw[strong_locals_rel_def,lookup_insert]>>
  IF_CASES_TAC>>fs[]
QED

Theorem evaluate_remove_dead:
  ∀prog live prog' livein st t res rst.
  strong_locals_rel I (domain livein) st.locals t ∧
  evaluate (prog,st) = (res,rst) ∧
  remove_dead prog live = (prog',livein) ∧
  res ≠ SOME Error ⇒
  ∃t'.
    evaluate(prog',st with locals := t) = (res,rst with locals:=t') ∧
    (case res of
      NONE => strong_locals_rel I (domain live) rst.locals t'
    | SOME _ => rst.locals = t')
Proof
  ho_match_mp_tac remove_dead_ind>>rw[]>>
  fs[remove_dead_def]>>
  rpt var_eq_tac>>fs[get_live_def,evaluate_def,state_component_equality,set_var_def]
  >-
    (var_eq_tac>>fs[])
  >- (* Move *)
    (qpat_x_assum`A=(res,rst)` mp_tac>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    qpat_x_assum`A=(prog',livein)` mp_tac>>
    IF_CASES_TAC>-
      (*Special case where everything happens to be not live*)
      (rw[]>>rpt var_eq_tac>>
      fs[evaluate_def,state_component_equality,set_vars_def,strong_locals_rel_def]>>
      imp_res_tac get_vars_length_lemma>>
      simp[lookup_alist_insert]>>
      ntac 2 strip_tac>>
      TOP_CASE_TAC>>simp[]>>
      rw[]>>
      `MEM n (MAP FST ls)` by
        (imp_res_tac ALOOKUP_MEM>>
        rfs[MEM_ZIP,MEM_EL]>>
        metis_tac[])>>
      fs[MEM_MAP,FILTER_EQ_NIL,EVERY_MEM]>>
      res_tac>>
      Cases_on`y`>>fs[domain_lookup])
    >>
      (* Normal case *)
      rw[]>>rpt var_eq_tac>>fs[evaluate_def]>>
      qmatch_goalsub_abbrev_tac`ALL_DISTINCT Z`>>
      `ALL_DISTINCT Z` by
        (qpat_x_assum `ALL_DISTINCT (MAP FST ls)` mp_tac>>
        fs[Abbr`Z`]>>
        rpt (pop_assum kall_tac)>>
        Induct_on`ls`>>fs[FORALL_PROD]>>rw[]>>
        fs[MEM_MAP,FORALL_PROD,MEM_FILTER])>>
      simp[]>>
      qmatch_goalsub_abbrev_tac`get_vars A stt`>>
      imp_res_tac get_vars_exists>>
      `set A ⊆ domain stt.locals` by
        (unabbrev_all_tac>>
        fs[SUBSET_DEF,MEM_MAP,MEM_FILTER,EXISTS_PROD,strong_locals_rel_def,domain_numset_list_insert]>>
        rw[]>>
        fs[domain_lookup]>>
        fs[SUBSET_DEF,domain_lookup]>>
        metis_tac[MEM_MAP,SND])>>
      imp_res_tac get_vars_eq>>fs[]>>
      unabbrev_all_tac>>fs[set_vars_def,state_component_equality]>>
      qpat_x_assum`A=x` sym_sub_tac>>
      last_x_assum mp_tac>>
      qpat_x_assum`A ⊆ Z` mp_tac>>
      qpat_x_assum`A ⊆ Z` mp_tac>>
      qpat_x_assum`ALL_DISTINCT A` mp_tac>>
      qpat_x_assum`ALL_DISTINCT A` mp_tac>>
      rpt (pop_assum kall_tac)>>
      qid_spec_tac`live`>>
      Induct_on`ls`>>
      fs[numset_list_insert_def,FORALL_PROD,alist_insert_def]>>rw[]>>
      fs[alist_insert_def]
      >-
        (match_mp_tac strong_locals_rel_I_insert_insert>>rw[]
        >-
          (first_x_assum(qspec_then`delete p_1 live` mp_tac)>>
          fs[AND_IMP_INTRO]>>
          qpat_abbrev_tac`A = FILTER P ls`>>
          qpat_abbrev_tac`Z = FILTER P ls`>>
          `A=Z` by
            (fs[Abbr`A`,Abbr`Z`,lookup_delete]>>
            qpat_x_assum`¬(MEM p_1 (MAP FST ls))` mp_tac>>
            rpt (pop_assum kall_tac)>>
            Induct_on`ls`>>fs[FORALL_PROD])>>
          fs[]>>impl_tac>>
          fs[domain_numset_list_insert,domain_FOLDR_delete,DELETE_DEF,strong_locals_rel_def]>>
          rw[]>>
          first_assum match_mp_tac>>fs[MEM_MAP,MEM_FILTER]>>
          Cases_on`y`>>fs[EXISTS_PROD]>>
          metis_tac[])
        >>
          fs[domain_lookup,domain_numset_list_insert,domain_FOLDR_delete,strong_locals_rel_def,numset_list_insert_def]>>
          pop_assum(qspecl_then[`p_2`,`v`] mp_tac)>>fs[])
      >>
        match_mp_tac strong_locals_rel_insert_notin>>
        fs[domain_lookup])
  >- (* Inst *)
    (Cases_on`i`>>fs[inst_def]
    >-
      (fs[remove_dead_inst_def,get_live_inst_def]>>
      rpt var_eq_tac>>fs[evaluate_def,state_component_equality])
    >-
      (fs[assign_def]>>EVERY_CASE_TAC>>fs[]>>
      rpt var_eq_tac>>fs[evaluate_def,set_var_def,remove_dead_inst_def]>>
      fs[strong_locals_rel_insert_notin,state_component_equality,domain_lookup]>>
      fs[inst_def,assign_def]>>
      imp_res_tac strong_locals_rel_I_word_exp>>
      fs[get_live_exp_def,big_union_def]>>
      res_tac>>
      fs[set_var_def,state_component_equality,strong_locals_rel_def,lookup_insert,get_live_inst_def]>>
      rw[])
    >-
      (Cases_on`a`>>fs[assign_def]>>
      TRY
        (EVERY_CASE_TAC>>fs[]>>
        rpt var_eq_tac>>fs[evaluate_def,set_var_def,remove_dead_inst_def]>>
        fs[strong_locals_rel_insert_notin,state_component_equality,domain_lookup]>>
        fs[inst_def,assign_def]>>
        imp_res_tac strong_locals_rel_I_word_exp>>
        fs[big_union_def,get_live_exp_def,get_live_inst_def,domain_union,INSERT_UNION_EQ]>>
        FULL_SIMP_TAC std_ss [Once (GSYM domain_delete)]>>
        res_tac>>
        fs[set_var_def,state_component_equality,strong_locals_rel_def,lookup_insert]>>rw[]>>NO_TAC)
      >>
        (* 3 cases for the extra insts *)
        (fs[]>>EVERY_CASE_TAC>>
        fs[remove_dead_inst_def,set_var_def]>>
        rpt var_eq_tac>>fs[evaluate_def]>>
        fs[strong_locals_rel_insert_notin,state_component_equality,domain_lookup]>>
        fs[inst_def,get_live_inst_def]>>
        qmatch_goalsub_abbrev_tac`get_vars ls _`>>
        `get_vars ls (st with locals := t) = get_vars ls st` by
          (fs[]>>match_mp_tac strong_locals_rel_I_get_vars>>
          HINT_EXISTS_TAC>>fs[Abbr`ls`]>>
          metis_tac[])>>
        fs[set_var_def,state_component_equality,strong_locals_rel_def,lookup_insert]>>
        rw[]))
    >-
      (Cases_on`a`>>Cases_on`m`>>fs[assign_def]>>
      EVERY_CASE_TAC>>fs[]>>
      rpt var_eq_tac>>fs[evaluate_def,set_var_def,remove_dead_inst_def]>>
      fs[strong_locals_rel_insert_notin,state_component_equality,domain_lookup]>>
      fs[inst_def,assign_def,mem_load_def,mem_store_def]>>
      imp_res_tac strong_locals_rel_I_word_exp>>
      fs[big_union_def,get_live_exp_def,get_live_inst_def,domain_union,INSERT_UNION_EQ]>>
      FULL_SIMP_TAC std_ss [Once (GSYM domain_delete)]>>
      (*first 2 cases*)
      TRY(res_tac>>
        fs[set_var_def,state_component_equality,strong_locals_rel_def,lookup_insert]>>rw[]>>NO_TAC)
      (*next 2 cases*)
      >>
        (pop_assum(qspecl_then[`t`,`live`] mp_tac)>>impl_tac
        >-
          (fs[strong_locals_rel_def]>>metis_tac[])>>
        simp[]>>
        imp_res_tac strong_locals_rel_I_get_var>>
        pop_assum kall_tac>>
        pop_assum(qspecl_then[`t`,`domain live`] mp_tac)>>impl_tac
        >-
          (fs[strong_locals_rel_def]>>metis_tac[])>>
        fs[state_component_equality,strong_locals_rel_def]))
    >- (* FP *)
      (Cases_on`f`>>fs[assign_def]>>
      every_case_tac>>
      fs[remove_dead_inst_def]>>rw[]>>rfs[]>>
      fs[evaluate_def,state_component_equality,set_var_def,inst_def,get_live_inst_def,get_fp_var_def]>>
      fs[strong_locals_rel_insert_notin,state_component_equality,domain_lookup,set_fp_var_def]>>
      fs[strong_locals_rel_I_insert_insert]>>
      imp_res_tac strong_locals_rel_I_get_var >>
      fs[Once INSERT_COMM]>>
      imp_res_tac strong_locals_rel_I_get_var >>
      fs[set_fp_var_def,state_component_equality]>>
      metis_tac[strong_locals_rel_subset,SUBSET_OF_INSERT,strong_locals_rel_insert])
    )
  >- (* assign *)
    rm_tac
  >- (* get *)
    rm_tac
  >- (* OpCurrHeap *)
   (rm_tac \\ fs[evaluate_def,state_component_equality,set_var_def,word_exp_def,
       get_var_def,
       the_words_def,AllCaseEqs(),PULL_EXISTS,get_live_exp_def,big_union_def]>>
    first_x_assum (qspecl_then [‘t’,‘delete num live’] mp_tac) >>
    impl_tac >- (fs [domain_delete] \\ metis_tac []) >>
    strip_tac \\ fs [] \\ rw [lookup_insert])
  >- (* loc value *)
    rm_tac
  >- (* seq *)
    (rpt (pairarg_tac>>fs[])>>
    qpat_x_assum`A=(res,rst)` mp_tac>>IF_CASES_TAC>>fs[]>>
    rpt var_eq_tac>>fs[evaluate_def]
    >-
      (strip_tac>> first_x_assum drule>>
      disch_then drule>> simp[]>> strip_tac>>
      rw[]>>fs[evaluate_def])
    >>
      strip_tac>>first_x_assum drule>>
      disch_then drule>> simp[]>> strip_tac>>
      rw[]>>fs[state_component_equality,evaluate_def]>>
      FULL_CASE_TAC>>fs[])
  >- (*must terminate*)
    (rpt (pairarg_tac>>fs[])>>
    qpat_x_assum`A=(res,rst)` mp_tac>>EVERY_CASE_TAC>>fs[]>>
    rpt var_eq_tac>>fs[evaluate_def]>>
    first_x_assum (qspecl_then [`st with <|clock := MustTerminate_limit (:'a) ; termdep := st.termdep -1|>` ] mp_tac)>>
    fs[]>>disch_then drule>>rw[]>>fs[state_component_equality])
  >- (* if *)
    (rpt (pairarg_tac>>fs[])>>
    qpat_x_assum`A=(res,rst)` mp_tac>>
    ntac 4 (TOP_CASE_TAC>>fs[])>>
    rpt var_eq_tac>>
    Cases_on`ri`>>fs[get_var_imm_def]>>
    imp_res_tac strong_locals_rel_I_get_var>>
    TRY(first_x_assum(qspecl_then[`t`,`domain (union e2_live e3_live)`] mp_tac)>>
    impl_tac>-
      (fs[strong_locals_rel_def]>>
      metis_tac[]))>>
    rw[]>>fs[evaluate_def,get_var_imm_def]>>
    TRY(first_assum match_mp_tac>>fs[strong_locals_rel_def,domain_union]>>
    NO_TAC)>>
    last_assum match_mp_tac>>fs[strong_locals_rel_def,domain_union])
  >- (*call*)
    (qpat_x_assum`A=(res,rst)` mp_tac>>
    ntac 7 (TOP_CASE_TAC>>fs[])>>
    pairarg_tac>>fs[]>>
    rpt var_eq_tac>>fs[evaluate_def]>>
    `get_vars (MAP I args) (st with locals:=t) = SOME x` by
      (match_mp_tac strong_locals_rel_get_vars>>
      fs[]>>
      first_assum (match_exists_tac o concl)>>
      simp[domain_numset_list_insert,domain_union])>>
      fs[add_ret_loc_def]>>
    `cut_envs cutsets t = SOME x'` by
      (match_mp_tac (GEN_ALL strong_locals_rel_I_cut_envs)>>
      fs[]>>
      qexists_tac`st`>>fs[domain_numset_list_insert]>>
      fs[cut_env_def,domain_union]>>
      fs[strong_locals_rel_def] >>
      rw[] >>  metis_tac[])>>
    fs[] >>
    IF_CASES_TAC>>fs[call_env_def,flush_state_def]
    >-
      (simp[state_component_equality,strong_locals_rel_def]>>
       rw[] >> fs[] >> Cases_on `h` >> fs [] >>
       Cases_on `x''` >> fs [] >> Cases_on `r` >> fs []  >>
       Cases_on `r''` >> fs [] >> rveq >>
       fs [push_env_def, env_to_list_def] >> metis_tac []) >>
      fs [dec_clock_def]>>
      qpat_abbrev_tac`A = push_env x' B C with <|locals:=D; locals_size := Ls;
       stack_max := SM; clock:=E|>`>>
      qpat_abbrev_tac`A = push_env x' B C with <|locals:=D;locals_size := Ls;
            stack_max := SM; clock:=E|>`>>
      `A=A'` by
        (unabbrev_all_tac>>Cases_on`h`>>EVERY_CASE_TAC>>fs[push_env_def])>>
      fs[]>>
      ntac 3 (TOP_CASE_TAC>>fs[])
      >-
        (ntac 3 (TOP_CASE_TAC>>fs[set_vars_def])>>
        strip_tac>>
        res_tac>>
        fs[]>>
        pop_assum match_mp_tac>>
        fs[strong_locals_rel_def])
      >-
        (TOP_CASE_TAC>>fs[]
        >-
          (fs[state_component_equality,strong_locals_rel_def]>>
          rw[]>>fs[])
        >>
        ntac 5 (TOP_CASE_TAC>>fs[])>>
        Cases_on`remove_dead q''' live`>>fs[set_var_def]>>
        strip_tac>>res_tac>>
        fs[]>>
        first_assum match_mp_tac>>
        fs[strong_locals_rel_def])
      >>
        fs[state_component_equality,strong_locals_rel_def]>>
        rw[]>>fs[])
  (* The rest don't touch the locals, so the transformation just does nothing  *)
  >- (* set (global store) *)
    (qpat_x_assum`A=(res,rst)` mp_tac>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    fs[set_store_def]>>rw[]>>rpt var_eq_tac>>
    imp_res_tac strong_locals_rel_I_word_exp>>
    fs[state_component_equality,strong_locals_rel_def,lookup_insert,domain_union])
  >- (* Store *)
    (qpat_x_assum`A=(res,rst)` mp_tac>>
    ntac 4 (TOP_CASE_TAC>>fs[])>>
    imp_res_tac strong_locals_rel_I_word_exp>>
    pop_assum (qspecl_then [`t`,`live`] mp_tac)>>impl_tac
    >-
      (fs[strong_locals_rel_def,lookup_insert,domain_union]>>
      metis_tac[])
    >>
    rw[]>>
    imp_res_tac strong_locals_rel_I_get_var>>fs[mem_store_def]>>
    fs[state_component_equality,strong_locals_rel_def,lookup_insert,domain_union]>>rw[])
  >- (* call NONE *)
    (qpat_x_assum`A=(res,rst)` mp_tac>>
    ntac 4 (TOP_CASE_TAC>>fs[])>>
    rename1 `¬bad_dest_args xs ys` >>
    `get_vars (MAP I ys) (st with locals:=t) = SOME x` by
      (match_mp_tac strong_locals_rel_get_vars>>
      fs[]>>
      first_assum (match_exists_tac o concl)>>
      simp[domain_numset_list_insert])>>
    fs[]>>
    EVERY_CASE_TAC>>fs[call_env_def, flush_state_def,state_component_equality,dec_clock_def] >> rw [] >> metis_tac [])
  >- (* alloc *)
    (qpat_x_assum`A=(res,rst)` mp_tac>>
    fs[alloc_def]>>
    ntac 6 (TOP_CASE_TAC>>fs[])>>
    fs[gc_def]>>
    qpat_x_assum`A=SOME x'` mp_tac>>
    ntac 4 (TOP_CASE_TAC>>fs[])>>
    strip_tac>>
    imp_res_tac strong_locals_rel_I_get_var>>fs[]>>
    rename1 `cut_envs names st.locals = SOME x` >>
    `cut_envs names t = SOME x` by
      (match_mp_tac (GEN_ALL strong_locals_rel_I_cut_envs)>>fs[]>>
      qexists_tac`st`>>fs[]>>
      fs[strong_locals_rel_def,domain_union] >>
      metis_tac[])>>
    fs[push_env_def,env_to_list_def,gc_def,set_store_def]>>
    strip_tac>>
    qexists_tac`rst.locals`>>fs[state_component_equality]>>
    FULL_CASE_TAC>>fs[strong_locals_rel_def])
  >- ( (* StoreConsts *)
    qpat_x_assum`A=(res,rst)`mp_tac>>
    TOP_CASE_TAC>>simp[]>>
    imp_res_tac strong_locals_rel_I_get_var>>fs[]>>
    TOP_CASE_TAC>>simp[]>>
    fs[Once INSERT_COMM]>>
    TOP_CASE_TAC>>simp[]>>
    imp_res_tac strong_locals_rel_I_get_var>>fs[]>>
    TOP_CASE_TAC>>simp[]>>
    every_case_tac>>fs[unset_var_def,state_component_equality]>>
    rw[]>>
    qpat_x_assum`_=rst.locals` sym_sub_tac>>
    fs[strong_locals_rel_def]>>
    simp[lookup_insert,lookup_delete]>>rw[])
  >- (*raise*)
    (qpat_x_assum`A=(res,rst)`mp_tac>>
    fs[jump_exc_def]>>
    ntac 4 (TOP_CASE_TAC>>fs[])>>
    imp_res_tac strong_locals_rel_I_get_var>>fs[]>>
    strip_tac>>rpt var_eq_tac>>fs[state_component_equality])
  >- (*return*)
    (qpat_x_assum`A=(res,rst)`mp_tac>>
    ntac 3 (TOP_CASE_TAC>>fs[])>>
    imp_res_tac strong_locals_rel_I_get_var>>
    fs[] >>
    imp_res_tac strong_locals_rel_I_get_vars>>
    pop_assum mp_tac >>
    impl_tac >-
    simp[INSERT_SING_UNION,domain_numset_list_insert] >>
    rw[] >> fs[] >>
    fs[flush_state_def])
  >- (* Tick *)
    (IF_CASES_TAC>>
    fs[call_env_def, flush_state_def,dec_clock_def,state_component_equality,strong_locals_rel_def]>>
    rpt var_eq_tac>>fs[] >> metis_tac [])
  >- (* Install *)
    (fs[case_eq_thms]>>pairarg_tac>>
    fs[case_eq_thms]>>rw[]>>
    fs[list_insert_def]>>
    imp_res_tac strong_locals_rel_I_cut_env>>
    pop_assum(qspec_then`t` mp_tac)>>
    impl_tac>-
      (fs[strong_locals_rel_def,list_insert_def,domain_union]>>
      metis_tac[]) >>
    rw[]>>
    imp_res_tac strong_locals_rel_I_get_var>>
    rename1`cut_env sss _ = _`>>
    rpt(
      pop_assum(qspecl_then[`t`,`sss`] mp_tac)>>
      impl_tac>- (fs[strong_locals_rel_def]>>metis_tac[]))>>
    rw[state_component_equality]>>
    fs[strong_locals_rel_def] >>
    fs [PULL_EXISTS,get_var_def] >>
    metis_tac [])
  >- (* CBW *)
    (fs[case_eq_thms,list_insert_def]>>
    imp_res_tac strong_locals_rel_I_get_var>>
    rpt(
      pop_assum(qspecl_then[`t`,`domain live`] mp_tac)>>
      impl_tac>- (fs[strong_locals_rel_def]>>metis_tac[]))>>
    rw[state_component_equality]>>
    fs[strong_locals_rel_def])
  >- (* DBW *)
    (fs[case_eq_thms,list_insert_def]>>
    imp_res_tac strong_locals_rel_I_get_var>>
    rpt(
      pop_assum(qspecl_then[`t`,`domain live`] mp_tac)>>
      impl_tac>- (fs[strong_locals_rel_def]>>metis_tac[]))>>
    rw[state_component_equality]>>
    fs[strong_locals_rel_def])
  >- (* FFI *)
    (qpat_x_assum`A=(res,rst)` mp_tac>>
    rpt (TOP_CASE_TAC>>fs[])>>
    imp_res_tac strong_locals_rel_I_get_var >>
    rename1 `cut_env names st.locals = SOME x` >>
    rpt (*This is super inefficient*)
     (first_x_assum(qspecl_then[`t`,`domain (union (FST names) (SND names))`] mp_tac)>>
      impl_tac>-
       (fs[strong_locals_rel_def]>>
       metis_tac[]))>>
    rw[]>> gvs[] >>
    `cut_env names t = SOME x` by
      (match_mp_tac (GEN_ALL strong_locals_rel_I_cut_env)>>fs[]>>
      qexists_tac`st`>>fs[]>>
      fs[strong_locals_rel_def,domain_union] >> metis_tac[])>>
    gvs[]
    >- fs[strong_locals_rel_def]
    >- fs[flush_state_def])
  >> rename1`m=Store \/ m = Store8 \/ m = Store32` >>
  qabbrev_tac`mcase=(m=Store \/ m = Store8 \/ m = Store32)`>>
  fs[AllCaseEqs(),PULL_EXISTS] >>
  Cases_on`mcase` >> gvs[]
  >- (
    gvs[oneline share_inst_def,
      oneline sh_mem_store_def,
      oneline sh_mem_store_byte_def,
      oneline sh_mem_store32_def,
      markerTheory.Abbrev_def,flush_state_def] >>
    drule_all_then (irule_at (Pos hd)) strong_locals_rel_I_word_exp >>
    gvs[domain_union,AllCaseEqs(),PULL_EXISTS] >>
    simp[state_component_equality]>>
    drule_then (irule_at $ Pos hd) strong_locals_rel_I_get_var >>
    fs[strong_locals_rel_def] >>
    metis_tac[]
  ) >>
  gvs[oneline share_inst_def,
    oneline sh_mem_load_def,
    oneline sh_mem_load_byte_def,
    oneline sh_mem_load32_def,
    oneline sh_mem_set_var_def,
    AllCaseEqs(),set_var_def,
    markerTheory.Abbrev_def,flush_state_def] >>
  drule_all_then (irule_at (Pos hd)) strong_locals_rel_I_word_exp >>
  simp[state_component_equality]>>
  irule strong_locals_rel_I_insert_insert >>
  fs[strong_locals_rel_def,domain_union]
QED

Theorem evaluate_remove_dead_prog:
  ∀prog st rst res.
  evaluate (prog,st) = (res,rst) ∧
  res ≠ SOME Error ⇒
  ∃t'.
    evaluate(remove_dead_prog prog,st) = (res,rst with locals:=t') ∧
    (IS_SOME res ⇒ rst.locals = t')
Proof
  rw[remove_dead_prog_def]>>
  Cases_on`remove_dead prog LN`>>
  drule_at (Pos (el 2)) evaluate_remove_dead>>
  disch_then (drule_at Any)>>
  simp[]>>
  disch_then(qspec_then`st.locals` mp_tac)>>
  impl_tac >-
    simp[strong_locals_rel_def]>>
  rw[]>>
  `st with locals := st.locals = st` by fs[state_component_equality]>>
  gvs[]>>
  every_case_tac>>gvs[]>>
  metis_tac[]
QED

(*SSA Proof*)

val size_tac = impl_tac>- (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)

(*This might not be the optimal invariant.. because it is very
  restrictive on the ssa_mapping*)
Definition ssa_locals_rel_def:
  ssa_locals_rel na ssa st_locs cst_locs =
  ((∀x y. lookup x ssa = SOME y ⇒ y ∈ domain cst_locs) ∧
  (∀x y. lookup x st_locs = SOME y ⇒
    x ∈ domain ssa ∧
    lookup (THE (lookup x ssa)) cst_locs = SOME y ∧
    (is_alloc_var x ⇒ x < na)))
End

(*ssa_map_ok specifies the form of ssa_maps we care about
  1) The remapped keys are ALL_DISTINCT
  2) The remap keyset is bounded, and no phy vars
*)
Definition ssa_map_ok_def:
  ssa_map_ok na ssa =
  (∀x y. lookup x ssa = SOME y ⇒
    ¬is_phy_var y ∧ y < na)
End

Triviality list_next_var_rename_lemma_1:
  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ⇒
  let len = LENGTH ls in
  ALL_DISTINCT ls' ∧
  ls' = (MAP (λx. 4*x+na) (COUNT_LIST len)) ∧
  na' = na + 4* len
Proof
  Induct>>
  full_simp_tac(srw_ss())[list_next_var_rename_def,LET_THM,next_var_rename_def,COUNT_LIST_def]>>
  ntac 7 strip_tac>>
  srw_tac[][]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>
  Cases_on`r`>>full_simp_tac(srw_ss())[]>>
  res_tac
  >-
    (`∀x. MEM x q ⇒ na < x` by
      (srw_tac[][MEM_MAP]>>DECIDE_TAC)>>
    qpat_x_assum`A = ls'` (sym_sub_tac)>>
    `¬ MEM na q` by
      (SPOSE_NOT_THEN assume_tac>>
      res_tac>>DECIDE_TAC)>>
    full_simp_tac(srw_ss())[ALL_DISTINCT])
  >-
    (full_simp_tac(srw_ss())[MAP_MAP_o]>>
    qpat_x_assum`A = ls'` sym_sub_tac>>
    full_simp_tac(srw_ss())[MAP_EQ_f]>>srw_tac[][]>>
    DECIDE_TAC)
  >>
    DECIDE_TAC
QED

Triviality list_next_var_rename_lemma_2:
  ∀ls ssa na.
  ALL_DISTINCT ls ⇒
  let (ls',ssa',na') = list_next_var_rename ls ssa na in
  ls' = MAP (λx. THE(lookup x ssa')) ls ∧
  domain ssa' = domain ssa ∪ set ls ∧
  (∀x. ¬MEM x ls ⇒ lookup x ssa' = lookup x ssa) ∧
  (∀x. MEM x ls ⇒ ∃y. lookup x ssa' = SOME y)
Proof
  Induct>>full_simp_tac(srw_ss())[list_next_var_rename_def,LET_THM,next_var_rename_def]>>
  srw_tac[][]>>
  first_x_assum(qspecl_then[`insert h na ssa`,`na+4`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`list_next_var_rename ls (insert h na ssa) (na+4)`>>Cases_on`r`>>
  full_simp_tac(srw_ss())[lookup_insert,EXTENSION]>>srw_tac[][]>>
  metis_tac[]
QED

val exists_tac = qexists_tac`cst.permute`>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def
      ,ssa_cc_trans_def];

Triviality ssa_locals_rel_get_var:
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_var n st = SOME x
  ⇒
  get_var (option_lookup ssa n) cst = SOME x
Proof
  full_simp_tac(srw_ss())[get_var_def,ssa_locals_rel_def,strong_locals_rel_def,option_lookup_def]>>
  srw_tac[][]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[domain_lookup]>>
  first_x_assum(qspecl_then[`n`,`x`] assume_tac)>>rev_full_simp_tac(srw_ss())[]
QED

Triviality ssa_locals_rel_get_vars:
  ∀ls y na ssa st cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  get_vars ls st = SOME y
  ⇒
  get_vars (MAP (option_lookup ssa) ls) cst = SOME y
Proof
  Induct>>full_simp_tac(srw_ss())[get_vars_def]>>srw_tac[][]>>
  Cases_on`get_var h st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac ssa_locals_rel_get_var>>full_simp_tac(srw_ss())[]>>
  Cases_on`get_vars ls st`>>full_simp_tac(srw_ss())[]>>
  res_tac>>full_simp_tac(srw_ss())[]
QED

Triviality ssa_map_ok_extend:
  ssa_map_ok na ssa ∧
  ¬is_phy_var na ⇒
  ssa_map_ok (na+4) (insert h na ssa)
Proof
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
  res_tac>-
    DECIDE_TAC
QED

Triviality merge_moves_frame:
  ∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')
Proof
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  (CONJ_TAC>-
    (full_simp_tac(srw_ss())[is_alloc_var_def]>>
    (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`r1`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions]
QED

Triviality merge_moves_fst:
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  na ≤ na' ∧
  EVERY (λx. x < na' ∧ x ≥ na) (MAP FST moveL) ∧
  EVERY (λx. x < na' ∧ x ≥ na) (MAP FST moveR)
Proof
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[EVERY_MAP]>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`]assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A = moveL` (sym_sub_tac)>>
  qpat_x_assum`A = moveR` (sym_sub_tac)>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>
  res_tac>>
  DECIDE_TAC
QED

(*Characterize result of merge_moves*)
Triviality merge_moves_frame2:
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  domain ssaL' = domain ssaL ∧
  domain ssaR' = domain ssaR ∧
  ∀x. MEM x ls ∧ x ∈ domain (inter ssaL ssaR) ⇒
    lookup x ssaL' = lookup x ssaR'
Proof
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]
  >-
    metis_tac[]
  >> TRY
    (full_simp_tac(srw_ss())[domain_inter]>>srw_tac[][]>>
    qpat_x_assum`A=domain ssaL` (sym_sub_tac)>>
    qpat_x_assum`A=domain ssaR` (sym_sub_tac)>>
    full_simp_tac(srw_ss())[domain_lookup]>>
    full_simp_tac(srw_ss())[optionTheory.SOME_11]>>
    res_tac>>
    rev_full_simp_tac(srw_ss())[])
  >>
    full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][]>>
    metis_tac[domain_lookup,lookup_insert]
QED

(*Another frame proof about unchanged lookups*)
Triviality merge_moves_frame3:
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  ∀x. ¬MEM x ls ∨ x ∉ domain (inter ssaL ssaR) ⇒
    lookup x ssaL' = lookup x ssaL ∧
    lookup x ssaR' = lookup x ssaR
Proof
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  TRY(metis_tac[])>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_frame2>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  `h ∈ domain r3 ∧ h ∈ domain r2` by full_simp_tac(srw_ss())[domain_lookup]>>
  full_simp_tac(srw_ss())[domain_inter]>>
  metis_tac[]
QED

(*Don't know a neat way to prove this for both sides at once neatly,
Also, the cases are basically copy pasted... *)

Triviality mov_eval_head:
  evaluate(Move p moves,st) = (NONE,rst) ∧
  y ∈ domain st.locals ∧
  ¬MEM y (MAP FST moves) ∧
  ¬MEM x (MAP FST moves)
  ⇒
  evaluate(Move p ((x,y)::moves),st) = (NONE, rst with locals:=insert x (THE (lookup y st.locals)) rst.locals)
Proof
  full_simp_tac(srw_ss())[evaluate_def,get_vars_def,get_var_def,domain_lookup]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>
  full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
  qpat_x_assum `A=rst` (sym_sub_tac)>>full_simp_tac(srw_ss())[]
QED

Triviality merge_moves_correctL:
  ∀ls na ssaL ssaR stL cstL pri.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaL
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaL stL.locals cstL.locals ⇒
  let (resL,rcstL) = evaluate(Move pri moveL,cstL) in
    resL = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaL' = lookup x ssaL) ∧
    (∀x y. (x < na ∧ lookup x cstL.locals = SOME y)
    ⇒  lookup x rcstL.locals = SOME y) ∧
    ssa_locals_rel na' ssaL' stL.locals rcstL.locals ∧
    word_state_eq_rel cstL rcstL)
Proof
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
  (srw_tac[][]>>
  full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
  rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`,`pri`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  Cases_on`evaluate(Move pri q,cstL)`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_fst>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  imp_res_tac mov_eval_head>>
  pop_assum(qspec_then`r1` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM]>>
    res_tac>>
    DECIDE_TAC)>>
  strip_tac>>
  pop_assum(qspec_then`x'` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM,ssa_map_ok_def]>>
    res_tac>>
    DECIDE_TAC)>>
  impl_tac>-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    metis_tac[])>>
  strip_tac>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
  >-
    (`x'' ≠ r1` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[lookup_insert])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h ssaL = SOME x'` (SUBST_ALL_TAC)>>
      full_simp_tac(srw_ss())[])>>
      res_tac>>
      full_simp_tac(srw_ss())[domain_lookup]>>
       `v'' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>DECIDE_TAC))
  >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]
QED

Triviality merge_moves_correctR:
  ∀ls na ssaL ssaR stR cstR pri.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaR
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = merge_moves ls ssaL ssaR na in
  (ssa_locals_rel na ssaR stR.locals cstR.locals ⇒
  let (resR,rcstR) = evaluate(Move pri moveR,cstR) in
    resR = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaR' = lookup x ssaR) ∧
    (∀x y. (x < na ∧ lookup x cstR.locals = SOME y)
    ⇒  lookup x rcstR.locals = SOME y) ∧
    ssa_locals_rel na' ssaR' stR.locals rcstR.locals ∧
    word_state_eq_rel cstR rcstR)
Proof
  Induct>>full_simp_tac(srw_ss())[merge_moves_def]>-
  (srw_tac[][]>>
  full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
  rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stR`,`cstR`,`pri`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`merge_moves ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  Cases_on`evaluate(Move pri r0,cstR)`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`ls`]assume_tac)>>
  Q.ISPECL_THEN [`ls`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_fst>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  imp_res_tac mov_eval_head>>
  pop_assum(qspec_then`r1` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM]>>
    res_tac>>
    DECIDE_TAC)>>
  strip_tac>>
  pop_assum(qspec_then`x` mp_tac)>>impl_tac>-
    (SPOSE_NOT_THEN assume_tac>>full_simp_tac(srw_ss())[EVERY_MEM,ssa_map_ok_def]>>
    res_tac>>
    DECIDE_TAC)>>
  impl_tac>-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    metis_tac[])>>
  strip_tac>>
  srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
  >-
    (`x'' ≠ r1` by DECIDE_TAC>>
    full_simp_tac(srw_ss())[lookup_insert])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x''=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h ssaR = SOME x` (SUBST_ALL_TAC)>>
      full_simp_tac(srw_ss())[])>>
      res_tac>>
      full_simp_tac(srw_ss())[domain_lookup]>>
       `v'' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v'' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>DECIDE_TAC))
  >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]
QED

Triviality fake_moves_frame:
  ∀ls na ssaL ssaR.
  is_alloc_var na
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  is_alloc_var na' ∧
  na ≤ na' ∧
  (ssa_map_ok na ssaL ⇒ ssa_map_ok na' ssaL') ∧
  (ssa_map_ok na ssaR ⇒ ssa_map_ok na' ssaR')
Proof
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  (CONJ_TAC>-
    (full_simp_tac(srw_ss())[is_alloc_var_def]>>
    (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`r1`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions]
QED

Triviality fake_moves_frame2:
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  domain ssaL' = domain ssaL ∪ (set ls ∩ (domain ssaR ∪ domain ssaL)) ∧
  domain ssaR' = domain ssaR ∪ (set ls ∩ (domain ssaR ∪ domain ssaL)) ∧
  ∀x. MEM x ls ∧ x ∉ domain(inter ssaL ssaR) ⇒ lookup x ssaL' = lookup x ssaR'
Proof
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[EXTENSION,domain_inter]>>srw_tac[][]>>
  metis_tac[domain_lookup,lookup_insert]
QED

Triviality fake_moves_frame3:
  ∀ls na ssaL ssaR.
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  ∀x. ¬ MEM x ls ∨ x ∈ domain(inter ssaL ssaR) ⇒
    lookup x ssaL' = lookup x ssaL ∧
    lookup x ssaR' = lookup x ssaR
Proof
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[LET_THM]>>
  last_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>rev_full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN[`ls`,`na`,`ssaL`,`ssaR`] assume_tac fake_moves_frame2>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[EXTENSION,domain_inter]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[lookup_insert]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
  `h ∈ domain r2` by full_simp_tac(srw_ss())[domain_lookup]>>
  res_tac>>
  full_simp_tac(srw_ss())[lookup_NONE_domain]
QED

Triviality fake_moves_correctL:
  ∀ls na ssaL ssaR stL cstL.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaL
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  (ssa_locals_rel na ssaL stL.locals cstL.locals ⇒
  let (resL,rcstL) = evaluate(moveL,cstL) in
    resL = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaL' = lookup x ssaL) ∧
    (∀x y. (x < na ∧ lookup x cstL.locals = SOME y)
    ⇒  lookup x rcstL.locals = SOME y) ∧
    ssa_locals_rel na' ssaL' stL.locals rcstL.locals ∧
    word_state_eq_rel cstL rcstL)
Proof
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
    (srw_tac[][]>>
    full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
    rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stL`,`cstL`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[evaluate_def,LET_THM,evaluate_def,fake_move_def,word_exp_def,inst_def,assign_def]>>
  Cases_on`evaluate(q,cstL)`>>full_simp_tac(srw_ss())[]>>
  `na ≤ r1 ∧ ssa_map_ok r1 r2` by
    (imp_res_tac fake_moves_frame>>
    full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum(qspecl_then[`ssaR`,`ssaL`,`prio`,`ls`]assume_tac)>>rev_full_simp_tac(srw_ss())[])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,get_vars_def,get_var_def,set_vars_def,alist_insert_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h r2 = SOME v'''` SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v''' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v''' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,set_var_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
        (res_tac>>full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def])
QED

Triviality fake_moves_correctR:
  ∀ls na ssaL ssaR stR cstR.
  is_alloc_var na ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssaR
  ⇒
  let(moveL,moveR,na',ssaL',ssaR') = fake_moves prio ls ssaL ssaR na in
  (ssa_locals_rel na ssaR stR.locals cstR.locals ⇒
  let (resR,rcstR) = evaluate(moveR,cstR) in
    resR = NONE ∧
    (∀x. ¬MEM x ls ⇒ lookup x ssaR' = lookup x ssaR) ∧
    (∀x y. (x < na ∧ lookup x cstR.locals = SOME y)
    ⇒  lookup x rcstR.locals = SOME y) ∧
    ssa_locals_rel na' ssaR' stR.locals rcstR.locals ∧
    word_state_eq_rel cstR rcstR)
Proof
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>-
  (srw_tac[][]>>
  full_simp_tac(srw_ss())[evaluate_def,word_state_eq_rel_def,get_vars_def,set_vars_def,alist_insert_def]>>
  rev_full_simp_tac(srw_ss())[]>>srw_tac[][])>>
  rpt strip_tac>>
  first_x_assum(qspecl_then[`na`,`ssaL`,`ssaR`,`stR`,`cstR`]mp_tac)>>
  impl_tac>-
    (rev_full_simp_tac(srw_ss())[LET_THM]>>
    metis_tac[])>>
  strip_tac>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`fake_moves prio ls ssaL ssaR na`>>PairCases_on`r`>>full_simp_tac(srw_ss())[]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  strip_tac>>full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[evaluate_def,LET_THM,evaluate_def,fake_move_def,word_exp_def,inst_def,assign_def]>>
  Cases_on`evaluate(r0,cstR)`>>full_simp_tac(srw_ss())[]>>
  `na ≤ r1 ∧ ssa_map_ok r1 r3` by
    (imp_res_tac fake_moves_frame>>
    full_simp_tac(srw_ss())[LET_THM]>>
    pop_assum(qspecl_then[`ssaR`,`ssaL`,`prio`,`ls`]assume_tac)>>rev_full_simp_tac(srw_ss())[])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,set_var_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
        (res_tac>>full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def])
  >-
    (full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,get_vars_def,get_var_def,set_vars_def,alist_insert_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[lookup_insert]
    >-
      (`x' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[lookup_insert])
    >-
      (IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[])
    >-
      (Cases_on`x'=h`>>full_simp_tac(srw_ss())[]>-
      (res_tac>>full_simp_tac(srw_ss())[]>>
      qpat_x_assum`lookup h r3 = SOME v'''` SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[])
      >>
      res_tac>>full_simp_tac(srw_ss())[]>>
      `v''' < r1` by
        (full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        metis_tac[])>>
      `v''' ≠ r1` by DECIDE_TAC>>
      full_simp_tac(srw_ss())[])
    >-
      (res_tac>>
      DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def])
QED

(*Swapping lemma that allows us to swap in ssaL for ssaR
  after we are done fixing them*)
Triviality ssa_eq_rel_swap:
  ssa_locals_rel na ssaR st.locals cst.locals ∧
  domain ssaL = domain ssaR ∧
  (∀x. lookup x ssaL = lookup x ssaR) ⇒
  ssa_locals_rel na ssaL st.locals cst.locals
Proof
  srw_tac[][ssa_locals_rel_def]
QED

Triviality ssa_locals_rel_more:
  ssa_locals_rel na ssa stlocs cstlocs ∧ na ≤ na' ⇒
  ssa_locals_rel na' ssa stlocs cstlocs
Proof
  srw_tac[][ssa_locals_rel_def]>>full_simp_tac(srw_ss())[]
  >- metis_tac[]>>
  res_tac>>full_simp_tac(srw_ss())[]>>
  DECIDE_TAC
QED

Triviality ssa_map_ok_more:
  ssa_map_ok na ssa ∧ na ≤ na' ⇒
  ssa_map_ok na' ssa
Proof
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
  >-
    metis_tac[]>>
  res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC
QED

Triviality get_var_ignore:
  ∀ls a.
  get_var x cst = SOME y ∧
  ¬MEM x ls ∧
  LENGTH ls = LENGTH a ⇒
  get_var x (set_vars ls a cst) = SOME y
Proof
  Induct>>full_simp_tac(srw_ss())[get_var_def,set_vars_def,alist_insert_def]>>
  srw_tac[][]>>
  Cases_on`a`>>full_simp_tac(srw_ss())[alist_insert_def,lookup_insert]
QED

Triviality fix_inconsistencies_correctL:
  ∀na ssaL ssaR.
  is_alloc_var na ∧
  ssa_map_ok na ssaL
  ⇒
  let(moveL,moveR,na',ssaU) = fix_inconsistencies prio ssaL ssaR na in
  (∀(stL:('a,'b,'c) wordSem$state) (cstL:('a,'b,'c) wordSem$state).
  ssa_locals_rel na ssaL stL.locals cstL.locals ⇒
  let (resL,rcstL) = evaluate(moveL,cstL) in
    resL = NONE ∧
    ssa_locals_rel na' ssaU stL.locals rcstL.locals ∧
    word_state_eq_rel cstL rcstL)
Proof
  full_simp_tac(srw_ss())[fix_inconsistencies_def]>>LET_ELIM_TAC>>
  rename1`Move pp`>>
  Q.ISPECL_THEN [`var_union`,`na`,`ssaL`,`ssaR`,`stL`,`cstL`,`pp`] mp_tac
      merge_moves_correctL>>
  full_simp_tac(srw_ss())[]>>
  (impl_keep_tac>-
    (full_simp_tac(srw_ss())[Abbr`var_union`,ALL_DISTINCT_MAP_FST_toAList]))>>
  LET_ELIM_TAC>>
  Q.ISPECL_THEN [`var_union`,`na'`,`ssaL'`,`ssaR'`,`stL`,`rcstL'`]mp_tac
      fake_moves_correctL>>
  (impl_tac>-
      (Q.ISPECL_THEN [`var_union`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_frame>>rev_full_simp_tac(srw_ss())[LET_THM]))>>
  LET_ELIM_TAC>>
  rev_full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A=moveL` sym_sub_tac>>
  qpat_x_assum`A=(resL,B)` mp_tac>>
  simp[Once evaluate_def]>>
  full_simp_tac(srw_ss())[]>>
  rpt VAR_EQ_TAC>>full_simp_tac(srw_ss())[]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def]
QED

Triviality fix_inconsistencies_correctR:
  ∀na ssaL ssaR prio.
  is_alloc_var na ∧
  ssa_map_ok na ssaR
  ⇒
  let(moveL,moveR,na',ssaU) = fix_inconsistencies prio ssaL ssaR na in
  (∀(stR:('a,'b,'c) wordSem$state) (cstR:('a,'b,'c) wordSem$state).
  ssa_locals_rel na ssaR stR.locals cstR.locals ⇒
  let (resR,rcstR) = evaluate(moveR,cstR) in
    resR = NONE ∧
    ssa_locals_rel na' ssaU stR.locals rcstR.locals ∧
    word_state_eq_rel cstR rcstR)
Proof
  full_simp_tac(srw_ss())[fix_inconsistencies_def]>>LET_ELIM_TAC>>
  rename1`Move ppl Lmov`>>
  rename1`Move ppr Rmov`>>
  Q.ISPECL_THEN [`var_union`,`na`,`ssaL`,`ssaR`,`stR`,`cstR`,`ppr`] mp_tac merge_moves_correctR>>
  full_simp_tac(srw_ss())[]>>
  (impl_keep_tac>-
    (full_simp_tac(srw_ss())[Abbr`var_union`,ALL_DISTINCT_MAP_FST_toAList]))>>
  LET_ELIM_TAC>>
  Q.ISPECL_THEN [`var_union`,`na'`,`ssaL'`,`ssaR'`,`stR`,`rcstR'`]mp_tac fake_moves_correctR>>
  (impl_tac>-
      (Q.ISPECL_THEN [`var_union`,`na`,`ssaL`,`ssaR`] assume_tac merge_moves_frame>>rev_full_simp_tac(srw_ss())[LET_THM]))>>
  LET_ELIM_TAC>>
  rev_full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A=moveR` sym_sub_tac>>
  qpat_x_assum`A=(resR,B)` mp_tac>>
  simp[Once evaluate_def]>>
  full_simp_tac(srw_ss())[]>>
  rpt VAR_EQ_TAC>>full_simp_tac(srw_ss())[]>>
  srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
  Q.ISPECL_THEN[`var_union`,`na`,`ssaL`,`ssaR`] assume_tac
    merge_moves_frame2>>
  Q.ISPECL_THEN[`var_union`,`na'`,`ssaL'`,`ssaR'`] assume_tac
    fake_moves_frame2>>
  Q.ISPECL_THEN[`var_union`,`na`,`ssaL`,`ssaR`] assume_tac
    merge_moves_frame3>>
  Q.ISPECL_THEN[`var_union`,`na'`,`ssaL'`,`ssaR'`] assume_tac
    fake_moves_frame3>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  match_mp_tac (GEN_ALL ssa_eq_rel_swap)>>
  HINT_EXISTS_TAC>>rev_full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[Abbr`var_union`,EXTENSION]>>CONJ_ASM1_TAC>-
    (full_simp_tac(srw_ss())[toAList_domain,domain_union]>>
    metis_tac[])>>
  full_simp_tac(srw_ss())[toAList_domain]>>srw_tac[][]>>
  reverse(Cases_on`x ∈ domain (union ssaL ssaR)`)
  >-
    (full_simp_tac(srw_ss())[domain_union]>>
    metis_tac[lookup_NONE_domain])
  >>
    full_simp_tac(srw_ss())[domain_inter]>>
    metis_tac[]
QED

fun use_ALOOKUP_ALL_DISTINCT_MEM (g as (asl,w)) =
  let
    val tm = find_term(can(match_term(lhs(snd(dest_imp(concl
      ALOOKUP_ALL_DISTINCT_MEM)))))) w
    val (_,[al,k]) = strip_comb tm
  in
    mp_tac(ISPECL [al,k] (Q.GENL[`al`,`k`,`v`] ALOOKUP_ALL_DISTINCT_MEM))
  end g;

Triviality list_next_var_rename_move_preserve:
  ∀st ssa na ls cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  set ls ⊆ domain st.locals ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssa ∧
  word_state_eq_rel st cst
  ⇒
  let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
  let (res,rcst) = evaluate (mov,cst) in
    res = NONE ∧
    ssa_locals_rel na' ssa' st.locals rcst.locals ∧
    word_state_eq_rel st rcst ∧
    (¬is_phy_var na ⇒ ∀w. is_phy_var w ⇒ lookup w rcst.locals = lookup w cst.locals) ∧
    (∀x y. lookup x st.locals = SOME y ⇒ lookup (THE (lookup x ssa)) rcst.locals = SOME y)
Proof
    full_simp_tac(srw_ss())[list_next_var_rename_move_def,ssa_locals_rel_def]>>
  srw_tac[][]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  imp_res_tac list_next_var_rename_lemma_2>>
  first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
  full_simp_tac(srw_ss())[LET_THM,evaluate_def]>>rev_full_simp_tac(srw_ss())[]>>
  rev_full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_COUNT_LIST,Abbr`cur_ls`]>>full_simp_tac(srw_ss())[]>>
  imp_res_tac get_vars_eq>>
  qpat_x_assum`A=(res,rcst)` mp_tac>>
  qabbrev_tac`v=get_vars ls st`>>
  qpat_abbrev_tac`cls = MAP (option_lookup ssa) ls`>>
  `get_vars cls cst = v` by
    (full_simp_tac(srw_ss())[Abbr`cls`]>>
    match_mp_tac ssa_locals_rel_get_vars>>
    full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
    qexists_tac`na`>>
    qexists_tac`st`>>full_simp_tac(srw_ss())[]>>
    metis_tac[])>>
  full_simp_tac(srw_ss())[Abbr`v`]>>srw_tac[][]
  >-
    (full_simp_tac(srw_ss())[set_vars_def,domain_alist_insert]>>
    Cases_on`MEM x ls`>>res_tac>>full_simp_tac(srw_ss())[]
    >-
      (DISJ2_TAC>>full_simp_tac(srw_ss())[MEM_MAP]>>
      HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
    >>
      (res_tac>>
      full_simp_tac(srw_ss())[]))
  >-
    (full_simp_tac(srw_ss())[set_vars_def,lookup_alist_insert]>>
    res_tac>>
    Cases_on`MEM x ls`>>full_simp_tac(srw_ss())[]
    >-
      (res_tac>>
      use_ALOOKUP_ALL_DISTINCT_MEM >>
      simp[ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,PULL_EXISTS] >>
      strip_tac>>
      pop_assum(qspec_then`x` assume_tac)>>
      rev_full_simp_tac(srw_ss())[])
    >>
      (full_simp_tac(srw_ss())[domain_lookup]>>
      qpat_abbrev_tac `opt:'a word_loc option = ALOOKUP (ZIP A) v`>>
      qsuff_tac `opt = NONE` >>full_simp_tac(srw_ss())[Abbr`opt`]>>
      match_mp_tac (SPEC_ALL ALOOKUP_NONE|>REWRITE_RULE[EQ_IMP_THM]|>CONJ_PAIR|>snd)>>
      SPOSE_NOT_THEN assume_tac>>
      full_simp_tac(srw_ss())[MAP_ZIP]>>
      full_simp_tac(srw_ss())[domain_lookup]>>
      `v < na` by
        metis_tac[ssa_map_ok_def]>>
      rev_full_simp_tac(srw_ss())[]>>
      rpt (qpat_x_assum`A = B` sym_sub_tac)>>
      full_simp_tac(srw_ss())[MEM_MAP]>>DECIDE_TAC))
  >-
    (res_tac>>DECIDE_TAC)
  >-
    full_simp_tac(srw_ss())[word_state_eq_rel_def,set_vars_def]
  >-
    (full_simp_tac(srw_ss())[lookup_alist_insert,set_vars_def]>>
    FULL_CASE_TAC>>
    imp_res_tac ALOOKUP_MEM>>
    full_simp_tac(srw_ss())[MEM_ZIP]>>
    qpat_x_assum`MAP A B = MAP C D` sym_sub_tac>>
    rev_full_simp_tac(srw_ss())[EL_MAP,LENGTH_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
    `is_stack_var na ∨ is_alloc_var na` by
      metis_tac[convention_partitions]>>
    `is_stack_var w ∨ is_alloc_var w` by
      (qspec_then `4` mp_tac arithmeticTheory.MOD_PLUS >>
      impl_tac>>
      full_simp_tac(srw_ss())[is_phy_var_def,is_alloc_var_def,is_stack_var_def]>>
      disch_then(qspecl_then[`4*n`,`na`](SUBST1_TAC o SYM)) >>
      `(4*n) MOD 4 =0 ` by
        (`0<4:num` by DECIDE_TAC>>
        `∀k.(4:num)*k=k*4` by DECIDE_TAC>>
        metis_tac[arithmeticTheory.MOD_EQ_0])>>
      full_simp_tac(srw_ss())[])>>
    metis_tac[convention_partitions])
  >>
    fs[ssa_locals_rel_def,ssa_map_ok_def,domain_lookup]>>
    res_tac>>fs[set_vars_def,lookup_alist_insert]>>
    qpat_abbrev_tac`lss = ZIP(A,B)`>>
    `ALOOKUP lss v = NONE` by
      (fs[ALOOKUP_NONE,Abbr`lss`,MEM_MAP,FORALL_PROD,MEM_ZIP]>>
      rw[]>>
      Cases_on`n<LENGTH ls`>>fs[EL_MAP]>>
      qpat_assum`MAP A B = MAP C ls` (mp_tac o SYM o (Q.AP_TERM `EL n`))>>
      simp[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>rw[]>>
      res_tac>>fs[])>>
    fs[]>>
    ntac 3 (last_x_assum kall_tac)>>
    rfs[]
QED

Triviality get_vars_list_insert_eq_gen:
  !ls x locs a b. (LENGTH ls = LENGTH x /\ ALL_DISTINCT ls /\
                  LENGTH a = LENGTH b /\ !e. MEM e ls ==> ~MEM e a)
  ==> get_vars ls (st with locals := alist_insert (a++ls) (b++x) locs) = SOME x
Proof
  ho_match_mp_tac alist_insert_ind>>
  srw_tac[][]>- (full_simp_tac(srw_ss())[get_vars_def])>>
  full_simp_tac(srw_ss())[get_vars_def,get_var_def,lookup_alist_insert]>>
  `LENGTH (ls::ls') = LENGTH (x::x')` by full_simp_tac(srw_ss())[]>>
  IMP_RES_TAC rich_listTheory.ZIP_APPEND>>
  ntac 9 (pop_assum (SUBST1_TAC o SYM))>>
  full_simp_tac(srw_ss())[ALOOKUP_APPEND]>>
  first_assum(qspec_then `ls` assume_tac)>>full_simp_tac(srw_ss())[]>>
  `ALOOKUP (ZIP (a,b)) ls = NONE` by metis_tac[ALOOKUP_NONE,MEM_MAP,MAP_ZIP]>>
  full_simp_tac(srw_ss())[]>>
  first_x_assum(qspecl_then [`a++[ls]`,`b++[x]`] assume_tac)>>
  `LENGTH (a++[ls]) = LENGTH (b++[x])` by full_simp_tac(srw_ss())[]>> rev_full_simp_tac(srw_ss())[]>>
  `a++[ls]++ls' = a++ls::ls' /\ b++[x]++x' = b++x::x'` by full_simp_tac(srw_ss())[]>>
  ntac 2 (pop_assum SUBST_ALL_TAC)>> full_simp_tac(srw_ss())[]
QED

Triviality get_vars_set_vars_eq:
  ∀ls x.
  ALL_DISTINCT ls ∧ LENGTH x = LENGTH ls ⇒
  get_vars ls (set_vars ls x cst) = SOME x
Proof
  full_simp_tac(srw_ss())[get_vars_def,set_vars_def]>>srw_tac[][]>>
  Q.ISPECL_THEN [`cst`,`ls`,`x`,`cst.locals`,`[]:num list`
    ,`[]:'a word_loc list`] mp_tac (GEN_ALL get_vars_list_insert_eq_gen)>>
  impl_tac>>full_simp_tac(srw_ss())[]
QED

Triviality ssa_locals_rel_ignore_set_var:
  ssa_map_ok na ssa ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  is_phy_var v
  ⇒
  ssa_locals_rel na ssa st.locals (set_var v a cst).locals
Proof
  srw_tac[][ssa_locals_rel_def,ssa_map_ok_def,set_var_def]>>
  full_simp_tac(srw_ss())[lookup_insert]>-
    metis_tac[]
  >>
  res_tac>>
  full_simp_tac(srw_ss())[domain_lookup]>>
  metis_tac[]
QED

Triviality ssa_locals_rel_ignore_insert:
  ssa_map_ok na ssa ∧
  ssa_locals_rel na ssa stloc cstloc ∧
  is_phy_var v
  ⇒
  ssa_locals_rel na ssa stloc (insert v a cstloc)
Proof
  srw_tac[][ssa_locals_rel_def,ssa_map_ok_def,set_var_def]>>
  full_simp_tac(srw_ss())[lookup_insert]>-
    metis_tac[]
  >>
  res_tac>>
  full_simp_tac(srw_ss())[domain_lookup]>>
  metis_tac[]
QED


Triviality ssa_locals_rel_ignore_list_insert:
  ssa_map_ok na ssa ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  EVERY is_phy_var ls ∧
  LENGTH ls = LENGTH x
  ⇒
  ssa_locals_rel na ssa st.locals (alist_insert ls x cst.locals)
Proof
  srw_tac[][ssa_locals_rel_def,ssa_map_ok_def]>>
  full_simp_tac(srw_ss())[domain_alist_insert,lookup_alist_insert]>-
    metis_tac[]
  >>
  res_tac>>
  full_simp_tac(srw_ss())[domain_lookup]>>
  res_tac>>
  `ALOOKUP (ZIP(ls,x)) v = NONE` by
    (srw_tac[][ALOOKUP_FAILS,MEM_ZIP]>>
    metis_tac[EVERY_EL])>>
  full_simp_tac(srw_ss())[]
QED

Triviality ssa_locals_rel_set_var:
  ssa_locals_rel na ssa st.locals cst.locals ∧
  ssa_map_ok na ssa ∧
  n < na ⇒
  ssa_locals_rel (na+4) (insert n na ssa) (insert n w st.locals) (insert na w cst.locals)
Proof
  srw_tac[][ssa_locals_rel_def]>>
  full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=n`>>full_simp_tac(srw_ss())[]
  >-
    metis_tac[]
  >-
    (res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,ssa_map_ok_def]>>
    first_x_assum(qspecl_then[`x`,`v`]assume_tac)>>
    (*Next part is a key reasoning step --
      We only have alloc_vars < na in the range of ssa
      Otherwise, the new one may overwrite an old mapping
    *)
    rev_full_simp_tac(srw_ss())[]>>
    `v ≠ na` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[])
  >-
    DECIDE_TAC
  >>
    (*Finally, this illustrates need for <na assumption on st.locals*)
    full_simp_tac(srw_ss())[ssa_map_ok_def]>>res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC
QED

Triviality ssa_locals_rel_insert:
  ssa_locals_rel na ssa stloc cstloc ∧
  ssa_map_ok na ssa ∧
  n < na ⇒
  ssa_locals_rel (na+4) (insert n na ssa) (insert n w stloc) (insert na w cstloc)
Proof
  srw_tac[][ssa_locals_rel_def]>>
  full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=n`>>full_simp_tac(srw_ss())[]
  >-
    metis_tac[]
  >-
    (res_tac>>
    full_simp_tac(srw_ss())[domain_lookup,ssa_map_ok_def]>>
    first_x_assum(qspecl_then[`x`,`v`]assume_tac)>>
    (*Next part is a key reasoning step --
      We only have alloc_vars < na in the range of ssa
      Otherwise, the new one may overwrite an old mapping
    *)
    rev_full_simp_tac(srw_ss())[]>>
    `v ≠ na` by DECIDE_TAC >>
    full_simp_tac(srw_ss())[])
  >-
    DECIDE_TAC
  >>
    (*Finally, this illustrates need for <na assumption on st.locals*)
    full_simp_tac(srw_ss())[ssa_map_ok_def]>>res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC
QED

Triviality is_alloc_var_add:
  is_alloc_var na ⇒ is_alloc_var (na+4)
Proof
  full_simp_tac(srw_ss())[is_alloc_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[])
QED

Triviality is_stack_var_add:
  is_stack_var na ⇒ is_stack_var (na+4)
Proof
  full_simp_tac(srw_ss())[is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[])
QED

Triviality is_alloc_var_flip:
  is_alloc_var na ⇒ is_stack_var (na+2)
Proof
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  drule arithmeticTheory.MOD_PLUS >>
  disch_then $ qspecl_then [`na`,`2`] assume_tac >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []
QED

Triviality is_stack_var_flip:
  is_stack_var na ⇒ is_alloc_var (na+2)
Proof
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  drule arithmeticTheory.MOD_PLUS >>
  disch_then $ qspecl_then [`na`,`2`] assume_tac >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []
QED

Triviality list_next_var_rename_props:
  ∀ls ssa na ls' ssa' na'.
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa ∧
  list_next_var_rename ls ssa na = (ls',ssa',na')
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'
Proof
  Induct>>full_simp_tac(srw_ss())[list_next_var_rename_def,next_var_rename_def]>>
  LET_ELIM_TAC>>
  first_x_assum(qspecl_then[`ssa''`,`na''`,`ys`,`ssa'''`,`na'''`]
    mp_tac)>>
  (impl_tac>-
    (full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
    >-
      metis_tac[is_alloc_var_add,is_stack_var_add]
    >-
      (full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
      metis_tac[convention_partitions])
    >-
      (full_simp_tac(srw_ss())[lookup_insert]>>Cases_on`x=h`>>full_simp_tac(srw_ss())[]>>
      res_tac>>DECIDE_TAC)))>>
  srw_tac[][]>> TRY(DECIDE_TAC)>> full_simp_tac(srw_ss())[]>>
  metis_tac[is_alloc_var_add,is_stack_var_add]
QED

Triviality list_next_var_rename_move_props:
  ∀ls ssa na ls' ssa' na'.
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa ∧
  list_next_var_rename_move ssa na ls = (ls',ssa',na')
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'
Proof
  full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>
  full_simp_tac(srw_ss())[]>>
  imp_res_tac list_next_var_rename_props
QED

Triviality ssa_cc_trans_inst_props:
  ∀i ssa na i' ssa' na'.
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ∧
  ssa_map_ok na ssa ∧
  is_alloc_var na
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssa'
Proof
  ho_match_mp_tac ssa_cc_trans_inst_ind>>rw[]>>
  gvs[ssa_cc_trans_inst_def,next_var_rename_def,AllCaseEqs()]>>
  rpt(pairarg_tac>>gvs[])>>
  `na + 8 = na + 4 +4` by fs[]>>
  metis_tac[is_alloc_var_add,ssa_map_ok_extend,convention_partitions]
QED

val exp_tac = (LET_ELIM_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    TRY(DECIDE_TAC)>>
    metis_tac[ssa_map_ok_extend,convention_partitions,is_alloc_var_add]);

Triviality fix_inconsistencies_props:
  ∀ssaL ssaR na a b na' ssaU.
  fix_inconsistencies prio ssaL ssaR na = (a,b,na',ssaU) ∧
  is_alloc_var na ∧
  ssa_map_ok na ssaL ∧
  ssa_map_ok na ssaR
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssaU
Proof
  full_simp_tac(srw_ss())[fix_inconsistencies_def]>>LET_ELIM_TAC>>
  imp_res_tac merge_moves_frame>>
  pop_assum(qspecl_then[`ssaR`,`ssaL`,`var_union`] assume_tac)>>
  Q.ISPECL_THEN [`var_union`,`na''`,`ssa_L'`,`ssa_R'`] assume_tac fake_moves_frame>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  DECIDE_TAC
QED

val th =
  (MATCH_MP
    (PROVE[]``((a ⇒ b) ∧ (c ⇒ d)) ⇒ ((a ∨ c) ⇒ b ∨ d)``)
    (CONJ is_stack_var_flip is_alloc_var_flip))

Triviality flip_rw:
  is_stack_var(na+2) = is_alloc_var na ∧
    is_alloc_var(na+2) = is_stack_var na
Proof
  conj_tac >> (reverse EQ_TAC >-
    metis_tac[is_alloc_var_flip,is_stack_var_flip]) >>
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  qspec_then `4` mp_tac arithmeticTheory.MOD_PLUS >>
  (impl_tac >- full_simp_tac(srw_ss())[]>>
  disch_then(qspecl_then[`na`,`2`](SUBST1_TAC o SYM)) >>
  `na MOD 4 < 4` by full_simp_tac(srw_ss())[]>>
  imp_res_tac (DECIDE ``n:num<4⇒(n=0)∨(n=1)∨(n=2)∨(n=3)``)>>
  full_simp_tac(srw_ss())[])
QED

val list_next_var_rename_props_2 =
  list_next_var_rename_props
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["na","na'"]))
  |> Q.SPECL[`na+2`] |> SPEC_ALL
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP (UNDISCH th)
  |> DISCH_ALL
  |> REWRITE_RULE[flip_rw]
  |> GEN_ALL
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["ls","ssa","na"]));

Triviality ssa_map_ok_lem:
  ssa_map_ok na ssa ⇒ ssa_map_ok (na+2) ssa
Proof
  metis_tac[ssa_map_ok_more, DECIDE``na:num ≤ na+2``]
QED

Triviality list_next_var_rename_move_props_2:
  ∀ls ssa na ls' ssa' na'.
  (is_alloc_var na ∨ is_stack_var na) ∧ ssa_map_ok na ssa ∧
  list_next_var_rename_move ssa (na+2) ls = (ls',ssa',na') ⇒
  (na+2) ≤ na' ∧
  (is_alloc_var na ⇒ is_stack_var na') ∧
  (is_stack_var na ⇒ is_alloc_var na') ∧
  ssa_map_ok na' ssa'
Proof
  ntac 7 strip_tac>>imp_res_tac list_next_var_rename_move_props>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[is_stack_var_flip,is_alloc_var_flip,ssa_map_ok_lem]
QED

Triviality ssa_map_ok_inter:
  ssa_map_ok na ssa ⇒
  ssa_map_ok na (inter ssa ssa')
Proof
  full_simp_tac(srw_ss())[ssa_map_ok_def,lookup_inter]>>srw_tac[][]>>EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[]
QED

Theorem ssa_map_ok_insert:
  ssa_map_ok na ssa ∧
  y < na ∧ ¬is_phy_var y ⇒
  ssa_map_ok na (insert x y ssa)
Proof
  rw[ssa_map_ok_def,lookup_insert]>>
  pop_assum mp_tac>>rw[]>>
  metis_tac[]
QED

Theorem ssa_map_ok_force_rename:
  ∀ls ssa.
  ssa_map_ok na ssa ∧
  EVERY (λx. SND x < na ∧ ¬is_phy_var (SND x)) ls
  ⇒
  ssa_map_ok na (force_rename ls ssa)
Proof
  Induct>>simp[FORALL_PROD]>>rw[force_rename_def]>>
  first_x_assum match_mp_tac>>
  simp[]>>
  match_mp_tac ssa_map_ok_insert>>
  simp[]
QED


(*Prove the properties that hold of ssa_cc_trans independent of semantics*)
Theorem ssa_cc_trans_props[local]:
  ∀prog ssa na prog' ssa' na'.
  ssa_cc_trans prog ssa na = (prog',ssa',na') ∧
  ssa_map_ok na ssa ∧
  is_alloc_var na
  ⇒
  na ≤ na' ∧
  is_alloc_var na' ∧
  ssa_map_ok na' ssa'
Proof
  ho_match_mp_tac ssa_cc_trans_ind>>
  full_simp_tac(srw_ss())[ssa_cc_trans_def]>>
  rpt conj_tac >> rpt gen_tac
  >- (
    (* Move *)
    LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[]
    >-
      metis_tac[list_next_var_rename_props]
    >-
      metis_tac[list_next_var_rename_props]
    >- (
      drule_at Any list_next_var_rename_props>>
      simp[]>>
      disch_then drule>>rw[]>>
      drule ssa_map_ok_force_rename>>
      disch_then match_mp_tac>>
      DEP_REWRITE_TAC[every_zip_snd]>>
      drule list_next_var_rename_lemma_1>>
      unabbrev_all_tac>>rw[EVERY_MEM,MEM_FILTER]>>
      pairarg_tac>>
      gvs[LENGTH_COUNT_LIST,MEM_MAP,MEM_COUNT_LIST,MEM_ZIP,EL_MAP,EL_COUNT_LIST]>>
      rename1`4 * xx + na`>>
      `is_alloc_var (4 * xx + na)` by
        gvs[is_alloc_var_def]>>
      metis_tac[convention_partitions]) )
  >- (
    (* StoreConsts *)
    LET_ELIM_TAC>>fs[next_var_rename_def]
    >- (
      rw[]>>
      `is_alloc_var ((d2+4)+4)` by
        fs[is_alloc_var_add]>>
      fs[])>>
    drule ssa_map_ok_extend >>
    disch_then(qspec_then `d` mp_tac)>>
    impl_tac >-
      metis_tac[convention_partitions]>>
    rw[]>>
    drule ssa_map_ok_extend >>
    disch_then(qspec_then `c` mp_tac)>>
    impl_tac >- metis_tac[convention_partitions,is_alloc_var_add]>>
    simp[])
  >-
    (LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[]>>
    metis_tac[ssa_cc_trans_inst_props])
  >- exp_tac
  >- exp_tac
  >- exp_tac
  >-
    (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    DECIDE_TAC)
  >-
    (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    DECIDE_TAC)
  >-
    (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_map_ok_more>>
    first_x_assum(qspec_then`na3` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[]>>
    imp_res_tac fix_inconsistencies_props>>DECIDE_TAC)
  >-
    (* Alloc *)
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    `∀naa. ssa_map_ok naa ssa''' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[])>>
    `na ≤ na+2 ∧ na'' ≤ na''+2` by DECIDE_TAC>>
    imp_res_tac ssa_map_ok_more>>
    imp_res_tac list_next_var_rename_props_2>>
    imp_res_tac ssa_map_ok_more>>
    res_tac>>
    imp_res_tac list_next_var_rename_props_2>>
    DECIDE_TAC)
  >- exp_tac
  >- exp_tac
  >- exp_tac
  >- exp_tac
  >- exp_tac
  >-
    (* Install *)
    (rpt gen_tac>> strip_tac>>
    simp[Once (GSYM markerTheory.Abbrev_def)]>>
    qpat_x_assum`_= (_,_,_)` mp_tac>>LET_ELIM_TAC >>
    ( (* multiple goals *)
      fs[next_var_rename_def]>>rw[]>>
      imp_res_tac list_next_var_rename_move_props_2>>
      rw[]>>fs[]>>
      rfs[]>>
      qabbrev_tac`na2 = na''+2`>>
      `is_alloc_var na2` by fs[Abbr`na2`,is_stack_var_flip]>>
      rw[]>>
      qmatch_asmsub_abbrev_tac`list_next_var_rename_move sss _ _ = _`>>
      Q.ISPECL_THEN[`ls`,`sss`,`na''+6`] mp_tac list_next_var_rename_move_props>>
      simp[]>>
      `is_alloc_var (na2+4)` by metis_tac[is_alloc_var_add]>>
      `na''+6 = na2+4` by fs[Abbr`na2`]>>
      impl_tac>-
        (simp[Abbr`sss`,Abbr`ssa_cut`]>>
        match_mp_tac ssa_map_ok_extend>>
        CONJ_TAC>-
         (match_mp_tac ssa_map_ok_inter>>
         fs[Abbr`na2`]>>
         match_mp_tac (GEN_ALL ssa_map_ok_more)>>
         asm_exists_tac>>fs[])>>
        metis_tac[convention_partitions])>>
      strip_tac>>
      fs[Abbr`na2`,markerTheory.Abbrev_def]))
  >- (* CBW *)
    (rw[]>>fs[])
  >- (* DBW *)
    (rw[]>>fs[])
  >-
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    `∀naa. ssa_map_ok naa ssa''' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[])>>
    `na ≤ na+2 ∧ na'' ≤ na''+2` by DECIDE_TAC>>
    imp_res_tac ssa_map_ok_more>>
    imp_res_tac list_next_var_rename_props_2>>
    imp_res_tac ssa_map_ok_more>>
    res_tac>>
    imp_res_tac list_next_var_rename_props_2>>
    DECIDE_TAC)
  >-
    (LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    rev_full_simp_tac(srw_ss())[])
  >-
  (*Calls*)
  (Count.apply (Cases_on`h`>-
    (
    full_simp_tac(srw_ss())[]>> rpt (disch_tac ORELSE gen_tac)>>
    qpat_abbrev_tac `goal = (_ ∧ _ ∧ _)` >>
    ntac 3 (pop_assum mp_tac)>>LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[PULL_FORALL,LET_THM]>>
    rveq >> gvs[] >>
    qspecl_then [`ret`, `ssa'''`, `na'''`]  assume_tac list_next_var_rename_props >>
    qspecl_then [`ls`, `ssa_cut`, `na''`]  assume_tac list_next_var_rename_move_props_2 >>
    qspecl_then [`ls`, `ssa`, `na`]  assume_tac list_next_var_rename_move_props_2 >>
    ntac 3 (pop_assum mp_tac) >>
    full_simp_tac(srw_ss())[] >>
    rpt strip_tac >>
    full_simp_tac(srw_ss())[] >>
    `ssa_map_ok na'' ssa_cut`
      by (
      pop_assum mp_tac >>
      srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[]) >>
    full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[Abbr`goal`]>>
    intLib.ARITH_TAC)

  >>
    (*This is a hacky mess*)
    PairCases_on`x`>>full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>
    rpt (disch_tac ORELSE gen_tac)>>
    qpat_abbrev_tac `goal = (_ ∧ _ ∧ _)` >>
    ntac 3 (pop_assum mp_tac)>>LET_ELIM_TAC>>
    rpt (pop_assum mp_tac) >>
    full_simp_tac(srw_ss())[PULL_FORALL,LET_THM]>>
    rpt (disch_tac) >>
    full_simp_tac(srw_ss())[]>>
    rveq >>
    ntac 21 (pop_assum mp_tac) >>
    full_simp_tac(srw_ss())[]>>
    rpt (disch_tac) >>
    rpt (first_x_assum (qspec_then `cur_ls'` mp_tac)) >>
    simp[markerTheory.Abbrev_def] >>
    rpt (disch_tac) >>
    drule fix_inconsistencies_props >>
    rpt (disch_tac) >>
    qspecl_then [`ret`, `ssa''''`, `n''`]  assume_tac list_next_var_rename_props >>
    qspecl_then [`ls`, `ssa_cut`, `n'`]  assume_tac list_next_var_rename_props_2 >>
    qspecl_then [`ls`, `ssa`, `na`]  assume_tac list_next_var_rename_props_2 >>
    ntac 3 (pop_assum mp_tac) >>
    full_simp_tac(srw_ss())[] >>
    rpt (disch_tac) >>
    full_simp_tac(srw_ss())[] >>
    `∀naa. ssa_map_ok naa ssa'' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      metis_tac[])>>
    `∀naa ssa. ssa_map_ok naa ssa ⇒ ssa_map_ok (naa + 2) ssa` by
      (
    rpt strip_tac >>
    irule ssa_map_ok_more>>
    first_x_assum (irule_at Any) >>
    intLib.ARITH_TAC) >>
    full_simp_tac(srw_ss())[next_var_rename_def] >>
    gvs[] >>
    qspecl_then [`ssa''''`, `n'''`,`x0`]  assume_tac (GEN_ALL ssa_map_ok_extend) >>
    pop_assum mp_tac >>
    impl_tac >-(
        fs[Once convention_partitions] >>
        imp_res_tac ssa_map_ok_more>>metis_tac[]) >>
    rpt strip_tac >>
    full_simp_tac(srw_ss())[is_alloc_var_add]>>
    ntac 16 (pop_assum mp_tac) >>
    full_simp_tac(srw_ss())[]>>
    rpt strip_tac >>
    `ssa_map_ok na_3 ssa_2`
     by (irule ssa_map_ok_more >>
     qexists_tac `n'''` >>
     fs[]) >>
    full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[Abbr`goal`]>>
    intLib.ARITH_TAC))
  >- ((*ShareInst*)
    rpt gen_tac >>
    simp[LET_THM] >>
    IF_CASES_TAC
    >- (rw[] >> simp[]) >>
    pairarg_tac >>
    simp[] >>
    rpt $ disch_then strip_assume_tac >>
    gvs[next_var_rename_def] >>
    conj_tac >- fs[is_alloc_var_def] >>
    drule_then irule ssa_map_ok_extend >>
    metis_tac[convention_partitions] )
QED

Triviality PAIR_ZIP_MEM:
  LENGTH c = LENGTH d ∧
  MEM (a,b) (ZIP (c,d)) ⇒
  MEM a c ∧ MEM b d
Proof
  srw_tac[][]>>imp_res_tac MEM_ZIP>>
  full_simp_tac(srw_ss())[MEM_EL]>>
  metis_tac[]
QED

Triviality ALOOKUP_ZIP_MEM:
  LENGTH a = LENGTH b ∧
  ALOOKUP (ZIP (a,b)) x = SOME y
  ⇒
  MEM x a ∧ MEM y b
Proof
  srw_tac[][]>>imp_res_tac ALOOKUP_MEM>>
  metis_tac[PAIR_ZIP_MEM]
QED

Triviality ALOOKUP_ALL_DISTINCT_REMAP:
  ∀ls x f y n.
  LENGTH ls = LENGTH x ∧
  ALL_DISTINCT (MAP f ls) ∧
  n < LENGTH ls ∧
  ALOOKUP (ZIP (ls,x)) (EL n ls) = SOME y
  ⇒
  ALOOKUP (ZIP (MAP f ls,x)) (f (EL n ls)) = SOME y
Proof
  Induct>>srw_tac[][]>>
  Cases_on`x`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac ALL_DISTINCT_MAP>>
  Cases_on`n`>>full_simp_tac(srw_ss())[]>>
  `¬MEM h ls` by metis_tac[MEM_MAP]>>
  full_simp_tac(srw_ss())[MEM_EL]>>
  pop_assum(qspec_then`n'` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
  full_simp_tac(srw_ss())[]>>
  `f h ≠ f (EL n' ls)` by
    (SPOSE_NOT_THEN assume_tac>>
    first_x_assum(qspec_then`n'` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
    metis_tac[EL_MAP])>>
  metis_tac[]
QED

Triviality set_toAList_keys:
  set (MAP FST (toAList t)) = domain t
Proof
  full_simp_tac(srw_ss())[toAList_domain,EXTENSION]
QED

val is_phy_var_tac =
    full_simp_tac(srw_ss())[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

Triviality ssa_cc_trans_exp_correct:
  ∀st w cst ssa na res.
  word_exp st w = SOME res ∧
  word_state_eq_rel st cst ∧
  ssa_locals_rel na ssa st.locals cst.locals
  ⇒
  word_exp cst (ssa_cc_trans_exp ssa w) = SOME res
Proof
  ho_match_mp_tac word_exp_ind>>srw_tac[][]>>
  full_simp_tac(srw_ss())[word_exp_def,ssa_cc_trans_exp_def]>>
  qpat_x_assum`A=SOME res` mp_tac
  >-
    (fs[get_var_def,ssa_locals_rel_def,word_state_eq_rel_def]>>rw[]>>
    res_tac>>rpt(qpat_x_assum`!x.P` kall_tac)>>
    fs[domain_lookup,option_lookup_def]>>
    rfs[])
  >-
    full_simp_tac(srw_ss())[word_state_eq_rel_def,get_store_def]
  >-
    (Cases_on`word_exp st w`>>
    res_tac>>full_simp_tac(srw_ss())[word_state_eq_rel_def,mem_load_def])
  >-
    (qpat_abbrev_tac`ls = MAP A B`>>
    qpat_abbrev_tac`ls' = MAP A B`>>
    TOP_CASE_TAC>>simp[]>>
    `ls = ls'` by
      (imp_res_tac the_words_EVERY_IS_SOME>>
      unabbrev_all_tac>>fs[MAP_EQ_f,MAP_MAP_o]>>
      fs[EVERY_MAP,EVERY_MEM]>>
      rw[]>>res_tac>>
      fs[IS_SOME_EXISTS])>>
    fs[])
  >-
    (Cases_on`word_exp st w`>>
    res_tac>>full_simp_tac(srw_ss())[word_state_eq_rel_def,mem_load_def])
QED

val exp_tac =
    (last_x_assum kall_tac>>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    imp_res_tac ssa_locals_rel_get_var>>
    imp_res_tac ssa_cc_trans_exp_correct>>full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    rev_full_simp_tac(srw_ss())[evaluate_def]>>
    fs[set_var_def,get_store_def,set_store_def]>>
    match_mp_tac ssa_locals_rel_set_var>>
    full_simp_tac(srw_ss())[every_var_def]);

val setup_tac = Cases_on`word_exp st expr`>>full_simp_tac(srw_ss())[]>>
                imp_res_tac ssa_cc_trans_exp_correct>>
                rev_full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
                full_simp_tac(srw_ss())[Abbr`expr`,ssa_cc_trans_exp_def,option_lookup_def,set_var_def];

Triviality get_var_set_vars_notin:
  ¬MEM v ls ∧
  LENGTH ls = LENGTH vs ⇒
  get_var v (set_vars ls vs st) = get_var v st
Proof
  fs[get_var_def,set_vars_def,lookup_alist_insert]>>
  rw[]>>CASE_TAC>>fs[]>>
  imp_res_tac ALOOKUP_ZIP_MEM>>
  fs[]
QED

Theorem ssa_locals_rel_delete_left:
  ssa_locals_rel na ssa stl cstl ⇒
  ssa_locals_rel na ssa (delete n stl) cstl
Proof
  rw[ssa_locals_rel_def]
  >-
    metis_tac[]>>
  fs[lookup_delete]
QED

Theorem ssa_locals_rel_delete_right:
  ssa_map_ok na ssa ∧ ssa_locals_rel na ssa stl cstl ∧ is_phy_var n ⇒
  ssa_locals_rel na ssa stl (delete n cstl)
Proof
  rw[ssa_locals_rel_def]
  >-
    metis_tac[]
  >- (
    fs[ssa_map_ok_def]>> last_x_assum drule>>simp[]>>
    metis_tac[])>>
  first_x_assum drule>>
  fs[ssa_map_ok_def,domain_lookup]>>rw[]>>
  last_x_assum drule>>simp[lookup_delete]>>
  metis_tac[]
QED

Theorem lookup_force_rename_aux:
  ∀ls ssa.
  lookup x (force_rename (REVERSE ls) ssa) =
  case ALOOKUP ls x of
    NONE => lookup x ssa
  | SOME y => SOME y
Proof
  ho_match_mp_tac SNOC_INDUCT>>
  rw[REVERSE_SNOC]
  >- simp[force_rename_def]>>
  rename1`h::REVERSE _`>>
  Cases_on`h`>>
  rw[force_rename_def]>>
  every_case_tac>>gvs[]>>
  rw[lookup_insert]>>gvs[ALOOKUP_SNOC]
QED

Theorem lookup_force_rename:
  lookup x (force_rename ls ssa) =
  case ALOOKUP (REVERSE ls) x of
    NONE => lookup x ssa
  | SOME y => SOME y
Proof
  metis_tac[lookup_force_rename_aux,REVERSE_REVERSE]
QED

Theorem domain_force_rename:
  domain (force_rename ls ssa) =
    domain ssa ∪ set (MAP FST ls)
Proof
  rw[EXTENSION,domain_lookup]>>
  rw[lookup_force_rename,EQ_IMP_THM]>>
  gvs[AllCaseEqs(),MEM_MAP]>>
  metis_tac[ALOOKUP_EXISTS_IFF,FST,PAIR,MEM_REVERSE,option_CASES]
QED

Theorem ssa_locals_rel_force_rename:
  ssa_locals_rel na ssa st1 st2 ∧
  EVERY (λx. lookup (FST x) st1 = lookup (SND x) st2) ls ∧
  set (MAP SND ls) ⊆ domain st2
  ⇒
  ssa_locals_rel na (force_rename ls ssa) st1 st2
Proof
  rw[]>>
  gvs[ssa_locals_rel_def]>>rw[]>>
  gvs[AllCaseEqs(),lookup_force_rename,domain_force_rename]
  >- metis_tac[]
  >- (
    drule ALOOKUP_MEM>>
    gvs[SUBSET_DEF,MEM_MAP]>>
    metis_tac[SND,PAIR,MEM_REVERSE])
  >- (
    every_case_tac>>rw[]>>
    drule ALOOKUP_MEM>>
    gvs[EVERY_MEM]>>rw[]>>
    metis_tac[PAIR,FST,SND])
QED

Theorem list_next_var_rename_move_distinct:
  list_next_var_rename_move ssa na ls = (mov,ssa',na') ∧
  ALL_DISTINCT ls ∧
  MEM x ls ∧ MEM y ls ∧
  option_lookup ssa' x = option_lookup ssa' y ⇒
  x = y
Proof
  rw[list_next_var_rename_move_def]>>
  rpt (pairarg_tac>>gvs[])>>
  drule list_next_var_rename_lemma_1 >>
  drule list_next_var_rename_lemma_2 >>
  LET_ELIM_TAC>>
  first_x_assum drule>> rw[]>>
  res_tac>>
  gvs[option_lookup_def,AllCaseEqs()]>>
  gvs[EL_ALL_DISTINCT_EL_EQ,MEM_EL,EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
  metis_tac[]
QED
(*TODO move*)

Theorem get_vars_NOT_MEM:
  ¬MEM h xs ==>
  get_vars xs (cs with locals :=  insert h h' ys) = get_vars xs (cs with locals := ys)
Proof
  Induct_on `xs` >> gvs[get_vars_def,get_var_def,lookup_insert]
QED

Theorem get_vars_set_vars:
  !xs xy cs.
  ALL_DISTINCT xs /\
  LENGTH xs = LENGTH xy ==>
  get_vars xs (set_vars xs xy cs) = SOME xy
Proof
  Induct_on `xs` >> rw[] >>
  fs[get_vars_def,set_vars_def,alist_insert_def] >>
  Cases_on `xy` >> fs[] >>
  fs[alist_insert_def,get_var_def] >>
  first_x_assum (qspecl_then [`t`,`cs`] assume_tac) >>
  gvs[] >>
  gvs[get_vars_NOT_MEM]
QED

Theorem ssa_cc_trans_correct:
  ∀prog st cst ssa na.
  word_state_eq_rel st cst ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  (*The following 3 assumptions are from the transform properties and
    are independent of semantics*)
  is_alloc_var na ∧
  every_var (λx. x < na) prog ∧
  ssa_map_ok na ssa
  ⇒
  ∃perm'.
  let (res,rst) = evaluate(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (prog',ssa',na') = ssa_cc_trans prog ssa na in
  let (res',rcst) = evaluate(prog',cst) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    (case res of
      NONE =>
        ssa_locals_rel na' ssa' rst.locals rcst.locals
    | SOME _    => rst.locals = rcst.locals )
Proof
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >-
    exists_tac
  >~ [`Move`]
  >- (
    last_x_assum kall_tac>>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[set_vars_def]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[evaluate_def]>>
    imp_res_tac list_next_var_rename_lemma_1>>
    imp_res_tac list_next_var_rename_lemma_2>>
    gvs[MAP_ZIP,LENGTH_COUNT_LIST]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    gvs[set_vars_def]>>
    qmatch_goalsub_abbrev_tac`ssa_locals_rel (na + 4 * LENGTH l) _ st1 st2`>>
    (* The ssa'' map would have been fine to return without
      forcing the renames too *)
    `ssa_locals_rel (na + 4 * LENGTH l) ssa'' st1 st2` by (
      unabbrev_all_tac>>
      fs[ssa_locals_rel_def]>>
      first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
      gvs[]>>
      imp_res_tac get_vars_length_lemma>>
      CONJ_ASM1_TAC
      >- (
        rw[domain_lookup]>>
        fs[lookup_alist_insert]>>
        EVERY_CASE_TAC>>
        rev_full_simp_tac(srw_ss())[ALOOKUP_NONE,MAP_ZIP]>>
        `¬ (MEM x' (MAP FST l))` by
          (CCONTR_TAC>>
          full_simp_tac(srw_ss())[MEM_MAP]>>
          first_x_assum(qspec_then`x'` assume_tac)>>
          rev_full_simp_tac(srw_ss())[]>>
          metis_tac[])>>
        `x' ∈ domain ssa'' ∧ x' ∈ domain ssa` by
          (CONJ_ASM1_TAC>-
            full_simp_tac(srw_ss())[domain_lookup]
          >>
          full_simp_tac(srw_ss())[EXTENSION]>>metis_tac[])>>
        metis_tac[domain_lookup]) >>
      gvs[strong_locals_rel_def]>>
      rw[]>>
      gvs[lookup_alist_insert]
      >- (
        Cases_on`MEM x' (MAP FST l)`>>
        full_simp_tac(srw_ss())[]>>
        Q.ISPECL_THEN [`MAP FST l`,`x`,`x'`] assume_tac ALOOKUP_ZIP_FAIL>>
        rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[])
      >- (
        Cases_on`MEM x' (MAP FST l)`>>
        full_simp_tac(srw_ss())[]
        >- (
          `ALL_DISTINCT (MAP FST (ZIP (MAP FST l,x)))` by full_simp_tac(srw_ss())[MAP_ZIP]>>
          full_simp_tac(srw_ss())[MEM_EL]>>
          imp_res_tac ALOOKUP_ALL_DISTINCT_EL>>
          pop_assum(qspec_then `n'` mp_tac)>>
          impl_tac>>
          full_simp_tac(srw_ss())[LENGTH_ZIP]>>srw_tac[][]>>
          rev_full_simp_tac(srw_ss())[EL_ZIP]>>full_simp_tac(srw_ss())[]>>
          imp_res_tac ALOOKUP_ALL_DISTINCT_REMAP>>
          full_simp_tac(srw_ss())[LENGTH_MAP])
        >>
        Q.ISPECL_THEN [`MAP FST l`,`x`,`x'`] assume_tac ALOOKUP_ZIP_FAIL>>
        gvs[ssa_map_ok_def]>>
        ntac 11 (last_x_assum kall_tac)>>
        res_tac>>
        fs[domain_lookup]>>res_tac>>
        qabbrev_tac `ls = MAP (\x. THE (lookup x ssa'')) (MAP FST l)`>>
        qsuff_tac `ALOOKUP (ZIP (ls,x)) v = NONE` >>
        full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[ALOOKUP_NONE]>>
        qpat_x_assum`A = ls` (sym_sub_tac)>>
        full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_COUNT_LIST]>>
        full_simp_tac(srw_ss())[MEM_MAP]>>srw_tac[][]>>
        DECIDE_TAC)
      >>
        EVERY_CASE_TAC>>rev_full_simp_tac(srw_ss())[every_var_def]
        >-
          metis_tac[DECIDE``x'<na ⇒ x' < na + 4*LENGTH l``]
        >>
          `MEM x' (MAP FST l)` by
            metis_tac[ALOOKUP_ZIP_MEM,LENGTH_MAP]>>
          full_simp_tac(srw_ss())[EVERY_MEM]>>
          metis_tac[DECIDE``x'<na ⇒ x' < na + 4*LENGTH l``]
      )>>
    drule get_vars_length_lemma>>
    simp[]>>strip_tac>>
    (* but we force some new mappings *)
    match_mp_tac ssa_locals_rel_force_rename>>
    simp[]>>
    CONJ_TAC >- (
      simp[EVERY_MEM,MEM_FILTER,MEM_ZIP,LENGTH_COUNT_LIST]>>
      rw[]>>
      fs[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST]>>
      qmatch_goalsub_abbrev_tac`A = B`>>
      rename1`ii < LENGTH l`>>
      `B = SOME (EL ii x)` by (
        unabbrev_all_tac>>
        DEP_REWRITE_TAC[lookup_alist_insert]>>
        simp[LENGTH_COUNT_LIST,AllCaseEqs()]>>
        DISJ2_TAC>>
        match_mp_tac ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME>>
        simp[MAP_ZIP,LENGTH_COUNT_LIST,MEM_ZIP]>>
        qexists_tac`ii`>>simp[EL_MAP,LENGTH_COUNT_LIST,EL_COUNT_LIST])>>
      pop_assum SUBST1_TAC>>
      unabbrev_all_tac>>
      DEP_REWRITE_TAC[lookup_alist_insert]>>
      simp[AllCaseEqs()]>>
      DISJ1_TAC>>
      simp[ALOOKUP_NONE,MAP_ZIP]>>
      imp_res_tac get_vars_exists>>
      imp_res_tac get_vars_eq>>
      gvs[EL_MAP,SUBSET_DEF,MEM_MAP,PULL_EXISTS,domain_lookup,MEM_EL]>>
      first_x_assum(qspec_then`ii` mp_tac)>>simp[]>>
      rw[]>>simp[])
    >- (
      simp[Abbr`st2`,SUBSET_DEF,MEM_MAP,MEM_FILTER,MEM_ZIP,LENGTH_COUNT_LIST,PULL_EXISTS,EL_MAP,EL_COUNT_LIST]>>
      DEP_REWRITE_TAC[domain_alist_insert]>>
      simp[LENGTH_COUNT_LIST,MEM_MAP,MEM_COUNT_LIST]>>
      simp[MEM_COUNT_LIST]>>
      metis_tac[ADD_COMM])
  )
  >~ [`Inst`]
  >- (
    last_x_assum kall_tac>>
    exists_tac>>
    Cases_on`i`>> (TRY (Cases_on`a`))>> (TRY(Cases_on`m`))>>
    fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def,evaluate_def,LET_THM]
    >~[`Const`]
    >- (
      Cases_on`word_exp st (Const c)`>>
      full_simp_tac(srw_ss())[set_var_def,word_exp_def]>>
      match_mp_tac ssa_locals_rel_set_var>>
      full_simp_tac(srw_ss())[every_var_inst_def,every_var_def])
    >~[`Binop`]
    >-(
      Cases_on`r`>>
      fs[evaluate_def,inst_def,assign_def]>>
      qpat_abbrev_tac `expr = (Op b [Var n0;Z])`>>
      setup_tac>>
      match_mp_tac ssa_locals_rel_set_var>>
      full_simp_tac(srw_ss())[every_var_inst_def,every_var_def])
    >~[`Shift`]
    >- (
      qpat_abbrev_tac`expr = (Shift s (Var n0) Z)`>>
      setup_tac>>
      match_mp_tac ssa_locals_rel_set_var>>
      fs[every_var_inst_def,every_var_def])
    >- ( (*Div*)
      fs[]>>
      Cases_on`get_vars [n1;n0] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 2 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac ssa_locals_rel_get_var>>
      fs[set_vars_def,get_var_def,lookup_alist_insert]>>
      Cases_on`x'`>>Cases_on`x''`>>
      fs[set_var_def,alist_insert_def]>>
      IF_CASES_TAC>>
      fs[lookup_insert,alist_insert_def,insert_shadow,ssa_locals_rel_def,every_var_def,every_var_inst_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`LongMul`]
    >- ( (*LongMul*)
      Cases_on`get_vars [n1;n2] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 2 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      fs[get_vars_def,next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def,evaluate_def,LET_THM]>>
      imp_res_tac ssa_locals_rel_get_var>>
      fs[set_vars_def,get_var_def,lookup_alist_insert]>>
      rename1`lookup (_ n1) cst.locals = SOME xx1`>>
      rename1`lookup (_ n2) cst.locals = SOME xx2`>>
      Cases_on`xx1`>>Cases_on`xx2`>>
      fs[set_var_def,alist_insert_def]
      >- (
        (* is_x64 *)
        `option_lookup ssa n2 ≠ 0` by (
          fs[ssa_locals_rel_def]>>
          qpat_x_assum`lookup n1 _ = _` kall_tac>>
          first_x_assum drule>>
          rfs[domain_lookup,ssa_map_ok_def]>>
          strip_tac>>
          first_x_assum drule>>
          rw[]>>
          fs[is_phy_var_def,option_lookup_def]>>
          CCONTR_TAC>>
          fs[]>>
          qpat_x_assum`B=0n` SUBST_ALL_TAC>>fs[])>>
        fs[lookup_insert,alist_insert_def,insert_shadow,ssa_locals_rel_def,every_var_def,every_var_inst_def]>>
        CONJ_TAC>-
          (rw[]>>metis_tac[])>>
        ntac 2 strip_tac>>
        IF_CASES_TAC>>fs[]>>
        IF_CASES_TAC>>fs[ssa_map_ok_def]>>
        strip_tac>>
        first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>
        rfs[]>>
        fs[domain_lookup]>>
        first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>
        rfs[]>>
        IF_CASES_TAC>>fs[is_phy_var_def]>>
        rw[]>>fs[])
      (* Not needed
      >- (
        gvs[every_var_def,every_var_inst_def]>>
        `na + 8 = (na + 4) + 4` by fs[]>>
        pop_assum SUBST_ALL_TAC>>
        match_mp_tac ssa_locals_rel_insert>>
        reverse CONJ_TAC
        >- (
          simp[]>>
          match_mp_tac ssa_map_ok_extend>>
          metis_tac[convention_partitions])>>
        match_mp_tac ssa_locals_rel_insert>>
        simp[]
      ) *)
    )
    >~[`LongDiv`]
    >- ( (*LongDiv*)
      fs[]>>
      Cases_on`get_vars [n1;n2;n3] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 3 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac ssa_locals_rel_get_var>>fs[set_vars_def,get_var_def,lookup_alist_insert]>>
      `option_lookup ssa n3 ≠ 0 ∧ option_lookup ssa n3 ≠ 6` by
        (fs[ssa_locals_rel_def]>>
        first_x_assum(qspecl_then[`n3`,`x'`]assume_tac)>>
        rfs[domain_lookup,ssa_map_ok_def]>>
        first_x_assum(qspecl_then[`n3`,`v'`] assume_tac)>>
        rfs[]>>
        fs[is_phy_var_def,option_lookup_def]>>
        CCONTR_TAC>>
        fs[]>>
        pop_assum SUBST_ALL_TAC>>fs[])>>
      fs[]>>
      Cases_on`x'`>>Cases_on`x''`>>Cases_on`x'''`>>
      fs[set_var_def,alist_insert_def]>>
      IF_CASES_TAC>>
      fs[lookup_insert,alist_insert_def,insert_shadow,ssa_locals_rel_def,every_var_def,every_var_inst_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      IF_CASES_TAC>>fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`AddCarry`]
    >- ( (* AddCarry *)
      fs[]>>
      Cases_on`get_vars [n0;n1;n2] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 3 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac ssa_locals_rel_get_var>>fs[set_vars_def,get_var_def,lookup_alist_insert]>>
      `option_lookup ssa n0 ≠ 0 ∧ option_lookup ssa n1 ≠ 0` by
        (fs[ssa_locals_rel_def]>>
        first_assum (qspecl_then[`n0`,`x'''`] assume_tac)>>
        first_x_assum(qspecl_then[`n1`,`x''`] assume_tac)>>
        rfs[domain_lookup,ssa_map_ok_def]>>
        first_assum(qspecl_then[`n0`,`v''`] assume_tac)>>
        first_x_assum(qspecl_then[`n1`,`v'`] assume_tac)>>
        rfs[]>>
        fs[is_phy_var_def,option_lookup_def]>>
        CCONTR_TAC>>
        fs[]>>
        pop_assum SUBST_ALL_TAC>>fs[])>>
      fs[]>>
      Cases_on`x'`>>Cases_on`x''`>>Cases_on`x'''`>>fs[set_var_def,alist_insert_def]>>
      qpat_abbrev_tac`w1 = if A then B else C`>>
      qpat_abbrev_tac`w2 = n2w A`>>
      fs[ssa_locals_rel_def,lookup_insert,every_var_def,every_var_inst_def,alist_insert_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      IF_CASES_TAC>>fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`AddOverflow`]
    >- ( (* AddOverflow*)
      fs[]>>
      Cases_on`get_vars [n0;n1] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 2 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac ssa_locals_rel_get_var>>fs[set_vars_def,get_var_def,lookup_alist_insert]>>
      fs[]>>
      Cases_on`x'`>>Cases_on`x''`>>fs[set_var_def,alist_insert_def]>>
      qpat_abbrev_tac`w1 = if A then B else C`>>
      fs[ssa_locals_rel_def,lookup_insert,every_var_def,every_var_inst_def,alist_insert_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      IF_CASES_TAC>>fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`SubOverflow`]
    >- ( (*SubOverflow*)
      fs[]>>
      Cases_on`get_vars [n0;n1] st`>>fs[get_vars_def]>>
      pop_assum mp_tac>>
      ntac 2 FULL_CASE_TAC >>fs[]>>
      disch_then sym_sub_tac>>fs[]>>
      imp_res_tac ssa_locals_rel_get_var>>fs[set_vars_def,get_var_def,lookup_alist_insert]>>
      fs[]>>
      Cases_on`x'`>>Cases_on`x''`>>fs[set_var_def,alist_insert_def]>>
      qpat_abbrev_tac`w1 = if A then B else C`>>
      fs[ssa_locals_rel_def,lookup_insert,every_var_def,every_var_inst_def,alist_insert_def]>>
      CONJ_TAC>-
        (rw[]>>metis_tac[])>>
      ntac 2 strip_tac>>
      IF_CASES_TAC>>fs[]>>
      IF_CASES_TAC>>fs[ssa_map_ok_def]>>
      strip_tac>>
      first_x_assum (qspecl_then[`x`,`y`] assume_tac)>>rfs[]>>
      fs[domain_lookup]>>
      first_x_assum (qspecl_then[`x`,`v'`] assume_tac)>>rfs[]>>
      IF_CASES_TAC>>fs[is_phy_var_def]>>
      rw[]>>fs[])
    >~[`Mem Load _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      Cases_on`x`>>
      full_simp_tac(srw_ss())[mem_load_def]>> full_simp_tac(srw_ss())[GSYM mem_load_def]>>
      BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
      match_mp_tac ssa_locals_rel_set_var>>
      fs[every_var_inst_def,every_var_def])
    >~[`Mem Load8 _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      Cases_on`x`>>
      full_simp_tac(srw_ss())[mem_load_byte_aux_def]>>
      Cases_on`st.memory (byte_align c')`>>fs[]>>
      IF_CASES_TAC>>fs[]>>
      match_mp_tac ssa_locals_rel_set_var>>
      fs[every_var_inst_def,every_var_def])
    >~[`Mem Load32 _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=((Op Add [Var n';A]))`>>
      setup_tac>>
      Cases_on`x`>>
      full_simp_tac(srw_ss())[mem_load_32_def]>>
      Cases_on`st.memory (byte_align c')`>>fs[]>>
      ntac 2 (IF_CASES_TAC>>fs[])>> gvs[] >>
      match_mp_tac ssa_locals_rel_set_var>>
      fs[every_var_inst_def,every_var_def])
    >~[`Mem Store _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      full_simp_tac(srw_ss())[]>>
      setup_tac>>
      Cases_on`x`>>fs[]>>
      Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>imp_res_tac ssa_locals_rel_get_var>>
      fs[option_lookup_def]>>
      Cases_on`mem_store c x' st`>>
      fs[mem_store_def]>>
      IF_CASES_TAC>>fs[])
    >~[`Mem Store8 _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      fs[]>>
      setup_tac>>
      Cases_on`x`>>fs[]>>
      Cases_on`get_var n st`>>
      fs[]>>imp_res_tac ssa_locals_rel_get_var>>
      Cases_on`x`>>fs[option_lookup_def]>>
      CASE_TAC>>fs[])
    >~[`Mem Store32 _ (Addr _ _)`]
    >- (
      qpat_abbrev_tac`expr=Op Add [Var n';A]`>>
      fs[]>>
      setup_tac>>
      Cases_on`x`>>fs[]>>
      Cases_on`get_var n st`>>
      fs[]>>imp_res_tac ssa_locals_rel_get_var>>
      Cases_on`x`>>fs[option_lookup_def]>>
      CASE_TAC>>fs[])
    >~[`FP`]
    >- ( (* FP *)
      Cases_on`f`>>
      fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def,evaluate_def,get_fp_var_def,set_var_def,every_var_def,every_var_inst_def,set_fp_var_def]
      >~[ `FPMovFromReg`]
      >- (
        rw[]
        >~[`Move`]
        >- (
          (* Nasty special case for 32-bit FPMovFromReg *)
          Cases_on`get_var n0 st`>>fs[]>>
          Cases_on`x`>>fs[]>>
          Cases_on`get_var n1 st`>>fs[]>>
          Cases_on`x`>>fs[]>>
          imp_res_tac ssa_locals_rel_get_var>>
          gvs[evaluate_def,domain_lookup,get_vars_def,get_var_def,inst_def,set_vars_def,alist_insert_def,lookup_insert,set_fp_var_def]>>
          gvs[ssa_locals_rel_def,lookup_insert,AllCaseEqs()]>>
          rw[]
          >-  metis_tac[]>>
          first_x_assum drule>>
          rw[domain_lookup]>>
          gvs[ssa_map_ok_def]>>
          first_x_assum drule>>fs[])>>
        fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def,evaluate_def,get_fp_var_def,set_var_def,every_var_def,every_var_inst_def,set_fp_var_def]>>
        every_case_tac>>
        fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def,evaluate_def,get_fp_var_def,set_var_def,every_var_def,every_var_inst_def,set_fp_var_def]>>
        imp_res_tac ssa_locals_rel_get_var>>
        fs[ssa_locals_rel_set_var]>>
        rveq>>fs[state_component_equality])>>
      every_case_tac>>
      fs[next_var_rename_def,ssa_cc_trans_inst_def,inst_def,assign_def,evaluate_def,get_fp_var_def,set_var_def,every_var_def,every_var_inst_def,set_fp_var_def]>>
      imp_res_tac ssa_locals_rel_get_var>>
      fs[ssa_locals_rel_set_var]>>
      rveq>>fs[state_component_equality]>>
      (* Special case for two writes *)
      fs[ssa_locals_rel_def]>>
      (CONJ_TAC>-
        (simp[lookup_insert]>> rw[]>>metis_tac[])
      >>
      simp[lookup_insert]>>ntac 2 strip_tac>>
      IF_CASES_TAC>>simp[]>>
      IF_CASES_TAC>>simp[]>>
      last_x_assum kall_tac>>
      first_x_assum(qspecl_then [`x'`,`y`] assume_tac)>>rfs[]>>
      strip_tac>>
      res_tac>>fs[domain_lookup,ssa_map_ok_def]>>
      res_tac>>fs[]>>
      rw[]>>fs[]))
    )
  >-(*Assign*)
    exp_tac
  >-(*Get*)
    exp_tac
  >-(*Set*)
    exp_tac
  >-(*Store*)
    (exists_tac>>
    full_simp_tac(srw_ss())[]>>
    Cases_on`word_exp st e`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    imp_res_tac ssa_cc_trans_exp_correct>>
    rev_full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[mem_store_def,word_state_eq_rel_def]>>
    rev_full_simp_tac(srw_ss())[]>>
    qpat_x_assum`A=x'''` sym_sub_tac>>
    qpat_x_assum`A=x''` sym_sub_tac>>
    full_simp_tac(srw_ss())[])
  >- ((*MustTerminate*)
    rw[ssa_cc_trans_def]>>
    rpt(pairarg_tac>>gvs[])>>
    fs[evaluate_def,word_state_eq_rel_def]>>
    first_x_assum(qspecl_then[
    `p`,`st with <|clock:=MustTerminate_limit (:'a);termdep:=st.termdep-1|>`,
    `cst with <|clock:=MustTerminate_limit (:'a);termdep:=st.termdep-1|>`,`ssa`,`na`] mp_tac)>>
    size_tac>>
    impl_tac>-
     fs[every_var_def]>>
    strip_tac>>
    qexists_tac`perm'`>>simp[]>>
    IF_CASES_TAC>>fs[]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[AllCaseEqs()])
  >~[`Call`]
  >-(goalStack.print_tac"Slow ssa_cc_trans_correct Call proof">>
    Cases_on`o'`
    >- ((*Tail call*)
      exists_tac>>
      full_simp_tac(srw_ss())[MAP_ZIP]>>
      qpat_abbrev_tac`ls = GENLIST (λx.2*x) (LENGTH l)`>>
      `ALL_DISTINCT ls` by
        (full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_GENLIST]>>
        srw_tac[][]>>DECIDE_TAC)>>
      full_simp_tac(srw_ss())[]>>
      Cases_on`get_vars l st`>>full_simp_tac(srw_ss())[]>>
      imp_res_tac ssa_locals_rel_get_vars>>
      IF_CASES_TAC>>full_simp_tac(srw_ss())[]>>
      `¬bad_dest_args o1 ls` by
        (full_simp_tac(srw_ss())[Abbr`ls`,bad_dest_args_def]>>
        Cases_on`l`>>full_simp_tac(srw_ss())[GENLIST_CONS])>>
      `get_vars ls (set_vars ls x cst) = SOME x` by
        (match_mp_tac get_vars_set_vars_eq>>
        full_simp_tac(srw_ss())[Abbr`ls`,get_vars_length_lemma,LENGTH_MAP]>>
        metis_tac[get_vars_length_lemma])>>
      full_simp_tac(srw_ss())[set_vars_def]>>
      EVERY_CASE_TAC>>
      full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def]>>
      ntac 2 (pop_assum mp_tac)>>
      qpat_abbrev_tac`cst'=cst with <|locals:=A;locals_size := Ls; stack_max := SM; clock:=B|>`>>
      qpat_abbrev_tac`st'=st with <|locals:=A;locals_size := Ls;stack_max := SM; permute:=B;clock:=C|>`>>
      `cst' = st'` by
        (unabbrev_all_tac>>full_simp_tac(srw_ss())[state_component_equality])>>
      rev_full_simp_tac(srw_ss())[]) >>
    cheat)
    (* (*Non tail call*)
    PairCases_on`x`>> full_simp_tac(srw_ss())[] >>
    Q.PAT_ABBREV_TAC`pp = ssa_cc_trans X Y Z` >>
    PairCases_on`pp` >> simp[] >>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def]) >>
    simp_tac std_ss [ssa_cc_trans_def]>>
    LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[evaluate_def,add_ret_loc_def]>>
    ntac 7 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    `domain stack_set ≠ {}` by
      full_simp_tac(srw_ss())[Abbr`stack_set`,domain_fromAList,toAList_not_empty]>>
    `¬bad_dest_args o1 conv_args` by
      (full_simp_tac(srw_ss())[Abbr`conv_args`,Abbr`names`,bad_dest_args_def]>>
      Cases_on`l`>>full_simp_tac(srw_ss())[GENLIST_CONS])>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`]
      mp_tac list_next_var_rename_move_preserve>>
    impl_tac>- (
      srw_tac[][]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >-
        (full_simp_tac(srw_ss())[cut_env_def,Abbr`ls`]>>
        metis_tac[SUBSET_DEF,toAList_domain])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC))
    >>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`ls`,`ssa`,`na`,`stack_mov`,`ssa'`,`na'`] assume_tac list_next_var_rename_move_props_2>>
    Q.ISPECL_THEN [`ls`,`ssa_cut`,`na'`,`ret_mov`,`ssa''`,`na''`] assume_tac list_next_var_rename_move_props_2>>
    Q.ISPECL_THEN [`x2`,`ssa_2_p`,`na_2_p`,`ren_ret_handler`,`ssa_2`,`na_2`] assume_tac ssa_cc_trans_props>>
    rev_full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[MAP_ZIP]>>
    `ALL_DISTINCT conv_args` by
      (full_simp_tac(srw_ss())[Abbr`conv_args`,ALL_DISTINCT_GENLIST]>>
      srw_tac[][]>>DECIDE_TAC)>>
    (*Establish invariants about ssa_cut to use later*)
    `domain ssa_cut = domain x1` by
      (full_simp_tac(srw_ss())[EXTENSION,Abbr`ssa_cut`,domain_inter]>>
      srw_tac[][EQ_IMP_THM]>>
      full_simp_tac(srw_ss())[cut_env_def,SUBSET_DEF]>>
      res_tac>>
      full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒ lookup x ssa' = SOME y` by
      (srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    `ssa_map_ok na' ssa_cut` by
      full_simp_tac(srw_ss())[Abbr`ssa_cut`,ssa_map_ok_inter]>>
    (*Probably need to case split here to deal with the 2 cases*)
  Cases_on`o0`>>full_simp_tac(srw_ss())[]
  >- (
    qpat_x_assum`A=pp0` (sym_sub_tac)>>full_simp_tac(srw_ss())[Abbr`prog`]>>
    qpat_x_assum`A=stack_mov` (sym_sub_tac)>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,Abbr`move_args`]>>
    `LENGTH conv_args = LENGTH names` by
      (unabbrev_all_tac >>full_simp_tac(srw_ss())[])>>
    full_simp_tac(srw_ss())[MAP_ZIP]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    `get_vars names rcst = SOME x` by
      (fs[Abbr`names`]>>
      qpat_assum`get_vars l st = SOME x` mp_tac>>
      qid_spec_tac`x`>>
      qpat_assum`ssa_locals_rel na ssa st.locals cst.locals` mp_tac>>
      qpat_assum`!x y. lookup x st.locals = SOME y ⇒ P` mp_tac>>
      rpt(pop_assum kall_tac)>>
      Induct_on`l`>>rw[get_vars_def,get_var_def]>>
      fs[]>>
      pop_assum mp_tac>>
      ntac 2 (TOP_CASE_TAC>>fs[])>>rw[]>>
      fs[ssa_locals_rel_def]>>res_tac>>fs[domain_lookup,option_lookup_def]>>
      last_x_assum(qspecl_then[`h`,`x'`] assume_tac)>>rfs[])>>
    full_simp_tac(srw_ss())[Abbr`names`]>>
    `LENGTH l = LENGTH x` by
      metis_tac[get_vars_length_lemma]>>
    `get_vars conv_args (set_vars conv_args x rcst) = SOME x` by
      (match_mp_tac get_vars_set_vars_eq>>
      full_simp_tac(srw_ss())[Abbr`ls`,get_vars_length_lemma,LENGTH_MAP])>>
    full_simp_tac(srw_ss())[set_vars_def]>>
    qpat_abbrev_tac `rcst' =
      rcst with locals:= alist_insert conv_args x rcst.locals`>>
    (*Important preservation step*)
    `ssa_locals_rel na' ssa' st.locals rcst'.locals` by
      (full_simp_tac(srw_ss())[Abbr`rcst'`,Abbr`conv_args`]>>
      match_mp_tac ssa_locals_rel_ignore_list_insert>>
      full_simp_tac(srw_ss())[EVERY_MEM,MEM_GENLIST]>>
      srw_tac[][]>>
      is_phy_var_tac) >>
    full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    qabbrev_tac`f = option_lookup ssa'`>>
    (*Try to use cut_env_lemma from word_live*)
    Q.ISPECL_THEN [`x1`,`st.locals`,`rcst'.locals`,`x'`,`f`]
      mp_tac cut_env_lemma>>
    impl_tac>- (
      rfs[Abbr`f`]>>
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      ntac 1 (last_x_assum kall_tac)>>
      srw_tac[][INJ_DEF]>- (
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain]) >>
      full_simp_tac(srw_ss())[option_lookup_def,domain_lookup]>>
      res_tac>>
      full_simp_tac(srw_ss())[]>>
      qpat_x_assum`A=SOME v` SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[])
  >>
    srw_tac[][Abbr`rcst'`]>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
    IF_CASES_TAC  >>
    full_simp_tac(srw_ss())[call_env_def,flush_state_def] >-
     fs [push_env_def, env_to_list_def, stack_size_def, stack_size_frame_def,
         state_component_equality] >>
    qpat_abbrev_tac`rcst' = rcst with locals := A`>>
    Q.ISPECL_THEN[
      `y:'a word_loc num_map`,`x'`,`st with clock := st.clock-1`,
      `f`,`rcst' with clock := st.clock-1`,`NONE:(num#'a wordLang$prog#num#num)option`,
       `NONE:(num#'a wordLang$prog#num#num)option`,`λn. rcst.permute (n+1)`]
      mp_tac (GEN_ALL push_env_s_val_eq)>>
    impl_tac>-
      rev_full_simp_tac(srw_ss())[Abbr`rcst'`]
    >>
    strip_tac>>
    rev_full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def]>>
    qabbrev_tac `envx = push_env x'
            (NONE:(num # 'a wordLang$prog #num #num)option)
            (st with <|permute := perm; clock := st.clock − 1|>) with
          <|locals := fromList2 (q) ; locals_size := r' ;
            stack_max := OPTION_MAP2 MAX (push_env x' NONE
              (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
              (OPTION_MAP2 $+(stack_size (push_env x' NONE
               (st with <|permute := perm; clock := st.clock - 1|>)).stack) r')|>`>>
    qpat_abbrev_tac `envy = (push_env y A B) with <| locals := C; locals_size := lsz; stack_max := SM;
                     clock := _ |>`>>
    assume_tac evaluate_stack_swap>>
    pop_assum(qspecl_then [`q'`,`envx`] mp_tac)>>
    ntac 2 FULL_CASE_TAC >-
      (srw_tac[][]>>qexists_tac`perm`>>
       full_simp_tac(srw_ss())[dec_clock_def]) >>
    `envx with stack := envy.stack = envy` by
      (unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,state_component_equality]>>
      full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def, stack_size_def, stack_size_frame_def]) >>
    `s_val_eq envx.stack envy.stack` by
      (unabbrev_all_tac>> simp[] >> full_simp_tac(srw_ss())[])>>
    FULL_CASE_TAC
    >- (
      strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
      impl_tac>-
      (unabbrev_all_tac>> simp[])>>
      strip_tac>>full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[]>>
      (*Backwards chaining*)
      IF_CASES_TAC>-
        (qexists_tac`perm`>>full_simp_tac(srw_ss())[])>>
      Q.ISPECL_THEN [`(rcst' with clock := st.clock-1)`,
                    `r with stack := st'`,`y`,
                    `NONE:(num#'a wordLang$prog#num#num)option`]
                    assume_tac push_env_pop_env_s_key_eq>>
      Q.ISPECL_THEN [`(st with <|permute:=perm;clock := st.clock-1|>)`,
                    `r`,`x'`,
                    `NONE:(num#'a wordLang$prog#num#num)option`]
                    assume_tac push_env_pop_env_s_key_eq>>
      (*This went missing somewhere..*)
      `rcst'.clock = st.clock` by
        full_simp_tac(srw_ss())[Abbr`rcst'`]>>
      pop_assum SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[Abbr`envy`,Abbr`envx`,state_component_equality]>>
      rev_full_simp_tac(srw_ss())[]>>
      (*Now is a good place to establish the invariant ssa_locals_rel*)
      `ssa_locals_rel na' ssa_cut y'.locals y''.locals ∧
       word_state_eq_rel y' y''` by
      (full_simp_tac(srw_ss())[state_component_equality]>>
      `s_key_eq y'.stack y''.stack` by
       metis_tac[s_key_eq_trans,s_key_eq_sym] >>
      Q.ISPECL_THEN [`y''`, `y'`,  `st'`, `r`]
        assume_tac (GEN_ALL pop_env_frame) >>
      rev_full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
      full_simp_tac(srw_ss())[LET_THM,ssa_locals_rel_def]>>
      srw_tac[][]
      >-
        (ntac 20 (last_x_assum kall_tac)>>
        res_tac>>
        qpat_x_assum`A=domain(fromAList l'')` (sym_sub_tac)>>
        full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def]>>
        qexists_tac`x''`>>full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[Abbr`ssa_cut`,domain_inter,lookup_inter]>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
        metis_tac[domain_lookup])
      >-
        full_simp_tac(srw_ss())[domain_lookup]
      >-
        (`x'' ∈ domain ssa_cut` by metis_tac[domain_lookup]>>
        full_simp_tac(srw_ss())[domain_lookup]>>
        ntac 20 (last_x_assum kall_tac)>>
        res_tac>>
        `v = f x''` by full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def]>>
        full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
        full_simp_tac(srw_ss())[s_key_eq_def,s_val_eq_def]>>
        Cases_on`opt`>>Cases_on`opt'`>>
        full_simp_tac(srw_ss())[s_frame_key_eq_def,s_frame_val_eq_def]>>
        full_simp_tac(srw_ss())[lookup_fromAList]>>
        imp_res_tac key_map_implies>>
        rev_full_simp_tac(srw_ss())[]>>
        `l'' = ZIP(MAP FST l'',MAP SND l'')` by full_simp_tac(srw_ss())[ZIP_MAP_FST_SND_EQ]>>
        pop_assum SUBST1_TAC>>
        pop_assum (SUBST1_TAC o SYM)>>
        match_mp_tac ALOOKUP_key_remap_2>>
        full_simp_tac(srw_ss())[]>>CONJ_TAC>>
        metis_tac[LENGTH_MAP,ZIP_MAP_FST_SND_EQ])
      >>
        full_simp_tac(srw_ss())[cut_env_def,SUBSET_DEF]>>
        `x'' ∈ domain st.locals` by full_simp_tac(srw_ss())[domain_lookup]>>
        full_simp_tac(srw_ss())[domain_lookup])>>
      full_simp_tac(srw_ss())[]>>
      (*We set variable 2 but it is never in the
        locals so the ssa_locals_rel property is preserved*)
      `ssa_locals_rel na' ssa_cut y'.locals
        (set_var 2 w0 y'').locals` by
        (match_mp_tac ssa_locals_rel_ignore_set_var>>
        full_simp_tac(srw_ss())[]>> is_phy_var_tac)>>
      Q.SPECL_THEN [`y'`,`ssa_cut`,`na'+2`,`(MAP FST (toAList x1))`
                   ,`(set_var 2 w0 y'')`] mp_tac
                   list_next_var_rename_move_preserve>>
      impl_tac>-
      (srw_tac[][]
      >-
        (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        full_simp_tac(srw_ss())[]>>
        qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
        rev_full_simp_tac(srw_ss())[])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,set_toAList_keys]
      >-
        full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList,Abbr`ls`]
      >-
        (`na' ≤ na'+2`by DECIDE_TAC>>
        metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
      >>
        full_simp_tac(srw_ss())[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      full_simp_tac(srw_ss())[Abbr`mov_ret_handler`,evaluate_def]>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      `get_vars [2] rcst'' = SOME [w0]` by
        (full_simp_tac(srw_ss())[ssa_map_ok_more,DECIDE ``na:num ≤ na+2``]>>
        `¬ is_phy_var (na'+2)` by
          metis_tac[is_stack_var_flip,convention_partitions]>>
        full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>
        first_x_assum(qspec_then`2` assume_tac)>>
        full_simp_tac(srw_ss())[is_phy_var_def,set_var_def])>>
      full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
      qabbrev_tac`res_st = (set_var x0 w0 y')`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      `ssa_locals_rel na_2_p ssa_2_p res_st.locals res_rcst.locals` by
        (unabbrev_all_tac>>full_simp_tac(srw_ss())[next_var_rename_def,set_var_def]>>
        rpt VAR_EQ_TAC>>
        qpat_x_assum`A=fromAList l'` sym_sub_tac>>
        match_mp_tac ssa_locals_rel_set_var>>
        full_simp_tac(srw_ss())[every_var_def]>>
        rev_full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      first_x_assum(qspecl_then[`x2`,`res_st`,`res_rcst`,`ssa_2_p`,`na_2_p`] mp_tac)>>
      size_tac>>impl_tac>-
      (full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`,Abbr`res_rcst`,set_var_def]>>
      full_simp_tac(srw_ss())[every_var_def,next_var_rename_def]>>srw_tac[][]>>
      TRY
        (match_mp_tac every_var_mono>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      metis_tac[is_alloc_var_add,ssa_map_ok_extend,convention_partitions])>>
      srw_tac[][]>>
      qspecl_then[`q'`,`push_env x' (NONE:(num#'a wordLang$prog#num#num) option)
            (st with <|permute := perm; clock := st.clock − 1|>) with
          <|locals := fromList2 q; locals_size := r' ;
            stack_max := OPTION_MAP2 MAX (push_env x' NONE
              (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
              (OPTION_MAP2 $+ (stack_size (push_env x' NONE  (st with
               <|permute := perm; clock := st.clock - 1|>)).stack) r')|>` ,`perm'`]
      assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = push_env A B C with <|locals := D ; locals_size := Ls; stack_max := SM|>`>>
      qpat_x_assum `A = (SOME B,C)` mp_tac>>
      qpat_abbrev_tac `env2 = push_env A B C with
                    <|locals:=D; locals_size := Ls; stack_max := SM ; permute:=E|>`>>
      strip_tac>>
      `env1 = env2` by
      (unabbrev_all_tac>>
      simp[push_env_def,LET_THM,env_to_list_def ,state_component_equality,FUN_EQ_THM,
           stack_size_def, stack_size_frame_def])>>
      full_simp_tac(srw_ss())[]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])
    >- (
      (*Excepting without handler*)
      full_simp_tac(srw_ss())[]>>strip_tac>>
      imp_res_tac s_val_eq_LASTN_exists>>
      first_x_assum(qspecl_then[`envy.stack`,`e'`,`ls'`] assume_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      qexists_tac`perm`>>
      `ls'''=ls'` by
        (unabbrev_all_tac>>
        full_simp_tac(srw_ss())[push_env_def,env_to_list_def,LET_THM]>>
        Cases_on`st.handler < LENGTH st.stack`
        >-
          (imp_res_tac LASTN_TL>>
          rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[])
        >>
          `st.handler = LENGTH st.stack` by DECIDE_TAC>>
          rpt (qpat_x_assum `LASTN A B = C` mp_tac)>-
          simp[LASTN_LENGTH_cond])>>
      full_simp_tac(srw_ss())[]>>
      `lss = lss'` by
        (match_mp_tac LIST_EQ_MAP_PAIR>>full_simp_tac(srw_ss())[]>>
        qsuff_tac `e = e''`>-metis_tac[]>>
        unabbrev_all_tac>>
        full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
        `st.handler < LENGTH st.stack` by
          (SPOSE_NOT_THEN assume_tac>>
          `st.handler = LENGTH st.stack` by DECIDE_TAC>>
          ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
          simp[LASTN_LENGTH2])>>
        ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
        full_simp_tac(srw_ss())[LASTN_TL])>>
      metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans])
    >>
      (* 4 subgoals *)
      rw[]>>
      qexists_tac`perm`>>fs[]>>
      pop_assum(qspec_then`envy.stack` mp_tac)>>
      (impl_tac>- (unabbrev_all_tac>>full_simp_tac(srw_ss())[]))>>
      srw_tac[][]>>full_simp_tac(srw_ss())[])
  >>
    (*Handler reasoning*)
    qpat_x_assum`A=(pp0,pp1,pp2)` mp_tac>>PairCases_on`x''`>>full_simp_tac(srw_ss())[]>>
    LET_ELIM_TAC>>
    rev_full_simp_tac(srw_ss())[]>>
    qpat_x_assum`A=pp0` (sym_sub_tac)>>full_simp_tac(srw_ss())[Abbr`prog'`]>>
    qpat_x_assum`A=stack_mov` (sym_sub_tac)>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,Abbr`move_args`]>>
    `LENGTH conv_args = LENGTH names` by
      (unabbrev_all_tac >>full_simp_tac(srw_ss())[])>>
    full_simp_tac(srw_ss())[MAP_ZIP]>>
    imp_res_tac ssa_locals_rel_get_vars>>
    `get_vars names rcst = SOME x` by
      (fs[Abbr`names`]>>
      qpat_assum`get_vars l st = SOME x` mp_tac>>
      qid_spec_tac`x`>>
      qpat_assum`ssa_locals_rel na ssa st.locals cst.locals` mp_tac>>
      qpat_assum`!x y. lookup x st.locals = SOME y ⇒ P` mp_tac>>
      rpt(pop_assum kall_tac)>>
      Induct_on`l`>>rw[get_vars_def,get_var_def]>>
      fs[]>>
      pop_assum mp_tac>>
      ntac 2 (TOP_CASE_TAC>>fs[])>>rw[]>>
      fs[ssa_locals_rel_def]>>res_tac>>fs[domain_lookup,option_lookup_def]>>
      last_x_assum(qspecl_then[`h`,`x'`] assume_tac)>>rfs[])>>
    full_simp_tac(srw_ss())[Abbr`names`]>>
    `LENGTH l = LENGTH x` by
      metis_tac[get_vars_length_lemma]>>
    `get_vars conv_args (set_vars conv_args x rcst) = SOME x` by
      (match_mp_tac get_vars_set_vars_eq>>
      full_simp_tac(srw_ss())[Abbr`ls`,get_vars_length_lemma,LENGTH_MAP])>>
    full_simp_tac(srw_ss())[set_vars_def]>>
    qpat_abbrev_tac `rcst' =
      rcst with locals:= alist_insert conv_args x rcst.locals`>>
    (*Important preservation lemma*)
    `ssa_locals_rel na' ssa' st.locals rcst'.locals` by
      (full_simp_tac(srw_ss())[Abbr`rcst'`,Abbr`conv_args`]>>
      match_mp_tac ssa_locals_rel_ignore_list_insert>>
      full_simp_tac(srw_ss())[EVERY_MEM,MEM_GENLIST]>>
      srw_tac[][]>>
      is_phy_var_tac) >>
    full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    qabbrev_tac`f = option_lookup ssa'`>>
    (*Try to use cut_env_lemma from word_live*)
    Q.ISPECL_THEN [`x1`,`st.locals`,`rcst'.locals`,`x'`,`f`]
      mp_tac cut_env_lemma>>
    impl_tac>- (
      rfs[Abbr`f`]>>
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      srw_tac[][INJ_DEF]>- (
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain])
      >>
      ntac 20 (last_x_assum kall_tac)>>
      full_simp_tac(srw_ss())[option_lookup_def,domain_lookup]>>
      res_tac>>
      full_simp_tac(srw_ss())[]>>
      qpat_x_assum`A=SOME v` SUBST_ALL_TAC>>full_simp_tac(srw_ss())[])
    >>
    srw_tac[][Abbr`rcst'`]>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[call_env_def,flush_state_def]
    >- fs [push_env_def, env_to_list_def, stack_size_def, stack_size_frame_def,
         state_component_equality] >>
    qpat_abbrev_tac`rcst' = rcst with locals := A`>>
    Q.ISPECL_THEN
      [`y:'a word_loc num_map`,`x'`,`st with clock := st.clock-1`,
      `f`,`rcst' with clock := st.clock-1`,`SOME(2:num,cons_exc_handler,x''2,x''3)`,
       `SOME (x''0,x''1,x''2,x''3)`,`λn. rcst.permute (n+1)`]
      mp_tac (GEN_ALL push_env_s_val_eq)>>
    impl_tac>-
      rev_full_simp_tac(srw_ss())[Abbr`rcst'`]
    >>
    strip_tac>>
    rev_full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def]>>
    qabbrev_tac `envx = push_env x' (SOME (x''0,x''1,x''2,x''3))
            (st with <|permute := perm; clock := st.clock − 1|>) with
           <|locals := fromList2 (q) ; locals_size := r';
             stack_max :=
              OPTION_MAP2 MAX (push_env x' (SOME (x''0,x''1,x''2,x''3))
               (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
               (OPTION_MAP2 $+ (stack_size(push_env x' (SOME (x''0,x''1,x''2,x''3))
               (st with <|permute := perm; clock := st.clock - 1|>)).stack) r')|>`>>
    qpat_abbrev_tac `envy = (push_env y A B) with <| locals := C; locals_size := lsz; stack_max := SM;
                     clock := _ |>`>>
    assume_tac evaluate_stack_swap>>
    pop_assum(qspecl_then [`q'`,`envx`] mp_tac)>>
    ntac 2 FULL_CASE_TAC>-
      (srw_tac[][]>>qexists_tac`perm`>>
       full_simp_tac(srw_ss())[dec_clock_def])>>
    `envx with stack := envy.stack = envy` by
      (unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,state_component_equality]>>
      full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def, stack_size_def, stack_size_frame_def])>>
    `s_val_eq envx.stack envy.stack` by
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[]>>simp[])>>
    (*More props theorems that will be useful*)
    `ssa_map_ok na_2_p ssa_2_p ∧ is_alloc_var na_2_p` by
      (full_simp_tac(srw_ss())[next_var_rename_def]>>
      rpt VAR_EQ_TAC>>srw_tac[][]
      >-
        (match_mp_tac ssa_map_ok_extend>>
        full_simp_tac(srw_ss())[]>>metis_tac[convention_partitions])
      >>
        metis_tac[is_alloc_var_add])>>
    full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`x''1`,`ssa_3_p`,`na_3_p`,`ren_exc_handler`,`ssa_3`,`na_3`] mp_tac ssa_cc_trans_props>>
    impl_keep_tac>-
      (full_simp_tac(srw_ss())[next_var_rename_def]>>
      rpt VAR_EQ_TAC>>srw_tac[][]
      >-
        (match_mp_tac ssa_map_ok_extend>>
        full_simp_tac(srw_ss())[]>>srw_tac[][]>-
          (match_mp_tac (GEN_ALL ssa_map_ok_more)>>
          qexists_tac`na''`>>
          full_simp_tac(srw_ss())[]>>DECIDE_TAC)>>
        metis_tac[convention_partitions])
      >>
        metis_tac[is_alloc_var_add])>>
    strip_tac>>
    FULL_CASE_TAC
    >- (
      strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
      impl_tac>-
      (unabbrev_all_tac>> full_simp_tac(srw_ss())[])>>
      strip_tac>>full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[]>>
      (*Backwards chaining*)
      IF_CASES_TAC>-
        (qexists_tac`perm`>>full_simp_tac(srw_ss())[])>>
      Q.ISPECL_THEN [`(rcst' with clock := st.clock-1)`,
                    `r with stack := st'`,`y`,
                    `SOME (2:num,cons_exc_handler,x''2,x''3)`]
                    assume_tac push_env_pop_env_s_key_eq>>
      Q.ISPECL_THEN [`(st with <|permute:=perm;clock := st.clock-1|>)`,
                    `r`,`x'`,
                    `SOME (x''0,x''1,x''2,x''3)`]
                    assume_tac push_env_pop_env_s_key_eq>>
      (*This went missing somewhere..*)
      `rcst'.clock = st.clock` by full_simp_tac(srw_ss())[Abbr`rcst'`]>>
      pop_assum SUBST_ALL_TAC>>
      rev_full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[Abbr`envy`,Abbr`envx`,state_component_equality]>>
      rev_full_simp_tac(srw_ss())[] >>
      (*Now is a good place to establish the invariant ssa_locals_rel*)
      `ssa_locals_rel na' ssa_cut y'.locals y''.locals ∧
       word_state_eq_rel y' y''` by
      (full_simp_tac(srw_ss())[state_component_equality]>>
      `s_key_eq y'.stack y''.stack` by
        metis_tac[s_key_eq_trans,s_key_eq_sym]>>
      Q.ISPECL_THEN [`y''`, `y'`,  `st'`, `r`]
        assume_tac (GEN_ALL pop_env_frame) >>
      rev_full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
      full_simp_tac(srw_ss())[LET_THM,ssa_locals_rel_def]>>
      srw_tac[][]
      >-
        (ntac 20 (last_x_assum kall_tac)>>
        res_tac>>
        qpat_x_assum`A=domain(fromAList l'')` (sym_sub_tac)>>
        full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def]>>
        qexists_tac`x''`>>full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[Abbr`ssa_cut`,domain_inter,lookup_inter]>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
        metis_tac[domain_lookup])
      >-
        full_simp_tac(srw_ss())[domain_lookup]
      >-
        (`x'' ∈ domain ssa_cut` by metis_tac[domain_lookup]>>
        full_simp_tac(srw_ss())[domain_lookup]>>
        ntac 20 (last_x_assum kall_tac)>>
        res_tac>>
        `v = f x''` by full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def]>>
        full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
        full_simp_tac(srw_ss())[s_key_eq_def,s_val_eq_def]>>
        Cases_on`opt`>>Cases_on`opt'`>>
        full_simp_tac(srw_ss())[s_frame_key_eq_def,s_frame_val_eq_def]>>
        full_simp_tac(srw_ss())[lookup_fromAList]>>
        imp_res_tac key_map_implies>>
        rev_full_simp_tac(srw_ss())[]>>
        `l'' = ZIP(MAP FST l'',MAP SND l'')` by full_simp_tac(srw_ss())[ZIP_MAP_FST_SND_EQ]>>
        pop_assum SUBST1_TAC>>
        pop_assum (SUBST1_TAC o SYM)>>
        match_mp_tac ALOOKUP_key_remap_2>>
        full_simp_tac(srw_ss())[]>>CONJ_TAC>>
        metis_tac[LENGTH_MAP,ZIP_MAP_FST_SND_EQ])
      >>
        full_simp_tac(srw_ss())[cut_env_def,SUBSET_DEF]>>
        `x'' ∈ domain st.locals` by full_simp_tac(srw_ss())[domain_lookup]>>
        full_simp_tac(srw_ss())[domain_lookup])>>
      full_simp_tac(srw_ss())[]>>
      (*We set variable 2 but it is never in the
        locals so the ssa_locals_rel property is preserved*)
      `ssa_locals_rel na' ssa_cut y'.locals
        (set_var 2 w0 y'').locals` by
        (match_mp_tac ssa_locals_rel_ignore_set_var>>
        full_simp_tac(srw_ss())[]>> is_phy_var_tac)>>
      Q.ISPECL_THEN [`y'`,`ssa_cut`,`na'+2`,`(MAP FST (toAList x1))`
                   ,`(set_var 2 w0 y'')`] mp_tac
                   list_next_var_rename_move_preserve>>
      impl_tac>-
      (srw_tac[][]
      >-
        (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        full_simp_tac(srw_ss())[]>>
        qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
        rev_full_simp_tac(srw_ss())[])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,set_toAList_keys]
      >-
        full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList,Abbr`ls`]
      >-
        (`na' ≤ na'+2`by DECIDE_TAC>>
        metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
      >>
        full_simp_tac(srw_ss())[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      full_simp_tac(srw_ss())[Abbr`cons_ret_handler`,Abbr`mov_ret_handler`,evaluate_def]>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      `get_vars [2] rcst'' = SOME [w0]` by
        (full_simp_tac(srw_ss())[ssa_map_ok_more,DECIDE ``na:num ≤ na+2``]>>
        `¬ is_phy_var (na'+2)` by
          metis_tac[is_stack_var_flip,convention_partitions]>>
        full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>
        first_x_assum(qspec_then`2` assume_tac)>>
        full_simp_tac(srw_ss())[is_phy_var_def,set_var_def])>>
      full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
      qabbrev_tac`res_st = (set_var x0 w0 y')`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      `ssa_locals_rel na_2_p ssa_2_p res_st.locals res_rcst.locals` by
        (unabbrev_all_tac>>full_simp_tac(srw_ss())[next_var_rename_def,set_var_def]>>
        rpt VAR_EQ_TAC>>
        qpat_x_assum`A=fromAList l'` sym_sub_tac>>
        match_mp_tac ssa_locals_rel_set_var>>
        full_simp_tac(srw_ss())[every_var_def]>>
        rev_full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      first_x_assum(qspecl_then[`x2`,`res_st`,`res_rcst`,`ssa_2_p`,`na_2_p`] mp_tac)>>
      size_tac>>impl_tac>-
      (full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`,
        Abbr`res_rcst`,set_var_def]>>
      full_simp_tac(srw_ss())[every_var_def,next_var_rename_def]>>srw_tac[][]>>
      TRY
        (match_mp_tac every_var_mono>>
        qexists_tac `λx. x <na`>>full_simp_tac(srw_ss())[]>>
        srw_tac[][]>>DECIDE_TAC) >>
      metis_tac[is_alloc_var_add,ssa_map_ok_extend,convention_partitions])>>
      srw_tac[][]>>
      Q.ISPECL_THEN[`q'`,`push_env x' (SOME(x''0,x''1,x''2,x''3))
            (st with <|permute := perm; clock := st.clock − 1|>) with
           <|locals := fromList2 q; locals_size := r' ;
             stack_max :=  OPTION_MAP2 MAX(push_env x' (SOME (x''0,x''1,x''2,x''3))
               (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
               (OPTION_MAP2 $+(stack_size (push_env x' (SOME (x''0,x''1,x''2,x''3))
               (st with <|permute := perm; clock := st.clock - 1|>)).stack) r')|>`,`perm'`]
      assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = push_env A B C with
      <|locals := D ; locals_size := Ls; stack_max := SM|>`>>
      qpat_x_assum `A = (SOME B,C)` mp_tac>>
      qpat_abbrev_tac `env2 = push_env A B C with
                    <|locals:=D; locals_size := Ls; stack_max := SM; permute:=E|>`>>
      strip_tac>>
      `env1 = env2` by
      (unabbrev_all_tac>>
      simp[push_env_def,LET_THM,env_to_list_def,
           state_component_equality,FUN_EQ_THM, stack_size_def, stack_size_frame_def])>>
      full_simp_tac(srw_ss())[]>>
      Cases_on`evaluate(x2,res_st with permute:=perm')`>>
      Cases_on`evaluate(ren_ret_handler,res_rcst)`>>
      full_simp_tac(srw_ss())[]>>
      Cases_on`q'''`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q''`>>full_simp_tac(srw_ss())[]>>
      Q.ISPECL_THEN [`na_3`,`ssa_2`,`ssa_3`] mp_tac fix_inconsistencies_correctL>>
      `na_2 ≤ na_3` by
       (full_simp_tac(srw_ss())[next_var_rename_def]>>
       rpt VAR_EQ_TAC>>
       DECIDE_TAC)>>
      impl_tac>-
        (rev_full_simp_tac(srw_ss())[]>>
       metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      srw_tac[][]>>
      pop_assum (qspecl_then[`r''`,`r'''`] mp_tac)>>
      impl_tac>-
        (metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(ret_cons,r''')`>>full_simp_tac(srw_ss())[word_state_eq_rel_def])
    >- ( (*Excepting with handler*)
      full_simp_tac(srw_ss())[]>>strip_tac>>
      imp_res_tac s_val_eq_LASTN_exists>>
      first_x_assum(qspecl_then[`envy.stack`,`e'`,`ls'`] assume_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      rpt (qpat_x_assum `LASTN A B = C` mp_tac)>>
      simp[LASTN_LENGTH_cond]>>
      rpt strip_tac>>
      full_simp_tac(srw_ss())[domain_fromAList]>>
      imp_res_tac list_rearrange_keys>>
      `set (MAP FST lss') = domain y` by
        (qpat_x_assum`A=MAP FST lss'` (SUBST1_TAC o SYM)>>
        full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][EXISTS_PROD]>>
        simp[MEM_MAP,QSORT_MEM]>>srw_tac[][EQ_IMP_THM]
        >-
          (Cases_on`y'`>>
          full_simp_tac(srw_ss())[MEM_toAList]>>
          imp_res_tac domain_lookup>>
          metis_tac[])
        >>
          full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList]>>
          metis_tac[domain_lookup])>>
      `domain x' = set (MAP FST lss)` by
        (qpat_x_assum `A = MAP FST lss` (SUBST1_TAC o SYM)>>
          full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,QSORT_MEM,MEM_toAList
            ,EXISTS_PROD,domain_lookup])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
      rev_full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[domain_fromAList]>>
      IF_CASES_TAC>-
        (qexists_tac`perm`>>full_simp_tac(srw_ss())[])>>
      qabbrev_tac`ssa_cut = inter ssa' x1`>>
      qpat_abbrev_tac`cres=r with <|locals:= A;stack := B;handler:=C|>`>>
      `ssa_locals_rel na' ssa_cut r.locals cres.locals ∧
       word_state_eq_rel r cres` by
      (full_simp_tac(srw_ss())[Abbr`cres`,LET_THM,ssa_locals_rel_def,state_component_equality]>>
      srw_tac[][Abbr`ssa_cut`]
      >-
        (ntac 20 (last_x_assum kall_tac)>>
        full_simp_tac(srw_ss())[domain_fromAList,option_lookup_def,lookup_inter]>>
        EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
        qexists_tac`x''`>>full_simp_tac(srw_ss())[]>>
        metis_tac[EXTENSION,domain_lookup])
      >-
        (`x'' ∈ domain (fromAList lss)` by metis_tac[domain_lookup]>>
        full_simp_tac(srw_ss())[domain_fromAList]>>
        qpat_x_assum`A=MAP FST lss` sym_sub_tac>>
        metis_tac[MEM_MAP,mem_list_rearrange])
      >-
        (`x'' ∈ domain (fromAList lss)` by metis_tac[domain_lookup]>>
        full_simp_tac(srw_ss())[domain_fromAList]>>
        `x'' ∈ domain x'` by metis_tac[MEM_MAP,mem_list_rearrange]>>
        `x'' ∈ domain ssa' ∧ x'' ∈ domain x1` by
          (full_simp_tac(srw_ss())[cut_env_def,EXTENSION,domain_inter]>>
          metis_tac[])>>
        `THE (lookup x'' (inter ssa' x1)) = option_lookup ssa' x''` by
          full_simp_tac(srw_ss())[lookup_inter,option_lookup_def,domain_lookup]>>
        full_simp_tac(srw_ss())[lookup_fromAList]>>
        `lss' = ZIP(MAP FST lss',MAP SND lss')` by full_simp_tac(srw_ss())[ZIP_MAP_FST_SND_EQ]>>
        pop_assum SUBST_ALL_TAC>>
        `lss = ZIP(MAP FST lss,MAP SND lss)` by full_simp_tac(srw_ss())[ZIP_MAP_FST_SND_EQ]>>
        pop_assum SUBST_ALL_TAC>>
        full_simp_tac(srw_ss())[MAP_ZIP]>>
        imp_res_tac key_map_implies>>
        rev_full_simp_tac(srw_ss())[]>>
        pop_assum sym_sub_tac>>
        qpat_x_assum `A=MAP SND lss'` sym_sub_tac>>
        match_mp_tac ALOOKUP_key_remap_2>>
        srw_tac[][])
      >-
        (`x'' ∈ domain (fromAList lss)` by metis_tac[domain_lookup]>>
        full_simp_tac(srw_ss())[domain_fromAList]>>
        qpat_x_assum`A=MAP FST lss` sym_sub_tac>>
        `x'' ∈ domain x'` by metis_tac[MEM_MAP,mem_list_rearrange]>>
        full_simp_tac(srw_ss())[EXTENSION,every_var_def]>>
        first_x_assum(qspec_then`x''` assume_tac)>>
        rfs[every_name_def,toAList_domain,EVERY_MEM]>>
        `x'' < na` by full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)
      >>
        full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
        metis_tac[s_key_eq_trans,s_val_and_key_eq])>>
      `ssa_locals_rel na' ssa_cut r.locals
        (set_var 2 w0 cres).locals` by
        (match_mp_tac ssa_locals_rel_ignore_set_var>>
        full_simp_tac(srw_ss())[]>>srw_tac[][]>> is_phy_var_tac)>>
      Q.SPECL_THEN [`r`,`ssa_cut`,`na'+2`,`(MAP FST (toAList x1))`
                   ,`(set_var 2 w0 cres)`] mp_tac
                   list_next_var_rename_move_preserve>>
      impl_tac>-
      (srw_tac[][]
      >-
        (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        full_simp_tac(srw_ss())[]>>
        qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
        rev_full_simp_tac(srw_ss())[])
      >-
        full_simp_tac(srw_ss())[domain_fromAList,set_toAList_keys]
      >-
        full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList]
      >-
        (`na' ≤ na'+2`by DECIDE_TAC>>
        metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
      >>
        full_simp_tac(srw_ss())[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      rev_full_simp_tac(srw_ss())[LET_THM,evaluate_def]>>
      `get_vars [2] rcst' = SOME [w0]` by
        (full_simp_tac(srw_ss())[ssa_map_ok_more,DECIDE ``na:num ≤ na+2``]>>
        `¬ is_phy_var (na'+2)` by
          metis_tac[is_stack_var_flip,convention_partitions]>>
        full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>
        first_x_assum(qspec_then`2` assume_tac)>>
        full_simp_tac(srw_ss())[is_phy_var_def,set_var_def])>>
      full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
      qabbrev_tac`res_st = (set_var x''0 w0 r)`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      `ssa_locals_rel na_3_p ssa_3_p res_st.locals res_rcst.locals` by
        (unabbrev_all_tac>>full_simp_tac(srw_ss())[next_var_rename_def,set_var_def]>>
        rpt VAR_EQ_TAC>>
        qpat_x_assum`A=fromAList lss` sym_sub_tac>>
        match_mp_tac ssa_locals_rel_set_var>>
        full_simp_tac(srw_ss())[every_var_def]>>
        `na'' ≤ n'` by DECIDE_TAC>>
        srw_tac[][]>>
        TRY(DECIDE_TAC)>>
        metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      first_x_assum(qspecl_then[`x''1`,`res_st`,`res_rcst`,`ssa_3_p`,`na_3_p`] mp_tac)>>
      size_tac>>impl_tac>-
      (full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`,Abbr`res_rcst`,set_var_def]>>
      full_simp_tac(srw_ss())[every_var_def,next_var_rename_def]>>srw_tac[][]>>
      rev_full_simp_tac(srw_ss())[]>>
      match_mp_tac every_var_mono>>
      HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
      DECIDE_TAC)>>
      srw_tac[][]>>
      qspecl_then[`q'`,`push_env x' (SOME (x''0,x''1,x''2,x''3))
            (st with <|permute := perm; clock := st.clock − 1|>) with
          <| locals := fromList2 q; locals_size := r';
             stack_max :=  OPTION_MAP2 MAX (OPTION_MAP2 MAX st.stack_max
          (stack_size (StackFrame st.locals_size (list_rearrange (perm 0)
      (QSORT key_val_compare (toAList x'))) (SOME (st.handler,x''2,x''3))::st.stack)))
        (OPTION_MAP2 $+ (stack_size (StackFrame st.locals_size
       (list_rearrange (perm 0)(QSORT key_val_compare (toAList x')))
      (SOME (st.handler,x''2,x''3))::st.stack)) r')|>`,`perm'`]
        assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM,push_env_def,env_to_list_def]>>
      (*"Hot-swap" the suffix of perm, maybe move into lemma*)
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = st with <|locals:= A; locals_size := Ls; stack:= B;stack_max := SM;
         permute:= C; handler:=D;clock:=E|>`>>
      qpat_x_assum `A = (SOME B,C)` mp_tac>>
      qpat_abbrev_tac `env2 = st with <|locals:= A; locals_size := Ls; stack:= B; stack_max := SM;
        permute:= C; handler:=D;clock:=E|>`>>
      strip_tac>>
      `env1 = env2` by
      (unabbrev_all_tac>>
      rpt(pop_assum kall_tac)>>
      simp[state_component_equality,FUN_EQ_THM, stack_size_def, stack_size_frame_def])>>
      full_simp_tac(srw_ss())[]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
      Cases_on`evaluate(x''1,res_st with permute:=perm')`>>
      Cases_on`evaluate(ren_exc_handler,res_rcst)`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q'''`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q''`>>full_simp_tac(srw_ss())[]>>
      (*Fix inconsistencies*)
      rename1`fix_inconsistencies prio _ _`>>
      Q.SPECL_THEN [`na_3`,`ssa_2`,`ssa_3`,`prio`] assume_tac fix_inconsistencies_correctR >>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      pop_assum (qspecl_then[`r''`,`r'''`] mp_tac)>>
      impl_tac>-
        (metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(exc_cons,r''')`>>full_simp_tac(srw_ss())[word_state_eq_rel_def])
    >>
      srw_tac[][]>>qexists_tac`perm`>>full_simp_tac(srw_ss())[]>>
      first_x_assum(qspec_then`envy.stack` mp_tac)>>
      (impl_tac>- (unabbrev_all_tac>>full_simp_tac(srw_ss())[]))>>
      srw_tac[][]>>full_simp_tac(srw_ss())[])*)
  >- (*Seq*)
    (srw_tac[][]>>full_simp_tac(srw_ss())[evaluate_def,ssa_cc_trans_def,LET_THM]>>
    last_assum(qspecl_then[`p`,`st`,`cst`,`ssa`,`na`] mp_tac)>>
    size_tac>>
    impl_tac>>full_simp_tac(srw_ss())[every_var_def]>>srw_tac[][]>>
    Cases_on`ssa_cc_trans p ssa na`>>Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    Cases_on`ssa_cc_trans p0 q' r'`>>Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
    Cases_on`evaluate(p,st with permute:=perm')`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm'`>>full_simp_tac(srw_ss())[]) >>
    Cases_on`evaluate(q,cst)`>>full_simp_tac(srw_ss())[]>>
    reverse (Cases_on`q'''''`)
    >-
      (qexists_tac`perm'`>>srw_tac[][]>>full_simp_tac(srw_ss())[])
    >>
    full_simp_tac(srw_ss())[]>>
    first_assum(qspecl_then[`p0`,`r`,`r'''`,`q'`,`r'`] mp_tac)>>
    size_tac>>
    impl_tac>-
      (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>
      full_simp_tac(srw_ss())[]>>
      match_mp_tac every_var_mono>>
      HINT_EXISTS_TAC>>
      full_simp_tac(srw_ss())[]>>DECIDE_TAC)>>
    srw_tac[][]>>
    qspecl_then[`p`,`st with permute:=perm'`,`perm''`]
      assume_tac permute_swap_lemma>>
    rev_full_simp_tac(srw_ss())[LET_THM]>>
    qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[])
  >- (  (*If*)
    qpat_abbrev_tac `A = ssa_cc_trans B C D` >>
    PairCases_on`A`>>simp[]>>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def]) >>
    full_simp_tac(srw_ss())[evaluate_def,ssa_cc_trans_def]>>
    LET_ELIM_TAC>>fs[]>>
    qpat_x_assum`B = A0` sym_sub_tac>>full_simp_tac(srw_ss())[evaluate_def]>>
    Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var_imm r st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_var>>full_simp_tac(srw_ss())[Abbr`r1'`]>>
    `get_var_imm ri' cst = SOME(Word c'')` by
      (Cases_on`r`>>full_simp_tac(srw_ss())[Abbr`ri'`,get_var_imm_def]>>
      metis_tac[ssa_locals_rel_get_var])>>
    fs[] >>
    Cases_on`word_cmp c c' c''`>>full_simp_tac(srw_ss())[]
    >-
      (first_assum(qspecl_then[`p`,`st`,`cst`,`ssa`,`na`] mp_tac)>>
      size_tac>>
      impl_tac>-
        (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>
        full_simp_tac(srw_ss())[every_var_def])>>
      srw_tac[][]>>
      qexists_tac`perm'`>>full_simp_tac(srw_ss())[LET_THM]>>
      Cases_on`evaluate(p,st with permute := perm')`>>
      Cases_on`evaluate(e2',cst)`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q'`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      Q.SPECL_THEN [`na3`,`ssa2`,`ssa3`] mp_tac fix_inconsistencies_correctL>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      srw_tac[][]>>
      pop_assum (qspecl_then[`r'`,`r''`] mp_tac)>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(e2_cons,r'')`>>full_simp_tac(srw_ss())[word_state_eq_rel_def])
    >>
      (first_assum(qspecl_then[`p0`,`st`,`cst`,`ssa`,`na2`] mp_tac)>>
      size_tac>>
      impl_tac>-
        (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>srw_tac[][]
        >-
          metis_tac[ssa_locals_rel_more]
        >-
          (full_simp_tac(srw_ss())[every_var_def]>>match_mp_tac every_var_mono>>
          Q.EXISTS_TAC`λx.x<na`>>full_simp_tac(srw_ss())[] >>
          DECIDE_TAC)
        >>
          metis_tac[ssa_map_ok_more])
      >>
      srw_tac[][]>>
      qexists_tac`perm'`>>full_simp_tac(srw_ss())[LET_THM]>>
      Cases_on`evaluate(p0,st with permute := perm')`>>
      Cases_on`evaluate(e3',cst)`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q'`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      (*Start reasoning about fix_inconsistencies*)
      rename1`fix_inconsistencies prio _ _`>>
      Q.SPECL_THEN [`na3`,`ssa2`,`ssa3`,`prio`] mp_tac fix_inconsistencies_correctR>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>srw_tac[][]>>
      pop_assum (qspecl_then[`r'`,`r''`] mp_tac)>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(e3_cons,r'')`>>full_simp_tac(srw_ss())[word_state_eq_rel_def]))
  >~[`Alloc`]
  >-(
    qabbrev_tac`A = ssa_cc_trans (Alloc n p) ssa na`>>
    PairCases_on`A`>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>
    pop_assum mp_tac>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def]>>
    FULL_CASE_TAC>>Cases_on`x`>>full_simp_tac(srw_ss())[alloc_def]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`] mp_tac list_next_var_rename_move_preserve>>
    impl_keep_tac>-
      (srw_tac[][]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >-
        (
       full_simp_tac(srw_ss())[cut_envs_def,Abbr`ls`,Abbr`all_names`,AllCaseEqs()] >>
       rveq >>
       full_simp_tac(srw_ss())[set_MAP_FST_toAList_domain,domain_union] >>
       full_simp_tac(srw_ss())[cut_names_def])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]))>>
    LET_ELIM_TAC>>
    qpat_x_assum`A=A0` sym_sub_tac>>
    qpat_x_assum`A=A1` sym_sub_tac>>
    qpat_x_assum`A=A2` sym_sub_tac>>
    full_simp_tac(srw_ss())[Abbr`prog`,evaluate_def]>>
    simp_tac(srw_ss())[Once LET_THM] >>
    rev_full_simp_tac(srw_ss())[Abbr`num'`]>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`ls`,`ssa`,`na+2`,`mov`,`ssa'`,`na'`] assume_tac list_next_var_rename_move_props>>
    `is_stack_var (na+2)` by full_simp_tac(srw_ss())[is_alloc_var_flip]>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[get_vars_def,get_var_def,set_vars_def,alist_insert_def,Once LET_THM]>>
    qpat_abbrev_tac `rcstlocs = insert 2 A rcst.locals`>>
    full_simp_tac(srw_ss())[alloc_def]>>
    cheat)
    (*
    (*Try to use cut_env_lemma from word_live*)
    Q.ISPECL_THEN [`s`,`st.locals`,`rcstlocs`,`x`
                  ,`f` ] mp_tac cut_env_lemma>>
    impl_tac>- (
      gvs[Abbr`f`,ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[INJ_DEF]>- (
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain])
      >>
        full_simp_tac(srw_ss())[option_lookup_def,domain_lookup,Abbr`rcstlocs`,lookup_insert]>>
        last_x_assum kall_tac>>
        res_tac>>
        full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        first_x_assum(qspecl_then [`n'`,`v'`] mp_tac)>>
        simp[]>>
        qpat_x_assum`A=SOME v'` SUBST_ALL_TAC>>full_simp_tac(srw_ss())[]>>
        srw_tac[][is_phy_var_def])
    >>
    srw_tac[][]>>full_simp_tac(srw_ss())[set_store_def]>>
    qpat_abbrev_tac`non = NONE`>>
    Q.ISPECL_THEN [`y`,`x`,`st with store:= st.store |+ (AllocSize,Word c)`
    ,`f`,`rcst with store:= rcst.store |+ (AllocSize,Word c)`
    ,`non`,`non`,`rcst.permute`] assume_tac (GEN_ALL push_env_s_val_eq)>>
    rev_full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`non`]>>
    qexists_tac`perm`>>full_simp_tac(srw_ss())[]>>
    qpat_abbrev_tac `st' = push_env x NONE A`>>
    qpat_abbrev_tac `cst' = push_env y NONE B`>>
    Cases_on`gc st'`>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`st'`,`cst'`,`x'`] mp_tac gc_s_val_eq_gen>>
    impl_keep_tac>-
      (unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,word_state_eq_rel_def,
        stack_size_def, stack_size_frame_def]>>
      rev_full_simp_tac(srw_ss())[])
    >>
    srw_tac[][]>>simp[]>>
    unabbrev_all_tac>>
    imp_res_tac gc_frame>>
    Cases_on`pop_env x'`>>rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
    imp_res_tac push_env_pop_env_s_key_eq>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
    imp_res_tac gc_s_key_eq>>
    full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
    rpt (qpat_x_assum `s_key_eq A B` mp_tac)>>
    qpat_abbrev_tac `lsA = list_rearrange (rcst.permute 0)
        (QSORT key_val_compare ( (toAList y)))`>>
    qpat_abbrev_tac `lsB = list_rearrange (perm 0)
        (QSORT key_val_compare ( (toAList x)))`>>
    ntac 4 strip_tac>>
    Q.ISPECL_THEN [`x'.stack`,`y'`,`t'`,`NONE:(num#num#num) option`, `rcst.locals_size`
        ,`lsA`,`rcst.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
      impl_tac
    >-
      (full_simp_tac(srw_ss())[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])
    >>
    strip_tac>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`t'.stack`,`x''`,`x'`,`NONE:(num#num#num) option`, `st.locals_size`
      ,`lsB`,`st.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
      impl_tac
    >-
      (full_simp_tac(srw_ss())[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])
    >>
    srw_tac[][]>>
    `LENGTH ls' = LENGTH l ∧ LENGTH lsB = LENGTH l` by
      metis_tac[s_key_eq_def,s_frame_key_eq_def,
                s_val_eq_def,LENGTH_MAP,s_frame_val_eq_def]>>
    (*Establish invariants about ssa_cut to use later*)
    qabbrev_tac `ssa_cut = inter ssa' s` >>
    `domain ssa_cut = domain x` by
      (full_simp_tac(srw_ss())[EXTENSION,Abbr`ssa_cut`,domain_inter]>>
      srw_tac[][EQ_IMP_THM]>>
      full_simp_tac(srw_ss())[cut_env_def,SUBSET_DEF]>>
      last_x_assum kall_tac >>
      res_tac>>
      full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒ lookup x ssa' = SOME y` by
      (srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`,lookup_inter]>>
      Cases_on`lookup x''' ssa'`>>Cases_on`lookup x''' s`>>full_simp_tac(srw_ss())[])>>
   `domain x''.locals = domain x` by
     (full_simp_tac(srw_ss())[domain_fromAList,MAP_ZIP]>>
     full_simp_tac(srw_ss())[EXTENSION,Abbr`lsB`]>>
     full_simp_tac(srw_ss())[MEM_MAP,mem_list_rearrange,QSORT_MEM]>>
     srw_tac[][]>>
     full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList,domain_lookup])>>
    last_x_assum kall_tac>>
    `ssa_locals_rel na' ssa_cut x''.locals y'.locals ∧
        word_state_eq_rel x'' y'` by
       (full_simp_tac(srw_ss())[state_component_equality]>>
       full_simp_tac(srw_ss())[LET_THM,ssa_locals_rel_def]>>
       srw_tac[][]
       >-
         (qpat_x_assum`A=domain(fromAList l)` sym_sub_tac>>
         full_simp_tac(srw_ss())[option_lookup_def]>>
         res_tac>>full_simp_tac(srw_ss())[]>>
         qexists_tac`x'''`>>full_simp_tac(srw_ss())[]>>
         metis_tac[domain_lookup])
       >-
         metis_tac[domain_lookup]
       >-
         (`x''' ∈ domain x` by metis_tac[domain_lookup]>>
         qpat_x_assum`A = fromAList l` sym_sub_tac>>
         full_simp_tac(srw_ss())[lookup_fromAList,s_key_eq_def,s_frame_key_eq_def
           ,s_val_eq_def,s_frame_val_eq_def]>>
         qpat_x_assum`A = MAP FST l` sym_sub_tac>>
         qabbrev_tac`f = option_lookup ssa'`>>
         `MAP FST (MAP (λ(x,y). (f x,y)) lsB) =
          MAP f (MAP FST lsB)` by
           full_simp_tac(srw_ss())[MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
         full_simp_tac(srw_ss())[]>>
         `THE (lookup x''' ssa_cut) = f x'''` by
           (full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def]>>
           `x''' ∈ domain ssa_cut` by metis_tac[]>>
           full_simp_tac(srw_ss())[domain_lookup]>>res_tac>>
           full_simp_tac(srw_ss())[])>>
         simp[]>>
         match_mp_tac ALOOKUP_key_remap_2>>srw_tac[][]>>
         metis_tac[])
       >-
         (`x''' ∈ domain s` by metis_tac[domain_lookup]>>
         full_simp_tac(srw_ss())[every_var_def,every_name_def,EVERY_MEM,toAList_domain]>>res_tac>>
         DECIDE_TAC)
       >-
         (full_simp_tac(srw_ss())[word_state_eq_rel_def,pop_env_def]>>
         rev_full_simp_tac(srw_ss())[state_component_equality, stack_size_def, stack_size_frame_def]>>
         conj_tac >- fs [s_val_eq_def, s_frame_val_eq_def] >>
         metis_tac[s_val_and_key_eq,s_key_eq_sym,s_val_eq_sym,s_key_eq_trans])) >>
    ntac 2 (qpat_x_assum `A = (B,C)` mp_tac)>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[word_state_eq_rel_def,has_space_def]>>
    Cases_on`x'''`>>full_simp_tac(srw_ss())[]>>
    Cases_on`FLOOKUP x''.store NextFree`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x'''`>>full_simp_tac(srw_ss())[] >>
    Cases_on`FLOOKUP x''.store TriggerGC`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x'''`>>full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    ntac 2 strip_tac>> rveq >> full_simp_tac(srw_ss())[call_env_def,flush_state_def] >-
    (Q.SPECL_THEN [`rst`,`inter ssa' s`,`na'+2`,`(MAP FST (toAList s))`
                 ,`y'`] mp_tac list_next_var_rename_move_preserve>>
    impl_tac>-
    (srw_tac[][]
    >-
      (rev_full_simp_tac(srw_ss())[]>>
      match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
      full_simp_tac(srw_ss())[]>>
      qpat_x_assum `A = fromAList _` sym_sub_tac>>
      HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
    >-
      (srw_tac[][SUBSET_DEF]>>
      full_simp_tac(srw_ss())[MEM_MAP]>>Cases_on`y''`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
    >-
      (unabbrev_all_tac>>match_mp_tac ssa_map_ok_inter>>
      match_mp_tac (GEN_ALL ssa_map_ok_more)>>
      HINT_EXISTS_TAC>>
      full_simp_tac(srw_ss())[]>>DECIDE_TAC)
    >>
      full_simp_tac(srw_ss())[word_state_eq_rel_def])>>
    simp[] >>
    srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def]) >>
    full_simp_tac(srw_ss())[word_state_eq_rel_def, stack_size_def, stack_size_frame_def] >> srw_tac[][])
    *)
  >~[`StoreConsts`]
  >- (
    exists_tac>>fs[]>>
    Cases_on`get_var n1 st`>>fs[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    TOP_CASE_TAC>>simp[]>>
    Cases_on`get_var n2 st`>>fs[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    TOP_CASE_TAC>>simp[]>>
    fs[next_var_rename_def,evaluate_def,get_vars_def]>>
    simp[get_var_def,set_vars_def,lookup_alist_insert]>>
    IF_CASES_TAC>>simp[set_var_def,unset_var_def,lookup_insert]>>
    `n1 ∈ domain ssa ∧ n2 ∈ domain ssa ` by
      fs[ssa_locals_rel_def,get_var_def]>>
    fs[domain_lookup,option_lookup_def]>>
    `~(is_phy_var v') ∧ ¬(is_phy_var v'')` by
      (fs[ssa_map_ok_def]>>
      metis_tac[])>>
    `EVERY is_phy_var [0;2;4;6]` by
      fs[is_phy_var_def]>>
    fs[lookup_delete]>>
    rpt(IF_CASES_TAC>>gs[])>>
    simp[lookup_alist_insert]>>
    fs[get_var_def]>>
    simp[alist_insert_def]>>
    fs[every_var_def]>>
    `na+8 = (na+4)+4` by fs[]>>
    pop_assum SUBST_ALL_TAC>>
    drule ssa_map_ok_extend >>
    disch_then(qspec_then`n2` mp_tac)>>
    impl_tac>-
      metis_tac[convention_partitions]>>
    strip_tac>>
    match_mp_tac ssa_locals_rel_insert>> simp[]>>
    metis_tac[
      ssa_locals_rel_insert,
      ssa_locals_rel_delete_left,
      ssa_locals_rel_ignore_insert,
      ssa_locals_rel_delete_right,
      ssa_locals_rel_ignore_insert])
  >-
    (*Raise*)
    (exists_tac>>fs[]>>
    Cases_on`get_var n st`>>imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[get_vars_def,get_var_def,set_vars_def,lookup_alist_insert]>>
    full_simp_tac(srw_ss())[jump_exc_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>> gvs[])
  >-
    (*Return*)
    (exists_tac>>fs[]>>
    Cases_on`get_var n st`>> fs[] >>
    Cases_on `x` >> fs[] >>
    Cases_on`get_vars l st`>> fs[] >>
    full_simp_tac(srw_ss())[MAP_ZIP,ALL_DISTINCT_GENLIST] >>
    imp_res_tac ssa_locals_rel_get_vars>>
    full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[set_vars_def]>>
    imp_res_tac ssa_locals_rel_ignore_list_insert>>
    ntac 4 (pop_assum kall_tac)>>
    pop_assum(qspecl_then [`x`,`(GENLIST (λx. 2 * (x + 1)) (LENGTH l))`] mp_tac)>>
    pop_assum kall_tac >>
    impl_tac>- (full_simp_tac(srw_ss())[LENGTH_GENLIST]>>
   imp_res_tac get_vars_length_lemma >> gvs[]) >>
    impl_tac>- full_simp_tac(srw_ss())[EVERY_GENLIST,is_phy_var_def] >>
    srw_tac[][]>>full_simp_tac(srw_ss())[alist_insert_def]>>
    qpat_abbrev_tac`rcst=cst with locals:=A`>>
    rename1 `get_var _ cst = SOME (Loc l1 l2)`>>
    Q.ISPECL_THEN [`Loc l1 l2`,`st`,`ssa`,`na`,`n`,`rcst`] assume_tac (GEN_ALL ssa_locals_rel_get_var)>>
    pop_assum mp_tac >>
    impl_tac >- (unabbrev_all_tac>>rfs[])>>
    strip_tac >> full_simp_tac(srw_ss())[] >>
    unabbrev_all_tac >> full_simp_tac (srw_ss())[GSYM set_vars_def] >>
    DEP_REWRITE_TAC[get_vars_set_vars] >>
    fs[ALL_DISTINCT_GENLIST,LENGTH_GENLIST] >>
    CONJ_TAC >-
    (imp_res_tac get_vars_length_lemma >> gvs[]) >>
    fs[flush_state_def])
  >- (* Tick *)
    (exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def])
  >- (* OpCurrHeap *)
    (last_x_assum kall_tac>>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    imp_res_tac ssa_locals_rel_get_var>>
    imp_res_tac ssa_cc_trans_exp_correct>>full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    rev_full_simp_tac(srw_ss())[evaluate_def]>>
    fs[set_var_def,set_store_def,ssa_cc_trans_exp_def]>>
    match_mp_tac ssa_locals_rel_set_var>>
    full_simp_tac(srw_ss())[every_var_def])
  >-
    exp_tac
  >~[`Install`]
  >-(
    qexists_tac`cst.permute`>>
    full_simp_tac(srw_ss())[ssa_cc_trans_def]>>
    rpt (LET_ELIM_TAC>>full_simp_tac(srw_ss())[evaluate_def,AllCaseEqs()] >>
    rev_full_simp_tac(srw_ss())[] >>
    qpat_x_assum `_ = (res,rst)` mp_tac) >>
    srw_tac[][LET_THM] >>
    qpat_x_assum `_ = (res,rcst)` mp_tac >>
    full_simp_tac(srw_ss())[Abbr`prog`,Once evaluate_def] >>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`] mp_tac list_next_var_rename_move_preserve>>
    impl_keep_tac>-
      (srw_tac[][word_state_eq_rel_def]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >-
        (
       full_simp_tac(srw_ss())[cut_env_def,cut_envs_def,Abbr`ls`,Abbr`all_names`,AllCaseEqs()] >>
       rveq >>
       full_simp_tac(srw_ss())[set_MAP_FST_toAList_domain,domain_union] >>
       full_simp_tac(srw_ss())[cut_names_def])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC))>>
    qho_match_abbrev_tac `_ ⇒ goal` >>
    LET_ELIM_TAC >> qunabbrev_tac `goal` >>
    drule (list_next_var_rename_move_props_2 |> SIMP_RULE std_ss[Once CONJ_COMM] |> SIMP_RULE std_ss [ GSYM AND_IMP_INTRO]) >>
    disch_then drule>>
    full_simp_tac(srw_ss())[] >>
    disch_tac >>
    full_simp_tac(srw_ss())[] >>
    qpat_x_assum`A=stack_mov` sym_sub_tac>>
    qpat_x_assum`A=ssa'` sym_sub_tac>>
    qpat_x_assum`A=na'` sym_sub_tac>>
    full_simp_tac(srw_ss())[Once LET_THM,evaluate_def]>>
    imp_res_tac ssa_locals_rel_get_var >>
    full_simp_tac(srw_ss())[get_vars_def,Abbr`ptr'`,Abbr`len'`,Once LET_THM] >>
    cheat)
    (*
    qpat_abbrev_tac`rcst_mov = set_vars _ _ rcst`>>
    Q.ISPECL_THEN [`s`,`st.locals`,`rcst_mov.locals`,`env`
       ,`option_lookup ssa''` ] mp_tac cut_env_lemma>>
    simp[]>>impl_keep_tac>-
      (
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[INJ_DEF]
      >-
        ((* use property of list_next_var_rename_move *)
        qpat_x_assum`list_next_var_rename_move _ _ _ = _ `kall_tac>>
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[ALL_DISTINCT_MAP_FST_toAList,toAList_domain])
      >>
        fs[option_lookup_def,domain_lookup,Abbr`rcst_mov`,lookup_insert]>>
        res_tac>>
        fs[ssa_map_ok_def]>>
        rename1`lookup nn ssa = SOME vv`>>
        first_x_assum(qspecl_then [`nn`,`vv`] mp_tac)>>
        simp[set_vars_def,lookup_alist_insert]>>
        res_tac>>
        fs[is_phy_var_def]>>
        rw[]>>fs[])>>
    strip_tac>>
    `get_var (option_lookup ssa'' n1) rcst_mov = SOME (Word w3) ∧
     get_var (option_lookup ssa'' n2) rcst_mov = SOME (Word w4)` by
       (simp[Abbr`rcst_mov`]>>
       DEP_REWRITE_TAC [get_var_set_vars_notin]>>
       CONJ_TAC>-
         (fs[]>>CCONTR_TAC>>fs[option_lookup_def,case_eq_thms,ssa_map_ok_def]>>
         res_tac>>fs[is_phy_var_def])>>
       fs[ssa_locals_rel_def])>>
    fs[evaluate_def,Abbr`rcst_mov`]>>
    simp[get_var_def,set_vars_def,lookup_alist_insert]>>
    fs[word_state_eq_rel_def]>>
    qmatch_goalsub_abbrev_tac`evaluate (_,rcstt)`>>
    qabbrev_tac`ssa_cut = inter ssa'' s`>>
    `domain ssa_cut = domain env` by
      (fs[EXTENSION,Abbr`ssa_cut`,domain_inter]>>
      srw_tac[][EQ_IMP_THM]>>
      full_simp_tac(srw_ss())[cut_env_def,SUBSET_DEF]>>
      res_tac>>
      full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `ssa_locals_rel na''' ssa''' rst.locals rcstt.locals ∧ word_state_eq_rel rst rcstt` by
      (qpat_x_assum`Abbrev(_=rst)` mp_tac>>
      simp[markerTheory.Abbrev_def]>>
      disch_then (SUBST_ALL_TAC o SYM)>>
      fs[next_var_rename_def]>>
      fs[Abbr`rcstt`,ssa_locals_rel_def,word_state_eq_rel_def]>>
      rveq>>fs[]>>
      CONJ_TAC>-
        (simp[lookup_insert,domain_alist_insert,Abbr`ssa_cut`]>>rw[]>>
        DISJ1_TAC>>DISJ2_TAC>>
        fs[lookup_inter,case_eq_thms]>>
        fs[domain_lookup,option_lookup_def]>>
        qexists_tac`x`>>simp[])>>
      simp[lookup_insert]>>
      ntac 2 strip_tac>>
      IF_CASES_TAC
      >-
        (strip_tac>>simp[alist_insert_def]>>
        fs[every_var_def])
      >>
      strip_tac>>simp[]>>
      conj_asm1_tac
      >-
        (fs[Abbr`ssa_cut`,domain_inter]>>
        metis_tac[domain_lookup])>>
      conj_tac>-3
        (fs[strong_locals_rel_def,Abbr`ssa_cut`,alist_insert_def]>>
        first_x_assum drule>>
        disch_then drule>>
        `∃vv. lookup x (inter ssa'' s) = SOME vv ∧ vv ≠ na''+2 ∧ vv ≠ 2` by
          (fs[lookup_inter,domain_lookup,EXTENSION]>>
          first_x_assum(qspec_then`x` assume_tac)>>rfs[case_eq_thms]>>
          fs[ssa_map_ok_def]>>
          rpt (first_x_assum drule)>>
          fs[]>>rw[]>>
          CCONTR_TAC>>fs[is_phy_var_def])>>
        simp[lookup_insert]>>
        fs[lookup_inter,case_eq_thms,option_lookup_def])
      >>
        fs[every_var_def,every_name_def,EVERY_MEM,toAList_domain]>>
        last_x_assum drule>>
        simp[])>>
    drule list_next_var_rename_move_preserve >>
    disch_then(qspecl_then[`MAP FST (toAList s)`] mp_tac)>>
    simp[]>>
    impl_tac>-
      (fs[next_var_rename_def,SUBSET_DEF,toAList_domain]>>rw[]>>
      `na''+6 = na''+2+4` by fs[]>>
      pop_assum SUBST1_TAC>>
      match_mp_tac ssa_map_ok_extend>>
      reverse conj_tac>-
        metis_tac[convention_partitions,is_stack_var_flip]>>
      simp[Abbr`ssa_cut`]>>
      match_mp_tac ssa_map_ok_inter>>
      match_mp_tac (GEN_ALL ssa_map_ok_more)>>
      asm_exists_tac>>fs[])>>
    pairarg_tac>>fs[word_state_eq_rel_def]) *)
  >-
    exp_tac
  >-
    exp_tac
  >-(
    (*FFI*)
    qexists_tac`cst.permute`>>
    LET_ELIM_TAC >>
    qabbrev_tac`A = ssa_cc_trans (FFI s n n0 n1 n2 p) ssa na`>>
    PairCases_on`A`>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>
    pop_assum mp_tac>> LET_ELIM_TAC >>
    rev_full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def,CaseEq"option",CaseEq"word_loc"]>>
    rpt (qpat_x_assum `_ = (res,rst)` mp_tac >>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    rev_full_simp_tac(srw_ss())[]) >>
    rveq >>
    qpat_x_assum `_ = (res',rcst)` mp_tac >>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`] mp_tac list_next_var_rename_move_preserve>>
    impl_keep_tac>-
      (srw_tac[][word_state_eq_rel_def]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >-
        (full_simp_tac(srw_ss())[cut_env_def,cut_envs_def,Abbr`ls`,Abbr`all_names`,AllCaseEqs()] >>
        rveq >>
        full_simp_tac(srw_ss())[set_MAP_FST_toAList_domain,domain_union] >>
        full_simp_tac(srw_ss())[cut_names_def])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC))>>
    qho_match_abbrev_tac `_ ⇒ goal` >>
    LET_ELIM_TAC >> qunabbrev_tac `goal` >>
    full_simp_tac(srw_ss())[Abbr`A0`,evaluate_def]>>
    rveq >> full_simp_tac(srw_ss())[Once LET_THM] >>
    `get_vars [cptr1; clen1; cptr2; clen2] rcst' = SOME [Word w2;Word w;Word w4;Word w3]` by
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[get_vars_def]>>
      imp_res_tac ssa_locals_rel_get_var>>full_simp_tac(srw_ss())[get_var_def])>>
    full_simp_tac(srw_ss())[Once LET_THM] >>
(*    rename1 `_ = FFI_return ff _` >>*)
    qabbrev_tac`f = option_lookup ssa'`>>
    Q.ISPECL_THEN [`ls`,`ssa`,`na+2`,`mov`,`ssa'`,`na'`] assume_tac list_next_var_rename_move_props>>
    `is_stack_var (na+2)` by full_simp_tac(srw_ss())[is_alloc_var_flip]>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
    qmatch_goalsub_abbrev_tac `insert 2 A (insert 4 B (insert 6 C (insert 8 D (rcst'.locals))))`>>
    qpat_abbrev_tac `rcstlocs = insert 2 A (insert 4 B (insert 6 C (insert 8 D (rcst'.locals))))`>>
    full_simp_tac(srw_ss())[get_var_def]>>
    `lookup 8 rcstlocs = SOME D ∧
     lookup 6 rcstlocs = SOME C ∧
     lookup 4 rcstlocs = SOME B ∧
     lookup 2 rcstlocs = SOME A` by
      (unabbrev_all_tac >>
      full_simp_tac(srw_ss())[lookup_insert])>>
    full_simp_tac(srw_ss())[Abbr`A`,Abbr`B`,Abbr`C`,Abbr`D`]>>
    ntac 4 $ pop_assum kall_tac >>
    cheat)(*
    Q.ISPECL_THEN [`s0`,`st.locals`,`rcstlocs`,`x`
                  ,`f` ] mp_tac cut_env_lemma>>
    impl_tac>-
      (rev_full_simp_tac(srw_ss())[Abbr`f`]>>
      full_simp_tac(srw_ss())[ssa_locals_rel_def,strong_locals_rel_def]>>
      srw_tac[][INJ_DEF]>-
        ((* use property of list_next_var_rename_move *)
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain])
      >>
        full_simp_tac(srw_ss())[option_lookup_def,domain_lookup,Abbr`rcstlocs`,lookup_insert]>>
        res_tac>>
        full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        first_x_assum(qspecl_then [`n'`,`v'`] mp_tac)>>
        simp[]>>
        qpat_x_assum`A=SOME v'` SUBST_ALL_TAC>>full_simp_tac(srw_ss())[]>>
        srw_tac[][is_phy_var_def])>>
    srw_tac[][]>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    reverse(Cases_on`call_FFI st.ffi (ExtCall s) x'' x'`)>>full_simp_tac(srw_ss())[]
    >- fs[call_env_def,flush_state_def] >>
    qpat_abbrev_tac`mem = write_bytearray A B C D E`>>
    qabbrev_tac`rst = st with <|locals := x;memory:=mem;ffi:=f'|>`>>
    qpat_abbrev_tac`rcstt = rcst with <|locals := A;memory:=B;ffi:=D|>`>>
    `domain ssa_cut = domain x` by
      (full_simp_tac(srw_ss())[EXTENSION,Abbr`ssa_cut`,domain_inter]>>
      srw_tac[][EQ_IMP_THM]>>
      full_simp_tac(srw_ss())[cut_env_def,SUBSET_DEF]>>
      res_tac>>
      full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒ lookup x ssa' = SOME y` by
      (srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`,lookup_inter]>>
      Cases_on`lookup x''' ssa'`>>Cases_on`lookup x''' s0`>>full_simp_tac(srw_ss())[])>>
   `domain rst.locals = domain x` by
     full_simp_tac(srw_ss())[Abbr`rst`]>>
   `ssa_locals_rel na' ssa_cut rst.locals rcstt.locals ∧
       word_state_eq_rel rst rcstt` by
      (full_simp_tac(srw_ss())[Abbr`rst`,Abbr`rcstt`,state_component_equality
      ,word_state_eq_rel_def,ssa_locals_rel_def]>>
      srw_tac[][]
      >-
        (qexists_tac`x'''`>>unabbrev_all_tac>>
        full_simp_tac(srw_ss())[option_lookup_def,lookup_inter]>>
        pop_assum mp_tac >>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[domain_lookup])
      >-
        metis_tac[domain_lookup]
      >-
        (`THE (lookup x''' ssa_cut) = f x'''` by
          (full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def]>>
          `x''' ∈ domain ssa_cut` by metis_tac[domain_lookup]>>
          full_simp_tac(srw_ss())[domain_lookup]>>res_tac>>
          full_simp_tac(srw_ss())[])>>
        full_simp_tac(srw_ss())[strong_locals_rel_def]>>
        metis_tac[domain_lookup])
      >-
        (`x''' ∈ domain s0` by metis_tac[domain_lookup]>>
        full_simp_tac(srw_ss())[every_var_def,every_name_def,EVERY_MEM,toAList_domain]>>res_tac>>
        DECIDE_TAC))>>
    Q.SPECL_THEN [`rst`,`inter ssa' s0`,`na'+2`,`(MAP FST (toAList s0))`
                   ,`rcstt`] mp_tac list_next_var_rename_move_preserve>>
      impl_tac>-
      (srw_tac[][]
      >-
        (unabbrev_all_tac>>rev_full_simp_tac(srw_ss())[]>>
        match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        full_simp_tac(srw_ss())[]>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
      >-
        (srw_tac[][SUBSET_DEF,Abbr`ls`]>>
        full_simp_tac(srw_ss())[MEM_MAP]>>Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
      >-
        (unabbrev_all_tac>>match_mp_tac ssa_map_ok_inter>>
        match_mp_tac (GEN_ALL ssa_map_ok_more)>>
        HINT_EXISTS_TAC>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC))>>
      full_simp_tac(srw_ss())[LET_THM]>>
      srw_tac[][]>>
      Cases_on`evaluate(ret_mov,rcstt)`>>unabbrev_all_tac>>full_simp_tac(srw_ss())[state_component_equality,word_state_eq_rel_def] )
  *)
  (*ShareInst*)
  >-(
    exists_tac >>
    pairarg_tac >>
    simp[] >>
    rename1`m = Store \/ m = Store8 \/ m = Store32`>>
    qabbrev_tac `mcase = (m = Store \/ m = Store8 \/ m = Store32)`>>
    fs[AllCaseEqs()] >>
    IF_CASES_TAC >>
    gvs[next_var_rename_def,evaluate_def] >>
    drule_then (drule_at $ Pos last) ssa_cc_trans_exp_correct
    >- (
      impl_tac >- simp[word_state_eq_rel_def] >>
      disch_then (fn t => simp[t]) >>
      gvs[oneline share_inst_def,
        oneline sh_mem_store_def,
        oneline sh_mem_store_byte_def,
        oneline sh_mem_store32_def,
        markerTheory.Abbrev_def,flush_state_def,AllCaseEqs()] >>
      drule_then (drule_then assume_tac) ssa_locals_rel_get_var >>
      simp[]) >>
    impl_tac >- simp[word_state_eq_rel_def] >>
    disch_then (fn t => simp[t]) >>
    gvs[oneline share_inst_def,
      oneline sh_mem_load_def,
      oneline sh_mem_load_byte_def,
      oneline sh_mem_load32_def,
      oneline sh_mem_set_var_def,
      set_var_def,flush_state_def,AllCaseEqs(),
      markerTheory.Abbrev_def] >>
    irule ssa_locals_rel_set_var >>
    fs[every_var_def] )
QED

(*For starting up*)
Triviality setup_ssa_props:
  is_alloc_var lim ∧
  domain st.locals = set (even_list n) ⇒
  let (mov:'a wordLang$prog,ssa,na) = setup_ssa n lim (prog:'a wordLang$prog) in
  let (res,cst) = evaluate(mov,st) in
    res = NONE ∧
    word_state_eq_rel st cst ∧
    ssa_map_ok na ssa ∧
    ssa_locals_rel na ssa st.locals cst.locals ∧
    is_alloc_var na ∧
    lim ≤ na
Proof
  srw_tac[][setup_ssa_def]>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,evaluate_def]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  full_simp_tac(srw_ss())[LET_THM,MAP_ZIP,LENGTH_COUNT_LIST]>>
  full_simp_tac(srw_ss())[ALL_DISTINCT_MAP]>>
  `set args ⊆ domain st.locals` by full_simp_tac(srw_ss())[]>>
  imp_res_tac get_vars_eq>>
  full_simp_tac(srw_ss())[set_vars_def,state_component_equality]
  >>
    TRY(`ssa_map_ok lim LN` by
      full_simp_tac(srw_ss())[ssa_map_ok_def,lookup_def]>>
    imp_res_tac list_next_var_rename_props>>NO_TAC)>>
  full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
  `ALL_DISTINCT args` by
    (unabbrev_all_tac>>
    full_simp_tac(srw_ss())[even_list_def,ALL_DISTINCT_GENLIST]>>srw_tac[][]>>
    DECIDE_TAC)>>
  imp_res_tac list_next_var_rename_lemma_2>>
  pop_assum kall_tac>>
  pop_assum(qspecl_then [`LN`,`lim`] mp_tac)>>
  LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]
  >-
    (qpat_x_assum`A=cst.locals` (sym_sub_tac)>>
    full_simp_tac(srw_ss())[domain_alist_insert,LENGTH_COUNT_LIST]>>
    `x ∈ domain ssa` by full_simp_tac(srw_ss())[domain_lookup]>>
    qpat_x_assum `MAP f args = B` (sym_sub_tac)>>
    DISJ2_TAC>>
    full_simp_tac(srw_ss())[MEM_MAP]>>
    qexists_tac`x`>>
    `x ∈ domain ssa` by full_simp_tac(srw_ss())[domain_lookup]>>
    full_simp_tac(srw_ss())[]>>metis_tac[EXTENSION])
  >-
    (`x ∈ domain st.locals` by full_simp_tac(srw_ss())[domain_lookup]>>
    metis_tac[EXTENSION])
  >-
    (qpat_x_assum`A=cst.locals` (sym_sub_tac)>>
    full_simp_tac(srw_ss())[lookup_alist_insert,LENGTH_COUNT_LIST]>>
    full_simp_tac(srw_ss())[ALOOKUP_ALL_DISTINCT_EL]>>
    use_ALOOKUP_ALL_DISTINCT_MEM >>
    full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_COUNT_LIST]>>
    strip_tac>>
    pop_assum(qspec_then `y` mp_tac)>>impl_tac
    >-
      (full_simp_tac(srw_ss())[MEM_ZIP,LENGTH_COUNT_LIST]>>
      `x ∈ set args` by metis_tac[domain_lookup]>>
      full_simp_tac(srw_ss())[MEM_EL]>>HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[EL_MAP]>>
      full_simp_tac(srw_ss())[LIST_EQ_REWRITE]>>last_x_assum(qspec_then`n''` assume_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[EL_MAP,LENGTH_COUNT_LIST])
    >>
    full_simp_tac(srw_ss())[])
  >>
    `x ∈ domain st.locals` by full_simp_tac(srw_ss())[domain_lookup]>>
    `MEM x args` by metis_tac[EXTENSION]>>
    full_simp_tac(srw_ss())[Abbr`args`]>>
    full_simp_tac(srw_ss())[even_list_def,MEM_GENLIST]>>
    `is_phy_var x` by is_phy_var_tac>>
    metis_tac[convention_partitions]
QED

Triviality max_var_exp_max:
  ∀exp.
    every_var_exp (λx. x≤ max_var_exp exp) exp
Proof
  ho_match_mp_tac max_var_exp_ind>>
  srw_tac[][every_var_exp_def,max_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>res_tac>>
  match_mp_tac every_var_exp_mono>>
  HINT_EXISTS_TAC>>srw_tac[][]>>
  qpat_abbrev_tac`ls':(num list) = MAP f ls`>>
  Q.ISPECL_THEN [`ls'`] assume_tac list_max_max>>
  full_simp_tac(srw_ss())[EVERY_MEM,Abbr`ls'`,MEM_MAP,PULL_EXISTS]>>
  pop_assum(qspec_then`a` assume_tac)>>rev_full_simp_tac(srw_ss())[]>>
  DECIDE_TAC
QED

Triviality max_var_inst_max:
  ∀inst.
    every_var_inst (λx. x ≤ max_var_inst inst) inst
Proof
  ho_match_mp_tac max_var_inst_ind>>
  srw_tac[][every_var_inst_def,max_var_inst_def]>>
  TRY(Cases_on`ri`)>>full_simp_tac(srw_ss())[every_var_imm_def]>>
  TRY(IF_CASES_TAC)>>full_simp_tac(srw_ss())[]>>
  DECIDE_TAC
QED

Triviality MAX_DEF2:
  MAX m n = (if n > m then n else m)
Proof
  fs[MAX_DEF]
QED

Theorem max_var_max:
    ∀prog.
    every_var (λx. x ≤ max_var prog) prog
Proof
  ho_match_mp_tac max_var_ind>>
  rpt strip_tac >>
  full_simp_tac(std_ss)[every_var_def,max_var_def]
  >-
  (Q.ISPECL_THEN [`MAP FST ls ++ MAP SND ls`] assume_tac list_max_max>>
  rev_full_simp_tac(srw_ss())[] >> NO_TAC)
  >- metis_tac[max_var_inst_max] >>
  TRY
    (match_mp_tac every_var_exp_mono>>
    qexists_tac`λx. x ≤ max_var_exp exp`>>
    full_simp_tac(srw_ss())[max_var_exp_max]>>
    DECIDE_TAC)
  >- (
     EVERY_CASE_TAC >> full_simp_tac(srw_ss())[] >>
     TRY (full_simp_tac(srw_ss())[list_max_max,LET_THM] >> NO_TAC) >>
     rpt strip_tac  >> full_simp_tac(srw_ss())[EVERY_MEM,every_name_def] >>
     rpt strip_tac >> LET_ELIM_TAC >> full_simp_tac(srw_ss())[] >>
     TRY (  match_mp_tac every_var_mono>>
     first_x_assum (irule_at (Pos last)) >>
     rw[]) >>
     TRY (
     qmatch_asmsub_abbrev_tac `MEM _ ls` >>
     Q.ISPECL_THEN [`ls`] assume_tac list_max_max>>
     full_simp_tac(srw_ss())[EVERY_MEM] >>
     first_x_assum drule_all >>
     disch_tac >> rw[]) >>
     UNABBREV_ALL_TAC >> EVERY_CASE_TAC >>
     rw[] >> intLib.ARITH_TAC
     )
  >-(srw_tac[][] >> match_mp_tac every_var_mono>>
    TRY(HINT_EXISTS_TAC)>>TRY(qexists_tac`λx. x ≤ max_var prog`)>>
    srw_tac[][]>>
    DECIDE_TAC)
  >-(
    Cases_on `ri` >> full_simp_tac(srw_ss())[every_var_imm_def] >>
    LET_ELIM_TAC >> UNABBREV_ALL_TAC >>
    TRY (intLib.ARITH_TAC) >>
    rpt IF_CASES_TAC >> fs[] >>
    match_mp_tac every_var_mono>>
    first_x_assum (irule_at (Pos last)) >>
    full_simp_tac (srw_ss())[] >>
    intLib.ARITH_TAC)
  >-((*This is ugly*)
   fs[every_name_def] >>
   fs[EVERY_MEM] >> rw[] >>
   qmatch_asmsub_abbrev_tac `MEM x ls` >>
   Q.ISPECL_THEN [`ls`] assume_tac list_max_max>>
   fs[EVERY_MEM])
  >-(fs[GSYM FOLDR_MAX_0_list_max])
  >-(
   fs[GSYM FOLDR_MAX_0_list_max] >>
   fs[FOLDR_MAX_0_list_max] >>
   fs[every_name_def] >>
   fs[EVERY_MEM] >> rw[] >>
   qmatch_asmsub_abbrev_tac `MEM x ls` >>
   Q.ISPECL_THEN [`ls`] assume_tac list_max_max>>
   fs[EVERY_MEM])
  >-(
   fs[GSYM FOLDR_MAX_0_list_max] >>
   fs[FOLDR_MAX_0_list_max] >>
   fs[every_name_def] >>
   fs[EVERY_MEM] >> rw[] >>
   qmatch_asmsub_abbrev_tac `MEM x ls` >>
   Q.ISPECL_THEN [`ls`] assume_tac list_max_max>>
   fs[EVERY_MEM])
  >-(
    fs[list_max_def] >>
    IF_CASES_TAC >> fs[list_max_max] >>
    Q.ISPECL_THEN [`ns`] assume_tac list_max_max>>
    fs[EVERY_MEM] >> rw[] >> res_tac >> intLib.ARITH_TAC)
QED

Triviality limit_var_props:
  limit_var prog = lim ⇒
  is_alloc_var lim ∧
  every_var (λx. x< lim) prog
Proof
  reverse (srw_tac[][limit_var_def,is_alloc_var_def])
  >-
    (qspec_then `prog` assume_tac max_var_max >>
    match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC>>
    srw_tac[][]>>
    full_simp_tac(srw_ss())[Abbr`x'`]>>
    DECIDE_TAC)
  >>
  qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>
  `(x + (4 - x MOD 4)) MOD 4 = 0` by
   (`x MOD 4 < 4` by full_simp_tac(srw_ss())[]>>
    `(x MOD 4 = 0) ∨ (x MOD 4 = 1) ∨ (x MOD 4 = 2) ∨ (x MOD 4 = 3)` by
      DECIDE_TAC>>
    full_simp_tac std_ss [EVAL “0<4:num”]>>
    (*Fastest way I could find*)
    `(0 MOD 4 = 0) ∧
    (1 MOD 4 = 1) ∧
    (2 MOD 4 = 2) ∧
    (3 MOD 4 = 3) ∧
    (4 MOD 4 = 0)` by full_simp_tac(srw_ss())[]>>
    `((0+0)MOD 4 = 0) ∧
    ((1+3)MOD 4 = 0) ∧
    ((2+2)MOD 4 = 0) ∧
    ((3+1)MOD 4 = 0)` by full_simp_tac(srw_ss())[]>>
    metis_tac[]) >>
  full_simp_tac std_ss [EVAL “0<4:num”]>>
  first_x_assum(qspecl_then [`x+(4- x MOD 4)`,`1`] assume_tac)>>
  pop_assum sym_sub_tac>>
  full_simp_tac(srw_ss())[]
QED

(*Full correctness theorem*)
Theorem full_ssa_cc_trans_correct:
 ∀prog st n.
  domain st.locals = set (even_list n) ⇒
  ∃perm'.
  let (res,rst) = evaluate(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (res',rcst) = evaluate(full_ssa_cc_trans n prog,st) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    (case res of
      NONE => T
    | SOME _    => rst.locals = rcst.locals )
Proof
  srw_tac[][]>>
  qpat_abbrev_tac`sprog = full_ssa_cc_trans n prog`>>
  full_simp_tac(srw_ss())[full_ssa_cc_trans_def]>>
  pop_assum mp_tac>>LET_ELIM_TAC>>
  assume_tac limit_var_props>>
  pop_assum mp_tac>> impl_tac>- metis_tac[]>>
  srw_tac[][]>>
  imp_res_tac setup_ssa_props>>
  pop_assum(qspec_then`prog` mp_tac)>>
  LET_ELIM_TAC>>
  simp[Abbr`sprog`,Once evaluate_def]>>
  rev_full_simp_tac(srw_ss())[]>>
  Q.ISPECL_THEN [`prog`,`st`,`cst`,`ssa`,`na`] mp_tac ssa_cc_trans_correct>>
  impl_tac>-
    (full_simp_tac(srw_ss())[]>>match_mp_tac every_var_mono>>HINT_EXISTS_TAC >>
    srw_tac[][]>>DECIDE_TAC)>>
  srw_tac[][]>>
  qexists_tac`perm'`>>srw_tac[][]>>
  full_simp_tac(srw_ss())[LET_THM]>>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[]
QED

(* Prove that the ssa form sets up pre_alloc_conventions
   and preserves some syntactic conventions
*)
Triviality fake_moves_conventions:
  ∀ls ssaL ssaR na.
  let (a,b,c,d,e) = fake_moves prio ls ssaL ssaR na in
  every_stack_var is_stack_var a ∧
  every_stack_var is_stack_var b ∧
  call_arg_convention a ∧
  call_arg_convention b
Proof
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>>
  LET_ELIM_TAC>>
  TRY(first_x_assum (assume_tac o SYM)>>
  full_simp_tac(srw_ss())[call_arg_convention_def,every_stack_var_def,fake_moves_def]>>NO_TAC)>>
  EVERY_CASE_TAC>>
  first_x_assum(qspecl_then[`ssaL`,`ssaR`,`na`] mp_tac)>>LET_ELIM_TAC>>
  full_simp_tac(srw_ss())[LET_THM,fake_move_def]>>rpt VAR_EQ_TAC>>
  full_simp_tac(srw_ss())[call_arg_convention_def,every_stack_var_def,fake_moves_def,inst_arg_convention_def]
QED

Triviality fix_inconsistencies_conventions:
  ∀ssaL ssaR na prio.
  let (a:'a wordLang$prog,b:'a wordLang$prog,c,d) =
    fix_inconsistencies prio ssaL ssaR na in
  every_stack_var is_stack_var a ∧
  every_stack_var is_stack_var b ∧
  call_arg_convention a ∧
  call_arg_convention b
Proof
  full_simp_tac(srw_ss())[fix_inconsistencies_def,inst_arg_convention_def,call_arg_convention_def,every_stack_var_def,UNCURRY]>>
  rpt strip_tac>>
  srw_tac[][]>>unabbrev_all_tac>>
  full_simp_tac(srw_ss())[every_stack_var_def,call_arg_convention_def]>>
  qabbrev_tac `ls = MAP FST (toAList (union ssaL ssaR))` >>
  Q.SPECL_THEN [`ls`,`ssa_L'`,`ssa_R'`,`na'`]
  assume_tac fake_moves_conventions>>rev_full_simp_tac(srw_ss())[LET_THM]
QED

(*Prove that the transform sets up arbitrary programs with
  the appropriate conventions*)
Theorem ssa_cc_trans_pre_alloc_conventions:
  ∀prog ssa na.
  is_alloc_var na ∧
  ssa_map_ok na ssa ⇒
  let (prog',ssa',na') = ssa_cc_trans prog ssa na in
  pre_alloc_conventions prog'
Proof
  completeInduct_on`wordLang$prog_size (K 0) prog`>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,LET_THM]>>
  Cases_on`prog`>>
  TRY(full_simp_tac(srw_ss())[ssa_cc_trans_def,pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,LET_THM,UNCURRY]>>srw_tac[][]>>NO_TAC)>>
  full_simp_tac(srw_ss())[ssa_cc_trans_def,pre_alloc_conventions_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[call_arg_convention_def,every_stack_var_def]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    fs[ssa_cc_trans_inst_def,next_var_rename_def]>>
    every_case_tac>>fs[]>>
    rw[]>>fs[every_stack_var_def,call_arg_convention_def,inst_arg_convention_def])
  >-
    (first_x_assum(qspecl_then [`p`,`ssa`,`na`] mp_tac)>>
    size_tac>>simp[])
  >-cheat
    (* ( (* Call *)
    Cases_on`o'`
    >- (
      full_simp_tac(srw_ss())[ssa_cc_trans_def]>>LET_ELIM_TAC>>
      unabbrev_all_tac>>
      full_simp_tac(srw_ss())[every_stack_var_def,call_arg_convention_def])
    >>
    PairCases_on`x`>>Cases_on`o0`>>TRY(PairCases_on`x`)>>
    full_simp_tac(srw_ss())[ssa_cc_trans_def]>>LET_ELIM_TAC>>
    `∀x. x ∈ domain stack_set ⇒ is_stack_var x` by
    (unabbrev_all_tac>>
    rpt (qhdtm_x_assum `list_next_var_rename_move` mp_tac)>>
    full_simp_tac(srw_ss())[domain_fromAList,MAP_ZIP,list_next_var_rename_move_def]>>
    LET_ELIM_TAC>>
    `ALL_DISTINCT (MAP FST (toAList x1))` by full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList]>>
    imp_res_tac list_next_var_rename_lemma_2>>
    pop_assum(qspecl_then [`ssa`,`na+2`] assume_tac)>>
    imp_res_tac list_next_var_rename_lemma_1>>rev_full_simp_tac(srw_ss())[LET_THM]>>
    full_simp_tac(srw_ss())[MAP_MAP_o]>>
    `MEM x new_ls'` by
      (`MAP (option_lookup ssa' o FST) (toAList x1) = new_ls'` by
      (qpat_x_assum`new_ls' = A` sym_sub_tac>>
      qpat_x_assum`A=new_ls'` sym_sub_tac>>
      full_simp_tac(srw_ss())[MAP_EQ_f,option_lookup_def]>>srw_tac[][]>>
      `FST e ∈  domain ssa'` by
        (Cases_on`e`>>
        full_simp_tac(srw_ss())[EXISTS_PROD,MEM_MAP])>>
      full_simp_tac(srw_ss())[domain_lookup])>>
      pop_assum sym_sub_tac>>
      full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD]>>
      metis_tac[])>>
    rev_full_simp_tac(srw_ss())[MEM_MAP,is_stack_var_def]>>
    qspec_then `4` mp_tac arithmeticTheory.MOD_PLUS >>
    impl_tac>-simp[]>>
    disch_then(qspecl_then[`4*x'`,`na+2`](SUBST1_TAC o SYM)) >>
    `(4*x') MOD 4 =0 ` by
      (`0<4:num` by DECIDE_TAC>>
          `∀k.(4:num)*k=k*4` by DECIDE_TAC>>
          metis_tac[arithmeticTheory.MOD_EQ_0])>>
    `is_stack_var (na+2)` by metis_tac[is_alloc_var_flip]>>
    full_simp_tac(srw_ss())[is_stack_var_def])>>
    unabbrev_all_tac>>full_simp_tac(srw_ss())[]>>
    imp_res_tac list_next_var_rename_move_props_2>>
    rev_full_simp_tac(srw_ss())[ssa_map_ok_inter]>>
    first_assum(qspecl_then[`x2`,`ssa_2_p`,`na_2_p`] mp_tac)>>
    size_tac>>
    (impl_keep_tac>-
      (full_simp_tac(srw_ss())[next_var_rename_def]>>
       metis_tac[is_alloc_var_add,ssa_map_ok_extend,convention_partitions]))>>
    strip_tac>>
    TRY(
    imp_res_tac ssa_cc_trans_props>>full_simp_tac(srw_ss())[]>>
    first_x_assum(qspecl_then[`x1'`,`ssa_3_p`,`na_3_p`] mp_tac)>>
    size_tac>>
    impl_tac>-
    (full_simp_tac(srw_ss())[next_var_rename_def]>>
     srw_tac[][]>-
        metis_tac[is_alloc_var_add]
     >-
      (match_mp_tac ssa_map_ok_extend>>
      srw_tac[][]>-
        (match_mp_tac (GEN_ALL ssa_map_ok_more)>>
        qexists_tac`na''`>>
        rev_full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      rev_full_simp_tac(srw_ss())[]>>metis_tac[convention_partitions])))>>
    rpt (qhdtm_x_assum `list_next_var_rename_move` mp_tac)>>
    full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[EQ_SYM_EQ]>>srw_tac[][]>>
    full_simp_tac(srw_ss())[every_stack_var_def,call_arg_convention_def]>>
    full_simp_tac(srw_ss())[every_name_def,toAList_domain,EVERY_MEM]>>
    rev_full_simp_tac(srw_ss())[]>>
    TRY(
    rename1`fix_inconsistencies prio`>>
    Q.ISPECL_THEN [`ssa_2`,`ssa_3`,`na_3`,`prio`] assume_tac fix_inconsistencies_conventions>>
    gvs[EQ_SYM_EQ,LET_THM])>>
    rev_full_simp_tac(srw_ss())[LET_THM]>>
    rpt(pairarg_tac>>gvs[])
    )*)
  >- ( (*Seq*)
    first_assum(qspecl_then[`p`,`ssa`,`na`] assume_tac)>>
    first_x_assum(qspecl_then[`p0`,`ssa'`,`na'`] assume_tac)>>
    ntac 2 (pop_assum mp_tac >> size_tac)>>
    srw_tac[][]>>metis_tac[ssa_cc_trans_props])
  >- ( (*If*)
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[]>>
    imp_res_tac ssa_cc_trans_props>>
    first_assum(qspecl_then[`p`,`ssa`,`na`] mp_tac)>>
    (size_tac>>impl_tac>-full_simp_tac(srw_ss())[])>>
    strip_tac>>
    first_x_assum(qspecl_then[`p0`,`ssa`,`na2`] mp_tac)>>
    (size_tac>>impl_tac>-metis_tac[ssa_map_ok_more])>>
    strip_tac>>
    rev_full_simp_tac(srw_ss())[]>>
    Q.SPECL_THEN [`ssa2`,`ssa3`,`na3`,`prio`] assume_tac fix_inconsistencies_conventions>>
    rev_full_simp_tac(srw_ss())[LET_THM])
  >> cheat
  (*
  (*Alloc and FFI*)
  TRY(full_simp_tac(srw_ss())[Abbr`prog`,list_next_var_rename_move_def]>>
  ntac 2 (qpat_x_assum `A = (B,C,D)` mp_tac)>>
  LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
  qpat_x_assum`A=stack_mov` sym_sub_tac>>
  qpat_x_assum`A=ret_mov` sym_sub_tac>>
  full_simp_tac(srw_ss())[every_stack_var_def,is_stack_var_def,call_arg_convention_def]>>
  full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain]>>
  srw_tac[][Abbr`stack_set`]>>
  full_simp_tac(srw_ss())[domain_numset_list_insert,EVERY_MEM,domain_fromAList]>>
  full_simp_tac(srw_ss())[MAP_ZIP]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  `ALL_DISTINCT ls` by
    (full_simp_tac(srw_ss())[Abbr`ls`]>>metis_tac[ALL_DISTINCT_MAP_FST_toAList])>>
  imp_res_tac list_next_var_rename_lemma_2>>
  pop_assum(qspecl_then[`ssa`,`na+2`] assume_tac)>>rev_full_simp_tac(srw_ss())[LET_THM]>>
  qabbrev_tac `lss = MAP (λx. THE(lookup x ssa')) ls`>>
  (qabbrev_tac `lss' = MAP (option_lookup ssa' o FST) (toAList s)`
   ORELSE
   qabbrev_tac `lss' = MAP (option_lookup ssa' o FST) (toAList s0)`)>>
  `∀x. MEM x lss' ⇒ MEM x lss` by
    (unabbrev_all_tac>>
    full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD]>>srw_tac[][]>>
    res_tac>>
    full_simp_tac(srw_ss())[option_lookup_def]>>
    HINT_EXISTS_TAC>>
    full_simp_tac(srw_ss())[])>>
  `MEM e lss'` by
    (unabbrev_all_tac>>
    full_simp_tac(srw_ss())[MEM_MAP,MAP_MAP_o,EXISTS_PROD]>>
    metis_tac[])>>
  res_tac>>
  qpat_x_assum`A = lss` sym_sub_tac>>
  full_simp_tac(srw_ss())[MEM_MAP]>>
  `is_stack_var (na+2)` by full_simp_tac(srw_ss())[is_alloc_var_flip]>>
  `(4 * x) MOD 4 = 0` by
    (qspec_then `4` assume_tac arithmeticTheory.MOD_EQ_0>>
    full_simp_tac(srw_ss())[]>>pop_assum(qspec_then `x` assume_tac)>>
    DECIDE_TAC)>>
  `(na +2) MOD 4 = 3` by full_simp_tac(srw_ss())[is_stack_var_def]>>
  qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>
  pop_assum mp_tac >>impl_tac>-
    full_simp_tac(srw_ss())[]>>
  disch_then(qspecl_then [`4*x`,`na+2`] assume_tac)>>
  rev_full_simp_tac(srw_ss())[is_stack_var_def])
  >- (
    (* Install *)
    fs[Abbr`prog`,every_stack_var_def,call_arg_convention_def,list_next_var_rename_move_def]>>
    rpt (pairarg_tac>>fs[])>>rw[every_stack_var_def,call_arg_convention_def]>>
    `ALL_DISTINCT ls` by
      (fs[Abbr`ls`]>>metis_tac[ALL_DISTINCT_MAP_FST_toAList])>>
    drule list_next_var_rename_lemma_2>>
    disch_then(qspecl_then[`ssa`,`na+2`] assume_tac)>>rfs[]>>
    simp[Abbr`stack_set`,every_name_def,EVERY_MEM,MEM_MAP,MEM_toAList,EXISTS_PROD,lookup_fromAList]>>
    rw[]>>
    imp_res_tac ALOOKUP_MEM>>
    fs[MEM_MAP]>>
    Cases_on`y`>>fs[MEM_toAList]>>
    `MEM q ls` by
      fs[Abbr`ls`,MEM_toAList,MEM_MAP,EXISTS_PROD]>>
    res_tac>>fs[option_lookup_def]>>
    drule list_next_var_rename_lemma_1>>rw[]>>
    fs[LIST_EQ_REWRITE]>>
    fs[MEM_EL]>>rw[]>>
    pop_assum drule>>
    simp[EL_MAP]>>rw[]>>
    `is_stack_var (na+2)` by metis_tac[is_alloc_var_flip]>>
    fs[is_stack_var_def]>>
    qmatch_goalsub_abbrev_tac`na + (4 * aa + 2)`>>
    `na+(4*aa+2) = aa * 4 + (na+2)` by fs[]>>
    pop_assum SUBST1_TAC>>
    DEP_REWRITE_TAC [MOD_TIMES]>>
    fs[] )
  >> (*ShareInst*)
   IF_CASES_TAC >>
   fs[every_stack_var_def,call_arg_convention_def]
  *)
QED

Triviality setup_ssa_props_2:
  is_alloc_var lim ⇒
  let (mov:'a wordLang$prog,ssa,na) = setup_ssa n lim (prog:'a wordLang$prog) in
    ssa_map_ok na ssa ∧
    is_alloc_var na ∧
    pre_alloc_conventions mov ∧
    lim ≤ na
Proof
  srw_tac[][setup_ssa_def,list_next_var_rename_move_def,pre_alloc_conventions_def]>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,evaluate_def,every_stack_var_def,call_arg_convention_def]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  full_simp_tac(srw_ss())[LET_THM,MAP_ZIP,LENGTH_COUNT_LIST]>>
  full_simp_tac(srw_ss())[ALL_DISTINCT_MAP]>>
  TRY(`ssa_map_ok lim LN` by
    full_simp_tac(srw_ss())[ssa_map_ok_def,lookup_def]>>
  imp_res_tac list_next_var_rename_props>>NO_TAC)
QED

Theorem full_ssa_cc_trans_pre_alloc_conventions:
 ∀n prog.
  pre_alloc_conventions (full_ssa_cc_trans n prog)
Proof
  full_simp_tac(srw_ss())[full_ssa_cc_trans_def,pre_alloc_conventions_def,list_next_var_rename_move_def]>>LET_ELIM_TAC>>
  full_simp_tac(srw_ss())[Abbr`lim'`]>>
  imp_res_tac limit_var_props>>
  imp_res_tac setup_ssa_props_2>>
  pop_assum(qspecl_then [`prog`,`n`] assume_tac)>>rev_full_simp_tac(srw_ss())[LET_THM]>>
  imp_res_tac ssa_cc_trans_props>>
  Q.ISPECL_THEN [`prog`,`ssa`,`na`] assume_tac ssa_cc_trans_pre_alloc_conventions>>
  rev_full_simp_tac(srw_ss())[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,LET_THM]
QED

Triviality fake_moves_distinct_tar_reg:
  ∀ls ssal ssar na l r a b c conf.
  fake_moves prio ls ssal ssar na = (l,r,a,b,c) ⇒
  every_inst distinct_tar_reg l ∧
  every_inst distinct_tar_reg r
Proof
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>>srw_tac[][]>>full_simp_tac(srw_ss())[every_inst_def]>>
  pop_assum mp_tac>> LET_ELIM_TAC>> EVERY_CASE_TAC>> full_simp_tac(srw_ss())[LET_THM]>>
  unabbrev_all_tac>>
  metis_tac[fake_move_def,every_inst_def,distinct_tar_reg_def]
QED

Theorem ssa_cc_trans_distinct_tar_reg:
  ∀prog ssa na.
    is_alloc_var na ∧
    every_var (λx. x < na) prog ∧
    ssa_map_ok na ssa ⇒
    every_inst distinct_tar_reg (FST (ssa_cc_trans prog ssa na))
Proof
  ho_match_mp_tac ssa_cc_trans_ind>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>srw_tac[][]>>
  unabbrev_all_tac>>
  full_simp_tac(srw_ss())[every_inst_def]>>imp_res_tac ssa_cc_trans_props>>full_simp_tac(srw_ss())[]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    full_simp_tac(srw_ss())[ssa_cc_trans_inst_def,LET_THM,next_var_rename_def]>>
    every_case_tac>>
    rw[]>>
    fs[every_var_def,every_var_inst_def,every_var_imm_def,every_inst_def]>>
    full_simp_tac(srw_ss())[distinct_tar_reg_def,ssa_map_ok_def,option_lookup_def]>>
    EVERY_CASE_TAC>>srw_tac[][]>>res_tac>>full_simp_tac(srw_ss())[]>>
    fs[is_alloc_var_def]>>CCONTR_TAC>>fs[])
  >-
    (full_simp_tac(srw_ss())[every_var_def]>>
    first_x_assum match_mp_tac>>
    match_mp_tac every_var_mono >>
    HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>DECIDE_TAC)
  >-
    full_simp_tac(srw_ss())[every_var_def]
  >-
    (full_simp_tac(srw_ss())[every_var_def]>>qpat_x_assum`A = (B,C,D,E)`mp_tac>>full_simp_tac(srw_ss())[fix_inconsistencies_def,fake_moves_def]>>LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[every_inst_def,EQ_SYM_EQ]>>
    TRY(metis_tac[fake_moves_distinct_tar_reg])>>
    first_x_assum match_mp_tac>>
    srw_tac[][]
    >-
      (match_mp_tac every_var_mono >>
      HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>DECIDE_TAC)
    >>
    metis_tac[ssa_map_ok_more])
  >> TRY
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[every_inst_def,EQ_SYM_EQ]>>NO_TAC)
  >-
   (rename [‘OpCurrHeap’]>>
    full_simp_tac(srw_ss())[ssa_cc_trans_inst_def,LET_THM,next_var_rename_def]>>
    every_case_tac>> rw[]>>
    fs[every_var_def,every_var_inst_def,every_var_imm_def,every_inst_def]>>
    full_simp_tac(srw_ss())[distinct_tar_reg_def,ssa_map_ok_def,option_lookup_def]>>
    EVERY_CASE_TAC>>srw_tac[][]>>res_tac>>full_simp_tac(srw_ss())[]>>
    fs[is_alloc_var_def]>>CCONTR_TAC>>fs[])
  >>
  FULL_CASE_TAC>>full_simp_tac(srw_ss())[every_var_def,every_inst_def]

  >-
    (qpat_x_assum`A ∧ B ∧ C ⇒ every_inst distinct_tar_reg D` mp_tac>>
    impl_tac>-
      (
        qmatch_asmsub_abbrev_tac `list_next_var_rename_move _ _ ls` >>
        qspecl_then [`ret`, `ssa''`, `na''`]  assume_tac list_next_var_rename_props >>
        qspecl_then [`ls`, `ssa`, `na`]  assume_tac list_next_var_rename_move_props_2 >>
        qspecl_then [`ls`, `(inter ssa' (union (FST numset) (SND numset)))`, `na'`]  assume_tac list_next_var_rename_move_props_2 >>
        ntac 3 (pop_assum mp_tac) >>
        full_simp_tac(srw_ss())[]>>
        rpt disch_tac >>
        full_simp_tac(srw_ss())[]>>
       `ssa_map_ok na' (inter ssa' (union (FST numset) (SND numset)))` by
        metis_tac[ssa_map_ok_inter]>>
        full_simp_tac(srw_ss())[]>>
        match_mp_tac every_var_mono>>HINT_EXISTS_TAC>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >>
      full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>
      rpt(qpat_x_assum`A=(B,C,D)` mp_tac)>>
      LET_ELIM_TAC>>full_simp_tac(srw_ss())[EQ_SYM_EQ,every_inst_def])
    >>
      PairCases_on`x`>>full_simp_tac(srw_ss())[fix_inconsistencies_def]>>LET_ELIM_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[every_inst_def]>>
      qpat_x_assum`A ∧ B ∧ C ⇒ every_inst distinct_tar_reg ren_ret_handler` mp_tac>>
      impl_keep_tac>-
        (
        gvs[] >>
        qmatch_asmsub_abbrev_tac `list_next_var_rename_move _ _ ls` >>
        qspecl_then [`ret`, `ssa''`, `na''`]  assume_tac list_next_var_rename_props >>
        qspecl_then [`ls`, `ssa`, `na`]  assume_tac list_next_var_rename_move_props_2 >>
        qspecl_then [`ls`, `(inter ssa' (union (FST numset) (SND numset)))`, `na'`]  assume_tac list_next_var_rename_move_props_2 >>
        ntac 3 (pop_assum mp_tac) >>
        full_simp_tac(srw_ss())[]>>
        rpt disch_tac >>
        full_simp_tac(srw_ss())[]>>
        `ssa_map_ok na' (inter ssa' (union (FST numset) (SND numset)))` by
          metis_tac[ssa_map_ok_inter]>>
        full_simp_tac(srw_ss())[]>>
        match_mp_tac every_var_mono>>
        qexists_tac` λx. x < na`>>full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)
        >>
      qpat_x_assum`A ∧ B ∧ C ⇒ every_inst distinct_tar_reg ren_exc_handler` mp_tac>>
      impl_keep_tac>-
        (
        gvs[] >>
        qmatch_asmsub_abbrev_tac `list_next_var_rename_move _ _ ls` >>
        qspecl_then [`ret`, `ssa''`, `na''`]  assume_tac list_next_var_rename_props >>
        qspecl_then [`ls`, `ssa`, `na`]  assume_tac list_next_var_rename_move_props_2 >>
        qspecl_then [`ls`, `(inter ssa' (union (FST numset) (SND numset)))`, `na'`]  assume_tac list_next_var_rename_move_props_2 >>
        ntac 3 (pop_assum mp_tac) >>
        full_simp_tac(srw_ss())[]>>
        rpt disch_tac >>
        full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[next_var_rename_def]>>
        `ssa_map_ok na' (inter ssa' (union (FST numset) (SND numset)))` by
          metis_tac[ssa_map_ok_inter]>>
        rev_full_simp_tac(srw_ss())[]>>srw_tac[][]
        >-
          metis_tac[is_alloc_var_add]
        >-
          (match_mp_tac every_var_mono>>
          qexists_tac` λx. x < na`>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)
        >>
          match_mp_tac ssa_map_ok_extend>>
          full_simp_tac(srw_ss())[]>>srw_tac[][]
          >-
            (`na'' ≤ n'` by DECIDE_TAC>>
            metis_tac[ssa_map_ok_more])
          >> metis_tac[convention_partitions])
      >>
      full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>
      rpt(qpat_x_assum`A=(B,C,D)` mp_tac)>>
      LET_ELIM_TAC>>full_simp_tac(srw_ss())[EQ_SYM_EQ,every_inst_def]>>
      metis_tac[fake_moves_distinct_tar_reg]
QED

Theorem full_ssa_cc_trans_distinct_tar_reg:
  ∀n prog.
    every_inst distinct_tar_reg (full_ssa_cc_trans n prog)
Proof
  srw_tac[][]>>
  full_simp_tac(srw_ss())[full_ssa_cc_trans_def]>>
  LET_ELIM_TAC>>
  simp[every_inst_def]>>CONJ_TAC
  >-
    (full_simp_tac(srw_ss())[setup_ssa_def,list_next_var_rename_move_def,LET_THM]>>
    pairarg_tac>>full_simp_tac(srw_ss())[]>>
    metis_tac[every_inst_def])
  >>
  assume_tac limit_var_props>>
  full_simp_tac(srw_ss())[markerTheory.Abbrev_def]>>
  rev_full_simp_tac(srw_ss())[]>>
  imp_res_tac setup_ssa_props_2>>
  pop_assum(qspecl_then[`prog`,`n`] mp_tac)>>
  LET_ELIM_TAC>>
  gvs[]>>
  drule ssa_cc_trans_distinct_tar_reg>>
  disch_then (drule_at Any)>>
  disch_then(qspecl_then[`prog`] mp_tac)>>
  impl_tac>- (
    simp[]>>
    match_mp_tac every_var_mono>>
    first_x_assum (irule_at Any)>>
    simp[])>>
  simp[]
QED

Triviality exp_to_addr_ShareInst:
  exp_to_addr exp = SOME (Addr n c) <=>
    ((exp = Var n /\ c = 0w) \/ (exp = Op Add [Var n; Const c]))
Proof
  eq_tac
  >- (
    simp[DefnBase.one_line_ify NONE exp_to_addr_def] >>
    rpt (TOP_CASE_TAC >> simp[])
  ) >>
  rw[] >>
  simp[exp_to_addr_def]
QED

Triviality fake_moves_conventions2:
  ∀ls ssal ssar na l r a b c conf.
  fake_moves prio ls ssal ssar na = (l,r,a,b,c) ⇒
  full_inst_ok_less conf l ∧
  full_inst_ok_less conf r ∧
  every_inst distinct_tar_reg l ∧
  every_inst distinct_tar_reg r
Proof
  Induct>>full_simp_tac(srw_ss())[fake_moves_def]>>srw_tac[][]>>full_simp_tac(srw_ss())[flat_exp_conventions_def,full_inst_ok_less_def,every_inst_def]>>
  pop_assum mp_tac>> LET_ELIM_TAC>> EVERY_CASE_TAC>> full_simp_tac(srw_ss())[LET_THM]>>
  unabbrev_all_tac>>
  rveq>>fs[flat_exp_conventions_def,fake_move_def,full_inst_ok_less_def,inst_ok_less_def,every_inst_def,distinct_tar_reg_def]>>
  metis_tac[]
QED

Theorem ssa_cc_trans_full_inst_ok_less[local]:
  ∀prog ssa na c.
    every_var (λx. x < na) prog ∧
    is_alloc_var na ∧
    ssa_map_ok na ssa ∧
    full_inst_ok_less c prog ⇒
    full_inst_ok_less c (FST (ssa_cc_trans prog ssa na))
Proof
  ho_match_mp_tac ssa_cc_trans_ind>>
  full_simp_tac(srw_ss())[ssa_cc_trans_def]>>srw_tac[][]>>
  unabbrev_all_tac>>
  full_simp_tac(srw_ss())[full_inst_ok_less_def]
  >- (
    full_simp_tac(srw_ss())[oneline ssa_cc_trans_inst_def,LET_THM,next_var_rename_def,ssa_map_ok_def,
    AllCaseEqs()]>> rveq >>
    full_simp_tac(srw_ss())[EQ_SYM_EQ,inst_ok_less_def,full_inst_ok_less_def,every_var_def,every_var_inst_def]>>
    rw[]>>
    fs[option_lookup_def]>>every_case_tac>>rw[]>>
    pop_assum (assume_tac o SYM)>>res_tac>>
    intLib.ARITH_TAC)
  >>
  (* Some trivial cases *)
  TRY
    (rw[]>>first_x_assum match_mp_tac>>fs[every_var_def]>>
    imp_res_tac ssa_cc_trans_props>>
    fs[]>>
    match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC>>fs[])
  >- ( (* If *)
    pop_assum mp_tac>>
    fs[fix_inconsistencies_def,fake_moves_def]>>
    rpt(pairarg_tac>>gvs[])>>
    strip_tac>>gvs[]>>
    fs[full_inst_ok_less_def,every_var_def]>>
    CONJ_TAC >- metis_tac[fake_moves_conventions2]>>
    CONJ_TAC >- (
      first_x_assum match_mp_tac>>
      imp_res_tac ssa_cc_trans_props>>fs[]>>
      CONJ_TAC>-
        (match_mp_tac every_var_mono>>HINT_EXISTS_TAC>>fs[])>>
      match_mp_tac ssa_map_ok_more>>fs[])>>
    metis_tac[fake_moves_conventions2])
  >>
    TRY
    (full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>
    rpt (pop_assum mp_tac)>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[full_inst_ok_less_def,EQ_SYM_EQ]>>NO_TAC)
  >-
    ((*Call SOME*)
    EVERY_CASE_TAC>>unabbrev_all_tac>>
    gvs[fix_inconsistencies_def]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[full_inst_ok_less_def]>>
    rpt(first_x_assum (irule_at Any))>>
    imp_res_tac fake_moves_conventions2>>
    gvs[every_var_def,list_next_var_rename_move_def,next_var_rename_def]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[full_inst_ok_less_def]>>
    ntac 2 (pop_assum mp_tac) >>
    qmatch_asmsub_abbrev_tac `list_next_var_rename ret _ m` >>
    qmatch_goalsub_abbrev_tac `list_next_var_rename ls _ _` >>
    disch_tac >>
    qmatch_asmsub_abbrev_tac `list_next_var_rename ls ssa''' (m' + _)` >>
    disch_tac >>
    qspecl_then [`ret`,`ssa''`,`m`] mp_tac list_next_var_rename_props >>
    qspecl_then [`ls`,`ssa'''`,`m'`] mp_tac list_next_var_rename_props_2 >>
    qspecl_then [`ls`,`ssa`,`na`] mp_tac list_next_var_rename_props_2 >>
    gvs[] >> rpt disch_tac >>
    `ssa_map_ok (na+2) ssa` by (
      match_mp_tac ssa_map_ok_more>>
      simp[])>> gvs[] >>
    `ssa_map_ok (m' +2) ssa'''` by (
      simp[Abbr`ssa'''`] >>
      match_mp_tac ssa_map_ok_inter>>
      irule ssa_map_ok_more>>
      first_x_assum (irule_at Any)>>
      simp[])>> gvs[]
    >-(
      match_mp_tac every_var_mono >>
      first_x_assum (irule_at Any) >>
      simp[])
    >-(
    CONJ_TAC
    >-(
      match_mp_tac every_var_mono >>
      first_x_assum (irule_at Any) >>
      simp[]) >>
    qspecl_then [`prog`,`ssa_2_p`,`na_2_p`] mp_tac ssa_cc_trans_props>>
    gvs[] >> rpt disch_tac >> gvs[is_alloc_var_add] >>
    CONJ_TAC
    >-(
      match_mp_tac every_var_mono >>
      first_x_assum (irule_at Any) >>
      simp[])
    >- (
      irule ssa_map_ok_insert >>
      irule_at Any ssa_map_ok_more >>
      first_x_assum (irule_at Any)>>
      simp[Once convention_partitions])))
  >> (*ShareInst*)
    qpat_x_assum `option_CASE _ _ _` mp_tac >>
    ntac 2 TOP_CASE_TAC >>
    strip_tac >>
    IF_CASES_TAC >>
    simp[full_inst_ok_less_def] >>
    gvs[exp_to_addr_ShareInst,ssa_cc_trans_exp_def] >>
    simp[exp_to_addr_def]
QED

Theorem full_ssa_cc_trans_full_inst_ok_less:
  ∀prog n c.
  full_inst_ok_less c prog ⇒
  full_inst_ok_less c (full_ssa_cc_trans n prog)
Proof
  full_simp_tac(srw_ss())[full_ssa_cc_trans_def,list_next_var_rename_move_def]>>
  LET_ELIM_TAC>>
  fs[markerTheory.Abbrev_def]>>
  imp_res_tac (GSYM limit_var_props)>>
  imp_res_tac setup_ssa_props_2>>
  pop_assum(qspecl_then [`prog`,`n`] assume_tac)>>
  rfs[]>>
  fs[setup_ssa_def,list_next_var_rename_move_def]>>
  pairarg_tac>>fs[]>>rpt var_eq_tac>>fs[full_inst_ok_less_def]>>
  Q.SPECL_THEN [`prog`,`ssa`,`n'`,`c`] mp_tac ssa_cc_trans_full_inst_ok_less>>
  impl_tac>>fs[]>>
  match_mp_tac every_var_mono>>
  HINT_EXISTS_TAC>>fs[]
QED

(* word_alloc syntactic stuff *)

val is_phy_var_tac =
    full_simp_tac(srw_ss())[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

Triviality call_arg_convention_preservation:
  ∀prog f.
  every_var (λx. is_phy_var x ⇒ f x = x) prog ∧
  call_arg_convention prog ⇒
  call_arg_convention (apply_colour f prog)
Proof
  ho_match_mp_tac call_arg_convention_ind>>
  srw_tac[][call_arg_convention_def,every_var_def]>>
  EVERY_CASE_TAC>>unabbrev_all_tac>>
  full_simp_tac(srw_ss())[call_arg_convention_def]
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`r`)>>TRY(Cases_on`m`)>>
    TRY(Cases_on`f'`>>every_case_tac)>>
    fs[inst_arg_convention_def,every_var_inst_def,is_phy_var_def]) >>
  TRY(is_phy_var_tac>>NO_TAC)>>
  rpt conj_tac >>
  TRY (qpat_abbrev_tac `ysl = LENGTH _` >> gvs[]) >>
  fs[MAP_GENLIST,GENLIST_FUN_EQ,EVERY_GENLIST] >>
  rw[] >> res_tac >> is_phy_var_tac
QED

(*Composing with a function using apply_colour*)
Theorem every_var_inst_apply_colour_inst:
    ∀P inst Q f.
  every_var_inst P inst ∧
  (∀x. P x ⇒ Q (f x)) ⇒
  every_var_inst Q (apply_colour_inst f inst)
Proof
  ho_match_mp_tac every_var_inst_ind>>srw_tac[][every_var_inst_def]>>
  TRY(Cases_on`ri`>>full_simp_tac(srw_ss())[apply_colour_imm_def])>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[every_var_imm_def]
QED

Theorem every_var_exp_apply_colour_exp:
    ∀P exp Q f.
  every_var_exp P exp ∧
  (∀x. P x ⇒ Q (f x)) ⇒
  every_var_exp Q (apply_colour_exp f exp)
Proof
  ho_match_mp_tac every_var_exp_ind>>srw_tac[][every_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MAP,EVERY_MEM]
QED

Theorem every_var_apply_colour:
    ∀P prog Q f.
  every_var P prog ∧
  (∀x. P x ⇒ Q (f x)) ⇒
  every_var Q (apply_colour f prog)
Proof
  ho_match_mp_tac every_var_ind>>srw_tac[][every_var_def]>>
  full_simp_tac(srw_ss())[MAP_ZIP,(GEN_ALL o SYM o SPEC_ALL) MAP_MAP_o]>>
  full_simp_tac(srw_ss())[EVERY_MAP,EVERY_MEM]
  >-
    metis_tac[every_var_inst_apply_colour_inst]
  >-
    metis_tac[every_var_exp_apply_colour_exp]
  >-
    metis_tac[every_var_exp_apply_colour_exp]
  >-
    (Cases_on `names` >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>srw_tac[][]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
  >-
    (Cases_on `names` >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>srw_tac[][]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
  >-
    (EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[every_var_def,EVERY_MAP,EVERY_MEM]>>
    rename1 `(apply_nummaps_key f names)` >>
    Cases_on `names` >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
  >-
    (Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def])
  >-
    (Cases_on `numset` >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>srw_tac[][]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
  >>
    metis_tac[every_var_exp_apply_colour_exp]
QED

Theorem every_stack_var_apply_colour:
    ∀P prog Q f.
  every_stack_var P prog ∧
  (∀x. P x ⇒ Q (f x)) ⇒
  every_stack_var Q (apply_colour f prog)
Proof
  ho_match_mp_tac every_stack_var_ind>>srw_tac[][every_stack_var_def]
  >>
  (EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[every_stack_var_def,EVERY_MAP,EVERY_MEM]>>
    TRY (rename1 `(apply_nummaps_key f names)` >> Cases_on `names`) >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
QED

Triviality every_var_exp_get_reads_exp:
  ∀exp. every_var_exp (λx. MEM x (get_reads_exp exp)) exp
Proof
  assume_tac every_var_exp_get_live_exp>>
  rw[]>>pop_assum(qspec_then`exp` assume_tac)>>
  ho_match_mp_tac every_var_exp_mono>>
  HINT_EXISTS_TAC>>fs[get_reads_exp_get_live_exp]
QED

val exp_tac =
  assume_tac (Q.SPEC `exp` every_var_exp_get_reads_exp)>>
  ho_match_mp_tac every_var_exp_mono>>
  HINT_EXISTS_TAC>>fs[in_clash_tree_def];

Triviality every_var_in_get_clash_tree:
  ∀prog.
  every_var (in_clash_tree (get_clash_tree prog)) prog
Proof
  ho_match_mp_tac get_clash_tree_ind>>rw[get_clash_tree_def]>>
  fs[every_var_def,in_clash_tree_def,EVERY_MEM,in_clash_tree_def,every_name_def,toAList_domain]>>
  TRY(exp_tac)
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`r`)>>TRY(Cases_on`m`)>>TRY(Cases_on`f`)>>
    fs[every_var_imm_def,get_delta_inst_def,every_var_inst_def,in_clash_tree_def])
  >-
    metis_tac[every_var_mono,in_clash_tree_def]
  >-
    (Cases_on`ri`>>fs[every_var_imm_def]>>
    rw[]>>
    `MEM r1 [r1]` by fs[]>>
    `MEM r1 [r1;n] ∧ MEM n [r1;n]` by fs[]>>
    metis_tac[every_var_mono,in_clash_tree_def])
  >>
    EVERY_CASE_TAC>>
    fs[in_clash_tree_def,domain_numset_list_insert,domain_union]>>
    metis_tac[every_var_mono,in_clash_tree_def]
QED

Triviality every_var_T:
  ∀prog.
  every_var (λx. T) prog
Proof
  rw[]>>
  mp_tac (Q.SPEC`prog` max_var_max)>>
  rw[]>>
  ho_match_mp_tac every_var_mono>>HINT_EXISTS_TAC>>
  fs[]
QED

Triviality every_var_is_phy_var_total_colour:
  every_var is_phy_var (apply_colour (total_colour col) prog)
Proof
  match_mp_tac every_var_apply_colour>>
  qexists_tac`\x. T`>>
  simp[every_var_T]>>
  fs[total_colour_def]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  is_phy_var_tac
QED

Triviality oracle_colour_ok_conventions:
  pre_alloc_conventions prog ∧
  oracle_colour_ok k col_opt (get_clash_tree prog) prog ls = SOME x ⇒
  post_alloc_conventions k x
Proof
  fs[oracle_colour_ok_def]>>EVERY_CASE_TAC>>
  fs[post_alloc_conventions_def,pre_alloc_conventions_def]>>
  rw[]>>fs[every_var_is_phy_var_total_colour]>>
  match_mp_tac call_arg_convention_preservation>>fs[]>>
  ho_match_mp_tac every_var_mono>>
  qexists_tac`λx. T`>>fs[every_var_T]>>
  rw[total_colour_def]>>FULL_CASE_TAC>>
  fs[every_even_colour_def]>>
  fs[GSYM MEM_toAList]>>
  fs[EVERY_MEM,FORALL_PROD]>>
  first_x_assum drule>>rw[]>>
  metis_tac[is_phy_var_def,EVEN_MOD2,EVEN_EXISTS,TWOxDIV2]
QED

Theorem pre_post_conventions_word_alloc:
  ∀fc c alg prog k col_opt.
  pre_alloc_conventions prog ⇒
  post_alloc_conventions k (word_alloc fc c alg k prog col_opt)
Proof
  rpt strip_tac>>fs[word_alloc_def]>>
  reverse TOP_CASE_TAC>>fs[]
  >-
    metis_tac[oracle_colour_ok_conventions]
  >>
  qpat_abbrev_tac`forced = get_forced _ _ _`>>
  qpat_abbrev_tac`tree = get_clash_tree _`>>
  qpat_abbrev_tac`fs = get_stack_only _`>>
  `EVERY (λx,y.in_clash_tree tree x ∧ in_clash_tree tree y) forced` by
    (unabbrev_all_tac>>fs[get_forced_in_get_clash_tree])>>
  pairarg_tac>>fs[]>>
  drule select_reg_alloc_correct>>
  disch_then(qspecl_then [`alg`,`spillcosts`,`k`,`heu_moves`,`fs`] assume_tac)>>rfs[]>>fs[]>>
  assume_tac (Q.ISPEC`prog:'a wordLang$prog`every_var_in_get_clash_tree)>>
  rfs[]>>
  fs[post_alloc_conventions_def,pre_alloc_conventions_def]>>rw[]
  >-
    metis_tac[every_var_is_phy_var_total_colour]
  >-
    (match_mp_tac every_stack_var_apply_colour>>
    imp_res_tac every_var_imp_every_stack_var>>
    qexists_tac `λx. (in_clash_tree tree x ∧ is_stack_var x)` >>srw_tac[][]
    >-
      metis_tac[every_stack_var_conj,ETA_AX]
    >>
    first_x_assum drule>>fs[]>>
    rw[total_colour_def,sp_default_def,domain_lookup]>>rfs[]>>
    metis_tac[convention_partitions])
  >>
    match_mp_tac call_arg_convention_preservation>>
    srw_tac[][]>>match_mp_tac every_var_mono>>
    qexists_tac `in_clash_tree tree` >> rw[]>>
    first_x_assum drule>>fs[]>>rw[]>>
    fs[total_colour_def,sp_default_def,domain_lookup]>>rfs[]>>
    metis_tac[is_phy_var_def,EVEN_MOD2,EVEN_EXISTS,TWOxDIV2]
QED

(*word_alloc preserves syntactic conventions*)
Triviality word_alloc_full_inst_ok_less_lem:
  ∀f prog c.
  full_inst_ok_less c prog ∧
  EVERY (λ(x,y). (f x) ≠ (f y)) (get_forced c prog []) ⇒
  full_inst_ok_less c (apply_colour f prog)
Proof
  ho_match_mp_tac apply_colour_ind>>
  fs[full_inst_ok_less_def,get_forced_def]>>rw[]>>
  TRY
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f'`)>>
    fs[inst_ok_less_def,full_inst_ok_less_def]>>
    rw[]>>fs[]>>rfs[])
  >>
    EVERY_CASE_TAC>>unabbrev_all_tac>>
    gvs[get_forced_def,DefnBase.one_line_ify NONE
      exp_to_addr_def,AllCaseEqs(),apply_colour_exp_def]>>
    metis_tac[EVERY_get_forced]
QED

(*
Triviality lookup_undir_g_insert_existing:
  lookup x G = SOME v ⇒
  lookup x (undir_g_insert a b G) =
  if x = a then SOME (insert b () v)
  else if x = b then SOME (insert a () v)
  else SOME v
Proof
  rw[undir_g_insert_def,dir_g_insert_def,lookup_insert]>>
  fs[insert_shadow]
QED
*)

Triviality forced_distinct_col:
  EVERY (λ(x,y). (sp_default spcol) x = (sp_default spcol) y ⇒ x = y) ls /\
  EVERY (λx,y. x ≠ y) ls ==>
  EVERY (λ(x,y). (total_colour spcol) x <> (total_colour spcol) y) ls
Proof
  fs[EVERY_MEM,FORALL_PROD]>>rw[]>>
  first_x_assum drule>>
  fs[total_colour_alt]>>
  metis_tac[]
QED

Theorem word_alloc_full_inst_ok_less:
  ∀fc alg k prog col_opt c.
  full_inst_ok_less c prog ⇒
  full_inst_ok_less c (word_alloc fc c alg k prog col_opt)
Proof
  fs[word_alloc_def,oracle_colour_ok_def]>>
  rpt strip_tac>>
  pairarg_tac>>fs[]>>
  qpat_abbrev_tac`forced = get_forced _ _ _`>>
  qpat_abbrev_tac`tree = get_clash_tree prog`>>
  qpat_abbrev_tac`fs = get_stack_only _`>>
  EVERY_CASE_TAC>>fs[]>>
  rw[]>>rveq>>
  match_mp_tac word_alloc_full_inst_ok_less_lem>>fs[]>>
  `EVERY (λx,y.in_clash_tree tree x ∧ in_clash_tree tree y) forced` by
    (unabbrev_all_tac>>fs[get_forced_in_get_clash_tree])>>
  drule select_reg_alloc_correct>>
  disch_then(qspecl_then [`alg`,`spillcosts`,`k`,`heu_moves`,`fs`] assume_tac)>>rfs[]>>
  fs[]>>
  match_mp_tac forced_distinct_col>>rfs[]>>
  unabbrev_all_tac>>
  match_mp_tac get_forced_pairwise_distinct>>
  simp[]
QED

val _ = export_theory();

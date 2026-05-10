(*
  Correctness proof for word_alloc
*)
Theory word_allocProof
Libs
  preamble
Ancestors
  mllist wordLang wordSem wordProps word_alloc reg_alloc
  reg_allocProof linear_scan linear_scanProof wordConvs

(* Ensures we have the correct ML bindings *)
open reg_allocTheory reg_allocProofTheory linear_scanTheory
     linear_scanProofTheory wordLangTheory wordSemTheory wordPropsTheory
     wordConvsTheory word_allocTheory;

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

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

Theorem INJ_UNION[local]:
  !f A B.
  INJ f (A ∪ B) UNIV ⇒
  INJ f A UNIV ∧
  INJ f B UNIV
Proof
  srw_tac[][]>>
  metis_tac[INJ_SUBSET,SUBSET_DEF,SUBSET_UNION]
QED

Theorem INJ_less[local]:
  INJ f s' UNIV ∧ s ⊆ s'
  ⇒
  INJ f s UNIV
Proof
  metis_tac[INJ_DEF,SUBSET_DEF]
QED

Theorem LET_FORALL_ELIM'[local]:
 LET f v ⇔ $! (S ($==> ∘ $= v) f)
Proof
  simp[combinTheory.LET_FORALL_ELIM,o_DEF,S_DEF,markerTheory.Abbrev_def]
QED
(* TODO: can we have a global for this *)
Definition hide_def:
  hide x = x
End

Theorem INJ_IMP_IMAGE_DIFF[local]:
  INJ f (s ∪ t) UNIV ⇒
  IMAGE f (s DIFF t) = (IMAGE f s) DIFF (IMAGE f t)
Proof
  rw[EXTENSION,EQ_IMP_THM]>> TRY (metis_tac[])>>
  fs[INJ_DEF]>>
  metis_tac[]
QED

Theorem INJ_IMP_IMAGE_DIFF_single[local]:
  INJ f (s ∪ {n}) UNIV ⇒
  (IMAGE f s) DIFF {f n} = IMAGE f (s DIFF {n})
Proof
  rw[]>>
  `{f n} = IMAGE f {n}` by fs[]>>
  fs[INJ_IMP_IMAGE_DIFF]
QED

Theorem INJ_ALL_DISTINCT_MAP[local]:
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
  (colouring_ok f (Seq s1 s2) live lt =
    (*Normal live sets*)
    let s2_live = get_live s2 live lt in
    let s1_live = get_live s1 s2_live lt in
      INJ f (domain s1_live) UNIV ∧
      (*Internal clash sets*)
      colouring_ok f s2 live lt ∧ colouring_ok f s1 s2_live lt) ∧
  (colouring_ok f (If cmp r1 ri e2 e3) live lt =
    let e2_live = get_live e2 live lt in
    let e3_live = get_live e3 live lt in
    let union_live = union e2_live e3_live in
    let merged = case ri of Reg r2 => insert r2 () (insert r1 () union_live)
                      | _ => insert r1 () union_live in
    (*All of them must be live at once*)
      INJ f (domain merged) UNIV ∧
      (*Internal clash sets*)
      colouring_ok f e2 live lt ∧ colouring_ok f e3 live lt) ∧
  (colouring_ok f (Call(SOME(v,cutset,ret_handler,l1,l2))dest args h) live lt =
    let args_set = numset_list_insert args LN in
    let all_names = union (SND cutset) (FST cutset) in
    INJ f (domain (union all_names args_set)) UNIV ∧
    INJ f (domain (numset_list_insert v all_names )) UNIV ∧
    (*returning handler*)
    colouring_ok f ret_handler live lt ∧
    (*exception handler*)
    (case h of
    | NONE => T
    | SOME(v,prog,l1,l2) =>
        INJ f (domain (insert v () all_names)) UNIV ∧
        colouring_ok f prog live lt)) ∧
  (colouring_ok f (MustTerminate p) live lt =
    colouring_ok f p live lt) ∧
  (colouring_ok f (Loop names body exit_names) live lt =
    (INJ f (domain names) UNIV ∧
    INJ f (domain exit_names) UNIV ∧
    colouring_ok f body names ((names,exit_names)::lt))) ∧
  (colouring_ok f prog live lt =
    (*live before must be fine, and clash set must be fine*)
    let lset = get_live prog live lt in
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

Theorem strong_locals_rel_subset_domain[local]:
  strong_locals_rel f s l1 l2 ∧ s ⊆ domain l1 ⇒
  ∀v. v ∈ s ⇒ f v ∈ domain l2
Proof
  rpt strip_tac >>
  `v ∈ domain l1` by
    (qpat_x_assum `s ⊆ _` (mp_tac o SIMP_RULE std_ss [SUBSET_DEF]) >>
     disch_then drule >> simp[]) >>
  fs[domain_lookup] >>
  qpat_x_assum `strong_locals_rel _ _ _ _`
    (assume_tac o REWRITE_RULE [strong_locals_rel_def]) >>
  first_x_assum drule_all >>
  rw[] >>
  first_assum (irule_at Any)
QED

Theorem domain_numset_list_insert:
    ∀ls locs.
  domain (numset_list_insert ls locs) = domain locs UNION set ls
Proof
  Induct>>full_simp_tac(srw_ss())[numset_list_insert_def]>>srw_tac[][]>>
  metis_tac[INSERT_UNION_EQ,UNION_COMM]
QED

Theorem strong_locals_rel_get_var[local]:
  strong_locals_rel f live st.locals cst.locals ∧
  n ∈ live ∧
  get_var n st = SOME x
  ⇒
  get_var (f n) cst = SOME x
Proof
  full_simp_tac(srw_ss())[get_var_def,strong_locals_rel_def]
QED

Theorem strong_locals_rel_get_var_imm[local]:
  strong_locals_rel f live st.locals cst.locals ∧
  (case n of Reg n => n ∈ live | _ => T) ∧
  get_var_imm n st = SOME x
  ⇒
  get_var_imm (apply_colour_imm f n) cst = SOME x
Proof
  Cases_on`n`>>full_simp_tac(srw_ss())[get_var_imm_def]>>
  metis_tac[strong_locals_rel_get_var]
QED

Theorem strong_locals_rel_get_vars[local]:
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

Theorem strong_locals_rel_UNION:
    strong_locals_rel f (A ∪ B) t l <=> strong_locals_rel f A t l /\ strong_locals_rel f B t l
Proof
   EQ_TAC >> DISCH_TAC >> fs[strong_locals_rel_def] >>
   rpt strip_tac >> fs[]
QED

Theorem domain_big_union_subset[local]:
  !ls a.
  MEM a ls ⇒
  domain (get_live_exp a) ⊆
  domain (big_union (MAP get_live_exp ls))
Proof
  Induct>>rw[]>>fs[big_union_def,domain_union,SUBSET_UNION,SUBSET_DEF]>>
  metis_tac[]
QED

val size_tac= (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC);

Theorem apply_nummap_key_domain[local]:
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

Theorem cut_envs_lemma:
  INJ f (domain n1) UNIV ∧
  INJ f (domain n2) UNIV ∧
  cut_envs (n1,n2) sloc = SOME (x1,x2) ∧
  strong_locals_rel f (domain n1) sloc tloc ∧
  strong_locals_rel f (domain n2) sloc tloc
  ⇒
  ∃y1 y2.
    cut_envs (apply_nummaps_key f (n1,n2)) tloc = SOME (y1,y2) ∧
    domain y1 = IMAGE f (domain n1) ∧
    domain y2 = IMAGE f (domain n2) ∧
    strong_locals_rel f (domain n1) x1 y1 ∧
    strong_locals_rel f (domain n2) x2 y2 ∧
    INJ f (domain x1) UNIV ∧
    INJ f (domain x2) UNIV ∧
    domain x1 = domain n1 ∧
    domain x2 = domain n2
Proof
  rw[]>>
  fs[cut_envs_def,apply_nummaps_key_def,AllCaseEqs()]>>
  drule_all cut_names_lemma>>
  pop_assum mp_tac>>
  drule_all cut_names_lemma>>
  rw[]>>
  simp[]
QED

Theorem cut_env_lemma:
  INJ f (domain (FST names) ∪ domain (SND names)) UNIV ∧
  cut_env names sloc = SOME x ∧
  strong_locals_rel f (domain (FST names) ∪ domain (SND names)) sloc tloc
  ⇒
  ∃y.
    cut_env (apply_nummaps_key f names) tloc = SOME y ∧
    domain y = IMAGE f (domain x) ∧
    strong_locals_rel f (domain (FST names) ∪ domain (SND names)) x y ∧
    INJ f (domain x) UNIV ∧
    domain x = domain (FST names) ∪ domain (SND names)
Proof
  rw[]>>
  gvs[cut_env_def,AllCaseEqs()]>>
  Cases_on`names`>>gvs[]>>
  drule_at Any cut_envs_lemma>>
  disch_then (qspecl_then [`tloc`,`f`] mp_tac)>>
  impl_tac >- (
    fs[strong_locals_rel_UNION]>>
    metis_tac[INJ_less,SUBSET_UNION])>>
  rw[]>>simp[domain_union]>>
  fs[AC UNION_COMM UNION_ASSOC] >>
  fs[strong_locals_rel_def]>>
  ntac 2 strip_tac>>
  DISCH_THEN (assume_tac o CONJUNCT2)>>
  fs[lookup_union,AllCaseEqs()]
  >- (
    `n ∈ domain q ∧ n ∉ domain r` by (
      fs[domain_lookup,EXTENSION]>>
      metis_tac[option_CLAUSES])>>
    `(f n) ∉ domain y2` by (
      fs[]>>
      CCONTR_TAC>>fs[INJ_DEF]>>
      metis_tac[])>>
    fs[domain_lookup]>>
    metis_tac[option_CLAUSES])>>
  DISJ2_TAC>>
  first_x_assum irule>>
  metis_tac[option_CLAUSES,domain_lookup]
QED

Theorem nummaps_to_nummap[local]:
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

Theorem LENGTH_list_rerrange[local]:
  LENGTH (list_rearrange mover xs) = LENGTH xs
Proof
  full_simp_tac(srw_ss())[list_rearrange_def]>>
  IF_CASES_TAC>>full_simp_tac(srw_ss())[]
QED

(*For any 2 lists that are permutations of each other,
  We can give a list_rearranger that permutes one to the other*)
Theorem list_rearrange_perm[local]:
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

Theorem GENLIST_MAP[local]:
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

Theorem env_to_list_perm[local]:
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
  qabbrev_tac `xls = sort key_val_compare (toAList x)`>>
  qabbrev_tac `yls = sort key_val_compare (toAList y)`>>
  qabbrev_tac `ls = list_rearrange (perm 0) yls`>>
  full_simp_tac(srw_ss())[(GEN_ALL o SYM o SPEC_ALL) list_rearrange_MAP]>>
  `PERM (MAP (λx,y.f x,y) xls) yls` by
    (match_mp_tac PERM_ALL_DISTINCT >>srw_tac[][]
    >-
      (match_mp_tac ALL_DISTINCT_MAP_INJ>>srw_tac[][]
      >-
        (full_simp_tac(srw_ss())[INJ_DEF,Abbr`xls`,sort_MEM]>>
        Cases_on`x'`>>Cases_on`y'`>>full_simp_tac(srw_ss())[]>>
        imp_res_tac MEM_toAList>>
        full_simp_tac(srw_ss())[domain_lookup])
      >>
      full_simp_tac(srw_ss())[Abbr`xls`]>>
      metis_tac[sort_PERM,ALL_DISTINCT_MAP_FST_toAList
               ,ALL_DISTINCT_FST,ALL_DISTINCT_PERM])
    >-
      metis_tac[sort_PERM,ALL_DISTINCT_MAP_FST_toAList
               ,ALL_DISTINCT_FST,ALL_DISTINCT_PERM]
    >>
      unabbrev_all_tac>>
      full_simp_tac(srw_ss())[sort_MEM,MEM_MAP]>>
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
      metis_tac[sort_PERM,ALL_DISTINCT_MAP_FST_toAList
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
  domain y' = IMAGE f (domain x') ∧
  INJ f (domain x') UNIV ∧
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
  s_val_eq (push_env (x',x) b (st with permute:=perm)).stack
           (push_env (y',y) b' cst).stack
Proof
  srw_tac[][]>>Cases_on`b`>>
  TRY(PairCases_on`x''`>> Cases_on`b'`>>full_simp_tac(srw_ss())[]>>PairCases_on`x''`>>full_simp_tac(srw_ss())[])>>
  (fs[push_env_def]>>
  qspecl_then [`y`] drule_all env_to_list_perm >>
  disch_then (qspecl_then[`cst.permute`,`tperm`]assume_tac)>>full_simp_tac(srw_ss())[LET_THM]>>
  Cases_on`env_to_list y cst.permute`>>
  fs[]>>
  qexists_tac`perm'`>>
  Cases_on`env_to_list x perm'`>>
  fs[env_to_list_def,LET_THM]>> rveq >>
  fs[s_val_eq_def,s_val_eq_refl]>>
  CONJ_TAC>-(
    simp[mem_list_rearrange,MEM_MAP,sort_MEM] >>
    simp[EXISTS_PROD,MEM_toAList,GSYM domain_lookup] >>
    metis_tac[INJ_DEF]) >>
  fs[s_frame_val_eq_def]>>
  qpat_abbrev_tac `q = list_rearrange A
    (sort key_val_compare (toAList x))`>>
  `MAP SND (MAP (λx,y.f x,y) q) = MAP SND q` by
    (simp_tac(srw_ss()++ETA_ss)[MAP_MAP_o,ELIM_UNCURRY,o_ABS_R]) >>
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

(* Convenient rewrite for pop_env
  TODO: do we need more on lsz'?
*)
Theorem s_key_eq_val_eq_pop_env:
  pop_env s = SOME s' ∧
  s_key_eq s.stack ((StackFrame n lsz ls opt)::keys) ∧
  s_val_eq s.stack vals
  ⇒
  ∃lsz' ls' rest.
  vals = StackFrame n lsz' ls' opt :: rest ∧
  s'.locals =
    union (fromAList (ZIP (MAP FST ls,MAP SND ls'))) (fromAList lsz) ∧
  s_key_eq s'.stack keys ∧
  s_val_eq s'.stack rest ∧
  case opt of NONE => s'.handler = s.handler
            | SOME (h,l1,l2) => s'.handler = h
Proof
  strip_tac>>
  gvs[pop_env_def,AllCaseEqs()]>>
  Cases_on`vals`>>
  fs[s_val_eq_def,s_key_eq_def]>>
  gvs[oneline s_frame_key_eq_def,AllCasePreds(),oneline s_frame_val_eq_def]>>
  metis_tac[ZIP_MAP_FST_SND_EQ]
QED

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

Theorem ALOOKUP_key_remap_INJ:
  INJ f (n INSERT set ls) UNIV ∧
  LENGTH ls = LENGTH vals ⇒
  ALOOKUP (ZIP (ls,vals)) n =
  ALOOKUP (ZIP (MAP f ls,vals)) (f n)
Proof
  rw[]>>
  Cases_on`ALOOKUP (ZIP (ls,vals)) n`
  >- (
    gvs[ALOOKUP_NONE,MEM_MAP,FORALL_PROD]>>
    CCONTR_TAC>>gvs[MEM_ZIP,EL_MAP]>>
    gvs[INJ_DEF]>>
    metis_tac[MEM_EL])>>
  match_mp_tac EQ_SYM>>
  irule ALOOKUP_key_remap_2>>
  gvs[INJ_DEF]
QED

val lookup_alist_insert = sptreeTheory.lookup_alist_insert |> INST_TYPE [alpha|->``:'a word_loc``]

Theorem strong_locals_rel_subset[local]:
  s ⊆ s' ∧
  strong_locals_rel f s' stl cstl
  ⇒
  strong_locals_rel f s stl cstl
Proof
  srw_tac[][strong_locals_rel_def]>>
  metis_tac[SUBSET_DEF]
QED

Theorem env_to_list_keys[local]:
  let (l,permute) = env_to_list x perm in
  set (MAP FST l) = domain x
Proof
  full_simp_tac(srw_ss())[LET_THM,env_to_list_def,EXTENSION,MEM_MAP,EXISTS_PROD]>>
  srw_tac[][EQ_IMP_THM]
  >-
    (imp_res_tac mem_list_rearrange>>
    full_simp_tac(srw_ss())[sort_MEM,MEM_toAList,domain_lookup])
  >>
    full_simp_tac(srw_ss())[mem_list_rearrange,sort_MEM,MEM_toAList,domain_lookup]
QED

Theorem list_rearrange_keys:
  list_rearrange perm (ls:('a,'b) alist) = e ⇒
  set(MAP FST e) = set(MAP FST ls)
Proof
  rw[]>>fs[EXTENSION]>>
  metis_tac[MEM_toAList,mem_list_rearrange,MEM_MAP]
QED

Theorem list_rearrange_keys_2:
  set(MAP FST (list_rearrange perm (ls:('a,'b) alist))) = set(MAP FST ls)
Proof
  metis_tac[list_rearrange_keys]
QED

Theorem MAP_FST_list_rearrange_keys_SORT:
  set(MAP FST (list_rearrange perm
    (sort key_val_compare (toAList x)))) = domain x
Proof
  simp[list_rearrange_keys_2]>>
  simp[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList,EXISTS_PROD,domain_lookup]
QED

Theorem MAP_FST_keys_SORT[local]:
  set(MAP FST (sort f (toAList x))) = domain x
Proof
  simp[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList,EXISTS_PROD,domain_lookup]
QED

Theorem pop_env_frame:
  s_val_eq r'.stack st' ∧
  s_key_eq y'.stack y''.stack ∧
  pop_env (r' with stack:= st') = SOME y'' ∧
  pop_env r' = SOME y' ⇒
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

Theorem apply_colour_exp_lemma[local]:
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
  >> namedCases_on ‘word_exp st w’ ["", "x"] >> fs []
  >> Cases_on ‘x’ >> fs []
  >> namedCases_on ‘word_exp st w'’ ["", "x"] >> fs []
  >> Cases_on ‘x’ >> fs []
  >> ntac 2 $ last_x_assum $ qspecl_then [‘cst’, ‘f’] assume_tac >> gvs []
  >> ntac 2 $ pop_assum $ DEP_REWRITE_TAC o single >> fs []
  >> rpt strip_tac >> fs [] >> first_assum irule >> fs [domain_union]
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

Theorem LASTN_LENGTH2[local]:
  LASTN (LENGTH xs +1) (x::xs) = x::xs
Proof
  `LENGTH (x::xs) = LENGTH xs +1` by simp[]>>
  metis_tac[LASTN_LENGTH_ID]
QED

Theorem toAList_not_empty[local]:
  domain t ≠ {} ⇒
  toAList t ≠ []
Proof
  CCONTR_TAC>>full_simp_tac(srw_ss())[GSYM MEMBER_NOT_EMPTY]>>
  full_simp_tac(srw_ss())[GSYM toAList_domain]
QED

Theorem PAIR_CASE_PAIR_MAP:
  pair_CASE ((f ## g) e) h = (case e of (x,y) => h (f x) (g y))
Proof
 Cases_on `e` >> simp[]
QED

Theorem permute_swap_lemma4:
   (!st'. evaluate (prog,st) = (SOME Error,st') ==>
   P (SOME Error,st')) /\ (?perm. P ((I ## (\s . s with permute := perm)) (evaluate (prog,st)))) ==>
   (?perm. P (evaluate (prog,st with permute := perm)))
Proof
   strip_tac >>
   qspecl_then [`prog`,`st`,`perm`] mp_tac permute_swap_lemma >>
   LET_ELIM_TAC >>
   Cases_on `res = SOME Error` >> fs[]
   >-(
     Q.EXISTS_TAC `st.permute` >>
     `st with permute := st.permute = st` by simp[state_component_equality] >>
     pop_assum SUBST_ALL_TAC >>
     simp[])
   >- metis_tac[]
QED

Theorem MEM_ZIP_weak:
  LENGTH l1 = LENGTH l2 ∧
  MEM (x1,x2) (ZIP(l1,l2)) ⇒
  MEM x1 l1 ∧ MEM x2 l2
Proof
  strip_tac>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[MEM_ZIP]>>
  rw[]>>gvs[MEM_EL]>>
  metis_tac[]
QED

Theorem strong_locals_rel_set_vars_dom:
  LENGTH ns = LENGTH ls ∧
  INJ f X UNIV ∧
  domain s.locals ⊆ X ∧
  set ns ⊆ X ∧
  strong_locals_rel f d s.locals t.locals ⇒
  strong_locals_rel f d (set_vars ns ls s).locals (set_vars (MAP f ns) ls t).locals
Proof
  rw[strong_locals_rel_def,set_vars_def,lookup_alist_insert]>>
  gvs[AllCaseEqs()]
  >- (
    DISJ1_TAC>>
    CCONTR_TAC>>
    gvs[ALOOKUP_NONE,MEM_MAP,MEM_ZIP,PULL_FORALL,EL_MAP]>>
    gvs[INJ_DEF]>>
    last_x_assum (drule_at Any)>>
    impl_tac>-
      gvs[SUBSET_DEF,EL_MEM,domain_lookup]>>
    metis_tac[])>>
  DISJ2_TAC>>
  irule ALOOKUP_key_remap_2>>
  simp[]>>
  rw[]>>gvs[INJ_DEF]>>
  first_x_assum irule>>
  gvs[SUBSET_DEF]
QED

Theorem s_key_eq_push_env_imp_MAP_FST:
  s_key_eq
    (push_env (x',x'') o0 s).stack
    (StackFrame n' bb l opt::ls) ∧
  env_to_list x'' s.permute = (ll,res) ⇒
  MAP FST ll = MAP FST l ∧
  set (MAP FST bb) = domain x'
Proof
  rw[oneline push_env_def]>>
  every_case_tac>>
  gvs[s_key_eq_def,oneline s_frame_key_eq_def,AllCasePreds()]>>
  simp[EXTENSION,domain_lookup,MEM_MAP,EXISTS_PROD,MEM_toAList]
QED

Theorem strong_locals_rel_set_var_dom:
  INJ f X UNIV ∧
  domain s.locals ⊆ X ∧
  n ∈ X ∧
  strong_locals_rel f d s.locals t.locals ⇒
  strong_locals_rel f d (set_var n l s).locals (set_var (f n) l t).locals
Proof
  rw[strong_locals_rel_def,set_var_def,lookup_insert]>>
  gvs[AllCaseEqs()]>>rw[]>>
  gvs[INJ_DEF]>>
  last_x_assum (drule_at Any)>>
  impl_tac>-
    gvs[SUBSET_DEF,EL_MEM,domain_lookup]>>
  metis_tac[]
QED

Theorem strong_locals_rel_extend_aux[local]:
  domain src ⊆ s ∧
  strong_locals_rel f s src tgt ⇒
  strong_locals_rel f t src tgt
Proof
  rw[strong_locals_rel_def,SUBSET_DEF]>>
  metis_tac[domain_lookup]
QED

Theorem evaluate_apply_colour_Loop_helper[local]:
  ∀(st:('a,'c,'ffi) wordSem$state) cst f names body exit_names live lt.
    colouring_ok f (Loop names body exit_names) live lt ∧
    word_state_eq_rel st cst ∧
    strong_locals_rel f
      (domain (get_live (Loop names body exit_names) live lt))
      st.locals cst.locals ∧
    (∀(st:('a,'c,'ffi) wordSem$state) cst f live lt.
       colouring_ok f body live lt ∧
       word_state_eq_rel st cst ∧
       strong_locals_rel f (domain (get_live body live lt))
         st.locals cst.locals ⇒
       ∃perm'.
         (let (res,rst) = evaluate (body,st with permute := perm') in
            res = SOME Error ∨
            let (res',rcst) = evaluate (apply_colour f body,cst) in
              res = res' ∧ word_state_eq_rel rst rcst ∧
              case res of
                NONE =>
                  strong_locals_rel f (domain live) rst.locals rcst.locals
              | SOME (Break n) =>
                  (case oEL n lt of
                   | SOME (_,exit_names) =>
                       strong_locals_rel f (domain exit_names)
                         rst.locals rcst.locals
                   | NONE => T)
              | SOME (Continue n) =>
                  (case oEL n lt of
                   | SOME (names,_) =>
                       strong_locals_rel f (domain names)
                         rst.locals rcst.locals
                   | NONE => T)
              | SOME _ => rst.locals = rcst.locals))
    ⇒
    ∃perm'.
      (let (res,rst) = evaluate
                         (Loop names body exit_names,
                          st with permute := perm') in
         res = SOME Error ∨
         let (res',rcst) = evaluate
                             (apply_colour f
                                (Loop names body exit_names),cst) in
           res = res' ∧ word_state_eq_rel rst rcst ∧
           case res of
             NONE =>
               strong_locals_rel f (domain live) rst.locals rcst.locals
           | SOME (Break n) =>
               (case oEL n lt of
                | SOME (_,exit_names) =>
                    strong_locals_rel f (domain exit_names)
                      rst.locals rcst.locals
                | NONE => T)
           | SOME (Continue n) =>
               (case oEL n lt of
                | SOME (names,_) =>
                    strong_locals_rel f (domain names)
                      rst.locals rcst.locals
                | NONE => T)
           | SOME _ => rst.locals = rcst.locals)
Proof
  gen_tac>>
  completeInduct_on `st.clock`>>
  rpt strip_tac>>
  fs[get_live_def]>>
  simp[Once evaluate_def,apply_colour_def]>>
  simp[Once evaluate_def]>>
  Cases_on `cut_state (names,LN) st`
  >- (qexists_tac`cst.permute`>>simp[])>>
  simp[]>>
  fs[cut_state_def,AllCaseEqs()]>>
  drule_at (Pos (el 2)) cut_env_lemma>>
  disch_then (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  impl_tac>- (
    fs[colouring_ok_def]>>
    drule_at_then Any irule strong_locals_rel_subset>>
    simp[SUBSET_UNION])>>
  strip_tac>>
  fs[apply_nummaps_key_def,apply_nummap_key_def]>>
  gvs[sptreeTheory.toAList_def,sptreeTheory.foldi_def,sptreeTheory.fromAList_def]>>
  last_assum (qspecl_then [`st with locals := env`,`cst with locals := y`,`f`,`names`,`(names,exit_names)::lt`] mp_tac)>>
  impl_tac>- (
    fs[colouring_ok_def]>>
    fs[word_state_eq_rel_def]>>
    irule strong_locals_rel_extend_aux>>
    qexists_tac`domain names`>>
    simp[])>>
  strip_tac>>
  Cases_on `evaluate (body,st with <|locals := env; permute := perm'|>)`>>
  Cases_on `evaluate (apply_colour f body,cst with locals := y)`>>
  fs[]
  >- (qexists_tac`perm'`>>simp[])>>
  gvs[]>>
  Cases_on `q`
  >- ((* q = NONE, cont_loop fires *)
    gvs[cont_loop_def,exit_loop_def]>>
    `r.clock = r'.clock` by fs[word_state_eq_rel_def]>>
    Cases_on `r.clock = 0` >> fs[]
    >- (qexists_tac`perm'`>>gvs[flush_state_def, word_state_eq_rel_def, strong_locals_rel_def])>>
    simp[STOP_def]>>
    imp_res_tac wordSemTheory.evaluate_clock>>
    `(dec_clock r).clock < st.clock` by gvs[dec_clock_def]>>
    first_x_assum drule>>
    disch_then (qspecl_then [`dec_clock r`,`dec_clock r'`,`f`,`names`,`body`,`exit_names`,`live`,`lt`] mp_tac)>>
    impl_tac>- (
      rpt conj_tac
      >- simp[]
      >- first_assum ACCEPT_TAC
      >- fs[word_state_eq_rel_def,dec_clock_def]
      >- fs[LLOOKUP_def,dec_clock_def]
      >- first_assum ACCEPT_TAC)>>
    strip_tac>>
    Q.ISPECL_THEN [`body`,`st with <|locals:=env; permute:=perm'|>`,`perm''`]
      assume_tac permute_swap_lemma>>
    rfs[LET_THM]>>
    qexists_tac`perm'³'`>>simp[]>>
    `dec_clock (r with permute := perm'') = dec_clock r with permute := perm''` by simp[dec_clock_def]>>
    fs[STOP_def])>>
  Cases_on `x`>>fs[cont_loop_def,exit_loop_def]
  >- ((* Result *) qexists_tac`perm'`>>simp[])
  >- ((* Exception *) qexists_tac`perm'`>>simp[])
  >- ((* Break n *)
    Cases_on `n = 0` >> fs[]
    >- ((* Break 0: both sides cut on exit_names *)
      qexists_tac`perm'`>>
      gvs[LLOOKUP_def]>>
      Cases_on `cut_env (exit_names,LN) r.locals` >> fs[]>>
      drule_at (Pos (el 2)) cut_env_lemma>>
      disch_then (qspecl_then [`r'.locals`,`f`] mp_tac)>>
      impl_tac>- (
        fs[colouring_ok_def]>>
        drule_at_then Any irule strong_locals_rel_subset>>
        simp[SUBSET_UNION])>>
      strip_tac>>
      fs[apply_nummaps_key_def,apply_nummap_key_def]>>
      gvs[sptreeTheory.toAList_def,sptreeTheory.foldi_def,sptreeTheory.fromAList_def]>>
      conj_tac>- fs[word_state_eq_rel_def]>>
      fs[strong_locals_rel_def]>>
      rw[]>>
      `n ∈ domain x` by metis_tac[domain_lookup]>>
      metis_tac[])>>
    qexists_tac`perm'`>>Cases_on `n`>>gvs[LLOOKUP_def])
  >- ((* Continue n *)
    Cases_on `n = 0` >> fs[]
    >- ((* Continue 0: cont_loop fires *)
      `r.clock = r'.clock` by fs[word_state_eq_rel_def]>>
      Cases_on `r.clock = 0` >> fs[]
      >- (qexists_tac`perm'`>>gvs[flush_state_def, word_state_eq_rel_def, strong_locals_rel_def])>>
      simp[STOP_def]>>
      imp_res_tac wordSemTheory.evaluate_clock>>
      `(dec_clock r).clock < st.clock` by gvs[dec_clock_def]>>
      first_x_assum drule>>
      disch_then (qspecl_then [`dec_clock r`,`dec_clock r'`,`f`,`names`,`body`,`exit_names`,`live`,`lt`] mp_tac)>>
      impl_tac>- (
        rpt conj_tac
        >- simp[]
        >- first_assum ACCEPT_TAC
        >- fs[word_state_eq_rel_def,dec_clock_def]
        >- fs[LLOOKUP_def,dec_clock_def]
        >- first_assum ACCEPT_TAC)>>
      strip_tac>>
      Q.ISPECL_THEN [`body`,`st with <|locals:=env; permute:=perm'|>`,`perm''`]
        assume_tac permute_swap_lemma>>
      rfs[LET_THM]>>
      qexists_tac`perm'³'`>>simp[]>>
      `dec_clock (r with permute := perm'') = dec_clock r with permute := perm''` by simp[dec_clock_def]>>
      fs[STOP_def])>>
    qexists_tac`perm'`>>Cases_on `n`>>gvs[LLOOKUP_def])
  >- ((* TimeOut *) qexists_tac`perm'`>>simp[])
  >- ((* NotEnoughSpace *) qexists_tac`perm'`>>simp[])
  >- ((* FinalFFI *) qexists_tac`perm'`>>simp[])
  >- ((* Error *) qexists_tac`perm'`>>simp[])
QED

(*liveness theorem*)
Theorem evaluate_apply_colour:
  ∀prog st cst f live lt.
  colouring_ok f prog live lt ∧
  word_state_eq_rel (st:('a,'c,'ffi) wordSem$state) cst ∧
  strong_locals_rel f (domain (get_live prog live lt)) st.locals cst.locals
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
    | SOME (Break n) =>
        (case oEL n lt of
         | SOME (_, exit_names) =>
             strong_locals_rel f (domain exit_names) rst.locals rcst.locals
         | NONE => T)
    | SOME (Continue n) =>
        (case oEL n lt of
         | SOME (names, _) =>
             strong_locals_rel f (domain names) rst.locals rcst.locals
         | NONE => T)
    | SOME _ => rst.locals = rcst.locals )
Proof
  (*Induct on size of program*)
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >~[`Skip`] >- suspend "Skip"
  >~[`Move`] >- suspend "Move"
  >~[`Inst`] >- suspend "Inst"
  >~[`Assign`] >- suspend "Assign"
  >~[`Get`] >- suspend "Get"
  >~[`Set`] >- suspend "Set"
  >~[`Store`] >- suspend "Store"
  >~[`MustTerminate`] >- suspend "MustTerminate"
  >~[`Seq`] >- suspend "Seq"
  >~[`If`] >- suspend "If"
  >~[`Alloc`] >- suspend "Alloc"
  >~[`StoreConsts`] >- suspend "StoreConsts"
  >~[`Raise`] >- suspend "Raise"
  >~[`Return`] >- suspend "Return"
  >~[`Tick`] >- suspend "Tick"
  >~[`OpCurrHeap`] >- suspend "OpCurrHeap"
  >~[`LocValue`] >- suspend "LocValue"
  >~[`Install`] >- suspend "Install"
  >~[`CodeBufferWrite`] >- suspend "CodeBufferWrite"
  >~[`DataBufferWrite`] >- suspend "DataBufferWrite"
  >~[`FFI`] >- suspend "FFI"
  >~[`ShareInst`] >- suspend "ShareInst"
  >~[`Call`] >- suspend "Call"
  >~[`Loop`] >- suspend "Loop"
  >~[`Break`] >- suspend "Break"
  >~[`Continue`] >- suspend "Continue"
QED

Resume evaluate_apply_colour[Skip]:
  full_simp_tac(srw_ss()++LET_ss)[evaluate_def,get_live_def,word_state_eq_rel_def]
QED

Resume evaluate_apply_colour[Move]:
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
  full_simp_tac(srw_ss())[]
QED

Resume evaluate_apply_colour[Inst]:
  exists_tac>>
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
  rename1 ‘Shift _ _ (case r of _ => _ | _ => _)’>>
  setup_tac>>
  impl_tac>-
   (Cases_on ‘r’>>
    irule strong_locals_rel_subset>>
    first_assum $ irule_at (Pos last)>>
    full_simp_tac(srw_ss())[get_live_exp_def,big_union_def,domain_union]) >>
  Cases_on ‘r’>>
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
  fs[mem_load_32_alt]>>
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
  )
QED

Resume evaluate_apply_colour[Assign]:
  exists_tac>>exists_tac_2>>  rpt strip_tac >>
  fs[word_state_eq_rel_def,set_var_def]>>
  fs[domain_union,get_writes_def,get_writes_inst_def,GSYM INSERT_SING_UNION]>>
  irule strong_locals_rel_insert >> fs[] >>
  metis_tac[INSERT_SING_UNION,strong_locals_rel_subset,SUBSET_OF_INSERT
           ,strong_locals_rel_insert,SUBSET_UNION]
QED

Resume evaluate_apply_colour[Get]:
  exists_tac>>
  EVERY_CASE_TAC>>
  full_simp_tac(srw_ss())[colouring_ok_def,set_var_def,get_store_def,get_live_def]>>
  gvs[] >> irule strong_locals_rel_insert >> fs[] >>
  fs[domain_union,get_writes_def,get_writes_inst_def,GSYM INSERT_SING_UNION]
QED

Resume evaluate_apply_colour[Set]:
  exists_tac>>exists_tac_2>>
  srw_tac[][]>>
  rev_full_simp_tac(srw_ss())[set_store_def,word_state_eq_rel_def]>>
  metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset
           ,domain_union,SUBSET_UNION]
QED

Resume evaluate_apply_colour[Store]:
  exists_tac>>exists_tac_2>>
  srw_tac[][]>>
  rev_full_simp_tac(srw_ss())[set_store_def,word_state_eq_rel_def]>>
  Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
  imp_res_tac strong_locals_rel_get_var>>
  full_simp_tac(srw_ss())[mem_store_def]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>>
  metis_tac[SUBSET_OF_INSERT,strong_locals_rel_subset
           ,domain_union,SUBSET_UNION]
QED

Resume evaluate_apply_colour[MustTerminate]:
  first_x_assum(qspec_then`p` assume_tac)>>
  full_simp_tac(srw_ss())[colouring_ok_def,evaluate_def,LET_THM,word_state_eq_rel_def]>>
  IF_CASES_TAC>>simp[]>>
  first_x_assum(qspecl_then[
  `st with <|clock:=MustTerminate_limit (:α);termdep:=st.termdep-1|>`,
  `cst with <|clock:=MustTerminate_limit (:α);termdep:=st.termdep-1|>`,`f`,`live`,`lt`] mp_tac)>>
  impl_tac>- fs[get_live_def]>>
  strip_tac>>
  qexists_tac`perm'`>>simp[]>>
  pop_assum mp_tac >>
  ntac 2 (pairarg_tac>>full_simp_tac(srw_ss())[])>>
  IF_CASES_TAC >> fs[] >> IF_CASES_TAC >> fs[get_live_def] >>
  metis_tac[]
QED

Resume evaluate_apply_colour[Call]:
  goalStack.print_tac"Slow evaluate_apply_colour Call proof" >>
  full_simp_tac(srw_ss())[o_UNCURRY_R, C_UNCURRY_L, S_UNCURRY_R,LET_FORALL_ELIM',
  o_THM, o_ABS_R, C_ABS_L, C_THM,S_ABS_R,FORALL_UNCURRY]>>
  fs [evaluate_def,LET_THM,colouring_ok_def,get_live_def]>>
  Cases_on`get_vars l st`>>full_simp_tac(srw_ss())[]>>
  Cases_on`bad_dest_args o1 l`>- full_simp_tac(srw_ss())[bad_dest_args_def]>>
  `¬bad_dest_args o1 (MAP f l)` by full_simp_tac(srw_ss())[bad_dest_args_def]>>
  `get_vars (MAP f l) cst = SOME x` by
  (imp_res_tac strong_locals_rel_get_vars>>
  first_x_assum irule >> simp[oneline get_live_def,
  TypeBase.case_rand_of ``:'a option``,
  TypeBase.case_rand_of ``:'a # 'b``] >>
  simp[domain_numset_list_insert,domain_union] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  (rpt (TOP_CASE_TAC >> simp[]))) >> simp[] >>
  Cases_on`find_code o1 (add_ret_loc o' x) st.code st.stack_size`>>
  full_simp_tac(srw_ss())[]>>
  PairCases_on`x'`>>full_simp_tac(srw_ss())[]>>
  TOP_CASE_TAC
  >- ( (*Tail call*)
  full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
  Cases_on`o0`>> fs []>>
  qexists_tac`cst.permute`>>full_simp_tac(srw_ss())[]>>
  Cases_on`st.clock=0`>- full_simp_tac(srw_ss())[call_env_def,flush_state_def]>>
  full_simp_tac(srw_ss())[]>>
  `call_env x'0 x'2 (dec_clock cst) =
   call_env x'0 x'2 (dec_clock(st with permute:= cst.permute))` by
    rev_full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def,state_component_equality]>>
  rfs [] >>EVERY_CASE_TAC>>
  fs [])
  >>
  (*Returning calls*)
  simp[TypeBase.case_eq_of ``:'a # 'b``,PULL_EXISTS] >>
  `?n names ret_handler l1 l2. x' = (n,names,ret_handler,l1,l2)`
   by  (PairCases_on `x'` >> simp[]) >>
  pop_assum SUBST_ALL_TAC >> full_simp_tac(srw_ss())[get_live_def]>>
  qmatch_asmsub_abbrev_tac `add_ret_loc (SOME A)` >>
  qmatch_goalsub_abbrev_tac `add_ret_loc (SOME B)` >>
  `add_ret_loc (SOME B) x  = add_ret_loc (SOME A) x`
  by simp[Abbr`A`,Abbr`B`,add_ret_loc_def] >>
  fs[] >>
  MAP_EVERY Q.UNABBREV_TAC [`A`,`B`] >>
  `cst.code = st.code /\ cst.stack_size = st.stack_size` by
      full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
  fs[] >>
  Cases_on`domain (FST names) = {} ∨ ¬ALL_DISTINCT n`>>full_simp_tac(srw_ss())[]>>
  `domain (FST (apply_nummaps_key f names)) <> ∅`
  by (PURE_REWRITE_TAC[nummaps_to_nummap,apply_nummap_key_domain] >>
  simp[]) >>
  `ALL_DISTINCT (MAP f n)` by (
  irule ALL_DISTINCT_MAP_INJ >>
  gvs[colouring_ok_def]>>
  qpat_x_assum`INJ _ _ _` mp_tac>>
  rpt (pop_assum kall_tac)>>
  simp[domain_numset_list_insert,domain_union]>>
  strip_tac>> dxrule INJ_less>>
  disch_then (qspec_then `set n` mp_tac)>>
  simp[INJ_DEF])>>
  simp[] >>
  full_simp_tac(srw_ss())[cut_envs_def] >>
  Cases_on `cut_names (FST names) st.locals` >> full_simp_tac(srw_ss())[] >>
  Cases_on `cut_names (SND names) st.locals` >> full_simp_tac(srw_ss())[] >>
  imp_res_tac cut_names_lemma >>
  pop_assum kall_tac >>
  pop_assum (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  pop_assum (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  impl_tac >-
  full_simp_tac(srw_ss())[strong_locals_rel_def,domain_union]>>
  impl_tac >-
  (full_simp_tac(srw_ss())[colouring_ok_def,LET_THM,domain_union]>>
  fs[AllCasePreds()] >>
  irule INJ_less >>
  qpat_x_assum `INJ f (domain _) _` kall_tac >>
  qpat_x_assum `INJ f (_ UNION _) _` (irule_at Any) >>
  SET_TAC[]) >>
  strip_tac >>
  impl_tac >-
  full_simp_tac(srw_ss())[strong_locals_rel_def,domain_union]>>
  impl_tac >-
  (full_simp_tac(srw_ss())[colouring_ok_def,LET_THM,domain_union]>>
  fs[AllCasePreds()] >>
  irule INJ_less >>
  qpat_x_assum `INJ f (domain _) _` kall_tac >>
  qpat_x_assum `INJ f (_ UNION _) _` (irule_at Any) >>
  SET_TAC[]) >>
  strip_tac >>
  simp[nummaps_to_nummap,Excl "apply_nummap_key_def"] >>
  `cst.clock = st.clock` by
  full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
  POP_ASSUM SUBST_ALL_TAC >>
  Cases_on `st.clock = 0` >> simp[]
  >- (
  full_simp_tac(srw_ss())[call_env_def, flush_state_def,add_ret_loc_def,word_state_eq_rel_def] >>
  Cases_on `o0` >> fs [push_env_def, env_to_list_def, stack_size_def, stack_size_frame_def] >>
  PairCases_on `x'''` >> fs [] >>
  fs[push_env_def,env_to_list_def, stack_size_def, stack_size_frame_def]) >>
  qpat_abbrev_tac`f_o0=
  case o0 of NONE => NONE
  | SOME (v,prog,l1,l2) => SOME (f v,apply_colour f prog,l1,l2)`>>
  Q.ISPECL_THEN[
  `y'`,`y`,`x'`,`x''`,`dec_clock st`,
  `f`,`dec_clock cst `,`f_o0`,`o0`,`λn. cst.permute (n+1)`]
  mp_tac (GEN_ALL push_env_s_val_eq)  >>
  impl_tac >- (
  full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
  rev_full_simp_tac(srw_ss())[LET_THM,Abbr`f_o0`]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `s_val_eq st'.stack cst'.stack` >>
  qabbrev_tac `st'' = call_env x'0 x'2  st'` >>
  qabbrev_tac `cst'' = call_env x'0 x'2  cst'` >>
  `cst'' = st'' with stack := cst''.stack`
  by (UNABBREV_ALL_TAC >>
  Cases_on `o0` >> TRY (PairCases_on `x'''`) >>
  simp[call_env_def,oneline push_env_def,ELIM_UNCURRY] >>
  simp[state_component_equality,dec_clock_def,stack_size_eq] >>
  fs[word_state_eq_rel_def] >>
  Cases_on `env_to_list y cst.permute` >>
  Cases_on `env_to_list x'' perm` >>
  fs[env_to_list_def]) >>
  pop_assum $ ASSUME_NAMED_TAC "stack_swap" >>
  `s_val_eq st''.stack cst''.stack`
  by simp[Abbr`st''`,Abbr`cst''`] >>
  qrefine `\n. if n = 0 then perm 0 else perm'' (n - 1)` >>
  `!perm''. push_env (x',x'') o0
                 (dec_clock
                    (st with
                     permute :=
                       (λn. if n = 0 then perm 0 else perm'' (n − 1)))) =
  st' with permute := perm''`
   by (namedCases_on `o0` ["","HAND"] >> TRY (PairCases_on `HAND`) >>
  simp[oneline push_env_def,Abbr`st'`,env_to_list_def,dec_clock_def,SF ETA_ss]) >>
  pop_assum (simp o single) >>
  qho_match_abbrev_tac `?perm''. P (evaluate (x'1,st'' with permute := perm''))`>>
  ho_match_mp_tac permute_swap_lemma4 >>
  Q.UNABBREV_TAC `P` >>
  CONJ_TAC >- simp[] >>
  simp_tac(srw_ss())[] >>
  simp[PAIR_CASE_PAIR_MAP] >>
  namedCases_on `evaluate (x'1,st'')` ["res1 st1"] >>
  namedCases_on `res1` ["","res2"] >>
  TRY (Cases_on `res2`) >>
  asm_simp_tac(srw_ss())[]
  (*Result*)
  >- (
  Q.SPECL_THEN [`x'1`,`st''`]  mp_tac evaluate_stack_swap >>
  simp[] >> disch_then strip_assume_tac >>
  first_x_assum (qspec_then `cst''.stack` mp_tac) >>
  LABEL_X_ASSUM  "stack_swap" (SUBST_ALL_TAC o GSYM) >>
  simp[] >> disch_then strip_assume_tac >> simp[] >>
  TOP_CASE_TAC >>
  MAP_EVERY Q.UNABBREV_TAC [`cst''`,`st''`,`cst'`,`st'`] >>
  full_simp_tac(srw_ss())[] >>
  `st''' = (st1 with stack := st''').stack` by simp[] >>
  pop_assum (RULE_ASSUM_TAC o SUBS o single) >>
  EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac push_env_pop_env_s_key_eq)) >>
  rw[]>>
  gvs[domain_union,s_val_eq_def,s_key_eq_def,s_frame_val_eq_def2,s_frame_key_eq_def2]>>
  fs[domain_union,AC UNION_COMM UNION_ASSOC] >>
  (*finally using IH*)
  first_x_assum irule >>
  CONJ_TAC >- (
    full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
    gvs[AllCaseEqs(),pop_env_def])>>
  CONJ_TAC >- (
    drule_at (Pos (el 3)) pop_env_frame>>
    disch_then (drule_at (Pos (el 3)))>>
    impl_tac >- (
      fs[s_val_eq_def,s_frame_val_eq_def2]>>
      metis_tac[s_key_eq_trans,s_key_eq_sym,word_state_eq_rel_def])>>
    simp[word_state_eq_rel_def])>>
  gvs[colouring_ok_def,domain_numset_list_insert,domain_union]>>
  irule strong_locals_rel_set_vars_dom>>
  simp[]>>
  qpat_x_assum`INJ _ (_ ∪ _ ∪ set n) _` (irule_at Any)>>
  CONJ_TAC >-
    simp[SUBSET_DEF]>>
  CONJ_TAC >-(
    fs[domain_union,AC UNION_COMM UNION_ASSOC] >>
    simp[SUBSET_DEF])>>
  (* Strong locals rel *)
  fs[domain_fromAList]>>
  pairarg_tac>>gvs[]>>
  pairarg_tac>>gvs[]>>
  imp_res_tac s_key_eq_push_env_imp_MAP_FST>>
  rfs[]>>
  ntac 2 (pop_assum kall_tac)>>
  rename1`strong_locals_rel _ _ (union (fromAList ll) _) (union (fromAList lll) _)`>>
  `MAP FST lll = MAP f (MAP FST ll)` by
    metis_tac[key_map_implies]>>
  rw[strong_locals_rel_def]>>
  rename1`lookup (f nn) _`>>
  qpat_x_assum` nn ∈ domain _` kall_tac>>
  fs[AC UNION_COMM UNION_ASSOC] >>
  fs[lookup_union,lookup_fromAList]>>
  `ALOOKUP ll nn = ALOOKUP lll (f nn)` by (
    simp[Once (GSYM ZIP_MAP_FST_SND_EQ)]>>
    simp[Once (GSYM ZIP_MAP_FST_SND_EQ), SimpRHS]>>
    irule ALOOKUP_key_remap_INJ>>
    CONJ_TAC >-
      metis_tac[LENGTH_MAP]>>
    irule INJ_less>>
    last_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]>>
    gvs[AllCaseEqs()]>>
    drule ALOOKUP_MEM>>
    metis_tac[MEM_MAP,FST])>>
  fs[AllCaseEqs(),ALOOKUP_toAList]>>
  `~MEM nn (MAP FST ll)` by (
    fs[ALOOKUP_NONE]>>
    metis_tac[MEM_MAP])>>
  fs[strong_locals_rel_def]>>
  first_x_assum irule>>
  metis_tac[domain_lookup])
  (*Exception*)
  >-(
  Q.SPECL_THEN [`x'1`,`st''`]  mp_tac evaluate_stack_swap >>
  simp[] >> disch_then strip_assume_tac >>
  first_x_assum (qspec_then `cst''.stack` mp_tac) >>
  LABEL_X_ASSUM  "stack_swap" (SUBST_ALL_TAC o GSYM) >>
  simp[] >> disch_then strip_assume_tac >> simp[] >>
  drule_all s_val_eq_LASTN_exists >>
  disch_then strip_assume_tac >> fs[] >>
  Cases_on `o0`
  (*No handler*)
  >-
    (full_simp_tac(srw_ss())[Abbr`f_o0`]>>
    `e0=e0' /\ ls = ls'` by
    (unabbrev_all_tac>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def,push_env_def,env_to_list_def,LET_THM]>>
    Cases_on`st.handler < LENGTH st.stack` >> full_simp_tac(srw_ss())[]
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
    qsuff_tac `e = e'`>-metis_tac[]>>
    unabbrev_all_tac>>
    full_simp_tac(srw_ss())[word_state_eq_rel_def,push_env_def,LET_THM,env_to_list_def]>>
    `st.handler < LENGTH st.stack` by
      (CCONTR_TAC>>
      `st.handler = LENGTH st.stack` by DECIDE_TAC>>
      ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
      simp[LASTN_LENGTH2])>>
    ntac 2 (qpat_x_assum`LASTN A B = C` mp_tac)>>
    full_simp_tac(srw_ss())[LASTN_TL])>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def] >>
  metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans]) >>
  (*Handler*)
  `?n' h l1' l2'. x''' = (n',h,l1',l2')`
    by (PairCases_on `x'''` >> simp[]) >>
  POP_ASSUM SUBST_ALL_TAC >>
  full_simp_tac(srw_ss())[Abbr`f_o0`] >>
  IF_CASES_TAC >- simp[] >>
  simp[] >>
  unabbrev_all_tac>>
  full_simp_tac(srw_ss())[word_state_eq_rel_def,push_env_def,LET_THM,env_to_list_def]>>
  rpt (qpat_x_assum `LASTN A B = C` mp_tac)>>
  simp[LASTN_LENGTH_cond]>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[domain_union,domain_fromAList]>>
  imp_res_tac list_rearrange_keys>>
  `set (MAP FST lss') = domain y` by
    (qpat_x_assum`A=MAP FST lss'` (SUBST1_TAC o SYM)>>
    full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][EXISTS_PROD]>>
    simp[MEM_MAP,sort_MEM]>>srw_tac[][EQ_IMP_THM]
    >-
      (Cases_on`y''`>>
      full_simp_tac(srw_ss())[MEM_toAList]>>
      imp_res_tac domain_lookup>>
      metis_tac[])
    >>
      full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList]>>
      metis_tac[domain_lookup])>>
  `domain (SND names) = set (MAP FST lss)` by
    (qpat_x_assum `A = MAP FST lss` (SUBST1_TAC o SYM)>>
      full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList
        ,EXISTS_PROD,domain_lookup])>>
  `set (MAP FST e0) = domain x'` by
    (full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][EXISTS_PROD]>>
    simp[MEM_MAP,sort_MEM]>>srw_tac[][EQ_IMP_THM]
    >-
      (Cases_on`y''`>>
      full_simp_tac(srw_ss())[MEM_toAList]>>
      imp_res_tac domain_lookup>>
      metis_tac[])
    >>
      full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList]>>
      metis_tac[domain_lookup])>>
  `domain (FST names) = set (MAP FST e0)` by
     (full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList
        ,EXISTS_PROD,domain_lookup])>>
  `set (MAP FST e0') = IMAGE f (domain x')` by
    (full_simp_tac(srw_ss())[EXTENSION]>>srw_tac[][EXISTS_PROD]>>
    simp[MEM_MAP,sort_MEM]>>srw_tac[][EQ_IMP_THM]
    >-
      (Cases_on`y''`>>
      full_simp_tac(srw_ss())[MEM_toAList]>>
      imp_res_tac domain_lookup>>
      metis_tac[])
    >>
      full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList]>>
      metis_tac[domain_lookup])>>
  fs[domain_union,AC UNION_COMM UNION_ASSOC] >>
  (*Use IH*)
  first_x_assum irule >>
  fs[colouring_ok_def]>>
  CONJ_TAC >-
    metis_tac[s_val_and_key_eq,s_key_eq_sym,s_key_eq_trans]>>
  irule strong_locals_rel_set_var_dom>>
  qpat_assum`INJ _ (_ INSERT _) _` (irule_at Any)>>
  simp[]>>
  CONJ_TAC >-(
    fs[domain_union,AC UNION_COMM UNION_ASSOC,domain_fromAList] >>
    simp[SUBSET_DEF])>>
  (* Strong locals rel *)
  fs[domain_fromAList]>>
  rename1`strong_locals_rel _ _ (union (fromAList ll) _) (union (fromAList lll) _)`>>
  `MAP FST lll = MAP f (MAP FST ll)` by
    metis_tac[key_map_implies]>>
  rw[strong_locals_rel_def]>>
  rename1`lookup (f nn) _`>>
  qpat_x_assum` nn ∈ domain _` kall_tac>>
  fs[AC UNION_COMM UNION_ASSOC] >>
  fs[lookup_union,lookup_fromAList]>>
  `ALOOKUP ll nn = ALOOKUP lll (f nn)` by (
    simp[Once (GSYM ZIP_MAP_FST_SND_EQ)]>>
    simp[Once (GSYM ZIP_MAP_FST_SND_EQ), SimpRHS]>>
    irule ALOOKUP_key_remap_INJ>>
    CONJ_TAC >-
      metis_tac[LENGTH_MAP]>>
    irule INJ_less>>
    qpat_assum`INJ _ (_ INSERT _) _` (irule_at Any)>>
    simp[SUBSET_DEF]>>
    gvs[AllCaseEqs()]>>
    drule ALOOKUP_MEM>>
    simp[domain_union]>>
    metis_tac[MEM_MAP,FST])>>
  fs[AllCaseEqs(),ALOOKUP_toAList]>>
  `~MEM nn (MAP FST ll)` by (
    fs[ALOOKUP_NONE]>>
    metis_tac[MEM_MAP])>>
  fs[strong_locals_rel_def]>>
  first_x_assum irule>>
  metis_tac[domain_lookup])
  (*Remaining Cases*)
  >>(
  Q.SPECL_THEN [`x'1`,`st''`]  mp_tac evaluate_stack_swap >>
  simp[] >> disch_then strip_assume_tac >>
  first_x_assum (qspec_then `cst''.stack` mp_tac) >>
  LABEL_X_ASSUM  "stack_swap" (SUBST_ALL_TAC o GSYM) >>
  simp[] >> disch_then strip_assume_tac >> simp[] >>
  Q.EXISTS_TAC `st1.permute` >>
  simp[word_state_eq_rel_def])
QED

Resume evaluate_apply_colour[Seq]:
  srw_tac[][]>>fs[evaluate_def,colouring_ok_def,LET_THM,get_live_def]>>
  last_assum(qspecl_then[`p`,`st`,`cst`,`f`,`get_live p0 live lt`,`lt`]
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
  first_assum(qspecl_then[`p0`,`r`,`r'`,`f`,`live`,`lt`] mp_tac)>>
  impl_tac>- size_tac>>
  srw_tac[][]>>
  Q.ISPECL_THEN[`p`,`st with permute:=perm'`,`perm''`]
    assume_tac permute_swap_lemma>>
  rev_full_simp_tac(srw_ss())[LET_THM]>>
  qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[]
QED

Resume evaluate_apply_colour[If]:
  full_simp_tac(srw_ss())[evaluate_def,colouring_ok_def,LET_THM,get_live_def]>>
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
  >- (
    qmatch_goalsub_abbrev_tac `evaluate (w,st with permute := _)` >>
    first_assum(qspecl_then[`w`,`st`,`cst`,`f`,`live`,`lt`] mp_tac)>>
    impl_tac>- size_tac>>
    impl_tac>-
      (Cases_on`r`>>
      full_simp_tac(srw_ss())[domain_insert,domain_union]>>
      metis_tac[SUBSET_OF_INSERT,SUBSET_UNION,strong_locals_rel_subset])>>
    srw_tac[][])
  >- (
    qmatch_goalsub_abbrev_tac `evaluate (w,st with permute := _)` >>
    first_assum(qspecl_then[`w`,`st`,`cst`,`f`,`live`,`lt`] mp_tac)>>
    impl_tac>- size_tac>>
    impl_tac>-
      (Cases_on`r`>>
      full_simp_tac(srw_ss())[domain_insert,domain_union]>>
      metis_tac[SUBSET_OF_INSERT,SUBSET_UNION,strong_locals_rel_subset])>>
    srw_tac[][])
  >- simp [word_cmp_def]
  >- (TOP_CASE_TAC >> gvs [])
  >- (TOP_CASE_TAC >> gvs [])
  >- (
    Cases_on `c` >> simp [word_cmp_def] >>
    rpt (IF_CASES_TAC >> gvs []) >>
    pairarg_tac >> gvs [] >> (
      qmatch_goalsub_abbrev_tac `evaluate (w,_)` >>
      first_assum(qspecl_then[`w`,`st`,`cst`,`f`,`live`,`lt`] mp_tac)>>
      impl_tac>- size_tac>>
      impl_tac>-
        (Cases_on`r`>>
        full_simp_tac(srw_ss())[domain_insert,domain_union]>>
        metis_tac[SUBSET_OF_INSERT,SUBSET_UNION,strong_locals_rel_subset])>>
      srw_tac[][]))
  >- simp [word_cmp_def]
QED

Resume evaluate_apply_colour[Loop]:
  rename1`Loop names body exit_names`>>
  irule evaluate_apply_colour_Loop_helper>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  first_assum (irule_at Any)>>
  rpt strip_tac>>
  first_x_assum irule>>
  simp[]
QED

Resume evaluate_apply_colour[Alloc]:
  last_x_assum kall_tac>>
  fs[evaluate_def,colouring_ok_def,get_live_def,get_writes_def]>>
  Cases_on`get_var n st`>>fs[]>>
  drule strong_locals_rel_get_var>>
  disch_then (drule_at Any)>>
  simp[]>> strip_tac>>
  rename1`get_var _ _ = SOME x`>>
  Cases_on`x`>>fs[alloc_def]>>
  rename1`cut_envs p`>>
  Cases_on`cut_envs p st.locals`>>
  fs[]>>
  rename1`cut_envs p _ = SOME x`>>
  PairCases_on`p`>>
  PairCases_on`x`>>
  drule_at (Pos (el 3)) cut_envs_lemma>>
  disch_then (qspecl_then [`cst.locals`, `f`] mp_tac)>>
  impl_tac >- (
    gvs[domain_union]>>
    irule_at Any INJ_less>>
    last_assum (irule_at Any)>>
    irule_at Any INJ_less>>
    last_x_assum (irule_at Any)>>
    irule_at Any strong_locals_rel_subset>>
    last_assum (irule_at Any)>>
    irule_at Any strong_locals_rel_subset>>
    last_x_assum (irule_at Any)>>
    simp[SUBSET_DEF])>>
  rw[]>>simp[]>>
  fs[set_store_def]>>
  qpat_abbrev_tac`non = NONE`>>
  Q.ISPECL_THEN [`y1`,`y2`,`x0`,`x1`,`st with store:= st.store |+ (AllocSize,Word c)`,
    `f`,`cst with store:= cst.store |+ (AllocSize,Word c)`,`non`,`non`,`cst.permute`] mp_tac (GEN_ALL push_env_s_val_eq)>>
  impl_tac >- (
    simp[Abbr`non`]>>
    fs[word_state_eq_rel_def])>>
  rw[]>>
  qexists_tac`perm`>>fs[Abbr`non`]>>
  qpat_abbrev_tac `st' = push_env (x0,x1) NONE A`>>
  qpat_abbrev_tac `cst' = push_env (y1,y2) NONE B`>>
  Cases_on`gc st'`>>full_simp_tac(srw_ss())[]>>
  rename1`gc st' = SOME x`>>
  Q.ISPECL_THEN [`st'`,`cst'`,`x`] mp_tac gc_s_val_eq_gen>>
  impl_keep_tac>- (
    unabbrev_all_tac>>
    full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,word_state_eq_rel_def, stack_size_def, stack_size_frame_def]>>
    rev_full_simp_tac(srw_ss())[]) >>
  srw_tac[][]>>simp[]>>
  unabbrev_all_tac>>
  imp_res_tac gc_frame>>
  drule push_env_pop_env_s_key_eq>>
  strip_tac>>
  rename1`pop_env ctt = SOME cxx`>>
  simp[]>>
  rename1`pop_env tt`>>
  Cases_on`pop_env tt`>>fs[]>>
  rename1`pop_env tt = SOME xx`>>
  `strong_locals_rel f (domain live) xx.locals cxx.locals ∧
   word_state_eq_rel xx cxx` by (
    imp_res_tac gc_s_key_eq>>
    fs[push_env_def,env_to_list_def]>>
    ntac 2(pop_assum mp_tac>>simp[Once s_key_eq_sym])>>
    ntac 2 strip_tac>>
    rpt (qpat_x_assum `s_key_eq A B` mp_tac)>>
    qpat_abbrev_tac `lsA = list_rearrange (cst.permute 0)
      (sort key_val_compare ( (toAList y2)))`>>
    qpat_abbrev_tac `lsB = list_rearrange (perm 0)
      (sort key_val_compare ( (toAList x1)))`>>
    ntac 4 strip_tac>>
    Q.ISPECL_THEN [`tt.stack`,`cxx`,`ctt`,`NONE:(num#num#num) option`,
       `st.locals_size`, `(toAList y1)`,`lsA`,`cst.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
    impl_tac
    >- (
      fs[word_state_eq_rel_def]>>
      metis_tac[s_key_eq_sym,s_val_eq_sym])>>
    Q.ISPECL_THEN [`ctt.stack`,`xx`,`tt`,`NONE:(num#num#num) option`
      ,`st.locals_size`,`toAList x0`, `lsB`,`st.stack`] mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
    impl_tac
    >- (
      fs[word_state_eq_rel_def]>>
      metis_tac[s_key_eq_sym,s_val_eq_sym])>>
    rw[]
    >-(
      (* Strong locals rel *)
      fs[strong_locals_rel_def,lookup_union,lookup_fromAList]>>
      rw[]>>
      rename1`nn ∈ domain live`>>
      qpat_x_assum` nn ∈ domain live` kall_tac>>
      `MAP FST l = MAP f (MAP FST lsB)` by
        fs[s_key_eq_def,s_frame_key_eq_def,MAP_EQ_f,MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
      `LENGTH (MAP FST lsB) = LENGTH (MAP SND l)` by
        metis_tac[LENGTH_MAP]>>
      `nn ∈ domain (union p0 p1)` by (
        fs[AllCaseEqs()]>>drule ALOOKUP_MEM>>
        simp[MEM_toAList,domain_union]
        >- metis_tac[domain_lookup]>>
        strip_tac>> drule_at Any MEM_ZIP_weak>>
        simp[Abbr`lsB`,MAP_FST_list_rearrange_keys_SORT])>>
      `ALOOKUP (ZIP (MAP FST lsB,MAP SND l)) nn =
        ALOOKUP l (f nn)` by (
        simp[Once (GSYM ZIP_MAP_FST_SND_EQ), SimpRHS]>>
        irule ALOOKUP_key_remap_INJ>>
        simp[Abbr`lsB`,MAP_FST_list_rearrange_keys_SORT]>>
        irule INJ_less>>
        last_x_assum (irule_at Any)>>
        simp[domain_union,SUBSET_DEF])>>
      fs[AllCaseEqs(),ALOOKUP_toAList]>>
      `~MEM nn (MAP FST lsB)` by (
        fs[ALOOKUP_NONE]>>
        metis_tac[MEM_MAP])>>
      pop_assum mp_tac>>
      simp[Abbr`lsB`,MAP_FST_list_rearrange_keys_SORT]>>
      strip_tac>>
      first_x_assum irule>>
      fs[domain_union])>>
    fs[word_state_eq_rel_def,pop_env_def]>>
    rfs[state_component_equality]>>
    metis_tac[s_val_and_key_eq,s_key_eq_sym,s_val_eq_sym,s_key_eq_trans])>>
  pop_assum mp_tac>>
  simp[Once word_state_eq_rel_def]>>
  strip_tac>>
  pairarg_tac>>simp[]>>
  pairarg_tac>>simp[]>>
  pop_assum mp_tac>>
  simp[AllCaseEqs()]>>
  strip_tac>>
  gvs[get_store_def,has_space_def,AllCaseEqs()]>>
  simp[word_state_eq_rel_def,flush_state_def]
QED

Resume evaluate_apply_colour[StoreConsts]:
  exists_tac>>
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
    simp[]
QED

Resume evaluate_apply_colour[Raise]:
  exists_tac>>
  Cases_on`get_var n st`>> fs[]>>
  imp_res_tac strong_locals_rel_get_var>>full_simp_tac(srw_ss())[jump_exc_def]>>
  EVERY_CASE_TAC>>full_simp_tac(srw_ss())[] >> gvs[]
QED

Resume evaluate_apply_colour[Return]:
  exists_tac>>
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
  full_simp_tac(srw_ss())[]
QED

Resume evaluate_apply_colour[Break]:
  exists_tac>>
  TOP_CASE_TAC>>
  PairCases_on`x`>>fs[]
QED

Resume evaluate_apply_colour[Continue]:
  exists_tac>>
  TOP_CASE_TAC>>
  PairCases_on`x`>>fs[]
QED

Resume evaluate_apply_colour[Tick]:
  exists_tac>>IF_CASES_TAC>>full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def]
QED

Resume evaluate_apply_colour[OpCurrHeap]:
  exists_tac>>
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
           ,strong_locals_rel_insert,SUBSET_UNION]
QED

Resume evaluate_apply_colour[LocValue]:
  exists_tac>>fs[set_var_def,strong_locals_rel_def]>>rw[]>>
  fs[lookup_insert]>>
  Cases_on`n'=n`>>fs[]>>
  `f n ≠ f n'` by
  (fs[get_writes_def]>>
  FULL_SIMP_TAC bool_ss [INJ_DEF,domain_union,domain_insert]>>
  first_x_assum(qspecl_then[`n`,`n'`] assume_tac)>>
  ntac 4 (pop_assum mp_tac)>>
  rpt (pop_assum kall_tac)>>
  simp[])>>
  fs[]
QED

Resume evaluate_apply_colour[Install]:
  exists_tac>>
  pairarg_tac>>fs[case_eq_thms]>>
  pop_assum mp_tac>>pairarg_tac>>strip_tac>>
  rfs[case_eq_thms]>>rw[]>>
  drule_at Any cut_env_lemma >>
  disch_then (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  impl_tac >- (
    CONJ_TAC >- (
      irule (GEN_ALL INJ_less)>>
      last_x_assum (irule_at Any)>>
      simp[SUBSET_DEF,domain_list_insert,domain_union])>>
    fs[list_insert_def,strong_locals_rel_def,domain_union]>>
    metis_tac[])>>
  strip_tac>>fs[]>>
  imp_res_tac strong_locals_rel_get_var>>
  fs[list_insert_def]>>
  fs[strong_locals_rel_def,lookup_insert]>>rw[]
  >-
    (qpat_x_assum`INJ _ _ _` kall_tac>>
    qpat_x_assum`INJ _ _ _` mp_tac>>
    simp[get_writes_def,domain_union]>>
    SIMP_TAC bool_ss [INJ_DEF]>>
    strip_tac>>
    first_x_assum(qspecl_then [`n'`,`n`] assume_tac)>>full_simp_tac(srw_ss())[])
  >>
    first_x_assum irule>>
    fs[EXTENSION]>>
    metis_tac[domain_lookup]
QED

Resume evaluate_apply_colour[CodeBufferWrite]:
  exists_tac>>pairarg_tac>>fs[case_eq_thms]>>
  imp_res_tac strong_locals_rel_get_var>>fs[list_insert_def]>>
  rw[]>>fs[]>>
  match_mp_tac (GEN_ALL strong_locals_rel_subset|>SIMP_RULE std_ss[Once CONJ_COMM])>>
  asm_exists_tac>>
  fs[SUBSET_DEF]
QED

Resume evaluate_apply_colour[DataBufferWrite]:
  exists_tac>>pairarg_tac>>fs[case_eq_thms]>>
  imp_res_tac strong_locals_rel_get_var>>fs[list_insert_def]>>
  rw[]>>fs[]>>
  match_mp_tac (GEN_ALL strong_locals_rel_subset|>SIMP_RULE std_ss[Once CONJ_COMM])>>
  asm_exists_tac>>
  fs[SUBSET_DEF]
QED

Resume evaluate_apply_colour[FFI]:
  exists_tac>>
  pairarg_tac>>pop_assum mp_tac>>
  gvs[]>>
  simp[Ntimes case_eq_thms 9]>>rw[]>>
  imp_res_tac strong_locals_rel_get_var>>
  simp[]>>
  drule_at Any cut_env_lemma >>
  disch_then (qspecl_then [`cst.locals`,`f`] mp_tac)>>
  impl_tac >- (
    CONJ_TAC >- (
      irule (GEN_ALL INJ_less)>>
      last_x_assum (irule_at Any)>>
      simp[domain_union,SUBSET_DEF])>>
    fs[strong_locals_rel_def,domain_union]>>
    metis_tac[])>>
  rw[]>>simp[]>>
  gvs[AllCaseEqs()]>>
  fs[strong_locals_rel_def]>>
  rw[]>>simp[call_env_def,flush_state_def]>>
  first_x_assum irule>>
  fs[EXTENSION]>>
  metis_tac[domain_lookup]
QED

Resume evaluate_apply_colour[ShareInst]:
  exists_tac>>
  pairarg_tac>>
  gvs[AllCaseEqs()]>>
  drule apply_colour_exp_lemma >>
  disch_then $ qspecl_then [`cst`,`f`] mp_tac >>
  rename1`m = Store \/ m = Store8 \/ m = Store16 \/ m = Store32`>>
  qabbrev_tac `mcase = (m = Store \/ m = Store8 \/ m = Store16 \/ m = Store32)`>>
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
    oneline sh_mem_store16_def,
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
    oneline sh_mem_load16_def,
    oneline sh_mem_set_var_def,
    flush_state_def,set_var_def,
    markerTheory.Abbrev_def,AllCaseEqs()] >>
  irule strong_locals_rel_insert >>
  fs[domain_union] >>
  (conj_tac >- (
    drule_then irule INJ_SUBSET >>
    simp[get_writes_def])) >>
  drule_at_then (Pos last) irule strong_locals_rel_subset >>
  metis_tac[SUBSET_UNION])
QED

Finalise evaluate_apply_colour;

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
Theorem get_clash_sets_hd[local]:
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

Theorem every_var_exp_get_live_exp[local]:
  ∀exp.
  every_var_exp (λx. x ∈ domain (get_live_exp exp)) exp
Proof
  ho_match_mp_tac get_live_exp_ind>>
  srw_tac[][]>>full_simp_tac(srw_ss())[get_live_exp_def,every_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>res_tac>>
  match_mp_tac every_var_exp_mono>>
  first_assum $ irule_at (Pos last)>>
  full_simp_tac(srw_ss())[domain_union]>>
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

Theorem wf_insert_swap[local]:
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
Theorem numset_list_insert_swap[local]:
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

Theorem domain_insert_eq_union[local]:
  domain (insert num () live) = domain (union (insert num () LN) live)
Proof
  fs[domain_union,domain_insert,UNION_COMM,EXTENSION]>>
  metis_tac[]
QED

Theorem domain_numset_list_insert_eq_union[local]:
  domain (numset_list_insert ls live) = domain (union (numset_list_insert ls LN) live)
Proof
  fs[domain_union,domain_numset_list_insert,UNION_COMM]
QED

Theorem get_reads_exp_get_live_exp[local]:
  ∀exp.
  set(get_reads_exp exp) = domain (get_live_exp exp)
Proof
  ho_match_mp_tac get_reads_exp_ind>>
  fs[get_reads_exp_def,get_live_exp_def]>>
  rw[EXTENSION]>>
  fs[MEM_FLAT,MEM_MAP]>>rw[EQ_IMP_THM]>>
  res_tac>>fs[]>>
  imp_res_tac domain_big_union_subset>>
  fs[SUBSET_DEF,domain_union]>>
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

Theorem lookup_numset_list_insert[local]:
  ∀ls n t.
  lookup n (numset_list_insert ls t) =
  if MEM n ls then SOME () else lookup n t
Proof
  Induct>>fs[numset_list_insert_def,lookup_insert]>>rw[]>>
  fs[]
QED

Theorem numset_list_insert_eq_UNION[local]:
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

Theorem wf_delete_swap[local]:
  wf t ⇒
  delete a (delete c t) =
  delete c (delete a t)
Proof
  rw[]>>
  dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]>>
  fs[wf_delete,lookup_delete]>>
  rw[]
QED

Theorem numset_list_delete_swap[local]:
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

Theorem wf_numset_list_delete_eq[local]:
  ∀ls t live.
  wf t ⇒
  FOLDR delete t ls = numset_list_delete ls t
Proof
  Induct>>fs[numset_list_delete_def,numset_list_delete_swap]
QED

Theorem wf_get_live_exp[local]:
  ∀exp. wf(get_live_exp exp)
Proof
  ho_match_mp_tac get_live_exp_ind>>fs[get_live_exp_def,wf_insert,wf_def]>>
  rw[]>>
  fs[big_union_def, Req0 wf_union]>>
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
  ∀prog lt f live flive livein flivein.
  wf_cutsets prog ∧
  wf live ∧
  EVERY (λ(n,e). wf n ∧ wf e) lt ∧
  domain flive = IMAGE f (domain live) ∧
  INJ f (domain live) UNIV ∧
  check_clash_tree f (get_clash_tree prog lt) live flive = SOME (livein,flivein) ⇒
  (*very slow when this is not hidden...*)
  hide(wf livein ∧
  INJ f (domain livein) UNIV ∧
  colouring_ok f prog live lt ∧
  livein = get_live prog live lt ∧
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
      Cases_on`lookup x (get_live prog live lt)`>>fs[])>>
    fs[numset_list_insert_def,wf_insert_swap]>>
    dep_rewrite.DEP_REWRITE_TAC[spt_eq_thm]>>
    fs[wf_insert,wf_union,lookup_insert,lookup_numset_list_insert,toAList_domain,domain_lookup,lookup_difference,lookup_union]>>rw[]>>
    FULL_CASE_TAC>>fs[])
    >-
      (Cases_on`lookup n' (get_live prog' live lt)`>>fs[])
    >>
      Cases_on`lookup n (get_live prog' live lt)`>>fs[])
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
  >- ((*ShareInst Store16*)
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
  >- ((*ShareInst Load/Load8/Load16/Load32*)
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
  >- ((*Loop*) suspend "Loop")
  >- ((*Break*) suspend "Break")
  >- ((*Continue*) suspend "Continue")
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

Resume clash_tree_colouring_ok[Loop]:
  fs[wf_cutsets_def]>>
  every_case_tac>>fs[]>>
  imp_res_tac check_col_INJ>>
  rveq>>
  last_x_assum $ drule_at (Pos last)>>
  simp[]>>
  strip_tac>>
  fs[hide_def,colouring_ok_def]
QED

Resume clash_tree_colouring_ok[Break]:
  every_case_tac>>fs[check_clash_tree_def]>>
  imp_res_tac check_col_INJ>>
  rveq>>
  fs[hide_def,wf_def]>>
  fs[EVERY_EL,LLOOKUP_EQ_EL]>>
  first_x_assum drule>>
  pairarg_tac>>fs[]
QED

Resume clash_tree_colouring_ok[Continue]:
  every_case_tac>>fs[check_clash_tree_def]>>
  imp_res_tac check_col_INJ>>
  rveq>>
  fs[hide_def,wf_def]>>
  fs[EVERY_EL,LLOOKUP_EQ_EL]>>
  first_x_assum drule>>
  pairarg_tac>>fs[]
QED

Finalise clash_tree_colouring_ok;

(*Actually, it should probably be exactly 0,2,4,6...*)
Definition even_starting_locals_def:
  even_starting_locals (locs:'a word_loc num_map) ⇔
    ∀x. x ∈ domain locs ⇒ is_phy_var x
End

fun rm_let tm = tm|> SIMP_RULE std_ss [LET_THM];

Theorem get_forced_tail_split[local]:
  ∀c p ls ls'.
  get_forced c p (ls++ls') =
  get_forced c p ls ++ ls'
Proof
  ho_match_mp_tac get_forced_ind>>rw[get_forced_def]>>
  EVERY_CASE_TAC>>fs[]
QED

Theorem EVERY_get_forced[local]:
  EVERY P (get_forced c p ls) ⇔
  EVERY P (get_forced c p []) ∧ EVERY P ls
Proof
  Q.SPECL_THEN [`c`,`p`,`[]`,`ls`] assume_tac get_forced_tail_split>>
  fs[]
QED

Theorem get_forced_pairwise_distinct[local]:
  ∀c prog ls.
  EVERY (λx,y. x ≠ y) ls ⇒
  EVERY (λx,y. x ≠ y) (get_forced c prog ls)
Proof
  ho_match_mp_tac get_forced_ind>>rw[get_forced_def]>>
  EVERY_CASE_TAC>>fs[]
QED

Theorem get_forced_in_get_clash_tree[local]:
  ∀prog lt c.
  EVERY (λx,y.in_clash_tree (get_clash_tree prog lt) x ∧ in_clash_tree (get_clash_tree prog lt) y) (get_forced c prog [])
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
    ((* Loop *) fs[EVERY_MEM,FORALL_PROD]>>metis_tac[])
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
    | SOME (Break _) => T
    | SOME (Continue _) => T
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
    Q.ISPECL_THEN [`prog`,`[]:(num_set#num_set) list`,`total_colour x'`,`LN:num_set`,`LN:num_set`,`q`,`r`] mp_tac clash_tree_colouring_ok>>
    fs[wf_def,hide_def]>> rw[]>>
    Q.ISPECL_THEN[`prog`,`st`,`st`,`total_colour x'`,`LN:num_set`,`[]:(num_set#num_set) list`] mp_tac evaluate_apply_colour>>
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
    every_case_tac>>full_simp_tac(srw_ss())[])
  >>
  `EVERY (λx,y.in_clash_tree tree x ∧ in_clash_tree tree y) forced` by
    (unabbrev_all_tac>>fs[get_forced_in_get_clash_tree])>>
  drule select_reg_alloc_correct>>
  disch_then(qspecl_then [`alg`,`spillcosts`,`k`,`heu_moves`,`fs`] assume_tac)>>rfs[]>>fs[]>>
  Q.ISPECL_THEN[`prog`,`st`,`st`,`total_colour spcol`,`LN:num_set`,`[]:(num_set#num_set) list`] mp_tac evaluate_apply_colour>>
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
      disch_then(qspecl_then[`[]:(num_set#num_set) list`,`total_colour spcol`,`LN`,`LN`,`livein`,`gliveout`] assume_tac)>>
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
  every_case_tac>>fs[]
QED

Theorem apply_colour_exp_I[local]:
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
Definition live_store_rel_def:
  live_store_rel nlive sstore tstore ⇔
  ∀n.
    n ∉ set nlive ⇒
    FLOOKUP sstore n = FLOOKUP tstore n
End

Theorem live_store_rel_less:
  live_store_rel ls st tt ∧
  set ls ⊆ set ls' ⇒
  live_store_rel ls' st tt
Proof
  rw[live_store_rel_def,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem live_store_rel_FLOOKUP_store:
  live_store_rel ls sstore tstore ∧
  s ∉ set ls ⇒
  FLOOKUP tstore s = FLOOKUP sstore s
Proof
  rw[live_store_rel_def]
QED

Definition nlive_store_def:
  (nlive_store nlive
    (Op _ ls) ⇔
      EVERY (nlive_store nlive) ls) ∧
  (nlive_store nlive (Lookup s) ⇔
    s ∉ set nlive) ∧
  (nlive_store nlive (Load e) ⇔
    nlive_store nlive e) ∧
  (nlive_store nlive (Shift _ e1 e2) ⇔
    nlive_store nlive e1 ∧ nlive_store nlive e2) ∧
  (nlive_store nlive _ ⇔ T)
End

Theorem strong_locals_rel_I_get_var[local]:
  get_var x st = SOME v ∧
  strong_locals_rel I (x INSERT live) st.locals t ⇒
  get_var x (st with <|locals:=t;store:=tstore|>) = SOME v
Proof
  fs[strong_locals_rel_def,get_var_def]
QED

Theorem strong_locals_rel_I_get_var'[local]:
  get_var x st = SOME v ∧
  strong_locals_rel I (x INSERT live) st.locals t ⇒
  get_var x (st with <|locals:=t|>) = SOME v
Proof
  fs[strong_locals_rel_def,get_var_def]
QED

Theorem strong_locals_rel_I_word_exp[local]:
  ∀st exp res.
  word_exp st exp = SOME res ∧
  strong_locals_rel I
    (domain (union (get_live_exp exp) live)) st.locals t ∧
  live_store_rel nlive st.store tstore ∧
  nlive_store nlive exp
  ⇒
  word_exp (st with <| locals := t; store := tstore |>) exp = SOME res
Proof
  ho_match_mp_tac word_exp_ind>>
  rw[word_exp_def]
  >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[get_live_exp_def,domain_union]>>
    qexists_tac`{}`>>simp[])
  >- (
    gvs[get_store_def,nlive_store_def,live_store_rel_def]
  )
  >- (
    gvs[AllCaseEqs()]>>
    first_x_assum (irule_at Any)>>
    gvs[mem_load_def,nlive_store_def]>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[get_live_exp_def,domain_union])
  >- (
    gvs[AllCaseEqs()]>>
    first_x_assum (irule_at Any)>>
    imp_res_tac the_words_EVERY_IS_SOME>>
    qpat_x_assum`the_words _ = _` sym_sub_tac>>
    AP_TERM_TAC >>
    gvs[nlive_store_def]>>
    fs[MAP_EQ_f,EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
    rw[]>>
    first_x_assum drule>>
    first_x_assum drule>>
    rw[IS_SOME_EXISTS]>>gvs[]>>
    first_x_assum irule>>
    simp[]>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[get_live_exp_def,domain_union]>>
    irule SUBSET_TRANS>>
    irule_at Any domain_big_union_subset>>
    first_x_assum (irule_at Any)>>
    simp[ETA_AX])
  >- (
    gvs[AllCaseEqs(),nlive_store_def]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    gvs[]>>
    conj_tac >- (
      irule strong_locals_rel_subset>>
      first_assum (irule_at Any)>>
      simp[get_live_exp_def,domain_union]>>
      fs[SUBSET_DEF]) >>
    first_x_assum irule>>
    irule strong_locals_rel_subset>>
    first_assum (irule_at Any)>>
    simp[get_live_exp_def,domain_union]>>
    fs[SUBSET_DEF])
QED

Theorem strong_locals_rel_insert_notin[local]:
  strong_locals_rel f live s t ∧
  n ∉ live ⇒
  strong_locals_rel f live (insert n v s) t
Proof
  rw[strong_locals_rel_def,lookup_insert]>>
  Cases_on`n'=n`>>fs[]
QED

Theorem strong_locals_rel_I_get_vars'[local]:
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

Theorem strong_locals_rel_I_cut_envs[local]:
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

Theorem strong_locals_rel_I_cut_env[local]:
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

Theorem get_vars_eq[local]:
  (set ls) SUBSET domain st.locals ==> ?z. get_vars ls st = SOME z /\
                                             z = MAP (\x. THE (lookup x st.locals)) ls
Proof
  Induct_on`ls`>>full_simp_tac(srw_ss())[get_vars_def,get_var_def]>>srw_tac[][]>>
  full_simp_tac(srw_ss())[domain_lookup]
QED

Theorem get_vars_exists[local]:
  ∀ls.
  (∃z. get_vars ls st = SOME z) ⇔
  set ls ⊆ domain st.locals
Proof
  Induct>>fs[get_vars_def,get_var_def]>>rw[]>>
  EVERY_CASE_TAC>>fs[domain_lookup]
QED

Theorem strong_locals_rel_I_insert_insert[local]:
  strong_locals_rel I (live DELETE p) A B ∧
  v = v' ⇒
  strong_locals_rel I live (insert p v A) (insert p v' B)
Proof
  rw[strong_locals_rel_def,lookup_insert]>>
  IF_CASES_TAC>>fs[]
QED

Theorem st_eq[simp,local]:
  rst with <|locals := t; store := tstore|> =
  rst with <|locals := t'; store := tstore'|> ⇔
  t = t' ∧ tstore = tstore'
Proof
  rw[state_component_equality]
QED

Theorem live_store_rel_NIL[simp,local]:
  live_store_rel [] sstore tstore ⇔
  sstore = tstore
Proof
  rw[live_store_rel_def]>>
  metis_tac[fmap_eq_flookup]
QED

Theorem live_store_rel_refl[simp,local]:
  live_store_rel ls sstore sstore
Proof
  rw[live_store_rel_def]
QED

Theorem with_same_store[simp,local]:
  st with store := st.store = st
Proof
  rw[state_component_equality]
QED

Theorem with_same_locals[simp,local]:
  st with locals := st.locals = st
Proof
  rw[state_component_equality]
QED

Theorem evaluate_remove_dead_Loop_helper[local]:
  ∀(st:('a,'c,'ffi) wordSem$state) t tstore names body exit_names
    live nlive lt prog' livein nlivein res rst.
    strong_locals_rel I (domain livein) st.locals t ∧
    live_store_rel nlivein st.store tstore ∧
    evaluate (Loop names body exit_names, st) = (res,rst) ∧
    flat_exp_conventions body ∧
    remove_dead (Loop names body exit_names) live nlive lt =
      (prog',livein,nlivein) ∧
    nlivein = [] ∧
    res ≠ SOME Error ∧
    (∀(st':('a,'c,'ffi) wordSem$state) t' tstore' prog'' livein' nlivein' res' rst'.
       strong_locals_rel I (domain livein') st'.locals t' ∧
       live_store_rel nlivein' st'.store tstore' ∧
       evaluate (body,st') = (res',rst') ∧
       remove_dead body names [] ((names,exit_names)::lt) =
         (prog'',livein',nlivein') ∧
       res' ≠ SOME Error ⇒
       ∃t'' tstore''.
         evaluate (prog'',st' with <|locals := t'; store := tstore'|>) =
           (res',rst' with <|locals := t''; store := tstore''|>) ∧
         (case res' of
            NONE =>
              strong_locals_rel I (domain names) rst'.locals t'' ∧
              live_store_rel [] rst'.store tstore''
          | SOME (Break n) =>
              rst'.store = tstore'' ∧
              (case oEL n ((names,exit_names)::lt) of
                 SOME (_,exit_names) =>
                   strong_locals_rel I (domain exit_names) rst'.locals t''
               | NONE => T)
          | SOME (Continue n) =>
              rst'.store = tstore'' ∧
              (case oEL n ((names,exit_names)::lt) of
                 SOME (names,_) =>
                   strong_locals_rel I (domain names) rst'.locals t''
               | NONE => T)
          | SOME _ => rst'.locals = t'' ∧ rst'.store = tstore''))
  ⇒
    ∃t' tstore'.
      evaluate (prog', st with <|locals := t; store := tstore|>) =
        (res, rst with <|locals := t'; store := tstore'|>) ∧
      (case res of
         NONE =>
           strong_locals_rel I (domain live) rst.locals t' ∧
           live_store_rel nlive rst.store tstore'
       | SOME (Break n) =>
           rst.store = tstore' ∧
           (case oEL n lt of
              SOME (_,exit_names) =>
                strong_locals_rel I (domain exit_names) rst.locals t'
            | NONE => T)
       | SOME (Continue n) =>
           rst.store = tstore' ∧
           (case oEL n lt of
              SOME (names,_) =>
                strong_locals_rel I (domain names) rst.locals t'
            | NONE => T)
       | SOME _ => rst.locals = t' ∧ rst.store = tstore')
Proof
  gen_tac>>completeInduct_on `st.clock`>>rpt strip_tac>>
  gvs[remove_dead_def,live_store_rel_NIL]>>
  pairarg_tac>>gvs[]>>
  qpat_x_assum `evaluate (Loop _ _ _, _) = _` mp_tac>>
  simp[Once evaluate_def]>>
  Cases_on `cut_state (livein,LN) st`
  >- (fs[]>>strip_tac>>gvs[])>>
  gvs[cut_state_def,AllCaseEqs()]>>
  `cut_env (livein,LN) t = SOME env` by (
    qspecl_then [`env`,`t`,`st`,`(livein,LN)`] mp_tac
      (GEN_ALL strong_locals_rel_I_cut_env)>>
    fs[domain_union])>>
  ONCE_REWRITE_TAC[evaluate_def]>>
  simp[cut_state_def]>>
  pairarg_tac>>fs[]>>
  strip_tac>>
  rename1 `remove_dead body livein [] ((livein,exit_names)::lt) =
    (body',bodylivein,bodynlivein)`>>
  qpat_assum `∀st' t' tstore' res' rst'. _` mp_tac>>
  disch_then (qspecl_then
    [`st with locals := env`,`env`,`st.store`,`res'`,`s1`] mp_tac)>>
  impl_tac>- (
    fs[live_store_rel_def]>>
    CONJ_TAC>- rw[strong_locals_rel_def]>>
    CCONTR_TAC>>gvs[])>>
  strip_tac>>
  qpat_x_assum `evaluate (body',_) = _` mp_tac>>
  `st with <|locals := env; store := st.store|> = st with locals := env` by
    simp[state_component_equality]>>
  simp[]>>
  strip_tac>>
  Cases_on `res'`>>fs[]
  >- suspend "none">>
  Cases_on `x`>>fs[]
  >- ((* Result *) gvs[])
  >- ((* Exception *) gvs[])
  >- ((* Break *) suspend "break")
  >- ((* Continue *) suspend "continue")
  >- ((* TimeOut *) gvs[])
  >- ((* NotEnoughSpace *) gvs[])
  >> ((* FinalFFI *) gvs[])
QED

Resume evaluate_remove_dead_Loop_helper[none]:
  (* NONE: cont_loop fires; s1.store = tstore'' from body-IH NONE case *)
  `tstore'' = s1.store` by fs[]>>
  gvs[]>>
  Cases_on `s1.clock = 0`>>fs[]
  >- (qexistsl_tac [`LN`,`FEMPTY`]>>
      gvs[flush_state_def,state_component_equality])>>
  simp[STOP_def]>>
  imp_res_tac wordSemTheory.evaluate_clock>>fs[]>>
  `(dec_clock s1).clock < st.clock` by fs[dec_clock_def]>>
  qpat_x_assum `∀m. _ < _ ⇒ _` drule>>
  disch_then (qspec_then `dec_clock s1` mp_tac)>>
  simp[dec_clock_def]>>
  disch_then (qspecl_then
    [`t''`,`livein`,`body`,`exit_names`,`live`,`nlive`,`lt`,
     `Loop livein body' exit_names`,`livein`,`res`,`rst`] mp_tac)>>
  impl_tac>- (
    qpat_x_assum `evaluate (STOP _,_) = _` mp_tac>>
    simp[STOP_def,dec_clock_def,remove_dead_def]>>
    strip_tac>>
    rpt (pairarg_tac>>fs[])>>
    first_x_assum ACCEPT_TAC)>>
  strip_tac>>
  first_assum (irule_at Any)>>
  fs[]
QED

Resume evaluate_remove_dead_Loop_helper[break]:
  `tstore'' = s1.store` by fs[]>>
  gvs[]>>
  IF_CASES_TAC>>fs[LLOOKUP_def]
  >- ((* Break 0: cut exit_names *)
    Cases_on `cut_env (exit_names,LN) s1.locals`>>gvs[]>>
    rename1 `cut_env _ _ = SOME exit_env`>>
    `cut_env (exit_names,LN) t'' = SOME exit_env` by (
      qspecl_then [`exit_env`,`t''`,`s1`,`(exit_names,LN)`] mp_tac
        (GEN_ALL strong_locals_rel_I_cut_env)>>
      fs[domain_union])>>
    simp[]>>
    qexistsl_tac [`exit_env`,`s1.store`]>>
    gvs[strong_locals_rel_def,state_component_equality])>>
  qexistsl_tac [`t''`,`s1.store`]>>
  gvs[state_component_equality]
QED

Resume evaluate_remove_dead_Loop_helper[continue]:
  `tstore'' = s1.store` by fs[]>>
  gvs[]>>
  IF_CASES_TAC>>fs[LLOOKUP_def]
  >- ((* Continue 0: cont_loop fires, recurse *)
    Cases_on `s1.clock = 0`>>fs[]
    >- (qexistsl_tac [`LN`,`FEMPTY`]>>
        gvs[flush_state_def,state_component_equality])>>
    simp[STOP_def]>>
    imp_res_tac wordSemTheory.evaluate_clock>>fs[]>>
    `(dec_clock s1).clock < st.clock` by fs[dec_clock_def]>>
    qpat_x_assum `∀m. _ < _ ⇒ _` drule>>
    disch_then (qspec_then `dec_clock s1` mp_tac)>>
    simp[dec_clock_def]>>
    disch_then (qspecl_then
      [`t''`,`livein`,`body`,`exit_names`,`live`,`nlive`,`lt`,
       `Loop livein body' exit_names`,`livein`,`res`,`rst`] mp_tac)>>
    impl_tac>- (
      qpat_x_assum `evaluate (STOP _,_) = _` mp_tac>>
      simp[STOP_def,dec_clock_def,remove_dead_def]>>
      strip_tac>>
      rpt (pairarg_tac>>fs[])>>
      first_x_assum ACCEPT_TAC)>>
    strip_tac>>
    first_assum (irule_at Any)>>
    fs[])>>
  qexistsl_tac [`t''`,`s1.store`]>>
  gvs[state_component_equality]
QED

Finalise evaluate_remove_dead_Loop_helper;

Theorem evaluate_remove_dead:
  ∀prog live nlive lt prog' livein nlivein st t tstore res rst.
  strong_locals_rel I (domain livein) st.locals t ∧
  live_store_rel nlivein st.store tstore ∧
  evaluate (prog,st) = (res,rst) ∧
  flat_exp_conventions prog ∧
  remove_dead prog live nlive lt = (prog',livein,nlivein) ∧
  res ≠ SOME Error ⇒
  ∃t' tstore'.
    evaluate(prog',st with <| locals := t ; store := tstore|> ) =
      (res,rst with <| locals:=t'; store := tstore' |> ) ∧
    (case res of
      NONE =>
        strong_locals_rel I (domain live) rst.locals t' ∧
        live_store_rel nlive rst.store tstore'
    | SOME (Break n) =>
        rst.store = tstore' ∧
        (case oEL n lt of
           SOME (_, exit_names) =>
             strong_locals_rel I (domain exit_names) rst.locals t'
         | NONE => T)
    | SOME (Continue n) =>
        rst.store = tstore' ∧
        (case oEL n lt of
           SOME (names, _) =>
             strong_locals_rel I (domain names) rst.locals t'
         | NONE => T)
    | SOME _ => rst.locals = t' ∧ rst.store = tstore')
Proof
  ho_match_mp_tac remove_dead_ind>>rw[]>>
  gvs[flat_exp_conventions_def]
  >~[`Move`] >- suspend "Move"
  >~[`Inst`] >- suspend "Inst"
  >~[`Get`] >- suspend "Get"
  >~[`OpCurrHeap`] >- suspend "OpCurrHeap"
  >~[`LocValue`] >- suspend "LocValue"
  >~[`Set`] >- suspend "Set"
  >~[`Seq`] >- suspend "Seq"
  >~[`MustTerminate`] >- suspend "MustTerminate"
  >~[`If`] >- suspend "If"
  >~[`Call (SOME _)`] >- suspend "CallSome"
  >~[`Call NONE`] >- suspend "CallNone"
  >~[`Loop`] >- suspend "Loop"
  >~[`Break`] >- suspend "Break"
  >~[`Continue`] >- suspend "Continue"
  >~[`Alloc`] >- suspend "Alloc"
  >~[`Raise`] >- suspend "Raise"
  >~[`Return`] >- suspend "Return"
  >~[`Skip`] >- suspend "Skip"
  >~[`StoreConsts`] >- suspend "StoreConsts"
  >~[`Tick`] >- suspend "Tick"
  >~[`Install`] >- suspend "Install"
  >~[`CodeBufferWrite`] >- suspend "CodeBufferWrite"
  >~[`DataBufferWrite`] >- suspend "DataBufferWrite"
  >~[`FFI`] >- suspend "FFI"
  >~[`ShareInst _ _ _`] >- suspend "ShareInst"
QED

Resume evaluate_remove_dead[Move]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),set_vars_def]
  >- (* empty filter case *)
    (fs[strong_locals_rel_def]>>
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
  >> (* normal case *)
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
  qpat_x_assum`A=vs` sym_sub_tac>>
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
    fs[domain_lookup]
QED

Resume evaluate_remove_dead[Inst]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),inst_def,
      remove_dead_inst_def,get_live_inst_def,assign_def,
      word_exp_def,set_var_def, PULL_EXISTS]>>
  TRY (match_mp_tac strong_locals_rel_insert_notin>>
       fs[domain_lookup]>>
       match_mp_tac strong_locals_rel_insert_notin>>
       fs[domain_lookup]>>
       NO_TAC) >>
  TRY (irule strong_locals_rel_I_insert_insert >> simp[] >> NO_TAC) >>
  TRY (
   imp_res_tac strong_locals_rel_I_get_var >>
   gvs[get_vars_def,the_words_def,CaseEq"option",CaseEq"word_loc",PULL_EXISTS] >>
   irule_at Any strong_locals_rel_I_insert_insert >> simp[] >>
   imp_res_tac strong_locals_rel_I_get_var >> gvs[] >>
   irule_at Any strong_locals_rel_subset >>
   first_x_assum (irule_at Any) >>
   simp[SUBSET_DEF] >> gvs[mem_load_def] >>
   goal_assum $ drule_at Any \\ simp[] >>
   qmatch_rename_tac`∃lv. strong_locals_rel I (_ INSERT lv) _ _`
   \\ metis_tac[INSERT_COMM] ) >>
  TRY (
    imp_res_tac strong_locals_rel_I_get_vars' >>
    gvs[get_vars_def, get_var_def, CaseEq"option", CaseEq"word_loc"] >>
    irule_at Any strong_locals_rel_I_insert_insert >> simp[] >>
    irule_at Any strong_locals_rel_I_insert_insert >> simp[] >>
    irule_at Any strong_locals_rel_subset >>
    first_assum (irule_at Any) >>
    simp[SUBSET_DEF] >>
    TRY(first_assum (irule_at Any)) >>
    rw[] >> fsrw_tac[DNF_ss][] >> gvs[] >> NO_TAC) >>
  TRY (
    imp_res_tac strong_locals_rel_I_get_var >>
    TRY pairarg_tac >>
    gvs[get_var_def, the_words_def, CaseEq"option", CaseEq"word_loc",
        mem_store_def] >>
    irule_at Any strong_locals_rel_subset >> simp[] >>
    rpt(first_assum (irule_at Any)) >>
    simp[SUBSET_DEF] >>
    metis_tac[INSERT_COMM] )
QED

Resume evaluate_remove_dead[Get]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),set_var_def]
  >-
    (match_mp_tac strong_locals_rel_insert_notin>>fs[domain_lookup])
  >>
    fs[PULL_EXISTS,get_store_def]>>
    drule live_store_rel_FLOOKUP_store>>
    disch_then (fn th => DEP_REWRITE_TAC[th])>>
    simp[MEM_FILTER]>>
    CONJ_TAC >- (
      irule strong_locals_rel_I_insert_insert>>
      fs[])>>
    irule live_store_rel_less>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF,MEM_FILTER]
QED

Resume evaluate_remove_dead[OpCurrHeap]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),set_var_def]
  >- (
    match_mp_tac strong_locals_rel_insert_notin>>
    fs[domain_lookup])>>
  drule strong_locals_rel_I_word_exp>>
  disch_then (irule_at Any)>>
  first_assum (irule_at Any)>>
  simp[nlive_store_def,MEM_FILTER,get_live_exp_def,big_union_def,domain_union]>>
  qexists_tac`(delete num live)`>>rw[]
  >- (
    irule strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF])
  >- (
    irule strong_locals_rel_I_insert_insert>>
    simp[]>>
    irule strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF])
  >- (
    irule live_store_rel_less>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF,MEM_FILTER])
QED

Resume evaluate_remove_dead[LocValue]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),set_var_def]
  >-
    (match_mp_tac strong_locals_rel_insert_notin>>fs[domain_lookup])>>
  fs[strong_locals_rel_def,lookup_insert,domain_union]>>rw[]
QED

Resume evaluate_remove_dead[Set]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),word_exp_def,set_store_def,flat_exp_conventions_def]
  >- (
    fs[live_store_rel_def,FLOOKUP_UPDATE]>>
    metis_tac[])>>
  drule_all strong_locals_rel_I_get_var>>
  simp[]>>disch_then kall_tac>>
  CONJ_TAC >- (
    irule strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF])>>
  fs[live_store_rel_def,FLOOKUP_UPDATE]
QED

Resume evaluate_remove_dead[Seq]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>fs[])>>
  gvs[]>>
  qpat_x_assum`_ = (res,rst)` mp_tac>>IF_CASES_TAC>>
  strip_tac
  >- (
    first_x_assum drule>>
    disch_then drule>> simp[]>> strip_tac>>
    first_x_assum drule>>
    disch_then drule>> simp[]>> strip_tac>>
    rw[]>>fs[evaluate_def]>>
    every_case_tac>>fs[])
  >>
    gvs[]>>first_x_assum drule>>
    disch_then drule>> simp[]>> strip_tac>>
    rw[]>>fs[evaluate_def]>>
    every_case_tac>>fs[]
QED

Resume evaluate_remove_dead[MustTerminate]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>fs[])>>
  gvs[]>>
  qpat_x_assum`A=(res,rst)` mp_tac>>
  IF_CASES_TAC>>strip_tac>>
  gvs[evaluate_def]>>
  first_x_assum (qspecl_then [`st with <|clock := MustTerminate_limit (:'a) ; termdep := st.termdep -1|>` ] mp_tac)>>
  fs[]>>
  disch_then drule_all>>
  rw[]>>fs[]
QED

Resume evaluate_remove_dead[If]:
  gvs[evaluate_def,remove_dead_def] >>
  rpt (pairarg_tac >> fs[]) >> gvs[] >>
  Cases_on `ri`
  (* Reg: resolve get_var for register operand, then apply IH *)
  >- (
    gvs[AllCaseEqs(),domain_insert,domain_union,get_var_imm_def] >>
    gvs[Once INSERT_COMM] >>
    imp_res_tac strong_locals_rel_I_get_var >> gvs[] >>
    `get_var n (st with <|locals := t; store := tstore|>) = SOME y` by (
      first_x_assum (qspecl_then [`t`,`r1 INSERT domain e2_live ∪ domain e3_live`]
        mp_tac) >>
      impl_tac >- gvs[Once INSERT_COMM] >> simp[]) >>
    first_x_assum (fn ih =>
      qspecl_then [`st`,`t`,`tstore`,`res`,`rst`] mp_tac ih >>
      impl_tac >- (
        simp[] >>
        CONJ_TAC >- (
          irule strong_locals_rel_subset >>
          first_x_assum (irule_at Any) >> simp[SUBSET_DEF]) >>
        irule live_store_rel_less >>
        first_x_assum (irule_at Any) >> gvs[SUBSET_DEF,MEM_FILTER]) >>
      strip_tac >> IF_CASES_TAC >> gvs[evaluate_def,get_var_imm_def] >>
      simp[]))
  (* Imm: apply IH directly *)
  >- (
    gvs[AllCaseEqs(),domain_insert,domain_union,get_var_imm_def] >>
    gvs[Once INSERT_COMM] >>
    imp_res_tac strong_locals_rel_I_get_var >> gvs[] >>
    first_x_assum (fn ih =>
      qspecl_then [`st`,`t`,`tstore`,`res`,`rst`] mp_tac ih >>
      impl_tac >- (
        simp[] >>
        CONJ_TAC >- (
          irule strong_locals_rel_subset >>
          first_x_assum (irule_at Any) >> simp[SUBSET_DEF]) >>
        irule live_store_rel_less >>
        first_x_assum (irule_at Any) >> gvs[SUBSET_DEF,MEM_FILTER]) >>
      strip_tac >> IF_CASES_TAC >> gvs[evaluate_def,get_var_imm_def] >>
      simp[]))
QED

Resume evaluate_remove_dead[CallSome]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs()] >>
  rpt (pairarg_tac >> fs[]) >> gvs[] >>
  rpt strip_tac >>
  `get_vars args (st with locals := t) = SOME xs` by (
    irule (GEN_ALL strong_locals_rel_I_get_vars') >>
    first_x_assum (irule_at Any) >>
    first_x_assum (irule_at Any) >>
    simp[domain_numset_list_insert,domain_union]) >>
  `cut_envs cutsets t = SOME envs` by (
    irule (GEN_ALL strong_locals_rel_I_cut_envs) >>
    first_x_assum (irule_at Any) >>
    irule strong_locals_rel_subset >>
    first_x_assum (irule_at Any) >>
    simp[domain_union,SUBSET_DEF]) >>
  `∀s. push_env envs (case h of NONE => NONE
         | SOME (n,p,a,b) =>
             SOME (n,FST (remove_dead p live nlive lt),a,b)) s =
       push_env envs h s` by
    (Cases_on `h` >> simp[push_env_def] >>
     rename1 `SOME htup` >> PairCases_on `htup` >>
     simp[push_env_def]) >>
  simp[Once evaluate_def, add_ret_loc_def] >>
  gvs[fix_clock_def, add_ret_loc_def] >>
  gvs[flush_state_def, call_env_def, dec_clock_def] >>
  Cases_on `env_to_list (SND envs) st.permute` >> gvs[]
  >- ((*Result*)
    rename1 `remove_dead _ live nlive lt = (ret_handler, ret_live)` >>
    first_x_assum (qspecl_then
      [`FST ret_live`, `SND ret_live`,
       `set_vars prog ys s1`,
       `(set_vars prog ys s1).locals`,
       `(set_vars prog ys s1).store`,
       `res`, `rst`] mp_tac) >>
    impl_tac >- simp[strong_locals_rel_def] >>
    strip_tac >> gvs[state_component_equality])
  >- ((*Exception*)
    rename1 `evaluate (handler, set_var hn _ _) = _` >>
    `push_env envs (SOME (hn,FST (remove_dead handler live nlive lt),l1',l2')) st =
     push_env envs (SOME (hn,handler,l1',l2')) st` by
      simp[push_env_def] >>
    gvs[] >>
    qpat_x_assum `∀a b c d e f g h.
      _ ∧ _ ∧ evaluate (handler,_) = _ ∧ _ ∧ _ ⇒ _`
      (qspecl_then
        [`FST (remove_dead handler live nlive lt)`,
         `FST (SND (remove_dead handler live nlive lt))`,
         `SND (SND (remove_dead handler live nlive lt))`,
         `set_var hn y s2`,
         `(set_var hn y s2).locals`,
         `(set_var hn y s2).store`,
         `res`, `rst`] mp_tac) >>
    impl_tac >- simp[strong_locals_rel_def] >>
    strip_tac >> gvs[state_component_equality])
QED

Resume evaluate_remove_dead[CallNone]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  simp[PULL_EXISTS]>>
  first_x_assum (irule_at Any)>>
  rename1 `¬bad_dest_args xss yss` >>
  imp_res_tac strong_locals_rel_I_get_vars'>>
  gvs[domain_numset_list_insert]>>
  fs[call_env_def,dec_clock_def]>>
  qexistsl [`rst.store`,`rst.locals`]>>
  simp[state_component_equality]>>
  every_case_tac>>fs[]
QED

Resume evaluate_remove_dead[Loop]:
  gvs[remove_dead_def]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  qspecl_then
    [`st`,`t`,`st.store`,`live`,`prog`,`exit_names`,`live'`,`nlive`,`lt`,
     `Loop live body' exit_names`,`live`,`[]`,`res`,`rst`]
    mp_tac evaluate_remove_dead_Loop_helper>>
  simp[remove_dead_def,flat_exp_conventions_def]
QED

Resume evaluate_remove_dead[Break]:
  gvs[evaluate_def,remove_dead_def,get_live_def]>>
  every_case_tac>>fs[]
QED

Resume evaluate_remove_dead[Continue]:
  gvs[evaluate_def,remove_dead_def,get_live_def]>>
  every_case_tac>>fs[]
QED

Resume evaluate_remove_dead[Alloc]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  imp_res_tac strong_locals_rel_I_get_var'>>fs[]>>
  gvs[alloc_def,AllCaseEqs()]>>
  simp[PULL_EXISTS]>>
  rename1 `cut_envs names st.locals = SOME x` >>
  `cut_envs names t = SOME x` by
    (match_mp_tac (GEN_ALL strong_locals_rel_I_cut_envs)>>fs[]>>
    qexists_tac`st`>>fs[]>>
    fs[strong_locals_rel_def,domain_union] >>
    metis_tac[])>>
  simp[]>>
  fs[get_store_def]>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  qexists_tac`rst.locals`>>
  fs[strong_locals_rel_def]
QED

Resume evaluate_remove_dead[Raise]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  imp_res_tac strong_locals_rel_I_get_var'>>fs[]>>
  gvs[jump_exc_def,AllCaseEqs()]
QED

Resume evaluate_remove_dead[Return]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  imp_res_tac strong_locals_rel_I_get_var'>>fs[]>>
  irule strong_locals_rel_I_get_vars'>>fs[]>>
  first_x_assum (irule_at Any)>>
  simp[domain_numset_list_insert]
QED

Resume evaluate_remove_dead[Skip]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]
QED

Resume evaluate_remove_dead[StoreConsts]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  imp_res_tac strong_locals_rel_I_get_var>>fs[]>>
  gs[Once INSERT_COMM]>>
  first_x_assum drule>>rw[]>>
  simp[set_var_def,unset_var_def]>>
  fs[strong_locals_rel_def]>>rw[lookup_insert,lookup_delete]
QED

Resume evaluate_remove_dead[Tick]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def,
    flush_state_def,dec_clock_def,state_component_equality]
QED

Resume evaluate_remove_dead[Install]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  pairarg_tac>>
  gvs[AllCaseEqs()]>>
  fs[list_insert_def]>>
  first_x_assum $ irule_at Any>> simp[]>>
  first_x_assum $ irule_at Any>> simp[]>>
  drule_at Any strong_locals_rel_I_cut_env>>
  disch_then $ irule_at Any>>
  CONJ_TAC >- (
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF,domain_union])>>
  ntac 4 (CONJ_TAC >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    qexists_tac`{}`>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]))>>
  simp[strong_locals_rel_def]
QED

Resume evaluate_remove_dead[CodeBufferWrite]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  fs[list_insert_def,PULL_EXISTS]>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  ntac 2 (CONJ_TAC >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    qexists_tac`{}`>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]))>>
  irule_at Any strong_locals_rel_subset>>
  first_x_assum (irule_at Any)>>
  simp[SUBSET_DEF]
QED

Resume evaluate_remove_dead[DataBufferWrite]:
  gvs[evaluate_def,remove_dead_def,AllCaseEqs(),get_live_def]>>
  fs[list_insert_def,PULL_EXISTS]>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  ntac 2 (CONJ_TAC >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    qexists_tac`{}`>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]))>>
  irule_at Any strong_locals_rel_subset>>
  first_x_assum (irule_at Any)>>
  simp[SUBSET_DEF]
QED

Resume evaluate_remove_dead[FFI]:
  gvs[evaluate_def,remove_dead_def,CaseEqs["option","word_loc"],get_live_def]>>
  simp[PULL_EXISTS]>>
  last_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[GSYM PULL_EXISTS]>>
  ntac 4 (
    CONJ_TAC >- (
    irule strong_locals_rel_I_get_var>>
    simp[]>>
    qexists_tac`{}`>>
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]))>>
  drule_at Any strong_locals_rel_I_cut_env>>
  disch_then $ irule_at Any>>
  simp[GSYM PULL_EXISTS]>>
  CONJ_TAC >- (
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF,domain_union])>>
  TOP_CASE_TAC>>gvs[]
  >-
    fs[strong_locals_rel_def]
  >-
    fs[flush_state_def]
QED

Resume evaluate_remove_dead[ShareInst]:
  gvs[evaluate_def,remove_dead_def,CaseEqs["option","word_loc"],get_live_def]>>
  gvs[oneline flat_exp_conventions_def,AllCasePreds()]>>
  drule strong_locals_rel_I_word_exp>>
  disch_then (irule_at Any)>>
  first_assum (irule_at Any)>>
  rename1`share_inst aa bb`>>
  fs[nlive_store_def,get_live_exp_def,domain_union,GSYM PULL_EXISTS]>>
  (CONJ_TAC >- (
    irule_at Any strong_locals_rel_subset>>
    first_x_assum (irule_at Any)>>
    qexists_tac`delete bb live`>>
    rw[SUBSET_DEF]>>simp[domain_union]))>>
  gvs[oneline share_inst_def,AllCaseEqs(),
    oneline sh_mem_store_def,
    oneline sh_mem_store_byte_def,
    oneline sh_mem_store16_def,
    oneline sh_mem_store32_def,
    oneline sh_mem_load_def,
    oneline sh_mem_load_byte_def,
    oneline sh_mem_load16_def,
    oneline sh_mem_load32_def,
    oneline sh_mem_set_var_def,
    set_var_def,
    flush_state_def, get_live_def] >>
  TRY(irule_at Any strong_locals_rel_I_insert_insert >>
    fs[strong_locals_rel_def,domain_union])>>
  irule_at Any strong_locals_rel_I_get_var'>>
  gvs[]>>
  fs[strong_locals_rel_def,domain_union]>>
  metis_tac[]
QED

Finalise evaluate_remove_dead;

Theorem evaluate_remove_dead_prog:
  ∀prog st rst res.
  flat_exp_conventions prog ∧
  evaluate (prog,st) = (res,rst) ∧
  res ≠ SOME Error ⇒
  ∃t'.
    evaluate(remove_dead_prog prog,st) = (res,rst with locals := t') ∧
    (case res of
       NONE => T
     | SOME (Break _) => T
     | SOME (Continue _) => T
     | SOME _ => rst.locals = t')
Proof
  rw[remove_dead_prog_def]>>
  `?prog' livein nlivein.
    remove_dead prog LN [] [] = (prog',livein,nlivein)` by metis_tac[PAIR]>>
  drule_at (Pos (el 5)) evaluate_remove_dead>>
  disch_then (drule_at Any)>>
  disch_then (drule_at Any)>>
  simp[]>>
  disch_then(qspecl_then[`st.locals`,`st.store`] mp_tac)>>
  impl_tac >-
    simp[strong_locals_rel_def]>>
  rw[]>>
  qexists_tac`t'`>>
  `rst.store = tstore'` by
    (every_case_tac>>fs[live_store_rel_def, fmap_eq_flookup])>>
  gvs[state_component_equality]>>
  every_case_tac>>gvs[]
QED

(*SSA Proof*)

val size_tac2 = impl_tac>- (full_simp_tac(srw_ss())[prog_size_def]>>DECIDE_TAC)

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

Theorem list_next_var_rename_lemma_1[local]:
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

Theorem list_next_var_rename_lemma_2[local]:
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

Theorem list_next_var_rename_lemma_2'[local]:
  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ==>
  ALL_DISTINCT ls ⇒
  ls' = MAP (λx. THE(lookup x ssa')) ls ∧
  domain ssa' = domain ssa ∪ set ls ∧
  (∀x. ¬MEM x ls ⇒ lookup x ssa' = lookup x ssa) ∧
  (∀x. MEM x ls ⇒ ∃y. lookup x ssa' = SOME y)
Proof
  assume_tac list_next_var_rename_lemma_2 >>
  rpt (GEN_TAC ORELSE DISCH_THEN STRIP_ASSUME_TAC) >>
  first_x_assum (Q.SPECL_THEN [`ls`,`ssa`,`na`] mp_tac) >>
  simp[]
QED

val exists_tac = qexists_tac`cst.permute`>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM,word_state_eq_rel_def
      ,ssa_cc_trans_def];

Theorem ssa_locals_rel_get_var[local]:
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

Theorem ssa_locals_rel_get_vars[local]:
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

Theorem ssa_map_ok_extend[local]:
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

Theorem merge_moves_frame[local]:
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
    (assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`4`,`r1`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions]
QED

Theorem merge_moves_fst[local]:
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
Theorem merge_moves_frame2[local]:
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
Theorem merge_moves_frame3[local]:
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

Theorem mov_eval_head[local]:
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

Theorem merge_moves_correctL[local]:
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

Theorem merge_moves_correctR[local]:
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

Theorem fake_moves_frame[local]:
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
    (assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`4`,`r1`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[]))
  >>
  CONJ_TAC>-
    DECIDE_TAC)
  >>
  metis_tac[ssa_map_ok_extend,convention_partitions]
QED

Theorem fake_moves_frame2[local]:
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

Theorem fake_moves_frame3[local]:
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

Theorem fake_moves_correctL[local]:
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

Theorem fake_moves_correctR[local]:
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
Theorem ssa_eq_rel_swap[local]:
  ssa_locals_rel na ssaR st.locals cst.locals ∧
  domain ssaL = domain ssaR ∧
  (∀x. lookup x ssaL = lookup x ssaR) ⇒
  ssa_locals_rel na ssaL st.locals cst.locals
Proof
  srw_tac[][ssa_locals_rel_def]
QED

Theorem ssa_locals_rel_more[local]:
  ssa_locals_rel na ssa stlocs cstlocs ∧ na ≤ na' ⇒
  ssa_locals_rel na' ssa stlocs cstlocs
Proof
  srw_tac[][ssa_locals_rel_def]>>full_simp_tac(srw_ss())[]
  >- metis_tac[]>>
  res_tac>>full_simp_tac(srw_ss())[]>>
  DECIDE_TAC
QED

Theorem ssa_map_ok_more[local]:
  ssa_map_ok na ssa ∧ na ≤ na' ⇒
  ssa_map_ok na' ssa
Proof
  full_simp_tac(srw_ss())[ssa_map_ok_def]>>srw_tac[][]
  >-
    metis_tac[]>>
  res_tac>>full_simp_tac(srw_ss())[]>>DECIDE_TAC
QED

Theorem get_var_ignore[local]:
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

Theorem fix_inconsistencies_correctL[local]:
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

Theorem fix_inconsistencies_correctR[local]:
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

Theorem list_next_var_rename_move_preserve[local]:
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
      (mp_tac arithmeticTheory.MOD_PLUS >>
      full_simp_tac(srw_ss())[is_phy_var_def,is_alloc_var_def,is_stack_var_def]>>
      disch_then(qspecl_then[`4`,`4*n`,`na`](SUBST1_TAC o SYM)) >>
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

Theorem option_lookup_subset_helper[local]:
  ∀ssa cst_locs ls.
    (∀x y. lookup x ssa = SOME y ⇒ y ∈ domain cst_locs) ∧
    set ls ⊆ domain ssa ⇒
    set (MAP (option_lookup ssa) ls) ⊆ domain cst_locs
Proof
  rw[SUBSET_DEF,MEM_MAP]>>
  `y ∈ domain ssa` by metis_tac[]>>
  fs[domain_lookup]>>
  rename1`lookup y ssa = SOME z`>>
  `option_lookup ssa y = z` by simp[option_lookup_def]>>
  res_tac>>fs[]
QED

Theorem list_next_var_rename_move_preserve_weak[local]:
  ∀st ssa na ls cst.
  ssa_locals_rel na ssa st.locals cst.locals ∧
  set ls ⊆ domain ssa ∧
  ALL_DISTINCT ls ∧
  ssa_map_ok na ssa ∧
  word_state_eq_rel st cst
  ⇒
  let (mov,ssa',na') = list_next_var_rename_move ssa na ls in
  let (res,rcst) = evaluate (mov,cst) in
    res = NONE ∧
    ssa_locals_rel na' ssa' st.locals rcst.locals ∧
    word_state_eq_rel st rcst
Proof
  rpt strip_tac>>
  qabbrev_tac`cls = MAP (option_lookup ssa) ls`>>
  `set cls ⊆ domain cst.locals` by (
    simp[Abbr`cls`]>>
    irule option_lookup_subset_helper>>
    fs[ssa_locals_rel_def]>>
    metis_tac[])>>
  `LENGTH cls = LENGTH ls` by simp[Abbr`cls`]>>
  full_simp_tac(srw_ss())[list_next_var_rename_move_def,ssa_locals_rel_def]>>
  srw_tac[][]>>
  imp_res_tac list_next_var_rename_lemma_1>>
  imp_res_tac list_next_var_rename_lemma_2>>
  first_x_assum(qspecl_then[`ssa`,`na`] assume_tac)>>
  full_simp_tac(srw_ss())[LET_THM,evaluate_def]>>rev_full_simp_tac(srw_ss())[]>>
  rev_full_simp_tac(srw_ss())[MAP_ZIP,LENGTH_COUNT_LIST]>>full_simp_tac(srw_ss())[]>>
  imp_res_tac get_vars_eq>>
  qpat_x_assum`A=(res,rcst)` mp_tac>>
  full_simp_tac(srw_ss())[MAP_ZIP]>>srw_tac[][]
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
      (qsuff_tac `ALOOKUP (ZIP (MAP (λx. THE (lookup x ssa')) ls,
                                 MAP (λx. THE (lookup x cst.locals)) cls))
                          (THE (lookup x ssa')) = SOME y`
      >- rw[]>>
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM>>
      full_simp_tac(srw_ss())[MAP_ZIP]>>
      full_simp_tac(srw_ss())[MEM_EL]>>
      qexists_tac`n`>>
      full_simp_tac(srw_ss())[EL_ZIP,EL_MAP,Abbr`cls`]>>
      full_simp_tac(srw_ss())[domain_lookup,option_lookup_def]>>
      `THE (lookup (ls:num list)❲n❳ ssa) = v` by simp[]>>fs[])
    >>
      (full_simp_tac(srw_ss())[domain_lookup]>>
      qpat_abbrev_tac `opt:'a word_loc option = ALOOKUP (ZIP A) v`>>
      qsuff_tac `opt = NONE`
      >- (`THE (lookup x ssa) = v` by simp[]>>fs[Abbr`opt`])>>
      full_simp_tac(srw_ss())[Abbr`opt`]>>
      match_mp_tac (SPEC_ALL ALOOKUP_NONE|>REWRITE_RULE[EQ_IMP_THM]|>CONJ_PAIR|>snd)>>
      SPOSE_NOT_THEN assume_tac>>
      full_simp_tac(srw_ss())[MAP_ZIP]>>
      `v < na` by (full_simp_tac(srw_ss())[ssa_map_ok_def]>>res_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      rpt (qpat_x_assum`A = B` sym_sub_tac)>>
      full_simp_tac(srw_ss())[MEM_MAP]>>
      Cases_on`y`>>gvs[MEM_ZIP,EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST]))
  >-
    (res_tac>>DECIDE_TAC)
  >-
    full_simp_tac(srw_ss())[word_state_eq_rel_def,set_vars_def]
QED

Theorem get_vars_list_insert_eq_gen[local]:
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

Theorem get_vars_set_vars_eq[local]:
  ∀ls x.
  ALL_DISTINCT ls ∧ LENGTH x = LENGTH ls ⇒
  get_vars ls (set_vars ls x cst) = SOME x
Proof
  full_simp_tac(srw_ss())[get_vars_def,set_vars_def]>>srw_tac[][]>>
  Q.ISPECL_THEN [`cst`,`ls`,`x`,`cst.locals`,`[]:num list`
    ,`[]:'a word_loc list`] mp_tac (GEN_ALL get_vars_list_insert_eq_gen)>>
  impl_tac>>full_simp_tac(srw_ss())[]
QED

Theorem ssa_locals_rel_ignore_set_var[local]:
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

Theorem ssa_locals_rel_ignore_insert[local]:
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


Theorem ssa_locals_rel_ignore_list_insert[local]:
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

Theorem ssa_locals_rel_set_var[local]:
  ssa_locals_rel na ssa stl cstl ∧
  ssa_map_ok na ssa ∧
  n < na ⇒
  ssa_locals_rel (na+4) (insert n na ssa) (insert n w stl) (insert na w cstl)
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

Theorem ssa_locals_rel_insert[local]:
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

val is_phy_var_tac =
    full_simp_tac(srw_ss())[is_phy_var_def]>>
    `0<2:num` by DECIDE_TAC>>
    `∀k.(2:num)*k=k*2` by DECIDE_TAC>>
    metis_tac[arithmeticTheory.MOD_EQ_0];

Theorem ssa_locals_rel_list_next_var_rename[local]:
  ∀xs ssa na stloc cstloc ys ssa' na' ls.
  list_next_var_rename xs ssa na = (ys,ssa',na') ∧
  ssa_locals_rel na ssa stloc cstloc ∧
  ssa_map_ok na ssa ∧
  LENGTH xs = LENGTH ls ∧
  EVERY (λx. x < na) xs ∧
  ALL_DISTINCT xs ∧
  ¬is_phy_var na ⇒
  ssa_locals_rel na' ssa' (alist_insert xs ls stloc) (alist_insert ys ls cstloc)
Proof
  Induct>>rw[list_next_var_rename_def,quantHeuristicsTheory.LIST_LENGTH_COMPARE_SUC]>>
  rpt(pairarg_tac>>gvs[])>>
  gvs[alist_insert_def,next_var_rename_def]>>
  last_x_assum drule>>
  rename1`insert na _ (alist_insert yss _ _)`>>
  `¬MEM na yss` by (
    drule list_next_var_rename_lemma_1>>
    rw[]>>
    simp[MEM_MAP])>>
  simp[GSYM alist_insert_pull_insert]>>
  disch_then irule>>
  rw[]
  >-
    is_phy_var_tac
  >- (
    irule EVERY_MONOTONIC>>
    first_x_assum (irule_at Any)>>
    simp[])
  >-
    simp[ssa_map_ok_extend]>>
  irule ssa_locals_rel_insert>>
  simp[]
QED

Theorem is_alloc_var_add[local]:
  is_alloc_var na ⇒ is_alloc_var (na+4)
Proof
  full_simp_tac(srw_ss())[is_alloc_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[])
QED

Theorem is_stack_var_add[local]:
  is_stack_var na ⇒ is_stack_var (na+4)
Proof
  full_simp_tac(srw_ss())[is_stack_var_def]>>
  (qspec_then `4` assume_tac arithmeticTheory.MOD_PLUS>>full_simp_tac(srw_ss())[]>>
    pop_assum (qspecl_then [`na`,`4`] assume_tac)>>
    rev_full_simp_tac(srw_ss())[])
QED

Theorem is_alloc_var_flip[local]:
  is_alloc_var na ⇒ is_stack_var (na+2)
Proof
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  qspecl_then [`4`,`na`,`2`] assume_tac
    arithmeticTheory.MOD_PLUS >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []
QED

Theorem is_stack_var_flip[local]:
  is_stack_var na ⇒ is_alloc_var (na+2)
Proof
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  ‘0 < 4:num’ by fs [] >>
  qspecl_then [`4`,`na`,`2`] assume_tac
    arithmeticTheory.MOD_PLUS >>
  full_simp_tac std_ss [EVAL “2 MOD 4”] >>
  strip_tac >> fs []
QED

(*ordered such that its easy to drule*)
Theorem list_next_var_rename_props[local]:
  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename ls ssa na = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
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
  (impl_tac>-simp[] >>
   impl_tac >-
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

(*ordered such that its easy to drule*)
Theorem list_next_var_rename_move_props[local]:
  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename_move ssa na ls = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
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

Theorem next_var_rename_props[local]:
  next_var_rename ls ssa na = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧
  ssa_map_ok na ssa
  ⇒
  na ≤ na' ∧
  (is_alloc_var na ⇒ is_alloc_var na') ∧
  (is_stack_var na ⇒ is_stack_var na') ∧
  ssa_map_ok na' ssa'
Proof
  strip_tac>>
  strip_tac>>
  irule_at Any list_next_var_rename_props>>
  simp[]>>
  qexists_tac`[ls]`>>
  qexists_tac`[ls']`>>
  qexists_tac`ssa`>>
  simp[list_next_var_rename_def]
QED

(*ordered such that its easy to drule*)
Theorem ssa_cc_trans_inst_props[local]:
  ∀i ssa na i' ssa' na'.
  ssa_cc_trans_inst i ssa na = (i',ssa',na') ==>
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

Theorem fix_inconsistencies_props[local]:
  ∀ssaL ssaR na a b na' ssaU.
  fix_inconsistencies prio ssaL ssaR na = (a,b,na',ssaU) ==>
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

Theorem flip_rw[local]:
  is_stack_var(na+2) = is_alloc_var na ∧
    is_alloc_var(na+2) = is_stack_var na
Proof
  conj_tac >> (reverse EQ_TAC >-
    metis_tac[is_alloc_var_flip,is_stack_var_flip]) >>
  full_simp_tac(srw_ss())[is_alloc_var_def,is_stack_var_def]>>
  mp_tac arithmeticTheory.MOD_PLUS >>
  (disch_then(qspecl_then[`4`,`na`,`2`](SUBST1_TAC o SYM)) >>
  `na MOD 4 < 4` by full_simp_tac(srw_ss())[]>>
  imp_res_tac (DECIDE ``n:num<4⇒(n=0)∨(n=1)∨(n=2)∨(n=3)``)>>
  full_simp_tac(srw_ss())[])
QED

val swap_imp =PROVE[]``A ==> B ==> C <=> B ==> A ==> C``

val list_next_var_rename_props_2 =
  list_next_var_rename_props
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["na","na'"]))
  |> Q.SPECL[`na+2`] |> SPEC_ALL
  |> UNDISCH
  |> REWRITE_RULE[GSYM AND_IMP_INTRO]
  |> C MATCH_MP (UNDISCH th)
  |> DISCH_ALL
  |> REWRITE_RULE[flip_rw]
  |> ONCE_REWRITE_RULE [swap_imp]
  |> UNDISCH
  |> REWRITE_RULE[AND_IMP_INTRO]
  |> DISCH_ALL
  |> GEN_ALL
  |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["ls","ssa","na"]));

Theorem ssa_map_ok_lem[local]:
  ssa_map_ok na ssa ⇒ ssa_map_ok (na+2) ssa
Proof
  metis_tac[ssa_map_ok_more, DECIDE``na:num ≤ na+2``]
QED

(*ordered such that its easy to drule*)
Theorem list_next_var_rename_move_props_2[local]:
  ∀ls ssa na ls' ssa' na'.
  list_next_var_rename_move ssa (na+2) ls = (ls',ssa',na') ==>
  (is_alloc_var na ∨ is_stack_var na) ∧ ssa_map_ok na ssa
  ⇒
  (na+2) ≤ na' ∧
  (is_alloc_var na ⇒ is_stack_var na') ∧
  (is_stack_var na ⇒ is_alloc_var na') ∧
  ssa_map_ok na' ssa'
Proof
  ntac 7 strip_tac>>imp_res_tac list_next_var_rename_move_props>>
  full_simp_tac(srw_ss())[]>>
  metis_tac[is_stack_var_flip,is_alloc_var_flip,ssa_map_ok_lem]
QED

Theorem ssa_map_ok_inter[local]:
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
  ∀prog ssa na lt prog' ssa' na'.
  ssa_cc_trans prog ssa na lt = (prog',ssa',na') ==>
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
    (*This is a slightly hacky mess*)
    PairCases_on`x`>>full_simp_tac(srw_ss())[list_next_var_rename_move_def]>>
    rpt (disch_tac ORELSE gen_tac)>>
    qpat_abbrev_tac `goal = (_ ∧ _ ∧ _)` >>
    ntac 3 (pop_assum mp_tac)>>LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[PULL_FORALL,LET_THM]>>
    rveq >>
    full_simp_tac(srw_ss())[GSYM PULL_FORALL] >>
    rveq >>
    rev_full_simp_tac(srw_ss())[]>>
    drule_then assume_tac fix_inconsistencies_props >>
    qspecl_then [`ret`, `ssa''''`, `n''`]  (mp_tac) list_next_var_rename_props >>
    qspecl_then [`ls`, `ssa_cut`, `n'`]  (mp_tac) list_next_var_rename_props_2 >>
    qspecl_then [`ls`, `ssa`, `na`]  (mp_tac) list_next_var_rename_props_2 >>
    simp[] >>
    `∀naa. ssa_map_ok naa ssa'' ⇒ ssa_map_ok naa ssa_cut` by
      (srw_tac[][Abbr`ssa_cut`,ssa_map_ok_def,lookup_inter]>>
      full_simp_tac(srw_ss())[AllCaseEqs()]>>
      metis_tac[])>>
    `∀naa ssa. ssa_map_ok naa ssa ⇒ ssa_map_ok (naa + 2) ssa` by
      (
    rpt strip_tac >>
    irule ssa_map_ok_more>>
    first_x_assum (irule_at Any) >>
    intLib.ARITH_TAC) >>
    simp[] >>
    rpt $ disch_then strip_assume_tac >>
    Q.UNABBREV_TAC `goal` >>
    full_simp_tac(srw_ss())[next_var_rename_def] >>
    rveq >>
    qspecl_then [`ssa''''`, `n'''`,`x0`] mp_tac (GEN_ALL ssa_map_ok_extend) >>
    impl_tac >-(
        fs[Once convention_partitions] >>
        imp_res_tac ssa_map_ok_more>>metis_tac[]) >>
    rpt $ disch_then strip_assume_tac >>
    full_simp_tac(srw_ss())[is_alloc_var_add]>>
    rfs[] >>
    `ssa_map_ok na_3 ssa_2`
     by (irule ssa_map_ok_more >>
     qexists_tac `n'''` >>
     fs[]) >>
    fs[]))
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
  >- ((*Loop*) suspend "Loop")
  >- ((*Break*) suspend "Break")
  >- ((*Continue*) suspend "Continue")
QED

Resume ssa_cc_trans_props[Loop]:
  strip_tac >>
  LET_ELIM_TAC >>
  fs[loop_setup_def] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  rveq >>
  drule_then assume_tac list_next_var_rename_props >>
  rfs[] >>
  qpat_x_assum `list_next_var_rename_move _ _ _ = _` assume_tac >>
  drule_then assume_tac list_next_var_rename_move_props >>
  rfs[] >>
  unabbrev_all_tac >>
  `ssa_map_ok na_refreshed (inter ssa_refreshed names)` by
    (match_mp_tac ssa_map_ok_inter >> first_x_assum ACCEPT_TAC) >>
  qpat_x_assum `_ ∧ is_alloc_var na_refreshed ⇒ _` mp_tac >>
  impl_tac >- simp[] >>
  strip_tac >>
  rpt conj_tac >>
  TRY (match_mp_tac ssa_map_ok_inter >>
       irule ssa_map_ok_more >>
       qexists_tac `na_refreshed`) >>
  gs[]
QED

Resume ssa_cc_trans_props[Break]:
  fs[ssa_cc_trans_def]>>every_case_tac>>fs[]>>rveq>>simp[]
QED

Resume ssa_cc_trans_props[Continue]:
  fs[ssa_cc_trans_def]>>every_case_tac>>fs[]>>rveq>>simp[]
QED

Finalise ssa_cc_trans_props;

Theorem PAIR_ZIP_MEM[local]:
  LENGTH c = LENGTH d ∧
  MEM (a,b) (ZIP (c,d)) ⇒
  MEM a c ∧ MEM b d
Proof
  srw_tac[][]>>imp_res_tac MEM_ZIP>>
  full_simp_tac(srw_ss())[MEM_EL]>>
  metis_tac[]
QED

Theorem ALOOKUP_ZIP_MEM[local]:
  LENGTH a = LENGTH b ∧
  ALOOKUP (ZIP (a,b)) x = SOME y
  ⇒
  MEM x a ∧ MEM y b
Proof
  srw_tac[][]>>imp_res_tac ALOOKUP_MEM>>
  metis_tac[PAIR_ZIP_MEM]
QED

Theorem ALOOKUP_ALL_DISTINCT_REMAP[local]:
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

Theorem ssa_cc_trans_exp_correct[local]:
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
    (strip_tac>>
    gvs[AllCaseEqs()]>>
    res_tac>>gvs[])
QED

val exp_tac2 =
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

Theorem get_var_set_vars_notin[local]:
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

Theorem get_vars_eq_alist_insert:
  ∀regs l.
  ALL_DISTINCT regs ∧
  LENGTH regs = LENGTH l ∧
  (∀x. MEM x regs ⇒
  lookup x st.locals =
  lookup x (alist_insert regs l rest)) ⇒
  get_vars regs st = SOME l
Proof
  Induct>>rw[get_vars_def,quantHeuristicsTheory.LIST_LENGTH_COMPARE_SUC]>>
  fs[get_var_def,alist_insert_def]>>
  rename1`LENGTH ll = LENGTH _`>>
  last_x_assum(qspec_then`ll` mp_tac)>>
  simp[]>>
  impl_tac >-
    rw[lookup_insert]>>
  simp[]
QED

Theorem cut_envs_domain_SUBSET:
  cut_envs (x1,x2) locs = SOME x ⇒
  domain x1 ⊆ domain locs ∧
  domain x2 ⊆ domain locs
Proof
  rw[cut_envs_def,cut_names_def]>>gvs[AllCaseEqs()]
QED

Theorem ssa_reconcile_distinct_lemma[local]:
  ∀f g ns.
    INJ f (domain ns) UNIV ⇒
    ALL_DISTINCT (MAP FST
      (FILTER (λ(a,b). a ≠ b)
        (MAP (λv. (f v, g v)) (MAP FST (toAList ns)))))
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `ALL_DISTINCT X` >>
  `X = MAP f (FILTER (λv. f v ≠ g v) (MAP FST (toAList ns)))` by (
    unabbrev_all_tac >>
    qspec_tac (`MAP FST (toAList ns)`, `L`) >>
    Induct >> simp[] >>
    rw[]) >>
  simp[] >>
  match_mp_tac ALL_DISTINCT_MAP_INJ >>
  reverse conj_tac
  >- (match_mp_tac FILTER_ALL_DISTINCT >>
      simp[ALL_DISTINCT_MAP_FST_toAList]) >>
  rw[MEM_FILTER, MEM_MAP, MEM_toAList] >>
  PairCases_on `y'` >> PairCases_on `y''` >>
  fs[MEM_toAList] >>
  fs[INJ_DEF] >>
  metis_tac[domain_lookup]
QED

Theorem ssa_reconcile_moves_eq[local]:
  ∀L.
    FILTER (λ(a,b). a ≠ b)
      (FLAT (MAP (λv. case lookup v m of
                      | NONE => []
                      | SOME cv => [(f v, cv)]) L)) =
    MAP (λv. (f v, THE (lookup v m)))
      (FILTER (λv. case lookup v m of NONE => F | SOME cv => f v ≠ cv) L)
Proof
  Induct >> simp[] >>
  strip_tac >>
  Cases_on `lookup h m` >> fs[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem ssa_reconcile_filtered_all_distinct[local]:
  ALL_DISTINCT (FILTER (λv. case lookup v cur_ssa of
                            | NONE => F
                            | SOME cv => option_lookup tgt_ssa v ≠ cv)
                  (MAP FST (toAList ns)))
Proof
  match_mp_tac FILTER_ALL_DISTINCT >>
  simp[ALL_DISTINCT_MAP_FST_toAList]
QED

Theorem ssa_reconcile_filtered_in_dom[local]:
  ∀v. MEM v (FILTER (λv. case lookup v cur_ssa of
                         | NONE => F
                         | SOME cv => option_lookup tgt_ssa v ≠ cv)
              (MAP FST (toAList ns))) ⇒
    v ∈ domain ns ∧
    ∃cv. lookup v cur_ssa = SOME cv ∧ option_lookup tgt_ssa v ≠ cv ∧
         THE (lookup v cur_ssa) = cv
Proof
  simp[MEM_FILTER, MEM_MAP, MEM_toAList, PULL_EXISTS, EXISTS_PROD] >>
  rpt strip_tac >>
  Cases_on `lookup v cur_ssa` >> fs[domain_lookup]
QED

Theorem ssa_reconcile_get_vars_lemma[local]:
  ∀ls cur_ssa (cst:('a,'b,'c) wordSem$state).
    ALL_DISTINCT ls ∧
    (∀v. MEM v ls ⇒
         ∃val. lookup (THE (lookup v cur_ssa)) cst.locals = SOME val) ⇒
    ∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) ls) cst = SOME vs ∧
         LENGTH vs = LENGTH ls ∧
         ∀i. i < LENGTH ls ⇒
             lookup (THE (lookup (EL i ls) cur_ssa)) cst.locals = SOME (EL i vs)
Proof
  Induct >- simp[get_vars_def] >>
  rpt strip_tac >>
  fs[] >>
  `∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) ls) cst = SOME vs ∧
        LENGTH vs = LENGTH ls ∧
        ∀i. i < LENGTH ls ⇒
            lookup (THE (lookup (EL i ls) cur_ssa)) cst.locals = SOME (EL i vs)`
    by (first_x_assum match_mp_tac >> rpt strip_tac >>
        last_x_assum match_mp_tac >> simp[]) >>
  `∃val. lookup (THE (lookup h cur_ssa)) cst.locals = SOME val`
    by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  qexists_tac `val::vs` >>
  simp[get_vars_def, get_var_def] >>
  Cases >> simp[]
QED

Theorem alookup_zip_map_some[local]:
  ∀ls vs i f.
    ALL_DISTINCT (MAP f ls) ∧
    i < LENGTH ls ∧
    LENGTH vs = LENGTH ls ⇒
    ALOOKUP (ZIP (MAP f ls, vs)) (f (EL i ls)) = SOME (EL i vs)
Proof
  rpt strip_tac >>
  irule ALOOKUP_ALL_DISTINCT_MEM >>
  conj_tac
  >- (`LENGTH (MAP f ls) = LENGTH vs` by simp[LENGTH_MAP] >>
      simp[MAP_ZIP]) >>
  `LENGTH (MAP f ls) = LENGTH ls` by simp[LENGTH_MAP] >>
  simp[MEM_ZIP] >>
  qexists_tac `i` >> simp[EL_MAP]
QED

Theorem alookup_zip_map_option_lookup_none[local]:
  ∀ls vs n ns f.
    INJ f (domain ns) UNIV ∧
    n ∈ domain ns ∧
    ¬MEM n ls ∧
    (∀v. MEM v ls ⇒ v ∈ domain ns) ∧
    LENGTH vs = LENGTH ls ⇒
    ALOOKUP (ZIP (MAP f ls, vs)) (f n) = NONE
Proof
  rpt strip_tac >>
  Cases_on `ALOOKUP (ZIP (MAP f ls, vs)) (f n)` >> simp[] >>
  imp_res_tac ALOOKUP_MEM >>
  `LENGTH (MAP f ls) = LENGTH vs` by simp[LENGTH_MAP] >>
  fs[MEM_ZIP] >>
  `f n = f (EL n' ls)` by
    (`EL n' (MAP f ls) = f (EL n' ls)` by (irule EL_MAP >> simp[]) >>
     fs[]) >>
  `MEM (EL n' ls) ls` by (simp[MEM_EL] >> qexists_tac `n'` >> simp[]) >>
  `EL n' ls ∈ domain ns` by (first_x_assum irule >> simp[]) >>
  `EL n' ls = n` by (
    qpat_x_assum `INJ f _ _` mp_tac >>
    simp[INJ_DEF] >> strip_tac >>
    first_x_assum irule >> simp[]) >>
  fs[]
QED

Theorem evaluate_ssa_reconcile[local]:
  ssa_locals_rel na cur_ssa st_locs cst.locals ∧
  INJ (option_lookup tgt_ssa) (domain ns) UNIV ⇒
  ∃cst'.
    evaluate (ssa_reconcile cur_ssa tgt_ssa ns, cst) = (NONE, cst') ∧
    word_state_eq_rel cst cst' ∧
    strong_locals_rel (option_lookup tgt_ssa) (domain ns) st_locs cst'.locals
Proof
  rpt strip_tac >>
  simp[ssa_reconcile_def] >>
  qmatch_goalsub_abbrev_tac `if moves = [] then Skip else _` >>
  `moves = MAP (λv. (option_lookup tgt_ssa v, THE (lookup v cur_ssa)))
    (FILTER (λv. case lookup v cur_ssa of
                 | NONE => F
                 | SOME cv => option_lookup tgt_ssa v ≠ cv)
       (MAP FST (toAList ns)))` by
    (unabbrev_all_tac >> simp[ssa_reconcile_moves_eq]) >>
  qmatch_asmsub_abbrev_tac `MAP _ filtered_vars` >>
  `ALL_DISTINCT filtered_vars` by
    (unabbrev_all_tac >> simp[ssa_reconcile_filtered_all_distinct]) >>
  `∀v. MEM v filtered_vars ⇒ v ∈ domain ns ∧
       ∃cv. lookup v cur_ssa = SOME cv ∧ option_lookup tgt_ssa v ≠ cv ∧
            THE (lookup v cur_ssa) = cv` by
    (unabbrev_all_tac >>
     simp[MEM_FILTER, MEM_MAP, MEM_toAList, PULL_EXISTS, EXISTS_PROD] >>
     rpt strip_tac >>
     Cases_on `lookup v cur_ssa` >> fs[domain_lookup]) >>
  `ALL_DISTINCT (MAP (option_lookup tgt_ssa) filtered_vars)` by
    (match_mp_tac ALL_DISTINCT_MAP_INJ >>
     conj_tac >- (rw[] >> res_tac >> fs[INJ_DEF]) >>
     simp[]) >>
  Cases_on `moves = []`
  >- suspend "skip_case"
  >- suspend "move_case"
QED

Resume evaluate_ssa_reconcile[skip_case]:
  simp[evaluate_def, word_state_eq_rel_def, strong_locals_rel_def] >>
  rpt strip_tac >>
  `n ∈ domain cur_ssa ∧ lookup (THE (lookup n cur_ssa)) cst.locals = SOME v`
    by (fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
  Cases_on `lookup n cur_ssa` >- fs[domain_lookup] >>
  rename1 `lookup n cur_ssa = SOME cv` >>
  `lookup cv cst.locals = SOME v` by fs[] >>
  `filtered_vars = []` by (Cases_on `filtered_vars` >> fs[]) >>
  `option_lookup tgt_ssa n = cv` by (
    qpat_x_assum `filtered_vars = _` mp_tac >>
    unabbrev_all_tac >>
    simp[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP, MEM_toAList, EXISTS_PROD,
         PULL_EXISTS] >>
    fs[domain_lookup] >>
    disch_then drule >>
    simp[]) >>
  simp[]
QED

Resume evaluate_ssa_reconcile[move_case]:
  simp[evaluate_def] >>
  `MAP FST moves = MAP (option_lookup tgt_ssa) filtered_vars ∧
   MAP SND moves = MAP (λv. THE (lookup v cur_ssa)) filtered_vars` by
    (qpat_x_assum `moves = MAP _ _` SUBST1_TAC >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >>
     simp[MAP_EQ_f]) >>
  simp[] >>
  `∀v. MEM v filtered_vars ⇒
       ∃val. lookup (THE (lookup v cur_ssa)) cst.locals = SOME val` by (
    rpt strip_tac >> res_tac >>
    fs[ssa_locals_rel_def] >>
    res_tac >> fs[domain_lookup]) >>
  `∃vs. get_vars (MAP (λv. THE (lookup v cur_ssa)) filtered_vars) cst
          = SOME vs ∧
        LENGTH vs = LENGTH filtered_vars ∧
        ∀i. i < LENGTH filtered_vars ⇒
            lookup (THE (lookup (EL i filtered_vars) cur_ssa)) cst.locals =
              SOME (EL i vs)`
    by (match_mp_tac ssa_reconcile_get_vars_lemma >> simp[]) >>
  qexists_tac
    `cst with locals := alist_insert
       (MAP (option_lookup tgt_ssa) filtered_vars) vs cst.locals` >>
  simp[set_vars_def, MAP_MAP_o, combinTheory.o_DEF, GSYM (SF ETA_ss)] >>
  simp[word_state_eq_rel_def, strong_locals_rel_def] >>
  rpt strip_tac >>
  `n ∈ domain cur_ssa ∧ lookup (THE (lookup n cur_ssa)) cst.locals = SOME v`
    by (fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
  Cases_on `lookup n cur_ssa` >- fs[domain_lookup] >>
  rename1 `lookup n cur_ssa = SOME cv` >>
  `lookup cv cst.locals = SOME v` by fs[] >>
  simp[lookup_alist_insert] >>
  Cases_on `option_lookup tgt_ssa n = cv`
  >- (
    (* Case A: not in filtered_vars *)
    `¬MEM n filtered_vars` by (
      strip_tac >> res_tac >> fs[]) >>
    `ALOOKUP (ZIP (MAP (option_lookup tgt_ssa) filtered_vars, vs))
       (option_lookup tgt_ssa n) = NONE` by (
      qspecl_then [`filtered_vars`, `vs`, `n`, `ns`, `option_lookup tgt_ssa`]
        mp_tac alookup_zip_map_option_lookup_none >>
      impl_tac
      >- (simp[] >> rpt strip_tac >> res_tac >> simp[]) >>
      simp[]) >>
    fs[]) >>
  (* Case B: in filtered_vars *)
  `MEM n filtered_vars` by (
    unabbrev_all_tac >>
    simp[MEM_FILTER, MEM_MAP, MEM_toAList, EXISTS_PROD] >>
    fs[domain_lookup] >> metis_tac[]) >>
  `∃i. i < LENGTH filtered_vars ∧ EL i filtered_vars = n` by metis_tac[MEM_EL] >>
  `ALOOKUP (ZIP (MAP (option_lookup tgt_ssa) filtered_vars, vs))
     (option_lookup tgt_ssa n) = SOME (EL i vs)` by (
    qpat_x_assum `EL i filtered_vars = n` (assume_tac o GSYM) >>
    simp[] >>
    irule alookup_zip_map_some >>
    simp[]) >>
  simp[] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  impl_tac >- simp[] >>
  simp[] >> rw[]
QED

Finalise evaluate_ssa_reconcile;

Definition lt_ok_def:
  lt_ok lt ⇔
    EVERY (λ(tgt_ssa, names, exit_names).
      INJ (option_lookup tgt_ssa) (domain names) UNIV ∧
      INJ (option_lookup tgt_ssa) (domain exit_names) UNIV) lt
End

Theorem foldr_insert_const_swap[local]:
  ∀rs h (v:'a word_loc) m.
    FOLDR (λr loc. insert r v loc) (insert h v m) rs =
    insert h v (FOLDR (λr loc. insert r v loc) m rs)
Proof
  Induct >> rw[] >>
  Cases_on `h = h'` >> simp[insert_swap]
QED

(* Evaluating a chain of fake_move r writes 0 to each register in rs,
   leaves the rest of state untouched. *)
Theorem evaluate_fake_const_chain[local]:
  ∀rs (cst:('a,'b,'c) wordSem$state).
    evaluate (FOLDR Seq Skip (MAP (λr. (fake_move r):'a wordLang$prog) rs), cst) =
      (NONE, cst with locals := FOLDR (λr loc. insert r (Word 0w) loc) cst.locals rs)
Proof
  Induct
  >- simp[evaluate_def, wordSemTheory.state_component_equality] >>
  rpt strip_tac >>
  simp[evaluate_def, fake_move_def, inst_def, assign_def, word_exp_def,
       set_var_def] >>
  first_x_assum (qspec_then `cst with locals := insert h (Word 0w) cst.locals`
                            mp_tac) >>
  simp[fake_move_def, inst_def, assign_def, word_exp_def, set_var_def] >>
  disch_then kall_tac >>
  simp[foldr_insert_const_swap]
QED

Theorem evaluate_fake_const_chain_locals[local]:
  ∀rs (cst:('a,'b,'c) wordSem$state).
    let rcst = SND (evaluate (FOLDR Seq Skip
      (MAP (λr. (fake_move r):'a wordLang$prog) rs), cst)) in
    word_state_eq_rel cst rcst ∧
    domain rcst.locals = domain cst.locals ∪ set rs ∧
    (∀r. ¬ MEM r rs ⇒ lookup r rcst.locals = lookup r cst.locals) ∧
    (∀r. MEM r rs ⇒ lookup r rcst.locals = SOME (Word 0w))
Proof
  simp[evaluate_fake_const_chain] >>
  Induct >- simp[word_state_eq_rel_def] >>
  rpt strip_tac >> rpt conj_tac
  >- fs[word_state_eq_rel_def]
  >- (fs[EXTENSION] >> metis_tac[])
  >- (rw[lookup_insert] >> fs[] >>
      first_x_assum (qspec_then `cst` mp_tac) >> simp[])
  >- (rw[lookup_insert] >> fs[] >>
      first_x_assum (qspec_then `cst` mp_tac) >> simp[])
QED

(* Bundles the (extend, fake_init, refresh) Loop-entry setup. Establishes
   ssa_locals_rel under ssa_refreshed and INJ on names/exit_names domains
   by construction. *)
Theorem loop_setup_correct[local]:
  ∀ (st:('a,'b,'c) wordSem$state) cst ssa na names exit_names
    setup_prog ssa_refreshed na_refreshed.
    word_state_eq_rel st cst ∧
    ssa_locals_rel na ssa st.locals cst.locals ∧
    ssa_map_ok na ssa ∧
    is_alloc_var na ∧
    loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed) ⇒
    ∃rcst.
      evaluate (setup_prog, cst) = (NONE,rcst) ∧
      word_state_eq_rel st rcst ∧
      ssa_locals_rel na_refreshed ssa_refreshed st.locals rcst.locals ∧
      na ≤ na_refreshed ∧
      is_alloc_var na_refreshed ∧
      ssa_map_ok na_refreshed ssa_refreshed ∧
      domain ssa_refreshed = domain ssa ∪ domain (union names exit_names) ∧
      INJ (option_lookup ssa_refreshed) (domain names) UNIV ∧
      INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV ∧
      (∀v. v ∈ domain ssa_refreshed ⇒
        option_lookup ssa_refreshed v ∈ domain rcst.locals)
Proof
  rpt strip_tac >>
  fs[loop_setup_def] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >>
  rveq >>
  qabbrev_tac
    `extend_ls = FILTER (λv. lookup v ssa = NONE)
       (MAP FST (toAList (union names exit_names)))` >>
  qabbrev_tac
    `refresh_ls = FILTER (λv. IS_SOME (lookup v ssa))
       (MAP FST (toAList (union names exit_names)))` >>
  `ALL_DISTINCT extend_ls ∧ ALL_DISTINCT refresh_ls` by (
    unabbrev_all_tac >> conj_tac >> irule FILTER_ALL_DISTINCT >>
    simp[ALL_DISTINCT_MAP_FST_toAList]) >>
  `set extend_ls ∩ set refresh_ls = ∅` by (
    unabbrev_all_tac >>
    simp[EXTENSION, MEM_FILTER] >> metis_tac[NOT_SOME_NONE]) >>
  `set extend_ls ∪ set refresh_ls = domain (union names exit_names)` by (
    unabbrev_all_tac >>
    simp[EXTENSION, MEM_FILTER, MEM_MAP, MEM_toAList,
         EXISTS_PROD, domain_lookup] >>
    metis_tac[option_CASES, IS_SOME_DEF]) >>
  qpat_x_assum `list_next_var_rename extend_ls _ _ = _` assume_tac >>
  drule_then assume_tac list_next_var_rename_props >>
  rfs[] >>
  drule_then assume_tac list_next_var_rename_lemma_1 >>
  fs[LET_THM] >>
  qspecl_then [`extend_ls`, `ssa`, `na`] mp_tac list_next_var_rename_lemma_2 >>
  simp[LET_THM] >> strip_tac >>
  (* fake_prog evaluation *)
  mp_tac (Q.SPECL [`fresh_pos_ls`, `cst`]
    (INST_TYPE [beta |-> ``:'b``, gamma |-> ``:'c``] evaluate_fake_const_chain)) >>
  qmatch_goalsub_abbrev_tac `(NONE, fake_cst)` >>
  strip_tac >>
  mp_tac (Q.SPECL [`fresh_pos_ls`, `cst`]
    (INST_TYPE [beta |-> ``:'b``, gamma |-> ``:'c``] evaluate_fake_const_chain_locals)) >>
  simp[] >> strip_tac >>
  `word_state_eq_rel st fake_cst` by (
    simp[Abbr `fake_cst`] >> fs[word_state_eq_rel_def]) >>
  `ssa_locals_rel na_ext ssa_ext st.locals fake_cst.locals`
    by (suspend "ssa_rel_after_fakes") >>
  `set refresh_ls ⊆ domain ssa_ext` by (
    fs[SUBSET_DEF, EXTENSION] >>
    `∀v. MEM v refresh_ls ⇒ MEM v (MAP FST (toAList (union names exit_names)))`
      by (unabbrev_all_tac >> simp[MEM_FILTER]) >>
    `∀v. MEM v refresh_ls ⇒ v ∈ domain ssa` by (
      unabbrev_all_tac >>
      simp[MEM_FILTER, domain_lookup, IS_SOME_EXISTS] >>
      metis_tac[]) >>
    metis_tac[]) >>
  qspecl_then [`st`, `ssa_ext`, `na_ext`, `refresh_ls`, `fake_cst`]
    mp_tac list_next_var_rename_move_preserve_weak >>
  simp[] >>
  pairarg_tac >> fs[] >>
  strip_tac >>
  qpat_x_assum `list_next_var_rename_move ssa_ext _ refresh_ls = _`
    assume_tac >>
  drule_then assume_tac list_next_var_rename_move_props >>
  rfs[] >>
  fs[list_next_var_rename_move_def] >>
  pairarg_tac >> fs[] >> rveq >>
  qpat_x_assum `list_next_var_rename refresh_ls _ _ = _` assume_tac >>
  drule_then assume_tac list_next_var_rename_lemma_1 >>
  qspecl_then [`refresh_ls`, `ssa_ext`, `na + 4 * LENGTH extend_ls`]
    mp_tac list_next_var_rename_lemma_2 >>
  fs[LET_THM] >> rfs[] >> strip_tac >>
  qexists_tac `rcst` >>
  qpat_x_assum `new_ls = _` (assume_tac o GSYM) >> fs[] >>
  `∀v. MEM v extend_ls ⇒
       ∃idx. idx < LENGTH extend_ls ∧
             option_lookup ssa' v = na + 4 * idx`
    by (suspend "extend_ls_fresh") >>
  `∀v. MEM v refresh_ls ⇒
       ∃j. j < LENGTH refresh_ls ∧
           option_lookup ssa' v = na + 4 * LENGTH extend_ls + 4 * j`
    by (suspend "refresh_ls_fresh") >>
  `INJ (option_lookup ssa') (set extend_ls ∪ set refresh_ls) UNIV`
    by (suspend "INJ_extend_refresh") >>
  `domain names ⊆ set extend_ls ∪ set refresh_ls ∧
   domain exit_names ⊆ set extend_ls ∪ set refresh_ls` by (
    fs[SUBSET_DEF] >> rpt strip_tac >>
    `x ∈ domain (union names exit_names)` by (
      simp[domain_union] >> metis_tac[]) >>
    metis_tac[IN_UNION]) >>
  rpt conj_tac
  >- simp[evaluate_def]
  >- (qpat_x_assum `set extend_ls ∪ set refresh_ls = _`
        (assume_tac o GSYM) >> fs[AC UNION_ASSOC UNION_COMM])
  >- (irule INJ_less >>
      qexists_tac `set extend_ls ∪ set refresh_ls` >> simp[])
  >- (irule INJ_less >>
      qexists_tac `set extend_ls ∪ set refresh_ls` >> simp[])
  >- suspend "domain_coverage"
QED

Resume loop_setup_correct[ssa_rel_after_fakes]:
  simp[ssa_locals_rel_def] >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `MEM x extend_ls`
      >- (`MEM y (MAP (λx. THE (lookup x ssa_ext)) extend_ls)` by (
            simp[MEM_MAP] >> qexists_tac `x` >> simp[]) >>
          metis_tac[domain_lookup, IS_SOME_DEF])
      >- (`lookup x ssa = SOME y` by metis_tac[] >>
          `y ∈ domain cst.locals` by (
            fs[ssa_locals_rel_def] >> metis_tac[]) >>
          fs[])) >>
  ntac 2 gen_tac >> strip_tac >>
  `x ∈ domain ssa ∧ lookup (THE (lookup x ssa)) cst.locals = SOME y ∧
   (is_alloc_var x ⇒ x < na)` by (fs[ssa_locals_rel_def] >> metis_tac[]) >>
  `¬MEM x extend_ls` by (
    unabbrev_all_tac >> simp[MEM_FILTER] >>
    fs[domain_lookup, IS_SOME_EXISTS]) >>
  `lookup x ssa_ext = lookup x ssa` by metis_tac[] >>
  rpt conj_tac
  >- (`x ∈ domain ssa_ext` by (
        qpat_x_assum `domain ssa_ext = _` SUBST1_TAC >> simp[]) >>
      simp[])
  >- (`∃z. lookup x ssa = SOME z` by fs[domain_lookup] >>
      `THE (lookup x ssa) < na`
        by (fs[ssa_map_ok_def] >> res_tac >> simp[]) >>
      `¬MEM (THE (lookup x ssa)) fresh_pos_ls` by (
        qpat_x_assum `fresh_pos_ls = _` SUBST1_TAC >>
        simp[MEM_MAP, MEM_COUNT_LIST] >>
        rpt strip_tac >> gvs[]) >>
      `¬MEM (THE (lookup x ssa)) (MAP (λx. THE (lookup x ssa_ext)) extend_ls)`
        by metis_tac[] >>
      `lookup (THE (lookup x ssa)) fake_cst.locals =
       lookup (THE (lookup x ssa)) cst.locals` by metis_tac[] >>
      metis_tac[])
  >- (strip_tac >> res_tac >> DECIDE_TAC)
QED

Resume loop_setup_correct[extend_ls_fresh]:
  rpt strip_tac >>
  `∃idx. idx < LENGTH extend_ls ∧ EL idx extend_ls = v` by metis_tac[MEM_EL] >>
  qexists_tac `idx` >> simp[] >>
  `¬MEM v refresh_ls` by (fs[EXTENSION] >> metis_tac[]) >>
  `lookup v ssa' = lookup v ssa_ext` by metis_tac[] >>
  `∃y. lookup v ssa_ext = SOME y` by metis_tac[] >>
  simp[option_lookup_def] >>
  `THE (lookup v ssa_ext) = EL idx (MAP (λx. THE (lookup x ssa_ext)) extend_ls)`
    by simp[EL_MAP] >>
  rfs[] >>
  qpat_x_assum `MAP (λx. na + 4 * x) _ = _` (SUBST1_TAC o GSYM) >>
  DEP_REWRITE_TAC[EL_MAP, EL_COUNT_LIST] >> simp[LENGTH_COUNT_LIST]
QED

Resume loop_setup_correct[refresh_ls_fresh]:
  rpt strip_tac >>
  `∃j. j < LENGTH refresh_ls ∧ EL j refresh_ls = v` by metis_tac[MEM_EL] >>
  qexists_tac `j` >> simp[] >>
  `∃y. lookup v ssa' = SOME y` by metis_tac[] >>
  simp[option_lookup_def] >>
  `THE (lookup v ssa') = EL j (MAP (λx. THE (lookup x ssa')) refresh_ls)`
    by simp[EL_MAP] >>
  rfs[] >>
  qpat_x_assum `MAP (λx. na + (4 * x + 4 * LENGTH extend_ls)) _ = _`
    (SUBST1_TAC o GSYM) >>
  DEP_REWRITE_TAC[EL_MAP, EL_COUNT_LIST] >> simp[LENGTH_COUNT_LIST]
QED

Resume loop_setup_correct[INJ_extend_refresh]:
  simp[INJ_DEF] >>
  `∀v ix. MEM v extend_ls ∧ ix < LENGTH extend_ls ∧ EL ix extend_ls = v ⇒
          option_lookup ssa' v = na + 4 * ix` by (
    rpt strip_tac >>
    `¬MEM v refresh_ls` by (fs[EXTENSION] >> metis_tac[]) >>
    `lookup v ssa' = lookup v ssa_ext` by metis_tac[] >>
    `∃z. lookup v ssa_ext = SOME z` by metis_tac[] >>
    simp[option_lookup_def] >>
    `THE (lookup v ssa_ext) = EL ix (MAP (λx. THE (lookup x ssa_ext)) extend_ls)`
      by simp[EL_MAP] >>
    rfs[] >>
    qpat_x_assum `MAP (λx. na + 4 * x) _ = _` (SUBST1_TAC o GSYM) >>
    DEP_REWRITE_TAC[EL_MAP, EL_COUNT_LIST] >> simp[LENGTH_COUNT_LIST]) >>
  `∀v iy. MEM v refresh_ls ∧ iy < LENGTH refresh_ls ∧ EL iy refresh_ls = v ⇒
          option_lookup ssa' v = na + 4 * LENGTH extend_ls + 4 * iy` by (
    rpt strip_tac >>
    `∃z. lookup v ssa' = SOME z` by metis_tac[] >>
    simp[option_lookup_def] >>
    `THE (lookup v ssa') = EL iy (MAP (λx. THE (lookup x ssa')) refresh_ls)`
      by simp[EL_MAP] >>
    rfs[] >>
    qpat_x_assum `MAP (λx. na + (4 * x + 4 * LENGTH extend_ls)) _ = _`
      (SUBST1_TAC o GSYM) >>
    DEP_REWRITE_TAC[EL_MAP, EL_COUNT_LIST] >> simp[LENGTH_COUNT_LIST]) >>
  ntac 2 gen_tac >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  disch_tac >>
  Cases_on `MEM x extend_ls`
  >- (Cases_on `MEM y extend_ls`
      >- (`∃ix. ix < LENGTH extend_ls ∧ EL ix extend_ls = x` by metis_tac[MEM_EL] >>
          `∃iy. iy < LENGTH extend_ls ∧ EL iy extend_ls = y` by metis_tac[MEM_EL] >>
          `option_lookup ssa' x = na + 4 * ix` by metis_tac[] >>
          `option_lookup ssa' y = na + 4 * iy` by metis_tac[] >>
          `na + 4 * ix = na + 4 * iy` by metis_tac[] >>
          `ix = iy` by gs[] >>
          metis_tac[])
      >- (`MEM y refresh_ls` by fs[] >>
          `∃ix. ix < LENGTH extend_ls ∧ EL ix extend_ls = x` by metis_tac[MEM_EL] >>
          `∃iy. iy < LENGTH refresh_ls ∧ EL iy refresh_ls = y` by metis_tac[MEM_EL] >>
          `option_lookup ssa' x = na + 4 * ix` by metis_tac[] >>
          `option_lookup ssa' y = na + 4 * LENGTH extend_ls + 4 * iy` by metis_tac[] >>
          `na + 4 * ix = na + 4 * LENGTH extend_ls + 4 * iy` by metis_tac[] >>
          `F` by gs[] >>
          fs[]))
  >- (`MEM x refresh_ls` by fs[] >>
      Cases_on `MEM y refresh_ls`
      >- (`∃ix. ix < LENGTH refresh_ls ∧ EL ix refresh_ls = x` by metis_tac[MEM_EL] >>
          `∃iy. iy < LENGTH refresh_ls ∧ EL iy refresh_ls = y` by metis_tac[MEM_EL] >>
          `option_lookup ssa' x = na + 4 * LENGTH extend_ls + 4 * ix` by metis_tac[] >>
          `option_lookup ssa' y = na + 4 * LENGTH extend_ls + 4 * iy` by metis_tac[] >>
          `na + 4 * LENGTH extend_ls + 4 * ix =
           na + 4 * LENGTH extend_ls + 4 * iy` by metis_tac[] >>
          `ix = iy` by gs[] >>
          metis_tac[])
      >- (`MEM y extend_ls` by fs[] >>
          `∃ix. ix < LENGTH refresh_ls ∧ EL ix refresh_ls = x` by metis_tac[MEM_EL] >>
          `∃iy. iy < LENGTH extend_ls ∧ EL iy extend_ls = y` by metis_tac[MEM_EL] >>
          `option_lookup ssa' x = na + 4 * LENGTH extend_ls + 4 * ix` by metis_tac[] >>
          `option_lookup ssa' y = na + 4 * iy` by metis_tac[] >>
          `na + 4 * LENGTH extend_ls + 4 * ix = na + 4 * iy` by metis_tac[] >>
          `F` by gs[] >>
          fs[]))
QED

Resume loop_setup_correct[domain_coverage]:
  rpt strip_tac >>
  `∃y. lookup v ssa' = SOME y` by (
    Cases_on `MEM v refresh_ls` >- metis_tac[] >>
    `lookup v ssa' = lookup v ssa_ext` by metis_tac[] >>
    `v ∈ domain ssa_ext` by (
      qpat_x_assum `domain ssa_ext = _` SUBST1_TAC >>
      simp[] >> fs[]) >>
    fs[domain_lookup]) >>
  fs[option_lookup_def, ssa_locals_rel_def] >>
  metis_tac[]
QED

Finalise loop_setup_correct;


(* If P evaluates to (NONE, t), Seq P Q evaluates as Q from t. *)
Theorem evaluate_seq_collapse[local]:
  evaluate (P, s) = (NONE, t) ⇒
  evaluate (Seq P Q, s) = evaluate (Q, t)
Proof
  simp[evaluate_def]
QED

(* fromAList (MAP f (toAList LN)) behaves like LN in cut_env. *)
Theorem cut_env_fromAList_LN[local]:
  cut_env (a, fromAList (MAP (g:num#unit -> num#unit) (toAList LN))) v =
  cut_env (a, LN) v
Proof
  simp[cut_env_def, cut_envs_def, cut_names_def,
       sptreeTheory.toAList_def, sptreeTheory.foldi_def,
       sptreeTheory.fromAList_def] >>
  rpt CASE_TAC >> simp[]
QED

(* Helper for Loop iter; target is the INNER Loop (not the full translation),
   so the clock-IH recursive call lines up with the inner Loop's STOP-recursion
   without re-running the outer fake_prog + refresh_mov setup each iter. *)
Theorem ssa_cc_trans_Loop_helper[local]:
  ∀(st:('a,'b,'c) wordSem$state) cst ssa_refreshed na_refreshed
    names body exit_names lt body' ssa' na'.
    word_state_eq_rel st cst ∧
    strong_locals_rel (option_lookup ssa_refreshed) (domain names)
      st.locals cst.locals ∧
    (∀v. v ∈ domain names ⇒
       option_lookup ssa_refreshed v ∈ domain cst.locals) ∧
    ssa_map_ok na_refreshed ssa_refreshed ∧
    is_alloc_var na_refreshed ∧
    every_var (λx. x < na_refreshed) body ∧
    INJ (option_lookup ssa_refreshed) (domain names) UNIV ∧
    INJ (option_lookup ssa_refreshed) (domain exit_names) UNIV ∧
    domain names ⊆ domain ssa_refreshed ∧
    domain exit_names ⊆ domain ssa_refreshed ∧
    EVERY (λx. x < na_refreshed) (MAP FST (toAList names)) ∧
    EVERY (λx. x < na_refreshed) (MAP FST (toAList exit_names)) ∧
    lt_ok lt ∧
    ssa_cc_trans body (inter ssa_refreshed names) na_refreshed
      ((ssa_refreshed,names,exit_names)::lt) = (body',ssa',na') ∧
    (∀(st':('a,'b,'c) wordSem$state) cst' ssa'' na'' lt'.
       word_state_eq_rel st' cst' ∧
       ssa_locals_rel na'' ssa'' st'.locals cst'.locals ∧
       is_alloc_var na'' ∧
       every_var (λx. x < na'') body ∧
       ssa_map_ok na'' ssa'' ∧
       lt_ok lt' ⇒
       ∃perm'.
         (let (res,rst) = evaluate (body, st' with permute := perm') in
            res = SOME Error ∨
            (let (prog',ssaB,naB) = ssa_cc_trans body ssa'' na'' lt';
                 (res',rcst) = evaluate (prog', cst') in
               res = res' ∧ word_state_eq_rel rst rcst ∧
               case res of
                 NONE => ssa_locals_rel naB ssaB rst.locals rcst.locals
               | SOME (Break n) =>
                   (case oEL n lt' of
                      NONE => T
                    | SOME (tgt_ssa,_,exit_names) =>
                        strong_locals_rel (option_lookup tgt_ssa)
                          (domain exit_names) rst.locals rcst.locals)
               | SOME (Continue n') =>
                   (case oEL n' lt' of
                      NONE => T
                    | SOME (tgt_ssa,names,_) =>
                        strong_locals_rel (option_lookup tgt_ssa)
                          (domain names) rst.locals rcst.locals)
               | SOME _ => rst.locals = rcst.locals))) ⇒
    let back_moves = ssa_reconcile ssa' ssa_refreshed names in
    let body_final = if back_moves = Skip then body' else Seq body' back_moves in
    let ssa_names = apply_nummap_key (option_lookup ssa_refreshed) names in
    let ssa_exit = apply_nummap_key (option_lookup ssa_refreshed) exit_names in
    ∀res' rcst.
      evaluate (Loop ssa_names body_final ssa_exit, cst) = (res',rcst) ⇒
      ∃perm'.
        (λ(res,rst).
            res = SOME Error ∨
            res = res' ∧ word_state_eq_rel rst rcst ∧
            case res of
              NONE => ssa_locals_rel na' (inter ssa_refreshed exit_names)
                        rst.locals rcst.locals
            | SOME (Break n) =>
                (case oEL n lt of
                   NONE => T
                 | SOME (tgt_ssa,_,exit_names) =>
                     strong_locals_rel (option_lookup tgt_ssa)
                       (domain exit_names) rst.locals rcst.locals)
            | SOME (Continue n') =>
                (case oEL n' lt of
                   NONE => T
                 | SOME (tgt_ssa,names,_) =>
                     strong_locals_rel (option_lookup tgt_ssa)
                       (domain names) rst.locals rcst.locals)
            | SOME _ => rst.locals = rcst.locals)
          (evaluate (Loop names body exit_names, st with permute := perm'))
Proof
  gen_tac>>
  qid_spec_tac `st`>>
  completeInduct_on `cst.clock`>>
  rpt strip_tac>>
  simp[LET_DEF]>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum `evaluate (Loop _ _ _, cst) = _` mp_tac>>
  simp[Once evaluate_def]>>
  TOP_CASE_TAC>>fs[]
  >- ((* target_cut_none *)
      strip_tac >>
      qpat_x_assum `cut_state _ cst = NONE` mp_tac >>
      simp[cut_state_def, cut_env_def, cut_envs_def, cut_names_def,
           apply_nummap_key_def, domain_fromAList, MAP_MAP_o,
           combinTheory.o_DEF, SUBSET_DEF, MEM_MAP, EXISTS_PROD,
           MEM_toAList, AllCaseEqs(), PULL_EXISTS] >>
      rpt strip_tac >>
      fs[SUBSET_DEF, domain_lookup] >>
      metis_tac[]) >>
  (* main: source cut split *)
  rename1 `cut_state _ cst = SOME cut_cst` >>
  strip_tac >>
  Cases_on `cut_state (names,LN) st`
  >- (qexists_tac `cst.permute` >>
      simp[Once evaluate_def]) >>
  rename1 `cut_state (names,LN) st = SOME cut_st` >>
  (* core: drive cut_env_lemma *)
  simp[Once evaluate_def] >>
  fs[cut_state_def, AllCaseEqs()] >>
  drule_at (Pos (el 2)) cut_env_lemma >>
  disch_then (qspecl_then [`cst.locals`, `option_lookup ssa_refreshed`] mp_tac) >>
  impl_tac
  >- (simp[domain_union] >>
      fs[strong_locals_rel_def, apply_nummap_key_def] >>
      rw[]) >>
  strip_tac >>
  (* after_cut_lemma *)
  gvs[apply_nummaps_key_def, cut_env_fromAList_LN] >>
  (* after_cut_unified: instantiate body-IH *)
  last_assum (qspecl_then
    [`st with locals := env'`,
     `cst with locals := env`,
     `inter ssa_refreshed names`,
     `na_refreshed`,
     `(ssa_refreshed,names,exit_names)::lt`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- fs[word_state_eq_rel_def]
      >- ((* body_ih_locals_rel: 5-conjunct ssa_locals_rel *)
          simp[ssa_locals_rel_def] >>
          rw[]
          >- ((* blr_case_inter_dom *)
              rename1 `lookup k1 (inter _ _) = SOME _` >>
              qexists_tac `k1` >>
              Cases_on `lookup k1 names` >>
              gvs[sptreeTheory.lookup_inter_EQ, option_lookup_def,
                  sptreeTheory.domain_lookup])
          >- ((* blr_case_dom_ssa *)
              `x ∈ domain env'` by
                (simp[sptreeTheory.domain_lookup] >> metis_tac[]) >>
              `x ∈ domain names` by metis_tac[] >>
              fs[SUBSET_DEF])
          >- ((* blr_case_dom_names *)
              `x ∈ domain env'` by
                (simp[sptreeTheory.domain_lookup] >> metis_tac[]) >>
              metis_tac[])
          >- ((* blr_case_lookup_env *)
              subgoal `x ∈ domain env'`
              >- (simp[sptreeTheory.domain_lookup] >> metis_tac[]) >>
              subgoal `x ∈ domain names` >- metis_tac[] >>
              subgoal `x ∈ domain ssa_refreshed`
              >- metis_tac[SUBSET_DEF] >>
              Cases_on `lookup x ssa_refreshed`
              >- fs[sptreeTheory.domain_lookup] >>
              gvs[sptreeTheory.lookup_inter_alt] >>
              qpat_x_assum
                `strong_locals_rel _ _ env' env`
                (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
              disch_then (qspecl_then [`x`, `y`] mp_tac) >>
              simp[option_lookup_def])
          >- ((* blr_case_alloc *)
              `x ∈ domain env'` by
                (simp[sptreeTheory.domain_lookup] >> metis_tac[]) >>
              `x ∈ domain names` by metis_tac[] >>
              fs[EVERY_MEM, toAList_domain]))
      >- fs[]
      >- fs[every_var_def]
      >- ((* body_ih_map_ok *)
          fs[ssa_map_ok_def, sptreeTheory.lookup_inter_EQ] >>
          metis_tac[])
      >- (fs[lt_ok_def] >>
          first_assum ACCEPT_TAC)) >>
  strip_tac >>
  Cases_on `evaluate (body,st with <|permute := perm'; locals := env'|>)` >>
  rename1 `evaluate (body, _) = (bres, brst)` >>
  Cases_on `bres = SOME Error`
  >- (qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) st = SOME (st with locals := env')` by
        fs[wordSemTheory.cut_state_def] >>
      gvs[wordSemTheory.exit_loop_def, wordSemTheory.cont_loop_def]) >>
  fs[] >>
  Cases_on `evaluate (body',cst with locals := env)` >>
  rename1 `evaluate (body', _) = (bres', brcst)` >>
  fs[] >>
  Cases_on `bres`
  >- ((* NONE: cont_loop fires; recurse via clock-IH *)
      suspend "none") >>
  Cases_on `x`
  >- ((* Result *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- ((* Exception *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- ((* Break n *)
      Cases_on `n`
      >- ((* Break 0: Loop catches Break 0, cuts on exit_names, returns NONE *)
          qexists_tac `perm'` >>
          simp[Once wordSemTheory.evaluate_def] >>
          `cut_state (names,LN) (st with permute := perm') =
             SOME (st with <|permute := perm'; locals := env'|>)` by
            fs[wordSemTheory.cut_state_def] >>
          Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              wordSemTheory.evaluate_def, LLOOKUP_def,
              wordSemTheory.cut_state_def] >>
          suspend "break0")
      >- (qexists_tac `perm'` >>
          simp[Once wordSemTheory.evaluate_def] >>
          `cut_state (names,LN) (st with permute := perm') =
             SOME (st with <|permute := perm'; locals := env'|>)` by
            fs[wordSemTheory.cut_state_def] >>
          Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              wordSemTheory.evaluate_def, LLOOKUP_def]))
  >- ((* Continue n *)
      Cases_on `n`
      >- ((* Continue 0: cont_loop fires; recurse via clock-IH like NONE *)
          suspend "continue0")
      >- (qexists_tac `perm'` >>
          simp[Once wordSemTheory.evaluate_def] >>
          `cut_state (names,LN) (st with permute := perm') =
             SOME (st with <|permute := perm'; locals := env'|>)` by
            fs[wordSemTheory.cut_state_def] >>
          Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              wordSemTheory.evaluate_def, LLOOKUP_def]))
  >- ((* TimeOut *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- ((* NotEnoughSpace *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- ((* FinalFFI *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.evaluate_def])
  >- gvs[]  (* Error case: contradiction with bres ≠ SOME Error *)
QED

Resume ssa_cc_trans_Loop_helper[break0]:
  markerLib.RESUME_TAC >>
  Cases_on `cut_env (exit_names,LN) brst.locals` >> gvs[] >>
  drule_at (Pos (el 2)) cut_env_lemma >>
  disch_then (qspecl_then [`brcst.locals`, `option_lookup ssa_refreshed`] mp_tac) >>
  impl_tac
  >- (simp[domain_union] >>
      fs[strong_locals_rel_def] >>
      rw[]) >>
  strip_tac >>
  gvs[apply_nummaps_key_def, apply_nummap_key_def, cut_env_fromAList_LN] >>
  conj_tac >- fs[word_state_eq_rel_def] >>
  simp[ssa_locals_rel_def] >>
  rw[] >>
  TRY (rename1 `_ ∈ domain ssa_refreshed` >>
       `x' ∈ domain x` by
         (rewrite_tac[sptreeTheory.domain_lookup] >>
          qexists_tac `y'` >> first_assum ACCEPT_TAC) >>
       `x' ∈ domain exit_names` by gvs[] >>
       fs[SUBSET_DEF] >> NO_TAC) >>
  TRY (rename1 `_ ∈ domain exit_names` >>
       `x' ∈ domain x` by
         (rewrite_tac[sptreeTheory.domain_lookup] >>
          qexists_tac `y'` >> first_assum ACCEPT_TAC) >>
       gvs[] >> NO_TAC) >>
  TRY (rename1 `lookup (THE _) y = SOME _` >>
       `x' ∈ domain x` by
         (rewrite_tac[sptreeTheory.domain_lookup] >>
          qexists_tac `y'` >> first_assum ACCEPT_TAC) >>
       `x' ∈ domain exit_names` by gvs[] >>
       `x' ∈ domain ssa_refreshed` by
         (qpat_x_assum `domain exit_names ⊆ domain ssa_refreshed`
            (assume_tac o SIMP_RULE std_ss [SUBSET_DEF]) >>
          first_x_assum drule >> simp[]) >>
       Cases_on `lookup x' ssa_refreshed`
       >- fs[sptreeTheory.domain_lookup] >>
       gvs[sptreeTheory.lookup_inter_alt] >>
       qpat_x_assum `strong_locals_rel _ _ x _`
         (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
       disch_then (qspecl_then [`x'`, `y'`] mp_tac) >>
       simp[option_lookup_def] >> NO_TAC) >>
  TRY (rename1 `_ < na'` >>
       `x' ∈ domain x` by
         (rewrite_tac[sptreeTheory.domain_lookup] >>
          qexists_tac `y'` >> first_assum ACCEPT_TAC) >>
       `x' ∈ domain exit_names` by gvs[] >>
       `x' < na_refreshed` by fs[EVERY_MEM, toAList_domain] >>
       `ssa_map_ok na_refreshed (inter ssa_refreshed names)` by
         (irule ssa_map_ok_inter >> first_assum ACCEPT_TAC) >>
       drule ssa_cc_trans_props >>
       impl_tac >- gvs[] >>
       strip_tac >> gvs[] >> NO_TAC) >>
  TRY (rename1 `word_state_eq_rel _ _` >>
       fs[word_state_eq_rel_def] >> NO_TAC) >>
  ((* inter_dom: only inter_dom goals reach here *)
   qexists_tac `x'` >>
   gvs[option_lookup_def, sptreeTheory.lookup_inter_alt, AllCaseEqs()])
QED

Resume ssa_cc_trans_Loop_helper[none]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `_ (ssa_cc_trans body _ _ _)` mp_tac >>
  simp[LLOOKUP_def] >>
  strip_tac >>
  (* Run evaluate_ssa_reconcile to bridge from ssa_locals_rel (body-IH NONE
     conclusion) to strong_locals_rel.  In Skip case the post-state cst'
     coincides with brcst (since evaluate(Skip, brcst) = (NONE, brcst));
     in non-Skip case cst' is the post-ssa_reconcile state. *)
  mp_tac (let val tvs = type_vars_in_term (Thm.concl evaluate_ssa_reconcile)
              val delta = List.hd tvs
              val typed = INST_TYPE [delta |-> Type`:unit`] evaluate_ssa_reconcile
          in Q.SPECL [`ssa_refreshed`, `brst.locals`, `names`,
                      `na'`, `ssa'`, `brcst`] (GEN_ALL typed) end) >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  Cases_on `brst.clock = 0`
  >- ((* TimeOut case *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) st = SOME (st with locals := env')` by
        fs[wordSemTheory.cut_state_def] >>
      simp[] >>
      gvs[] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.evaluate_def, wordSemTheory.cont_loop_def]
      >- (`brcst.clock = 0` by fs[word_state_eq_rel_def] >>
          gvs[wordSemTheory.flush_state_def, word_state_eq_rel_def]) >>
      `cst'.clock = 0` by fs[word_state_eq_rel_def] >>
      gvs[wordSemTheory.flush_state_def, word_state_eq_rel_def]) >>
  (* clock != 0: source recursive Loop on dec_clock brst, target on dec_clock cst' *)
  `brst.clock = brcst.clock` by fs[word_state_eq_rel_def] >>
  `brcst.clock = cst'.clock` by fs[word_state_eq_rel_def] >>
  Cases_on `cut_env (names, LN) brst.locals`
  >- ((* source recursive cut fails: source returns Error *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      simp[] >>
      `(brst with clock := brst.clock).clock ≠ 0` by simp[] >>
      gvs[wordSemTheory.fix_clock_def, wordSemTheory.cont_loop_def,
          STOP_def, wordSemTheory.dec_clock_def] >>
      simp[Once wordSemTheory.evaluate_def,
           wordSemTheory.cut_state_def]) >>
  imp_res_tac wordSemTheory.evaluate_clock >>
  `(dec_clock cst').clock < cst.clock` by gvs[dec_clock_def] >>
  qpat_x_assum `∀m. m < cst.clock ⇒ _`
    (qspec_then `(dec_clock cst').clock` mp_tac) >>
  impl_keep_tac >- simp[] >>
  disch_then (qspec_then `dec_clock cst'` mp_tac) >>
  simp[] >>
  `domain names ⊆ domain brst.locals` by
    (qpat_x_assum `cut_env (names,LN) brst.locals = _`
       (mp_tac o REWRITE_RULE [wordSemTheory.cut_env_def]) >>
     simp[AllCaseEqs()] >>
     rpt strip_tac >>
     drule cut_envs_domain_SUBSET >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `∀v. v ∈ domain names ⇒
         option_lookup ssa_refreshed v ∈ domain cst'.locals` by
    (rpt strip_tac >>
     `∃v''. lookup v brst.locals = SOME v''` by
       (`v ∈ domain brst.locals` by
          (qpat_x_assum `domain names ⊆ domain brst.locals` mp_tac >>
           simp[SUBSET_DEF] >> disch_then drule >> simp[]) >>
        qpat_x_assum `v ∈ domain brst.locals` mp_tac >>
        simp[domain_lookup]) >>
     `lookup (option_lookup ssa_refreshed v) cst'.locals = SOME v''` by
       (qpat_x_assum `strong_locals_rel _ _ brst.locals cst'.locals`
          (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
        disch_then (qspecl_then [`v`, `v''`] mp_tac) >>
        impl_tac
        >- (conj_tac
            >- first_assum ACCEPT_TAC
            >- first_assum ACCEPT_TAC) >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     simp[domain_lookup] >>
     qexists_tac `v''` >>
     first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then
    [`dec_clock brst`, `ssa_refreshed`, `na_refreshed`,
     `names`, `body`, `exit_names`, `lt`,
     `body'`, `ssa'`, `na'`] mp_tac) >>
  impl_tac
  >- gvs[word_state_eq_rel_def, dec_clock_def, strong_locals_rel_def] >>
  strip_tac >>
  first_x_assum (qspec_then `res'` mp_tac) >>
  disch_then (qspec_then `rcst` mp_tac) >>
  impl_tac
  >- (Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >> gvs[]
      >- ((* Skip case: derive cst' = brcst, then unfold STOP to match asm *)
          `cst' = brcst` by
            (qpat_x_assum `evaluate (Skip, brcst) = _` mp_tac >>
             simp[Once wordSemTheory.evaluate_def]) >>
          qpat_x_assum `cst' = brcst` (fn th => REWRITE_TAC [th]) >>
          qpat_x_assum `evaluate (STOP _, _) = _`
            (mp_tac o REWRITE_RULE [STOP_def]) >>
          rw[])
      >- ((* non-Skip case: body_final = Seq body' ssa_reconcile *)
          `evaluate (Seq body' (ssa_reconcile ssa' ssa_refreshed names),
                     cst with locals := env) = (NONE, cst')` by
            (simp[Once wordSemTheory.evaluate_def] >> gvs[]) >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.fix_clock_def,
              STOP_def])) >>
  strip_tac >>
  Q.ISPECL_THEN
    [`body`, `st with <|locals := env'; permute := perm'|>`, `perm''`]
    assume_tac wordPropsTheory.permute_swap_lemma >>
  rfs[LET_THM] >>
  pop_assum mp_tac >>
  impl_keep_tac >- gvs[] >>
  strip_tac >>
  qexists_tac `perm'³'` >> simp[] >>
  simp[Once wordSemTheory.evaluate_def] >>
  simp[wordSemTheory.cut_state_def] >>
  `dec_clock (brst with permute := perm'') =
     dec_clock brst with permute := perm''`
    by simp[dec_clock_def] >>
  fs[STOP_def, wordSemTheory.cont_loop_def] >>
  gvs[]
QED

Resume ssa_cc_trans_Loop_helper[continue0]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `_ (ssa_cc_trans body _ _ _)` mp_tac >>
  simp[LLOOKUP_def] >>
  strip_tac >>
  `brst.clock = brcst.clock` by fs[word_state_eq_rel_def] >>
  Cases_on `brst.clock = 0`
  >- ((* TimeOut: clock=0 → both sides flush *)
      qexists_tac `perm'` >>
      simp[Once wordSemTheory.evaluate_def] >>
      `cut_state (names,LN) (st with permute := perm') =
         SOME (st with <|permute := perm'; locals := env'|>)` by
        fs[wordSemTheory.cut_state_def] >>
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >>
      gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
          wordSemTheory.flush_state_def, wordSemTheory.evaluate_def,
          word_state_eq_rel_def])
  >- ((* clock != 0: recursive via clock-IH *)
      Cases_on `ssa_reconcile ssa' ssa_refreshed names = Skip` >> fs[]
      >- ((* Skip case: body_final = body' *)
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              STOP_def] >>
          Cases_on `cut_env (names, LN) brst.locals`
          >- ((* recursive cut fails: source returns Error *)
              qexists_tac `perm'` >>
              simp[Once wordSemTheory.evaluate_def] >>
              `cut_state (names,LN) (st with permute := perm') =
                 SOME (st with <|permute := perm'; locals := env'|>)` by
                fs[wordSemTheory.cut_state_def] >>
              simp[] >>
              `(brst with clock := brst.clock).clock ≠ 0` by simp[] >>
              gvs[wordSemTheory.fix_clock_def, wordSemTheory.cont_loop_def,
                  STOP_def, wordSemTheory.dec_clock_def] >>
              simp[Once wordSemTheory.evaluate_def,
                   wordSemTheory.cut_state_def]) >>
          (* recursive cut succeeds: apply IH *)
          imp_res_tac wordSemTheory.evaluate_clock >>
          `(dec_clock brcst).clock < cst.clock` by gvs[dec_clock_def] >>
          qpat_x_assum `∀m. m < cst.clock ⇒ _`
            (qspec_then `(dec_clock brcst).clock` mp_tac) >>
          impl_keep_tac >- simp[] >>
          disch_then (qspec_then `dec_clock brcst` mp_tac) >>
          simp[] >>
          `strong_locals_rel (option_lookup ssa_refreshed) (domain names)
             brst.locals brcst.locals` by
            (simp[strong_locals_rel_def] >> first_assum ACCEPT_TAC) >>
          `domain names ⊆ domain brst.locals` by
            (qpat_x_assum `cut_env (names,LN) brst.locals = _`
               (mp_tac o REWRITE_RULE [wordSemTheory.cut_env_def]) >>
             simp[AllCaseEqs()] >>
             rpt strip_tac >>
             drule cut_envs_domain_SUBSET >>
             strip_tac >> first_assum ACCEPT_TAC) >>
          `∀v. v ∈ domain names ⇒
                 option_lookup ssa_refreshed v ∈ domain brcst.locals` by
            (rpt strip_tac >>
             `∃v''. lookup v brst.locals = SOME v''` by
               (`v ∈ domain brst.locals` by
                  (qpat_x_assum `domain names ⊆ domain brst.locals` mp_tac >>
                   simp[SUBSET_DEF] >> disch_then drule >> simp[]) >>
                qpat_x_assum `v ∈ domain brst.locals` mp_tac >>
                simp[domain_lookup]) >>
             `lookup (option_lookup ssa_refreshed v) brcst.locals = SOME v''` by
               (qpat_x_assum `strong_locals_rel _ _ brst.locals brcst.locals`
                  (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
                disch_then (qspecl_then [`v`, `v''`] mp_tac) >>
                impl_tac
                >- (conj_tac
                    >- first_assum ACCEPT_TAC
                    >- first_assum ACCEPT_TAC) >>
                strip_tac >> first_assum ACCEPT_TAC) >>
             simp[domain_lookup] >>
             qexists_tac `v''` >>
             first_assum ACCEPT_TAC) >>
          disch_then (qspecl_then
            [`dec_clock brst`, `ssa_refreshed`, `na_refreshed`,
             `names`, `body`, `exit_names`, `lt`,
             `body'`, `ssa'`, `na'`] mp_tac) >>
          impl_tac
          >- gvs[word_state_eq_rel_def, dec_clock_def, strong_locals_rel_def] >>
          strip_tac >>
          first_x_assum (qspec_then `res'` mp_tac) >>
          disch_then (qspec_then `rcst` mp_tac) >>
          impl_tac >- simp[] >>
          strip_tac >>
          Q.ISPECL_THEN
            [`body`, `st with <|locals := env'; permute := perm'|>`, `perm''`]
            assume_tac wordPropsTheory.permute_swap_lemma >>
          rfs[LET_THM] >>
          qexists_tac `perm'³'` >> simp[] >>
          simp[Once wordSemTheory.evaluate_def] >>
          simp[wordSemTheory.cut_state_def] >>
          `dec_clock (brst with permute := perm'') =
             dec_clock brst with permute := perm''`
            by simp[dec_clock_def] >>
          fs[STOP_def, wordSemTheory.cont_loop_def] >>
          gvs[])
      >- ((* non-Skip case: body_final = Seq body' ssa_reconcile *)
          `evaluate (Seq body' (ssa_reconcile ssa' ssa_refreshed names),
                     cst with locals := env) = (SOME (Continue 0), brcst)` by
            (simp[Once wordSemTheory.evaluate_def] >> gvs[]) >>
          fs[] >>
          gvs[wordSemTheory.cont_loop_def, wordSemTheory.exit_loop_def,
              STOP_def] >>
          Cases_on `cut_env (names, LN) brst.locals`
          >- ((* recursive cut fails: source returns Error *)
              qexists_tac `perm'` >>
              simp[Once wordSemTheory.evaluate_def] >>
              `cut_state (names,LN) (st with permute := perm') =
                 SOME (st with <|permute := perm'; locals := env'|>)` by
                fs[wordSemTheory.cut_state_def] >>
              simp[] >>
              `(brst with clock := brst.clock).clock ≠ 0` by simp[] >>
              gvs[wordSemTheory.fix_clock_def, wordSemTheory.cont_loop_def,
                  STOP_def, wordSemTheory.dec_clock_def] >>
              simp[Once wordSemTheory.evaluate_def,
                   wordSemTheory.cut_state_def]) >>
          imp_res_tac wordSemTheory.evaluate_clock >>
          `(dec_clock brcst).clock < cst.clock` by gvs[dec_clock_def] >>
          qpat_x_assum `∀m. m < cst.clock ⇒ _`
            (qspec_then `(dec_clock brcst).clock` mp_tac) >>
          impl_keep_tac >- simp[] >>
          disch_then (qspec_then `dec_clock brcst` mp_tac) >>
          simp[] >>
          `domain names ⊆ domain brst.locals` by
            (qpat_x_assum `cut_env (names,LN) brst.locals = _`
               (mp_tac o REWRITE_RULE [wordSemTheory.cut_env_def]) >>
             simp[AllCaseEqs()] >>
             rpt strip_tac >>
             drule cut_envs_domain_SUBSET >>
             strip_tac >> first_assum ACCEPT_TAC) >>
          `∀v. v ∈ domain names ⇒
                 option_lookup ssa_refreshed v ∈ domain brcst.locals` by
            (rpt strip_tac >>
             `∃v''. lookup v brst.locals = SOME v''` by
               (`v ∈ domain brst.locals` by
                  (qpat_x_assum `domain names ⊆ domain brst.locals` mp_tac >>
                   simp[SUBSET_DEF] >> disch_then drule >> simp[]) >>
                qpat_x_assum `v ∈ domain brst.locals` mp_tac >>
                simp[domain_lookup]) >>
             `lookup (option_lookup ssa_refreshed v) brcst.locals = SOME v''` by
               (qpat_x_assum `strong_locals_rel _ _ brst.locals brcst.locals`
                  (mp_tac o REWRITE_RULE [strong_locals_rel_def]) >>
                disch_then (qspecl_then [`v`, `v''`] mp_tac) >>
                impl_tac
                >- (conj_tac
                    >- first_assum ACCEPT_TAC
                    >- first_assum ACCEPT_TAC) >>
                strip_tac >> first_assum ACCEPT_TAC) >>
             simp[domain_lookup] >>
             qexists_tac `v''` >>
             first_assum ACCEPT_TAC) >>
          disch_then (qspecl_then
            [`dec_clock brst`, `ssa_refreshed`, `na_refreshed`,
             `names`, `body`, `exit_names`, `lt`,
             `body'`, `ssa'`, `na'`] mp_tac) >>
          impl_tac
          >- gvs[word_state_eq_rel_def, dec_clock_def, strong_locals_rel_def] >>
          strip_tac >>
          first_x_assum (qspec_then `res'` mp_tac) >>
          disch_then (qspec_then `rcst` mp_tac) >>
          impl_tac >- simp[] >>
          strip_tac >>
          Q.ISPECL_THEN
            [`body`, `st with <|locals := env'; permute := perm'|>`, `perm''`]
            assume_tac wordPropsTheory.permute_swap_lemma >>
          rfs[LET_THM] >>
          qexists_tac `perm'³'` >> simp[] >>
          simp[Once wordSemTheory.evaluate_def] >>
          simp[wordSemTheory.cut_state_def] >>
          `dec_clock (brst with permute := perm'') =
             dec_clock brst with permute := perm''`
            by simp[dec_clock_def] >>
          fs[STOP_def, wordSemTheory.cont_loop_def] >>
          gvs[]))
QED

Finalise ssa_cc_trans_Loop_helper;

Theorem ssa_cut_inter_lemma[local]:
  domain ssa' ∩ domain (union x1 x2) = domain x1 ∪ domain x2 ⇒
  xx ∈ domain (union x1 x2) ⇒
  xx ∈ domain ssa'
Proof
  rw[EXTENSION,IN_INTER,domain_union] >>
  metis_tac[]
QED

Theorem ssa_cc_trans_correct:
  ∀ prog st cst ssa na lt.
  word_state_eq_rel st cst ∧
  ssa_locals_rel na ssa st.locals cst.locals ∧
  (*The following 3 assumptions are from the transform properties and
    are independent of semantics*)
  is_alloc_var na ∧
  every_var (λx. x < na) prog ∧
  ssa_map_ok na ssa ∧
  lt_ok lt
  ⇒
  ∃perm'.
  let (res,rst) = evaluate(prog,st with permute:=perm') in
  if (res = SOME Error) then T else
  let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in
  let (res',rcst) = evaluate(prog',cst) in
    res = res' ∧
    word_state_eq_rel rst rcst ∧
    (case res of
      NONE =>
        ssa_locals_rel na' ssa' rst.locals rcst.locals
    | SOME (Break n) =>
        (case oEL n lt of
           SOME (tgt_ssa,_,exit_names) =>
             strong_locals_rel (option_lookup tgt_ssa) (domain exit_names)
               rst.locals rcst.locals
         | NONE => T)
    | SOME (Continue n) =>
        (case oEL n lt of
           SOME (tgt_ssa,names,_) =>
             strong_locals_rel (option_lookup tgt_ssa) (domain names)
               rst.locals rcst.locals
         | NONE => T)
    | SOME _    => rst.locals = rcst.locals )
Proof
  completeInduct_on`prog_size (K 0) prog`>>
  rpt strip_tac>>
  full_simp_tac(srw_ss())[PULL_FORALL,evaluate_def]>>
  Cases_on`prog`
  >~[`Skip`] >- suspend "Skip"
  >~[`Move`] >- suspend "Move"
  >~[`Inst`] >- suspend "Inst"
  >~[`Assign`] >- suspend "Assign"
  >~[`Get`] >- suspend "Get"
  >~[`Set`] >- suspend "Set"
  >~[`Store`] >- suspend "Store"
  >~[`MustTerminate`] >- suspend "MustTerminate"
  >~[`Call`] >- suspend "Call"
  >~[`Seq`] >- suspend "Seq"
  >~[`If`] >- suspend "If"
  >~[`Alloc`] >- suspend "Alloc"
  >~[`StoreConsts`] >- suspend "StoreConsts"
  >~[`Raise`] >- suspend "Raise"
  >~[`Return`] >- suspend "Return"
  >~[`Tick`] >- suspend "Tick"
  >~[`OpCurrHeap`] >- suspend "OpCurrHeap"
  >~[`LocValue`] >- suspend "LocValue"
  >~[`Install`] >- suspend "Install"
  >~[`CodeBufferWrite`] >- suspend "CodeBufferWrite"
  >~[`DataBufferWrite`] >- suspend "DataBufferWrite"
  >~[`FFI`] >- suspend "FFI"
  >~[`ShareInst`] >- suspend "ShareInst"
  >~[`Loop`] >- suspend "Loop"
  >~[`Break`] >- suspend "Break"
  >~[`Continue`] >- suspend "Continue"
QED

Resume ssa_cc_trans_correct[Skip]:
    exists_tac
QED

Resume ssa_cc_trans_correct[Move]:
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
QED

Resume ssa_cc_trans_correct[Inst]:
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
      rename1`Shift _ n n0 r`>>
      Cases_on`r`>>
      fs[evaluate_def,inst_def,assign_def,get_vars_def]
      >- (
        fs[word_exp_def]>>
        rename1`Reg n'`>>
        Cases_on`get_var n0 st`>>fs[]>>
        rename1`get_var _ _ = SOME x`>>
        Cases_on`x`>>simp[]>>
        Cases_on`get_var n' st`>>fs[]>>
        rename1`get_var _ _ = SOME x`>>
        Cases_on`x`>>simp[]>>
        imp_res_tac ssa_locals_rel_get_var>>
        fs[set_vars_def,get_var_def,lookup_alist_insert]>>
        `option_lookup ssa n0 ≠ 8` by (
          fs[ssa_locals_rel_def]>>
          qpat_x_assum`lookup n' _ = _` kall_tac>>
          first_x_assum drule>>
          rfs[domain_lookup,ssa_map_ok_def]>>
          strip_tac>>
          first_x_assum drule>>
          rw[]>>
          fs[is_phy_var_def,option_lookup_def]>>
          CCONTR_TAC>>
          fs[])>>
        fs[]>>
        every_case_tac>>
        simp[set_var_def,alist_insert_def]>>
        match_mp_tac ssa_locals_rel_set_var>>
        fs[every_var_def,every_var_inst_def]>>
        irule ssa_locals_rel_ignore_insert>>
        simp[is_phy_var_def])
     >- (
        qpat_abbrev_tac`expr = (Shift s (Var n0) Z)`>>
        setup_tac>>
        match_mp_tac ssa_locals_rel_set_var>>
        fs[every_var_inst_def,every_var_def])
    )
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
      full_simp_tac(srw_ss())[mem_load_32_alt]>>
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
QED

Resume ssa_cc_trans_correct[Assign]:
    exp_tac2
QED

Resume ssa_cc_trans_correct[Get]:
    exp_tac2
QED

Resume ssa_cc_trans_correct[Set]:
    exp_tac2
QED

Resume ssa_cc_trans_correct[Store]:
    exists_tac>>
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
    full_simp_tac(srw_ss())[]
QED

Resume ssa_cc_trans_correct[MustTerminate]:
    rw[ssa_cc_trans_def]>>
    rpt(pairarg_tac>>gvs[])>>
    fs[evaluate_def,word_state_eq_rel_def]>>
    first_x_assum(qspecl_then[
    `p`,`st with <|clock:=MustTerminate_limit (:'a);termdep:=st.termdep-1|>`,
    `cst with <|clock:=MustTerminate_limit (:'a);termdep:=st.termdep-1|>`,`ssa`,`na`,`lt`] mp_tac)>>
    size_tac2>>
    impl_tac>-
     fs[every_var_def]>>
    strip_tac>>
    qexists_tac`perm'`>>simp[]>>
    IF_CASES_TAC>>fs[]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[AllCaseEqs()]
QED

Resume ssa_cc_trans_correct[Call]:
    Cases_on`o'`
    >- suspend "Call_tail"
    >> suspend "Call_returning"
QED

Resume ssa_cc_trans_correct[Call_tail]:
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
    qpat_x_assum `evaluate (q', st with <|locals := _; locals_size := _; stack_max := _; permute := _; clock := _|>) = _` mp_tac>>
    qpat_x_assum `evaluate (q', cst with <|locals := _; locals_size := _; stack_max := _; clock := _|>) = _` mp_tac>>
    qpat_abbrev_tac`cst'=cst with <|locals:=A;locals_size := Ls; stack_max := SM; clock:=B|>`>>
    qpat_abbrev_tac`st'=st with <|locals:=A;locals_size := Ls;stack_max := SM; permute:=B;clock:=C|>`>>
    `cst' = st'` by
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[state_component_equality])>>
    rw [] >> every_case_tac >> gvs [bad_fun_return_def]
QED

Resume ssa_cc_trans_correct[Call_returning]:
    PairCases_on`x`>> full_simp_tac(srw_ss())[] >>
    Q.PAT_ABBREV_TAC`pp = ssa_cc_trans X Y Z lt` >>
    PairCases_on`pp` >> simp[] >>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def]) >>
    simp_tac std_ss [ssa_cc_trans_def]>>
    LET_ELIM_TAC>>
    full_simp_tac(srw_ss())[Abbr`all_names`,evaluate_def,add_ret_loc_def]>>
    ntac 7 (TOP_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    drule_then assume_tac cut_envs_domain_SUBSET>>
    `domain (FST stack_set) ≠ {}` by
      full_simp_tac(srw_ss())[Abbr`stack_set`,domain_fromAList,toAList_not_empty,nummaps_to_nummap]>>
    `ALL_DISTINCT regs` by
      fs[Abbr`regs`,ALL_DISTINCT_GENLIST]>>
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
      >- (
        gvs[Abbr`ls`,toAList_domain,SUBSET_DEF,domain_union]>>
        metis_tac[])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)) >>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`ls`,`ssa`,`na`,`stack_mov`,`ssa'`,`na'`] assume_tac list_next_var_rename_move_props_2>>
    Q.ISPECL_THEN [`ls`,`ssa_cut`,`na'`,`ret_mov`,`ssa''`,`na''`] assume_tac list_next_var_rename_move_props_2>>
    Q.ISPECL_THEN [`x3`,`ssa_2_p`,`na_2_p`,`lt`,`ren_ret_handler`,`ssa_2`,`na_2`] assume_tac ssa_cc_trans_props>>
    rev_full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[MAP_ZIP]>>
    `ALL_DISTINCT conv_args` by
      (full_simp_tac(srw_ss())[Abbr`conv_args`,ALL_DISTINCT_GENLIST]>>
      srw_tac[][]>>DECIDE_TAC)>>
    (*Establish invariants about ssa_cut to use later*)
    `domain ssa_cut = domain x1 ∪ domain x2` by (
      full_simp_tac(srw_ss())[EXTENSION,Abbr`ssa_cut`,domain_inter,domain_union]>>
      srw_tac[][EQ_IMP_THM]>>
      gvs[SUBSET_DEF]>>
      first_x_assum drule>>
      fs[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒ lookup x ssa' = SOME y` by
      (srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`,lookup_inter]>>
      EVERY_CASE_TAC>>full_simp_tac(srw_ss())[])>>
    `ssa_map_ok na' ssa_cut` by
      full_simp_tac(srw_ss())[Abbr`ssa_cut`,ssa_map_ok_inter]>>
    (*Probably need to case split here to deal with the 2 cases*)
    Cases_on`o0`>>full_simp_tac(srw_ss())[]
    >- suspend "Call_returning_no_handler"
    >> suspend "Call_returning_with_handler"
QED

Resume ssa_cc_trans_correct[Call_returning_no_handler]:

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
      (*Try to use cut_envs_lemma from word_live*)
      `INJ f (domain x1 ∪ domain x2) UNIV` by (
        srw_tac[][INJ_DEF]>>
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain,domain_union])>>
      rename1`push_env yy NONE _`>>
      PairCases_on`yy`>>
      drule_at Any cut_envs_lemma>>
      disch_then (qspecl_then [`rcst'.locals`,`f`] mp_tac)>>
      impl_tac>- (
        CONJ_TAC >- metis_tac[INJ_UNION]>>
        CONJ_TAC >- metis_tac[INJ_UNION]>>
        rfs[Abbr`f`]>>
        fs[ssa_locals_rel_def,strong_locals_rel_def]>>
        ntac 1 (last_x_assum kall_tac)>>
        srw_tac[][]>>
        full_simp_tac(srw_ss())[option_lookup_def,domain_lookup]>>
        res_tac>>
        full_simp_tac(srw_ss())[]>>
        qpat_x_assum`A=SOME v` SUBST_ALL_TAC>>
        full_simp_tac(srw_ss())[]) >>
      srw_tac[][Abbr`rcst'`]>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
      IF_CASES_TAC  >>
      full_simp_tac(srw_ss())[call_env_def,flush_state_def] >-
        fs [push_env_def, env_to_list_def, stack_size_def, stack_size_frame_def,
           state_component_equality] >>
      qpat_abbrev_tac`rcst' = rcst with locals := A`>>
      Q.ISPECL_THEN[
        `y1`,`y2`,
        `yy0`,`yy1:'a word_loc num_map`,`st with clock := st.clock-1`,
        `f`,`rcst' with clock := st.clock-1`,`NONE:(num#'a wordLang$prog#num#num)option`,
         `NONE:(num#'a wordLang$prog#num#num)option`,`λn. rcst.permute (n+1)`]
        mp_tac (GEN_ALL push_env_s_val_eq)>>
      impl_tac>-
        rev_full_simp_tac(srw_ss())[Abbr`rcst'`]>>
      strip_tac>>
      rev_full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def]>>
      qabbrev_tac `envx = push_env (yy0,yy1)
              (NONE:(num # 'a wordLang$prog #num #num)option)
              (st with <|permute := perm; clock := st.clock − 1|>) with
            <|locals := fromList2 (q) ; locals_size := r' ;
              stack_max := OPTION_MAP2 MAX (push_env (yy0,yy1) NONE
                (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
                (OPTION_MAP2 $+(stack_size (push_env (yy0,yy1) NONE
                 (st with <|permute := perm; clock := st.clock - 1|>)).stack) r')|>`>>
      qpat_abbrev_tac `envy = (push_env (y1,y2) A B) with <| locals := C; locals_size := lsz; stack_max := SM;
                       clock := _ |>`>>
      mp_tac evaluate_stack_swap>>
      disch_then (qspecl_then [`q'`,`envx`] mp_tac)>>
      ntac 2 FULL_CASE_TAC >- (
        srw_tac[][]>>qexists_tac`perm`>>
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
        IF_CASES_TAC>- (
          qexists_tac`perm`>>
          full_simp_tac(srw_ss())[Abbr`regs`])>>
        qspecl_then [`(y1,y2)`,`NONE:(num#'a wordLang$prog#num#num)option`,
          `(rcst' with clock := st.clock-1)`,`r with stack := st'`]
          assume_tac push_env_pop_env_s_key_eq>>
        qspecl_then [`(yy0,yy1)`,`NONE:(num#'a wordLang$prog#num#num)option`,
           `(st with <|permute:=perm;clock := st.clock-1|>)`,`r`]
          assume_tac push_env_pop_env_s_key_eq>>
        (*This went missing somewhere..*)
        `rcst'.clock = st.clock` by
          full_simp_tac(srw_ss())[Abbr`rcst'`]>>
        pop_assum SUBST_ALL_TAC>>
        full_simp_tac(srw_ss())[Abbr`envy`,Abbr`envx`,state_component_equality]>>
        rev_full_simp_tac(srw_ss())[]>>
        (*Now is a good place to establish the invariant ssa_locals_rel*)
        `ssa_locals_rel na' ssa_cut y.locals y'.locals ∧
         word_state_eq_rel y y'` by (
          full_simp_tac(srw_ss())[state_component_equality]>>
          `s_key_eq y.stack y'.stack` by
            metis_tac[s_key_eq_trans,s_key_eq_sym] >>
          Q.ISPECL_THEN [`y'`, `y`,  `st'`, `r`]
            assume_tac (GEN_ALL pop_env_frame) >>
          rev_full_simp_tac(srw_ss())[]>>
          rpt (qpat_x_assum`_ cst = _` kall_tac)>>
          rpt (qpat_x_assum`_ rcst = _` kall_tac)>>
          rpt (qpat_x_assum`_ st = _` kall_tac)>>
          last_x_assum kall_tac>>
          fs[ssa_locals_rel_def,Abbr`ssa_cut`]>>
          CONJ_TAC  >- (
            rpt (qpat_x_assum`A=domain _` mp_tac)>>
            fs[Abbr`f`]>>
            rpt (pop_assum kall_tac)>>
            rw[]>>
            qpat_x_assum`_ ∪ _ = _` kall_tac>>
            qpat_x_assum`_ ∪ _ = _` sym_sub_tac>>
            gvs[lookup_inter,lookup_union,AllCaseEqs(),option_lookup_def]>>
            metis_tac[domain_lookup])>>
          rpt gen_tac>>
          rename1`lookup xx`>>
          strip_tac>>
          `xx ∈ domain (union x1 x2)` by
            metis_tac[domain_lookup,UNION_COMM,domain_union]>>
          `xx ∈ domain ssa'` by metis_tac[ssa_cut_inter_lemma]>>
          rpt CONJ_TAC
          >- gvs[domain_union]
          >- (
            `xx ∈ domain (inter ssa' (union x1 x2))` by
              fs[domain_inter,domain_union]>>
            pop_assum mp_tac>> simp[domain_lookup]>>
            strip_tac>>
            `v = f xx` by full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def,lookup_inter,lookup_union,AllCaseEqs()]>>
            rveq>>
            full_simp_tac(srw_ss())[lookup_fromAList,lookup_union]>>
            rename1`ALOOKUP lll xx` >>
            rename1`ALOOKUP flll (f xx)` >>
            full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
            full_simp_tac(srw_ss())[s_key_eq_def,s_val_eq_def]>>
            Cases_on`opt`>>Cases_on`opt'`>>
            full_simp_tac(srw_ss())[s_frame_key_eq_def,s_frame_val_eq_def]>>
            full_simp_tac(srw_ss())[lookup_fromAList]>>
            `flll = ZIP (MAP f (MAP FST lll), MAP SND lll)` by (
              imp_res_tac key_map_implies>>
              rev_full_simp_tac(srw_ss())[]>>
              metis_tac[ZIP_MAP_FST_SND_EQ])>>
            Q.ISPECL_THEN [`MAP SND lll`, `xx`, `MAP FST lll`,`f`]
              MP_TAC $  GEN_ALL ALOOKUP_key_remap_INJ >>
            impl_tac >- (
              simp[]>>
              irule INJ_less>>
              last_x_assum (irule_at Any)>>
              fs[domain_union,domain_fromAList,SUBSET_DEF,EXTENSION]>>
              metis_tac[])>>
            strip_tac>>fs[ZIP_MAP_FST_SND_EQ]>>
            TOP_CASE_TAC>> fs[]>>
            qpat_x_assum`strong_locals_rel f (domain x1) yy0 y1` mp_tac>>
            simp[strong_locals_rel_def]>>
            fs[ALOOKUP_toAList]>>
            metis_tac[domain_lookup])
          >- (
            strip_tac>>
            `xx < na` by (
               qpat_x_assum `every_var _ _` mp_tac >>
               simp[every_var_def,every_name_def,EVERY_MEM,set_MAP_FST_toAList_domain] >>
               gvs[domain_union]) >>
            intLib.ARITH_TAC))>>
        full_simp_tac(srw_ss())[AC UNION_COMM UNION_ASSOC]>>
        (*We set the return variables but it is never in the
          locals so the ssa_locals_rel property is preserved*)
        `ssa_locals_rel na' ssa_cut y.locals
          (alist_insert regs l' y'.locals)` by (
          match_mp_tac ssa_locals_rel_ignore_list_insert>>
          full_simp_tac(srw_ss())[]>>
          rw[EVERY_MEM,Abbr`regs`,MEM_GENLIST]>>
          is_phy_var_tac)>>
        qspecl_then [`y`,`ssa_cut`,`na'+2`,`MAP FST (toAList (union x1 x2))`
                     ,`(set_vars regs l' y')`] mp_tac
                     list_next_var_rename_move_preserve>>
        impl_tac>- (
          rw[set_vars_def]
          >-
            (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
            full_simp_tac(srw_ss())[]>>
            qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
            rev_full_simp_tac(srw_ss())[])
          >- (
            full_simp_tac(srw_ss())[Abbr`ls`,set_MAP_FST_toAList_domain,domain_union,SUBSET_DEF,EXTENSION]>>
            metis_tac[])
          >-
            full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList,Abbr`ls`]
          >-
            (`na' ≤ na'+2`by DECIDE_TAC>>
            metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
          >>
            full_simp_tac(srw_ss())[word_state_eq_rel_def,set_var_def])>>
        LET_ELIM_TAC>>
        full_simp_tac(srw_ss())[Abbr`mov_ret_handler`,evaluate_def]>>
        `LENGTH ret' = LENGTH regs ∧
          ALL_DISTINCT ret'` by (
          drule list_next_var_rename_lemma_1>>
          rw[Abbr`regs`,LENGTH_COUNT_LIST])>>
        rev_full_simp_tac(srw_ss())[LET_THM,MAP_ZIP,set_vars_def]>>
        `get_vars regs rcst'' = SOME l'` by (
          `¬ is_phy_var (na'+2)` by
            metis_tac[is_stack_var_flip,convention_partitions]>>
          first_x_assum drule>>
          strip_tac>>
          irule get_vars_eq_alist_insert>>
          rw[Abbr`regs`]
          >- (
            qexists_tac`y'.locals`>>
            rw[MEM_GENLIST]>>
            first_x_assum irule>>
            is_phy_var_tac)>>
          rw[ALL_DISTINCT_GENLIST])>>
        full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
        qabbrev_tac`res_st = (set_vars x0 l' y)`>>
        qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
        `ssa_locals_rel na_2_p ssa_2_p res_st.locals res_rcst.locals` by (
          unabbrev_all_tac>>
          simp[set_vars_def]>>
          irule ssa_locals_rel_list_next_var_rename>>
          simp[]>>
          first_x_assum (irule_at Any)>>
          simp[]>>
          CONJ_TAC >-
            metis_tac[convention_partitions]>>
          irule EVERY_MONOTONIC>>
          full_simp_tac (srw_ss()) [every_var_def]>>
          first_x_assum (irule_at Any)>>
          simp[])>>
        first_x_assum(qspecl_then[`x3`,`res_st`,`res_rcst`,`ssa_2_p`,`na_2_p`,`lt`] mp_tac)>>
        size_tac2>>
        impl_tac>-(
          full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`,Abbr`res_rcst`,set_var_def]>>
          drule list_next_var_rename_props>>
          impl_tac >- simp[]>>
          simp[]>>
          full_simp_tac(srw_ss())[every_var_def,next_var_rename_def]>>srw_tac[][]>>
          match_mp_tac every_var_mono>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
          DECIDE_TAC)>>
        srw_tac[][]>>
        qspecl_then[`q'`,`push_env (yy0,yy1) (NONE:(num#'a wordLang$prog#num#num) option)
              (st with <|permute := perm; clock := st.clock − 1|>) with
            <|locals := fromList2 q; locals_size := r' ;
              stack_max := OPTION_MAP2 MAX (push_env (yy0,yy1) NONE
                (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
                (OPTION_MAP2 $+ (stack_size (push_env (yy0,yy1) NONE  (st with
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
        full_simp_tac(srw_ss())[Abbr`regs`]>>
        rev_full_simp_tac(srw_ss())[set_vars_def,Abbr`res_st`] )
      >- (
        (*Excepting without handler*)
        full_simp_tac(srw_ss())[]>>strip_tac>>
        imp_res_tac s_val_eq_LASTN_exists>>
        first_x_assum(qspecl_then[`envy.stack`,`e0'`,`e'`,`ls'`] assume_tac)>>
        rev_full_simp_tac(srw_ss())[]>>
        qexists_tac`perm`>>
        `ls'''=ls' ∧ e0 = e0''` by
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
        srw_tac[][]>>full_simp_tac(srw_ss())[]
QED

Resume ssa_cc_trans_correct[Call_returning_with_handler]:
    (*Handler reasoning*)
    qpat_x_assum`A=(pp0,pp1,pp2)` mp_tac>>
    PairCases_on`x''`>>full_simp_tac(srw_ss())[]>>
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
    `INJ f (domain x1 ∪ domain x2) UNIV` by (
      srw_tac[][INJ_DEF]>>
      drule list_next_var_rename_move_distinct>>
      disch_then match_mp_tac>>
      simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain,domain_union])>>
    (*Try to use cut_env_lemma from word_live*)
    rename1`push_env yy (SOME _) _`>>
    PairCases_on`yy`>>
    drule_at Any cut_envs_lemma>>
    disch_then (qspecl_then [`rcst'.locals`,`f`] mp_tac)>>
    impl_tac>- (
      CONJ_TAC >- metis_tac[INJ_UNION]>>
      CONJ_TAC >- metis_tac[INJ_UNION]>>
      rfs[Abbr`f`]>>
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      ntac 1 (last_x_assum kall_tac)>>
      srw_tac[][]>>
      full_simp_tac(srw_ss())[option_lookup_def,domain_lookup]>>
      res_tac>>
      full_simp_tac(srw_ss())[]>>
      qpat_x_assum`A=SOME v` SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[])>>
    srw_tac[][Abbr`rcst'`]>>full_simp_tac(srw_ss())[add_ret_loc_def]>>
    IF_CASES_TAC>>full_simp_tac(srw_ss())[call_env_def,flush_state_def]
    >- fs [push_env_def, env_to_list_def, stack_size_def, stack_size_frame_def,
         state_component_equality] >>
    qpat_abbrev_tac`rcst' = rcst with locals := A`>>
    Q.ISPECL_THEN[
        `y1`,`y2`,
        `yy0`,`yy1:'a word_loc num_map`,`st with clock := st.clock-1`,
        `f`,`rcst' with clock := st.clock-1`,`SOME(2:num,cons_exc_handler,x''2,x''3)`,
       `SOME (x''0,x''1,x''2,x''3)`,`λn. rcst.permute (n+1)`]
      mp_tac (GEN_ALL push_env_s_val_eq)>>
    impl_tac>-
      rev_full_simp_tac(srw_ss())[Abbr`rcst'`]>>
    strip_tac>>
    rev_full_simp_tac(srw_ss())[LET_THM,env_to_list_def,dec_clock_def]>>
    qabbrev_tac `envx = push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
            (st with <|permute := perm; clock := st.clock − 1|>) with
           <|locals := fromList2 (q) ; locals_size := r';
             stack_max :=
              OPTION_MAP2 MAX (push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
               (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
               (OPTION_MAP2 $+ (stack_size(push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
               (st with <|permute := perm; clock := st.clock - 1|>)).stack) r')|>`>>
    qpat_abbrev_tac `envy = (push_env y A B) with <| locals := C; locals_size := lsz; stack_max := SM;
                     clock := _ |>`>>
    mp_tac evaluate_stack_swap>>
    disch_then(qspecl_then [`q'`,`envx`] mp_tac)>>
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
    `ssa_map_ok na_2_p ssa_2_p ∧ is_alloc_var na_2_p ∧ na'' ≤ na_2_p ` by (
      drule list_next_var_rename_props>>
      impl_tac >- simp[]>>
      simp[])>>
    full_simp_tac(srw_ss())[]>>
    drule ssa_cc_trans_props>>
    impl_keep_tac>- (
      drule next_var_rename_props>>
      impl_tac >- (
        simp[]>>
        match_mp_tac (GEN_ALL ssa_map_ok_more)>>
        first_x_assum (irule_at (Pos (el 1)))>>
        full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      simp[])>>
    strip_tac>>
    FULL_CASE_TAC
    >- suspend "Call_returning_with_handler_main"
    >- suspend "Call_returning_with_handler_excepting"
    >> (
      srw_tac[][]>>qexists_tac`perm`>>full_simp_tac(srw_ss())[]>>
      first_x_assum(qspec_then`envy.stack` mp_tac)>>
      (impl_tac>- (unabbrev_all_tac>>full_simp_tac(srw_ss())[]))>>
      srw_tac[][]>>full_simp_tac(srw_ss())[])
QED

Resume ssa_cc_trans_correct[Call_returning_with_handler_excepting]:
      full_simp_tac(srw_ss())[]>>strip_tac>>
      imp_res_tac s_val_eq_LASTN_exists>>
      first_x_assum(qspecl_then[`envy.stack`,`e0'`,`e'`,`ls'`] assume_tac)>>
      rev_full_simp_tac(srw_ss())[]>>
      unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
      rpt (qpat_x_assum `LASTN A B = C` mp_tac)>>
      simp[LASTN_LENGTH_cond]>>
      rpt strip_tac>>
      full_simp_tac(srw_ss())[domain_fromAList]>>
      imp_res_tac list_rearrange_keys>>
      `set (MAP FST lss') = domain y2` by (
        qpat_x_assum`A=MAP FST lss'` (SUBST1_TAC o SYM)>>
        qpat_x_assum`set _ = set _` mp_tac>>
        qpat_x_assum`set _ = set _` mp_tac>>
        rpt (pop_assum kall_tac)>>
        simp[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList,EXISTS_PROD,domain_lookup])>>
      `domain yy1 = set (MAP FST lss)` by (
        qpat_x_assum `A = MAP FST lss` (SUBST1_TAC o SYM)>>
        full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,sort_MEM,MEM_toAList
          ,EXISTS_PROD,domain_lookup])>>
      full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
      rev_full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[domain_union,domain_fromAList]>>
      IF_CASES_TAC>-
        (qexists_tac`perm`>>full_simp_tac(srw_ss())[])>>
      `set (MAP FST e0'') = domain y1` by
        metis_tac[set_MAP_FST_toAList_domain]>>
      full_simp_tac(srw_ss()) [AC UNION_COMM UNION_ASSOC]>>
      qabbrev_tac`ssa_cut = inter ssa' (union x1 x2)`>>
      qpat_abbrev_tac`cres=r with <|locals:= A;stack := B;handler:=C|>`>>
      `ssa_locals_rel na' ssa_cut r.locals cres.locals ∧
       word_state_eq_rel r cres` by suspend "Call_returning_with_handler_excepting_byclause">>
      `ssa_locals_rel na' ssa_cut r.locals
        (set_var 2 w0 cres).locals` by
        (match_mp_tac ssa_locals_rel_ignore_set_var>>
        full_simp_tac(srw_ss())[]>>srw_tac[][]>> is_phy_var_tac)>>
      Q.SPECL_THEN [`r`,`ssa_cut`,`na'+2`,`(MAP FST (toAList (union x1 x2)))`
                   ,`(set_var 2 w0 cres)`] mp_tac
                   list_next_var_rename_move_preserve>>
      impl_tac>- (
        srw_tac[][]
        >-
          (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
          full_simp_tac(srw_ss())[]>>
          qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
          rev_full_simp_tac(srw_ss())[])
        >-
          full_simp_tac(srw_ss())[domain_fromAList,set_MAP_FST_toAList_domain,domain_union]
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
      `ssa_locals_rel na_3_p ssa_3_p res_st.locals res_rcst.locals` by (
        unabbrev_all_tac>>
        full_simp_tac(srw_ss())[next_var_rename_def,set_var_def]>>
        rpt VAR_EQ_TAC>>
        qpat_x_assum`A=union _ _` sym_sub_tac>>
        match_mp_tac ssa_locals_rel_set_var>>
        `na'' ≤ n'` by DECIDE_TAC>>
        CONJ_TAC >-
          metis_tac[ssa_locals_rel_more] >>
        CONJ_TAC >-
          metis_tac[ssa_map_ok_more] >>
        full_simp_tac(srw_ss())[every_var_def]>>
        DECIDE_TAC)>>
      first_x_assum(qspecl_then[`x''1`,`res_st`,`res_rcst`,`ssa_3_p`,`na_3_p`,`lt`] mp_tac)>>
      size_tac2>>
      impl_tac>-
        (full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`,Abbr`res_rcst`,set_var_def]>>
        full_simp_tac(srw_ss())[every_var_def,next_var_rename_def]>>srw_tac[][]>>
        rev_full_simp_tac(srw_ss())[]>>
        match_mp_tac every_var_mono>>
        HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      qspecl_then[`q'`,`push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
            (st with <|permute := perm; clock := st.clock − 1|>) with
          <| locals := fromList2 q; locals_size := r';
             stack_max :=  OPTION_MAP2 MAX (OPTION_MAP2 MAX st.stack_max
          (stack_size (StackFrame st.locals_size (toAList yy0)
            (list_rearrange (perm 0)(sort key_val_compare (toAList yy1)))
            (SOME (st.handler,x''2,x''3))::st.stack)))
        (OPTION_MAP2 $+ (stack_size (StackFrame st.locals_size (toAList yy0)
         (list_rearrange (perm 0)(sort key_val_compare (toAList yy1)))
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
    suspend "Call_returning_with_handler_excepting_tail"
QED

Resume ssa_cc_trans_correct[Call_returning_with_handler_excepting_byclause]:
        `r.stack = st'` by metis_tac[s_key_eq_trans,s_val_and_key_eq]>>
        full_simp_tac(srw_ss())[Abbr`cres`,LET_THM,ssa_locals_rel_def,state_component_equality,word_state_eq_rel_def]>>
        simp[Abbr`ssa_cut`]>>
        rpt (qpat_x_assum`_ cst = _` kall_tac)>>
        rpt (qpat_x_assum`_ rcst = _` kall_tac)>>
        rpt (qpat_x_assum`_ st = _` kall_tac)>>
        last_x_assum kall_tac>>
        CONJ_TAC  >- (
          rw[]>>
          gvs[lookup_inter,lookup_union,AllCaseEqs(),option_lookup_def,domain_union,domain_fromAList]>>
          metis_tac[domain_lookup])>>
        rpt gen_tac>>
        rename1`lookup xx`>>
        strip_tac>>
        full_simp_tac (srw_ss()) [MAP_FST_keys_SORT]>>
        `domain (fromAList lss) = domain yy1 ∧
          domain (fromAList e0) = domain yy0` by
          metis_tac[domain_fromAList,set_MAP_FST_toAList_domain]>>
        CONJ_ASM1_TAC >- (
          CONJ_ASM2_TAC >- (
            qpat_x_assum `_ ∩ _ = _` mp_tac>>
            fs[EXTENSION,domain_union]>>
            metis_tac[domain_union])>>
          gvs[lookup_union,AllCaseEqs(),domain_union]>>
          metis_tac[domain_lookup])>>
        CONJ_TAC >- (
          `xx ∈ domain (inter ssa' (union x1 x2))` by
            fs[domain_inter]>>
          pop_assum mp_tac>> simp[domain_lookup]>>
          strip_tac>>
          `v = (option_lookup ssa') xx` by full_simp_tac(srw_ss())[option_lookup_def,lookup_inter,lookup_union,AllCaseEqs()]>>
          rveq>>
          full_simp_tac(srw_ss())[lookup_fromAList,lookup_union]>>
          rename1`ALOOKUP lll xx` >>
          rename1`ALOOKUP flll (f xx)` >>
          `flll = ZIP (MAP f (MAP FST lll), MAP SND lll)` by (
            imp_res_tac key_map_implies>>
            rev_full_simp_tac(srw_ss())[]>>
            metis_tac[ZIP_MAP_FST_SND_EQ])>>
          Q.ISPECL_THEN [`MAP SND lll`, `xx`, `MAP FST lll`,`f`]
            MP_TAC $  GEN_ALL ALOOKUP_key_remap_INJ >>
          impl_tac >- (
            simp[]>>
            irule INJ_less>>
            last_x_assum (irule_at Any)>>
            fs[domain_union,domain_fromAList,SUBSET_DEF,EXTENSION]>>
            metis_tac[])>>
          strip_tac>>fs[ZIP_MAP_FST_SND_EQ]>>
          TOP_CASE_TAC>> fs[]>>
          qpat_x_assum`strong_locals_rel f (domain x1) yy0 y1` mp_tac>>
          simp[strong_locals_rel_def]>>
          fs[ALOOKUP_toAList]>>
          metis_tac[domain_lookup])>>
        strip_tac>>
        `xx < na` by (
          qpat_x_assum `every_var _ _` mp_tac >>
          fs[every_var_def,every_name_def,EVERY_MEM,set_MAP_FST_toAList_domain,domain_union] >>
          ASM_SET_TAC[]) >>
        qpat_x_assum`_ ≤ na'` mp_tac>>
        pop_assum mp_tac>>
        rpt(pop_assum kall_tac)>>
        intLib.ARITH_TAC
QED

Resume ssa_cc_trans_correct[Call_returning_with_handler_excepting_tail]:
      Cases_on`q'³'`>>fs[]>>
      Cases_on`q''`>>fs[]>>
      rename1`fix_inconsistencies prio _ _`>>
      Q.SPECL_THEN [`na_3`,`ssa_2`,`ssa_3`,`prio`] assume_tac fix_inconsistencies_correctR >>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      pop_assum (qspecl_then[`r''`,`r'³'`] mp_tac)>>
      impl_tac>-
        (metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(exc_cons,r'³')`>>fs[word_state_eq_rel_def]
QED

Resume ssa_cc_trans_correct[Call_returning_with_handler_main]:
      strip_tac>>pop_assum(qspec_then`envy.stack` mp_tac)>>
      impl_tac>-
        (unabbrev_all_tac>> simp[])>>
      strip_tac>>full_simp_tac(srw_ss())[]>>
      rev_full_simp_tac(srw_ss())[]>>
      IF_CASES_TAC>- (
        qexists_tac`perm`>>
        full_simp_tac(srw_ss())[Abbr`regs`])>>
      qspecl_then [`(y1,y2)`,`SOME (2:num,cons_exc_handler,x''2,x''3)`,
        `(rcst' with clock := st.clock-1)`,`r with stack := st'`]
        assume_tac push_env_pop_env_s_key_eq>>
      qspecl_then [`(yy0,yy1)`,`SOME (x''0,x''1,x''2,x''3)`,
         `(st with <|permute:=perm;clock := st.clock-1|>)`,`r`]
        assume_tac push_env_pop_env_s_key_eq>>
      `rcst'.clock = st.clock` by
        full_simp_tac(srw_ss())[Abbr`rcst'`]>>
      pop_assum SUBST_ALL_TAC>>
      full_simp_tac(srw_ss())[Abbr`envy`,Abbr`envx`,state_component_equality]>>
      rev_full_simp_tac(srw_ss())[]>>
      `ssa_locals_rel na' ssa_cut y.locals y'.locals ∧
       word_state_eq_rel y y'` by (
        full_simp_tac(srw_ss())[state_component_equality]>>
        `s_key_eq y.stack y'.stack` by
          metis_tac[s_key_eq_trans,s_key_eq_sym] >>
        Q.ISPECL_THEN [`y'`, `y`,  `st'`, `r`]
          assume_tac (GEN_ALL pop_env_frame) >>
        rev_full_simp_tac(srw_ss())[]>>
        rpt (qpat_x_assum`_ cst = _` kall_tac)>>
        rpt (qpat_x_assum`_ rcst = _` kall_tac)>>
        rpt (qpat_x_assum`_ st = _` kall_tac)>>
        last_x_assum kall_tac>>
        fs[ssa_locals_rel_def,Abbr`ssa_cut`]>>
        CONJ_TAC  >- (
          rpt (qpat_x_assum`A=domain _` mp_tac)>>
          fs[Abbr`f`]>>
          rpt (pop_assum kall_tac)>>
          rw[]>>
          qpat_x_assum`_ ∪ _ = _` kall_tac>>
          qpat_x_assum`_ ∪ _ = _` sym_sub_tac>>
          gvs[lookup_inter,lookup_union,AllCaseEqs(),option_lookup_def]>>
          metis_tac[domain_lookup])>>
        rpt gen_tac>>
        rename1`lookup xx`>>
        strip_tac>>
        `xx ∈ domain (union x1 x2)` by
          metis_tac[domain_lookup,UNION_COMM,domain_union]>>
        `xx ∈ domain ssa'` by metis_tac[ssa_cut_inter_lemma]>>
        rpt CONJ_TAC
        >- gvs[domain_union]
        >- (
          `xx ∈ domain (inter ssa' (union x1 x2))` by
            fs[domain_inter,domain_union]>>
          pop_assum mp_tac>> simp[domain_lookup]>>
          strip_tac>>
          `v = f xx` by full_simp_tac(srw_ss())[Abbr`f`,option_lookup_def,lookup_inter,lookup_union,AllCaseEqs()]>>
          rveq>>
          full_simp_tac(srw_ss())[lookup_fromAList,lookup_union]>>
          rename1`ALOOKUP lll xx` >>
          rename1`ALOOKUP flll (f xx)` >>
          full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
          full_simp_tac(srw_ss())[s_key_eq_def,s_val_eq_def]>>
          Cases_on`opt`>>Cases_on`opt'`>>
          full_simp_tac(srw_ss())[s_frame_key_eq_def,s_frame_val_eq_def]>>
          full_simp_tac(srw_ss())[lookup_fromAList]>>
          `flll = ZIP (MAP f (MAP FST lll), MAP SND lll)` by (
            imp_res_tac key_map_implies>>
            rev_full_simp_tac(srw_ss())[]>>
            metis_tac[ZIP_MAP_FST_SND_EQ])>>
          Q.ISPECL_THEN [`MAP SND lll`, `xx`, `MAP FST lll`,`f`]
            MP_TAC $  GEN_ALL ALOOKUP_key_remap_INJ >>
          impl_tac >- (
            simp[]>>
            irule INJ_less>>
            last_x_assum (irule_at Any)>>
            fs[domain_union,domain_fromAList,SUBSET_DEF,EXTENSION]>>
            metis_tac[])>>
          strip_tac>>fs[ZIP_MAP_FST_SND_EQ]>>
          TOP_CASE_TAC>> fs[]>>
          qpat_x_assum`strong_locals_rel f (domain x1) yy0 y1` mp_tac>>
          simp[strong_locals_rel_def]>>
          fs[ALOOKUP_toAList]>>
          metis_tac[domain_lookup])
        >- (
          strip_tac>>
          `xx < na` by (
             qpat_x_assum `every_var _ _` mp_tac >>
             simp[every_var_def,every_name_def,EVERY_MEM,set_MAP_FST_toAList_domain] >>
             gvs[domain_union]) >>
          intLib.ARITH_TAC))>>
      full_simp_tac(srw_ss())[AC UNION_COMM UNION_ASSOC]>>
      `ssa_locals_rel na' ssa_cut y.locals
        (alist_insert regs l' y'.locals)` by (
        match_mp_tac ssa_locals_rel_ignore_list_insert>>
        full_simp_tac(srw_ss())[]>>
        rw[EVERY_MEM,Abbr`regs`,MEM_GENLIST]>>
        is_phy_var_tac)>>
      qspecl_then [`y`,`ssa_cut`,`na'+2`,`MAP FST (toAList (union x1 x2))`
                   ,`(set_vars regs l' y')`] mp_tac
                   list_next_var_rename_move_preserve>>
      impl_tac>- (
        rw[set_vars_def]
        >-
          (match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
          full_simp_tac(srw_ss())[]>>
          qexists_tac`na'`>>full_simp_tac(srw_ss())[]>>
          rev_full_simp_tac(srw_ss())[])
        >- (
          full_simp_tac(srw_ss())[Abbr`ls`,set_MAP_FST_toAList_domain,domain_union,SUBSET_DEF,EXTENSION]>>
          metis_tac[])
        >-
          full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList,Abbr`ls`]
        >-
          (`na' ≤ na'+2`by DECIDE_TAC>>
          metis_tac[ssa_map_ok_more,Abbr`ssa_cut`,ssa_map_ok_inter])
        >>
          full_simp_tac(srw_ss())[word_state_eq_rel_def,set_var_def])>>
      LET_ELIM_TAC>>
      full_simp_tac(srw_ss())[Abbr`cons_ret_handler`,Abbr`mov_ret_handler`,evaluate_def]>>
      `LENGTH ret' = LENGTH regs ∧
        ALL_DISTINCT ret'` by (
        drule list_next_var_rename_lemma_1>>
        rw[Abbr`regs`,LENGTH_COUNT_LIST])>>
      rev_full_simp_tac(srw_ss())[LET_THM,MAP_ZIP,set_vars_def]>>
      `get_vars regs rcst'' = SOME l'` by (
        `¬ is_phy_var (na'+2)` by
          metis_tac[is_stack_var_flip,convention_partitions]>>
        first_x_assum drule>>
        strip_tac>>
        irule get_vars_eq_alist_insert>>
        rw[Abbr`regs`]
        >- (
          qexists_tac`y'.locals`>>
          rw[MEM_GENLIST]>>
          first_x_assum irule>>
          is_phy_var_tac)>>
        rw[ALL_DISTINCT_GENLIST])>>
      full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
      qabbrev_tac`res_st = (set_vars x0 l' y)`>>
      qpat_abbrev_tac`res_rcst = rcst'' with locals:=A`>>
      `ssa_locals_rel na_2_p ssa_2_p res_st.locals res_rcst.locals` by (
        unabbrev_all_tac>>
        simp[set_vars_def]>>
        irule ssa_locals_rel_list_next_var_rename>>
        simp[]>>
        first_x_assum (irule_at Any)>>
        simp[]>>
        CONJ_TAC >-
          metis_tac[convention_partitions]>>
        irule EVERY_MONOTONIC>>
        full_simp_tac (srw_ss()) [every_var_def]>>
        first_x_assum (irule_at Any)>>
        simp[])>>
      first_x_assum(qspecl_then[`x3`,`res_st`,`res_rcst`,`ssa_2_p`,`na_2_p`,`lt`] mp_tac)>>
      size_tac2>>
      impl_tac>-(
        full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`res_st`,Abbr`res_rcst`,set_var_def]>>
        drule list_next_var_rename_props>>
        impl_tac >- simp[]>>
        simp[]>>
        full_simp_tac(srw_ss())[every_var_def,next_var_rename_def]>>srw_tac[][]>>
        qpat_x_assum`every_var _ x3` mp_tac>>
        qspecl_then [`λx. x < na`, `x3`, `λx. x < na_2_p`] mp_tac wordConvsTheory.every_var_mono>>
        rw[]>>
        first_x_assum match_mp_tac>>
        rw[]>>
        DECIDE_TAC)>>
      srw_tac[][]>>
      qspecl_then[`q'`,`push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
                  (st with <|permute := perm; clock := st.clock − 1|>) with
                <|locals := fromList2 q; locals_size := r';
                  stack_max := OPTION_MAP2 MAX (push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))
                    (st with <|permute := perm; clock := st.clock - 1|>)).stack_max
                    (OPTION_MAP2 $+ (stack_size (push_env (yy0,yy1) (SOME (x''0,x''1,x''2,x''3))  (st with
                     <|permute := perm; clock := st.clock - 1|>)).stack) r')|>` ,`perm'`]
            assume_tac permute_swap_lemma>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      qexists_tac`λn. if n = 0:num then perm 0 else perm'' (n-1)`>>
      qpat_abbrev_tac `env1 = push_env A B C with <|locals := D ; locals_size := Ls; stack_max := SM|>`>>
      qpat_x_assum `evaluate _ = (SOME (Result _ _), _ with permute := _)` mp_tac>>
      qpat_abbrev_tac `env2 = push_env A B C with
                    <|locals:=D; locals_size := Ls; stack_max := SM ; permute:=E|>`>>
      strip_tac>>
      `env1 = env2` by
        (unabbrev_all_tac>>
        simp[push_env_def,LET_THM,env_to_list_def ,state_component_equality,FUN_EQ_THM,
             stack_size_def, stack_size_frame_def])>>
      full_simp_tac(srw_ss())[Abbr`regs`]>>
      rev_full_simp_tac(srw_ss())[set_vars_def,Abbr`res_st`]>>
      qspecl_then [`na_3`,`ssa_2`,`ssa_3`] mp_tac fix_inconsistencies_correctL>>
      impl_tac>- (
        simp[]>>
        `na_2 ≤ na_3` by (
          drule next_var_rename_props>>
          impl_tac >- (rw[]>> metis_tac[ssa_map_ok_more])>>
          rw[])>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      strip_tac>>
      Cases_on`evaluate (x3, y with <|locals := alist_insert x0 l' (union (fromAList l'') (fromAList (toAList yy0))); permute := perm'|>)`>>fs[]>>
      Cases_on`q''`>>fs[]>>
      Cases_on`evaluate (ren_ret_handler, rcst'' with locals := alist_insert ret' l' rcst''.locals)`>>fs[]>>
      Cases_on`q''`>>fs[]>>
      rfs[Abbr`res_rcst`]>>
      qpat_x_assum`_ (evaluate (ren_ret_handler, rcst'' with locals := alist_insert ret' l' rcst''.locals))` mp_tac>>
      simp[]>>strip_tac>>
      `na_2 ≤ na_3` by (
        `na_2 ≤ na_3_p` by (
          qpat_x_assum`next_var_rename x''0 ssa'' na_2 = _` mp_tac>>
          simp[next_var_rename_def]>>rw[])>>
        `(na_3_p:num) ≤ na_3` by full_simp_tac(srw_ss())[]>>
        DECIDE_TAC)>>
      `ssa_locals_rel na_3 ssa_2 r''.locals r'³'.locals` by (
        match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
        qexists_tac`na_2`>>simp[])>>
      qpat_x_assum`∀stL cstL. ssa_locals_rel na_3 ssa_2 _ _ ⇒ _` (qspecl_then[`r''`,`r'³'`] mp_tac)>>
      simp[]>>
      Cases_on`evaluate(ret_cons,r'³')`>>fs[word_state_eq_rel_def]>>
      rw[]>>fs[]
QED

Resume ssa_cc_trans_correct[Seq]:
    srw_tac[][]>>full_simp_tac(srw_ss())[evaluate_def,ssa_cc_trans_def,LET_THM]>>
    last_assum(qspecl_then[`p`,`st`,`cst`,`ssa`,`na`,`lt`] mp_tac)>>
    size_tac2>>
    impl_tac>>full_simp_tac(srw_ss())[every_var_def]>>srw_tac[][]>>
    Cases_on`ssa_cc_trans p ssa na lt`>>Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    Cases_on`ssa_cc_trans p0 q' r' lt`>>Cases_on`r`>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def,LET_THM]>>
    Cases_on`evaluate(p,st with permute:=perm')`>>full_simp_tac(srw_ss())[]
    >- (qexists_tac`perm'`>>full_simp_tac(srw_ss())[]) >>
    Cases_on`evaluate(q,cst)`>>full_simp_tac(srw_ss())[]>>
    reverse (Cases_on`q'''''`)
    >-
      (qexists_tac`perm'`>>srw_tac[][]>>full_simp_tac(srw_ss())[]>>
       Cases_on`x`>>fs[]>>
       every_case_tac>>fs[]>>
       imp_res_tac ssa_cc_trans_props>>
       metis_tac[ssa_locals_rel_more])
    >>
    full_simp_tac(srw_ss())[]>>
    first_assum(qspecl_then[`p0`,`r`,`r'''`,`q'`,`r'`,`lt`] mp_tac)>>
    size_tac2>>
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
    qexists_tac`perm'''`>>srw_tac[][]>>full_simp_tac(srw_ss())[]
QED

Resume ssa_cc_trans_correct[If]:
    qpat_abbrev_tac `A = ssa_cc_trans B C D E` >>
    PairCases_on`A`>>simp[]>>
    pop_assum(mp_tac o SYM o SIMP_RULE std_ss[markerTheory.Abbrev_def]) >>
    full_simp_tac(srw_ss())[evaluate_def,ssa_cc_trans_def]>>
    LET_ELIM_TAC>>fs[]>>
    qpat_x_assum`B = A0` sym_sub_tac>>full_simp_tac(srw_ss())[evaluate_def]>>
    Cases_on `get_var n st` >> gvs [] >>
    Cases_on `get_var_imm r st` >> gvs [] >>
    imp_res_tac ssa_locals_rel_get_var >> gvs [Abbr `r1'`] >>
    `get_var_imm ri' cst = SOME x'` by (
      Cases_on `r` >> gvs [Abbr `ri'`, get_var_imm_def] >>
      metis_tac [ssa_locals_rel_get_var]) >>
    gvs [] >>
    Cases_on `word_cmp c x x'` >> gvs [] >>
    Cases_on `x''` >> gvs []
    >- (
      first_assum(qspecl_then[`p`,`st`,`cst`,`ssa`,`na`,`lt`] mp_tac)>>
      size_tac2>>
      impl_tac>-
        (rev_full_simp_tac(srw_ss())[]>>imp_res_tac ssa_cc_trans_props>>
        full_simp_tac(srw_ss())[every_var_def])>>
      srw_tac[][]>>
      qexists_tac`perm'`>>full_simp_tac(srw_ss())[LET_THM]>>
      Cases_on`evaluate(p,st with permute := perm')`>>
      Cases_on`evaluate(e2',cst)`>>full_simp_tac(srw_ss())[]>>
      gvs[] >>
      Cases_on`q`>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
      Q.SPECL_THEN [`na3`,`ssa2`,`ssa3`] mp_tac fix_inconsistencies_correctL>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_map_ok_more])>>
      rev_full_simp_tac(srw_ss())[LET_THM]>>
      disch_then (qspecl_then[`r'`,`r''`] mp_tac)>>
      impl_tac>-
        (imp_res_tac ssa_cc_trans_props>>
        metis_tac[ssa_locals_rel_more,ssa_map_ok_more])>>
      Cases_on`evaluate(e2_cons,r'')`>>full_simp_tac(srw_ss())[word_state_eq_rel_def])
    >>
      first_assum(qspecl_then[`p0`,`st`,`cst`,`ssa`,`na2`,`lt`] mp_tac)>>
      size_tac2>>
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
      Cases_on`evaluate(e3_cons,r'')`>>full_simp_tac(srw_ss())[word_state_eq_rel_def]
QED

Resume ssa_cc_trans_correct[Alloc]:
    last_x_assum kall_tac>>
    qabbrev_tac`A = ssa_cc_trans (Alloc n p) ssa na lt`>>
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
    PairCases_on`p`>>
    PairCases_on`x`>>
    `INJ (option_lookup ssa') (domain p0 UNION domain p1 ) 𝕌(:num)` by(
      rw[INJ_DEF] >> (
        drule list_next_var_rename_move_distinct>>
        disch_then match_mp_tac>>
        simp[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList,toAList_domain,Abbr`all_names`,domain_union])) >>
    drule_at Any cut_envs_lemma>>
    disch_then (qspecl_then [`rcstlocs`,`option_lookup ssa'`] mp_tac)>>
    impl_tac>- (
      gvs[ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[]
      >- (
        drule INJ_UNION >> simp[])
      >- (
        drule INJ_UNION >> simp[])
      >>
        full_simp_tac(srw_ss())[option_lookup_def,domain_lookup,Abbr`rcstlocs`,lookup_insert]>>
        last_x_assum kall_tac>>
        res_tac>>
        full_simp_tac(srw_ss())[ssa_map_ok_def]>>
        first_x_assum(qspecl_then [`n'`,`v'`] mp_tac)>>
        simp[]>>
        qpat_x_assum`A=SOME v'` SUBST_ALL_TAC>>full_simp_tac(srw_ss())[]>>
        srw_tac[][is_phy_var_def])>>
    srw_tac[][]>>full_simp_tac(srw_ss())[set_store_def]>>
    qpat_abbrev_tac`non = NONE`>>
    Q.ISPECL_THEN [`y1`,`y2`,`x0`,`x1`,`st with store:= st.store |+ (AllocSize,Word c)`
    ,`option_lookup ssa'`,`rcst with store:= rcst.store |+ (AllocSize,Word c)`
    ,`non`,`non`,`rcst.permute`] assume_tac (GEN_ALL push_env_s_val_eq)>>
    rev_full_simp_tac(srw_ss())[word_state_eq_rel_def,Abbr`non`]>>
    qexists_tac`perm`>>full_simp_tac(srw_ss())[]>>
    qpat_abbrev_tac `st' = push_env x NONE A`>>
    qpat_abbrev_tac `cst' = push_env y NONE B`>>
    Cases_on`gc st'`>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`st'`,`cst'`,`x`] mp_tac gc_s_val_eq_gen>>
    impl_keep_tac>-
      (unabbrev_all_tac>>
      full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def,word_state_eq_rel_def,
        stack_size_def, stack_size_frame_def]>>
      rev_full_simp_tac(srw_ss())[])>>
    srw_tac[][]>>simp[]>>
    unabbrev_all_tac>>
    imp_res_tac gc_frame>>
    Cases_on`pop_env x`>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
    imp_res_tac push_env_pop_env_s_key_eq>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[]>>
    imp_res_tac gc_s_key_eq>>
    full_simp_tac(srw_ss())[push_env_def,LET_THM,env_to_list_def]>>
    rpt (qpat_x_assum `s_key_eq A B` mp_tac)>>
    qpat_abbrev_tac `lsA = list_rearrange (rcst.permute 0)
        (sort key_val_compare ( (toAList y2)))`>>
    qpat_abbrev_tac `lsB = list_rearrange (perm 0)
        (sort key_val_compare ( (toAList x1)))`>>
    ntac 4 strip_tac>>
    Q.ISPECL_THEN [`x.stack`,`y`,`t'`,`NONE:(num#num#num) option`,
      `rcst.locals_size`,`toAList y1`,`lsA`,`rcst.stack`]
      mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
    impl_tac
    >-
      (full_simp_tac(srw_ss())[]>>metis_tac[s_key_eq_sym,s_val_eq_sym])>>
    strip_tac>>full_simp_tac(srw_ss())[]>>
    Q.ISPECL_THEN [`t'.stack`,`x'`,`x`,`NONE:(num#num#num) option`,
      `st.locals_size`, `toAList x0`,`lsB`,`st.stack`]
      mp_tac (GEN_ALL s_key_eq_val_eq_pop_env)>>
    impl_tac
    >-
      (full_simp_tac(srw_ss())[]>>
      metis_tac[s_key_eq_sym,s_val_eq_sym])>>
    srw_tac[][]>>
    `LENGTH ls' = LENGTH l ∧ LENGTH lsB = LENGTH l` by
      metis_tac[s_key_eq_def,s_frame_key_eq_def,
                s_val_eq_def,LENGTH_MAP,s_frame_val_eq_def]>>
    `x'.stack = ls /\ y.stack = ls /\ s_key_eq ls st.stack /\ rest = ls ` by
       (rpt $ irule_at Any s_val_and_key_eq >>
        rpt $ PRED_ASSUM is_forall (K ALL_TAC) >>
        rpt $ PRED_ASSUM is_imp (K ALL_TAC) >>
        gvs[s_key_eq_def,s_val_eq_def,s_key_eq_refl,s_val_eq_refl] >>
        rpt (qpat_x_assum `s_key_eq _ _` mp_tac) >>
        rpt (qpat_x_assum `s_val_eq _ _` mp_tac) >>
        POP_ASSUM_LIST $ K ALL_TAC >>
        metis_tac[s_key_eq_trans,s_key_eq_sym,s_val_eq_trans,s_val_eq_sym]) >>
    POP_ASSUM SUBST_ALL_TAC >>
    `lsz' = (toAList x0)`
       by fs[s_key_eq_def,s_frame_key_eq_def2] >>
    POP_ASSUM SUBST_ALL_TAC >>
    (*Establish invariants about ssa_cut to use later*)
    qabbrev_tac `s = union p0 p1`>>
    qabbrev_tac `ssa_cut = inter ssa' s` >>
    `domain ssa_cut = domain x0 ∪ domain x1` by
      (full_simp_tac(srw_ss())[EXTENSION,Abbr`ssa_cut`,domain_inter,Abbr`s`,domain_union]>>
      drule cut_envs_domain_SUBSET>>
      srw_tac[][EQ_IMP_THM]>>
      full_simp_tac(srw_ss())[SUBSET_DEF]>>
      last_x_assum kall_tac >>
      full_simp_tac(srw_ss())[ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒
      lookup x ssa' = SOME y` by (
      srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`,lookup_inter]>>
      pop_assum mp_tac>>simp[AllCaseEqs()])>>
    `domain x'.locals = domain x0 ∪ domain x1` by (
      full_simp_tac(srw_ss())[domain_fromAList,MAP_ZIP,domain_union]>>
      full_simp_tac(srw_ss())[EXTENSION,Abbr`lsB`]>>
      full_simp_tac(srw_ss())[MEM_MAP,mem_list_rearrange,sort_MEM]>>
      srw_tac[][]>>
      full_simp_tac(srw_ss())[EXISTS_PROD,MEM_toAList,domain_lookup]>>
      metis_tac[])>>
    `ssa_locals_rel na' ssa_cut x'.locals y.locals ∧
      word_state_eq_rel x' y` by (
      CONJ_TAC
      >- (
        rpt (qpat_x_assum`_ cst = _` kall_tac)>>
        rpt (qpat_x_assum`_ rcst = _` kall_tac)>>
        rpt (qpat_x_assum`_ x = _` kall_tac)>>
        rpt (qpat_x_assum`_ t' = _` kall_tac)>>
        fs[ssa_locals_rel_def,Abbr`ssa_cut`,Abbr`s`]>>
        CONJ_TAC
        >- (
          qpat_x_assum`A=domain _` sym_sub_tac>>
          simp[lookup_inter,AllCaseEqs(),lookup_union,domain_lookup]>>
          simp[option_lookup_def,AllCaseEqs()]>>
          metis_tac[])>>
        rpt gen_tac>>
        rename1`lookup xx`>>
        `set (MAP FST lsB) = domain x1` by
          simp[Abbr`lsB`, MAP_FST_list_rearrange_keys_SORT]>>
        strip_tac >>
        `xx ∈ ((domain x0) UNION (domain x1))`
             by ( imp_res_tac$  GSYM domain_lookup >>
               fs[domain_union,domain_fromAList] >>
               rfs[MAP_ZIP] >> fs[set_MAP_FST_toAList_domain] >>metis_tac[]) >>
        CONJ_TAC >- (ASM_SET_TAC[]) >>
        reverse CONJ_TAC >- (
          disch_tac >>
          `xx < na`
            by (
             qpat_x_assum `every_var _ _` mp_tac >>
             simp[every_var_def,every_name_def,EVERY_MEM,set_MAP_FST_toAList_domain] >>
             ASM_SET_TAC[]) >>
          intLib.ARITH_TAC) >>
        Q.ISPECL_THEN [`MAP SND l`, `xx`, `MAP FST lsB`,`option_lookup ssa'`]
          MP_TAC $  GEN_ALL ALOOKUP_key_remap_INJ >>
        impl_tac >-
          (simp[] >>
          irule INJ_SUBSET >>
          Q.EXISTS_TAC `(domain p0 UNION domain p1)` >>
          first_x_assum (irule_at (Pos last)) >>
          simp[] >> ASM_SET_TAC[]) >>
        disch_tac >>
        Q.PAT_X_ASSUM `lookup xx _ = SOME _` mp_tac >>
        simp_tac(srw_ss())[lookup_union,lookup_fromAList] >>
        qmatch_asmsub_abbrev_tac `ALOOKUP  A B = ALOOKUP C D` >>
        disch_tac >>
        qmatch_goalsub_abbrev_tac `ALOOKUP C' D'` >>
        `C = C' /\ D = D'`  by (
          simp[Abbr`C`,Abbr`C'`,Abbr`D`,Abbr`D'`] >>
          simp[SimpRHS,Once $GSYM ZIP_MAP_FST_SND_EQ ] >>
          simp[] >>
          CONJ_TAC >-
            (`MAP FST l = MAP FST (MAP (λ(x,y). (option_lookup ssa' x,y)) lsB)`
                by fs[s_key_eq_def,s_frame_key_eq_def2] >>
            POP_ASSUM SUBST_ALL_TAC >>
            simp[MAP_MAP_o,ELIM_UNCURRY,o_DEF]) >>
          qmatch_goalsub_abbrev_tac `_ = THE C`>>
          `?y. C = SOME y`
             by (
               simp[Abbr`C`,Abbr`B`,Abbr`A`,GSYM domain_lookup] >>
               ASM_SET_TAC[domain_union]) >>
          `lookup B ssa' = C`
              by (simp[Abbr`C`] >> METIS_TAC[]) >>
          simp_tac(srw_ss())[option_lookup_def,Abbr`C`] >>
          ASM_REWRITE_TAC[] >>
          simp_tac(srw_ss())[]) >>
        ntac 2 $ POP_ASSUM (SUBST_TAC o single o GSYM) >>
        ntac 2 $ POP_ASSUM $ K ALL_TAC >>
        POP_ASSUM MP_TAC >>
        simp[AllCaseEqs(),DISJ_IMP_THM] >>
        MAP_EVERY Q.UNABBREV_TAC [`A`,`B`,`C`,`D`] >>
        strip_tac >>
        qpat_x_assum `strong_locals_rel (option_lookup ssa') (domain p0) x0 y1` mp_tac>>
        simp[strong_locals_rel_def] >>
        disch_then (qspec_then `xx` mp_tac) >>
        full_simp_tac(bool_ss)[ALOOKUP_toAList] >>
        simp_tac(srw_ss())[] >>
        impl_tac >- (
          EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac (iffLR ALOOKUP_NONE))) >>
          simp[MAP_ZIP] >>
          ASM_SET_TAC[]) >>
        simp_tac(srw_ss())[])
      >-
        (full_simp_tac(srw_ss())[word_state_eq_rel_def,pop_env_def]>>
        rev_full_simp_tac(srw_ss())[state_component_equality, stack_size_def, stack_size_frame_def]>>
        metis_tac[s_val_and_key_eq,s_key_eq_sym,s_val_eq_sym,s_key_eq_trans]))>>
    ntac 3 (qpat_x_assum `A = (B,C)` mp_tac)>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[word_state_eq_rel_def,has_space_def,get_store_def]>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[]>>
    Cases_on`FLOOKUP x'.store NextFree`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[] >>
    Cases_on`FLOOKUP x'.store TriggerGC`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x''`>>full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    ntac 2 strip_tac>> rveq >> full_simp_tac(srw_ss())[call_env_def,flush_state_def]
    >- (
      Q.SPECL_THEN [`rst`,`ssa_cut`,`na'+2`,`(MAP FST (toAList s))`
                   ,`s1`] mp_tac list_next_var_rename_move_preserve>>
      impl_tac>-(
        srw_tac[][]
        >-
          (rev_full_simp_tac(srw_ss())[]>>
          match_mp_tac (GEN_ALL ssa_locals_rel_more)>>
          full_simp_tac(srw_ss())[]>>
          qpat_x_assum `A = union (fromAList _) _` sym_sub_tac>>
          HINT_EXISTS_TAC>>full_simp_tac(srw_ss())[])
        >-
          (srw_tac[][SUBSET_DEF]>>
          full_simp_tac(srw_ss())[MEM_MAP,Abbr`s`]>>
          Cases_on`y`>>
          full_simp_tac(srw_ss())[MEM_toAList,domain_lookup,lookup_union]>>
          pop_assum mp_tac>>simp[AllCaseEqs()]>>
          metis_tac[])
        >-
          (unabbrev_all_tac>>match_mp_tac ssa_map_ok_inter>>
          match_mp_tac (GEN_ALL ssa_map_ok_more)>>
          HINT_EXISTS_TAC>>
          full_simp_tac(srw_ss())[]>>DECIDE_TAC)
        >>
          full_simp_tac(srw_ss())[word_state_eq_rel_def])>>
      simp[] >>
      srw_tac[][]>>full_simp_tac(srw_ss())[word_state_eq_rel_def]) >>
    full_simp_tac(srw_ss())[word_state_eq_rel_def, stack_size_def, stack_size_frame_def] >>
    rw[state_component_equality]
QED

Resume ssa_cc_trans_correct[StoreConsts]:
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
      ssa_locals_rel_ignore_insert]
QED

Resume ssa_cc_trans_correct[Raise]:
    exists_tac>>fs[]>>
    Cases_on`get_var n st`>>imp_res_tac ssa_locals_rel_get_var>>
    full_simp_tac(srw_ss())[get_vars_def,get_var_def,set_vars_def,lookup_alist_insert]>>
    full_simp_tac(srw_ss())[jump_exc_def]>>EVERY_CASE_TAC>>full_simp_tac(srw_ss())[]>> gvs[]
QED

Resume ssa_cc_trans_correct[Return]:
    exists_tac>>fs[]>>
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
    DEP_REWRITE_TAC[get_vars_set_vars_eq] >>
    fs[ALL_DISTINCT_GENLIST,LENGTH_GENLIST] >>
    CONJ_TAC >-
    (imp_res_tac get_vars_length_lemma >> gvs[]) >>
    fs[flush_state_def]
QED

Resume ssa_cc_trans_correct[Tick]:
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[call_env_def, flush_state_def,dec_clock_def]
QED

Resume ssa_cc_trans_correct[OpCurrHeap]:
    last_x_assum kall_tac>>
    exists_tac>>
    EVERY_CASE_TAC>>full_simp_tac(srw_ss())[next_var_rename_def]>>
    imp_res_tac ssa_locals_rel_get_var>>
    imp_res_tac ssa_cc_trans_exp_correct>>full_simp_tac(srw_ss())[word_state_eq_rel_def]>>
    rev_full_simp_tac(srw_ss())[evaluate_def]>>
    fs[set_var_def,set_store_def,ssa_cc_trans_exp_def]>>
    match_mp_tac ssa_locals_rel_set_var>>
    full_simp_tac(srw_ss())[every_var_def]
QED

Resume ssa_cc_trans_correct[LocValue]:
    exp_tac2
QED

Resume ssa_cc_trans_correct[Install]:
    qexists_tac`cst.permute`>>
    fs[evaluate_def,word_state_eq_rel_def,ssa_cc_trans_def]>>
    last_x_assum kall_tac>>
    PairCases_on`p`>>
    pairarg_tac>>fs[case_eq_thms]>>
    pop_assum mp_tac>>pairarg_tac>>fs[]>>
    strip_tac>>
    pop_assum mp_tac >>
    rpt (TOP_CASE_TAC >> gvs []) >>
    qmatch_goalsub_abbrev_tac ‘rstt = rst ⇒ _’ >> rw [] >>
    pairarg_tac>>fs[]>>
    pop_assum mp_tac>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    qmatch_asmsub_abbrev_tac`MAP FST (toAList s)`>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`MAP FST (toAList s)`,`cst`] mp_tac list_next_var_rename_move_preserve>>
    impl_keep_tac>- (
      srw_tac[][word_state_eq_rel_def]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >- (
        fs[cut_env_def,AllCaseEqs()]>>
        drule cut_envs_domain_SUBSET >>
        simp[Abbr`s`,toAList_domain,SUBSET_DEF,domain_union]>>
        metis_tac[])
      >-
        full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC))>>
    rw[]>>fs[]>>
    qpat_x_assum` _ = (stack_mov,_,_)` assume_tac>>
    drule (list_next_var_rename_move_props |> SIMP_RULE std_ss[Once CONJ_COMM] |> SIMP_RULE std_ss [ GSYM AND_IMP_INTRO]) >>
    disch_then drule>>
    `is_stack_var (na+2)` by fs[is_alloc_var_flip]>>
    simp[]>>strip_tac>>
    qpat_x_assum`_ (evaluate _)` mp_tac>>
    pairarg_tac>>fs[]>>
    rw[]>>
    simp[evaluate_def,get_vars_def]>>
    drule (GEN_ALL ssa_locals_rel_get_var)>>
    strip_tac>>
    res_tac>>simp[]>>
    qpat_abbrev_tac`rcst_mov = set_vars _ _ rcst`>>
    drule_at Any cut_env_lemma>>
    disch_then (qspecl_then[`rcst_mov.locals`,`option_lookup ssa''`] mp_tac)>>
    `domain p0 ∪ domain p1 = domain s` by
      simp[Abbr`s`,domain_union]>>
    simp[]>>
    impl_keep_tac >- (
      fs[ssa_locals_rel_def,strong_locals_rel_def]>>
      rw[INJ_DEF]
      >-
        ((* use property of list_next_var_rename_move *)
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
    `domain ssa_cut = domain env` by (
      fs[Abbr`ssa_cut`,domain_union]>>
      irule SUBSET_INTER2>>
      fs[SUBSET_DEF,toAList_domain,ssa_locals_rel_def]>>
      metis_tac[domain_lookup])>>
    `ssa_locals_rel na''' ssa''' rst.locals rcstt.locals ∧ word_state_eq_rel rst rcstt` by
      (qpat_x_assum`Abbrev(rst=_)` mp_tac>>
      simp[markerTheory.Abbrev_def]>>
      disch_then (SUBST_ALL_TAC)>>
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
      conj_tac>-
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
        qpat_x_assum`_ ∪ _ = domain s` sym_sub_tac>>
        fs[]>>
        last_x_assum drule>>
        simp[])>>
    drule list_next_var_rename_move_preserve >>
    disch_then(qspecl_then[`MAP FST (toAList s)`] mp_tac)>>
    simp[]>>
    impl_tac>-
      (fs[Abbr`s`,Abbr `rst`, next_var_rename_def,SUBSET_DEF,toAList_domain,domain_union]>>rw[]>>
      `na''+6 = na''+2+4` by fs[]>>
      pop_assum SUBST1_TAC>>
      match_mp_tac ssa_map_ok_extend>>
      reverse conj_tac>-
        metis_tac[convention_partitions,is_stack_var_flip]>>
      simp[Abbr`ssa_cut`]>>
      match_mp_tac ssa_map_ok_inter>>
      match_mp_tac (GEN_ALL ssa_map_ok_more)>>
      asm_exists_tac>>fs[])>>
    pairarg_tac>>fs[word_state_eq_rel_def]
QED

Resume ssa_cc_trans_correct[CodeBufferWrite]:
    exp_tac2
QED

Resume ssa_cc_trans_correct[DataBufferWrite]:
    exp_tac2
QED

Resume ssa_cc_trans_correct[FFI]:
    (*FFI*)
    exists_tac>>
    last_x_assum kall_tac>>
    rename1 ‘FFI s n n0 n1 n2 p’>>
    qabbrev_tac`A = ssa_cc_trans (FFI s n n0 n1 n2 p) ssa na lt`>>
    PairCases_on`p`>>
    PairCases_on`A`>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>
    pop_assum mp_tac>>
    LET_ELIM_TAC>>full_simp_tac(srw_ss())[]>>
    full_simp_tac(srw_ss())[evaluate_def]>>
    Cases_on`get_var n0 st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var n st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var n2 st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`get_var n1 st`>>full_simp_tac(srw_ss())[]>>
    Cases_on`x`>>full_simp_tac(srw_ss())[]>>
    Cases_on`cut_env (p0,p1) st.locals`>>full_simp_tac(srw_ss())[]>>
    FULL_CASE_TAC>>full_simp_tac(srw_ss())[LET_THM]>>
    FULL_CASE_TAC>>fs[LET_THM]>>
    Q.SPECL_THEN [`st`,`ssa`,`na+2`,`ls`,`cst`] mp_tac list_next_var_rename_move_preserve>>
    impl_keep_tac>- (
      srw_tac[][word_state_eq_rel_def]
      >-
        (match_mp_tac ssa_locals_rel_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC)
      >- (
        unabbrev_all_tac>>
        fs[cut_env_def,AllCaseEqs()]>>
        drule cut_envs_domain_SUBSET >>
        simp[toAList_domain,SUBSET_DEF,domain_union]>>
        metis_tac[])
      >-
        full_simp_tac(srw_ss())[Abbr`ls`,ALL_DISTINCT_MAP_FST_toAList]
      >-
        (match_mp_tac ssa_map_ok_more>>
        full_simp_tac(srw_ss())[]>>DECIDE_TAC))>>
    LET_ELIM_TAC>>
    qpat_x_assum`A=A0` sym_sub_tac>>
    full_simp_tac(srw_ss())[Abbr`prog`,evaluate_def,LET_THM]>>
    srw_tac[][]>>
    `get_vars [cptr1; clen1; cptr2; clen2] rcst = SOME [Word c';Word c;Word c''';Word c'']` by
      (unabbrev_all_tac>>full_simp_tac(srw_ss())[get_vars_def]>>
      imp_res_tac ssa_locals_rel_get_var>>full_simp_tac(srw_ss())[get_var_def])>>
    qabbrev_tac`f = option_lookup ssa'`>>
    Q.ISPECL_THEN [`ls`,`ssa`,`na+2`,`mov`,`ssa'`,`na'`] assume_tac list_next_var_rename_move_props>>
    `is_stack_var (na+2)` by full_simp_tac(srw_ss())[is_alloc_var_flip]>>
    rev_full_simp_tac(srw_ss())[]>>full_simp_tac(srw_ss())[set_vars_def,alist_insert_def]>>
    qpat_abbrev_tac `rcstlocs = insert 2 A (insert 4 B (insert 6 C (insert 8 D (rcst.locals))))`>>
    full_simp_tac(srw_ss())[get_var_def]>>
    `lookup 8 rcstlocs = SOME (Word c'') ∧
     lookup 6 rcstlocs = SOME (Word c''') ∧
     lookup 4 rcstlocs = SOME (Word c) ∧
     lookup 2 rcstlocs = SOME (Word c')` by
      full_simp_tac(srw_ss())[Abbr`rcstlocs`,lookup_insert]>>
    full_simp_tac(srw_ss())[]>>
    drule_at Any cut_env_lemma>>
    disch_then (qspecl_then[`rcstlocs`,`f`] mp_tac)>>
    `domain p0 ∪ domain p1 = domain all_names` by
      simp[Abbr`all_names`,domain_union]>>
    simp[]>>
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
    `domain ssa_cut = domain x` by (
      fs[Abbr`ssa_cut`,domain_union,cut_env_def,AllCaseEqs()]>>
      drule cut_envs_domain_SUBSET>>
      fs[SUBSET_DEF,toAList_domain,ssa_locals_rel_def,EXTENSION]>>
      metis_tac[domain_lookup])>>
    `∀x y. lookup x ssa_cut = SOME y ⇒ lookup x ssa' = SOME y` by
       (srw_tac[][]>>full_simp_tac(srw_ss())[Abbr`ssa_cut`,lookup_inter]>>
       gvs[AllCaseEqs()])>>
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
         (`x''' ∈ domain all_names` by metis_tac[domain_lookup]>>
         full_simp_tac(srw_ss())[every_var_def,every_name_def,EVERY_MEM,toAList_domain]>>
         qpat_x_assum`_ ∪ _ = domain all_names` sym_sub_tac>>
         fs[]>>
         res_tac>>
         DECIDE_TAC))>>
     Q.SPECL_THEN [`rst`,`inter ssa' all_names`,`na'+2`,`(MAP FST (toAList all_names))`
                    ,`rcstt`] mp_tac list_next_var_rename_move_preserve>>
     impl_tac>- (
       srw_tac[][]
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
     Cases_on`evaluate(ret_mov,rcstt)`>>unabbrev_all_tac>>full_simp_tac(srw_ss())[state_component_equality,word_state_eq_rel_def]
QED

Resume ssa_cc_trans_correct[ShareInst]:
    exists_tac >>
    pairarg_tac >>
    simp[] >>
    rename1`m = Store \/ m = Store8 \/ m = Store16 \/ m = Store32`>>
    qabbrev_tac `mcase = (m = Store \/ m = Store8 \/ m = Store16 \/ m = Store32)`>>
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
        oneline sh_mem_store16_def,
        oneline sh_mem_store32_def,
        markerTheory.Abbrev_def,flush_state_def,AllCaseEqs()] >>
      drule_then (drule_then assume_tac) ssa_locals_rel_get_var >>
      simp[]) >>
    impl_tac >- simp[word_state_eq_rel_def] >>
    disch_then (fn t => simp[t]) >>
    gvs[oneline share_inst_def,
      oneline sh_mem_load_def,
      oneline sh_mem_load_byte_def,
      oneline sh_mem_load16_def,
      oneline sh_mem_load32_def,
      oneline sh_mem_set_var_def,
      set_var_def,flush_state_def,AllCaseEqs(),
      markerTheory.Abbrev_def] >>
    irule ssa_locals_rel_set_var >>
    fs[every_var_def]
QED

Resume ssa_cc_trans_correct[Loop]:
  rename1 `Loop names body exit_names` >>
  qpat_x_assum `every_var _ _` mp_tac >> simp[every_var_def] >> strip_tac >>
  simp[ssa_cc_trans_def] >>
  rpt (pairarg_tac >> fs[]) >>
  drule_then drule loop_setup_correct >>
  rpt (disch_then drule) >>
  strip_tac >>
  drule evaluate_seq_collapse >>
  strip_tac >>
  qpat_x_assum `inter ssa_refreshed exit_names = ssa'` (assume_tac o GSYM) >>
  qpat_x_assum `na'' = na'` (assume_tac o GSYM) >>
  fs[] >>
  `domain names ⊆ domain ssa_refreshed ∧
   domain exit_names ⊆ domain ssa_refreshed` by (
    qpat_x_assum `domain ssa_refreshed = _` SUBST1_TAC >>
    simp[domain_union, SUBSET_DEF]) >>
  `strong_locals_rel (option_lookup ssa_refreshed) (domain names)
     st.locals rcst'.locals` by (
    rw[strong_locals_rel_def] >>
    `n ∈ domain ssa_refreshed ∧
     lookup (THE (lookup n ssa_refreshed)) rcst'.locals = SOME v` by
      (conj_asm1_tac >- fs[SUBSET_DEF] >>
       fs[ssa_locals_rel_def] >> res_tac >> simp[]) >>
    Cases_on `lookup n ssa_refreshed` >- fs[domain_lookup] >>
    fs[option_lookup_def]) >>
  qspecl_then
    [`st`, `rcst'`, `ssa_refreshed`, `na_refreshed`, `names`, `body`,
     `exit_names`, `lt`, `body'`, `ssa''`, `na''`]
    mp_tac ssa_cc_trans_Loop_helper >>
  impl_tac
  >- (rpt conj_tac >> fs[]
      >- (rpt strip_tac >>
          first_x_assum irule >> fs[SUBSET_DEF])
      >- (irule every_var_mono >>
          qexists_tac `λx. x < na` >> fs[])
      >- (irule MONO_EVERY >>
          qexists_tac `λx. x < na` >> fs[])
      >- (irule MONO_EVERY >>
          qexists_tac `λx. x < na` >> fs[])) >>
  simp[LET_DEF] >>
  disch_then (qspecl_then [`res'`, `rcst`] mp_tac) >>
  impl_tac
  >- (qpat_x_assum `Seq setup_prog _ = prog'` (assume_tac o SYM) >>
      fs[] >>
      qpat_x_assum `∀Q. evaluate (Seq _ _, _) = _` (fn th =>
        once_rewrite_tac [GSYM th]) >>
      first_x_assum ACCEPT_TAC) >>
  simp[]
QED

Resume ssa_cc_trans_correct[Break]:
  qexists_tac `cst.permute` >>
  simp[evaluate_def, ssa_cc_trans_def] >>
  Cases_on `oEL n lt` >> simp[]
  >- (simp[evaluate_def] >> gvs[word_state_eq_rel_def]) >>
  PairCases_on `x` >> simp[] >>
  `MEM (x0, x1, x2) lt` by (fs[oEL_EQ_EL, MEM_EL] >> metis_tac[]) >>
  `INJ (option_lookup x0) (domain x2) UNIV` by
    (fs[lt_ok_def, EVERY_MEM] >> res_tac >> fs[]) >>
  `∃cst'. evaluate (ssa_reconcile ssa x0 x2, cst) = (NONE, cst') ∧
          word_state_eq_rel cst cst' ∧
          strong_locals_rel (option_lookup x0) (domain x2)
            st.locals cst'.locals`
    by (match_mp_tac evaluate_ssa_reconcile >> simp[]) >>
  IF_CASES_TAC
  >- (gvs[evaluate_def, word_state_eq_rel_def]) >>
  gvs[evaluate_def, word_state_eq_rel_def]
QED

Resume ssa_cc_trans_correct[Continue]:
  qexists_tac `cst.permute` >>
  simp[evaluate_def, ssa_cc_trans_def] >>
  Cases_on `oEL n lt` >> simp[]
  >- (simp[evaluate_def] >> gvs[word_state_eq_rel_def]) >>
  PairCases_on `x` >> simp[] >>
  `MEM (x0, x1, x2) lt` by (fs[oEL_EQ_EL, MEM_EL] >> metis_tac[]) >>
  `INJ (option_lookup x0) (domain x1) UNIV` by
    (fs[lt_ok_def, EVERY_MEM] >> res_tac >> fs[]) >>
  `∃cst'. evaluate (ssa_reconcile ssa x0 x1, cst) = (NONE, cst') ∧
          word_state_eq_rel cst cst' ∧
          strong_locals_rel (option_lookup x0) (domain x1)
            st.locals cst'.locals`
    by (match_mp_tac evaluate_ssa_reconcile >> simp[]) >>
  IF_CASES_TAC
  >- (gvs[evaluate_def, word_state_eq_rel_def]) >>
  gvs[evaluate_def, word_state_eq_rel_def]
QED

Finalise ssa_cc_trans_correct ;

(*For starting up*)
Theorem setup_ssa_props[local]:
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

Theorem max_var_exp_max[local]:
  ∀exp.
    every_var_exp (λx. x≤ max_var_exp exp) exp
Proof
  ho_match_mp_tac max_var_exp_ind>>
  srw_tac[][every_var_exp_def,max_var_exp_def]>>
  full_simp_tac(srw_ss())[EVERY_MEM]>>srw_tac[][]>>res_tac>>
  match_mp_tac every_var_exp_mono>>
  first_assum $ irule_at (Pos last)>>
  srw_tac[][]>>
  irule LE_TRANS >>
  irule_at (Pos (el 2)) MAX_LIST_PROPERTY >>
  simp[MEM_MAP,PULL_EXISTS] >>
  first_x_assum (fn x => irule_at (Any) x >> first_x_assum irule)
QED

Theorem max_var_inst_max[local]:
  ∀inst.
    every_var_inst (λx. x ≤ max_var_inst inst) inst
Proof
  ho_match_mp_tac max_var_inst_ind>>
  srw_tac[][every_var_inst_def,max_var_inst_def]>>
  gvs [oneline every_var_imm_def, AllCaseEqs()]>>
  TOP_CASE_TAC >> simp []
QED

Theorem max3_eq[local]:
  !x y z. max3 x y z = MAX x (MAX y z)
Proof
  simp[MAX_DEF,max3_def]
QED

Theorem max_var_max:
    ∀prog.
    every_var (λx. x ≤ max_var prog) prog
Proof[exclude_simps = max3_def]
  ho_match_mp_tac max_var_ind>>
  rpt strip_tac
  >~[`Loop`] >- (
    full_simp_tac(std_ss)[every_var_def,max_var_def,every_name_def,max3_eq] >>
    rpt strip_tac
    >>~-([`EVERY`],
      fs[EVERY_MEM] >> srw_tac[][] >>
      every_drule MAX_LIST_PROPERTY >>
      simp[]) >>
    match_mp_tac every_var_mono>>
    first_x_assum (irule_at (Pos $ el 2)) >>
    fs[])
  >~[`Break`] >- simp[every_var_def]
  >~[`Continue`] >- simp[every_var_def]
  >~[`Call`] >- (
    full_simp_tac(std_ss)[every_var_def,max_var_def,every_name_def,max3_eq] >>
     rpt TOP_CASE_TAC >> fs[] >>
     rpt strip_tac
     >>~-([`EVERY`],
       fs[EVERY_MEM] >> srw_tac[][] >>
       every_drule MAX_LIST_PROPERTY >>
       simp[])
     >>~-([`max_var`],
       srw_tac[][] >> match_mp_tac every_var_mono>>
       first_x_assum (irule_at (Pos $ el 2)) >>
       fs[]))
  >~[`If`] >- (
    full_simp_tac(std_ss)[every_var_def,max_var_def,every_name_def,max3_eq] >>
     TOP_CASE_TAC >> simp[every_var_imm_def] >>
     (srw_tac[][] >> match_mp_tac every_var_mono>>
     TRY(HINT_EXISTS_TAC)>>TRY(qexists_tac`λx. x ≤ max_var prog`)>>
     srw_tac[][]>>
     DECIDE_TAC)) >>

  full_simp_tac(std_ss)[every_var_def,max_var_def,every_name_def,max3_eq] >>
  simp[]
  >~[`max_var_inst`] >- (metis_tac[max_var_inst_max])
  >>~-([`max_var_exp`],
    match_mp_tac every_var_exp_mono>>
    qexists_tac`λx. x ≤ max_var_exp exp`>>
    full_simp_tac(srw_ss())[max_var_exp_max]>>
    DECIDE_TAC)
  >>~[`max_var`] >- (
    srw_tac[][] >> match_mp_tac every_var_mono>>
    first_x_assum (irule_at (Pos $ el 2)) >>
    fs[])
  >>~-([`EVERY`],
    fs[EVERY_MEM] >> srw_tac[][] >>
    every_drule MAX_LIST_PROPERTY >>
    simp[])
QED

Theorem limit_var_props[local]:
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
  assume_tac arithmeticTheory.MOD_PLUS>>
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
  first_x_assum(qspecl_then [`4`,`x+(4- x MOD 4)`,`1`] assume_tac)>>
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
    | SOME (Break _) => T
    | SOME (Continue _) => T
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
  Q.ISPECL_THEN [`prog`,`st`,`cst`,`ssa`,`na`,`[]:(num num_map # num_set # num_set) list`] mp_tac ssa_cc_trans_correct>>
  impl_tac>-
    (full_simp_tac(srw_ss())[lt_ok_def]>>match_mp_tac every_var_mono>>
    HINT_EXISTS_TAC >> srw_tac[][]>>DECIDE_TAC)>>
  srw_tac[][]>>
  qexists_tac`perm'`>>srw_tac[][]>>
  full_simp_tac(srw_ss())[LET_THM]>>
  every_case_tac>>full_simp_tac(srw_ss())[]
QED

(* Prove that the ssa form sets up pre_alloc_conventions
   and preserves some syntactic conventions
*)
Theorem fake_moves_conventions[local]:
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

Theorem fix_inconsistencies_conventions[local]:
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

Theorem every_name_def2:
  every_name P t = EVERY P (MAP FST (toAList (union (FST t) (SND t))))
Proof
  simp[every_name_def] >>
  simp[EVERY_MEM,set_MAP_FST_toAList_domain,domain_union,DISJ_IMP_THM,FORALL_AND_THM]
QED

Theorem union_apply_nummaps_key[local]:
   domain (union (FST (apply_nummaps_key (f) p))
                       (SND (apply_nummaps_key (f) p))) =
   domain (apply_nummap_key (f) (union (FST p) (SND p)) )
Proof
  simp[nummaps_to_nummap] >>
  simp[domain_fromAList,domain_union] >>
  simp[MAP_MAP_o,ELIM_UNCURRY,o_ABS_R] >>
  simp[GSYM o_DEF,GSYM MAP_MAP_o] >>
  ONCE_REWRITE_TAC[LIST_TO_SET_MAP] >>
  simp[set_MAP_FST_toAList_domain] >>
  simp[domain_union]
QED

Theorem fake_seq_pre_alloc_conventions[local]:
  ∀ls. pre_alloc_conventions (FOLDR Seq Skip (MAP (λr. fake_move r) ls))
Proof
  Induct>>
  fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,
    fake_move_def,inst_arg_convention_def]
QED

Theorem fake_seq_every_inst_distinct_tar_reg[local]:
  ∀ls. every_inst distinct_tar_reg (FOLDR Seq Skip (MAP (λr. fake_move r) ls))
Proof
  Induct>>
  fs[every_inst_def,fake_move_def,distinct_tar_reg_def]
QED

Theorem fake_seq_full_inst_ok_less[local]:
  ∀c ls. full_inst_ok_less c (FOLDR Seq Skip (MAP (λr. fake_move r) ls))
Proof
  rpt strip_tac>>Induct_on`ls`>>
  fs[full_inst_ok_less_def,fake_move_def,inst_ok_less_def]
QED

Theorem loop_setup_pre_alloc_conventions[local]:
  loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed) ⇒
  pre_alloc_conventions setup_prog
Proof
  rw[loop_setup_def]>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,
    list_next_var_rename_move_def]>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  fs[every_stack_var_def,call_arg_convention_def,inst_arg_convention_def]>>
  qspec_then `fresh_pos_ls` mp_tac fake_seq_pre_alloc_conventions>>
  fs[pre_alloc_conventions_def]
QED

Theorem loop_setup_props_local[local]:
  loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed) ∧
  ssa_map_ok na ssa ∧ is_alloc_var na ⇒
  is_alloc_var na_refreshed ∧ ssa_map_ok na_refreshed ssa_refreshed ∧
  na ≤ na_refreshed
Proof
  rw[loop_setup_def]>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  drule list_next_var_rename_props>>simp[]>>strip_tac>>
  qpat_x_assum `list_next_var_rename_move _ _ _ = _` assume_tac>>
  drule list_next_var_rename_move_props>>simp[]
QED

Theorem loop_setup_every_inst_distinct_tar_reg[local]:
  loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed) ⇒
  every_inst distinct_tar_reg setup_prog
Proof
  rw[loop_setup_def]>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  fs[every_inst_def,list_next_var_rename_move_def]>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  fs[every_inst_def,distinct_tar_reg_def]>>
  qspec_then `fresh_pos_ls` mp_tac fake_seq_every_inst_distinct_tar_reg>>fs[]
QED

Theorem loop_setup_full_inst_ok_less[local]:
  loop_setup names exit_names ssa na = (setup_prog,ssa_refreshed,na_refreshed) ⇒
  full_inst_ok_less c setup_prog
Proof
  rw[loop_setup_def]>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  fs[full_inst_ok_less_def,list_next_var_rename_move_def]>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  fs[full_inst_ok_less_def,inst_ok_less_def]>>
  qspecl_then [`c`,`fresh_pos_ls`] mp_tac fake_seq_full_inst_ok_less>>fs[]
QED

(*Prove that the transform sets up arbitrary programs with
  the appropriate conventions*)
Theorem ssa_cc_trans_pre_alloc_conventions:
  ∀prog ssa na lt.
  is_alloc_var na ∧
  ssa_map_ok na ssa ⇒
  let (prog',ssa',na') = ssa_cc_trans prog ssa na lt in
  pre_alloc_conventions prog'
Proof
  full_simp_tac(srw_ss())[o_UNCURRY_R, C_UNCURRY_L, S_UNCURRY_R,LET_FORALL_ELIM',
   o_THM, o_ABS_R, C_ABS_L, C_THM,S_ABS_R,FORALL_UNCURRY]>>
  simp[PULL_FORALL,AND_IMP_INTRO,SF CONJ_ss,ssa_cc_trans_props] >>
  ho_match_mp_tac ssa_cc_trans_ind >>
  rpt strip_tac>>
  TRY (
  fs[ssa_cc_trans_def,UNCURRY_EQ] >> rveq >>
  fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def] >> NO_TAC)
  >- ( (*Inst*)
    fs[ssa_cc_trans_def,oneline ssa_cc_trans_inst_def,AllCaseEqs(),UNCURRY_EQ] >> rveq >>
    simp[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,inst_arg_convention_def])
  >- ( (*Seq*)
     fs[ssa_cc_trans_def,UNCURRY_EQ] >> rveq >>
     fs[] >>
     EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac ssa_cc_trans_props)) >>
     fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def])
  >- ( (*If*)
     fs[ssa_cc_trans_def,UNCURRY_EQ] >> rveq >>
     fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def] >>
     EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac ssa_cc_trans_props)) >>
     rename1 `fix_inconsistencies prio ssa2 ssa3 na3` >>
     Q.SPECL_THEN [`ssa2`,`ssa3`,`na3`,`prio`] mp_tac fix_inconsistencies_conventions>>
     simp[] >>
     rpt (DISCH_THEN STRIP_ASSUME_TAC) >>
     fs[] >>
     `ssa_map_ok na2 ssa` by(
        irule ssa_map_ok_more >>
        asm_exists_tac >> fs[]) >>
      fs[])
  >- ( (*Alloc*)
     fs[ssa_cc_trans_def,UNCURRY_EQ] >> rveq >>
     fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def] >>
     full_simp_tac(srw_ss())[list_next_var_rename_move_def,LET_DEF,UNCURRY_EQ] >> rveq >>
     simp[every_stack_var_def,call_arg_convention_def] >>
     simp[every_name_def2,EVERY_MEM] >>
     PURE_REWRITE_TAC[set_MAP_FST_toAList_domain] >>
     PURE_REWRITE_TAC[union_apply_nummaps_key] >>
     simp[domain_fromAList,apply_nummap_key_def] >>
     simp[MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
     simp[GSYM MAP_MAP_o,GSYM o_DEF,GSYM EVERY_MEM] >>
     qmatch_goalsub_abbrev_tac `EVERY _ ls` >>
     `ls = new_ls`
       by (
       EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_2')) >>
       rpt (impl_tac >- simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList] >>
       strip_tac) >>
       simp[Abbr`ls`] >>
       simp[MAP_EQ_f] >>
       simp[option_lookup_def,option_case_compute,IS_SOME_EXISTS]) >>
     POP_ASSUM SUBST_ALL_TAC >>
     EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_1)) >>
     simp[] >> rpt strip_tac >>
     simp[MAP_COUNT_LIST,EVERY_GENLIST] >>
     fs[is_stack_var_def,is_alloc_var_def] >>
     intLib.ARITH_TAC)
  >- ( (*Install*)
     fs[ssa_cc_trans_def,UNCURRY_EQ] >> rveq >>
     fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def] >>
     full_simp_tac(srw_ss())[list_next_var_rename_move_def,LET_DEF,UNCURRY_EQ] >> rveq >>
     simp[every_stack_var_def,call_arg_convention_def] >>
     simp[every_name_def2,EVERY_MEM] >>
     PURE_REWRITE_TAC[set_MAP_FST_toAList_domain] >>
     PURE_REWRITE_TAC[union_apply_nummaps_key] >>
     simp[domain_fromAList,apply_nummap_key_def] >>
     simp[MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
     simp[GSYM MAP_MAP_o,GSYM o_DEF,GSYM EVERY_MEM] >>
     qmatch_goalsub_abbrev_tac `EVERY _ ls` >>
     `ls = new_ls`
       by (
       EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_2')) >>
       rpt (impl_tac >- simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList] >>
       strip_tac) >>
       simp[Abbr`ls`] >>
       simp[MAP_EQ_f] >>
       simp[option_lookup_def,option_case_compute,IS_SOME_EXISTS]) >>
     POP_ASSUM SUBST_ALL_TAC >>
     EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_1)) >>
     simp[] >> rpt strip_tac >>
     simp[MAP_COUNT_LIST,EVERY_GENLIST] >>
     fs[is_stack_var_def,is_alloc_var_def] >>
     intLib.ARITH_TAC)
  >- ( (*FFI*)
     fs[ssa_cc_trans_def,UNCURRY_EQ] >> rveq >>
     fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def] >>
     full_simp_tac(srw_ss())[list_next_var_rename_move_def,LET_DEF,UNCURRY_EQ] >> rveq >>
     simp[every_stack_var_def,call_arg_convention_def] >>
     simp[every_name_def2,EVERY_MEM] >>
     PURE_REWRITE_TAC[set_MAP_FST_toAList_domain] >>
     PURE_REWRITE_TAC[union_apply_nummaps_key] >>
     simp[domain_fromAList,apply_nummap_key_def] >>
     simp[MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
     simp[GSYM MAP_MAP_o,GSYM o_DEF,GSYM EVERY_MEM] >>
     qmatch_goalsub_abbrev_tac `EVERY _ ls` >>
     `ls = new_ls`
       by (
       EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_2')) >>
       rpt (impl_tac >- simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList] >>
       strip_tac) >>
       simp[Abbr`ls`] >>
       simp[MAP_EQ_f] >>
       simp[option_lookup_def,option_case_compute,IS_SOME_EXISTS]) >>
     POP_ASSUM SUBST_ALL_TAC >>
     EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_1)) >>
     simp[] >> rpt strip_tac >>
     simp[MAP_COUNT_LIST,EVERY_GENLIST] >>
     fs[is_stack_var_def,is_alloc_var_def] >>
     intLib.ARITH_TAC)
  >- ( (*Call*)
    fs[ssa_cc_trans_def,UNCURRY_EQ] >> rveq >>
    fs[Once $ AllCaseEqs()]
    >- (
      fs[] >> rveq >>
      fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def] >>
      qspecl_then[`ret`,`ssa'''`,`na'''`] mp_tac list_next_var_rename_props >>
      EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_move_props_2)) >>
      fs[] >> rpt (DISCH_THEN STRIP_ASSUME_TAC) >>
      qpat_x_assum `ssa_map_ok _ (inter _ _) ==> _` mp_tac >>
      impl_tac >-
        (fs[ssa_map_ok_def,lookup_inter,AllCaseEqs()] >>
        metis_tac[]) >>
      strip_tac >>
      fs[] >>
      full_simp_tac(srw_ss())[list_next_var_rename_move_def,LET_DEF,UNCURRY_EQ] >> rveq >>
      fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def] >>
      simp[every_name_def2,EVERY_MEM] >>
      PURE_REWRITE_TAC[set_MAP_FST_toAList_domain] >>
      PURE_REWRITE_TAC[union_apply_nummaps_key] >>
      simp[domain_fromAList,apply_nummap_key_def] >>
      simp[MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
      simp[GSYM MAP_MAP_o,GSYM o_DEF,GSYM EVERY_MEM] >>
      qmatch_goalsub_abbrev_tac `EVERY _ ls` >>
      `ls = new_ls`
          by (
          EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_2')) >>
          rpt (impl_tac >- simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList] >>
          strip_tac) >>
          simp[Abbr`ls`] >>
          simp[MAP_EQ_f] >>
          simp[option_lookup_def,option_case_compute,IS_SOME_EXISTS]) >>
      POP_ASSUM SUBST_ALL_TAC >>
      EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_1)) >>
      simp[] >> rpt strip_tac >>
      simp[MAP_COUNT_LIST,EVERY_GENLIST] >>
      fs[is_stack_var_def,is_alloc_var_def] >>
      intLib.ARITH_TAC) >>
    fs[AllCaseEqs(),UNCURRY_EQ] >> rveq >>
    fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def] >>
    qspecl_then[`ret`,`ssa'''`,`na'''`] mp_tac list_next_var_rename_props >>
    EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_move_props_2)) >>
    fs[] >> rpt (DISCH_THEN STRIP_ASSUME_TAC) >>
    qpat_x_assum `ssa_map_ok _ (inter _ _) ==> _` mp_tac >>
     impl_tac >-
        (fs[ssa_map_ok_def,lookup_inter,AllCaseEqs()] >>
        metis_tac[]) >>
     EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac ssa_cc_trans_props)) >>
     fs[] >>
     rpt (DISCH_THEN STRIP_ASSUME_TAC) >>
     fs[] >> rfs[] >>
     qmatch_asmsub_abbrev_tac `fix_inconsistencies prio ssaL ssaR NA` >>
     Q.ISPECL_THEN [`ssaL`, `ssaR`, `NA`, `prio`] mp_tac fix_inconsistencies_conventions >>
     fs[] >>
     rpt (DISCH_THEN STRIP_ASSUME_TAC) >>
     `is_alloc_var na_3_p ∧ ssa_map_ok na_3_p ssa_3_p`
        by (full_simp_tac(srw_ss())[next_var_rename_def] >> rveq >>
            MAP_EVERY (irule_at Any) [is_alloc_var_add,ssa_map_ok_extend] >>
            irule_at Any ssa_map_ok_more >>
            asm_exists_tac >> simp[] >>
            metis_tac[convention_partitions]) >>
     fs[] >>
     full_simp_tac(srw_ss())[list_next_var_rename_move_def,LET_DEF,UNCURRY_EQ] >> rveq >>
     simp[every_stack_var_def,call_arg_convention_def] >>
     simp[every_name_def2,EVERY_MEM] >>
     PURE_REWRITE_TAC[set_MAP_FST_toAList_domain] >>
     PURE_REWRITE_TAC[union_apply_nummaps_key] >>
     simp[domain_fromAList,apply_nummap_key_def] >>
     simp[MAP_MAP_o,o_DEF,ELIM_UNCURRY] >>
     simp[GSYM MAP_MAP_o,GSYM o_DEF,GSYM EVERY_MEM] >>
     qmatch_goalsub_abbrev_tac `EVERY _ ls` >>
     `ls = new_ls`
       by (
       EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_2')) >>
       rpt (impl_tac >- simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList] >>
       strip_tac) >>
       simp[Abbr`ls`] >>
       simp[MAP_EQ_f] >>
       simp[option_lookup_def,option_case_compute,IS_SOME_EXISTS]) >>
     POP_ASSUM SUBST_ALL_TAC >>
     EVERY_ASSUM (TRY o (mp_then.mp_then (Pos hd) mp_tac list_next_var_rename_lemma_1)) >>
     simp[] >> rpt strip_tac >>
     simp[MAP_COUNT_LIST,EVERY_GENLIST] >>
     fs[is_stack_var_def,is_alloc_var_def] >>
     intLib.ARITH_TAC)
  >- ( (*ShareInst*)
     fs[ssa_cc_trans_def,UNCURRY_EQ,AllCaseEqs()] >> rveq >>
     simp[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def])
  >- ((*Loop*) suspend "Loop")
  >- ((*Break*) suspend "Break")
  >- ((*Continue*) suspend "Continue")
QED

Resume ssa_cc_trans_pre_alloc_conventions[Loop]:
  fs[ssa_cc_trans_def,UNCURRY_EQ]>>rveq>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  drule loop_setup_pre_alloc_conventions>>strip_tac>>
  drule loop_setup_props_local>>simp[]>>strip_tac>>
  qpat_x_assum `loop_setup _ _ _ _ = _` (assume_tac o GSYM)>>
  last_x_assum drule>>disch_then drule>>strip_tac>>
  qpat_x_assum `∀prog' _ _. _` (qspecl_then [`body'`,`ssa''`,`na'`] mp_tac)>>
  impl_tac
  >- (simp[]>>match_mp_tac ssa_map_ok_inter>>simp[])>>
  strip_tac>>
  fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def]>>
  IF_CASES_TAC>>fs[every_stack_var_def,call_arg_convention_def]>>
  fs[ssa_reconcile_def]>>every_case_tac>>
  fs[every_stack_var_def,call_arg_convention_def]
QED

Resume ssa_cc_trans_pre_alloc_conventions[Break]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def]
QED

Resume ssa_cc_trans_pre_alloc_conventions[Continue]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def]
QED

Finalise ssa_cc_trans_pre_alloc_conventions;

Theorem setup_ssa_props_2[local]:
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
  qspecl_then [`prog`,`ssa`,`na`,`[]`] assume_tac ssa_cc_trans_pre_alloc_conventions>>
  rev_full_simp_tac(srw_ss())[pre_alloc_conventions_def,every_stack_var_def,call_arg_convention_def,LET_THM]
QED

Theorem fake_moves_distinct_tar_reg[local]:
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
  ∀prog ssa na lt.
    is_alloc_var na ∧
    every_var (λx. x < na) prog ∧
    ssa_map_ok na ssa ⇒
    every_inst distinct_tar_reg (FST (ssa_cc_trans prog ssa na lt))
Proof
  ho_match_mp_tac ssa_cc_trans_ind>>full_simp_tac(srw_ss())[ssa_cc_trans_def]>>srw_tac[][]>>
  unabbrev_all_tac>>
  full_simp_tac(srw_ss())[every_inst_def]>>imp_res_tac ssa_cc_trans_props>>full_simp_tac(srw_ss())[]
  >- (
    Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`m`)>>TRY(Cases_on`r`)>>
    TRY(Cases_on`f`)>>
    full_simp_tac(srw_ss())[ssa_cc_trans_inst_def,LET_THM,next_var_rename_def]>>
    every_case_tac>>
    rw[]>>
    fs[every_var_def,every_var_inst_def,every_var_imm_def,every_inst_def]>>
    full_simp_tac(srw_ss())[distinct_tar_reg_def,ssa_map_ok_def,option_lookup_def]>>
    EVERY_CASE_TAC>>srw_tac[][]>>res_tac>>full_simp_tac(srw_ss())[]>>
    fs[is_alloc_var_def]>>CCONTR_TAC>>gvs[])
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
  >~[`Loop`] >- suspend "Loop"
  >~[`Break`] >- suspend "Break"
  >~[`Continue`] >- suspend "Continue"
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

Resume ssa_cc_trans_distinct_tar_reg[Loop]:
  fs[ssa_cc_trans_def,UNCURRY_EQ,every_var_def]>>rveq>>
  rpt(pairarg_tac>>fs[])>>rveq>>
  drule loop_setup_props_local>>simp[]>>strip_tac>>
  drule loop_setup_every_inst_distinct_tar_reg>>strip_tac>>
  last_x_assum mp_tac>>
  impl_tac
  >- (simp[]>>
      conj_tac
      >- (match_mp_tac every_var_mono>>
          qexists_tac`λx. x < na`>>fs[]>>DECIDE_TAC)>>
      match_mp_tac ssa_map_ok_inter>>simp[])>>
  strip_tac>>
  fs[every_inst_def]>>
  IF_CASES_TAC>>fs[every_inst_def]>>
  fs[ssa_reconcile_def]>>every_case_tac>>
  fs[every_inst_def]
QED

Resume ssa_cc_trans_distinct_tar_reg[Break]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[every_inst_def,distinct_tar_reg_def]
QED

Resume ssa_cc_trans_distinct_tar_reg[Continue]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[every_inst_def,distinct_tar_reg_def]
QED

Finalise ssa_cc_trans_distinct_tar_reg;

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
  disch_then(qspecl_then[`prog`,`[]`] mp_tac)>>
  impl_tac>- (
    simp[]>>
    match_mp_tac every_var_mono>>
    first_x_assum (irule_at Any)>>
    simp[])>>
  simp[]
QED

Theorem exp_to_addr_ShareInst[local]:
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

Theorem fake_moves_conventions2[local]:
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
  ∀prog ssa na lt c.
    every_var (λx. x < na) prog ∧
    is_alloc_var na ∧
    ssa_map_ok na ssa ∧
    full_inst_ok_less c prog ⇒
    full_inst_ok_less c (FST (ssa_cc_trans prog ssa na lt))
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
    qspecl_then [`prog`,`ssa_2_p`,`na_2_p`,`lt`] mp_tac ssa_cc_trans_props>>
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
  >~[`Loop`] >- suspend "Loop"
  >~[`Break`] >- suspend "Break"
  >~[`Continue`] >- suspend "Continue"
  >> (*ShareInst*)
    qpat_x_assum `option_CASE _ _ _` mp_tac >>
    ntac 2 TOP_CASE_TAC >>
    strip_tac >>
    IF_CASES_TAC >>
    simp[full_inst_ok_less_def] >>
    gvs[exp_to_addr_ShareInst,ssa_cc_trans_exp_def] >>
    simp[exp_to_addr_def]
QED

Resume ssa_cc_trans_full_inst_ok_less[Loop]:
  qpat_x_assum `every_var _ _` mp_tac>>simp[every_var_def]>>strip_tac>>
  drule loop_setup_props_local>>simp[]>>strip_tac>>
  drule loop_setup_full_inst_ok_less>>strip_tac>>
  last_x_assum (qspec_then `c` mp_tac)>>
  impl_tac
  >- (simp[]>>
      conj_tac
      >- (match_mp_tac every_var_mono>>
          qexists_tac`λx. x < na`>>fs[]>>DECIDE_TAC)>>
      match_mp_tac ssa_map_ok_inter>>simp[])>>
  strip_tac>>
  fs[full_inst_ok_less_def]>>
  IF_CASES_TAC>>fs[full_inst_ok_less_def]>>
  fs[ssa_reconcile_def]>>every_case_tac>>
  fs[full_inst_ok_less_def,inst_ok_less_def]
QED

Resume ssa_cc_trans_full_inst_ok_less[Break]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[full_inst_ok_less_def]
QED

Resume ssa_cc_trans_full_inst_ok_less[Continue]:
  fs[ssa_cc_trans_def,ssa_reconcile_def]>>every_case_tac>>fs[]>>rveq>>
  fs[full_inst_ok_less_def]
QED

Finalise ssa_cc_trans_full_inst_ok_less;

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
  qspecl_then [`prog`,`ssa`,`n'`,`[]`,`c`] mp_tac ssa_cc_trans_full_inst_ok_less>>
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

Theorem call_arg_convention_preservation[local]:
  ∀prog f.
  every_var (λx. is_phy_var x ⇒ f x = x) prog ∧
  call_arg_convention prog ⇒
  call_arg_convention (apply_colour f prog)
Proof
  ho_match_mp_tac call_arg_convention_ind>>
  srw_tac[][call_arg_convention_def,every_var_def]>>
  EVERY_CASE_TAC>>unabbrev_all_tac>>
  full_simp_tac(srw_ss())[call_arg_convention_def]
  >- (
    Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`r`)>>TRY(Cases_on`m`)>>
    TRY(Cases_on`f'`>>every_case_tac)>>
    fs[inst_arg_convention_def,every_var_inst_def,is_phy_var_def,every_var_imm_def])>>
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

Theorem every_apply_nummap_key_helper[local]:
  ∀f names P Q.
  EVERY P (MAP FST (toAList names)) ∧ (∀x. P x ⇒ Q (f x)) ⇒
  EVERY Q (MAP FST (toAList (fromAList (MAP (λ(x:num,y:unit). (f x,())) (toAList names)))))
Proof
  rw[EVERY_MEM, MEM_MAP, EXISTS_PROD, MEM_toAList, domain_lookup, lookup_fromAList]>>
  imp_res_tac ALOOKUP_MEM>>
  fs[MEM_MAP, EXISTS_PROD, MEM_toAList]>>
  rw[]>>
  metis_tac[]
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
  >- metis_tac[every_var_inst_apply_colour_inst]
  >- metis_tac[every_var_exp_apply_colour_exp]
  >- metis_tac[every_var_exp_apply_colour_exp]
  >- (Cases_on `names` >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>srw_tac[][]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
  >- (Cases_on `names` >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>srw_tac[][]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
  >- (EVERY_CASE_TAC>>unabbrev_all_tac>>full_simp_tac(srw_ss())[every_var_def,EVERY_MAP,EVERY_MEM]>>
    rename1 `(apply_nummaps_key f names)` >>
    Cases_on `names` >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    srw_tac[][]>>full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
  >- (Cases_on`ri`>>full_simp_tac(srw_ss())[every_var_imm_def])
  >- (Cases_on `numset` >>
    full_simp_tac(srw_ss())[every_name_def,EVERY_MEM,toAList_domain,apply_nummaps_key_def]>>
    full_simp_tac(srw_ss())[domain_fromAList,MEM_MAP,ZIP_MAP]>>srw_tac[][]>>
    Cases_on`y'`>>full_simp_tac(srw_ss())[MEM_toAList,domain_lookup])
  >- metis_tac[every_var_exp_apply_colour_exp]
  >- metis_tac[every_var_exp_apply_colour_exp]
  >- (* Loop names *)
    (rw[]>>Cases_on `x`>>fs[MEM_toAList, lookup_fromAList]>>
    imp_res_tac ALOOKUP_MEM>>fs[MEM_MAP, EXISTS_PROD]>>rw[]>>res_tac>>fs[])
  >- (* Loop exit_names *)
    (rw[]>>Cases_on `x`>>fs[MEM_toAList, lookup_fromAList]>>
    imp_res_tac ALOOKUP_MEM>>fs[MEM_MAP, EXISTS_PROD]>>rw[]>>res_tac>>fs[])
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

Theorem every_var_exp_get_reads_exp[local]:
  ∀exp. every_var_exp (λx. MEM x (get_reads_exp exp)) exp
Proof
  assume_tac every_var_exp_get_live_exp>>
  rw[]>>pop_assum(qspec_then`exp` assume_tac)>>
  ho_match_mp_tac every_var_exp_mono>>
  HINT_EXISTS_TAC>>fs[get_reads_exp_get_live_exp]
QED

val exp_tac3 =
  assume_tac (Q.SPEC `exp` every_var_exp_get_reads_exp)>>
  ho_match_mp_tac every_var_exp_mono>>
  HINT_EXISTS_TAC>>fs[in_clash_tree_def];

Theorem every_var_in_get_clash_tree[local]:
  ∀prog lt.
  every_var (in_clash_tree (get_clash_tree prog lt)) prog
Proof
  ho_match_mp_tac get_clash_tree_ind>>rw[get_clash_tree_def]
  >~ [`wordLang$Loop names body exit_names`] >- (fs[every_var_def,in_clash_tree_def,EVERY_MEM,every_name_def,toAList_domain]>>metis_tac[every_var_mono,in_clash_tree_def])
  >~ [`Break n`] >- fs[every_var_def]
  >~ [`Continue n`] >- fs[every_var_def]
  >>
  fs[every_var_def,in_clash_tree_def,EVERY_MEM,every_name_def,toAList_domain]>>
  TRY(exp_tac3)
  >-
    (Cases_on`i`>>TRY(Cases_on`a`)>>TRY(Cases_on`r`)>>TRY(Cases_on`m`)>>TRY(Cases_on`f`)>>
    fs[every_var_imm_def,get_delta_inst_def,every_var_inst_def,in_clash_tree_def])
  >-
    metis_tac[every_var_mono,in_clash_tree_def]
  >-
    (Cases_on`ri`>>fs[every_var_imm_def]>>
    rw[]>>fs[in_clash_tree_def]>>
    metis_tac[every_var_mono,in_clash_tree_def])
  >>
    EVERY_CASE_TAC>>
    fs[in_clash_tree_def,domain_numset_list_insert,domain_union]>>
    metis_tac[every_var_mono,in_clash_tree_def]
QED

Theorem every_var_T[local]:
  ∀prog.
  every_var (λx. T) prog
Proof
  rw[]>>
  mp_tac (Q.SPEC`prog` max_var_max)>>
  rw[]>>
  ho_match_mp_tac every_var_mono>>HINT_EXISTS_TAC>>
  fs[]
QED

Theorem every_var_is_phy_var_total_colour[local]:
  every_var is_phy_var (apply_colour (total_colour col) prog)
Proof
  match_mp_tac every_var_apply_colour>>
  qexists_tac`\x. T`>>
  simp[every_var_T]>>
  fs[total_colour_def]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  is_phy_var_tac
QED

Theorem oracle_colour_ok_conventions[local]:
  pre_alloc_conventions prog ∧
  oracle_colour_ok k col_opt (get_clash_tree prog lt) prog ls = SOME x ⇒
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
  TOP_CASE_TAC>>fs[]
  >- (
    qpat_abbrev_tac`forced = get_forced _ _ _`>>
    qpat_abbrev_tac`tree = get_clash_tree _ _`>>
    qpat_abbrev_tac`fs = get_stack_only _`>>
    `EVERY (λx,y.in_clash_tree tree x ∧ in_clash_tree tree y) forced` by
      (unabbrev_all_tac>>fs[get_forced_in_get_clash_tree])>>
    pairarg_tac>>fs[]>>
    drule select_reg_alloc_correct>>
    disch_then(qspecl_then [`alg`,`spillcosts`,`k`,`heu_moves`,`fs`] assume_tac)>>rfs[]>>fs[]>>
    assume_tac (Q.ISPECL[`prog:'a wordLang$prog`,`[]:(num_set # num_set) list`]every_var_in_get_clash_tree)>>
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
      metis_tac[is_phy_var_def,EVEN_MOD2,EVEN_EXISTS,TWOxDIV2])
  >>
  metis_tac[oracle_colour_ok_conventions]
QED

(*word_alloc preserves syntactic conventions*)
Theorem word_alloc_full_inst_ok_less_lem[local]:
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
Theorem lookup_undir_g_insert_existing[local]:
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

Theorem forced_distinct_col[local]:
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
  qpat_abbrev_tac`tree = get_clash_tree _ _`>>
  qpat_abbrev_tac`fs = get_stack_only _`>>
  `EVERY (λx,y.in_clash_tree tree x ∧ in_clash_tree tree y) forced` by
    (unabbrev_all_tac>>fs[get_forced_in_get_clash_tree])>>
  EVERY_CASE_TAC>>fs[]>>
  rw[]>>rveq>>
  match_mp_tac word_alloc_full_inst_ok_less_lem>>fs[]>>
  drule select_reg_alloc_correct>>
  disch_then(qspecl_then [`alg`,`spillcosts`,`k`,`heu_moves`,`fs`] assume_tac)>>rfs[]>>
  fs[]>>
  match_mp_tac forced_distinct_col>>rfs[]>>
  unabbrev_all_tac>>
  match_mp_tac get_forced_pairwise_distinct>>
  simp[]
QED

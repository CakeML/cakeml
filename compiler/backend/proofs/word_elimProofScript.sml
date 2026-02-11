(*
  Correctness proof for word_elim
*)
Theory word_elimProof
Libs
  preamble
Ancestors
  mllist wordLang word_elim wordSem wordProps spt_closure wordConvs


val _ = temp_delsimps ["fromAList_def"]
val _ = Parse.hide"mem";
val _ = Parse.bring_to_front_overload"domain"{Thy="sptree",Name="domain"};

(**************************** ANALYSIS LEMMAS *****************************)

Theorem lookup_analyse_word_code:
     ∀ code n arity prog. ALOOKUP code n = SOME (arity, prog)
    ⇒ lookup n (analyse_word_code code) = SOME (find_word_ref prog)
Proof
    Induct >> fs[FORALL_PROD] >> fs[analyse_word_code_def] >>
    fs[lookup_insert] >> rw[]
QED

Theorem remove_word_code_thm:
     ∀ n reachable:num_set l . ALL_DISTINCT (MAP FST l)
    ⇒ ∀ v . (n ∈ domain reachable ∧ MEM (n, v) l ⇔
        MEM (n, v) (remove_word_code reachable l))
Proof
    rw[] >> EQ_TAC >> rw[]
    >- (Induct_on `l` >> rw[] >> fs[remove_word_code_def] >>
        fs[domain_lookup] >>
        Cases_on `IS_SOME (lookup (FST h) reachable)` >> fs[])
    >> fs[remove_word_code_def]
    >- (Induct_on `l` >> rw[] >> fs[domain_lookup, IS_SOME_EXISTS])
    >- (fs[MEM_MAP, MEM_FILTER] >> qexists_tac `y` >> rw[])
QED



(**************************** DEFINITIONS *****************************)

Definition dest_word_loc_def:
    (* 'a word_loc = Word ('a word) | Loc num num *)
    (dest_word_loc (Loc n _) = SOME n) ∧
    (dest_word_loc (_:'a word_loc) = NONE)
End

Definition dest_result_loc_def:
    (dest_result_loc (SOME (Result w ns)) =
    BIGUNION (set (MAP (\x. case (dest_word_loc x) of NONE => ∅  | SOME x => {x}) ns))) /\
    (dest_result_loc (SOME (Exception w (Loc n n0))) = {n}) ∧
    (dest_result_loc _ = {})
End

(* TODO could do alt def using toAList -
    not necessary though, may not be cleaner *)
Definition get_locals_def:
  (* locals : ('a word_loc) num_map *)
    (get_locals (LN : ('a word_loc) num_map) = LN) ∧
    (get_locals (LS a) = case (dest_word_loc a) of
        | SOME n => insert n () LN
        | NONE => LN) ∧
    (get_locals (BN t1 t2) = union (get_locals t1) (get_locals t2)) ∧
    (get_locals (BS t1 a t2) =
        let t = (union (get_locals t1) (get_locals t2)) in
            case (dest_word_loc a) of
                | SOME n => insert n () t
                | NONE => t)
End

Theorem domain_get_locals_lookup:
  ∀ n t . n ∈ domain (get_locals t) ⇔ ∃ k n1 . lookup k t = SOME (Loc n n1)
Proof
  rw[] >> reverse (EQ_TAC) >> rw[]
  >- (pop_assum mp_tac >> map_every qid_spec_tac [`n`,`k`,`t`] >>
      Induct >> rw[lookup_def, get_locals_def, dest_word_loc_def, domain_union]
      >- metis_tac[]
      >- metis_tac[] >>
      Cases_on `dest_word_loc a` >> fs[] >> rw[domain_union] >>
      fs[lookup_def] >>
      Cases_on `n = 0` >> fs[] >> rveq >> fs[dest_word_loc_def] >>
      Cases_on `a` >> fs[dest_word_loc_def] >> Cases_on `EVEN n` >> fs[] >>
      metis_tac[]
     ) >>
  Induct_on `t`
  >- rw[get_locals_def, domain_def]
  >- (rw[get_locals_def, domain_def, lookup_def] >>
      Cases_on `a` >> fs[dest_word_loc_def])
  >- (rw[get_locals_def, domain_def, lookup_def] >>
      fs[domain_union] >> res_tac
      >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
          once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
      >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
          once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV]))
  >- (rw[get_locals_def, domain_def, lookup_def] >>
      Cases_on `a` >> fs[dest_word_loc_def] >>
      simp[AllCaseEqs()] >> gvs[EXISTS_OR_THM]
      >- (qexists ‘2 * k + 2’ >> simp[EVEN_ADD, EVEN_MULT])
      >- (qexists ‘2 * k + 1’ >> simp[EVEN_ADD, EVEN_MULT])
      >- (disj2_tac >> qexists ‘2 * k + 2’ >> simp[EVEN_ADD, EVEN_MULT])
      >- (disj2_tac >> qexists ‘2 * k + 1’ >> simp[EVEN_ADD, EVEN_MULT]))
QED

Theorem get_locals_insert_Loc:
     ∀ k n1 n0 (locals : ('a word_loc) num_map).
        domain (get_locals (insert k (Loc n1 n0) locals)) ⊆
            domain (get_locals locals) ∪ {n1}
Proof
        rw[] >> fs[SUBSET_DEF] >>  rw[domain_get_locals_lookup] >>
        fs[lookup_insert] >> rw[] >>
        Cases_on `k' = k` >> fs[] >> disj1_tac >> qexists_tac `k'` >>
        qexists_tac `n1'` >> fs[]
QED

Theorem get_locals_insert:
     ∀ k v (locals : ('a word_loc) num_map).
        domain (get_locals (insert k v locals)) ⊆ domain (get_locals locals)
        ∪ (case dest_word_loc v of | NONE => {} | SOME n => {n})
Proof
        reverse(Cases_on `v`) >> fs[dest_word_loc_def]
        >- fs[get_locals_insert_Loc]
        >- (rw[] >> fs[SUBSET_DEF] >>  rw[domain_get_locals_lookup] >>
            fs[lookup_insert] >> rw[] >>
            Cases_on `k' = k` >> fs[] >> qexists_tac `k'` >>
            qexists_tac `n1` >> fs[])
QED

(*TODO fix conflict with get_store in WordSem*)
Definition get_store_def:
  (* store : store_name |-> 'a word_loc *)
    get_store (st:store_name |-> 'a word_loc) =
        let locSet = SET_TO_LIST (FRANGE st) in
        let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc locSet)) in
        FOLDL (λ acc loc . insert loc () acc) LN locList
End

Theorem domain_get_store:
     ∀ n store . n ∈ domain (get_store store) ⇔
        (∃ k n1 . FLOOKUP store k = SOME (Loc n n1))
Proof
    fs[get_store_def] >> fs[MEM_MAP, MEM_FILTER] >>
    rw[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
    EQ_TAC >> rw[]
    >- (Cases_on `y'` >> fs[dest_word_loc_def] >> metis_tac[])
    >- (qexists_tac `Loc n n1` >> qexists_tac `k` >> fs[dest_word_loc_def])
QED

Theorem get_store_update:
     ∀ store k v .
        domain (get_store (store |+ (k,v))) ⊆ domain (get_store store)
            ∪ (case dest_word_loc v of | NONE => {} | SOME n => {n})
Proof
    Cases_on `v` >> fs[dest_word_loc_def] >> rw[] >> fs[SUBSET_DEF] >>
    rw[domain_get_store] >>
    fs[lookup_insert] >> rw[] >> fs[FLOOKUP_UPDATE] >> Cases_on `k = k'` >> fs[]
    >| [ALL_TAC, disj1_tac] >> qexists_tac `k'` >> qexists_tac `n1` >> fs[]
QED

Definition get_num_wordloc_alist_def:
    get_num_wordloc_alist (l: (num, 'a word_loc) alist) =
        let locs = MAP THE (FILTER IS_SOME (MAP (dest_word_loc o SND) l)) in
        FOLDL (λ acc loc . insert loc () acc) LN locs
End

Theorem get_num_wordloc_alist_thm:
     ∀ n e l . (∃ n0 . MEM (Loc n n0) (MAP SND l)) ⇔
        n ∈ domain (get_num_wordloc_alist l)
Proof
    fs[get_num_wordloc_alist_def] >> fs[MEM_MAP, MEM_FILTER] >>
    rw[] >> EQ_TAC >> rw[]
    >- (qexists_tac `dest_word_loc (Loc n n0)` >> fs[dest_word_loc_def] >>
        qexists_tac `y` >> metis_tac[dest_word_loc_def])
    >- (Cases_on `SND y'` >> fs[dest_word_loc_def] >>
        qexists_tac `n0` >> qexists_tac `y'` >> fs[])
QED

Theorem get_num_wordloc_alist_get_locals:
     ∀ e .
        domain (get_locals (fromAList e)) ⊆ domain (get_num_wordloc_alist e)
Proof
    Induct >> rw[] >>
    fs[fromAList_def, get_num_wordloc_alist_def, domain_def, get_locals_def] >>
    Cases_on `h` >> Cases_on `r` >> fs[dest_word_loc_def, fromAList_def]
    >- (qspecl_then [`q`, `Word c`, `(fromAList e)`] mp_tac get_locals_insert >>
        rw[dest_word_loc_def] >> imp_res_tac SUBSET_TRANS)
    >- (qspecl_then [`q`, `Loc n n0`, `(fromAList e)`]
            mp_tac get_locals_insert >> rw[dest_word_loc_def] >>
        fs[Once INSERT_SING_UNION] >> rw[Once UNION_COMM] >>
        fs[SUBSET_DEF] >> metis_tac[])
QED

Theorem get_locals_union_subset:
   !A B.
   domain (get_locals (union A B)) ⊆ (domain (union (get_locals A) (get_locals B)))
Proof
   Induct_on `A` >> fs[union_def,get_locals_def] >>
   Cases_on `B` >> fs[get_locals_def] >>
   rw[] >> EVERY_CASE_TAC >> fs[] >>
   ASM_SET_TAC[]
QED

Definition get_stack_def:
  (* stack : ('a stack_frame) list *)
    (get_stack [] = LN:num_set) ∧
    (get_stack ((StackFrame lsz e0 e _)::xs) =
        union (union (get_num_wordloc_alist e0) (get_num_wordloc_alist e)) (get_stack xs))
End

val get_stack_ind = theorem "get_stack_ind";

Theorem get_stack_hd_thm:
     ∀ stack dr l0 l opt t . domain (get_stack stack) ⊆ dr ∧
        stack = StackFrame lsz l l0 opt::t
        ⇒ domain (get_locals (union (fromAList l0) (fromAList l))) ⊆ dr ∧
          domain (get_stack t) ⊆ dr
Proof
    recInduct get_stack_ind >>
    rpt conj_tac >> rpt (gen_tac ORELSE disch_tac) >>
    fs[get_stack_def, domain_union, fromAList_def, get_locals_def] >>
    rveq >>
    Cases_on `e` >> fs[get_stack_def, domain_union,
    fromAList_def, get_locals_def]
    >- metis_tac[get_num_wordloc_alist_get_locals, SUBSET_TRANS]
    >> Cases_on `e0` >> fs[get_stack_def, domain_union,
    fromAList_def, get_locals_def]
    >- metis_tac[get_num_wordloc_alist_get_locals, SUBSET_TRANS]
    >> irule SUBSET_TRANS >> irule_at (Pos hd) get_locals_union_subset
    >> fs[domain_union]
    >- metis_tac[get_num_wordloc_alist_get_locals, SUBSET_TRANS]
QED

Theorem get_stack_LASTN:
     ∀ stack n . domain (get_stack (LASTN n stack)) ⊆ domain (get_stack stack)
Proof
    recInduct get_stack_ind >> rw[get_stack_def, LASTN_ALT] >>
    Cases_on `SUC (LENGTH xs) ≤ n` >> fs[get_stack_def, domain_union]
    \\ fs[SUBSET_DEF] \\ metis_tac[]
QED

Theorem get_stack_CONS:
     ∀ h t . domain (get_stack [h]) ⊆ domain (get_stack (h::t)) ∧
        domain (get_stack t) ⊆ domain (get_stack (h::t))
Proof
    Cases_on `h` >> fs[get_stack_def, domain_union] >> ASM_SET_TAC[]
QED

Theorem get_stack_enc_stack:
     ∀ stack reachable . domain (get_stack stack) ⊆ domain reachable
    ⇒ ∀ e . MEM e (enc_stack stack)
    ⇒ (case dest_word_loc e of | NONE => {} | SOME n => {n}) ⊆
        domain reachable
Proof
    recInduct get_stack_ind >> rw[enc_stack_def, get_stack_def, domain_union]
    >- (last_x_assum kall_tac >>
        Cases_on `e'` >> fs[dest_word_loc_def] >>
        qsuff_tac `n ∈ domain (get_num_wordloc_alist e)` >> fs[SUBSET_DEF] >>
        imp_res_tac get_num_wordloc_alist_thm)
    >- res_tac
QED

Theorem get_stack_dec_stack:
     ∀ locs stack reachable new_stack .
    (∀ n n0 . MEM (Loc n n0) locs ⇒ n ∈ domain reachable) ∧
    domain (get_stack stack) ⊆ domain reachable ∧
    dec_stack locs stack = SOME new_stack
    ⇒ domain (get_stack new_stack) ⊆ domain reachable
Proof
    ho_match_mp_tac dec_stack_ind >> rw[]
    >- (fs[dec_stack_def] >> rveq >> fs[get_stack_def])
    >- (`∀ n n0 . MEM (Loc n n0) (DROP (LENGTH l) locs)
            ⇒ n ∈ domain reachable` by metis_tac[MEM_DROP_IMP] >>
        fs[dec_stack_def] >>
        Cases_on `dec_stack (DROP (LENGTH l) locs) stack` >> fs[] >>
        first_x_assum (qspec_then `reachable` mp_tac) >> rw[] >>
        fs[get_stack_def, domain_union] >> rw[]
        >- (fs[SUBSET_DEF, GSYM get_num_wordloc_alist_thm] >> rw[] >>
            fs[MEM_MAP] >>
            `LENGTH (MAP FST l) = LENGTH (TAKE (LENGTH l) locs)` by
                fs[LENGTH_TAKE] >>
            fs[MEM_ZIP] >> fs[] >> `n < LENGTH (TAKE (LENGTH l) locs)` by
                fs[LENGTH_TAKE] >>
            qsuff_tac `MEM (Loc x' n0) locs` >- metis_tac[] >> fs[EL_TAKE] >>
            fs[MEM_EL] >> qexists_tac `n` >> fs[])
        >- res_tac)
    >- fs[dec_stack_def]
QED

Definition get_memory_def:
  (* 'a word -> 'a word_loc *)
    get_memory (mem:'a word -> 'a word_loc) (mdom:'a word set) =
        let locSet = SET_TO_LIST(IMAGE mem mdom) in
        let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc locSet)) in
        FOLDL (λ acc loc . insert loc () acc) LN locList
End

Theorem FINITE_mdom_mem:
     ∀ mdom . FINITE mdom ⇒ FINITE {mem x | x ∈ mdom}
Proof
    ho_match_mp_tac FINITE_INDUCT >>
    rw[] >>
    qsuff_tac `{mem x | x = e ∨ x ∈ mdom} = mem e INSERT {mem x | x ∈ mdom}`
    >- rw[] >>
    fs[EXTENSION] >> metis_tac[]
QED

Theorem domain_get_memory:
     ∀ mem (mdom : 'a word set) n .
       n ∈ domain (get_memory mem mdom) ⇔
         ∃ k n1 . k ∈ mdom ∧ mem k = Loc n n1
Proof
    fs[get_memory_def, IMAGE_DEF] >> fs[FILTER_MAP, MAP_MAP_o] >> rw[] >>
    fs[MEM_MAP, MEM_FILTER] >>
    `FINITE {mem x | x ∈ mdom}` by
      metis_tac[FINITE_mdom_mem, WORD_FINITE] >>
    rw[MEM_SET_TO_LIST] >>
    EQ_TAC >> rw[]
    >- (Cases_on `mem x` >> fs[dest_word_loc_def] >> metis_tac[])
    >- (qexists_tac `Loc n n1` >> fs[dest_word_loc_def] >> metis_tac[])
QED

Theorem get_memory_update:
     ∀ k v (memory : 'a word -> 'a word_loc) (mdomain : 'a word set) .
        (domain (get_memory ((k =+ v) memory) mdomain)) ⊆
            (domain (get_memory memory mdomain))
        ∪ (case (dest_word_loc v) of | NONE => {} | SOME n => {n})
Proof
        Cases_on `v` >> fs[dest_word_loc_def] >> rw[] >> fs[SUBSET_DEF] >>
        rw[domain_get_memory] >>
        fs[lookup_insert] >> rw[] >> fs[APPLY_UPDATE_THM] >>
        Cases_on `k' = k` >> fs[]
        >| [ALL_TAC, disj1_tac] >> qexists_tac `k'` >> qexists_tac `n1` >> fs[]
QED

Definition find_loc_state_def:
    find_loc_state s =
        let loc = (get_locals s.locals) in
        let sto = (get_store s.store) in
        let sta = (get_stack s.stack) in
        let mem = (get_memory s.memory s.mdomain) in
        union (union loc sto) (union sta mem)
End

Theorem domain_find_loc_state:
     ∀ s . domain (find_loc_state s) =
        domain (get_locals s.locals) ∪ domain (get_store s.store) ∪
        domain (get_stack s.stack) ∪ domain (get_memory s.memory s.mdomain)
Proof
    rw[find_loc_state_def, domain_union, UNION_ASSOC]
QED

Definition code_rel_def:
    code_rel (reachable:num_set) s_code
        (t_code :(num # ('a wordLang$prog)) num_map) =
        ∀ n . n ∈ domain reachable ⇒
            lookup n s_code = lookup n t_code
End

Definition code_closed_def:
    code_closed reachable c1 ⇔ ∃ code1 . c1 = fromAList code1 ∧
        ∀ n m . n ∈ domain reachable ∧
        is_reachable (analyse_word_code code1) n m ⇒
        m ∈ domain reachable
End

Definition gc_no_new_locs_def:
    gc_no_new_locs (g:'a gc_fun_type) ⇔  ∀ sta mem mdom sto wl mem1 sto1 sta1 .
        (g (enc_stack sta, mem, mdom, sto) = SOME (wl, mem1, sto1)) ∧
         dec_stack wl sta = SOME sta1 ⇒
        domain (get_stack sta1) ⊆ domain (get_stack sta) ∧
        domain (get_memory mem1 mdom) ⊆ domain (get_memory mem mdom) ∧
        domain (get_store sto1) ⊆ domain (get_store sto)
End

Definition word_state_rel_def:
    word_state_rel (reachable:num_set) t s ⇔
        s.locals         = t.locals ∧
        s.fp_regs        = t.fp_regs ∧
        s.store          = t.store ∧
        s.stack          = t.stack ∧
        s.memory         = t.memory ∧
        s.mdomain        = t.mdomain ∧
        s.sh_mdomain     = t.sh_mdomain ∧
        s.permute        = t.permute ∧
        s.compile        = t.compile ∧
        s.compile_oracle = t.compile_oracle ∧
        s.code_buffer    = t.code_buffer ∧
        s.data_buffer    = t.data_buffer ∧
        s.gc_fun         = t.gc_fun ∧
        s.handler        = t.handler ∧
        s.clock          = t.clock ∧
        s.termdep        = t.termdep ∧
        s.be             = t.be ∧
        s.ffi            = t.ffi ∧
        s.locals_size    = t.locals_size /\
        s.stack_max      = t.stack_max /\
        s.stack_limit    = t.stack_limit /\
        s.stack_size     = t.stack_size  /\
        code_rel reachable (s.code) (t.code) ∧
        domain (find_loc_state t) ⊆ domain (reachable)
End


(**************************** OTHER LEMMAS *****************************)

Theorem ALOOKUP_ZIP_SUCCESS:
     ∀ x y k v . LENGTH x = LENGTH y
    ⇒ ALOOKUP (ZIP (x, y)) k = SOME v ⇒ MEM v y
Proof
    rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_EL] >> drule EL_ZIP >> rw[] >>
    pop_assum (qspec_then `n` mp_tac) >> rw[] >>
    imp_res_tac LENGTH_ZIP >> rfs[] >>
    fs[] >> qexists_tac `n` >> fs[]
QED

Theorem get_vars_locals:
     ∀ args s x y. get_vars args s = SOME x ∧ MEM y x
    ⇒ ∃ n . lookup n s.locals = SOME y
Proof
    Induct >- (rw[get_vars_def] >> fs[MEM]) >>
    strip_tac >> strip_tac >> strip_tac >> strip_tac >>
    simp[get_vars_def] >>  Cases_on `get_var h s` >> simp[] >>
    Cases_on `get_vars args s` >> simp[] >> fs[get_var_def] >>
    first_x_assum (qspecl_then [`s`, `x''`, `y`] mp_tac) >> rw[] >>
    Cases_on `MEM y x''` >- metis_tac[] >> fs[MEM] >> rveq >>
    qexists_tac `h` >> fs[]
QED

Theorem get_vars_get_locals:
     ∀ args s x n n1. get_vars args s = SOME x ∧ MEM (Loc n n1) x
    ⇒ n ∈ domain (get_locals s.locals)
Proof
    rw[] >> drule_all get_vars_locals >> strip_tac >>
    irule (iffRL domain_get_locals_lookup) >>
    goal_assum drule
QED

Theorem get_locals_fromList2:
     ∀ args s x t . get_vars args s = SOME x ∧ x ≠ [] ∧ t = fromList2 x
    ⇒ domain (get_locals t) ⊆ domain (get_locals s.locals)
Proof
    rw[] >> rw[SUBSET_DEF] >>
    qspecl_then [`x'`, `fromList2 x`] mp_tac domain_get_locals_lookup >> rw[] >>
    `MEM (Loc x' n1) x` by (fs[fromList2_value] >> qexists_tac `k` >> fs[]) >>
    metis_tac[get_vars_get_locals]
QED

Theorem get_locals_fromList2_extension:
     ∀  x y ys. x ∈ domain (get_locals (fromList2 ys))
    ⇒ x ∈ domain (get_locals (fromList2 (ys ⧺ [y])))
Proof
        rw[] >> fs[domain_get_locals_lookup] >> qexists_tac `k` >>
        qexists_tac `n1` >>
        Induct_on `ys` >> rw[] >- (fs[fromList2_def, lookup_def]) >>
        fs[lookup_fromList2, lookup_fromList] >>
        qpat_x_assum `k DIV 2 < LENGTH ys ∧ _ ⇒ _` kall_tac >>
        imp_res_tac EVEN_EXISTS >> rveq >> fs[EVEN_DOUBLE] >>
        `2 * m DIV 2 = m` by (
          once_rewrite_tac [MULT_COMM] >> fs[MULT_DIV]) >> fs[] >>
        Cases_on `m` >> gvs[EL_APPEND_EQN]
QED

Theorem get_locals_fromList2_FRONT:
     ∀ args s x xf t . get_vars args s = SOME x ∧
        x ≠ [] ∧ xf = FRONT x ∧ t = fromList2 xf
    ⇒ domain (get_locals t) ⊆ domain (get_locals s.locals)
Proof
    rw[] >> match_mp_tac SUBSET_TRANS >>
    qexists_tac `domain (get_locals (fromList2 x))` >>
    reverse(CONJ_TAC) >- metis_tac[get_locals_fromList2]
        >- (`∃ y ys . x = SNOC y ys` by metis_tac[SNOC_CASES] >>
            FULL_SIMP_TAC std_ss [FRONT_SNOC] >>
            fs[SNOC_APPEND] >> rw[SUBSET_DEF] >>
            imp_res_tac get_locals_fromList2_extension >> fs[])
QED

Theorem get_memory_write_bytearray_lemma:
     ∀ mem mdom reachable c r be .
        domain(get_memory mem mdom) ⊆ domain reachable
    ⇒ domain (get_memory (write_bytearray c r mem mdom be) mdom) ⊆
        domain reachable
Proof
    Induct_on `r` >> fs[write_bytearray_def] >> rw[] >>
    fs[mem_store_byte_aux_def] >>
    Cases_on `write_bytearray (c + 1w) r mem mdom be (byte_align c)` >> fs[] >>
    Cases_on `byte_align c ∈ mdom` >> fs[] >> first_x_assum drule >> rw[] >>
    pop_assum (qspecl_then [`c + 1w`, `be`] mp_tac) >> rw[] >>
    qspecl_then [`byte_align c`, `Word (set_byte c h c' be)`,
        `write_bytearray (c + 1w) r mem mdom be`, `mdom`]
        mp_tac get_memory_update >> rw[dest_word_loc_def] >>
        metis_tac[SUBSET_TRANS]
QED

Theorem stack_list_rearrange_lemma:
     ∀ s dr locs opt lsz .
        domain (get_locals s.locals) ⊆ dr ∧
        domain (get_stack s.stack) ⊆ dr
    ⇒ domain (get_stack (StackFrame lsz (toAList (inter s.locals n)) (list_rearrange (s.permute 0)
    (sort key_val_compare (toAList (inter s.locals locs)))) opt::s.stack))
        ⊆ dr
Proof
    rw[] >> fs[get_stack_def, domain_union] >> rw[SUBSET_DEF] >>
    imp_res_tac get_num_wordloc_alist_thm >>
    fs[MEM_MAP] >> fs[mem_list_rearrange, sort_MEM] >>
    Cases_on `y` >> fs[MEM_toAList] >> fs[lookup_inter] >>
    gvs[option_case_eq] >>
    fs[SUBSET_DEF, domain_get_locals_lookup] >> metis_tac[]
QED

Theorem remove_word_code_thm_FST:
     ∀ n reachable:num_set l . ALL_DISTINCT (MAP FST l)
    ⇒ (n ∈ domain reachable ∧ MEM n (MAP FST l) ⇔
    MEM n (MAP FST (remove_word_code reachable l)))
Proof
    rw[] >> EQ_TAC >> rw[]
    >- (Induct_on `l` >> rw[] >> fs[remove_word_code_def] >>
        fs[domain_lookup] >>
    Cases_on `IS_SOME (lookup (FST h) reachable)` >> fs[])
    >> fs[remove_word_code_def]
    >- (Induct_on `l` >> rw[] >> fs[domain_lookup, IS_SOME_EXISTS])
    >- (fs[MEM_MAP, MEM_FILTER] >> qexists_tac `y` >> rw[])
QED

Theorem remove_word_code_MAP_FST_lemma:
     ∀ reachable:num_set (l: (num,num # α prog) alist) .
        MAP FST (FILTER (λx. IS_SOME (lookup (FST x) reachable)) l) =
            FILTER (λx. IS_SOME (lookup x reachable)) (MAP FST l)
Proof
    Induct_on `l` >> rw[]
QED

(**************************** WORD STATE REL ***************************)

Theorem word_state_rel_get_var:
    word_state_rel reachable s t
    ⇒ get_var v t = get_var v s
Proof
   fs[word_state_rel_def, get_var_def]
QED

Theorem word_state_rel_get_store:
    word_state_rel reachable s t
    ⇒  wordSem$get_store v t = wordSem$get_store v s
Proof
   fs[word_state_rel_def, wordSemTheory.get_store_def]
QED

Theorem word_state_rel_get_vars:
    word_state_rel reachable s t
    ⇒ get_vars vs t = get_vars vs s
Proof
   rw[] >> Induct_on `vs` >> fs[get_vars_def]
   >> drule word_state_rel_get_var >> fs[]
QED

Theorem word_state_rel_set_var:
   word_state_rel reachable s t /\
   (case dest_word_loc v of NONE => ∅ | SOME n => {n}) ⊆
        domain reachable
   ==>
   word_state_rel reachable (set_var n v s)
          (set_var n v t)
Proof
  rw[] >> fs[word_state_rel_def] >>
  CONJ_TAC >- (fs[set_var_def]) >>
  fs[domain_find_loc_state,set_var_def] >>
  irule SUBSET_TRANS >>
  irule_at Any get_locals_insert >> fs[]
QED

(*TODO maybe depreciate?*)
Theorem word_state_rel_set_var_word:
   word_state_rel reachable s t ==>
   word_state_rel reachable (set_var n (Word w) s)
          (set_var n (Word w) t)
Proof
  rw[] >> irule word_state_rel_set_var >>
  fs[dest_word_loc_def]
QED

(*TODO add assum to prove it*)
Theorem word_state_rel_set_vars:
   word_state_rel reachable s t /\
   BIGUNION
           (set
              (MAP (λx'. case dest_word_loc x' of NONE => ∅ | SOME x => {x})
                 l)) ⊆ domain reachable  /\
   LENGTH l0 = LENGTH l ==>
   word_state_rel reachable (set_vars l0 l s)
          (set_vars l0 l t)
Proof
  map_every qid_spec_tac [`l`,`l0`] >>
  Induct_on `l0` >> fs[set_vars_def,alist_insert_def]
  >-(
  `!x. x with locals := x.locals = x` by simp[state_component_equality] >> fs[])
  >> rpt strip_tac >>
  fs[word_state_rel_def,domain_find_loc_state,LENGTH_EQ_NUM,alist_insert_def] >>
  irule SUBSET_TRANS >>
  irule_at Any get_locals_insert >> fs[]
QED

(*This can be strengthened to an equality*)
Theorem word_state_rel_set_fp_var:
   word_state_rel reachable s t ==>
   word_state_rel reachable (set_fp_var n v s)
          (set_fp_var n v t)
Proof
  rw[] >> fs[word_state_rel_def] >>
  CONJ_TAC >- (fs[set_fp_var_def]) >>
  fs[domain_find_loc_state]
QED

Theorem word_state_rel_word_exp:
     ∀ s1 exp s2 reachable . word_state_rel reachable s1 s2
        ⇒ word_exp s2 exp = word_exp s1 exp
Proof
    recInduct word_exp_ind >> rw[word_exp_def]
    >- (drule word_state_rel_get_var >> fs[])
    >- (drule word_state_rel_get_store >> fs[])
    >- (first_x_assum drule >> rw[] >> PURE_TOP_CASE_TAC >> rw[] >>
        PURE_TOP_CASE_TAC >> fs[] >> fs[mem_load_def, word_state_rel_def])
    >- (`MAP (λ a . word_exp s a) wexps = MAP (λ a . word_exp s2 a) wexps` by
            (fs[MAP_EQ_f] >> metis_tac[]) >> fs[])
    >- (first_x_assum drule >> rw[])
QED

Theorem word_state_rel_mem_load:
    word_state_rel reachable s t
    ⇒ mem_load addr t = mem_load addr s
Proof
   fs[word_state_rel_def, mem_load_def]
QED

Theorem word_state_rel_mem_load_32:
  word_state_rel reachable s t ⇒
  mem_load_32 s.memory s.mdomain s.be c =
  mem_load_32 t.memory t.mdomain t.be c
Proof
  gvs[word_state_rel_def]
QED

Theorem word_state_rel_get_fp_var:
    word_state_rel reachable s t
    ⇒ get_fp_var v s = get_fp_var v t
Proof
   fs[word_state_rel_def, get_fp_var_def]
QED

Theorem word_state_rel_assign_NONE:
     ∀ reg exp s reachable t . word_state_rel reachable s t
    ⇒ (assign reg exp s = NONE ⇔  assign reg exp t = NONE)
Proof
    rw[] >>
    drule_then (qspec_then `exp` assume_tac) word_state_rel_word_exp >>
    gvs[assign_def,AllCaseEqs()]
QED

Theorem word_state_rel_inst_NONE:
  ∀ reachable s t i . word_state_rel reachable s t
  ⇒ (inst i s = NONE ⇔ inst i t = NONE)
Proof
   rw[] >>
   drule_then assume_tac word_state_rel_assign_NONE >>
   drule_then assume_tac word_state_rel_get_vars >>
   drule_then assume_tac word_state_rel_get_var >>
   drule_then assume_tac word_state_rel_word_exp >>
   drule_then assume_tac word_state_rel_mem_load >>
   drule_then assume_tac word_state_rel_get_fp_var >>
   fs[word_state_rel_def] >> fs[inst_def] >>
   Cases_on `i` >> fs[]
   >-(
     Cases_on `a` >> fs[] >> every_case_tac >> fs[]
     )
   >-(
     Cases_on `a` >> fs[] >> Cases_on `m` >> fs[]
     >> every_case_tac >> fs[mem_store_def] >> gvs[]
     )
   >-(
     Cases_on `f` >> fs[]
     >> every_case_tac >> fs[]
     )
QED

Theorem word_state_rel_assign_SOME:
  word_state_rel reachable s t ⇒
  ( assign reg exp s = (SOME s1) ∧ assign reg exp t = SOME t1
    ⇒ word_state_rel reachable s1 t1)
Proof
  disch_tac >>
  drule_then assume_tac word_state_rel_word_exp >>
  fs[assign_def] >>
  every_case_tac >> fs[] >>
  rw[] >> gvs[] >>
  fs[word_state_rel_def] >>
  reverse (rpt strip_tac)
    >-(fs[domain_find_loc_state]
      >> fs[set_var_def]
      >> irule SUBSET_TRANS
      >> irule_at Any get_locals_insert
      >> fs[UNION_SUBSET]
      >> Cases_on `exp` >> fs[word_exp_def]
      >> gvs[]
        >- (fs[dest_word_loc_def])
        >- (Cases_on `x` >>
            fs[dest_word_loc_def]
            >> irule SUBSET_IMP
            >> qpat_x_assum `domain (get_locals _) ⊆ domain reachable` (irule_at Any)
            >> fs[domain_get_locals_lookup,get_var_def]
            >> first_x_assum (irule_at Any))
        >- (Cases_on `x` >>
            fs[dest_word_loc_def]
            >> irule SUBSET_IMP
            >> qpat_x_assum `domain (get_store _) ⊆ domain reachable` (irule_at Any)
            >> fs[domain_get_store,wordSemTheory.get_store_def]
            >> first_x_assum (irule_at Any))
        >-(Cases_on `x` >>
            fs[dest_word_loc_def]
            >> every_case_tac >> fs[]
            >> fs[mem_load_def]
            >> irule SUBSET_IMP
            >> qpat_x_assum `domain (get_memory _ _) ⊆ domain reachable` (irule_at Any)
            >> fs[domain_get_memory]
            >> gvs[]
            >> first_x_assum (irule_at Any)
            >> first_x_assum (irule_at Any))
        >-(Cases_on `x` >>
           fs[dest_word_loc_def]
           >> every_case_tac >> fs[])
        >-(Cases_on `x` >>
           fs[dest_word_loc_def]
           >> every_case_tac >> fs[])
      )
    >> (fs[set_var_def])
QED

Theorem word_state_rel_inst_SOME:
  ∀ reachable s t i s1 t1 . word_state_rel reachable s t ⇒
  (inst i s = SOME s1 ∧ inst i t = SOME t1 ⇒ word_state_rel reachable s1 t1)
Proof
  rpt gen_tac >> disch_tac >>
  drule_then assume_tac word_state_rel_assign_SOME >>
  drule_then assume_tac word_state_rel_get_vars >>
  drule_then assume_tac word_state_rel_get_var >>
  drule_then assume_tac word_state_rel_word_exp >>
  drule_then assume_tac word_state_rel_mem_load >>
  drule_then assume_tac word_state_rel_get_fp_var >>
  fs[inst_def] >> Cases_on `i` >> fs[]
  >- (rw[] >> gvs[])
  >- (first_x_assum MATCH_ACCEPT_TAC)
  >- (
    Cases_on `a` >> fs[]
    >- (first_x_assum MATCH_ACCEPT_TAC)
    >- (first_x_assum MATCH_ACCEPT_TAC)
    (* 6 subgoals *)
    >>(rpt (TOP_CASE_TAC >> fs[]) >>
       rw[] >> gvs[] >>
       rpt (irule word_state_rel_set_var_word) >>
       TRY $ first_x_assum MATCH_ACCEPT_TAC))
  >- (
    (* memory cases *)
    rw[AllCaseEqs()]>>
    gvs[word_state_rel_def,mem_store_def,domain_find_loc_state,domain_get_memory,set_var_def,mem_store_byte_aux_def,mem_store_32_def,AllCaseEqs()]
    >>~-(
      [`domain (get_locals (insert _ _ _))`],
      irule SUBSET_TRANS
      >> irule_at Any get_locals_insert
      >> fs[]
      >> fs[dest_word_loc_def]
      >> fs[mem_load_def]
      >> rename1`dest_word_loc ww`
      >> Cases_on `ww`
      >> fs[dest_word_loc_def]
      >> irule SUBSET_THM
      >> qpat_assum `domain (get_memory _ _) ⊆ domain reachable` (irule_at Any)
      >> fs[domain_get_memory]
      >> gvs[] >> METIS_TAC[])
    >>~- (
      [`domain (get_memory _ _) ⊆ domain reachable`],
      irule SUBSET_TRANS
      >> irule_at Any get_memory_update
      >> fs[dest_word_loc_def]
      >> rename1`dest_word_loc ww`
      >> Cases_on `ww`
      >> fs[dest_word_loc_def]
      >> fs[get_var_def]
      >> irule SUBSET_THM
      >> qpat_assum `domain (get_locals _) ⊆ domain reachable` (irule_at Any)
      >> gvs[]
      >> fs[domain_get_locals_lookup]
      >> METIS_TAC[]))
  >- (
    Cases_on `f` >> fs[]
    >>(rpt (TOP_CASE_TAC >> fs[]) >>
       strip_tac >> gvs[] >>
       rpt (irule word_state_rel_set_var_word ORELSE irule word_state_rel_set_fp_var) >>
       TRY $ first_x_assum MATCH_ACCEPT_TAC)
  )
QED

Theorem word_state_rel_pop_env_NONE:
     ∀ reachable s t . word_state_rel reachable s t
    ==> ( pop_env s = NONE <=> pop_env t = NONE )
Proof
   rw[] >> fs[word_state_rel_def,pop_env_def] >>
   rpt (TOP_CASE_TAC >> simp[])
QED

Theorem word_state_rel_pop_env:
     ∀ reachable s t s1 l1 l2 . word_state_rel reachable s t
    ==> pop_env s = SOME (s1)
    ⇒ ∃ t1 . pop_env t = SOME (t1) ∧ word_state_rel reachable s1 t1
Proof
   rw[] >> fs[word_state_rel_def,pop_env_def] >>
   rpt (TOP_CASE_TAC >> fs[]) >> rveq >> fs[] >>
   fs[domain_find_loc_state] >>
  (drule get_stack_hd_thm >> rw[] >> metis_tac[])
QED

Theorem word_state_rel_jump_exc:
     ∀ reachable s t s1 l1 l2 . word_state_rel reachable s t
    ==> jump_exc s = SOME (s1, l1, l2)
    ⇒ ∃ t1 . jump_exc t = SOME (t1, l1, l2) ∧ word_state_rel reachable s1 t1
Proof
    rpt strip_tac >> pop_assum mp_tac >>
    fs[jump_exc_def] >> `s.handler = t.handler ∧ s.stack = t.stack` by
        fs[word_state_rel_def] >> fs[] >>
    EVERY_CASE_TAC >> fs[] >> rw[] >> fs[word_state_rel_def] >> rw[] >>
    fs[domain_find_loc_state] >>
    qmatch_asmsub_abbrev_tac `LASTN A B` >>
    qspecl_then [`B`,`A`] mp_tac get_stack_LASTN >>
    simp[] >> UNABBREV_ALL_TAC >> rw[] >>
    drule get_stack_hd_thm >> ASM_SET_TAC[]
QED

Theorem word_state_rel_gc:
     ∀ reachable s t s1 .
    word_state_rel reachable s t ∧ gc_no_new_locs s.gc_fun ⇒
    gc s = SOME s1 ⇒ ∃ t1 . gc t = SOME t1 ∧ word_state_rel reachable s1 t1
Proof
    rw[] >> qpat_assum `word_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
    qpat_x_assum `gc _ = _` mp_tac >>
    full_simp_tac (srw_ss())[gc_def] >> fs[] >>
    CASE_TAC >> fs[] >> PairCases_on `x` >> fs[] >>
    Cases_on `dec_stack x0 s.stack` >> fs[] >>
    fs[word_state_rel_def] >> rw[] >> fs[] >>
    fs[gc_no_new_locs_def, domain_find_loc_state] >>
    first_x_assum drule >> disch_then drule >> rw[] >> imp_res_tac SUBSET_TRANS
QED

Theorem word_state_rel_alloc:
     ∀ reachable s t res c n s1 . word_state_rel reachable s t ∧
    res ≠ SOME Error ∧ gc_no_new_locs s.gc_fun
    ⇒ alloc c n s = (res, s1) ⇒
        ∃ t1 . alloc c n t = (res, t1) ∧ word_state_rel reachable s1 t1 ∧
      dest_result_loc res ⊆ domain reachable
Proof
    rw[] >> qpat_assum `word_state_rel _ _ _` mp_tac >>
    SIMP_TAC std_ss [Once word_state_rel_def] >>
    strip_tac >> qpat_x_assum `alloc _ _ _ = _` mp_tac >>
    fs[alloc_def] >>
    fs[cut_envs_def,cut_names_def] >>
    Cases_on `domain (FST n) ⊆ domain s.locals` >> fs[] >>
    Cases_on `domain (SND n) ⊆ domain s.locals` >> fs[] >>
    disch_tac >>
    qmatch_asmsub_abbrev_tac `gc s_state` >>
    qmatch_goalsub_abbrev_tac `gc t_state` >>
    qpat_x_assum `(_) = (a,b)` mp_tac >>
    `word_state_rel reachable s_state t_state`
        by (UNABBREV_ALL_TAC >>
            simp[push_env_def, env_to_list_def,
                 wordSemTheory.get_store_def, set_store_def,
                 word_state_rel_def, domain_find_loc_state] >> rw[]
             >> fs[domain_find_loc_state]
             >-(irule SUBSET_TRANS >>
                irule_at (Pos hd) get_store_update >>
                fs[dest_word_loc_def])
            >- fs[stack_list_rearrange_lemma]) >>
    TOP_CASE_TAC >> fs[] >>
    qspecl_then [`reachable`, `s_state`, `t_state`, `x`]
        mp_tac word_state_rel_gc >>
    impl_tac >- fs[push_env_def, Abbr `s_state`]
    >>  rw[] >> fs[] >>
        drule_then assume_tac word_state_rel_pop_env_NONE >>
        drule_then assume_tac word_state_rel_pop_env >>
        qpat_assum `word_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
        qpat_x_assum `(_) = (a,b)` mp_tac >> fs[] >>
        TOP_CASE_TAC >> fs[] >>
        drule_then assume_tac word_state_rel_get_store >> fs[] >>
        qpat_assum `word_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
        TOP_CASE_TAC >> fs[] >>
        fs[has_space_def] >>
        rpt (TOP_CASE_TAC >> fs[]) >>
        strip_tac >> rveq >> fs[flush_state_def, dest_result_loc_def, word_state_rel_def] >>
        fs[domain_find_loc_state,get_locals_def,get_stack_def,get_store_def]
QED

Theorem const_writes_eq_Loc:
  ∀words a c m k l1 l2.
    const_writes a c words m k = Loc l1 l2 ⇒ m k = Loc l1 l2
Proof
  Induct \\ fs [const_writes_def,FORALL_PROD]
  \\ rw [] \\ res_tac \\ fs [APPLY_UPDATE_THM,AllCaseEqs()]
QED
(*TODO move*)
Theorem push_env_def2:
  push_env env handler s =
      (let l0 = toAList (FST env) in
       let (l,permute) = env_to_list (SND env) s.permute in
       let handler = (case handler of NONE => NONE | SOME (w,h,l1,l2) => SOME (s.handler,l1,l2)) in
      let stack = StackFrame s.locals_size l0 l handler::s.stack in
       s with <|stack := stack;
          stack_max := OPTION_MAP2 MAX s.stack_max (stack_size stack);
          permute := permute; handler := (case handler of NONE => s.handler | SOME x => LENGTH s.stack)|>)
Proof
  fs[oneline push_env_def,UNCURRY] >> rpt (TOP_CASE_TAC >> fs[]) >> simp[state_component_equality]
QED

(**************************** MAIN LEMMAS *****************************)
Theorem word_removal_lemma:
     ∀ program state result new_state reachable removed_state .
        wordSem$evaluate (program, state) = (result, new_state) ∧
        result ≠ SOME Error ∧ word_state_rel reachable state removed_state ∧
        gc_no_new_locs state.gc_fun ∧
        no_install program ∧ no_install_code state.code ∧
        no_install_code removed_state.code ∧
        domain (find_word_ref program) ⊆ domain (reachable) ∧
        code_closed reachable state.code
        ⇒ ∃ s .
            wordSem$evaluate (program, removed_state) = (result, s) ∧
            word_state_rel reachable new_state s ∧
            (dest_result_loc result) ⊆ domain (reachable)
Proof
        recInduct wordSemTheory.evaluate_ind >> reverse(rw[]) >>
        qpat_x_assum `evaluate _ = _` mp_tac >>
        qpat_assum `word_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
        drule_then assume_tac word_state_rel_get_vars >>
        drule_then assume_tac word_state_rel_get_var >>
        drule_then assume_tac word_state_rel_get_store >>
        drule_then assume_tac word_state_rel_word_exp
    >-  (
    (* CALL *)
        simp[wordSemTheory.evaluate_def,no_install_def] >>
        ntac 2 (TOP_CASE_TAC >> fs[]) >>
        (*This might want to be moved out*)
        `get_vars args s = SOME [] ⇒ args = []` by (Cases_on `args` >>
            gvs[bad_dest_args_def,get_vars_def,AllCaseEqs()]) >>
        `find_code dest (add_ret_loc ret x) s.code s.stack_size =
            find_code dest (add_ret_loc ret x) removed_state.code s.stack_size`
        by (
         rpt (qpat_x_assum `!x. _` kall_tac) >>
         simp[oneline find_code_def] >>
         TOP_CASE_TAC >> fs[]
         >-(
           fs[bad_dest_args_def] >>
           rename1 `get_vars args s = SOME x` >>
           `x ≠ []`
              by (Cases_on `args` >> gvs[get_vars_def,AllCaseEqs()]) >>
           namedCases_on `add_ret_loc ret x` ["","h t"] >> fs[] >>
           ntac 2 (TOP_CASE_TAC >> fs[]) >>
           `MEM (Loc n 0) x` by
             (Cases_on `ret` >> fs[add_ret_loc_def]
              >- metis_tac[LAST_DEF, MEM_LAST, MEM]
              >- (PairCases_on `x'` >> gvs[add_ret_loc_def,LAST_DEF] >>
                  Cases_on `t` >> fs[] >> metis_tac[LAST_DEF, MEM_LAST, MEM])) >>
           drule_all_then assume_tac get_vars_get_locals >>
           `n ∈ domain reachable`
                by (fs[domain_find_loc_state] >>
                 METIS_TAC[SUBSET_DEF]) >>
           `lookup n s.code = lookup n removed_state.code` by
                 metis_tac[code_rel_def] >> fs[])
         >> `x' ∈ domain reachable` by
                 fs[find_word_ref_def, SUBSET_DEF, domain_union] >>
            `lookup x' s.code = lookup x' removed_state.code` by
                 metis_tac[code_rel_def] >> fs[])
        >> pop_assum (SUBST_ALL_TAC o SYM) >> fs[] >>
        ntac 4 (TOP_CASE_TAC >> fs[])
        (*Tail Call Case*)
        >- (
           ntac 2 (TOP_CASE_TAC >> fs[])
           >- (
               strip_tac >> rveq >>
               simp[dest_result_loc_def,word_state_rel_def,flush_state_def] >>
               fs[domain_find_loc_state,get_locals_def,get_stack_def,get_store_def]) >>
           ntac 2 (TOP_CASE_TAC >> fs[]) >>
           strip_tac >> rveq >>
           qmatch_asmsub_abbrev_tac `evaluate (q',A)` >>
           qmatch_goalsub_abbrev_tac `evaluate (q',B)` >>
           first_x_assum (qspecl_then [`reachable`, `B`] mp_tac) >>
           impl_tac >-(
             fs[Abbr `A`,Abbr `B`] >>
             CONJ_TAC >-(
               rename [`word_state_rel _ _ _`] >>
               simp[word_state_rel_def,dec_clock_def] >>
               simp[call_env_def] >>
               fs[domain_find_loc_state] >>
               Cases_on `dest` >> gvs[find_code_def,add_ret_loc_def,AllCaseEqs()]
               >-(irule SUBSET_TRANS >>
                  qpat_assum `domain (get_locals _) ⊆ _` $ irule_at (Pos last) >>
                  irule get_locals_fromList2_FRONT >> METIS_TAC[])
               >> irule SUBSET_TRANS >>
               qpat_assum `domain (get_locals _) ⊆ _` $ irule_at (Pos last) >>
               Cases_on `q = []` >- simp[fromList2_def,get_locals_def ] >>
               irule get_locals_fromList2 >> METIS_TAC[]) >>
             CONJ_TAC >-(
               rename [`no_install _`] >>
               imp_res_tac no_install_find_code) >>
             qpat_x_assum `code_closed _ _` assume_tac >>
             fs[code_closed_def,is_reachable_def] >>
             simp[SUBSET_DEF] >> rw[] >>
             first_x_assum irule >>
             irule_at Any RTC_SINGLE >>
             simp[is_adjacent_def] >>
             irule_at (Pos hd) lookup_analyse_word_code >>
             Cases_on `dest` >> gvs[find_code_def,AllCaseEqs()] >>
             fs[lookup_fromAList] >>
             first_assum $ irule_at (Pos hd) >>
             (CONJ_TAC >- fs[domain_lookup])
             >- (
             fs[domain_find_loc_state,add_ret_loc_def] >>
             irule SUBSET_THM >>
             qpat_assum `domain (get_locals _) ⊆ _` $ irule_at (Pos last) >>
             irule get_vars_get_locals >>
             METIS_TAC[MEM_LAST_NOT_NIL ])
             >- (fs[find_word_ref_def])) >>
             strip_tac >> fs[])
        (*Regular Call Case*)
        >> qmatch_asmsub_rename_tac`add_ret_loc (SOME l)`
        >>  PairCases_on `l` >> fs[] >>
            Cases_on `domain l1 = {} ∨ ¬ALL_DISTINCT l0` >> fs[] >>
            fs[cut_envs_def,cut_names_def] >>
            Cases_on `domain l1 ⊆ domain s.locals` >>
            fs[] >>
            Cases_on `domain l2 ⊆ domain s.locals` >>
            fs[] >>
            Cases_on `s.clock = 0` >> fs[]
            >- (strip_tac >> rveq >>
               simp[dest_result_loc_def] >>
               simp[flush_state_def,word_state_rel_def,call_env_def] >>
               fs[domain_find_loc_state] >>
               simp[get_locals_def,get_stack_def,get_store_def] >>
               simp[oneline push_env_def,env_to_list_def] >>
               rpt (TOP_CASE_TAC >> fs[])) >>
            fs[add_ret_loc_def] >>
                fs[find_word_ref_def, domain_find_loc_state, domain_union] >>
                `domain (find_word_ref q') ⊆ domain reachable` by (
                    rpt (qpat_x_assum `!x. _` kall_tac) >>
                    Cases_on `dest` >> fs[find_code_def, code_closed_def]
                    >- (
                        fs[AllCaseEqs()] >>
                        rveq >> Cases_on `x` >> rfs[bad_dest_args_def] >>
                        rw[] >>
                        `loc ∈ domain reachable` by (
                            `MEM (Loc loc 0) (h::t)` by
                                metis_tac[MEM, LAST_DEF, MEM_LAST] >>
                            qspecl_then [`args`, `s`, `h::t`, `loc`, `0`] mp_tac
                                get_vars_get_locals >> rw[] >>
                                fs[SUBSET_DEF]) >>
                        rw[SUBSET_DEF] >>
                        qpat_x_assum `∀ n m . n ∈ _ ∧ _ ⇒ _`
                            (qspecl_then [`loc`, `x`] mp_tac) >>
                        reverse(impl_tac) >> fs[] >> fs[is_reachable_def] >>
                        match_mp_tac RTC_SINGLE >> fs[is_adjacent_def] >>
                        fs[domain_lookup, lookup_fromAList] >>
                        irule_at Any lookup_analyse_word_code >>
                        goal_assum (drule_at Any) >>
                        goal_assum drule)
                    >- (
                        fs[AllCaseEqs()] >>
                        rveq >> Cases_on `x` >>
                        fs[] >> rw[SUBSET_DEF] >>
                        qpat_x_assum `∀ n m . n ∈ _ ∧ _ ⇒ _`
                            (qspecl_then [`x'`, `x`] mp_tac) >>
                        reverse(impl_tac) >> fs[] >>
                        fs[is_reachable_def] >> match_mp_tac RTC_SINGLE >>
                        fs[is_adjacent_def, domain_lookup] >>
                        goal_assum (drule_at Any) >>
                        irule lookup_analyse_word_code >>
                        metis_tac[lookup_fromAList])
                        ) >>
                `word_state_rel reachable (call_env q r' (push_env
                    (inter s.locals l1,inter s.locals l2) handler (dec_clock s)))
                    (call_env q r' (push_env (inter s.locals l1,inter s.locals l2) handler
                    (dec_clock removed_state)))` by (
                       rpt (qpat_x_assum `!x. _` kall_tac) >>
                        `∀ e . MEM e q ⇒ (case dest_word_loc e of | NONE => {}
                            | SOME n => {n}) ⊆ domain reachable` by (
                        rw[] >> Cases_on `e` >>
                        fs[dest_word_loc_def, SUBSET_EMPTY] >>
                        Cases_on `dest` >>
                        fs[find_code_def] >>
                        EVERY_CASE_TAC >> fs[] >> rveq >>
                        imp_res_tac MEM_FRONT >> fs[] >>
                        METIS_TAC[get_vars_get_locals,SUBSET_DEF]) >>
                      fs[dec_clock_def, call_env_def, flush_state_def] >>
                      Cases_on `handler`
                      >- (fs[word_state_rel_def, domain_find_loc_state] >>
                          fs[call_env_def,push_env_def,env_to_list_def]
                          >> rw[]
                          >- (rw[SUBSET_DEF] >> fs[domain_get_locals_lookup] >>
                              imp_res_tac fromList2_value >>
                              qpat_x_assum `∀ e . MEM _ _ ⇒ _`
                                (qspec_then `Loc x' n1` mp_tac) >>
                              fs[dest_word_loc_def])
                          >- fs[stack_list_rearrange_lemma])
                      >- (PairCases_on `x'` >> fs[] >>
                          fs[push_env_def, env_to_list_def, word_state_rel_def,
                            domain_find_loc_state] >>
                          rw[]
                          >- (rw[SUBSET_DEF] >> fs[domain_get_locals_lookup] >>
                              imp_res_tac fromList2_value >>
                              qpat_x_assum `∀ e . MEM _ _ ⇒ _`
                                (qspec_then `Loc x' n1` mp_tac) >>
                              fs[dest_word_loc_def])
                          >- fs[stack_list_rearrange_lemma])) >>
                Cases_on `evaluate (q', call_env q r' (push_env
                    (inter s.locals l1,inter s.locals l2) handler (dec_clock s)))` >> fs[] >>
                Cases_on `q'' = SOME Error` >> fs[] >>
                last_x_assum (drule_at (Pos hd)) >>
                impl_tac >- (fs[] >> imp_res_tac no_install_find_code) >>
                strip_tac >> fs[] >>
                Cases_on `q''` >> fs[] >> Cases_on `x'` >> fs[] >>
                TRY (strip_tac >> fs[] >> NO_TAC)
                (*Result Case*)
                >- (
                    drule_then assume_tac word_state_rel_pop_env_NONE >>
                    drule_then assume_tac word_state_rel_pop_env >>
                    qpat_assum `word_state_rel _ _ _` mp_tac >>
                    SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
                    Cases_on `w = Loc l4 l5 ⇒ LENGTH l ≠ LENGTH l0` >> fs[] >>
                    TOP_CASE_TAC >> fs[] >>
                    qpat_assum `word_state_rel _ _ _` mp_tac >>
                    SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
                    TOP_CASE_TAC >> fs[] >>
                    strip_tac >> fs[] >>
                    qmatch_asmsub_abbrev_tac `evaluate (l3,A)` >>
                    qmatch_goalsub_abbrev_tac `evaluate (l3,B)` >>
                    first_x_assum (qspecl_then [`reachable`, `B`] mp_tac) >>
                    impl_tac >- (
                      fs[Abbr`A`,Abbr`B`] >>
                      CONJ_TAC >- (
                      qpat_assum `dest_result_loc _ ⊆ _` assume_tac >>
                      fs[dest_result_loc_def] >>
                      fs[word_state_rel_set_vars])
                       >>
                      CONJ_TAC >-
                            (imp_res_tac pop_env_code_gc_fun_clock  >> fs[] >>
                             imp_res_tac evaluate_consts >> fs[]) >>
                      CONJ_TAC >- fs[no_install_def]
                      >> fs[word_state_rel_def] >>
                      (imp_res_tac no_install_find_code >> fs[]) >>
                      imp_res_tac no_install_evaluate_const_code >>
                      imp_res_tac pop_env_code_gc_fun_clock  >> fs[] >>
                      gvs[]) >>
                    rw[] >> fs[])
                (*Exception Case*)
                >- (
                    namedCases_on `handler`["","h"] >> fs[]
                    >- (rw[] >> fs[]) >>
                    PairCases_on `h` >> fs[] >>
                    TOP_CASE_TAC >> fs[] >>
                    qpat_assum `word_state_rel _ _ _` mp_tac >>
                    SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
                    fs[] >>
                    TOP_CASE_TAC >> fs[] >>
                    strip_tac >> fs[] >>
                    qmatch_asmsub_abbrev_tac `evaluate (h1,A)` >>
                    qmatch_goalsub_abbrev_tac `evaluate (h1,B)` >>
                    first_x_assum (qspecl_then [`reachable`, `B`] mp_tac) >>
                    impl_tac >- (
                      fs[Abbr`A`,Abbr`B`] >>
                      CONJ_TAC >- (
                      qpat_x_assum `dest_result_loc _ ⊆ domain _` assume_tac >>
                      Cases_on `w0` >> fs[]
                      >- (irule word_state_rel_set_var_word >> fs[])
                      >> fs[dest_result_loc_def]
                      >> fs[word_state_rel_def]
                      >> CONJ_TAC >- simp[set_var_def]
                      >> fs[domain_find_loc_state,set_var_def]
                      >> irule SUBSET_TRANS
                      >> irule_at Any get_locals_insert
                      >> fs[dest_word_loc_def])
                      >>
                      CONJ_TAC >-
                            (imp_res_tac evaluate_consts >> fs[]) >>
                      CONJ_TAC >- fs[no_install_def]
                      >> fs[word_state_rel_def] >>
                      (imp_res_tac no_install_find_code >> fs[]) >>
                      imp_res_tac no_install_evaluate_const_code >>
                      gvs[]) >>
                    rw[] >> fs[])
       )
    >- ( (* ShareInst *)
       fs[wordSemTheory.evaluate_def,oneline share_inst_def] >>
       rpt (TOP_CASE_TAC >> fs[]) >>
        gvs[AllCaseEqs(),
        sh_mem_load_def,sh_mem_load_byte_def,
        sh_mem_load32_def,sh_mem_store32_def,
        sh_mem_load16_def,sh_mem_store16_def,
        sh_mem_store_def,sh_mem_store_byte_def,
        DefnBase.one_line_ify NONE sh_mem_set_var_def] >>
      rw[set_var_def,dest_result_loc_def,flush_state_def] >>
      drule_then assume_tac word_state_rel_word_exp >>
      gvs[word_state_rel_def,domain_find_loc_state] >>
      gvs[domain_find_loc_state,domain_get_locals_lookup,
        SUBSET_DEF] >>
      rpt strip_tac >>
      gvs[domain_lookup,lookup_insert,
        PULL_EXISTS,AllCaseEqs(),get_stack_def,get_var_def,get_store_def] >>
      first_x_assum $ drule_then irule )
    >- ( (* FFI *)
        fs[wordSemTheory.evaluate_def,flush_state_def] >>
        rpt (TOP_CASE_TAC >> fs[]) >>
        strip_tac >> rveq >>
        fs[word_state_rel_def] >>
        fs[domain_find_loc_state] >>
        simp[dest_result_loc_def,get_stack_def,get_locals_def,get_store_def] >>
        fs[get_memory_write_bytearray_lemma] >>
        gvs[cut_env_def,cut_envs_def,cut_names_def,AllCaseEqs()] >>
        irule SUBSET_TRANS >> irule_at (Pos hd) get_locals_union_subset
        \\ fs[domain_union]
        \\ fs[SUBSET_DEF]
        \\ rw[]
        \\ imp_res_tac domain_get_locals_lookup
        \\ fs[lookup_inter, case_eq_thms]
        \\ fs[domain_lookup]
        \\ imp_res_tac (SIMP_RULE std_ss [domain_lookup, PULL_FORALL]
            domain_get_locals_lookup)
        \\ fs[]
        )
    >- ( (* DataBufferWrite *)
        simp[wordSemTheory.evaluate_def] >>
        rpt (TOP_CASE_TAC >> fs[]) >>
        strip_tac >> rveq >>
        fs[word_state_rel_def] >>
        fs[domain_find_loc_state, dest_result_loc_def]
        )
    >- ( (* CodeBufferWrite *)
        simp[wordSemTheory.evaluate_def] >>
        rpt (TOP_CASE_TAC >> fs[]) >>
        fs[get_var_def, buffer_write_def] >>
        strip_tac >> rveq >>
        fs[word_state_rel_def] >>
        fs[domain_find_loc_state, dest_result_loc_def]
        )
    >- ( (* Install *)
        fs[no_install_def]
        )
    >- ( (* LocValue *)
        simp[wordSemTheory.evaluate_def] >> fs[find_word_ref_def] >>
        imp_res_tac code_rel_def >>
        Cases_on `l1 ∈ domain s.code` >> fs[] >>
        `l1 ∈ domain removed_state.code` by fs[domain_lookup] >>
        rw[] >> fs[set_var_def, word_state_rel_def] >>
        fs[domain_find_loc_state] >>
        `domain (get_locals (insert r (Loc l1 0) s.locals)) ⊆
            domain (get_locals s.locals) ∪ {l1}`
        by (metis_tac[get_locals_insert_Loc]) >> fs[SUBSET_DEF] >> rw[] >>
        res_tac >> fs[]
        >> fs[dest_result_loc_def]
        )
    >- ( (* If *)
        `get_var_imm ri removed_state = get_var_imm ri s` by (
            Cases_on `ri` >> fs[get_var_imm_def, get_var_def]) >>
        simp[wordSemTheory.evaluate_def] >>
        rpt (TOP_CASE_TAC >> fs[]) >>
        rw[] >>
        fs[find_word_ref_def, domain_union, no_install_def]
        )
    >- ( (* Raise *)
        simp[wordSemTheory.evaluate_def] >>
        TOP_CASE_TAC >> fs[] >>
       `jump_exc s = NONE ⇔ jump_exc removed_state = NONE` by (
            fs[jump_exc_def] >> EVERY_CASE_TAC) >>
        drule word_state_rel_jump_exc >> strip_tac >> Cases_on `jump_exc s` >>
        fs[] >>
        PairCases_on `x'` >> fs[] >> rw[] >> fs[word_state_rel_def]
        >> Cases_on `x` >> fs[dest_result_loc_def] >>
           fs[SUBSET_DEF,get_var_def] >>
            qspecl_then [`n'`, `s.locals`] mp_tac domain_get_locals_lookup >>
            rw[] >>
            fs[domain_find_loc_state] >> res_tac >> fs[]
        )
    >- ( (* Return *)
        simp[wordSemTheory.evaluate_def,flush_state_def] >>
        rpt (TOP_CASE_TAC >> fs[]) >>
        strip_tac >> rveq >>
        simp[dest_result_loc_def] >>
        fs[word_state_rel_def,domain_find_loc_state,get_locals_def] >>
        irule SUBSET_TRANS >>
        qpat_x_assum `domain (get_locals _) ⊆ domain reachable`
        (irule_at (Pos last)) >>
        fs[oneline dest_word_loc_def] >>
        pop_assum mp_tac >>
        rpt (pop_assum kall_tac) >>
        map_every qid_spec_tac $ [`x`,`s`,`ms`] >>
        Induct_on `x` >> rw[] >> fs[]
        >-(Cases_on `ms` >>
           gvs[get_vars_def,AllCaseEqs()] >>
           EVERY_CASE_TAC >>
           fs[get_var_def] >> METIS_TAC[domain_get_locals_lookup])
        >> Cases_on `ms` >> fs[get_vars_def,AllCaseEqs()]
        >> METIS_TAC[])
    >- ( (* Seq *)
        simp[wordSemTheory.evaluate_def] >>
        fs[find_word_ref_def, domain_union] >>
        Cases_on `evaluate (c1, s)` >> fs[] >> Cases_on `q` >> fs[] >> rw[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        strip_tac >> rveq >> fs[no_install_def, find_word_ref_def] >> rw[] >>
        fs[] >> rfs[] >>
        first_x_assum (qspecl_then [`reachable`, `s'`] match_mp_tac) >> fs[] >>
        `s.code = r.code ∧ removed_state.code = s'.code ∧
        r.code = new_state.code ∧ r.gc_fun = s.gc_fun` by
            metis_tac[no_install_evaluate_const_code, evaluate_consts] >>
        rveq >> fs[]
        )
    >- ( (* MustTerminate *)
        simp[wordSemTheory.evaluate_def] >> Cases_on `s.termdep` >> fs[] >>
        Cases_on `evaluate (p, s with <|clock := MustTerminate_limit (:'a);
            termdep := n|>)` >> fs[] >>
        Cases_on `q = SOME TimeOut` >> fs[] >> rw[] >>
        first_x_assum (qspecl_then [`reachable`,
            `removed_state with <|clock := MustTerminate_limit (:'a);
                termdep := n|>`] mp_tac) >>
        impl_tac >> rw[] >>
        fs[no_install_def, word_state_rel_def, find_word_ref_def,
            domain_find_loc_state]
        )
    >- ( (* Tick *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `s.clock = 0` >> fs[]
        >- (fs[call_env_def, flush_state_def, fromList2_def] >>
            rw[word_state_rel_def] >>
            rw[find_loc_state_def, domain_union,
                get_locals_def, get_stack_def, get_store_def] >>
            fs[domain_find_loc_state, SUBSET_DEF, dest_result_loc_def])
        >- (rw[] >> fs[dec_clock_def, word_state_rel_def, domain_find_loc_state,
            dest_result_loc_def])
        )
    >- ( (* Store *)
        simp[wordSemTheory.evaluate_def] >>
        ntac 3 (TOP_CASE_TAC >> fs[]) >>
        fs[mem_store_def] >>
        Cases_on `c ∈ s.mdomain` >> fs[] >> rw[] >>
        fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def] >>
        qspecl_then [`c`, `x`, `s.memory`, `s.mdomain`] mp_tac
            get_memory_update >> fs[] >>
        Cases_on `x` >> fs[dest_word_loc_def] >> rw[]
        >- metis_tac[SUBSET_TRANS] >>
        `n ∈ domain reachable` by (
            fs[get_var_def] >>
            imp_res_tac domain_get_locals_lookup >>
            fs[SUBSET_DEF]) >>
        fs[SUBSET_DEF] >> metis_tac[]
        )
    >- ( (* OpCurrHeap *)
        simp[wordSemTheory.evaluate_def,word_exp_def,the_words_def] >>
        rpt (TOP_CASE_TAC >> fs[]) >> fs[AllCaseEqs()] >>
        strip_tac >> rveq >>
        gvs [dest_result_loc_def,set_var_def] >>
        fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def]
        \\ qspecl_then [`dst`, `Word z`, `s.locals`] mp_tac get_locals_insert
        \\ fs[dest_word_loc_def] \\ metis_tac[SUBSET_TRANS]
        )
    >- ( (* Set *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `v = Handler ∨ v = BitmapBase` >> fs[] >>
        Cases_on `word_exp s exp` >> fs[] >>
        strip_tac >> rveq >>
        fs[set_store_def] >> rw[] >>
        fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def] >>
        fs[find_word_ref_def] >>
        qspecl_then [`s.store`, `v`, `x`] mp_tac get_store_update >>
        Cases_on `x` >> fs[dest_word_loc_def] >> rw[]
        >- metis_tac[SUBSET_TRANS] >>
        `n ∈ domain reachable` by (Cases_on `exp` >> fs[word_exp_def]
            >- (fs[get_var_def] >> metis_tac[domain_get_locals_lookup, SUBSET_DEF])
            >- (fs[wordSemTheory.get_store_def] >> metis_tac[domain_get_store, SUBSET_DEF])
            >- (Cases_on `word_exp s e` >> fs[] >>
                Cases_on `x` >> fs[] >>
                fs[mem_load_def] >> metis_tac[domain_get_memory, SUBSET_DEF])
            >- (Cases_on `the_words (MAP (λa. word_exp s a) l)` >>
                fs[])
            >- (Cases_on `word_exp s e` >> fs[] >>
                Cases_on `x` >> fs[])) >>
        fs[SUBSET_DEF] >> metis_tac[]
        )
    >- ( (* Get *)
        simp[wordSemTheory.evaluate_def] >> fs[] >>
        TOP_CASE_TAC >> fs[] >>
        strip_tac >> rveq >>
        fs[set_var_def,wordSemTheory.get_store_def] >>
        rw[] >>
        fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def] >>
        fs[get_locals_insert_Loc] >>
        qspecl_then [`v`, `x`, `s.locals`] mp_tac get_locals_insert >>
        Cases_on `x` >> fs[dest_word_loc_def] >- metis_tac[SUBSET_TRANS] >>
        rw[] >>
        `n ∈ domain reachable` by metis_tac[domain_get_store, SUBSET_DEF] >>
        fs[SUBSET_DEF] >> metis_tac[]
        )
    >- ( (* Assign *)
        simp[wordSemTheory.evaluate_def] >> fs[] >>
        Cases_on `word_exp s exp` >> fs[] >>
        fs[set_var_def] >> rw[] >> fs[word_state_rel_def, domain_find_loc_state,
            dest_result_loc_def] >>
        qspecl_then [`v`, `x`, `s.locals`] mp_tac get_locals_insert >>
        Cases_on `x` >> fs[dest_word_loc_def] >- metis_tac[SUBSET_TRANS] >>
        rw[] >>
        `n ∈ domain reachable` by (Cases_on `exp` >> fs[word_exp_def]
            >- (fs[get_var_def] >> metis_tac[domain_get_locals_lookup, SUBSET_DEF])
            >- (fs[wordSemTheory.get_store_def] >> metis_tac[domain_get_store, SUBSET_DEF])
            >- (Cases_on `word_exp s e` >> fs[] >> Cases_on `x` >>
                fs[] >>
                fs[mem_load_def] >> metis_tac[domain_get_memory, SUBSET_DEF])
            >- (Cases_on `the_words (MAP (λa. word_exp s a) l)` >>
                fs[])
            >- (Cases_on `word_exp s e` >> fs[] >>
                Cases_on `x` >> fs[])) >>
        fs[SUBSET_DEF] >> metis_tac[]
        )
    >- ( (* Inst *)
        simp[wordSemTheory.evaluate_def] >>
        `inst i s = NONE ⇔ inst i removed_state = NONE` by
            metis_tac[word_state_rel_inst_NONE] >>
        Cases_on `inst i s` >> fs[] >>
        Cases_on `inst i removed_state` >> fs[] >> rw[]
        >- metis_tac[word_state_rel_inst_SOME]
        >- fs[dest_result_loc_def]
        )
    >- ( (* Move *)
        simp[wordSemTheory.evaluate_def] >> EVERY_CASE_TAC >> fs[] >> rw[] >>
        fs[set_vars_def] >>
        fs[word_state_rel_def, domain_find_loc_state] >> fs[alist_insert_def] >>
        fs[SUBSET_DEF, domain_get_locals_lookup] >> rw[] >>
        imp_res_tac get_vars_length_lemma >>
        fs[lookup_alist_insert] >>
        Cases_on `ALOOKUP (ZIP (MAP FST moves, x)) k` >> fs[]
        >- metis_tac[]
        >- (qsuff_tac `MEM x'' x`
            >- metis_tac[get_vars_get_locals, domain_get_locals_lookup]
            >> `LENGTH x = LENGTH (MAP FST moves)` by
                    metis_tac[LENGTH_MAP] >> rveq >>
               metis_tac[ALOOKUP_ZIP_SUCCESS])
        >> fs[dest_result_loc_def]
        )
    >- ( (* StoreConsts *)
        simp[wordSemTheory.evaluate_def] >>
        fs[get_var_def] >>
        every_case_tac >> fs [set_var_def,unset_var_def] >> rw [] >>
        gvs [word_state_rel_def] >>
        irule SUBSET_TRANS >>
        first_x_assum $ irule_at Any >>
        fs [find_loc_state_def,domain_union,dest_result_loc_def] >> fs [SUBSET_DEF] >>
        fs [domain_get_locals_lookup,lookup_insert,AllCaseEqs(),lookup_delete,
            domain_get_memory] >> rw [] >>
        imp_res_tac const_writes_eq_Loc >>
        rw [] >> fs [] >> metis_tac []
        )
    >- ( (* Alloc *)
        simp[wordSemTheory.evaluate_def] >>
        fs[get_var_def] >>
        Cases_on `lookup n s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >>
        metis_tac[word_state_rel_alloc]
        )
    >- ( (* Skip *)
        simp[wordSemTheory.evaluate_def] >> rw[] >>
        fs[word_state_rel_def, dest_result_loc_def]
        )
QED

(**************************** WORD_REMOVAL_THM *****************************)

Theorem word_removal_thm:
     ∀ start state result new_state r reachable code1.
        wordSem$evaluate (Call NONE (SOME start) [0] NONE, state) =
            (result, new_state) ∧
        result ≠ SOME Error ∧ state.code = fromAList code1 ∧
        domain (find_loc_state state) ⊆ domain reachable ∧
        gc_no_new_locs state.gc_fun ∧
        reachable = closure_spt (insert start () LN) (analyse_word_code code1) ∧
        ALL_DISTINCT (MAP FST code1) ∧ no_install_code state.code
        ⇒ ∃ s .
            wordSem$evaluate (Call NONE (SOME start) [0] NONE,
                state with code :=
                    fromAList (remove_word_code reachable code1)) = (result, s)
Proof
    rpt strip_tac >>
    drule word_removal_lemma >> disch_then drule >>
    strip_tac >>
    pop_assum (qspecl_then [`reachable`,
        `state' with code := fromAList(remove_word_code reachable code1)`]
        mp_tac) >>
    reverse(impl_tac) >- metis_tac[] >>
    qspecl_then [`analyse_word_code code1`,`insert start () LN`]
      mp_tac closure_spt_thm >>
    reverse (rw[])
    >- (fs[code_closed_def] >> qexists_tac `code1` >>
        fs[] >> fs[is_reachable_def] >>
        metis_tac[RTC_TRANSITIVE, transitive_def])
    >- (fs[find_word_ref_def, is_reachable_def, RTC_REFL])
    >- (fs[no_install_code_def] >> rw[] >> first_x_assum match_mp_tac >>
        qexists_tac `k` >>
        qexists_tac `n` >> fs[] >> fs[lookup_fromAList] >>
        imp_res_tac ALOOKUP_MEM >>
        imp_res_tac remove_word_code_thm >>
        metis_tac[ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME])
    >- fs[no_install_def]
    >- (fs[word_state_rel_def, code_rel_def, lookup_fromAList] >>
        fs[EXTENSION, SUBSET_DEF] >> rw[] >>
        res_tac >> rename1 `closure_spt x y` >>
        Cases_on `ALOOKUP code1 n` >> fs[]
            >- (fs[ALOOKUP_NONE] >>
                drule remove_word_code_thm_FST >> rw[] >>
                pop_assum (qspecl_then [`n`, `closure_spt x y`] mp_tac) >>
                rw[])
            >- (imp_res_tac ALOOKUP_MEM >> drule remove_word_code_thm >>
                rw[] >>
                pop_assum (qspecl_then [`n`, `closure_spt x y`] mp_tac) >>
                rw[] >> res_tac >>
                `ALL_DISTINCT (MAP FST
                    (remove_word_code (closure_spt x y) code1))` by (
                    fs[remove_word_code_def] >>
                    `MAP FST (FILTER (λx'. IS_SOME (lookup (FST x')
                        (closure_spt x y))) code1)
                        = FILTER (λx'. IS_SOME (lookup x'
                        (closure_spt x y))) (MAP FST code1)` by
                        metis_tac[remove_word_code_MAP_FST_lemma] >>
                    fs[FILTER_ALL_DISTINCT]
                ) >> fs[ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME])
        )
QED

open preamble backendComputeLib sptreeTheory wordLangTheory reachabilityTheory word_elimTheory wordSemTheory wordPropsTheory

val m = Hol_pp.print_apropos;
val f = print_find;

val _ = new_theory "word_elimProof";

val _ = Parse.hide"mem";

(******************************************************** NOINSTALL PREDICATE *********************************************************)

(*  ensures there are no install instructions in the code to be optimised - these will break the dead code elimination
    pass as they introduce new code at runtime, which may reference code that has been eliminated *)
val noInstall_def = Define `
    (noInstall (MustTerminate p) = noInstall p) ∧
    (noInstall (Call ret _ _ handler) = (case ret of
        | NONE => (case handler of
            | NONE => T
            | SOME (_,ph,_,_) => noInstall ph)
        | SOME (_,_,pr,_,_) => (case handler of
            | NONE => noInstall pr
            | SOME (_,ph,_,_) => noInstall ph ∧ noInstall pr))) ∧
    (noInstall (Seq p1 p2) = (noInstall p1 ∧ noInstall p2)) ∧
    (noInstall (If _ _ _ p1 p2) = (noInstall p1 ∧ noInstall p2)) ∧
    (noInstall (Install _ _ _ _ _) = F) ∧
    (noInstall _ = T)
`

val noInstall_ind = theorem "noInstall_ind";

val noInstall_code_def = Define `
    noInstall_code (code : (num # ('a wordLang$prog)) num_map) ⇔
        ∀ k n p . lookup k code = SOME (n, p) ⇒ noInstall p
`

val noInstall_find_code = Q.store_thm("noInstall_find_code",
    `∀ code dest args args1 expr . noInstall_code code ∧ find_code dest args code = SOME (args1, expr)
    ⇒ noInstall expr`,
    rw[noInstall_code_def] >> Cases_on `dest` >> fs[find_code_def] >> EVERY_CASE_TAC >> metis_tac[]
);

val noInstall_evaluate_const_code = Q.store_thm("noInstall_evaluate_const_code",
    `∀ prog s result s1 . evaluate (prog, s) = (result, s1) ∧
        noInstall prog ∧ noInstall_code s.code
    ⇒ s.code = s1.code`,
    recInduct evaluate_ind >> rw[] >> qpat_x_assum `evaluate _ = _` mp_tac >>
    fs[evaluate_def]
    >- (EVERY_CASE_TAC >> fs[] >> rw[] >> imp_res_tac alloc_const >> fs[])
    >- (fs[get_vars_def, set_vars_def] >> EVERY_CASE_TAC >> fs[] >> rw[] >> fs[get_vars_def])
    >- (rw[] >> EVERY_CASE_TAC >> imp_res_tac inst_const_full >> fs[] >> rveq >> fs[])
    >- (EVERY_CASE_TAC >> fs[set_var_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[set_var_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[set_store_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[mem_store_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[call_env_def, dec_clock_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[] >> rename1 `evaluate (p, st)` >> Cases_on `evaluate (p, st)` >>
        fs[noInstall_def] >> EVERY_CASE_TAC >> fs[] >> rw[] >> fs[])
    >- (Cases_on `evaluate (c1,s)` >> fs[noInstall_def] >> CASE_TAC >> rfs[])
    >- (EVERY_CASE_TAC >> fs[call_env_def] >> rw[] >> fs[])
    >- (fs[jump_exc_def] >> EVERY_CASE_TAC >> rw[] >> fs[])
    >- (fs[noInstall_def] >> EVERY_CASE_TAC >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[set_var_def] >> rw[] >> fs[])
    >- (fs[noInstall_def])
    >- (EVERY_CASE_TAC >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> rw[] >> fs[] >> fs[ffiTheory.call_FFI_def] >>
        EVERY_CASE_TAC >> rw[] >> fs[state_component_equality])
    >- (fs[noInstall_def, dec_clock_def, call_env_def, push_env_def, cut_env_def, pop_env_def, set_var_def] >>
        EVERY_CASE_TAC >> rw[] >> fs[] >> metis_tac[noInstall_find_code])
);

(******************************************************** STATE RELATION *********************************************************)

(**************************** DESTWORDLOC, DESTRESULTLOC *****************************)

val destWordLoc_def = Define ` (* 'a word_loc = Word ('a word) | Loc num num *)
    (destWordLoc (Loc n _) = SOME n) ∧
    (destWordLoc (_:'a word_loc) = NONE)
`

val destWordLoc_thm = Q.store_thm("destWordLoc_thm",
    `∀ wl n1 . destWordLoc wl = SOME n1 ⇒ ∃ n0 . wl = Loc n1 n0`,
    Cases_on `wl` >> fs[destWordLoc_def]
);

val destResultLoc_def = Define `
    (destResultLoc (SOME (Result w (Loc n n0))) = {n}) ∧
    (destResultLoc (SOME (Exception w (Loc n n0))) = {n}) ∧
    (destResultLoc _ = {})
`

(**************************** GETLOCALS *****************************)

(* TODO could do alt def using toAList - not necessary though, may not be cleaner *)
val getLocals_def = Define ` (* locals : ('a word_loc) num_map *)
    (getLocals (LN : ('a word_loc) num_map) = LN) ∧
    (getLocals (LS a) = case (destWordLoc a) of
        | SOME n => insert n () LN
        | NONE => LN) ∧
    (getLocals (BN t1 t2) = union (getLocals t1) (getLocals t2)) ∧
    (getLocals (BS t1 a t2) = let t = (union (getLocals t1) (getLocals t2)) in
        case (destWordLoc a) of
            | SOME n => insert n () t
            | NONE => t)
`

(******** THEOREMS ********)

val getLocals_thm = Q.store_thm("getLocals_thm",
    `∀ t n1 n0 locs .
        (∃ n . lookup n (t:('a word_loc) num_map) = SOME (Loc n1 n0)) ∧
        locs = getLocals t ⇒ n1 ∈ domain locs`,
    Induct >> rw[lookup_def, getLocals_def, destWordLoc_def, domain_union]
    >- (fs[lookup_def] >> Cases_on `EVEN n` >> fs[] >> metis_tac[])
    >- (Cases_on `destWordLoc a` >> fs[] >> rw[domain_union] >> fs[lookup_def] >>
        Cases_on `n = 0` >> fs[] >> rveq >> fs[destWordLoc_def] >>
        Cases_on `a` >> fs[destWordLoc_def] >> Cases_on `EVEN n` >> fs[] >> metis_tac[])
);

val domain_getLocals_lookup = Q.store_thm ("domain_getLocals_lookup",
    `∀ n t . n ∈ domain (getLocals t) ⇔ ∃ k n1 . lookup k t = SOME (Loc n n1)`,
    rw[] >> reverse (EQ_TAC) >> rw[]
    >- (match_mp_tac getLocals_thm >> fs[PULL_EXISTS] >> qexists_tac `t` >>
        qexists_tac `n1` >> qexists_tac `k` >> fs[])
    >> Induct_on `t`
        >- rw[getLocals_def, domain_def]
        >- (rw[getLocals_def, domain_def, lookup_def] >> Cases_on `a` >> fs[destWordLoc_def])
        >- (rw[getLocals_def, domain_def, lookup_def] >> fs[domain_union] >> res_tac
            >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
            >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV]))
        >- (rw[getLocals_def, domain_def, lookup_def] >> Cases_on `a` >> fs[destWordLoc_def]
            >- (fs[domain_union] >> res_tac
                >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
                >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV]))
            >- (rveq >> qexists_tac `0n` >> fs[])
            >- (fs[domain_union] >> res_tac
                >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
                >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >> once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])))
);

val getLocals_insert_Loc = Q.store_thm("getLocals_insert_Loc",
    `∀ k n1 n0 (locals : ('a word_loc) num_map).
        domain (getLocals (insert k (Loc n1 n0) locals)) ⊆ domain (getLocals locals) ∪ {n1}`,
        rw[] >> fs[SUBSET_DEF] >>  rw[domain_getLocals_lookup] >> fs[lookup_insert] >> rw[] >>
        Cases_on `k' = k` >> fs[] >> disj1_tac >> qexists_tac `k'` >> qexists_tac `n1'` >> fs[]
);

val getLocals_insert = Q.store_thm("getLocals_insert",
    `∀ k v (locals : ('a word_loc) num_map).
        domain (getLocals (insert k v locals)) ⊆ domain (getLocals locals)
        ∪ (case destWordLoc v of | NONE => {} | SOME n => {n})`,
        reverse(Cases_on `v`) >> fs[destWordLoc_def]
        >- fs[getLocals_insert_Loc]
        >- (rw[] >> fs[SUBSET_DEF] >>  rw[domain_getLocals_lookup] >> fs[lookup_insert] >> rw[] >>
            Cases_on `k' = k` >> fs[] >> qexists_tac `k'` >> qexists_tac `n1` >> fs[])
);

(**************************** GETSTORE *****************************)

val getStore_def = Define ` (* store : store_name |-> 'a word_loc *)
    getStore (st:store_name |-> 'a word_loc) =
        let locSet = SET_TO_LIST (FRANGE st) in
        let locList = MAP THE (FILTER IS_SOME (MAP destWordLoc locSet)) in
        FOLDL (λ acc loc . insert loc () acc) LN locList
`

val domain_getStore = Q.store_thm("domain_getStore",
    `∀ n store . n ∈ domain (getStore store) ⇔ (∃ k n1 . FLOOKUP store k = SOME (Loc n n1))`,
    fs[getStore_def] >> fs[MEM_MAP, MEM_FILTER] >>
    rw[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
    EQ_TAC >> rw[]
    >- (Cases_on `y'` >> fs[destWordLoc_def] >> metis_tac[])
    >- (qexists_tac `Loc n n1` >> qexists_tac `k` >> fs[destWordLoc_def])
);

val getStore_update = Q.store_thm("getStore_update",
    `∀ store k v . domain (getStore (store |+ (k,v))) ⊆ domain (getStore store)
        ∪ (case destWordLoc v of | NONE => {} | SOME n => {n})`,
    Cases_on `v` >> fs[destWordLoc_def] >> rw[] >> fs[SUBSET_DEF] >> rw[domain_getStore] >>
    fs[lookup_insert] >> rw[] >> fs[FLOOKUP_UPDATE] >> Cases_on `k = k'` >> fs[]
    >| [ALL_TAC, disj1_tac] >> qexists_tac `k'` >> qexists_tac `n1` >> fs[]
);

(**************************** GETSTACK *****************************)

(******** GET_NUMWORDLOC_ALIST ********)

val get_NumWordLoc_alist_def = Define `
    get_NumWordLoc_alist (l: (num, 'a word_loc) alist) =
        let locs = MAP THE (FILTER IS_SOME (MAP (destWordLoc o SND) l)) in
        FOLDL (λ acc loc . insert loc () acc) LN locs
`

val get_NumWordLoc_alist_thm = Q.store_thm ("get_NumWordLoc_alist_thm",
    `∀ n e l . (∃ n0 . MEM (Loc n n0) (MAP SND l)) ⇔ n ∈ domain (get_NumWordLoc_alist l)`,
    fs[get_NumWordLoc_alist_def] >> fs[MEM_MAP, MEM_FILTER] >> rw[] >> EQ_TAC >> rw[]
    >- (qexists_tac `destWordLoc (Loc n n0)` >> fs[destWordLoc_def] >>
        qexists_tac `y` >> metis_tac[destWordLoc_def])
    >- (Cases_on `SND y'` >> fs[destWordLoc_def] >>
        qexists_tac `n0` >> qexists_tac `y'` >> fs[])
);

val get_NumWordLoc_alist_getLocals = Q.store_thm ("get_NumWordLoc_alist_getlocals",
    `∀ e . domain (getLocals (fromAList e)) ⊆ domain (get_NumWordLoc_alist e)`,
    Induct >> rw[] >> fs[fromAList_def, get_NumWordLoc_alist_def, domain_def, getLocals_def] >>
    Cases_on `h` >> Cases_on `r` >> fs[destWordLoc_def, fromAList_def]
    >- (qspecl_then [`q`, `Word c`, `(fromAList e)`] mp_tac getLocals_insert >> rw[destWordLoc_def] >> imp_res_tac SUBSET_TRANS)
    >- (qspecl_then [`q`, `Loc n n0`, `(fromAList e)`] mp_tac getLocals_insert >> rw[destWordLoc_def] >>
        fs[Once INSERT_SING_UNION] >> rw[Once UNION_COMM] >> fs[SUBSET_DEF] >> metis_tac[])
);

(******** GETSTACK ********)

val getStack_def = Define ` (* stack : ('a stack_frame) list *)
    (getStack [] = LN:num_set) ∧
    (getStack ((StackFrame e _)::xs) = union (get_NumWordLoc_alist e) (getStack xs))
`

val getStack_ind = theorem "getStack_ind";

(******** THEOREMS ********)

val getStack_hd_thm = Q.store_thm ("getStack_hd_thm",
    `∀ stack reachable l opt t . domain (getStack stack) ⊆ domain reachable ∧ stack = StackFrame l opt::t
        ⇒ domain (getLocals (fromAList l)) ⊆ domain reachable ∧ domain (getStack t) ⊆ domain (reachable)`,
            recInduct getStack_ind >> rw[]
            >- (Cases_on `e` >> fs[getStack_def, domain_union, fromAList_def, getLocals_def] >>
                fs[getStack_def, domain_union, fromAList_def] >>
                metis_tac[get_NumWordLoc_alist_getLocals, SUBSET_TRANS])
            >-  fs[getStack_def, domain_union]
);

val getStack_LASTN = Q.store_thm("getStack_LASTN",
    `∀ stack reachable n . domain (getStack stack) ⊆ domain reachable
    ⇒ domain(getStack (LASTN n stack)) ⊆ domain reachable`,
    recInduct getStack_ind >> rw[getStack_def, LASTN_ALT] >>
    Cases_on `SUC (LENGTH xs) ≤ n` >> fs[getStack_def, domain_union]
);

val getStack_CONS = Q.store_thm("getStack_CONS",
    `∀ h t . domain (getStack [h]) ⊆ domain (getStack (h::t)) ∧ domain (getStack t) ⊆ domain (getStack (h::t))`,
    Cases_on `h` >> fs[getStack_def, domain_union]
);

val getStack_enc_stack = Q.store_thm("getStack_enc_stack",
    `∀ stack reachable . domain (getStack stack) ⊆ domain reachable ⇒ ∀ e . MEM e (enc_stack stack)
    ⇒ (case destWordLoc e of | NONE => {} | SOME n => {n}) ⊆ domain reachable`,
    recInduct getStack_ind >> rw[enc_stack_def, getStack_def, domain_union]
    >- (last_x_assum kall_tac >>
        Cases_on `e'` >> fs[destWordLoc_def] >>
        qsuff_tac `n ∈ domain (get_NumWordLoc_alist e)` >> fs[SUBSET_DEF] >>
        imp_res_tac get_NumWordLoc_alist_thm)
    >- res_tac
);

val getStack_dec_stack = Q.store_thm("getStack_dec_stack",
    `∀ locs stack reachable new_stack . (∀ n n0 . MEM (Loc n n0) locs ⇒ n ∈ domain reachable) ∧
    domain (getStack stack) ⊆ domain reachable ∧ dec_stack locs stack = SOME new_stack
    ⇒ domain (getStack new_stack) ⊆ domain reachable`,
    ho_match_mp_tac dec_stack_ind >> rw[]
    >- (fs[dec_stack_def] >> rveq >> fs[getStack_def])
    >- (`∀ n n0 . MEM (Loc n n0) (DROP (LENGTH l) locs) ⇒ n ∈ domain reachable` by metis_tac[MEM_DROP_IMP] >>
        fs[dec_stack_def] >> Cases_on `dec_stack (DROP (LENGTH l) locs) stack` >> fs[] >>
        first_x_assum (qspec_then `reachable` mp_tac) >> rw[] >> fs[getStack_def, domain_union] >> rw[]
        >- (fs[SUBSET_DEF, GSYM get_NumWordLoc_alist_thm] >> rw[] >> fs[MEM_MAP] >>
            `LENGTH (MAP FST l) = LENGTH (TAKE (LENGTH l) locs)` by fs[LENGTH_TAKE] >>
            fs[MEM_ZIP] >> fs[] >> `n < LENGTH (TAKE (LENGTH l) locs)` by fs[LENGTH_TAKE] >>
            qsuff_tac `MEM (Loc x' n0) locs` >- metis_tac[] >> fs[EL_TAKE] >>
            fs[MEM_EL] >> qexists_tac `n` >> fs[])
        >- res_tac)
    >- fs[dec_stack_def]
);

val s_val_eq_getStack = Q.store_thm("s_val_eq_getStack",
    `∀ stack1 stack2 . s_val_eq stack1 stack2 ⇒ getStack stack1 = getStack stack2`,
        recInduct getStack_ind >> rw[] >> Cases_on `stack2` >> fs[s_val_eq_def] >>
        Cases_on `h` >> fs[s_frame_val_eq_def, getStack_def] >>
        first_x_assum drule >> rw[] >> Cases_on `v0` >> Cases_on `o'` >> fs[s_frame_val_eq_def] >> rw[] >>
        `MAP (destWordLoc o SND) e = MAP (destWordLoc o SND) l` by rw[GSYM MAP_MAP_o] >> fs[] >>
        fs[get_NumWordLoc_alist_def]
);

(**************************** GETMEMORY *****************************)

val getMemory_def = Define ` (* 'a word -> 'a word_loc *)
    getMemory (mem:'a word -> 'a word_loc) (mdom:'a word set) =
        let locSet = SET_TO_LIST(IMAGE mem mdom) in
        let locList = MAP THE (FILTER IS_SOME (MAP destWordLoc locSet)) in
        FOLDL (λ acc loc . insert loc () acc) LN locList
`

val FINITE_mdom_mem = Q.store_thm("FINITE_mdom_mem",
    `∀ mdom . FINITE mdom ⇒ FINITE {mem x | x ∈ mdom}`,
    ho_match_mp_tac FINITE_INDUCT >>
    rw[] >>
    qsuff_tac `{mem x | x = e ∨ x ∈ mdom} = mem e INSERT {mem x | x ∈ mdom}` >- rw[] >>
    fs[EXTENSION] >> metis_tac[]
);

val domain_getMemory = Q.store_thm ("domain_getMemory",
    `∀ mem (mdom : 'a word set) n . (n ∈ domain (getMemory mem mdom) ⇔ (∃ k n1 . k ∈ mdom ∧ mem k = Loc n n1))`,
    fs[getMemory_def, IMAGE_DEF] >> fs[FILTER_MAP, MAP_MAP_o] >> rw[] >>
    `FINITE mdom` by metis_tac[WORD_FINITE] >>
    fs[MEM_MAP, MEM_FILTER] >> `FINITE {mem x | x ∈ mdom}` by metis_tac[FINITE_mdom_mem] >>
    rw[MEM_SET_TO_LIST] >>
    EQ_TAC >> rw[]
    >- (Cases_on `mem x` >> fs[destWordLoc_def] >> metis_tac[])
    >- (qexists_tac `Loc n n1` >> fs[destWordLoc_def] >> metis_tac[])
);

val getMemory_update = Q.store_thm("getMemory_update",
    `∀ k v (memory : 'a word -> 'a word_loc) (mdomain : 'a word set) .
        (domain (getMemory ((k =+ v) memory) mdomain)) ⊆ (domain (getMemory memory mdomain))
        ∪ (case (destWordLoc v) of | NONE => {} | SOME n => {n})`,
        Cases_on `v` >> fs[destWordLoc_def] >> rw[] >> fs[SUBSET_DEF] >> rw[domain_getMemory] >>
        fs[lookup_insert] >> rw[] >> fs[APPLY_UPDATE_THM] >> Cases_on `k' = k` >> fs[]
        >| [ALL_TAC, disj1_tac] >> qexists_tac `k'` >> qexists_tac `n1` >> fs[]
);

(**************************** FINDLOCSTATE *****************************)

val findLocState_def = Define`
    findLocState s =
        let loc = (getLocals s.locals) in
        let sto = (getStore s.store) in
        let sta = (getStack s.stack) in
        let mem = (getMemory s.memory s.mdomain) in
        union (union loc sto) (union sta mem)
`

val domain_findLocState = Q.store_thm("domain_findLocState",
    `∀ s . domain (findLocState s) =
        domain (getLocals s.locals) ∪ domain (getStore s.store) ∪
        domain (getStack s.stack) ∪ domain (getMemory s.memory s.mdomain)`,
    rw[findLocState_def, domain_union, UNION_ASSOC]
);

(**************************** CODE_REL, CODE_CLOSED, GCNONEWLOCS *****************************)

val code_rel_def = Define`
    code_rel (reachable:num_set) s_code (t_code :(num # ('a wordLang$prog)) num_map) =
        ∀ n . n ∈ domain reachable ⇒
            lookup n s_code = lookup n t_code
`

val codeClosed_def = Define`
    codeClosed reachable c1 ⇔ ∃ code1 . c1 = fromAList code1 ∧
        ∀ n m . n ∈ domain reachable ∧ isReachable (mk_wf_set_tree (analyseWordCode code1)) n m ⇒
        m ∈ domain reachable
`

val gcNoNewLocs_def = Define`
    gcNoNewLocs (g:'a gc_fun_type) ⇔  ∀ sta mem mdom sto wl mem1 sto1 sta1 .
        (g (enc_stack sta, mem, mdom, sto) = SOME (wl, mem1, sto1)) ∧ dec_stack wl sta = SOME sta1 ⇒
        domain (getStack sta1) ⊆ domain (getStack sta) ∧ domain (getMemory mem1 mdom) ⊆ domain (getMemory mem mdom) ∧
        domain (getStore sto1) ⊆ domain (getStore sto)
`

(**************************** WORD_STATE_REL *****************************)

val word_state_rel_def = Define `
    word_state_rel (reachable:num_set) t s ⇔
        s.locals         = t.locals ∧
        s.fp_regs        = t.fp_regs ∧
        s.store          = t.store ∧
        s.stack          = t.stack ∧
        s.memory         = t.memory ∧
        s.mdomain        = t.mdomain ∧
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
        code_rel reachable (s.code) (t.code) ∧
        domain (findLocState t) ⊆ domain (reachable)
`


(******************************************************** OTHER LEMMAS *********************************************************)

(**************************** GENERIC LEMMAS *****************************)

val EL_APPEND = Q.store_thm("EL_APPEND",
    `∀ n x e x1 . EL n x = e ∧ n < LENGTH x ⇒ EL n (x ⧺ [x1]) = e`,
    Induct_on `x` >> rw[Once EL] >> Cases_on `n` >> rw[]
);

val ALOOKUP_ZIP_SUCCESS = Q.store_thm ("ALOOKUP_ZIP_SUCCESS",
    `∀ x y k v . LENGTH x = LENGTH y ⇒ ALOOKUP (ZIP (x, y)) k = SOME v ⇒ MEM v y`,
    rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_EL] >> drule EL_ZIP >> rw[] >>
    pop_assum (qspec_then `n` mp_tac) >> rw[] >> imp_res_tac LENGTH_ZIP >> rfs[] >>
    fs[] >> qexists_tac `n` >> fs[]
);

(******** WORDLANG LEMMAS ********)

val get_vars_locals = Q.store_thm("get_vars_locals",
    `∀ args s x y. get_vars args s = SOME x ∧ MEM y x ⇒ ∃ n . lookup n s.locals = SOME y`,
    Induct >- (rw[get_vars_def] >> fs[MEM]) >>
    strip_tac >> strip_tac >> strip_tac >> strip_tac >>
    simp[get_vars_def] >>  Cases_on `get_var h s` >> simp[] >>
    Cases_on `get_vars args s` >> simp[] >> fs[get_var_def] >>
    first_x_assum (qspecl_then [`s`, `x''`, `y`] mp_tac) >> rw[] >>
    Cases_on `MEM y x''` >- metis_tac[] >> fs[MEM] >> rveq >>  qexists_tac `h` >> fs[]
);

(**************************** GETLOCALS/GETMEMORY/GETSTACK LEMMAS *****************************)

val get_vars_getLocals = Q.store_thm("get_vars_getLocals",
    `∀ args s x n n1. get_vars args s = SOME x ∧ MEM (Loc n n1) x
    ⇒ n ∈ domain (getLocals s.locals)`,
    ASSUME_TAC get_vars_locals >>
    strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
    first_x_assum (qspecl_then [`args`, `s`, `x`, `Loc n n1`] mp_tac) >>
    rw[] >> fs[] >> imp_res_tac getLocals_thm >> metis_tac[]
);

val getLocals_fromList2 = Q.store_thm("getLocals_fromList2",
    `∀ args s x t . get_vars args s = SOME x ∧ x ≠ [] ∧ t = fromList2 x
    ⇒ domain (getLocals t) ⊆ domain (getLocals s.locals)`,
    rw[] >> rw[SUBSET_DEF] >>
    qspecl_then [`x'`, `fromList2 x`] mp_tac domain_getLocals_lookup >> rw[] >>
    `MEM (Loc x' n1) x` by (fs[fromList2_value] >> qexists_tac `k` >> fs[]) >>
    metis_tac[get_vars_getLocals]
);

val getLocals_fromList2_extension = Q.store_thm("getLocals_fromList2_extension",
    `∀  x y ys. x ∈ domain (getLocals (fromList2 ys)) ⇒ x ∈ domain (getLocals (fromList2 (ys ⧺ [y])))`,
        rw[] >> fs[domain_getLocals_lookup] >> qexists_tac `k` >> qexists_tac `n1` >>
        Induct_on `ys` >> rw[] >- (fs[fromList2_def, lookup_def]) >>
        fs[lookup_fromList2, lookup_fromList] >> qpat_x_assum `k DIV 2 < LENGTH ys ∧ _ ⇒ _` kall_tac >>
        imp_res_tac EVEN_EXISTS >> rveq >> fs[EVEN_DOUBLE] >>
        `2 * m DIV 2 = m` by (once_rewrite_tac [MULT_COMM] >> fs[MULT_DIV]) >> fs[] >>
        imp_res_tac EL_APPEND >> `LENGTH (h::ys) = SUC (LENGTH ys)` by (Induct_on `ys` >> rw[]) >> fs[]
);

val getLocals_fromList2_FRONT = Q.store_thm("getLocals_fromList2_FRONT",
    `∀ args s x xf t . get_vars args s = SOME x ∧ x ≠ [] ∧ xf = FRONT x ∧ t = fromList2 xf
    ⇒ domain (getLocals t) ⊆ domain (getLocals s.locals)`,
    rw[] >> match_mp_tac SUBSET_TRANS >> qexists_tac `domain (getLocals (fromList2 x))` >>
    reverse(CONJ_TAC) >- metis_tac[getLocals_fromList2]
        >- (`∃ y ys . x = SNOC y ys` by metis_tac[SNOC_CASES] >> FULL_SIMP_TAC std_ss [FRONT_SNOC] >>
            fs[SNOC_APPEND] >> rw[SUBSET_DEF] >> imp_res_tac getLocals_fromList2_extension >> fs[])
);

val getMemory_write_bytearray_lemma = Q.store_thm("getMemory_write_bytearray_lemma",
    `∀ mem mdom reachable c r be . domain(getMemory mem mdom) ⊆ domain reachable
    ⇒ domain (getMemory (write_bytearray c r mem mdom be) mdom) ⊆ domain reachable`,
    Induct_on `r` >> fs[write_bytearray_def] >> rw[] >> fs[mem_store_byte_aux_def] >>
    Cases_on `write_bytearray (c + 1w) r mem mdom be (byte_align c)` >> fs[] >>
    Cases_on `byte_align c ∈ mdom` >> fs[] >> first_x_assum drule >> rw[] >>
    pop_assum (qspecl_then [`c + 1w`, `be`] mp_tac) >> rw[] >>
    qspecl_then [`byte_align c`, `Word (set_byte c h c' be)`, `write_bytearray (c + 1w) r mem mdom be`, `mdom`]
        mp_tac getMemory_update >> rw[destWordLoc_def] >> metis_tac[SUBSET_TRANS]
);

val stack_list_rearrange_lemma = Q.store_thm("stack_list_rearrange_lemma",
    `∀ s reachable locs opt . domain (getLocals s.locals) ⊆ domain reachable ∧ domain (getStack s.stack) ⊆ domain reachable
    ⇒ domain (getStack (StackFrame (list_rearrange (s.permute 0) (QSORT key_val_compare (toAList (inter s.locals locs)))) opt::s.stack))
        ⊆ domain reachable`,
    rw[] >> fs[getStack_def, domain_union] >> rw[SUBSET_DEF] >> imp_res_tac get_NumWordLoc_alist_thm >>
    fs[MEM_MAP] >> fs[mem_list_rearrange, QSORT_MEM] >> Cases_on `y` >> fs[MEM_toAList] >> fs[lookup_inter] >>
    Cases_on `lookup q s.locals` >> fs[] >> Cases_on `lookup q locs` >> fs[] >> rveq >>
    fs[SUBSET_DEF, domain_getLocals_lookup] >> metis_tac[]
);

(**************************** IMPLEMENTATION LEMMAS *****************************)

val removeWordCode_thm_FST = Q.store_thm("removeWordCode_thm_FST",
    `∀ n reachable:num_set l . ALL_DISTINCT (MAP FST l)
    ⇒ (n ∈ domain reachable ∧ MEM n (MAP FST l) ⇔ MEM n (MAP FST (removeWordCode reachable l)))`,
    rw[] >> EQ_TAC >> rw[]
    >- (Induct_on `l` >> rw[] >> fs[removeWordCode_def] >> fs[domain_lookup] >> Cases_on `IS_SOME (lookup (FST h) reachable)` >> fs[])
    >> fs[removeWordCode_def]
    >- (Induct_on `l` >> rw[] >> fs[domain_lookup, IS_SOME_EXISTS])
    >- (fs[MEM_MAP, MEM_FILTER] >> qexists_tac `y` >> rw[])
);

val removeWordCode_MAP_FST_lemma = Q.store_thm("removeWordCode_MAP_FST_lemma",
    `∀ reachable:num_set (l: (ctor_id, ctor_id # α prog) alist) .
        MAP FST (FILTER (λx. IS_SOME (lookup (FST x) reachable)) l) = FILTER (λx. IS_SOME (lookup x reachable)) (MAP FST l)`,
    Induct_on `l` >> rw[]
);

(**************************** WORD_STATE_REL LEMMAS *****************************)

val word_state_rel_word_exp = Q.store_thm("word_state_rel_word_exp",
    `∀ s1 exp s2 reachable . word_state_rel reachable s1 s2 ⇒ word_exp s1 exp = word_exp s2 exp`,
    recInduct word_exp_ind >> rw[word_exp_def]
    >- (fs[word_state_rel_def]) >- (fs[word_state_rel_def])
    >- (first_x_assum drule >> rw[] >> Cases_on `word_exp s2 addr'` >> rw[] >> Cases_on `x` >> fs[] >> fs[mem_load_def, word_state_rel_def])
    >- (`MAP (λ a . word_exp s a) wexps = MAP (λ a . word_exp s2 a) wexps` by (fs[MAP_EQ_f] >> metis_tac[]) >> fs[])
    >- (first_x_assum drule >> rw[])
);

val word_state_rel_inst_NONE = Q.store_thm("word_state_rel_inst_NONE",
    `∀ reachable s t i . word_state_rel reachable s t ⇒ (inst i s = NONE ⇔ inst i t = NONE)`,
    rw[] >> fs[word_state_rel_def] >> Cases_on `i` >> fs[inst_def]
    >- (fs[assign_def] >>
        `word_exp s (Const c) = word_exp t (Const c)` by metis_tac[word_state_rel_word_exp, word_state_rel_def] >>
        fs[] >> Cases_on `word_exp t (Const c)` >> rw[])
    >- (fs[get_var_def, get_vars_def] >> EVERY_CASE_TAC >> fs[assign_def]
       >- (`word_exp s (Op b [Var n0; Var n']) = word_exp t (Op b [Var n0; Var n'])` by
                metis_tac[word_state_rel_word_exp, word_state_rel_def] >> fs[] >>
            Cases_on `word_exp t (Op b [Var n0; Var n'])` >> fs[])
       >- (`word_exp s (Op b [Var n0; Const c]) = word_exp t (Op b [Var n0; Const c])` by
                metis_tac[word_state_rel_word_exp, word_state_rel_def] >> fs[] >>
            Cases_on `word_exp t (Op b [Var n0; Const c])` >> fs[])
       >- (`word_exp s (Shift s' (Var n0) n1) = word_exp t (Shift s' (Var n0) n1)` by
                metis_tac[word_state_rel_word_exp, word_state_rel_def] >> fs[] >>
            Cases_on `word_exp t (Shift s' (Var n0) n1)` >> fs[]))
    >- (`∀ exp . word_exp t exp = word_exp s exp` by metis_tac[word_state_rel_word_exp, word_state_rel_def] >>
        fs[get_var_def, mem_load_def, set_var_def] >> EVERY_CASE_TAC >> rfs[mem_store_def])
    >- (fs[get_fp_var_def, set_var_def, set_fp_var_def, get_var_def] >>
        EVERY_CASE_TAC >> fs[])
);

val word_state_rel_inst_SOME = Q.store_thm ("word_state_rel_inst_SOME",
    `∀ reachable s t i s1 t1 . word_state_rel reachable s t ⇒ (inst i s = SOME s1 ∧ inst i t = SOME t1 ⇒ word_state_rel reachable s1 t1)`,
    fs[inst_def] >> Cases_on `i` >> fs[]
    >- (fs[assign_def] >> fs[word_exp_def] >> fs[set_var_def] >> fs[word_state_rel_def] >> rw[] >> fs[domain_findLocState] >>
        qspecl_then [`n`, `Word c`, `s.locals`] mp_tac getLocals_insert >> rw[destWordLoc_def] >> imp_res_tac SUBSET_TRANS)
    >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
        fs[get_vars_def, get_var_def] >> Cases_on `a` >> fs[] >> `s.locals = t.locals` by fs[word_state_rel_def] >> fs[]
        >- (fs[assign_def] >>
            `word_exp s (Op b [Var n0; case r of Reg r3 => Var r3 | Imm w => Const w]) =
                word_exp t (Op b [Var n0; case r of Reg r3 => Var r3 | Imm w => Const w])` by metis_tac[word_state_rel_word_exp] >> fs[] >>
            Cases_on `word_exp t (Op b [Var n0; case r of Reg r3 => Var r3 | Imm w => Const w])` >> fs[] >> fs[set_var_def] >> rw[] >>
            fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[word_exp_def] >> fs[the_words_def] >> EVERY_CASE_TAC >> fs[] >>
           qspecl_then [`n`, `Word z'`, `s.locals`] mp_tac getLocals_insert >> rw[destWordLoc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (fs[assign_def] >>
            `word_exp s (Shift s' (Var n0) n1) =
                word_exp t (Shift s' (Var n0) n1)` by metis_tac[word_state_rel_word_exp] >> fs[] >>
            Cases_on `word_exp t (Shift s' (Var n0) n1)` >> fs[] >> fs[set_var_def] >> rw[] >>
            fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[word_exp_def] >> fs[the_words_def] >> EVERY_CASE_TAC >> fs[] >>
            qspecl_then [`n`, `Word z'`, `s.locals`] mp_tac getLocals_insert >> rw[destWordLoc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[] >> fs[set_var_def] >> fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[] >>
            qspecl_then [`n`, `Word (c' / c)`, `s.locals`] mp_tac getLocals_insert >> rw[destWordLoc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (fs[set_var_def] >> fs[] >>
            fs[] >> EVERY_CASE_TAC >> fs[] >> fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[] >>
            qspecl_then [`n`, `Word (n2w (w2n c * w2n c' DIV dimword (:α)))`, `s.locals`] mp_tac getLocals_insert >> rw[destWordLoc_def] >>
            qspecl_then [`n0`, `Word (n2w (w2n c * w2n c'))`, `insert n (Word (n2w (w2n c * w2n c' DIV dimword (:α)))) s.locals`]
                mp_tac getLocals_insert >> rw[destWordLoc_def] >> fs[] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[set_var_def] >> fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[] >>
            qspecl_then [`n0`, `Word (n2w ((w2n c' + dimword (:α) * w2n c) MOD w2n c''))`, `s.locals`] mp_tac getLocals_insert >>
            rw[destWordLoc_def] >>
            qspecl_then [`n`, `Word (n2w ((w2n c' + dimword (:α) * w2n c) DIV w2n c''))`,
                `insert n0 (Word (n2w ((w2n c' + dimword (:α) * w2n c) MOD w2n c''))) s.locals`] mp_tac getLocals_insert >>
                rw[destWordLoc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[set_var_def] >> fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[]
            >| [qspecl_then [`n`, `Word (n2w (w2n c + w2n c'))`, `s.locals`] mp_tac getLocals_insert >>
                qspecl_then [`n2`, `Word 1w`, `insert n (Word (n2w (w2n c + w2n c'))) s.locals`] mp_tac getLocals_insert    ,
                qspecl_then [`n`, `Word (n2w (w2n c + w2n c'))`, `s.locals`] mp_tac getLocals_insert >>
                qspecl_then [`n2`, `Word 0w`, `insert n (Word (n2w (w2n c + w2n c'))) s.locals`] mp_tac getLocals_insert    ,
                qspecl_then [`n`, `Word (n2w (w2n c + (w2n c' + 1)))`, `s.locals`] mp_tac getLocals_insert >>
                qspecl_then [`n2`, `Word 1w`, `insert n (Word (n2w (w2n c + (w2n c' + 1)))) s.locals`] mp_tac getLocals_insert    ,
                qspecl_then [`n`, `Word (n2w (w2n c + (w2n c' + 1)))`, `s.locals`] mp_tac getLocals_insert >>
                qspecl_then [`n2`, `Word 0w`, `insert n (Word (n2w (w2n c + (w2n c' + 1)))) s.locals`] mp_tac getLocals_insert] >>
            rw[destWordLoc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[set_var_def] >> fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[] >>
            qspecl_then [`n`, `Word (c + c')`, `s.locals`] mp_tac getLocals_insert
            >| [qspecl_then [`n2`, `Word 1w`, `insert n (Word (c + c')) s.locals`] mp_tac getLocals_insert  ,
                qspecl_then [`n2`, `Word 0w`, `insert n (Word (c + c')) s.locals`] mp_tac getLocals_insert] >>
                rw[destWordLoc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[set_var_def] >> fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[] >>
            qspecl_then [`n`, `Word (c + -1w * c')`, `s.locals`] mp_tac getLocals_insert
            >| [qspecl_then [`n2`, `Word 1w`, `insert n (Word (c + -1w * c')) s.locals`] mp_tac getLocals_insert  ,
                qspecl_then [`n2`, `Word 0w`, `insert n (Word (c + -1w * c')) s.locals`] mp_tac getLocals_insert] >>
                rw[destWordLoc_def] >> imp_res_tac SUBSET_TRANS))
    >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> Cases_on `a` >> fs[] >>
        `word_exp t (Op Add [Var n'; Const c]) = word_exp s (Op Add [Var n'; Const c])` by metis_tac[word_state_rel_word_exp] >>
        Cases_on `m` >> fs[] >> fs[word_exp_def, the_words_def, word_state_rel_def] >> Cases_on `lookup n' s.locals` >> fs[] >>
        Cases_on `x` >> fs[]
        >- (fs[word_op_def, mem_load_def] >> Cases_on `c + c' ∈ s.mdomain` >> fs[] >> fs[set_var_def] >> rw[] >> fs[] >>
            fs[domain_findLocState] >> qspecl_then [`n`, `s.memory (c + c')`, `s.locals`] mp_tac getLocals_insert >> rw[] >>
            Cases_on `s.memory (c + c')` >> fs[destWordLoc_def] >> rw[] >- imp_res_tac SUBSET_TRANS >>
            `n'' ∈ domain reachable` by metis_tac[SUBSET_DEF, domain_getMemory] >> fs[SUBSET_DEF] >> metis_tac[])
        >- (fs[word_op_def, mem_load_byte_aux_def] >> Cases_on `s.memory (byte_align (c + c'))` >> fs[] >>
            Cases_on `byte_align (c + c') ∈ s.mdomain` >> fs[] >> fs[set_var_def] >> rw[] >> fs[domain_findLocState] >>
            qspecl_then [`n`, `Word (w2w (get_byte (c + c') c'' s.be))`, `s.locals`] mp_tac getLocals_insert >> rw[destWordLoc_def] >>
            rw[] >> imp_res_tac SUBSET_TRANS)
        >- (fs[word_op_def, get_var_def] >> Cases_on `lookup n s.locals` >> fs[] >> fs[mem_store_def] >>
            Cases_on `c + c' ∈ s.mdomain` >> fs[] >> rw[] >> fs[domain_findLocState] >>
            qspecl_then [`c + c'`, `x`, `s.memory`, `s.mdomain`] mp_tac getMemory_update >> rw[] >>
            Cases_on `x` >> fs[destWordLoc_def] >> rw[] >- imp_res_tac SUBSET_TRANS >>
            `n'' ∈ domain reachable` by metis_tac[SUBSET_DEF, domain_getLocals_lookup] >> fs[SUBSET_DEF] >> metis_tac[])
        >- (fs[word_op_def, get_var_def] >> Cases_on `lookup n s.locals` >> fs[] >> Cases_on `x` >> fs[] >> fs[mem_store_byte_aux_def] >>
            Cases_on `s.memory (byte_align (c + c'))` >> fs[] >> Cases_on `byte_align (c + c') ∈ s.mdomain` >> fs[] >>
            rw[] >> fs[domain_findLocState] >> qspecl_then [`byte_align (c + c')`, `Word(set_byte (c + c') (w2w c'') c''' s.be)`,
                `s.memory`, `s.mdomain`] mp_tac getMemory_update >> rw[] >> fs[destWordLoc_def] >> rw[] >> imp_res_tac SUBSET_TRANS))
    >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
        fs[get_var_def, get_fp_var_def, set_fp_var_def, set_var_def] >> `t.fp_regs = s.fp_regs` by fs[word_state_rel_def] >>
        EVERY_CASE_TAC >> fs[] >> fs[word_state_rel_def, domain_findLocState] >> rw[] >> fs[] >>
        `∀ w . domain (getLocals (insert n (Word w) s.locals)) ⊆ domain reachable` by
            (rw[] >> qspecl_then [`n`, `Word w`, `s.locals`] mp_tac getLocals_insert >>
             fs[destWordLoc_def] >> rw[] >> imp_res_tac SUBSET_TRANS) >> fs[] >>
        rfs[] >>
        qspecl_then [`n`, `Word ((31 >< 0) x)`, `s.locals`] mp_tac getLocals_insert >>
        qspecl_then [`n0`, `Word ((63 >< 32) x)`, `insert n (Word ((31 >< 0) x)) s.locals`] mp_tac getLocals_insert >>
        rw[destWordLoc_def] >> imp_res_tac SUBSET_TRANS)
);

val word_state_rel_jump_exc = Q.store_thm("word_state_rel_jump_exc",
    `∀ reachable s t s1 l1 l2 . word_state_rel reachable s t ==> jump_exc s = SOME (s1, l1, l2)
    ⇒ ∃ t1 . jump_exc t = SOME (t1, l1, l2) ∧ word_state_rel reachable s1 t1`,
    strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
    fs[jump_exc_def] >> `s.handler = t.handler ∧ s.stack = t.stack` by fs[word_state_rel_def] >> fs[] >>
    EVERY_CASE_TAC >> fs[] >> rw[] >> fs[word_state_rel_def] >> rw[] >> fs[domain_findLocState] >>
    `domain (getStack (StackFrame l (SOME (q,l1,l2))::t')) ⊆ domain reachable` by metis_tac[getStack_LASTN] >>
    drule getStack_hd_thm >> rw[]
);

val word_state_rel_gc = Q.store_thm("word_state_rel_gc",
    `∀ reachable s t s1 . word_state_rel reachable s t ∧ gcNoNewLocs s.gc_fun ⇒
    gc s = SOME s1 ⇒ ∃ t1 . gc t = SOME t1 ∧ word_state_rel reachable s1 t1`,
    rw[] >> qpat_assum `word_state_rel _ _ _` mp_tac >> SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
    qpat_x_assum `gc _ = _` mp_tac >>
    full_simp_tac (srw_ss())[gc_def] >> fs[] >>
    CASE_TAC >> fs[] >> PairCases_on `x` >> fs[] >>
    Cases_on `dec_stack x0 s.stack` >> fs[] >>
    fs[word_state_rel_def] >> rw[] >> fs[] >>
    fs[gcNoNewLocs_def, domain_findLocState] >>
    first_x_assum drule >> disch_then drule >> rw[] >> imp_res_tac SUBSET_TRANS
);

val word_state_rel_alloc = Q.store_thm("word_state_rel_alloc",
    `∀ reachable s t res c n s1 . word_state_rel reachable s t ∧ res ≠ SOME Error ∧ gcNoNewLocs s.gc_fun
    ⇒ alloc c n s = (res, s1) ⇒ ∃ t1 . alloc c n t = (res, t1) ∧ word_state_rel reachable s1 t1 ∧
      destResultLoc res ⊆ domain reachable`,
    rw[] >> qpat_assum `word_state_rel _ _ _` mp_tac >> SIMP_TAC std_ss [Once word_state_rel_def] >>
    strip_tac >> qpat_x_assum `alloc _ _ _ = _` mp_tac >>
    fs[alloc_def] >> fs[cut_env_def, domain_findLocState] >>
    Cases_on `domain n ⊆ domain s.locals` >> fs[] >> CASE_TAC >> fs[] >>
    `word_state_rel reachable (push_env (inter s.locals n) NONE (set_store AllocSize (Word c) s))
        (push_env (inter s.locals n) NONE (set_store AllocSize (Word c) t))` by (
            simp[push_env_def, env_to_list_def, set_store_def, word_state_rel_def, domain_findLocState] >> rw[]
            >- (qspecl_then [`s.store`, `AllocSize`, `Word c`] mp_tac getStore_update >> fs[destWordLoc_def] >>
                rw[] >> imp_res_tac SUBSET_TRANS)
            >- fs[stack_list_rearrange_lemma]) >>
    `(push_env (inter s.locals n) NONE (set_store AllocSize (Word c) s)).gc_fun = s.gc_fun` by
        fs[env_to_list_def, push_env_def, set_store_def] >> fs[] >> rw[] >>
    qmatch_asmsub_abbrev_tac `gc s_state` >> qmatch_goalsub_abbrev_tac `gc t_state` >>
    qspecl_then [`reachable`, `s_state`, `t_state`, `x`] mp_tac word_state_rel_gc >>
    impl_tac >- fs[push_env_def, Abbr `s_state`]
    >>  rw[] >> fs[] >>
        qpat_assum `word_state_rel _ _ _` mp_tac >> SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
        qpat_x_assum `(_) = (a,b)` mp_tac >> fs[pop_env_def] >> Cases_on `x.stack` >> fs[] >>
        Cases_on `h` >> fs[] >> Cases_on `o'` >> fs[] >| [ALL_TAC, (Cases_on `x'` >> fs[])] >>
        EVERY_CASE_TAC >> fs[has_space_def, call_env_def, fromList2_def] >> rfs[] >>
        strip_tac >> rveq >> fs[destResultLoc_def, word_state_rel_def] >> rw[] >>
        fs[domain_findLocState]
        >- (drule getStack_hd_thm >> rw[] >> metis_tac[]) >- (fs[getLocals_def, getStack_def])
        >- (drule getStack_hd_thm >> rw[] >> metis_tac[]) >- (fs[getLocals_def, getStack_def])
);


(******************************************************** MAIN PROOFS *********************************************************)

(**************************** WORD_REMOVAL LEMMA *****************************)

val word_removal_lemma = Q.store_thm ("word_removal_lemma",
    `∀ program state result new_state reachable removed_state .
        wordSem$evaluate (program, state) = (result, new_state) ∧
        result ≠ SOME Error ∧ word_state_rel reachable state removed_state ∧
        gcNoNewLocs state.gc_fun ∧
        noInstall program ∧ noInstall_code state.code ∧ noInstall_code removed_state.code ∧
        domain (findWordRef program) ⊆ domain (reachable) ∧
        codeClosed reachable state.code
        ⇒ ∃ s .
            wordSem$evaluate (program, removed_state) = (result, s) ∧
            word_state_rel reachable new_state s ∧
            (destResultLoc result) ⊆ domain (reachable)`
    ,
        recInduct wordSemTheory.evaluate_ind >> reverse(rw[]) >>
        qpat_x_assum `evaluate _ = _` mp_tac >> qpat_assum `word_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
        `∀ args . get_vars args removed_state = get_vars args s` by (
            Induct >> rw[get_vars_def] >> rw[get_var_def] >> rw[])
    >| [

    (* CALL - DONE !!! *)
        simp[wordSemTheory.evaluate_def] >> Cases_on `get_vars args s` >> fs[] >>
        Cases_on `bad_dest_args dest args` >> fs[noInstall_def] >>
        `get_vars args s = SOME [] ⇒ args = []` by (Cases_on `args` >>
            fs[get_vars_def] >> Cases_on `get_var h s` >> fs[] >>
            Cases_on `get_vars t s` >> fs[] >> rveq >> fs[NOT_CONS_NIL]) >>
        `find_code dest (add_ret_loc ret x) s.code =
            find_code dest (add_ret_loc ret x) removed_state.code` by (
                Cases_on `dest` >> rw[find_code_def] >> Cases_on `x` >> rfs[bad_dest_args_def]
                >- (Cases_on `LAST (add_ret_loc ret (h::t))` >> fs[] >> Cases_on `n0` >> fs[] >>
                    `MEM (Loc n 0) (h::t)` by (Cases_on `ret` >> fs[add_ret_loc_def]
                        >- metis_tac[LAST_DEF, MEM_LAST, MEM]
                        >- (PairCases_on `x` >> fs[add_ret_loc_def] >> metis_tac[LAST_DEF, MEM_LAST, MEM])) >>
                    qspecl_then [`args`, `s`, `h::t`, `n`, `0`] mp_tac get_vars_getLocals >> rw[] >>
                    `n ∈ domain reachable` by (qspec_then `s` mp_tac domain_findLocState >>
                        fs[SUBSET_DEF, SUBSET_UNION, SUBSET_TRANS]) >>
                    `lookup n s.code = lookup n removed_state.code` by metis_tac[code_rel_def] >> fs[])
                >> `x' ∈ domain reachable` by fs[findWordRef_def, SUBSET_DEF, domain_union] >>
                   `lookup x' s.code = lookup x' removed_state.code` by metis_tac[code_rel_def] >> fs[]
        ) >> rveq >> Cases_on `find_code dest (add_ret_loc ret x) removed_state.code` >> fs[] >>
        PairCases_on `x'` >> fs[] >> Cases_on `ret` >> fs[]
        >- (Cases_on `handler` >> fs[] >> Cases_on `s.clock = 0` >> fs[]
            >- (fs[call_env_def, fromList2_def] >> rw[word_state_rel_def] >>
                rw[findLocState_def, domain_union, getLocals_def, getStack_def] >>
                fs[domain_findLocState, SUBSET_DEF, destResultLoc_def])
            >- (`word_state_rel reachable (call_env x'0 (dec_clock s))
                (call_env x'0 (dec_clock removed_state))` by (
                    rw[word_state_rel_def, call_env_def, dec_clock_def] >>
                    fs[findLocState_def, domain_union, domain_findLocState] >> fs[add_ret_loc_def] >>
                    Cases_on `dest` >> fs[find_code_def] >> Cases_on `x` >> rfs[bad_dest_args_def]
                    >- (Cases_on `LAST (h::t)` >> fs[] >> Cases_on `n0` >> fs[] >>
                        qspecl_then [`args`, `s`, `(h::t)`, `n`, `0`] mp_tac get_vars_getLocals >> strip_tac >>
                        `n ∈ domain reachable` by (qspec_then `s` mp_tac domain_findLocState >> rw[] >>
                            metis_tac[SUBSET_DEF, SUBSET_UNION, SUBSET_TRANS, MEM_LAST]) >>
                        `lookup n s.code = lookup n removed_state.code` by metis_tac[code_rel_def] >> fs[] >>
                        Cases_on `lookup n removed_state.code` >> fs[] >> Cases_on `x` >> fs[] >>
                        qspecl_then [`args`, `s`, `(h::t)`, `x'0`, `fromList2 x'0`] mp_tac getLocals_fromList2_FRONT >>
                        rw[] >> metis_tac[SUBSET_TRANS])
                    >>  fs[findWordRef_def, domain_insert] >>
                        `lookup x' s.code = lookup x' removed_state.code` by metis_tac[code_rel_def] >>
                        Cases_on `lookup x' removed_state.code` >> fs[] >> Cases_on `x` >> fs[]
                        >- (rw[SUBSET_DEF] >> fs[SUBSET_DEF, fromList2_def, getLocals_def])
                        >- (qspecl_then [`args`, `s`, `(h::t)`, `fromList2 (h::t)`] mp_tac getLocals_fromList2 >>
                            rw[] >> metis_tac[SUBSET_TRANS])) >>
                Cases_on `evaluate (x'1, call_env x'0 (dec_clock s))` >> fs[] >>
                Cases_on `q = SOME Error` >> fs[] >> first_x_assum drule >>
                reverse(impl_tac) >- (strip_tac >> fs[] >> Cases_on `q` >> fs[] >> rw[] >> fs[])
                    >- (rw[dec_clock_def, call_env_def] >> fs[add_ret_loc_def] >> Cases_on `dest` >> fs[find_code_def]
                        >- (EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >> fs[noInstall_code_def] >> res_tac)
                        >- (EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >> fs[noInstall_code_def] >> res_tac)
                        >- (`∃ y ys . x = SNOC y ys` by metis_tac[SNOC_CASES] >> full_simp_tac std_ss [LAST_SNOC, FRONT_SNOC] >>
                            Cases_on `y` >> fs[] >> Cases_on `n0` >> fs[] >> Cases_on `lookup n s.code` >> fs[] >>
                            Cases_on `x'` >> fs[] >> rveq >> fs[ADD1] >> rveq >> fs[domain_findLocState] >>
                            `n ∈ domain reachable` by (
                                qspecl_then [`args`, `s`, `SNOC (Loc n 0) x'0`, `n`, `0`] mp_tac get_vars_getLocals >>
                                strip_tac >> fs[MEM_SNOC] >> rfs[] >> qspec_then `s` mp_tac domain_findLocState >>
                                rw[] >> fs[SUBSET_UNION, SUBSET_DEF]) >>
                            fs[codeClosed_def] >> simp[SUBSET_DEF] >> rw[] >> last_x_assum drule >> disch_then match_mp_tac >>
                            fs[isReachable_def] >> match_mp_tac RTC_SINGLE >> fs[isAdjacent_def] >>
                            `∃ aSetx . lookup n (analyseWordCode code1) = SOME aSetx ∧ x ∈ domain aSetx` by (
                                rfs[lookup_fromAList] >> drule lookup_analyseWordCode >> fs[]) >>
                            drule lookup_mk_wf_set_tree >> rw[] >> asm_exists_tac >> fs[] >> fs[domain_lookup] >>
                            `wf_set_tree (mk_wf_set_tree (analyseWordCode code1))`
                                by metis_tac[mk_wf_set_tree_thm] >>
                            fs[wf_set_tree_def] >> last_x_assum drule >> fs[SUBSET_DEF, domain_lookup])
                        >- (fs[findWordRef_def] >> rename1 `n ∈ domain reachable` >> rename1 `get_vars _ _ = SOME z` >>
                            fs[codeClosed_def] >> simp[SUBSET_DEF] >> rw[] >> last_x_assum drule >> disch_then match_mp_tac >>
                            fs[isReachable_def] >> match_mp_tac RTC_SINGLE >> fs[isAdjacent_def] >>
                            `∃ aSetx . lookup n (analyseWordCode code1) = SOME aSetx ∧ x ∈ domain aSetx` by (
                                rfs[lookup_fromAList] >> Cases_on `ALOOKUP code1 n` >> fs[] >>
                                Cases_on `x'` >> fs[] >> drule lookup_analyseWordCode >> fs[]) >>
                            drule lookup_mk_wf_set_tree >> rw[] >> asm_exists_tac >> fs[] >> fs[domain_lookup] >>
                            `wf_set_tree (mk_wf_set_tree (analyseWordCode code1))`
                                by metis_tac[mk_wf_set_tree_thm] >>
                            fs[wf_set_tree_def] >> last_x_assum drule >> fs[SUBSET_DEF, domain_lookup]))
               )
           )
        >>  PairCases_on `x'` >> fs[] >> Cases_on `domain x'1' = {}` >> fs[] >>
            fs[cut_env_def] >> Cases_on `domain x'1' ⊆ domain s.locals` >> fs[] >>
            Cases_on `s.clock = 0` >> fs[]
            >- (fs[call_env_def, fromList2_def] >> rw[word_state_rel_def] >>
                rw[findLocState_def, domain_union, getLocals_def, getStack_def] >>
                fs[domain_findLocState, SUBSET_DEF, destResultLoc_def])
            >>  fs[add_ret_loc_def] >> fs[findWordRef_def, domain_findLocState, domain_union] >>
                `domain (findWordRef x'1) ⊆ domain reachable` by (Cases_on `dest` >> fs[find_code_def, codeClosed_def]
                    >- (Cases_on `LAST (Loc x'3 x'4 :: x)`>> fs[] >> Cases_on `lookup n s.code` >> fs[] >>
                        Cases_on `n0` >> fs[] >> Cases_on `x'` >> fs[] >> rveq >> Cases_on `x` >> rfs[bad_dest_args_def] >> rw[] >>
                        `n ∈ domain reachable` by (`MEM (Loc n 0) (h::t)` by metis_tac[MEM, LAST_DEF, MEM_LAST] >>
                            qspecl_then [`args`, `s`, `h::t`, `n`, `0`] mp_tac get_vars_getLocals >> rw[] >> fs[SUBSET_DEF]) >>
                            rw[SUBSET_DEF] >> qpat_x_assum `∀ n m . n ∈ _ ∧ _ ⇒ _` (qspecl_then [`n`, `x`] mp_tac) >>
                            reverse(impl_tac) >> fs[] >> fs[isReachable_def] >> match_mp_tac RTC_SINGLE >> fs[isAdjacent_def] >>
                            `wf_set_tree(mk_wf_set_tree (analyseWordCode code1))` by metis_tac[mk_wf_set_tree_thm] >>
                            fs[wf_set_tree_def] >> qexists_tac `findWordRef r` >> fs[lookup_analyseWordCode] >>
                            `lookup n (analyseWordCode code1) = SOME (findWordRef r)` by fs[lookup_fromAList, lookup_analyseWordCode] >>
                            imp_res_tac lookup_mk_wf_set_tree >> `wf (findWordRef r) ∧ wf y` by metis_tac[wf_findWordRef] >>
                            `y = findWordRef r` by (fs[spt_eq_thm, domain_lookup, EXTENSION] >> rw[] >>
                                Cases_on `lookup n' y` >> fs[] >> Cases_on `lookup n' (findWordRef r)` >> fs[] >> rfs[] >>
                                qpat_x_assum `∀ x . lookup _ _ = _ ⇔ _` (qspec_then `n'` mp_tac) >> rw[] >> fs[]) >> rveq >>
                            fs[domain_lookup, SUBSET_DEF] >> metis_tac[])
                    >- (Cases_on `lookup x' s.code` >> fs[] >> Cases_on `x''` >> fs[] >> rw[SUBSET_DEF] >>
                        qpat_x_assum `∀ n m . n ∈ _ ∧ _ ⇒ _` (qspecl_then [`x'`, `x''`] mp_tac) >> reverse(impl_tac) >> fs[] >>
                        fs[isReachable_def] >> match_mp_tac RTC_SINGLE >> fs[isAdjacent_def] >>
                        `wf_set_tree(mk_wf_set_tree (analyseWordCode code1))` by metis_tac[mk_wf_set_tree_thm] >>
                        fs[wf_set_tree_def] >> qexists_tac `findWordRef r` >> fs[lookup_analyseWordCode] >>
                        `lookup x' (analyseWordCode code1) = SOME (findWordRef r)` by (match_mp_tac lookup_analyseWordCode >>
                            qexists_tac `SUC (LENGTH x)` >> metis_tac[lookup_fromAList]) >> imp_res_tac lookup_mk_wf_set_tree >>
                        `wf (findWordRef r) ∧ wf y` by metis_tac[wf_findWordRef] >>
                        `y = findWordRef r` by (fs[spt_eq_thm, domain_lookup, EXTENSION] >> rw[] >>
                        Cases_on `lookup n y` >> fs[] >> Cases_on `lookup n (findWordRef r)` >> fs[] >> rfs[] >>
                        qpat_x_assum `∀ x . lookup _ _ = _ ⇔ _` (qspec_then `n` mp_tac) >> rw[] >> fs[]) >> rveq >>
                        fs[domain_lookup, SUBSET_DEF] >> metis_tac[]) ) >>
                `codeClosed reachable (call_env x'0 (push_env (inter s.locals x'1') handler (dec_clock s))).code` by (
                    fs[call_env_def, dec_clock_def] >> Cases_on `handler` >> TRY(PairCases_on `x'` >> fs[]) >>
                    fs[push_env_def, env_to_list_def] ) >>
                `word_state_rel reachable (call_env x'0 (push_env (inter s.locals x'1') handler (dec_clock s)))
                    (call_env x'0 (push_env (inter s.locals x'1') handler (dec_clock removed_state)))` by (
                    `∀ e . MEM e x'0 ⇒ (case destWordLoc e of | NONE => {} | SOME n => {n}) ⊆ domain reachable` by (
                        rw[] >> Cases_on `e` >> fs[destWordLoc_def, SUBSET_EMPTY] >> Cases_on `dest` >> fs[find_code_def] >>
                        EVERY_CASE_TAC >> fs[] >> rveq >> imp_res_tac MEM_FRONT >> fs[] >>
                        qspecl_then [`args`, `s`, `x`, `n`, `n0`] mp_tac get_vars_getLocals >> rw[] >> fs[SUBSET_DEF]) >>
                      fs[dec_clock_def, call_env_def] >> Cases_on `handler`
                      >- (fs[push_env_def, env_to_list_def] >> fs[word_state_rel_def, domain_findLocState] >> rw[]
                          >- (rw[SUBSET_DEF] >> fs[domain_getLocals_lookup] >> imp_res_tac fromList2_value >>
                              qpat_x_assum `∀ e . MEM _ _ ⇒ _` (qspec_then `Loc x' n1` mp_tac) >> fs[destWordLoc_def])
                          >- fs[stack_list_rearrange_lemma])
                      >- (PairCases_on `x'` >> fs[] >> fs[push_env_def, env_to_list_def, word_state_rel_def, domain_findLocState] >>
                          rw[]
                          >- (rw[SUBSET_DEF] >> fs[domain_getLocals_lookup] >> imp_res_tac fromList2_value >>
                              qpat_x_assum `∀ e . MEM _ _ ⇒ _` (qspec_then `Loc x' n1` mp_tac) >> fs[destWordLoc_def])
                          >- fs[stack_list_rearrange_lemma]) ) >>
                Cases_on `evaluate (x'1, call_env x'0 (push_env (inter s.locals x'1') handler (dec_clock s)))` >> fs[] >>
                Cases_on `q` >> fs[] >> Cases_on `x'` >> fs[] >>
                `r.gc_fun = s.gc_fun` by (
                    fs[call_env_def, dec_clock_def] >> Cases_on `handler` >> fs[push_env_def, env_to_list_def]
                    >- (drule evaluate_consts >> fs[]) >> PairCases_on `x'` >> fs[push_env_def, env_to_list_def]
                    >> drule evaluate_consts >> fs[] ) >>
                `gcNoNewLocs (call_env x'0 (push_env (inter s.locals x'1') handler (dec_clock s))).gc_fun` by (
                    fs[call_env_def, dec_clock_def] >> Cases_on `handler` >> fs[push_env_def, env_to_list_def] >>
                    PairCases_on `x'` >> fs[push_env_def, env_to_list_def] )
                >- (Cases_on `w ≠ Loc x'3 x'4` >> fs[] >> fs[pop_env_def] >> Cases_on `r.stack` >> fs[] >>
                    Cases_on `h` >> fs[] >> Cases_on `o'` >> fs[]
                    >- (Cases_on `domain (fromAList l) = domain (inter s.locals x'1')` >> fs[] >> rw[] >>
                        first_x_assum (qspecl_then [`reachable`,
                            `call_env x'0 (push_env (inter s.locals x'1') handler (dec_clock removed_state))`] mp_tac) >>
                        rw[] >> fs[] >> `noInstall x'1` by metis_tac[noInstall_find_code] >> fs[] >>
                        `s'.stack = r.stack` by fs[word_state_rel_def] >> fs[] >>
                        first_x_assum (qspecl_then [`reachable`,`set_var x'0' w0 (s' with <|locals := fromAList l;stack := t|>)`] mp_tac) >>
                        reverse(impl_tac) >> fs[set_var_def] >>
                        `r.code = s.code` by (fs[call_env_def, dec_clock_def] >> Cases_on `handler`
                            >- (fs[push_env_def, env_to_list_def] >> imp_res_tac noInstall_evaluate_const_code >> fs[])
                            >- (PairCases_on `x'` >> fs[] >> fs[push_env_def, env_to_list_def] >>
                                imp_res_tac noInstall_evaluate_const_code >> fs[])) >>
                        fs[] >> fs[word_state_rel_def, domain_findLocState] >> rw[]
                        >- (`domain (getLocals (fromAList l)) ⊆ domain reachable` by imp_res_tac getStack_hd_thm >>
                            qspecl_then [`x'0'`, `w0`, `fromAList l`] mp_tac getLocals_insert >> rw[] >>
                            Cases_on `w0` >> fs[destWordLoc_def] >> rw[] >- imp_res_tac SUBSET_TRANS >>
                            fs[destResultLoc_def] >> fs[SUBSET_DEF] >> metis_tac[])
                        >- metis_tac[getStack_hd_thm]
                        >- (Cases_on `handler` >> fs[] >> PairCases_on `x'` >> fs[])
                        >- (`s'.code = removed_state.code` by (imp_res_tac noInstall_evaluate_const_code >> fs[]) >> rveq >> fs[])
                       )
                    >- (Cases_on `x'` >> fs[] >> Cases_on `domain (fromAList l) = domain (inter s.locals x'1')` >> fs[] >> rw[] >>
                        first_x_assum (qspecl_then [`reachable`,
                            `call_env x'0 (push_env (inter s.locals x'1') handler (dec_clock removed_state))`] mp_tac) >> rw[] >>
                        fs[] >> `noInstall x'1` by metis_tac[noInstall_find_code] >> fs[] >>
                        `s'.stack = r.stack` by fs[word_state_rel_def] >> fs[] >>
                        first_x_assum (qspecl_then [`reachable`,`set_var x'0' w0
                            (s' with <|locals := fromAList l; stack := t; handler := q|>)`] mp_tac) >>
                        reverse(impl_tac) >> fs[set_var_def] >>
                        `r.code = s.code` by (fs[call_env_def, dec_clock_def] >> Cases_on `handler`
                            >- (fs[push_env_def, env_to_list_def] >> imp_res_tac noInstall_evaluate_const_code >> fs[])
                            >- (PairCases_on `x'` >> fs[] >> fs[push_env_def, env_to_list_def] >>
                                imp_res_tac noInstall_evaluate_const_code >> fs[])) >>
                            fs[] >> fs[word_state_rel_def, domain_findLocState] >> rw[]
                        >- (`domain (getLocals (fromAList l)) ⊆ domain reachable` by imp_res_tac getStack_hd_thm >>
                            qspecl_then [`x'0'`, `w0`, `fromAList l`] mp_tac getLocals_insert >> rw[] >>
                            Cases_on `w0` >> fs[destWordLoc_def] >> rw[] >- imp_res_tac SUBSET_TRANS >>
                            fs[destResultLoc_def] >> fs[SUBSET_DEF] >> metis_tac[])
                        >- metis_tac[getStack_hd_thm]
                        >- (Cases_on `handler` >> fs[] >> PairCases_on `x'` >> fs[])
                        >- (`s'.code = removed_state.code` by (imp_res_tac noInstall_evaluate_const_code >> fs[]) >> rveq >> fs[])
                        )
                   )
                >- (Cases_on `handler` >> fs[] >> `noInstall x'1` by metis_tac[noInstall_find_code] >> fs[]
                    >- (rw[] >> qmatch_goalsub_abbrev_tac `(_, n_state)` >>
                        first_x_assum (qspecl_then [`reachable`, `n_state`] mp_tac) >>
                        reverse(impl_tac) >- (rw[] >> fs[])
                        >> fs[call_env_def, push_env_def, dec_clock_def, env_to_list_def, word_state_rel_def, domain_findLocState] >>
                        rw[] >> `n_state.code = removed_state.code` by (fs[Abbr `n_state`]) >> rveq >> fs[])
                    >- (PairCases_on `x'` >> fs[] >> Cases_on `w ≠ Loc x'2' x'3'` >> fs[] >>
                        Cases_on `domain r.locals = domain (inter s.locals x'1')` >> fs[] >> rw[] >>
                        first_x_assum (qspecl_then [`reachable`, `call_env x'0 (push_env (inter s.locals x'1')
                            (SOME (x'0'',x'1'',x'2',x'3')) (dec_clock removed_state))`] mp_tac) >> rw[] >> fs[] >>
                        `s'.locals = r.locals` by fs[word_state_rel_def] >> fs[] >>
                        first_x_assum (qspecl_then [`reachable`, `set_var x'0'' w0 s'`] mp_tac) >>
                        reverse(impl_tac) >> fs[] >> fs[set_var_def, word_state_rel_def, domain_findLocState] >> rw[]
                        >- (qspecl_then [`x'0''`, `w0`, `r.locals`] mp_tac getLocals_insert >> rw[] >>
                            Cases_on `w0` >> fs[destWordLoc_def] >> rw[] >- imp_res_tac SUBSET_TRANS >>
                            fs[destResultLoc_def] >> fs[SUBSET_DEF] >> metis_tac[])
                        >> `r.code = s.code ∧ removed_state.code = s'.code` by (
                                fs[push_env_def, env_to_list_def] >> imp_res_tac noInstall_evaluate_const_code >> fs[]) >> fs[])
                   )
                >>  first_x_assum (qspecl_then [`reachable`,
                    `call_env x'0 (push_env (inter s.locals x'1') handler (dec_clock removed_state))`] mp_tac) >>
                    rw[] >> rw[] >> rfs[dec_clock_def] >> `noInstall x'1` by metis_tac[noInstall_find_code] >> fs[]
,   (* FFI - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> fs[get_var_def] >> Cases_on `lookup len1 s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >> Cases_on `lookup ptr1 s.locals` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `lookup len2 s.locals` >> fs[] >> Cases_on `x` >> fs[] >> Cases_on `lookup ptr2 s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >> Cases_on `cut_env names s.locals` >> fs[] >>
        Cases_on `read_bytearray c' (w2n c) (mem_load_byte_aux s.memory s.mdomain s.be)` >> fs[] >>
        Cases_on `read_bytearray c''' (w2n c'') (mem_load_byte_aux s.memory s.mdomain s.be)` >> fs[] >>
        simp[case_eq_thms]
        \\ reverse strip_tac \\ fs[word_state_rel_def, cut_env_def]
          \\ rveq \\ fs[call_env_def,destResultLoc_def,domain_findLocState]
          \\ fs[getMemory_write_bytearray_lemma]
        >- EVAL_TAC
        \\ fs[SUBSET_DEF]
        \\ rw[]
        \\ imp_res_tac domain_getLocals_lookup
        \\ fs[lookup_inter, case_eq_thms]
        \\ fs[domain_lookup]
        \\ imp_res_tac (SIMP_RULE std_ss [domain_lookup, PULL_FORALL] domain_getLocals_lookup)
        \\ fs[]
,   (* DataBufferWrite - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `get_var r1 s` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `get_var r2 s` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `buffer_write s.data_buffer c c'` >> fs[] >>
        fs[get_var_def, buffer_write_def] >>
        strip_tac >> rveq >>
        fs[word_state_rel_def] >>
        fs[domain_findLocState, destResultLoc_def]
,   (* CodeBufferWrite - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `get_var r1 s` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `get_var r2 s` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `buffer_write s.code_buffer c (w2w c')` >> fs[] >>
        fs[get_var_def, buffer_write_def] >>
        strip_tac >> rveq >>
        fs[word_state_rel_def] >>
        fs[domain_findLocState, destResultLoc_def]
,   (* Install - DONE!!! *)
        fs[noInstall_def]
,   (* LocValue - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> fs[findWordRef_def] >> imp_res_tac code_rel_def >>
        Cases_on `l1 ∈ domain s.code` >> fs[] >> `l1 ∈ domain removed_state.code` by fs[domain_lookup] >>
        rw[] >> fs[set_var_def, word_state_rel_def] >> fs[domain_findLocState] >>
        `domain (getLocals (insert r (Loc l1 0) s.locals)) ⊆ domain (getLocals s.locals) ∪ {l1}`
        by (metis_tac[getLocals_insert_Loc]) >> fs[SUBSET_DEF] >> rw[] >> res_tac >> fs[]
        >> fs[destResultLoc_def]
,   (* If - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> fs[get_var_def] >> Cases_on `lookup r1 s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >> `get_var_imm ri s = get_var_imm ri removed_state` by (Cases_on `ri` >> fs[get_var_imm_def, get_var_def]) >>
        fs[] >> Cases_on `get_var_imm ri removed_state` >> fs[] >> Cases_on `x` >> fs[] >> Cases_on `word_cmp cmp c c'` >> fs[] >> rw[] >>
        fs[findWordRef_def, domain_union, noInstall_def]
,   (* Raise - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> fs[get_var_def] >> Cases_on `lookup n s.locals` >> fs[] >>
        `jump_exc s = NONE ⇔ jump_exc removed_state = NONE` by (fs[jump_exc_def] >> EVERY_CASE_TAC) >>
        drule word_state_rel_jump_exc >> strip_tac >> Cases_on `jump_exc s` >> fs[] >>
        PairCases_on `x'` >> fs[] >> rw[] >> fs[word_state_rel_def]
        >> Cases_on `x` >> fs[destResultLoc_def] >> fs[SUBSET_DEF] >>
            qspecl_then [`n'`, `s.locals`] mp_tac domain_getLocals_lookup >> rw[] >>
            fs[domain_findLocState] >> res_tac >> fs[]
,   (* Return - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> fs[get_var_def] >> Cases_on `lookup n s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >> Cases_on `lookup m s.locals` >> fs[] >> rw[] >>
        fs[call_env_def, fromList2_def, word_state_rel_def, domain_findLocState, getLocals_def]
        >> Cases_on `x` >> fs[destResultLoc_def] >> fs[SUBSET_DEF] >>
            qspecl_then [`n''`, `s.locals`] mp_tac domain_getLocals_lookup >> rw[] >>
            fs[domain_findLocState] >> res_tac >> fs[]
,   (* Seq - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> fs[findWordRef_def, domain_union] >>
        Cases_on `evaluate (c1, s)` >> fs[] >> Cases_on `q` >> fs[] >> rw[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state`] mp_tac) >>
        strip_tac >> rveq >> fs[noInstall_def, findWordRef_def] >> rw[] >> fs[] >> rfs[] >>
        first_x_assum (qspecl_then [`reachable`, `s'`] match_mp_tac) >> fs[] >>
        `s.code = r.code ∧ removed_state.code = s'.code ∧ r.code = new_state.code ∧ r.gc_fun = s.gc_fun` by
            metis_tac[noInstall_evaluate_const_code, evaluate_consts] >> rveq >> fs[]
,   (* MustTerminate - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> Cases_on `s.termdep` >> fs[] >>
        Cases_on `evaluate (p, s with <|clock := MustTerminate_limit (:'a); termdep := n|>)` >> fs[] >>
        Cases_on `q = SOME TimeOut` >> fs[] >> rw[] >>
        first_x_assum (qspecl_then [`reachable`, `removed_state with <|clock := MustTerminate_limit (:'a); termdep := n|>`] mp_tac) >>
        impl_tac >> rw[] >> fs[noInstall_def, word_state_rel_def, findWordRef_def, domain_findLocState]
,   (* Tick - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `s.clock = 0` >> fs[]
        >- (fs[call_env_def, fromList2_def] >> rw[word_state_rel_def] >>
            rw[findLocState_def, domain_union, getLocals_def, getStack_def] >>
            fs[domain_findLocState, SUBSET_DEF, destResultLoc_def])
        >- (rw[] >> fs[dec_clock_def, word_state_rel_def, domain_findLocState, destResultLoc_def])
,   (* Store - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        `word_exp s exp = word_exp removed_state exp` by metis_tac[word_state_rel_word_exp] >> fs[] >>
        Cases_on `word_exp removed_state exp` >> fs[] >> Cases_on `x` >> fs[] >> fs[get_var_def] >>
        Cases_on `lookup v s.locals` >> fs[] >> fs[mem_store_def] >> Cases_on `c ∈ s.mdomain` >> fs[] >>
        rw[] >> fs[word_state_rel_def, domain_findLocState, destResultLoc_def] >>
        qspecl_then [`c`, `x`, `s.memory`, `s.mdomain`] mp_tac getMemory_update >> fs[] >>
        Cases_on `x` >> fs[destWordLoc_def] >> rw[] >- metis_tac[SUBSET_TRANS] >>
        `n ∈ domain reachable` by (imp_res_tac domain_getLocals_lookup >> fs[SUBSET_DEF]) >>
        fs[SUBSET_DEF] >> metis_tac[]
,   (* Set - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `v = Handler ∨ v = BitmapBase` >> fs[] >>
        `word_exp s exp = word_exp removed_state exp` by metis_tac[word_state_rel_word_exp] >> fs[] >>
        Cases_on `word_exp removed_state exp` >> fs[] >>
        fs[set_store_def] >>
        rw[] >> fs[word_state_rel_def, domain_findLocState, destResultLoc_def] >>
        fs[findWordRef_def] >>
        qspecl_then [`s.store`, `v`, `x`] mp_tac getStore_update >>
        Cases_on `x` >> fs[destWordLoc_def] >> rw[] >- metis_tac[SUBSET_TRANS] >>
        `n ∈ domain reachable` by (Cases_on `exp` >> fs[word_exp_def]
            >- (metis_tac[domain_getLocals_lookup, SUBSET_DEF])
            >- (metis_tac[domain_getStore, SUBSET_DEF])
            >- (Cases_on `word_exp removed_state e` >> fs[] >> Cases_on `x` >> fs[] >>
                fs[mem_load_def] >> metis_tac[domain_getMemory, SUBSET_DEF])
            >- (`MAP (λa. word_exp s a) l = MAP (λa. word_exp removed_state a) l` by (fs[MAP_EQ_f] >> rw[] >>
                    `word_state_rel reachable s removed_state` by fs[word_state_rel_def, domain_findLocState] >>
                    metis_tac[word_state_rel_word_exp]) >> fs[] >>
                Cases_on `the_words (MAP (λa. word_exp removed_state a) l)` >> fs[])
            >- (Cases_on `word_exp removed_state e` >> fs[] >> Cases_on `x` >> fs[])) >>
        fs[SUBSET_DEF] >> metis_tac[]
,   (* Get - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `FLOOKUP s.store name` >> fs[] >>
        fs[set_var_def] >>
        rw[] >> fs[word_state_rel_def, domain_findLocState, destResultLoc_def] >>
        fs[getLocals_insert_Loc] >>
        qspecl_then [`v`, `x`, `s.locals`] mp_tac getLocals_insert >>
        Cases_on `x` >> fs[destWordLoc_def] >- metis_tac[SUBSET_TRANS] >> rw[] >>
        `n ∈ domain reachable` by metis_tac[domain_getStore, SUBSET_DEF] >>
        fs[SUBSET_DEF] >> metis_tac[]
,   (* Assign - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        `word_exp s exp = word_exp removed_state exp` by metis_tac[word_state_rel_word_exp] >> fs[] >>
        fs[] >> Cases_on `word_exp removed_state exp` >> fs[] >>
        fs[set_var_def] >> rw[] >> fs[word_state_rel_def, domain_findLocState, destResultLoc_def] >>
        qspecl_then [`v`, `x`, `s.locals`] mp_tac getLocals_insert >>
        Cases_on `x` >> fs[destWordLoc_def] >- metis_tac[SUBSET_TRANS] >> rw[] >>
        `n ∈ domain reachable` by (Cases_on `exp` >> fs[word_exp_def]
            >- (metis_tac[domain_getLocals_lookup, SUBSET_DEF])
            >- (metis_tac[domain_getStore, SUBSET_DEF])
            >- (Cases_on `word_exp removed_state e` >> fs[] >> Cases_on `x` >> fs[] >>
                fs[mem_load_def] >> metis_tac[domain_getMemory, SUBSET_DEF])
            >- (`MAP (λa. word_exp s a) l = MAP (λa. word_exp removed_state a) l` by (fs[MAP_EQ_f] >> rw[] >>
                    `word_state_rel reachable s removed_state` by fs[word_state_rel_def, domain_findLocState] >>
                    metis_tac[word_state_rel_word_exp]) >> fs[] >>
                Cases_on `the_words (MAP (λa. word_exp removed_state a) l)` >> fs[])
            >- (Cases_on `word_exp removed_state e` >> fs[] >> Cases_on `x` >> fs[])) >>
        fs[SUBSET_DEF] >> metis_tac[]
,   (* Inst - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        `inst i s = NONE ⇔ inst i removed_state = NONE` by metis_tac[word_state_rel_inst_NONE] >>
        Cases_on `inst i s` >> fs[] >>
        Cases_on `inst i removed_state` >> fs[] >> rw[]
        >- metis_tac[word_state_rel_inst_SOME]
        >- fs[destResultLoc_def]
,   (* Move - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> EVERY_CASE_TAC >> fs[] >> rw[] >> fs[set_vars_def] >>
        fs[word_state_rel_def, domain_findLocState] >> fs[alist_insert_def] >>
        fs[SUBSET_DEF, domain_getLocals_lookup] >> rw[] >> imp_res_tac get_vars_length_lemma >>
        fs[lookup_alist_insert] >> Cases_on `ALOOKUP (ZIP (MAP FST moves, x)) k` >> fs[]
        >- metis_tac[]
        >- (qsuff_tac `MEM x'' x` >- metis_tac[get_vars_getLocals, domain_getLocals_lookup]
            >> `LENGTH x = LENGTH (MAP FST moves)` by metis_tac[LENGTH_MAP] >> rveq >>
               metis_tac[ALOOKUP_ZIP_SUCCESS])
        >> fs[destResultLoc_def]
,   (* Alloc - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >>
        fs[get_var_def] >>
        Cases_on `lookup n s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >>
        metis_tac[word_state_rel_alloc]
,   (* Skip - DONE!!! *)
        simp[wordSemTheory.evaluate_def] >> rw[] >> fs[word_state_rel_def, destResultLoc_def]
    ]
);

(**************************** WORD_REMOVAL_THM *****************************)

val word_removal_thm = Q.store_thm("word_removal_thm",
    `∀ start state result new_state r reachable code1.
        wordSem$evaluate (Call NONE (SOME start) [0] NONE, state) = (result, new_state) ∧
        result ≠ SOME Error ∧ state.code = fromAList code1 ∧
        domain (findLocState state) ⊆ domain reachable ∧ gcNoNewLocs state.gc_fun ∧
        reachable = closure_spt (insert start () LN)  (mk_wf_set_tree (analyseWordCode code1)) ∧
        ALL_DISTINCT (MAP FST code1) ∧ noInstall_code state.code
        ⇒ ∃ s .
            wordSem$evaluate (Call NONE (SOME start) [0] NONE,
                state with code := fromAList (removeWordCode reachable code1)) = (result, s)`,
    rpt strip_tac >>
    drule word_removal_lemma >> disch_then drule >>
    strip_tac >> pop_assum (qspecl_then [`reachable`, `state' with code := fromAList(removeWordCode reachable code1)`] mp_tac) >>
    reverse(impl_tac) >- metis_tac[]
    >>  qspecl_then [`code1`, `analyseWordCode code1`, `insert start () LN`, `start`,
            `mk_wf_set_tree (analyseWordCode code1)`] mp_tac analyseWordCode_reachable_thm >>
        reverse(impl_tac >> rw[])
        >- (fs[codeClosed_def] >> qexists_tac `code1` >> fs[] >> fs[isReachable_def] >> metis_tac[RTC_TRANSITIVE, transitive_def])
        >- (fs[findWordRef_def, isReachable_def, RTC_REFL])

        >- (fs[noInstall_code_def] >> rw[] >> first_x_assum match_mp_tac >> qexists_tac `k` >>
            qexists_tac `n` >> fs[] >> fs[lookup_fromAList] >> imp_res_tac ALOOKUP_MEM >>
            imp_res_tac removeWordCode_thm >> metis_tac[ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME])
        >- fs[noInstall_def]
        >- (fs[word_state_rel_def, code_rel_def, lookup_fromAList] >> fs[EXTENSION, SUBSET_DEF] >> rw[] >>
            res_tac >> rename1 `closure_spt x y` >> Cases_on `ALOOKUP code1 n` >> fs[]
                >- (fs[ALOOKUP_NONE] >> drule removeWordCode_thm_FST >> rw[] >>
                    pop_assum (qspecl_then [`n`, `closure_spt x y`] mp_tac) >> rw[])
                >- (imp_res_tac ALOOKUP_MEM >> drule removeWordCode_thm >> rw[] >>
                    pop_assum (qspecl_then [`n`, `closure_spt x y`] mp_tac) >> rw[] >> res_tac >>
                    `ALL_DISTINCT (MAP FST (removeWordCode (closure_spt x y) code1))` by (fs[removeWordCode_def] >>
                    `MAP FST (FILTER (λx'. IS_SOME (lookup (FST x') (closure_spt x y))) code1)
                        = FILTER (λx'. IS_SOME (lookup x' (closure_spt x y))) (MAP FST code1)` by
                            metis_tac[removeWordCode_MAP_FST_lemma] >>
                    fs[FILTER_ALL_DISTINCT]) >> fs[ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME]))
        >- (fs[evaluate_def, get_vars_def, bad_dest_args_def, add_ret_loc_def, find_code_def] >>
            Cases_on `lookup start (fromAList code1)` >> fs[] >> fs[get_var_def] >> EVERY_CASE_TAC >> fs[] >>
            fs[lookup_fromAList] >> drule lookup_analyseWordCode >> rw[] >> fs[domain_lookup] >>
            drule lookup_mk_wf_set_tree >> rw[] >> fs[])
);

val _ = export_theory();

(*
  Correctness proof for word_elim
*)

open preamble wordLangTheory
     word_elimTheory wordSemTheory wordPropsTheory
     flat_elimProofTheory

val _ = new_theory "word_elimProof";
val _ = set_grammar_ancestry
  ["wordLang", "word_elim", "wordSem", "wordProps",
   "flat_elimProof"];
val _ = Parse.hide"mem";
val _ = Parse.bring_to_front_overload"domain"{Thy="sptree",Name="domain"};

(**************************** ANALYSIS LEMMAS *****************************)

Theorem wf_find_word_ref:
     ∀ prog tree . find_word_ref prog = tree ⇒ wf tree
Proof
    recInduct find_word_ref_ind >>
    rw[find_word_ref_def, wf_union, wf_def, wf_insert] >>
    TRY(CASE_TAC) >> rw[wf_def, wf_insert]
    >- (Cases_on `ret` >> Cases_on `handler` >> fs[wf_union, wf_def] >>
        PairCases_on `x` >> fs[] >> TRY(PairCases_on `x'`) >>
        fs[wf_union, wf_insert])
    >- (Cases_on `ret` >> Cases_on `handler` >>
        fs[wf_union, wf_insert, wf_def] >>
        PairCases_on `x'` >> fs[wf_union, wf_insert, wf_def] >>
        PairCases_on `x''` >>
        fs[wf_insert, wf_union, wf_def])
QED

Theorem wf_analyse_word_code:
     ∀ l t . analyse_word_code l = t ⇒ wf t
Proof
    Induct >- (rw[analyse_word_code_def] >> rw[wf_def])
    >> Cases_on `h` >> Cases_on `r` >> rw[analyse_word_code_def] >>
        rw[wf_insert]
QED

Theorem lookup_analyse_word_code:
     ∀ code n arity prog. ALOOKUP code n = SOME (arity, prog)
    ⇒ lookup n (analyse_word_code code) = SOME (find_word_ref prog)
Proof
    Induct >> fs[FORALL_PROD] >> fs[analyse_word_code_def] >>
    fs[lookup_insert] >> rw[]
QED

Theorem remove_word_code_thm:
     ∀ n reachable v l . n ∈ domain reachable ∧ MEM (n, v) l
    ⇒ MEM (n, v) (remove_word_code reachable l)
Proof
    Induct_on `l` >> rw[] >> fs[remove_word_code_def] >> fs[domain_lookup] >>
    Cases_on `IS_SOME (lookup (FST h) reachable)` >> fs[]
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

Theorem analyse_word_code_reachable_thm:
     ∀ (code : (num, num # α prog) alist) t start n tree.
    analyse_word_code code = t ∧  start = insert n () (LN:num_set) ∧
        domain start ⊆ domain tree ∧ tree = mk_wf_set_tree t
    ⇒ domain (closure_spt start tree) =
        {a | ∃ n . is_reachable tree n a ∧ n ∈ domain start}
Proof
    rw[] >> fs[domain_insert] >>
    qspecl_then
        [`mk_wf_set_tree (analyse_word_code code)`, `insert n () LN`]
        mp_tac closure_spt_thm >>
    `wf_set_tree(mk_wf_set_tree (analyse_word_code code))` by
        metis_tac[mk_wf_set_tree_thm] >> rw[] >>
    rw[wf_insert, wf_def]
QED



(**************************** no_install *****************************)

(*  ensures there are no install instructions in the code to be optimised -
    these will break the dead code elimination
    pass as they introduce new code at runtime,
    which may reference code that has been eliminated *)

val no_install_def = Define `
    (no_install (MustTerminate p) = no_install p) ∧
    (no_install (Call ret _ _ handler) = (case ret of
        | NONE => (case handler of
            | NONE => T
            | SOME (_,ph,_,_) => no_install ph)
        | SOME (_,_,pr,_,_) => (case handler of
            | NONE => no_install pr
            | SOME (_,ph,_,_) => no_install ph ∧ no_install pr))) ∧
    (no_install (Seq p1 p2) = (no_install p1 ∧ no_install p2)) ∧
    (no_install (If _ _ _ p1 p2) = (no_install p1 ∧ no_install p2)) ∧
    (no_install (Install _ _ _ _ _) = F) ∧
    (no_install _ = T)
`

val no_install_ind = theorem "no_install_ind";

val no_install_code_def = Define `
    no_install_code (code : (num # ('a wordLang$prog)) num_map) ⇔
        ∀ k n p . lookup k code = SOME (n, p) ⇒ no_install p
`

Theorem no_install_find_code:
     ∀ code dest args args1 expr .
    no_install_code code ∧ find_code dest args code = SOME (args1, expr)
    ⇒ no_install expr
Proof
    rw[no_install_code_def] >> Cases_on `dest` >> fs[find_code_def] >>
    EVERY_CASE_TAC >> metis_tac[]
QED

Theorem no_install_evaluate_const_code:
     ∀ prog s result s1 . evaluate (prog, s) = (result, s1) ∧
        no_install prog ∧ no_install_code s.code
    ⇒ s.code = s1.code
Proof
    recInduct evaluate_ind >> rw[] >> qpat_x_assum `evaluate _ = _` mp_tac >>
    fs[evaluate_def]
    >- (EVERY_CASE_TAC >> fs[] >> rw[] >> imp_res_tac alloc_const >> fs[])
    >- (fs[get_vars_def, set_vars_def] >> EVERY_CASE_TAC >>
        fs[] >> rw[] >> fs[get_vars_def])
    >- (rw[] >> EVERY_CASE_TAC >> imp_res_tac inst_const_full >>
        fs[] >> rveq >> fs[])
    >- (EVERY_CASE_TAC >> fs[set_var_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[set_var_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[set_store_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[mem_store_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[call_env_def, dec_clock_def] >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[] >> rename1 `evaluate (p, st)` >>
        Cases_on `evaluate (p, st)` >>
        fs[no_install_def] >> EVERY_CASE_TAC >> fs[] >> rw[] >> fs[])
    >- (Cases_on `evaluate (c1,s)` >> fs[no_install_def] >> CASE_TAC >> rfs[])
    >- (EVERY_CASE_TAC >> fs[call_env_def] >> rw[] >> fs[])
    >- (fs[jump_exc_def] >> EVERY_CASE_TAC >> rw[] >> fs[])
    >- (fs[no_install_def] >> EVERY_CASE_TAC >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> fs[set_var_def] >> rw[] >> fs[])
    >- (fs[no_install_def])
    >- (EVERY_CASE_TAC >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> rw[] >> fs[])
    >- (EVERY_CASE_TAC >> rw[] >> fs[] >> fs[ffiTheory.call_FFI_def] >>
        EVERY_CASE_TAC >> rw[] >> fs[state_component_equality])
    >- (fs[no_install_def, dec_clock_def, call_env_def, push_env_def,
        cut_env_def, pop_env_def, set_var_def] >>
        EVERY_CASE_TAC >> rw[] >> fs[] >> metis_tac[no_install_find_code])
QED



(**************************** DEFINITIONS *****************************)

val dest_word_loc_def = Define `
    (* 'a word_loc = Word ('a word) | Loc num num *)
    (dest_word_loc (Loc n _) = SOME n) ∧
    (dest_word_loc (_:'a word_loc) = NONE)
`

Theorem dest_word_loc_thm:
     ∀ wl n1 . dest_word_loc wl = SOME n1 ⇒ ∃ n0 . wl = Loc n1 n0
Proof
    Cases_on `wl` >> fs[dest_word_loc_def]
QED

val dest_result_loc_def = Define `
    (dest_result_loc (SOME (Result w (Loc n n0))) = {n}) ∧
    (dest_result_loc (SOME (Exception w (Loc n n0))) = {n}) ∧
    (dest_result_loc _ = {})
`

(* TODO could do alt def using toAList -
    not necessary though, may not be cleaner *)
val get_locals_def = Define ` (* locals : ('a word_loc) num_map *)
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
`

Theorem get_locals_thm:
     ∀ t n1 n0 locs .
        (∃ n . lookup n (t:('a word_loc) num_map) = SOME (Loc n1 n0)) ∧
        locs = get_locals t ⇒ n1 ∈ domain locs
Proof
    Induct >> rw[lookup_def, get_locals_def, dest_word_loc_def, domain_union]
    >- (fs[lookup_def] >> Cases_on `EVEN n` >> fs[] >> metis_tac[])
    >- (Cases_on `dest_word_loc a` >> fs[] >> rw[domain_union] >>
        fs[lookup_def] >>
        Cases_on `n = 0` >> fs[] >> rveq >> fs[dest_word_loc_def] >>
        Cases_on `a` >> fs[dest_word_loc_def] >> Cases_on `EVEN n` >> fs[] >>
        metis_tac[])
QED

Theorem domain_get_locals_lookup:
     ∀ n t . n ∈ domain (get_locals t) ⇔ ∃ k n1 . lookup k t = SOME (Loc n n1)
Proof
    rw[] >> reverse (EQ_TAC) >> rw[]
    >- (match_mp_tac get_locals_thm >> fs[PULL_EXISTS] >> qexists_tac `t` >>
        qexists_tac `n1` >> qexists_tac `k` >> fs[])
    >> Induct_on `t`
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
            Cases_on `a` >> fs[dest_word_loc_def]
            >- (fs[domain_union] >> res_tac
                >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
                    once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
                >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
                    once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV]))
            >- (rveq >> qexists_tac `0n` >> fs[])
            >- (fs[domain_union] >> res_tac
                >- (qexists_tac `2 * k + 2` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
                    once_rewrite_tac[MULT_COMM] >> fs[DIV_MULT])
                >- (qexists_tac `2 * k + 1` >> fs[EVEN_DOUBLE, EVEN_ADD] >>
                    once_rewrite_tac[MULT_COMM] >> fs[MULT_DIV])))
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

val get_store_def = Define ` (* store : store_name |-> 'a word_loc *)
    get_store (st:store_name |-> 'a word_loc) =
        let locSet = SET_TO_LIST (FRANGE st) in
        let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc locSet)) in
        FOLDL (λ acc loc . insert loc () acc) LN locList
`

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

val get_num_wordloc_alist_def = Define `
    get_num_wordloc_alist (l: (num, 'a word_loc) alist) =
        let locs = MAP THE (FILTER IS_SOME (MAP (dest_word_loc o SND) l)) in
        FOLDL (λ acc loc . insert loc () acc) LN locs
`

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

val get_stack_def = Define ` (* stack : ('a stack_frame) list *)
    (get_stack [] = LN:num_set) ∧
    (get_stack ((StackFrame e _)::xs) =
        union (get_num_wordloc_alist e) (get_stack xs))
`

val get_stack_ind = theorem "get_stack_ind";

Theorem get_stack_hd_thm:
     ∀ stack dr l opt t . domain (get_stack stack) ⊆ dr ∧
        stack = StackFrame l opt::t
        ⇒ domain (get_locals (fromAList l)) ⊆ dr ∧
          domain (get_stack t) ⊆ dr
Proof
            recInduct get_stack_ind >> rw[]
            >- (Cases_on `e` >>
                fs[get_stack_def, domain_union,
                    fromAList_def, get_locals_def] >>
                fs[get_stack_def, domain_union, fromAList_def] >>
                metis_tac[get_num_wordloc_alist_get_locals, SUBSET_TRANS])
            >-  fs[get_stack_def, domain_union]
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
    Cases_on `h` >> fs[get_stack_def, domain_union]
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

Theorem s_val_eq_get_stack:
     ∀ stack1 stack2 . s_val_eq stack1 stack2
    ⇒ get_stack stack1 = get_stack stack2
Proof
        recInduct get_stack_ind >> rw[] >> Cases_on `stack2` >>
        fs[s_val_eq_def] >>
        Cases_on `h` >> fs[s_frame_val_eq_def, get_stack_def] >>
        first_x_assum drule >> rw[] >> Cases_on `v0` >> Cases_on `o'` >>
        fs[s_frame_val_eq_def] >> rw[] >>
        `MAP (dest_word_loc o SND) e = MAP (dest_word_loc o SND) l` by
            rw[GSYM MAP_MAP_o] >> fs[] >>
        fs[get_num_wordloc_alist_def]
QED

val get_memory_def = Define ` (* 'a word -> 'a word_loc *)
    get_memory (mem:'a word -> 'a word_loc) (mdom:'a word set) =
        let locSet = SET_TO_LIST(IMAGE mem mdom) in
        let locList = MAP THE (FILTER IS_SOME (MAP dest_word_loc locSet)) in
        FOLDL (λ acc loc . insert loc () acc) LN locList
`

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
     ∀ mem (mdom : 'a word set) n . (n ∈ domain (get_memory mem mdom)
    ⇔ (∃ k n1 . k ∈ mdom ∧ mem k = Loc n n1))
Proof
    fs[get_memory_def, IMAGE_DEF] >> fs[FILTER_MAP, MAP_MAP_o] >> rw[] >>
    `FINITE mdom` by metis_tac[WORD_FINITE] >>
    fs[MEM_MAP, MEM_FILTER] >> `FINITE {mem x | x ∈ mdom}` by
        metis_tac[FINITE_mdom_mem] >>
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

val find_loc_state_def = Define`
    find_loc_state s =
        let loc = (get_locals s.locals) in
        let sto = (get_store s.store) in
        let sta = (get_stack s.stack) in
        let mem = (get_memory s.memory s.mdomain) in
        union (union loc sto) (union sta mem)
`

Theorem domain_find_loc_state:
     ∀ s . domain (find_loc_state s) =
        domain (get_locals s.locals) ∪ domain (get_store s.store) ∪
        domain (get_stack s.stack) ∪ domain (get_memory s.memory s.mdomain)
Proof
    rw[find_loc_state_def, domain_union, UNION_ASSOC]
QED

val code_rel_def = Define`
    code_rel (reachable:num_set) s_code
        (t_code :(num # ('a wordLang$prog)) num_map) =
        ∀ n . n ∈ domain reachable ⇒
            lookup n s_code = lookup n t_code
`

val code_closed_def = Define`
    code_closed reachable c1 ⇔ ∃ code1 . c1 = fromAList code1 ∧
        ∀ n m . n ∈ domain reachable ∧
        is_reachable (mk_wf_set_tree (analyse_word_code code1)) n m ⇒
        m ∈ domain reachable
`

val gc_no_new_locs_def = Define`
    gc_no_new_locs (g:'a gc_fun_type) ⇔  ∀ sta mem mdom sto wl mem1 sto1 sta1 .
        (g (enc_stack sta, mem, mdom, sto) = SOME (wl, mem1, sto1)) ∧
         dec_stack wl sta = SOME sta1 ⇒
        domain (get_stack sta1) ⊆ domain (get_stack sta) ∧
        domain (get_memory mem1 mdom) ⊆ domain (get_memory mem mdom) ∧
        domain (get_store sto1) ⊆ domain (get_store sto)
`

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
        domain (find_loc_state t) ⊆ domain (reachable)
`


(**************************** OTHER LEMMAS *****************************)

Theorem EL_APPEND:
     ∀ n x e x1 . EL n x = e ∧ n < LENGTH x ⇒ EL n (x ⧺ [x1]) = e
Proof
    Induct_on `x` >> rw[Once EL] >> Cases_on `n` >> rw[]
QED

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
    ASSUME_TAC get_vars_locals >>
    strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
    first_x_assum (qspecl_then [`args`, `s`, `x`, `Loc n n1`] mp_tac) >>
    rw[] >> fs[] >> imp_res_tac get_locals_thm >> metis_tac[]
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
        `2 * m DIV 2 = m` by (once_rewrite_tac [MULT_COMM] >>
        fs[MULT_DIV]) >> fs[] >>
        imp_res_tac EL_APPEND >> `LENGTH (h::ys) = SUC (LENGTH ys)` by
            (Induct_on `ys` >> rw[]) >> fs[]
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
     ∀ s dr locs opt .
        domain (get_locals s.locals) ⊆ dr ∧
        domain (get_stack s.stack) ⊆ dr
    ⇒ domain (get_stack (StackFrame (list_rearrange (s.permute 0)
    (QSORT key_val_compare (toAList (inter s.locals locs)))) opt::s.stack))
        ⊆ dr
Proof
    rw[] >> fs[get_stack_def, domain_union] >> rw[SUBSET_DEF] >>
    imp_res_tac get_num_wordloc_alist_thm >>
    fs[MEM_MAP] >> fs[mem_list_rearrange, QSORT_MEM] >>
    Cases_on `y` >> fs[MEM_toAList] >> fs[lookup_inter] >>
    Cases_on `lookup q s.locals` >> fs[] >>
    Cases_on `lookup q locs` >> fs[] >> rveq >>
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
     ∀ reachable:num_set (l: (ctor_id, ctor_id # α prog) alist) .
        MAP FST (FILTER (λx. IS_SOME (lookup (FST x) reachable)) l) =
            FILTER (λx. IS_SOME (lookup x reachable)) (MAP FST l)
Proof
    Induct_on `l` >> rw[]
QED

Theorem word_state_rel_word_exp:
     ∀ s1 exp s2 reachable . word_state_rel reachable s1 s2
        ⇒ word_exp s1 exp = word_exp s2 exp
Proof
    recInduct word_exp_ind >> rw[word_exp_def]
    >- (fs[word_state_rel_def]) >- (fs[word_state_rel_def])
    >- (first_x_assum drule >> rw[] >> PURE_TOP_CASE_TAC >> rw[] >>
        PURE_TOP_CASE_TAC >> fs[] >> fs[mem_load_def, word_state_rel_def])
    >- (`MAP (λ a . word_exp s a) wexps = MAP (λ a . word_exp s2 a) wexps` by
            (fs[MAP_EQ_f] >> metis_tac[]) >> fs[])
    >- (first_x_assum drule >> rw[])
QED

Theorem word_state_rel_inst_NONE:
     ∀ reachable s t i . word_state_rel reachable s t
    ⇒ (inst i s = NONE ⇔ inst i t = NONE)
Proof
    rw[] >> fs[word_state_rel_def] >> Cases_on `i` >> fs[inst_def]
    >- (fs[assign_def] >>
        `word_exp s (Const c) = word_exp t (Const c)`
            by metis_tac[word_state_rel_word_exp, word_state_rel_def] >>
        fs[] >> Cases_on `word_exp t (Const c)` >> rw[])
    >- (fs[get_var_def, get_vars_def] >> EVERY_CASE_TAC >> fs[assign_def]
       >- (`word_exp s (Op b [Var n0; Var n']) =
                word_exp t (Op b [Var n0; Var n'])` by
                metis_tac[word_state_rel_word_exp, word_state_rel_def] >>
                fs[] >>
            Cases_on `word_exp t (Op b [Var n0; Var n'])` >> fs[])
       >- (`word_exp s (Op b [Var n0; Const c]) =
                word_exp t (Op b [Var n0; Const c])` by
                metis_tac[word_state_rel_word_exp, word_state_rel_def] >>
                fs[] >>
            Cases_on `word_exp t (Op b [Var n0; Const c])` >> fs[])
       >- (`word_exp s (Shift s' (Var n0) n1) =
            word_exp t (Shift s' (Var n0) n1)` by
                metis_tac[word_state_rel_word_exp, word_state_rel_def] >>
                fs[] >>
            Cases_on `word_exp t (Shift s' (Var n0) n1)` >> fs[]))
    >- (`∀ exp . word_exp t exp = word_exp s exp` by
            metis_tac[word_state_rel_word_exp, word_state_rel_def] >>
        fs[get_var_def, mem_load_def, set_var_def] >> EVERY_CASE_TAC >>
        rfs[mem_store_def])
    >- (fs[get_fp_var_def, set_var_def, set_fp_var_def, get_var_def] >>
        EVERY_CASE_TAC >> fs[])
QED

Theorem word_state_rel_inst_SOME:
     ∀ reachable s t i s1 t1 . word_state_rel reachable s t ⇒
    (inst i s = SOME s1 ∧ inst i t = SOME t1 ⇒ word_state_rel reachable s1 t1)
Proof
    fs[inst_def] >> Cases_on `i` >> fs[]
    >- (fs[assign_def] >> fs[word_exp_def] >> fs[set_var_def] >>
        fs[word_state_rel_def] >> rw[] >> fs[domain_find_loc_state] >>
        qspecl_then [`n`, `Word c`, `s.locals`] mp_tac get_locals_insert >>
        rw[dest_word_loc_def] >> imp_res_tac SUBSET_TRANS)
    >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
        strip_tac >>
        fs[get_vars_def, get_var_def] >> Cases_on `a` >> fs[] >>
        `s.locals = t.locals` by fs[word_state_rel_def] >> fs[]
        >- (fs[assign_def] >>
            `word_exp s (Op b [Var n0; case r of Reg r3 => Var r3
                                               | Imm w => Const w]) =
                word_exp t (Op b [Var n0; case r of Reg r3 => Var r3
                                                  | Imm w => Const w])` by
                    metis_tac[word_state_rel_word_exp] >> fs[] >>
            Cases_on `word_exp t (Op b [Var n0; case r of Reg r3 => Var r3
                                                        | Imm w => Const w])` >>
            fs[] >> fs[set_var_def] >> rw[] >>
            fs[word_state_rel_def, domain_find_loc_state] >> rw[] >>
            fs[word_exp_def] >> fs[the_words_def] >> EVERY_CASE_TAC >> fs[] >>
           qspecl_then [`n`, `Word z'`, `s.locals`] mp_tac get_locals_insert >>
           rw[dest_word_loc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (fs[assign_def] >>
            `word_exp s (Shift s' (Var n0) n1) =
                word_exp t (Shift s' (Var n0) n1)` by
                    metis_tac[word_state_rel_word_exp] >> fs[] >>
            Cases_on `word_exp t (Shift s' (Var n0) n1)` >> fs[] >>
            fs[set_var_def] >> rw[] >>
            fs[word_state_rel_def, domain_find_loc_state] >> rw[] >>
            fs[word_exp_def] >> fs[the_words_def] >> EVERY_CASE_TAC >> fs[] >>
            qspecl_then [`n`, `Word z'`, `s.locals`] mp_tac get_locals_insert >>
            rw[dest_word_loc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[] >> fs[set_var_def] >>
            fs[word_state_rel_def, domain_find_loc_state] >> rw[] >> fs[] >>
            qspecl_then [`n`, `Word (c' / c)`, `s.locals`]
                mp_tac get_locals_insert >> rw[dest_word_loc_def] >> rw[] >>
            imp_res_tac SUBSET_TRANS)
        >- (fs[set_var_def] >> fs[] >>
            fs[] >> EVERY_CASE_TAC >> fs[] >>
            fs[word_state_rel_def, domain_find_loc_state] >> rw[] >> fs[] >>
            qspecl_then [`n`, `Word (n2w (w2n c * w2n c' DIV dimword (:α)))`,
                `s.locals`] mp_tac get_locals_insert >> rw[dest_word_loc_def] >>
            qspecl_then [`n0`, `Word (n2w (w2n c * w2n c'))`,
            `insert n (Word (n2w (w2n c * w2n c' DIV dimword (:α)))) s.locals`]
                mp_tac get_locals_insert >> rw[dest_word_loc_def] >> fs[] >>
                rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[set_var_def] >>
            fs[word_state_rel_def, domain_find_loc_state] >> rw[] >> fs[] >>
            qspecl_then [`n0`,
                `Word (n2w ((w2n c' + dimword (:α) * w2n c) MOD w2n c''))`,
                `s.locals`] mp_tac get_locals_insert >>
            rw[dest_word_loc_def] >>
            qspecl_then [`n`,
                `Word (n2w ((w2n c' + dimword (:α) * w2n c) DIV w2n c''))`,
                `insert n0 (Word (n2w ((w2n c' + dimword (:α) * w2n c)
                    MOD w2n c''))) s.locals`] mp_tac get_locals_insert >>
                rw[dest_word_loc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[set_var_def] >>
            fs[word_state_rel_def, domain_find_loc_state] >> rw[] >> fs[]
            >| [
                qspecl_then [`n`, `Word (n2w (w2n c + w2n c'))`, `s.locals`]
                mp_tac get_locals_insert >>
                qspecl_then [`n2`, `Word 1w`,
                    `insert n (Word (n2w (w2n c + w2n c'))) s.locals`] mp_tac
                    get_locals_insert,
                qspecl_then [`n`, `Word (n2w (w2n c + w2n c'))`, `s.locals`]
                    mp_tac get_locals_insert >>
                qspecl_then [`n2`,
                    `Word 0w`, `insert n (Word (n2w (w2n c + w2n c')))
                    s.locals`] mp_tac get_locals_insert,
                qspecl_then [`n`, `Word (n2w (w2n c + (w2n c' + 1)))`,
                    `s.locals`] mp_tac get_locals_insert >>
                qspecl_then [`n2`, `Word 1w`,
                    `insert n (Word (n2w (w2n c + (w2n c' + 1)))) s.locals`]
                    mp_tac get_locals_insert,
                qspecl_then [`n`, `Word (n2w (w2n c + (w2n c' + 1)))`,
                    `s.locals`] mp_tac get_locals_insert >>
                qspecl_then [`n2`, `Word 0w`,
                    `insert n (Word (n2w (w2n c + (w2n c' + 1)))) s.locals`]
                    mp_tac get_locals_insert
            ] >>
            rw[dest_word_loc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[set_var_def] >>
            fs[word_state_rel_def, domain_find_loc_state] >> rw[] >> fs[] >>
            qspecl_then [`n`, `Word (c + c')`, `s.locals`]
                mp_tac get_locals_insert
            >| [
                qspecl_then [`n2`, `Word 1w`,
                    `insert n (Word (c + c')) s.locals`]
                    mp_tac get_locals_insert  ,
                qspecl_then [`n2`, `Word 0w`,
                `insert n (Word (c + c')) s.locals`] mp_tac get_locals_insert
              ] >>
                rw[dest_word_loc_def] >> rw[] >> imp_res_tac SUBSET_TRANS)
        >- (EVERY_CASE_TAC >> fs[set_var_def] >>
            fs[word_state_rel_def, domain_find_loc_state] >> rw[] >> fs[] >>
            qspecl_then [`n`, `Word (c + -1w * c')`, `s.locals`]
                mp_tac get_locals_insert
            >| [
                qspecl_then [`n2`, `Word 1w`,
                `insert n (Word (c + -1w * c')) s.locals`]
                mp_tac get_locals_insert  ,
                qspecl_then [`n2`, `Word 0w`,
                    `insert n (Word (c + -1w * c')) s.locals`]
                    mp_tac get_locals_insert
              ] >>
                rw[dest_word_loc_def] >> imp_res_tac SUBSET_TRANS))
    >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
        strip_tac >> Cases_on `a` >> fs[] >>
        `word_exp t (Op Add [Var n'; Const c]) =
            word_exp s (Op Add [Var n'; Const c])` by
                metis_tac[word_state_rel_word_exp] >>
        Cases_on `m` >> fs[] >>
        fs[word_exp_def, the_words_def, word_state_rel_def] >>
        Cases_on `lookup n' s.locals` >> fs[] >>
        Cases_on `x` >> fs[]
        >- (fs[word_op_def, mem_load_def] >> Cases_on `c + c' ∈ s.mdomain` >>
            fs[] >> fs[set_var_def] >> rw[] >> fs[] >>
            fs[domain_find_loc_state] >>
            qspecl_then [`n`, `s.memory (c + c')`, `s.locals`]
                mp_tac get_locals_insert >> rw[] >>
            Cases_on `s.memory (c + c')` >> fs[dest_word_loc_def] >> rw[]
            >- imp_res_tac SUBSET_TRANS >>
            `n'' ∈ domain reachable` by
                metis_tac[SUBSET_DEF, domain_get_memory] >>
                fs[SUBSET_DEF] >> metis_tac[])
        >- (fs[word_op_def, mem_load_byte_aux_def] >>
            Cases_on `s.memory (byte_align (c + c'))` >> fs[] >>
            Cases_on `byte_align (c + c') ∈ s.mdomain` >> fs[] >>
            fs[set_var_def] >> rw[] >> fs[domain_find_loc_state] >>
            qspecl_then [`n`, `Word (w2w (get_byte (c + c') c'' s.be))`,
                `s.locals`] mp_tac get_locals_insert >> rw[dest_word_loc_def] >>
            rw[] >> imp_res_tac SUBSET_TRANS)
        >- (fs[word_op_def, get_var_def] >>
            Cases_on `lookup n s.locals` >> fs[] >> fs[mem_store_def] >>
            Cases_on `c + c' ∈ s.mdomain` >> fs[] >> rw[] >>
            fs[domain_find_loc_state] >>
            qspecl_then [`c + c'`, `x`, `s.memory`, `s.mdomain`]
                mp_tac get_memory_update >> rw[] >>
            Cases_on `x` >> fs[dest_word_loc_def] >> rw[]
            >- imp_res_tac SUBSET_TRANS >>
            `n'' ∈ domain reachable` by
                metis_tac[SUBSET_DEF, domain_get_locals_lookup] >>
            fs[SUBSET_DEF] >> metis_tac[])
        >- (fs[word_op_def, get_var_def] >>
            Cases_on `lookup n s.locals` >> fs[] >> Cases_on `x` >> fs[] >>
            fs[mem_store_byte_aux_def] >>
            Cases_on `s.memory (byte_align (c + c'))` >> fs[] >>
            Cases_on `byte_align (c + c') ∈ s.mdomain` >> fs[] >>
            rw[] >> fs[domain_find_loc_state] >>
            qspecl_then [`byte_align (c + c')`,
                `Word(set_byte (c + c') (w2w c'') c''' s.be)`,
                `s.memory`, `s.mdomain`] mp_tac get_memory_update >>
            rw[] >> fs[dest_word_loc_def] >> rw[] >> imp_res_tac SUBSET_TRANS))
    >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
        strip_tac >>
        fs[get_var_def, get_fp_var_def, set_fp_var_def, set_var_def] >>
        `t.fp_regs = s.fp_regs` by fs[word_state_rel_def] >>
        EVERY_CASE_TAC >> fs[] >>
        fs[word_state_rel_def, domain_find_loc_state] >>
        rw[] >> fs[] >>
        `∀ w . domain (get_locals (insert n (Word w) s.locals)) ⊆
            domain reachable` by
            (rw[] >>
             qspecl_then [`n`, `Word w`, `s.locals`] mp_tac get_locals_insert >>
             fs[dest_word_loc_def] >> rw[] >> imp_res_tac SUBSET_TRANS) >>
             fs[] >>
        rfs[] >>
        qspecl_then [`n`, `Word ((31 >< 0) x)`, `s.locals`]
            mp_tac get_locals_insert >>
        qspecl_then [`n0`, `Word ((63 >< 32) x)`,
            `insert n (Word ((31 >< 0) x)) s.locals`] mp_tac
                get_locals_insert >>
        rw[dest_word_loc_def] >> imp_res_tac SUBSET_TRANS)
QED

Theorem word_state_rel_jump_exc:
     ∀ reachable s t s1 l1 l2 . word_state_rel reachable s t
    ==> jump_exc s = SOME (s1, l1, l2)
    ⇒ ∃ t1 . jump_exc t = SOME (t1, l1, l2) ∧ word_state_rel reachable s1 t1
Proof
    strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
    strip_tac >> strip_tac >>
    fs[jump_exc_def] >> `s.handler = t.handler ∧ s.stack = t.stack` by
        fs[word_state_rel_def] >> fs[] >>
    EVERY_CASE_TAC >> fs[] >> rw[] >> fs[word_state_rel_def] >> rw[] >>
    fs[domain_find_loc_state] >>
    `domain (get_stack (StackFrame l (SOME (q,l1,l2))::t')) ⊆
        domain reachable` by metis_tac[get_stack_LASTN,SUBSET_TRANS] >>
    drule get_stack_hd_thm >> rw[]
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
    fs[alloc_def] >> fs[cut_env_def, domain_find_loc_state] >>
    Cases_on `domain n ⊆ domain s.locals` >> fs[] >> CASE_TAC >> fs[] >>
    `word_state_rel reachable (push_env (inter s.locals n) NONE
        (set_store AllocSize (Word c) s))
        (push_env (inter s.locals n) NONE
        (set_store AllocSize (Word c) t))` by (
            simp[push_env_def, env_to_list_def, set_store_def,
                 word_state_rel_def, domain_find_loc_state] >> rw[]
            >- (qspecl_then [`s.store`, `AllocSize`, `Word c`] mp_tac
                get_store_update >> fs[dest_word_loc_def] >>
                rw[] >> imp_res_tac SUBSET_TRANS)
            >- fs[stack_list_rearrange_lemma]) >>
    `(push_env (inter s.locals n) NONE
        (set_store AllocSize (Word c) s)).gc_fun = s.gc_fun` by
        fs[env_to_list_def, push_env_def, set_store_def] >> fs[] >> rw[] >>
    qmatch_asmsub_abbrev_tac `gc s_state` >>
    qmatch_goalsub_abbrev_tac `gc t_state` >>
    qspecl_then [`reachable`, `s_state`, `t_state`, `x`]
        mp_tac word_state_rel_gc >>
    impl_tac >- fs[push_env_def, Abbr `s_state`]
    >>  rw[] >> fs[] >>
        qpat_assum `word_state_rel _ _ _` mp_tac >>
        SIMP_TAC std_ss [Once word_state_rel_def] >> strip_tac >>
        qpat_x_assum `(_) = (a,b)` mp_tac >> fs[pop_env_def] >>
        Cases_on `x.stack` >> fs[] >>
        Cases_on `h` >> fs[] >> Cases_on `o'` >> fs[]
        >| [ALL_TAC, (Cases_on `x'` >> fs[])] >>
        EVERY_CASE_TAC >> fs[has_space_def, call_env_def, fromList2_def] >>
        rfs[] >>
        strip_tac >> rveq >> fs[dest_result_loc_def, word_state_rel_def] >>
        rw[] >>
        fs[domain_find_loc_state]
        >- (drule get_stack_hd_thm >> rw[] >> metis_tac[])
        >- (fs[get_locals_def, get_stack_def])
        >- (drule get_stack_hd_thm >> rw[] >> metis_tac[])
        >- (fs[get_locals_def, get_stack_def])
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
        `∀ args . get_vars args removed_state = get_vars args s` by (
            Induct >> rw[get_vars_def] >> rw[get_var_def] >> rw[])
    >- (
    (* CALL *)
        simp[wordSemTheory.evaluate_def] >> Cases_on `get_vars args s` >>
        fs[] >>
        Cases_on `bad_dest_args dest args` >> fs[no_install_def] >>
        `get_vars args s = SOME [] ⇒ args = []` by (Cases_on `args` >>
            fs[get_vars_def] >> Cases_on `get_var h s` >> fs[] >>
            Cases_on `get_vars t s` >> fs[] >> rveq >> fs[NOT_CONS_NIL]) >>
        `find_code dest (add_ret_loc ret x) s.code =
            find_code dest (add_ret_loc ret x) removed_state.code`
        by (
         Cases_on `dest` >> rw[find_code_def] >> Cases_on `x` >>
         rfs[bad_dest_args_def]
         >- (Cases_on `LAST (add_ret_loc ret (h::t))` >> fs[] >>
             Cases_on `n0` >> fs[] >>
             `MEM (Loc n 0) (h::t)` by
                 (Cases_on `ret` >> fs[add_ret_loc_def]
                 >- metis_tac[LAST_DEF, MEM_LAST, MEM]
                 >- (PairCases_on `x` >> fs[add_ret_loc_def] >>
                     metis_tac[LAST_DEF, MEM_LAST, MEM])) >>
             qspecl_then [`args`, `s`, `h::t`, `n`, `0`]
                 mp_tac get_vars_get_locals >> rw[] >>
             `n ∈ domain reachable` by (qspec_then `s` mp_tac
                 domain_find_loc_state >>
                 fs[SUBSET_DEF, SUBSET_UNION, SUBSET_TRANS]) >>
             `lookup n s.code = lookup n removed_state.code` by
                 metis_tac[code_rel_def] >> fs[])
         >> `x' ∈ domain reachable` by
                 fs[find_word_ref_def, SUBSET_DEF, domain_union] >>
            `lookup x' s.code = lookup x' removed_state.code` by
                 metis_tac[code_rel_def] >> fs[]
        ) >> rveq >>
        Cases_on `find_code dest (add_ret_loc ret x) removed_state.code` >>
        fs[] >>
        qmatch_asmsub_rename_tac`_ = SOME p` >>
        PairCases_on `p` >> fs[] >> Cases_on `ret` >> fs[]
        >- (Cases_on `handler` >> fs[] >> Cases_on `s.clock = 0` >> fs[]
            >- (fs[call_env_def, fromList2_def] >> rw[word_state_rel_def] >>
                rw[find_loc_state_def, domain_union,
                    get_locals_def, get_stack_def] >>
                fs[domain_find_loc_state, SUBSET_DEF, dest_result_loc_def])
            >- (`word_state_rel reachable (call_env p0 (dec_clock s))
                (call_env p0 (dec_clock removed_state))` by (
                    rw[word_state_rel_def, call_env_def, dec_clock_def] >>
                    fs[find_loc_state_def, domain_union,
                        domain_find_loc_state] >>
                    fs[add_ret_loc_def] >>
                    Cases_on `dest` >> fs[find_code_def] >> Cases_on `x` >>
                    rfs[bad_dest_args_def]
                    >- (Cases_on `LAST (h::t)` >> fs[] >>
                        Cases_on `n0` >> fs[] >>
                        qspecl_then [`args`, `s`, `(h::t)`, `n`, `0`] mp_tac
                            get_vars_get_locals >> strip_tac >>
                        `n ∈ domain reachable` by (qspec_then `s` mp_tac
                            domain_find_loc_state >> rw[] >>
                            metis_tac[SUBSET_DEF, SUBSET_UNION,
                                      SUBSET_TRANS, MEM_LAST]) >>
                        `lookup n s.code = lookup n removed_state.code` by
                            metis_tac[code_rel_def] >> fs[] >>
                        Cases_on `lookup n removed_state.code` >> fs[] >>
                        Cases_on `x` >> fs[] >>
                        qspecl_then [`args`, `s`, `(h::t)`,
                            `p0`, `fromList2 p0`] mp_tac
                            get_locals_fromList2_FRONT >>
                        rw[] >> metis_tac[SUBSET_TRANS])
                    >>  fs[find_word_ref_def, domain_insert] >>
                        `lookup x' s.code = lookup x' removed_state.code` by
                            metis_tac[code_rel_def] >>
                        Cases_on `lookup x' removed_state.code` >> fs[] >>
                        Cases_on `x` >> fs[]
                        >- (rw[SUBSET_DEF] >>
                            fs[SUBSET_DEF, fromList2_def, get_locals_def])
                        >- (qspecl_then [`args`, `s`, `(h::t)`,
                            `fromList2 (h::t)`] mp_tac get_locals_fromList2 >>
                            rw[] >> metis_tac[SUBSET_TRANS])) >>
                PURE_TOP_CASE_TAC >> fs[] >>
                Cases_on `q = SOME Error` >> fs[] >> first_x_assum drule >>
                reverse(impl_tac)
                >- (strip_tac >> fs[] >> Cases_on `q` >> fs[] >> rw[] >> fs[])
                    >- (rw[dec_clock_def, call_env_def] >>
                        fs[add_ret_loc_def] >> Cases_on `dest` >>
                        fs[find_code_def]
                        >- (EVERY_CASE_TAC >> fs[] >> rveq >>
                            fs[] >> fs[no_install_code_def] >> res_tac)
                        >- (EVERY_CASE_TAC >> fs[] >> rveq >> fs[] >>
                            fs[no_install_code_def] >> res_tac)
                        >- (`∃ y ys . x = SNOC y ys` by
                                metis_tac[SNOC_CASES] >>
                            full_simp_tac std_ss [LAST_SNOC, FRONT_SNOC] >>
                            Cases_on `y` >> fs[] >> Cases_on `n0` >> fs[] >>
                            Cases_on `lookup n s.code` >> fs[] >>
                            Cases_on `x'` >> fs[] >> rveq >> fs[ADD1] >> rveq >>
                            fs[domain_find_loc_state] >>
                            `n ∈ domain reachable` by (
                                qspecl_then [`args`, `s`, `SNOC (Loc n 0) p0`,
                                    `n`, `0`] mp_tac get_vars_get_locals >>
                                strip_tac >> fs[MEM_SNOC] >> rfs[] >>
                                qspec_then `s` mp_tac domain_find_loc_state >>
                                rw[] >> fs[SUBSET_UNION, SUBSET_DEF]) >>
                            fs[code_closed_def] >> simp[SUBSET_DEF] >> rw[] >>
                            last_x_assum drule >> disch_then match_mp_tac >>
                            fs[is_reachable_def] >> match_mp_tac RTC_SINGLE >>
                            fs[is_adjacent_def] >>
                            `∃ aSetx . lookup n (analyse_word_code code1) =
                                SOME aSetx ∧ x ∈ domain aSetx` by (
                                rfs[lookup_fromAList] >>
                                drule lookup_analyse_word_code >> fs[]) >>
                            drule lookup_mk_wf_set_tree >> rw[] >>
                            asm_exists_tac >> fs[] >> fs[domain_lookup] >>
                            `wf_set_tree (mk_wf_set_tree
                                (analyse_word_code code1))`
                                by metis_tac[mk_wf_set_tree_thm] >>
                            fs[wf_set_tree_def] >> last_x_assum drule >>
                            fs[SUBSET_DEF, domain_lookup])
                        >- (fs[find_word_ref_def] >>
                            rename1 `n ∈ domain reachable` >>
                            rename1 `get_vars _ _ = SOME z` >>
                            fs[code_closed_def] >> simp[SUBSET_DEF] >> rw[] >>
                            last_x_assum drule >> disch_then match_mp_tac >>
                            fs[is_reachable_def] >> match_mp_tac RTC_SINGLE >>
                            fs[is_adjacent_def] >>
                            `∃ aSetx . lookup n (analyse_word_code code1) =
                                SOME aSetx ∧ x ∈ domain aSetx` by (
                                rfs[lookup_fromAList] >>
                                Cases_on `ALOOKUP code1 n` >> fs[] >>
                                Cases_on `x'` >> fs[] >>
                                drule lookup_analyse_word_code >> fs[]) >>
                            drule lookup_mk_wf_set_tree >> rw[] >>
                            asm_exists_tac >> fs[] >> fs[domain_lookup] >>
                            `wf_set_tree (mk_wf_set_tree
                                (analyse_word_code code1))`
                                by metis_tac[mk_wf_set_tree_thm] >>
                            fs[wf_set_tree_def] >> last_x_assum drule >>
                            fs[SUBSET_DEF, domain_lookup]))
               )
           )
        >> qmatch_asmsub_rename_tac`add_ret_loc (SOME l)`
        >>  PairCases_on `l` >> fs[] >> Cases_on `domain l1 = {}` >> fs[] >>
            fs[cut_env_def] >> Cases_on `domain l1 ⊆ domain s.locals` >>
            fs[] >>
            Cases_on `s.clock = 0` >> fs[]
            >- (fs[call_env_def, fromList2_def] >> rw[word_state_rel_def] >>
                rw[find_loc_state_def, domain_union,
                    get_locals_def, get_stack_def] >>
                fs[domain_find_loc_state, SUBSET_DEF, dest_result_loc_def])
            >>  fs[add_ret_loc_def] >>
                fs[find_word_ref_def, domain_find_loc_state, domain_union] >>
                `domain (find_word_ref p1) ⊆ domain reachable` by (
                    Cases_on `dest` >> fs[find_code_def, code_closed_def]
                    >- (Cases_on `LAST (Loc l3 l4 :: x)`>> fs[] >>
                        Cases_on `lookup n s.code` >> fs[] >>
                        Cases_on `n0` >> fs[] >> Cases_on `x'` >> fs[] >>
                        rveq >> Cases_on `x` >> rfs[bad_dest_args_def] >>
                        rw[] >>
                        `n ∈ domain reachable` by (
                            `MEM (Loc n 0) (h::t)` by
                                metis_tac[MEM, LAST_DEF, MEM_LAST] >>
                            qspecl_then [`args`, `s`, `h::t`, `n`, `0`] mp_tac
                                get_vars_get_locals >> rw[] >>
                                fs[SUBSET_DEF]) >>
                        rw[SUBSET_DEF] >>
                        qpat_x_assum `∀ n m . n ∈ _ ∧ _ ⇒ _`
                            (qspecl_then [`n`, `x`] mp_tac) >>
                        reverse(impl_tac) >> fs[] >> fs[is_reachable_def] >>
                        match_mp_tac RTC_SINGLE >> fs[is_adjacent_def] >>
                        `wf_set_tree(mk_wf_set_tree
                            (analyse_word_code code1))` by
                            metis_tac[mk_wf_set_tree_thm] >>
                        fs[wf_set_tree_def] >>
                        qexists_tac `find_word_ref p1` >>
                        fs[lookup_analyse_word_code] >>
                        `lookup n (analyse_word_code code1) =
                            SOME (find_word_ref p1)` by
                            fs[lookup_fromAList, lookup_analyse_word_code] >>
                        imp_res_tac lookup_mk_wf_set_tree >>
                        `wf (find_word_ref p1) ∧ wf y` by
                            metis_tac[wf_find_word_ref] >>
                        `y = find_word_ref p1` by (
                            fs[spt_eq_thm, domain_lookup, EXTENSION] >> rw[] >>
                            Cases_on `lookup n' y` >> fs[] >>
                            Cases_on `lookup n' (find_word_ref p1)` >>
                            fs[] >> rfs[] >>
                            qpat_x_assum `∀ x . lookup _ _ = _ ⇔ _`
                                (qspec_then `n'` mp_tac) >> rw[] >> fs[]) >>
                        rveq >>
                        fs[domain_lookup, SUBSET_DEF] >> metis_tac[])
                    >- (Cases_on `lookup x' s.code` >> fs[] >> Cases_on `x''` >>
                        fs[] >> rw[SUBSET_DEF] >>
                        qpat_x_assum `∀ n m . n ∈ _ ∧ _ ⇒ _`
                            (qspecl_then [`x'`, `x''`] mp_tac) >>
                        reverse(impl_tac) >> fs[] >>
                        fs[is_reachable_def] >> match_mp_tac RTC_SINGLE >>
                        fs[is_adjacent_def] >>
                        `wf_set_tree(mk_wf_set_tree
                            (analyse_word_code code1))` by
                            metis_tac[mk_wf_set_tree_thm] >>
                        fs[wf_set_tree_def] >> qexists_tac `find_word_ref p1` >>
                        fs[lookup_analyse_word_code] >>
                        `lookup x' (analyse_word_code code1) =
                            SOME (find_word_ref p1)` by
                            (match_mp_tac lookup_analyse_word_code >>
                            qexists_tac `SUC (LENGTH x)` >>
                            metis_tac[lookup_fromAList]) >>
                        imp_res_tac lookup_mk_wf_set_tree >>
                        `wf (find_word_ref p1) ∧ wf y` by
                            metis_tac[wf_find_word_ref] >>
                        `y = find_word_ref p1` by
                            (fs[spt_eq_thm, domain_lookup, EXTENSION] >> rw[] >>
                                Cases_on `lookup n y` >> fs[] >>
                                Cases_on `lookup n (find_word_ref p1)` >> fs[] >>
                                rfs[] >>
                                qpat_x_assum `∀ x . lookup _ _ = _ ⇔ _`
                                    (qspec_then `n` mp_tac) >> rw[] >> fs[]) >>
                            rveq >>
                        fs[domain_lookup, SUBSET_DEF] >> metis_tac[]) ) >>
                `code_closed reachable (call_env p0 (push_env
                    (inter s.locals l1) handler (dec_clock s))).code` by (
                    fs[call_env_def, dec_clock_def] >> Cases_on `handler` >>
                    TRY(PairCases_on `x'` >> fs[]) >>
                    fs[push_env_def, env_to_list_def] ) >>
                `word_state_rel reachable (call_env p0 (push_env
                    (inter s.locals l1) handler (dec_clock s)))
                    (call_env p0 (push_env (inter s.locals l1) handler
                    (dec_clock removed_state)))` by (
                        `∀ e . MEM e p0 ⇒ (case dest_word_loc e of | NONE => {}
                            | SOME n => {n}) ⊆ domain reachable` by (
                        rw[] >> Cases_on `e` >>
                        fs[dest_word_loc_def, SUBSET_EMPTY] >>
                        Cases_on `dest` >>
                        fs[find_code_def] >>
                        EVERY_CASE_TAC >> fs[] >> rveq >>
                        imp_res_tac MEM_FRONT >> fs[] >>
                        qspecl_then [`args`, `s`, `x`, `n`, `n0`] mp_tac
                            get_vars_get_locals >> rw[] >> fs[SUBSET_DEF]) >>
                      fs[dec_clock_def, call_env_def] >> Cases_on `handler`
                      >- (fs[push_env_def, env_to_list_def] >>
                          fs[word_state_rel_def, domain_find_loc_state] >> rw[]
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
                          >- fs[stack_list_rearrange_lemma]) ) >>
                Cases_on `evaluate (p1, call_env p0 (push_env
                    (inter s.locals l1) handler (dec_clock s)))` >> fs[] >>
                Cases_on `q` >> fs[] >> Cases_on `x'` >> fs[] >>
                `r.gc_fun = s.gc_fun` by (
                    fs[call_env_def, dec_clock_def] >> Cases_on `handler` >>
                    fs[push_env_def, env_to_list_def]
                    >- (drule evaluate_consts >> fs[]) >> PairCases_on `x'` >>
                    fs[push_env_def, env_to_list_def]
                    >> drule evaluate_consts >> fs[] ) >>
                `gc_no_new_locs (call_env p0 (push_env (inter s.locals l1)
                    handler (dec_clock s))).gc_fun` by (
                    fs[call_env_def, dec_clock_def] >> Cases_on `handler` >>
                    fs[push_env_def, env_to_list_def] >>
                    PairCases_on `x'` >> fs[push_env_def, env_to_list_def] )
                >- (Cases_on `w ≠ Loc l3 l4` >> fs[] >> fs[pop_env_def] >>
                    Cases_on `r.stack` >> fs[] >>
                    Cases_on `h` >> fs[] >>
                    rename [‘r.stack = StackFrame l opt::t’] >>
                    Cases_on `opt` >> fs[]
                    >- (Cases_on `domain (fromAList l) =
                        domain (inter s.locals l1)` >> fs[] >> rw[] >>
                        first_x_assum (qspecl_then [`reachable`,
                            `call_env p0 (push_env (inter s.locals l1)
                                handler (dec_clock removed_state))`] mp_tac) >>
                        rw[] >> fs[] >> `no_install p1` by
                            metis_tac[no_install_find_code] >> fs[] >>
                        `s'.stack = r.stack` by fs[word_state_rel_def] >>
                        fs[] >>
                        first_x_assum (qspecl_then [`reachable`,
                            `set_var l0 w0 (s' with <|locals := fromAList l;
                            stack := t|>)`] mp_tac) >>
                        reverse(impl_tac) >> fs[set_var_def] >>
                        `r.code = s.code` by (fs[call_env_def, dec_clock_def] >>
                            Cases_on `handler`
                            >- (fs[push_env_def, env_to_list_def] >>
                                imp_res_tac no_install_evaluate_const_code >>
                                fs[])
                            >- (PairCases_on `x'` >> fs[] >>
                                fs[push_env_def, env_to_list_def] >>
                                imp_res_tac no_install_evaluate_const_code >>
                                fs[])) >>
                        fs[] >> fs[word_state_rel_def, domain_find_loc_state] >>
                        rw[]
                        >- (`domain (get_locals (fromAList l)) ⊆
                                domain reachable` by
                                imp_res_tac get_stack_hd_thm >>
                            qspecl_then [`l0`, `w0`, `fromAList l`] mp_tac
                                get_locals_insert >> rw[] >>
                            Cases_on `w0` >> fs[dest_word_loc_def] >> rw[]
                            >- imp_res_tac SUBSET_TRANS >>
                            fs[dest_result_loc_def] >> fs[SUBSET_DEF] >>
                            metis_tac[])
                        >- metis_tac[get_stack_hd_thm]
                        >- (Cases_on `handler` >> fs[] >>
                            PairCases_on `x'` >> fs[])
                        >- (`s'.code = removed_state.code` by
                                (imp_res_tac no_install_evaluate_const_code >>
                                 fs[]) >> rveq >> fs[])
                       )
                    >- (Cases_on `x'` >> fs[] >>
                        Cases_on `domain (fromAList l) =
                            domain (inter s.locals l1)` >> fs[] >> rw[] >>
                        first_x_assum (qspecl_then [`reachable`,
                            `call_env p0 (push_env (inter s.locals l1)
                            handler (dec_clock removed_state))`] mp_tac) >>
                            rw[] >>
                        fs[] >> `no_install p1` by
                            metis_tac[no_install_find_code] >> fs[] >>
                        `s'.stack = r.stack` by fs[word_state_rel_def] >>
                        fs[] >>
                        first_x_assum (qspecl_then [`reachable`,`set_var l0 w0
                            (s' with <|locals := fromAList l; stack := t;
                                handler := q|>)`] mp_tac) >>
                        reverse(impl_tac) >> fs[set_var_def] >>
                        `r.code = s.code` by (fs[call_env_def, dec_clock_def] >>
                        Cases_on `handler`
                            >- (fs[push_env_def, env_to_list_def] >>
                                imp_res_tac no_install_evaluate_const_code >>
                                fs[])
                            >- (PairCases_on `x'` >> fs[] >>
                                fs[push_env_def, env_to_list_def] >>
                                imp_res_tac no_install_evaluate_const_code >>
                                fs[])) >>
                        fs[] >>
                        fs[word_state_rel_def, domain_find_loc_state] >>
                        rw[]
                        >- (`domain (get_locals (fromAList l)) ⊆
                                domain reachable` by
                                imp_res_tac get_stack_hd_thm >>
                            qspecl_then [`l0`, `w0`, `fromAList l`]
                                mp_tac get_locals_insert >> rw[] >>
                            Cases_on `w0` >> fs[dest_word_loc_def] >> rw[]
                            >- imp_res_tac SUBSET_TRANS >>
                            fs[dest_result_loc_def] >> fs[SUBSET_DEF] >>
                            metis_tac[])
                        >- metis_tac[get_stack_hd_thm]
                        >- (Cases_on `handler` >> fs[] >>
                            PairCases_on `x'` >> fs[])
                        >- (`s'.code = removed_state.code` by
                                (imp_res_tac no_install_evaluate_const_code >>
                                fs[]) >>
                            rveq >> fs[])
                        )
                   )
                >- (Cases_on `handler` >> fs[] >>
                    `no_install p1` by metis_tac[no_install_find_code] >> fs[]
                    >- (rw[] >> qmatch_goalsub_abbrev_tac `(_, n_state)` >>
                        first_x_assum (qspecl_then [`reachable`, `n_state`]
                            mp_tac) >>
                        reverse(impl_tac) >- (rw[] >> fs[])
                        >> fs[call_env_def, push_env_def, dec_clock_def,
                                env_to_list_def, word_state_rel_def,
                                domain_find_loc_state] >>
                        rw[] >> `n_state.code = removed_state.code` by
                            (fs[Abbr `n_state`]) >> rveq >> fs[])
                    >- (PairCases_on `x'` >> fs[] >>
                        Cases_on `w ≠ Loc x'2 x'3` >> fs[] >>
                        Cases_on `domain r.locals =
                            domain (inter s.locals l1)` >> fs[] >> rw[] >>
                        first_x_assum (qspecl_then [`reachable`,
                            `call_env p0 (push_env (inter s.locals l1)
                            (SOME (x'0,x'1,x'2,x'3))
                            (dec_clock removed_state))`] mp_tac) >> rw[] >>
                        fs[] >>
                        `s'.locals = r.locals` by fs[word_state_rel_def] >>
                        fs[] >>
                        first_x_assum (qspecl_then [`reachable`,
                            `set_var x'0 w0 s'`] mp_tac) >>
                        reverse(impl_tac) >> fs[] >>
                        fs[set_var_def, word_state_rel_def,
                            domain_find_loc_state] >> rw[]
                        >- (qspecl_then [`x'0`, `w0`, `r.locals`] mp_tac
                            get_locals_insert >> rw[] >>
                            Cases_on `w0` >> fs[dest_word_loc_def] >> rw[]
                            >- imp_res_tac SUBSET_TRANS >>
                            fs[dest_result_loc_def] >> fs[SUBSET_DEF] >>
                            metis_tac[])
                        >> `r.code = s.code ∧ removed_state.code = s'.code` by (
                                fs[push_env_def, env_to_list_def] >>
                                imp_res_tac no_install_evaluate_const_code >>
                                fs[]) >> fs[])
                   )
                >>  first_x_assum (qspecl_then [`reachable`,
                    `call_env p0 (push_env (inter s.locals l1) handler
                        (dec_clock removed_state))`] mp_tac) >>
                    rw[] >> rw[] >> rfs[dec_clock_def] >> `no_install p1` by
                        metis_tac[no_install_find_code] >> fs[]
        )
    >- ( (* FFI *)
        simp[wordSemTheory.evaluate_def] >> fs[get_var_def] >>
        Cases_on `lookup len1 s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >> Cases_on `lookup ptr1 s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >>
        Cases_on `lookup len2 s.locals` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `lookup ptr2 s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >> Cases_on `cut_env names s.locals` >> fs[] >>
        Cases_on `read_bytearray c' (w2n c)
            (mem_load_byte_aux s.memory s.mdomain s.be)` >> fs[] >>
        Cases_on `read_bytearray c''' (w2n c'')
            (mem_load_byte_aux s.memory s.mdomain s.be)` >> fs[] >>
        simp[case_eq_thms]
        \\ reverse strip_tac \\ fs[word_state_rel_def, cut_env_def]
          \\ rveq \\ fs[call_env_def,dest_result_loc_def,domain_find_loc_state]
          \\ fs[get_memory_write_bytearray_lemma]
        >- EVAL_TAC
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
        Cases_on `get_var r1 s` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `get_var r2 s` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `buffer_write s.data_buffer c c'` >> fs[] >>
        fs[get_var_def, buffer_write_def] >>
        strip_tac >> rveq >>
        fs[word_state_rel_def] >>
        fs[domain_find_loc_state, dest_result_loc_def]
        )
    >- ( (* CodeBufferWrite *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `get_var r1 s` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `get_var r2 s` >> fs[] >> Cases_on `x` >> fs[] >>
        Cases_on `buffer_write s.code_buffer c (w2w c')` >> fs[] >>
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
        simp[wordSemTheory.evaluate_def] >> fs[get_var_def] >>
        Cases_on `lookup r1 s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >>
        `get_var_imm ri s = get_var_imm ri removed_state` by (
            Cases_on `ri` >> fs[get_var_imm_def, get_var_def]) >>
        fs[] >> Cases_on `get_var_imm ri removed_state` >> fs[] >>
        Cases_on `x` >> fs[] >> Cases_on `word_cmp cmp c c'` >> fs[] >> rw[] >>
        fs[find_word_ref_def, domain_union, no_install_def]
        )
    >- ( (* Raise *)
        simp[wordSemTheory.evaluate_def] >> fs[get_var_def] >>
        Cases_on `lookup n s.locals` >> fs[] >>
        `jump_exc s = NONE ⇔ jump_exc removed_state = NONE` by (
            fs[jump_exc_def] >> EVERY_CASE_TAC) >>
        drule word_state_rel_jump_exc >> strip_tac >> Cases_on `jump_exc s` >>
        fs[] >>
        PairCases_on `x'` >> fs[] >> rw[] >> fs[word_state_rel_def]
        >> Cases_on `x` >> fs[dest_result_loc_def] >> fs[SUBSET_DEF] >>
            qspecl_then [`n'`, `s.locals`] mp_tac domain_get_locals_lookup >>
            rw[] >>
            fs[domain_find_loc_state] >> res_tac >> fs[]
        )
    >- ( (* Return *)
        simp[wordSemTheory.evaluate_def] >> fs[get_var_def] >>
        Cases_on `lookup n s.locals` >> fs[] >>
        Cases_on `x` >> fs[] >> Cases_on `lookup m s.locals` >> fs[] >> rw[] >>
        fs[call_env_def, fromList2_def, word_state_rel_def,
            domain_find_loc_state, get_locals_def]
        >> Cases_on `x` >> fs[dest_result_loc_def] >> fs[SUBSET_DEF] >>
            qspecl_then [`n''`, `s.locals`] mp_tac domain_get_locals_lookup >>
            rw[] >>
            fs[domain_find_loc_state] >> res_tac >> fs[]
        )
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
        >- (fs[call_env_def, fromList2_def] >> rw[word_state_rel_def] >>
            rw[find_loc_state_def, domain_union,
                get_locals_def, get_stack_def] >>
            fs[domain_find_loc_state, SUBSET_DEF, dest_result_loc_def])
        >- (rw[] >> fs[dec_clock_def, word_state_rel_def, domain_find_loc_state,
            dest_result_loc_def])
        )
    >- ( (* Store *)
        simp[wordSemTheory.evaluate_def] >>
        `word_exp s exp = word_exp removed_state exp` by
            metis_tac[word_state_rel_word_exp] >> fs[] >>
        Cases_on `word_exp removed_state exp` >> fs[] >> Cases_on `x` >> fs[] >>
        fs[get_var_def] >>
        Cases_on `lookup v s.locals` >> fs[] >> fs[mem_store_def] >>
        Cases_on `c ∈ s.mdomain` >> fs[] >> rw[] >>
        fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def] >>
        qspecl_then [`c`, `x`, `s.memory`, `s.mdomain`] mp_tac
            get_memory_update >> fs[] >>
        Cases_on `x` >> fs[dest_word_loc_def] >> rw[]
        >- metis_tac[SUBSET_TRANS] >>
        `n ∈ domain reachable` by (imp_res_tac domain_get_locals_lookup >>
            fs[SUBSET_DEF]) >>
        fs[SUBSET_DEF] >> metis_tac[]
        )
    >- ( (* Set *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `v = Handler ∨ v = BitmapBase` >> fs[] >>
        `word_exp s exp = word_exp removed_state exp` by
            metis_tac[word_state_rel_word_exp] >> fs[] >>
        Cases_on `word_exp removed_state exp` >> fs[] >>
        fs[set_store_def] >> rw[] >>
        fs[word_state_rel_def, domain_find_loc_state, dest_result_loc_def] >>
        fs[find_word_ref_def] >>
        qspecl_then [`s.store`, `v`, `x`] mp_tac get_store_update >>
        Cases_on `x` >> fs[dest_word_loc_def] >> rw[]
        >- metis_tac[SUBSET_TRANS] >>
        `n ∈ domain reachable` by (Cases_on `exp` >> fs[word_exp_def]
            >- (metis_tac[domain_get_locals_lookup, SUBSET_DEF])
            >- (metis_tac[domain_get_store, SUBSET_DEF])
            >- (Cases_on `word_exp removed_state e` >> fs[] >>
                Cases_on `x` >> fs[] >>
                fs[mem_load_def] >> metis_tac[domain_get_memory, SUBSET_DEF])
            >- (`MAP (λa. word_exp s a) l =
                    MAP (λa. word_exp removed_state a) l` by (
                    fs[MAP_EQ_f] >> rw[] >>
                    `word_state_rel reachable s removed_state` by
                        fs[word_state_rel_def, domain_find_loc_state] >>
                    metis_tac[word_state_rel_word_exp]) >> fs[] >>
                Cases_on `the_words (MAP (λa. word_exp removed_state a) l)` >>
                fs[])
            >- (Cases_on `word_exp removed_state e` >> fs[] >>
                Cases_on `x` >> fs[])) >>
        fs[SUBSET_DEF] >> metis_tac[]
        )
    >- ( (* Get *)
        simp[wordSemTheory.evaluate_def] >>
        Cases_on `FLOOKUP s.store name` >> fs[] >>
        fs[set_var_def] >>
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
        simp[wordSemTheory.evaluate_def] >>
        `word_exp s exp = word_exp removed_state exp` by
            metis_tac[word_state_rel_word_exp] >> fs[] >>
        fs[] >> Cases_on `word_exp removed_state exp` >> fs[] >>
        fs[set_var_def] >> rw[] >> fs[word_state_rel_def, domain_find_loc_state,
            dest_result_loc_def] >>
        qspecl_then [`v`, `x`, `s.locals`] mp_tac get_locals_insert >>
        Cases_on `x` >> fs[dest_word_loc_def] >- metis_tac[SUBSET_TRANS] >>
        rw[] >>
        `n ∈ domain reachable` by (Cases_on `exp` >> fs[word_exp_def]
            >- (metis_tac[domain_get_locals_lookup, SUBSET_DEF])
            >- (metis_tac[domain_get_store, SUBSET_DEF])
            >- (Cases_on `word_exp removed_state e` >> fs[] >> Cases_on `x` >>
                fs[] >>
                fs[mem_load_def] >> metis_tac[domain_get_memory, SUBSET_DEF])
            >- (`MAP (λa. word_exp s a) l =
                    MAP (λa. word_exp removed_state a) l` by (
                        fs[MAP_EQ_f] >> rw[] >>
                        `word_state_rel reachable s removed_state` by
                            fs[word_state_rel_def, domain_find_loc_state] >>
                    metis_tac[word_state_rel_word_exp]) >> fs[] >>
                Cases_on `the_words (MAP (λa. word_exp removed_state a) l)` >>
                fs[])
            >- (Cases_on `word_exp removed_state e` >> fs[] >>
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
        reachable = closure_spt (insert start () LN)
                        (mk_wf_set_tree (analyse_word_code code1)) ∧
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
    reverse(impl_tac) >- metis_tac[]
    >>  qspecl_then [`code1`, `analyse_word_code code1`,
                     `insert start () LN`, `start`,
            `mk_wf_set_tree (analyse_word_code code1)`]
            mp_tac analyse_word_code_reachable_thm >>
        reverse(impl_tac >> rw[])
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
        >- (fs[evaluate_def, get_vars_def, bad_dest_args_def,
                add_ret_loc_def, find_code_def] >>
            Cases_on `lookup start (fromAList code1)` >> fs[] >>
            fs[get_var_def] >> EVERY_CASE_TAC >> fs[] >>
            fs[lookup_fromAList] >> drule lookup_analyse_word_code >> rw[] >>
            fs[domain_lookup] >>
            drule lookup_mk_wf_set_tree >> rw[] >> fs[])
QED

val _ = export_theory();

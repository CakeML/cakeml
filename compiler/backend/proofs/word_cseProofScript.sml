(*
  Correctness proof for word_cse
*)
Theory word_cseProof
Libs
  preamble helperLib
Ancestors
  wordLang wordSem wordProps word_cse alist toto reg_alloc
  word_simp wordConvs

(* The reads of a stored arith fact, tracked as self-mappings in
   to_canonical (registered at fact creation), so that a later write to any
   of them resets the data. *)
Definition in_names_set_def:
  in_names_set (a:'a arith) tc ⇔
    EVERY (λr. sptree$lookup r tc = SOME r) (arithReads a)
End

(* The invariant is factored into a STATE-FREE syntactic part (wf_data) and
   a state-dependent semantic part (sem_inv). The If-join merge needs
   syntactic facts about the not-taken branch's data without having run that
   branch: wf_data is established for it by the standalone syntactic theorem
   word_cse_wf_data. The (:'a) itself argument ties the quantified arith
   instructions to the state's word width. *)
Definition wf_data_def:
  wf_data (:'a) (data:knowledge) ⇔
    (∀r v.
       lookup r data.to_canonical = SOME v ⇒
       lookup v data.to_canonical = SOME v ∧ ODD r ∧ ODD v) ∧
    (∀r v.
       lookup r data.to_latest = SOME v ⇒
       r IN domain data.to_canonical ∧
       v IN domain data.to_canonical) ∧
    (∀k v.
       balanced_map$lookup listCmp k data.instrs_mem = SOME v ⇒
       lookup v data.to_canonical = SOME v) ∧
    (∀(a:'a arith) v.
       balanced_map$lookup listCmp (instToNumList (Arith a)) data.instrs_mem = SOME v ⇒
       in_names_set a data.to_canonical ∧ can_mem_arith a) ∧
    (∀op src v.
       balanced_map$lookup listCmp (OpCurrHeapToNumList op src) data.instrs_mem = SOME v ⇒
       lookup src data.to_canonical = SOME src) ∧
    (∀x v.
       ALOOKUP data.gets_mem x = SOME v ⇒
       lookup v data.to_canonical = SOME v) ∧
    ALL_DISTINCT (MAP FST data.gets_mem) ∧
    balanced_map$invariant listCmp data.instrs_mem ∧
    (∀k v.
       balanced_map$lookup listCmp k data.loads_mem = SOME v ⇒
       lookup v data.to_canonical = SOME v) ∧
    (∀op a (ofs:'a word) v.
       balanced_map$lookup listCmp (loadToNumList op a ofs) data.loads_mem = SOME v ⇒
       lookup a data.to_canonical = SOME a) ∧
    balanced_map$invariant listCmp data.loads_mem
End

Definition sem_inv_def:
  sem_inv (data:knowledge) (s:('a,'c,'ffi) wordSem$state) ⇔
    (∀r v.
       lookup r data.to_canonical = SOME v ⇒
       get_var r s = get_var v s) ∧
    (∀r v.
       lookup r data.to_latest = SOME v ⇒
       get_var r s = get_var v s) ∧
    (∀n c v.
       balanced_map$lookup listCmp (instToNumList (Const n c)) data.instrs_mem = SOME v ⇒
       lookup v s.locals = SOME (Word c)) ∧
    (∀(a:'a arith) v.
       balanced_map$lookup listCmp (instToNumList (Arith a)) data.instrs_mem = SOME v ⇒
       ∃w. get_var v s = SOME w ∧
           evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s)) ∧
    (∀op src v.
       balanced_map$lookup listCmp (OpCurrHeapToNumList op src) data.instrs_mem = SOME v ⇒
       ∃w. word_exp s (Op op [Var src; Lookup CurrHeap]) = SOME w ∧
           get_var v s = SOME w) ∧
    (∀l v.
       balanced_map$lookup listCmp [48; l] data.instrs_mem = SOME v ⇒
       lookup v s.locals = SOME (Loc l 0)) ∧
    (∀x v.
       ALOOKUP data.gets_mem x = SOME v ⇒
       ∃w. FLOOKUP s.store x = SOME w ∧ get_var v s = SOME w) ∧
    (∀op a ofs v.
       ¬is_store op ∧
       balanced_map$lookup listCmp (loadToNumList op a ofs) data.loads_mem = SOME v ⇒
       ∃w. get_var v s = SOME w ∧
           ∀r. evaluate (Inst (Mem op r (Addr a ofs)), s) = (NONE, set_var r w s))
End

Definition data_inv_def:
  data_inv (data:knowledge) (s:('a,'c,'ffi) wordSem$state) ⇔
    wf_data (:'a) data ∧ sem_inv data s
End

Theorem canonicalRegs_correct[simp]:
  ∀data r s. data_inv data s ⇒ get_var (canonicalRegs data r) s = get_var r s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def, sem_inv_def, canonicalRegs_def]
  \\ fs [lookup_any_def]
  \\ Cases_on ‘lookup r data.to_canonical’ \\ fs []
QED

Theorem canonicalRegs'_correct[simp]:
  ∀a data r s. data_inv data s ⇒ get_var (canonicalRegs' a data r) s = get_var r s
Proof
  rw [canonicalRegs'_def]
QED

Theorem canonicalRegs_correct_bis[simp]:
  ∀data r s. data_inv data s ⇒ lookup (canonicalRegs data r) s.locals = lookup r s.locals
Proof
  rpt strip_tac
  \\ gvs [data_inv_def, sem_inv_def, canonicalRegs_def]
  \\ fs [lookup_any_def]
  \\ Cases_on ‘lookup r data.to_canonical’ \\ fs [get_var_def]
QED

Theorem canonicalArith_correct[simp]:
  ∀data s a. data_inv data s ⇒ inst (Arith (canonicalArith data a)) s = inst (Arith a) s
Proof
  rpt gen_tac
  \\ strip_tac
  \\ Cases_on ‘a’ \\ gvs [canonicalArith_def, inst_def, assign_def, word_exp_def, the_words_def]
  \\ gvs [get_vars_def]
  \\ fs [GSYM get_var_def]
  \\ Cases_on ‘get_var n0 s’ \\ fs []
  \\ Cases_on ‘x’ \\ fs []
  \\ Cases_on ‘r’ \\ fs []
  \\ gvs [canonicalImmReg'_def, word_exp_def, GSYM get_var_def]
QED

Theorem wordToNum_unique[simp]:
  ∀c1 c2. wordToNum c1 = wordToNum c2 ⇔ c1 = c2
Proof
  gvs [wordToNum_def]
QED

Theorem arithOpToNum_eq[simp]:
  ∀op1 op2. arithOpToNum op1 = arithOpToNum op2 ⇔ op1 = op2
Proof
  strip_tac
  \\ Cases_on ‘op1’ \\ Cases_on ‘op2’ \\ gvs [arithOpToNum_def]
QED

Theorem memOpToNum_eq[simp]:
  ∀op1 op2. memOpToNum op1 = memOpToNum op2 ⇔ op1 = op2
Proof
  strip_tac
  \\ Cases_on ‘op1’ \\ Cases_on ‘op2’ \\ gvs [memOpToNum_def]
QED

Theorem firstRegOfArith_canonicalArith[simp]:
  ∀data a. firstRegOfArith (canonicalArith data a) = firstRegOfArith a
Proof
  rpt gen_tac \\ Cases_on ‘a’ \\ gvs [firstRegOfArith_def, canonicalArith_def]
QED

(* Some usefull proofs to automize *)

Theorem data_inv_locals[simp]:
  ∀s. s with locals := s.locals = s
Proof
  rpt gen_tac
  \\ gvs [state_component_equality]
QED

Theorem insert_eq:
  ∀(n1:num) n2 v1 v2 l. insert n1 v1 l = insert n1 v2 l ⇔ v1 = v2
Proof
  rpt strip_tac \\ eq_tac \\ gvs [] \\ strip_tac
  \\ ‘lookup n1 (insert n1 v1 l) = lookup n1 (insert n1 v2 l)’ by asm_rewrite_tac []
  \\ gvs []
QED

(* A stored arith fact concerns a can_mem_arith shape, whose evaluation is
   a single set_var of a value computed from the registers it reads; the
   fact transports across a write to any register the instruction does not
   read. *)
Theorem evaluate_arith_set_var:
  ∀a r u w s.
    can_mem_arith a ∧ ¬MEM r (arithReads a) ⇒
    (evaluate (Inst (Arith a), set_var r u s) =
       (NONE, set_var (firstRegOfArith a) w (set_var r u s)) ⇔
     evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s))
Proof
  rpt strip_tac
  \\ Cases_on ‘a’
  \\ gvs [can_mem_arith_def, arithReads_def, firstRegOfArith_def]
  >- (Cases_on ‘r'’ \\ gvs [can_mem_arith_def, arithReads_def]
      >- (gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def,
               get_var_def, set_var_def, lookup_insert]
          \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
          \\ Cases_on ‘x’ \\ gvs []
          \\ Cases_on ‘lookup n' s.locals’ \\ gvs []
          \\ Cases_on ‘x’ \\ gvs []
          \\ Cases_on ‘word_op b [c; c']’ \\ gvs [state_component_equality, insert_eq])
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def,
              get_var_def, set_var_def, lookup_insert]
      \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ Cases_on ‘word_op b [c'; c]’ \\ gvs [state_component_equality, insert_eq])
  >- (Cases_on ‘r'’ \\ gvs [can_mem_arith_def, arithReads_def]
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def,
              get_var_def, set_var_def, lookup_insert]
      \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ Cases_on ‘word_sh s' c' (w2n c)’ \\ gvs [state_component_equality, insert_eq])
  >- (gvs [evaluate_def, inst_def, assign_def, get_vars_def, get_var_def,
           set_var_def, lookup_insert]
      \\ Cases_on ‘lookup n1 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs [state_component_equality, insert_eq]
      \\ Cases_on ‘c = 0w’ \\ gvs [state_component_equality, insert_eq])
QED

(* A successful load evaluation determines the loaded value from the address
   register and memory alone, so the same load at ANY destination evaluates
   the same way — this gives the ∀-quantified-destination form stored by the
   loads clause of sem_inv. *)
Theorem evaluate_load_any_dest:
  ∀op r0 a ofs w s r.
    ¬is_store op ∧
    evaluate (Inst (Mem op r0 (Addr a ofs)), s) = (NONE, set_var r0 w s) ⇒
    evaluate (Inst (Mem op r (Addr a ofs)), s) = (NONE, set_var r w s)
Proof
  rpt strip_tac \\ Cases_on ‘op’
  \\ gvs [is_store_def, evaluate_def, inst_def, AllCaseEqs(), set_var_def,
          insert_eq]
QED

(* A load reads its address register, the memory fields and be; the
   evaluation equation transports across a write to any OTHER register, for
   any destination (including the written one, by insert collapsing). *)
Theorem evaluate_load_set_var:
  ∀op r a ofs n u w s.
    ¬is_store op ∧ a ≠ n ⇒
    (evaluate (Inst (Mem op r (Addr a ofs)), set_var n u s) =
       (NONE, set_var r w (set_var n u s)) ⇔
     evaluate (Inst (Mem op r (Addr a ofs)), s) = (NONE, set_var r w s))
Proof
  rpt strip_tac
  \\ Cases_on ‘op’ \\ gvs [is_store_def]
  \\ gvs [evaluate_def, inst_def, word_exp_def, the_words_def, set_var_def,
          lookup_insert, mem_load_def, get_var_def]
  >- (Cases_on ‘lookup a s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs [wordLangTheory.word_op_def]
      \\ IF_CASES_TAC \\ gvs [state_component_equality, insert_eq])
  \\ Cases_on ‘lookup a s.locals’ \\ gvs []
  \\ Cases_on ‘x’ \\ gvs [wordLangTheory.word_op_def]
  \\ TOP_CASE_TAC
  \\ gvs [AllCaseEqs()] \\ gvs [state_component_equality, insert_eq]
QED

(* A load's address register may be replaced by any register holding the
   same value — the bridge from the executed address to its canonical
   representative. *)
Theorem evaluate_load_change_addr[local]:
  ∀op r a a' ofs w (s:('a,'c,'ffi) wordSem$state).
    ¬is_store op ∧
    lookup a' s.locals = lookup a s.locals ∧
    evaluate (Inst (Mem op r (Addr a ofs)), s) = (NONE, set_var r w s) ⇒
    evaluate (Inst (Mem op r (Addr a' ofs)), s) = (NONE, set_var r w s)
Proof
  rpt strip_tac \\ Cases_on ‘op’
  \\ gvs [is_store_def, evaluate_def, inst_def, word_exp_def, the_words_def,
          get_var_def, AllCaseEqs()]
QED

(* A storable arith instruction reads and writes registers only; its
   evaluation equation is insensitive to the memory contents. *)
Theorem evaluate_arith_memory[local]:
  ∀a w s m.
    can_mem_arith a ⇒
    (evaluate (Inst (Arith a), s with memory := m) =
       (NONE, set_var (firstRegOfArith a) w s with memory := m) ⇔
     evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s))
Proof
  rpt strip_tac \\ Cases_on ‘a’
  \\ gvs [can_mem_arith_def, firstRegOfArith_def, evaluate_def, inst_def,
          assign_def, word_exp_def, the_words_def, get_vars_def, get_var_def,
          set_var_def, AllCaseEqs()]
  \\ gvs [state_component_equality, insert_eq]
  \\ Cases_on ‘r’ \\ gvs [can_mem_arith_def, word_exp_def, get_var_def]
QED

(* Every register mentioned by the invariant lies in the domain of
   to_canonical, so an untracked register is unmentioned. *)
Theorem wf_data_untracked:
  ∀data n.
    wf_data (:'a) data ∧ sptree$lookup n data.to_canonical = NONE ⇒
    (∀r v. lookup r data.to_canonical = SOME v ⇒ r ≠ n ∧ v ≠ n) ∧
    (∀r v. lookup r data.to_latest = SOME v ⇒ r ≠ n ∧ v ≠ n) ∧
    (∀k v. balanced_map$lookup listCmp k data.instrs_mem = SOME v ⇒ v ≠ n) ∧
    (∀(a:'a arith) v.
       balanced_map$lookup listCmp (instToNumList (Arith a)) data.instrs_mem = SOME v ⇒
       ¬MEM n (arithReads a) ∧ can_mem_arith a) ∧
    (∀op src v.
       balanced_map$lookup listCmp (OpCurrHeapToNumList op src) data.instrs_mem = SOME v ⇒
       src ≠ n) ∧
    (∀x v. ALOOKUP data.gets_mem x = SOME v ⇒ v ≠ n) ∧
    (∀k v. balanced_map$lookup listCmp k data.loads_mem = SOME v ⇒ v ≠ n) ∧
    (∀op a (ofs:'a word) v.
       balanced_map$lookup listCmp (loadToNumList op a ofs) data.loads_mem = SOME v ⇒
       a ≠ n)
Proof
  rw [wf_data_def]
  \\ rpt strip_tac
  \\ res_tac
  \\ gvs [domain_lookup, in_names_set_def, EVERY_MEM]
  \\ res_tac \\ gvs []
QED

Theorem data_inv_set_var:
  ∀data s n v.
    sptree$lookup n data.to_canonical = NONE ⇒
    data_inv data (set_var n v s) = data_inv data s
Proof
  rpt gen_tac \\ strip_tac
  \\ rw [data_inv_def]
  \\ Cases_on ‘wf_data (:'a) data’ \\ gvs []
  \\ drule_all wf_data_untracked \\ strip_tac
  \\ gvs [sem_inv_def]
  \\ eq_tac \\ strip_tac \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ res_tac
  \\ gvs [get_var_set_var, set_var_def, lookup_insert,
          word_exp_def, the_words_def, evaluate_arith_set_var]
  \\ gvs [AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
  >- (res_tac \\ gvs [])
  >- (‘a ≠ n’ by (strip_tac \\ gvs [])
      \\ gvs [SRULE [set_var_def] evaluate_load_set_var])
  >- (‘v' ≠ n’ by (strip_tac \\ gvs []) \\ qexists_tac ‘w’ \\ gvs [])
  >- (‘src ≠ n ∧ v' ≠ n’ by (rpt strip_tac \\ gvs []) \\ gvs [])
  \\ ‘v' ≠ n ∧ a ≠ n’ by (rpt strip_tac \\ gvs []) \\ qexists_tac ‘w’
  \\ gvs [SRULE [set_var_def] evaluate_load_set_var]
QED

(* The unset_var (locals-delete) clones of the set_var transports, for
   StoreConsts' two unsets. *)
Theorem evaluate_arith_unset_var[local]:
  ∀a r w (s:('a,'c,'ffi) wordSem$state).
    can_mem_arith a ∧ ¬MEM r (arithReads a) ⇒
    (evaluate (Inst (Arith a), unset_var r s) =
       (NONE, set_var (firstRegOfArith a) w (unset_var r s)) ⇔
     evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s))
Proof
  rpt strip_tac
  \\ Cases_on ‘a’
  \\ gvs [can_mem_arith_def, arithReads_def, firstRegOfArith_def]
  >- (Cases_on ‘r'’ \\ gvs [can_mem_arith_def, arithReads_def]
      >- (gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def,
               get_var_def, set_var_def, unset_var_def, lookup_delete]
          \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
          \\ Cases_on ‘x’ \\ gvs []
          \\ Cases_on ‘lookup n' s.locals’ \\ gvs []
          \\ Cases_on ‘x’ \\ gvs []
          \\ Cases_on ‘word_op b [c; c']’
          \\ gvs [state_component_equality, insert_eq])
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def,
              get_var_def, set_var_def, unset_var_def, lookup_delete]
      \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ Cases_on ‘word_op b [c'; c]’
      \\ gvs [state_component_equality, insert_eq])
  >- (Cases_on ‘r'’ \\ gvs [can_mem_arith_def, arithReads_def]
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def,
              get_var_def, set_var_def, unset_var_def, lookup_delete]
      \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ Cases_on ‘word_sh s' c' (w2n c)’
      \\ gvs [state_component_equality, insert_eq])
  >- (gvs [evaluate_def, inst_def, assign_def, get_vars_def, get_var_def,
           set_var_def, unset_var_def, lookup_delete]
      \\ Cases_on ‘lookup n1 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs []
      \\ Cases_on ‘lookup n0 s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs [state_component_equality, insert_eq]
      \\ Cases_on ‘c = 0w’ \\ gvs [state_component_equality, insert_eq])
QED

Theorem evaluate_load_unset_var[local]:
  ∀op r a ofs n w (s:('a,'c,'ffi) wordSem$state).
    ¬is_store op ∧ a ≠ n ⇒
    (evaluate (Inst (Mem op r (Addr a ofs)), unset_var n s) =
       (NONE, set_var r w (unset_var n s)) ⇔
     evaluate (Inst (Mem op r (Addr a ofs)), s) = (NONE, set_var r w s))
Proof
  rpt strip_tac
  \\ Cases_on ‘op’ \\ gvs [is_store_def]
  \\ gvs [evaluate_def, inst_def, word_exp_def, the_words_def, set_var_def,
          unset_var_def, lookup_delete, mem_load_def, get_var_def]
  >- (Cases_on ‘lookup a s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs [wordLangTheory.word_op_def]
      \\ IF_CASES_TAC \\ gvs [state_component_equality, insert_eq])
  \\ Cases_on ‘lookup a s.locals’ \\ gvs []
  \\ Cases_on ‘x’ \\ gvs [wordLangTheory.word_op_def]
  \\ TOP_CASE_TAC
  \\ gvs [AllCaseEqs()] \\ gvs [state_component_equality, insert_eq]
QED

Theorem data_inv_unset_var:
  ∀data (s:('a,'c,'ffi) wordSem$state) n.
    sptree$lookup n data.to_canonical = NONE ⇒
    data_inv data (unset_var n s) = data_inv data s
Proof
  rpt gen_tac \\ strip_tac
  \\ rw [data_inv_def]
  \\ Cases_on ‘wf_data (:'a) data’ \\ gvs []
  \\ drule_all wf_data_untracked \\ strip_tac
  \\ gvs [sem_inv_def]
  \\ eq_tac \\ strip_tac \\ rpt conj_tac \\ rpt gen_tac \\ strip_tac
  \\ res_tac
  \\ gvs [get_var_def, unset_var_def, lookup_delete,
          word_exp_def, the_words_def, evaluate_arith_unset_var]
  \\ gvs [AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
  \\ res_tac \\ gvs []
  \\ ‘a ≠ n’ by (strip_tac \\ gvs [])
  \\ gvs [SRULE [unset_var_def] evaluate_load_unset_var]
QED

Theorem not_seen_data_inv_alist_insert[simp]:
  ∀data s l r v.
    sptree$lookup r data.to_canonical = NONE ⇒
    data_inv data (s with locals := l) ⇒
    data_inv data (s with locals := insert r v l)
Proof
  rpt strip_tac
  \\ ‘s with locals := insert r v l = set_var r v (s with locals := l)’ by
       gvs [set_var_def]
  \\ gvs [data_inv_set_var]
QED

Theorem listCmpEq_correct:
  ∀L1 L2. listCmp L1 L2 = Equal ⇔ L1 = L2
Proof
  strip_tac
  \\Induct_on ‘L1’
    >- (Cases_on ‘L2’
        \\ rw[listCmp_def])
    >- (Cases_on ‘L2’
        >- rw[listCmp_def]
        >- (strip_tac >>
            Cases_on ‘h=h'’
            \\ rw[listCmp_def]))
QED

Theorem antisym_listCmp:
  ∀x y. listCmp x y = Greater ⇔ listCmp y x = Less
Proof
  gen_tac \\ Induct_on ‘x’
  >- (Cases_on ‘y’ \\ gvs [listCmp_def])
  \\ rpt gen_tac
  \\ Cases_on ‘y’ \\ gvs [listCmp_def]
  \\ Cases_on ‘h=h'’ \\ gvs []
  \\ Cases_on ‘h>h'’ \\ gvs []
QED

Theorem transit_listCmp:
  ∀x y z. listCmp x y = Less ∧ listCmp y z = Less ⇒ listCmp x z = Less
Proof
  gen_tac
  \\ Induct_on ‘x’
  >- (Cases_on ‘y’ \\ Cases_on ‘z’ \\ gvs [listCmp_def])
  \\ rpt gen_tac \\ strip_tac
  \\ Cases_on ‘y’ \\ Cases_on ‘z’ \\ gvs [listCmp_def]
  \\ Cases_on ‘h=h'’ \\ Cases_on ‘h'=h''’ \\ gvs [listCmp_def]
  >- (‘listCmp x t = Less ∧ listCmp t t' = Less’ by gvs []
      \\ first_x_assum drule_all \\ gvs [])
  \\ Cases_on ‘h>h'’ \\ Cases_on ‘h'>h''’ \\ gvs []
QED

Theorem TotOrd_listCmp[simp]:
  TotOrd listCmp
Proof
  gvs [TotOrd, listCmpEq_correct, antisym_listCmp, transit_listCmp, SF SFY_ss]
QED

Theorem good_cmp_listCmp[simp]:
  good_cmp listCmp
Proof
  irule comparisonTheory.TotOrder_imp_good_cmp \\ fs []
QED

Theorem lookup_listCmp_empty[simp]:
  lookup listCmp k empty = NONE
Proof
  EVAL_TAC
QED

Theorem data_inv_empty[simp]:
  ∀s. data_inv empty_data s
Proof
  gvs [data_inv_def, wf_data_def, sem_inv_def, empty_data_def] \\ EVAL_TAC \\ gvs []
QED

Theorem invariant_listCmp_empty[simp]:
  invariant listCmp empty
Proof
  EVAL_TAC
QED

(* The loads-wipe transport: a pure memory write preserves the whole
   invariant once the load facts are wiped — every other clause reads only
   locals, store and code. Used by the Mem-store and StoreConsts cases. *)
Theorem data_inv_memory:
  ∀data s m.
    data_inv data s ⇒
    data_inv (data with loads_mem := empty) (s with memory := m)
Proof
  rpt strip_tac
  \\ gvs [data_inv_def, wf_data_def, sem_inv_def]
  \\ rpt strip_tac \\ res_tac \\ gvs [get_var_def]
  >- (‘can_mem_arith a’ by res_tac \\ gvs [evaluate_arith_memory])
  \\ gvs [word_exp_def, the_words_def, get_store_def, AllCaseEqs()]
QED

(* A storable arith instruction reads and writes locals only; its evaluation
   equation transports to any state with the same locals. *)
Theorem evaluate_arith_agree[local]:
  ∀a w (s1:('a,'c,'ffi) wordSem$state) (s2:('a,'c,'ffi) wordSem$state).
    evaluate (Inst (Arith a), s1) =
      (NONE, set_var (firstRegOfArith a) w s1) ∧
    can_mem_arith a ∧ s2.locals = s1.locals ⇒
    evaluate (Inst (Arith a), s2) = (NONE, set_var (firstRegOfArith a) w s2)
Proof
  rpt strip_tac \\ Cases_on ‘a’
  \\ gvs [can_mem_arith_def, firstRegOfArith_def, evaluate_def, inst_def,
          assign_def, word_exp_def, the_words_def, get_vars_def, get_var_def,
          set_var_def, AllCaseEqs(), insert_eq]
  \\ gvs [state_component_equality, insert_eq]
  \\ Cases_on ‘r’ \\ gvs [can_mem_arith_def, word_exp_def, get_var_def]
  \\ gvs [AllCaseEqs(), state_component_equality, insert_eq]
QED

(* A load reads its address register, the memory fields and be; its
   evaluation equation transports to any state agreeing on those. *)
Theorem evaluate_load_agree[local]:
  ∀op r a ofs w (s1:('a,'c,'ffi) wordSem$state) (s2:('a,'c,'ffi) wordSem$state).
    evaluate (Inst (Mem op r (Addr a ofs)), s1) = (NONE, set_var r w s1) ∧
    ¬is_store op ∧ s2.locals = s1.locals ∧ s2.memory = s1.memory ∧
    s2.mdomain = s1.mdomain ∧ s2.be = s1.be ⇒
    evaluate (Inst (Mem op r (Addr a ofs)), s2) = (NONE, set_var r w s2)
Proof
  rpt strip_tac \\ Cases_on ‘op’
  \\ gvs [is_store_def, evaluate_def, inst_def, word_exp_def, the_words_def,
          get_var_def, set_var_def, mem_load_def, AllCaseEqs(), insert_eq]
  \\ gvs [state_component_equality, insert_eq]
QED

(* The generic state-agreement transport: the whole invariant depends only
   on locals, store and the memory fields.  Covers buffer writes, ffi
   extensions and stack changes in one lemma. *)
Theorem data_inv_state_agree:
  ∀data (s1:('a,'c,'ffi) wordSem$state) (s2:('a,'c,'ffi) wordSem$state).
    data_inv data s1 ∧
    s2.locals = s1.locals ∧ s2.store = s1.store ∧ s2.memory = s1.memory ∧
    s2.mdomain = s1.mdomain ∧ s2.be = s1.be ⇒
    data_inv data s2
Proof
  rpt strip_tac
  \\ fs [data_inv_def, wf_data_def, sem_inv_def]
  \\ rpt strip_tac \\ res_tac \\ fs [get_var_def]
  >- (drule_all evaluate_arith_agree \\ gvs [])
  >- (gvs [word_exp_def, the_words_def, AllCaseEqs()]
      \\ gvs [get_var_def, get_store_def])
  \\ gen_tac \\ qpat_x_assum ‘∀r. evaluate _ = _’ (qspec_then ‘r’ assume_tac)
  \\ drule_all evaluate_load_agree \\ gvs []
QED

(* IF-JOIN MERGE SUPPORT

   bm_inter_eq_acc m2 m1 acc inserts into acc exactly the entries of m1 that
   are present with an equal value in m2; characterised pointwise on to_fmap. *)
Theorem bm_inter_eq_acc_thm:
  ∀m2 m1 acc.
    invariant listCmp m2 ∧ invariant listCmp m1 ∧ invariant listCmp acc ⇒
    invariant listCmp (bm_inter_eq_acc m2 m1 acc) ∧
    ∀ks. FLOOKUP (to_fmap listCmp (bm_inter_eq_acc m2 m1 acc)) ks =
         case FLOOKUP (to_fmap listCmp m1) ks of
         | NONE => FLOOKUP (to_fmap listCmp acc) ks
         | SOME v => if FLOOKUP (to_fmap listCmp m2) ks = SOME v then SOME v
                     else FLOOKUP (to_fmap listCmp acc) ks
Proof
  gen_tac \\ Induct_on ‘m1’
  >- rw [bm_inter_eq_acc_def, balanced_mapTheory.to_fmap_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [balanced_mapTheory.invariant_eq]
  \\ qabbrev_tac ‘acc1 = if balanced_map$lookup listCmp k m2 = SOME v
                         then balanced_map$insert listCmp k v acc else acc’
  \\ ‘invariant listCmp acc1 ∧
      ∀ks. FLOOKUP (to_fmap listCmp acc1) ks =
           if ks = key_set listCmp k ∧ balanced_map$lookup listCmp k m2 = SOME v
           then SOME v else FLOOKUP (to_fmap listCmp acc) ks’ by
        (rw [Abbr‘acc1’]
         \\ gvs [balanced_mapTheory.insert_thm, FLOOKUP_UPDATE]
         \\ rw [] \\ gvs [])
  \\ simp [bm_inter_eq_acc_def]
  \\ first_x_assum (qspec_then ‘acc1’ mp_tac)
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ gen_tac \\ Cases_on ‘ks = key_set listCmp k’
  \\ gvs [balanced_mapTheory.to_fmap_def, FLOOKUP_UPDATE, FLOOKUP_FUNION,
          balanced_mapTheory.lookup_thm, FLOOKUP_DEF]
  \\ rw [FAPPLY_FUPDATE_THM, finite_mapTheory.FUNION_DEF]
  \\ gvs [IN_DISJOINT] \\ res_tac \\ gvs []
  \\ metis_tac []
QED

Theorem invariant_bm_inter_eq:
  ∀m1 m2.
    invariant listCmp m1 ∧ invariant listCmp m2 ⇒
    invariant listCmp (bm_inter_eq m1 m2)
Proof
  rw [bm_inter_eq_def]
  \\ qspecl_then [‘m2’,‘m1’,‘empty’] mp_tac bm_inter_eq_acc_thm
  \\ gvs [balanced_mapTheory.empty_def, balanced_mapTheory.invariant_def]
QED

Theorem lookup_bm_inter_eq:
  ∀m1 m2 k v.
    invariant listCmp m1 ∧ invariant listCmp m2 ⇒
    (balanced_map$lookup listCmp k (bm_inter_eq m1 m2) = SOME v ⇔
     balanced_map$lookup listCmp k m1 = SOME v ∧
     balanced_map$lookup listCmp k m2 = SOME v)
Proof
  rw [bm_inter_eq_def]
  \\ qspecl_then [‘m2’,‘m1’,‘empty’] mp_tac bm_inter_eq_acc_thm
  \\ impl_tac
  >- gvs [balanced_mapTheory.empty_def, balanced_mapTheory.invariant_def]
  \\ strip_tac
  \\ gvs [balanced_mapTheory.lookup_thm, balanced_mapTheory.empty_def,
          balanced_mapTheory.to_fmap_def]
  \\ first_x_assum (qspec_then ‘key_set listCmp k’ assume_tac)
  \\ gvs [AllCaseEqs()]
  \\ rpt strip_tac \\ gvs []
QED

Theorem ALL_DISTINCT_MAP_FST_FILTER[local]:
  ∀l P. ALL_DISTINCT (MAP FST l) ⇒ ALL_DISTINCT (MAP FST (FILTER P l))
Proof
  Induct \\ rw [] \\ gvs [MEM_MAP, MEM_FILTER] \\ metis_tac []
QED

(* A merged fact is present (with equal value) in both branches' data; its
   semantic content comes from whichever branch actually ran, its syntactic
   well-formedness from both. *)
Theorem data_inv_merge_l:
  ∀d1 d2 (s:('a,'c,'ffi) wordSem$state).
    wf_data (:'a) d1 ∧ wf_data (:'a) d2 ∧ sem_inv d1 s ⇒
    data_inv (merge_data d1 d2) s
Proof
  rpt strip_tac \\ gvs [data_inv_def, merge_data_def]
  \\ qpat_x_assum ‘wf_data _ d1’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘wf_data _ d2’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv d1 s’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()] \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq]
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) d1.to_canonical ∧ _’ drule
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) d2.to_canonical ∧ _’ drule
      \\ rpt strip_tac
      \\ gvs [in_names_set_def, EVERY_MEM]
      \\ rpt strip_tac
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [MEM_FILTER]
      \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (irule ALL_DISTINCT_MAP_FST_FILTER \\ simp [])
  >- (irule invariant_bm_inter_eq \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (irule invariant_bm_inter_eq \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac
      \\ simp [SF SFY_ss])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac
      \\ simp [SF SFY_ss])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [MEM_FILTER]
      \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
      \\ res_tac \\ simp [SF SFY_ss])
  \\ rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac
  \\ simp [SF SFY_ss]
QED

Theorem data_inv_merge_r:
  ∀d1 d2 (s:('a,'c,'ffi) wordSem$state).
    wf_data (:'a) d1 ∧ wf_data (:'a) d2 ∧ sem_inv d2 s ⇒
    data_inv (merge_data d1 d2) s
Proof
  rpt strip_tac \\ gvs [data_inv_def, merge_data_def]
  \\ qpat_x_assum ‘wf_data _ d1’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘wf_data _ d2’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv d2 s’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()] \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq]
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) d1.to_canonical ∧ _’ drule
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) d2.to_canonical ∧ _’ drule
      \\ rpt strip_tac
      \\ gvs [in_names_set_def, EVERY_MEM]
      \\ rpt strip_tac
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [MEM_FILTER]
      \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (irule ALL_DISTINCT_MAP_FST_FILTER \\ simp [])
  >- (irule invariant_bm_inter_eq \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (irule invariant_bm_inter_eq \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac
      \\ simp [SF SFY_ss])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac
      \\ simp [SF SFY_ss])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [MEM_FILTER]
      \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
      \\ res_tac \\ simp [SF SFY_ss])
  \\ rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq] \\ res_tac
  \\ simp [SF SFY_ss]
QED

(* ------------------------------------------------------------------------
   KNOWLEDGE-UPDATE SUPPORT

   Lookups in an extended instruction map, read registration, transport of
   data_inv across the writes a rewritten program performs, and generic
   extension lemmas for the knowledge fields.
   ------------------------------------------------------------------------ *)

Theorem lookup_insert_listCmp:
  ∀k i v m.
    invariant listCmp m ⇒
    invariant listCmp (insert listCmp i v m) ∧
    lookup listCmp k (insert listCmp i v m) =
    (if k = i then SOME v else lookup listCmp k m)
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [balanced_mapTheory.insert_thm]
  \\ gvs [balanced_mapTheory.lookup_thm, balanced_mapTheory.insert_thm,
          FLOOKUP_UPDATE, balanced_mapTheory.key_set_eq, listCmpEq_correct]
  \\ rw [] \\ gvs []
QED

Theorem register_read_simps[simp]:
  (register_read data r).instrs_mem = data.instrs_mem ∧
  (register_read data r).to_latest = data.to_latest ∧
  (register_read data r).gets_mem = data.gets_mem ∧
  (register_read data r).loads_mem = data.loads_mem
Proof
  rw [register_read_def]
QED

Theorem register_reads_simps[simp]:
  ∀rs data.
    (register_reads data rs).instrs_mem = data.instrs_mem ∧
    (register_reads data rs).to_latest = data.to_latest ∧
    (register_reads data rs).gets_mem = data.gets_mem ∧
    (register_reads data rs).loads_mem = data.loads_mem
Proof
  Induct \\ rw [register_reads_def]
QED

Theorem lookup_register_read:
  sptree$lookup x (register_read data r).to_canonical =
  if x = r ∧ ¬EVEN r ∧ sptree$lookup r data.to_canonical = NONE
  then SOME r else sptree$lookup x data.to_canonical
Proof
  rw [register_read_def, keep_data_def, lookup_insert] \\ gvs []
QED

Theorem lookup_register_reads:
  ∀rs data x.
    sptree$lookup x (register_reads data rs).to_canonical =
    if MEM x rs ∧ ¬EVEN x ∧ sptree$lookup x data.to_canonical = NONE
    then SOME x else sptree$lookup x data.to_canonical
Proof
  Induct \\ gvs [register_reads_def]
  \\ rw [lookup_register_read] \\ gvs []
QED

(* Extending to_canonical with a fresh key mapped to itself or to an
   already-canonical register preserves the invariant: the fresh key is
   unmentioned elsewhere, and existing self-maps survive the insert. *)
Theorem data_inv_insert_to_canonical:
  ∀data (s:('a,'c,'ffi) wordSem$state) x y.
    data_inv data s ∧
    sptree$lookup x data.to_canonical = NONE ∧
    sptree$lookup y (insert x y data.to_canonical) = SOME y ∧
    ODD x ∧ ODD y ∧
    get_var x s = get_var y s ⇒
    data_inv (data with to_canonical := insert x y data.to_canonical) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw []
      \\ gvs [lookup_insert]
      \\ qpat_x_assum ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                             lookup v data.to_canonical = SOME v ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.instrs_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) data.to_canonical ∧ _’ drule
      \\ strip_tac
      \\ gvs [in_names_set_def, EVERY_MEM]
      \\ rpt strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op src v. _ ⇒ lookup src data.to_canonical = SOME src’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀x v. ALOOKUP data.gets_mem x = SOME v ⇒
                             lookup v data.to_canonical = SOME v’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.loads_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op a ofs v. _ ⇒ lookup a data.to_canonical = SOME a’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw [] \\ gvs [])
  \\ rpt gen_tac \\ strip_tac \\ res_tac \\ gvs []
QED

(* to_latest entries only require domain membership and agreeing values. *)
Theorem data_inv_insert_to_latest:
  ∀data (s:('a,'c,'ffi) wordSem$state) x y.
    data_inv data s ∧
    x ∈ domain data.to_canonical ∧ y ∈ domain data.to_canonical ∧
    get_var x s = get_var y s ⇒
    data_inv (data with to_latest := insert x y data.to_latest) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                             lookup v data.to_canonical = SOME v ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw [] \\ gvs []
      \\ qpat_x_assum ‘∀r v. lookup r data.to_latest = SOME v ⇒ _ ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.instrs_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op src v. _ ⇒ lookup src data.to_canonical = SOME src’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀x v. ALOOKUP data.gets_mem x = SOME v ⇒
                             lookup v data.to_canonical = SOME v’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.loads_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op a ofs v. _ ⇒ lookup a data.to_canonical = SOME a’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw [] \\ gvs [])
  \\ rpt gen_tac \\ strip_tac \\ res_tac \\ gvs []
QED

(* Record a fresh Get fact: the destination becomes self-tracked and the
   store name maps to it.  Matches the Get-miss arm of word_cse. *)
Theorem data_inv_insert_gets[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) name v w.
    data_inv data s ∧
    sptree$lookup v data.to_canonical = NONE ∧ ODD v ∧
    ALOOKUP data.gets_mem name = NONE ∧
    FLOOKUP s.store name = SOME w ∧ get_var v s = SOME w ⇒
    data_inv (data with <|to_canonical := insert v v data.to_canonical;
                          to_latest := insert v v data.to_latest;
                          gets_mem := (name,v)::data.gets_mem|>) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def, ALOOKUP_NONE] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw []
      \\ gvs [lookup_insert]
      \\ qpat_x_assum ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                             lookup v data.to_canonical = SOME v ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw [] \\ gvs []
      \\ qpat_x_assum ‘∀r v. lookup r data.to_latest = SOME v ⇒ _ ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.instrs_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) data.to_canonical ∧ _’ drule
      \\ strip_tac
      \\ gvs [in_names_set_def, EVERY_MEM]
      \\ rpt strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op src v. _ ⇒ lookup src data.to_canonical = SOME src’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [AllCaseEqs(), lookup_insert]
      \\ qpat_x_assum ‘∀x v. ALOOKUP data.gets_mem x = SOME v ⇒
                             lookup v data.to_canonical = SOME v’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- gvs [ALOOKUP_NONE]
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.loads_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op a ofs v. _ ⇒ lookup a data.to_canonical = SOME a’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  \\ rpt gen_tac \\ strip_tac \\ gvs [AllCaseEqs()] \\ res_tac \\ gvs [SF SFY_ss]
QED

(* Dropping store facts never hurts. Matches the Set-arm FILTER. *)
Theorem data_inv_filter_gets[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) x.
    data_inv data s ⇒
    data_inv (data with gets_mem := FILTER (λ(m,n). m ≠ x) data.gets_mem) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def, ALOOKUP_FILTER, ALL_DISTINCT_MAP_FST_FILTER]
  \\ rpt conj_tac
  \\ rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [SF SFY_ss]
QED

(* Record a true store fact about an already-tracked register.  Matches the
   Set-arm cons. *)
Theorem data_inv_cons_gets[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) x h w.
    data_inv data s ∧
    ALOOKUP data.gets_mem x = NONE ∧
    sptree$lookup h data.to_canonical = SOME h ∧
    FLOOKUP s.store x = SOME w ∧ get_var h s = SOME w ⇒
    data_inv (data with gets_mem := (x,h)::data.gets_mem) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def, ALOOKUP_NONE]
  \\ rpt conj_tac
  \\ rpt gen_tac \\ strip_tac \\ gvs [AllCaseEqs(), ALOOKUP_NONE]
  \\ res_tac \\ gvs [SF SFY_ss]
QED

(* A store write to a name no fact mentions preserves the invariant: only
   the OpCurrHeap clause (CurrHeap) and the gets clauses read the store. *)
Theorem data_inv_set_store:
  ∀data (s:('a,'c,'ffi) wordSem$state) x w.
    data_inv data s ∧ x ≠ CurrHeap ∧ ALOOKUP data.gets_mem x = NONE ⇒
    data_inv data (set_store x w s)
Proof
  rpt strip_tac
  \\ fs [data_inv_def, wf_data_def, sem_inv_def]
  \\ rpt strip_tac \\ res_tac
  \\ fs [get_var_def, set_store_def, FLOOKUP_UPDATE]
  >- (drule evaluate_arith_agree
      \\ disch_then (qspec_then ‘s with store := s.store |+ (x,w)’ mp_tac)
      \\ gvs [])
  >- gvs [word_exp_def, the_words_def, get_store_def, FLOOKUP_UPDATE,
          AllCaseEqs()]
  >- (IF_CASES_TAC \\ gvs [])
  \\ gen_tac \\ qpat_x_assum ‘∀r. evaluate _ = _’ (qspec_then ‘r’ assume_tac)
  \\ drule evaluate_load_agree
  \\ disch_then (qspec_then ‘s with store := s.store |+ (x,w)’ mp_tac)
  \\ gvs []
QED

(* Re-registering a register's canonical entry is sound: fresh self-map for
   an untracked register, no-op for a tracked one. *)
Theorem data_inv_reinsert_canonical[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) v.
    data_inv data s ∧ ODD v ⇒
    data_inv (data with to_canonical :=
                insert v (lookup_any v data.to_canonical v)
                  data.to_canonical) s
Proof
  rpt strip_tac \\ gvs [lookup_any_def]
  \\ Cases_on ‘lookup v data.to_canonical’ \\ gvs []
  >- (irule data_inv_insert_to_canonical \\ gvs [lookup_insert])
  \\ ‘insert v x data.to_canonical = data.to_canonical’ by
       gvs [insert_unchanged]
  \\ ‘data with to_canonical := data.to_canonical = data’ by
       simp [word_cseTheory.knowledge_component_equality]
  \\ simp []
QED

Theorem empty_data_loads_wipe[simp]:
  empty_data with loads_mem := empty = empty_data
Proof
  simp [empty_data_def]
QED

Theorem lookup_empty_data[simp]:
  sptree$lookup r empty_data.to_canonical = NONE
Proof
  simp [empty_data_def, lookup_def]
QED

Theorem data_inv_register_read:
  ∀data (s:('a,'c,'ffi) wordSem$state) r.
    data_inv data s ⇒ data_inv (register_read data r) s
Proof
  rw [register_read_def, keep_data_def]
  \\ irule data_inv_insert_to_canonical
  \\ gvs [ODD_EVEN]
QED

Theorem data_inv_register_reads:
  ∀rs data (s:('a,'c,'ffi) wordSem$state).
    data_inv data s ⇒ data_inv (register_reads data rs) s
Proof
  Induct \\ rw [register_reads_def]
  \\ first_x_assum irule \\ gvs [data_inv_register_read]
QED

(* Invalidation facts for multi-output instructions. *)
Theorem lookup_invalidate_regs_mono[local]:
  ∀ws data r.
    sptree$lookup r data.to_canonical = NONE ⇒
    sptree$lookup r (invalidate_regs data ws).to_canonical = NONE
Proof
  Induct \\ rw [invalidate_regs_def]
  \\ first_x_assum irule
  \\ rw [invalidate_data_def, keep_data_def]
QED

Theorem lookup_invalidate_regs[local]:
  ∀ws data r.
    MEM r ws ⇒
    sptree$lookup r (invalidate_regs data ws).to_canonical = NONE
Proof
  Induct \\ rw [invalidate_regs_def] \\ gvs [SF SFY_ss]
  \\ irule lookup_invalidate_regs_mono
  \\ rw [invalidate_data_def, keep_data_def]
  \\ Cases_on ‘lookup h data.to_canonical’ \\ gvs [keep_data_def]
QED

Theorem data_inv_invalidate_regs[local]:
  ∀ws data (s:('a,'c,'ffi) wordSem$state).
    data_inv data s ⇒ data_inv (invalidate_regs data ws) s
Proof
  Induct \\ rw [invalidate_regs_def]
  \\ first_x_assum irule
  \\ rw [invalidate_data_def, keep_data_def]
QED

(* The invariant never reads the fp registers. *)
Theorem data_inv_set_fp_var[simp]:
  ∀data v x (s:('a,'c,'ffi) wordSem$state).
    data_inv data (set_fp_var v x s) = data_inv data s
Proof
  rpt gen_tac \\ eq_tac \\ strip_tac
  \\ irule data_inv_state_agree
  \\ first_assum (irule_at Any)
  \\ gvs [set_fp_var_def]
QED

Theorem with_locals_insert[local]:
  s with locals := insert r v l = set_var r v (s with locals := l)
Proof
  gvs [set_var_def]
QED

Theorem data_inv_alist_insert_locals[local]:
  ∀xs ys data (s:('a,'c,'ffi) wordSem$state) l.
    EVERY (λx. sptree$lookup x data.to_canonical = NONE) xs ⇒
    (data_inv data (s with locals := alist_insert xs ys l) ⇔
     data_inv data (s with locals := l))
Proof
  Induct \\ gvs [alist_insert_def]
  \\ rpt strip_tac \\ Cases_on ‘ys’ \\ gvs [alist_insert_def]
  \\ gvs [with_locals_insert, data_inv_set_var]
QED

(* data_inv is insensitive to writes to untracked registers. *)
Theorem data_inv_set_vars:
  ∀xs ys data (s:('a,'c,'ffi) wordSem$state).
    EVERY (λx. sptree$lookup x data.to_canonical = NONE) xs ⇒
    (data_inv data (set_vars xs ys s) ⇔ data_inv data s)
Proof
  rw [set_vars_def, data_inv_alist_insert_locals]
QED

(* The Move every cache hit emits. *)
Theorem evaluate_Move1:
  ∀pri r k w (s:('a,'c,'ffi) wordSem$state).
    get_var k s = SOME w ⇒
    evaluate (Move pri [(r,k)], s) = (NONE, set_var r w s)
Proof
  rw [evaluate_def, get_vars_def, set_vars_def, alist_insert_def, set_var_def]
QED

Theorem shiftToNum_eq[simp]:
  ∀s1 s2. shiftToNum s1 = shiftToNum s2 ⇔ s1 = s2
Proof
  Cases \\ Cases \\ gvs [shiftToNum_def]
QED

(* The instruction-map key of a can_mem_arith instruction determines its
   operation and reads (but not its destination), hence also the value it
   computes: two instructions with the same key evaluate identically up to
   the destination register. The sem_inv arith clause quantifies over all
   instructions with a stored key, so inserting a fact for one of them must
   yield the fact for all of them. *)
Theorem arith_keys_eq:
  ∀a1 a2.
    can_mem_arith a1 ∧ arithToNumList a1 = arithToNumList a2 ⇒
    can_mem_arith a2 ∧ arithReads a2 = arithReads a1 ∧
    ∀(s:('a,'c,'ffi) wordSem$state) w.
      evaluate (Inst (Arith a1), s) = (NONE, set_var (firstRegOfArith a1) w s) ⇒
      evaluate (Inst (Arith a2), s) = (NONE, set_var (firstRegOfArith a2) w s)
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on ‘a1’ \\ Cases_on ‘a2’
  \\ gvs [can_mem_arith_def, arithToNumList_def, regImmToNumList_def]
  >- (Cases_on ‘r’ \\ Cases_on ‘r'’
      \\ gvs [can_mem_arith_def, regImmToNumList_def, arithReads_def,
              firstRegOfArith_def]
      \\ rpt strip_tac
      \\ gvs [evaluate_def, inst_def, assign_def, AllCaseEqs(), set_var_def,
              state_component_equality, insert_eq])
  >- (Cases_on ‘r’ \\ Cases_on ‘r'’
      \\ gvs [can_mem_arith_def, regImmToNumList_def, arithReads_def,
              firstRegOfArith_def]
      \\ rpt strip_tac
      \\ gvs [evaluate_def, inst_def, assign_def, AllCaseEqs(), set_var_def,
              state_component_equality, insert_eq])
  \\ gvs [arithReads_def, firstRegOfArith_def] \\ rpt strip_tac
  \\ gvs [evaluate_def, inst_def, assign_def, AllCaseEqs(), set_var_def,
          state_component_equality, insert_eq]
QED

(* Storing a new fact: one lemma per key family, each requiring the holder
   to be self-mapped and the fact's semantic content to hold. *)
Theorem data_inv_insert_instrs_Const[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) r n (w:'a word).
    data_inv data s ∧
    sptree$lookup r data.to_canonical = SOME r ∧
    lookup r s.locals = SOME (Word w) ⇒
    data_inv (data with instrs_mem :=
                insert listCmp (instToNumList (Const n w)) r data.instrs_mem) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def, lookup_insert_listCmp] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                             lookup v data.to_canonical = SOME v ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_latest = SOME v ⇒ _ ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [AllCaseEqs()] \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) data.to_canonical ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀x v. ALOOKUP data.gets_mem x = SOME v ⇒
                             lookup v data.to_canonical = SOME v’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.loads_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op a ofs v. _ ⇒ lookup a data.to_canonical = SOME a’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  \\ rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

Theorem data_inv_insert_instrs_Arith[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) r (a:'a arith) w.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = SOME r ∧
    can_mem_arith a ∧ in_names_set a data.to_canonical ∧
    get_var r s = SOME w ∧
    evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s) ⇒
    data_inv (data with instrs_mem :=
                insert listCmp (instToNumList (Arith a)) r data.instrs_mem) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def, lookup_insert_listCmp] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                             lookup v data.to_canonical = SOME v ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_latest = SOME v ⇒ _ ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [AllCaseEqs()] \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [instToNumList_def]
      \\ rw []
      >- (qspecl_then [‘a’, ‘a'’] mp_tac arith_keys_eq \\ impl_tac >- gvs []
          \\ strip_tac \\ gvs [in_names_set_def])
      >- (qspecl_then [‘a’, ‘a'’] mp_tac arith_keys_eq \\ impl_tac >- gvs []
          \\ strip_tac \\ gvs [in_names_set_def])
      \\ qpat_x_assum ‘lookup listCmp (3::arithToNumList a') _ = SOME _’
           (assume_tac o REWRITE_RULE [GSYM instToNumList_def])
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) data.to_canonical ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀x v. ALOOKUP data.gets_mem x = SOME v ⇒
                             lookup v data.to_canonical = SOME v’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.loads_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op a ofs v. _ ⇒ lookup a data.to_canonical = SOME a’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [instToNumList_def]
      \\ rw []
      >- (qspecl_then [‘a’, ‘a'’] mp_tac arith_keys_eq \\ impl_tac >- gvs []
          \\ strip_tac \\ first_x_assum drule \\ strip_tac
          \\ qexists_tac ‘w’ \\ gvs [])
      \\ qpat_x_assum ‘lookup listCmp (3::arithToNumList a') _ = SOME _’
           (assume_tac o REWRITE_RULE [GSYM instToNumList_def])
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ ∃w2. get_var _ _ = SOME _ ∧ evaluate _ = _’ drule
      \\ strip_tac \\ gvs [SF SFY_ss])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  \\ rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

Theorem data_inv_insert_instrs_OpCurrHeap[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) r op src w.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = SOME r ∧
    sptree$lookup src data.to_canonical = SOME src ∧
    word_exp s (Op op [Var src; Lookup CurrHeap]) = SOME w ∧
    get_var r s = SOME w ⇒
    data_inv (data with instrs_mem :=
                insert listCmp (OpCurrHeapToNumList op src) r data.instrs_mem) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def, lookup_insert_listCmp] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                             lookup v data.to_canonical = SOME v ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_latest = SOME v ⇒ _ ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [AllCaseEqs()] \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) data.to_canonical ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀x v. ALOOKUP data.gets_mem x = SOME v ⇒
                             lookup v data.to_canonical = SOME v’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [SF SFY_ss])
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

Theorem data_inv_insert_instrs_LocValue[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) r l.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = SOME r ∧
    lookup r s.locals = SOME (Loc l 0) ⇒
    data_inv (data with instrs_mem :=
                insert listCmp [48; l] r data.instrs_mem) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def, lookup_insert_listCmp] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                             lookup v data.to_canonical = SOME v ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀r v. lookup r data.to_latest = SOME v ⇒ _ ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [AllCaseEqs()] \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) data.to_canonical ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀x v. ALOOKUP data.gets_mem x = SOME v ⇒
                             lookup v data.to_canonical = SOME v’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.loads_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op a ofs v. _ ⇒ lookup a data.to_canonical = SOME a’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [SF SFY_ss])
  \\ rpt gen_tac \\ strip_tac \\ gvs [instToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

(* Generic correctness of add_to_data_aux, with the family-specific content
   as premises: a hit's holder carries the computed value, and (for the odd
   destination of a miss) inserting the new fact preserves the invariant.
   The destination is freshly invalidated at every call site. *)
Theorem add_to_data_aux_correct:
  ∀data (s:('a,'c,'ffi) wordSem$state) r i p w data' p'.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = NONE ∧
    add_to_data_aux data r i p = (data', p') ∧
    evaluate (p, s) = (NONE, set_var r w s) ∧
    (∀v. balanced_map$lookup listCmp i data.instrs_mem = SOME v ⇒
         get_var v s = SOME w) ∧
    (¬EVEN r ⇒
       data_inv ((data with to_canonical := insert r r data.to_canonical)
                 with instrs_mem :=
                   insert listCmp i r
                     (data with to_canonical :=
                        insert r r data.to_canonical).instrs_mem)
                (set_var r w s)) ⇒
    evaluate (p', s) = (NONE, set_var r w s) ∧
    data_inv data' (set_var r w s)
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [add_to_data_aux_def, AllCaseEqs()]
  >- gvs [data_inv_set_var]
  >- (fs []
      \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
      \\ qmatch_asmsub_abbrev_tac ‘data_inv D2 (set_var r w s)’
      \\ ‘DD = D2 with to_latest := insert r r D2.to_latest’ by
           (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule data_inv_insert_to_latest
      \\ unabbrev_all_tac \\ simp [domain_lookup, lookup_insert])
  >- (‘get_var (lookup_any r' data.to_latest r') s = SOME w’ by
        (gvs [lookup_any_def] \\ Cases_on ‘lookup r' data.to_latest’ \\ gvs []
         \\ qpat_x_assum ‘data_inv data _’ mp_tac
         \\ rw [data_inv_def, sem_inv_def]
         \\ res_tac \\ gvs [])
      \\ gvs [evaluate_Move1, data_inv_set_var])
  \\ ‘get_var (lookup_any r' data.to_latest r') s = SOME w’ by
       (gvs [lookup_any_def] \\ Cases_on ‘lookup r' data.to_latest’ \\ gvs []
        \\ qpat_x_assum ‘data_inv data _’ mp_tac
        \\ rw [data_inv_def, sem_inv_def]
        \\ res_tac \\ gvs [])
  \\ ‘lookup r' data.to_canonical = SOME r' ∧ ODD r'’ by
       (qpat_x_assum ‘data_inv data _’ mp_tac \\ rw [data_inv_def, wf_data_def]
        \\ res_tac \\ gvs [])
  \\ ‘r' ≠ r’ by (strip_tac \\ gvs [])
  \\ simp [evaluate_Move1]
  \\ ‘data_inv (data with to_canonical := insert r r' data.to_canonical)
               (set_var r w s)’ by
       (irule data_inv_insert_to_canonical
        \\ gvs [data_inv_set_var, lookup_insert, ODD_EVEN, get_var_set_var])
  \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
  \\ ‘DD = (data with to_canonical := insert r r' data.to_canonical)
            with to_latest :=
              insert r' r ((data with to_canonical :=
                              insert r r' data.to_canonical).to_latest)’ by
       (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_insert_to_latest
  \\ simp [domain_lookup, lookup_insert]
  \\ gvs [get_var_set_var, lookup_any_def] \\ gvs [AllCaseEqs(), get_var_def]
QED

(* A canonical representative is itself canonical (by idempotence) or an
   untracked register mapped to itself by the next registration. *)
Theorem canonicalRegs_self_or_fresh[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) x.
    data_inv data s ⇒
    sptree$lookup (canonicalRegs data x) data.to_canonical =
      SOME (canonicalRegs data x) ∨
    sptree$lookup (canonicalRegs data x) data.to_canonical = NONE
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [canonicalRegs_def, lookup_any_def]
  \\ Cases_on ‘lookup x data.to_canonical’ \\ gvs []
  \\ qpat_x_assum ‘data_inv data _’ mp_tac \\ rw [data_inv_def, wf_data_def]
  \\ res_tac \\ gvs []
QED

(* The avoiding variant only differs when the canonical representative is
   the (freshly invalidated) destination, which forces the argument itself
   to be that untracked destination. *)
Theorem canonicalRegs'_self_or_fresh[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) r1 x.
    data_inv data s ∧ sptree$lookup r1 data.to_canonical = NONE ⇒
    sptree$lookup (canonicalRegs' r1 data x) data.to_canonical =
      SOME (canonicalRegs' r1 data x) ∨
    sptree$lookup (canonicalRegs' r1 data x) data.to_canonical = NONE
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [canonicalRegs'_def, canonicalRegs_def, lookup_any_def]
  \\ Cases_on ‘lookup x data.to_canonical’ \\ gvs []
  \\ qpat_x_assum ‘data_inv data _’ mp_tac \\ rw [data_inv_def, wf_data_def]
  \\ res_tac \\ gvs []
  \\ rw [] \\ gvs []
QED

Theorem can_mem_arith_ODD_reads[local]:
  ∀a. can_mem_arith a ⇒ EVERY ODD (arithReads a)
Proof
  Cases \\ gvs [can_mem_arith_def, arithReads_def]
  \\ Cases_on ‘r’ \\ gvs [can_mem_arith_def, arithReads_def]
QED

(* The four instantiations of add_to_data_aux_correct, one per call site. *)
Theorem add_to_data_Const_correct:
  ∀data (s:('a,'c,'ffi) wordSem$state) r (w:'a word) data' p'.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = NONE ∧
    add_to_data data r (Const r w) (Const r w) = (data', p') ⇒
    evaluate (p', s) = (NONE, set_var r (Word w) s) ∧
    data_inv data' (set_var r (Word w) s)
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [add_to_data_def]
  \\ qspecl_then [‘data’, ‘s’, ‘r’, ‘instToNumList (Const r w)’,
                  ‘Inst (Const r w)’, ‘Word w’, ‘data'’, ‘p'’]
       mp_tac add_to_data_aux_correct
  \\ impl_tac
  >- (gvs [] \\ rpt conj_tac
      >- simp [evaluate_def, inst_def, assign_def, word_exp_def]
      >- (rpt strip_tac
          \\ qpat_x_assum ‘data_inv data _’ mp_tac
          \\ rw [data_inv_def, sem_inv_def]
          \\ res_tac \\ gvs [get_var_def])
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
      \\ ‘DD = (data with to_canonical := insert r r data.to_canonical)
                with instrs_mem :=
                  insert listCmp (instToNumList (Const r w)) r
                    ((data with to_canonical :=
                        insert r r data.to_canonical).instrs_mem)’ by
           (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule data_inv_insert_instrs_Const
      \\ simp [lookup_insert, set_var_def]
      \\ irule data_inv_insert_to_canonical
      \\ gvs [lookup_insert, ODD_EVEN])
  \\ simp []
QED

Theorem add_to_data_LocValue_correct:
  ∀data (s:('a,'c,'ffi) wordSem$state) r l data' p'.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = NONE ∧
    l ∈ domain s.code ∧
    add_to_data_aux data r [48; l] (LocValue r l) = (data', p') ⇒
    evaluate (p', s) = (NONE, set_var r (Loc l 0) s) ∧
    data_inv data' (set_var r (Loc l 0) s)
Proof
  rpt gen_tac \\ strip_tac
  \\ qspecl_then [‘data’, ‘s’, ‘r’, ‘[48; l]’, ‘LocValue r l’, ‘Loc l 0’,
                  ‘data'’, ‘p'’] mp_tac add_to_data_aux_correct
  \\ impl_tac
  >- (gvs [] \\ rpt conj_tac
      >- simp [evaluate_def]
      >- (rpt strip_tac
          \\ qpat_x_assum ‘data_inv data _’ mp_tac
          \\ rw [data_inv_def, sem_inv_def]
          \\ res_tac \\ gvs [get_var_def])
      \\ strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
      \\ ‘DD = (data with to_canonical := insert r r data.to_canonical)
                with instrs_mem :=
                  insert listCmp [48; l] r
                    ((data with to_canonical :=
                        insert r r data.to_canonical).instrs_mem)’ by
           (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule data_inv_insert_instrs_LocValue
      \\ simp [lookup_insert, set_var_def]
      \\ irule data_inv_insert_to_canonical
      \\ gvs [lookup_insert, ODD_EVEN])
  \\ simp []
QED

Theorem add_to_data_OpCurrHeap_correct:
  ∀data (s:('a,'c,'ffi) wordSem$state) b r1 r2 r2' w data' p'.
    data_inv data s ∧
    sptree$lookup r1 data.to_canonical = NONE ∧
    r2' = canonicalRegs' r1 data r2 ∧
    ¬EVEN r2 ∧ r2 ≠ r1 ∧
    word_exp s (Op b [Var r2; Lookup CurrHeap]) = SOME w ∧
    add_to_data_aux (register_read data r2') r1 (OpCurrHeapToNumList b r2')
      (OpCurrHeap b r1 r2) = (data', p') ⇒
    evaluate (p', s) = (NONE, set_var r1 w s) ∧
    data_inv data' (set_var r1 w s)
Proof
  rpt gen_tac \\ strip_tac
  \\ ‘ODD r2' ∧ r2' ≠ r1 ∧
      lookup r2' (register_read data r2').to_canonical = SOME r2' ∧
      lookup r1 (register_read data r2').to_canonical = NONE’ by
     (qpat_x_assum ‘data_inv data _’ mp_tac \\ rw [data_inv_def, wf_data_def]
      \\ gvs [lookup_register_read, canonicalRegs'_def, canonicalRegs_def,
              lookup_any_def]
      \\ Cases_on ‘lookup r2 data.to_canonical’ \\ gvs [ODD_EVEN]
      \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
  \\ qspecl_then [‘register_read data r2'’, ‘s’, ‘r1’,
                  ‘OpCurrHeapToNumList b r2'’, ‘OpCurrHeap b r1 r2’, ‘w’,
                  ‘data'’, ‘p'’] mp_tac add_to_data_aux_correct
  \\ impl_tac
  >- (gvs [data_inv_register_read] \\ rpt conj_tac
      >- simp [evaluate_def]
      >- (rpt strip_tac
          \\ ‘lookup (canonicalRegs' r1 data r2) s.locals =
              lookup r2 s.locals’ by (rw [canonicalRegs'_def] \\ gvs [])
          \\ qpat_x_assum ‘data_inv data _’ mp_tac
          \\ rw [data_inv_def, sem_inv_def]
          \\ res_tac
          \\ gvs [word_exp_def, the_words_def, get_var_def, AllCaseEqs()])
      >- (strip_tac
          \\ ‘data_inv (register_read data (canonicalRegs' r1 data r2))
                (set_var r1 w s)’
               by simp [data_inv_register_read, data_inv_set_var]
          \\ ‘data_inv (register_read data (canonicalRegs' r1 data r2) with
                          to_canonical :=
                            insert r1 r1
                              (register_read data
                                 (canonicalRegs' r1 data r2)).to_canonical)
                       (set_var r1 w s)’ by
               (irule data_inv_insert_to_canonical
                \\ gvs [lookup_insert, ODD_EVEN])
          \\ ‘lookup (canonicalRegs' r1 data r2) s.locals =
              lookup r2 s.locals’ by (rw [canonicalRegs'_def] \\ gvs [])
          \\ qspecl_then [‘register_read data (canonicalRegs' r1 data r2) with
                             to_canonical :=
                               insert r1 r1
                                 (register_read data
                                    (canonicalRegs' r1 data r2)).to_canonical’,
                          ‘set_var r1 w s’, ‘r1’, ‘b’,
                          ‘canonicalRegs' r1 data r2’,
                          ‘w’] mp_tac data_inv_insert_instrs_OpCurrHeap
          \\ impl_tac
          >- (simp [lookup_insert, get_var_set_var]
              \\ gvs [word_exp_def, the_words_def, set_var_def, lookup_insert,
                      AllCaseEqs()]
              \\ gvs [get_var_def, lookup_insert])
          \\ strip_tac \\ gvs []))
  \\ simp []
QED

Theorem add_to_data_Arith_correct:
  ∀data (s:('a,'c,'ffi) wordSem$state) a a' r w data' p'.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = NONE ∧
    a' = canonicalArith data a ∧
    can_mem_arith a' ∧ ¬MEM r (arithReads a') ∧
    r = firstRegOfArith a ∧
    evaluate (Inst (Arith a), s) = (NONE, set_var r w s) ∧
    add_to_data (register_reads data (arithReads a')) r (Arith a') (Arith a)
      = (data', p') ⇒
    evaluate (p', s) = (NONE, set_var r w s) ∧
    data_inv data' (set_var r w s)
Proof
  rpt gen_tac \\ strip_tac \\ gvs [add_to_data_def]
  \\ ‘evaluate (Inst (Arith (canonicalArith data a)), s) =
      (NONE, set_var (firstRegOfArith a) w s)’ by gvs [evaluate_def]
  \\ ‘EVERY (λx. lookup x data.to_canonical = SOME x ∨
                 lookup x data.to_canonical = NONE)
       (arithReads (canonicalArith data a))’ by
     (Cases_on ‘a’
      \\ gvs [canonicalArith_def, arithReads_def, can_mem_arith_def,
              canonicalImmReg'_def, firstRegOfArith_def]
      >- (Cases_on ‘r’ \\ gvs [canonicalImmReg'_def, arithReads_def]
          \\ metis_tac [canonicalRegs_self_or_fresh,
                        canonicalRegs'_self_or_fresh])
      >- (Cases_on ‘r’ \\ gvs [canonicalImmReg'_def, arithReads_def]
          \\ metis_tac [canonicalRegs_self_or_fresh,
                        canonicalRegs'_self_or_fresh])
      \\ gvs [arithReads_def]
      \\ metis_tac [canonicalRegs_self_or_fresh, canonicalRegs'_self_or_fresh])
  \\ ‘EVERY (λx. lookup x (register_reads data
                   (arithReads (canonicalArith data a))).to_canonical = SOME x)
       (arithReads (canonicalArith data a))’ by
     (drule can_mem_arith_ODD_reads
      \\ gvs [EVERY_MEM, lookup_register_reads] \\ rpt strip_tac
      \\ res_tac \\ gvs [ODD_EVEN] \\ rw [] \\ gvs [])
  \\ ‘lookup (firstRegOfArith a)
        (register_reads data
           (arithReads (canonicalArith data a))).to_canonical = NONE’ by
     (rw [lookup_register_reads] \\ gvs [])
  \\ qspecl_then [‘register_reads data (arithReads (canonicalArith data a))’,
                  ‘s’, ‘firstRegOfArith a’,
                  ‘instToNumList (Arith (canonicalArith data a))’,
                  ‘Inst (Arith a)’, ‘w’, ‘data'’, ‘p'’]
       mp_tac add_to_data_aux_correct
  \\ impl_tac
  >- (gvs [data_inv_register_reads] \\ rpt conj_tac
      >- (rpt strip_tac
          \\ qpat_x_assum ‘data_inv data _’
               (strip_assume_tac o REWRITE_RULE [data_inv_def, sem_inv_def])
          \\ qpat_x_assum
               ‘∀a2 v2. _ ⇒ ∃w2. get_var _ _ = SOME _ ∧ evaluate _ = _’ drule
          \\ strip_tac
          \\ gvs [set_var_def, state_component_equality, insert_eq])
      \\ strip_tac
      \\ qspecl_then [‘canonicalArith data a’, ‘firstRegOfArith a’, ‘w’, ‘w’,
                      ‘s’] mp_tac evaluate_arith_set_var
      \\ impl_tac >- simp []
      \\ strip_tac
      \\ ‘evaluate (Inst (Arith (canonicalArith data a)),
                    set_var (firstRegOfArith a) w s) =
          (NONE, set_var (firstRegOfArith a) w
                   (set_var (firstRegOfArith a) w s))’ by gvs []
      \\ ‘data_inv (register_reads data (arithReads (canonicalArith data a)))
            (set_var (firstRegOfArith a) w s)’
           by simp [data_inv_register_reads, data_inv_set_var]
      \\ ‘data_inv
            (register_reads data (arithReads (canonicalArith data a)) with
               to_canonical :=
                 insert (firstRegOfArith a) (firstRegOfArith a)
                   (register_reads data
                      (arithReads (canonicalArith data a))).to_canonical)
            (set_var (firstRegOfArith a) w s)’ by
           (irule data_inv_insert_to_canonical \\ gvs [lookup_insert, ODD_EVEN])
      \\ qspecl_then
           [‘register_reads data (arithReads (canonicalArith data a)) with
               to_canonical :=
                 insert (firstRegOfArith a) (firstRegOfArith a)
                   (register_reads data
                      (arithReads (canonicalArith data a))).to_canonical’,
            ‘set_var (firstRegOfArith a) w s’, ‘firstRegOfArith a’,
            ‘canonicalArith data a’, ‘w’]
           mp_tac data_inv_insert_instrs_Arith
      \\ impl_tac
      >- (gvs [lookup_insert, get_var_set_var]
          \\ gvs [in_names_set_def, EVERY_MEM, lookup_insert]
          \\ rpt strip_tac \\ res_tac \\ rw [] \\ gvs [])
      \\ strip_tac \\ gvs [])
  \\ simp []
QED

(* Storing a new load fact (the loads_mem sibling of the F-family): the
   holder and the address must be self-mapped, and the fact's ∀-destination
   evaluation equation must hold. *)
Theorem data_inv_insert_loads[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) r op a (ofs:'a word) w.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = SOME r ∧
    sptree$lookup a data.to_canonical = SOME a ∧
    ¬is_store op ∧
    get_var r s = SOME w ∧
    (∀r'. evaluate (Inst (Mem op r' (Addr a ofs)), s) = (NONE, set_var r' w s)) ⇒
    data_inv (data with loads_mem :=
                insert listCmp (loadToNumList op a ofs) r data.loads_mem) s
Proof
  rpt strip_tac
  \\ gvs [data_inv_def]
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘sem_inv _ _’ (strip_assume_tac o REWRITE_RULE [sem_inv_def])
  \\ simp [wf_data_def, sem_inv_def, lookup_insert_listCmp] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [AllCaseEqs()] \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [loadToNumList_def, AllCaseEqs()]
      \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  \\ rpt gen_tac \\ strip_tac \\ gvs [loadToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs [SF SFY_ss]
QED

(* Generic correctness of add_to_load_aux — the loads_mem mirror of
   add_to_data_aux_correct, with the same premise structure. *)
Theorem add_to_load_aux_correct:
  ∀data (s:('a,'c,'ffi) wordSem$state) r i p w data' p'.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = NONE ∧
    add_to_load_aux data r i p = (data', p') ∧
    evaluate (p, s) = (NONE, set_var r w s) ∧
    (∀v. balanced_map$lookup listCmp i data.loads_mem = SOME v ⇒
         get_var v s = SOME w) ∧
    (¬EVEN r ⇒
       data_inv ((data with to_canonical := insert r r data.to_canonical)
                 with loads_mem :=
                   insert listCmp i r
                     (data with to_canonical :=
                        insert r r data.to_canonical).loads_mem)
                (set_var r w s)) ⇒
    evaluate (p', s) = (NONE, set_var r w s) ∧
    data_inv data' (set_var r w s)
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [add_to_load_aux_def, AllCaseEqs()]
  >- gvs [data_inv_set_var]
  >- (fs []
      \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
      \\ qmatch_asmsub_abbrev_tac ‘data_inv D2 (set_var r w s)’
      \\ ‘DD = D2 with to_latest := insert r r D2.to_latest’ by
           (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule data_inv_insert_to_latest
      \\ unabbrev_all_tac \\ simp [domain_lookup, lookup_insert])
  >- (‘get_var (lookup_any r' data.to_latest r') s = SOME w’ by
        (gvs [lookup_any_def] \\ Cases_on ‘lookup r' data.to_latest’ \\ gvs []
         \\ qpat_x_assum ‘data_inv data _’ mp_tac
         \\ rw [data_inv_def, sem_inv_def]
         \\ res_tac \\ gvs [])
      \\ gvs [evaluate_Move1, data_inv_set_var])
  \\ ‘get_var (lookup_any r' data.to_latest r') s = SOME w’ by
       (gvs [lookup_any_def] \\ Cases_on ‘lookup r' data.to_latest’ \\ gvs []
        \\ qpat_x_assum ‘data_inv data _’ mp_tac
        \\ rw [data_inv_def, sem_inv_def]
        \\ res_tac \\ gvs [])
  \\ ‘lookup r' data.to_canonical = SOME r' ∧ ODD r'’ by
       (qpat_x_assum ‘data_inv data _’ mp_tac \\ rw [data_inv_def, wf_data_def]
        \\ res_tac \\ gvs [])
  \\ ‘r' ≠ r’ by (strip_tac \\ gvs [])
  \\ simp [evaluate_Move1]
  \\ ‘data_inv (data with to_canonical := insert r r' data.to_canonical)
               (set_var r w s)’ by
       (irule data_inv_insert_to_canonical
        \\ gvs [data_inv_set_var, lookup_insert, ODD_EVEN, get_var_set_var])
  \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
  \\ ‘DD = (data with to_canonical := insert r r' data.to_canonical)
            with to_latest :=
              insert r' r ((data with to_canonical :=
                              insert r r' data.to_canonical).to_latest)’ by
       (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_insert_to_latest
  \\ simp [domain_lookup, lookup_insert]
  \\ gvs [get_var_set_var, lookup_any_def] \\ gvs [AllCaseEqs(), get_var_def]
QED

(* The instantiation of add_to_load_aux_correct at the word_cseInst Mem-arm
   call site. *)
Theorem add_to_load_correct:
  ∀data (s:('a,'c,'ffi) wordSem$state) op r a a' (ofs:'a word) w data' p'.
    data_inv data s ∧
    sptree$lookup r data.to_canonical = NONE ∧
    a' = canonicalRegs' r data a ∧
    ¬is_store op ∧ ¬EVEN r ∧ ¬EVEN a ∧ a ≠ r ∧
    evaluate (Inst (Mem op r (Addr a ofs)), s) = (NONE, set_var r w s) ∧
    add_to_load_aux (register_read data a') r (loadToNumList op a' ofs)
      (Inst (Mem op r (Addr a ofs))) = (data', p') ⇒
    evaluate (p', s) = (NONE, set_var r w s) ∧
    data_inv data' (set_var r w s)
Proof
  rpt gen_tac \\ strip_tac
  \\ ‘ODD a' ∧ a' ≠ r ∧
      lookup a' (register_read data a').to_canonical = SOME a' ∧
      lookup r (register_read data a').to_canonical = NONE’ by
     (qpat_x_assum ‘data_inv data _’ mp_tac \\ rw [data_inv_def, wf_data_def]
      \\ gvs [lookup_register_read, canonicalRegs'_def, canonicalRegs_def,
              lookup_any_def]
      \\ Cases_on ‘lookup a data.to_canonical’ \\ gvs [ODD_EVEN]
      \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
  \\ ‘lookup a' s.locals = lookup a s.locals’ by
       (gvs [] \\ rw [canonicalRegs'_def] \\ gvs [])
  \\ ‘evaluate (Inst (Mem op r (Addr a' ofs)), s) = (NONE, set_var r w s)’ by
       (qspecl_then [‘op’,‘r’,‘a’,‘a'’,‘ofs’,‘w’,‘s’] mp_tac
          evaluate_load_change_addr \\ gvs [])
  \\ ‘∀r2. evaluate (Inst (Mem op r2 (Addr a' ofs)), s) =
           (NONE, set_var r2 w s)’ by
       (gen_tac
        \\ qspecl_then [‘op’,‘r’,‘a'’,‘ofs’,‘w’,‘s’,‘r2’] mp_tac
             evaluate_load_any_dest \\ gvs [])
  \\ qspecl_then [‘register_read data a'’, ‘s’, ‘r’, ‘loadToNumList op a' ofs’,
                  ‘Inst (Mem op r (Addr a ofs))’, ‘w’, ‘data'’, ‘p'’]
       mp_tac add_to_load_aux_correct
  \\ impl_tac
  >- (gvs [data_inv_register_read] \\ rpt conj_tac
      >- (rpt strip_tac
          \\ qpat_x_assum ‘data_inv data _’
               (strip_assume_tac o REWRITE_RULE [data_inv_def, sem_inv_def])
          \\ qpat_x_assum ‘∀op2 a2 ofs2 v2. _ ∧ _ ⇒ ∃w2. _’ drule_all
          \\ strip_tac
          \\ first_x_assum (qspec_then ‘r’ assume_tac)
          \\ gvs [set_var_def, state_component_equality, insert_eq])
      \\ ‘data_inv (register_read data (canonicalRegs' r data a))
            (set_var r w s)’
           by simp [data_inv_register_read, data_inv_set_var]
      \\ ‘data_inv (register_read data (canonicalRegs' r data a) with
                      to_canonical :=
                        insert r r
                          (register_read data
                             (canonicalRegs' r data a)).to_canonical)
                   (set_var r w s)’ by
           (irule data_inv_insert_to_canonical \\ gvs [lookup_insert, ODD_EVEN])
      \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
      \\ ‘DD = (register_read data (canonicalRegs' r data a) with
                  to_canonical :=
                    insert r r
                      (register_read data
                         (canonicalRegs' r data a)).to_canonical)
                with loads_mem :=
                  insert listCmp
                    (loadToNumList op (canonicalRegs' r data a) ofs) r
                    ((register_read data (canonicalRegs' r data a) with
                        to_canonical :=
                          insert r r
                            (register_read data
                               (canonicalRegs' r data a)).to_canonical).
                       loads_mem)’ by (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule data_inv_insert_loads
      \\ gvs [lookup_insert, get_var_set_var, evaluate_load_set_var])
  \\ simp []
QED

Theorem MAP_FST_lemma[local]:
  ∀moves. MAP FST (MAP (λ(a,b). (a,canonicalRegs data b)) moves) = MAP FST moves
Proof
  Induct \\ gvs []
  \\ gen_tac \\ Cases_on ‘h’ \\ gvs []
QED

Theorem MAP_SND_lemma[local]:
  ∀moves x.
    get_vars (MAP SND moves) s = SOME x ∧ data_inv data s ⇒
    get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s = SOME x
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  \\ Cases_on ‘h’ \\ gvs [get_vars_def]
  \\ Cases_on ‘get_var r s’ \\ gvs []
  \\ Cases_on ‘get_vars (MAP SND moves) s’ \\ gvs []
QED

Theorem lookup_map_insert0:
  ∀xs r. lookup r (map_insert xs m) =
         case ALOOKUP xs r of NONE => lookup r m | SOME r' => SOME r'
Proof
  Induct
  >- gvs [map_insert_def, ALOOKUP_def]
  \\ rpt gen_tac
  \\ Cases_on ‘h’ \\ gvs [map_insert_def, lookup_insert]
  \\ Cases_on ‘r=q’ \\ gvs []
QED

Theorem get_set_vars_lemma:
  ∀xs xs' x y s. ¬MEM x xs ∧ ¬MEM y xs ⇒
                 get_var x s = get_var y s ⇒
                 get_var x (set_vars xs xs' s) = get_var y (set_vars xs xs' s)
Proof
  Induct
  >- rw [set_vars_def, alist_insert_def]
  \\ rpt strip_tac
  \\ Cases_on ‘xs'’
  >- rw [set_vars_def, alist_insert_def]
  \\ gvs [set_vars_def, alist_insert_def, get_var_def, lookup_insert]
QED

Theorem get_set_vars_not_in[local]:
  ∀rs vs r s. ¬MEM r rs ⇒ get_var r (set_vars rs vs s) = get_var r s
Proof
  Induct \\ gvs [set_vars_def]
  >- gvs [alist_insert_def, get_var_def]
  \\ rpt strip_tac
  \\ gvs [get_var_def]
  \\ Cases_on ‘vs’ \\ gvs [alist_insert_def, lookup_insert]
QED

Theorem MEM_FST_reduc:
  ∀moves r p_2. MEM (r,p_2) moves ⇒ MEM r (MAP FST moves)
Proof
  Induct \\ gvs []
  \\ rpt strip_tac
  >- (Cases_on ‘h’ \\ gvs [])
  \\ first_x_assum drule \\ rw []
QED

Theorem get_set_vars_in[local]:
  ∀moves r p_2 x s.
    MEM (r,p_2) moves ⇒
    ALL_DISTINCT (MAP FST moves) ⇒
    get_vars (MAP SND moves) s = SOME x ⇒
    get_var r (set_vars (MAP FST moves) x s) = get_var p_2 s
Proof
  Induct \\ gvs [set_vars_def]
  \\ rpt strip_tac
  >- (Cases_on ‘x’ \\ gvs [alist_insert_def, get_vars_def, AllCaseEqs()]
      \\ gvs [get_var_def, lookup_insert])
  \\ gvs [get_vars_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ gvs [alist_insert_def, get_var_def]
  \\ Cases_on ‘h’ \\ gvs [lookup_insert]
  \\ drule MEM_FST_reduc \\ strip_tac
  \\ Cases_on ‘r=q’ \\ gvs []
QED

Theorem get_set_vars_in_2[local]:
  ∀moves r p_2 x' x data s.
    MEM (r,p_2) moves ⇒
    ALL_DISTINCT (MAP FST moves) ⇒
    lookup p_2 data.to_canonical = SOME x' ⇒
    get_vars (MAP SND (MAP (λ(a,b). (a,canonicalRegs data b)) moves)) s = SOME x ⇒
    get_var r (set_vars (MAP FST moves) x s) = get_var x' s
Proof
  Induct \\ gvs [set_vars_def]
  \\ rpt strip_tac
  >- (Cases_on ‘x’ \\ gvs [alist_insert_def, get_vars_def, AllCaseEqs()]
      \\ gvs [get_var_def, lookup_insert, canonicalRegs_def, lookup_any_def])
  \\ gvs [get_vars_def, AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac
  \\ gvs [alist_insert_def, get_var_def]
  \\ Cases_on ‘h’ \\ gvs [lookup_insert]
  \\ drule MEM_FST_reduc \\ strip_tac
  \\ Cases_on ‘r=q’ \\ gvs [canonicalRegs_def, lookup_any_def]
QED

Theorem lookup_set_vars_not_in[local]:
  ∀moves v data c x.
    ¬MEM v (MAP FST moves) ⇒
    lookup v s.locals = SOME (Word c) ⇒
    lookup v (set_vars (MAP FST moves) x s).locals = SOME (Word c)
Proof
  Induct \\ gvs [set_vars_def]
  >- gvs [alist_insert_def, get_var_def]
  \\ rpt strip_tac
  \\ gvs [get_var_def]
  \\ Cases_on ‘x’ \\ gvs [alist_insert_def, lookup_insert]
QED

Theorem list_insert_insert[local]:
  ∀l n an. list_insert l (insert n () an) = insert n () (list_insert l an)
Proof
  Induct \\ gvs [list_insert_def]
  \\ rpt gen_tac
  \\ Cases_on ‘h=n’ \\ gvs []
  \\ qspecl_then [‘h’, ‘n’, ‘()’, ‘()’, ‘list_insert l an’] assume_tac insert_insert
  \\ gvs []
QED

(* Field-explicit corollaries of the two extension lemmas, in the shape the
   map_insert induction produces. *)
Theorem data_inv_insert_canonical_pair[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) x y tc tl.
    data_inv (data with <|to_canonical := tc; to_latest := tl|>) s ∧
    sptree$lookup x tc = NONE ∧
    sptree$lookup y (insert x y tc) = SOME y ∧
    ODD x ∧ ODD y ∧
    get_var x s = get_var y s ⇒
    data_inv (data with <|to_canonical := insert x y tc; to_latest := tl|>) s
Proof
  rpt strip_tac
  \\ qmatch_asmsub_abbrev_tac ‘data_inv D2 s’
  \\ ‘data with <|to_canonical := insert x y tc; to_latest := tl|> =
      D2 with to_canonical := insert x y D2.to_canonical’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_insert_to_canonical
  \\ unabbrev_all_tac \\ gvs [lookup_insert]
QED

(* One recorded register equivalence (fresh destination, already-canonical
   source) on top of arbitrary to_canonical/to_latest contents. *)
Theorem data_inv_insert_pair[local]:
  ∀data (s:('a,'c,'ffi) wordSem$state) x y tc tl.
    data_inv (data with <|to_canonical := tc; to_latest := tl|>) s ∧
    sptree$lookup x tc = NONE ∧ sptree$lookup y tc = SOME y ∧
    ODD x ∧ ODD y ∧ get_var x s = get_var y s ⇒
    data_inv (data with <|to_canonical := insert x y tc;
                          to_latest := insert y x tl|>) s
Proof
  rpt strip_tac
  \\ ‘y ≠ x’ by (strip_tac \\ gvs [])
  \\ qmatch_asmsub_abbrev_tac ‘data_inv D2 s’
  \\ ‘data with <|to_canonical := insert x y tc; to_latest := insert y x tl|> =
      (D2 with to_canonical := insert x y D2.to_canonical)
        with to_latest :=
          insert y x
            ((D2 with to_canonical := insert x y D2.to_canonical).to_latest)’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_insert_to_latest
  \\ simp [Abbr ‘D2’, domain_lookup, lookup_insert]
  \\ irule data_inv_insert_canonical_pair
  \\ gvs [lookup_insert]
QED

(* Recording a list of register equivalences (fresh destination, canonical
   source) pair by pair: the Move case's knowledge update. *)
Theorem data_inv_move_pairs[local]:
  ∀ps data (s:('a,'c,'ffi) wordSem$state).
    data_inv data s ∧
    ALL_DISTINCT (MAP FST ps) ∧
    EVERY (λ(x,y). sptree$lookup x data.to_canonical = NONE ∧
                   sptree$lookup y data.to_canonical = SOME y ∧
                   ODD x ∧ get_var x s = get_var y s) ps ⇒
    data_inv (data with
                <|to_canonical := map_insert ps data.to_canonical;
                  to_latest := map_insert (MAP (λ(a,b). (b,a)) ps)
                                 data.to_latest|>) s
Proof
  Induct
  >- (rw [map_insert_def]
      \\ ‘data with <|to_canonical := data.to_canonical;
                      to_latest := data.to_latest|> = data’
           by simp [word_cseTheory.knowledge_component_equality]
      \\ gvs [])
  \\ namedCases_on ‘h’ ["x y"] \\ rpt strip_tac \\ gvs [map_insert_def]
  \\ ‘data_inv (data with
        <|to_canonical := map_insert ps data.to_canonical;
          to_latest := map_insert (MAP (λ(a,b). (b,a)) ps) data.to_latest|>) s’
       by (first_x_assum irule \\ gvs [])
  \\ ‘ODD y’ by
       (qpat_x_assum ‘data_inv data _’ mp_tac \\ rw [data_inv_def, wf_data_def]
        \\ res_tac \\ gvs [])
  \\ ‘ALOOKUP ps x = NONE ∧ ALOOKUP ps y = NONE’ by
       (rw [ALOOKUP_NONE] \\ strip_tac
        \\ gvs [MEM_MAP, EXISTS_PROD, EVERY_MEM]
        \\ first_x_assum drule \\ gvs [])
  \\ irule data_inv_insert_pair
  \\ gvs [lookup_map_insert0]
QED

(* The Move case: registering the sources and recording the surviving
   destination/canonical-source equivalences preserves the invariant across
   the parallel assignment. *)
Theorem canonicalMoveRegs_lemma:
  ∀data (s:('a,'c,'ffi) wordSem$state) rs vs.
    data_inv data s ∧
    ALL_DISTINCT (MAP FST rs) ∧
    get_vars (MAP SND rs) s = SOME vs ⇒
    data_inv (canonicalMoveRegs data rs) (set_vars (MAP FST rs) vs s)
Proof
  rw [canonicalMoveRegs_def]
  \\ ‘data.to_latest = (register_reads data (MAP SND rs)).to_latest’ by simp []
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_move_pairs
  \\ rpt conj_tac
  >- (gvs [MAP_FST_lemma] \\ irule ALL_DISTINCT_MAP_FST_FILTER \\ simp [])
  >- (gvs [EVERY_MEM, MEM_MAP, MEM_FILTER, EXISTS_PROD, PULL_EXISTS]
      \\ rpt strip_tac
      >- (first_x_assum drule \\ rw [keep_data_def, IS_NONE_EQ_NONE])
      >- (‘MEM p_2 (MAP SND rs)’ by (gvs [MEM_MAP, EXISTS_PROD] \\ metis_tac [])
          \\ ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                    lookup v data.to_canonical = SOME v’ by
               (qpat_x_assum ‘data_inv data _’ mp_tac
                \\ rw [data_inv_def, wf_data_def] \\ res_tac \\ gvs [])
          \\ gvs [canonicalRegs_def, lookup_any_def, lookup_register_reads]
          \\ Cases_on ‘lookup p_2 data.to_canonical’ \\ gvs []
          \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
      >- gvs [ODD_EVEN]
      \\ ‘MEM p_2 (MAP SND rs)’ by (gvs [MEM_MAP, EXISTS_PROD] \\ metis_tac [])
      \\ ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                lookup v data.to_canonical = SOME v’ by
           (qpat_x_assum ‘data_inv data _’ mp_tac
            \\ rw [data_inv_def, wf_data_def] \\ res_tac \\ gvs [])
      \\ ‘lookup (canonicalRegs (register_reads data (MAP SND rs)) p_2)
            (register_reads data (MAP SND rs)).to_canonical =
          SOME (canonicalRegs (register_reads data (MAP SND rs)) p_2)’ by
           (gvs [canonicalRegs_def, lookup_any_def, lookup_register_reads]
            \\ Cases_on ‘lookup p_2 data.to_canonical’ \\ gvs []
            \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
      \\ ‘¬MEM (canonicalRegs (register_reads data (MAP SND rs)) p_2)
            (MAP FST rs)’ by
           (strip_tac \\ gvs [MEM_MAP, EXISTS_PROD]
            \\ first_x_assum drule
            \\ rw [keep_data_def, IS_NONE_EQ_NONE] \\ gvs [])
      \\ ‘data_inv (register_reads data (MAP SND rs)) s’
           by simp [data_inv_register_reads]
      \\ drule_all get_set_vars_in \\ strip_tac
      \\ ‘get_var (canonicalRegs (register_reads data (MAP SND rs)) p_2)
            (set_vars (MAP FST rs) vs s) =
          get_var (canonicalRegs (register_reads data (MAP SND rs)) p_2) s’ by
           (irule get_set_vars_not_in \\ simp [])
      \\ gvs [])
  \\ ‘EVERY (λx. lookup x
        (register_reads data (MAP SND rs)).to_canonical = NONE)
       (MAP FST rs)’ by gvs [EVERY_MEM, keep_data_def, IS_NONE_EQ_NONE]
  \\ gvs [data_inv_set_vars, data_inv_register_reads]
QED

(* ------------------------------------------------------------------------
   THE MAIN CORRECTNESS THEOREM

   One suspend/Resume ladder over the evaluate induction: the dispatcher
   names every case, Break and Continue close inline (word_cse keeps the
   data and the program unchanged), and each Resume block below carries one
   case's proof.
   ------------------------------------------------------------------------ *)

Theorem if_eq_rw[local,simp]:
  (if x = y then y else x) = x
Proof
  rw []
QED

(* The stored evaluation equations are insensitive to the clock and termdep
   fields — clones of the memory transports for the Tick/MustTerminate
   cases. *)
Theorem evaluate_arith_clock[local]:
  ∀a w s c td.
    can_mem_arith a ⇒
    (evaluate (Inst (Arith a), s with <|clock := c; termdep := td|>) =
       (NONE,
        set_var (firstRegOfArith a) w s with <|clock := c; termdep := td|>) ⇔
     evaluate (Inst (Arith a), s) = (NONE, set_var (firstRegOfArith a) w s))
Proof
  rpt strip_tac \\ Cases_on ‘a’
  \\ gvs [can_mem_arith_def, firstRegOfArith_def, evaluate_def, inst_def,
          assign_def, word_exp_def, the_words_def, get_vars_def, get_var_def,
          set_var_def, AllCaseEqs()]
  \\ gvs [PULL_EXISTS]
QED

Theorem evaluate_load_clock[local]:
  ∀op r a ofs w s c td.
    ¬is_store op ⇒
    (evaluate (Inst (Mem op r (Addr a ofs)),
               s with <|clock := c; termdep := td|>) =
       (NONE, set_var r w s with <|clock := c; termdep := td|>) ⇔
     evaluate (Inst (Mem op r (Addr a ofs)), s) = (NONE, set_var r w s))
Proof
  rpt strip_tac
  \\ Cases_on ‘op’ \\ gvs [is_store_def]
  \\ gvs [evaluate_def, inst_def, word_exp_def, the_words_def, set_var_def,
          mem_load_def, get_var_def]
  >- (Cases_on ‘lookup a s.locals’ \\ gvs []
      \\ Cases_on ‘x’ \\ gvs [wordLangTheory.word_op_def]
      \\ IF_CASES_TAC \\ gvs [state_component_equality, insert_eq])
  \\ Cases_on ‘lookup a s.locals’ \\ gvs []
  \\ Cases_on ‘x’ \\ gvs [wordLangTheory.word_op_def]
  \\ TOP_CASE_TAC
  \\ gvs [AllCaseEqs()] \\ gvs [state_component_equality, insert_eq]
QED

(* data_inv is insensitive to the clock and termdep fields. *)
Theorem data_inv_clock:
  ∀data s c td.
    data_inv data s ⇒ data_inv data (s with <|clock := c; termdep := td|>)
Proof
  rpt strip_tac
  \\ gvs [data_inv_def, wf_data_def, sem_inv_def]
  \\ rpt strip_tac \\ res_tac \\ gvs [get_var_def]
  >- (‘can_mem_arith a’ by res_tac \\ gvs [evaluate_arith_clock])
  \\ gvs [evaluate_load_clock]
QED

(* ------------------------------------------------------------------------
   SYNTACTIC WF PRESERVATION

   word_cse preserves the state-free half of the invariant with no
   semantic premises.  The If case of comp_correct needs wf_data of the
   NOT-taken branch's output, which no evaluation establishes; these
   lemmas mirror the data_inv-level update lemmas above restricted to
   their wf_data content, and culminate in word_cse_wf_data.
   ------------------------------------------------------------------------ *)

Theorem wf_data_empty[simp]:
  wf_data (:'a) empty_data
Proof
  gvs [wf_data_def, empty_data_def, lookup_def]
QED

(* Wiping the load facts only removes obligations. *)
Theorem wf_data_loads_wipe:
  ∀data. wf_data (:'a) data ⇒ wf_data (:'a) (data with loads_mem := empty)
Proof
  rpt strip_tac \\ gvs [wf_data_def]
  \\ rpt strip_tac \\ res_tac \\ gvs []
QED

Theorem wf_data_invalidate:
  ∀data r. wf_data (:'a) data ⇒ wf_data (:'a) (invalidate_data data r)
Proof
  rw [invalidate_data_def]
QED

Theorem wf_data_invalidate_regs:
  ∀rs data. wf_data (:'a) data ⇒ wf_data (:'a) (invalidate_regs data rs)
Proof
  Induct \\ rw [invalidate_regs_def]
  \\ first_x_assum irule \\ irule wf_data_invalidate \\ gvs []
QED

(* wf sibling of data_inv_insert_to_canonical. *)
Theorem wf_data_insert_to_canonical:
  ∀data x y.
    wf_data (:'a) data ∧
    sptree$lookup x data.to_canonical = NONE ∧
    sptree$lookup y (insert x y data.to_canonical) = SOME y ∧
    ODD x ∧ ODD y ⇒
    wf_data (:'a) (data with to_canonical := insert x y data.to_canonical)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac \\ pop_assum mp_tac \\ simp [lookup_insert]
      \\ rw []
      \\ gvs [lookup_insert]
      \\ qpat_x_assum ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                             lookup v data.to_canonical = SOME v ∧ _’ drule
      \\ strip_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac \\ res_tac \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.instrs_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) data.to_canonical ∧ _’ drule
      \\ strip_tac
      \\ gvs [in_names_set_def, EVERY_MEM]
      \\ rpt strip_tac
      \\ first_x_assum drule \\ strip_tac
      \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀op src v. _ ⇒ lookup src data.to_canonical = SOME src’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀x v. ALOOKUP data.gets_mem x = SOME v ⇒
                             lookup v data.to_canonical = SOME v’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  >- (rpt gen_tac \\ strip_tac
      \\ qpat_x_assum ‘∀k v. lookup listCmp k data.loads_mem = SOME v ⇒ _’ drule
      \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs [])
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum ‘∀op a ofs v. _ ⇒ lookup a data.to_canonical = SOME a’ drule
  \\ strip_tac \\ gvs [lookup_insert] \\ rw [] \\ gvs []
QED

(* wf sibling of data_inv_insert_to_latest. *)
Theorem wf_data_insert_to_latest:
  ∀data x y.
    wf_data (:'a) data ∧
    x ∈ domain data.to_canonical ∧ y ∈ domain data.to_canonical ⇒
    wf_data (:'a) (data with to_latest := insert x y data.to_latest)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def]
  \\ rpt strip_tac \\ gvs [lookup_insert, AllCaseEqs()] \\ res_tac \\ gvs []
QED

Theorem wf_data_register_read:
  ∀data r. wf_data (:'a) data ⇒ wf_data (:'a) (register_read data r)
Proof
  rw [register_read_def, keep_data_def]
  \\ irule wf_data_insert_to_canonical
  \\ gvs [lookup_insert, ODD_EVEN]
QED

Theorem wf_data_register_reads:
  ∀rs data. wf_data (:'a) data ⇒ wf_data (:'a) (register_reads data rs)
Proof
  Induct \\ rw [register_reads_def]
  \\ first_x_assum irule \\ gvs [wf_data_register_read]
QED

(* wf siblings of the per-family fact-insert lemmas (F1-F5): a new fact
   with a self-mapped holder (and, per family, self-mapped reads) keeps the
   data well-formed. *)
Theorem wf_data_insert_instrs_Const[local]:
  ∀data r n (w:'a word).
    wf_data (:'a) data ∧
    sptree$lookup r data.to_canonical = SOME r ⇒
    wf_data (:'a) (data with instrs_mem :=
                     insert listCmp (instToNumList (Const n w)) r
                       data.instrs_mem)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def, lookup_insert_listCmp]
  \\ rpt strip_tac
  \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

Theorem wf_data_insert_instrs_Arith[local]:
  ∀data r (a:'a arith).
    wf_data (:'a) data ∧
    sptree$lookup r data.to_canonical = SOME r ∧
    can_mem_arith a ∧ in_names_set a data.to_canonical ⇒
    wf_data (:'a) (data with instrs_mem :=
                     insert listCmp (instToNumList (Arith a)) r
                       data.instrs_mem)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ ‘∀a2:'a arith. arithToNumList a2 = arithToNumList a ⇒
        in_names_set a2 data.to_canonical ∧ can_mem_arith a2’ by
       (rpt gen_tac \\ strip_tac
        \\ qspecl_then [‘a’, ‘a2’] mp_tac arith_keys_eq
        \\ impl_tac >- gvs []
        \\ strip_tac \\ gvs [in_names_set_def])
  \\ simp [wf_data_def, lookup_insert_listCmp]
  \\ rpt strip_tac
  \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

Theorem wf_data_insert_instrs_OpCurrHeap[local]:
  ∀data r op src.
    wf_data (:'a) data ∧
    sptree$lookup r data.to_canonical = SOME r ∧
    sptree$lookup src data.to_canonical = SOME src ⇒
    wf_data (:'a) (data with instrs_mem :=
                     insert listCmp (OpCurrHeapToNumList op src) r
                       data.instrs_mem)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def, lookup_insert_listCmp]
  \\ rpt strip_tac
  \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

Theorem wf_data_insert_instrs_LocValue[local]:
  ∀data r l.
    wf_data (:'a) data ∧
    sptree$lookup r data.to_canonical = SOME r ⇒
    wf_data (:'a) (data with instrs_mem :=
                     insert listCmp [48; l] r data.instrs_mem)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def, lookup_insert_listCmp]
  \\ rpt strip_tac
  \\ gvs [instToNumList_def, OpCurrHeapToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

Theorem wf_data_insert_loads[local]:
  ∀data r op a (ofs:'a word).
    wf_data (:'a) data ∧
    sptree$lookup r data.to_canonical = SOME r ∧
    sptree$lookup a data.to_canonical = SOME a ⇒
    wf_data (:'a) (data with loads_mem :=
                     insert listCmp (loadToNumList op a ofs) r
                       data.loads_mem)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def, lookup_insert_listCmp]
  \\ rpt strip_tac
  \\ gvs [loadToNumList_def, AllCaseEqs()]
  \\ res_tac \\ gvs []
QED

(* wf mirror of add_to_data_aux_correct: the hit case re-points the
   destination at the stored (self-mapped) holder; the family-specific
   miss case arrives as a premise in the same nested-with form. *)
Theorem wf_add_to_data_aux:
  ∀data r i (p:'a prog) data' p'.
    wf_data (:'a) data ∧
    sptree$lookup r data.to_canonical = NONE ∧
    add_to_data_aux data r i p = (data', p') ∧
    (¬EVEN r ⇒
       wf_data (:'a)
         ((data with to_canonical := insert r r data.to_canonical)
          with instrs_mem :=
            insert listCmp i r
              (data with to_canonical :=
                 insert r r data.to_canonical).instrs_mem)) ⇒
    wf_data (:'a) data'
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [add_to_data_aux_def, AllCaseEqs()]
  >- (fs []
      \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
      \\ ‘DD = ((data with to_canonical := insert r r data.to_canonical)
                with instrs_mem :=
                  insert listCmp i r
                    (data with to_canonical :=
                       insert r r data.to_canonical).instrs_mem)
               with to_latest :=
                 insert r r
                   (((data with to_canonical := insert r r data.to_canonical)
                     with instrs_mem :=
                       insert listCmp i r
                         (data with to_canonical :=
                            insert r r data.to_canonical).instrs_mem).
                      to_latest)’ by (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule wf_data_insert_to_latest
      \\ simp [domain_lookup, lookup_insert])
  \\ ‘lookup r' data.to_canonical = SOME r' ∧ ODD r'’ by
       (qpat_x_assum ‘wf_data _ data’ mp_tac \\ rw [wf_data_def]
        \\ res_tac \\ gvs [])
  \\ ‘r' ≠ r’ by (strip_tac \\ gvs [])
  \\ ‘wf_data (:'a) (data with to_canonical := insert r r' data.to_canonical)’
       by (irule wf_data_insert_to_canonical \\ gvs [lookup_insert, ODD_EVEN])
  \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
  \\ ‘DD = (data with to_canonical := insert r r' data.to_canonical)
            with to_latest :=
              insert r' r ((data with to_canonical :=
                              insert r r' data.to_canonical).to_latest)’ by
       (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule wf_data_insert_to_latest
  \\ simp [domain_lookup, lookup_insert]
QED

Theorem wf_add_to_load_aux:
  ∀data r i (p:'a prog) data' p'.
    wf_data (:'a) data ∧
    sptree$lookup r data.to_canonical = NONE ∧
    add_to_load_aux data r i p = (data', p') ∧
    (¬EVEN r ⇒
       wf_data (:'a)
         ((data with to_canonical := insert r r data.to_canonical)
          with loads_mem :=
            insert listCmp i r
              (data with to_canonical :=
                 insert r r data.to_canonical).loads_mem)) ⇒
    wf_data (:'a) data'
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [add_to_load_aux_def, AllCaseEqs()]
  >- (fs []
      \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
      \\ ‘DD = ((data with to_canonical := insert r r data.to_canonical)
                with loads_mem :=
                  insert listCmp i r
                    (data with to_canonical :=
                       insert r r data.to_canonical).loads_mem)
               with to_latest :=
                 insert r r
                   (((data with to_canonical := insert r r data.to_canonical)
                     with loads_mem :=
                       insert listCmp i r
                         (data with to_canonical :=
                            insert r r data.to_canonical).loads_mem).
                      to_latest)’ by (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule wf_data_insert_to_latest
      \\ simp [domain_lookup, lookup_insert])
  \\ ‘lookup r' data.to_canonical = SOME r' ∧ ODD r'’ by
       (qpat_x_assum ‘wf_data _ data’ mp_tac \\ rw [wf_data_def]
        \\ res_tac \\ gvs [])
  \\ ‘r' ≠ r’ by (strip_tac \\ gvs [])
  \\ ‘wf_data (:'a) (data with to_canonical := insert r r' data.to_canonical)’
       by (irule wf_data_insert_to_canonical \\ gvs [lookup_insert, ODD_EVEN])
  \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
  \\ ‘DD = (data with to_canonical := insert r r' data.to_canonical)
            with to_latest :=
              insert r' r ((data with to_canonical :=
                              insert r r' data.to_canonical).to_latest)’ by
       (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule wf_data_insert_to_latest
  \\ simp [domain_lookup, lookup_insert]
QED

(* wf siblings of the Get/Set knowledge-update lemmas. *)
Theorem wf_data_insert_gets[local]:
  ∀data name v.
    wf_data (:'a) data ∧
    sptree$lookup v data.to_canonical = NONE ∧ ODD v ∧
    ALOOKUP data.gets_mem name = NONE ⇒
    wf_data (:'a) (data with <|to_canonical := insert v v data.to_canonical;
                               to_latest := insert v v data.to_latest;
                               gets_mem := (name,v)::data.gets_mem|>)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def, ALOOKUP_NONE]
  \\ rpt strip_tac
  \\ gvs [lookup_insert, in_names_set_def, EVERY_MEM, AllCaseEqs(),
          ALOOKUP_NONE]
  \\ res_tac \\ gvs [] \\ rw [] \\ gvs []
QED

Theorem wf_data_filter_gets[local]:
  ∀data x.
    wf_data (:'a) data ⇒
    wf_data (:'a) (data with gets_mem :=
                     FILTER (λ(m,n). m ≠ x) data.gets_mem)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def, ALOOKUP_FILTER, ALL_DISTINCT_MAP_FST_FILTER]
  \\ rpt strip_tac \\ res_tac \\ gvs []
QED

Theorem wf_data_cons_gets[local]:
  ∀data x h.
    wf_data (:'a) data ∧
    ALOOKUP data.gets_mem x = NONE ∧
    sptree$lookup h data.to_canonical = SOME h ⇒
    wf_data (:'a) (data with gets_mem := (x,h)::data.gets_mem)
Proof
  rpt strip_tac
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def, ALOOKUP_NONE]
  \\ rpt strip_tac \\ gvs [AllCaseEqs(), ALOOKUP_NONE] \\ res_tac \\ gvs []
QED

Theorem wf_data_reinsert_canonical[local]:
  ∀data v.
    wf_data (:'a) data ∧ ODD v ⇒
    wf_data (:'a) (data with to_canonical :=
                     insert v (lookup_any v data.to_canonical v)
                       data.to_canonical)
Proof
  rpt strip_tac \\ gvs [lookup_any_def]
  \\ Cases_on ‘lookup v data.to_canonical’ \\ gvs []
  >- (irule wf_data_insert_to_canonical \\ gvs [lookup_insert])
  \\ ‘insert v x data.to_canonical = data.to_canonical’ by
       gvs [insert_unchanged]
  \\ ‘data with to_canonical := data.to_canonical = data’ by
       simp [word_cseTheory.knowledge_component_equality]
  \\ simp []
QED

(* wf sibling of data_inv_merge_l/_r: well-formedness of both arms is
   enough for the equality-intersection merge. *)
Theorem wf_data_merge:
  ∀d1 d2.
    wf_data (:'a) d1 ∧ wf_data (:'a) d2 ⇒ wf_data (:'a) (merge_data d1 d2)
Proof
  rpt strip_tac \\ gvs [merge_data_def]
  \\ qpat_x_assum ‘wf_data _ d1’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ qpat_x_assum ‘wf_data _ d2’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def] \\ rpt conj_tac
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()] \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac \\ gvs [lookup_bm_inter_eq]
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) d1.to_canonical ∧ _’ drule
      \\ qpat_x_assum ‘∀a2 v2. _ ⇒ in_names_set (a2:'a arith) d2.to_canonical ∧ _’ drule
      \\ rpt strip_tac
      \\ gvs [in_names_set_def, EVERY_MEM]
      \\ rpt strip_tac
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ imp_res_tac ALOOKUP_MEM
      \\ gvs [MEM_FILTER]
      \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
      \\ gvs [sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (irule ALL_DISTINCT_MAP_FST_FILTER \\ simp [])
  >- (irule invariant_bm_inter_eq \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  >- (rpt gen_tac \\ strip_tac
      \\ gvs [lookup_bm_inter_eq, sptreeTheory.lookup_inter_eq, AllCaseEqs()]
      \\ res_tac \\ simp [])
  \\ irule invariant_bm_inter_eq \\ simp []
QED

(* wf sibling of data_inv_move_pairs — WITHOUT the ALL_DISTINCT premise:
   word_cse runs on syntactically arbitrary Moves, including ones with
   duplicate destinations that the semantics would reject, so the proof is
   a direct characterization via lookup_map_insert0 rather than the
   pair-by-pair induction.  Sources are self-mapped, hence never
   destinations, so their entries survive every insert. *)
Theorem wf_data_move_pairs[local]:
  ∀ps data.
    wf_data (:'a) data ∧
    EVERY (λ(x,y). sptree$lookup x data.to_canonical = NONE ∧
                   sptree$lookup y data.to_canonical = SOME y ∧
                   ODD x ∧ ODD y) ps ⇒
    wf_data (:'a)
      (data with <|to_canonical := map_insert ps data.to_canonical;
                   to_latest := map_insert (MAP (λ(a,b). (b,a)) ps)
                                  data.to_latest|>)
Proof
  rpt strip_tac
  \\ ‘∀x y. ALOOKUP ps x = SOME y ⇒
            lookup x data.to_canonical = NONE ∧
            lookup y data.to_canonical = SOME y ∧ ODD x ∧ ODD y’ by
       (rpt gen_tac \\ strip_tac \\ imp_res_tac ALOOKUP_MEM
        \\ gvs [EVERY_MEM] \\ first_x_assum drule \\ simp [])
  \\ ‘∀v. lookup v data.to_canonical = SOME v ⇒ ALOOKUP ps v = NONE’ by
       (gen_tac \\ strip_tac \\ Cases_on ‘ALOOKUP ps v’ \\ gvs []
        \\ first_x_assum drule \\ strip_tac \\ gvs [])
  \\ ‘∀x y. ALOOKUP (MAP (λ(a,b). (b,a)) ps) x = SOME y ⇒
            lookup x data.to_canonical = SOME x ∧
            ALOOKUP ps y ≠ NONE’ by
       (rpt gen_tac \\ strip_tac \\ imp_res_tac ALOOKUP_MEM
        \\ gvs [MEM_MAP, EXISTS_PROD, EVERY_MEM, ALOOKUP_NONE]
        \\ res_tac \\ gvs [SF SFY_ss]
        \\ qpat_x_assum ‘∀e. MEM e ps ⇒ _’ drule \\ simp [])
  \\ qpat_x_assum ‘wf_data _ _’ (strip_assume_tac o REWRITE_RULE [wf_data_def])
  \\ simp [wf_data_def]
  \\ rpt strip_tac
  \\ gvs [lookup_map_insert0, AllCaseEqs(), in_names_set_def, EVERY_MEM,
          domain_lookup]
  \\ res_tac \\ gvs [lookup_map_insert0, AllCaseEqs(), SF SFY_ss]
  >- (Cases_on ‘ALOOKUP ps r’ \\ gvs [])
  >- (Cases_on ‘ALOOKUP ps v’ \\ gvs [])
  \\ Cases_on ‘ALOOKUP ps v’ \\ gvs [] \\ res_tac
QED

(* wf sibling of canonicalMoveRegs_lemma's knowledge-update content. *)
Theorem wf_canonicalMoveRegs:
  ∀data rs. wf_data (:'a) data ⇒ wf_data (:'a) (canonicalMoveRegs data rs)
Proof
  rw [canonicalMoveRegs_def]
  \\ ‘data.to_latest = (register_reads data (MAP SND rs)).to_latest’ by simp []
  \\ pop_assum SUBST1_TAC
  \\ irule wf_data_move_pairs
  \\ rpt conj_tac
  >- (gvs [EVERY_MEM, MEM_MAP, MEM_FILTER, EXISTS_PROD, PULL_EXISTS]
      \\ rpt strip_tac
      >- (first_x_assum drule \\ rw [keep_data_def, IS_NONE_EQ_NONE])
      >- (‘MEM p_2 (MAP SND rs)’ by (gvs [MEM_MAP, EXISTS_PROD] \\ metis_tac [])
          \\ ‘∀r v. lookup r data.to_canonical = SOME v ⇒
                    lookup v data.to_canonical = SOME v’ by
               (qpat_x_assum ‘wf_data _ data’ mp_tac
                \\ rw [wf_data_def] \\ res_tac \\ gvs [])
          \\ gvs [canonicalRegs_def, lookup_any_def, lookup_register_reads]
          \\ Cases_on ‘lookup p_2 data.to_canonical’ \\ gvs []
          \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
      >- gvs [ODD_EVEN]
      \\ ‘MEM p_2 (MAP SND rs)’ by (gvs [MEM_MAP, EXISTS_PROD] \\ metis_tac [])
      \\ ‘∀r v. lookup r data.to_canonical = SOME v ⇒ ODD v’ by
           (qpat_x_assum ‘wf_data _ data’ mp_tac
            \\ rw [wf_data_def] \\ res_tac \\ gvs [])
      \\ gvs [canonicalRegs_def, lookup_any_def, lookup_register_reads]
      \\ Cases_on ‘lookup p_2 data.to_canonical’ \\ gvs [ODD_EVEN]
      \\ res_tac \\ gvs [] \\ rw [] \\ gvs [ODD_EVEN])
  \\ gvs [wf_data_register_reads]
QED

(* wf-premise variants of the self-or-fresh lemmas (the data_inv versions
   above only use the wf half of their premise). *)
Theorem canonicalRegs_self_or_fresh_wf[local]:
  ∀data x.
    wf_data (:'a) data ⇒
    sptree$lookup (canonicalRegs data x) data.to_canonical =
      SOME (canonicalRegs data x) ∨
    sptree$lookup (canonicalRegs data x) data.to_canonical = NONE
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [canonicalRegs_def, lookup_any_def]
  \\ Cases_on ‘lookup x data.to_canonical’ \\ gvs []
  \\ qpat_x_assum ‘wf_data _ _’ mp_tac \\ rw [wf_data_def]
  \\ res_tac \\ gvs []
QED

Theorem canonicalRegs'_self_or_fresh_wf[local]:
  ∀data r1 x.
    wf_data (:'a) data ∧ sptree$lookup r1 data.to_canonical = NONE ⇒
    sptree$lookup (canonicalRegs' r1 data x) data.to_canonical =
      SOME (canonicalRegs' r1 data x) ∨
    sptree$lookup (canonicalRegs' r1 data x) data.to_canonical = NONE
Proof
  rpt gen_tac \\ strip_tac
  \\ gvs [canonicalRegs'_def, canonicalRegs_def, lookup_any_def]
  \\ Cases_on ‘lookup x data.to_canonical’ \\ gvs []
  \\ qpat_x_assum ‘wf_data _ _’ mp_tac \\ rw [wf_data_def]
  \\ res_tac \\ gvs []
  \\ rw [] \\ gvs []
QED

Theorem in_names_set_insert_self[local]:
  ∀a tc x. in_names_set a tc ⇒ in_names_set a (insert x x tc)
Proof
  rw [in_names_set_def, EVERY_MEM] \\ res_tac \\ rw [lookup_insert]
QED

Theorem in_names_set_register_reads[local]:
  ∀a data.
    EVERY ODD (arithReads a) ∧
    EVERY (λw. sptree$lookup w data.to_canonical = NONE ∨
               sptree$lookup w data.to_canonical = SOME w) (arithReads a) ⇒
    in_names_set a (register_reads data (arithReads a)).to_canonical
Proof
  rw [in_names_set_def, EVERY_MEM]
  \\ res_tac \\ gvs [lookup_register_reads, ODD_EVEN]
  \\ rw [] \\ gvs []
QED

(* The reads of a canonicalized storable arith are canonical registers:
   tracked-and-self-mapped, or untracked (registered as self-maps next). *)
Theorem canonicalArith_reads_self_or_fresh[local]:
  ∀data (a:'a arith).
    wf_data (:'a) data ∧
    can_mem_arith (canonicalArith data a) ∧
    sptree$lookup (firstRegOfArith a) data.to_canonical = NONE ⇒
    EVERY (λw. sptree$lookup w data.to_canonical = NONE ∨
               sptree$lookup w data.to_canonical = SOME w)
          (arithReads (canonicalArith data a))
Proof
  rpt strip_tac
  \\ namedCases_on ‘a’
       ["b r1 r2 ri", "sh r1 r2 ri", "r1 r2 r3", "r1 r2 r3 r4",
        "r1 r2 r3 r4 r5", "r1 r2 r3 r4", "r1 r2 r3 r4", "r1 r2 r3 r4"]
  \\ gvs [canonicalArith_def, can_mem_arith_def, firstRegOfArith_def]
  >- (namedCases_on ‘ri’ ["r3", "imm"]
      \\ gvs [canonicalImmReg'_def, can_mem_arith_def, arithReads_def]
      \\ metis_tac [canonicalRegs_self_or_fresh_wf,
                    canonicalRegs'_self_or_fresh_wf])
  >- (namedCases_on ‘ri’ ["r3", "imm"]
      \\ gvs [canonicalImmReg'_def, can_mem_arith_def, arithReads_def]
      \\ metis_tac [canonicalRegs_self_or_fresh_wf,
                    canonicalRegs'_self_or_fresh_wf])
  \\ gvs [arithReads_def]
  \\ metis_tac [canonicalRegs_self_or_fresh_wf,
                canonicalRegs'_self_or_fresh_wf]
QED

(* The main syntactic preservation theorem, one Resume per constructor
   whose case updates the knowledge (the catch-all closes the identity and
   full-reset cases).  Consumed by the If case of comp_correct for the
   not-taken branch. *)
Theorem word_cse_wf_data:
  ∀p data.
    wf_data (:'a) data ⇒ wf_data (:'a) (FST (word_cse data (p:'a prog)))
Proof
  Induct
  \\ simp []
  \\ rpt gen_tac \\ strip_tac
  >~ [`Move`] >- suspend "Move"
  >~ [`Inst`] >- suspend "Inst"
  >~ [`Get`] >- suspend "Get"
  >~ [`wordLang$Set`] >- suspend "Set"
  >~ [`Store`] >- suspend "Store"
  >~ [`MustTerminate`] >- suspend "MustTerminate"
  >~ [`wordLang$Seq`] >- suspend "Seq"
  >~ [`wordLang$If`] >- suspend "If"
  >~ [`OpCurrHeap`] >- suspend "OpCurrHeap"
  >~ [`wordLang$LocValue`] >- suspend "LocValue"
  >~ [`wordLang$StoreConsts`] >- suspend "StoreConsts"
  >~ [`wordLang$ShareInst`] >- suspend "ShareInst"
  >~ [`Loop`] >- suspend "Loop"
  >> gvs [word_cse_def]
QED

Resume word_cse_wf_data[Move]:
  gvs [word_cse_def, wf_canonicalMoveRegs]
QED

Resume word_cse_wf_data[Inst]:
  gvs [word_cse_def]
  \\ Cases_on ‘word_cseInst data i’ \\ gvs []
  \\ namedCases_on ‘i’ ["", "n c", "a", "m n ad", "f"]
  >- ((* Skip *)
      gvs [word_cseInst_def])
  >- ((* Const *)
      gvs [word_cseInst_def, add_to_data_def, AllCaseEqs(),
           wf_data_invalidate]
      \\ ‘wf_data (:'a) (invalidate_data data n) ∧
          lookup n (invalidate_data data n).to_canonical = NONE’ by
           (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
      \\ qpat_x_assum ‘wf_data _ (invalidate_data data n)’
           (mp_then (Pos hd) mp_tac wf_add_to_data_aux)
      \\ disch_then drule
      \\ disch_then drule
      \\ impl_tac
      >- (strip_tac
          \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
          \\ ‘DD = (invalidate_data data n with
                      to_canonical :=
                        insert n n (invalidate_data data n).to_canonical)
                   with instrs_mem :=
                     insert listCmp (instToNumList (Const n c)) n
                       ((invalidate_data data n with
                           to_canonical :=
                             insert n n (invalidate_data data n).to_canonical).
                          instrs_mem)’ by (unabbrev_all_tac \\ simp [])
          \\ pop_assum SUBST1_TAC
          \\ irule wf_data_insert_instrs_Const
          \\ gvs [lookup_insert]
          \\ irule wf_data_insert_to_canonical
          \\ gvs [lookup_insert, ODD_EVEN, wf_data_invalidate])
      \\ simp [])
  >- ((* Arith *)
      gvs [word_cseInst_def]
      \\ ‘wf_data (:'a) (invalidate_regs data (arithWrites a))’ by
           gvs [wf_data_invalidate_regs]
      \\ ‘lookup (firstRegOfArith a)
            (invalidate_regs data (arithWrites a)).to_canonical = NONE’ by
           (irule lookup_invalidate_regs
            \\ Cases_on ‘a’ \\ gvs [arithWrites_def, firstRegOfArith_def])
      \\ qmatch_asmsub_abbrev_tac ‘if GATE then _ else _’
      \\ Cases_on ‘GATE’ \\ gvs [markerTheory.Abbrev_def]
      \\ gvs [add_to_data_def]
      \\ ‘in_names_set
            (canonicalArith (invalidate_regs data (arithWrites a)) a)
            (register_reads (invalidate_regs data (arithWrites a))
               (arithReads
                  (canonicalArith (invalidate_regs data (arithWrites a)) a))).
              to_canonical’ by
           (irule in_names_set_register_reads
            \\ gvs [can_mem_arith_ODD_reads,
                    canonicalArith_reads_self_or_fresh])
      \\ ‘wf_data (:'a)
            (register_reads (invalidate_regs data (arithWrites a))
               (arithReads
                  (canonicalArith (invalidate_regs data (arithWrites a)) a)))’
           by gvs [wf_data_register_reads]
      \\ ‘lookup (firstRegOfArith a)
            (register_reads (invalidate_regs data (arithWrites a))
               (arithReads
                  (canonicalArith (invalidate_regs data (arithWrites a)) a))).
              to_canonical = NONE’ by gvs [lookup_register_reads]
      \\ qpat_x_assum ‘wf_data _ (register_reads _ _)’
           (mp_then (Pos hd) mp_tac wf_add_to_data_aux)
      \\ disch_then drule
      \\ disch_then drule
      \\ impl_tac
      >- (strip_tac
          \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
          \\ ‘DD = (register_reads (invalidate_regs data (arithWrites a))
                      (arithReads
                         (canonicalArith
                            (invalidate_regs data (arithWrites a)) a)) with
                      to_canonical :=
                        insert (firstRegOfArith a) (firstRegOfArith a)
                          (register_reads
                             (invalidate_regs data (arithWrites a))
                             (arithReads
                                (canonicalArith
                                   (invalidate_regs data (arithWrites a)) a))).
                            to_canonical)
                   with instrs_mem :=
                     insert listCmp
                       (instToNumList
                          (Arith
                             (canonicalArith
                                (invalidate_regs data (arithWrites a)) a)))
                       (firstRegOfArith a)
                       ((register_reads (invalidate_regs data (arithWrites a))
                           (arithReads
                              (canonicalArith
                                 (invalidate_regs data (arithWrites a)) a)) with
                           to_canonical :=
                             insert (firstRegOfArith a) (firstRegOfArith a)
                               (register_reads
                                  (invalidate_regs data (arithWrites a))
                                  (arithReads
                                     (canonicalArith
                                        (invalidate_regs data
                                           (arithWrites a)) a))).to_canonical).
                          instrs_mem)’ by (unabbrev_all_tac \\ simp [])
          \\ pop_assum SUBST1_TAC
          \\ irule wf_data_insert_instrs_Arith
          \\ gvs [lookup_insert, in_names_set_insert_self]
          \\ irule wf_data_insert_to_canonical
          \\ gvs [lookup_insert, ODD_EVEN, wf_data_register_reads,
                  wf_data_invalidate_regs])
      \\ simp [])
  >- ((* Mem *)
      namedCases_on ‘ad’ ["ar ofs"]
      \\ gvs [word_cseInst_def]
      \\ Cases_on ‘is_store m’ \\ gvs [wf_data_loads_wipe]
      \\ ‘wf_data (:'a) (invalidate_data data n) ∧
          lookup n (invalidate_data data n).to_canonical = NONE’ by
           (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
      \\ Cases_on ‘EVEN n ∨ EVEN ar ∨ ar = n’ \\ gvs []
      \\ ‘ODD (canonicalRegs' n (invalidate_data data n) ar) ∧
          canonicalRegs' n (invalidate_data data n) ar ≠ n ∧
          lookup (canonicalRegs' n (invalidate_data data n) ar)
            (register_read (invalidate_data data n)
               (canonicalRegs' n (invalidate_data data n) ar)).to_canonical =
          SOME (canonicalRegs' n (invalidate_data data n) ar) ∧
          lookup n
            (register_read (invalidate_data data n)
               (canonicalRegs' n (invalidate_data data n) ar)).to_canonical =
          NONE’ by
           (qpat_x_assum ‘wf_data _ (invalidate_data data n)’ mp_tac
            \\ rw [wf_data_def]
            \\ gvs [lookup_register_read, canonicalRegs'_def,
                    canonicalRegs_def, lookup_any_def]
            \\ Cases_on ‘lookup ar (invalidate_data data n).to_canonical’
            \\ gvs [ODD_EVEN]
            \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
      \\ ‘wf_data (:'a)
            (register_read (invalidate_data data n)
               (canonicalRegs' n (invalidate_data data n) ar))’ by
           gvs [wf_data_register_read]
      \\ qpat_x_assum ‘wf_data _ (register_read _ _)’
           (mp_then (Pos hd) mp_tac wf_add_to_load_aux)
      \\ disch_then drule
      \\ disch_then drule
      \\ impl_tac
      >- (strip_tac
          \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
          \\ ‘DD = (register_read (invalidate_data data n)
                      (canonicalRegs' n (invalidate_data data n) ar) with
                      to_canonical :=
                        insert n n
                          (register_read (invalidate_data data n)
                             (canonicalRegs' n (invalidate_data data n) ar)).
                            to_canonical)
                   with loads_mem :=
                     insert listCmp
                       (loadToNumList m
                          (canonicalRegs' n (invalidate_data data n) ar) ofs) n
                       ((register_read (invalidate_data data n)
                           (canonicalRegs' n (invalidate_data data n) ar) with
                           to_canonical :=
                             insert n n
                               (register_read (invalidate_data data n)
                                  (canonicalRegs' n (invalidate_data data n)
                                     ar)).to_canonical).loads_mem)’
               by (unabbrev_all_tac \\ simp [])
          \\ pop_assum SUBST1_TAC
          \\ irule wf_data_insert_loads
          \\ gvs [lookup_insert]
          \\ irule wf_data_insert_to_canonical
          \\ gvs [lookup_insert, ODD_EVEN, wf_data_register_read,
                  wf_data_invalidate])
      \\ simp [])
  \\ (* FP *)
    gvs [word_cseInst_def, wf_data_invalidate_regs]
QED

Resume word_cse_wf_data[Get]:
  gvs [word_cse_def]
  \\ ‘wf_data (:'a) (invalidate_data data n) ∧
      lookup n (invalidate_data data n).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  \\ namedCases_on ‘ALOOKUP (invalidate_data data n).gets_mem s’ ["", "k"]
  \\ gvs []
  >- (Cases_on ‘EVEN n’ \\ gvs []
      \\ irule wf_data_insert_gets \\ gvs [ODD_EVEN])
  \\ Cases_on ‘EVEN n’ \\ gvs []
  \\ ‘lookup k (invalidate_data data n).to_canonical = SOME k ∧ ODD k’ by
       (qpat_x_assum ‘wf_data _ (invalidate_data data n)’ mp_tac
        \\ rw [wf_data_def] \\ res_tac \\ gvs [])
  \\ ‘k ≠ n’ by (strip_tac \\ gvs [])
  \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
  \\ ‘DD = (invalidate_data data n with to_canonical :=
              insert n k (invalidate_data data n).to_canonical)
            with to_latest :=
              insert k n
                ((invalidate_data data n with to_canonical :=
                    insert n k (invalidate_data data n).to_canonical).
                   to_latest)’ by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule wf_data_insert_to_latest
  \\ simp [domain_lookup, lookup_insert]
  \\ irule wf_data_insert_to_canonical
  \\ gvs [lookup_insert, ODD_EVEN]
QED

Resume word_cse_wf_data[Set]:
  gvs [word_cse_def]
  \\ Cases_on ‘s = CurrHeap’ \\ gvs []
  \\ namedCases_on ‘dest_Var e’ ["", "v"] \\ gvs [wf_data_filter_gets]
  \\ Cases_on ‘EVEN v’ \\ gvs [wf_data_filter_gets]
  \\ ‘lookup (canonicalRegs data v)
        (insert v (lookup_any v data.to_canonical v) data.to_canonical) =
      SOME (canonicalRegs data v)’ by
       (gvs [canonicalRegs_def, lookup_any_def]
        \\ Cases_on ‘lookup v data.to_canonical’ \\ gvs [lookup_insert]
        \\ qpat_x_assum ‘wf_data _ data’ mp_tac
        \\ rw [wf_data_def] \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
  \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
  \\ ‘DD = ((data with to_canonical :=
               insert v (lookup_any v data.to_canonical v) data.to_canonical)
             with gets_mem :=
               FILTER (λ(m,n). m ≠ s)
                 (data with to_canonical :=
                    insert v (lookup_any v data.to_canonical v)
                      data.to_canonical).gets_mem)
            with gets_mem :=
              (s,canonicalRegs data v)::
                ((data with to_canonical :=
                    insert v (lookup_any v data.to_canonical v)
                      data.to_canonical)
                  with gets_mem :=
                    FILTER (λ(m,n). m ≠ s)
                      (data with to_canonical :=
                         insert v (lookup_any v data.to_canonical v)
                           data.to_canonical).gets_mem).gets_mem’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule wf_data_cons_gets
  \\ rpt conj_tac
  >- gvs [ALOOKUP_FILTER]
  >- gvs []
  \\ irule wf_data_filter_gets
  \\ irule wf_data_reinsert_canonical
  \\ gvs [ODD_EVEN]
QED

Resume word_cse_wf_data[Store]:
  gvs [word_cse_def, wf_data_loads_wipe]
QED

Resume word_cse_wf_data[MustTerminate]:
  gvs [word_cse_def] \\ pairarg_tac \\ gvs []
  \\ first_x_assum drule \\ gvs []
QED

Resume word_cse_wf_data[Seq]:
  gvs [word_cse_def]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum drule \\ strip_tac
  \\ last_x_assum drule \\ strip_tac
  \\ gvs []
QED

Resume word_cse_wf_data[If]:
  gvs [word_cse_def]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum drule \\ strip_tac
  \\ first_x_assum (qspec_then ‘data’ mp_tac) \\ impl_tac >- simp []
  \\ strip_tac
  \\ gvs [wf_data_merge]
QED

Resume word_cse_wf_data[OpCurrHeap]:
  gvs [word_cse_def]
  \\ ‘wf_data (:'a) (invalidate_data data n) ∧
      lookup n (invalidate_data data n).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  \\ Cases_on ‘EVEN n0 ∨ n0 = n’ \\ gvs []
  \\ ‘ODD (canonicalRegs' n (invalidate_data data n) n0) ∧
      canonicalRegs' n (invalidate_data data n) n0 ≠ n ∧
      lookup (canonicalRegs' n (invalidate_data data n) n0)
        (register_read (invalidate_data data n)
           (canonicalRegs' n (invalidate_data data n) n0)).to_canonical =
      SOME (canonicalRegs' n (invalidate_data data n) n0) ∧
      lookup n
        (register_read (invalidate_data data n)
           (canonicalRegs' n (invalidate_data data n) n0)).to_canonical =
      NONE’ by
       (qpat_x_assum ‘wf_data _ (invalidate_data data n)’ mp_tac
        \\ rw [wf_data_def]
        \\ gvs [lookup_register_read, canonicalRegs'_def, canonicalRegs_def,
                lookup_any_def]
        \\ Cases_on ‘lookup n0 (invalidate_data data n).to_canonical’
        \\ gvs [ODD_EVEN]
        \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
  \\ ‘wf_data (:'a)
        (register_read (invalidate_data data n)
           (canonicalRegs' n (invalidate_data data n) n0))’ by
       gvs [wf_data_register_read]
  \\ Cases_on ‘add_to_data_aux
                 (register_read (invalidate_data data n)
                    (canonicalRegs' n (invalidate_data data n) n0)) n
                 (OpCurrHeapToNumList b
                    (canonicalRegs' n (invalidate_data data n) n0))
                 (OpCurrHeap b n n0)’ \\ gvs []
  \\ qpat_x_assum ‘wf_data _ (register_read _ _)’
       (mp_then (Pos hd) mp_tac wf_add_to_data_aux)
  \\ disch_then drule
  \\ disch_then drule
  \\ impl_tac
  >- (strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
      \\ ‘DD = (register_read (invalidate_data data n)
                  (canonicalRegs' n (invalidate_data data n) n0) with
                  to_canonical :=
                    insert n n
                      (register_read (invalidate_data data n)
                         (canonicalRegs' n (invalidate_data data n) n0)).
                        to_canonical)
               with instrs_mem :=
                 insert listCmp
                   (OpCurrHeapToNumList b
                      (canonicalRegs' n (invalidate_data data n) n0)) n
                   ((register_read (invalidate_data data n)
                       (canonicalRegs' n (invalidate_data data n) n0) with
                       to_canonical :=
                         insert n n
                           (register_read (invalidate_data data n)
                              (canonicalRegs' n (invalidate_data data n) n0)).
                             to_canonical).instrs_mem)’
           by (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule wf_data_insert_instrs_OpCurrHeap
      \\ gvs [lookup_insert]
      \\ irule wf_data_insert_to_canonical
      \\ gvs [lookup_insert, ODD_EVEN, wf_data_register_read,
              wf_data_invalidate])
  \\ simp []
QED

Resume word_cse_wf_data[LocValue]:
  gvs [word_cse_def]
  \\ ‘wf_data (:'a) (invalidate_data data n) ∧
      lookup n (invalidate_data data n).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  \\ Cases_on ‘add_to_data_aux (invalidate_data data n) n [48; n0]
                 (LocValue n n0)’ \\ gvs []
  \\ qpat_x_assum ‘wf_data _ (invalidate_data data n)’
       (mp_then (Pos hd) mp_tac wf_add_to_data_aux)
  \\ disch_then drule
  \\ disch_then drule
  \\ impl_tac
  >- (strip_tac
      \\ qmatch_goalsub_abbrev_tac ‘wf_data _ DD’
      \\ ‘DD = (invalidate_data data n with
                  to_canonical :=
                    insert n n (invalidate_data data n).to_canonical)
               with instrs_mem :=
                 insert listCmp [48; n0] n
                   ((invalidate_data data n with
                       to_canonical :=
                         insert n n (invalidate_data data n).to_canonical).
                      instrs_mem)’ by (unabbrev_all_tac \\ simp [])
      \\ pop_assum SUBST1_TAC
      \\ irule wf_data_insert_instrs_LocValue
      \\ gvs [lookup_insert]
      \\ irule wf_data_insert_to_canonical
      \\ gvs [lookup_insert, ODD_EVEN, wf_data_invalidate])
  \\ simp []
QED

Resume word_cse_wf_data[StoreConsts]:
  gvs [word_cse_def, wf_data_loads_wipe, wf_data_invalidate_regs]
QED

Resume word_cse_wf_data[ShareInst]:
  gvs [word_cse_def] \\ rw [wf_data_invalidate]
QED

Resume word_cse_wf_data[Loop]:
  simp [Once word_cse_def] \\ pairarg_tac \\ gvs []
QED

Finalise word_cse_wf_data;

Theorem comp_correct:
  ∀v v1 res s' data p' data'.
    evaluate (v,v1) = (res,s') ∧ flat_exp_conventions v ∧ data_inv data v1 ∧
    res ≠ SOME Error ∧ word_cse data v = (data',p') ⇒
    evaluate (p',v1) = (res,s') ∧ (res = NONE ⇒ data_inv data' s')
Proof
  recInduct evaluate_ind
  \\ rpt conj_tac
  >~ [`Skip`] >- suspend "Skip"
  >~ [`Alloc`] >- suspend "Alloc"
  >~ [`Move`] >- suspend "Move"
  >~ [`Inst`] >- suspend "Inst"
  >~ [`Assign`] >- suspend "Assign"
  >~ [`Get`] >- suspend "Get"
  >~ [`wordLang$Set`] >- suspend "Set"
  >~ [`OpCurrHeap`] >- suspend "OpCurrHeap"
  >~ [`Store`] >- suspend "Store"
  >~ [`Tick`] >- suspend "Tick"
  >~ [`MustTerminate`] >- suspend "MustTerminate"
  >~ [`wordLang$Seq`] >- suspend "Seq"
  >~ [`Return`] >- suspend "Return"
  >~ [`wordLang$Raise`] >- suspend "Raise"
  >~ [`wordLang$If`] >- suspend "If"
  >~ [`wordLang$LocValue`] >- suspend "LocValue"
  >~ [`wordLang$Install`] >- suspend "Install"
  >~ [`wordLang$CodeBufferWrite`] >- suspend "CodeBufferWrite"
  >~ [`wordLang$DataBufferWrite`] >- suspend "DataBufferWrite"
  >~ [`wordLang$FFI`] >- suspend "FFI"
  >~ [`wordLang$Call`] >- suspend "Call"
  >~ [`wordLang$StoreConsts`] >- suspend "StoreConsts"
  >~ [`wordLang$ShareInst`] >- suspend "ShareInst"
  >~ [`Break`] >- (gvs[word_cse_def, evaluate_def])
  >~ [`Continue`] >- (gvs[word_cse_def, evaluate_def])
  >~ [`Loop`] >- suspend "Loop"
QED

(* proof of the cases *)

Resume comp_correct[Skip]:
  gvs [word_cse_def, evaluate_def]
QED

Resume comp_correct[Alloc]:
  gvs [word_cse_def]
QED

Resume comp_correct[Move]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ irule canonicalMoveRegs_lemma \\ gvs []
QED

Resume comp_correct[Inst]:
  rpt gen_tac \\ strip_tac
  \\ namedCases_on ‘i’ ["", "n c", "a", "m n ad", "f"]
  >- ((* Skip *)
      gvs [word_cse_def, word_cseInst_def, evaluate_def, inst_def,
           AllCaseEqs()])
  >- ((* Const *)
      gvs [word_cse_def, word_cseInst_def, evaluate_def, inst_def, assign_def,
           word_exp_def, AllCaseEqs()]
      \\ ‘data_inv (invalidate_data data n) s ∧
          lookup n (invalidate_data data n).to_canonical = NONE’ by
           (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
      \\ Cases_on ‘EVEN n’
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def,
              data_inv_set_var]
      \\ Cases_on ‘add_to_data (invalidate_data data n) n (Const n c)
                     (Const n c)’
      \\ gvs []
      \\ drule_all add_to_data_Const_correct \\ gvs [])
  >- ((* Arith *)
      gvs [word_cse_def, word_cseInst_def]
      \\ ‘data_inv (invalidate_regs data (arithWrites a)) s’ by
           gvs [data_inv_invalidate_regs]
      \\ ‘lookup (firstRegOfArith a)
            (invalidate_regs data (arithWrites a)).to_canonical = NONE’ by
           (irule lookup_invalidate_regs
            \\ Cases_on ‘a’ \\ gvs [arithWrites_def, firstRegOfArith_def])
      \\ qmatch_asmsub_abbrev_tac ‘if GATE then _ else _’
      \\ Cases_on ‘GATE’ \\ gvs [markerTheory.Abbrev_def]
      >- (
          namedCases_on ‘a’
            ["b n n0 ri", "sh n n0 ri", "n n0 n1", "n n0 n1 n2",
             "n n0 n1 n2 n3", "n n0 n1 n2", "n n0 n1 n2", "n n0 n1 n2"]
          \\ gvs [canonicalArith_def, can_mem_arith_def, firstRegOfArith_def]
          >- ((* Binop *)
              ‘∃w. res = NONE ∧
                   s' = set_var (firstRegOfArith (Binop b n n0 ri)) w s’ by
                (Cases_on ‘ri’
                 \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def,
                         the_words_def, firstRegOfArith_def, AllCaseEqs()]
                 \\ irule_at Any EQ_REFL)
              \\ gvs [] \\ pairarg_tac \\ gvs []
              \\ qspecl_then [‘invalidate_regs data (arithWrites (Binop b n n0 ri))’,
                              ‘s’, ‘Binop b n n0 ri’,
                              ‘Binop b n
                                 (canonicalRegs' n
                                    (invalidate_regs data
                                       (arithWrites (Binop b n n0 ri))) n0)
                                 (canonicalImmReg' n
                                    (invalidate_regs data
                                       (arithWrites (Binop b n n0 ri))) ri)’,
                              ‘n’, ‘w’, ‘data'’, ‘p’]
                   mp_tac add_to_data_Arith_correct
              \\ impl_tac >- gvs [canonicalArith_def, firstRegOfArith_def]
              \\ gvs [firstRegOfArith_def])
          >- ((* Shift *)
              ‘∃w. res = NONE ∧
                   s' = set_var (firstRegOfArith (Shift sh n n0 ri)) w s’ by
                (Cases_on ‘ri’
                 \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def,
                         the_words_def, firstRegOfArith_def,
                         can_mem_arith_def, canonicalImmReg'_def,
                         AllCaseEqs()]
                 \\ irule_at Any EQ_REFL)
              \\ gvs [] \\ pairarg_tac \\ gvs []
              \\ qspecl_then [‘invalidate_regs data (arithWrites (Shift sh n n0 ri))’,
                              ‘s’, ‘Shift sh n n0 ri’,
                              ‘Shift sh n
                                 (canonicalRegs' n
                                    (invalidate_regs data
                                       (arithWrites (Shift sh n n0 ri))) n0)
                                 (canonicalImmReg' n
                                    (invalidate_regs data
                                       (arithWrites (Shift sh n n0 ri))) ri)’,
                              ‘n’, ‘w’, ‘data'’, ‘p’]
                   mp_tac add_to_data_Arith_correct
              \\ impl_tac >- gvs [canonicalArith_def, firstRegOfArith_def]
              \\ gvs [firstRegOfArith_def])
          \\ (* Div *)
             ‘∃w. res = NONE ∧ s' = set_var (firstRegOfArith (Div n n0 n1)) w s’ by
               (gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def,
                     get_vars_def, get_var_def, firstRegOfArith_def, AllCaseEqs()]
                \\ irule_at Any EQ_REFL)
          \\ gvs [] \\ pairarg_tac \\ gvs []
          \\ qpat_x_assum ‘data_inv (invalidate_regs _ _) _’
               (mp_then (Pos hd) mp_tac add_to_data_Arith_correct)
          \\ disch_then (drule_at (Pos last))
          \\ simp [canonicalArith_def, firstRegOfArith_def, can_mem_arith_def,
                   arithReads_def])
      \\ strip_tac \\ gvs []
      \\ Cases_on ‘a’
      \\ gvs [evaluate_def, inst_def, assign_def, word_exp_def, the_words_def,
              get_vars_def, get_var_def, arithWrites_def, AllCaseEqs(),
              data_inv_set_var, lookup_invalidate_regs]
      \\ pairarg_tac \\ gvs [data_inv_set_var, lookup_invalidate_regs])
  >- ((* Mem *)
      namedCases_on ‘ad’ ["ar ofs"]
      \\ gvs [word_cse_def, word_cseInst_def]
      \\ Cases_on ‘is_store m’ \\ gvs []
      >- ((* store: wipe the load facts, keep the register facts *)
          strip_tac \\ Cases_on ‘m’
          \\ gvs [is_store_def, evaluate_def, inst_def, word_exp_def,
                  the_words_def, mem_store_def, AllCaseEqs(), data_inv_memory])
      \\ (* load *)
      ‘data_inv (invalidate_data data n) s ∧
       lookup n (invalidate_data data n).to_canonical = NONE’ by
        (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
      \\ ‘∃w. res = NONE ∧ s' = set_var n w s’ by
           (Cases_on ‘m’
            \\ gvs [is_store_def, evaluate_def, inst_def, AllCaseEqs()]
            \\ irule_at Any EQ_REFL)
      \\ gvs []
      \\ Cases_on ‘EVEN n ∨ EVEN ar ∨ ar = n’
      \\ gvs [evaluate_def, data_inv_set_var]
      \\ pairarg_tac \\ gvs []
      \\ qpat_x_assum ‘data_inv (invalidate_data _ _) _’
           (mp_then (Pos hd) mp_tac add_to_load_correct)
      \\ disch_then (drule_at (Pos last))
      \\ simp []
      \\ disch_then (qspec_then ‘w’ mp_tac) \\ gvs []
      \\ impl_tac >- gvs [evaluate_def]
      \\ gvs [])
  \\ (* FP *)
    gvs [word_cse_def, word_cseInst_def]
    \\ Cases_on ‘f’
    \\ gvs [evaluate_def, inst_def, fpWrites_def, AllCaseEqs(),
            data_inv_set_var, lookup_invalidate_regs, data_inv_invalidate_regs]
    \\ pairarg_tac \\ gvs [invalidate_regs_def]
QED

Resume comp_correct[Assign]:
  fs [flat_exp_conventions_def]
QED

Resume comp_correct[Get]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs(), invalidate_data_def,
          keep_data_def]
  >- gvs [data_inv_set_var]
  >- (IF_CASES_TAC \\ gvs []
      \\ irule data_inv_insert_gets
      \\ gvs [set_var_def, get_var_def, lookup_insert, get_store_def,
              ODD_EVEN, empty_data_def, SRULE [set_var_def] data_inv_set_var])
  >- (‘get_var k s = SOME x’ by
        (qpat_x_assum ‘data_inv data s’ mp_tac
         \\ rw [data_inv_def, sem_inv_def]
         \\ res_tac \\ gvs [get_store_def])
      \\ ‘get_var (lookup_any k data.to_latest k) s = SOME x’ by
           (gvs [lookup_any_def] \\ Cases_on ‘lookup k data.to_latest’ \\ gvs []
            \\ qpat_x_assum ‘data_inv data _’ mp_tac
            \\ rw [data_inv_def, sem_inv_def]
            \\ res_tac \\ gvs [])
      \\ conj_tac
      >- (qexists_tac ‘[x]’
          \\ gvs [get_vars_def, set_vars_def, alist_insert_def, set_var_def])
      \\ gvs [data_inv_set_var])
  >- gvs [empty_data_def]
  \\ IF_CASES_TAC \\ gvs [empty_data_def]
  \\ ‘get_var k s = SOME x’ by
       (qpat_x_assum ‘data_inv data s’ mp_tac
        \\ rw [data_inv_def, sem_inv_def]
        \\ res_tac \\ gvs [get_store_def])
  \\ ‘lookup k data.to_canonical = SOME k ∧ ODD k’ by
       (qpat_x_assum ‘data_inv data s’ mp_tac
        \\ rw [data_inv_def, wf_data_def]
        \\ res_tac \\ gvs [])
  \\ ‘k ≠ v’ by (strip_tac \\ gvs [])
  \\ ‘get_var (lookup_any k data.to_latest k) s = SOME x’ by
       (gvs [lookup_any_def] \\ Cases_on ‘lookup k data.to_latest’ \\ gvs []
        \\ qpat_x_assum ‘data_inv data _’ mp_tac
        \\ rw [data_inv_def, sem_inv_def]
        \\ res_tac \\ gvs [])
  \\ conj_tac
  >- (qexists_tac ‘[x]’
      \\ gvs [get_vars_def, set_vars_def, alist_insert_def, set_var_def])
  \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
  \\ ‘DD = (data with to_canonical := insert v k data.to_canonical)
             with to_latest :=
               insert k v
                 (data with to_canonical := insert v k data.to_canonical).
                 to_latest’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_insert_to_latest
  \\ rpt conj_tac
  >- gvs [get_var_def, set_var_def, lookup_insert]
  >- gvs [domain_insert, domain_lookup, lookup_insert, SF SFY_ss]
  >- gvs [domain_insert]
  \\ irule data_inv_insert_to_canonical
  \\ gvs [lookup_insert, ODD_EVEN, get_var_def, set_var_def,
          SRULE [set_var_def] data_inv_set_var]
QED

Resume comp_correct[Set]:
  rpt gen_tac \\ strip_tac
  \\ Cases_on ‘exp’ \\ gvs [flat_exp_conventions_def]
  \\ gvs [word_cse_def, evaluate_def, dest_Var_def, word_exp_def, AllCaseEqs()]
  >- (irule data_inv_set_store \\ gvs [ALOOKUP_FILTER, data_inv_filter_gets])
  \\ ‘get_var (canonicalRegs data n) s = SOME w’ by gvs []
  \\ ‘lookup (canonicalRegs data n)
        (insert n (lookup_any n data.to_canonical n) data.to_canonical) =
      SOME (canonicalRegs data n)’ by
       (gvs [canonicalRegs_def, lookup_any_def]
        \\ Cases_on ‘lookup n data.to_canonical’ \\ gvs [lookup_insert]
        \\ qpat_x_assum ‘data_inv data s’ mp_tac
        \\ rw [data_inv_def, wf_data_def] \\ res_tac \\ gvs [] \\ rw [] \\ gvs [])
  \\ qmatch_goalsub_abbrev_tac ‘data_inv DD _’
  \\ ‘DD = ((data with to_canonical :=
               insert n (lookup_any n data.to_canonical n) data.to_canonical)
             with gets_mem :=
               FILTER (λ(m,n'). m ≠ v)
                 (data with to_canonical :=
                    insert n (lookup_any n data.to_canonical n)
                      data.to_canonical).gets_mem)
            with gets_mem :=
              (v,canonicalRegs data n)::
                ((data with to_canonical :=
                    insert n (lookup_any n data.to_canonical n)
                      data.to_canonical)
                  with gets_mem :=
                    FILTER (λ(m,n'). m ≠ v)
                      (data with to_canonical :=
                         insert n (lookup_any n data.to_canonical n)
                           data.to_canonical).gets_mem).gets_mem’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_cons_gets
  \\ rpt conj_tac
  >- gvs [ALOOKUP_FILTER]
  >- gvs []
  >- (qexists_tac ‘w’ \\ gvs [set_store_def, FLOOKUP_UPDATE, get_var_def])
  \\ irule data_inv_set_store \\ gvs [ALOOKUP_FILTER]
  \\ qmatch_goalsub_abbrev_tac ‘data_inv D2 _’
  \\ ‘D2 = (data with to_canonical :=
              insert n (lookup_any n data.to_canonical n) data.to_canonical)
            with gets_mem :=
              FILTER (λ(m,n'). m ≠ v)
                (data with to_canonical :=
                   insert n (lookup_any n data.to_canonical n)
                     data.to_canonical).gets_mem’
       by (unabbrev_all_tac \\ simp [])
  \\ pop_assum SUBST1_TAC
  \\ irule data_inv_filter_gets
  \\ irule data_inv_reinsert_canonical \\ gvs [ODD_EVEN]
QED

Resume comp_correct[OpCurrHeap]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ ‘data_inv (invalidate_data data dst) s ∧
      lookup dst (invalidate_data data dst).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  >- gvs [data_inv_set_var]
  >- gvs [data_inv_set_var]
  \\ qspecl_then [‘invalidate_data data dst’, ‘s’, ‘b’, ‘dst’, ‘src’,
                  ‘canonicalRegs' dst (invalidate_data data dst) src’, ‘w’,
                  ‘data'’, ‘p'’] mp_tac add_to_data_OpCurrHeap_correct
  \\ impl_tac >- gvs []
  \\ gvs []
QED

Resume comp_correct[Store]:
  fs [flat_exp_conventions_def]
QED

Resume comp_correct[Tick]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ drule_then (qspecl_then [‘s.clock - 1’, ‘s.termdep’] assume_tac) data_inv_clock
  \\ ‘s with <|clock := s.clock - 1; termdep := s.termdep|> = dec_clock s’
       by gvs [dec_clock_def, state_component_equality]
  \\ gvs []
QED

Resume comp_correct[MustTerminate]:
  rpt gen_tac
  \\ strip_tac
  \\ rpt gen_tac
  \\ strip_tac
  \\ gs [word_cse_def]
  \\ pairarg_tac \\ gvs [evaluate_def, flat_exp_conventions_def]
  \\ gvs [AllCaseEqs()]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum (drule_at Any)
  \\ Cases_on ‘res'' = SOME TimeOut’ \\ gvs []
  \\ impl_tac
  >- gvs [data_inv_clock]
  \\ rpt (strip_tac \\ gvs [data_inv_clock])
QED

Resume comp_correct[Seq]:
  rpt gen_tac \\
  strip_tac \\
  rpt gen_tac \\
  strip_tac \\
  gvs [word_cse_def, evaluate_def, flat_exp_conventions_def] \\
  rpt (pairarg_tac \\ gvs []) \\
  reverse (gvs [AllCaseEqs(), evaluate_def])
  >- (pairarg_tac \\ gvs [] \\
      first_x_assum drule_all \\ gs []) \\
  pairarg_tac \\ gvs [] \\
  first_x_assum drule_all \\ gs [] \\
  strip_tac \\ gvs [] \\
  first_x_assum drule_all \\
  fs []
QED

Resume comp_correct[Return]:
  fs [word_cse_def, evaluate_def, flat_exp_conventions_def]
  \\ rw []
  \\ gvs [AllCaseEqs()]
QED

Resume comp_correct[Raise]:
  fs [word_cse_def, evaluate_def, flat_exp_conventions_def]
  \\ rw []
  \\ gvs [AllCaseEqs()]
QED

Resume comp_correct[If]:
  rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def]
  \\ pairarg_tac \\ gvs []
  \\ pairarg_tac \\ gvs []
  \\ gvs [evaluate_def, flat_exp_conventions_def, AllCaseEqs()]
  >- (first_x_assum drule_all \\ strip_tac
      \\ gvs [] \\ strip_tac \\ gvs []
      \\ irule data_inv_merge_l
      \\ ‘wf_data (:'a) data’ by gvs [data_inv_def]
      \\ drule word_cse_wf_data
      \\ disch_then (qspec_then ‘c2’ assume_tac)
      \\ gvs [data_inv_def])
  \\ first_x_assum drule_all \\ strip_tac
  \\ gvs [] \\ strip_tac \\ gvs []
  \\ irule data_inv_merge_r
  \\ ‘wf_data (:'a) data’ by gvs [data_inv_def]
  \\ drule word_cse_wf_data
  \\ disch_then (qspec_then ‘c1’ assume_tac)
  \\ gvs [data_inv_def]
QED

Resume comp_correct[LocValue]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ ‘data_inv (invalidate_data data r) s ∧
      lookup r (invalidate_data data r).to_canonical = NONE’ by
       (rw [invalidate_data_def, keep_data_def] \\ gvs [empty_data_def])
  \\ drule_all add_to_data_LocValue_correct \\ gvs []
QED

Resume comp_correct[Install]:
  gvs [word_cse_def]
QED

Resume comp_correct[CodeBufferWrite]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ irule data_inv_state_agree
  \\ qexists_tac ‘s’ \\ gvs []
QED

Resume comp_correct[DataBufferWrite]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ irule data_inv_state_agree
  \\ qexists_tac ‘s’ \\ gvs []
QED

Resume comp_correct[FFI]:
  gvs [word_cse_def]
QED

Resume comp_correct[Call]:
  gvs [word_cse_def]
QED

Resume comp_correct[StoreConsts]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs(), invalidate_regs_def,
          invalidate_data_def, keep_data_def]
  \\ rpt IF_CASES_TAC
  \\ gvs [data_inv_memory, data_inv_set_var, data_inv_unset_var]
QED

Resume comp_correct[ShareInst]:
  rpt gen_tac \\ strip_tac
  \\ gvs [word_cse_def, evaluate_def, AllCaseEqs()]
  \\ Cases_on ‘op’
  \\ gvs [is_store_def, share_inst_def, sh_mem_load_def, sh_mem_load_byte_def,
          sh_mem_load16_def, sh_mem_load32_def, sh_mem_set_var_def,
          sh_mem_store_def, sh_mem_store_byte_def, sh_mem_store16_def,
          sh_mem_store32_def, invalidate_data_def, keep_data_def, AllCaseEqs()]
  >- (irule data_inv_state_agree \\ qexists_tac ‘s’ \\ gvs [])
  >- (irule data_inv_state_agree \\ qexists_tac ‘s’ \\ gvs [])
  >- (irule data_inv_state_agree \\ qexists_tac ‘s’ \\ gvs [])
  >- (irule data_inv_state_agree \\ qexists_tac ‘s’ \\ gvs [])
  \\ strip_tac \\ IF_CASES_TAC \\ gvs []
  \\ qpat_x_assum ‘sh_mem_set_var _ _ _ = _’ mp_tac
  \\ IF_CASES_TAC \\ simp [sh_mem_set_var_def]
  \\ qmatch_goalsub_abbrev_tac ‘sh_mem_set_var (SOME ffires) _ _’
  \\ Cases_on ‘ffires’ \\ simp [sh_mem_set_var_def]
  \\ strip_tac \\ gvs []
  \\ qmatch_goalsub_abbrev_tac ‘data_inv _ (sv with ffi := _)’
  \\ irule data_inv_state_agree \\ qexists_tac ‘sv’
  \\ gvs [Abbr ‘sv’, data_inv_set_var]
QED

Resume comp_correct[Loop]:
  rpt gen_tac >> strip_tac >>
  gvs [word_cse_def] >> rpt (pairarg_tac >> gvs []) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum ‘evaluate (Loop _ _ _, _) = _’ mp_tac >>
  once_rewrite_tac [evaluate_def] >>
  simp [cut_state_def, UNCURRY, STOP_def] >>
  TOP_CASE_TAC >> simp [] >>
  Cases_on ‘evaluate (c, x)’ >> simp [] >> strip_tac >>
  ‘q ≠ SOME Error’ by
    (CCONTR_TAC >> gvs [cont_loop_def, exit_loop_def, AllCaseEqs()]) >>
  ‘evaluate (c', x) = (q, r)’ by
    (qpat_x_assum ‘∀v. cut_state _ _ = SOME v ⇒ _’ (qspec_then ‘x’ mp_tac) >>
     impl_tac >- gvs [cut_state_def, AllCaseEqs()] >>
     disch_then (qspecl_then [‘q’,‘r’,‘empty_data’,‘c'’,‘_0’] mp_tac) >>
     gvs [flat_exp_conventions_def, data_inv_empty]) >>
  simp [] >>
  qpat_x_assum ‘(if cont_loop _ then _ else _) = _’ mp_tac >>
  IF_CASES_TAC >> simp []
  >- (IF_CASES_TAC >> simp [] >> strip_tac >>
      first_x_assum (qspecl_then [‘x’,‘q’,‘r’] mp_tac) >>
      impl_tac >- gvs [cut_state_def, AllCaseEqs()] >>
      disch_then (qspecl_then [‘res’,‘s'’,‘empty_data’,
        ‘Loop names c' exit_names’,‘empty_data’] mp_tac) >>
      simp [STOP_def, flat_exp_conventions_def, data_inv_empty, word_cse_def] >>
      rpt (pairarg_tac >> gvs []))
QED

Finalise comp_correct;

Theorem word_common_subexp_elim_correct:
  evaluate (p, s) = (res,s1) ∧
  flat_exp_conventions p ∧ res ≠ SOME Error ⇒
  evaluate (word_common_subexp_elim p, s) = (res,s1)
Proof
  rw [word_common_subexp_elim_def]
  \\ pairarg_tac \\ gvs []
  \\ drule comp_correct \\ fs []
  \\ disch_then imp_res_tac \\ fs []
QED

(* ------------------------------------------------------------------------
   SYNTACTIC CONVENTIONS

   word_cse emits only original instructions or Moves (the canonicalized
   arith only feeds the hash key, never the output program), so every
   syntactic convention transports with no well-formedness premise.
   ------------------------------------------------------------------------ *)

Theorem word_cse_full_inst_ok_less:
  ∀p data c data' (q:'a prog).
    full_inst_ok_less c p ∧ word_cse data p = (data',q) ⇒
    full_inst_ok_less c q
Proof
  Induct
  \\ simp []
  \\ rpt gen_tac \\ strip_tac
  >~ [`Inst`] >- (
    gvs [word_cse_def]
    \\ pairarg_tac \\ gvs []
    \\ namedCases_on ‘i’ ["", "r w", "a", "m r ad", "fp"]
    >- gvs [word_cseInst_def, full_inst_ok_less_def]
    >- gvs [word_cseInst_def, add_to_data_def, add_to_data_aux_def,
            AllCaseEqs(), full_inst_ok_less_def]
    >- gvs [word_cseInst_def, add_to_data_def, add_to_data_aux_def,
            AllCaseEqs(), full_inst_ok_less_def]
    >- (namedCases_on ‘ad’ ["ar ofs"]
        \\ gvs [word_cseInst_def, add_to_load_aux_def, AllCaseEqs(),
                full_inst_ok_less_def])
    \\ gvs [word_cseInst_def, full_inst_ok_less_def])
  >~ [`MustTerminate`] >- (
    gvs [word_cse_def, full_inst_ok_less_def]
    \\ pairarg_tac \\ gvs [full_inst_ok_less_def]
    \\ first_x_assum drule_all \\ simp [])
  >~ [`wordLang$Seq`] >- (
    gvs [word_cse_def, full_inst_ok_less_def]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs [full_inst_ok_less_def]
    \\ res_tac \\ simp [])
  >~ [`wordLang$If`] >- (
    gvs [word_cse_def, full_inst_ok_less_def]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs [full_inst_ok_less_def]
    \\ res_tac \\ simp [])
  >~ [`Loop`] >- (
    gvs [word_cse_def, full_inst_ok_less_def]
    \\ pairarg_tac \\ gvs [full_inst_ok_less_def]
    \\ first_x_assum drule_all \\ simp [])
  >> gvs [word_cse_def, add_to_data_aux_def, full_inst_ok_less_def,
          AllCaseEqs()]
QED

Theorem word_cse_pre_alloc_conventions:
  ∀p data data' (q:'a prog).
    pre_alloc_conventions p ∧ word_cse data p = (data',q) ⇒
    pre_alloc_conventions q
Proof
  Induct
  \\ simp []
  \\ rpt gen_tac \\ strip_tac
  >~ [`Inst`] >- (
    gvs [word_cse_def]
    \\ pairarg_tac \\ gvs []
    \\ namedCases_on ‘i’ ["", "r w", "a", "m r ad", "fp"]
    >- gvs [word_cseInst_def, pre_alloc_conventions_def,
            every_stack_var_def, call_arg_convention_def]
    >- gvs [word_cseInst_def, add_to_data_def, add_to_data_aux_def,
            AllCaseEqs(), pre_alloc_conventions_def, every_stack_var_def,
            call_arg_convention_def]
    >- gvs [word_cseInst_def, add_to_data_def, add_to_data_aux_def,
            AllCaseEqs(), pre_alloc_conventions_def, every_stack_var_def,
            call_arg_convention_def]
    >- (namedCases_on ‘ad’ ["ar ofs"]
        \\ gvs [word_cseInst_def, add_to_load_aux_def, AllCaseEqs(),
                pre_alloc_conventions_def, every_stack_var_def,
                call_arg_convention_def])
    \\ gvs [word_cseInst_def, pre_alloc_conventions_def,
            every_stack_var_def, call_arg_convention_def])
  >~ [`MustTerminate`] >- (
    gvs [word_cse_def]
    \\ pairarg_tac \\ gvs []
    \\ ‘pre_alloc_conventions p’ by
         (qpat_x_assum ‘pre_alloc_conventions (MustTerminate _)’ mp_tac
          \\ simp [pre_alloc_conventions_def, every_stack_var_def,
                   call_arg_convention_def])
    \\ res_tac
    \\ gvs [pre_alloc_conventions_def, every_stack_var_def,
            call_arg_convention_def])
  >~ [`wordLang$Seq`] >- (
    gvs [word_cse_def]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ ‘pre_alloc_conventions p ∧ pre_alloc_conventions p'’ by
         (qpat_x_assum ‘pre_alloc_conventions (Seq _ _)’ mp_tac
          \\ simp [pre_alloc_conventions_def, every_stack_var_def,
                   call_arg_convention_def])
    \\ res_tac
    \\ gvs [pre_alloc_conventions_def, every_stack_var_def,
            call_arg_convention_def])
  >~ [`wordLang$If`] >- (
    gvs [word_cse_def]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ ‘pre_alloc_conventions p ∧ pre_alloc_conventions p'’ by
         (qpat_x_assum ‘pre_alloc_conventions (If _ _ _ _ _)’ mp_tac
          \\ simp [pre_alloc_conventions_def, every_stack_var_def,
                   call_arg_convention_def])
    \\ res_tac
    \\ gvs [pre_alloc_conventions_def, every_stack_var_def,
            call_arg_convention_def])
  >~ [`Loop`] >- (
    gvs [word_cse_def]
    \\ pairarg_tac \\ gvs []
    \\ ‘pre_alloc_conventions p’ by
         (qpat_x_assum ‘pre_alloc_conventions (Loop _ _ _)’ mp_tac
          \\ simp [pre_alloc_conventions_def, every_stack_var_def,
                   call_arg_convention_def])
    \\ res_tac
    \\ gvs [pre_alloc_conventions_def, every_stack_var_def,
            call_arg_convention_def])
  >> gvs [word_cse_def, add_to_data_aux_def, pre_alloc_conventions_def,
          every_stack_var_def, call_arg_convention_def, AllCaseEqs()]
QED

Theorem word_cse_every_inst_distinct_tar_reg:
  ∀p data data' (q:'a prog).
    every_inst distinct_tar_reg p ∧ word_cse data p = (data',q) ⇒
    every_inst distinct_tar_reg q
Proof
  Induct
  \\ simp []
  \\ rpt gen_tac \\ strip_tac
  >~ [`Inst`] >- (
    gvs [word_cse_def]
    \\ pairarg_tac \\ gvs []
    \\ namedCases_on ‘i’ ["", "r w", "a", "m r ad", "fp"]
    >- gvs [word_cseInst_def, every_inst_def]
    >- gvs [word_cseInst_def, add_to_data_def, add_to_data_aux_def,
            AllCaseEqs(), every_inst_def]
    >- gvs [word_cseInst_def, add_to_data_def, add_to_data_aux_def,
            AllCaseEqs(), every_inst_def]
    >- (namedCases_on ‘ad’ ["ar ofs"]
        \\ gvs [word_cseInst_def, add_to_load_aux_def, AllCaseEqs(),
                every_inst_def])
    \\ gvs [word_cseInst_def, every_inst_def])
  >~ [`MustTerminate`] >- (
    gvs [word_cse_def, every_inst_def]
    \\ pairarg_tac \\ gvs [every_inst_def]
    \\ first_x_assum drule_all \\ simp [])
  >~ [`wordLang$Seq`] >- (
    gvs [word_cse_def, every_inst_def]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs [every_inst_def]
    \\ res_tac \\ simp [])
  >~ [`wordLang$If`] >- (
    gvs [word_cse_def, every_inst_def]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs [every_inst_def]
    \\ res_tac \\ simp [])
  >~ [`Loop`] >- (
    gvs [word_cse_def, every_inst_def]
    \\ pairarg_tac \\ gvs [every_inst_def]
    \\ first_x_assum drule_all \\ simp [])
  >> gvs [word_cse_def, add_to_data_aux_def, every_inst_def, AllCaseEqs()]
QED

Theorem word_cse_every_inst_two_reg:
  ∀p data data' (q:'a prog).
    every_inst two_reg_inst p ∧ word_cse data p = (data',q) ⇒
    every_inst two_reg_inst q
Proof
  Induct
  \\ simp []
  \\ rpt gen_tac \\ strip_tac
  >~ [`Inst`] >- (
    gvs [word_cse_def]
    \\ pairarg_tac \\ gvs []
    \\ namedCases_on ‘i’ ["", "r w", "a", "m r ad", "fp"]
    >- gvs [word_cseInst_def, every_inst_def]
    >- gvs [word_cseInst_def, add_to_data_def, add_to_data_aux_def,
            AllCaseEqs(), every_inst_def]
    >- gvs [word_cseInst_def, add_to_data_def, add_to_data_aux_def,
            AllCaseEqs(), every_inst_def]
    >- (namedCases_on ‘ad’ ["ar ofs"]
        \\ gvs [word_cseInst_def, add_to_load_aux_def, AllCaseEqs(),
                every_inst_def])
    \\ gvs [word_cseInst_def, every_inst_def])
  >~ [`MustTerminate`] >- (
    gvs [word_cse_def, every_inst_def]
    \\ pairarg_tac \\ gvs [every_inst_def]
    \\ first_x_assum drule_all \\ simp [])
  >~ [`wordLang$Seq`] >- (
    gvs [word_cse_def, every_inst_def]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs [every_inst_def]
    \\ res_tac \\ simp [])
  >~ [`wordLang$If`] >- (
    gvs [word_cse_def, every_inst_def]
    \\ pairarg_tac \\ gvs []
    \\ pairarg_tac \\ gvs [every_inst_def]
    \\ res_tac \\ simp [])
  >~ [`Loop`] >- (
    gvs [word_cse_def, every_inst_def]
    \\ pairarg_tac \\ gvs [every_inst_def]
    \\ first_x_assum drule_all \\ simp [])
  >> gvs [word_cse_def, add_to_data_aux_def, every_inst_def, AllCaseEqs()]
QED

Theorem every_inst_distinct_tar_reg_word_common_subexp_elim:
  every_inst distinct_tar_reg p ⇒
  every_inst distinct_tar_reg (word_common_subexp_elim p)
Proof
  strip_tac
  \\ fs [word_common_subexp_elim_def] \\ pairarg_tac \\ gvs []
  \\ drule_all word_cse_every_inst_distinct_tar_reg \\ simp []
QED

Theorem pre_alloc_conventions_word_common_subexp_elim:
  pre_alloc_conventions p ⇒
  pre_alloc_conventions (word_common_subexp_elim p)
Proof
  strip_tac
  \\ fs [word_common_subexp_elim_def] \\ pairarg_tac \\ gvs []
  \\ drule_all word_cse_pre_alloc_conventions \\ simp []
QED

Theorem full_inst_ok_less_word_common_subexp_elim:
  full_inst_ok_less ac p ⇒
  full_inst_ok_less ac (word_common_subexp_elim p)
Proof
  strip_tac
  \\ fs [word_common_subexp_elim_def] \\ pairarg_tac \\ gvs []
  \\ drule_all word_cse_full_inst_ok_less \\ simp []
QED

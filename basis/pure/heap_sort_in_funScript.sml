(*
  Heap-sort in an array, where the array is represented by a function.

  Used to verify a stateful heap sort which uses a mutable array to
  hold the heap contents during sorting, e.g. one written in CakeML.

  Could potentially move out of CakeML to HOL4 sorting theories.
*)
Theory heap_sort_in_fun
Ancestors
   list rich_list sorting container bag


Definition heap_inv_def:
  heap_inv R sz hp = (! i. 1n < i /\ i <= sz ==> R (hp (i DIV 2)) (hp i))
End

Theorem heap_inv_thm = hd (RES_CANON heap_inv_def)

Theorem div_2_idem_lemma[local]:
  (i = i DIV 2) = (i = 0)
Proof
  qspec_then `i` assume_tac arithmeticTheory.ODD_OR_EVEN
  \\ fs []
QED

Theorem heap_inv_min:
  heap_inv R sz hp ==>
  transitive R ==>
  reflexive R ==>
  1 <= i /\ i <= sz ==>
  R (hp 1) (hp i)
Proof
  measureInduct_on `I i`
  \\ rw []
  \\ fs []
  \\ Cases_on `i = 1`
  \\ fs [relationTheory.reflexive_def]
  \\ fs [relationTheory.transitive_def]
  \\ first_x_assum irule
  \\ qexists_tac `hp (i DIV 2)`
  \\ drule_then (simp o single) heap_inv_thm
  \\ first_x_assum irule
  \\ simp [arithmeticTheory.X_LE_DIV]
QED

Theorem heap_inv_upd:
  heap_inv R sz hp ==>
  0 < i ==>
  (1 < i ==> R (hp (i DIV 2)) x) ==>
  (i * 2 <= sz ==> R x (hp (i * 2))) ==>
  (i * 2 + 1 <= sz ==> R x (hp (i * 2 + 1))) ==>
  heap_inv R sz (hp(|i |-> x|))
Proof
  rw [heap_inv_def]
  \\ first_x_assum (qspec_then `i'` assume_tac)
  \\ fs [combinTheory.UPDATE_def]
  \\ rw [] \\ gs [div_2_idem_lemma]
  \\ qspec_then `i'` assume_tac arithmeticTheory.ODD_OR_EVEN
  \\ gs []
QED

Definition heap_contents_def:
  heap_contents sz hp = LIST_TO_BAG (GENLIST (hp o ((+) 1)) sz)
End

Theorem heap_contents_mem:
  0 < i /\ i <= sz ==> BAG_IN (hp i) (heap_contents sz hp)
Proof
  rw [heap_contents_def, IN_LIST_TO_BAG, MEM_GENLIST]
  \\ qexists_tac `i - 1`
  \\ simp []
QED

Theorem heap_contents_upd:
  heap_contents sz (hp(|i |-> x|)) = (if 0 < i /\ i <= sz
    then BAG_UNION (heap_contents sz hp) {|x|} - {|hp i|}
    else heap_contents sz hp)
Proof
  simp [heap_contents_def]
  \\ rw []
  >- (
    qspecl_then [`hp`, `sz - (i - 1)`, `i - 1`]
      (mp_tac o Q.GEN `hp`) GENLIST_APPEND
    \\ rw [LIST_TO_BAG_APPEND]
    \\ subgoal `sz + 1 - i = SUC (sz - i)`
    \\ simp [GENLIST_CONS, BAG_UNION_INSERT]
    \\ ONCE_REWRITE_TAC [BAG_INSERT_commutes]
    \\ simp []
    \\ irule (Q.prove (`(a = c) /\ (b = d) ==> (BAG_UNION a b = BAG_UNION c d)`, metis_tac []))
    \\ rw []
    \\ AP_TERM_TAC
    \\ irule GENLIST_CONG
    \\ simp [combinTheory.UPDATE_APPLY]
  )
  >- (
    AP_TERM_TAC
    \\ irule GENLIST_CONG
    \\ simp [combinTheory.UPDATE_APPLY]
  )
QED

Definition heap_insert_larger_def:
  heap_insert_larger R sz i x hp = (if i = 0 then hp
    else if (i * 2) + 1 <= sz /\ R (hp ((i * 2) + 1)) x /\ R (hp ((i * 2) + 1)) (hp (i * 2))
    then heap_insert_larger R sz ((i * 2) + 1) x (hp(|i |-> hp ((i * 2) + 1)|))
    else if i * 2 <= sz /\ R (hp (i * 2)) x /\ ((i * 2) + 1 <= sz ==> R (hp (i * 2)) (hp ((i * 2) + 1)))
    then heap_insert_larger R sz (i * 2) x (hp(|i |-> hp (i * 2)|))
    else hp(| i |-> x |))
Termination
  qexists_tac `measure (\(_, sz, i, _). sz - i)`
  \\ simp []
End

Theorem total_lemma[local]:
  total R ==> ~ R x y ==> R y x
Proof
  metis_tac [relationTheory.total_def]
QED

Theorem transitive_lemma[local] = hd (RES_CANON relationTheory.transitive_def)

Theorem heap_insert_larger_inv:
  heap_inv R sz hp ==> R (hp i) x ==> 0 < i ==> i <= sz ==>
  reflexive R ==> transitive R ==> total R ==>
  heap_inv R sz (heap_insert_larger R sz i x hp)
Proof
  qid_spec_tac `hp`
  \\ measureInduct_on `(\i. sz - i) i`
  \\ rw [] \\ fs []
  \\ drule_then (qspec_then `i` mp_tac) heap_inv_thm
  \\ drule_then (qspec_then `i * 2` mp_tac) heap_inv_thm
  \\ drule_then (qspec_then `i * 2 + 1` mp_tac) heap_inv_thm
  \\ ONCE_REWRITE_TAC [heap_insert_larger_def]
  \\ rw [] \\ fs []
  \\ TRY (first_x_assum irule)
  \\ irule_at Any heap_inv_upd
  \\ fs [relationTheory.reflexive_def, combinTheory.UPDATE_APPLY]
  \\ rw []
  \\ drule_then (fsrw_tac [SFY_ss] o single) transitive_lemma
  \\ drule_then (simp o single) total_lemma
  \\ metis_tac [transitive_lemma, total_lemma]
QED

Theorem heap_insert_larger_contents:
  heap_contents sz (heap_insert_larger R sz i x hp) =
  heap_contents sz (hp (|i |-> x|))
Proof
  qid_spec_tac `hp`
  \\ measureInduct_on `(\i. sz - i) i`
  \\ rw []
  \\ ONCE_REWRITE_TAC [heap_insert_larger_def]
  \\ mp_tac heap_contents_mem
  \\ rw [] \\ fs []
  \\ simp [heap_contents_upd, combinTheory.UPDATE_APPLY]
  \\ simp [BAG_UNION_INSERT]
  \\ fs [GSYM BAG_DIFF_INSERT_SUB_BAG]
  \\ metis_tac [BAG_DIFF_INSERT_SUB_BAG, BAG_INSERT_commutes,
        BAG_DIFF_2L, COMM_BAG_UNION, BAG_DIFF_INSERT_same,
        BAG_DIFF_EMPTY]
QED

Definition heap_pop_def:
  heap_pop R sz hp = (hp 1, heap_insert_larger R (sz - 1) 1 (hp sz) hp)
End

Theorem heap_pop_inv:
  heap_inv R sz hp ==> 0 < sz ==>
  reflexive R ==> transitive R ==> total R ==>
  heap_inv R (sz - 1) (SND (heap_pop R sz hp))
Proof
  rw [heap_pop_def]
  \\ Cases_on `sz = 1`
  >- (
    simp [heap_inv_def]
  )
  \\ irule heap_insert_larger_inv
  \\ simp []
  \\ drule_then (irule_at Any) heap_inv_min
  \\ simp []
  \\ fs [heap_inv_def]
QED

Theorem heap_pop_contents:
  (heap_pop R sz hp = (x, hp2)) ==>
  0 < sz ==>
  (BAG_UNION {|x|} (heap_contents (sz - 1) hp2) =
  heap_contents sz hp)
Proof
  simp [heap_pop_def]
  \\ rw []
  \\ simp [heap_insert_larger_contents, heap_contents_upd]
  \\ Cases_on `sz = 1` \\ fs []
  \\ simp [heap_contents_def]
  \\ Cases_on `sz` \\ fs []
  \\ simp [GENLIST, SNOC_APPEND, LIST_TO_BAG_APPEND]
  \\ Cases_on `n` \\ fs []
  \\ simp [GENLIST_CONS]
  \\ simp [GENLIST_CONS, BAG_UNION_INSERT]
  \\ simp [arithmeticTheory.SUC_ONE_ADD]
QED

Theorem heap_pop_min:
  (heap_pop R sz hp = (x, hp2)) ==>
  heap_inv R sz hp ==> 0 < sz ==>
  reflexive R ==> transitive R ==>
  (x = hp 1) /\ (0 < (sz - 1) ==> R x (hp2 1))
Proof
  rpt disch_tac
  \\ subgoal `0 < sz - 1 ==> BAG_IN (hp2 1) (heap_contents sz hp)`
  >- (
    drule heap_pop_contents
    \\ simp []
    \\ disch_then (simp o single o GSYM)
    \\ simp [heap_contents_def]
    \\ Cases_on `sz - 1` \\ simp []
    \\ simp [GENLIST_CONS]
  )
  \\ fs [heap_pop_def]
  \\ rw []
  \\ fs [heap_contents_def, IN_LIST_TO_BAG, MEM_GENLIST]
  \\ drule_then irule heap_inv_min
  \\ simp []
QED

Definition heap_insert_smaller_def:
  heap_insert_smaller R sz i x hp = (if i <= 1 then hp(| i |-> x |)
    else if R x (hp (i DIV 2))
    then heap_insert_smaller R sz (i DIV 2) x (hp(|i |-> hp (i DIV 2)|))
    else hp(| i |-> x |))
End

Theorem heap_insert_smaller_inv:
  heap_inv R sz hp ==> (i < sz ==> R x (hp i)) ==> 0 < i ==> i <= sz ==>
  reflexive R ==> transitive R ==> total R ==>
  heap_inv R sz (heap_insert_smaller R sz i x hp)
Proof
  qid_spec_tac `hp`
  \\ measureInduct_on `I i`
  \\ rw [] \\ fs []
  \\ drule_then (qspec_then `i` mp_tac) heap_inv_thm
  \\ drule_then (qspec_then `i * 2` mp_tac) heap_inv_thm
  \\ drule_then (qspec_then `i * 2 + 1` mp_tac) heap_inv_thm
  \\ ONCE_REWRITE_TAC [heap_insert_smaller_def]
  \\ rw [] \\ fs []
  \\ TRY (first_x_assum irule)
  \\ irule_at Any heap_inv_upd
  \\ fs [relationTheory.reflexive_def, combinTheory.UPDATE_APPLY, div_2_idem_lemma]
  \\ rw []
  \\ fs [dividesTheory.DIV_POS]
  \\ drule_then (fsrw_tac [SFY_ss] o single) transitive_lemma
  \\ drule_then (simp o single) total_lemma
QED

Theorem heap_insert_smaller_contents:
  0 < i ==> i <= sz ==>
  (heap_contents sz (heap_insert_smaller R sz i x hp) = heap_contents sz (hp (|i |-> x|)))
Proof
  qid_spec_tac `hp`
  \\ measureInduct_on `I i`
  \\ rw [] \\ fs []
  \\ ONCE_REWRITE_TAC [heap_insert_smaller_def]
  \\ rw []
  \\ fs [dividesTheory.DIV_POS]
  \\ simp [heap_contents_upd, dividesTheory.DIV_POS, combinTheory.UPDATE_APPLY, div_2_idem_lemma]
  \\ mp_tac heap_contents_mem
  \\ rw [] \\ fs []
  >- (
    simp [BAG_UNION_INSERT]
    \\ fs [GSYM BAG_DIFF_INSERT_SUB_BAG]
    \\ metis_tac [BAG_DIFF_INSERT_SUB_BAG, BAG_INSERT_commutes,
        BAG_DIFF_2L, COMM_BAG_UNION, BAG_DIFF_INSERT_same,
        BAG_DIFF_EMPTY]
  )
  \\ qspec_then `i` assume_tac arithmeticTheory.ODD_OR_EVEN
  \\ gs []
QED

Definition heap_add_def:
  heap_add R sz hp x = heap_insert_smaller R (sz + 1) (sz + 1) x
    (hp(| sz + 1 |-> hp((sz + 1) DIV 2)|))
End

Theorem heap_add_inv:
  heap_inv R sz hp ==>
  reflexive R ==> transitive R ==> total R ==>
  heap_inv R (sz + 1) (heap_add R sz hp x)
Proof
  rw [heap_add_def]
  \\ irule heap_insert_smaller_inv
  \\ rw [heap_inv_def]
  \\ drule_then (qspec_then `i` mp_tac) heap_inv_thm
  \\ rw [] \\ gs []
  \\ rw [combinTheory.UPDATE_def]
  \\ fs [div_2_idem_lemma, relationTheory.reflexive_def]
  \\ qspec_then `i` assume_tac arithmeticTheory.ODD_OR_EVEN
  \\ gs []
QED

Theorem heap_add_contents:
  heap_contents (sz + 1) (heap_add R sz hp x) =
  BAG_UNION {|x|} (heap_contents sz hp)
Proof
  simp [heap_add_def, heap_insert_smaller_contents]
  \\ simp [heap_contents_upd]
  \\ simp [heap_contents_def]
  \\ simp [GSYM arithmeticTheory.ADD1]
  \\ simp [GENLIST, SNOC_APPEND, LIST_TO_BAG_APPEND]
  \\ simp [arithmeticTheory.ADD1]
  \\ simp [BAG_UNION_INSERT]
  \\ ONCE_REWRITE_TAC [BAG_INSERT_commutes]
  \\ simp []
QED

Definition heap_add_all_def:
  (heap_add_all R sz [] hp = hp) /\
  (heap_add_all R sz (x :: xs) hp =
    heap_add_all R (sz + 1) xs (heap_add R sz hp x))
End

Theorem heap_add_all_inv:
  heap_inv R sz hp ==>
  reflexive R ==> transitive R ==> total R ==>
  (sz2 = sz + LENGTH xs) ==>
  heap_inv R sz2 (heap_add_all R sz xs hp)
Proof
  qid_spec_tac `hp`
  \\ qid_spec_tac `sz`
  \\ qid_spec_tac `sz2`
  \\ Induct_on `xs`
  \\ simp [heap_add_all_def]
  \\ rw []
  \\ simp_tac bool_ss [arithmeticTheory.SUC_ONE_ADD, arithmeticTheory.ADD_ASSOC]
  \\ first_x_assum irule
  \\ simp []
  \\ irule heap_add_inv
  \\ simp []
QED

Theorem heap_add_all_contents:
  (sz2 = sz + LENGTH xs) ==>
  (heap_contents sz2 (heap_add_all R sz xs hp) =
    BAG_UNION (heap_contents sz hp) (LIST_TO_BAG xs))
Proof
  qid_spec_tac `hp`
  \\ qid_spec_tac `sz`
  \\ qid_spec_tac `sz2`
  \\ Induct_on `xs`
  \\ simp [heap_add_all_def]
  \\ rw []
  \\ asm_simp_tac bool_ss [arithmeticTheory.SUC_ONE_ADD, arithmeticTheory.ADD_ASSOC]
  \\ simp [heap_add_contents]
  \\ simp [BAG_INSERT_UNION]
  \\ simp [ASSOC_BAG_UNION]
  \\ simp [COMM_BAG_UNION]
QED

Definition heap_pop_all_def:
  heap_pop_all R sz xs hp = (if sz = 0 then xs
    else let (x, hp2) = heap_pop R sz hp in
      heap_pop_all R (sz - 1) (x :: xs) hp2)
End

Theorem heap_pop_all_sorted:
  heap_inv R sz hp ==>
  reflexive R ==> transitive R ==> total R ==>
  SORTED (\x y. R y x) xs ==>
  (xs <> [] ==> 0 < sz ==> R (HD xs) (hp 1)) ==>
  (R2 = (\x y. R y x)) ==>
  SORTED R2 (heap_pop_all R sz xs hp)
Proof
  qid_spec_tac `hp`
  \\ qid_spec_tac `xs`
  \\ qid_spec_tac `R2`
  \\ Induct_on `sz`
  \\ ONCE_REWRITE_TAC [heap_pop_all_def]
  \\ simp []
  \\ rw []
  \\ pairarg_tac
  \\ drule heap_pop_inv
  \\ simp []
  \\ rw []
  \\ fs []
  \\ first_x_assum (drule_then irule)
  \\ simp []
  \\ drule heap_pop_min
  \\ rw []
  \\ Cases_on `xs` \\ fs []
QED

Theorem heap_pop_all_contents:
  LIST_TO_BAG (heap_pop_all R sz xs hp) =
    BAG_UNION (LIST_TO_BAG xs) (heap_contents sz hp)
Proof
  qid_spec_tac `hp`
  \\ qid_spec_tac `xs`
  \\ Induct_on `sz`
  \\ ONCE_REWRITE_TAC [heap_pop_all_def]
  \\ simp []
  >- (
    simp [heap_contents_def]
  )
  >- (
    rw []
    \\ pairarg_tac \\ fs []
    \\ drule_then (mp_tac o GSYM) heap_pop_contents
    \\ simp []
    \\ simp [BAG_INSERT_UNION, COMM_BAG_UNION]
    \\ metis_tac [ASSOC_BAG_UNION, COMM_BAG_UNION]
  )
QED

Definition heap_sort_def:
  heap_sort R xs = (case xs of [] => []
    | (x :: _) => (let R2 = (\x y. R y x);
        hp = heap_add_all R2 0 xs (K x) in
        heap_pop_all R2 (LENGTH xs) [] hp))
End

Theorem heap_sort_sorted:
  reflexive R ==> transitive R ==> total R ==>
  SORTED R (heap_sort R xs)
Proof
  rw [heap_sort_def]
  \\ Cases_on `xs` \\ fs []
  \\ irule heap_pop_all_sorted
  \\ simp []
  \\ irule_at Any heap_add_all_inv
  \\ simp []
  \\ simp [heap_inv_def, FUN_EQ_THM]
  \\ fs [relationTheory.reflexive_def, relationTheory.total_def]
  \\ fs [relationTheory.transitive_def]
  \\ metis_tac []
QED

Theorem heap_sort_contents:
  LIST_TO_BAG (heap_sort R xs) = LIST_TO_BAG xs
Proof
  simp [heap_sort_def]
  \\ Cases_on `xs` \\ simp []
  \\ simp [heap_pop_all_contents, heap_add_all_contents]
  \\ simp [heap_contents_def]
QED

Theorem heap_sort_perm:
  PERM (heap_sort R xs) xs
Proof
  simp [GSYM PERM_LIST_TO_BAG, heap_sort_contents]
QED


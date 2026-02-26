(*

  A heap-sort variant that builds a list of exactly-balanced heaps.

  This is prototyped and verified as a standard recursive functional program.

  It is also presented as an in-array algorithm, where the list of heaps are
  placed in segments of an array.

  This allows the one algorithm to be evaluated either via its pure functional
  instance or as an in-place algorithm in CakeML.

  The heap segments all point in the correct direction, so, unlike a standard
  in-array heap-sort, sorting a sorted array requires linear-time comparisons
  and no data moves.
*)

Theory heap_list_sort
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

Datatype:
  simple_tree = Empty_Tree | Node 'a simple_tree simple_tree
End

Definition tree_top_less_def:
  tree_top_less R Empty_Tree y = T /\
  tree_top_less R (Node x _ _) y = R x y
End

Definition heap_tree_inv_def:
  (heap_tree_inv R n Empty_Tree = (n = 0)) /\
  (heap_tree_inv R n (Node y l r) = (n > 0 /\
    heap_tree_inv R (n - 1) l /\ tree_top_less R l y /\
    heap_tree_inv R (n - 1) r /\ tree_top_less R r y
  ))
End

Theorem heap_tree_inv_empty_eq_eq[local]:
  heap_tree_inv R n t ==> ((t = Empty_Tree) = (n = 0))
Proof
  Cases_on `t` \\ simp [heap_tree_inv_def]
QED

Definition heaps_tree_inv_def:
  heaps_tree_inv R xs = (EVERY (\(t, n). heap_tree_inv R n t /\ n > 0) xs /\
    SORTED (\(t1, _) (t2, _). case t1 of Empty_Tree => F | Node x _ _ =>
        (case t2 of Empty_Tree => F | Node y _ _ => R y x)) xs
  )
End

Theorem heaps_tree_inv_rec_def:
  (heaps_tree_inv R [] = T) /\
  (heaps_tree_inv R (x :: xs) = (heap_tree_inv R (SND x) (FST x) /\ SND x > 0 /\
    ((xs <> []) ==> tree_top_less R (FST (HD xs)) (case x of (Node y _ _, _) => y)) /\
    heaps_tree_inv R xs))
Proof
  simp [heaps_tree_inv_def]
  \\ Cases_on `x` \\ simp []
  \\ Cases_on `xs` \\ simp []
  \\ rpt (pairarg_tac \\ fs [])
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [hd (CONJUNCTS heap_tree_inv_def)]
  \\ simp [tree_top_less_def]
  \\ EQ_TAC \\ rw [] \\ simp []
QED

Definition tree_to_bag_def:
  tree_to_bag Empty_Tree = {||} /\
  tree_to_bag (Node x l r) = BAG_INSERT x (BAG_UNION (tree_to_bag l) (tree_to_bag r))
End

(* Insert into a balanced heap/tree maintaining the invariant. *)
Definition insert_tree_inv_def:
  insert_tree_inv R Empty_Tree x = Empty_Tree /\
  insert_tree_inv R (Node _ l r) x = (case l of Empty_Tree => Node x l r
    | Node lx _ _ => (case r of Empty_Tree => Node x l r
    | Node rx _ _ => if R lx x /\ R rx x then Node x l r
    else if R lx rx then Node rx l (insert_tree_inv R r x)
    else Node lx (insert_tree_inv R l x) r
  ))
End

Theorem insert_tree_inv_size:
  simple_tree_size (K 0) (insert_tree_inv R t x) =
  simple_tree_size (K 0) t
Proof
  Induct_on `t`
  \\ simp [insert_tree_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
QED

(* Insert into a chain of heap/trees. *)
Definition insert_trees_inv_def:
  (insert_trees_inv R [] x = []) /\
  (insert_trees_inv R ((t1, n1) :: ts) x = (case ts of
    | [] => [(insert_tree_inv R t1 x, n1)]
    | (t2, n2) :: tl_ts =>
        (case t1 of Empty_Tree =>
            (* won't happen, leave list the same *) ((t1, n1) :: ts)
        | Node _ l r => (case t2 of Empty_Tree =>
            (* won't happen, leave list the same *) ((t1, n1) :: ts)
        | Node t2x _ _ => if ~ (R t2x x) /\
            ~ (case l of Empty_Tree => F | Node lx _ _ => R t2x lx) /\
            ~ (case r of Empty_Tree => F | Node rx _ _ => R t2x rx)
        then (Node t2x l r, n1) :: insert_trees_inv R ts x
        else (insert_tree_inv R t1 x, n1) :: ts
  ))))
End

Theorem insert_trees_inv_size:
  MAP (simple_tree_size (K 0) o FST) (insert_trees_inv R ts x) =
  MAP (simple_tree_size (K 0) o FST) ts
Proof
  measureInduct_on `LENGTH ts`
  \\ Cases_on `ts`
  \\ simp [insert_trees_inv_def]
  \\ Cases_on `h`
  \\ simp [insert_trees_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [insert_tree_inv_size]
QED

Theorem insert_trees_inv_length =
  Q.AP_TERM `LENGTH` insert_trees_inv_size |> REWRITE_RULE [LENGTH_MAP]

Definition add_trees_step1_def:
  add_trees_step1 ts x = (case ts of
    (t1, n1) :: (t2, n2) :: ts2 => if n1 = n2
        then (Node x t2 t1, n1 + 1) :: ts2
        else (Node x Empty_Tree Empty_Tree, 1) :: ts
  | _ => (Node x Empty_Tree Empty_Tree, 1) :: ts
  )
End

Definition add_trees_def:
  add_trees R ts x = insert_trees_inv R (add_trees_step1 ts x) x
End

Definition build_trees_def:
  build_trees R ts [] = ts /\
  build_trees R ts (x :: xs) = build_trees R (add_trees R ts x) xs
End

Definition extend_trees_def:
  extend_trees R ts t n = (case t of
    Empty_Tree => ts
  | Node x l r => (let ord = (case ts of ((Node y _ _, _) :: _) => R y x | _ => T)
    in if ord then (t, n) :: ts
        else insert_trees_inv R ((t, n) :: ts) x
  ))
End

Theorem extend_trees_size:
  SUM (MAP (\t_n. simple_tree_size (K 0) (FST t_n)) (extend_trees R ts t n)) =
    simple_tree_size (K 0) t + SUM (MAP (\t_n. simple_tree_size (K 0) (FST t_n)) ts)
Proof
  simp [extend_trees_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [REWRITE_RULE [combinTheory.o_DEF] insert_trees_inv_size]
QED

Definition pull_trees_def:
  pull_trees R [] acc = acc /\
  pull_trees R ((Empty_Tree, _) :: ts) acc = acc /\
  pull_trees R ((Node x l r, n) :: ts) acc =
    let ts2 = extend_trees R ts l (n - 1);
        ts3 = extend_trees R ts2 r (n - 1)
    in pull_trees R ts3 (x :: acc)
Termination
  WF_REL_TAC `measure (\(R, ts, acc). SUM (MAP (simple_tree_size (K 0) o FST) ts))`
  \\ rw []
  \\ simp [extend_trees_size]
End

Definition another_heap_sort_def:
  another_heap_sort R xs = pull_trees R (build_trees R [] xs) []
End

(* Invariant preservation. *)
Theorem insert_tree_inv_less[local]:
  (case t of Node _ l r => tree_top_less R l y /\ tree_top_less R r y | _ => T) ==>
  R x y ==>
  transitive R ==> total R ==>
  tree_top_less R (insert_tree_inv R t x) y
Proof
  Cases_on `t` \\ simp [insert_tree_inv_def, tree_top_less_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [tree_top_less_def]
QED

Theorem insert_tree_inv:
  heap_tree_inv R n t ==>
  transitive R ==> total R ==>
  heap_tree_inv R n (insert_tree_inv R t x)
Proof
  qid_spec_tac `n`
  \\ Induct_on `t`
  \\ rw [insert_tree_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ gs [heap_tree_inv_def, tree_top_less_def]
  \\ irule_at Any insert_tree_inv_less
  \\ simp []
  \\ metis_tac [total_lemma, transitive_lemma]
QED

Theorem insert_tree_inv_greater[local]:
  R x y \/ (case l of Node ly _ _ => R x ly | _ => F) \/
      (case r of Node ry _ _ => R x ry | _ => F) ==>
  transitive R ==> total R ==>
  ((l = Empty_Tree) = (r = Empty_Tree)) ==>
  R x (case insert_tree_inv R (Node x_old l r) y of
    Empty_Tree => Anything | Node z _ _ => z)
Proof
  simp [insert_tree_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [tree_top_less_def]
  \\ metis_tac [transitive_lemma, total_lemma]
QED

Theorem insert_tree_inv_contents:
  tree_to_bag (insert_tree_inv R t x) = (case t of Empty_Tree => {||}
    | Node _ l r => tree_to_bag (Node x l r))
Proof
  Induct_on `t`
  \\ simp [insert_tree_inv_def, tree_to_bag_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [tree_to_bag_def]
  \\ simp [BAG_UNION_INSERT]
  \\ simp [BAG_INSERT_commutes]
QED

Theorem tree_top_less_mono:
  tree_top_less R t x ==> R x y ==>
  transitive R ==>
  tree_top_less R t y
Proof
  Cases_on `t`
  \\ simp [tree_top_less_def]
  \\ metis_tac [transitive_lemma]
QED

Theorem tree_top_less_neg[local]:
  (~ (case t of Empty_Tree => F | Node y _ _ => R x y)) ==>
  total R ==>
  tree_top_less R t x
Proof
  BasicProvers.EVERY_CASE_TAC \\ simp [tree_top_less_def]
  \\ metis_tac [total_lemma]
QED

Theorem heap_tree_inv_mono:
  heap_tree_inv R n (Node x l r) ==>
  R x y ==> transitive R ==>
  heap_tree_inv R n (Node y l r)
Proof
  simp [heap_tree_inv_def]
  \\ metis_tac [tree_top_less_mono]
QED

Theorem insert_trees_inv_less[local]:
  (case ts of [] => F | (Empty_Tree, _) :: _ => F | ((Node _ l r, _) :: ts2) =>
    tree_top_less R l y /\ tree_top_less R r y /\
    (ts2 <> [] ==> FST (HD (ts2)) <> Empty_Tree /\
        tree_top_less R (FST (HD ts2)) y)) ==>
  R x y ==>
  transitive R ==> total R ==>
  tree_top_less R (FST (HD (insert_trees_inv R ts x))) y
Proof
  BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [insert_trees_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ rw []
  \\ fs [tree_top_less_def, insert_tree_inv_less]
QED

Theorem insert_trees_inv:
  heaps_tree_inv R ts ==>
  transitive R ==> total R ==>
  heaps_tree_inv R (insert_trees_inv R ts x)
Proof
  Induct_on `ts`
  \\ simp [insert_trees_inv_def, pairTheory.FORALL_PROD, heaps_tree_inv_rec_def]
  \\ rpt gen_tac
  \\ ntac 2 BasicProvers.TOP_CASE_TAC
  \\ simp [insert_tree_inv, heaps_tree_inv_rec_def]
  \\ ntac 2 BasicProvers.TOP_CASE_TAC
  \\ simp [insert_tree_inv, heaps_tree_inv_rec_def]
  \\ fs [hd (CONJUNCTS heap_tree_inv_def)]
  \\ csimp []
  \\ rw [heaps_tree_inv_rec_def]
  \\ simp [insert_tree_inv]
  >- (
    fs [heap_tree_inv_def, tree_top_less_def]
    \\ rpt (dxrule tree_top_less_neg)
    \\ simp []
  )
  >- (
    irule insert_trees_inv_less
    \\ fs [heap_tree_inv_def, tree_top_less_def]
    \\ fsrw_tac [SFY_ss] [total_lemma]
    \\ rpt strip_tac
    \\ Cases_on `t` \\ fs []
    \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
  )
  >- (
    simp [tree_top_less_def]
    \\ irule insert_tree_inv_greater
    \\ fs [heap_tree_inv_def]
    \\ rpt (dxrule heap_tree_inv_empty_eq_eq)
    \\ simp []
  )
QED

Theorem insert_trees_inv_contents:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) (insert_trees_inv R ts x)) =
    (case ts of [] => {||}
      | (Node _ l r, _) :: ts => BAG_UNION (tree_to_bag (Node x l r))
          (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) ts)))
  )
Proof
  Induct_on `ts`
  \\ simp [pairTheory.FORALL_PROD, insert_trees_inv_def, tree_to_bag_def]
  \\ rw []
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
  \\ gs []
  \\ simp [insert_tree_inv_contents, tree_to_bag_def]
  \\ simp [BAG_UNION_INSERT]
  \\ simp [BAG_INSERT_commutes]
QED

Theorem insert_trees_non_empty:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  EVERY (\p. FST p <> Empty_Tree) (insert_trees_inv R ts x)
Proof
  Induct_on `ts`
  \\ simp [pairTheory.FORALL_PROD, insert_trees_inv_def]
  \\ rw []
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ gs []
  \\ rw [insert_tree_inv_def]
QED

Theorem build_trees_contents:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) (build_trees R ts xs)) =
  BAG_UNION (LIST_TO_BAG xs) (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) ts)) /\
  EVERY (\p. FST p <> Empty_Tree) (build_trees R ts xs)
Proof
  qid_spec_tac `ts`
  \\ Induct_on `xs`
  \\ rw [build_trees_def]
  \\ simp [add_trees_def, add_trees_step1_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ fs []
  \\ simp [insert_trees_inv_contents, insert_trees_non_empty, tree_to_bag_def]
  \\ simp [BAG_UNION_INSERT]
  \\ simp [BAG_INSERT_commutes, ASSOC_BAG_UNION, COMM_BAG_UNION]
QED

Theorem insert_tree_inv_adj[local]:
  insert_tree_inv R (Node x_dc l r) x =
  insert_tree_inv R (Node y_dc l r) x
Proof
  simp [insert_tree_inv_def]
QED

Theorem insert_tree_adj_inv[local]:
  heap_tree_inv R n (insert_tree_inv R (Node x l r) x)
  ==>
  heap_tree_inv R n (insert_tree_inv R (Node x_dc l r) x)
Proof
  simp [insert_tree_inv_def]
QED

Theorem insert_trees_adj_inv1[local]:
  heaps_tree_inv R (insert_trees_inv R ((Node x_dc l r, n) :: ts) x) ==>
  heaps_tree_inv R (insert_trees_inv R ((Node y_dc l r, n) :: ts) x)
Proof
  simp [insert_trees_inv_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [insert_tree_inv_def]
  \\ csimp [heaps_tree_inv_rec_def, heap_tree_inv_def]
QED

Theorem insert_trees_adj_inv2[local]:
  heaps_tree_inv R ts ==>
  heap_tree_inv R n (Node x_dc l r) ==>
  transitive R ==> total R ==> reflexive R ==>
  heaps_tree_inv R (insert_trees_inv R ((Node x_dc l r, n) :: ts) x)
Proof
  Cases_on `heaps_tree_inv R ((Node x_dc l r, n) :: ts)`
  \\ simp [insert_trees_inv]
  \\ rw []
  \\ irule insert_trees_adj_inv1
  \\ qexists_tac `case HD ts of (Node x _ _, _) => x`
  \\ irule insert_trees_inv
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
  \\ Cases_on `FST (HD ts)` \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs []
  \\ fs [tree_top_less_def]
  \\ simp [heaps_tree_inv_rec_def, heap_tree_inv_def, tree_top_less_def]
  \\ fs [relationTheory.reflexive_def]
  \\ rw []
  \\ drule_then irule tree_top_less_mono
  \\ simp []
  \\ metis_tac [total_lemma]
QED

Theorem insert_trees_adj_inv3[local]:
  heaps_tree_inv R ts ==>
  heap_tree_inv R (n - 1) l ==>
  heap_tree_inv R (n - 1) r ==>
  n > 0 ==>
  transitive R ==> total R ==> reflexive R ==>
  heaps_tree_inv R (insert_trees_inv R ((Node x_dc l r, n) :: ts) x)
Proof
  Cases_on `heap_tree_inv R n (Node (case l of Node y _ _ => y) l r) \/
      heap_tree_inv R n (Node (case r of Node y _ _ => y) l r)`
  >- (
    rw [] \\ fs []
    \\ irule insert_trees_adj_inv1
    \\ irule_at Any insert_trees_adj_inv2
    \\ simp []
    \\ first_x_assum (irule_at Any)
  )
  >- (
    rw [] \\ fs []
    \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [tree_top_less_def]
    \\ gs [relationTheory.reflexive_def]
    \\ irule insert_trees_adj_inv1
    \\ irule_at Any insert_trees_adj_inv2
    \\ simp [heap_tree_inv_def, relationTheory.reflexive_def, tree_top_less_def]
    \\ metis_tac [total_lemma]
  )
QED

Theorem build_trees_inv:
  heaps_tree_inv R ts ==>
  transitive R ==> total R ==> reflexive R ==>
  heaps_tree_inv R (build_trees R ts xs)
Proof
  qid_spec_tac `ts`
  \\ Induct_on `xs`
  \\ rw [build_trees_def]
  \\ simp [add_trees_def, add_trees_step1_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp []
  \\ first_x_assum irule
  \\ simp []
  \\ irule insert_trees_adj_inv3
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def, tree_top_less_def]
QED

Theorem extend_trees_contents[local]:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) (extend_trees R ts t n)) =
  BAG_UNION (tree_to_bag t) (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) ts))
Proof
  simp [extend_trees_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [tree_to_bag_def]
  \\ simp [insert_trees_inv_contents, insert_trees_non_empty, tree_to_bag_def]
QED

Theorem extend_trees_not_empty[local]:
  EVERY (\p. FST p <> Empty_Tree) ts ==>
  EVERY (\p. FST p <> Empty_Tree) (extend_trees R ts t n)
Proof
  simp [extend_trees_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ simp [insert_trees_non_empty]
QED

Theorem extend_trees_inv[local]:
  (t <> Empty_Tree ==> heap_tree_inv R n t) ==>
  heaps_tree_inv R ts ==>
  total R /\ transitive R /\ reflexive R ==>
  heaps_tree_inv R (extend_trees R ts t n)
Proof
  simp [extend_trees_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ csimp [heaps_tree_inv_rec_def, heap_tree_inv_def, tree_top_less_def]
  \\ rw []
  \\ irule insert_trees_adj_inv3
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
QED

Theorem extend_trees_less[local]:
  (ts <> [] ==> tree_top_less R (FST (HD ts)) x) ==>
  tree_top_less R t x ==>
  total R ==> transitive R ==>
  (extend_trees R ts t n <> []) ==>
  heaps_tree_inv R ts ==>
  heap_tree_inv R n t ==>
  tree_top_less R (FST (HD (extend_trees R ts t n))) x
Proof
  simp [extend_trees_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp []
  \\ rw []
  \\ irule insert_trees_inv_less
  \\ fs [tree_top_less_def]
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def]
  \\ fsrw_tac [SFY_ss] [tree_top_less_mono]
  \\ CCONTR_TAC
  \\ Cases_on `ts`
  \\ gs [heaps_tree_inv_rec_def, heap_tree_inv_def]
QED

Theorem pull_trees_contents:
  ! R ts acc. EVERY (\p. FST p <> Empty_Tree) ts ==>
  LIST_TO_BAG (pull_trees R ts acc) =
  BAG_UNION (FOLDR BAG_UNION {||} (MAP (tree_to_bag o FST) ts)) (LIST_TO_BAG acc)
Proof
  recInduct pull_trees_ind
  \\ rw []
  \\ simp [pull_trees_def, tree_to_bag_def]
  \\ simp [extend_trees_contents, extend_trees_not_empty]
  \\ simp [BAG_UNION_INSERT]
  \\ simp [BAG_INSERT_commutes, ASSOC_BAG_UNION, COMM_BAG_UNION]
QED

Theorem pull_trees_sorted:
  ! R ts acc. heaps_tree_inv R ts ==>
  transitive R ==> total R ==> reflexive R ==>
  SORTED R acc ==>
  ((ts <> []) ==> (acc <> []) ==> tree_top_less R (FST (HD ts)) (HD acc)) ==>
  SORTED R (pull_trees R ts acc)
Proof
  recInduct pull_trees_ind
  \\ rw [] \\ fs []
  \\ simp [pull_trees_def]
  \\ fs [heaps_tree_inv_rec_def, heap_tree_inv_def, tree_top_less_def]
  \\ gs []
  \\ first_x_assum irule
  \\ simp [extend_trees_inv]
  \\ rw []
  \\ simp [extend_trees_less, extend_trees_inv]
  \\ Cases_on `acc`
  \\ fs []
QED

Theorem another_heap_sort_sorted:
  reflexive R ==> transitive R ==> total R ==>
  SORTED R (another_heap_sort R xs)
Proof
  rw [another_heap_sort_def]
  \\ irule pull_trees_sorted
  \\ simp []
  \\ irule build_trees_inv
  \\ simp [heaps_tree_inv_def]
QED

Theorem another_heap_sort_contents:
  LIST_TO_BAG (another_heap_sort R xs) = LIST_TO_BAG xs
Proof
  rw [another_heap_sort_def]
  \\ simp [pull_trees_contents, build_trees_contents]
QED


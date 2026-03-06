(*
  Using the monadic translator to translate heap sorting functions.

  Bit of an experiment, may move to ListProg if useful.
*)

Theory heap_sort_monadic
Ancestors
  heap_sort_in_fun ml_translator ml_monad_translator
Libs
  preamble ml_translatorLib ml_monad_translator_interfaceLib

(* Part 1. Translator Setup. *)

(* Set up translator to not check subtractions never underflow. *)
val _ = ml_translatorLib.use_sub_check true;

val _ = set_up_monadic_translator ();

(* The type variable used as parameter to the state type. It seems very
   important that this is used consistently. Strangely `'a` seems to work (for
   the current code) though it created problems in a previous iteration. *)
val tvar = ``: 'state``;

(* Create the data type to handle the references *)
Datatype:
  state_refs = <|
                 heap_array : ( ^tvar ) list;
                 sz_array : num list;
                |>
End

(* Data type for the exceptions. Seems to be standard. *)
Datatype:
  state_exn = Fail string | Subscript
End

val state_type = ``: ( ^tvar ) state_refs``;

val config = local_state_config |>
              with_state state_type |>
              with_exception ``:state_exn`` |>
              with_resizeable_arrays [
                ("heap_array", listSyntax.mk_list ([], tvar), ``Subscript``, ``Subscript``),
                ("sz_array", ``[] : num list``, ``Subscript``, ``Subscript``)
              ];

val _ = start_translation config;

val run_init_state_def = define_run state_type [] "init_state";

(* It seems important to turn this on last, or something turns it off again? *)
val _ = ParseExtras.tight_equality();

(* Part 2. Definition of heap-list sort via "suffix encoded" balanced trees.
   Every heap/tree is of power-of-two-minus-one size, with the largest element
   at the end, and two equal-sized smaller trees before it. *)

(* Positions of the left child in a suffix encoded balanced tree
   of height ht. *)
Definition sfx_heap_left_def:
  sfx_heap_left i ht = (i - (2 EXP (ht - 1)))
End

(* Insert a value into a balanced suffix heap of height ht, replacing the
   current top element which is at index i. *)
Definition insert_into_sfx_heap_def:
  insert_into_sfx_heap R i ht x = if ht <= 1
  then update_heap_array i x
  else do
    l <- return (sfx_heap_left i ht);
    r <- return (i - 1);
    lx <- heap_array_sub l;
    rx <- heap_array_sub r;
    if R lx x /\ R rx x
    then update_heap_array i x
    else if R lx rx
    then do
      update_heap_array i rx;
      insert_into_sfx_heap R r (ht - 1) x
    od
    else do
      update_heap_array i lx;
      insert_into_sfx_heap R l (ht - 1) x
    od
  od
End

(* Insert a value into a sequence of balanced suffix heaps, heights stored
   in positions [0 ..< j] of the sz_array. Replace the top elements of the
   final heap, which is at index i.  *)
Definition insert_into_sfx_heap_list_def:
  insert_into_sfx_heap_list R i j x =
  if j <= 1 then do
    ht <- sz_array_sub (j - 1);
    insert_into_sfx_heap R i ht x
  od
  else do
    ht <- sz_array_sub (j - 1);
    i2 <- return ((i + 1) - (2 EXP ht));
    t2x <- heap_array_sub i2;
    cond1 <- return (~ R t2x x);
    cond <- if cond1 /\ (1 < ht)
      then do
        l <- return (sfx_heap_left i ht);
        r <- return (i - 1);
        lx <- heap_array_sub l;
        rx <- heap_array_sub r;
        return (~ R t2x lx /\ ~ R t2x rx)
      od
      else return cond1;
    if cond
    then do
      update_heap_array i t2x;
      insert_into_sfx_heap_list R i2 (j - 1) x
    od
    else insert_into_sfx_heap R i ht x
  od
End

(* Expand the total size of a sequence of balanced suffix heaps from i to
   i + 1 total elements, starting with j total heaps. *)
Definition add_to_sfx_heaps_step1_def:
  add_to_sfx_heaps_step1 j = do
    merge <- if j <= 1
      then return F
      else do
        n1 <- sz_array_sub (j - 1);
        n2 <- sz_array_sub (j - 2);
        return (n1 = n2);
      od;
    if merge
    then do
      n <- sz_array_sub (j - 2);
      update_sz_array (j - 2) (n + 1);
      return (j - 1);
    od
    else do
      update_sz_array j 1;
      return (j + 1);
    od
  od
End

(* Expand from i to i + 1 elements, set the new element, and preserve the heap
   invariants. *)
Definition add_to_sfx_heaps_def:
  add_to_sfx_heaps R i j x = do
    j' <- add_to_sfx_heaps_step1 j;
    insert_into_sfx_heap_list R i j' x;
    return j'
  od
End

(* Extend a list of suffix heaps by a list of values. *)
Definition add_all_to_sfx_heaps_def:
  (add_all_to_sfx_heaps R i j [] = return (i, j)) /\
  (add_all_to_sfx_heaps R i j (x :: xs) = do
    j <- add_to_sfx_heaps R i j x;
    add_all_to_sfx_heaps R (i + 1) j xs;
  od)
End

(* Take an intact heap in the correct position and add it to the heap sequence,
   i.e. ensure its top element is the overall top element. *)
Definition reinsert_tree_def:
  reinsert_tree R i j ht =
  do
    update_sz_array j ht;
    x <- heap_array_sub (i - 1);
    upd <- if 0 < j then do
      i2 <- return (i - (2 EXP ht));
      t2x <- heap_array_sub i2;
      return (~ (R t2x x))
    od else return F;
    if upd
    then insert_into_sfx_heap_list R (i - 1) (j + 1) x
    else return ();
  od
End

(* Reduce a sequence of suffix-encoded heaps to a list. *)
Definition sfx_trees_to_list_def:
  sfx_trees_to_list R i j acc =
  if i = 0 then return acc
  else do
    ht <- sz_array_sub (j - 1);
    x <- heap_array_sub (i - 1);
    if ht <= 1 then sfx_trees_to_list R (i - 1) (j - 1) (x :: acc)
    else do
      l <- return (sfx_heap_left i ht);
      reinsert_tree R l (j - 1) (ht - 1);
      reinsert_tree R (i - 1) j (ht - 1);
      sfx_trees_to_list R (i - 1) (j + 1) (x :: acc)
    od
  od
End

(* Compute an overapproximation of the base-2 logarithm of v *)
Definition above_log2_def:
  above_log2 i v n = if n = 0n \/ v <= n
    then i
    else above_log2 (i + 1n) v (n * 2)
Termination
  WF_REL_TAC `measure (\(i, v, n). (v - n))`
End

Definition sort_via_sfx_trees_worker_def:
  sort_via_sfx_trees_worker R x xs = do
      sz <- return (LENGTH xs);
      alloc_heap_array (sz + 1) x;
      sz_log <- return (above_log2 0 (sz + 1) 1);
      alloc_sz_array (sz_log + 5) 0;
      (i, j) <- add_all_to_sfx_heaps R 0 0 xs;
      sfx_trees_to_list R i j []
  od
End

Definition sort_via_sfx_trees_run_worker_def:
  sort_via_sfx_trees_run_worker R x xs =
  run_init_state (sort_via_sfx_trees_worker R x xs)
    (init_state [] [])
End

Definition sort_via_sfx_trees_def:
  sort_via_sfx_trees R xs = (case xs of [] => []
    | x :: _ => (case sort_via_sfx_trees_run_worker R x xs of
        M_success ys => ys
      | _ => [])
  )
End

(* Part 3. Proof that this monadic encoding computes the same as the pure heap
   list sort implementation. *)

(* 3.1: Setup *)

Definition bs_tree_to_list_def:
  (bs_tree_to_list 0 t = []) /\
  (bs_tree_to_list (SUC ht) t =
     bs_tree_to_list ht (case t of Node _ l r => l | _ => t) ++
     bs_tree_to_list ht (case t of Node _ l r => r | _ => t) ++
     [case t of Node x l r => x]
  )
End

Theorem bs_tree_to_list_tree_rec[local]:
  (i = 0 ==> bs_tree_to_list i Empty_Tree = []) /\
  (0 < i ==> bs_tree_to_list i (Node x l r) =
    bs_tree_to_list (i - 1) l ++
    bs_tree_to_list (i - 1) r ++
    [x])
Proof
  Cases_on `i` \\ simp [bs_tree_to_list_def]
QED

Definition two_exp_min_1_def:
  two_exp_min_1 i = (2n EXP i) - 1
End

Theorem two_exp_min_1_less_rec[local]:
  0 < i ==> two_exp_min_1 i = two_exp_min_1 (i - 1) + two_exp_min_1 (i - 1) + 1
Proof
  Cases_on `i`
  \\ fs [two_exp_min_1_def, EXP]
  \\ rw [SUB_RIGHT_ADD]
QED

Theorem two_exp_min_1_rec[local]:
  two_exp_min_1 0 = 0 /\
  two_exp_min_1 (SUC i) = two_exp_min_1 i + two_exp_min_1 i + 1
Proof
  simp [two_exp_min_1_less_rec] \\ simp [two_exp_min_1_def]
QED

Theorem to_two_exp_min_1[local]:
  (2n EXP i) = (two_exp_min_1 i + 1)
Proof
  rw [two_exp_min_1_def, SUB_RIGHT_ADD]
QED

Theorem LENGTH_bs_tree_to_list[local]:
  ! i t. LENGTH (bs_tree_to_list i t) = two_exp_min_1 i
Proof
  Induct
  \\ simp [bs_tree_to_list_def, two_exp_min_1_rec]
QED

Theorem LAST_bs_tree_to_list[local]:
  0 < ht ==> LAST (bs_tree_to_list ht t) = (
    case t of Node x _ _ => x)
Proof
  Cases_on `ht` \\ simp [bs_tree_to_list_def, two_exp_min_1_rec]
QED

Definition tree_balanced_height_def:
  (tree_balanced_height i Empty_Tree = (i = 0n)) /\
  (tree_balanced_height i (Node x l r) = (
    (i > 0) /\ tree_balanced_height (i - 1) l /\
        tree_balanced_height (i - 1) r)
  )
End

Theorem tree_balanced_height_0[local]:
  (tree_balanced_height 0 t = (t = Empty_Tree))
Proof
  Cases_on `t` \\ simp [tree_balanced_height_def]
QED

Theorem tree_balanced_height_eq_0[local]:
  ht = 0 ==> (tree_balanced_height ht t = (t = Empty_Tree))
Proof
  Cases_on `t` \\ simp [tree_balanced_height_def]
QED

Theorem tree_balanced_height_pos[local]:
  0 < ht ==> tree_balanced_height ht t =
    (?x l r. t = Node x l r /\ tree_balanced_height (ht - 1) l /\
        tree_balanced_height (ht - 1) r)
Proof
  Cases_on `t` \\ simp [tree_balanced_height_def]
QED

Definition bs_tree_list_to_list_def:
  bs_tree_list_to_list ts =
    FLAT (MAP (\(t, i). bs_tree_to_list i t) (REVERSE ts))
End

Theorem bs_tree_list_to_list_rec[local]:
  bs_tree_list_to_list (t_i :: ts) = (
    bs_tree_list_to_list ts ++ bs_tree_to_list (SND t_i) (FST t_i)
  ) /\
  bs_tree_list_to_list [] = []
Proof
  simp [bs_tree_list_to_list_def]
  \\ rpt (pairarg_tac \\ fs[])
QED

Theorem st_ex_ignore_bind_simp[local]:
  st_ex_ignore_bind f g = st_ex_bind f (\_. g)
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_ignore_bind_def]
QED

(*
Theorem monad_simps[local] = LIST_CONJ
    [fetch "-" "update_heap_array_def", fetch "-" "heap_array_sub_def",
        ml_monadBaseTheory.monad_eqs, st_ex_ignore_bind_simp,
         fetch "-" "update_sz_array_def", fetch "-" "sz_array_sub_def"]

Theorem tree_len_simps_no_less[local] = LIST_CONJ
    [tree_balanced_height_def, tree_balanced_height_0,
        two_exp_min_1_rec,
        LENGTH_bs_tree_to_list, bs_tree_to_list_def,
        bs_tree_to_list_tree_rec, bs_tree_list_to_list_rec]

Theorem tree_len_simps[local] = LIST_CONJ [tree_len_simps_no_less,
        two_exp_min_1_less_rec]

Theorem TAKE_DROP_eq_imp[local]:
  !xs i j. TAKE i (DROP j xs) = ys ==>
  i <= LENGTH ys ==>
  ys = [] \/ (?xs_pre xs_post. xs = xs_pre ++ ys ++ xs_post /\
    j = LENGTH xs_pre /\ i = LENGTH ys)
Proof
  Cases_on `ys = []` \\ simp []
  \\ rw []
  \\ qexists_tac `TAKE j xs`
  \\ qexists_tac `DROP (i + j) xs`
  \\ fs [GSYM TAKE_SUM]
  \\ fs [LENGTH_TAKE_EQ]
QED

Theorem TAKE_DROP_last_eq_imp[local]:
  TAKE l (DROP ((i + 1) - l) xs) = ys /\
  i + 1 <= LENGTH xs /\ l <= i + 1 /\
  l <= LENGTH ys /\ 0 < l ==>
  ?xs_pre xs_post. xs = xs_pre ++ ys ++ xs_post /\
    l = LENGTH ys /\ i = LENGTH xs_pre + (LENGTH ys - 1)
Proof
  rpt strip_tac
  \\ dxrule TAKE_DROP_eq_imp
  \\ Cases_on `ys = []` \\ fs []
  \\ rw []
  \\ irule_at Any EQ_REFL
  \\ simp []
QED
*)

Theorem two_exp_min_1_pos[local]:
  (0 < two_exp_min_1 r) = (0 < r)
Proof
  Cases_on `r` \\ simp [two_exp_min_1_rec]
QED

Theorem MAP_SND_insert_trees_inv[local]:
  !ts. MAP SND (insert_trees_inv R ts x) = MAP SND ts
Proof
  Induct \\ simp [pairTheory.FORALL_PROD, insert_trees_inv_def]
  \\ rw []
  \\ rpt (TOP_CASE_TAC \\ simp [])
  \\ simp []
QED

Theorem MAP_LENGTH_insert_trees_inv[local]:
  MAP (LENGTH o (\(t, n). bs_tree_to_list n t))
            (insert_trees_inv R ts x) =
    MAP (LENGTH o (\(t, n). bs_tree_to_list n t)) ts
Proof
  qspec_then `ts` (mp_tac o Q.AP_TERM `MAP two_exp_min_1`) MAP_SND_insert_trees_inv
  \\ simp [MAP_MAP_o, o_DEF, UNCURRY, bs_tree_list_to_list_rec, LENGTH_bs_tree_to_list]
QED

Theorem LENGTH_insert_trees_inv[local] =
  Q.AP_TERM `LENGTH` (SPEC_ALL MAP_LENGTH_insert_trees_inv)
    |> REWRITE_RULE [LENGTH_MAP]

Theorem LENGTH_list_of_insert_trees[local]:
  LENGTH (bs_tree_list_to_list (insert_trees_inv R ts x)) =
  LENGTH (bs_tree_list_to_list ts)
Proof
  simp [bs_tree_list_to_list_def, LENGTH_FLAT, MAP_MAP_o, MAP_REVERSE]
  \\ simp [MAP_LENGTH_insert_trees_inv]
QED

Theorem tree_to_list_unfold = LIST_CONJ [
  bs_tree_list_to_list_rec, bs_tree_to_list_tree_rec]

Theorem LENGTH_add_tree_step1_facts[local]:
  0 < LENGTH (add_trees_step1 ts x) /\
  LENGTH (bs_tree_list_to_list (add_trees_step1 ts x)) =
    LENGTH (bs_tree_list_to_list ts) + 1 /\
  LENGTH (add_trees_step1 ts x) <= LENGTH ts + 1 /\
  (MAP SND (add_trees_step1 ts x) = MAP SND (add_trees_step1 ts y)) = T /\
  (LENGTH (add_trees_step1 ts x) = LENGTH (add_trees_step1 ts y)) = T
Proof
  simp [add_trees_step1_def]
  \\ rpt (TOP_CASE_TAC \\ fs [tree_to_list_unfold])
QED

Theorem inv_add_tree_step1[local]:
  (EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
    EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) (add_trees_step1 ts x)
  ) /\
  (EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts /\
    SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) ==>
    SORTED ($<=) (TAKE 2 (MAP SND (add_trees_step1 ts x))) /\
    SORTED ($<) (MAP SND (DROP 1 (add_trees_step1 ts x)))
  )
Proof
  simp [add_trees_step1_def]
  \\ rpt (TOP_CASE_TAC \\ fs [tree_balanced_height_def])
  \\ rpt (pairarg_tac \\ fs [])
  \\ rw []
  \\ fs []
  \\ imp_res_tac SORTED_TL \\ fs []
  \\ Cases_on `t'` \\ fs []
QED

Theorem insert_trees_adj_with_inv[local]:
  EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
  insert_trees_inv R ((Node x_dc l r, n) :: ts) x =
      insert_trees_inv R ((Node y_dc l r, n) :: ts) x
Proof
  simp [insert_trees_inv_def]
  \\ rpt (TOP_CASE_TAC \\ fs []) \\ rw [] \\ fs [tree_balanced_height_def]
  \\ simp [insert_tree_inv_def]
QED

Theorem insert_trees_adj_add_trees_with_inv[local]:
  EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
  insert_trees_inv R (add_trees_step1 ts x_dc) x =
      insert_trees_inv R (add_trees_step1 ts y_dc) x
Proof
  simp [add_trees_step1_def]
  \\ rpt (TOP_CASE_TAC \\ fs [tree_balanced_height_def])
  \\ rw []
  \\ irule insert_trees_adj_with_inv
  \\ simp []
QED

Theorem LENGTH_to_list_add_trees[local]:
  LENGTH (bs_tree_list_to_list (add_trees R ts x)) =
    LENGTH (bs_tree_list_to_list ts) + 1
Proof
  simp [add_trees_def, LENGTH_list_of_insert_trees, LENGTH_add_tree_step1_facts]
QED

Theorem insert_tree_inv_balance_inv[local]:
  !t ht. tree_balanced_height ht t ==>
  tree_balanced_height ht (insert_tree_inv R t x)
Proof
  Induct \\ simp [insert_tree_inv_def]
  \\ rpt (TOP_CASE_TAC \\ fs [tree_balanced_height_def])
QED

Theorem insert_trees_inv_balance_inv[local]:
  !ts x. EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
  EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) (insert_trees_inv R ts x)
Proof
  Induct \\ simp [pairTheory.FORALL_PROD, insert_trees_inv_def]
  \\ rw []
  \\ rpt (TOP_CASE_TAC \\ fs [tree_balanced_height_def, insert_tree_inv_balance_inv])
QED

Theorem inv_add_trees[local]:
  (EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts ==>
    EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) (add_trees R ts x)
  ) /\
  (EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts /\
    SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) ==>
    SORTED ($<=) (TAKE 2 (MAP SND (add_trees R ts x))) /\
    SORTED ($<) (MAP SND (DROP 1 (add_trees R ts x)))
  )
Proof
  simp [add_trees_def, MAP_SND_insert_trees_inv, MAP_DROP]
  \\ simp [GSYM MAP_DROP, inv_add_tree_step1, insert_trees_inv_balance_inv]
QED

Theorem sum_lengths_greater_equal_exp[local]:
  ! ts n. EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED $< (MAP SND ts) /\
  ts <> [] /\ n <= SND (HD ts) /\ 1 <= n ==>
  ((2 EXP (LENGTH ts + (n - 1))) - 1) <= LENGTH (bs_tree_list_to_list ts)
Proof
  Induct \\ rw []
  \\ fs [tree_to_list_unfold, LENGTH_bs_tree_to_list]
  \\ pairarg_tac \\ fs []
  \\ first_x_assum (qspec_then `SUC n` mp_tac)
  \\ imp_res_tac SORTED_TL
  \\ simp [EXP]
  \\ Cases_on `ts` \\ fs []
  >- (
    simp [tree_to_list_unfold]
    \\ simp [two_exp_min_1_def, LEFT_SUB_DISTRIB]
    \\ simp [GSYM EXP, ADD1]
    \\ rw [SUB_RIGHT_ADD]
  )
  >- (
    rw []
    \\ gs [ADD1]
  )
QED

Theorem inv_trees_less_via_exp[local]:
  EVERY (\(t,n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED $< (DROP 1 (MAP SND ts)) /\
  LENGTH (bs_tree_list_to_list ts) < 2 ** lg /\
  lg + i + 2 <= bd ==>
  LENGTH ts + i < bd
Proof
  rw []
  \\ fs [GSYM MAP_DROP]
  \\ drule_at (Pat `SORTED _ _`) sum_lengths_greater_equal_exp
  \\ simp [EVERY_DROP]
  \\ disch_then (qspec_then `1` mp_tac)
  \\ Cases_on `LENGTH ts <= 1` \\ fs []
  \\ impl_tac
  >- (
    fs [HD_DROP, EVERY_EL, UNCURRY]
    \\ first_x_assum (qspec_then `1` mp_tac)
    \\ simp []
  )
  \\ disch_tac
  \\ subgoal `2n ** (LENGTH ts - 1) < 2 ** lg`
  >- (
    drule_then irule LESS_EQ_LESS_TRANS
    \\ Cases_on `ts` \\ fs [tree_to_list_unfold]
    \\ pairarg_tac \\ fs []
    \\ gs [tree_balanced_height_pos, tree_to_list_unfold]
  )
  \\ fs []
QED

Theorem LENGTH_extend_trees_facts[local]:
  tree_balanced_height ht t /\ 0 < ht ==>
  LENGTH (extend_trees R ts t ht) = LENGTH ts + 1
  /\
  MAP SND (extend_trees R ts t ht) = ht :: MAP SND ts
  /\
  LENGTH (bs_tree_list_to_list (extend_trees R ts t ht)) =
  LENGTH (bs_tree_list_to_list ts) + LENGTH (bs_tree_to_list ht t) /\
  (EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
    EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) (extend_trees R ts t ht)
  )
Proof
  rw [extend_trees_def]
  \\ fs [tree_to_list_unfold, tree_balanced_height_pos]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ simp [LENGTH_insert_trees_inv, MAP_SND_insert_trees_inv,
        LENGTH_list_of_insert_trees, tree_to_list_unfold, tree_balanced_height_def,
        insert_trees_inv_balance_inv]
QED

Theorem above_log2_is_above_ind[local]:
  ! i v n. n = 2 EXP i ==> v <= 2 ** (above_log2 i v n)
Proof
  recInduct above_log2_ind
  \\ rw [] \\ fs []
  \\ ONCE_REWRITE_TAC [above_log2_def]
  \\ rw [] \\ fs [EXP_ADD]
QED

Theorem build_trees_facts[local]:
  !xs ts.
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
  LENGTH (bs_tree_list_to_list (build_trees R ts xs)) =
    LENGTH (bs_tree_list_to_list ts) + LENGTH xs /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) (build_trees R ts xs) /\
  (SORTED $< (MAP SND (DROP 1 ts)) /\ SORTED $<= (TAKE 2 (MAP SND ts)) ==>
    SORTED $< (MAP SND (DROP 1 (build_trees R ts xs))) /\
    SORTED $<= (TAKE 2 (MAP SND (build_trees R ts xs))))
Proof
  Induct \\ simp [tree_to_list_unfold, build_trees_def]
  \\ rw []
  \\ simp [inv_add_trees, LENGTH_to_list_add_trees]
  \\ fs [IMP_CONJ_THM, FORALL_AND_THM]
QED

(* 3.2: State/Heap-list equivalence setup. *)

Definition mk_st_def:
  mk_st hps szs =
    (<|
        sz_array := REVERSE (FST szs) ++ SND szs;
        heap_array := bs_tree_list_to_list (FST hps) ++ SND hps
    |> : 'a state_refs)
End

Definition is_last_ix_def:
  is_last_ix szs i = (SUM (MAP two_exp_min_1 szs) = i + 1)
End

Theorem is_last_ix_eq_min_1:
  is_last_ix szs i ==> i = SUM (MAP two_exp_min_1 szs) - 1
Proof
  simp [is_last_ix_def]
QED

Theorem bind_success_eqI:
  m st = (M_success v, st2) /\ f v st2 = rhs ==>
  st_ex_bind m f st = rhs
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def]
QED

Theorem bind_success_rdonly_eqI =
  Q.INST [`st2` |-> `st`] bind_success_eqI

Theorem mk_st_node_split_r:
  0 < ht ==>
  mk_st ((Node x l r, ht) :: hps, oths) szs =
  mk_st ((r, ht - 1) :: (l, ht - 1) :: hps, x :: oths) szs
Proof
  simp [mk_st_def, tree_to_list_unfold]
QED

Theorem mk_st_node_split_l:
  0 < ht ==>
  mk_st ((Node x l r, ht) :: hps, oths) szs =
  mk_st ((l, ht - 1) :: hps, bs_tree_to_list (ht - 1) r ++ x :: oths) szs
Proof
  simp [mk_st_def, tree_to_list_unfold]
QED

Theorem mk_st_move_others:
  mk_st ((t, ht) :: hps, oths) szs_pair =
  mk_st (hps, bs_tree_to_list ht t ++ oths) szs_pair /\
  mk_st hps_pair (n :: szs, sz_oths) =
  mk_st hps_pair (szs, n :: sz_oths)
Proof
  simp [mk_st_def, tree_to_list_unfold]
QED

Theorem LENGTH_bs_tree_list_to_list_eq_SUM[local]:
  LENGTH (bs_tree_list_to_list ts) = SUM (MAP two_exp_min_1 (MAP SND ts))
Proof
  simp [bs_tree_list_to_list_def, LENGTH_FLAT, MAP_MAP_o, o_DEF]
  \\ simp [UNCURRY, LENGTH_bs_tree_to_list, MAP_REVERSE, SUM_REVERSE]
QED

Theorem heap_array_sub_curr_bind_eq:
  is_last_ix (ht :: MAP SND hps) i /\ 0 < ht ==>
  st_ex_bind (heap_array_sub i) f
    (mk_st ((Node x l r, ht) :: hps, oths) szs) =
  f x (mk_st ((Node x l r, ht) :: hps, oths) szs)
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "heap_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, tree_to_list_unfold, LENGTH_bs_tree_to_list]
  \\ fs [is_last_ix_def, LENGTH_bs_tree_list_to_list_eq_SUM, two_exp_min_1_less_rec,
            EL_APPEND1, EL_APPEND2, LENGTH_bs_tree_to_list, EL_CONS_IF]
QED

Theorem is_last_ix_imps:
  is_last_ix (ht :: hts) i ==>
  (1 < ht ==> is_last_ix (ht - 1 :: hts) (sfx_heap_left i ht)) /\
  (1 < ht ==> is_last_ix (ht - 1 :: ht - 1 :: hts) (i - 1)) /\
  (0 < LENGTH hts /\ 0 < HD hts ==> is_last_ix hts (i - two_exp_min_1 ht))
Proof
  fs [is_last_ix_def]
  \\ rw []
  \\ fs [sfx_heap_left_def, to_two_exp_min_1, two_exp_min_1_less_rec]
  \\ Cases_on `hts` \\ fs []
  \\ fs [sfx_heap_left_def, to_two_exp_min_1, two_exp_min_1_less_rec]
QED

Theorem heap_array_sub_left_bind_eq:
  is_last_ix (ht :: MAP SND hps) i /\ 1 < ht ==>
  st_ex_bind (heap_array_sub (sfx_heap_left i ht)) f
    (mk_st ((Node x (Node lx ll lr) r, ht) :: hps, oths) szs) =
  f lx (mk_st ((Node x (Node lx ll lr) r, ht) :: hps, oths) szs)
Proof
  rw []
  \\ imp_res_tac is_last_ix_imps
  \\ fs []
  \\ simp [Once mk_st_node_split_l]
  \\ simp [heap_array_sub_curr_bind_eq]
  \\ simp [mk_st_node_split_l]
QED

Theorem heap_array_sub_right_bind_eq:
  is_last_ix (ht :: MAP SND hps) i /\ 1 < ht ==>
  st_ex_bind (heap_array_sub (i - 1)) f
    (mk_st ((Node x l (Node rx rl rr), ht) :: hps, oths) szs) =
  f rx (mk_st ((Node x l (Node rx rl rr), ht) :: hps, oths) szs)
Proof
  rw []
  \\ imp_res_tac is_last_ix_imps
  \\ fs []
  \\ simp [Once mk_st_node_split_r]
  \\ simp [heap_array_sub_curr_bind_eq]
  \\ simp [mk_st_node_split_r]
QED

Theorem heap_array_sub_prev_bind_eq:
  is_last_ix (ht :: MAP SND hps) i /\ 0 < LENGTH hps /\
    EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) hps ==>
  st_ex_bind (heap_array_sub (i - two_exp_min_1 ht)) f
    (mk_st ((t, ht) :: hps, oths) szs) =
  f (case hps of (Node x _ _, _) :: _ => x) (mk_st ((t, ht) :: hps, oths) szs)
Proof
  rw []
  \\ imp_res_tac is_last_ix_imps
  \\ fs []
  \\ simp [mk_st_move_others]
  \\ Cases_on `HD hps` \\ Cases_on `hps` \\ fs []
  \\ gs [tree_balanced_height_pos]
  \\ simp [heap_array_sub_curr_bind_eq]
QED

Theorem update_heap_array_mk_st_eq:
  is_last_ix (ht :: MAP SND hps) i /\ 0 < ht ==>
  update_heap_array i x (mk_st ((Node x_dc l r, ht) :: hps, oths) szs) =
        (M_success (), mk_st ((Node x l r, ht) :: hps, oths) szs)
Proof
  simp [fetch "-" "update_heap_array_def", ml_monadBaseTheory.monad_eqs]
  \\ rw [is_last_ix_def, mk_st_def]
  \\ fs [tree_to_list_unfold, LENGTH_bs_tree_to_list,
            LENGTH_bs_tree_list_to_list_eq_SUM, LUPDATE_APPEND,
            two_exp_min_1_less_rec, LUPDATE_DEF]
QED

Theorem return_bind_eq:
  st_ex_bind (return v) f = f v
Proof
  simp [ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.st_ex_return_def, FUN_EQ_THM]
QED

Theorem sz_array_sub_bind_eq:
  i < LENGTH szs ==>
  st_ex_bind (sz_array_sub i) f (mk_st hps (szs, oths)) =
  f (EL (LENGTH szs - (i + 1)) szs) (mk_st hps (szs, oths))
Proof
  rw []
  \\ irule bind_success_eqI
  \\ simp [fetch "-" "sz_array_sub_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def, EL_APPEND1, EL_REVERSE, PRE_SUB1]
QED

Theorem update_sz_array_eq:
  i < LENGTH szs ==>
  update_sz_array i x (mk_st hps (szs, oths)) =
    (M_success (), mk_st hps (LUPDATE x (LENGTH szs - (i + 1)) szs, oths))
Proof
  rw []
  \\ simp [fetch "-" "update_sz_array_def", ml_monadBaseTheory.monad_eqs]
  \\ simp [mk_st_def]
  \\ qspecl_then [`REVERSE szs`, `i`] mp_tac LESS_LENGTH
  \\ simp [listTheory.SWAP_REVERSE_SYM]
  \\ rw []
  \\ simp [LUPDATE_APPEND1, LUPDATE_APPEND2, LUPDATE_DEF]
QED

(* 3.3: Proofs of equivalence *)

Theorem insert_into_sfx_heap_eq:
  ! ht hps oths t R i x st.
  is_last_ix (ht :: MAP SND hps) i /\ ht > 0 /\
  tree_balanced_height ht t ==>
  insert_into_sfx_heap R i ht x (mk_st ((t, ht) :: hps, oths) szs) =
    (M_success (), (mk_st ((insert_tree_inv R t x, ht) :: hps, oths) szs))
Proof
  Induct
  \\ simp [ADD1]
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_def]
  \\ simp [tree_balanced_height_pos]
  \\ rw []
  >- (
    Cases_on `ht` \\ fs [tree_balanced_height_0]
    \\ simp [insert_tree_inv_def, update_heap_array_mk_st_eq]
  )
  >- (
    simp [return_bind_eq]
    \\ gs [tree_balanced_height_pos]
    \\ ONCE_REWRITE_TAC [insert_tree_inv_def]
    \\ drule_then assume_tac is_last_ix_imps
    \\ gs []
    \\ simp [heap_array_sub_left_bind_eq, heap_array_sub_right_bind_eq]
    \\ rpt TOP_CASE_TAC
    \\ simp [update_heap_array_mk_st_eq, st_ex_ignore_bind_simp]
    >- (
      simp [st_ex_ignore_bind_simp]
      \\ irule bind_success_eqI
      \\ simp [update_heap_array_mk_st_eq]
      \\ simp [Once mk_st_node_split_r]
      \\ simp [mk_st_node_split_r]
    )
    >- (
      simp [st_ex_ignore_bind_simp]
      \\ irule bind_success_eqI
      \\ simp [update_heap_array_mk_st_eq]
      \\ simp [Once mk_st_node_split_l]
      \\ simp [mk_st_node_split_l]
    )
  )
QED

Theorem insert_into_sfx_heap_list_eq:
  ! j ts R i x oths szs.
  j = LENGTH ts /\
  is_last_ix (MAP SND ts) i /\
  0 < j /\ EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts ==>
  insert_into_sfx_heap_list R i j x (mk_st (ts, oths) (MAP SND ts, szs)) =
    (M_success (), mk_st (insert_trees_inv R ts x, oths) (MAP SND ts, szs))
Proof
  Induct
  \\ simp []
  \\ ONCE_REWRITE_TAC [insert_into_sfx_heap_list_def]
  \\ rpt strip_tac
  \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs []
  \\ gs [ADD1, TAKE_SUM]
  \\ simp [insert_trees_inv_def]
  \\ rw []
  >- (
    Cases_on `t` \\ fs []
    \\ simp [sz_array_sub_bind_eq, return_bind_eq]
    \\ simp [insert_into_sfx_heap_eq]
  )
  \\ simp [sz_array_sub_bind_eq, return_bind_eq]
  \\ simp [ADD1]
  \\ simp [to_two_exp_min_1, heap_array_sub_prev_bind_eq]
  \\ irule bind_success_rdonly_eqI
  \\ qexists_tac `case t of ((Node t2x _ _, _) :: _) =>
        ~ R t2x x /\ ~ (case q of Node _ (Node lx _ _) _ => R t2x lx | _ => F) /\
        ~ (case q of Node _ _ (Node rx _ _) => R t2x rx | _ => F) | _ => F`
  \\ conj_tac
  >- (
    Cases_on `HD t` \\ Cases_on `t` \\ fs []
    \\ rw []
    >- (
      gs [tree_balanced_height_pos]
      \\ simp [heap_array_sub_left_bind_eq, heap_array_sub_right_bind_eq]
      \\ simp [ml_monadBaseTheory.monad_eqs]
    )
    >- (
      simp [ml_monadBaseTheory.monad_eqs]
      \\ gs [tree_balanced_height_pos, tree_balanced_height_eq_0]
    )
  )
  \\ simp []
  \\ TOP_CASE_TAC
  >- (
    gs [tree_balanced_height_pos]
    \\ simp [st_ex_ignore_bind_simp]
    \\ irule bind_success_eqI
    \\ simp [update_heap_array_mk_st_eq]
    \\ simp [mk_st_move_others]
    \\ drule_then assume_tac is_last_ix_imps
    \\ gs []
    \\ Cases_on `HD t` \\ Cases_on `t` \\ fs []
    \\ gs [tree_balanced_height_pos]
    \\ simp [insert_trees_inv_def, mk_st_move_others]
  )
  >- (
    simp [insert_into_sfx_heap_eq]
    \\ Cases_on `HD t` \\ Cases_on `t` \\ fs []
    \\ gs [tree_balanced_height_pos]
  )
QED

Theorem add_to_sfx_heaps_step1_eq:
  j = LENGTH ts /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  0 < LENGTH oth_szs ==>
  ? oth_szs2.
  let ts2 = add_trees_step1 ts x in
  add_to_sfx_heaps_step1 j (mk_st (ts, x :: oths) (MAP SND ts, oth_szs)) =
        (M_success (LENGTH ts2), mk_st (ts2, oths) (MAP SND ts2, oth_szs2)) /\
  LENGTH ts2 + LENGTH oth_szs2 = LENGTH ts + LENGTH oth_szs
Proof
  rw []
  \\ simp [add_to_sfx_heaps_step1_def, add_trees_step1_def]
  \\ irule_at Any bind_success_rdonly_eqI
  \\ qexists_tac `case ts of (_, n1) :: (_, n2) :: _ => n1 = n2 | _ => F`
  \\ simp [GSYM PULL_EXISTS]
  \\ conj_tac
  >- (
    every_case_tac \\ fs []
    \\ simp [sz_array_sub_bind_eq, ADD1]
    \\ simp [ml_monadBaseTheory.monad_eqs]
  )
  \\ TOP_CASE_TAC
  >- (
    every_case_tac \\ fs []
    \\ simp [sz_array_sub_bind_eq, ADD1, st_ex_ignore_bind_simp]
    \\ irule_at Any bind_success_eqI
    \\ simp [update_sz_array_eq, ml_monadBaseTheory.monad_eqs]
    \\ simp [ADD1, LUPDATE_DEF]
    \\ simp [mk_st_node_split_r, mk_st_move_others]
    \\ irule_at Any EQ_REFL
    \\ simp []
  )
  >- (
    simp [st_ex_ignore_bind_simp]
    \\ irule_at Any bind_success_eqI
    \\ Cases_on `oth_szs` \\ fs []
    \\ simp [GSYM mk_st_move_others]
    \\ simp [update_sz_array_eq, ml_monadBaseTheory.monad_eqs]
    \\ simp [ADD1, LUPDATE_DEF]
    \\ every_case_tac \\ fs []
    \\ simp [mk_st_move_others, bs_tree_to_list_tree_rec]
    \\ REWRITE_TAC [GSYM APPEND_ASSOC, APPEND]
    \\ irule_at Any EQ_REFL
    \\ simp []
  )
QED

Theorem add_to_sfx_heaps_eq:
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts) /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  0 < LENGTH oth_szs /\ 0 < LENGTH oths ==>
  let ts2 = add_trees R ts x in
  ? oth_szs2.
  add_to_sfx_heaps R i j x (mk_st (ts, oths) (MAP SND ts, oth_szs)) =
    (M_success (LENGTH ts2), mk_st (ts2, TL oths) (MAP SND ts2, oth_szs2)) /\
  LENGTH ts2 + LENGTH oth_szs2 = LENGTH ts + LENGTH oth_szs
Proof
  rpt strip_tac
  \\ qspecl_then [`HD oths`, `TL oths`] mp_tac (Q.GENL [`x`, `oths`] add_to_sfx_heaps_step1_eq)
  \\ Cases_on `oths` \\ fs []
  \\ rw []
  \\ simp [add_to_sfx_heaps_def, add_trees_def]
  \\ irule_at Any bind_success_eqI
  \\ simp [st_ex_ignore_bind_simp]
  \\ irule_at Any bind_success_eqI
  \\ simp [ml_monadBaseTheory.monad_eqs, LENGTH_insert_trees_inv]
  \\ dep_rewrite.DEP_REWRITE_TAC [insert_into_sfx_heap_list_eq]
  \\ simp [LENGTH_add_tree_step1_facts, inv_add_tree_step1, is_last_ix_def,
        GSYM LENGTH_bs_tree_list_to_list_eq_SUM]
  \\ simp [MAP_SND_insert_trees_inv]
  \\ irule_at Any (Q.prove (`a = b /\ c = d ==> mk_st a c = mk_st b d`, simp []))
  \\ simp []
  \\ metis_tac [insert_trees_adj_add_trees_with_inv, LENGTH_add_tree_step1_facts]
QED

Theorem add_all_to_sfx_heaps_eq:
  !xs i j ts oths oth_szs.
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ts) /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) /\
  lg + 3 <= LENGTH ts + LENGTH oth_szs /\
  i + LENGTH xs < 2 EXP lg ==>
  LENGTH xs <= LENGTH oths ==>
  let ts2 = build_trees R ts xs in
  ? oth_szs2.
  add_all_to_sfx_heaps R i j xs (mk_st (ts, oths) (MAP SND ts, oth_szs)) =
        (M_success (LENGTH (bs_tree_list_to_list ts2), LENGTH ts2),
            mk_st (ts2, DROP (LENGTH xs) oths) (MAP SND ts2, oth_szs2)) /\
  LENGTH ts2 + LENGTH oth_szs2 = LENGTH ts + LENGTH oth_szs
Proof
  Induct
  \\ simp [add_all_to_sfx_heaps_def, build_trees_def]
  >- (
    simp [ml_monadBaseTheory.monad_eqs]
    \\ metis_tac []
  )
  \\ rpt strip_tac
  \\ irule_at Any bind_success_eqI
  \\ qmatch_goalsub_abbrev_tac `add_to_sfx_heaps R i j x`
  \\ mp_tac add_to_sfx_heaps_eq
  \\ fs [markerTheory.Abbrev_def]
  \\ impl_keep_tac
  >- (
    (* exponential argument that there is space in szs array *)
    drule inv_trees_less_via_exp
    \\ disch_then (qspecl_then [`lg`, `1`] mp_tac)
    \\ simp [GSYM MAP_DROP]
    \\ disch_then dxrule
    \\ simp []
  )
  \\ rw [] \\ simp []
  \\ qmatch_goalsub_abbrev_tac `mk_st (ts2, _)`
  \\ first_x_assum (qspecl_then [`ts2`, `TL oths`, `oth_szs2`] mp_tac)
  \\ fs [markerTheory.Abbrev_def]
  \\ simp [LENGTH_to_list_add_trees, inv_add_trees]
  \\ rw [] \\ simp []
  \\ Cases_on `oths` \\ fs []
  \\ irule_at Any EQ_REFL
  \\ simp []
QED

Theorem reinsert_tree_eq:
  j = LENGTH ts /\ i = LENGTH (bs_tree_list_to_list ((t, ht) :: ts)) /\
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) /\
  0 < ht /\ tree_balanced_height ht t ==>
  reinsert_tree R i j ht (mk_st ((t, ht) :: ts, oths) (dc :: MAP SND ts, oth_szs)) =
    (let ts2 = extend_trees R ts t ht in
        (M_success (), mk_st (ts2, oths) (MAP SND ts2, oth_szs)))
Proof
  simp [reinsert_tree_def, extend_trees_def]
  \\ rw []
  \\ gs [tree_balanced_height_pos]
  \\ qmatch_goalsub_abbrev_tac `mk_st (COND tree_cond _ _, _)`
  \\ simp [st_ex_ignore_bind_simp]
  \\ irule_at Any bind_success_eqI
  \\ simp [update_sz_array_eq]
  \\ dep_rewrite.DEP_REWRITE_TAC [heap_array_sub_curr_bind_eq]
  \\ conj_asm1_tac
  >- (
    fs [markerTheory.Abbrev_def]
    \\ simp [is_last_ix_def, LENGTH_bs_tree_list_to_list_eq_SUM]
    \\ fs [two_exp_min_1_less_rec]
  )
  \\ irule_at Any bind_success_rdonly_eqI
  \\ qexists_tac `~ tree_cond`
  \\ conj_tac
  >- (
    rw []
    \\ simp [return_bind_eq, to_two_exp_min_1]
    \\ simp [heap_array_sub_prev_bind_eq |> Q.GEN `i` |> Q.SPEC `i - 1`
        |> SIMP_RULE (srw_ss ()) [GSYM SUB_PLUS, ADD_COMM]]
    \\ simp [ml_monadBaseTheory.monad_eqs]
    \\ every_case_tac \\ fs [markerTheory.Abbrev_def]
    \\ gs [tree_balanced_height_pos]
  )
  \\ rw []
  >- (
    simp [ADD1, LUPDATE_DEF]
    \\ qmatch_goalsub_abbrev_tac `mk_st (tt :: ts, _)`
    \\ qspecl_then [`j`, `tt :: ts`] (mp_tac o Q.GEN `j`) insert_into_sfx_heap_list_eq
    \\ fs [markerTheory.Abbrev_def, tree_balanced_height_def, ADD1]
    \\ simp [MAP_SND_insert_trees_inv]
  )
  \\ simp [ml_monadBaseTheory.monad_eqs]
  \\ simp [ADD1, LUPDATE_DEF]
QED

Theorem sfx_trees_to_list_eq:
  !i j acc ts oths oth_szs.
  EVERY (\(t, n). 0 < n /\ tree_balanced_height n t) ts /\
  SORTED ($<=) (TAKE 2 (MAP SND ts)) /\ SORTED ($<) (MAP SND (DROP 1 ts)) /\
  LENGTH ts = j /\ LENGTH (bs_tree_list_to_list ts) = i /\
  lg + 4 <= LENGTH ts + LENGTH oth_szs /\
  i < 2 EXP lg ==>
  ?st'. sfx_trees_to_list R i j acc (mk_st (ts, oths) (MAP SND ts, oth_szs)) =
    (M_success (pull_trees R ts acc), st')
Proof
  Induct
  \\ REWRITE_TAC []
  \\ ONCE_REWRITE_TAC [sfx_trees_to_list_def]
  >- (
    rw []
    \\ Cases_on `ts` \\ fs []
    \\ simp [ml_monadBaseTheory.monad_eqs, pull_trees_def]
    \\ rpt (pairarg_tac \\ fs []) \\ gs [tree_to_list_unfold, tree_balanced_height_pos]
  )
  \\ rw []
  \\ subgoal `is_last_ix (MAP SND ts) i`
  >- (
    fs [is_last_ix_def, ADD1]
    \\ fs [LENGTH_bs_tree_list_to_list_eq_SUM]
  )
  \\ Cases_on `HD ts` \\ Cases_on `ts` \\ fs [bs_tree_list_to_list_rec]
  \\ simp [sz_array_sub_bind_eq, ADD1]
  \\ gs [tree_balanced_height_pos, bs_tree_to_list_tree_rec, ADD1]
  \\ simp [heap_array_sub_curr_bind_eq]
(*
  \\ drule inv_trees_less_via_exp
  \\ simp [GSYM MAP_DROP]
  \\ disch_then (qspecl_then [`lg`, `2`] mp_tac)
*)
  \\ subgoal `SORTED $<= (TAKE 2 (MAP SND t)) ∧ SORTED $< (DROP 1 (MAP SND t))`
  >- (
    Cases_on `TL t` \\ Cases_on `t` \\ fs []
  )
  \\ rw []
  >- (
    gs [tree_balanced_height_eq_0]
    \\ simp [mk_st_move_others, bs_tree_to_list_tree_rec, pull_trees_def,
            extend_trees_def]
    \\ first_x_assum irule
    \\ fs [bs_tree_to_list_tree_rec, MAP_DROP]
  )
  >- (
    simp [st_ex_ignore_bind_simp, return_bind_eq]
    \\ simp [mk_st_node_split_l]
    \\ simp [ml_monadBaseTheory.monad_eqs]
    \\ dep_rewrite.DEP_REWRITE_TAC [reinsert_tree_eq]
    \\ qpat_x_assum `_ = _ + 1n` (assume_tac o GSYM)
    \\ simp [MAP_DROP, sfx_heap_left_def, bs_tree_list_to_list_rec,
            LENGTH_bs_tree_to_list, to_two_exp_min_1]
    \\ Cases_on `oth_szs`
    >- (
      (* log/exp proof there is still a spare sz slot *)
      gs []
      \\ drule inv_trees_less_via_exp
      \\ disch_then (qspecl_then [`lg`, `2`] mp_tac)
      \\ simp []
      \\ disch_then drule
      \\ simp []
    )
    \\ simp [GSYM mk_st_move_others]
    \\ dep_rewrite.DEP_REWRITE_TAC [reinsert_tree_eq]
    \\ simp [LENGTH_extend_trees_facts, MAP_DROP, bs_tree_list_to_list_rec]
    \\ conj_tac
    >- (
      Cases_on `t` \\ fs []
    )
    \\ qmatch_goalsub_abbrev_tac `sfx_trees_to_list _ _ _ acc2 (mk_st (ts, oths2) (_, oth_szs2))`
    \\ first_x_assum (qspecl_then [`acc2`, `ts`, `oths2`, `oth_szs2`] mp_tac)
    \\ fs [markerTheory.Abbrev_def, LENGTH_extend_trees_facts, ADD1, MAP_DROP]
    \\ impl_tac
    >- (
      Cases_on `t` \\ fs []
    )
    \\ rw [] \\ simp []
    \\ simp [pull_trees_def]
  )
QED

Theorem sort_via_sfx_trees_eq:
  sort_via_sfx_trees R xs = another_heap_sort R xs
Proof
  simp [sort_via_sfx_trees_def, another_heap_sort_def]
  \\ Cases_on `xs`
  >- (
    simp [build_trees_def, pull_trees_def]
  )
  \\ simp [sort_via_sfx_trees_run_worker_def]
  \\ simp [run_init_state_def, ml_monadBaseTheory.run_def, sort_via_sfx_trees_worker_def]
  \\ simp [ml_monadBaseTheory.exc_case_eq, pairTheory.FST_EQ_EQUIV]
  \\ DISJ1_TAC
  \\ simp [fetch "-" "alloc_heap_array_def", fetch "-" "alloc_sz_array_def",
        ml_monadBaseTheory.monad_eqs, st_ex_ignore_bind_simp]
  \\ qmatch_goalsub_abbrev_tac `add_all_to_sfx_heaps _ _ _ xs st`
  \\ qspecl_then [`above_log2 0 (LENGTH xs + 1) 1`, `xs`,
            `0`, `0`, `[]`, `st.heap_array`, `st.sz_array`]
        mp_tac (add_all_to_sfx_heaps_eq |> Q.GEN `lg`)
  \\ qspecl_then [`0`, `LENGTH xs + 1`, `1`] assume_tac above_log2_is_above_ind
  \\ gs [markerTheory.Abbrev_def, bs_tree_list_to_list_rec, ADD1]
  \\ simp [mk_st_def |> Q.SPEC `([], x)`, bs_tree_list_to_list_rec]
  \\ rw [] \\ simp []
  \\ dep_rewrite.DEP_REWRITE_TAC [sfx_trees_to_list_eq |> Q.GEN `lg`]
  \\ simp [build_trees_facts]
  \\ simp [ADD1, bs_tree_list_to_list_rec]
  \\ drule_at_then Any (irule_at Any) LESS_LESS_EQ_TRANS
  \\ simp []
QED

(* Part 4: translation of the sfx variants. *)

fun fix_state_type thm = let
    val types_in_thm = thm |> concl |> all_atoms
      |> HOLset.listItems |> map type_of
      |> map (fn t => fst (strip_fun t) @ [snd (strip_fun t)])
      |> List.concat
    val state_matching_types = types_in_thm
      |> filter (can (match_type state_type))
      |> HOLset.fromList Type.compare |> HOLset.listItems
    val substs = map (fn t => match_type t state_type) state_matching_types
  in case substs of
    [] => thm
  | [s] => INST_TYPE s thm
  | _ => failwith "fix_state_type: multiple!"
  end

Definition comp_exp_def:
  comp_exp m x 0 = x /\
  comp_exp (m : num) x (SUC i) = comp_exp m (x * m) i
End

Theorem comp_exp_eq_ind[local]:
  !i x. comp_exp m x i = x * (m EXP i)
Proof
  Induct \\ simp [comp_exp_def, EXP]
QED

Theorem use_comp_exp:
  (m EXP i) = comp_exp m 1 i
Proof
  simp [comp_exp_eq_ind]
QED

val comp_exp_v_thm = comp_exp_def |> translate;

val sfx_heap_left_v_thm = sfx_heap_left_def
  |> REWRITE_RULE [use_comp_exp] |> translate;

val insert_into_sfx_heap_v_thm = insert_into_sfx_heap_def
  |> fix_state_type |> m_translate;

val insert_into_sfx_heap_list_v_thm = insert_into_sfx_heap_list_def
  |> REWRITE_RULE [use_comp_exp]
  |> fix_state_type |> m_translate;

Theorem bind_assoc[local]:
  st_ex_bind (st_ex_bind f g) h = do
    x <- f;
    y <- g x;
    h y
  od
Proof
  rw [ml_monadBaseTheory.st_ex_bind_def, FUN_EQ_THM]
  \\ rpt (TOP_CASE_TAC \\ fs [])
QED

val add_to_sfx_heaps_v_thm = add_to_sfx_heaps_def
  |> SIMP_RULE bool_ss [add_to_sfx_heaps_step1_def, bind_assoc]
  |> fix_state_type |> m_translate;

val add_all_to_sfx_heaps_v_thm = add_all_to_sfx_heaps_def
  |> fix_state_type |> m_translate;

val reinsert_tree_v_thm = reinsert_tree_def
  |> REWRITE_RULE [use_comp_exp]
  |> fix_state_type |> m_translate;

val sfx_trees_to_list_v_thm = sfx_trees_to_list_def
  |> fix_state_type |> m_translate;

val length_v_thm = LENGTH |> translate;

val above_log2_v_thm = above_log2_def |> translate;

val sort_via_sfx_trees_worker_v_thm = sort_via_sfx_trees_worker_def
  |> fix_state_type |> m_translate;

val sort_via_sfx_trees_run_worker_v_thm = sort_via_sfx_trees_run_worker_def
  |> fix_state_type |> m_translate_run;

val sort_via_sfx_trees_v_thm = sort_via_sfx_trees_def |> translate;


